-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3912
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:02:32.771933+00:00
-- url     : https://prove2.me/submissions/2c0084d4-1500-4a9b-befc-356037b9cd3e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 703417266 ≤ n < 703597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 703418516 1250 703417266 703417271
    0xa08040609030519031b05011104030308160c170a0306150323011d0a0e0d0e271602030409020c07030b0601111c02010b090901060302120d0905150c030a12 68
    0x844c00025078070b110120000340071542e0500c600707000d1a201c0e406081d01500413000440c4101005541554070351140e00185d0004000c1d00c100406040c801080c00d1700c200700d030718110041d06508d80300d041071811880390040543c1c80008480c1c4106110340c0004e03010f042e0502807010344000d8034002600505060404040303e000e01c00c07529610045088100c0e04841200040301d00c96440e61070b4540700c0c4c5100500c1c4504403650b0300c015040101d01000400c0b22562581c8504902c156164100814000380e01c0b1009880b04c0e8900340840c00e2142401016007100c6400701b0b16001c51503803102a4218000c580103040d407544045241200c81c80c0000d01841241e000e030102e14000e032111401181c0005400c0312006840d8000c0728078000c941001000e048060a60b0310001030700540043c0007c25442741910f295406a45400d428805e40c5003412504894550500c02030600d130307003907110103041084140703d00340c0f184070010b4104026500507030844800c402e400040d82e540d00035403d0003400c0f09540d134050403005403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 703419766 1250 703418516 703418533
    0x7020c1c0221060606070317040f02040540050d020a03080a02071a0402010e04060906090b01021c0c02030309100f14210a060f0b032e05060c0a080406090305 69
    0x72210301e082c4064122000d8400e070b070b581c3d8050017816408039104608200d44641c1c0040d040200c101c5443c0110310400c40d5443c0381c23070603004000580c1d85c05444115480c1d4541380c0003c0303009284050510412007492408640550308107411403642110501410f103000303007400b501e26580d01040034800c06210740c4442485440c1c2c2e5203900100d02907518020035500c0400302132400200b80c10b1001d0345c0544145860103a49400384003240640751a940240381903922100e0521002456020361030040200b8401800d15140001900412140c2c140c901d000b0f00450081c0300040d074038140200c030002c49002d02410f001c0ca00d1100e0040014002640650004001d406440c00e10010780301100d020344680320b540c1560785070b01429800100f0300904501c40c026074a2100140c41c54824001400800c550200542c1764542405100e485543c1e070100c140d00581c1c45400c108881507400322803030a60303030243c80007038941c100302d100b2508e4500e520342c002d0709161001c540010510b61228001058a00c18000e680001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 703421016 1250 703419766 703419799
    0xc0603090a0b070c0b01030f1104150911130e2e050414090d030b03010603140d020d0302030613050603010b0d0c080f16090e03040b04060917030901020d0807020c1c02 73
    0x130f01103d00081c54072950100420101d8032041e22040d405004005504907040090002000c841c41088a0384c10a0041c6400300031401544c801c1540e5030078208040d40c50072071944002e2050031640c5c0030340422054100003013903182001842c2c000008802421000421184403007500c0d1001c800c1c030136039208a0400c159000041e14aa46940c0070390403410051103000700c102c50540c00b4010a0b4500364142d907031054008041804040300d01071a940d07440c0074084141a03144001d0174075100707222100600d0300400a1014644501d072459044054048002070343d07440d0300c8006805420701c1480203a028002142000034401900340b41c00440d802202118003030340e100c00704240c4501298003032046401c200e22040240f948950001050700c420042500d160684814200c1100d0300300b504500002425100d00380405802c103105000d240c0a90401581464480d83c0000d568000d503240000801c6040404034119a0081048c50340703031100207068174100c0d0300346a000112040c40ea030003039109554071070350040b00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 703422266 1250 703421016 703421027
    0xf02030c0a1a13021008070201180c08011d0709150b1b071208071b03080418110f2205030706110c040c02280b13110102030f09010804050c0603090a0b07 67
    0x143c0340c1c06000c0b45c05802e440881075600d01e00041800b41503540b240c0700007940081a4070724440c040e00c00c0d0403c40b10b0030b0a08014608440400826156210030790040751384a0f0300c0010400207c0f10500740c0890821040004210005020b5005c035650200104e5011411151078004100d9961010200d40d040f5640701ca190220b0140108040d0030880108038440101d0b004030038408030241d80455021030a59241e40380012a0701680c40141418845461002d404a45006500e03c0362110128a401c080c03165040101c00e114080c80b420310f10780383e5040303c0c030b5858400700d07000010f00008065400113559014058100b4a40c02001500e5010b1a000400146014450082d440403d64000d050004a400c500d050f90702940c0b00c101401030307401c000100002c0c841c101c4684521030201c0c04201171a69444c01038440d10000308024155002400b0b0200c0408515007601d02000d0300740fa0580307003600e42d42030860074900026500da80002000040240300b260001e801880c2d94400d0071900e42c641c1d40c00b4401c848 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 703423516 1250 703422266 703422301
    0xf0606031a06090109030602030a060b030f1b040609060e04111912110a0809102901020109120f0908010f091b0b16060209120c1002010209090103030f02030c0a1a 71
    0x170890310305060000c540380d076015662011041000040946d2030b1150600c3c66082102d9a41d140d6082c242009240760200d03505e2010220742c158518106420080c000d0110440c41c01074004004c9440e04c0c0789010b0380e03035070041441580b00001141d501c4841000030640d484004030004e000c64036524400317035400307140d21406198a44503181d890034814a21011241d5041c0502011958400c1044031040b000305071060104040308010301800ba6004e80c001042081d5081c1c600e0350559140c249003002041c609000c48407002040d1512800d20210440c0941e00d2103400c1c1c003c41250740c0b81c809649400c0420798000040b00d40111081001d44041443c3c0514003034060168989000c402c0c803041d41400013021450315424401c03070b07001d4244548000450750308068190f1041150344a085101c8090402c0460700d4180c4541d0710080d0304d046d10a00c08540202010310004042218004480c8802d500c02d10554180040d44025184a11a1810b0070340f00203501180503410040c80b0b0002c5810b42500009512 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 703424766 1250 703423516 703423519
    0x1030818011b1b0e0c09040b06031501031107060219090f0308090f040905150f060d020f06070614070306140f010f180b0403050a14010e0303190f0606031a0609 70
    0x8503215a0b6588030807944041c0d60b146100940c10342c1021a18003031300d9041e544606500014240c40f000d008003040709440304c040c1d075140120010001c4c0210311aa2009940d4190700a080101e02901a451460036511403510f020303104134408181000740480c2e040c0805000090b0b556182c001c10f84652611910650601c001410440200000e50840c140b20b90442100700300144009a08130030b58a54904002041c1811700c10700080d04208040071004400e201c0e04180103030b5000084031549c1d40494802c40e1072601041c0b040078041000c604100294014000d514031800c0f8000060a0103c0e0282c060709182c019003a0b10f003d1188002020300300f1140c0d011103003505a5412205084c0c405080e520000f041d404100c1142d1a90f00128040301c000000f000154030402c0103010070b05040c1001702003003008000401940e41007010400159000005a80d00b00402c9003054103032045070b581441c0204114003010711254249440002c5a40e0182d01810521146101e4245008140c40c20028244114400c0a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 703426016 1250 703424766 703424807
    0x507020316112707090905090307150f02040305072909130605040509101802030c0105180405131202060702061315180c06020c180a140103081801 64
    0x36804030b01541515114680041c0c282440c641d40e0385220341c1e81c41440c54081180e102040180321349164000d10441c0141100d6204112078103182607180d1300c0788a90300e0003a01403021505900b05610f003661206c00783c0103050000310368440d80c03464890b0316444540309644400c40d8080201d80d101c40030104001c061904044010f00d07020240081061100d5050701c00c00058fc0e4800002c03d981d00d0720f00c40d032401480c0c80c00040c042c4140030034074002910f551981c80110b40405000c5034005840005a0440308442403c0c4143c84000c0300521094100980004581c418100014032020318034140b2000c03503940c00345e06003c64100746200103076900d04054840200592080c40002e83c407101409039808154460114800d81403d508115025201222030358140e5514000410301000751030300c01440148501e00150840b03140b280000307040f1b0074802c00404001d00c241c000080b034015642e484640c4408164402141958407400d2501042e00031904000070003402108003100d07580039a003506051000366106 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 703427266 1250 703426016 703426057
    0x260301090911031204050301060609080714011b060f1b0e011b08181215011e030f050f0f16051509120a030e04060b03040b040512071505070203 63
    0x32000401104809a451520a00c0440010f690602c403002e03210101d030840b10b841300c5c2030008043c00c503505030740483c1c02c0c400e8482081020000106a0408913140000c04151810000005070381c06880943c41030140882c1c18480760800c40140c1c0f1401102c9800702c2c0810949400e265203001c810320044080c2e02143c0408c54002c011f40c070a690340d500880012803541c030440c0b00340d510049140c001c0d4600c140c000c015203030100d20074201004203c1034042008020300b01d2215001104207224010301803950004604c0c406c608414000d03007803003401180c0c0040c88100c0031a845c201141c40e101c1c59031020040b405903211a180301440019805180010101710159980c07604d0304000710346a8442c008103000b68244040c1140ea074800450803006a010406080b40300142d190080c580304048201038851ba16101060040072444003c1e2030340280c2c4001d81140c10388031410802d240040c000366184544000144110801655008a041c00011040c007030003140c4540d5003d83c3c8034040d54110255411072400c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 703428516 1250 703427266 703427279
    0x80c010e06031b22031407030b0c090a050d060f050f090706030b130c0c0b0c030c030112020a0302030d180f051f03110d060e07110d0311091804260301 66
    0x145107005200d01036841c6041190360310780c1901d070303031022404c048251300c61020001d001044c2c0e01109004890005401303814115030714170414040180181c141d0031004100001035450307218205001d0500100000729412b4540344c19009810784200c0c01c0072441c10a0301180301c90b51a44035190055030058050b00055060000c02c50007400c0000360158060340032551a407805107180f0445401d144240e0f07074003046a035941070584030018050300340802d00b4010410080740800100c282e0781525540408a1008206400000d665480d41d40000c0c2d80350181400d070001d03454003c0c0740000c07015824204039001940d16541c04001c0502c1c1c2c414a038014941c0d0120308106880204c121703c0e082c0c024140001c0900c0010074000d401d400c00d070750314500703165200018002c08105440303566001e002e81c54102403100d9492161615071000c2025031040c1516803020f080510390303203070a513044082c2c0505002c140e6040c181c901e4480b21401d0701c094030441001240d80d075500782400f2030700724080003001c01d07546940d18044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 703429766 1250 703428516 703428541
    0x1c030908090a03060b19080d110f0f0303090706211e0501081b0919150e090706090f06080c09040902091f060e0a091d0a050106080c010e0603 62
    0x601191665001c1141400710760329400044040e40c05900005803c00c0710302c062010740b01004a00a010b011082c3c0100000400002d90311060411441c15520f220950000c203407410240303101d003800900409418a210b100008041d602c2081f5074401c403050f80ba912401980c95282ca043c04001e51400034483c03000f6a40c007134210b8840c1008152202200304140144d50b01211803e802c0320140c0e07081620501400c880d03803860402c80840482d807104003810185404105004c000d01000300054680311b02204810803010228000c22940222400515201e2241c5480f00c1c2c960140c20042001003002150302c280075a084000d03525252203180103512482c3c008082900002c0c469070740035448066440041c0c0300c503080781e40947c070a05c0c0d000b09135080708050441d452402da0030000070051040300303124403951040e210f881100c61842c00003587d07203000d4404102591810700c24103110b00c03c040d074640c10010158440c000301d448039030960303810304442c6004465814010080355841802400481e03803020580707 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 703431016 1250 703429766 703429781
    0x20c060c09011e0e01080f1302010809010f060e04051501060c0f0215040b0d0506100c030305180706090e1b09040510051203090a0806040503040e0408040330021c03 72
    0x5041810383c0c4098442c11220003c20300c420318000910f1040140394558010104607000b112009940306139141c03103504100c0641c103070740c000790400010001041c6d001d4000e41c4900203000c10100148495030f213074074400c3d40d8540c2c140c031708544070702c584040703001d08004280d40707203068406580e6180c05400094440521501c001c06c0140e0303120348900207141c49054001c001b40010400300c81d1040c1c81e2a141c44001d01100c00003030009024208d80200c01c1e6290754030600903481154141000615900c4102150034004c801181c440564400e4070782c0490000d400200d01c0048510804011030355580e0f804161501044171031042d840900c00b404041264606500015072040940b4904260107a4070000280f0015030307207140000c26000040c66861900300360740c5800c040d09014006050714100343e5221075480c81184038140b5a40d42d81c01c082000c000c842d00840d00259002010302d00010440310071040e40507000010303007204c1c071881a81d20881034008134203942c990410200c65200880c2a94007a400f400c0704 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 703432266 1250 703431016 703431019
    0x402091609090614030c040911060706020d0204060503041214190e090c180f090a0b01050c010c120515010801030605060f120c09100b03010302011b0b1810020c060c09 73
    0xc0110219201c800380c4650340042001413940c412400f4500d0525003080a000012030080d400c0c010144041180c842d40542030210555180f5038810302d500300f07a0002d0140300e240783c1c00301d03000080004a1507440009140103901071b40c00740140c3c80088909580700d02604c82c0000c80400d0034049404402002481011007212a0400110400c102000624a0754003164494410b110102c4c0ba072240e40791512846d41c0e4094180ea0601040b4070150000d2010a0010308140006031a080a080390341d20400946009102c0407009001c0c604182c1070203000050061040c40d02030b860103001a1558090007000d01c542c2e103068481c04800d900355280d180c042c1a006210f907400c00040c881201c01ca489034161400c0d207003071003005400088180c0d000c0000268015001a00c01031500c3d40c28085030400b84100c3e4112942420701c1882e004241911203203000b00c12138003800b80d6020074200000a900b180458085401000030ba0f850b02d1401c100c046c08034020303002b803d89240e101c0e00005003c07070360000040005c03050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 703433516 1250 703432266 703432277
    0xc1e1d190507021c0509062502060a030b04051501050703030e0712030c140f03180a09050405030705210a180306090804080d090b09011803081b0f0604020916 69
    0x32050444054850544609005070722249048020040e0944640790755071281c90182d00d000c1800d80000d041c0d01031b0b5075a000c1350500804070142c2c1e40e820450100380107a4040c4c1a1901c9505850002d030007001900042c40c095400c103800524000c4506102d04a0404161a194240007403610218018035070000280345a20603d08081148020090003100300d038401c0e41c6040d0303d981c00b40740c0701c82401640c50000000390b0161032443c1e9588004400d4812004900c50000c61350300038003001071403040031503000200e141e107030070180018450040700401c04c42c0e0044045070314101c651041e03080b80341c1c0040c0c6c0f03a900d0410300744068a07407070344a078260000308503088502c490226140d8803114101c600c45501111403200003d820400ca04d0288030f0300000360001d00b0324141c4203107403542da02c280d441030700e074500d040114504008110040d154641c1c406581c0210009849148078101c0c4c0503d0140c0b40400e0b80c83c2e100340309074075036289000910140b16076800340c898420340d200c80e0301c003200140c000c45601c0300727000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 703434766 1250 703433516 703433551
    0x604230a05060c18100807050f040f1212140423060a030507080c0405100305092121010f060302070312050a0603020108091b0f010e0d0c1e1d 62
    0x80c03080262500909202d10f10b903544180111004d04541d01100200b40103840110003218490303000b0551551008250829603920f00001060280510990b040b400600500250202d0410b1203000401741440c801c07284c1d000301c68450101036584061400c0880f030398080804c0180042082c0074080480d14509035010325095062000045803604030b11500c0c4000b0344c0d0750301040038196225200395049421585054502424a4007081e00c0408941a02080c11788940220380328400400280c1d500502446d01e1000054504000182c01e5026003042c991900c000d5803003004e40d549503a0340b281280c80b4000c42c10320f85840e1400940180d088080141c040c44007040c4087c28101c280c1c010381d482034410300e5000504905610015104203c058039052140d03001c03110807034900d103143c038030f18080d100119640750440c0c046c17000484801c803e80d9040c81d044810180715004100c0780c402980300f13441c140c1d174548040707204211a241203600c1c0352181c94074010a852954444007008004241c029002807403140d0a42c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 703436016 1250 703434766 703434773
    0x60903010e10140f07021002070311100903090906080c12030f0f0c120306100c02130f021b0102190311040e0903030a110a0f08100815180604230a 64
    0x500340c4504032010b59140c0c0f80c030000c0c40401e454420f9018100c403003042428204440d00070355610449102c00340442d40043d0301030900d4050903040d8481540c00c800c0b00c10407810b0325100c8010300070b80c01085002c9449000c010540c0480c80c0035220948080e0001064181007050800c4034421850020f642640410048103a0b8405440b0003031100784c414119480c0d880345469086440e00307d004145840750348050082c401180d540492620060706545403204044175240001a528024410300140c5a03186c07113a0b419100c03105070017601a04a8481c0c841820101083d820303801d0f40308544040806495110117503900d03e00a134007101c10403183d030242500302511a403003113000b004d0540f1807c10948c00803003008072070380c068000c85013420022402c20341020751000001d000402c80c407081c01e050180744400501441021a0244003d00ca0f103411201054003240e02600c101405844950a03c421260f181c80c82d824009400c6004d035a000001ba0201e09403020b45098651201c43d509a09020700241903012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 703437266 1250 703436016 703436023
    0xf070803090337081801090c0608070203030705070605250f03050c2b0612030c05011508032506020304030305010e18070b03040614040b01140a0e010e04140f06010513020c0606060903010e 82
    0x2150301c40c01c0504230050a15402411a91000306018210b510400400080c56405025103d4050348040b01007400c1d12409882590191048036105a41d8443d25500c0d4055030300c04a415020181c40e02c00b08419110100c00c9a420301c03e4003515100141010782c1480020020b000020700c42c0940364002035180d440e003460012511540e90141d0005001044030b43c14420700b03204240c01100c0300c2c02c9403840f19240c0b0100d030361640100d5a4941079514091040075505415025a000b0694031001c215640c1c40c0914020300104030a015074130411000c0400140d03041c8608007a548000f094800400c011450300084040c50f0b03100600c102e4201b0780710b885a118810411840f0340c0228410098500c456040a111840354994001c6644c4601d20404041007032150310b20341d01c1d054800a40d880344070f0740e4071070501040d06a00e003e0b4980484c490b00402c80c0007084041101030503600100c480e002001003120001d0260b003ea521003040641140000c036025140403001004116000340001c280009a00d40980c02d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 703438516 1250 703437266 703437281
    0x2120303040501020409180f0b06041104080a0b090f061609050d0c0501020606060708030402130204031b090b10170613060e04060b0d030906050f070803090337081801 73
    0x102d07a0340125044c002c8180a01940c040310780111007114000390180ca80001d002c541c2c0c60060841d0a4200109565494030f400c800240091803106a9a9036035800803180d035980604c806441d84c0c280c8034007045031503074007107220f039107003070000004054030740715900211603480c08080100c0511154002c0020703a911800c034150807e5004050047c003040c944030001e802c00100800c03c900c01e040c104000d81c001510b86055031340064041c0c0310f1943c000031503010a4004e2182e074002034541d008a00002176815800a000007c2e56120b400500c4030194040070b0068075500380e4001c070045082c40140c00d6158034001d40555000500502c000e0b07014004007280011209180c2100401030100820442440308078020031880132401e48288851a08503100100444840e001d183e040080001e07825914504080c15501c0107600480e2655503820321040d8641d407544032541160603000e80c13000511900c0d07000202c0c501c108808481d01204080101412210700030010300f4079100c415114910446103800f440b40e101d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 703439766 1250 703438516 703438523
    0x120512040303240609141201020c0f01060e0408161a01171207051f06091406040b0d0809100c0b0f040201080c0a050d02070809040507050310080a05030a0c0212030304 73
    0x80c0f400c040000b8800401c035400881d82120924480411100b40e00144090031165141c1054890000101c005031060500f80500c4c1010740c004600c03100c0b01040400c03e82141d2018400801c0300a946200f03210384400304903005814070f40b01344030407042d0541c480b60440303510b0b00c5020700700142c407621003440304800c00030381200e090b41404100312107420b40204038540c1d204240308651810f2091540d1003550340d107209540c00001050345024500210102c0e04007002615585d0b1090020b004014403009038400d0440b409071156007008603e10240c03d049211182d865000001586400070500c14003034000144031100d010481544860b40c082050180b0982c0030342e2040d40e414880e42001c0c0001814440b0242080c15940c2c420040000303510780040c00c90305030305652040540c0361502c0f410308807214040c01040d603070403505000800c0180d580c010000e610405900600d031054607280ca494a584000503500200a03902c200030188409015041c450400da2005004e07200d5603c40c101d005085030003c0c2c030200c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 703441016 1250 703439766 703439771
    0x30d0e0102030a180f03030e030706020d1a0612040809010c0501050903030603011b08010311040f1505010201180804030b13050d02030c0607110604032001110c07061407120512040303 80
    0x848001d038180104c0321440010031101280c20740d1911081c05110a0110003401e244c2c2c0d40e46494403e031010b0040d00c0f5600d80240d4110f40354440c1204082c05458890541d01d000e000c6003c0221442c640f03001944d400701d03011103440340150364a0751400c506a00460050341403041f5079000000140e000d014281c8074030000000b964031303070a044080c0742c2510b0b85040e00545040e107c08044031800e602c0088141125003120f0b08001d011550001714004204030b11f002040241000680309c203000240038988111002a80200162042c80000035411f050120b002045038800700700070404a002910b0181d00440c2242031212561025a00c0910b0100c00d8007110016070001b00b08040346010500c80380707a004d2101e0421001d03803001c912941d0f48400b802400141405400f0503c0c0c401010340c85009861400521b008021544a01414070460f4100301d092580e103118001d4013160040c843c140e00c11200942400c3e080c02c0440700d03a0f41015040500400d001006410f02007600e0a129400040d80100c0c0241c800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 703442266 1250 703441016 703441021
    0x30702030a32070b0a09021003050a0b09041a0f093406022a0d03030e010605280b120601210c0306090b0102010b10050a02070503060f01061e0210020309030d0e010203 73
    0x1040132030b134000c0c002200c0754602032554002da2615a0f00c48001407051400180c1e9544a03004040201122006181c00000480c10001041120701800a4035030a121041440381d0751a2002d404000c411195207015801402190070448140c000c1d8503101c55205da28881d40d040248070815041d100c40e0f010b200103a10041000d1400d00d061007040005032659403e2501e0700101c040070a03400c2903840001020503648440001c800750003948a10040c2c01c0041158110f0b0404810a464042c001c0010010000d0320301400258044010219480c1040c02c00b6000c0751540d401c80151103140c0c002401c0704d84046103001d24950001d49100301f0001c58215100007401c2030038030903064100d4400c01021419a0301d03041c400c1e24184d9540c2038000001d055071500390b0751419084412400c0202031b5006542510405d800c1c0280f11010559a9050343c0c243d98035006a035005a55803070f18420075440020258100d2024494404420b030011a80301c0d0041044038600103510302c0e50000c4901c5600c6180d040d941c003109 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 703443516 1250 703442266 703442273
    0x903080f070f0c0b0c1e091201061409070c0602030a090309080d210f05390a050d270203060a0c0e0f0a0302131a06030702030a3207 58
    0x11501d4000c0c105107010a501c0e018240050142800b0b820050034201c80314000909034103400c02120180800300e14240c4c00c3e05042c0055002c2d9421000e02e07644075075212100d01144500510442088458490011510a01d407200340311001402809038410000e00c0d480c910085902ea0000b140900294800007808901c141001000d030800c540103522140c00c6800781404080d407244280b200319107802e9a518001209a149000408004011114190414040040d41d150500c01c280b000a0319a04c0020000f407c0d0040d40280e420400b43c42140103424071920046a11820140c402044c1201c0009081c2c01c00e8140928484407510032942e084400d50801421424140701c03080d00300f0040b40081c003e20480e0880a0541d0240c400c10f140154124150216a951005400d600031034020300110403001c00c0a44040180100703a840704c000140d600305000040c1002001c03030b03200e90703019800f443c00c22001c901c0444040e5034122050900108803203003c581c00e0215568030850502296009940d10036526 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 703444766 1250 703443516 703443541
    0x3050601140604270b040c0201020403021305160c02042a0f080106020727060b04080c010504031212060f0b0c190c17070906030f0308151c110301090308 67
    0x414190040b20148810420409052410481d000001d01c4026507050004404001890040000781c0c1c03103400c00c40110003054040d80104107407802903c000d6030215041002c40305440e426141d0111b20140d1860450545101c0e03085d01101030302c010070104013800c0a840c240c0035124082141001a0003003c0f40d903020035003000000c08005014140310b4400d40c03515401949a80051292803009030548142d400300074000c0d01c2103812040c02080070424544c03506141c40090b0001c0c052a20140700706850501558059400c0c0c40c2100d80c040b105098010f02c92008552601c82d141c085081d141c1c03125008070b40700c40300b00d403840064130580c080103484650201d6450f2074130712065400c8540091101c59100400c022080400640300550b07116180040309041035807503c4030039841020a985001404020441c0000402d450b06010f07648003c0d80d03460790f0042024140400b0303016a444505500c1100c6c1d0200c1407a20000864011004c3c00350f440700346408a401e486147c03d00300c2c0000c0000040140340e14108 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 703446016 1250 703444766 703444799
    0x100812040603180c06110709050903130905090a030c020d06050f060a060804050d0507081c0207020a06020d0c120306120507090e0f07180605040920060c120702040209030703050601 79
    0x588000c1c24074503e44c4580302d20548a020f8401001908000f001e0702d1042040703407900520150b2000c001c945400b00003143c40b41c1141d40c55100c4405010790019030348081e0300031107005041d07100143c503148402d50341c10b44a848140c802242c01809425032140031440c4d42c41000d00c20b9078211580f40030743c50103404000e9403030b41e80d400c20024080c0c004203200101c0c0e07000031401d8000c40b05080c825503032405800d1901b11401204030000409184c58a81c0c3d0040c001c9030060600c0324425910800d40e15115642642c4900040701541d000480a241c500e0102e0000b8030004001d2040341400285030f902c40e10002482000400152255803201da41004400e01c5441101c112008072406401c07804e4083c0d81d0070361035070fa1a204200800c1403201c01c43c400d640941d4844001898020800c00c0551018507158010f101000d201400c00308003062000100c0c100001111034004000000e0418840880d03c284441d070403074070090b0707005070f03080c440d4110548040184030b000c0c6004500403c0191f2401c498260f03540e095 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 703447266 1250 703446016 703446041
    0x20f0f070e060406181d0d0c1e0b010b0903060705121612141801050c16020109050603040b0708011a0f070812190c1706120c030d05090f060a05090108100812040603 72
    0x21561042c200c1d40015840c1950b584100c2d02c0327100010100341e1503014540f0840c0038088000100000509a44c10402018029001c0e010b03210655a00351094415008254060f000c020100c00016880b00d8228004001c044072418081c50030580d1000c10b600700c0315506c107114403124688003442000c540c8284500d040045030402408140361050220109004083c1c10b90a6a5141000312045a002c0c4440300003411000d0485926441c041c100851500c9060b60a0070206d60300000118049440e07411031000601c5442000d4a445114003030100290703c141816180108103000d049031041da440380084c00b0350001d81c07201b803c00c03009000040803985615840c4051101114a01002d49011001140d00400c12100420582e80700d415103810806100d224a0703160280c0407000e40c03000c1c0c00001508100030195802e10340b9001c000180000c600c03450400b0000300f482800300c4105980310b0540141d1009651400300c220f00d0395107000914007111007451030854100414180503107549031198050310f80c007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 703448516 1250 703447266 703447273
    0x403060f020c19050f010c0c1e020f0d0501150803091e010917010b180106020c0603010f090c091e0303080f0f010b090303160b0106020f0f070e060406181d 68
    0xd0b07040300340c1d81e5100c90074004600b041d4a0500c0109110701845140748040c0020020f1140300c4040c50020010420103500716854600c04541d030036004902080594600c3d405403100003200000400c0000203074440c04211000c1d901d48180c1c019030806034400400400d5580700540c1c90300c2c000020066200d07040c5140042d60f401d00030140b9111780c0e020900308116198140ca02d0001564024102d0142004880c082d0b01304500480c01c004105070040000d048883c503074291411740c2d40790000c028a500c0207102e0f4085506007144c050040070300311740c02211711041a04100216035611844241d1007201c0c044420b03442401b860b010024141c1050a45e607005a03c80c02d41c1d03d032441d0a0003800038401060181c880c9103c80414060080d803030030005c81d41202c1c46000004000c406514018566610900981005002d4641d64080c034100000344207400c48194000f41c00780c81d080485107080d06600802455115845600000e00075024141d0f2084102c00400007040010020b0746079150810744600190300d0b83e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 703449766 1250 703448516 703448527
    0xc01060f08030306122e0b061218030703081f030b07121404031719021201051206060604030314040f06110606010e1005070602090604080d0f0305130f060603050d03020403060f02 78
    0x51085689000c50340351a1080e01c1920642c032070760001004000c118507004038000079809c0c0c00215404145200740100004075442545496680c0d441b03001d00301b130040102c0d001c070307001c00c6400d4410000400f00c002c804c5a040344d0075999403181c411900b400d84090300451003607041d842e00024a0701400c60880c90458250455040554008014220030350040c9880c81400e408150b14050319468080c5002c043e19056403511000400307401450400c0c0f00341481041d110405202450004c20410312a5100401e010b0a151441d1001d8034401c10044100d500c14008000100b010074022400501038811640d406801606101c0481d2a03c94003030a418140611841007030200d95880380503002c40c03021460500c5e00c5456924004000c1c0c0111500203038050710100e00030a1a40001490308030000c420b82c0c0b241d0069501725001e404441d410740d800c0440e261000c0b0f401e40403520244446900921074280040e001d41c2c1c83d16003c3c20510120300c50310009400040c1001401054090246222002d920452405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 703451016 1250 703449766 703449793
    0x609010b0109092a17011202090c0c010e1006140d0b1b040801090521070b06010c03210b0a08010e03040e0423031309051b0c01060f0803030612 63
    0x2940c042c0310b03600056481c0d1801c88494140d050012214404003c440d008507284c040f030203444203411020748580e21450100005030816800d83c5003082a4000d403842c0d40c162200e803100b030081d0340048000403496482c0c005000c019241004216003088254800040090130720615a00c1c0c0d49520088a00c10403615070010046021240c3c4e2541000d40c580c00f01c0c1e10b00d50104d03c071030034034000ca80c007408d1554608034151080c40341c00703d200300f5440045002100b81c54101c0360b4180031405894070180c540f20240c4001035865020300d80c41c0d444d0b98040e0410b800301c41640c4944540c049000d402181c00c581e100d0103801514282104544003500c641030090102d5800703c03a8040d920b01440c8180d0207003d94460100c2c09100c56a481841501411100c0304180390800b107901d652a48034100145441c90130840010b102617044c81143c0c0a0038003060b02044840815400f40d425030424076442d2529580c44500288001171429004000d0189001030b680782c0c40c0c45010816501e08075051076082d9001454a803100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 703452266 1250 703451016 703451027
    0x1031401200318032113030905040f1e0e0c01020f060a3207020c0616031d0a140f0612010b131503330b070f0f080a020609010b01 57
    0x910224210707140e160740c3c40c1002061481c0c103e074241600b501001a0b61045407001c03413507034483c60a8801104c5640d454100131032070110024007010300010381011060003245041d4101281c100d811802c080743c032200c8a48602c64150148921055040c1d0b03d16040483c810306101031084078100340003502e009182010200c0d21010002c01c0c500c5019500c010382800c2d4449100d040c0300390000f214144500070080010012400c0080d41d070315000d803103020250001c0c1c1c0340c40c40440310400b0400085200c50001035800f40d84901d0240c0324621000d103203c4040080f84c440460311030041c05800302c0484620f100109000b06440c0e980380440c014402044242c029182c0092001c0c1115902010546d58a034246400a00d02c0780940044800c5489142c2050b025581600b01a50961031400c40103020a40113030106118210130040842004002c4420804144040058204140664941c00d0680020740d60801c42140d803036002c5074040d60209544003e280c3c1044074a41c4035040340004c021030f1841e400068078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 703453516 1250 703452266 703452311
    0x4051311060f1b101d01060506040501050a08060d0813030303050a0504020307061407082a0a12031802042c03090f090a1b11100605060a03090f0c0e01031401 69
    0x8809031585180e294075404c1010209150b1460360030840f01084948148002c113004000181c290b0900a01140900e0284121012110141c45161810701c0c0b42c001580c030f45d03034003c0c55940e0001d0380c1c40102011441800040460071204600031302114158a009070807070b80042c00002c0350510340000c1000503100003981d401a140c45d414020002d1801c0b018070405d0744902240109079042c0401c841c0b03107415a190701401f03900022400001440b2030fa8540ba0354484050b40c0280042e000c01800400242c0030b5800441046400410700d150941d8075000f04003500c0b80c1e06403090244400350469080301c40d507841030207414040c0002451402d0200c0000540b0590b16140703440c80b600d40b0030080307120042542d0245901c4401c41c0703a103254141002c0c1c005400e8181c4010b10a20030700507007601103071040240c0320340020303208020011130400c90300c84c0040300140040b00e407c40f2055501c44281000c81c04015400340180000d6034400382c958110724000883c00080300481c3c02c541c0c1050369010200014011486 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 703454766 1250 703453516 703453537
    0xd050a061d0a020d0b06060f0d0204030c05041505040e030717040602070501090e010509130515150d210309051f0c08060d1412040806060a060e09190b04051311060f 72
    0xb1406c0d152000056500d10071181c03d00c0d1401c200140111514030305801500469000e485050300c1d141da40c10078481503a403120720040c0184c0c107046090100d450281c0c0300914103021002201c0c1802040c0c1c2d00c42c02c1012003c0c21466409002107006c01c4810b50402154002d003000b0310742074817661303d01030b285c030403111040c0507081c4201c000d400003c41540b203414203440301c0e41c1c104045440300b494540518000410075601c0b001000c00b030080400c443e0512120a245403503126030f811480e011503480c140c2c0072404154001d41058bc07540545000300303900b002010f0b500420000085503404203e211603044420304460030052244030f108005a40c0d517100c03c04041c840d0004800c68980c101143c1d0b01d8146040400d9000d00d900000c100890312a00014140d8400c3c83c064404204c00e07070b280c201c280c0d11000baa175a40f80d4059010300c0061204143c0300400c0c000c20303900d0b400128040d400c0320700050036100101c44450240e41114002814401804010481d409042c0d424900e0b210a040100207184a02080341 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 703456016 1250 703454766 703454783
    0x120c150306010e060a0315090e0d03020919030c080c030604120309031404060e01090e1012080706050c030717190911150316030204080d030b0d050a061d0a020d 70
    0x78110b074010380c1030740d02098004000c240d94281c5808080d005210342001c01040b01032200c408948241e075881020901886900102449591140110041d5100740103540d0860014001702031608a07000095000e07504c1061301100c104d04102030307580341503603055019110b40c1c00142072001080d2650030f510743c40600b81c6008105240c560805942200322103210703a2843c440000c0c00940d0070380c010042440c500003643c505282c1e65446600c2803082d0410740c0d2001016410a60030441000741c90307416022603126440450030301c0b14645400c41154021103029500c1c003000810411f900f6800044a01140c0c0901200e0125090407152a2404421000e400c082951f542c2c12403424040801c1c02541030210040c2524110300a0f00210017084d001528010b180f41c0044445891142c0680255816109000020031004c4d0003003030211b0151103040001e42d0030460000152000c14001d2114841c0540240400304078044a40080c0d075010115030300f00c160302d40264030002d0059071034120740c92a880c0c020151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 703457266 1250 703456016 703456021
    0x90602120a180b071106090106050f040615051e04030302241e07050408010216060c0203180d0f080d09030810030807260a020c01140702090f0414030c010b120c1503 72
    0x10b5903950008011710402c4c3c0311340820055100e00c1508440250f4a090301d407040c40e50000b4080c802615954010540020140c0716070b0040c1f03510613805400125603060980180700c1100364015060b03885504180c0050304507040e010b0000c061482c1d801c042c440300c0484415945803106071034000e42c01010428003030a8600740451a0203118009070383c050400c0c90021942d4200c01014032a240c0902034049503003500f0102490031090021041d00c0c960020400d180c0340000d8903d00300142c603d0103560480f58072450440e40d0b004a0351003000f9004014a100b0000f80107034150a001d000c82000400344170f012260003505000050b010400d940d416640000d048944064140c0300d900100e410703003144450280045629500303640e0008400e1842d440a890700070a139030400c01104268491080065085104000030551081c43c107200580c1c8103006840756569551409809400c0d50f102400b80011603469001a00381440c00804034183d01920b000180364401c420008500050018040340d6400d0070f01000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 703458516 1250 703457266 703457281
    0x140d02120601140d090240060308120a1503030f0306080d020a021201060e0903130905010f060f0320180f030d05030406140a06090f0c02072304090602120a180b 70
    0x100d074400f842c0a40d2041c11030341503040d41d11f400800704100b001c80b40414104a0b8160018512410707050740e8021051a10300703210200c0c101c540c04009450301070303519030354062441540c5d40b1078612400b4500c41d43c0e81c05510511440001c0a55045420141c02904240728044440b5000144e8100c943d40c10383c3c1050545400001603801480e403580a01d80d5a0092820024480404401403480714145100c140d00b607912400c0304003c0b5002400b1340300112001100174000d02c1e00500403010190314918000c1030311700d103404040b1600490030204200207080480d285c1d01060100c0c4420f02180c4c0c0942d400b018441e13145001956450b100ca03003210a1103000000324061140c00d0300001c11100b0448411209801c05600d49001410740344581d1410924001c400f41962485006001003084141e004000b43d1303082c40340900c1340d01050f0200c0368519000d110203a0031900e50740030b0b0235003032401144010380360f0b00c0081560400704d500a00707620406150401d5034451550010038552540c1c0c0200406107507645411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 703459766 1250 703458516 703458529
    0x3060f150e040606090303110c03060423100606020d0c08031b07050304030b0406050a1802010f0302040504060b04030209090d120527060403140403030c080307140d02120601140d0902 80
    0x181d020350020f04018012501c0d680000390072003103034441da441c1d86a04074940003c50f110400c00e803010b50f068110b0300100d804030b11030080c09400300c03030050580440c1c242d040c440d1034541140c102210b040c007500c80800f040040d40610030284201914200300401c140c1e40c0d910b50f607040c4801000c644d102260303e441200c542d1401d070280d601c426402012243d69540306d04013146241411078007156981d0502d40018280d001500a01701d0010200f0034460a500c403550041d07a0000c0f2032224001095401d200004150342c6500800c40288003941e0595a02c0e4194014000c81d040000c2078040241e1088070828205a4441103440e0551091440021140c0b11600c504401d0020500d54103c040c50005000d030b000100030515500540c881d03121a4203251460010011600403072001801182c6a580d0000124080300c000b580d1014840c54000c000150100100c1c83e540c111840c2050023550100301d00c400817240c207042e10340004003401c1a0010307402d50844101c541c81603031780d80728400e43c1b1420800215203406 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 703461016 1250 703459766 703459787
    0x50106050303070614062209021903321e01230907052d0a0803030c120702062e0504060b0d050c03090a1205070515061003060f15 57
    0x60940e60380d240c09041013809400c4000250480035013801c0411100d140c1405d007248800244001d40c0c407640a103803102002007842e00303420b13a004010144840e40380c1d039007c52464061407041c41414041010781c00c4188454404444801d45001b00d00d00301c02d92070034002041c00c40b500e1040d0070420380001c802000d80c09010080800c40c0c1503104950b2041e50220b00003500c0380304001240807140703880d41d0b80d02081102408010b01003d20030081800b01e6070b003003d40a807104015400f824850084d5981c21809240d54000c0310071007842c1d031b07020a402c01400815544a0b801150a100070a041d0070700c0315018a08007404008070260f4802c18030051a103510707a440f82002048004e200300a01c0307580b1000d811a80d0710412100206070720308000900c680002d0000c0c0ca000d042c0d00f5005141c1f40c501a03803804600c685003c0d4080510609118640014000b0000c0c212107640c48540040c2030304220f4144241c6102c56603c0d034003810300780030090003851015070100049a0a0810b0300b20300d0b9a90960543d08190070b03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 703462266 1250 703461016 703461019
    0x20d030e03120654070f0302071b090c12060b09060319110d200706020901091206060e13050a080f07140106030203071e060e130c03061a0406051605010605 68
    0x104290068984d180d800300c01481030450011400c3d081e40c0201d030150700d5800c44004003c0340721034400500305c501c04c3d0301a016151180280000c00e000203082a443c480c2640c0c040c0c039505440c0c4010b04034003036025070401c044046121041c00164241906114103010750768006015601c08400643e50f0540c1c442e0b00b81a85c80400003c02130064100e000c28a5607000305c00011040d8102243e4034a58052004007150380c2c1342c1e0116190030700c47d0fa5a541e030041e500240001c1c2c108400d040c170104d542e100d001e00d10b9491503c5080000390003440c100341e00003049001844042507803045110080810720100f00e40380d600703604c6440c00f80d0340e011951180402d40900f5001402032005240969450001540100103490080b42220412030b55035403004848c0d90401d4081c407540ba40d24404210305030140010b24460800144105000980005444100d81c500080f0600080e00c0c3c540c01c201d0b40c40449503a1540010000c846440e20b420000050710784c0c81407d01c0d003e01d4000255010060110039401280074000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 703463516 1250 703462266 703462339
    0xb06040b18071701080f060109230a0b09160c0605220c090e03090102100b010507020414180d05070f0c050d030206070807020304060e13110a020d030e031206 69
    0x5210030000c0c4400d2101d00b03401c1e5020f001d0000072801c2400000c102402209000c0140541e0b0308000062001d404500322506503040c1c54045502001e0689450500c00c511100000a00d030712080100320a102000e04240816180c4001e08030f0340c1a17100d2260226142c02c107d010540703441d00c8a07500100c070341c03400d15554080c00e80101c040412044440300c2c412141c03240b000384043c40c128900161684656240345000d680046402138080f940c9030010000301d02c05040c03150070304010b47c02141c10759140020380c88a41d9036190810828540700c01034400003130340380401046c0041c03920034094442d1007698409007807907280d00c200b0020005140343d190060003014120740c01014541c0340280d642c605c140c5030309000c100c1110000c0c0c0254800026202100c200740d4820507078a99103018041ca2010114070944140d881d04031443c41107024000502c0b90015640c003d110b40110410b00400f21020386000b0101d0760010403a01070050452003109810680031168242031201c403819015040700000700d8080340b0803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 703464766 1250 703463516 703463521
    0x305041401020a121506090303110f010f091a04020f220e070617040521090a0f050a06080f040b07180e0f070f0f03110f040807090e06040b06040b18 65
    0x1d80c400340312190204d07480c40030b205c00040280102c2418580b40079003000540300c9001080442e1140303031850300c1d50701d51009649154549202c010b083d0f8900c000300023010703601e178540c007000c011464420100c000114584000c03035051541c0015003001c02e110740e0500c03a000c400a0554891641400e4205038110282c08109070b03030340c100e940c42d01c0300070a07ca500045200802d0007880700748a6248544541d51140c09004502249030300904880c0e80050343c0c00514805208001060700ea110300071014144050075400145c1c40d002c02c114015400b03810003001c2007000f0b030500618003104509140c0240d440a01801240d860171004c44408819801c02120f0f1401c041d000118103c569800703a0080056070030042c201c0d42c802c50141c40740214241110001107410501004880c480c5d84010703c0441655481840c168268828068a0f0070641045600d82c11110081140e5212032050030900b2090340f000d440345150a4407144200c3d4001000280501d4a81e001c40c8841d94812114848081c0040140f24050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 703466016 1250 703464766 703464787
    0x91b0906040f03020315011203030c0306082a010906020a02060a0c020a030609020f060c0d0c0804050a080102030f1303050a080a1805060402120613030509040917070606060c0c06030504140102 84
    0x219250b2105074040c0c05254080c6c000221000d44080c181c6a00910407500d90205039022002015590519401c2554800d40400d9204c0e050021a05c240712800054041d104040c00c0b281100c0c81021102d8140f25818000f00451600072038031000607a01100d1007604e8400c0210142c54245e29040e000750f1004d00c81d5404000c11180b1791100740090300030f071a805114904042848002d100d0b2503104800c0e60f0140d40c4040c0c88620402080340724500c0341e6081d60401c1d0303550010500c800c0558001c0c004933500030040001d154448090300d41d011021001c0c4152404040e100a4014032410b14808c0810098400040303a1810303640156583c40e09459a03140d00c22020306081c0d4440006440403881a40c0300c4080060625000408901400140c040128008001e0303409a07403a6001e00c0031785402603101c003236210100d1003000d080c0c007501e9440c04540b5136031041031034100200c0e40f842e0400340501001e00c00038030100300e00c545c2d00710903a03050b4100041c00e619142803000b9030b520078103030401d8250700000702011403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 703467266 1250 703466016 703466039
    0xd0b030303070903050d0224070306050910080c27071803110103050604060513021809090a05060903030408040b030a0216030e040b09040f0f08160c0f080c091b090604 73
    0x84074010006d071001000003010490710f50000400d4500310700d0907200001498407485402680084440c05c0019115940d01c1c0030410b812400c0f01c11400e1280040410483c911090029440304202200c3d188605a80301e00906944019003030030003804e0f120000090300e01c6010b1043d40c101000c1ea58007044c542c6a0300d07c0c1208041e441d4007402800242080081404c50070140205000d50354000c0c11100039111408079903000b500a101c0c10180000180b0b000c658a885485d2070324000c603400c2010b00101134030303400c0c20341c545280948001c40c80e500400801c4040b43c0b032042139a098580407070032540e60340c485205000180c0a003010300b00004403a80190020150099080810b1000544d01030003451940410401c03a0441210060802c0345124406c0340040c07005407400f28060301c50040c1d141010200544060701402c0010111004800450b0502a9110880c0b0000017098803400400d1803400c00000301d000039101401e40c640300160015003641c544080c0007500c55429001d0049610b46030341d401d04445 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 703468516 1250 703467266 703467269
    0x1090c093213170309100605060712030e1002030f01090606021614150c0607020610180504030302070515041509021f020304081603061103041e020301060918030905041505060d0b0303030709 83
    0x51b83c61501c5000640703070401c1c000352060a5004150459408009803003900070341441d840d0f1031218041c4001c042c115180741e00c0a1401003240709031105103981422403c00c2214140d4000c0c82c103645c00004401c00d2144140710f02c40c25214201451903031030501d000490344c2041c80c0710080250300340200380e200c40c10750001900c51042c1950b9017100c80319221202c1d002480b000500822040081ca15000342c103107445074211580262117441d0042c5001016251503042c142c000c05074081c1f6030701c3e1500303000600140212518000c802c0403420070840c0b00660004440d101d200700c6554402c54564404d20140307000b0300c00d41c0d0080641005031250000c5070003800001311558002169603500d4460b0b441e41c0000d40205503440759611110b100190142c40e4054000d4044200b41281d040d0348845010407a40e405000c0c2266500d68080000300710b081a1801a1000e28190407641c0a207250089858100b11030b4200c40c0c0032114140e03440c5a9483c200e448040260006c02074a5415220010078460040c1c2d004c4900e00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 703469766 1250 703468516 703468543
    0x33304020a030c03151d1f08030403050111040f050907110304061110090c170c0406270b0f0103020c03071211070f0501020303060105090301090c093213170309 70
    0xc505482081c002c1c0001015008003411b0000c580c8501c0f0b138000280010725041992551405c000300b03200c110b4070030041410b0300319420ba908041010810440c1c00d0003000d10301100c8003050360a040c140010381080c41c83c584104e0703214602050200e0051400703949050001c0000d40c0a980d641c5882b4540039048180c1164405a940304200341c0c000301140f58410348007603c0c5c1c031000161049290070f184451520300c5c2031002056024000c5140d005a8a5100d1070004204058050034000041071052074100c01d4060501085414030b1041551996040c0c01002004001d003401a00d81c02c40d54551417850103040c600501100141550042140d00a41d41120f0780744141c044400042c5c5842c00007424841621032203000d0307072050000c220691b0103180600f074045006400055403d5035900c60140445c2e0304c0e4022991180d40d80c5200c03080c10103010f09000d0301342c01d0598032441d50305400d1072000880c10003044032003144458842a42000701d5000e560200c401000d80c0345881e070828840d5183c403440c0061156 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 703471016 1250 703469766 703469771
    0x3061305010b04050a091b0e120d020d0809012a030626061e07050d09051c0207050109050603180a051506040f0905100c1107060c0203070902033304020a030c03 70
    0x1074a01103070040106e035201e02a20720740c00031070480f815210110b119072441d41c04230080d109c0800c4500704000a03002e0800640c028484410400c8001c2c01180000d851001182d0400e0071501d4262b11141049603505526107500740b0781008100c04400a1585402c00c00001100803440c1880a0114a010601d00b10803000d46680343c481d00045511403500d00c565090303e506060016080f80e0149000d800c0791140c074200890404400c2c1d03a020700740401c49903182c1445000030003507401d1960421590f0091701080c200401c14604003000034415000040007242900b130405003082006106000f194000d580c000111030100d0f054041484071031400301e50090103a854440d0b40105910280500440306421401a004100d032400e07600303002d4038080d4003031814403181190190034003030208903081c02001c00d03030380d4104058400c8c030416003000015406440c80314014000e01644a000540c1d101d08016004920b05078841c2d9405404041512400741551040c40440d22220f41c0b60190050342c884141607808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 703472266 1250 703471016 703471019
    0x405030c01030b0d0f020d0606031a0a0c02151f0303051b070e010b0310080d110709060806060d060f020a0801080d021b040f0605030d05130909030c030503061305010b04050a 76
    0x110210340d4024149980104d481448a000c5605071141070f00b19030018040c501104403503140c000542c1d0745c951040b64451000c0b00009500150420495080914a04240070381012060001e5480c40f0b001c07203101554181c60085000401c2e608810040c4082e44d06041003129504d040280c100d0300403085121841d8075461144840d020b000c00e8007030660744143d0034908a81d08068146085030002045030000c0c4248030f10100d8000410840004660b8680c0d030f0700c13004070250000007410b0a0050703000c40529800d16109000d01d5101180c01070b03111200b0303110384084144500f0103402405040c010341c11624030004070550203545c000c0070181600c0c00f00048900c0c05405020480e5100c0c0c40ca0f8201181c80403400c405442444e05802c980c000060018003c1540c40d218400241002501c0510700301140d4002000003503401c806111000602c11a00200301152841d10042d280019440c001030400c40000000303002599080d125280080301e1040821070703581c40e405c08080f145c1c410300aa82c801d80781c1120 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 703473516 1250 703472266 703472269
    0xb040e0901020a1d040b1305061219241505040b1801030b0a020c0304080303040c0e010f060302070804090c020703110f0a09020306041d060402011e0507150e010e030405030c 76
    0x3c56007030340e03010354480a65840d50480201102c40e40c038185a03001e0341b12100e20700c5540c0d0f0b1160002d0a0210894000341d1400c0c0b180401050303045c1d2010b07400c040d07009114214640ca00541c6107540068001807174080300e02408804103004004078102400b26454001c0160a1840e0b54000030141c2d0025030f800c10058400d8804c10026506680c022440b1558a070010300005040d0303024540c02240210015040c2016180541c1c1580c004c0d4014910b0341c4c3c404010070060001c0298094000d001d442596035055040052540007044a4040e4005054001031681d0811407200112001010300c04000c00102c03007210320094032008140f02c192440d00c641d142401d028a054045250190401000c0f000c1080c80c15907004007a400c0104030a43c8160b544004ca00700d00a560028141214164090702141c941440054401c0c0c0c11110b440404202c40b03200c0e032041d00d40183c01c546001d608015001c48040600c0301039030151604c201036035915400d00c0c02e40a09100c0010141064503800ca003a500c403010202d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 703474766 1250 703473516 703473521
    0x307060914010c080f0f070209060607020a060311040f0b0d150b1c091707060c0201090b0601032409020a030605121509030421030f2d02070e010b040e0901 68
    0x1070310111030828035078882542c02462010b40c0c4511411030582032210075442c9007981d40010340c0e01c0341501c0c4001070440442c5026122194803010407a40e25060030010740200301c00e11624003c1a040c0340c2e0340c046140300800d00d00c09560041c401c04482102c010b4452030446425080410000a1035043c14a0140c8200440800c20300340e034545020f480c140f0403840d0789a90989010b1046a43e4070390303a407907440c0204034a5500210560001d941507559070f1194901a411204000444421640b6140c07200d0009920140059007245091801090383c903045a86201000c0c00e10b1200d070b116030b045220005a0883ca50080c02d000403071520104040c968580c1480b40e405801d0010b4201c1c0c5d089541802d640d440d01424880c0c00440300c10481e42420707140c01441c201e02c207130107204240c550f000b0241101016800701c1048020451890b2500c0394452019500c10300004c0d5103103600198030805c04400d0103a1081001d40010300152000b000a9603540307080000741c1c0e00a020380080f0001e1240021400303034050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 703476016 1250 703474766 703474769
    0x110417010b012a060216020a081515180106080a060e0603030403080a180326070c18111803060c1201031e050f01060603180506010b0304030e030a0b040203070609 71
    0x41e1070b4065501880210004035510600c183e1405160015185020424a102410454145082e051072482c0c01d801080b000134550303402100568000c00041e048603985075a15508404402c00361784006c0f00007400585444107280000811508400001a1180e030200d6aa8003940050508200c400d442e5411001d100c20121506605a40100020000503400c000180900c124170b140000341c120101c01058104d510540c4252020440d85040d02c0165080c0e056004006110009036841c0000d50360703401082e60110310400c0e908003088121045031700040d170010103510140844d059500c4501420107444800c0000400f8060f20500300060540c3c0c000400f1580804802e2a0307040b016840c40c0c5d113031110004005503081c103a6039584885800a941044681080784841001082083c2010401022141c120f016081c540203251403500216034041001810344010b03816850340d955407410269400c84403003030b5143c0c140c41100b08640c10300c40e90f44035280c0680d02c22000e40709803590711b000c00c880202d920f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 703477266 1250 703476016 703476019
    0x315011a13030b06040e0a210305130f080408010f06080106270c0c080d0e0f03041802030a091b030303061a03070c0f0c140924060d0f110417010b 64
    0x7400014804034400040c00c9a00080090000c903001080c2c13a4094101000220100d4200c100d48050380c6c441e680c144a0002c600314286030401c228a02030480030401c010641c00a45403085600000c014412680c04a40180114500900840104140070801400c0610841c4d4035940303086004500c40d00304447e030700e002c44400902800d51001101713140e00240316043da02e000780011802540001800103000d0106004010300010b40710171994046804c01d5415013402d400c5810400c418002154400740050507408007110050300c035510300d002003004283c003840140124604000c0c25450030703441c1d8002c409807480780c0d9082c001140da48003640050512001c41b0084060180005100a4840e10301c089003180074000550300b28400752909103110381c2ea500889920306601c40320030741504021811f940c00246d1340c121403991480401100c4804120003d44601c245400600d200101e00c0d0b6400c0641003186030742d010002d01d4000503042c01550701501c503c080340c200b032100002240106100300c0550b04030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 703478516 1250 703477266 703477297
    0xf1a070c05011107091107210816020c0303160c090501050109171e030a030b0102060907152003092b02010305130807050d02060c03010807061404050315011a 69
    0x5000040d6024585a84140f10500c01c021001849502d1801540da18094018019a07101c0c900c0c2400944420900d804042001c0c03840720700480c0c00d82c0044070741c0e0b000b01c0081e04080c43c90710183d07040b814911020b031100e44c98070020542c01c0c0d25070818110a101a8030500381c00e0105c1741d489500c0e10680740b09100d2140407810504080001400c4440d500600216440558044104800318411002803144000c80103500108070788c0489501407190210f080400d000900540c80d2048095a0718200b60040742c8106140c0c28041c24601c1c040c1c54601c056141a80b405000040c1340d600c496641d07040342418038130804590171205440174540e840701114010355441c460b101c1c59190010b40103048043e040d004218940e0b0904008152104003a060062158014012803e03007508000d2421401071700e400b0040c0400c000401c480d000008003c411107455050500d0000c81d102151903143c01594006c64040c00f0b081c1702c5192240448000c24161050846c911b4886200d0780750803800b500400711640551003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 703479766 1250 703478516 703478519
    0x110907080f1f091e06050f060d0b0301140a1e09020f191a071a0c0304060e070b0d02030619061407020a12050607020111180d06090b010f1a070c 63
    0x40d100d40c081d041d45401c10354000159654020780494031000a04680f1613890012604014140d000300030040404440c4d800340e00c20614009a0756200305080141480c4d40c60000603102e840070340207041d40000c1040051800d01e003101c81000030b480d00c401e14540d0341031541d25513103002030141f10f50340c0c80075000380800000b0744018080c092412000c2d850140b0200c94140c0c00590138100c030010504c1c0e141543d040390b40342c0662703190035089185c0e1042d02c18082c00000c0204003030600e01c402600e9101780c1201012440401001405003451030302d402000402c0400504c1603000c0b24070741c00460041a05451008813801d40003081c4900540900864000a29611078a030240013140041c0c000c1c00c1c0014264440180e0b201c049150f6030b4a00b650484590f0004400c0003448c0b6028441c055603c1c28440300c0914040c2041d031007100e1542d070003240300d100b81030300341c0d12805000b0541e202c02d0346c159124003554003950b102c000716040d51042d84180c07130541046081074444da20003842036401d00307903101c1104108203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 703481016 1250 703479766 703479781
    0x200d0f0c03090f080d1d011e0306091a01170132100201091e020d020d03020a0b071805061e0a050c0a0c1403060f070806010219110907080f 61
    0x400c1038040a0782045810080441c6030000c1d00c103104000c1891500420204144000151068900b41c4003261444141890803002c0d0f600050229900c01151703144440c5646134002c25001000d0542011710341c2c0d890020600d89a0340110820081e0140076200e0f0030a501e02c958848088201c02d00600c40f0200b440c0c0d010001020a02e500780c00611342030f044881e0807440c0f0002040094803849503500040c1c2d1102511030500081100004101c400d41c03081328492007003078010410054004200a00070030039003941c00309241c030034400755600580c004111182e81c200350f10000c20f161200c400c502c042d1406401c00150500e0701804655045503812880802c1c84080400410f003608244414014000c041284a03c5401c061000d40d4241d403180c0314002520f4102802040801e2900c803449000354000414041d480e281d04070b005a00400c5850601c40e9590303030310300407030520b11030000b0000f102034081f0f44401000311108038184860300a40c0c3d4025140d40e0082d04846101082e140c0305400d105960109211 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 703482266 1250 703481016 703481027
    0xb030109021b011a13091b03120504030c0b0708090603090a0203060603030c060402120708120a1b03081603060b0c060117010212040f030201090b0a0e070f08100b0301061203200d0f 79
    0x350611450000b00700c4400d4a81c0107140c007040440c403481c004c1071f0f00144100481c801c1c582806401c18a41541058115500c0c04401c0c0500e00680200c040b0100d41181040740c040200c4244d4200600826102d04010040d65076461028508a11074000c1e200007441504001090351611949500104032030b0700c0d60780900408860250600c01d045c01044000b01d8840710401080b9106030308202041d548031170051000703025090200c0407140b03001030140d0940219602c04889900500041003503080e283c0707488001e070020b0030941d0241204403004101c1c1c0359528808241039048885045012409043c459403a500300c2c031034100000110000e85000c140450504c00301c44285520a000000c2c0c242c1540d00c9070b008444003107590060041d15030100103200c0c1d005001d00c0004098140038008440d040181e41500c414515042080031035941c1581c0d00640d030300750010002085a4040c1600100c0d81d420010020400d0266003040180480c150804442d00000d888006180558800601d0086d13a03000710380 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 703483516 1250 703482266 703482289
    0x2012d0b0a050913030206090d171f080109060f020f0703081e0f06010e030d050a030b0a1503150e01061d0d020301060b030601020d0801080a1b0b030109021b011a 71
    0x204034a0700c12000c0745503100c01e603040b40101c0100009101040582c07074002e203801e80040205219820050f8007680d01a0052154500d940702451900c501d550f8030500340b010301460440381501c0d0b1440c034000203240c5206501454080703000c5d03a411300c428140d855441003030b486800440404110200304c480d0110740724007400307a0132000c1000181e2140701007100000e81401c041e90103000b03034094031042c081ea1790f0b007100c40000c20714015005071000039150803019050f1b0190807040800d054036405240300940e00d01e244800500300d4901e90707401820001d003008000345001841c002900c0141d200100d44200410412030484800303a8a21400c1c40b401d012500c00c0345803c1c0e203003507000012500700c40c3c0165820300444000d07010014103541c9902c3c2c008002031401a4009203d8207002441005221100f0040359000c801600200300450204012000d0000e10307000f0381c0000290340003c8004120b481e0b00380c00510601c402038800d01d03162013520403030500b241c5c071425402c540c442d003480340c090060406209610 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 703484766 1250 703483516 703483519
    0x80c2b020a0e010305240601080103060c021213050901170a11360610090b09120d0504060e0a150e060d0f1d01050105060703111c03020a02012d0b 64
    0x40741c07941c0b07001041c4000c0080c0c03c2150241c01031040c403010810b0301c1c202040c04000001c0b0104082c2000b03000606804011b00001d040c16490710540c120441c02003040f06030044443c2c034002e5581c81085000c60684400303008148c415408180005084410307108074000d032280c45005007035480c4041c2e49016500c5084000d0540003945420340c1222440034000b03010f070202c581400a0103100c0f00a94a01d1810001031142d442548004016a050f0381c3c40903101095507a0007110543d03401880c00041c1c6da40411681c00c1c00340344604038050304140d03440009402201c18030b4030354405280e8030604100c2100f075503010340c401d92280c26442d05043c910954669020910180940d480e1206280007001650b40e56a048100f49448030381800c1038031059100541c04903428002040340b03506000004045100d55840a01005039250240303c130342009000c902c02d840300d00b419a2140e0781c00c80c1e10181c00307900702034480000b6518003400c005407042e000d03801d00100b018400d400d114914000c240100141148410035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 703486016 1250 703484766 703484779
    0x30c070e07210f0f15050f0d05030a022415091f060e120703050c01050d02120114041505060d150f0f0e09010207030219050a120306080c2b02 62
    0x1a40c0c0c0d85a441446203880786420011400205007500e0781c0544041c010440440ca01d4046100c0400190a41800517a40c04440c07038447e03c24140009040040e421001802500000840700300c1c09400003030344d6100340d40100c2028185501c48482c0404c1c910201c445d103c945a500e8000e4100c1c3c81c2000d506a8801c19004010013290565105000040d00c65045100440d004c070302c0314805880c0c40381ea13000354803400c1d8004041c0241155909600e07040500301050511801140a04450b00c00b0303010340e14200405051503200703603035515201c485044095400d9004a1900401008042210401d80e05403003003c0c11452526602c0150314000b8032003a42c0d044140d0b0b96044000c100c603102111104010706c0340b50280d00c0304504080d140b05e0547c40240a046103a071040101d000001e8010078441c0c1296200e0103c0c1c01c010f803003410500c1c2005140b82c0000c041d001030030200b00c40c00350103070b1054040d0740c410001c03903078020042c005000ca00d012120320700c200c910f00c503000d0310740b092025100f40422500c050981c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 703487266 1250 703486016 703486037
    0x80609070c060e01022d040902071406160e0d0209011a04030c120201030b03033a050412020606150412050f030304060e19020d02150c030a020709050108030c070e07 72
    0x28078007180d03600f821049880c2d400041e9138541044021400c1400708003222524000b10490f0000100d92040d4460703079070b040d60042400780074400610103c141030310403002644d1440c40d1460384c050081c40000303090000301c6d8102003241c00d42c1c00d03d0400c021040f40e010f0981d040d41c0e42045240410408011504019150100800f000103000000307024002c00340e20303d1180c40d104c0c0510000d8183c1303001000c25402544103202e803440000205400c000c41590460300500c1c283c8404981015400b600d030403400d0301d281848288020440c845001c10004010740c2e0981d50b20b40c0b10b8100308121100c9500b4040d1420300d0901c03090000001804190190700d1264049800c0d07840c4007002c0d44d0460b0001c45081c0ca005603074601d80c00c0c40f40c03c14451481d440ca54070420740444202d075400140e10012018001e4080c15851207512003d40d480342c00c842c010302d5800c00b142d0710b40c860f54100a6480c43e41d4044d01e85214105000000d000c04000250f410101250010b0502a818000015012840108010b081196017047c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 703488516 1250 703487266 703487273
    0x161e030905010f0906050105030705270604020d180303050a0b1e0f030a03090f060e10110a05190203070f050105121b07081b0c15070614010b0319020a080609070c 71
    0x4c1c501041e0322411011585600d08002c02d4286001640303d68000c19081000404a10000d41d0703085038802e82039001140740d00c801c00400e00074003a00310090002072602100f50140380d03041c0f404010181c8296400c1c080741c0d40c0d03010b10b0001e56240c0760145401503024884500d84589150000100138070180c080d44e060b19444000031710b0841c50003001d03000300c0c4500c0028099005024000307006880e42d41070243d403002070300c070100b5010f50b10400324104001000007000d410403003c1c402070000a400408030785070086aa418003c1c00900c01d00124171034481c1304400240180941c0c481d00480e0016150181402d040c00c86810113888000c0010300011b11103080032407612035400250800d01e008009050300c1d0302c262038403003904404049100b81c0302d50006404c4040c82d0b844c6544810240d040c441400e84420309494a003014100b0b00d82c08466000316400080340e410084005148a80c2055414044411081c0c0c0700c0c0c0f00f280700f544241c03000114200001001410300f10652a0044805d18008420348001c0d107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 703489766 1250 703488516 703488521
    0x6031e060e0a0b1f0e120c011b022403071814150d1404020a1403120a120504140d0801030b06040c050405120a030807050c100c02010902100503161e030905010f 70
    0x1501a000301780300c000115600d00b024a1043c034644c03c03600061180e1495500040c08101080d02000803200c054aa941308546800340c04c400700700b84004c09010f407500f0003111030b1a980c201306c030014001650424122010000100b406007103d0382e0040620840400006100b10b0380d800004400c0b00741000c00ca4811401c0c01403280143c0d03075131409040c400600b000d01c104517403501c4590000342e4038900100d41e103015650200b40d25148410000c4d000f80d4409210800350707100448055448a0945440108400e000015000e080003440d80b1060311085403802c2d00c29030300000c080c08042d140c05e1070f900004e0301c03c0c20264009002c0706a2801d080b41401c0c0c1e54400205c0c010307055058131400c4d420066480c802c240e00100389a4000c155814014104041180303810740e50554100341c0b482d401d4540182c901701c14000e50107042442c1e000780c90561000c00c90000a4500e07070050712801100703090182c0e0040128400d2510341c12240f941d14003d4100402101d08502030004c450064030155602e8554100407459807 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 703491016 1250 703489766 703489819
    0x50616020d0501090c05040209060306010804230c030105012709080403020904060b030c040e3316022509410108010504050703120908030406031e060e0a0b 68
    0x400c0041140541450b0900e980300090344607e0181d030051010103266618003043c1d991207842842d1142040c1c4c0c4504010004204074012500c0b008280c0000001400020543c0d440d5540c00360300038000ca0b42e81c2d00301d506400030050160907040d0043e5103500a03590107900034601650040c44441c2c113145d103a07000151040400d4070100c03009543c4280743d0102d418203114210028004540400105000c02009500e4400303240c1d800b0b203050101001c420a6041c2c00120b90000084010300e4411403400000101e80040c845042c2d5015218052101184480d0401d0070f0b5800110b03640800442480c1600b41c80241c02a407524049007203a01400d1884404010408516100c0700079412014440c034000c40e00241c0c0d0b042e00700c400c1a034100401c000200b000058010222a4402c018442030039030103100b180e8040c05504445402e00000800180540d4141c0280061201c2c0000340200d542902c88810219a40d51080d242e4040a20000404080d125400b0380321946018242800c1c0200c000c0e109110032401c4e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 703492266 1250 703491016 703491023
    0xa170f070e0103111503060d02060403050102070803060307080a02130509031c020a090603020915030403020a080a0c2307060509060405040216050d1103090607060b0910170a0b01050616020d 83
    0x601d0040003408411000f02103158402d80c0c0c0b40c03181c0e504150030710030750b48001490503004156901c0910f0854507071f001160f0045030070900840d11003401e0b15102d03c5603030007600d00d54400d20521001003400400820b01c13010482c0c0c020140c0202d00318071851800075250041241c4401e000510201c2e0a02c0a542c80034408800a41c0005a07109080c12000d0040350054000400b018030510921030320340c07215103505401a200704110340d00c981d00d61030202d00d0160111340081115401040c40c3c80d01c2500006003013400d41c46009121495680315801100d00300402d420b01042e54808070f010424103009000a01c9100c4020b840f0529064403500400e003a40c0c441196603422100c41301000e07080c084240440007030722004c0d00d48071010301c1400107415921700412003402e106a200141c0c034410404c0691040c4242a40a481e2107150714040c2542034603c451846088d1b0703a001301075603000b054540030404144c01a400300510109908000c00e000e666000031804510800302200301e0405aa00d19840303400c01c910 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 703493516 1250 703492266 703492289
    0x21040e07020f10110403080903030c0a1b0b09010c02090a0615080405011b051207091815060e0604120503040803190e0418060207020a0e0a020a18050a170f07 69
    0x3241c2d002d003890441c511103000ca003185090140030450520034129000c0300d41101c2000d89620310741c000070742548110905002d0b540f003001000010003100205c1c500074a2854822601110b0799002d40c561184614804640081c100c0303000e4000500e0482003054000c4c501180020703000f5140c0c6540345914064401c04000714680034200010800d007405012404081c400c40c200e408041098041c0240c00790354940d1180a1300e850010320424401c00010700100802c0304190301d045d425080300001071030f40c420b901c4291200440d012640d40e0080e02042d03413060028182034501890511602c81100700706000716001d000402001030103242c2000585100c0140030780203c804502d0a1010f404800e400c844980100c0c180010383c0601c2404160b00300d00c081c0c00401c090307681c0d0010320009007401c3d0682c05c2020035001c29810700145201c42c0d40a0014a0059107500f000002c50003001d0034015150b21556034400c904120602160b9202000004030348407a00c00c40342c0daa6192042241040500c0d0030480c05010b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 703494766 1250 703493516 703493533
    0x1809060b0711030a0c0509090c030303100503060a050c030a1d01020c1509061603050c1303200108060a350a020f041509021303140303060a0e010821040e0702 69
    0x2c086410840250012801405225540c2d940c03500e10002c41c0c403401c0e100311082e80004a1942d001d01040f070440c40010181c0380d0740d25000c0340c0c62100704200d00a141c003901c00c2030b000401000d030910981c1c1c0285540900c807429a1780d0b980740d0340302921110700190511905800359440d0b050090010700019003043c0d0260461700782c0c500c0840c5112000a062540681c40841030000b20f20341c482d0009121402c07450085841e42d40e94020013010b100e840281940303d00d0201002041c401c008400c805400500c0340340072204400c80d0011076841b502038501c1d69114070560742c2004407904070302c646440c1e44010030401e2442d03424564942c40031100c0e00c60002213600300070500d50440c9000489406032601c100d40410011898032801008030180c1d000d21204141d00252a14022042c00311a2004641c010401c0c0e80051212807103d4503a04247d924500413940e03000b000c1050384584040b6810380703581d00002c02d500030520740c4800c5513a031100e807443d407800e20400c40800d91000641d02c441c4201e010360010000705 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 703496016 1250 703494766 703494773
    0x102210423090c070f0201030b180a060e10050a1401141204030806060f0910180801020d051602061501170403020c0112180b09010f14040302010e0703080a1809060b07 73
    0x400b00185041c0212204004010000b0b00c6180040405034080c40c000031020680404202100240b10300301420f00304178410404400a20340101051302c03e100c4840005440d6444880300840e241e000f40742e844000c0b108244451505003681003100b000501d82025101c00681000d02c0c3c41e4480c10303c18240200d403104100500d41c0200246400801c11354049180c038000191240c0310b03018180910703100341c0f107015125540d81c1c480c0380b000311103a040c040460711055640043d07038000d40c001003542801500380800200113002c0c0480030301741d95190340c01070301080d030b06d100d05a001c181d15600322a0501004034801c9180c5803440216501c514130a400404910502d400050724807020390700e20b05082400e014420b001405031341003140d4410341c8046059803584421081d00d002d44000842c04140c145031460800c0c29203030710714030940200c0c02500200038052400d180303d030b2101c8090001030003442040042d107007468407034200b0003c0b80b030000d10b8041820b0f444103040310580c2c1082d804202e0074040030a102060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 703497266 1250 703496016 703496029
    0x2191a040e130f02060c012426030f03090a06020f04062003090609030109060f09030906030c08010509040303091a01061b0b27010606020304091a0102210423 69
    0xc000d400711803100103060b070754405940d03400108000b8028800802c1103c03200c0001d402100361640e03540050b003280a8407054941c01901e440c481d2021892040e240d0603012904105040a8902c0d08000385207080b00003a562091684050416003051082000030f00100d21144050300140c210050042d50721031420000070309103010300030381e0502000503170010345403610000300300d980403407060701e40e2511000140c00190042000800107031640c0c0c2408a980e510b040c4c1035001007000c0b071094441a00258a03004210100e0350301c51004008503100c40c006100340d15142c140300b60301920901e0049420341d616521052548240346486146c01803440050080f00d42120260b042d44007000c40c480403200c12519005039050001d008001007601c48101c106200d41e0b000704142403807208074001d12215a98800084d6030b0b074020300c16800418601248601d00400c035501d19502c00105a00a00c980d4100c4501c00d4105c0810021a0f0310007041000000761008002c1009c03d48105480b642010124000d030a0089 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 703498516 1250 703497266 703497271
    0x111030a0c1502091305060f06030405070f0b0309070302010e060d0924020741030a0206060a15110f1605030c040506060a0c060b0603150102010c02160302191a040e 72
    0x8181d0040c803566204d034031200c00c40c99007a5000c84000c05c041d01d1b584042403544402011054000318000b0030031003070010002d01b01045590203080c0d1414560f0b14810161140415110754525420014040002d9842614031003e8440c008000324640300000488504035440c02c90102d03400200c0ba01084200441c2d06001441c140303841005524121280c0d4607101303401e0148a41c400f854051540800c840701040340220340c001c08900540902240341d86c80540c0d40c2d009400510018450000040c1103814400d008030202c8000d1054400b502102102c1030790602c5004d8100c00d85445400d0748030110314010810010100f000c0704540240c20b0400c1c00713040c246529060b440b0301880c204801e102044d260740040f6028244d80c1d25081c900740d0883e00e4508050035043c81003541c01200442401010301c040d8107601d0000c4001d800030480000016030507600c3c0c08103030203004d14030f03d40f05074200b002d42000c0300415103141840323400b507442d5600c41401085003103d00442400c90507020400340804094450303100d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 703499766 1250 703498516 703498553
    0x203010b030d0c0311030702030703051b0604120303020c011b110c040504031b150f050a0f11040605070302030d05090705010f02070b16050a050604060506040b09160302090111030a0c 80
    0x242c1400c0b905005403208503061401010814145001440d4400c10700c169803103e64000c09513100c4907070300e0800076610300101804c040c80620345d0342e040349245440c200310b40c02c03100364104d5a0240000c94405034000c0d008900512101c0d522040d0100c244401200c5ea4140c00780c4544030340741d00e840d80450040c40c1002c0b40b00007500943c43d000500000c41c2e04082e4540049030620031042d140d00742c82c98290802c0c005801043c4c810b0b814001c0d040321030746445d08820710034552050204004144c06008405540c40180c0490003008204428041103100d0001440d849000f030045a141400d5042548201c0310b017110160001e4000071403c0c8015a8000742c60004a035103413004000c110b044c200c0030b5602d40b14107107980038481c010340c2c4181c08200342800244a100e400005860403841d050424001400c0d044980e00d00c074a01e000c103d18034924009010030300a020240c188450b003044138500340c009500c45810303541400034000c07003960036400c208001c0c00203224036624200e0080e000d2601d5041c50f5070280038503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 703501016 1250 703499766 703499773
    0x13030b0115030b03070509070c050303040503520503030c09190608070c030c0602031501090906030f08031f140423060409080d09050304150c0b010b03070e0603070c0203010b03 77
    0x14034042d0313000608034050382e00842d0415041d80707030400103481540c640f4100070302a0101100f040140318012001c0c02e03449621551502d02c1c0d50079403002c0d05079502050f00303091151440e0905030303111101805805010b6800c084d540140b411181d1159880c7da0012180024400d41c00034002100b03042030751444030700d90790308404501080c3c2408030290404070020005020040d09803203080070306100d148004400350b0000e00441d901d040480a203100c0601d2171b0b083c503022900b4810000b800030028412007003125003101c00b441c2191000c0c0e85613040d0394405842a0119a8500210b1101c80240c00303a0303c0c010800c56003030403141c01c003007020f01054500c1100c0c07454940380d0128030380420340d03c104402580700c142140c000444032940c0c60204240d0107124145a031462411480d0406c2207000401403003625104003030601c4032040d030307142203800c2010780ba00106070440c0140104410801138001d07503000042070a00d0300743c10700780a003c2082900200d0306500010780d0703e241602035040030301c589400998140c001d03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 703502266 1250 703501016 703501031
    0x922061e150c060207060c08010e011805250f2a0618050f07030201090e010b0a0f024b1c2303010e0c0313020f0613030b011503 56
    0x416100c520030312070840310748180800080e00911503050a4200d50703002d0021501c60409090800092802d00c503c0d0000c00c000c079001081142c403800c00141210000c2103a281341e00c001110100181401401c480c08081caa96010140300318007000c04a44e844060341e41e445150b51000e002007490024407a02c54017416086010055041540071640d40190400008541c010b108010303800c4610b01c242024249000308203400f5a1a04081280d80481e4000d80c0c440d5001c588a603c154505c0c5002e1141d041410420032044900a0040710f61144400d050f0040c6d9014008500c1c48490f203000c000a4248800d9810710900703525a410a4098080040002007201c0340720040c8840360760780c00104d12066101905012445207510a0038034000c030bd000c2254408440310340300c10b100d000380c0081c0103a20001540100280201c5c5014044e244a40e5455941056000c001d07002d1110280e0b090f22469000315082224041080c101044000258882c86882081d50b1400c0c6210b100d200500044408044c100200e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 703503516 1250 703502266 703502309
    0xe03071a040501050a050909090601062a1704081209041103060112020d02040305030c010912111f06080d020a05060a0605150f070f081206270903092206 67
    0xd031400d582d400e0820079600e14442000303558500aa4011035448030044041040608000c40d445040319000d4030f074118000701c02003504444090403041d00011900998000c408a096261015100029007074590f19254490110605020b2800a1100490350004440c02e090410748141d032561041d00c040c007415400e00d400000e1038076207110968008240c0200b5102504035956044070b0003142e001c421203596000251b80d45001e00b6a505040d030303c0180712042d0101c0e0902580c10900d020190a01605036050a24100c2510030480303405680c0b12031340d031040800d01035010010303c44a4002c51f0010700305803420780350842c50100000d2008202c00c0c2004002c0000f81c56240495017070403074411119484003036004609100d401100401360900480074406005e0004110040c0720041450b10b4600c0b0640c0c2d00020311190309400d05a880e1407251042000d1500e0080c00c007000d1b0071481c42400d591030329440c480007908809001e086215a8aa8500580c0c1504824860312006002407189000214415007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 703504766 1250 703503516 703503569
    0x6140309100f060510020618150c0a030f0504080316031109040e12030f0f070503010b1902010e1002040608010f050f0904030e0a140108090a0804140a0305010207030e0307 75
    0xa030050020750310b500020800406a4210030f01411018000e803266038050800290303184001d42d04007041e1501c1c4059402e503850086500c0b1302c4c8510302c04001036252121a411141d41d4440c0519008060ba95142d02036084100d00405024a0142031225105e04000b80762499652a51604900303151401e940481d0015101058884280c800c860000d00050540d94242c10b24001000d101400700d400400c11941c40e0110700d0007409100440a485e0140d52150010780e103d02c0280182e02c2d0400081c400d00c11040d05000186005440f03e100120f203521881160301d24000d2081c0402c00d00c243c000c602403080d6640142220f0040c9002c2d111118030a2402f00800d5889174148003050060325001c00040a042c01100980255500a0b04104010b9075130000c8048101e490240d581c00034140e900030480415002540c6861140c101d1613003403509240041d00c00c9070301030456042d0b804c07510004001020440a20140138018002e03100c02c25810411310816007001d915402030240c540c603440c0344980601148 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 703506016 1250 703504766 703504783
    0x1214070806070c140706261e09010e0607200606060a0503070219050703060b0316050609180f100e01031709010c021c0302012702041802120706140309 66
    0xb82801190f2003801d0030400c0e141212400d8056003031040a5000035419480401d8030900703010302d0001b4202c1c0c100c258071035955210a0b90118000d82c0200e0b01902c900301103020007500001d10f1000050603080840445040400440703ca00101300c10100481c80c40c218600f04580d10020318014103400d1500d880002c69502803484800108a404400904994000c1211150810308424000d048050358036101f583c1e49818001140c91604000c8020f40c14203000809090301000d4000940c03210707040c8800d111082d0017445107183d21400b402007184894241860150003800c1a940184851902c500200c10707071403465128140740c403880380041010480d02c0100c400c1441050303c0c420359900302c160048411141c041c4010354060b00001035030007507a8050304490400c178440e40007482980807a0003111001c4500c04180c00c01000e006c00c5a00042c60a54400d10391011022031040e00d4a0098000c6050100891703c070100a0f030000c0300601103903030840c6040c040581c0009405145141190301942c403074024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 703507266 1250 703506016 703506031
    0x1209020604030b070302070c080a1a0601080a15231903031407030e1804060c0504141302041a03011a0906040303030515060315150c06010e0a0b0a1214070806 69
    0x1500d0104c2c00c203511030380440302a543c001c50400038160312414041d494618001046071500100c0b880031608000c00000c140c441c0d40161a1702006642c0c198440c005008140c118000c0020750300c1c8041030034160365080488029a000381103420304060f40c180211806000005500500a4031301000004d81c800f541d80e41e02c3e201080074545500c41864250303400009a09002d6100c601611091500e01030000444d2003580207000520a5845e0354078181c410f80700300e001e50301007401e0480c1c4031222401c116000d22260400400010703c0e0a56488811601d0b10000d0518000400700000400501038410112501920041101072030030a0340000696144560f01c4014181500c400006450f40f40080b4002404003002c1e0150341e1f0fa24000700307200040d032010000c882c0300740c107815890740c607c00d1702d14103451038042c0303c03c0240340a03420728102c2d00d016200103100c2175000342c90300c18606491302c48231105c2c4010207040d43c5600400314903103840d00c021704154182c124180e2020404200c035000009455400100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 703508516 1250 703507266 703507283
    0x70b040b03040816061e140105090117031b0c01080109060b03160507120305010611150103060e0a051009123e0105010f061115010510030624120902060403 68
    0x9103404c91400e190503040207010145002d040300140d00c1800c0301d9504500c0c1d00e0b40f0030400101000c201100a07902030265503000a6488010302c030403214040900c201094800c06c890030300c1d82d1003944080a0ba0764214058064001070701400300307542c01c200301c0d81c050b11603032106000c0d5500b0120300c400701c0d0100030320898013411038803850500c1c14024030407140000d801400b4031072022421180a405004c0038850000014070700c484034001a1400706c0c0b9000741081421034221070ba4a5a1201000341102c201c41d1b1b507143c01811781c04c00002c0e40c100a42c03440c09120a034082072034040750500e580c0c00604cc0c40080180042d0b01b80e42d81850785024461002041820720b41c01c003d444c2e050079008600c5075901c1030a09581b8100001c25401c5c1e00103180e1044071407030350381d40445402c010015174130359811413050024014030707034014801303480c2c100c1d0117400002c410f150010f01d442e51403c100314a130b0b002020b0380c0c0ca603c580c490b10100050344072880c185d1456000d602070140e01403941c0885d54920451001500024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 703509766 1250 703508516 703508527
    0x40b0a051b0d0914010201180f030207150201050a060605070503070b0901062102090a09052113060f08070f120b0d0204110c25050d020120030705070b040b030408 71
    0x3841940140c0c804624411251640e085140141c280190f500400c140c044190400c0c81c92980705010700c50b504513600149007014031013691801c024203c4e0f01c40840c00e502800f040852000c1c09103010050410171a400495a41458001c02c000c840060300000100f14080004c03401241c13000040f1294203a01540360b40c11a40d030805054014425600680c409421540c04c40751000f60302c040186c000c0b402180c00300103540f544001c50044901f80c540043c2960080a03504d000595801e4200c0105281940c00f070386040d0a6440801c440310040e006500404c03880e00e00c06150a600144040d802031490902d001003000c40c2e840a40390490b00b0b00c0804020b5100d2041c00c0691f210a00520325055014200b40582103081113902da10780c104202024261291694201040300e51b24110600020326819100001d800c00c0e041c0700001c800b0340d030164144070640c6d001885d0115146013043e48104940c005d15100e49861a00c5800c03c0c0c1150300c105d0701c0e43c505001c14414a80c00c07034213390300280d1105145030f881 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 703511016 1250 703509766 703509787
    0x8160c05150702011b110d0c08100207030e01020a0803010b0a020309060a230906120411030a0c17060103080d0b030f010f050a0f0c09030b151906020f03040b0a05 71
    0x95950006a00500c000414190284410000c1c0908920036210340034003003140b0340021080c1c0382485c40a84108030481031590241051500038601d03d01440301012000e80721032aa501e4003040400c408680750340001c040d414140e2050b00284542c40074400b900740480f041d224024180010b00515807041e030300058050016000700300f02c903820b00c0094041d503200c0352090009085901c840b4940d68183c400881031070442d450f694111550710f01d0080c4036600740f41518412a2104500402c1100c559031815188940d540c0c08200040c841407080100200250400074005420010f41002d9502544900018400100c0c1c000c2918a0800f5000001880141e01000a803070000304c0c080d005165441d018030034090350499003100e84079512805003401541c62803518081121020040a0009040d2810600009180c12040c03500b0000001071a4110385503140015a418500040b0614405a600c02008010f8050003640050303d05034018506091034030b0004c40d114411401c000080040001e118480c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 703512266 1250 703511016 703511033
    0x30a03450b03040b0412030e070803030702061609140a090e060117030a2304031a090601150206272a10020604030e0612091b0906060a0c0f0210050d050a090816 70
    0x100b048038001c86104962341e0000584a9005544dc04012f010b41000a41c088c842c000c0416080011681c40180d01e51800820010201080045580c0500c80c40340c00543c0d4802406032850040481025141951411a07a00a031800118001d00c241e0002d002c149200e581100c0302043e82c42130019804082c6440300050b415174811504018991400d440c168070310000c0c60703044940305203880e00c01c941003039072103200451001c1c45500b002c00050f40038a0005801a1140302802400301c003280b025002e80d001d5481a50a000004940013205603120203524400541c0700b0606100303040550f5101d0840108040094499070020005828000c180b11442d0864990500b1105a807600d59407015050810010035901d0b07031504989021110440d881d409003034580900154002c40006240314a003038003582094480c40719590702910413681401c00d81c030150711000c6000c0031000761a99855601c1200c04042c0080350006001c00c59540d1500b290240082d0640b0200d84100e104003400409881080c0341003c074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 703513516 1250 703512266 703512281
    0x90501060b030c03090106050d080a0e1207090f0f15061b081b0d1d120307020307090518030a05041221120c020309030a03450b03040b041203 62
    0x2400c0d81d0010421000810110185004024460080c8915a82e400c1001000300416001130100e020070004449914090340c1c51007030341c0c10042d0620b001d50211a80c003a00f003d15a41c48000c034662142c5103000b24800740d100d00c10341030503111b40800c05000c4292a0381840c43d0240203440600c13001840c409800a6014a907215a41e4440c00d050354034075803407408507030b040010008550b0a20600f1641070b504e0703008100000c0ca01840c84414000c80384040204203800020306840d10b00c9000c02c11078100980c80c00d01100c80a00907030100401d0a0425100c0c90049000e00400b407a05a0414002d5014071a0710000b1a01190400c00c80710010110501349212140007248480803007400480ca445901c84e0001d8a0214181000c002000b201c2c8900100b40e89a1140c920300b01e42c99080b20341da04000034060711003203610507001850065450320320410380c0d1f04c8624551940c01041c0340042480841e22460540c01f02030a00070705042e003181020758402c4101100034000074507000c5402d01c0403d149209a100300d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 703514766 1250 703513516 703513529
    0x6180111180f0d06060b0a030c03020a081f03060e0607090501090303080105091008030a02010c18030302190326060a060e03060f0916030602070c050306010b0307050c0304050604080f010609051909050106 89
    0x2045d1541c41e110000141d00c00710040011909014807180064024429140035072420703103500c50950344030504c0c0b00c40d1009804211841501004010012503d14030824002d4240b001c0140b0180c188039502401c0d298561f0703c40ba041040803501800013a0380001c40604450003030700c148032551203c8103000a820200e402c401850b00c004944221103a605400521140307110713031612560400c0000300c00b20064814000580540d10880b0071510480f0160849021140a868030000017003805081001700141c100028210480131001e00c002480d150211034014140c40c244072000319204d001007500c4150050082c1c02c2c2c1c0c00540005840c2007014441040602c4500f401000340507164a0a8802508105001c6d110408401d00c0411740d4140082ca0382d05955440e500503040d42d441c4003048800341d10040d40700740140014480000d00351035243c0640040d00b00d04018200f11310f510a8854211411a402400814142028864820009074a2004508181710301040054080c18814090002d075440744 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 703516016 1250 703514766 703514771
    0x140c0a080f09011404050d031202130f0f09150b130812070611030103030903200d030806040e0c0f1c05060106030e070e06060a031d06180111180f0d06 66
    0x1542140c0148000b4980024240c071070102e0105401044001401903005a9810601c2c0320a0030020030b00400d41074600744610080036180035202082003601030855808030486035202c8900b40082041c05841d03402822041c00c0411401020b0f103a0b00061100340d10030007a980030001080c03030503803074214008805410050304540340806001900d0140754402d000550b0b806150030b86240519050600300c0b41220b40654480c001ba505544803103410700141c862124101000c0381058599417900200220790714040e440309099441d0000900c001d5600c00400c1c1406d9802440f54500540e83d590916400042c1c00e40b500c0d00b4035180310002008000d440c10002d0074510543c1700019405038947c011855003010720087d21070550351a404011804802c0d0307070f50350b408102404a514094807947c400a8503100b080c00030b922800e003c1c141d40c0c1c1048004d41b0b60032600726441101e544140b03c240503203045200c50143d158074101260307c0c0702c2c5214002e440d00c14481d0400c0031211505540e2500c20b1051030382c120408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 703517266 1250 703516016 703516027
    0xa020712051e0609101503030f09030618060e0a020a150210052e0e0c0306060f030f07030606140909070908030318072c040201020304090e0c0f03060601140c0a08 71
    0x2e60359a500f164146140e00c50140d0071642c0c2e1070035000d01020780c00e4241402d80310504595090340e460b015003c01d40c0c10044041c400001081050140c501d0b03000340d01d4105440802caa06140080c1c0d002103251055680c0b141e40883d0045c1c40d48011403040703c0c6051840030003c0128102241004000c49480d090303241441d00380700d0003032100c2d840039190710038001948030069411861001050641d210329103034140204000f4102941c100c00031540700c000101180e20309403110300b21b008550400d58501c0080074107002000003a40d0184181d401030806420103034545140e007044030703040c0d119410740b0314041d64540f40031030400e500036040c04014001d4034058a490b403809610f0410788060b28640324070302c2e1046860000e881080c12006e83e4003c4e4001c00d1080f0410301407044c440c040e1001410890443c4810070000440b03d5040c490150010280f40c041c0c414039080c1000c1000403000e030b10350b42c1e10a42009080c400c5d43d80e00103c10a00c10720400316480d8481e66550185400e228903144050712030f102c000384 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 703518516 1250 703517266 703517323
    0x1030e030703020c0310140c030402060702041a041409030913090f030819060509040816051f0e03180d03021c0903050118020f01050705010207020a080c13020a02071205 74
    0x1002030103513400303404440380401c1c1d51140701d06895400c010b880c500341c8542c000c6007512180d01c00465006001a110524190071503001c9001c85404564015421028450404007844c0500520040e12040d000d00030749402d0400a00d030f04d078821504000c2c89400d203000c3ca10070204060b002003501d10b820071181c40d1309011505010389481400c50340e00c0003014a0740c20a01c1048460f1055500b5506d026102088503511907681e101140e216490031407003090101101b400043d003c1045140450216064224041444450f107090f1008412400c030b4603001480308000e01110f82602941c004422201c440c10f180140c20306908012043c2d080c44090300c0f240403581c0615400c0842a003c49114070001c104c00c10030649511885042d10100a602c241400134114181d0300c01c0c1d0103819041d001d40001844d1040c250300141c8001a1688105456040810306190b0b518054103a0300c3e13040c480c41010345c85c00860150080d101e4081c0c3c083c100500c1802029101070007010003208a1078004005030300c070075054902 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 703519766 1250 703518516 703518523
    0xf22060308041706091902061905040f08070302091302220203040b0105030f060f0709080a0501091202070b0724020d150f0612020d1514090105040b060a030b01030e03070302 76
    0x10b9414940300402c03020f00c10040014107544100b0b4803502412904070b5080051050404003502a0780c0031209114010310440780f04c102444070304041c1c0b10700760388624103400c9501680e1207902124450700911010000741c1c40341c0900d6540100620001d200750001031000404190a01c12680d00704814120114003450155005500a034007d00d04060503a0740c40c010540c1d24038054291030120f80203030000c071300160041c0d03942c036800904504050304141d8035880c940340b8201c05110103440580d1600035540c1441040b800c4d045000d600d034400341c031281c0e0410341010350a00c10745100801c45910140c42c1810f000d100c851211030035040301d00a641e284280ca8202c400b408400002807841034880c28005480f680214401045800360345880c051019201240c10094004805841c0040e072a00940c626025000300748101609006003500303020750511040c13200e40f0605030042401140707402c8036102c1540e2201e0607100c56200c940f80210f46040c0744801200900f004062002c80c61001003034034000c164021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 703521016 1250 703519766 703519769
    0x90b09150c0403331401031208010e0103031103040e04080c121c02130e091501090b061801020115261615051908090d030603020f2206030804 62
    0xa1039940c054480729196403107440746210081407400c0d02403810b91844094141e901051132000100c0d9a8003603c0120f03101924000014100c417003000100510410295000c0f00c1419030491030410309940c14440b0101c00c1c2d1906010140c2031000c40f040344880ba0b2400c004440203842002070300030703160800703203400e942d41e0f04100c640403094003603050600803070359004082e00c540d20884206107071245007071505c081c003d41c000c02c850050040c402c14042444c2440c20011070040c030b201300091a040c01c2c410f00c440e881d8001a009001d0042c18000031001c990f8501003070360700741e4642d07501502e040011200103034018a80681c0d00d04801c80484000203003040702c14140740c001d0b00400e075245903d90280080d992210b801d031012640410401c4414084080c0140303115031200b03120700740305240c019400341e01080102c40440010024406004000101c0c07014000088541442d0409020250455000400c480d1a0031f03403050040380c0c6070340411a014040e0504210000c4504420021a51282803099043d4050f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 703522266 1250 703521016 703521043
    0x8150f12033a0506030601060c0602090604030515070e030a020111010e0703080a030f06050604031e1e1202150408030c04051f02010c0503040c26030c0a0209092a010201090b09 77
    0xc2d00c0320b21000210a009031841490000e010f020b090f0708025007541c41e035400c54025208540d00f488444616260100104061400351004083d2880130491108131028014030b000c0401c406c0ca00b140403140c4000a0f035030082642420001d03244002004468014041c102044215120b18603000080c001c0715002440d2808940c1d0f000c0c44030300340d40e04004c03003070380c0c110700c541c0d0381003101000100082078185955005001c0c100d40480803040494540140720810190742045038050340e8012000c125204000380500444c5001824410070032003082c80050030001c001500c46980000020742c1d610404044074050940140f0782c0c800c18507082c045901c000c2800c071045d00598601001811700c1800354081d00e01c55540b00300405030300307400d0100c3e00000d0f82d52801005001c02d01e4800440004609101915920030321100405500030103004201c080000508404000d030030000005081c1c042c0700c1c601c2c09410240414000441c0d8188c07004034014500410098440302c0040305100c00c054001c00c0001ca0000c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 703523516 1250 703522266 703522357
    0x40504151116020f03070b030109020c010507080412080a0e0d0512010b0f0403120302040f08160501050c0d08060604050406060f0e030c0109050913120c020108150f1203 74
    0x7888020080342c80342c0031081d521106220b0320320b4011300d442100d112443c00040c080d0340402d582d421500302190070030b80002c142c0540201d8100c1d0040c2c4240310700c5500c01e445140181903401c0946550030683c04500240d400c2090200020b0748103902c4c0d8001c2074103001030400b01ca1820f08803140041483d00a8510540000805400000c1b82c0c810801560f00307980403101480d00e403526640e2503010b840c0000a40009043d020310001501c0800c00c4005c5008245400151240d001100c3d01e4a1842015820860600c60702384840d13841d1070000512404c840440d030921a0a9403100070018803603010b03560240e81d01034100100130480c1548080d46d02006003407601c0304001140300c14201520b8000901c2120700240c1640c0c0c1c104490301e80445601d401144940044030505615191103040b500014011408546584107031421540d1110b80258000800b030496400d0010b4a40004e02c1c2d00800c1c50751520901d00000480801d0b401401101d11082a070400f99280d00328029130007411001e00705030554802d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 703524766 1250 703523516 703523531
    0xc0c0c090402060306130e0106091a010305010e0c07060605090907030302060c03130b07110109030e011205010e0a050712060f0e0109021218070305060a060911070b01031e0204050415 80
    0x1030000c5218000da5000340050704594500c0c1c01d11500c844e80442420b0f14644031403017107000755002e110380707c080c000b00000401c40c1189215079907201603480da210350400d854280100440c55a03003004a030400c18410f000c41e9510400e06206000d44a00c1d001594000d68070380510000240005000c01140d10903001c1e9a042d40d90000060300300e000445440300c168049101d0306d40003d0504402e59030090050400c000c082008411040c2142c0c90644110302094103480103d50540c1c10001001071410910320074882903046c030030440c020503009000440b100d0f0311880800ca40b140500111410403003101f5080101a45da190050184a814072a00801020220001c0380c518060700032100e03291010032245040751115100d00868242040110f24203000c2c400d000f0000030320034080c5a011b1000c8540c045055030801c056502191096401e5500e01d150810444000500590041d4116500400c0100c0700a03401114081304403030441000790f000b80b83c078003084100100c2500e034108440f400f440801030403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 703526016 1250 703524766 703524769
    0x702310f090605101707120204151d180a0804150e1905040605010c12141b0309090717040f060915020c01050c030112150f02030106120e06010f230303030c0c0c 70
    0x41b5000d0040001800071045d4107405820280c21140318a0310412015044c142c0d82c8041410049842c1d16451030319040a0a0018504a9070741a00210040c0030190294020b16a21a0a00d200c4c602c591401420829004001d00c0d02034465048115030103401d4211084921480030f20703030803c0740500c071700c00e0f45000404903803035204006500315540d10141b03086001c2e10ba00415150041810341790760074081d040181d11111800c1c0b85281196a4414004540b83d40038601000b6a082c0c4c010031030410007072896081c0d02c071012040d030390f250441d40000040007500c129040480191404c0b210181c402c80800d8130a9025502c01c0d8010206201c014000b00241d88604c224003600d4402031251460428004a0b001c0100c1c078180000918031000c440001031f01d2041c40400c90581c0c100740c0c000c0e008228805823003582e043c0c2500418030344040d1580a05810741c1451422030900c0c00d54040e2900e41e000c1b034101d0101c203210601c460242c15400608480d228a02081104220f41c007898407007030140201805002d96 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 703527266 1250 703526016 703526023
    0xf260d1713020a0b090a0b0a0509030735101406010e0a0503060601030b0d0b130506130c0e0c070f081c060308090919110702310f0906051017 62
    0x1d05074028001c01c901c038944001e41085030803a01c900ca0f4480000c02d4001580035141000700310408540d21f4560301d40640000f0581400e120b50700943e07000100101210601903101e401503001204128580e8020101400041c509024141c0360001a403a242203a03800c030f000c038900c440c480e61091762176a41d2400c2031010301c1a214624441c00750550f0003007000c9483c560194111082020b4080c240e05020441c91b00c0e50780010b04150303070740984a1300405000e000c1c400e080c0202a8011001c9429020011160f500d1115001d014854071039683c08180224404001d04e50417180282d1300203250460b61080c40c00c0185140c1e02016407000703240c40c00d138006407180c83c0b80d0241d1740407a07030051101e82c142100c00c002d003c0c1c4840001d0000c03421041100a40c8400b101c0d034410740e4504240c0c074924a072a0561841442942d0108150703031542c281505852607080d50018440401903100040c002c100d01d00c104044d038000d00075480d00140b905040c02e08010019120031103450480340004c0c058583c10300c000140c00d0301c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 703528516 1250 703527266 703527301
    0x308100503030c07181404080702040606080c07060c0507210e040c0e300607080a060e0411011e0503060a05190911091c030215010f260d17 61
    0x49900701c0c0d0410030040d10007040401034405c07010070210380c9510024046081110842d022151048045083c0081d13081912984000e006a4200b161441c14094103181040c00b551130300520560306c501000d4440392081040c0c1c1c01c0d441e880021390511051000071082042b00c10034007000058800302e0135800c40d1a207030045c14001685502c0e001c0100d1100c500303001c00b10a44060540383e00c0c10350892403800d0b824200703080c04c40c031a0400103401107044c0502c0060820f00094450502a0304101c01404001d51508d0000c1d0082d80c40489605d104084900503200c203418a145c86001ca103a215801302e800b50041c004520071362003190460051070702c0d5000c01555104803400009418071418040c840d0184561020100000d074003511407c00c055240020101c11102d01240d00b5034204203985410140c0400c18103141040038160701d000396050401b40421200240700f0f00c0090380440c900500c0d0b50154484585400034a00151007409205810142c0342090030070b85c01d02445810400640c03030100071a075462 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 703529766 1250 703528516 703528537
    0x201c05010c14040e060411040e0103030207060c1a06030a0c09090c08010504080405060c0c060d060e0a2a0e040e0d1404050105040b070615030308100602030c06060427030810050303 79
    0x80c18030381050f05107139020000800355030b08190740b010120f0500c01500080c01c000d04140984003403660443c90b00a003014502e07403100c2c2c14080d820034202c000610128001401d81090954072810ba45e52100107413904140c00d2016141d2208000017040054143e000309809070b0090380c12401c80b6603103030341b4170b42292401c5501401f503100c28403080c02140760450081141103115011140c4003080e0000056060740318103d0142c50564480c410032101c0000c0d14002d03409203d2910070002200781c01c1411105580d404d200e0b00c6075041102040c020315000e5140305144a102800810424021000c49a503500340c0b0721001021400ca035004e0742e070321800e040860b020799806039105801c1074074114244401e900500300c03c640c001c0c0c84c1d2129198805007442d24000440c003d940300030352418110303c400c0e250b60b003070f0b007000c421900108403203941c030100014881c2d0400340035500090710860a482e061000f00c0340c00049196503500000010925502c0007489003d03150490303d585100e951002019a244503032058070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 703531016 1250 703529766 703529807
    0x108010f0606210b060408030d060536130606030609050f1605010c03090e07030923070509060f090702010c0837110a031b030203070c201c05010c 64
    0x103d02c02d80c03468020141e000405819141450b07101e602ea1801c60f0007462101071980e43c0c03030f002040503160800307010141640791100030350758036458500301304059440780c00e02d110f0011450105040412110380c48016039003211040004a8491078418050198500d0039100b512800d1511129150081500300b90760003000f004d01b02c85444e080054075581c0f810311082e07082c014808070000b00140055030042c8103481d1940c0020740c422913031502028000c60143c100c929001e1030382070704e0400240010000c003614000c5540003020b81d10480012420b80b448922103402090041c01e1043d0281c0540000000c0380103a100d0303812960785c82c4000c401241000801300f540201004404030791082820014007102600e40000c1048401000c0c03454050f407154400100003592140d64901081c1003200555040546140035451414a001e0007001c5417030b4003202910300c0c880d62241290325006c510071003401d10800341082101c4040c1d07680c0120848145a0141e41e1381d403c103015020100c3c42903032030002da50a0100031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 703532266 1250 703531016 703531067
    0x204051503070e060d060501031b0f06090506030a06032103060b03071209050106050901180608120307050a0507050d030203010306150302012007120b01150e061602010e090108010f0606 81
    0x10340c450503c01400064101c0809042c45001c15402d02419020b9400380c0000c0220382c9001898404040c003950152404000e00c00c03041c44050303441117191040b00c0c01111440d46070b8441000060041c0380541c001003409442200c50300860700054805050341840f0f803410441d20307540c0c000030780d86488100c5499000845542420501c0c20140e402001107038047d000008080303450320041600303508280c001c00c0c00042150440c14200c443d0b8000c007405040c0c80c40c040c00c0340c0345454015005c03a000c0500b582d07050110108640040e188200280c0b0745254104085407000116842c000e4020f50081c0000c0e1696402c0c1100b905103910f445d5450011a541a5500c151120842d558031040e4010003d0441403401a50000103000c81c01040000403180120710b41d02c03041d450041b041c460000342c0614501070114100210366181d44100c1921080304941e482410101114030049481140003480146d0060403d400490010015440301ca8030448250003003015030b884000a460000c03811205d6244c04440625 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 703533516 1250 703532266 703532279
    0x1090b060105181e040e011505060705150a0203060a3f06020c0d0e0118030b0703060503030705071a091f090e0c0a0f05090904110f030d0804020405150307 68
    0x103142c1c00c48443c15826006141200051000184c140620400d01071141c0d101640d140912600c08003400e9180200801c004418401010f40b929110340361040502140201c14803400340b02001c0040c1100315118031501c0c0a01d444402500b05071110340c0030f07079004200850b0180c034001c1c90b4030490031004d81044000c09440340039441c5012140500c140301c020305000c1d01c002140c50002d402d00c0c02d4001d02605500c040c15800130860005191040e041125111420440781c10f0182c032802660381058080145641e003c4044d0050300d5251301c000e805104c00210300003440340201c0e2107000c5e1030702000d68080f401c44520f2f047d01140a13003018503a0040d07503410039000308200d4004e041250342c514204481c08a03501c52000108840032620014004000540c070520507034000c00807070a840f42e604125090042c010082054490000c00080008a40d03101140c3e00d9540c001c81508140c3c40141100d210b01c800c42c400a20100c2c095800720b0040741030501041e80708940801c020302904000e030081032010714194 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 703534766 1250 703533516 703533527
    0x80a23040201120c20121b031b060402030645030307120b06160605070311040603090c15020a17070f0b0708130b01090b031608070509070201090b0601 66
    0x100308a041c0800341c0d0000290140070301510840050903261302c002215110101c0240c0005170001a4407070b0050b8074581c1c03d1030340e004240d402c0303140d0307400101c0c41c182c5e0303581481131031403003500e560900304003d01c000b00440c520002649440303544242c0607600c40d80c40b00100c0a041e070501d40c20440d030134815010307400c0004a425410068070301c0f41c0058801542e101d14011270440c1c0c4142c60880009619604002d4031100a0199007001d071009e644407031400440303090103524030183c02802087c080c0c80703201088040740300750001415040c0c039550030360ba5180d8912b03000d0010035014008982800f03c00c00c00080e8212038035101c5038245520303005003815142940c4c504440c082c40c0c1d06500fa4a61050104502040c0e14010303001040744282d01306801c500b0306c51400f5003210340041c1940b81d0216002e0500c4002242140614111240a1300c0400d0b0801580000fa00f401200c0030740c00e03d02010702c500056143c0c0000ba588007120b00581303c41b02d150b00d45031b90803400d03105110000b03045903021034082502c551051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 703536016 1250 703534766 703534771
    0x5030d1812030903140f12090307051e031e070e1b130b0705070e0f0631110315090405030a0f03021908071206080705090612030705060403080a23 64
    0xc3c070f841803042e134a070b81e1a20f0007441d406200119551008140d00c80700784003041600d80001c14010400e040118410010ba51010580103881c0200005207000d40d000c02d8001c10001007120040039140a5990503000005111910040b60440d07c42d884002680c05c100000141c001c0d95104c001360318803200a0032024086c0d010074906c41004417000e00001c3c88911600140c1030f058441c03005000050f1401e1400b0540300000350a8201202c0140148005d642c1d402c0001c0d101242c00d5503017000d9051035a401c031005140c24040c0050701f107090049030036540303050000440c0324015800030618141840410f1001440044800030700320f900c20064406511f00030492065803400c107280140c5060b5007480b143da86841d00ca400d041c089100141403021094110007800a00d041e40502040140d2820000e039640301ca1600c10f4a0250781c5983c041151a11101e2548460412400c12030f0365078803942c030b80326a451504403419400200640c000c20580306a40c003130784200d00b01d02404100c01901c8041c0103031598202 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 703537266 1250 703536016 703536023
    0x9010f1d0402030313030c0815090307030e060415030518060103120804051c120b030f07171e0304060f0e090a05071101052a04030c031b080109080405030d1812 70
    0x500c400740380280302c8000300c0d02452144030f0040c003151030254014274144104009640020300c40040151721500002522450307030b014504081d4468040000c102d1900c101e0b00001c02c0c0801524180b200359800d500544e002e0758404002c1001d0f403d602c000203484840a000081190551061501841e44a089003d402c103004400390f410907189050100d52070071a1200c820b021488010b1f0469034402c06124203002d0358010360250101d016007200c01903d8400c94007855400898502e00f10b14003550070000342c035850904e00d038842c0848031321050307003641c0c2d401c02e10902c0c0006810141202c040782c4901a07801040d84007070059100364682c0740903a40500b1009011504102c50900b00e06800e400901070301e40158502c186200700307400300080c0480100360094101d070000e01d04000c1040081c7c45605804210307600701c0012030307000400548a10701c40c0d01c941d1041030103608040e00308061109820040c001c0394400c8040354501d2803034103020303113608445404600d40d450840c03034100170041c2d2522152440b94070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 703538516 1250 703537266 703537273
    0xf0a0c05100203130510060807050d050705030304060207080d14071101030b030a0b06150304080d0c1803080d0b041a09060613081b09040b0c070303090204050a090209010f1d040203 79
    0xc0038110701e81281c00071292400d240414000c0035041c00320500000c00d00e0341e4001002d00109003842c5985030f4a4030340d40301d0360313004080c42030313612081c0a418071040d8003400c1c0c014241d0ba0703615600c000080d510006402100028041d917600343e00c0d1580520903001006152150a6040800300e840b2619042029804181403688980443c2c003250707028000342a22601c10f00c800001c904201c02072182d0891248004034451800700103002c08a000c00d03098801c00c01c0303480c0c0081085c43e025101142c0400c40302110300c040d03412130f1602004100c1060003401006039241c8003002040391805c200410b45910820903541c40132159070704060343c242401402d502001c003a184520707251450b11602d0300f0300c0f4950301042e00c640080b5001000480c41c2044206c0c011030403502c1c01c903107060a80300c040c0720642c00b42c0481c02c0e50301c0028280c4105030098104460790394004100304014a01114144040c0008620403849581c8100000c903103850340c944aa4140e403007102080241c4600c0c1f4005240c16500600240d90520 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 703539766 1250 703538516 703538533
    0x1b02091e010801020a1b020d050a060905100902060d0f270507080303060307060f0c020d081c06140418060213030b0606091e1201180510020f0a0c05 65
    0x884801465018211800c600312000a10200d20300440c001038000c5042c9034010801405142e600001c2c41034804010f0141d01e01440043c80000d2050410020007003207070003818010300c1888802d500211a0a0107142904c90b0325a040024030115003542034001c0d404203003841220340c030f400d41e82e1040c14807541c420000143943c03840c02c8c8000d1880f0741d50b1641c1c404403480c1e041d4038800c105081c080a4010054140254110f083c8100040d440302541c1c0601000c00201003803000c0418490341e0450440b60700501000c007644a1030411464a5000805031030200a0760540d84000c1c00c0e603442040101e4180211701403204100400300400707000394104c60000c000109207031401040052004090020f601000b00c1f010364650703d006004020010803451181d14148001202a00d624140d803111705e5804001d02c1c06150804005455034406040d0389400358a0010010000105083e8469140b4041c4007200d01c1d6614960108040e4880c1e082c139110700500034000340740554040c61042e010140f0034402da0318040c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 703541016 1250 703539766 703539769
    0xe0703021020070801090215040b030105060a0507080a0917060c041a070c090506150412030c230d021608070e130605091b030c0a0b180a0e0105100503090d1b02 70
    0x382e229008004d99075074842d00c1b00700b1450440401404d0107107030500c02e030401e45800c0000d81103000501c40c448c011030000901b043c2551086044500c035961040035180ca4031803c5200606100060050301d038131580703000036102d8415000480ca489010f440840034589030410058080c00006440d03182c01010051081c2d000140c03100c1c02c00700203000390060015151034000100607079107542c20030021205e01c1c10041802414031142801d1401605401c0c28509020a407a000c41e0030081c00030301c4445040c9180314410340d000041100d0382c00034a00c0e03003160f40300000d154203170700742042a210325183c07a0b004510030490108110b000039408410a42a10300780303e2940c03620401e840d41190030542c1c1c0c0c0c019940c00b20b82c0300111220b582540c1b1040c0c000308080c5074054045000204c0350b0060007602d54000c2202c207481041c01e071a45210300d034054005001d10f95501c90b09100c0900030b0180a10a03060954900d4840d882103007036034890600c0c0002820740120790103050b80d0b0490140e5000c00c1021b100200174000d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 703542266 1250 703541016 703541023
    0x18010902031e07050607030e092707090605030c0d02040c050f0301090609061418041b0e06130b0904030c0f080f071a090a0803061318060e0703021020 66
    0x1c1041280701d00c0441d440b49103501e800d020880d0003091140310180074150100b135004525614560007507501340e09580b01d12120444180440d5050174200200c2e40101004c0c220110300788089414003c0c0600c01c1d291224105a101d20142c5551a0419000c081c1b0300094609a00004950f90450814520304a824140202030354170980001601075101e8104100707200013841030000034242d6151080040c00080300181810750882c1e1707281d10803103008000c1014803500107440c40c03400405210404100b55540c102ca00e00000403103c1034854031155603039481402e240e0158100c4c03054010040030b56130343d80c0d0f40c0954010310003260076034160f51101404400145c480f001400c44500380450143c482c641c501e07000880b41001c803006114a500d00c014880403600c001251640164450856611b0f42c1d44c1c00d0216440b011b039803e98900141c00c201e00100c88524400b5074488850045006003e845040c582c4580e540d1340c64480250002c0b001d10045400740c1c0b0441b407228040448240301d140f031070bc810064502c1d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 703543516 1250 703542266 703542283
    0x7201503010f050607080403032f0f070b0705060403051602060a0e0310090c0513020c0a06022a03040504021c14091b0d02010c0f08070605010509060609091801090203 73
    0x108000000140030291144003004002e041c11202d00741740520715030780c102e054040e610000b0305100e049502d400c048015424aa20111561282c81c3c14089071a00b0350343c0d4a00c0300440b1002c41d03001d180000700b16541c0c0e0104a035040c43d001801860740d6162690b04a0741070303100017054040100030300003d4005076030710001490400f00c0c9070341c1c40300d03003900b00b404060902d10700c081c850060514200d411400254032480080480ba001c030344190003048400c0c80b00707010b071194810300000c601440f100c0004102055010348280390480741c078010000c03068410f40382c0b001c41e00c1c0302c41c50b807642c428042000310349080e070010701004400090402100c0c010180f25815940d8559000903121005020003010500c20020003105401ca1011007001540c80c031302188120b04110000303410021751260b1101482942c1107020411035014001903901d07001030074200e0040c6802c1c01554860400c03540400d081d4038010090390004403008240c100c0907225211901300965203042a12000d54039050900e015030b0f4184aaa43e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 703544766 1250 703543516 703543549
    0x5131805040c0e090d0f050c03040902040906081b100e100305060f0406030c05090627041205270a2c070201060e19110a0302070203060f010b0720 64
    0x3420382000d1402160a10701c41d0001e03c4038010380780c104060300c031000034610003001d010b0403c480704502c0c54800321428418401e6070f180c43d00c00090b000680201039401082112020901005020b0f142d101c401d48171090001c50110a4080302900e52a0780b400d59107450380c00070a818001090710490000c900c11070000e1030705202003507a07030701000814144010404a0740303e080320200003c904650740c40c4004006c41c05850b000d0765805c0300085040d104d2108032084100c410f81c100402c40c000c5821085c0c140000c950440b4150070070365003211000c2c0240c09880041042c420b982c1d0107050f03c6c2005000f01920904c005034400d0003480c001400d191068251540c00e01039242402100050319a40442c1403809007186086a142000800c46a040c40b1085030b00006480c070401c5602104502c2e20015040b929618400b2420000e042c542c0c042d00760f0b00802e030039442901520307640d0350b4525521070540b80c240305181070303c0030801081c00001c00012000d25022031401c4554210042c03400401d010504422400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 703546016 1250 703544766 703544771
    0x307020a0e040b0a0b15070602070c23031204050103200c03071a0f041e0b010609050108071106070c020105070f0b0103020a23010509120a060518071401051318 70
    0x28442c1d41c03c215603011102d00400d00c0280b868038045040419a003143c1018101d000c682c4804110f186c0e0122241d0503007081c100d403c46034403442c005460540e090f000c81c1042c00c03003000c50032107420013107008441d03240b00313100d010304040c44c260054002d04061141c035200c1c1440035803c1c040b498005806400e82c0c8028030700460303d460030f9107006140c44400f070103218070700e440441c200507100e81100301c096400761740040d49801c00c40d00060150800c5e8603c0b84014860454100003044069100a61a0494109070790310310440e01c40301c200386d07102d60b00d0007003400c00340c0c1000c030000d15680e0164130010881881890483c0c82c00703805171034010108105a0086a40302001c030010025450b010b403110004c0d00a02d0310407081d07991105c0003000341510880c02c0350b06100010404010590f64601c1c0c500380701640d07200381c44090000b484c05a00a10b02140c401300401c20040105518010000d0010151030446104030b42e0004090700540d2f01d500400c550344489680020041072405000410095412080102 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 703547266 1250 703546016 703546021
    0x305010b0f0d0b0601140415020c040f020a080103021c170306010f020706090e131401050619050109030602070c1a0a0f050306062710050903010501050f0d060e0307020a0e 75
    0x3000303040c520407981688999010060710703002c500800f034910341048003400c3c91486c1c82207a039019107003401160b2003245daa0301916500c1c0c2c03d05401003a42c0360705210484003000b0094a100d02d043c102c2c01604c0314040000c22000c018801810980d041c9080d111000c0c2803a440789003581e561722180c0901c0c900ca074508440c04414080d45580141402c1403030035081c00605102400d00200409a01c00e5100d08440000300300d000c40c0f5042c0850891403c0c035a00880407030200c0b91101d0606000c0e103000c0d15054040c040911803000003d803505404070550340160745d02a15980f464848001039002600103031000240c200300010010403c1c101086030210003240f0ba619040524030180c00c00078400d00740401c1c0041042045500d41c3d45a08407032941441d203103d61032120000014007180070070f0122840e0040d4400d54036000f90381c0c1001c06072800c44412002030040303030f0b02d0354188000780015210440d041800c1000c51030002d101500160700400c0004106c0f401e008603600000c031070540035400100602800d10a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 703548516 1250 703547266 703547269
    0xc0816032c120303070f181a13050603190902060c010e07090e030405090a0f0f1d0708010c020a02100e09040b01060305070309050d1404050d0803071b02010903020f060d060305010b 79
    0x4030a0740e00002c0c0382c0610704601c1c003003101a004418003000001081942c4c454030243e4805903281e14003a29103034480d000d810b1000c005131318031940a10000b001801d0445000580380c43c1000c1180e03c2503400c09034999810070b81d1203124002d40310000c001ca070301c108140310380b04443c0e40900c20020a905654001c0031191321b0010444100c0d00740c218003007459041040244096280e40c40798980005071000002070f64052a4450340c0240b0740688e42003102803d10803019007001643c800110001c03400016500070554a860540c225074180c085003015800488000e0301518184a030000110498205107001e515250300060101c1ca045600304c84030080c0100500210303501d4400d56500c49102d040800ca400c0240d1995a900d151030703d010010440b440e01c0e1010300d0150002500c0080002034a51003094036585007840140e00201d488a00007484c508100000d485482010105075406840c0d5500050840e02481500701000300b910341c020804024068500c4d41c030344209001113008000008004500d0b03070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 703549766 1250 703548516 703548529
    0x30c12060603120c12020a1e021311131d04080f190c120804050c1302040503100b0405060a0b042105160603150612020c07180603030f0c0816032c 64
    0x141000215840b40c40821f0006650030b0b05410404600320b51200011013500c0098049104441c0910415040000e00721407412244058101c0319046801151019110075aa0407400700c01c0c01402030901c581800306010030f0b1420024036000c8440703801c00746020742c0e203441004010003128400001484c4c12413040d080c428540d040350030909062601c44100e0516840c2c05039507030440c0301174038840c01007003160755207411880e81100c000300005000c1d40c1c0303402032047c10040107000100d0391a02031400c08001807581d00c1c011000100707072410103c0a90500e410182002c8800105485020076040b0441d25203010a5040010207e049031140c0c1d01074030541442402416254011441c405000002106004103600200020020a04100300688a80d0480d0780c42d4a01186075000d40a8070b00c00c041c3c446103a080e160000d400707a07802610740200c0000e044c0421182c580c14000007812400092000782041c0e0f84101e132400c420350203890800d0300001500716001642c072146d205440000e042c0b11480019041c0780 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 703551016 1250 703549766 703549793
    0x3021807141215270610230a03020d060902030624090f1c0819020706050405010813140109020a0b12040b0712060b030718030c12060603120c 62
    0x422542c1854201c001000c801c5002810040e45100384404004150301c0303000341c424190303a00030412501c0307584001c0c950480075800d4a92078080d40f4004604d903040c50084030031024402501908000420a894015034150007020103401003640070000070004020a0040384050b04041d4030042e628100b6078104031403459071074840703040c0405158840c10280c8000055503441001a1500543c1454500000300d4001c4034202e5002c03c00c1c1585010401d000903030005d00358500d4052003000e51941d03002c1b41683e840030184610400500200024000d1b0351040168a0f0081c00541164000607020768a04207003c0e9421029140b0740e5444029009625000415500501042050754a0711014500c2201f40d60700080000d04808004800300300f20921841c8180070340e403070800d410042603446070201d4509610541d5000002005901d0450965030700240340c07401c42e0340c040f40da1130320540352141014076080d2505051301e042d5568980000030480c904104d000110700e650f40c0348071100d201e00e000655003600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 703552266 1250 703551016 703551047
    0x30a0e1c020c0405090304090b03030f030103030c0b07021f0e0c03010c2c090117101401030605010b0310061803020d0f0506010b0c060735011a120c090a03021807 71
    0x10700b024042091008002c90b0242c408d184000702d5514038500200346944500226242001c20000c00001816031200c0c400440d548280c1e10003419441e00501280d03102081d405a10316031100d5026550440a41d9204803000701002095138100070411000908580c1055070b030501017031400f00c2405025003122040321000710002280c0055a440388049440c2e020305019080381c8801108602026107820051294a0010348109100e80480d540c28604031210a100403a4801d040200100340780c148801940c3c420f40d1030620040c2208c1c41e001045595507040c3e681014030156040b400301c0540c4500c00d4640400d03000f0f036640b07000041c90b440e0240c0782103016408141c001400740700c401d8141d4004200d054200341185410009020560041e1014140c5044a4561071002104025a0400c0844554100d807400c245460480c0c800039901c00340c9104208040303500f02e08c01030001e01303105062000380903c490040e1985421b161640e000c201488040541d491142100710100300d40c0a13841000340514605 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 703553516 1250 703552266 703552271
    0x31e040c2d060f081902161103010c09030f151806020315060306031c05120a0c0e0402090303070209091212010801060503190b040201111c1107050102070b030a0e1c020c04 75
    0x703c0801c0204082c4c40542001c1c802c000200c000f00d0f096030f4507010f80300d1101c1102c034030350b10a070f501d490a070a120441e0610b546c00ba50074034410074107240c040d0b21902e003280c2e0042012000000b1300e0781d81103c8130301c000c1c10202c07403113544000400000c01070500451101e44280d400599031f003042c010b0300504286644e44540f15080402c01c0024540700420644a020b0b0241500d4020100412040d2118021110301d00c102d0231070070041060300d00050b00326466880b40d07134456071100d401030b405101c143d22403035034965090b038001c0100700e0040c105200165030000d10003007980c0040ca130100c0d40c203500d94880c0481c7c9045c0750000c0014000c0d91400c1c41000c0040404500034081d4041e94214260f410250310000341900c8280000a0306690040010006085204064a030a050140749a0806222000c0c5810005080603140403038081c0c0010540c0540304140c004101071494000d202c041d680c8010008848541c943c000c0d26140042041b20b480b25050002030f10340280301800009250011604000d48940d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 703554766 1250 703553516 703553537
    0x20d20040b040933090f031d1e040f0f0e070807030f03050c011b120f02070b0103020f060d090c1517011502070e040b0703050606031e040c2d06 63
    0x20a8001e90303003071544024020b04040412200c030b074a05500420320941316582450403480400140c01d40c0300340068440d8881d80070603401c04130b4400c03105041c1d04040e81c0003a59000d0305500103a00441e0b04203482e02c000c7c4042405120099201c060b201d4003002030f00f400b0348031522488085004d0000f40090302902000b0600b0600e903803103c03002c50070b401c3c070040d05120000401403003020080d00302000071240302c1c0d40c10403d81c0048a00034240750541040550b92441c000310b401a0040034022118029007190300c0c10310a9081d40c00300012074450980b0541e00c603104000904010841d13004450080f80a22210b84100c1c0c5400d00308240c45130301c8000c0000b00058014100c0c084615041e0046c10341d080e0707490000c0c6040100905078903022480c1c1003640d80208640c100b0080104c55008244912410794060149840704814440c86000503210444800f600ca01a02c1881c240858001e500ca801403c0c4521029603442c00c5005241a2500c40e00d030004607841c100130940c206da200c0e40300815080c5400340c2d100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 703556016 1250 703554766 703554773
    0x9010b0313081803030a120507021b19051c0302120901020a0f08090a0305030904061d1902090405150f03061003030c0f0813090e07030c03060207020d20040b0409 71
    0x94071088001040404007264800629051080038401c140010b0101d9544042d0854068558051002e10b007200509110028403980c0c1b02060544034440c01840e0341d4544200e200401460f507075040b40103c2030030a500c00009160303452507980c1142080560420440100508000703040070744c00004050b208a080240140903603000498809680d041255144102100d00d01154541300e12148290700c401c8592000c000e029010000386803c034401c4504004160390340045415407000b20f14180e083c0c0c00a14001143c1c5014035094140550319044018903000c414030000e401c0741c03819140c2030501024040480b800f81040080e401e4145002c40081103107250038514400e051010707000c0242042110b0100000704035041000c11109a03000140980314043c0005a031740f4007141c0d200301d800540c28410400b190340c0011a80c41c09682e00719401411150071510340320040e5100e428204c3e01b100d901c0508601003801c007000b01620000000c0c0c407140141c1000100803c1c0d40c3c000d1070140c8928039004298000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 703557266 1250 703556016 703556041
    0xf05160605041206141801200a05130f120b061806060d0e031923040501210f06060e090c0a0804032606091810021308120909010b03 58
    0x1c8403d1103446a04000a6140800181c9040a8041c1020045105010b44146514203281032250010001c21401d0205102d490407a020701c8200d0384404000c1040321940761281c0018402c801008170b140c01801d80d204000c0005000c26813100d03280303540281949040003848020a41c0145c8100c60000c50f01540313894040c41c403203014102c03038802d0030300040b10483c0e04825002400f2015401e001d40740c07902200c441250b0007450340c101900c002204841110b0107040e103507400c04d103511038000203941454104801954040c2600d9000750190314021280301a0000502030b0b24204d507003d07080070a0079441d0040290140d80003105440c03245070550200b0408460480c1560281c904600d80b030b034025291804e0681e11010115001c4408448007402502c038101c984401c01e000d2a070955034411103030f6a400100c1070100d241c0c1048900c5070030500c60809440791341d4018150f409217500d00c0c0410943c1d100c402c0ca02c1d08505820581c1842e00201e09402c3d12719003101a035005146011a03e03103549000001d0045 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 703558516 1250 703557266 703557269
    0x4060e01290109051e1804030f1b02121509010603020117270c10030501080d08070201020c03040602010e0c010e03030304030c08040b030f0f101508091203040f0516060504 75
    0x607465412007034810640c1c0301d011010000d06000d00482800204980418003400d81041c1942c000c80c03107000d0600404000c075600074440d42d015a150b0100b1141c2d440c0490b1440706c16600c40d11803141c064901c80150ba140108001e90400071002445060100e800d00c2c00805030041c240622a45400e00410250741c210f052113070741d400b003060000440da0301c460350850002c04414881210495652010022050015400502d500115050a0b80d80015442101038038024018244590031181c00e011a860003026130f21307044401c9000140c06c0c40d110b02802c4e483c640160380b1040040c2c2d11100c1c0b00c070b000c0c002400b0007540b4031001e00c0e102244502c00000320ba524070002d04000c003080282e110020912480c4825a00503005807117070340f0750b603080c04c0c0c88480380e580d0243c8084103051920404240c9081061017400126205080e4250707123510702880940d4040d400918011180c01b400110420544014009521503032203081c440c140d4060f2800c000c3e103400601d546090040300f00540134018580c0107810f440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 703559766 1250 703558516 703558571
    0x3051e011d0901020403081902070504110f0a020c1e0f030a05060624040306020703030f0504020a05010302091201050f090d0f0c0f02040e0703080c0c06040b030a0203072604060e01 79
    0x90503a11400b01d040e00900c5650f00182c18080c022800280401840c2151240340341d5a50031615550b840e04100402c4036004401402d14510820200d0390105d640710290000301200e0058030084581840829071014419821010130303510310b000e030006031410101c10350504c4415030017800c20800554619558410141c0480e1284440741c154003006091100040300c00c020081525850300d0b035138078003040a50020038044010909084425055201c6d910a40d03200b590014100100949007100545c02588010502c94000c071942e006401a00401d0256900903c21210410f960b4034144408504100382002e4000400030552641a0000c0d84541c00091180d04500d21111075055440001c1c010320702c8070070102580c01120b01c00001d20070305c500170304a1900c408060380c0c5028540001c000b0700e0320031400380e60958041070010543c244a660301965110006007404c8200c441080240360749a2034440c10000031280e2002004100606401807076000d841d02d40080c4808003101100d0110b130032070f254080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 703561016 1250 703559766 703559819
    0x17010e03040509092a0906040902030a0209060d08040b0a021e120318010507021c051c150308030a230108060613020f040807150e060418091203051e01 66
    0x20704c0e5204140b100925049602a802a00c1d01d01120102441103107118014415115000010032030b00b01401056100d560003800b504603c4c029508002103010081c0051b50020800030105001503001170050010b403c010140981719542c100c8024134181205c003001c82c15008118aa14282c000024044c0c00b40c2c419941e00c64903239031a160003c040720062400e03416150b0030301c024080265000700b003403074200c100c0c2c0c9900c01200101d45401d42c2d03070f882029000c0c1c3c034129106404040030a260b6001d82e090788a41840c10910307650b6525070951542060701e01d203800c50740e1003c1070091010702101f000d4920551034907000c1d041d8500700000b500d03107900920b00c03402071600006e440c928403225811075518030700b0a50300589454541c108140d03100c004d0300a5002001c00f5071186a222070081e101c112032480020b01107890039040c0308502250208000f41000c0f116242c48801c070000d841c0d1365030248402090b50f000217440ca44650740d192186031415580c59807400c07103001403140a503141807056008810300b001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 703562266 1250 703561016 703561021
    0x304052806030504081303110a0b1312050c2706041404020103091a091005091b12070f0b0304050c09040503090103020702031e01020304050616050405090a02071b17010e03040509 78
    0xe820700c6c070a5020703801c0301c0f0b00c00d0710000c002c000740700890103400f0300182c5403083d80c0c0d86c0b50002c030006407140d180212900001031904100c08084120440c41d098030075001d94040c1035001c0003191540d003404404020401c00a415149003d64408485a105904640c140310a04022502080c4604050030107410107443d40505414801050301d400400541603140c08414507240204e280c0341d611844580420300e0a10340420f00509002900140440d4582d1090364031201d04000c01c010303000d00b94503002c1a80101c0d24005203240350b40c0c15440040c01c8401001c0c4e600e107894a000c03410303e0011000d00f40310300906070900c004100c00005a07000c07000b0a0a006a41f90035a0000a00d003038038103a101c4044025102d14004007280640145000d140300300e048540e2a03c52002074004021079020070b2000403401c1c403042140f8030389087c15a030413103007000d0700520f800f000d601c40d090b5000503911500351806031f42c913080184103002620094030b4080d0b60001c12000094880640d26031040b0700c1101e1003030410002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 703563516 1250 703562266 703562273
    0x8041106120f0714041406070311120a030f0c0903030302030a0207020a08010c020f06040506060d030311031005030607020a02060430050d0801210308070203090d050304052806030504 80
    0x440780107401d105034040d1a4a4038610b0100c86620441e04440010807000c0c080c0b803010b502c8010354054407080c0344e903801805034500501c42c0c0c40d00305000c1941040049200e2100300c1c841406811f40c0c02d41101400c550365411050080c096030701d00005030b2000380c5002c000e8941145d0048e210801e40b6414640940e0325100d05441c00080e004030031000c2c0d0701200e1524001035800055001c80007201054081d218040e41004550741c854408881c0038001ea04560000744039840d0120303803c1440f91084c10001000581c0581c0308441c0c0d00212640c40c0b2440c0102001d0000740380030031245a10251030310040290b07055035408107000e409a44500b020f0004207882a2065841c0700d192114001481007a400203242c107814220354945540c0700310f00110701c0c440700100d0700240f01d405801c182821044000d025203490f64080340c070140010049411400140325408203903a68046004c01907000e0b00086458078204400c01010300c00940750f200c290020352811ba940b075040e07903000c1003c4803d9400c0c0080e180e41c441c02d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 703564766 1250 703563516 703563529
    0x5090705040c03022203030504030809010c060e030304200d06180215041409010e0c03180304080d03050105030105043504091a090f13020a05030304090e100903080411 73
    0x41169512500301201c0c2d0300403035816409081c082214000703210300c8050100030100103a40d24000135001407002c002c10f00106070560018800c43d04107260481140220b0340304da908440c0300c5840f005d0140c0000040c0818840c080080c40048202c506a0950001da01300c0086e5032100e035048001c003900d8550400d80c0d82c01351a01d0010802d1034016042c4060102c42698145441d03110780074500b01390a000c070351003100c0e081140b51740c0c0c1070b00c035080600a00742d241c5003400042600700070aa40f00010f03080b00d03881d86460051003e440103154450080c5208074070010050107881e0140c1025000360b1401d0204000308048480030400b00184d1951080c2422501e04428803000311207004000c2007038000b90015503045d6681c0080c4201c0801d180d03c008640010f010131203203000035a180c41c070f8280d505010031540c201c00500c08080d58401821011400d6070350000c2815030300940e002c0f1821559501059145400522069134844594003040003102c420340e9000c1d1001c0e034041c00280600701000c06803a4162202c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 703566016 1250 703564766 703564769
    0xd0e1014040b0306280528030311071d0403030e07090c0c03030b010e010e090a09150b0411040303081f210519020a1502030f070609051501140103050907 67
    0x206a10340d60750751074000805107540141c8803140200d449008400100f440f00e550b14400d610304e007644440d00f514080400c2100d00101e061807032074454103480805038910220b980d4000758401c1c0ca80805006030341d142c850810900f070b401074000b80c1c1400f001910003c060501e2a90007603040c02c0c000340d51301805040070b1801d092500320703000482c605110460318603000703002615154801e40d02071210541c20001181d1503035500c0e3301180420758080d031070201c034a407040717045901c42c00b21280050b0700c14040e02c6140c080d2192100610459030340b48180c4180d81014001c51307403074a006941d994039091071954000e0443d41b0042040b859a54240f01c042c10380c03040c0c2c0281000034040f0158410031442100350080390001100412182c0d441000421011200c40070850f80301e03103030000c1c0f4801d0010714001000c1d115680400b0f8081c11408100560141240107501511a25004d0a80080c0c029414600740c0c0c038200614112000b40b4488000400407042450188445440c080c60045100c2e03c0c0c040c400c1c6d00d0140c29 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 703567266 1250 703566016 703566047
    0x20c030903120c100216060c0e040903030605040c051c050a062c01080d0909020d02041757100e03100b0607030513081c020606030d0e10 60
    0x20300b002d100002d07207030201900c24585000f0075208100c120881c02000c134804c2c0819481021001260600410610360003411115400e00b0455125180700e00000c0032116422000c0340170075515003050040d81040d1181a0b500501810980e00d0f00706042c210700c00666000a0240155440e10000f502e045510307089135008001d02102c2c1c00c008100282c1e00c1144122800401d16a040c0c00301c000a1340c210000307030340d01ca100000e4490660381e60400d9403e5010b0750041c151958100e800b003100140300350300740b1100741100c2452000741c417803a95030140c030317403404004202c061402c4007900060000040e40e000d4000340414040c1c0040500700991108034080401d01c00100340e20084180c500444207820803c00200074204401780c17091451003503d0790084606016205d90050000c0c1f18000001c1e0003a8020400150b89d0054031803070a90b224045403612907812440483c107185100020103140d0104661600310720110b0107041d5111202c0402044079070000310447c894400b644200c0d1105004900c112800d024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 703568516 1250 703567266 703567273
    0x90e04080d021602040c09050907110c100201020a080c0f030c16061a18040b1501120c180b0309100f09020a030b040c1a0a0c240504150c0909020c030903 67
    0x34009503c01514402c0c1d9010390141e41810803526950f031050052200341e950060108404d0f454000040325100c196000910043c81800301c40f00d03c642d900303c804005000e140d80007603038403020800c0041801e00080c0804176020420712140d684203041d04241d0794401d50803002c031916690640d4551400004c6d280d8060701e4540740142016080401c64020701810409440250b0420460780d1042810a001c4501800064140d0701040e008020f480201082d5641454030340f510003244135100d011605140d84e1403012480021020201c1c054000c143d0004205668010b41180341000200740c440c205042d11400460340c405d01121110801da004403c02500074004031031321500c80c5040d000780d40c0c0c20395090741c11a80c0c207a00040c1038820440910004030452611300d0901c225880140d8109890200031202c2e009100c3e06844c0703400e00100b0416140c0e03d84007000c80c1d0760410341042061056041c0000c4909070420a0544003660170280440c1110310441e4016580c050240401c2d003180a203001c01d0382d141c003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 703569766 1250 703568516 703568527
    0x10f081b2104060b04060b2503030908160b010e060609010e0102190b1509070903110d0215180301020a0f120b1c12021617011104080714090403090e04080d02 69
    0x2169400300d0201390003035404201281e242e0703076481c8240c000c0100560305980d0203a0a6014005401d0380d1081d42c5100b410301080c0f0140c00c2e80c800500381c005000412900811522170424410744803215401081101d84108007810207001086d0305101c0d6200c03150520200c3c002c1a10907920030429203c002c1002010103000070001d20b0001400c150583d040d00c04180381505001903413801030405405034203142c071a8004c030303840c1d03603101c050040e2240d00180e80264841e035000e015880b811081c0c4900b6031200401071ba521301c0d19070700c1e504d03e0a03400200d90090b0301c14840042101c0e0406400d0f6001070702400c14901000c6034281500240203800307440743d000030184451070030840c03812240c4980184a40103202d424454107400b00e9481018400901c4008174440c800c100400000e001511195031203000821440201200b074882940142e010076070300d03030240c2000c0150300f004440c00c003080c0c4011030b0525400e041071346008200302c02d140640402146078501040804c9a26402c441c0c1d1091a840155100c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 703571016 1250 703569766 703569773
    0x70c090e030d051501050702211203040b070c030917010b0409080903070603050c07110612070905010f080903040b1318091a3c01030b06010f081b2104 66
    0x25048042e0021016080070040313010508810103143c0d4261040e9600ca08000068080180e070a1107a0183c22401e82c00500355100200144502088a82020429a44da0509280c00a00c040c8000d04203010441194520000258011a0b40040f02d0104d01d000c0b01d21250808118014441080030035400781c03038480d0303000810802c04d019000186045050768900707075a40c8000c0d002d03030f0002ca0b42500c026408005000001d004a25241610348020b84511b062618000c18000303915001c0c0c5003000800c0d45050108800e40e4888001e00c502620340c075000c105424080c1e031044c2e40380246d0141104a050214030103441e036207010b41020080505090f484440340c80200d811009201c100c406540d00c2001c0816091070950300241e507405080003116545640005040040d500ca1125a880406520900b80d482c0b071945540102d50107035004010403041030034040005818900020b034142d0610080c0c00401ca582907801c0a11110500760b00c0603142e0b201c0140050061800a0340f40409100c0140c0c410710090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 703572266 1250 703571016 703571023
    0x82a0c0f060c1e1b0904030906080c041d0a0b010302090d060e0c031c0207090e19060608070905150109081b010507150c090e1611030409051906060305060114070c090e 73
    0x140040504114030781003107401d10088445c00c68018008c28107400c1e04001e850700c166442540440d04c0c00c001420281c54207009000d6034000d0702a507103040416400e00c41c0d041c1c0240b141380d850407001d007070862034949928003042a04011140c080c200c141d0b26101c00f14003410500c80600d088000505442591041080242c1d5940044020300011710541c0c42c04218000343d8407482422a107078100412540c0c2102009452a41c400e0104555071a00c8031000180400f00f000b401024202d4168041280e01d840c2a07104e4840c040302e20010304000700039804000d858001304141402d400c1c8502c2c407289800b54080141c485100f00d11006040366540b6580440110f00d40d070069200081c2076a811000c1a6102c91b03404840905440f0003d92840c94a1351003c003d010b4890058000d046001360390806944003165401c8a030100c1d00090986807500c0020507040706445100080e15203403d0801050500ca000242840c20341c4036216a14800003882c07005210028400300001c0c244000f003808035034a0340851644 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 703573516 1250 703572266 703572283
    0x1b0402091512091612141015030b10030c1203020312241f030c030b0a0e040312140a0902030a170a0f0e0d1e082a0c0f060c1e 55
    0x2e0600803007840381403d80c10130712500304a8a180484050301269a240c2442c1c2002c02e4000b00c065100390480000444040c0c007490380101900452090001e18504010145c070000801c01c13249181403c1301440010342c9811180196410302882c2c00380c090461500303910314458400c500c18420b0301002080820502d008036640b40c7c00d52003081c500e0075143d0030309108180203000a0201158013080c4c000340e066110fa17003c805033a03942c0c50007042808214010400480640c1c2042d520341c0000c01c10481807580204010f584035020243c1001200d54410400720161405420180b020b0780321444441995003c006032070210781c00c640c82d4072022444c80030115182e03003c240508041181121076281680c01031301e02404540025000894441e1784d07a5401e14100559100306220301e10240c4810041072100b03005e042d5031100040c60395081308100d88540f6904800200500059011841c5141e07507488001440c00c10341c50645006484208182c001420881642035809106495000d00302146000140611 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 703574766 1250 703573516 703573531
    0x5100c03050d0504080414030a030e2209060506122109040e060a060321020c0f041b0504030303112502150a0507110a0b0f070501021308010b0a05031b0402091512 71
    0x103905d451510309149d1900d20a1101601140b404a219462410062103179203485190b1a0760461078820344071101c0072203c3c126020381d01c55540c3c00c204000b50800c020084c8072040e4400040100d41d00800c2c2d90f41540a018000303202203440400c4001d20742d1180e411800c0314043c19001d4614a141c00440c0780c0050802d444103444004c20a61042020340780442c031401091129809440020322110501900131070b01d003050394016070360b00d4819005100080c5c0c40c4601d800c1a5a0340f0303a07941d02e5400c004050300c410f008035a0b041c03081046100c541203004412070714554a0310780c80b40380018850002881c4c540107001d44503648000014101c1410754440d0042c40700030300c13c240710f801c4c80f0805000e200c10700116000f400c0b900c03d030411540681010301c170080d008851081d4001f501d000484034640d4405182648254581e07034552141d2303820b80c03810b4003245015240550080c0083d100e0302404411418800c4940c601465001900702c142d62074840709540301c54043c0888554a10b0781039218031103540c007143c040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 703576016 1250 703574766 703574789
    0x18030c1d0606130306200a261012021203160b10030503030f090313060528052710230f03040206090103140f16020705100c03050d05040804 61
    0x741c460302d04102079807844210610b41a50050840e50749200900c24640d14140e540e1041c881042203400110042c00000b0321a9035511440040045001140810465020094008004200006c0c01200c500c5044a41c0c4d42400010742002d0300120f103442420001c5038507280800907843c241d095001000021142c800c00d42100e00f0b079200c0c24072400110060000500a400400114039007042c01860a03800c1091003080d00d03c0c02201c166a852000c1e80b80e441900401c42c041940c4000492101c40b1901d1004000315402c103550355128028403921600d812103c21500c44034010540f000c04018640c100782c005002c18000000e18240a400ca54100040c251104e4000e452606400140e2094030990440002e035181152995400c2180395007106950a0400d0345ea034203803021403c058581180140c00316078a010f05424082d40c00b0082200300c007848002c0d980500002c1100c0e848090300388001c001103107041d01e9000120b140c210b681e8804c19000120040c205420701040c800c0000040c8211103d12185 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 703577266 1250 703576016 703576021
    0x402011814030d0c1a071b0c030b07021902240309010e1e10020d020c010914010612020d080304030207050a060201020415030c080f06030f010e010506150c0d18030c1d 73
    0x11215400c0d0100005d041d454500c0d204254504c2e80c21074a900b080041c18000e402034004101442070785c00b401400c2c1d4010403004010814041c01643c03c0d9003010380c40c4007a01ca081000c044a85c4200b0083c28002d01440800e0841255025283c020314501704004070030036a40d0400c40c1c00a80601100c2c001e010380d5028480c801c02007555840400f409200c490320107850540c0740c4180240080d042a07200b00a0180c0820588064020030b10a5506151003208120007006010551a0031105180c21003601c032005511a03c001da03450b118a90070a507170001040703903603507903a1404a003442e411b40c0c07203250004a901c0000c40c510760190040c1042d5116901444c40200d409001141900c0303052a4400c045051440800c100b00011100c607607001c00080e00b05c039401c01c80c590140d801c555000c01d900e20700c0c0c0d54035400c1c440a8a001100007004c0640700c2442e5080c4039848880c0358440c0c100d02001e50038002201c2d549545940e020528400840d003000b00c03449040e56911003040c43c0c403410200a001155507000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 703578516 1250 703577266 703577293
    0x150103021c09030306170a0c14032e1e111813090506100f0509010303051207030915020a08091c03020c0a080d020903151608040201181403 61
    0x741c900c0845071200503400d59110301c407854001c105104060f81055140c074008121a18050044080310400130001d0500c2c0c800b0b0b0902d2681048250800742e03501d07644598400e100d42e03000408020a4036040b62420890500384242c20208416026500301281441c000705040400e250341500e00701c0c41e24006000003104d840712042d40d8480c861240c0c040740b0a201203202d141c10681c00e95480811401c000007648606600c44900e000e01c1215a0030344020140001d0000600b0811070000804013980c03074108550550b030b4060058040c0d4550036200c01030400000390712520a03040f60340340942224540140ba500d1182c004041d5100c910b00c1004541e440020a28402000070580b0b04080400c001840545035004110b010f50700141d03981c01070307200d0140c3e540007259025008000d500c0395050016600c01500741454109a4500c0c2582d06030700819040040c080090946500003025500e000c151658803480140c135080c1e0b04088981507103040e02c1c13000c074070408101c0d01c686a800c0c00307d0403119000c28065 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 703579766 1250 703578516 703578521
    0x2003030708041401021317070602010204050607060e120c030a112b02011d0304090b0d11040906020c011e15030201171003050a11040501050d02031f020c0a03020105150103 75
    0x15103000004014000040108066805542a1012080000d4603007001a180070041e03400d85e4100c40840d980c102104050380f501005110000c0100340001d60400b4a40070004001d80512000a007040c1c2d160000f104410030203000b03045400f05182501612158010011507503500550b0505000c0740704007032402c07950200001c8141c4000c9007080a10300e4910380500038880f04070400000c405540d26144003041d8120a8013074200841d0b404001103480b5860501d9007400d0b9803090206a01501600c0524004255000e03071000452a0549002c00c42c124540380220092084400d00d4646510741075000103100062100c03009c41548680d828018001000356140040740c0d03520000780411203122803007143e9504a065554003040300b00e20221455669201e0908007000c4803400c90710401e40304001c10140c9850b11629025160035520181081c02b40d40c0481d039244004840160305600545100c010401250111403601c4031410a84001c2a0185406070107800c3c241c2c0d141142c10780a501c0e205e8254800e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 703581016 1250 703579766 703579771
    0x50406091803030e0313030b3907080d020301031b0608091902040b0a08100606020316150b13020403020109140a1707030c03030807020d020f0705101806200303 70
    0x515a2005480d07a40d6040e0010075480040c1c1c1544d00090200c12441180c100c5494000d50141c42aa0b900346881c0c446801004110402c510301105044182c445803000e0700c4582c100f0f8616410801c1d99241c15040882560091003854517080380000000b00401121041405c000804c040001084070381741c1105444c1454101d45044051b4802c0502d840b1541449200c00000d500203032001a00d07040c20000310360481c4868215002d1a40055009150b90507148142c000903e41880614140744038a40071704070140c0c00460103070406071900b25546048001c0d074005c401e0940c0090110b05045001e90103030b0040d402a11099000c180d42c0300b000541c08810992643e400d65000703040c00c20302824000206140424030023220184d205203030001c400140f4440301c450145000384c40741c445516103098002e140c5409841c03010215007040c18001c0300c10600040640c00e032201120b03111803034072a254085614200300c00107220382c40754054000400942180740d010040d45074000120020402c034001940e01d1105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 703582266 1250 703581016 703581041
    0x3041502160503100908040312020f0f0a02030613051614121b0d2604030b2203110c06120106030b090f0601081308030403112112092505040609 63
    0x2c4c500c50301c802002c59006018462040003402d0600e51252511010004424840030243e8000c4203910301510040000c4da4091001000906061070b542d408a40c85030005812042c3e001c2e0b941da0a601000700034050075601d4044882020b04280c2d4444a038040d00c41d000c20940e00034030011005250725000810f14018103001c0690340d401c81c1c500c90040c4103000b070500785c007a505800110003503800039401d00c00c0e601410000005054469085d1700f0810b52004010704034421000084000792550451141c0b2400c00c0d07030b0907040c82d103028160314070b0550400c50680c691650265000075814080c1c00c05001d00b9040c1c0e4010381d010440800c81d0070a000c0d450209880301d60151103a03500098840d80b180c015240d01c05c4804400b0a4515295580c900442d0410b0750220040307801d440307007040030700e104004a10746014003000c0c58800100a01c046061403240d10b821400c00396880000030640c5600304826000c040d1a802440e100a100c1000500c0d040340301c1c01110311960800800040390030450050b1004604c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 703583516 1250 703582266 703582273
    0xb0a05010b3f1008100e0a1104060b0a020307050705060a120b0a0902030a05040203390307030f08030a0609060302010e0907180801020a180e0c030a0e03041502160503 73
    0x2004110140c0d141101c55041c415100c000404040301042c14041d902408410450041e20313814041a2414059404901d0500d145004c81820f10843d002070790524503074001c0b40ca5480c08120030007003009445260004010240000381da40141d69001005050340743c00f81081c2d901c1c9580300d80801c981c0e0312802c03110f403000501444a6022154250b401030303400a100030101e400050b9601e1014003660030480e030250701c40c2d5980e0204415410b003448428030100c1422280c12043c0008820000c0303002e4440700140181300d0510200c42d640d01c2c208601c4c0c0285400044000c161803003440c09010740d40c02122151200d82c1031560000b040380c868010542644d5050f100e444901480e0014030a080303400404031002c202500044808030040810743e440600485400581c1d03514142c1e02c0584565110f1a90a000480503c0c0400000030300e00034054204002c0d80c0031558a4844080701c2000d086030321108105400b0000f000640d440c1841c02140c200c09031602541c1c4803200303109603144d40702c05034880c5a80542 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 703584766 1250 703583516 703583557
    0x140a0503031603050a09110625030917061b090402041e1a030c0f03151003020306040b01080103050307080f0c25050d0506010b0904110d150b07030909050402060c0a0b0a05010b 77
    0x90413402400c58803000000440075001d032030056214140d8042d10680200710908000e20601161561441301c50602400500362810080c4544c14600502208030ec490b150104001d200c582d12501100d000f07140b20305070008019481c00340035951484074801c4082c5500c50742c003050b4819a41314280c0e8895007095072194100b44095500103415400144000300d1300410403510100c81e40c0b071141b901c0038006903540041c0c50b454010280022540300b44941410300c00d22500400c0002ca001080b15041984800e80e5526842500b860301a6400b8941042d8114056143c03211101240d07001c81880016517655500442d69491040c0011070300302400c007510540010006000b0950048014058840060000580080c400460a0454204115070320035661070f200c91441c69046442d03024040c0c0007040b856442d0440540d405044003406105400182d0f46400019080d540c030901641d1a01082d0016101740c11800e162240c44000119400e0801500d0400082105803507e015a010940900705215004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 703586016 1250 703584766 703584769
    0x9060103080a080403140726070c0b0a03060e0a0f0f0905030d0515060f090f010e03030d050a020702090114010f02030a0e13111b010b1c140a0503031603050a0911 71
    0x30100800c140c00744881414000d0501c00250f00a040304e03401031840c1d41a24900e44680c02c4102d0b0148c070030f0840b07000d050218101290070702070366500f110b07040401c1660fa0340c1043e100f83d010703003050b0303000c0c0c56115004010410b0f1006039401c980c800d5003648100300403e006400c240030440c0c55454001d040c60340117000c0390f01c003405139a01c0700c0e030002442c440e003d803040c0001c0002040c9a01c40c4888030184000403680c000942410240c90101d58000d003020340c2c0c40c240b4400131a80e82e00685240550903070f02c0744042021740d079107581146c0e401600607003000350303940e140c500c40c220618015900c00e000402421a01e58002c1c404010341d40f540b499962032180610070041040b0700740d40880d005040950f03640000c1c100c02418800185420030401406451400e84215194212401808060702402c2c50183c000e04a0048901d281c08483c7e100380352200c500c094480140c60a2107200009040c2e00c00001845030f07600d1a0103150200201e10f0307400380042e40c2c402c105881590b02a050050180c0301d10b95003d01d85 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 703587266 1250 703586016 703586027
    0x5330a050c10380301021803060c03070206040b0c0d06152c01030e03090a0e012c06061b06010b300c07032303101e09020d1503150509060103080a 64
    0xc00d0010f02c0e0803920340c40074100180c01c9900a01500c2c0e04100c60031250552414248031003503001042400840c01c501d81180c0180d1181001003004255a030a81d000941e42c0703000c40241c9110f80004a030400019481c1c1403030343e100e541841029070100754549003071004298107106c0e10400d4082c0384000e910309800d500041d40079100840300340c45070f030005100880044e1920f9440c00000c00641030000204d514050103110b05100c2c3d843c0d0203406401d0701c0c0c1c005540c4604103440c180c01c9201030700c0303150b41c580c0f000c82d4003c8842c14081c0b10400b24000c0d41c000049441d0b4a03000b900d4000a070882403407a400c130f4500840920010b482d02610820110400180c50080300405440c00c2402410000c06128498158590480810a46102c01840802449054422016510040c0243c001c0940d038002014031100c1d00f4032981c0c81612005034001824040000158000d2440f9112051006051301d8882c501200442a080204100345103403800042d0005c0e000a00c3c0342c1200d8001c0716003482c204800208903075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 703588516 1250 703587266 703587341
    0xf02010e0a090203090304090b1207050f0a03021906030606181214160e1509040b250509030d030b1c050c06070b070f0905330a050c10 59
    0x280305001c0e800014034030741c1c82d0000718420a50007019558030741c10f10022404a9162110700c82c003030030404601d0188031400260721790603240121181d080108072070b03002501d007191030b0700300a42202240003a1282c03036202040940c00d840f081d45051042d691a030004485041c22004030480d03101d07094034100b02e40041907944200d1513010300348680349210320f00b1205180c861302002812a20480010030030000100100076504450814407050080b02800c001420a0750080c00c0038103513001640100f901007403042012842d80385e10001c0c0c0d05801081900103032080e0401c912450082c0203481c50b00340d91a109103d805005c1e00001d00f0801c140300045c05110f403403121894100d034140301e4076003079003038541d1003c0c0030f00050351145418021700d181040d4010a11801c015180081c86000102841182d80c0e0b031010722018020000056000800e0f01c0c0e6000c1c00d6100e40b0b441a1091800150100c107040c0d1084c01014180d014138100c45091207403140310740441f001006548a00382c1c0c903100682500c20307105910304 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 703589766 1250 703588516 703588519
    0x6042d0602131203050319020403080906030601120c1701050a0b1c110d09020103140f06062206020606030610050d0204021b01151707150c05070308030709140303070f02010e 76
    0x1619652900d12450310f8995291007036012580100410980414541600d00d01c0c442012040d4106480c50340c0d09040b9000c1e0640c018860100403001450f980d11600141015511054050000c101e40c140c018206140b0f0392400380d0f210070480c0001c42c03541002440d110444103540c81161a108101d903480b00300e44e103058410f0f0541074480380d00456480c5044007801070151086800500d8200c2440007400300c0b00140b402040003140c42080005007461841419482401615035564079524800d03a400c0d43e030721548040500840c288070108505900007505442441c0c00e0302154895160403075602803041c281e2043c190300a90791041480181490340203000c0d622044100c012807113051024203070a5413600c0981804a0b04503c42c200088000306c40c10b2483d95684001420302a8103050304008098440c001210600241d0341c000010000100f00c040002c5130894009602c7c0d080299005001491a10441d0003c82410610850600d804001c45940316031105102c05400e49541c0156543c902c00032006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 703591016 1250 703589766 703589797
    0xf0602011a131d0d080a051f0501030b0a211205130b070206040323010c030908090d050c090c220e04141002070309171917091206042d0602 61
    0x48605120401109043d804e20340c4603542c46141032600c5008640780180040e003034603d0181c0c454005800c6403483c8050702d4080c81c0101d00340ba101070100e01c512515500212086940615490002d003050000407d200c0c481c1090403000c07070074840304070f405d8022842006c0007030500000800c005c110400040070380c1351020300000c0c1001d40d41c1e25541248181440c40c04030301e00c0011039540140340d083c4142d110059950400b0884d4600b02c1e02c4445c25030044050140c05900b1031010041404010081481d5190006001c9603062070442c90740c40c1141c0281e030440400c81400d80040d4240d035a41181d401c20f9404621192815540396202d04120307076101d044842407030003402804008664680005c0800500030f880724003501d4903002240188411f550040003050b0000c100c01c1c0282030720441900d9030380d50803109400212400c5c441c03600c080e00c907111120307911026099603801c071100b0200c0c2551159004641c0d50800c0c1030f0080c1140300f03130041c000640d002803a1621200000882a0303018243c10800c20456 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 703592266 1250 703591016 703591061
    0x150f0f090f040f0507080115052508030c1213111003090212070f1e030807050c1309060b030a031407050a050601060503040c080703120f05090a0f0602011a13 69
    0x2c10b00b01c41c0c2c0d070305044150544940810480c070343c2141c0701c9401006c03c0c040d092028200a0002400c0f4094103120150b02e120803103c482400c1ca0041e00c4940c500e80000b20565a818000d2545401d5404158001d50081804c00080c11580c8c003914000d8040350884c48180c510b45408040005084004e08000189960b41d4420400342c0c4850003100c5204000c40003c0842d00d00b8040380c981c13400b07420303401a83c40d42d070f442900020301181803006c901202e500c40855074a940141c9001420031290040f42604034442c0d04d2550852500c80d00300d000e115000d0441040016946014151984600040517002c10600d030255400c1c200700030020074002e8000c0c800d6506c0812560b9520b400d02c1000e0344400d00103200801480188040d5810313480040000800801040e8038683d981400001481c0c0c0840601840d13030400c40c001030040f0212400304800815031a19103403900031041c508100e0303020b208019031800c40420750f101d44181020130b402740300900c21054010100e10340c1014003810300300820103588031b605 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 703593516 1250 703592266 703592269
    0xf0703020d11030108010b0a080a020603090a150b1507050607120b090c0c0d1d1005090d0f030f0e060f0a02030c06070c110603062404080714150f0f090f 67
    0xa0100301151060b074060f62545005109402e480c2c928aa442c0700e0080398004000307489001802412969043d103050741c403a6500c2c00700c3c5007404420413001e0000c541c0424406035244040d8451030340403100b1a284c04e01030f0302164101241c1d00640304e0003003040e44100007042201d03000d0403024181042c03002c00881c801c5c800300080392841c9000d940000a094022a140460760002d01030021955200c5c5000a001c0059550281010000c6020907005e4402144c40c80c0426100c1c1c400c079003a80c1809044c1401ca4070540c601540c0c100d00489090b800107814416a412051007924070b42014100117011908100044402850a500c04404001548410060249280300501000e4410411a00c0b80640c588440c03c0400b0080c0d0322400103441002d0030001c02c8000d0351b0700765030f8840c42080440e01001a004080c0180784d94031598000d039800e4400c90170005001061580071a6102c0001c2c3d803a0701401100100c14401401852410141c50506112815690741001c01501303070218014008203100040c4070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 703594766 1250 703593516 703593521
    0x40507051206011406090907080a02090405091005090705130e07030204091b0509070c06090f0b13060e0a11150f031005040b010c0b07180b040b0307020d0908060f0703020d 75
    0x80c1c5009036401c0b00c40104980c1e60b00c0c007620090403005942142c6420996400200752410040490043c0100d02000c0381290006606840c64804042c10411441c2004240203a80b40603a60704000e00f942480300159001c04080380150450720003808200c01c14805010310000b83c0000d640394034041c801c0390400009a6030328086c044401b80143d02caa400d880103c1c1c0070301115429070b081180a94150340600c810b03070740d21442c000d956581050380015104c10900d000c0b81c004403007681c09003100d6820010300004000300c164140015114504c1000701032090310308a41c44a03105500903000081c1450a060b00c1d007000721802134081c4100318124074181c2c0c0c00c1000c0400d030304256480800c060312810140505d081134071480c407000000342841040303a901d5645403010f016008003102e0070048140154100b6040d51300b071307040103401e1280d40c280e00c44e504c03943d06c5809504100c1d4201d0041c400c1103000602c0f0390141200340306640b4000058296640d84060210b2035040251108080640c05c101c0354640c3d80c0f007807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 703596016 1250 703594766 703594789
    0x201020708030c03041403040503061302120114100519031403160309140913060c0207080a0809040b06040609090b1c0302010b031b030a0204090809100f023304050705 73
    0x802505841741810300f400d5132422042d040c001c00303940c400c10090040ba54000303501c0ea4000c3c114400e0801c610064801314610000550f4455295070810303070748000440f000c0412a00c102882140c0e0f0455603074800821000040ca15011108030005450078004590b82c4284402c80741040b00c03c60f890f121b01c22003005804541e8840680001d0006c020600c040b881040b207038070640c0750490b008403060900b91006c1500078190309006220301d40c2c0e20b1000c1d02050080c421300300240404800e5501201881c00c1c504050b502c1180080e1007980fa2540800e00b61030410180c1e4143c80c0c15507a400c8802d0300702205c5100901d02c0d1002d10740d00c000003110080351000350040c4081c0c5503100b9400030070310864010600d454000c5200700c1e030881040004821009480000c1c0c180815a0101e90120300240d40c0e081c61001c07841202085a00014118501d01429411520b0741d810110181d0880b000810964014510600e11128541c90403110180035030482d680d00c2c2c0665005405041a26210b5030380320005001c407100c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 703597122 1106 703596016 703596031
    0x203040609240f030e070603020319050403020a03081b0316030e030406020316060902120a0b0c07110f0f06030a0606110c09060d0c1508011e05150a020102070803 71
    0x25000031705203460820958000c1500c4110040213540304546541420f9990f0350a10701c1e800b03040c407d1610950700355001c0c0c9003021855800316150311010b4003246503512121300401403201418001c500039011600c50050010f41e5510117016290514045102900309100c00c00c413180e00402110b20f00707040c1a9040028403280c0c68090001c10410b007000e5000030107100c2c1d824034074400140c113007001c030300403080600c556a40030050407140c42140301c010680044140781014504040c61821340d2034100600c000540300e071290100c1c005410440e50605525140c1c6010803880d070708064440000c0b10940c1c0036000f1104103170003051045401404890092241011580a003d41c01880601900c0d104036968001c00840600a05681080c05800c400c0001e102d04070410207403054142c0100d600241c80b0400328000d0a800403540d030006403070107003555001c10081d0000b5040c0320007540325030705 = true := by decide +kernel

theorem cover : BRFrame.Cov 703417266 703597122 := by
  have h0 := BRFrame.cov_init 703417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 703417266 ≤ n) (h2 : n < 703597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
