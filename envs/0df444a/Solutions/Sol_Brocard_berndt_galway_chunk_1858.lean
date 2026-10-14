-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1858
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:55:52.557049+00:00
-- url     : https://prove2.me/submissions/feb4e09a-476a-4546-ab26-59fdcbf68cdd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 333992805 ≤ n < 334172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 333994055 1250 333992805 333992807
    0x14010e04020c0d080c0d0609050402240301170c040c0302120c04050303160809100f02010c020c0a260304030c0e0a020a080406021b0609010522120c080d1b020d 70
    0x201030b4002c200b0581d802160720f100b906004002043e04580c01e2807244d410040016920010341745950400c90607070381c0382d01c00d00085042003004850101508030010301c41c110400c5100c00507010512400ca02c0d0784c0d402e04000e88080c81449041c801d00b10250060004c4082c40e00d000d8069806415480700d80a10500003920043c0c0b010705840a03220010080d500e0100c5048510501030040c20042d10040c004108000c100da0760456104040300050302d03025481001c428000c4d003101d440a4841017035412a42000c0c08a80d0340c100d902b0250350925814107080c1c40441b0f40c01a4440c0707460b2112000e84070008000c000d20014004070b004445401e50366900310743e199000c5c0e4083e030003500c07403240104a07060301040011300550050809080101c0410310b901008080c072620b042010f50320000300d0703552241440414003010942400400403600e02d41c808000a83d545410040102c82100405c611288902c003009484021a251810207440501443c1150300e05018820f4000c483c0401522a90520503041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 333995305 1250 333994055 333994057
    0x501050703090612020c031201051905011e0309170301091802030a140309040c050903150105010203041701140403020c04140c070b1b0f030403020d08010f0b1303060614010e0402 78
    0x499165856501a9203054015913122548820088402d6000c0c0180f41c24100204094034140e40280c45a1884c1c2d49800c046c803a5103004101c0c0525481c840c603005005517600300320001c0321807010410090700402014412001030240040090051903074086070351040c00641c010b94180e4400010030040d1055003003690200211100009406070030800084021981041205100c258102c059a1910038000001812a4a02e1540d84080740300419900c1260600304911034071454030403203404840d418440044c1d600e024921503444140350740c40c0c0c01201c1501c00c0d0003c541010910080d109a03050615010f5220115100124011032800d014282018621040f25008002080c1c0b154940062502c0d501c4d850380d801058480600c1c58080742000c0c410343c640080040e1903c0714500382d22400c052a0081c2007040003c40041000706000050004101c010484000c5601c0b041c081c90b03a0710524021502e40d100d040d070000d002c0b945040d00c0026807640103100c891205409985400c5c07039030140404c000032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 333996555 1250 333995305 333995317
    0x6090f0f030315060d0605060d020414040606051611041407080907060912050f06070c02180103080f090f03070608090706020a050a02121501090c030c051801080606130902030f01050105 81
    0xf0291980280241400c103d4000c015884980c032001c01c1c080d446001140c0143e11490b00c010340240d00080801c903d4001c20003904608000300c17024008545080d600070154003a00620207c0d1000d004650020411042a18108006c1c003030420b00c81034007040e141d545070107000c41e40c01c8042901da2001482e01d02c004500c1d81c003607449a484e070f801a07a0500b0790584608400e00d03030440c1c440c03003041c04c000c101e080104101031140400c1d9a0760619480c2034414040c180320302900d01020350414070018800030b1038020039509e1907148a8149621032419100041d41e00342d00c0c00341d039034240c040c01a010401c01e80c407680745403195011000302e0ba005959100d04981d5080da500000d49160005042600140380800c0c110000e540d856044511035584005854111130082c5c1c4034500b02d0381c2c7c8a414030b50f00c4ea010b014008401905040150800b2040c0c1d040d00e0861000381412410405000c1c00520196114815940d10684010f06041070780d0311240c07010029801941c40ca0380c1402260000589580b0940803582 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 333997805 1250 333996555 333996571
    0x3030f140c03070903050f24010e04020105090a0506120a0e0f06040f080c1603060c08010b070f02010302040909060608070b04180c020c0d080702191508090c0306090f0f0303 76
    0x2003996648540c03418507402c05852081040940b401c0040403400401c01c000220707008401038500c1d0645400e1803000300340300007061486414024010056401805440c9500903020300309999110a0200020245032107600002d5215401199141d1506d22869403140b0680349940d0811035030b065940410358035503022009455550180d000900040e81250003c88500d1280d8800b90624a200c245581001c03000380e140044101078640400600050b0700622511850f10700b09100720b94180000641c540c41143d802a00148840341c81d0000c5920a5045500074180d4950401600510b884c214008d010b180c070481240303100d509004140344031024111400c883c1c0e010740d02030550349030103014005480096054029401054000c100503100d803405000080e00c030f00700c2e45580c0d4041e0b10400080711020380710604041c001c1d000c240a025030b000103200305501c0e94103000760103564400050740781081100000d40c260240388184001507000045411203620068280e85800c070215800d01c0d03580c001160021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 333999055 1250 333997805 333997841
    0x19020315010c0812011d01290c0f12130e090303062b0303330b07020307170309030706030b0105180d1a0601020d030b0d0b0709150c03030f 61
    0x203a11580250b00301800c903032281000d40c2c103004001c1c10694150a090703129400c041d02c1310000c80b01940c444425140581003221400341118400d0542d050700903440e04141c40003100008a60140f10020840712050b00c201500301e4401c40040c40100c1f4580c0c01c1400040e08403140c1e0f5070f0200b1805006c5000c90310544080d4011411591040c003080b040c80700310144a01c1140110350500032003d1480d05a000303103030184e1008507401a01c44240c8002d807541c00e0462000000b5102d80780101c00c610700e071181c01c41d0780700307008540c81d000c01d800040c0c00c00d141030f40301002005900c0306000000c04080054400c5c081c00303d040e28422982c80200b90103992848010500060040010b5242d481012040b201d0f9404042c090a000e01e440355201c814220506190320328040325042084041c1d81e04100f20103007050b5030f16062104c0a401004070f40007900c000001800808490300140046200340d2400009001038142c0e401c1031034400c600a881400d5800064001900303048281c88440418090130305103a25800d40c40c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 334000305 1250 333999055 333999091
    0x60620060f0c0c030d14090a0302060408030717010315050106020307110411210103050106050102190b07140f04050109050405040f02090c0f040f0509010501110d03180b040308190203 80
    0x40d0211140091200306002c000b849007448403c3c040019001040e0300000010b50b09801884021460b0002041c82125070320220700000000d60115905810580c00039015480f520350800558103171806200305100b0f410700c000008244012184030801540c0c501343c0402650f41c0710300040b0f0702c0384a191030203800b0300707400c02c1c040c1c1c100d040c039a001c3c254611052050034280014100680c0594180d58035036485030f0030440040c030070300100f84200c100520003400109540c45101008110900009c20050843c4948100161000380628107080004646161883c2e4400c480c150445060700079008041c00035104010104860901d44601401385801001e42800d000581e820800444002019107820f200c040c801da0f00401040000f62000d407500311135080c0d199090078244000c091059012030b040103c03030001d00300e480c00049281e1040409a14010500b283c014504255a200380c2c02d0040511011504100c00d141d03001c1c2030b5600a034040c900f15900140301d002e14a050340401e1b02c59800c0101d61540d6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 334001555 1250 334000305 334000321
    0x803040315020409060605030405010c050a0f0305040f02090906090f010513060b0d081305040f020a2007050312032d0a0c030b041401051c170c100e0106062006 70
    0xc0781076080d080740c00151070a61210300b03440a0f03074502d070b00c80c0c00412030104c1400200310702802566046081890301b0b42c100100702d4402032407040b05184043c107144d071b00c40110b41030002c02601201001e03000707003000c112810807500b201e03912142100d014426001c2c01500050502060042d07038000c3c00c0c000145020701403242c8a5200800b460908194000f08070884500011001000b8200303045070380202d42c010f6803400b0300b8403040d10b40300c0c0300c049242d92040080c42c030f48a8101858441c808001203580030b031105110012440c003143c03608901c0d410f10850b00349a11280c24200198400c55805101401d001742c00f018003411511490400d5055001c3d1000080743d510b0550b1110003983c12502e00428400c180d18089130071184c1a422a100006008006001c3e501700400b078058404850b03000c0420103020364030340480c0440c0300c0150b080341c2c0c580040c400f0fa8030744040109048848080b401049000c0007500424000c0030b0030b02c00c40c0c001c240c045c3d1241c403190519a0401d96031851800207461150b5580300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 334002805 1250 334001555 334001573
    0xa0302060402060f0c0708250b030a05040521040302040b0f0307060503060d060608030405011704050303040f03270e0105061c0509010207080f040504050a0c050a110f24010803030108030403 83
    0x800d50540d0007080c0541c2c00c0c05d80d41004028020b094450140a000001e02d04d481c04480c0c80c2085d449420b03c0302c1d0230410961403a00d049903444109880c0c005405d80759860072600385a4088852040c0c0034100100c00b02410301200103000310780c422074041100d1100d41040c880c0582d000b2140a034140c2041d03008100380342c003c0c00210781c001c0d03009010700d406010544e108402c031100d94120158690001c10103004558000d80d0300e98408a941d800d200151030603070b8402d5a6403200030002070184007140710304000c05002d40500f80642c25015803c0266000000524003000d0052046140d1103405100008442c101a8100c0705410f2a0031300e200306943e103004615014010107086101c00350340c02c005c404003051608000c0d02042d000e42c219142d88900d820308001c01c0e10790180c1820422480c1030040780303440d0380040071201040c0c000c3c1400084651080501403c003000450240c01c0f9002d42502e011190001840c417045064042051745590390303c1c0c00c3e0f400c0d1389010034085c58102d035008110a001065100c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 334004055 1250 334002805 334002817
    0x40603050c011d0a03050723030d0302090a0b0d0504060b1005070b091203041a01081b010c031403090304051207030201020d20030a0e1e0604090905030729090a030206040206 76
    0xb0448152200c580011840c040d096a100341c40c1900001008d10044d070040c4d000c10000d403105491000c0198034400004e4640b00c90308000ca040c1540043c03142d07215100c0c184002d0080c00c251a0a40d00c407813108180002600c4101d5085603901c1c074002591040c1e18000c0d41d41000d184c4955180e90820110703950300034200c84094110729840c4a942030b041200e4a104004600c02d9220320f45044451840c0410000c6420040e00519a142c11081001208459580c0307007002d400801d117810302c6401020300f4150341c0010561110003111000104020b0070107000402001104c03010703249480d5600f480d2600507160121400000e005800181101194601c02c1c1c1d03214248404e40d074800110fa043c00a46580340d94844941c2401140181f00703206014034180404616030100414040d107202149000140f440c480e03409090b0745680d80b042c203102401000c10546001c03650101109000c03850b22144c501d40c881008120420340f0a00350001030a8031808960440e86c44c1d41900100700c1e50301c43d0380c204000c0d90424 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 334005305 1250 334004055 334004087
    0x61e060d110405070c05060c03060d110f042405010c050d030c020f0f060f01060c0b061201150902030402120d0f03110c0607090303031a0603011406120f010e0105040603050c01 77
    0x300901d03004580d500c0c46528058000e0341c030b8180040000785819810310400070100700d0399010910400015449100384652943d034082e02200c122a80030340003034404600e980b130b8140c02078030340040c005c6040001c480351909917070719009494040342d4840045460fa03030511070040494100302d48030000070b8000d8015440e88600b03030050325507100c041d5100c0d030308d09050a03000100e540e0090041c48400101d8210441c0503088a00c2c2079855500301c0d441e0f0340d2514001503d07a6000d446032092007403240c1d0007035018002120101211040325541c071103150b0041e4200f83c50503131080c040c024a190740c507500002d035038520201c01e44506010044100042c1c005090068101000601c10080c04500c49401d07c0300500c5200c0741c2d194500c03070381c0c00e47c140102280d01c00050b5074180c030482482003205940300c901396030440e10a08c1040b505d10003244089102c50258030b40ba111281f80c0c032130a0046515a0710752540c141e130f160b03542141041c0c0c0e80300c00700410344c0c2d03ca103c050075035003012200c0e5905501c80c48400642400d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 334006555 1250 334005305 334005323
    0xd05041403191104060905090a0b040c1214061621020f0403081b0c01090509060402040b0307081603140403031508070621090803130606121202061e060d 67
    0x240301d42000c48a0701d042d4100c901080d40340c45103099192074803504000d404c00c480201300707a1912031660f0365034003402d260203000a0788400006040281d034418100c090709020b503c3e5100040107180c480c0100000ba0002009409100700040380891040f204642c0c0c09000e558021361b01c40101c2c442950040100f0400381c5442d020041e41c04000110340040c0000c0d03225950056035600c0c0d42100e04401c08180c080c4000035003000c51101c4140e070707102c542401610b00c1124040c2c5582c54500008000303110b182e000c1500c800b0044108060359411144051250303aa1106002105030440c0381202120190124240403883c0e41003c903001c20310030b52000d06560705102c4065180341d03c0f0380c503071482d09a05601050010f030019070000c0d0b078064014a0b01c10740541201e814403d110f0507a03a41c4055010041202a8201095005900340091900940010030060303c0e99002c03c9220300f403120100540800c0d24000d84100c0c00400c07074030080180c0c4004007446240800c0c5094560b0810425004080c0d0400d841d00d0708 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 334007805 1250 334006555 334006573
    0x60f0d150209150c010513050d030b030a020907020109050f15070e011110051801110403060b0102190c060f050a091806081005010f081504031b120804050f0d05041403 73
    0x540c060025001c00c01101090b0310703540309401320783c01d548000b88500550914070801c840082d80010704c0102c5002d0b1800c01064030490304001c240f0f0412004000b075032184411050000b005d0b01076000c0711800b802441501c0d003101c107940c04540c0d0740041e10304040c1a00d1564001030702c0749100e4040980114014509084003008020a0074a01403031031041c45511360350341007401040c0d80c804041b0b019003420305c0d00078004201c0c4902030018500861101506094039030217441c1ca81d070f10071700132424200c010280d025030038400c41c14481455000d070300585010885042900b05030354002c8040c1c1c1c0030413013150f031a0b0580134104002890054882c44200c4240e0b03403a02c5000c00e14800520440c000c0401511000680c0d62500c007400600c0a100d40c0300d0406038101c055080b5007851200c5440780e11a415040603034904003854034515002e03260090240010f280c59045006981d841040c23503000324001c40841e03400a4440307104a03110ba02c0044424085841003100301718003491440d601c14030b04401026204814 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 334009055 1250 334007805 334007809
    0x1a0702060c0705190f15030b090405030a261f08010e240f0c1602090405031308060c070b0910020c030d060906060e04090f1704030506060f0d150209 65
    0x2070890041103006070400c400512940c249110340b45102d90003450507044052034903004241d40085402450a440e1a1806180e2458001c1c0c002000180c005403c10400d85014100b031526a0050b51030f900000e0012010340e0f46107144280c80140141504450001c26203a8040218800e448606500c4035100390070f00000e0380c0e0f007027031090515030321401001d0944c0400c503c404059030304450520705000b2807a803040c803000c101c4045180c0e41c4a810346045a58920104c00d1030f81c0541130a01c0000e40c0b19012800304000c02902202914032001c0364854034541d182c441e59801d4603403204175020300c041c40061020001240018100075005000d6500f59403450540387c0c020801d03a40541c0d182c904941c000540343c04210140c6c4101c1000b800d82940820029061080043c101009200400d10554448002406100d00444008043c0e0307803180061030442c42036505800c5940251009035403d0040800055031030a040244090000d0018001502000d80b035841107460340e0344280800c04564280050840c0b0303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 334010305 1250 334009055 334009057
    0x60d060e010222080601060e2b150b0a0602190c1509060f08060108010b1c0c0306050f030f03091011030d02040f12021e060f070605041e0305041a070206 67
    0x448200c3c883e400e08801c40c8a450303c0903846590082240b580302100410840781e2010b00c0b80e0f40d013401110240ca010b510f4102403002c81d03075803c03980f0703101070702030b000708020020411640d000822441d0002d00202040108000110025204080142c0c014042c260941085210f054072080d110307114070070341580c542ca0b0307180800200c0120540407601c00398003808215085444001140441e05c0d152a0514000d030000305107503c103204521000e1030125004445880c010320031032048403448010440d041761600001d01410484c0300300c1e80500d503080f01110031410040391461201c08100b004600d442180e02c02d200c0c551170058408010010b804403800e09114007070006008843c042d080240c0c85a0510715950f0300342c80154072290100000c4580580161101d20019140c240440c0c1c1c0c129484030300002140d240e00c200da19440d10404001044e20400c50594001c50185008440c80c981340c5a50294100c07510820340c8018001c1141440704000c403c002070b9100200758103080c035403030070a040742d1302040c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 334011555 1250 334010305 334010317
    0xd060806040b0f01081b1201020a0c02120309150904060f060e031c02060f04110d060f05060609011202030426070201180b0a050d0605030a2603040b060d060e0102 71
    0x1150040390512050005600e400c5400102d032409452003549040c511650380c03ea41056011150040c601d080307480e83da0b007044c0c0d400d2804172034025503807280301060003005000c81000482c400d01d2a180e0f00800540300005407202c4031000341c455200c0e4140405010015000f04041e181d0242d1503203804183c07601c0c0c06c1d822000600040d00c404d0145060708041500b440c005541d5000c1a00c00e00401c0441c0310b41c00550390360064111100d0002d252540d0134450021541c41603450f802c50340f9507010740b041000d16400901003600300b180400007901d030741c0c04019092040803043e170b0024810a0329519091010344c000e64025110703500901910078089008500903040119640b03225101040488c10f550b040480040d94a0b07841c104504041d0070500e4400682c01881202c10400038081071613042e00455500c54405000c3c0281100e0411005241030030f030368408403010314030f00b4031510b000301100c0c01341702c00356400f603607100890300b00c1c0380e03510018400c0d0099800001d40d800d51302c038961a21402c4082c802041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 334012805 1250 334011555 334011569
    0xe100908161506090b0a0308090301090c0602070602151003021e040c050909070c1e020103090503070501020310080c010212301014060d0b1203180108060f0d080d020d06 74
    0x100500c0c2d40c07064200c03111544511441418900e0000c816650b043c0c0160070b0342c0e40140e0356a1501c82400110b801080643d500030002100c0c0400420410380004e20042281c045500b15040350041d41d0070310480f4101a2040e6400e031917100814401458043c9025071001d20040310230070030800405c0098286d52140048034046100020760000a05004858a50007000390070181401c00c07180d0b8500071891840d170000e11030040707508800001c582c03103034101d009440d03049001c69485004a0410780d00070760041d1980b030400c00341910009850080481c0c01204180140c0140403000780c2030f8540c041300e92014030706000314401211204a05e4081e0605404014420740305140246004035418079024002d070001c0000ca00e800e400d54841d9610303803044a2502c005884082092084440031071059112581005854000410406001d0200340041d000016003640d801602d0707214403091000d403040028590390030940102d800720108071428001c080303610b923403a0010b2400d44c60072000c804072203580e00440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 334014055 1250 334012805 334012823
    0x212030a08060f01020a120302160804170115030b010b0307120f0606081b0403110a05090406050702011103071205060613140420030103120507060203160f030e10090816 74
    0x10074107040030480700c2c64840f03081c001000d80d42e0b803e40350040d00d4a03078001c0c920101030300010302500ea00410000c0c0c0f1801b540c4a0580c649451300d903400242583c5800c074003c11550b1030002140d040014a44421046a8000486091590903d0040810b42e03000170240c0d42071017441d0016680c0c5075024441da40e100c00028400103140303070400200628041014040c042e83c80816000e903001b1402c06000c0344c040300d41c0420010700c500914404240c41003095800564801701080070401070065540020340308440c26070007007203050100410b450460009540080c0043d4190f51808140c0720254030564100d41d00400160400304030082c5800c803032403260880342519442c0e80f04200241801d00910540c0d40184084181480085040b101c0c9130005110203000500340540400d0b20720f0080302210750907608030005540c2ca10701030f5210030031800349400540000c0c450400341800d81d4801e00c120744c60402e00310f0142240c101680004c00161111070310a03101074108000da142290500001e000b4850700c200030b0700c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 334015305 1250 334014055 334014061
    0xb0f0c04170a12051903180516030512031501030905012c0c0604050d0b070504180219020c011b0201090824071d01080421050408010c05040815040212030a08 69
    0xc4400c043c00100c00c0050060500c07810202d128640c4c100241822a8680000d0780100c11850024140c98000c010748140140b04080c0001038001c41490243c0e4040c1d42118200045802002c581d48011101c42d032145030301082002c0700c0e611a801c5404e01c0742c01140003113040d00c4525141e0032140004103900d650008809a07003049460300740078101c6101c0085070740f14140780c40c2c9000b0513203140c031b50344c00100305800850025409034003800681d000b806503810881703155101150040c000794880701ea41105500714551847d055480090400502401a555403003541c0c80802c41c54081e01d1210812418440360003c0032076a00410080700a40d03060580c2122218000c940410080f60b001400800c10000c0d0742c0390182d00300403c0404000c840c0b40070720340940180e0761420007144900b041d070699070b0718502201e525202264094003500582d00000001c1055450003002035817a44118820b50000d80c00002d00300d40c0002040030942d40c450300251030403140007151000c6a0075680054100701c040740300f071014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 334016555 1250 334015305 334015313
    0x60905091e0f06012606040207080d061409010b18040c020a0204090b01050103110304050703081803190b07051204060b0103110c0a05150405100510090e031c090b0f0c04170a 76
    0x2812800303030790031700140c003410002c214400100c4400400d81d501a54000503054200b00c150002c40300c50044413441013100c1d5480d6400000310798013101c43e031446015640c0c0003103110300440c0c01315200c14207440c0d01603910b6004407041c0800b0306100d00b029030a501982c00e090000da02c4a014884480703100300556461903051a00140803901c0e03030600845c07080402d204010002d0000140b08050765000348440c0c6d181d85a0000b1100c403940d03a010a0303a0903028100000f0782c0d2691006200409502c10042400a03540b0400e0844090243e40404201e0060000c00304011802039809130969490625011440e00c41c1031038034801c1035002c0000443d040e4000f159050a03c00c061182c0f0700c040d9881c00400e99030741003d0b00e5103030b5a103000c030420411444d516400b20b01031810684120008011004003070000e0309816010310345070342100a142248601c001c0c014208920036206880c51282d00c210744444a03110b10710b02c540101d0004084421040c1e0800001c18130481c8000302c82c0c1d151189100800200b0082e180c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 334017805 1250 334016555 334016567
    0x1a0306010801020c03070b1f17060606032a0d060f060e0303070305040e1305010c02161205150c0412080304030e0a05010e012615031204060905091e0f0601 68
    0x40581c031181d20610900312402404403c4550094224860f8911074441c55010350b4201d800301d029680c0c5001408000501c2c1c028030f2810781135080c81070240c800954640c000c2c00501d00c02143c1d2900c6443c407808010740a00e440c01c521504412030343c04a030741000d4600c0c0302c05046035603540241c2e4015890301400c01025a00008203480040150055070801989503009810f50049000f07407856400164001660007086e170810f0342c10319400c40000c0c005101ca00502030b441d16a40d0580da41e16410403840403c1c0801044900b0100e81c1d8044010445640c2d40c1007564440080940026141d00d0304000004241c0e0116480710201170281221a03a20300307080c83d010b880f604a440c180d90188550380401c01c440c1e83c00c142038444c40311017800c1c0803070584032908444c9030b0241030a44e0840c0300070f581020312401d4120076280308080f07603050702100c1a448042441800c0c9010340d104540000300200824080c0e801c3c00e00700c02c0d4200702c50300552115211064552180000212400040e00000301c041042540c0d1041d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 334019055 1250 334017805 334017809
    0x30e03040509090a1b03110d0302010b04050a051f1203050a02070b0408060a1a1f0323041b030803010b07020d08031303090b04051503090f0706080907060f0c120207091a030601 77
    0x240100510742c41c6d03a41c2c1c8810040e5405109115940700055581418000e400c05068072000910410152034204d00540007400300341e031803050310a203054820000d900c96942c401d0941d0103401c5414024011540d089926a000158820450060b8a400500a488080584090081840036220300d1425192040c12540709503418400703816054110394441d200d100014681c1044229960344000d9520000d40150a04454524800c2141d4050f892080012070101c0d010341d10881081000d09504200e0b03201044c0e19010207441000304000402c9021324100c010315100d4030103080000f041c0d815031101a8140c10445280d09038881e00d0311100c04040c1c1c03103c460000b81243e0100d05003014140307c00308000400b0108405659200080803d00003842000342c25180c021290407a0602c2c1e442e02d0008220a0003030b00c100c540b510410201080860089545c40c030071849641e1002103071130030740d125100541c268403811805d6010300000804c4941032030090041d103403080410b40c2d80000001091500e044416 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 334020305 1250 334019055 334019093
    0x103030302070501110f12091f0213050301050403090e090a0c08010f050601030204080703020f0604031b090c0305010515031b0a0302090109050402070302060c03041a01170d030603050d030e03040509090a 89
    0xc0201300c17007010306601581c040300f188140b0002035540d0312380818a80036061801e103110900305100346160300e480740c005010b81d4101c040140403540d0754034145400e8400548006001c600009024040b00c460f61618690002c4020103d07541441c65031101960004503805c4800140d44036402c401c001090703805203641050003868210f18162800c011117480c1c00c0c0710301000784160040c10100300c8030350b9a8008d40c0c0103150006d0742d0001d00004400040c0d50307001d142c4603804106041c00d9100403110b009104450481c0d2028200d5082c04c4580d04042c21507510081441e05074041d003031030105c00d80c0401000380c80b04a080f03850041e40c0e2517100f0000341c0b160440d584203e00c1140100f02d82070010354040b90a1340c00112000301030f80c5a4907240741c0512036000c0e8048007000820034800005d09420310140c075501d0071240d08142c07803a5003030087d0114107071521401b01400c1e9510900b040a16244a548280d41005c1580180da00300350701c1c1da0009021000680b8442190342c014407120050006181842d00c444420b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 334021555 1250 334020305 334020307
    0x1210c03020d0c0305061312030c021002130303090b0f0711010302120405070518090c04051b0f040f05030a120806010507020d1406090613030f2f1902060d18020603010303030207050111 81
    0x960b0385580b801103408540c8000c060301c0d0b070541c4036824020400b0336500507004005640741d4456181210206d41c0520058000030036601002590f07210106c01c03110301e07000c51001140f4000c2c803078580341124032243d4107603030405a00300045001c607180384a029005a10a001800c010391910041103004003e4036a10440c59801c80b0178000265000900503188141c292004111583c03011881326034105400052039003084001500c880300c0c14144002c1066400344100241844c0d01c84050543e14034820000034529003420643c0c6026a0250f0350595001005140041c540501e55001ca1a643d003002d000b15440c00d042c2183e0459585c0500c02d469002d800c43c40248a10b02d0300340c040f18004860000007a0503c903148181d6128540700300102c0341040003284035036681c15564000c00c6040600061000e03002d01945000780802580c102c101040ba5400602950408200c0c0c81803a0040a0040c1c50404401803141c00d9801a19800090741c000e6000c2d440c0141c42e0044ca05255003542c00c0c1070045040c000b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 334022805 1250 334021555 334021591
    0x40f2a020c1c02060f0c071a0a0e130e0709050c0c0a0f031707110705040204180513060c0807120504020d0305030a200703020f0601210c03020d0c030506 67
    0x140c001080101440115a050b46024849003041d4021403810382c0a03400010024404071159086002400c4160070003007114036280d07a4480400900100791090410701c04100500f40500f44134240000700104020f2640e2800310101161b001120143c10300d2552582100318200186104c51103515030040c4030003c400c0c9084807680700305490300d105000040c5010300850444003414811549030028403004055001181019017001d0b100c0c0c00180d1f49038074944031701034021445080900030f450460755190403801c6000c01500641f409820002d2040c400c1044120031000411410b01034600300c4104d40c1c0f2000c07081d042c9008010100b2803440c0740301c066207044c203042c400162235580d51386840c56050702d4880d880c0c3c3c986c80d00900c007822000202c4040b0500c0d6407224000801c1c50402010070764070940843d155000da450340180c450320b003403262904e2012001d0765100c4440d07050041401c1d152241c055200c1264403540012031180724100103807003510520340c0500412a082100c42d030000c1018100b00ea01e11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 334024055 1250 334022805 334022807
    0x3030e040e0d050304052802121b12030c030a030b18010b250204060b0306040f050c09060a0c05030a03020405102c03120d0504060b100c0b15040f2a 65
    0x900300800041000b10001c0044e0905c002801180c00000403a003a440000f4020031f1450640140c039502a84036a101441c6c4040d51000052001d510701400e1a01d01030f070042040403c1804402e5480c40780e102c2c00200041c01c100d603410b100401f40c040d585d03100021041010020f00c66070105504007002001c0e000d0005100450f82e900954405c00d60000e42080c98400c8504900021101400c000390000d05111010840b0031038500954451101581d04200c84d552190001c001e80e10240d50500061008200d2082c1c0f60a00720000c01600d216030078800c061070060f80d546817940c0d1098806000085d408203003032101d45050103001c0056142843e090103401d503440d036001c102000d04078003441724110000031070f8041d840521000c40320784480ea80e000d48411480700c01c80c001c1c0c001203d0403100b00f86001d001d40744510f020030703000614501c0e036a1a4151528282d0b11030400840291503164002080c0040784110390f201c1c06008080b0203150004500c0d0400b03010402c3d000703408070031100560040c4030710100d070403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 334025305 1250 334024055 334024063
    0x606010f080a09020103020f0318012f070302010204030816152306030106120605040501050112150207060b04050103031106090102030601122c030a08011203080a0b01020c100903030e040e 82
    0xc0b400050008056500e440164000c0c8540e5134101003141012040148200041600903030105401e0024001d514040000c40c01034255401000c00f10242d1001c00c480ae040210003030801244203000062401c2e8607620396030b407941c001561404002018a1004d802c0042e9814445c0d500f60070360f2010321503c04424002c4902000e400003071203003100507000040d40780d54250000c2c00203260170210b000b13460f1a5070410402502044400ba02c10f0360901c0c00000d0243c054042c500c3c103d80e040407000c40000220340c01e02e0040d520004081e100d5546503000e07408155074074460580214880e4403034680d0011400d2000703007466001817903030350079910600030004a070741c00403101c41ca92030418000040266041d4000e400b80c210819000d20144c1c02d10541c0048400000010300c40e500320303500c44079001d0303a881130800324038900c594000340003e2031040462200c3c2c0881d005032210344014016102e8a0741418042401b5041810710180011072884041042c540c1080810030020300594040c00440e141c08010760359 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 334026555 1250 334025305 334025311
    0x40c0b030705190309080c010b0f0a06020607050304080d11071203050603031c090f0809150301050d020409110310150501050c251a0901080108010e0601090c1206090e0606010f08 78
    0x1820080f5000010030f03a00c66404454041c0d8402207030313501c626242891500074414900b18034003c40045001008510301004290100c401e66401009590741c1d0710350031a2150006001200c4000041c0071200080e15940909000c00c881d00d02255202c0c20b5500b01000e8095a200f412801c1c14030702810b20000c5c1e2408070454001503800900e24040411303260402c40200032a150151050900003030100070403030104000e01700f05004840c1f00d100c00d81c01b0401034005100a01c00c0a41c4010740d01c101d0310050410381c100c9201c0c14000c69408641090340004a0304041920a4104003280c0c1c03010030650940c0414100c4001d407034203103082401c0010640045e0360f2110a50404010401300110011421141040c9034001e40f080e8101c4c0c3c4444d50780c110740c1c2545a00074a4059010030140d00010452190503c61902c40002c01d04c01011184d192441c088000c0c00385d0b1026200b005103491804402e100d007030041100070200700c031000035038000c6c0a24060030110003400150421440c012404802075100a645030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 334027805 1250 334026555 334026577
    0x1502030316030e06060919150503010e06010b16020612090c0901060903030503011e0807030c050a150c1401240806060109080601090c05091f03060e060307120501150806040c0b030705 80
    0x380c540c072540e08141f8090082c002d803000b079a00340030160040c0050741e0101002c50301d0550082c410007847c0a101030300c840d001d004185828405000340d4000700c40f541661078015001411051400b20740641c0800200c400b110010400c2d408444004e55504011440b5801080d440c80c10068450565034000c28910043c03041c4070810f5a05800e13500901455041c6000a0417250200c80043d6035914040360403100901c41d085c0b2842041000140011400c81c1c0c131210707440c2c80d6490b8100c0c10400e5951041a020944221529659401640300c400c0021080c01411550740d644411045103441109031901c2c40080c0500c1c10004958810801e220f40043c0703489c10b4444102020030130846032001110a80503590003250f000c9010355134120594001d071950701c10700042e44d03814042c6644412312001540c2d0709544154040d4000ba80411000100c10700c15008e0301e10a100204100ba8a0000c800301c1c41c00e65049110560007030010720007001208400c0c10020b1003142070309400e619020901800324010006001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 334029055 1250 334027805 334027819
    0x6150f0a030f18050d0305281a100c020307080307120c05011e0603150c020c120102040e011e1202030604030305090f0708030d0b04020708030403181502030316030e0606 74
    0x7450580b59002940c5011a41e21019405001400d009aa5070b41d0407030400e001c030346094041400010381080a20489201400300b07210652110590002407940a01020086120030035696a682d68113855000c0c0d405140e98010700301c0781c02c1c010103040c51f403641d001c01c03c1e0340d004210103000981c4d49006a900444203092030f00c018030103070420300c2c05030a0130151945100c43d00744e442e81c0d40070f9040d030041003640d000701c0c14110100540e41c0ca0074202d40c512009440542e00501050b016450694281341080c03c0c50300004d03050598a5203080c290324003c5e04040c00d000d04a40c000c0604022840d8210020541062544800b03c08bd4020076111100540058101501c540000d160014104640c0360b54017201d07411100c0d80c1d683d80d402540c81ea00040a41000c0500301301c3c16032517030724090003501c01c09600109400c0c0713980c5407694144da201d40d4002031455420703207659002440b090314a8120114401da03030003640e92846c2c01c1b640201c40700d070041445400e0600e03225119544890004039981e2000d0141e82c02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 334030305 1250 334029055 334029071
    0xc020d0e101b0c060203070b1810110d0609021e0403030e0907050c0607080109060b1e1e0c10050a2c0c1207150201050403020d030c0c120806150f0a03 66
    0x900300241d008900502010f418420020f00c0d6603000004004076801501c590101c0e032100501c144600102040040c1c10fa402401a50136507141c3e54412945051040345641c80e105002e50620180c81866110002d8140d01080f459420485802144031020440181910301419540e01500017044d1075100f501501c0c0110000365010300801c21128040c00200884035649820480200000003d0203500034950824174002031106002c000d0311a85252112401e40c0703051600410312032500f00d040740d84150303c0207400c280781c0b4604800080c0b00c84581c030009414200855800340c815901c015000003a01d03440c01c94441e403040726440e408200c000249466071424140d41c8501c514041c0f611100035400b000e44200400d407540000351840c1202c0e40c0c01c440c0c040204074034a0903401c071a01102c002d80903170403405140030a036100e940030380d03031040c01803d0102840600782c540c0507902e85034850980c0400c503420b05001c0c2c60320704208400044e45030888201e18040305183e07004d40d02d00483c8204400d1540754202c2e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 334031555 1250 334030305 334030337
    0x212010621060b0a180e010e0a0206032a041706040f0204020c0c04050a09050c0303090102030306120a0b010e0f2401050d02070602030a0207300f031d010c020d0e10 72
    0xf82805100104252075594548004152014000340452503045c5070080540a2075011b01911401c0c1080c0c03005814010401d4007440380d294002800ca01c4001d800115042c11100f40d2888807981450016800b600c50341094840040c0c62150403419409601010401000032421014a40101d605980c0581c0b12480749091520f880180561035902034201b40402511480c140e0005002e0703400362046520034290310f0185500e91280c40d103540d0040c0c00410002c1d9043c1010343c00e9a0700403840d41c08440100b00203840721010b20780203801c0300707000081003824000c041c2d081440300ca42041a03981d1403005901116171007900308680e5030005043c00000701f0044c1c07024195905807800c40d50000c6042d55a1314241c00d8000003940700c4401140c83c0e45100b600c04000940030300c409000310103045400345100031005070070341e040403260080004040d20dd5030030b04070400400c7c1201e50100c800c00004a07522195420181c1403042241d0400b080101c0c00d10b00b9000e546d507480c002084c000590501c04003801c10010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 334032805 1250 334031555 334031561
    0xa030f0b0d1203110f070204050c0d0f02040e0711072105032d1305090a020c0a060903080a1e020304050c030703030c020910180f0f110304021201062106 67
    0x121080d400401001464103000c1d0b10261199042d10381e42e42080030991025914006000d001c200d01807005041c80404010300707059002d9904070391000f5056040020581511042d42e140c2d42c0741c140784030b4020408111600348120a26001500c500b000c00d002112800c2143e40e07115184a81a00c985159180e41c90280100a0301c0700065000030540ba62803040c204406030050b1740344c1c0c0554038034000c0c1c402c0420005010069400f00d152000303004048515107020001e105030003908111002c0d50030400a0440d000804c902141d15200d1880400c0165403800c001e48500d0006055030b00442c00c011300807000025400c0b8503030754202054401a00c179200c078100240741c040119001ca1b01489203040c040706064000003c480050310845108616a480b00364000107642c0718070407048030090005400000d03041c960001c5110549040c400140042960562401d84114942c290071980001042c0015400d08010305030310380031108001c1c400b403454480303c0440322504010010354402d400100c9810401560 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 334034055 1250 334032805 334032821
    0x30c18010e0d0c08160302100f020705300606010c06050c0f0a021e07030b06061c110a110604021c080d0203010f18090201090b0d0b041407020d020a05030a030f 70
    0x42c12551622002e03280022206019015000c404e21401c0c100085401c1240001803c0d42e50282101d0b42911071520140d81c0d1806981c120019800303103680100b015202c0702149071000074440450340441003180c42c10340c0c404c805808120810b030010000c10660741d1f0040e5201c884d13141e00104c00038081d51a16681000382c005c407040801d580c640010000e90343c1d43c0c00608029402d06510036200300212078000c0e15178480141c40000c1070b400000001039070758074040010300702c0c00c0c640f41401ea1079101c440da402d40440e03403684003440c0c0c42d1002180d034294265001104104000c0741130018090b600b0180c00185030324800130450003481c2c0c5107504030380030401e03000c05484c041640043c0554595031508600c88015190307000d9003908503151500c0c43c1091603140104008a50181c5070100040d0400804840581c0032400304c1503019140c540c142000c0d03c0c0c900c0f5191644d0504060341c08241040c140081c24020b071100b019046500c07181c030080c041400801101d0b07002c17403517080c0058504440c4905002502d420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 334035305 1250 334034055 334034059
    0x3030f0a0302031b16060b0d0c03050106060f03090533090105040b06010503070f030e150c0a140c07060503060112090b0712200c010603050a150b06030c18010e 70
    0x110312000426015000786018000044030416051100c1130304148500a0310003002407402c2d290401808a60580c1c000c00b200700014141450b0a005603d40d0114942c0300ea03c1194560742d00c8504102d0a6070040d400030361403915250a104c503103410340300c090395044d8008540c0d40c803240341ca88214082c06a0000d9021b241440b103106000b51810960041c000c0c0f030104d4052305c84030310040c0007840c03035072051302124402c2c002515501146c001c4038108a0081c4825000c9480c144a88602c100c0d10801c400760395446501c00203502c0b03540d0707a40c403200144a464031303044ca0414100240010701aa01000c40c811065540600d8090b449558910040b41d19a80b0081072180f55480c008001040c45060544030b032141c00e486e1202e0a111071303211340729411900646804038034604003c2900600701010f00040103000704020012a01a4483d250325041080c403601c116402d2028840c501d0700603c244c0207606058008a611605503c1e020495040a101e100c1c4802e91030003010641e218240e025401060b914500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 334036555 1250 334035305 334035307
    0xc010209090c07030912030203070f080d02070606080c120604061a0907031a0a05031510030c0f060212120c070507030606120302150c09010c050319090302100801060801120203030f 79
    0x7041002c80c2c40e44104020b500203040540040340c54403440c079000d401107625a000350b00e0030010380ca0b0038a030b14800380000c950101c81080003644450b000d001820185020b8400010201d280c9416079103043c4100c50454040d03140d030900103125101c08164a54455000000421a03100710082e0b4400b003000300000587c00b40c4041e00b88444107a0607445400743e512401403481e0035003c0c4004000c2e983c01e45200b025450790007001d02c015803404103442950400102d40c000003150f600c0385c1c0e841500b0034980d00402a48102c0078410082d46504000c807440d40e45440035035610302060b00903030350f4009400820000856000142c100d003000010030408004607041039040080545070300e888428181e01c00010b5005106040e204040c42060711511402403c0c0c00c4d4006107019004401034444000700c59042c0c4940c082841031110107551120120b20001050f600d1001175411071040100c500500d000d4201009501c4006000a50f000030769941506c1030003002e0481c001c8a4070009203588210b100030f4a2204c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 334037805 1250 334036555 334036561
    0xe01030f20220b0a05030709020a110106081f05040507050105071e05030d060e060d060b061201061e081b0d090c030803010e0112080d021822050714040b0c01020909 72
    0x101c207201e052680b204440090004405075020800041d00c02d006007585500503440420401c0025802000c94803410304040e00d00c0d5817880a81402c4138015404890940c0000c0718400c5034803210800d49031140c94041082040d0b00f81610b030182d075000c150141905101c0c00084010034825000115864168900084413400300d07580340158913904050909600b4034141100414951a4550b21500c228800780c1038422000040d00d88402a1040301c3e10290003403c03c010114a054100c1f0080b40600344540702c03075000311917408003150344103480e40c5c00804104484003803007031500c01a8845116070a01e02c81d0030b0f0720341404d2031800005001401e0020a110380e800701c000200b204000140d070480e06c1002d50380c81140e903504900700c034541400c02d0040008000b00b10039407400d1030355401380690f2410b00117035a44c0c4020a40229a06041d0782c0c0985113082c451440d0400b03400e145004150340504c1301e250249184204ca02c244007a07009900500021610201e940c2d5180c4d4025415a001000c0050111150382 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 334039055 1250 334037805 334037839
    0x50606040b13061e02102004120b060f0f0f030715030506042f03090a1502030402040c0f020304030303050415050c0a0e03010207020105030a0507020f1c02070e01030f20 74
    0x300c103a2150801250720103d0040722090b4010b0044c2c110402e9030098002c00c0b01811809001340b400300b41031032a41c101c240c01c2c2c40707190510202402c050000011a00300c0389210742010740388013100800541c8203214080d0707003094503110b06c0c0080d410aa41a2207410050f80d400d40001c1c1841c2c042d07000350b1003035005c014550700225410f810880c01180103413010000c0640032400842d06a484416a592401c60144047d4800500f00c008580c410721110503600021044e640b070717180303d5a8561410090729000f2041c041549040d215689003240b450802ca0b0305d4454405001c0c0d1039016910015003450f5a610024041c004403c26259015005000411491804a040d40c1c0590440000400018017498010f01f00341414421184400d80584649003503989403030034540030303120080c4160114019428400401c1c0010003008104a91540c01c983c00081076080003840c240c1c165000340d00d83e09079100100085142c414a1852440c0c002440c032080001140441c0c00c040c60100c0f4154200002c44000350b445 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 334040305 1250 334039055 334039087
    0x60411040506180423150903041512090506130b090606090621060709030b010605031014180705041d011a070c0f0807030309061d310209030124030303050606040b 71
    0x1031049280c15040c13984450030026901c0c0270314040d41c0304001d010581c0040483c001d00d0b032402910001480861260f11070760b1400c3c1403510644103608100e0b50145a10204102980d82035400525080108080e141074000100c0000001d04218003518100302d55090511118485000c090301e48003c55100c1c1c200740e00000d00c030f850340b4802590286910400071580c54801c0c006c42c0d0241c8000661854518244040c01e41c081030b545504680c405040b09440091241c200142403150345191140d0740c070b03145850501401034500d64589440503a50390018000d00c07144080b4180070407000039445484102034030300b520031111941c0210303d54900c0311200041d400b0000442c20281ea2084e0b4490520301d50792001901d0111000c01041d100481c441003001840c102582c5611400e40090740385412000c0c0c2080c520340482440120381d03880c540000752005942000d0041001c1c0401c403c441c6011b0b018095816208801540801401c140c0c0b00d901040315076440c4003e076400b4290007168543c0c0e0300c0d083c041d1300c112 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 334041555 1250 334040305 334040323
    0x303180e1008061f260d02070302040c030905060a02160b0a0c0219031e030612140712023d03050619050117131202060411040506180423 60
    0x5610403100000c0c0c607241c241059030f01c60b81d009403a44c1c1d48981450014072118542d43c91098020351081c1040310701c50010080c1000c00b8200d81c024019443c1540148025524030401d220249801c216020340010000a030180d4403a03074003240103032105a043d1a10240c8006024040c3c00000c40d502440010380b0140d1203001e101000b0780880c0c51502c8441d0313540858903520342d805004181150361040300b00a400e2003e070751955842c540094410740324214a150b00c1c44014041e1070b12860100399940c6118100040f8002e00001c45944c0d90414080d4001503210040060b03090741000d00c950414a00b014200c0300700202c2c800411200b4200c52801c000400611040700c1c140d224200c4140441083ca55542c01c19040d120180e4031745990301d01241e107840440601070030407803185030031800c4100801d1a030401d001f40c20310307035501425182c241414420540d01e5442071f0b091256141209001c03080c5d882c19140c044414103403040c625140e03a00c2c100032610362102c44400c201c4900c108801440c0718008500480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 334042805 1250 334041555 334041569
    0x20c15010905090d0917010b040e0d2a021314150319020f06091f17010602060106200a0f050601080f030c0d08100b071101030b10090303180e10 63
    0x1965078410343d9960f800c40e078441c6402003070809105000004040a02e031106048040010404048290100d412074000400f403042c10341201c4041c0700055844501c0311103034410140c0c1141c41d01c000d10100705010404803002885144c0721400c0c074040c00810340020540c0942404510041e10388001c0d425280000703010402c1c400e00840303440d0890168215901000d50350040d2170f04000022000030f0040030307841241a25800781d91600d054244c0a081c02d40f03e030101c555070341d90410240ca40099054441010b0b0420015034200b50014040c041c1e002c400d5180d40550142d0074151017240c03203102800c1c001c0c03c40c000b801664112000b18140b01c0001070745030480707040008890b03600450894042d00e80c014450503044542050030040341881c8240b400b5034200703100d061412042540c4a0ba8413000358010700b0100d03508004104546a04d40c1c051281000740c01090701c203400e103d06001d000a04084080c00010f060001141807040700c4290b03040c8540140c42c0740340b081e684a0a00c0d800700e5030005203a101e070b41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 334044055 1250 334042805 334042811
    0x1202040c110c040f021c0c090f030f062d060609060905010c11041103090c032407080712180204060501090b180f0a091e051504020c01020c150109 64
    0x410544034200351003189031074601802150611030200405020100b019810880c5c007400048481038101c03403c0c44078020400000a0440c0f118440645083c806074080054203401e0726007000426441c11100501c2d503841500002c1039102d9410740e44803c001d492401c07038241d2602c031244150700016400002654055151160b03155039440040740c0c0400310b4000c03240040c1500381c065001480266028903404002003002c501c04103407440e1954950000c89030300d440e0364807003030780b802440c00d06010420490056501880c103510054400390750400b00588040104075010000496461140d490342500410040061019503069030b1074a80b10341c2c000c00141d21852410380000748942c040c0703807004201d0390a03080d46818460804424001d01003c8520990030260b5100014000e9540c0c20026026003030500001404cc140503c0e504401805403280e941c441c0d180505006200f06504140c001c0d00808035805a80c0c0c0000402143c0640038811412405100310440540b00ca440400c2d03e5051f150080d100b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 334045305 1250 334044055 334044071
    0x30a0f020f0702010302162a0603090308040b13170d05060d050d080702010f051824061e10030e0d1b06021809070e03010b01050403020a0501200601120204 68
    0x440228820025181801d00c820030118005501903005850380000217101003158400d55290074124240d003181943c122095440104c020050f403040300c034041e142900c1c0802009440350303006498560040c1c005040e104914000908633125a03420322601c80e8025031a0300c6280082c06450f001c3c0d000110081d0441e400c0c80c0002d83e583c10005d040020321a08440185030300d8a900b2426140010080d001e01c08554a421111701045802d000702402030707805a0803003045106521110303003000e002a000504500b00240c041c1c0460480f40c5040b500880c0481d4404680c1c505024140300c07210031800050340000b003080c4400c0d2456050303408803408440b42420340d144d104520303100710b55042c541c0011490403251800424086030b40740e4050559903101402040248075000002000c2c0c0e10100c880d000020640c0300020200e0038280105051541e0a003003c40c20941141c2c0000c0081200d03009042c10092881c51906c58030340f0289824002c244d00f1070540d0195615102e690210209600b001e0f402103003480c1c85 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 334046555 1250 334045305 334045331
    0xb0a0b01031a122b0f030507120e011413030305010e04030c0b07050d0e010609110418051f0306060602240a0903090906090b040f05040209010314150c030a 68
    0x41d280d90b0640315441002c04203006042101110307980c201015541324031003850b221080e82038141d49280b02d62402604c018280407500400d14883e106134241054105030911070301d0383d000381004d0394008850801181d10074070748840c1303401003010754a0010741760703441d4052081c541a600399100d0340794000e03a41808a03a80723a206a007003020f0161030080005805032901da02240202038000c1d00700e00342c0d1900c1450801342030aa84140d0312180030078521a552842d0070802c0f50041c0c81000550340c0444c82482c00c181c500b03c803015240415805070b41c9a180ca400010710b103254100701c070398040c9200d00c0300c10115540b44c0c181700e0010600c0d405003c3c054440c00342c881c8032036803045001d01c152030600d42d20383c6e0035070761901c8502011b8180f1100807410322400ea040032500d810790b402120090000c005001800b910070004010a03540c1e8040421120792510f800d000258440c4034006040d07a800000381e655054100082916181c3c405106007107801690b014028004500002540201c191610901ca203542c0460 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 334047805 1250 334046555 334046561
    0x61b0c03301603050403020a0c0b0d050604050903090402160b0903070c0504020708072406080313090605010e090709051c02032505130204030b1609060809070306050c09030a0b0a0b0103 81
    0xb10341c4030598006801e0100c0c540319410540c0e025110784140c80c2100d0150360b820400c1d020b16042880c0c00e07040401c000c14040003501c54079502c000c0c00c644c00d0042c0d08110b2202903c1c0d10074203424501440d0005030110105215001024130103910010080721443d143c4007413900d0740c100c00c0040301d4003904000000744a2504c1d000b56540d40e508035410361301d402c14654074034000c2c040414514080d12883d070302038040c840652103082d0041c0200c00296942d0034081d4031202e01c141041e00601062031900034107000d280d0b84122100341194050b90098610b4882c00010f480090841c0d00180c0d1090509030203480d00c01a1991040a69100f901100e18002c1c0581500c180301d80e1030b003c0003c020b08030810402c450300c3c1c880b6417151104550b00005203801d8580e1101044140c08503030700d2082d1441c0b0700d0319032a06070348103400300000d2a652400808505002c3c0a40b40c644c0c04d1484040d11880e11440403074450780b015003ca4072035550080480d12161840c1c0f6290308030031003c94581c413150745403425100540d40640 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 334049055 1250 334047805 334047811
    0xe0a0b3001050d1509080a0908030408071e120825150f0b06160b0601053105060a0906030e1203040f06150602030306090a0b03061b0c0330 61
    0x3440d1000c50740e0a0800784510480152415120003686880b500b030030b6034541c420154100e0144510b00c1e600d000301035000d003000e0800d5000c003416074000c01c030400202002103440800c2c0c0b012001420100b8207038001d196100006a003010742004005008501003003400301c0240580e6115008070a1086800d14402d00c45040d1010050049205a45007140b200002d604c141c201103a0018001a10310481000c201981c025403481c803421890090341c20203011501281d42ea103d075092804510304000c00b02c10600ca4285205903c80001e50000343c1e18003c1e0a510180c80a028040e0155032556900180101803226030f20070440171901c1c2c42c09408011001140c1183e44140c0c1d1407002c2d1442d102c40d038420501224800083d2507250303031081e140d10808001c2c04641c0040441e03a0007036440b82404800c0180d03a40000d0400b100c0c1038504100c0413801c0d04d010800d140d21280c4494a00004040705c00d01c540103111305081d00340d06010014403034811010b4044c2d218074500c0d01d80300c0300280e01d400c009009410314040d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 334050305 1250 334049055 334049137
    0xf0321070c1202240f0f06011b020a180f1b091e0b030705030703050f04030915170a06090f050601080402130b040614120d0e0607030e0a0b 61
    0x804001c51042e200c0400750800700d00c11141c002d000d5040380e6109450954603607880001c49428480480c100d81c44294210300040d0040d01d45007003c00c0060030300800d5a4490141c05540160f400c1556141c2c44e540006002d82c4180000b2082410308440040020040e070403035041c9400030b4020804100841300030b8500c070765151000140c0c02c4c51501507658140c545200c20a00a80344045500255440614000d08042c0ca40e981c0f64105651b01400303452008051868816008003040046903119000c1012074042401101f40c60440304405c079107000b0341d0700310001c0400000091045288141c0d2211080301c9810108112040c0c001c001a400d1b20402d48640d400651204081005032400744d0607040c68010400c80010f4100c03401c001f040550710320b41d00c2200d405a00d01510116030070300c21000009604c804000d0002c2c4005600302070a81c1d40300c0f0140c240102e40118ac8041010300a00d0b441d19001c00050031800000d90f25001a0450b500c00000c160000c0c03080e101c40c003c4c00d000e80ca0214507030302c61 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 334051555 1250 334050305 334050317
    0x218010806151f0203041a0705030406080702010b0d0516060c080d0b0315010f0e22110402040302030618070b030c030105011d040f09060b010e090f09010b030f032107 73
    0x2582150b0075200002e00c02182c0c0c451201440c214900c80c603a94039100140c0250044e603142c9142030851281480c0d00003240f60b50381c408119460004001004480565849061010103070b00e81000480c0100b6607520352070b820051045200c0d0601c00006007481da664000e200e00d110303898903080102d4440408140c002d03c03942043c000b0380e100e90b0440e040160700da44042c080b10482c00914100d0280c0307000c2a40f10040c00408114240200c240280d02681d00c14100100b6410071080c904691300040d04e582405000180d0281406000f5583e9404079001190020107c40440c01d202c4845192200044001d4680b84200301e0005110701c2a202524843c800042c02542540c0c42c000c010b490700c0710300c03010311103425464540c103813419680d601c00c1d100d003203a0750070300090024a5450100304690400100505001e804407008555955100c445c540c0320450f89a02d52164407000c01103809400101085039040c05910300320b620079140000504007000740380a050030ba080d0503522a0070304607000d9807081c0000c0e403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 334052805 1250 334051555 334051561
    0x90402160b1609090e330606070b070806061c0509160608010308030c04091b0e012c0301020c0304030308150907050d09110303131703090f0d030e03190218010806 71
    0x139080e80155110360211050391441d000012550580440d01011189030350300380f05071040183d555140c101c0c0e204005452241c640030964442c0b403240d140060000c01081100340c00525a5200c000a441d0344041c622083e00d101824026410b0140604481010302e900c1000707408104240c102844400300c44a17034503064490b900310b40364050705901c010b205140c641810440010780c401c1500c2030a40e11460480d50b1b0f6044400600010404d2418400c1d00341041102d00b183e001e49110928550250a00108519403248240021a01a020b002004e144c1070101050020506410425039440b560000c0d001d030100550340d408102070044c0580e400307000140280702500e101d10b20369005446940c014070480c1e001d503100000213841e545c000c0b50418510b0b03201c04820042641c004088465949841003e9030614403540086032038000490743c0c0610660b008910a030a244c00744000c0ca040c0d48000c2d0503900c00700102614072a840e51540c2c401c03030143c50b1807141081000d402d01c8180c0d0584a240c006000180c07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 334054055 1250 334052805 334052819
    0x31713140c270f0912070204060f14090109090507030803040f0209010311120601050f010e0619230316080a0b0d0c0603050919080a0302090402160b1609 67
    0x4801005500d50700c151801120103585007809040c90484070356003480348801035144480001409081031040e001c0040034403155540100c1c00d10b20121980c8806503c0301050700008001d011b00e40e0125840185100340402d08256442e10101101001c0c1c0316001c0f40d99840141004036040d200000c1d203250020300060000800c00d10041d900700340192410b0b100001d158001981c101c00070703070045400c181211071b992000d040c84160320320511410030244c492507152401143d11481107c1c401d41c1041107001c030503c00e5940d9901a01d580b045420701d2040240d0894001503e80f504c60f50301403c0d4210306400c06038800315200c080320f100e0101c4c0020030222541c107850681d0780748005021b0050454841210306140d403104200080080c0c001c0d050a0744103440c1001c050205c0d900541f04227569000517440c0c00d00304080c504840300c0c4980c0714906994400790b001040f4001e0103002e5202c2c1e8024000030741c507420302020040e160811030041c80c407000d807525800d41524031201e8145410006c0b03100014104140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 334055305 1250 334054055 334054073
    0x60a062303060a0b0315040f061202060f040305030d05011404050105062d0a0c0b09210f0d050408070218011202120703080307050712050901052d0a0c031713 69
    0x1d0000707414070fa4a43d4aa04207481590801ca41e16005403900c01c0e4868411700d0540101403c46d442c05200700001c2d030070710300d451902c1c51038004007900400001400344890113002003242c00840d040f00643c1d850f090603a4540c2c000c0c01080c81a2580107419800c0d1070418641442110f04885005140c5031412002c0e103100d4060400540c442c090000a074418039a04801440060880d9149661255000c6e030140c40c00311103164010700180b100740c0c00f401804c1d00d100d00e910440d113455284001c083d62103500e200030303400440c03182d00255004d107824807091000f0400c0c81c0f409090403610885060340700c105801c400343d1300304500340300320208150030803000303c05400c0c810b0002e1a44c0b000072080c0d4000341e07144d17101c500d900e038010f0304c0e9200000c0000a2a0080c4007004024206200b0b203464001d141011f9040001c04034091003151080b0b0b4980740c02040a181c06100e8030390141c540d420161900d403c4001e001401c038824143c815004079071166100c6040c0169200550310560600e213081c416400180c42e00011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 334056555 1250 334055305 334055311
    0x12d061d1512030a080915070c0c0f06050a030507030b010206070c170a2001060506032e0f140307050a15200610050f01020a06050709030218060a062303 67
    0x2a00074818282095030302e68610141c0807105510045607107009002d0010100320006007100055002003054800249608442a40000c1e851a002e4402222030818241c281c074954001c020000c98101c00140d0075410070050130300d44407541c50410030b03540c840300d06409807141c0100c01801608a4000198414011220100b401d40220b907180b11409960244d00041d500c071500c0040401c807400702e082c203100428401d00d00c02c11204070082c0051460310707020500070300003e0640500a42c03101e1400a0707a11800350600c40d4a00780e62800ea401d6581d8201019040685024000c80000400c845042e40e080c001901301c2107400280c0501805c51808014210110b442c040d1003042113041c01e030101401d01000152881b500ca00c1d005030a0f241400707688201408000e5120b24028500004007000e923030b8010905010458101401050035520311504444000081c0c200a40c400104086001c20001c1e0150980c420710042c0e90310108240c8894040e5101c24100100e55503411040b204000322441e820041c42d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 334057805 1250 334056555 334056571
    0x20a0c030f020708120c0f150a111207030903090801140a0e010e0d09051e06092209260301080703060c0210021b010b010914060c0a0203012d061d 64
    0x550f2a00c8044040c141007441169264030640440c0b038262501051100401540048008000c001d0210ba100211402c0c0200b0118040303555001c820701e142c2c0c0b20b00460f4039404c280e0000010b2443c02c02d00150050031081410b80003d0b00d0b0842c0032500440c14407950262490904c24a00e06a44001d00500500000c1100c60a15500e5803001e03803048504002034041c05416403242d488290500007803060390300e00340303907080c00003480b4104c41001c0f904c40004882400d0001d844801d14205405902c41c07007080001c940074040c0c0e2a0011040500c03e0841c04000101c2c1ca02d009a8403c04840202c4800d500080c007030102c450b04a00301c01c04c0041c02983c000c09804055005407500f03510700c1c42d00c0200301d130455054096400c41e11640e581d0361350002c0c411030486071800d090854915003840032180c40783c0c03000c01e07880303006110016880310f071610704100a11200e980207000f844040480051980c0800c1c0d003aa8040060604003c1070704112001e02135003080d1100388042502800b9444560a40484040c05680c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 334059055 1250 334057805 334057813
    0x30c041e050907242a05030f0c0c0a031e1e08031510050f1602061605100c05070201030902180c0316020f06011a130905070e010201020a0c030f02 64
    0x510360309207806010b202d0700000c2d0141c058989850000000c52180c0d2600b80207a03550007515800c03103074006200201c10700c01000d0868048042c41000c460103c1411005040d610011510403011041c5000500c101711b1100d00341c54041030700e80280004c0801a000003001c51030458079043c0310b848008c004507181070049116458113440e50143c44066610300714250307140c200000070000e003440c10400007042c16100751143d100d0100310000c02042401140111800c1810000340003d03041c019004c0c4100445d0010049585d80c81151070b851240085030200302c0303550007890b84501e86070000f4400e02203010056210709180100366801100201426101203030300a40f21004510b500060a0340d070f0384143c9803a08001d6407030030140c0c80060100000c071020b004540c402000324407075a201261190449881d205001c40c103003209600540135000d01d0082185180c40b03040c0000d000d9043c0d801250145060361981010300403244012800e0b84600783c000e03400b0400150751480060310402d0031117000b4034148103907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 334060305 1250 334059055 334059101
    0x40c0e0c13030302030714060f0a1d1903030b0d0c090c0c05060405071e0503070306020309010902060d060f090b0f09090115060c0b090a171309020724020306030c04 72
    0x1070203000d1615003080e00180d001068400400000100d665600c50074000105003910741401c401e851940300801429000d0740b9010781c00070382c008040c03048400c4541c4038180d90389070b4207041c10700d901645a0b05080c0e0001e030a00100e00e5241c01c200c0032101c0000d81025202444600304028071014000032071181d000c0092000464010a80030f01c25280118840c00c0984081845c000c040d01d182020508050256800101c08000390742e0009080011a079120a01507182c0c0d80c0c15003158018510307060f0107900500c0004a42a22240a6100505030381056204c8400d66494038003072000c40b0f55400c11150410540001810103251850f07002c0e03488036003400003090b105004000450a6203150703020f00003144c030442d21182084404040c040d413008800c002415030707404a0f258041c07400c1c4003c64843c2e00c050f0001d0580760b40307409250382c040608810342c0103655880c40303440c0c0300c80b09030064011047d0502e440740584404c0c980754000c4901540f401030091054091540400004241c021b0722400042c2400b501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 334061555 1250 334060305 334060327
    0x315030b07080907080304050d1104180b010602010c030515010315180608010f020f030403110307051f0c020a0302060604180b0106050a11030703090b030717010b21040c0e0c 76
    0x44580700300365603070b60200701c3d04009501c1440c1614070b0300b0100a5400a100501c000e8440c51810003109810980300e4500c5000c1c800070030001d101c85421008c555044807041030500c0945400c4a0403552503900811509000c0d10049003242d0f02541c000c10003400009800b01a0b603c240c01c41900c1c0c05050f500004040d0361120380201d440e80300f10803508031a0311072404104d00d01081c40707101d2150039000000e61804c100715001d171120344002031004044c420040b102450021381001940da14503070000032034040892081d481d40c41c5600c400064642e081c10405102003103403011450003940303a859001030000b9100e440810000e000c43c4000f00c080018000000380108140e40a0280241102c1e00c4c2c00344e03210450b140044c2a101541100c0c00f039030344100000000640d000081c0b108407501d0030b8403e40c0342e84400500311000d04d80c0d91180407030507070800f00100d07281d50100e0081002210030116540d40c0352074070307200d4010f06400f01d80c0a450f000e0801c03801c0100c480c402d088540d01000c0f00703011038a0000d404030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 334062805 1250 334061555 334061573
    0x1a0a050c1024030f17070503070305041a161103010b030111030708011d06090c16030e030c03010c080f070e0612060117041509030e041a0a06090b0406031503 69
    0x300c0c0075501c90300d55005058054011000d070030700d80c4250030302144403401d54031019074100d41420300401e42440002c09070320390840340081c3e81c2c2050788202640d0381c1d5201c42c01d0040140d001405009229800c18074040c088207110340840b0981c140c05a40418401d0790742c0c9030b0796900c62541c584247c02d9502c40c00c0d8500d490780c080c414615002e0340000340f69283e050983c0018401b1034140c00c80d18484d0300b02c142240520700c00d40c100d17950204046621880b16075852134062800e0080b1243d900005844056080070541c004400365200720090342141c4004128000f014203039038003842c0745000314038205c01140c10362040a0b401e562000607401d16411200b062800315940d2752200703407802e151021440900110b580e212448c0f240d5214044192507040c1040d488a44004180d410300d80c452643d85c0700c50700b08150141d101c0b8020700f04000e20420451440c011048004d54080d5080c0d4803a01c0e1882000c5034031303801949160705403000038140d1402c0c10304202d01a070050500c45009404405105000000148100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 334064055 1250 334062805 334062823
    0x1204140108070e0a030308010e0907031509030e06070b06030f06100512070503150a0b0301060308310801140a050106091215020a03020d0c02120a121103091e071a0a050c 74
    0x10b6205451503240c105101d07409000500ac1c1c4a00d500101c02c1000420500b208215620000b07501c006501c1909140c00e490a800100801d03401c040c0100740341e010301c5020101148198001d90030754a40d0114849110b440c2c40c402c03520a460034400c05028001402c003021498440c00b090b07804c552003243c4840010341341601d100300800e010b0050b807003041080600c50048200303508098000384509070641e0f075200818040c2c0220050700c00403c6c041d1440c140340f400c0401030450b00300c003034405659032a140b0780b0f4061700020310140040c12800d404510750002074402c045c1200c1d0700765940e00b2803a040c00c0c01d2040d03400380002c0c00e40d14440d452903034440c039404620090014540710b803401a55480051108010344a042080100390f410009030002d00c010aa021184c2104441c640016001d654004000c0140011030403c84a19804000c104c110f070340018004c480c00e07010b651010386010b008078a2941e960024001c0b64410a81c5208240d0f01c00c0c0000060000b9a520741481410701c0300d0241c03210b1504c1c00360 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 334065305 1250 334064055 334064057
    0x30c03030f090b0c07030e12071a0306010507060b04021c0e0712020307062006160905041505120a050640060c0e03060f10060e0306040807080708031005031204140108070e0a0303 78
    0x1030010001007110b00d460908ad820140461400c52605400280480c0100070029201e241c417184070518a68496044665a19102c040b580c1c15080d0003010303000410411400310700912950390081444080d54040002c0c0603401001400042e007004021a01c00807142c10180d04001038400d030320903c030014003007540715040c503160381c0480400020f8000d0182026500441c021842c02d00004200451005144d0545100b96916100000e03411222858414892000740007405402c09201c48212080d80e81c3e02c00036000a003080d1504a070700390082d220303041c00856a86078004034031428009202c9822194400d03007142040b0048500100109040c03810448007400c2d005510420000144503940944001c1c00d034914000140c80300243c040307030340c400d409003024040001c00300b005003c10080d48116000f05600c0110191039080092103041d61034a180540e501c01d0003182513000f83c3d10b1181041d181190212030818114440d44401542d00b14030250111040000c9400d90406136110b01080030300071031113 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 334066555 1250 334065305 334065313
    0x5060f040b180a060f050711010207090e030d050a02130e06061201030b06030615150912010c08071205130f060603080313060b03010605031e030c0604030c03030f090b0c07030e12 78
    0x8104040110341c0d0b041201403000d04c3c079020072416401016510301e40e81c0a400c008c20115a0030051785081711552009100d20700b8001484440742c4040080c0242c00481d08061005850b1a01031100364003d5030b0410181280c008010131a01c00b988681d0b540104000c0c019501d0f00d0060340c482181854240c00c191072070003042c000c2c04680c1c181048103562010711901c07507203030502402c0b0005444032071020f0b0890324000d0114902105071382e011807171030110745c1080080061458019000e01104800c6824070089041210380d103d001c0c005010300c074819128502c035002c90f004c0c140d917506015220715a0566425070740b03a50210024007610000c602644400c0e05240514a46141034026030301000005070280e41049401c10182d140020ba48000f980c01c000000518600caa06052543c09036100c00541d5118680a220a141d00000fa80480d40d01a54040c0043c201e0426410180c0f000444d00801d00401d8200003900081440064801144a0f1410100314202c0c5000148110390103070304088140c02c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 334067805 1250 334066555 334066597
    0x361b05030403200717120a02010b03060112110105070f0b010902130b120615070606060903230703060213090501091406010c110d0f0f140f0a080405060f040b 69
    0x1800803c09a07010b40122541d014074880225003e031500414811200f40c1d004000401c001c603c0d040c8005c001d000c00703201c016902c42401c041d009000e00301e02103605010303008640001c55010050821969890b4000114000d020b019100440f2035a03c034801c00d4481c0d2841010020005180c03940150081080240140c0c89440054400e800740d2095408259201020044a503485815005240d405001210410008100500f00c03030603d2061040003040c140ca0480041169500140000c09407800b80085036042c00c45444150b51075544241540010b9010170380c1080014416001400100003801110924564507002542a60000e82141e1011529580d0300004c102c0c0f000903c41e4400d100f440c240545403450341302d0309020325043c07581a010341e00c1480b8900a0040442c1041c1426a1045064203400c0007414101d115114249011605024000310001000d00004460144c44d0f00f082d12285064501f0040040b00d900c01c048401e01c5607401c0c00002071906060029060103640e03030b140703100601 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 334069055 1250 334067805 334067807
    0x1401080706030e0c0f0105040b040906230f131d031c02030105060d0b040207171c0e0d080a060806040f050f0102030121020102010e1b0901361b05030403 67
    0x149640041c41094500100c0c481d6078030000490300c01400d03098030305074003520904004a074944180d0704030860400700001c0c0016840f00b1684140e04503001082c14031203e800040d00400d590381440c50245c0c0c082489001d40300c140c035040c000741081c030034100da0009154228036109068100524a0950240c00100d0342120a09040e41c03024200c00c0100c100b14074540c100000a400c9004610034031000d5580c032091038060b51240d604a83c8803942001408503240c015000e0790b5160b50208000503440010040040303001000c501494203007000e10405081300f0040ca480031500210020884016640c850700700062492052281c607004a01861f200c010003411070901c40e18000d07080314200080d80c03040004102e5440c6d1555a4042070040300c7d42c0030700f2281d05000407405041c9500003034030240162918401e50a80c0c0c106486c3c91780300140c0c0d0485542ea40c1d181c5111000c5020041c208000c2c4415080c4d03044a410031412060010103403800244504040c0b422940c2042c801e1a407001090001007440141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 334070305 1250 334069055 334069063
    0x40b091c030b1c0302071701020d05010e070e030109110f01020309041406150307090302060702011101240603050c07080901110a05010203180c0a2916030e010804050304060c080d140108 81
    0x18440c0000328041d5581940e4000c1d07031500c0c1032147d004503070707007441c101c1e04450402e40450390354442c10348050003e540c603590000025501565400c0104003400d403c500c150a041c080c2d49070071500f100c44464103410f0340c2c0900201038400040e950460104205111082c2d6403032003440303082031120312504254035104050113600c0b0700e1034525003480201402000f403800c0d80601d11006503075041d00d620703495525610045e030b0750403030103880240b965003007201040c100085207200c001903a03000707124030031803d580d4007042c1d044940588038000390050802503040810000001011001ca06160001d4154003040e0000e05102c06900c04482c0d99400005200c0c0c80080d01d149130f1306d08401040642442040100012201c000d81e1080b41c188882ca0801180940300d07004e03d05801000d0004070540c0c900c000c1c0e0000803500c551003030071004075000c0c2c1c120101c01d500c41c82c8201d2080e64803000440c9058240703a020307600c00d4182002110015001c1110a003100101e01400f5441e81300300303a170307010203505003d081400c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 334071555 1250 334070305 334070329
    0xf090f1407082806172b050f1c061e0521070305060604060e01140907021c090e0c040501090e1512011506050c031b03090409050f150609040b091c030b 66
    0x707030703204007604a01d00c0020641c0038801b030040e46440342020070980040d1200e01681d8803040220801141141d035035803e542680e000c1c149491010040562111141d00d680289403402c8007a503040e40400780702c142420b181000d548184003c000620181003855640b82c43e900b078004072802d801c880c0510120303081c81d006032005002c101410104a41c103040f40e080d040038801c1c6046118003110404035021034003c0c004080e0301508540030300203071103082030050143c2035184a0901d04004920004001440d500195000c1e52016503c02034818030344164621070703d0010702111501030341c00e19040c0040d942c0001240f401c400210003c1400d40f000d40b120803000071b1703d901c0802800360400940610440c080115031801450000031281c07600e036018030031305c4c50040445a030340007484c1800308802d21000154500c4031014680171110f001c06103910300d400400081d02d545400c009514041000125080d24480d407000a01d011209042e011104107592000101d4180d00826926611a0941e00344401c0d1454 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 334072805 1250 334071555 334071599
    0xa08040f0b0702061614060c130803030c071205040b0d050402090709060e130e0709021215030c1002030d090b0106090909020f0108130c0f090f1407082806 68
    0x1090090640104e4814032540142141e2420012040010011040c0608040c99030100c1202c1d11b5183c003164941855219040c660501499543d00082d45040001120320a6020420450600135a50b44d502c80d0a074a421001c000d01c907081c0400305141140401400842041180104480c1080d00603c5400c80010f0214010803c603c00b0034443c85410641c008541801581c1c41c402242604501d0340080c880d1404401160044407400100c4118640141004c5c1821403680e00154403800b1080c606500340443c4c150300750300301c5e13a1504558039045a40c0c0ca141e00d014010707a03180c00700309580c4204494070340d4800c80351380c8011001840120b45c00525900500f240c1401002024440d80002e2062040844114104085440000c82d03401c7c007032074003000b0303654001c40f0344c1242910f8000c3c60480854034001d140e0543d20704000c41d000710b46207028250090402070b07407c0d40242c480d40030032544d0050081c1610904c101c02030350900800c101d45100d40c0070500054000801c10300300340d9140c0652280c600401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 334074055 1250 334072805 334072807
    0x105091b010302120c0310090912030b0109030506040201030f0e0303070f02060105030109231207030806031204182d06081905120a0c08030103050607120c0e130e0a08040f0b 76
    0x145454228413103a4000101c40d0909450f6a00c80304014508015900701e46140c2d070074508001e041111010400e000890161014400b150640d0300458810000e44400b4102d940000007003805540207510450030102980d9001c610030754642c00152460f401a03c2440c001a64807080301d210035418000c0c41c0c0905400c030000c2c091804076403681181c40c1801c5100c403440488506081c0c0003400108540494400c3d480c0e40b072619015141030107015500d08075140c40c001d00851000c1c0500200704021030381503400c00c2c05681d00d55107034050810b004002d03e00300b035a00361500b1010300300803102c4025a9612980a914082207060904c5400d0b030803c01059038440c0703811654101ca0b00010004200e910041c4603a03114581c4030340184008481b08212004054941d0714000004420303c03c0126003d8404c1c002610386008c80d445242a00048400c119281d40000320350003c141d54914122050303034074603004d0b030501098001000510394141641e40008868401001800300061a103c0c492030004140f181155 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 334075305 1250 334074055 334074067
    0x3080a08180304061103160f14061b0c12130602120301140907030b090c071109070206221406180d30151802042102120105091b010302 59
    0x10ba5070f80968083c140502248050940752003c042003501d590760081c0f5290f074421403ca081c80918064058401d64203036880081480300c150740050b40c28016410302c006002d01164141c11003031503800c490019143c82c000c48090500211441e4045e00020603008000c102161604c04044e10b0200030342c114505404051004016105e00703000100b07030080b01502c81c01441c1d5210041207008046269a50342e2011603070003480302182542003d003d90368854440402454a0348040000c1900120b48020042c2d2002e80021200c2d1054041140040000001c29140b42295914511011000b06800007240c0c881c00401540840003e491107100d1003010140072802e280310002440150000c100f01c030400c481d07400701c00a4545201490003844906507042151070485400f48259901521440006404400340030304c02074141e108032022140003442c00c41e100da2804864080c546040b44007603034015118a044000f200302070080b136204041040141000890b003184048001e080b072440a41014814400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 334076555 1250 334075305 334075351
    0x1120603080d111201140a08030909190603050f0c0102060105010c030f031a0d0614010605090a12240c02060117030d050c0405100521090a12090e0103080a08 69
    0x2101c421000031a800b181c01c10300402010300d80d202d4003d854060600031000003074140042914001c40d51011207c480f01a540c0c0c01c551030b500d004500c9501d0384075800c000460404450a203c44001c0c1c2080c1d00c0c00720f0466076a4071a03d0604071266030001031030304440b548000560781808018054034003402d00c0d0609450316240204a0300c003015118041c10307951083d849410342c242407203400e9103100829800c80c810b49071030150081d0624a90390208941c0007000841d400740a036043d50001403014001120b040c2c6030802c180215101c00d40291200646001a000c01020348058000040040c60020580c4102003a0091411700c0c143c1c000319565078214840002c3c1c803408000c43d0762650000c2c0f804101a29017030100505482540d00ca81e6120080e24071254150b03420001402000081e0000d41582034100c050142d83d00404403180b40c1150040e000c1c1100050350031181400e4a00d440c0340900c50661510b80030b0003580d00a07001554549808209000c1583c0d000c0d5036642e1201102940800c88849607131 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 334077805 1250 334076555 334076557
    0x30114150a12150510080d05030415020708030702061321110601080c0109050d03020c060a090b03040804180b100f03110f04060207170d0809011b08060112060308 71
    0x1112803020804502902581d6440e604500c0c060b04014042c0c0186500510303000604010206142c00058145000550000048400041103a1000000d00311518030b41d081117566502c018001c84442405952800d0040303014400f51150751711804030035a40b420100710182c90824000c0c40000c282252107042000925262140c0411082585100621502080c001d503040c0702810307070964880c0304140000406000000384806c0200c020f8868140c500d0702c40c4284107410381110000340c0503a201d9102128181840d50042c003120000c1c0c0707410310841d03440300454181a03100380e600b600c0420001c1818040001c2c0e2034092840c082e00d07070104100842e0b8500c041803074040b500d400c000900080202ca00e5041e4069040707100074555600015a50b1504013144810540107402840c0061049900115840b512502050b1410700d184000b082107440e40d0f8001c80e0f60240091110701c2c19502d82d0b0101440780302c071842448080d80907481c0c24640c0d2510100040001d00400d1840440341e0034448100f0106507410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 334079055 1250 334077805 334077811
    0x160b040311040203180a0c060f090812030603030f072105030f0115020a06060306060311060f1206040f020c0106091a010905060c01150e01060201060f05010e12010605130b090105030114 81
    0x550b001d61241d684020f64aa4420003c031000d84500510707012604106568a281003a20400d480740034040c00443c804903503800c07140c0140600c03548402d26401907001040c007e168040d80042c1220b10b8188511a910019086000c044980071940d540c0080200542494040541e24900d4880e047d881d00c010143c16620381031242c4c1d09003001c04103007014054400d000340d0000b03640250b414402e03039540b0300e088401441d842c0700555444100d4a02d418040c42c0400485514800009005091001040789401810702c017034922644640d4401340160583c02c240082c08080d180900001903c4d0310f0848030301d0980f5001503032061200e18500e8542d886a03008405401558001c3c0e1301d146d16801c10402c1a4014284258411420320344094001102140d10804a040c1c44c03683d8020b1068a03611400600300c80030764051203012598040f401080d07410720801d04c0320096031900010501c9a52900840c000c0c5015105029280c1d0710b40344c0060b1076003000c216403801000c064008000303510110142420070b40000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 334080305 1250 334079055 334079059
    0x1a07020303220909051c080702060103120e10031505040b011704230619060e07050d06350c030607180b0d1a0301061413020f0a02160b040311 62
    0x30202c2290342007925070001c01518480380100140b42590601c1595031802c00007210020303149888021038148643d90180c0551f44503002000c541c0d08555440886c0340c0780102180c20442c1d50703000c21940343d40c1e1504500c00c8a02d680c0340014428603041005650411581180d80600c0c10148110402d9a004075010703641446801c0f000c90341d89807850010000d0b04c0d022040941c4d0076807030350144d08010700071410f14000c210b0184060815010300c024181034a0882c42240a03005140740000c1445014000a1180d8210200f00180c01c945501030300030b039140900400c0104c9403210b00e0984074140c1d1118024080a007a40080c400024090006661080010a04030801040e184ca02400341a5400f42c60080c1048000c07558454284c03602c0e4400810070f0154001202e880c0c0303001307868503040c113105036401d6a01404401c240c01c5132400a00104002030750003414165400c11800382c0f41071000004c0e01d034a4030682c0c0501a01548a0f020180c10009604081e02c1e1507810041000040d011407641c0600001c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 334081555 1250 334080305 334080337
    0x510030804140a031a0702070e0c04030f030210050709051314060d020625021e010207060f020f0609030405030f07081f020405040c030e1216020d1e06061a07020303 72
    0x2d00c01040d0864256031004000f2510400e40d010351a02c00c03400c59126080542c21190440d56400c0034200810007546c1400b2540c004000a0020071164203880706864082c1c0111550b0b0606089200e0841e00c044410380001440f603101480b8520b400c0309400c20880501e0010b01902121020503805880302422040c41101401000300031074440900751607040c40444940c1d1420785a005505924003040741d0300300d1080c00c102c0b518a20701c42d14141d0354003408006030300801403a411321509541404040c8103580c15489400c5801c402001e08002180c81400010045c6850b50326007000c0c103140030f0f046014042d0303581044200703000c0c030840059017801d50000c40703000c94160380c1c034001c0d20002031195400107500301341822544c40c5081d805400c10707241c0c45283c030110703105800740c459088080c0c0148101503012001c840f0680c0054a00707800000d00031340c003560b003000c00c040c00921240d0190b581d2442c1222441d8813400304002142c0841041c481040070b82100034504040c4d903000030349074440c04140c0c0d80d100718 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 334082805 1250 334081555 334081589
    0x6010201290f0316060206010501051606050705190306090f021935040302100b0f04021308030714070e1302060705010f0c050c06060a050d0b0406020d020a080105040510030804 77
    0x10b24840c1440c40d0880280079a521030300c40b407521180c2000340d4083c40300076102d00000068594840c0040b904007520074040c556840c03001c0d03501c02d005000064450300c100941448074181400c44080181100c0c0807907200065803a00e0f094071300064036400100b202003036106121030080045114840803281310a464259625150301c641018150117507a00011104a00040c0c1042e03254100c440c180928003035001c542c921254a80800252020040c3d03050b08903e802a10800d039041070b03000b500340084a4000c3c5903000d81c513803407081d207150060041a507030b00300048910414280d041c00f900002d00303860700507503a039850024100d100006880b5002070041d100051017005003d400e510030045510148402c7c4054902180000c11039040000402414090140491500d2404c0d2620004443e005403541035525030548400c00c0705417004100703803440e540801c5294031914840c40180a0103600f0f0711031800c2541054203000032900018410580d40003104403d201045080069a048640d40d940c50b003a118 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 334084055 1250 334082805 334082809
    0x7050112023016050a0c0f05030703021f06030b2d0f0106020f0622030c0615090b0105341b1d0c0f0a030b061606050601020129 56
    0x1102c0d01c5291800300d40c0100305032407090200c4208501269032946440502e44440400b0034074801c074a50b080c8041541004a0221607004046a411032070041e083c42c1c040c7c800d02c0c2c561900303661086c8011401600805c0711203202010801c3c1000007840310b41c5081081c1815075803544846540a0300d01c07041c0c1d101d0b0b401400041444d031928005060006904d0081070300b00040c20611b900c40a005800c09030007040c00e607442400c4001a524850501b51614041140d20603040302005603a0540a81c10080704010000108080b030046803600c00100701140504e41c07800d203004044541032200f20741001001c1003060512000f11420400c03403a1543d8100111001c00a51700d82a03181003c8010050102040c000d0ba000d202d03803400c40c00702e4000304c9180f002095401210f1018040882e008201403805000100b40d190401d40608084a03071414000340c6c840c06180014410b03084540c01d029400c0b0141854000c0012070301840c0d40080e0203000a012040310741100c40d8a000020901e002400c40ac05240800b41e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 334085305 1250 334084055 334084057
    0x90a11060711031c080c0703080402090601050c03040f0501090f1202090c1c050f161407061503081905040612150b0c0303010e090a022803020a06180f03050705011202 73
    0x41401400c503100e643c100d04c0d0040301c100c0440b42000110b496503001600c85c81c5100101d484180d130540c2c582055540d5503007007191140c030181117141041020300644010341800c00c000c00282c600076041554a030701e8030300010085070b81500025005280000100420358a401c10142030b030360704480c030381e00c99900c1c840c06e9192809840e990109803d0744482c0a080c2814541c0070340d000d001c0085044405a41d25082002a2518038424030006440e00010382640c602d030f40301801c10306121361004102d030244418018011030443d0030a480414002070045400e007040440510b400500342171560a0524043c030107081c035008016034445250310348e060005059842d84240340644214a002610b882c200c44400d07a40c0d40003401601411603024021910181c00003804c0102603a004048510211140200b80c0720441d04c0c210005540003403030307000f02c010395030301f2222005030546507103d002d4412031021081031804950710140700c0214840e014008180089040c40c01e40d0000c0c200001c10740d900300d80700002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 334086555 1250 334085305 334085333
    0x21606020313110402040501050a08100801090b0105100305060306160504080a030504182a02011e0c0311090d0b070c06090606060801060201050618180304030812090a110607 76
    0x41a10010401c401c40403405000c10b0118082d0901a40b00c02c11602480f04034491402080d0200b08240000c1ca44588500c0c0d215a10921400501141c075503030300060750a441c0c0e8083c0c1220301111035030040c801401e2151000b2241c1c0c0d0186024046030505d80d0100e40c132070300003a143d07014400d00f41c2640403841c0d0048084030000d224580440d102040c1c00e0500918a4002d07000380c1d48a100519140c0c0b002031603e00450b840c14010300c0c0c460001400c41522803141e4807810030403000f55500c546071000c0c90012295807680c07004480e100800c4030b45082200504541700d03080e110004140c1485440c82c5605e4252181c60710340c2c0d00a06460682e100e5078801e60300b2181d003480003811242030004030020041c460b08408225282501c6100140e6264001603003a2203088440541001c410f060070116a000c0340c0c045a0400342d41740008905112203e81a42180d1294006842018000801c1050148410321142d80040c0b07603000380040f280305546103592545803020281c880d1401042d101d0504c0341f10210104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 334087805 1250 334086555 334086563
    0xc0b061f050c160e060f010503010b030c070c09050f060102070828031403011d07080c030f040212030a081f050a0b0c0102090d03020f15151203131211011701090216 72
    0x92035403003403051134210080700d4079405101c903400c003c5d8140d4094811781e4107076081c2d04d45041c2142c1d101c0c80050310f5500b25135025140004130030f10000c0d44d50024400c0c1030040d40300d0010031805282000002e49044001d81c0090352547c89006400d4000c03000d076582044102e10300e0401140010181011992800b10a200e104071410000000403080350440d1300040c80c40d0058200344080d6100e40c1c05035010030045980405406040000600c00d12420300c0305640719100402c070721070310708040c0c417000d2440c0c004030000c401261109041c401b028003000b00d000c01c042c081c0890b8490075030905000c80c06080441c840c15644250200380c00601c1030082d0161502c0b210040c0c40542201c045080017942c03491071708800745d00c1c0c1c05200c0303100703950640c000020f52203a203500300d070203283d415214240444252181d0340704c00c00f40014454501508000e1400800400003080d2040c2200c2c8241401d0048042511880f0b0500100030682c0c1105d0b00084107450440c0c085810043c3c849440201d5079250103c1c91800070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 334089055 1250 334087805 334087843
    0x813080609070f0b09010e04020901180b040302030601151403040507051c060c1d0d051f020306011713061107020405100f0803160209250c0b061f050c 66
    0xc075180200055010864260b49100601107550b000341108611940328120b0000d41502401c134507031b051603002441684d0042c9083c010403854012010742820098000c4262040300103005c01c2907180410105005d400c0c0100141744c0100b90700009454400e080c0c0341e43c3c2c40c0100c0440000e050200074800320004000152440882c1010005e0b100d601048013641100e10b286005643d000541c030400213022003103c4410205007a0210008200c40d00d8000c0f407003140c0c20310400b002c00203004203101c0807401e00420402c0250b16400d0140002d410801c038140030040c0c40d04031a00700440c0401a0f24a8041c15400140c0000c0703001400000300f41901ca0007a019400c60308000c10f001404544011203821540919210032466403544503030780e101d00c20080d0361401c5401d913103000005850001c2c10070350800510034004c007088941e121411713040f040014030100420343d04440d800c18051044000703039108204507500c0c0076000010b000005007240c0148040100301d4049406403500f502000b07020640c3d10307020303544 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 334090305 1250 334089055 334089061
    0x90b0103110a0c0512030c070b0f040221161d0603150105130204080102120a06080a020918010b1c020102011406090a0902030f07230402250203070902030c030403090b0a0c08130806 79
    0x801c805508c10710007102d00118800c00140e0244489648501840d8014000f68803002d0708070b5154640e80180455103003a0051185105000c01c168030194018054004054a500307840c00c00300150200007802d86019400ca240c0078004d100d140380465065410447d00340f80c0041700224010001e004503081503d15600c00111980054203ca140d54800d4201031024000b8a803160000c5e501c1e80e00c010002500202210041031a10350b08403002c031180c09000b40006032070302d001c800081451000882585141d10f0304580e8a0540d40c1c280114460100d4811100c0814245034001c19150800107000d0113105940e03000000c01c6582c140100c0d1f81d481060b000f100d01891301c0722740c1c50030b10f208002c07000c02000c6800448401e00d81010700175210300a0129890400c00041c0410030342282c00420022681801a10300201d404422031000e14011282d01040d41c1d141d01d01031501a1511a0319081219018014009150b001c0c0d0f1211030540300e15808140b182c1c940c45485a8612071301055000500640595020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 334091555 1250 334090305 334090321
    0x90306020a0c11040e10022d030a1107080415020106050a090b040f05040201050702011d0324090f10020a09120303200307141b010e07090b0103110a0c051203 69
    0x100c010900401ca001585800d120801c0216070715540414400d0300089120411b82c07083d03501510b03101c040348902050204c403040c801d450502c0512112000c0c02004024003040b450701e840360b500f4007003200c84030b28940040c3e0388a900c1207000e0b0384203003400c1c043c18405035503d10b0300c05c0d00508d00810780541000202a16060309101030003592032958091403a00c0d0351841c4503506805428016034068403180d15020240d001120200b00c058400d0741b00440c01807600c0c002d51001c00808588250126a030843c3c0003100c80a0784d09000007070032180b11507005118854541e40007040080310304c51515401030740c441038040d003070b1407003c07240e40250781c2c801da0a1180c905140d059042960044020903100c2070000e0303000051010b500050310f031a80040c100400480b0700b005c4800081c0601c0c01d40702441a9078584504c2107900b9902800c3c00150250130070b031000c00541c0390030300481c0768549003400e00f4040050720000790713041d034021200048200400d07482200c0c24400240109800903109080007641c0e403505045c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 334092805 1250 334091555 334091567
    0x705010f09060b030d14092707020d110c01080a050601020f15070e0901140906060910110d09060e210d09030320060f04060617100c02120712090306020a 67
    0x20050180c014496406007140c032951100b140614442100c03810f06043c0c006110101c07008c504a8000d482c0d440c032048481e4142e41107403e205003030b154020f04000750204802407824100c1611544158810000c10b0b15980c2c11652055110818100018840c1c0e22940100c1ca00318415a505040e802000080c03c10307041c00403c042d208062a0f180c0340181402e80041c007200402c03d00ca50000f6801d1742c0e0410701d85192040055400003401004d081c1040c03003580c001003404003800c003400045002c5d40025416004140329411403a040d6007881c07038003907291a030b0140040d044030740c0d001d101d854445044200784105000c141100c000400c211500e1901e03084019000e02080c3c00140c02203840e10881c0c002e032a840e1100001c92841050103000341e91940600c1541025014000702ca0b020785640b00400c140154000002c0c3c189035010080250310400211801150001d0520307104640000094503036040303c1c042101c5100e81c1c041d00116480411020403103200c4515080104800c0c00010f104058a80c011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 334094055 1250 334092805 334092821
    0x40b070309061b02030d05090a02060f0306131a130e07092a08011a091f0903080a0e18040b010b0a1707030c02010e01050f0a021b0a030c0506010e040201050d020705010f0906 76
    0x6d401046940c80c0c56010301d44d2551100740080d40158200843d61949035081c02864005502901c0040d0004240355410f06403121004000c0c500812504e011280e440c0c400703e401d120300408001080002d460403541915000c0b00e0050344107042e1600e503050041d26400b07441045041840d40b2001700c0e0f081c8860000c000e101c0a00c110315800c40c5403c414040c1886003821101141c1c0001c01100c2030700d41031910300c4401c10750f2819038803e10680403400004903c542001300b5018119507610310360690020101300c0c00400d0704c140005022a0081000001041e030441c19065410704c20b05030340c0b56040c604045401540b10794812540e00c00d107600340000240c0503008001050342580003030016000d02400d490807a2801c030342200310684c0c1c10001c901c0c1007170150f000304803a040c4000c9000b03001600d1340e4240c0c070b0304001d0002200051b071030001c58014440207001440c050042030066040c141055000240a0f004111103007031016400500c47e81001000d601549986030384000910a50381203080c6000281001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 334095305 1250 334094055 334094077
    0x17160209090c030d090b030f0702010f0e030301080d08011d09030f0c01050103300509040b06030c1b0a030203090906040902100e030d02030405060301140f0303030a060504060608040b070309061b0203 87
    0x4d0040080160301031801c11040c1d9940150403400c42d0340b0b85844200d412805452802555685c20041700f000000f07004260100b869400116645c0d450308401c603140c000c500c03801c0700c104101440148400305124460402c201d030940003409640c0ca6040c01a4214840d00700d03110344613103002861405c0400107400080c1200c1c085c0f1015425804411316288800d440d80d9858613050102e482c54001003400346c1c003c0c01c61281c025100240d41c0940c0070200f101540b06441d90460f810010030340304005082c20001020181e0004041c0503200301ca030703070040d583c1d0082e1015580b05000202c00142c66440c0c0c2c1e070090040030380040c01c00c2464601010702030300340000245c82502a00071b8100700c01e036180c00002100d045440140c00c6d5441c40c2c0c42d00303803824202c1032581c0415902442403200b0900c582e408001450140e17060803000104c280c5090200400c80d040c5500a8003888103000c1000b010070170503206540d020059080104041c19144ac24000600c600300c801c03030318000390302c0001e180301c4d90000140c900c240b04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 334096555 1250 334095305 334095313
    0x305040e190b0114070204090809030a0c081603030f08150d030302270d030e0409080301080d0914060307112a010e190303050a020c040501090f0c03060317160209090c03 74
    0x44034004481c10001c0316044c40e1581c4007000f0002c010304281d884002d2044c001e91034142031801950002e82000500b210a41c0c4922040205010798981402124890850400c0203007005146503001390a40c04400804000d200c0e0050000358003100c140c54210240000401c00c031160030403460090003d400000c0d68007442d02e80788101d0380c600011021907580c0c0407030040800d0308100701c0f84c0e01200d00303104852000d604551070341d02c503000148003500a54040c0c46400c020f00742c08411032500500020041c2e01508980311001100307222030f102c24085030780040760351502c220000c0d004144c003441e2142494401e0428200010380d1034a801002e96000391040c0241d9449800c41e040d002004652003911403144e502418280003040002d0141004141c421034078010345913041a00000981150320903800b180e156a06c030300c8099141c0b4000d108604000d01d0a0404000300c50031520341c4400d550003c10310030703041c010014404101c0e2008484c84c001542c5d0042412070603190849941c2d480d64000501940241b20b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 334097805 1250 334096555 334096571
    0xb04110c15011818020d0c0810050f0c030c1201030803070e0609060405040b010207080d051917040204200f1e040305030702040b0409150c080901020c1203040305040e19 74
    0x24241994504941501c007046880078080800345008000080ba10359583c07a055003048010385802c86c0030070070640030b030460f070a900e40f500e5560350802d885081c0f540c1101d403400d420048013655040c0482d030085140503500e07881f503403154060346552007480381d42c04540800e04e0000041000b058002d40c070880c800d584580119914909111060058180711540030380c0c02d20007882541059440114411070510440d0241070380d4134025818400c2c0d840c800380c002040007031848181c603094101080502901c0c80c18580903400403c850980d26009000284256100c05801401080c2a0b0000b816201c41000b000d5548001d4040030103580d005c41d0b031180b80f05200c9111651810320300c5c015a4112904900550f18000490b800c10009140c1002203507801035a41500d070010a00c1d208010083c400d20203000921040c9070400501301d80340090072080181c3c0101b00c00c2200d5000400d00284141c0e5483e00c958407600c1d1450309a445002d03d40140c0c1c0009604820001500f49080e05448070703807905001001584 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 334099055 1250 334097805 334097833
    0xc080c010c020f04180b01170c06090f01080a110406090f120c0603020306030102040902040b091810090905010f0e030d0c08010509060f040e1c0e0f01020a0b0a0b04110c 74
    0x101c210901950060001843e85a0303030034035401586900d1260315914014481c0c554403948074140031b07081204120790a16580c4d6180e4010410070305501c030210780d014101100000000c15040d0000c280b181002454400b190700c4074515003103100d081120084490702ca948481c4000c00c10b100d98860441e250022410004180740c0e1125107030000703900b051224011508240e025000f0750b0000c0c000c25007665081000081e80c40e514400b61010303000685003959182003410030404445c50034401020180000310600101424003807130f80b0b04446407000e02107200c056a00303116004003030030100240010b040140200c410300c408001004541402e0b08200051404907004440003c000d006844c0c100c020340001c618203141030540101444002400410840700610f01c8909180d50380c0b000074090f407070034841440b00741d4100548404ca100103072680101c40c2c00081c0000c1d0b80c1c5007801c4024280024a8012409400305034201e500308000c003400900c0201c501d255a40d6143d803009a60210318000d01c140382c0d19030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 334100305 1250 334099055 334099067
    0x1020709020408072c0a2c030306011b020301140f07030b01020a03032711150702030c0d030c0503030108030d060918081c111e0a020a030c030512040c080c01 69
    0x41c0e5070343c80040000300d081030070074100081c5007401c0d2440c04034010f00c40f01a500d1240c19140c440c130800748000c40c03e058042c0201c1003c4001c2c241c0d51440c9a01c42c0c20704607101c1d00c0041982d41c408000d00c0d0001e1807041866010f8481c2141d003401a4040d400c04055000340a5030845640c0102c201507100a901d5407240310407811130b940043c03143d0040e0440c04104010a00c203411151060445a042c130900300807515180c000c24141241c11100d1850301c60020301b140c40c0c1884002c40010240001d14a00327030440d400680c8070a2104c031090311650760050b492061601c144454010140d11104880e5207507110a610b035a6070308041442c4e2409420014041440400da004004141240c60340240143d1000d564484207074000545511000101943d9188100194000c98a81980007202c20707603141a42624070708143c0000c01503083c462010019100200d0780054401d141036010f1401c072070008043c2ca0203c400340b09024411000401c0c020034002407200e49504482118404811504000c0c0450019601 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 334101555 1250 334100305 334100309
    0x20d200a080f0408040b1209100e0c060706060825120305030a110d0213170a0b040f0c0506030a0c020607020c0a06031d0a031e03050112061a03030408010b010207090204 74
    0x4103890049a85a42103205441d00144154513040c01d10381c43d00500d80031500f012010307102d500c03502418409010811b11103a0780e0074003076404c148004181c43d45519583c026038001c9a0290f540010504240320303143d07202d48060103010095800f41c0039680703000c00003001c00201042c6105019000010704c807035000304002c140342e030644501d41565a05a030100c0208850b0300844150b0380104040400741c19544020303c007040d000d45903042d0300c60030f06010b0030324480c0c6d01d41085940d41c45021035801280b00d8054141d80030342c2c0400c0420700c070300c900d1502c14100403541c0c1c421904080040240290401142c2200d250445503508031102941d078800100d9a518683c5407254001c02c0d4140c040c000b40344070350414445001c3c4408009621104420940d10301f421aa00980010321440e4001c0903144032481c059801c0107661400b0f1110f075040c1001300c2403d17910414000c3c02141e0b500c5014030005803111444941c80002030680751515512200c80d40078000b041481030042c0078260000c14911032074426a42 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 334102805 1250 334101555 334101557
    0xe07060801050f01020c040606051b0f03040524031801150b03060f280f0e01180f0906050c03011a2503090306060303052808070f12020d200a 62
    0x9400c1e440c02091048008005030321504601966551000b5a261401031400804107981c603940d5502c2400c0542031000404030300306205801c07600303001d0514440001550103444044801c112003802101d18940c401041010b003902c60a801f0041241804100f8492246050b04200a01c05040688410041c0b15417a0081c9240c2c0c03d000d102041e0581800110880049070140241c0c40d448945c200740c2444842c1c00240d00920b1207640428480c007008066854001c1c02d8106514250b5410601c0601d0504149145829082d9452110005003441074001500c42500b08904100c1e90030b18034040c18190b1f000740506000c0014058103000c1c81101c1e03c0c01c4802881404428140000c1410000ca0802d1361240c0190200040c241c3c0c0403001c5456403084400851003a1030b1159038044600c0b400005090041d02c0616900605210b4103166400501e00c66209500e0f2421254620358232105030b0302d46000c0ba4402060510108002082e55166030285212803045600301c400c0481006080e080341c400c00720b00c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 334104055 1250 334102805 334102817
    0x902070f03080901090f06020901030b12100908040b0313030e06121311031504020405060d0807060b04110c0606030c0d1a04031205070c17130b031b1603030e0706 71
    0xa00464852a401c5030003d1040c0e0010074501003d131036a1900d915090000d0384c00e80e9001601d000b41d9a0144207100e10010155540d02d400c4645c540503d440b1810040c00b071081e01d03107070110340d803c0003504022140a094003201040c3c03207050200080c182d000e4445000c0f40452590744840800b45007000588240d0108283e0a01c4107270b8856503801c02c04c8004d01c808a80e10f010f62019040701e554248100c50590300710000160461600d0f004100940314003402d07180c0a4940320300360001198161080341c030346940003407010070ba60f00c02002090040c01c1c5a04020951140810382095400c004a142401010300301e003180d80700e0301d4010412003905082c8000500c1c01a001006210380e0207106c03500c55009001e801c6c4100e0800e07110300e151096510494000b0001886011000100b045020b00c1521240c1c41c94105410504084c83d80605540107000390180950301200003225910004000e00d07044400c0d0008a07202c01010211440ba030300c51100441c0460b00b01100032152100001d1010f08480950383c881c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 334105305 1250 334104055 334104083
    0x2090c030906011a040b0d0e06040f060c0f14090a0f06030e01150506040e041509120305090a1509110a0801050601140a0c0201050a110d1d03030909010e250207050a090207 75
    0x8490103500003146100b1f4991203c800780884442844420310490080880d05a1001c280c5003c0c41141c20a001040920180a00e892007055003c40e40e40e40c2c246a46007003603940e5094800103040380400d41e000c0e0032008032074280450440d500d030f0031030100301001c98020322000080fa501003011203c0d03406000d402c402c040c00108043c50802680d940c109010f41320b18a41021007031298004c0e40c000034015204081d0001010089662612032070381d01c8140702000e800480c020350740b00c0d010501d2526144107040c0c0c1340c103026010f004804290890400c1c1c020401e001d119075400d8040d020f0101114010b021030304e009080c0d14402d1102c821079111000d1552980343c403c03291341c01500c154000c4524001005848006050982d008003c0c60703800e512251542c1d12140505440440302a0840270703154020340060001403c20703220040c5150540308142c540045560b5030140c200c86411100e002817450341440c035416400c0b2900032400100340c4506903450b0340803e0301c43c40b4050503449502c600403c070595050074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 334106555 1250 334105305 334105319
    0xf070509010b070201080c0f0f09010908030307090b180d0606030201020111070803010e0c070f03022503020d1509150e0c0d11040903050c01090b010e060a150c0f02090c030906011a04 80
    0x20741b07076110809400c02414a081d07586a4a007070b802c060b4009115940004040d0002d60300584200c001f0030840780298607601e048503000349100c8107441000001c00c00440c05884c403403410102c0b010b0000000c2d020051030b4905041210184c08588400d84c050752801e01c0710785596030a8070072100c0898005641c1c86c0b07103901c0c005010743c50b014010300100b0086400d1002900043e40641e10b282e402d4002e5000741000b80d001121032488481d854940f91051004038810801600c4054070350b81590340000010756140e1207071880101415042c0b1009105668030781042003040c08580c08000441d00c108200c481140c500000c0c444405c515100c003034054000c50940840919054020f140307072511074a001d600f861081c000369420745411000840e401c3c0aa400144001004164036661180080380c0b54450240703410410b00d08414007003010420885001516000d0042e02649000381c59405803031180313a80b40c8a035208005405c10344110846000b044000034102154031400703000c000300003240a03c1c1900d4104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 334107805 1250 334106555 334106567
    0x301050c071b0308030903070c05040b03070317040b0309150f24180109141609051009051306030b060405040201021209130e0a031b03080612011404050f070509010b070201 75
    0x40c8002d89880c032920040001904c010155001e841e2240043d42c03030b600d0510707020015440784d80069008c2c0307240c019545043c0d42c0002d104011207412403200003020303002c0f00f024001403082d80c010214855000080c403200010004460855580400040b01c1136121928002a8103105441ca1200b10520400901c030b2486c00c55109203507800c000704011400f44a011039110102d609070b00ca0741416030346603c164410300d41140001d900c00a0180100a8107000c600c0c00b0340036040c00d00445005552845880000501642740d4201500c0020401c44464a42d85541c40c054511408211b035500c405101040c00307030400c1c0c0102e5004540c143c015148180d94101207201c0c5421801107164408110b40070520750703116600c00e00c030312040d10502801c1550b07500d04000d002c41d44403404030034048518040090200b60300600d40d5130000780850310042410002c02e4014050818002201d440300c2e800c8080c80b041080024201c02d00441c144181c541440da00c100b000320140091050901c0e5040c2000104011340c8540d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 334109055 1250 334107805 334107833
    0x601140a110a05010b03011508030f090102070314030d0b0438090108060405190314071a091b0f130f1514011d0112090203100c0305040605060301050c07 67
    0x1290149000501044140c50000440b1060351503035940c4444240d90b06003802510a1010324400b225601403a01c42103075902e108403807005c24400400b0544082580c82401210300440e0010060f810400c0c21410362601c030b504c141e1010307403510b00c3c1600c0030034181460f0182c1c11480300c4409200821a00c00c03100482300d428801001900d00600540700b503115514942458081e0480c003008120600d003e1925900d485c0000102090040081d00c80c03800080d4003100203d039807803a8485480d1994494605036401111602803c45040100006c00c2030569001503200444549240034201000000041c00b04200da00188540c100894070240940352040341c0002c040001040000150590150742290943e4043e0b040392442c01581a13902580f0743c0e200c0e20207006140c0070041003c074940450000382031131107000604150552540121415542c00b40144d011000058a0500007080f1402c4024001d00d03040b14100c400701c1c45d01e400301e056400e05204051047c9075040e001c5282030660340b1800d891a02076 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 334110305 1250 334109055 334109057
    0x503030d0f2901082d04051213270606080601180b1614150f1f120606030c0b1c02120408030c040f0312110607050301050d031206030321050601140a 65
    0x80c42c01201c0171460742041c0e00900400441c50301c642c282417403d141480c2e03510941c5d1184003014400c000d0a4485504030340d00701da140f500c800c248c440904090031f0032103020100701c10b44545081c0002681580150003e0b10070700090f07031041040102c100e40c40500b6043d5028541c6109800d0210402078540c8428100d040e5004004268004100b918480d03e000c640842c102032041b6010148240000010f46030358121003480441d0244480c41d102d510310465051040760342e00c0740095140ca0902c174840c4c2c407113000340d0340040c0035103516038132424411015072014580c460003110981d44c0c0e1540640d07500c262004103980d006034084688032900c502c1c52a8001401d9510f580c0403c0100003180d90314a038005e00103504c0394006050a442001e0050100c00b5509224802c3e50031500400c62450380c40821241981e404892441c004200d5007012144041100c0903950700d1454060007206250700503414070754100464181100b01c1000d49548002c1c2c6900ba50402e0101d110b4001540c1c140013020080c18003e051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 334111555 1250 334110305 334110331
    0x12060c0a03061806030c0905090a020d06020d0f060f0b030f070f0207090c02100e0d020a0b0a02090d050606120d05040b070f08030709091a0105070f06060503030d0f290108 75
    0x100c0003420280b0340303010b1040d0f140558800702001007000141e0194011308042004014502e800109541c56901c4928000e00c01d80407000766808102050781528210b6104107000c00c40700031103030148801004240500ea012107001e010005407800307804112071240144d40710f060390a494030340041d5143c0807007900d031005600034a0720214005400e4400c0b2802842c19a0050190548440000b81280c2803001407160f00d401800da0848443c4c0c00240706103070140e1016007600195641c06802009020b00096264441700c0b40320a42c01b880000a21540503640480b41c440040c404810141c0e951550b0241c601e0104000340010044405d449025120041c01001e00031035108856a03951001c0e40100d4819003c103071090302c24810304102d4400d15081501d2158000355085011001030b08a00a00c140288201010002c0c18100a01ca0f001700d0b00410300501100c0d21019813010703040240003464542d1481d545400030300380b066500c80c40f040211742c2c015224481d50380010001101d00f000010081c10780701c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 334112805 1250 334111555 334111559
    0x30d0902010e0904240c0e010c08160501020d050901052401090f06020a050c0415090207020f030a030f030f05010b0406120b0603010b130f030305090607050c031902090612060c0a0306 80
    0x4612100d02c3c812885081da44040c0d0030941007410170b018802c0c105264861a0020080c0015088091405004d5003402c155030182003601d81004148280303095010000112104842084015000b8000b0f44104580511041d80d595012600320f0b107080b075038070480742d0716020381c80740403404a0403401c3c0b140810715180d46a0b43d101c414518030404164402001079002c400c040b010320a0500403610f210108032014003944480100f1700100c101da6004030340d50035600140c00821541c541c00c12689007200541230310b040c0d06890078054503044020114001007400c000c1d00c00304641c920320420303042c2e403c1c10140504142c200310044a40d01c400b40f440010040d41c6915420b910343e03412001d14000c0c418500c83e141d48200c001c6485056141c00d43c07201500740c00002c010300001e5004801d41e500340d007040d104641c5420440c18940c0c541903524024035094001d000780d00241c2c2c0d0164103030309012402039a84000380e860f480c06010408494648844858004002003222846d94800400c1800f00d13514010034803903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 334114055 1250 334112805 334112809
    0xf03070614120f071b0308150d060f1401081c0507060f110a020d051309020c03120403080a05060904050c0609030c120105010305120c0c06250b0103050601120203030d0902010e 77
    0x31000c1e5855400f0300c0d00da40c2081344582c2e0007414003140c201031901c007440004440d50081c0540c200a41aa1b001c1c0d100f000425000f038031a207544005480d0400307000e2044c080d01c181d48100610884000c05001903040b400440c00380310009160301c4264a00801d0045100b64600489150300101b10490310a07032508543c0d001085280a601000041000f101b540c3e40200c910180ca407080c18105a02804400d01020490078070300001d010448403e500c01580c0c41c0c0d0403521207415449520580402c0c20345007030510003495403100480d841a80351003020400c540f00e000400c014008101d800070501c0c0d0141f00340b07204d44d0070000003404516001900306c2c1c0700c2803c0306001a10320850401d0780c0d1981c2c0e544500400601c08100b001c283c4907006410f001d858026036201c1a034658a00c20501401401c0005505503901d400302d000101680c083c5d500d01c04030810501d8108030740389082c84180c9103072054500204d0b440c07506004d01065075500400031880d01944d03440d800e002e89030103d07040e0305000d5001c80c841030301d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 334115305 1250 334114055 334114087
    0xc05060624180910030f11180c0d1a060703030e1c121802030a081317010c030606090501120b0a050343090b041b0c0506060f03070614 59
    0xa10340e000c4540c100850101d00784144640d006001030140c1081000410108a03a41c42c450f070051f8014203080c2122012038003140c06046d00c2000000c078040d00c81e040015642d066006010070159603c82070124900c0380c00800e290340745040031b07107a0180701042204000381c0030768041c038000c039080003c0e03c02da014040361b099520580c405151000c241c2250300986103058a104115603c15558181e000031400e64011039902d071900e02c40140b0200e4000b0b45000c5000d420186103004102044030881c0c401010404c9501070009a04410003081c01c096011030312500a01d42c6c0800d88006948486604e520580407c01500684200c25006000000b0105043d1400d10124400107070345090596002244646a0061521540c002801c8041c501441d2191511565600c044500101d00030a0980796040003034020002984460046030072076451410740f5030045441c0801d503000c0c409548256507404140000c0e100b00d6903c107503154000e2901486901d00804440b445c8c7c0d00550001c3c2d0824040ba000c50401c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 334116555 1250 334115305 334115317
    0xf050108090a0b241905010531031a010b2b0203040804080d0302210a1e0518030705190c0f030602130503010213051e041a0406060c05060624 62
    0x2c0d2041d180b61303d91095443c0b01e00300d002c1d002515421520458603084200112040c0500d81c100800042d050780030041402d06c03004058041034019415603542102c0ca1448540c5220031a010794002650092015030002820304031806040c000c0d02c1c143e08881d101e903468070310b0307070003a00319003204110301700380e1503562002d144514401e0403265656400d10b01110300d04603181c001d48040500411800007880201030708000700c2c882989001d0b030243c03940d504603006084400300d200d03c80c03c03510504080008094100f14001c0c0c14100589605d0000c80240c0b0781c0301d03c680366002d0850741c04001d10358040d203080c0ca255820715000d550380d030051540301e202c0c0c1d00c0d01e0440c135881551455008a40190089200c101010003014110000c624104025100d0b6105500d01d10a50b881910696a00540d00382607001000700b80d000148104081400c1c80c0c90324102160001069011b280b9161000c03e001d40036482590401c4e42110081290365512820031050117030483c0201d90409016010903400f418004c09011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 334117805 1250 334116555 334116571
    0x6040c0302120a1b050a080303010f03060f020c0303070c0b1003021804030e0d0305040617060f0f0a0825050d08071e060e06061810030623160e0103060f050108090a0b 73
    0x1440a152000704006c0031004e4000c00032680007080100401c1d0940c1c01c030301046030792202c004100000c1c1ca0384488028000d00701c020302d090000200300110319901c6000d80502c41d00c208000a06a01e58400920442c003503400003d401c07810b231200b004401a1036022107036110388a858020b41030740002020030511134048400700c0c0880c50201e0180885038121064810303004c0b0900c9821000d00d014000520565003800340c2c10701500c01d25800c030190361280b403142d00180401d14111070040d4090140d000790314508804440311030074100c13400320b46490007103040c0025a40082640d81009916147c4240202c0040d5004200d100242c12120001e0054054108010711041c0a00164600002442004508805540c501d00e080b5010004805910321500c4141c0350003000008800b00d11940300243d240288490095140094040054410303c95080c80105034045c2d90706901e50441500540c01c0d903003180100c0101c00d003000002d22843d48280c2c0311940c805019012215602440e44406560360b0b4240ca0b464 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 334119055 1250 334117805 334117853
    0x3010c050c060a1a010e04241404020f0703180806010b070308070e03101a0603040506190b030d030507020c10050405010905190e060d1406010e070206040c0302120a 72
    0x1000c481c02070010035401442e0100610985051200d078118003080394201c18144120304510b0440c0e078a840c2d01844082500d000340015900c100046110080c007144126181c0c06040a102d0145040a00a4540d080f011110140c144800307642c0c10b44d0070b88000201c52800011001c030002b0b6144080106500814456800c0703907803900c00741002020480010109410f01400288206064400080358181d14442031400940000f0704505501d09401d64001ca50b03020a000c4107010500c440490042d002c3c2c0600144440c0b024003c0d0b0042054415044816502d900052060b50707042e0b010340c00050703100c40940b06640c49503560400007146029501000c8000030ba000c02e0610095801500c450080c120840745032624124504460242d03000b240210010360298201007070451302e81d408902c1c60f09e40d010320000c48021042d4603041e51500309110f6071240d4040c1c2e40108407804d00100395140034903080910104981d00f55003d0041c04030000c5031190349449007546184c0451140b00e034503070110740c1c080400d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 334120305 1250 334119055 334119067
    0x402160b0a15080d0906140c0f030a0206130f0609021c0c05040b0d0b0103080c121803070909120c02010e04140906161d060405040906021b010c0f120b03010c05 70
    0x1000c10403502da04016090307840b502d041300c00701d50044500c2e4102e510380d03c1c0c005c216030040360112840303014007410882c03288a0740300c20069911011018011804960f0f00300c42e110382d5400c0c00001c0d82080702c080030f4007140012501d000403415a030044500c02d40058031250100030f402c464000d01800301802070700c04c03103078050081c0700c03a103040d010343c4010f0030003196a06004034003030300e0360b83c42c0c0c0c90180b0000305280800182c80500c2941401320b88010f01ea140304950300e4500000051140440441030b03a0b2080c01041c80c00300e10828a0300c24449465085001d00345102c1c1100f0301a2a5070031854400d0f0305008025071707080d1190f92580100c0c9240c0181001c80e008a060104480b482d1450241000000c2e00c034060341214445d40c84490b4840e00009203c0c54901201070501280442c070032500b0050300309040c054601c041c812150000c02c260300380031290580b81c01c0f40703080040c200c0e60810009000550b151552a080512403810003110751618400095211104030009085442ca5916600410004591 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 334121555 1250 334120305 334120331
    0x91a01180b01020606060a0309050f0601030305030406140c0403120210021303050106052b08070501050703060503060a06060504180213030507061206080d0c08070b0108030306120a0f020402160b0a 86
    0x19981c0031480c01e000902840c00d0502c0060304030300400403d0300030141e0301c00900302840000c0181010a942050940300c06503144d060041155100702c406586280c200441241d503125807052503841500c4942440d03041c14216919000784800b082a11011449040c200c03614030441480241585411040d5000d0064a5890030500f943e406074441ca100d401c41d07000c9a20783c1c200f4a6166803004034005070101d009030040c034101c040350080034130180881d0300e00300c10440255010303400383c0281c2d08114104c841c00d0b6525044442076036101d02401c00061401d0004000103201720304840103d020b010700c05820810080803807815054643e01c1664150701809040141d150408024134038400911002e0040e2424200300b2961442c404a4000c20010320301604028420404141c901103603020400070302559403414161341c0c070740054070514801c0c2900702c41c0308580350001900001096104e609403540c0c0c00c06401300402500301d140089210f80004081b81c000440c4900312510440c030f0201c0c001205814105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 334122805 1250 334121555 334121561
    0x2120d0e0105091e06040804050402030403170c07110d120e0102010e1009022106010b090409021c1b030c17030f19080606040302180402010302040f06050c0d050a080703091a0118 78
    0x83d110313034260004000d00c00807809000c1110265402503038096901d40b154541150080840b0001d90b0554070880d044c0402401100c00406440c7e02811041c21800f808400b04090440d070711700010052150a00c02c40005130148141141d01b15050000040c07006111800c0d60070070148076840200d49030340d410034100f1880c1402007413009400e0310b466006c0d9000c240b207140c0d036940f03c1801681111100800c03105880d03a929003001c1601c540c043c2140f030440300c607100c071010702c503450b0390086400040c60b0f9008036035802060061030440350400c6041041620300817032507280d0079a212000c44a40810884441101c00d01001002000700d0b40c40a00c40303821410000400c0008007800c3c05114000802c020009a07581007046c0000400400c01c098040d12103200680091042d41c0c48203011074040c12000480320b41000160119981c4c0700166071000c065441c0441c0c0783c0c400c040c0500c0204422002140c55544241c2c415112648076855010703030703843c0c0383c000c1c6001d19000b68040400c2c0e00195500455021442c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 334124055 1250 334122805 334122853
    0x30305060f030d0228021804051002210c0a0f03150317030f060f0607060203070c0204060801140a0b0120071d0603010e07061d0a03020603040308040b090a0302120d0e010509 76
    0x1c0d4a481070100f00d80c2c00503419511a20b00310061580381004523092190600110b444501c2c50078045584a0701d880c150301c4208103d0360500100340d03201e40020f514404c1a8100e803181c03400b03a0f440400c407842d1850b040c1c0040c190b40c413041204104007800800090141310100766560340147d0125203d24020304c060b00200d00040102c0d00072034000410080c191140e105442c1074541c0a180540c60f40da074144215100d41e280c1001035809414000b000880f030750198459800304004140500640da901d80c4c0440c241c1d01c0082d02140013406d90503041c41c081c4411040d818a0114a0040d41c031007030f0340d8816215200d0b40052583c03212504c00024400305241c00d01c00d2002c804000c601074880c051500c0f50240aa06010441900c0c01c3d485440c0d10031079a6510784500060355005210076103034203090500800c1410100c4045513009103880218401600001e600020749506900401708507211158000440d00080c0d8207480064849000030b04001d002c0c000c26200e0380465005003100f000c420700800080c0d041d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 334125305 1250 334124055 334124113
    0x20a0b0114010210020906160309050a05040b0319150f38060a021204080c04110c06010b0a0519020609010f060506040506180303040902031f060507030305060f030d02 73
    0x22000341c9941d0300829a100c2e0100c071028010b1b142c00790a0040f072600e118040100901001c005100010190001184030030f0b1541030718180c81b856183c509020481c0c00c2034130050b5051b17000c10741700b440400d07180004802c0b040c0708249023400380c00100035040030390b50b1000303905182e16200d0020381c0c020341c000e072103c0d1224111000c10348111003c4650041c90a007c561205000b4040001c4002400f80200040700e0482007000303020355070b01e6544080644034207601e03509522850402e481010841c4100e03065030003110441004d000182d19100c8009002c1d0301c614995000c0c40b43c00d0100b40c041e414414aa03a541d005079802401c0c44d4500441a9800c5030031b1031414500a92500009021949600007a20155101554060b03a43d140500c0d50502c0f802d15120040d5040c40000707008102c00d2682c0e0050f500440528030303e2404196054078042a0002a00541c1e0000d41c0601c25079000c40e1086c0c10140d00090050142e0055054060102e0f0500b8119004100076074000d101c0051a1301600203060f00802076 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 334126555 1250 334125305 334125329
    0x703020904051b0d030c06050c0f0f090a0f080304120c050907050702010806060a140702060403141608011802041a04060833010e07020304090f060305060601090f091812020a0b01 78
    0x100765001b405054008801802c00e90f40c940009194102000031a50a00f0440540b581c6074048002540070b158000c10f001c5001d01e24902e40040d800501640e61001d5a000d040034508050820340000c0c41c0c01808441961130406841000450380c4a494032503014042d01c0d650710780d4030026400090700101024085501036102002905006a8082120745d85004940e00305680c4501702d0001950030f002e5a00003806d902d0104141c1ca1880d680054241601c80c400001007600d941d5aa4441d4200c40c1d503007440d6980a4080d0781c246d001494150700a40980c0841d01c802d403c6030588001240441c1c441ea0000740007a4030800c0300d54006d82514140e031905813910f442194462031500200c00140c0d81c107201ea2031010241c40e0120700304900078002d44004c0e14550340100b051112444284010384014403050f1514010b00f00851031a5100700d140e0003d0358019010079607404d00d00880e002c01029104481e000200102c5a4000000e0f10290280300d4121641d00400001e01507003401034902406903c101001c41c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 334127805 1250 334126555 334126579
    0x30f0201081e0c0c0c0a06030c1103121308070c0b0a200a0813031a010609080f0a02060901020111040902091831050f01240302010914030703020904051b 67
    0x1500303030400b03503c512038114071519202d56000c03203460681581203440c0d2003d000c101c0805c01c141d040c0d1018404085540e2003515410b10414025101c1c1328811813101642c03110300001c0c4080b64242108001076226a44030b5140510a8548000e800c0180d0402210410300003507542d2500e0703026446101d40d070341c12503403c0720b26405841d40e265a102001d03c01086402c000c1002900d841d00c0f022140010340c0c01000c0c0701c940102c907030401d10b5162000d001d000c01040c0401030104000070300040d41059810018018070401d60b15030200103140d04000221411592036000c445103521800c0041c0004200c03c0780f000d6100d150220800480e08a100703015040080d0f00000c1002d82440080c01d011078440841ea40c1c02150b0048590f150810321001c009021032145a031121740350311055201c40c000032600d40102050504006408150000c9444080e0000d00d00200c14054800c1e8800b99040d50007004048070981941c9078041032620008a03400c1e20a40c118604a003c11032024018075030b45441240c00315200700c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 334129055 1250 334127805 334127851
    0x105090309062203020a03120f1143030c0801020909011a070b0117150705040501080a06051f1404030b0a090f020301020f09010320040303080c0d06030f020108 70
    0x1000c2d00c0645205072244804851001183e03078244030145402404030200c558490900603010607550003240002581c03a8401103000d80300d038000041c0f89601c41302030045039000e0b075036065920380c00040301d04c0d4580040e408a20202d1041600c014015509940c0d5068240786041c02e06020415500c0b850242e401044cd000c4075a5072006e03180d040d10600030520454001c0c80e20302c4007442c081c1c00c800403c00d98501d4001f00c1e18541e442c188091500c0d480f01200c501d008010410041520195126800b1030300c01d200c1800b0541c000c0c0c0b2010f030b1056014100003125035907040012450f0b00001810402d01c4012011400b4145e40650060680160a82d102d0700d042d1455840b001e1408004011410499880342e4600800640c003416048a540007002035407100240c0b08107401550003840c1040c0406e1900c0c00040020703a2100724a1520482600305500b05171a68805940d603000081c02c01000e524100608820007907241708403005507008041c000580d40c4144005004c69a010704110a21105080c0e110b4080d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 334130305 1250 334129055 334129057
    0xc13020a0206010b0d0f0203070314100b030112061512050706020d02120d24090606020a0b04030e010c0b01091e09021e010c021507050c1f030c110102030f09010509030906 75
    0x65188500c500da441c030305945c021000f00440281c03a80201e00000902915540c55080801c680c0c0707041881d10381790f8441030102c0c0b80d02c400520400d07011400900040004210f600d58010751a0b001e0720002c2409003020030340c012080c0641c0c12030034280c80ca803501001480010000e49020781040d00040482044500000c0e41d280c40f110000e28103814006103440754444607802004003800c4401803100c48070710703140c2c04d140400a02e01078550014075250000440600c0003c00190441d0045003a400340d490f541c43c22180c070301e07800291300c0c144551074150400184280a0b441c0c02018219070002c0d00c1014000e40e88942061429020801410210140e02603901c4243c1c800482a803542c000c0076114504006a40345280c240740a90300c41101e5000d4100140751000506199124006440503000d02c0d60410205140166450303082109031403030511940d000c0e40c0002c003d80d410b401d141c0311b4840a40801c030f00b641d200720740c60552412281c05010b480f101c240180d5130014041000740d0f040107442c5021a80c6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 334131555 1250 334130305 334130309
    0x90c0604030f0b06040e0f07080c010c030c171207020109020118060503180c0406080703020310060323071715180a06050a0609061d0f04020a0303030902040f0e0c13020a020601 77
    0x1d0722038000b144c007690341c0380d01055490303444806507441c0c000280b5000380c448071180f081d4a498050200f0003580da40c03040350421034169041e01c0301c00c542c803900d80301c24021500c0c1e810303c800b1500080200c400340255026045101d074140d6030005c00c400005100040a010101c0b07283c40e00411020740030701440d40c201c0e080d6548102c000ea4000d10381080924400e01c0c000c1c4000102d9082840c0c4000442c900c9400f0800c49c090f0b0340207504884c0103080b182104402c5441503c0050120318003c40d00e030f001e05040014420703132b0300480000c0307800e210b0301c948281e2600000c443e0003038842d901406078100c080d80c4400005a20900000d0b40b0f0110820a06200d501c40407040001024550b540c8001003040c00c49601c480090005014200181500c0b030b4038030310b0b40700d200d103507801014011640051240300324054110322503580602008070544ca1075400790b015281e5024100d910a45825180c1e01c1456280700381101ea1255600500c2020b41d00814011120642071528070541c0c0100088920142c00003580c80c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 334132805 1250 334131555 334131563
    0x3060e070503070c050c190923010b07050109020a0b0c010509071a0903010608030304051e010e030d18060f0606030b030c0a14030f01051e0c070c0b0a11030f03090c0604030f 76
    0x800c030217251240c1070210030649207a010000c100b4006141103242c048009440c0a03a40422080c100001127580c1040c0c40030b014500403d0010060021041e07039009489103c1c8202d00103d240c1c5101d500090098699800655071f4100100750007101400034000c0b640c1000c101000b030420749007460111519010031200c0c10508140001e0805241d4400358000c0e0014907103e02904d0f128109858202d4a03002c0c242c1541030480c0c0c90400600c80c5010600c1401c0e19407029038000d6180499a5014001401c56003841c4d5202140d55540030300400c469008030710801002201c0003075100e0501d000074084030f41c00c40445010b64407014560071141c50302d14055060328038a220081010203881c00091a05840780c01241c10755082c14148a4008a80e400e80c40420108000a044c41e50700e40b690050345005180c0043c0c54410715a10401445960307400410748481d20345000c982240c000b182d114903550180302031003080e00f0000b08011040b01c1c24441480301c80c0007121200e03e4186961141c80e41da0b0440c010240c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 334134055 1250 334132805 334132817
    0x7051c052e09050103050c030d02161206060503011a01080c16020d0804030f03030501150503061305180d080f1522021213030809030309071206230703060e07050307 72
    0x401e015561840110041480c454140039035a16440d00035103e0a019006034002d1040142e0280708500101d03520400401f080703001e050261500700359010140182000340c0e8666038442011440b601c0a0189402545070803031001148551000010802c1800a146501500c02481f008041c04c0b030800e40559031503011035801404200c1810240b81130304c6180e20040c01d0700f070740690201c01c15805400c5103049a0300e940c0c0c98001480743c1c660981e940d110894a0030b034004d400500711000328000d64403181d0803000230b8160500c4412410800b40c580402c0750140c0700440d221400b0004ca041c0e50441c1642d008029601c0208004020004141d18455221540c02d44500c5081d0030316840841d681611500d641420780d0940901f4259241c441c0d601b0f4001003580004e079028000784001078008105c0380a00114801400d0140ca0404401250555000d08a07801e5489200d9068041c21703900d107100d0080c4a03000485158101480050104c55455000300f0911852000b000426500b200603698860000d003401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 334135305 1250 334134055 334134121
    0x30e06090a030f1502031e13050d120e070f0302060a020a02130b030d0305040c090e1603210903030504060e220e161a070312020307051c05 61
    0x5502405902034054124080030350020900466800e0428010701400200000640303074042007040c0c2c40110340e111100031601c0c45d182c00704440b85c20015480b90500703900c05910134a0350f036407900781b502403000d610026407140c501d46c030032908034800c03441c0805507000140703003992400c0b80307105560b00c1600c00644204004103c081c40036001348101038060340c0c001e20001c01144084001c900034a040c000f224001e01c40c2d24010001d19000344501400780760000040f5000c00d00d0100c850000d840540035481641c0100c0c050540c840084a0b01034014500c44c0301011080e61200c413144101c0c428401000d0104003001c0b008001203078220007114117440841ca00307600790400140211f50300781e010702004e80c95a0002d11403a1039400d0158800c58100c421710b021364007a020800f01940700501b442c01004840b54040c280f08000309070100041c0304080c071038200300e012602601030340401c0381c108440c1c10001c00d00000d40400090140303201d88500c0700b071800040000d401e245444141c450014560040d0aa6421004c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 334136555 1250 334135305 334135309
    0x12060105010f020f1015050904030c021002012301050316150e0a1203020a0204060936020907020a0210080702210c03040b1210030210050d0f0c080609010f12030e 71
    0x410204401600200c030020340341007800710010f11804141d05406c143c1088041074030710f000c1385080d002d40d0300360740c81d2041c140c0b45408025034581060394240656684028110340d00000740003c0b1980c0a81e0100e0080940c03500c030901d405c02040d17601c5022500104502401440c001200c2e02ca403103c1140b60148044074880040b41511107a03801141c08031510703824500406a0000750017144500c00c1e10f05001d09640d9441c03000646107600c0328641c501500c001d006c02c00045a03250701e02100c0e5480301c001150040b540100d064043c0c181c50080050300030660355800c0d414130b01042d104040c103034940450b103232400c440d0003500c0b07808950704055468492440c2082080d0860183d541900d0a541643d54460b034842c115102944030308040f40c03000c520350340020b80401440490100f100d401405512400d54100c8084031181d2110410300200c40e580c8108030080f1055200d0340f42d5100c1a91214042810b00a0401c0364001c0142d000010021800c003041c010071070b01c0c08114900c2c03685400c1c08a6089a1000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 334137805 1250 334136555 334136563
    0x102c040f0212030c0d0e030a080c0c180703050c090915010905040c0e09010803070201050913020c030301170c041b12110f21010303050702010c02120703080d0b12060105010f02 77
    0x29602c001140801c541e59a004801026402c4d40881107a115105042080d944056000c102d139916421405d0b20303402084200c40101000000a800c0d00c0e40c80d00500c0004035110049055054071750062010042d0064140c4223103500012580343d0141007000c04000201d070141c0013841208000700c000022041c9074020f1034030744050076004006000301070395000000d110000c10082c580c03160000c100001500040031044801c0160180e42d401d00c2c091601042c8154444038091585070554200f00036800c09100340081d5020700329400c03941d2601003c84580915064844130007d100d1882c00c1001d1281040e02040e2025046040c1001500580c1342a2107030010003c209030003500da1000a0f120005035110b90040900c404821a0500c1d0001112826030b0300b141e090200402044080104101560007128200c0c1c000344018a040c0e981d5010000d480e00b4840342e540115400c00c404950030100b0845c5020322442c8000c16100401840c400c03650143c1c1c3c80fa810b2048906100301e40e0801c0311880d100744 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 334139055 1250 334137805 334137833
    0x40804030f020117040b061c0c03120519020705010311031501031e150317030108030a18030f0b15030313050418120801080709020a0c03030c03020c07030b102c04 71
    0x45401c1340503d020308050440c1c59084525078403a40040d07412000c0c2540d882c00c49440990000320028100d030840d034034001c1000030312030140c06100741400b00300150b540c0c01010401440741640601404c92500c800541900c1141e0181d070008441801082000d0745211100300c404030b0300740b81c0030600c0390000c03180461540a07001c1c070419080c100145102d480205840443c11248260b8620b140581d171440c03055000d000a0144010035042001130854191041018041e100804001500429560b0b503800c04102284007048455950381000c00100c488010310b11b6a04640541c080c600d40100080601c001140f2406098031aa90721690600700a044c40751103800243e0040c1c0000318001a26000b826004091240c100c852244c0400412910382500a94146845c5a12401c484021681c3c1c150060558140503004259090240311221101040448001c5005c1d110800c0c076400e150ba504ea40404280e00103860821081c1640fa141d01505540111a40035504003101e19440d1460450921540c01d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 334140305 1250 334139055 334139087
    0xf0d0c05151308010905060103060e0c060c0d080901060b090120010c0203070b060d0c0302270a0e01110405090f0a110334050901050715020a11060a05040804030f0201 73
    0x7100044500d20729070002054160003a4180e1a049582d03403000c542a52000302c0014201d8000c01e00400018265820403000300400d181550b41c002021004141c85401c03071074218403590b2200c072024420035005000a5088070120000f48501810003051150500c50300d8461030400211000789944d080c48800d0848184407240005d02c001008100000e60304c0d0800e10099a0584801000c9a40b42c80d01c2c5142201b090303032240817002d0a0f13142d902080001a1082520607888000189041c0321761100e0030454072034101d1840018903021407000b01421610714550410781240204024012541c0c0d0003c0d040d413000d11003034108240d41d143e401c08009041004000112031002109110541040125011110001d4414400412051400100300007848505500490000c2040840551017640100009400f1300340614407004642d40aa00f00c0c0d10180c0030100142291107480e24940c410b20a40d81c11030180c070403d100905158586603050b201d031340300c010205070318001c8c120110b9002d2000b26a410081e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 334141555 1250 334140305 334140319
    0x20a0308070e0d050a0303020703081515070311061807090e060a021b03070b01090f020a2a0b09060612060705030a020d0902030327030d0806131503200a050f0d0c05 72
    0x20310301d4060040d41002070302b01e011070031210028841c0e4040d01c40388601d91030020b00018000144036050021a40030b4a420740800c501c0d400258515401000a1401002d28030780401d40407114000107414410700d0b400800c2164100384034500d00120010b0071540100c0b002d100181d0b241c40c130312003260126040d000101164000840c100c01408407604506048811640b41840201070100001040b0320032950b24138041895003d585000c6030681c05100303a1034207401403105140a1a445040206004403540e80c80782e88410300f0840d090401000032a4103444c01c000400c0349013003154019009000003400b0003c01c40e030205000c101c07414190410514560050156595910800d0210070b0618a01511414205590034100381500340011006a02c5146982d48440c0d86ca0b64401c001b588017504070305502090b100e0713050030b40c040d810405002c011803080380c0e00203640d840b0043e0079a44a045040c8540b0403080c1c0c3ca0108820b40b240307080420710180c100d034110b11800f494503007005843c0c9940c01440d00100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 334142805 1250 334141555 334141573
    0x1050f0a1d0918060903281704030306060807030b0121020d18050d05040509070c0f14060405010b0f01050901030e010902120303091015060f2a0302120403020a030f060f0c031b020a0308070e0d05 85
    0x140bda8092029a003156507032100d20b6680c0d00c4240c00b5540c0000e85180086c0172004400707202c00c42e100355903011610511001d40b9081d1140c00020944640c644030f0741103446500b0300d82c010403904008440d001103030783c14200e04040c600400114680002001174003404400d003811003c001d03078034100c0703036510764014031952f10754440c1031110341d43ea0f508460440795903180c0400441e2074642241c242500b040d0580d2100e1419014a00460103800c0c84107015041350340b2507080000503954841350303984152000e0020350700c1e46008504140b41c0120aa4040601031805100a6200390541c400000355041c0e42000200302c2d2030484100c0740c0d004210030303103140d40d6040c0030005082840302140780d0049000c0d5085800c1d400c545001468117214078072000790302542d502010000542412115440c05014034000100e0751110441c010556440045000000355100074684484403c0d1421720348a113160b1001701141c002c05d507000350506030701801e0071060110b10840005181d64158a000010f030380803041d500b2070a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 334144055 1250 334142805 334142807
    0x303090503060f0103082502030102071a1005012a0b010e07030c03020414011b1203091a0603060a050a0b06070c0f0501050f0a1d091806090328170403 66
    0x24140d00406100b40a03100c041400d0000c0c2807081e034141e07600600c1031860200340c01201c00e10110360000000007156014201c2e40075035002e2020b0301d401030203101c1458004100080c414101c00f00104150010f03030301c0001c10300c803903648141800d81c00b11001c00c1040100e5000c0002001c8011405d000400030204500003203402c46995801c18000c02060704c0a11481c035070220250b06a000d0b600858030b407070901000b208810b61284601d8468001540d6040300c986079252602c0d020350b1013410319000403075240c0364407000b0030815102402155040304609140381c242030000984626003c0d0018015546407008580203641650240c0402d00c00201000d94840551400208141e0244910a100800309000150950160007100c903866034001c1800e15001c000082640c14880b5a076950303065840c0c1e00c82640440c1c84903030096000380c00500d10b88440d001c4a181240ca4990300030318518058200f070044000c402c03d0304512000c01030046403000341000d6400022280e944264200309000624441804145 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 334145305 1250 334144055 334144067
    0x61503080d0b120a020d02060a03021e0702010207090509060601080a1e14460204030510050a020406051c0906051609050607020a210c080f1009050c2202040303 70
    0x1c0c48107643da5810701110002d81511180e6030007020703405c84800b8034904014603041d0020405c1c0185814018240900e030702d5480d40c0641c02844c1401030500000d580e0081d07603010031884c00140b0416005018074a48001d400740c40c0c1d2805040395041c48115070200713048403100e4214410021a400000c0102000c003e8400003400f2140303581046a203184020924820540c0428140100d1403a501e0707801100c402519054054503503419502c02ca00000c00440000e92400104000d60040740141880e85040050a08603030700034004050b400d10420041081503004420b075508060608019110120a0850f01c1b01410080c080240301c68a0710082180090391618480b00100e007940d504640189c5440074040540328024000c0d60010302c5103410041e10040c0e00068007141c444c50785481c41003030103945a1140c4451b9401c001c5003904081005007a03014200146403081010b00717014040e403100d030b480751505e070280601242c5c0140c44400400c41c4410f01c4c1602c0200d0300074204e00466407a43d803414028130b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 334146555 1250 334145305 334145321
    0x4060527130c0e0f0312031e01030b09150105100507020a05031009170c1005060418051b06040f090203100b0f03150d0c0e090a05060c040e09120403061503080d 70
    0x4900d0780022400c1c0e508110501890105010700100686d20f9243e01101032900001c0011002d188503200d00828406020142c6c3d00030b5201d80b84940d407030b081200308107003000061305129440d0342a40d4010815030762802c10501c400d05003403c140303a8607010b03400403811800258003c540c0610988030b490000c54201ea0010840d907000e00c10801184c003421a40201c1445040c203180ca03554881408166003001c950301040e00800010000140020030000f411102180024256126000078030f9a50310000902c652a0100c80201c0c0d0b99880c0605110b00d8a580d00928001d4011440d030110002c1d8072822062540d2010340300c95503805458402c16482c07001998170072206d443c0c204038681184020b60420103031144032150b00110a0440728202040c038481c48200030901000c80c80344a01c4140410024440540140c840c1035006554078240f201c03400900c00040e01c4d000c00e40e4041d031a00302510210005450076030b640440e000c103503900c43c41c06120b001c1c1b40e9904081c1818100241110200059a200c584 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 334147805 1250 334146555 334146557
    0xe0c0c061311010206070f0302160b090a0506010603110d0504081c090c09060e041202010f020c010e19050307030f020304180f150506040902092e080603010204060527130c 75
    0xe82c004101c2c004907221070301a40c643c0c01041602148581c014000c1e005403041d070020000e02c4080c0e40b80c41c1c8900060701c43c103851910054100503140803c2c070506025a501504084c20148801c6c0c2c071700e403a122440e108440300000744a41e40c0c8040390410103441c2c126007041d115401961400b45100c01050028403200030129200032100d4000600d0740914081c2f00c0440c0d502c01d035100e845030b886441d01042c0c1000100b0102c11956603104420030185d0510280c80e901010000001e501c011125080b0301d44050b05e0103c424804c541401c00001900020440c4d40d61b640c0340c5459804440e2165090f403a500468202d56100b15905400314502205540b007801c0c04a0300b48401c2c0b140c92b41c0d5020419583c80e090081d160404010001400240e26940003401001406407840700009203010b02c00300d9040306400104030302d031212600d240ca840d5100501c1604688120000c42c6440c0c903150003c1c200c1d2040400944020180002c6084050503a00120492420152001c034054900d140c1e600000d020101000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 334149055 1250 334147805 334147823
    0x90604080a120809010c0c021e1909050a2a0c05031b061003050309010309030e180615120604051801060306021b07030503071b2102010314040506010e0c0c0613 70
    0x1210000d0500440310606ca40f600e618440701060b80034800385003141032102c01000414805107645031548802203500d000f00c414880001d0f4208246082032314006018500803c0c10280d00000200300220542041f0810560b019105009940c2c01d4800000d4400041c2440c000812031280004208020243c503110031300030782d0096a6604202c000301c00c1540400b500c95841030280780c440794040e41c804450640281881440d5140749000107056800800600c62061020410b10940741400342060020075071100e11242040884012400070000041105124070b0300c0d04046070400c10003105242032181c102d00288001c40d182c0c107102d4007940c07002c4520950008108898800d0b500301080080680354024007442c076107000d43e200d8007121070801482d210aa0789510000404110407502c0d040e03104502c1040b18801d81450001608480200079000b5078100c02004110000d0300100c4c80e281520400d80d181042c5449e00300c0743c101540610b03c4400d00a110b110184801590002c02800400303100c0e030120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 334150305 1250 334149055 334149061
    0x31806090c0d0c0306021c0b1909330e0106050a050304120903051e060907050315070203040803040602010b100912020409030201111b06060d080d180c120209010f0f0308090604080a1208 81
    0xc0009c04044500b10454010761075024004480180c124480d90900c03c4039205103c100020000f0f4000304000700d04060300008901081202001451607004000324103080b0304003411035a002e000c3d8440184000c203010585401902014020a9201c020f03640040450b40342016840010728803807961004140c640c8240030014190840c0000d0750380a851000c0c02511042004071004000e10f03501901138010343c0010321010071508020009000101031543c008901c010100c81803180c00e032000d04031a0200700203508144800104071070070a0b81264141c0380024036201500703049006248020711040c0302480050b02e001002003014601c010b8420100a41c2c80b20786a040070000001d03083e0744001d06502c018401104100030700d900c804054040560481e40080550380e0750544400c01c0d800980d1441c50301d030302a00550410070681409840010002d400e07042c1070001c1d200d80364100e4400201f0204000030b000b1040d403502d0041e10028802c0d00c00311010075044c2e28002c4001c40080700a500001e0281c800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 334151555 1250 334150305 334150309
    0xf0c0b0d02031f1802070c03080a0504032f0603103b0720160e180d2a020a060804030212090901050f030f0f03031806090c0d0c0306021c0b 61
    0x7001d03041360184002101d4440f07482218402a4002100a684100018200101007a20103004288000a80ea203041c1d8507410742ca000040565180401170030307036140c1800c0312581402c0320300100ba111411115262039588070800c400044840b038004020b11007440d0a03240c40721110015142c09104e4902c20903c000b11303d1076060030880012100300c40019890441726240301d20f50f10b061030f10301c00804140ca58103650310024a1650b040c960050901c600090100315078450103080a000e4a030740c43c4040c0c03140e070114403030040088030001c0341200640c022900c0380c8c0203860005442c0d0513065000d40580e200740e07550390028203502d108440941c0540070b140c07103020b0381d401c0c240f00b22a005003000b00030304001d0342481c0c10300c41c402c480104600d405106000350518000f80c2001140003440d01800159aa450106c4841d400070010040520282d030085041c00104200401c625014001c21703182c100203600e8a00301048443c05940c070160406100040c000b4886a800310754203c0703124084014030882c08900c0c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 334152805 1250 334151555 334151611
    0xc02010513020f0a090513020f011e120b0a030605090d05040e15061c090c0611030405060c010605090406020711090402011d06130b0d06060302030f040f0c0b0d0203 72
    0x100c20400100a403a5140185001c21860030000c001500070008252501e801030121501174900501355904a1443c60452420400e121001f00e42860080b036401084d034501c182c84bd803050484014050144810302400300c95071711207440030800820300d002c0190340b070900030000d00f000d640310740b041d005000510030400d004004640441e012610884801ea44a0b0050f640d06098008501e80c0130038100b00d0754a1450003069403449406800724001608512460040441100d07940b180c0c0c180b00c40403031101e00b00c4402000342e40449800361032140d964444e0b142140c0c0104881d030801a0b11030000c006200030310803641d01070144a441400440351003c0d0f20400c10100160442d40240012594000701c24900c1e42200c0061304141c01421050501c0c0640d0403007030104001d07402940c240c80340420303040c2142c0b20350f00038480101401d003000c5107503040452105980d014020300280100100d00016810842c9485180c0000d0040708541c68440395030380d1800300070394005c0d19179500502c6100d0861401d02c00141f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 334154055 1250 334152805 334152811
    0x411010804080703030203061815120c01050d05093d02070f031b0605010909050606060405010f14130b0301050315071d03010f05181504080904020304061e0f0c020105 73
    0x84141c1c3e0411415641c11006944014056074000000ca480e80c4000c030340d07800d4114091b0300a1074008084032848400d00900c20102c0e113101644da0300140605429907080b004032041f0812000c80840d003917507400b1613a840c00f9165003820350500c006100000c030f0004035000812131800c169070309401200c1d801040340141d0140203406005400c0310742d2510002806410303075454480780b001c141c40c40c0c144c88bd1a54000c0758026070007240304607110710305842008014401d540d80000c04071071039402e103418040020700c9a00f150803d071080c81440d090142401c4144400e0354100b2000f035018201403511004011006e42081c0701c0c490007071041c4600081441003c2c10150b02c40c034110b544031801560013041260001c02c549010076055542c030040c1404071b222501400d44100d18002c0301000310511403002e145010b00a40b0184803425002d0b00380400500c00303170125901007808031005070f100d440d035050880c020300340d01700c0401c01c0c06400d40240707420400c00c3c1c120354455544e18100300b1441c0420b040c141c1c2668412 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 334155305 1250 334154055 334154063
    0x115050a050a020a3003020f0702060306060c06040609020a12051f0207060e0d110304030f03050306010905033004050108010521030a080a0c1403070e01030e030a080411010804 77
    0x240031030015140318030050074006001e441110490070040e02c0301c07114030302c026001d05421071420003c044070003650700102c6051041842d00714a40070129240c0701481c001e00100902c1440c000010808542d036a10035280d14548000c01d85042c2d08241c540391005100c81c0d84200c4c010400c2c884005550880c80b05403285898114024010b041194050b455001c3c00c024903c0e03004960074454040440c0f507a100e0004105000307401021090082c450191100442c00c4100a40e60b00400042c0001210241999001c5074181000340e240c0d200c0c440183d444914a81000e82c1620910171181102010f020294035400c081d020040c1d0140308128001c5914811070050301e000c0349561004210a00b8004685504c1e01c0000e410880b00c0b80500c2c4c2c003d821035001c1e00c01000050100c10612691521340e07c00d802c030001c4035061200407014406042052404024141341c1807004642003076813143d00941180c214234000806403981c941e40b03044013800d040400c0d5000e81d42d586064181b00215401030303107403070300640d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 334156555 1250 334155305 334155307
    0x20102010614100f180801020306131b0309030512041a160c0f0c0e1f080a022116060f2a120509090a1a010903150b0301061701050f011505 61
    0x201c04026525000503001d02ca04005c44411858208182c1402507405030034406c001513500d050a600b00403104c01c41c4011403004620701030703136581109500c051b014407103030712130601051018940c1419940c5024000983e01c8044400080100b00b001510340201d10b403030207415003d02501d80c0007400300c0130102c0301c11400200d40514000c1011881242e00f103800e0301d00c00c1c00190800da031034224126100704150341c030110b07103844900903c3c03a11020b505a000949048001004400c849070001606071030104544541c030010700f11641030792201880081403c01c00f5640c50080070382d950000034004403c00071400b000525401900c414100d01d214031130340315818280c101c10201425268924040c480c00301c42d106000301000041c08a0f201c1c08403c1e446582000b400050b0344441c2204000f1203500000300038100700180806000041c1082d032411046990400001100354542c030200b40145091f0b0019100800903a43c0000f01d030205410042c0311710b01c50005070356182d0382e0f05003452003142a00740040102e00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 334157805 1250 334156555 334156579
    0x7090e060f0409060c0207050a06021b10030b0a030c0512161406070c080a150509060106050f1c0501170a080f0d1b02070f0609051c030228020102010614 67
    0xd0401049881d0a2004200040c1159241d0751401182e4118081a000d608079040c1086581b4260100400411080c00589140e00c40d0000c2e9105101040c0c0c8124422144400b078854011f219a00030715215401503c10300c11030f0703103c2c20304044000840c402e00b8801c2d003191400c0c030071400011480061608101110400c0c1605184034403140045044010350401400d0117008040390064803454010412400908195181420101c3c0095011250110164100010300a510000107100c0d81142c100380381458031010341051811103480303580c0c2c1550414520b503160039401829507000702e048982001f50304007220b00c180787c150340300c040b028000380c078646050051802c0090f1150090100c00e002401c00115586404d041c400000c410326505001680030316410320115031b4114501001e01103078185960058074003400121100301c50f40c4400c40d00c1e0000041c03001010700070403e500800c9011006c8200150301c43d1070669846100501c26401582000e6000070300c0c0a18515881c003402c000b400010200d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 334159055 1250 334157805 334157809
    0x5070803040204020f03040c0801050703050112020906031204240c0803010308030c0f070506090c0f10120615021606030c050f160b090102121609031b03120801030b07090e06 76
    0xa04010010b0341c106400304038444100044100070b45c4940d2007484503a5079103040c80045401c543e4000e041c4018181303400c0060218a444030844070046604442c10380041e91640e020a080c00003d02c500900c500e408200404c2c111580c1204241600042030000100c000000c41107452001c82c40c009000a20204010302c046408800190f070b00c0301c1d80c40c862a1610038a0b400841031fa9000a00941e51030b000101031040d00703102407040b000d421000301c90760400c6140060000d201d16001c5000d940a001c050045d0102103612500284010302d4240561032074000b02e800081d440e2444025407424104150401240b200d000380b103115002d40c403590303940b418004c1140519526074000c120400c100c90f002113280340007454030181941b0503040e84001580b9914200710302e6490380c401a12100300c003402d04911086543c2d2141c0280704aa402111a207840f07007644041a0300c604568102821000d01a40c3d0301101541003000103040b284516450819a524524222060f00c010300500da45040084081032240c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 334160305 1250 334159055 334159057
    0xf060503070c1718101209060b0d080a021005010807090b0d050607031a06120606070c0b0f031005063117010e072102301605010f050708 60
    0x445a0815a40c1c0345541d4503080c01c003040c0000b0100014400003241d009486004070b2802c40c011080d0781011402d4101c9001034050000c00b800040b07061f40e00c40c04213041c042d20750441d000c4540c000d4050708000c001414807172100e5025444610251140d000000d1021160340316603412108003001501c0c1c0c460901c0507503800341650500f00d0364007042030700c2c00c203001c1082440080d010300142d480001e142004100361144001c1948902e9104140a01c00024420007103003c1c01e5001e0000c0b00c4041ea10070252500300107000e179a400440e8003104c0071466111005102009600030441c1c00d00c441081c0350b9803070400019101c0c40d8200040c6007003014011071242110000c01308050350440314520450385460601e8400d0100110620a9039125040d000440704184040c00290602441b40c60b000d4641202c85050300b034000c4002401040e500802261010910014001daa0704100445008101a0748056559081c5200b03c03062042105000103981d801005200030711030303840c1c17141030500c8200d4544c0d0f45a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 334161555 1250 334160305 334160311
    0xd020f0a03180b1f03050316050f370f0501020306040501120f03030c1209080909070201020f030438040507060f0906080a0b0301090b0403091418040201120e1509070f060503 76
    0xd0341e0403913030021000030400d01c0901070114640c00c00e8910100d41e8240a89407000c040401849904041e000d44070061940d4a825041200c01c002558941c1d0260b0b81c0030301829034690050300461806e0740345d0041003810340003540944000c4505000036600d0f6040501034103031140b0003c00307101034184d007000003034000c0c0c000e90031540300740c201101d9581c05860030300280c5404840071600307070600180211181c40c100f9070140c2c0003600c52000714186807620390003026521015002400160f0026482c0c4400c0841c00c1400d10001c0101c58480000b100d03019240700c00402c01d5800f00d406010f0040c004c41c8040c41034080005d505031076a92841c51900e850780c20358000001800303482125888051422460310309005003601d562013903c1c524180d02c0c003410010504002d41e081070064500ca8000c2a0300c641d21001e01c0c042d900d40098400381c0030f0b101c500c0103a0b5000c21042803000300c0c6061680c1d0400001021904400741e10005040001c140e0b40c1d00e00c40c1b610380d103284c010324800d0386080100380102c520480155038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 334162805 1250 334161555 334161601
    0x503010e0f1e090c12070503060c0c070512030c0109061b020c1f0e030a0f03021005060d0b2a0309010f1e05220809040b010302090112020d020d020f0a03180b 69
    0x5a0406801c0401c2c00b90001d10311724001d652002d0303802c200c40d00342045159441040361401908040d5105400c2d512030b0110312505124901107407551000074801d10441c0c4441100c00c0003080410b4582c40c00d000500700b02d01401d000d0a64850018030414000704180c080d1201c001e2100c034071405261000c07410014413040d03540c100402420454580c1c0c03403c10000d1342040c040d4441c00d114076807900d0003c0c90203000742d0307500c00c409003403000b4415280c8410306003110a540c040c1d808500d0340d581c2d80c3c0b52214500c0c20300c04007104840044490944441c8640250b009152403402405940d03080c510640030f445503400035003006800f17200d000214a045e54810ba400040c4510b021641c40508100107001500030941074030b1040c2c0001d03041d0744900e42440307440502d00007800d040d42419079240002c1c002081e0380700384101c00c0c0d0b00014600701505142e4111a280c5500040454079940950302c504420381200c1d17803800c042031614403c5a2443c0c07010350103a804550125080b0395070303603c1c80703058121103204d03c01a003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 334164055 1250 334162805 334162813
    0x6030c0108090309061809070219060504080d18061109010c0803070c140303090d08010803190e0a080c09070e030a15090c03030e0906040608070608061903030503010e0f1e09 76
    0x84c1281d48010050486800c201c1d0100c00e242c981000700704040d0400b400c2102076500110b101c112500391140d0707031490700360030520000301390340d41d4182a0141d00c900b0600302c0c0305904d0010603104000040e580d901455019000422603201210844c00462084008250104051041290003c1d050b40021030f03004805103048003414889945c2c81c02c0c2401c0c541c4203920550004070030400034090400240800014618100c1070030752400c07405540301e200f0203c0c40f00f160303c030820040240c103000d2449407047c2c10000d000d61180e075136216212070300e13121116030325481200313900d0114000c41d2180a5440c40d0950003005400c8071181559080c1d08482c0154801c2402521644404041501d0340e9021001390702030f0321074005012003181000801d0600a1840c1d116a01c0c1c03990a11001c1c20010310003080d2101d03420101e0140d111040025003002210342c924076104002e0130013108140d4014003441c1211940f9921580035280c240e0136016680e0103c980700d074410703d4103240003d844400e440280d005074406080e1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 334165305 1250 334164055 334164067
    0x726010e0706120213120b1f030206190e06030112060b03010e0c220f02040e09010e06011a0d020c010b090714030a090201030e0d0305090c0301140402060f2116050306030c01080903 79
    0x30b41d164440c000b9580c03141e40c0410440900740080b0f080f071800c404080d06060b23103415a400500140140081c40303000c2e0014640ca00c84490080040310b41000c0300511054996039269113940040c0441e8004490440c2044500401410305004901e0915102400f82c4800031103003040c028803042d000707003107020790018030454100000395100703091009020010241e640da04096460141080140048075680c0c584201c004c800340001c604141910101c0540c0e84500c000d07150320107510b0040343c00c1c00c0c070483d2002400014184055001e1038900e60156000d41d2541d691007029160406624044c1180c0e030010000103034143c8843d442140340c1032050500043c40c800304840e4500d401c07045080280443d59a030244150701c0c40401c450441d09000320002c0c400c1d40c2001e44000c103a0030780608000d000f41c07004250941d0306054501039444070030144402260060b0007403092a00703120f05440d8032610742c02050104070540d1281c0c0031203100b03500140041c807100039401300440341c0c1d0710000e00140d0b813400184a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 334166555 1250 334165305 334165319
    0x1e0a080310090213030b01062c15030c0310050a0602030316120f0c08010f0b04031103010e15071209240b060a020309040f0221090726010e0706120213 66
    0x13403c500482151310580d081d0442c50304092401060704002d00b4448a0403516071030022030a114100070b07100c1ca00e0380c017032100e0f0200460340c505a40080c00010741d10110401148107140700c040e5110f03121007210307648295078502c20300c20800000d000e1000180c10030030004d1640b800101c4000c03500080344c5400350400000b8291441100c00a580c000c4900b601d810a10f2b00d0241d229034034a0140050007200302607a403412032140c845d4840c0d4400101080c10004d0035500301d550030350015120404e05015201e0000f5420014005c0e484200e8144000c24540f80f11014980c100c0c0c0314503103501d0f900c0100c0c00146400412595000240004c81801c3c5507219507410703e0603140d4501130039031110103070011921080d40310100401e880603001a0800c1501c1444080c080c8841c0d03a0117000642c12a14407a092526013810540c1800901d0300204d20851442484250380f80d0a90303541d407014202d80d4000c0244820340d07040107844d6410340c4500c000040c8012201031600850768020f0403a41064058069010740e1a00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 334167805 1250 334166555 334166557
    0x2030d080402010228120801061b050102040e1806010b070c12050c060408010b1c020607080d0f1505040c1d0f0604031502030105031606050d05150a03060e1e0a0803100902 75
    0x2505141620b07031051020800071010500e01c6c041c0340c0c60500310708642c103043c0000d003624007058150100c501c24031010428054294103d8025005200041a03d4640307000c20303105d01e018404011382c103032007000d000284180c55001581c600581c44440a00c00e5490125080b03070345e0235035450546a0780030b1749542030307480d640301401080100124000800c5059a4104004d1220110690340d40c803800314500e68001070359000301b00d8102560024820340c40703d00110811004240b03a20030f85100c240340420440300081d14000c8903044442c02c0380d007400b200100d032000f21420070411500384a04000400030303101c1880c0c46001c420044801516050515030f8036203591000c2642c980301000702c50390000040c0100c5c107041c42006560389034800e404103407a240a00044c1140300f003606100549558402042c04980c605000e9200c5050040120350f109440b0706001d0020440f45206071064418420700002a02500c5440740b519080070018001d645155140c034a50b96200070086910148806c0d80480d8001c040d00c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 334169055 1250 334167805 334167853
    0x108010909052b0207060509030312070c1a10170601060f0203280f090e060904060e060403081009090b010909030504080703051f020301051e150714070b0702030d0804020102 76
    0x410042090f00c001c2e040607040c0200c40e0420401c11108005000d030585001003161080d249400300390310160781d9030300704460070308000c60b00406000f6100301c04498031224412060203581c11082c490503281e540e200d200d4480001849941c0c403600000e0040203018091002d090450456005032272070011109402890303800e03000c01e0101200c5044071003444e581e512032100341a24525050002483e8100040f0101c9040000c014501c070701c00d001c0000e010030202c2e800c5034070340c01c100e542120f40c5030519140103002610704581b407840440c52500d0004010506001d40c000d080c3e04050b0880f016420305500901400a03103106a00b48041003000140303400341008035030010b5025030050164550404401120203055140140d6a00d005000602141d51020320907101154558503e40200201c58046000c203d48101304a48211002c5034120174007484051262120701754005465641d91150302c0900140100030f0040c2d05548803070360606010b8005c3d07814a82090050046410b000050214104000040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 334170305 1250 334169055 334169113
    0x117220b01030501060501020c01020709180f03030c1d0a030f0204060b0f0409050a020405090612070b0c0c400e030406030e060702210f04120507170c010801090905 72
    0x100402c1072050a200d80b00240900f407029000100e44840000d40d101034500036240b060f5604c02d10403401c5005c1680d41310569601488a403240c944506024008003000c04040c0c0200b81035520406c0c0c100f4801400043d0041f008144080701800d603110b06155424440080780c115a48540c0820345c111f50350701070b10b03213510000d43c10f60395981042149400d864029003200d4046005001c240669903c24034010f910500903210340502010959005103031540580c00ba030800070000074000381c28a0041034240d6004020b88015144031500100c406c00070301c04649507034040210114074980c96201d400400384110340400c0105021034000c400340d081d81d0050b40b1160200740c3e205648030481c1018001190301015a0000e40882d4400c2c0022084400d111304400d0360903403000508401c00d401724070548024010006045901150b24a003050742c440c82809110b68204815640200d2200d0005841403441e8045c0c0d03591440d64a06003140c1701804103030304212058041c03100c4500300703504100450400d00c244 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 334171555 1250 334170305 334170323
    0x160f0c0218071b15050702010b040507181205030a080403050d060e0105010e10080103290118050c1603050a0c05011a090601050a05090d020d1e0b0c0405011722 70
    0x8101c007070521600500340d0b0300400c1d14050f6800210b60400074507000d54031442000310301981d0765a03040340101aa00d000c240c0c01841c082c14003003400e5001000c02010402065070360386040c2c03036580e251283c540f2848020019881000f00c00320580c41501600e4015101e41086410080c1a10b20030703060340c06a401a0703102c0144c41e00100700365a80b0560301c0b10034020036100319200c00d41112004103484014080a0062000641100003802c488020f50030007140c0c2540d52129541c4424100300c1c10079908984420725030400d00824100d2600d80d045030b4a1503503d01d02510f000c1d1580d9000d86060700026441d80c02d005c407503240b45001c554203026070303c280c1a103802e010307040d1003070007082007804000a4841030412074203000d00420703550418104c40d000300e0204c03203038550340c940c03840007880b20089824002d1003a46803d00801c002001c1001c136081c240d01c22510b00c40c140d510312614002c540140d04c0b6150000d52a140401c5020003401c0d500742d000031007614584031548008107415407907841100200c807101c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 334172661 1106 334171555 334171561
    0xc0115050310270c050f10021c120f020d06080309240d0e0a0c0504050705030601080405010b091029032d0a06030204050609160f0c0218 60
    0x2030002c80103c182840c98820400c807054481c0c180288a04001c0e003940749400c3c20007c1200c043d03a402000b40b80401102a044400310640040c24405405918000e42c40b0318025009a0207040d200565a002c0c001c090200b100d03803c0d4011030f0607800610040c10956101914541e24415182400c50703070b03420540c01c60015200d000c1c00c0c009007501e00b46014160460128058603000d00544414865950314410310042c0e6200301d070480009034041000a80660141024a8215001b5400068a02e410a002c907011b103c0646000400324801038040011403c00d00c14030100a4401c0d9900210700c0e1050710740c420030f000c040c20380000d858240b50705002c10300c82c0c10010080114400c4102c0c0e900d051054025000300040d000590240d42444009459810203c0d4014001e00d100301d50b6140700c0c2c0310b028048402e02b02d600000030030031420b41c0843d070142e5540076040d4281040d080c00800a42 = true := by decide +kernel

theorem cover : BRFrame.Cov 333992805 334172661 := by
  have h0 := BRFrame.cov_init 333992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 333992805 ≤ n) (h2 : n < 334172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
