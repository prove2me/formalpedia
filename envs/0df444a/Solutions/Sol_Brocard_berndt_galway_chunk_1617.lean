-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1617
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:53:17.780865+00:00
-- url     : https://prove2.me/submissions/82b83293-de09-4171-bc8a-0b4dceb5d05a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 290647482 ≤ n < 290827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 290648732 1250 290647482 290647531
    0x1b06150603130215041a030c0d0902240406122306060d050103050109050d09060e0d06140a0506041a01050d050a09050d0e1309030c030804170c03070605010e 69
    0x5040d200c0682c1d10803280c0c0c0160b51139408500c0340140440415a507541441c80c00040300c1c0ba40100c52060705401c10074481d44d00750300340454031f010f5170321980007a0b690140d10024004140640d56a0f00400c120818802e0540c0e8034801003085801a4848002c4d02010380e0008056440c89030a64010048149501c00c8074040d1201e4a648280000c1c6003500e01240740c1140360484d242a002074403942c0d52425500b04000e410420a540d511140c2002c1c0403091516500030480d4131182140b90160040f560700000b0007075a9040b00c40829005621000c05140c075000c400001c0c4822034074540300d00c0c20105000f40810b220940c2105000061352150714044040c80e20b04090b001c0a00389040b020354403c01c0c8004240140310364040720351155540c050f4070703011030100007806c1685100c2c442182e107491030100000e50032410026980e58941030003210383d9104e0a0856001204229441484200041816055502200604205116a800700b01c2d130790300c4030350200d1501c2c0100c0c0c400382280c801c01d002516200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 290649982 1250 290648732 290648737
    0x509060111100519020f09240406030f27020112020a020c0d050c030d1809050105010e09060a0e0117060117060705070602070203010606050408150c27060a02031b061506 74
    0x105041858130940c005410300c0e80032a480138080c070000280200f0710301c0d800d1070f200c40c031020b043d0704021240e00450f08083d010341e02480703581300325000e06949140d00c021202c456080038049500c45000c03005042045a024001c10415050072400034200119251803001d46109550302200141d0042a410702e031002440081ea0007158203403041e10680c40c010704036030f0b42040802c0e4000026503030301d00c11401c02d501103440d400c0d01b50040010b40b800d0000501059a122400c103c07000b01c222020314064072844086400324640350400000480030300004240d405803461040c610301c1100089840f26a80c0c0c5103014400c0a4400c08040981c0040740030843c014030070800390081d14056900107141c01d0030760340081d00f10b071450703031141d0041240403504007c0340009009001d442c5450540034103852a018411102511544a404851400700368000c070040202d6a00e1307040c0004040c040b503586000c07041c1c02035900c0c0c20941c104c950003200e0f1881d0a18a0002150042c05002d00007a289400c1d00840300304445074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 290651232 1250 290649982 290649991
    0xa021c08161103070305120c07030e091e010e060111011a300c0109150e12030708030a0203040204050907061b1103010f0f06050a05010813060605030f03030105090601111005 76
    0x40b10b0b00c003079001204188010001d561007900e880369070310010b03008011a50401412450905010710072000441d0300304a0200c41c0410450703190aa45c1d03a205e5000721429400d210381d10030340f262100040307a045804600b95000700000d8030703001038043d02420381c40e0a8510b130a196403816104c84000403214200301c090342200500c4140038458180c18143c0054501410b5000702c3c540d980001006555540c106c01e01101030180325441c0c403804000d411018082c0c1c65108440350181710903400d4030700c100c5400d10aa44e2410741c4000002d9482c01c1080b0600082e4105507410382c400d5250401084110780c0005011040703c04540380c0102c0940c0703840803040281115041030341e00b22101d25400f07002d66000e11039211140c21000000a9201800141c1d00840702640c00440c015103010405004683c2c05c1803269511400d07000080c4502079082c0742500c0a482d0940c01150542b00310742c0d90041013803011001d90f05170b403000d0364008050b566182c0111222007030304440440c644c0081c003c0700b030b0521440c3c1000303610 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 290652482 1250 290651232 290651237
    0x4031505130212010b0f01080f061009120506011706040c180b0a081c020c060724090c081603020d060f0e0d0203040806010b03040215030403030f02040b0a021c0816 72
    0x552416004119805010703004a002030b5951701400e40d00786080300c1107282500c402c0c41c20207098a4144506110003801601c1e90b8032520f400c100f2214124801c40780000508480304032628401078510b05255101004c1c0950345150380c001900d8201c066001450906c5640c008084035001413034480c0c500c00d514a849058000c0c90b440e01c410210640380c3c880180000c08290707000704040c45c20100d040710082c00c2520307150300315002204501c0305031741c800094401464000350503040e070744801c200324101c20b01c6202c1800e0140d8241100e071003d01010103600e07022200058291752010000c0707508c00c1c0b507070010303030100950024510801c0e00c08100e07958400001e000014400141c3c0340082c0003a02e11b0f1142944001006900c00038007407210207014045a03005000c04451142981001e500069106049402000440c0008030000d0145482074100c00b40490715200110350f142e454800014596204d010030601512500307460f5103000d03640e0311754280030340d03900c0c0d8a0b80d4850703c94001440300c101982c0990402c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 290653732 1250 290652482 290652511
    0xa020f090709050303070f02031b0906120f01050c09270f1e0901050601090806060f22050a09030e030615040c1215050f0d1220030a1d0604031505 64
    0x4513501c00304005c10685004200740c156170550362040502d40907905d000002d011400b260003000e1a1524020710790450000c6500344c0c1c4612024180d82d240405900d250102c660800c0140718201e0044d0005040110701501c516901d5002081500c0f00a0b5015007615a4207601c00006140e00c003104c000f45802c1100c030b140020100c8007007818000d0100080d80e20722840c0c3d41d280b080c00112343c0c12101c020010440e070b101070090341c609000080e070a102c1740d0001794007840b007200304550b403004010621030354050020010080f82c00c110202c02c000385802c0078114081a05a900c5c03410702d2500041040c403c180702c1a041031440c020906110242044105010601c180d400800616a07260301400c0d410600d002e400170212850315080084156140d0480da001d03449821054020032050100441000307210700b8869034025a07605015403030315810302020201d00000c41c000c2941c5a00130b400c51403241c40c00c1c9640c503150000b642088058400d52000401d9000d08110029044420707400c802d9100300f40458095 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 290654982 1250 290653732 290653739
    0x109020f040306093503160207120b0a050c030f0406090213021b160e0a0903020717060414070513090804050d05061e040c260f030d06080a020f090709 66
    0xa00b81c900340790b000c60f103061031800094803455240c040688408007017004140410380088a01c0d0440c0700c0540310400c491407620b4440c9010303000708800001040c1c80c401d0740d14030342ca0b1800c00d54030841c004d44d01c880c00035040c075011622070040f20080e640542404a0145c442d52160754542000780084001260400d181c2584c0c15040c500510103040000c0a01540b11080703101c1440351800e0420a14048021080010044c000c11081e580d07955413200b2006000034810a10381010707882c1403001d6002400d030400305820700c51411400f0601c030b40941d2080e032041000301200c0c600b068441e60680205900081c4000d0000d00b54143c0d900121911405654554501622900410001598000141c40c5640058140a40707c00f0800c01445001c0649241001e582415a039103048400c40388034888148458201d802090300950444110280c0218215034890380f03100c1181c1e844e6040503829082032881d0480014040c1004176101d000d05034010820002a40b0360010890132003405401d0340f0400c1044100403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 290656232 1250 290654982 290654993
    0x6090b0a02040906091a1302072405070c121805040614011407020604090b210d0e010203070203150c040f06020a11041803050306030f0307060905070609030305030109020f0403 77
    0x1a0080c08104009659a4284940d00d81512825800701110628290400c20712201c4c604c2034200d891002c035590021030003071440c060068003860700d0280c040f10f0700500104554450000c0741c003541803401d070240300c82d942d03020058a403240d06280c0a01889142141c00c0c100743d128031000b90f40340e07542c149a448020b49600100b001c48082d40c02c415500c0c06c10f804802d41030b680102c13158080c5c035a2411410b2a01c401603000c68044d006a20585179017544a10081a41e50341c1c180b45001c03000c0c004d0411200e5603c003140070940d00e1005003816000708001007001050f9501c08000c4411641c0c018000307061f200030042100140c013900802c00c4640903400d01003c0303521102080100000c25090b0300600c0552240e0a281a04094882d1058401c07840c00c209200001984050800c40d02d800d0308109840e83e40e050302090502c000b00c07080903094000003807107200700310840d8800424070b0f009d8012035a43c1d80c0c9503101038940000c503020160110314144010085125160020905c40c0c0c3e54040d0740e41025a85c2e0b450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 290657482 1250 290656232 290656253
    0xb09120106120b090706050706150e0f010546120f0b0601091212051605011d03090102061b0702060a0e01080702030f0d050402060f040b0301060e0d1106070609 70
    0x1103030b800b1855140701d03014803442d12081500089984007410542c0d2130004050480d106000000740b01c00d4842c006c05018000c00d090300300084c518403c0824107403500c02e40784040b0074824041c441c403455001240c0300441703038009000b01201d1044a00d20081181680150120039800c50801222003030380c1d040410310110103070319505803910810940c000041c09103071481c4c2c6840001d001c103041180360b00e02007014200400c03240c243d1075001640c031180d11900d064200c54620612046032150410325210f07004000c41584030700c43c020684141024010344a104107030b228854145c14900592081010949200391051059141e5092808030b074608549035021030031903007201214402091103076403480351950300103140b10fa0106051001e145130101030344000c0c0242c00742c3c09140da0365558903400582152600000c49002104840e07440b91903a81d40d001d855805c0d8400d000307110010350350b80382c1c014a03405c10f50401080740b50701081000c0e152449405005a030303000302c036050701c003683c4032011017000c078206400d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 290658732 1250 290657482 290657489
    0xc090604170c040506011707020111040b040501031a011403100305010f0b120a0302030d110418050105031203040b0112060b090115090e090303061507080f120901150b09120106 77
    0x98901c220311041e14200a20701c2025806203040008102442c1c4c2d10041c02d000c2590b010061420320f8440c070070124010a0800005078220344000b40100c0c5550300000900200c44099800b8401c1658801302d40010744040c0d040d240c00300c0c8010807a000088980d00146600900c1801c0e0080d801d40d40380c035010300750f8080e2851503000380c0d5901d84030042400e01004030881c0c6000d840083c40000c0d2140c1c0c00a41e2841a0303040a941c1540ea640750600d540341071022100203100118030071003c07548610f003400040900303214140c032920516001400741003500041d00d205641150441c0b0880c1c0c42c0c000b545008100c18041165010f941d0341e40703007101740c0d24140d605d4041d200c01ca102c0e451218040d0700180500095801801c15070521400b0414403038400000c40368800e0b001d5034600030443d00040c0440076030043d000014480320010030000d00c3c4440e400060070080700b5041c0a001162074143e402803ca44d221046440d4584100409001c00c154241c010b1860941c041c00102d2003001000440d82101c10940 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 290659982 1250 290658732 290658749
    0x302031326030c0a02090a150e0f10120206070215070b0103061d060105100504180f110c0307061a0d03030f0c0906200a1e20030a08030c090604 63
    0x381c4040c284158000040900312410000314905020000e60390b940c0c1000f0000240301e645110300040d10251280c1205e040381c40b190080100b04d64846a01220140080755a1219000f8240000701110b1208541c5402c0ba543c00c40000001521502031001e594013645050303030001d046051342008042c8000080140c54000c280c1c0c030840d03504524001090340c1458641700802e13042202000d08011001c1005411540c089540c40502051950161842e0065030300c01014110640701c01d206103a0907401c0136103c7d00003440b041003030b600c581428540070302480d6401900c5034411b001c001e000038a41da01121001106202c1c0b450301124800000b490034074a44000c0300020b03120040a4441c66044c010b0f42c1c43c080050070314961a41c01c00100500800b60880d405490031292181c030007284805100845403160000100100e50302d1000680c9114803200404848103803807107040190031040e6558070400028000e0181001418070780340c045071a0009040e035104030104000c3c5440079070318240144020003851 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 290661232 1250 290659982 290660009
    0x70b030a0219081504180203030a02153402100e03071b0302091b07020d03031a1f03020f0c0f0703020a090509030d020d180c0528030f03020313 63
    0x1c0207004103102e070070480814400d624090040715010400d51a21030002950f0000b0300c4100030700e050346c884000e007002a40500000441c0003200740d000c991080d49448041902c2803e40321044030000003000c4413042030032140c08201c60b5202001c00c0e207119002640a104603904146184003036412035040d1140040903500005040c000c0210b0300351022460840355903100c540f94036540200c0e1880d01c000345035582071025040c101c81d5401c400c0c0d0a480d40c8540150103020a60818640a0000c0200c583c43c11008030b04ca8160050307528101074016650f000050340012800d01501c801d90180d0040020b0405046080c440b40001c1c0c5030030410b0400c1c2d090150010f09055155005100781c9131450707003203074183c141400304111081d100042110041d010103d80140d8615006140e0401021400d5502c112400401114001d0002c0f41081e182951011520030b00e540d10012400c000c003c150065151581c99450410004100d43c0c01c0e881103401c0c000d005407858418100400e1001001c82e0300b0150810914 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 290662482 1250 290661232 290661247
    0x607050315010201091707021c050604110d020307031b1a0a030509030c070e04020a0e04030807080c09090408070303020f12070311041413021b0c0f0a06050f0309070b030a02 76
    0x203007a5501d0214000380000c00c8a08030310303141c03150b000811740318210714082c00142c01e204645805c2405184510a0740d16540e1070384251507c50784880054030240c0e0720400303035220303103019140c0034101d10200355009005041445c51956285042501e041500c02c1544006100040401c2e051003940b5040e1440ba404965a0b8030311400541103c9001e05000c200e5030082c824860a040c00140c40c10a48240c040c204950f65103510010303030202c01c1904640141c1400105000405801100b02405072406031a2100d20f980c1e113102c003140320b0040d0010340342e1005e118404a00443c3c95803005080b60f9010345409031602d41d02c1490f03003034554010760401042e0a1040c0400601d180d16200305200101c01d021000d19203490b1108001600b0b004036282c612550800d0144070101c200b9604840d400d00c440708480c000840c40d440032039111001901420b001d10b003600f1300c0d40418034100d881c40d01604c240f80c03507071405c08414411108440e00000c160301032501c512100890542c00313060140d48100b000c240c000d699841c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 290663732 1250 290662482 290662501
    0x509280512040320030c0409030309031d0f060304020315101d0f06010f0e130903120c050f031009060311030f010b0109050433081606021507020a0506070503 69
    0xc4400c0c414041c9801440240006014604400807114000d110003105030085030000b03042070401d032605648139182100000805426400605e007141c000d4a0300103480d0804041d5108650301900d407968406c404160b04180c030714001c405075801500150485039480381d8480c8070300c0301c090f090f607220104841c8050100320b510ba10181d2406020544244041e990804a211582402c0043c0900f410300c1030149034040f13034a200b200124100840141050002d005500195004005080d015400100840107480b4084088d0040c100c0e40d85450b515580352018803c0a0240750b04098034914030381d400c5c1d69000844044074040d00000c0e41c09039681050b2800f030f042c101450039038000e00e402d040707904142d0340070216a0000614000c403901541c0206101c07111071000105174401e0401c8054444200d152801e801c00442541d0007640e04600031101000d1502c00040303c840e030b43d44601001640224001148000c0d50b540071038002c60240100c1e4800c140320ba07242420140111a607034001003020042222080c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 290664982 1250 290663732 290663743
    0x302160f0504021809040f1e030c02010806190e0601030e010608030301030f0c030b07020303012309010e06010c0602180a23040b06040b1801230f0721090f0504020f0d05092805 77
    0x6039523411070800103000c0e0740e02070250081142d0113414415880300081a40c2c4410100c460501000500302e40f005407224100d000060050f2031032400640f401c000c0c44071083c0c05108078402c4d01c0c4500002d5046a01e955500c805011111204130b91070070030391400000282c10480020300034055070300595103c3d818100340c49119661302c0d4500c07888680508a11107151a180e400c24107403901001a0702a940d0303120f0042c0c030b0b08034507004018540ca100190440e600000717000c4111101d0000c8510002090b900c070850105400f07006050003900c00c01c40410461440d259101062070103001d0815428039580300c2648100d078000c4480d00a209580da01820310545e4050120200c40d110708440490200b00d034070200710715014840054070300150000b8801c0a215090380e82480360340c00040e403882010b840020080540d1030b2880345400385e0200c0c1d42c01088070315060095918103518287c3c40b07400c180c05110780d18050580078010f80070500400c40e180144407540441407410668000d110300c00c64125161961508 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 290666232 1250 290664982 290665013
    0x2a0c0c040902100e01021c0c0209010905070207090207061b020102030604060f06021510050a1e0f1a0d060e070c11060702060f03041a130302160f0504021809040f 71
    0x562410164500507610203d001404110514080f50b0031600b110040c0e1804140d40c000344046144411101c4130241e00040c240142071007a160350220780d80c1da40036501500d0b416245000540c010001c107005021480d03000d03081c018011100490311803014000d00060004024407080140d4000041280c1800c080c081c10000780f0400c0010006949007110003510364201c4000d0084414491010404101c62024000d014282c0140110401d90340d4000000c212000601c07020681c0022001c0000d04014881d16802112205214100580080c00e1642e01a074800f00d030081055a581402144160380700c0d8000c1d10481c0c06407101c490000c55070400341510744002038180c0c4100c034208120401038848805032141c0010000c8140d8803510355140030030010090307059008040341d0a504004080c82c0030004403805070b011790251000580300d5620310b142d00c40701e0b01900450f103689500402188c28071b035004205170313204014880c40d8000c0b10000141c44040c140c405840f1050541c4448051100078a10441c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 290667482 1250 290666232 290666239
    0xd1e1a0f070c03080703200307080417042318102102030d0309020d050a0b060a050d0b04140102040519050a0e0124050c15010303021908030a052a0c0c 66
    0xa501c0b03250380c020600000140030f8010191104c0c1c100d103a400031a0342140d01c0104642c0002e80b03a00c0c0c4450f009142120459007500c00d8100340c0000c112145c01c04c81281c056903a069503000b00c80c10242021140c1020ba0070070039401800d04115500d20404800e401c6014038850440d0744c0009117400d0045100200410401250300e05c03503181c01e8016a400101e841d9101c1c0c4034100807500702c280380009003010390f40d004041d02600a440c584010031003489845803141900f11a5442c506440e0000d00c03400409603030008046042c0d04020802107140510203114030482100003500d82921100481d02040f00c0740340e403414504070808148010300d01010200050101800070402d258500540c1c0c203034096160000d00d041c14030340000710068522034400c0f030ba50917000070b0840d0564200000a48031000c401d120540040c0174050100350449509003e03111110307000b030b10751401c6407601c0c00d0850091078060100100f00115207007640000141c045200304500b50103824544650310711030514180503200003250711 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 290668732 1250 290667482 290667497
    0x905010b0120030415020114010b030708180d0305040c08070e10080c030d14070803071205010b040b0a0e0a150908010f11041e0320040b030102090d1e1a0f07 69
    0x90840c00041910100c6031220300c00305078481c5c1010301707900409070318482d403400e000a4400810b02d42d043c400210300a60055844849540c1e40a41d43c0002d81484803c0192540018031503090311840ba4011075002806060a170728841d555403d01c07450702207d070317010030700d03081c8400c0c2001041c51132202544000c08040b40078041700c054450020f030301c4100c51400c98051220621614002d00d00d82002e031b0707103c180c3c400c0c0200c0d0f81c0c0c00c0210000d8240360506c1c0c002020107003424000300b0382400704001d4504861a00351680e0070400007071010b0f26035044032060180c100c50700300d0001900700070000441c00081025218881d5460a110440d0300751071841a45c001081d0a040103049030b46c0e08082190111103441c1c1c051614114003401c02114100e0907403001d80a0862414000d000c0c1e2500d50491204000881d4204280c030b01c041c052500340e0003142d1409611003030030510800441c20302182c038505028480040000301d069076440c071560b0f009051010000500c41170030000e010a4100b94035401280d01e04140c0b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 290669982 1250 290668732 290668787
    0x603050c030f01031502071b03060e010b011d03030c01180b090d050d0c02013804180611121e0112050714030109051e071e14060702040905010b01 64
    0x642c20034042c48001c09203c5400e518010500e6950705417410581d0110941d14141800000503180b00c1c090300040c0e50041c0780080c49811200140325491078554185c40b40e017a5282090031101c4101d184000d0141c140c00208818006101c0a1150300b0740b01d1110700248040c1d64107400c02e003000300d01c0100801215401034000c2c01c41150400d003560002c2d031a065000c01c03400e8410204078058201802105040313076101e0008200c100d0000d102c3c599082c1000800e002c09d0b8203603c00c22081c0c414400c1071841c80511490420080b440c1c603000107a80c021040b02d13441c50a0784099540844070300840d503180326803070381440b0030b094000750304003d41c01081c2d003040c00045e41c01340c2c1e101d09464555911901e01d00e028180c211449646080d0800b800054020007a1441102c090300c1450011450311000b50441c06100c0011030458009800011140c0c258004110f00d01d00300340d480a42c400c000d0700b03181c0d400320741413159800690301e034081ca00c4040c0c4200004920000700300005048038807119040c0f040b101c11510b01381d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 290671232 1250 290669982 290670001
    0x90c091d030f0702010915170c0a08190603170309010f020a1e020705030a080d0b1002070b0705030f070f140607050a1808010c09061206031106090f0a0f0603050c03 72
    0xc1e000485402c0d1050f07503d5880d0710050303986003090361020400300c250003200031701580c01041400d90881d088030b000c42a50f607141c18409840c400d0f142d907000440c02001c00304008061011940b01405600100029095181d88a07403840f800c81c000c0c1c400340100c1c00401c00c00010700c20b015600d0a01c0090070103504101c1184000b0781049903260207101c03200180c450b1a00c01e903108200ca940200001703010395064208034104110540c1c04986045000c40c1001c1005615007045403841100d50419070143c1049800e05a602c1c44680c040c03038040d5642d00c414046082d031403443c0b100614000303114015807a068506842c00d0b4080c40f41130510119950440402c020b035098100e130855000c1d902c140f62510554948103504144500310ba0000806503180107000014582c01640b00c0301516405e0329400100e0780002c692100740c0c6c01038000202458041071120b03caa06040014000c086001004010201445000f00b14180e40d550704c4000c0314103c40900300910358040c46416000f0b03158049091640c81c0c0040c1c0c0c1d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 290672482 1250 290671232 290671237
    0x20708070b071b050909030a020f2103090c04110405010e032802040e0a06020405090c03250507050d1d0402161410180308060108040c0b030c0d090c091d03 68
    0x942030340d4400c0a07410310542c240e201400a0a00241172001e0750814621481d942d40000c0802c002500c0f640c0705c844900403002461b002e12060317070001c0c00c1c0304121400824141c7c0d007001c4d20090082c4a21406401d0580d114040d2135214200195610b40310ba10740000100088481e4200c94080d41290048030b4a019005400d000098007406190b0f14510311031003c94014400c010b81e8800c5030141000d91010044160010000c803102140d03280c2c075a88903003080200600c4141c42000c003115411400c1c160400b943c03243d00180c4481820842d041001076228142000c281d0885603000603201044216111012070100d00c4a8105a408604140200c182d4400242c840e12000c1d0100f2202c22602c0c40d0319000b0880b00c920302003c807000740400c205040541a0000001c10120042010000007800552040008074420b0b900018601c449500d000d82c0119203500c00703015a51190750400072228400b100e40500000244141100c1e10aa498080c80344110380b40e0105004240c0524a010b82d030300c2d00000107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 290673732 1250 290672482 290672497
    0x21017010303030e070f12050115060f125606030a24030302060609060f04240314070f05013009050102120c030709030b04050a0b01080a03020708070b 66
    0x100010961480600c0d03905d40f000f0303a404151140b80000c0c0205407a190f1408000c8030301c2c0329000a02403890600c1a990b00094140204800170300c41d40e40d44100540301c8c40c1e114003c21202800080c82e2a004207d140c1c0400f0304145142c06020899003250340803001a100e00111502c0d000c0c08450048003040b81102e18a000b0344491281201001284500006600200c03076081c089210002d0300c0704800105041c24040c0c88242c015000394000a1a06c0c18001c10003441084020b22000c42c6505100c00c02c0000c000c60313070f0303280103035001013104000000030615403501450040c5c00c190009954001e00302e150280d030790010365009071030440400450b40c01c40d003150794116a050000c00d800740c07008454441550806a482c02450a107892031040c00300c10750042c00c1d018400a00584141d4642c0c000c0042071005840e01e8002801540007000030030310000d2580c1e0002c0c41041610040c0f5065250a00544801e8016603003607003120320000209501009602c0080042401a01c0450300e0100800c1683c002c420 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 290674982 1250 290673732 290673737
    0x405010506041a0f03010807380d0b0618031c0206041502070510060303031401051e060c01050103060b031504030f050c0c030f07090b030102091318050a03020a021017010303 76
    0xf18028040d1411005540c1500440440c0d1901c940e503035241c40d903480c0c01610407030300700e44412171401e0311009012110810340c1301100c035004040071141c5602e0045074000b03d804d074401c65641c40f038442d040d6103080c002c00b0060f072401d60740c6040007240c2041600301130940517411a500c80081c1c00c0c502041e00030921560068000980350b1070200d00c43d1002c400303482104001003c90140c81d200c0c52180c98582d10200550303009540070000c03906009540303007000c4428021998032281074031115442e841301035003440c5103d034040e1619042803021111942981c000b82c0089800b240c0f100103030701c42410104003030001c10141402c1c2984504040e10080c003031441d088400010042c0000d01d98003008001c0001714941e50f0082c0031622410f132848145510340700079010704c4000c0b505000c4080071a103014020b40d244c0000050090311804041c08514005040d1005601d00b03111603408400042001400b8040c1858005e1b001b410702607150b4810400c0e888203a003214801e0103c218500d1142c888440c811605503680b50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 290676232 1250 290674982 290675009
    0x81e010e070c020118120314031312030902060706050105100507120f09030b0f0609060a050f060306010c0206030901050a140106020c0d0201020f010204060c150605031504060603140307050c040501050604 89
    0x1800100c408580c280650300f881c1462a50000c1d96003200103281c2201b40c0070b40e40d0b1100e00b80070301000f10198072094410107010354429204002280e54600340b80c030b001c3c0d5241000608040c03d50b0202c0d0b01504903910035501c140d559401007185041003101c04407100042d00d0190300c0c2ca1902c0c1e41e1180d80c4040c2101072000c2140c1d0040210000b4020040a000f8581200600705203142072105158154030031501c2d00d001d002e03c0d2010480500f401d515203000d540c00200201c50001d0300805001d0743d900010499030400070503154480140c0c64500056025120b204004983c901c0c0000c0d6490941d11000c1d5101440c1442c0c0004010503640441c0e20b01e0062000c072030600c1390354a03c3c00100c1c40c28042c61840c0311203500c001800171b24070350044013a503c074a1244900301700280c1e285031030108580c81842010342540180d04209820050380004550141c480c00b0700007040d60b02d035156240700f105000100709041c1e00c00100b260034070608000c043c0800b001141c0511242d070604000c42c07440c3c01284038280144080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 290677482 1250 290676232 290676257
    0x1407030b010e06062502040c051309110d0905030408060601260a0f0f060e010f0308121306060f06180b0904020a020f15061e0603040201140702090106081e010e07 71
    0xf4034040744d04818207212503100c200c0b0f032605d100d8000c0a1212040303101d1468a9014000305004600b0344408400c812003080c882403501c503038080648121202d01c1c8009801b042943c10b015040e1144c5100c0354003401c020342d02c55041c0f070036040c83c05c24041e00b40c0d4140300d141000003420112140c0c00302031840d6116800340d16525030903110005040c1c03c0710004c4140e0705013208004141d40c00d03032105003105d0107030f2100314859a0780d0021100e081c4681c000034111100400103001e14506c446071141e00844940d11080b0111000c0d203c000444400b5007006c1c000c41c2e00100d081202c40d610208428030140c01c028031440c0645003030900c0505204001d82c1300e0081d40c006c18901c0070345000348161201c0c4003414040c1c50707000f42c0800c0c400c0340800045622030300c03072040250500d110b82007034004030150010180001c2d1558496070019a203210300d120303a904607514100844e100503104c084105000b4403054552102034106141c0e0400082038080c44030340040b401c000100f01c180400c2041940095141c100321411031103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 290678732 1250 290677482 290677489
    0x10608151005091302030717090c010804170307030b0901050103020a0801061d061c111608090a0b2205010c05070b09040608030403050c0a060801120b28091407030b010e06 75
    0x1032051400d920111000c48200a618a074001b50b01c580039590301c605410442c04032518001c1015654000b55070300000003203482d54002d400060300280a08070107404006143e02049140e0b1040f10b1650000e074480003017624a00b0191803030390142c00c00f42019410a030300c2c801e0050049030144116410800001c2c112485800101c4081540000c060840c9566602446016070350090ba6000c0701500b40c908031095510b240840e0599001a42280d40c008414400e91500b851580040445503808070321083d00040c0c43e102c0400a150300007007200b01e10f140c2d2482ca2000300c0c004103181d001c94184031814203001d00043c00440e0580944400551181d124540031010400078038140d006a030162100240101c00c0c800001554580e0724801c071980100280c036240121035244082c4200c00c1414041420040000c49000741c882c3c0c0140a10900d214441030032109030340c04403c4603481000d003a40c6614006c2400380d02c0c00e0081000c80300f0002001c410345540d64904445805100c3c07500d03600b0040380413a07076580d03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 290679982 1250 290678732 290678737
    0x9030324030708030421050a080901140703110d03020309031c0204030204060305100b1504050603091c11120405010e060a0c05010203041a13210c05190308010608151005 74
    0x5101504403402e0329100c158444d80c951003409025004a442d1204448209411015090300ca41c024003510b00405541d55200a40d040344202b54180201010b4910090852402402100b8000e584028010310480c640301d0610f41845c05507000c0600400800441100010889403003c0990f003480e0389203100400828003e00454000952003401c125000040c0a400215120300804000d000c004c200b00c0942001103040c40c403c1a0701c100d68040c00108803034580302c8043e540c020742e800180e40500a0300c04408070030040d0000d5a08c0861949a00540541d40030407585074494140280c00d4035003810140060104100c51600e00d10582e00020416941ca200342d14002e58564060000d54407070909162148450810002103400000d004000400c401408605802d41a40020b085030f40c3c0b4004c0c0011400061514120500f48445a03122030700041080101185408403c9070401204040f844d0042100c0c0040c0d2240b4104444013091100ca88404032035150706541c111112085010110801d80d02030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 290681232 1250 290679982 290680051
    0x1d120f030a0e0102120a0c020d06180503190207030f02150705150421080705030a090c14040b01090e07031d010e0715022409150405010204140108090303 67
    0x280804901448819002542c840c40000c0076025500038414020481c0d426004407440800081c003808030000140c188941ea14440d00d000d644c011070040707a2843d10740c0c400c04051704111829800054407542850003007102e00c1e195121031005d003030302c685161540c030080102c0800191244c138000c0d68100e41107800c802150003044d4401e0540744003c8e071104102c00c00b590308603400d6850b1611003c000b031825540d4141c00500800e1501c8940f0b030b54499500031107440e000104071301c9150740e80344044008500c240b86818002c2581d41d40041c0704a0580050100744c802c03d01c500341c14010340c903038144039032048840c01e80e520065510b00050540b40c4c074822407952166204904403175502c0c18002c1c2140c000f001ca0f284c1d00744c4500c0782002c044111101030407070741e030502c0312402080b00341001d2243c4401880e0f10017154000e01c142d4120b03a0701c500700444941e10164250390858040e035000608000e00c0ca03500c0c4100801c9d40003407c1081d2186403494250b6140c1c80000d007060340c0c4a104a0300d0030400302070410b408240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 290682482 1250 290681232 290681263
    0x1090b01060f02060703111b0c040e06011a130303051312050d0306060509010c031b0515090f010902010c02060903160f0e01050409120507031b150506011d12 69
    0x155039203100c080c02c0d6882030040040140110800150160b001c0d010b000c3c03580e440c90240324903001c2c20944001d4488080040690240034071840c2d141e00343d8583c01900000e140350000341c41154509120001074118581a10301d41d000d00b0f0110750100500040c0d41000c40c0d03010b081c010b40e1030031121882d11005815030480da00ba210310a0300c0d04248000010441884c042d01e4500f0009503440e0007007038410303000301c0c0340c114002074003803a0b4400040d01c9162543c101c00d009501e00c015540d184da03901c0d810200c1c28103910009032001c00401c4a090802c100051043d8850002000119003e4000034034000d04102c000c0d018079000200d90040303072010801011010740c000d0b088417182e40c85070704140b2024828400c00020340300e00300001c10700785020701c540b440b81507000b404000c00145040741596181c221500540170b010139010381082c080b1548100703500e014410700d0400e4010303000141000c21100b0140c64141045000b507810b0070203820000c1d2030701c400304c400c4414070052229040803031726015449001502 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 290683732 1250 290682482 290682503
    0x207060f0302070218040203010c080615160c150f05030c0403080c0c0d14100e070312110a030f1407231e06010611030a0c08090109080319032304060e0109 68
    0x500d00170000403d406144210000e20010440c50021200c0b0002aa8003e50000c010200304078030441100080001101010020020352503644030070340084165446080341d59900c0c3e46103031100d64030403840c0d9809043d5080c03060940c204040d01c2416409140001402107200181c02c0482a01c02c0000d0907040500503c00c02c400e81e41032806d076909510500d01d00d0b400e48030b00e019100422686000d03100d490448100141040f0740f5507100c000890b030700700c400c403c00d00c030303091903000503980e01400036010050194403051058400046c004100016508003e04204014004140040e080110440046800d26801c00c81c04800b0b0038540d050095202805030344001e441c1c0070038040d03080803c440d03040310090b0b11041910400880f64548070302c02c0401e444d000030001158078000031680c0019014000040c0b401c040450b88400f40c01e859070344802c2074040140250144020403a40c5405040030b840d640100400c4000000c28050750681d1000d400140758649411399100203c0c0c01b5484000c00340d420010040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 290684982 1250 290683732 290683759
    0x14130906090209240907030b03070e04020108370608160e0711280c06020102031807080a0213230108010b031c18080106060203280207060f03020702 65
    0x10188030000320b0183d0b000f500010666003c5500c1038070700d400f03c0704c2404c48a42d0403000300070708400c0081c092024035076241c0f108041c03134400b0400000548800407812505003041d0001401c5508014105019024501d0406450301e054610b090546402c101c0d05c0c0c079800301c0d00030b44240507140c01d40000741e682c81043d840c4681c4100240c2c248040740c0100e0300b4403500381c032544012100c0c0a586800321003103a10294880c1111190340f086a19a200c942e9480380b44811240e6075015640c40940c8140c005030340200034001c92083e410101c031141c403580320060085518040f10241ca540c0320440203803040e80c01e103810010300d03c1d140c0c00a0710303080159012003035039031080b24030003242c07400a0181100543c03800b01580d01170b00740001c1d0811078002441c0070f0b14181d070100c60f003180d806040940c200700b0400e0b408400513420074240202c4000d0071840c1c019544800c004c041081c3c0252040c4d0103a102c21a00580500b07640f50007240803800d0b105a0b142000314a030303032810150003034803074074070000d4100c0314020441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 290686232 1250 290684982 290684993
    0x1406011b0515090106230109051201020d02030f040303050f040302061f0e0709030c0b0414060703111e011505100528020105060f04050412030209030f0303100e01050307060207141309 80
    0x18050f5070f100102c44c41d50340255151a0000c0c038142030403d010400915050000c0c2c5480c400e021440000e42b4005031402d000a40d002050ba003082d282e40c0001c50a180030b0104058140c010310741e01c0390200c0803a070001d203407a88000759145005042c8503118085a28803042e09d10b40c801500000d07020810261041e41000d01c001011003403d4803013174801503c100c00200c0d000300a04c0407038003154003030314090005c450b81d401088090b5000c00421428003080605070303080f120b0240800c90000000c02d00000b903503100400c035182910281d03600303415a2030195005002c596501144542c1c02001842d00c01e84488d0809240000e1480f00310041040c5041c081c0700325a016415000207105540c2502c18440d880890f50038030007680c20030341e0020805130030b42c411203d03020300c1307030b8041c22203114004c084845503c0c41c0c961650842d0301c11358540c4124243c9c0b200920143c00d00d1000b0764010801075000b071074038030302e00388009446540a005644080402c0b01a02c0701503900da4468100d9400706420800a40c612864030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 290687482 1250 290686232 290686241
    0x40b0604031b0312021b0f12061503070609051507030309051002040918031b0203120c0a06060602060f1b21060a0906060207060804080408030406121406011b05150901 73
    0x1120b444100c00380c2108107038400b00340c0c121303044080c0c62201c0c1581c0308601081900541240c4540d08440e9545072303448032210400445020340842d005000c8403551007000d05060030015005007041c805801400c20154880d1030120a400108500c0652514881d1400320301400e000341000e001d030701c9490f4050019001642c0144121200d02174100024503210407001ea00a07110381c0d0242c00300e11405207940409800301500d28219200500b91703094500e113596101041d411802c49120b881c1d0000076100c0801601d403148002a11140c0000d00161030180c000111502d0004c182230144074206841002c6044190103440304550f8044103450ba1a910001e104030390340741161924465506a040080c640c16103224003420348007243e000d01901d40c14010140c8002c0c001800c100c80000c03040000190201007440070f0400342c07445c2d6544074802d409514448085d5401031002821208064003440302aa03005080350703c1810301c0c5610b0740c5880145007882810502036409442e84421407208020000006611 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 290688732 1250 290687482 290687489
    0x3070602031617192408010b0f06030402090c0a0e060d0e1b061e0708040801050402360402030a050a03020f1015140319060515030d020705040b0604031b 67
    0x40d40b10744900b41035000d510585040e11040c1200c6024007a00841d80c0180d00003405c20541c05144a4084002030700008120311107900c443c1c604e9550308011081c81ca09801c4c0071440d0082213540c00c0c01d5040603000a41c0f0068080e100e8051810001044a03000e4003510b81e03455003001c01042141c440c3e0014482c3c81c040d002c42d40300c0030150f00030003981d40901c691001c0c003240590000703070480d82001d1980180107040700408441348403080050040c180040c80c0400104040c2a01c01300100340741c14148144121140c01411162502e0300384c0d501142200b1501050840050383d400326080180c0f124004241000401c40d8041c0c15401810b074090207041e00001d8090320104400e003200c070505400b031030200c11203600761402078016422513802c000d8031881c101d0a85001c1d000600781d40c0380b9160f02440d1411101949002c0320070341e44800422102981041a0b40c10005090700175094000310b104000307445021500800780b26503a41d80840709641c0b5104140c1e03016507401032084403080b161683c040b600c44c1c682c0c407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 290689982 1250 290688732 290688737
    0x21011040e060607030c0206090d0503210c16080901030209060c01150b0f0d0905030c0a12020d05040b0d0504080c030c010218060901020717031306110d02030901020309090405030706020316 83
    0x80100b007142c03c015040b07030500c41e003541c4c0d04c1140d04000c0e8200b0039103500510029900090540c0d584002c20301c18401020300707000480144040d0056000b64a0203aa00207003003d03514541405110441c0040060a140c400d41c403000c01070390b41a4520040c0e00a01403526041d402950110700620300100561001da140d80a04c5040c0340c8031580c5587c4e10200d4890702c803031581010401c3c04490210b45403900041000d910a20540c0e04005031081c0c600d00d040500c0d0b10030344654a022001802c01c54040c0909014031348540381c100d107000d06215240d41180300f0025800d140550303c0b0000f4040c480b9600c02e446100f80e481054a0341c030b409180c0b0702e5010b500321410b10004046042002c5203141780c40e0b01101d840200680103880054a407aa0000503210f0713400c8600c80a00041086400f085d15030b242d00c501402e03050300e403c3d0585451a08051421b980c2c801e200c02550f2007007050041d241e030000f0075a440c030401103c0350010383e91030385061130440c090000300800140c004001d124440404120191500a082d03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 290691232 1250 290689982 290690009
    0x9020f040209010c060b150a1d0d0305071101030917070c0902040311100311040e091e0601120609083708040b041b030309060917031902101104 63
    0x4000c210403882a441c41c680810310140d01c05000400380e0304003e0030540002d01d4095001d69440044c100c40d801501180001180483c0901002c0c40d4140c600151500c15506007040881c0c03a600540f00f48034810003d0402d01c210210410140c1c401c2d002485290340c0215030307a90740780c009985403291303410119080382c900b0490000881c00d480d0034405d8a084a41007091840001c03178410901001040c00c1d048882010b03103407c0000c1000d483d01008100800c1c200a0520581c60700941080c01d003002e048007094000c80400103050071840004945054132881200150000303020f25060008141a500c010003100f008207600c0141c40505206008031210050111001d40700001007003e46c4540a04507000714201c90003040206e4100e0308465400703407051000e80c00700040765000d00c0200c0e01e580e00850014001d1a8140000c940c13211000c0c005041d9402c0c0a1400000140c440d501da02030004004081c280100c5c180586a1013040306241b8460424410451076001c0e42d411040303036102e070050b000d086108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 290692482 1250 290691232 290691259
    0x303010503101a130c110a05030d020705160b1801020604051e0c0910050118060f0c0317040c031704060905060327070914010b09010305061f03020c150115080a11030108010902 77
    0xc40e90b5031f1415400b002540c80e064012260b00c0c021b4101c10001e40b00e41c450301c2c2c2d1080c41c0899451030302002e0000c20a1442e25070766503004110f2602418141c00e81150005810300c0005800040c0390315221721108165145060410f1440340703010304d081c01c615440b100a9081c80300d004e070044041016180e003a0b8407842c0c1040c15013410300c042d045903c200e8002841059564410610442c0c287c1d0340d0b123110b481c26418440e84040c40109950003076030b042d00c040e0044241081040702d004803506800850030305407030038030b46484406021218140f0440d1b0141b0700010015445085184a040d41103680d035089099079620205150b550b1080e60140d50801803620503145005c1c80e28412081c102e035510002140b404c1007000c0110080d0001810070794010b0b0005141202141440c0f00317403001c244a0365401038036044030003100ea1900300340c081041c80348800200144550160200c0c1a00840c081c2d041c00801d0f51100403600300141820050110b00140120000c5121038064110310b220500032588040440c08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 290693732 1250 290692482 290692517
    0xc030e0d05120106030e0a061406030c013002130e0709050a0e0106111203090109110d050d0c0c090911040f140a0b010201090804140a080303010503101a130c 69
    0xd054140709106540b030004000092181d08480c4e00099103e0549502e43e0050382d400c02622583c030704c20701501c030751b41c403c2000a04040080c0b001038402441e15404d2422813075400c042c41d401c03481407220580d003080100001c041160b01261401d240e0086040e082d15a10a031904003414199944000030301100c10006d1680361071040c11003a2900303000e5000880e440d0040585400f02c6040038400c69010354070380a0704e2070b01c610f4061480b40341c03084004640b6003803d00d0050364030759100714801c0c4209c02c002441030100e1000075400c01c161a40f0300340b0f92421151800d1000a0301800e52000f03002c1d9040c013440700100800f00d4201c21004109403428001400094102002d59081da492007013a8803107030000501140b51a041050001d0b0180000150410340c0d4464400b030341d11070341012a100d80c5e43c65404c005414402607410043c504000910b00711350400c400641c90740e410603000f01c0380c80d132540583c50740c80081d160301201e4003400030822001c1104e40e15003080030f81107601d08a030100b021003040040215 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 290694982 1250 290693732 290693737
    0x1e0315020a021203310611040801060803070803040b3301080601020604030f050313080d0204031109010803041a0408031206010305011a19020118030c061a010c0204051503010c030e0d05 81
    0x4018000c90000c540100e06000341403405c0720715074100400c0d104000000f082807440385000b0011100103281d52141044820350035540a9401a141603004111580c089404181a25000f9a1010959040e62550342c100308507190403e2030144d03011701c0304100c501804000105a5035041007a00c1c0e181c0141d82d0b000c01a40c40c0c120460300500811003680241000510a02c02582d2005c330466086480071400d440d1070700581c0169101a8403141d00003800e00034840e21580c0c20000b10740171164814290305000f54161640281c0c440d001d8030001800404000c0100c02040d2006402520126503d548480d10510703000101510290b001c68504000032440201001d2101940021400002c0c9800d0b0703020700c01d82d150b100c0480c20301c2c1107551312105101d8424640d0210030300030380a95207281602100e81401801c9402c11210106c44074041002810076036040042d40210980417100040c46943d69000840c1c403107410041227a255280c103042084e1250158007071004074043c9001c07a6042104c100f800d542d01d2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 290696232 1250 290694982 290694991
    0x200a0c14060706111603030519020c031801030609051e0c1603080603010f1d010c021506040b041407030f140408030610030605030a12020f01050c041e0315020a021203 73
    0x104040007120085a03454110212840c220049130f0304d040c641940405200e144184110002601e031403e102d008461244203e05140700d4141c21441c06055080181d07503441607050354042440a101c4d8602560b0103640f0a5008100c1070030148090300e01a980480300d5050304100c0d0b0a02d20340c4401254104c400a0b00343e41c4944400f001070840751013551019240080004d06485d0b040d07491703187c0050403004a004401c4e031414224900d8070002c500e080640c1c250307142400510b0443d0700445031400d1516841928640000301a41c0018550b240080410042c040201100801800c0c03a014429081e516500c00404544c0251080010481440c083e032000881500c0c003500c007807414008110140b5000640d000d14844130304000031001c4e5140c012070300344a0004819110241d194081025480d0140070406155442d00d00820540c079110040190a02941c02842000c003440300324032080c0f0802c249002d018580004003882c0c100c0106050744045d50141044100500942c00001310104200d01641d005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 290697482 1250 290696232 290696239
    0x30f09050306043e15190c020102100504030e0907030905010507020619090209040314131805070e01020d030f0e0f0a110109060c170f1803070501111507200a0c14 71
    0x213458101080201482000d03222001d02e0004014200f1588a040540c565020b25900d50f4100002c0e44c0c0006400c3c01c0c2102c1c035501c100782c1080100000250310401421040074111115921511003120440080c0f62520004250350302c0e1605100100340c00099080c42130300050b00b41801c0013140594074064030031a000084d00f00701040c1c04140000d000f00c0030060b01e529401c14503801c2c40f054644941c0307910120780c445d11003490130302c80c501125117941c0110b50340301816045c0441d8094003100000d5075414079034035950406584050300d135001005900040751400c4841d080311460030f130642e10982c0f41c0c0c0110004480800c1d08800301c1c2035030f5019640b01400c4981903201d00034881296296902ca000410a94140c40e01e8104082c80c4500d100d000a001031072092a10b03a0800242c0400b41413034541c01d40c010340e052000003038840c0d6045400041c602d1008008a007244100d44400d503055405022940000001e108803110341c00480c4800039038801f100b809070b1200b043c100c0d43d8030b04481d02200c1140050b0b40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 290698732 1250 290697482 290697593
    0x1030606050d090f0c03060b1806010f03090809150405120c0a1502070f0b0309070e011a070501060b04030b090d0e010c020108070c0204020f0d050f06030703030f0905030604 76
    0x82c40441c0e404000141d0084c0e09001c050810782c0e9030400c0e5001c0740d4000725603080c0d641824131450300300407080081c91030045154034900e080c600c002800900c10040c201e420940c80c2c003400010400742e401079170501440a010300008140392510f040058100f4000c00c0c2c05608401c041c18082c0d813001401d64038000014208034a094104685440c1c0307595190b0b2408290711074010005100328448800318018000e071806a074503401d101000600b8004907a01100d11358001c940144040c00903042a010415428944140d4488003464894054410f55000c1b01c84e00002040000a00110002551180f410401901c0c0c00000c00c0205440310780c5800c441c5800102585c28050055001c0d6900d603130030600341e042032403182d112980050140d0380f0001880480c00b80204113104407100c0c3d07002d050b4109262076241d603018a04800440e5413a0302034400902000405144c400a0701d014070b424901600c3c028080e5100c901e402c0c00e0545c03a5800003006c07142031501000707405110b04030380002c5451400711004940d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 290699982 1250 290698732 290698747
    0x6070b011509030506070e030d0801050a0902090f0607230a0f020603070318080409110f0d0c0909020c030424210e010f06030501200702042a09030209060103060605 72
    0x48801d00d070000c078001030140001c004408100d04004c120310075145a07490040074130100f0280b500308000c0c82010400c1c40b524030b0050025a0b5084c5c111000e03a030201000503110981d0ba40080c1c049c11a4100150308800c001441000307000c00c401c1215507035411000ca011040e00014040c035907900d034408014101582c502854030061416000035504002e4915001c41d115070084045400c54441440484034003500140403c00d101c81e9005405540d0402031515041c1102c040344540700303103d040d84a4098507501e103400160340740075140000140010040071520382412200c2071f5907960107802145030568603101142c40da0130803070012623a400c90596034542c501207100c0c0788100c00320009100c40e1a1503143c1e00e07503401c0d880c0300344600014680001000314509145043c010308403441c094000304101103c402000b96401c0100c00c0fa40001c3c0e06860001e400d003582d181c03c4450079690164003030911a01d50080d9001070707100d2441000e4a00848102415858000040d01143c0e0300744280c0c40400c9040c230100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 290701232 1250 290699982 290699999
    0x220e0f0903071a0402012d0f0201020418090804030f14010f0203041a07140703081005010e0607031d09042001030203060d020d0c08150708010906030201080f061305071d06070b01 78
    0x2130381041c4113051048204e094030480200c2404411468084101c5401414000503480ba6928544c0c1c1c07081e0000b10315103801c01e8503848a50003c0010b5590b0a07485d0300074170003000303e99821900110340050000010002901d04840307180201e18880c030f015804c082c99042202d00c50320840b8003d580c40329551010986080001480e503100525030000e20440141041c0c440107014001e100302480b9a40e0100d1a14160b03040001d001c0542e04400e04110500101030410b03294002200c51503a09170409804a0300c420740b10706002c02c103609040d41c00c0315a0405000800c5405800038014071840141e0700340e4560030400440407408100c1c1c0d65a070011001700801d0142c1410a0001ca50074001d105044d180c90b110106180380c1400728001104003841c9104000740161320002040c05000201d0f0b090000c0343c9150002400440007070f046803141e180c2d60020601c40e44d549201c281c00c80044601c1801545480c180180c41c078091718403640f050401c00d06400d115450480c0480320040d03400440c20b0030303590030454039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 290702482 1250 290701232 290701283
    0x1050109120212071401081f0e0c0427050a14060d0606090219092106020a05070f08090a1202030d050304020d150504110103020a02060a02220e0f090307 67
    0x2030341c101c101500c0783c600300c0c0c0060040501400b0500041001e20b80c0d005e000420a21004107404540c0101080c20340d10080082e02903001c82e040b0142d03482440d25070f60302d00c07600d620907940141d680c15104040c05050f90f21420701d804840300442c2080200d5916540541d0954140385501c0400219104c001041d80c9408541700d04074034028000047e85544940030201264070400700800300c0b50408000340c01450380850350ac0058845080c034541e103952042c0c80308820780c00559005110350340105403500000d00c1b4005980ca035980008041c52000c0c0300d0308011b503041c3d10921180380a03944444002c40d07159444c60b009070040e076001c0c00421110002807400c0f52503800240007213900104944034040400c034402c08510a0700f24004d0006418149441c001400c140011701e450305150040c0004070754240c001c2029a0b1140100001603a035040e4008031042082020501a01340b4824805c0402d4228440007104d00ca00301e40e82100429407500c081156503030040c858003c0c0b04001080c1d501054484d403111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 290703732 1250 290702482 290702519
    0x1306290112090f061b14090609010c020d1a0603120715020403021905010e1e010804032105010503010c0c020310020f0d180203121e0f070c06080a0f0501050109 70
    0x180065201c080755038403810501c3e507510540f030141d1951940551140c0d0141805420308490408011441ea5141906154020000d4280c0319a5000c078008642d64040d00080e0a842e40c01000d1000d904000e19003d500c500b1113a01d0919041c542c03100141540c200012210162030258070703950b0922205a0f02e81094441c2d00c124001d5803034013480004010303118920038036020040381401040303080c1041c0004020b0300b1040d011501c50440604c0e04050b6401041c4154403110f820b01e040c1001c0c3d5103d081c01d0b51010469010b512041c800c81e00660311848250380018140c4400f180207000100321117208461055414a000e503240c0c00034050494401c070294000c20f6040b407081c140c036042a00049062003101d00f100000c0714101d4401220038210b260038000180d030200e40110701400c001b120f100c080b503041c02c04258004901400914159014450720a0f19401c584c0050540c0d0100d459030b10040000c1019200c0140a0b41071402041c04070743e4900885069840694501034136a1524903a85820149540c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 290704982 1250 290703732 290703767
    0x60e010e12010608030705070e07020309011b0203011e09020a0f080718110d0203061c0b1303020f06011d090714010309081204050c01090b070c0b070201090e13062901 73
    0xc3c00081e42c440c0c148042c00349140120080d2805924202c6c295040e40801018001103410800c01d5048613a00008694401c1a01c0754a80c05080118070200c1c2c01092190b503060041e9400104120074480c0c4d503001503181d10720a0341c038040c41170780c0c85104221410460203401c11581001c1e40900034231400c0380050b00252260040400c034001c0350220301c062584980d0801d1a056000000c1203110b003070080710b4211200781441d03196014001525412000c610140151840380c801c501c494041c18402c000030726100d2001c00550700c55596a410031510303448251081900030b40013000151510501141000844201c4003207421049002c078011002050381c1c1e43c007256000414403801c443d00000e076108511561107072000748000382034107001620341d030400c0d07100d452513200412000380002d0101e42a50211401c50b6005500c0300c4d101c1c4010380d480c881ca031708039150171100c2404100450048161441c051070007a0b00c20405014040d0b41c0d10b100e40640118039a1051503100c060b41c141d4070030840301c0c840c1303580003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 290706232 1250 290704982 290704991
    0x601031208040516320f1e120106030210140919030b07030605030105090118020402030c040e0c0a08060a081b0a090e03071a04030f030f18050115060e010e1201 70
    0x203600080040a25004141c188900c0d0489901c0000148005540c2c941741154042c003140316580092a803c4140002502441b60502c0445a00213100001440c01c1002402140c2400480550f940280141d20003039100e443da030243c544641d400381e010a0207443d0151881d616141030700c801e00035040c890714948a17048941100001c0401c420341003075070184580e83e03000310758145840201400e4450140410072540d01d0500144200c14285150151080e0f060314007503101e5aa41c2c3c1d8100752802035a00c20308900006104018000000500401234029262551103940d03c2c0c10040c408030a020740601d0b002c590240e5812145030f1604800355151400081800b204591514411400d58102410744000d95101045010030880750803064546403000b01c481070030364902503c0092021008d51071603c2499590351164010304115000000c680000e4403040a40c0e5503c6e00d40340b402408182d52190414010703000c041601442502d110007010016034841081004d250200040c2c10034604c43e6119135940e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 290707482 1250 290706232 290706253
    0x2070c090c0c03020f0609030d0b0409060c090801150509060d02030a051c02070b0c0706080403020a0c03240c08060f01020109290702010b0d0305071103100501140306010312080405 79
    0x840c001c804014146503542c07034102c80186000b9190000050a20100e60400300c20000c0031980001520041300621030080344108605000c10000c01100e00050300d6682000d0001044542041590013100c180c20002c003c160409824000280700c10302440b58010035100208246181030f500800c9101c3c001002d0b00c0d46940d00c2d0b501c403844c1205440c0301580d80801032000c0400103805001e400020601030f090140f515454000103030f00c2d0080c5000c0d0500340007a803408103041c07610801c840c1e40700607032254250304030580b28107043c441c0359103a11440158102e00144091084110b01400921404686072070009440348410000703201d1030894060304641d83d416260001c181032031911106624505154800c103002c0f883c04490700d94004014500350b80c103144070501c2e2a101d2030780e02900540c042c94255220110383c9840041c480380380300400d616100d200e60045240481e548494100d40404201546654821042c151900024807000c0d0030b22382c41a5098075400e004942180c2e009126100355240e6410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 290708732 1250 290707482 290707499
    0x90108090c0a0806011809020303040504051003080304050c04062102100e06031914040b0f04081b0c030705011d060d0e030a0e0a050a120210020304080f011b0e06040902070c 76
    0xd42d07078000403081c0d102e00300410801e000ca400307000148040080503c4441040d4000c43d9492289220300c030700840d510b1000400d40c21a44540d400039641c00041f02e41c2c0d9040906007140e858281016580c41645018400280e0806001c0c0300156040320116591441c001a001c010000743c20078412814041d00d101600d401c0d58074a801103105081e05045c030030b01ca5030100f103201c00f281c9086c8440b02e10100c0d6013040c080841e400d0500380380d02000c50404000c035a541e92a101c811070103010214030a101700005a40c0c51200049034070140c044040e0121807400d036880d1700444080f00006e00781e84040c8401450101e0b1414084000c1c21204405c81d00402e038201801d5078113146502000180001a000c81000007061905c0b940724070040c00100d4181a6207030401c448910349200e0058021310840c04080d5124080d802402070387d00034074140040d200079050031050075028040c1d1101560340d0080c517082e04801c4178000d000c4201811000341620781030505180340440254454a0b040d6010b5900f1200025440d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 290709982 1250 290708732 290708749
    0x7120f06050301090b1e090a15110301030302010b1f050a03020304170f0406140703080601080907093201060917010603020a09020417070e0a230405010c080702060408090108090c 78
    0x1442207400103820311b0965a03150030448001040318403079506105100b010140040c0d100e04083e0040d000032380030b01c1c0c0e207107a50340101f803100c0d0180705000c0084000024150194041311005505803041c1d192100c3d148440c0e08401012804040030070414091a10071920903400f45901600c103452003c464204d00701c0d103056070303049011220004940004d00780212503000b00d200300e44051800c01d450034190141c2c2c01400c150b20050096040111800000c1da91002c2040080c00131b080000040002c12500103080c080d10700840c495107680c0020341669903c000c003042c2d00c2412249107035640480207081240c4031114001c050200000d564039103101202503522400c24400402e009030b00140d455240011030081808101a020030b6500410400c01083d00d541c10b0055001155400000d06906c6200880b244050701c04100030001083c1780400003000340540c0400c0c3c54594540b1707803400315501c1010807a07440750119802040c07070780c0034442d0b180382e0b50061080320f0300140c00b0401d40c4d40030550030002c0381c20b10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 290711232 1250 290709982 290710001
    0x9080c06010e07200622021201020a0e010e0f01140f13091d0705150d02040b13050909100f0b0607030c061b08011a160b09010b0907120f06050301 64
    0x422800d02440119500000600342d80501203100004d141e4120900036158900102400032106800040e603805420b41c008540030f140d03006040c45205008a03034000e000303401c04501600032a0040180303250941c050a07807d4a80c0d400180250812504100111074a0010009544c00c0c040240719009501007540301418904c400d0b08210343d805480c241d05181610140061002c001020800c242c2030004007003203000603944203403194440304904a80e041000e1040c480f20b05402480410b02048641c102c400404910011840034007006407030300104401020151400071541d80300c0000084c89045a41006003a0b2809800002d00c1300c21070f5000c44c0250f44013000441c00100340b22030f20b50411905201d000d40320704141c800b081030180c2851014241c00018000c0c5c14504450b50f030301c5e051107816841119001076422428240b0720300d0398605402d07200c105132601c01c103a50a0500c00b800c00d0030b0000100384070f90b51175521001ca10015041d4000102040b1401c402915140c500c0461603460134080e8030701e02c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 290712482 1250 290711232 290711249
    0x6030b0a08100c1b29010e0708060f03070602030d050a0b030a060b010306030f05031308010608030f071502040e090708011a10030608030a02071e050a0b0c0703060921020a03021009080c0601 83
    0x4426000c0c17101c0715180c111101c40c9421000005010440301003060300d5112404d4207000361903860300c5001850350640d0155042d81342c0700324900454056800b10260280030b011010600c84c40d201d01d10818103580c41413500513010b6001040b0b000101d2816000002c2801041c100041c00b0350300e940320240c00d4800352000380c80550000070000d240e0801d4240001c01011910000c01c242410005110b49902c00c4c03401c801350100340424501c0504c544035038400411482110115911650340c066100e61480864414015004603100054622018000e041102904000300c06401d42410100440008400d581d0400c0543c2d902004c01c410303204000610254001d07400070406c8910309030030071250083e03010103415008048803042000344c4481450000b502c0d100d0b840c0d80c0e00c4445020b8540d103410300c50390026202a080ca1901c0c400d116080c45e02c8242c1aa2406920414080a0700180e07582c4512040050050340a01252030388612241e2040a0f114801c000c0c05d80751401e80321f4180d241c0b007400e8024000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 290713732 1250 290712482 290712503
    0x9030f1103060f0405071202180f040c142d040c020f010e07030b16051e180306070801530d2a12080106030b0a08100c1b 53
    0x1964901084026030240e42d41c1c022080d240351a98500c6e4444846100d0351800c20803483c20700045558541040106c0123a443c513030661403820850130300003594280c4042c1d99840c00081c0114000d40050303e44611000060841c508002c15010001500260030050140c5c00c0b00c1e01c41b203141da564650141c4003030123029034001c086010030050703da802c42d95543c84550b16540802000c000045081120681c8601d441c3c40ba00014156100e0a865034032418046802042104041e031141c80e01c000c028001c0c03c80600d41c190301e0f9030203c40506d6592241622143c0205511400400043c1d040d801030021922303948064102881c00f0804a03070305100c450703a003d01d241c40aa061100c000040441c0c1e031801204080003001c0001c201310018100721391001058403a00350740340d81c40400c59500f004110595074442000484041c0704400180038480a005502c0000d0070120328a001c2d140c68801c00d001e40c3d0b044c80140603d082105000001450648030b00301c207000314080004c490441c10030070341d05030600480b511403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 290714982 1250 290713732 290713763
    0x1605030411190e1302030a0210030603050f060403120501180b0a050303130e060102030405010815010309120503040b060111030a03150308040f14060f03150316061107050d021f09030f 80
    0xf024404000c0092030310298504100025031b07000103000804903010b44421040300d4580790110060041600090715510540740d0702c000038440000c80314803c501175907903800c1081800800b034042c5c482c00e01c52203030b03440044d54408100341d9050b4026408107000505480501d5610b07000301e4150b4200f401084450f21000c1010041e40000003d48c5602050901c060351410381400000b81c040300001c2c0c40e100303ca9044038207903102c0f64004c0d44000f0466402c124207000035034180c00000c205510484080356410410310106440b035025850b080321031005807001d9030500242000480081458040c1c811682e9280900007010403d003000810142c1454402c030700c01e4605003d01c500484103903038100c50040c4030800c03a580004005c00c003030340d400c1482e9515541c1e240304001c0010380b415955070040d032801c1c5d011070000030712030340c2190f1403000290320041a5641550307904100902e0b0700d0022006900440d40080710885041d174200700280c03800160400c2c51050380c0f25190100c0b1184541d0003210740d940903d4650 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 290716232 1250 290714982 290714999
    0x60312090810110f0c010f0609050403020d0f05040b0c03040b0d021201060504030809090603011e0606030e0303130311120403050109031407020a0b030601030209120705011403160503041119 83
    0x7100182615043c003190403900c00c0000203200311282942c607000040b902204900c002c0d004900410b079882424003d443e200c0c0c4100c3c0c007d000a03102200540b10300031070142e040d07000e070741030400b500a1501ea10381070030726004484c1003c0d80b2203803c08c206800204008191a208180608000b40e28541c006803a00c04000e8020645401a089441402024401040040d1684040f03a85d080015141c05c100c0c4d03142d20000c00e0142c03680c9103030b00c1c039040c96541c24802440c245920807800c840f00e0342c0d424481c100e403c0324400c0c0c40c4d100584210808035018004940840c2c060b04031040c62020590803074641c0141c20307030007104a4002d60004c6071181d44a42c41c810515034082807083c980540d03030000c246051200da000400350b180510411103c0c080c040001501d0342e0081d4191b030003482c03016040e040c040d0090b04c01039840d4005406000e01017034000c101100c4080300402a41d106403c40d074075140f0074545205e07041d112034000500454000c1100d6660210700e84030a0000c01c1c0601e5543d10341900541480441d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 290717482 1250 290716232 290716243
    0x30f070603111905090a0e040f05010c1d0402090a080d020106030b01051c020409080d02070f0605010902071a06060d02040321050f0706020708090a060f031401050f0f03010603120908 80
    0x102410050501544403d000d407034001d107200715064280560b4034030002000c20211403035070703100b0803132040c00d44c04010902071010400e00e003640c803e20081050325130003081901c0b0034a24a4048922007400c800d02c80683c2004c0d402045008002880b901a903580c5240d850f14085a04000d400141d45a080400411540b612924050401242c2d2501840782108100d0a14812030178040d100d95100c04401d000c1c000c05204640043c02c602c00199aa8035050806809412120300b0403580caa181500003c0c03041c14920968081990010f80103910340800d00000749084005020f0b40d600071740c02c0145804046151005100840c0b00705001d08004d10349005401d10143c1e00c045241c03d0007400c1040c22494a10b00044039801644101c0c010f80b107070424140f428041c01021a40c580011701c4160110b880d58006082c011f2035030350b660302401000441d03c51001d442c6070a00c60140c02015000b40c038282442c0085001c1c40760030000d4000104a50351f6200c1c44504403000070450003195001c00180000d182c00c0c0003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 290718732 1250 290717482 290717501
    0xb1e1e0c071406120403121506020c091b0a0201060b0711010e0f0901061809060b0c100605030a022b0b1006020a081219020403050304062706080a0902030f070603 71
    0x1000441144440302107480f42c4944844003840b01c07101400102014026030011407500b110250800c190241b0321241184428503005220140c4100380a10381146481e02c40c0c9071003404031203810084004002c0d0b00c1407582c0c1111850605654031a003010030a4182840a07014080c05251500345804c050000501602e5010070081d0003408080c1001c021900c41480081c1191072518012101c807000d33010801c90b00c1070b6904a100620700b450000030355908000090500c2c800441c0c02d486556070541c00c104125195403041c00e4150b00aa0700c40c40142c030782442c82e02c4c1602c0102452400d80584247c0c0301140d03050344607040750030b85011003d000c0710041015100b406810580003c180e02462900c800060b80180c0d0f12141610f0100000100c10a928102490400e00d051209546032512440c0070f94498126016040000e042d140107030311031810001417002702000703120207607064605003541111810801000d0b801d0f0940c44640a0005840401480b030f40300035060041c1000700d051810007801e4440081 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 290719982 1250 290718732 290718749
    0xe0901090b062803050a060506030d210609050a05070806040b0102060f04020d0b01030302210405010c03080424020306030d0224040309030605130606050603010b1e1e0c07 75
    0x14030040000c41c103244098010708116000300110071041240780f0305124061064400a01807400002000b4000030136950302da02c14001804665507140900d0b944c0d0525082c0d9000050041180488101107000d421b483c04030b0b102c002250080e140e035504406d0314010795406031444e40c2c0b03004000e2020351241d4a00c4c0c10000c1107505000403082d040c0000c0d0760f60780103070083d051083d42401042c119030b250740c022840d0b198480050501980d603810069181c3c14519a000c0000e6000303c4101310340034103d4115410b0321016101e0401d0b01d46251405c44210070300a0049034900e607034600c0005c100303848804c2d0140c4440c84020150356481c081c4107143c2081074910440b400d56100d004000c21190300c90150030104184005056510340c0d550030308546940340ca61000d400189002d01340440d40d0300084000d0707071060041d002404401c0c1e40c0c00c10720009100901c107401c0303000d00034407140849501c1807040e1560525451400f0381001058480f0300d18003034000400c042c0203440099408229041070008000814086 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 290721232 1250 290719982 290719991
    0x30d0f0b0604090e03040e090607080708130b060a050619030609090807030f0e06030a06141009051e03060c1308150703050624040f080f0a030c2a0e0901 67
    0x14011400501441c09502c3c18152148040003000e0010000d84001f01000c140c00009410005480c5854400c207441110000b90084001244c80c3d004d82c0c0003130702030812100301112014543d199500401c0700542036a500000f2034000103001d948440140103140c00c0e60700741001c0c11444207006022600f00354801c0c0c82d4681440000400300e003018042c1e480c10f54160400250100b1959011181c941c25281406c1c2d0001000c000d00c0758a282c1940800300741d94100c0c294034804080c00f010070034064950104000001c190f48018070490030481240c0029042d20702c4009008a4888006400c1800c100c4409848484c00303d1203070110290000324000801a82c00504025001d481c14200403000c0200840c051544071008605207031602c0c8074540c8001120243d001c02070f040c0303c4003103103158402d100301044002420404500c854001c124800c240d000c00000b040d40680725502a0f441c900d4070442a6445070403480c4c8488181144800507014428405991708424100031078000c2c2c40101402e28602c50703140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 290722482 1250 290721232 290721251
    0x3180509101a04090216150e060a0c050409050405030a0e12030307030b0f030a060c0f050c06041b03051005040510090b0f15030a061506020a12030e07090e030d0f 71
    0x8120308106480098602c1c819800307000d526400300d03224130313800350b6620703032002074100000c0351400d4415100341c0c420b801c03440112100b00540401d076040405d003001c2c00d400480c049544007805a10091084481d41452420325a94108a0003240e02c1110b05440a8100142614030958080c0c2e101c800010101d44580c52500540c003216600d01005043e0310501d6660700f076031501c07039554000400c079001d4003c00300c44170084145884809000710004110118070300e00b00a0382540d019105940c01c41c20904018a00d42c0d41d6502d8911044c0100108207524085243c4017002181040c024079140441091022405003043e141c124501172002018425003858002924005541000c4190700a40c83d1001c092581e240c1c841085200903d14980d60361502c1040310007030800180c0d401407501c1d942c011403110b420380e071703129410380c0c8414515000400320900340304000b6100e8000c0e441240d203d040d59046540c0aa1240e55500440d40403400c055107030380c8049582042e050343c9000301c004a4403d0b0ba07050001ca140e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 290723732 1250 290722482 290722501
    0xf020c07050a0b0409020a0e1f020607050f09040519090308011401170703050a060e07090f1703030609250504030501050a0b010f11030d1410080607020c0d03021903180509 75
    0x84d07005888040b9000180d400344588500f031070900480c40100f00020107100d0601c0c2049440c1c9a0040c3c03400b500a00c400600424003e41c2035810a0980040c01887e1940640400004007001060305207504030006c42042c51501a01c039483d81d051107912611869410172030f05c10082e6081c90308460400143e00c9440d0007881c00c00007050b41100d000d0a0120752511369801b0100501610f801111441800200708041a0761004681013200c555071540c186164959048003030440740c10080a881e540104049405428502412503011162128202ca09600c004900004491601e25080054804642402031050038401c4a40198501504224448407000040e081d40004120802400b0700d10400e41c03440b09051080b900d54200c00b69007045401c503060308120518100b69100c074500112110081000d02000030454003603200c0380c0003822540508801c1000b02d00d400036085045000301d01442c1d420040c115190403203503202c3c0d00da014002d002d50241a030112900d03072000780300d0109032080c05000700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 290724982 1250 290723732 290723737
    0x6060b0d060501021015030209040f0b07031a0117070f0c0c080c01080f06010207180e0319020f03040315020906090619020118030c0204020f0f071113050103031e02100f020c07050a0b 80
    0xc8e415500c03440030f13030f5882c245816240070310100644002424030401450582c0365100f98401036074801d060640c2050000111043d60350320341d100389400307a06404030f52050b00602083c05240720515000040c005942da500f0000c81c001d500c01a000c0e800260a02a0356800c42603196012142159260740f51a2050000b5610042440b078901e560900e103520404000d181d40000b00060315007021aa0360f03283c40c0c880f060500101400c06070050003002d801c120204000301c110740c11660040c900c04048501145002e009505c103402d91a444101040451301e1a01e4002c0a080c0074200020b081c449c0400c44400a42035a1244005103640b180c022160360000b0b4201041200c1507805890042c1c0340c8148020345400341c070451013010210980032409404200d5241c0701f0a40081081d5083d403020240d042284007900c10a0100502180d9204017400410f01d11030614007072424a4411a0600b464011550b0205c0e4a502d250403201c2e5000504400900c2c0c040010304020b21054501019813498a1080344003030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 290726232 1250 290724982 290724989
    0x40c0e1c02010e04021605060f0103081903060e0108030307120507140f0c01180507091e09020a1e090608070305030a0f09030b0705030a0f06140d06060b0d060501021015 74
    0x5884200d00c400c0d644210f420900143c0060811503450f071506800142c0901e0900c03040782c4600c11000000d6001c00c01c10300450481e94017075107032800e00c2d070344041c0b6644218403c210701d41016515140000c02c0c600c0c581c0840d00800c1200302950b82c0c2d0030b00c020000c041d8044c440240d641a400c0400303001005038400d07001240000307402075650b00c43c041600e049945100d204d1500da040d40c2421803818288004903540031980f0301ca10122409151349200388002d650000c40702000000150400c20b0680070315401c1018114030080c074170341205440d007050a00c15169198507003c110103140041c04541158415070024114400050552920355a038250f030301d00c195030309031041200c2058035004040c01101c00c0d00103164044590009440d1990004043e0b820884401c00214148807960110a049204940c00d40d02d01c8699128821920740a01c00c411000320310807508540d445400180200c605070180006e002041c1001c24801c0c40c1100082c64111044c000895081c6008801c0650380103600056044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 290727482 1250 290726232 290726269
    0x61d04090210140702060d141006140c030c06010e061e030316020a150305070306061107151211040807050118050405060103020705010e0606030610081209031c030b040c0e 75
    0x40c250048143c3c280381c01031320402034205001181d401690800c1d600030030b1070301004c000404c0c401c0d91210800070464450744104c034040390f6141014800d4608020081c20510420b50032649060703002600c0038034104099000030308000750324080c441c01e440c10341c2504120828a01d41c07800d082c40c1000000b40c807441101078901c030002d914035284045441d0104144010b01d5002c0c01c00c02013000300ca20180c0503280484103c00000d20f0400042030b4207004501d8021440340c8207004105003810701c0c2e5288a46a1103400c0c034803c2c000594140d4406019030b000b0140e0010088249603191803402d1409494040b41d504940c0c144581e034406014500176443e44002150b00403140881d25445100050340240b091703400282c1203508120f4211804c080000e00a801204c044e811243c8940d601d00c1c0b03110f21600f00380507060f00d98000c1842c0d008440098409001006e074000d05035485070f82441c01c80385000d4034003401e10300400d4541100f812103107424400c030400807009050007100500c07044001104543d41080090a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 290728732 1250 290727482 290727497
    0x9020a02060a180b0705040303090e040b0a0e030903070f030213020f0f0a0309021305160e0102030a0e0316030b09070807030f0210021005010b070b011e21020a061d04090210 76
    0x51a40c0c0c00c060080c0f826084800003442c2d06103140014080c1d0f000d40819800324542c50000144600c200500d40d00c1160405223024580d26640300c0200505480c0005105c144000c0c00300b003055990501210f03000741104002d40d02d0340d070318500c1844070704001d615204441500c1807024600c0f0130003180440d01c1c0c5800e80390181e6504c87c220b000540091440c1d4602030b41146000091a0040e100b640c001802a007103103001c0301c01c52187c2281111401103242076540160814091075400d180141d0a11121100050940f001004480c6c10604003040650082d01c00c8444d100034024124001d01401c0c0107403003140f02400925003140c58407600203400c0c501c0217020310f170001103542c82c20b131003400395450401e1012000d20a55a40f64810119600159002d44202601600020710081c1403100c54003051504a52000114640280030310b0420b012580b800000701c1010165005a44a100e110081c0503607407100111045081010614a64981c101d035001d1441c080803a00582c0e01c542111038a9140c0d0f241211 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 290729982 1250 290728732 290728751
    0x20309060c0f041e050414060307141804080306090a0506150703050c07030503042102180c040e0702030d111c0513080409060e06010c0c0603360c09020a02060a 70
    0xb40792240307910844070701a003500e0001c2d6161150880e00201c8808a07414001c80342c3d81c012043c0c2d0343c1400c0e075060b54191b014207130400501d049241c0350920044005c1c018600c01d80901980c03461640c048804032100c00d40001042a9440c01200036a008140c0035000c01c600d14003407000c607951100016041c4c10180000c61048200b520400407942589038540a41d00000e0380da2a0990350303500700c0d024a80540d2401d0140300401080d910182c1e0200da0000c103180008004100c0c0d0850300f41d800b030402d15890b0070411011499401c62200c107805180140e00640c0e071440c0001050b0200c8804020829171b41c00d080003524600d086441c03081841042da503a000032292101c100785404140c4072100103095100200700003808584c5c40d400803081340c0c10300000005903550070004480380300039040700070b01118034410140551032007a4420815101210100501904012243d50403c0103140da011903a002031001c84080045002ca80c0004046950041d030408010081c041c0d00c0320401840201c0c0304e80d0b1440d501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 290731232 1250 290729982 290730007
    0xa06020304020f04090c051e09010b0702040b180603070506030103050a0201180f080a110a061b081c0b211509070e100f05030703020901060f091e030b0604020309060c 73
    0x41c0f88980014030800001c9020720b40868550a41e02c68a40300301004280403011099200074504044070040241000380e082c902c040502d80c001c907400342c1e0071541c2d50038460040d8071039150401900000e014500c2c0039181c22800c0614201581c3c118501540c01030004000055000544004455090801d100e0364010a000048040f8944d84201c0950406680000313520704041000700d40c041c05542e40c130650304c40c9031061065100052143c01c00090f04a0891000305c40d2140d44d21598610424445161107414500e0100341c0a42c0c8100c201d080f9a1040080c45502d0b041480c00202d400c0210341d41007605120012984840300d82c01141c0d2003000c45000100c04480511110b8003414000850141c10b041c00580840700c00d023107020716001414044000700e1103160000f0b2610440380d0082491041d03070b0800108a031200d071a48030040034000744030004100c89a006201c0e0b4040c8084075000084a440c50901300d0b01407101619850150b03104106012241102240c0c481d40041c0c1c54214982d030704c56031110f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 290732482 1250 290731232 290731249
    0x304030c11060a0c0c091b0c03052a0f010911040f0b10050703020d0203030f04030f20010e100203190b060c03041401080c03091e100905060403090b0c0a0602030402 72
    0x3154020b10008000065540150f0880c1010b4000d04070300c282940c480c03080c0310440b2000c8100e071880c1e40743d0f1500207902c1c0c0d11070f0b1000200c0c188070745006414440c1d0781882040e81003115005483c100000c00d12950003c8040207240c0303415000c2002440202c001d43c071004203501d80c080707405008a171180d100329004141030708200c480302009400b001c50111340d0f080003842900706840441c010f0041d4050700c44854030000580e03028003100081040c894a95640a41e40c1c00b144100c1c41091080504440700c01110020010880566020000c104140c50041644c1014804010600301c94818004d21901e042e410154071440398005400286025800700000c0c8140203031050b4021900c40080e001c1680082e0241c41d414680e02038851b403000d62220883d10b045401308981400c65544072580c402c1e217042c042d0038411119100c00040d181c074884543e0a407804d0310100d5106803555800f001c140400c050744a02c1b8070005024005510b03003006502c80701c451f1900b580d444007408150b0040007140555659010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 290733732 1250 290732482 290732513
    0x20937090b0f040b0708040b0606031b0d1d0111040506090a05130c03060b0a05031f0801060305160f03030203030a021e0304050c0f01090602150901090b10090606050703050304030c 79
    0x720030342928000988004002c41200c0494450001c00045640e99000d4128513014581c0a00e000e129a6103110520200e0b8000800148d0510400095542d00d44000c0e40113001c6c21084110118001002816088501000d4181e003041685080040481c01e1008010303076007130728400c85140355104000c2e000581d05110b55042194481c941d240240c02340070307065012500c100d00c00d86040c0f02c2e007681d510300c01009000d44c54088020420810000d0a0a03804483c6082800d4148482d02e00e4aa1682032807402c503a11508100d409a001c0c481038080c910462034403100400d00440800c240c3c2c0d0642d034009450b40000340515038410380100344008655104e10001074041c0c54030b5482030701c92400d800c4c120b41e5003050b02485070049a1605165030750754072403900801510301d039800030002030a907694030358544000204540f24035540c0f0045c1c13500040b030707490300a40501c01031985842d00d07900b002e0403c800c4500c40e50007042401801c02426000940050550390b0280d01410800041c05403810103100b214860708 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 290734982 1250 290733732 290733743
    0x7020f010f052d0c0f120304020a050d06110c1506030606240705010c080105010e01080907060f050c011d060907060f030506240d060503010905060a020f0408160302093709 75
    0x19044d09024400103046010a4404007203e4846007800d02c060365903c03050360040d4005030045c82c28825414003d8540711910301c6010700241070386a080c02c203801c07504070000700003080d044819000c0e000001340501c2d0f600400d04070054422800d210001540c0300d114020150315080385103c644a0301881c0d1410340e20140e402070024055030442d050300422090090040741d0200d480c0c211115180e5100e17140c8244102c0342035004205090a007501920782daa030b40c01c0400200301080103003885aa03000e01490100032844040014400024191039041c09070041c81e402a943c402c120421280754408101c4c06038184c2420001020b40f40d0402003010b0103a03c554200144120921843c02ca403041002406154152001007001d0303500e0368101826220b8580b0007800550107400811045a034682c018280f06e00846010307881c0c550740c0c0301400c0c03e0600b19130540c0c003030150661042081d400c044450782d51059905c2d50503404490007184041ea49446681101c04004042c2100c0c205092640e015104554002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 290736232 1250 290734982 290734987
    0x30e15010f030605090118020f0604031a1501050309060103200301150e070201060302060702040f021201080a120801060206040b0a060f081011120a050a02130b07020f010f052d 77
    0x480d01c52520140700d11080300c0081c5414000b40ca00382041c0b08a14054a08100043d1000c2540d000c00441515442100340e006104010000014540440e0303200701c203150001d030a516240800c400a03c800e01c410300d00c0e0506c481001044007060300482d0150650340d00892209a40300310030318403d80041c60b00c801c99010740c40c0c15140384a15940d8101042120f0351044040e40320398850300e00f00d0036543e01d84002500403070144403200040c03a003030f0400100c0d8010640010b00300100c1d003500c010360b031300d003a4498a11030301700320008000c2c0018030741100100402400c000c10294035003007000b581c50100030005031810380e000000c04d0110290340c010800030032058000620321078940d5055074603103030f0114504500926007a04c106440d01d11000390340451070120840d0000da03545425100241100410f4120105d41c03c010010304287c031031490720041c080c140103180e1100141e1041c40240500e041d03002c1d05000404c003d540c0035aa000c4100e4402d501d80030300c075589400c8030300c080010030f0000c00161050030300003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 290737482 1250 290736232 290736239
    0xf122003031503071a0309010216200103060b1602040902120706090909380a0f0e07080304051e091513020a05030604090302032215050f0901030e1501 66
    0x101441c040c501d82011111122030310010550b4407031301c6201e200301d2900081041618000202c010315800302c07155001500d02400509145060041d4680485205000d100781c0c515500c01c01190b00514842801e04000e0381c0d052035218555401107003441c001c040070031ba40100841d01c503600700b06200c960150183d111205a0001c031030b1184001e0283c0313400129508800501c2018601940901035000034400702c5c803080e000e07001840c0c1c039001100001504000026031743c0303410b00f20101300d102e10294007000031409040c80c045004d6801055020020390301110042c02011004021036084038070446400718480c00408220608030003441941d94022124420084840e4001c00c4e507544d550000c41d006183c180b9a0030005040340030b40710f001c000040e41400055814205580300c22000e80c0a401140d0624010b4100301544400d80c00a10640c0e031219001048440c034003c200740800005418000e04092518401c500540284148070781015242c120360220f15005219540c20155a02c0c1010280d686 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 290738732 1250 290737482 290737547
    0xb090f0d02011206030b090c19090509120a02010501060f0507110f0d02150d050915010e0c1c0b011101091707210305070210181b121110030204030f12 66
    0xc0701c10180c0388c05424001a1145042c0003298154180801a490368070b0520300c00c40c6c024000145000c01e14444c0030515401c02e803e00000d0040c054650b4004182581004402443e415500c4400e0f41800014803d10b070009940800c0c0b40340d01c0000340c1d02c01c0c10019400002516080f20103101940110808000f11003214800c2c00a200d0442d90305810312140e00d42100d620382d94072081c2c003244840400c240052204c44202c41101e074110009400b00c60910803030910004e40c84100f440d9603011955503580344402c0c5e507000b80c115155039006100810a441040c1c0311007040d05440417070315840b2000000c00b2810006140100c03290400394a0b07910000e406050306c054018041a1250720140c451156446043c140c0c0e4040e10301f490901200e13a090b91801c03030356a10070000d0003901c00d070f401010060000c910f0303a5a0700c5400140c41d00801d00c500c03d42080c2c500303210340146101641402c041c0100300500200e501c182e02072251a03840040c0100c135111400d8122818505c1c0c21488070740000a01d1075000b07000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 290739982 1250 290738732 290738753
    0x703050301031b03081204020102160e150108010609050f06040e090a0b0c03280b120a06061a04030305130306320f07030b01021912090b090f0d0201120603 68
    0xa20404041002c61040c3c0c603204903810041c840188980000c02000c3c01c0320104903109a0801e10600403074541d0f0f98203040480046a05401410000c2d02140c1048880c203001c00d40100904802e00704490554100b0b40000c00c2c00d0b4040c09440c0c014407005030030000f103840b03401c200e40c003c204804000c50203050450314035840b640600d1f01926411040c401055503a18441c0889008d205c00b61200d87d070110b00038203882d0070198401110030000c1e80e1038070340f15601e444a0a91a02c6001c0c90800f41c4145506c900e450011076060741c2220050341c0b80020260050011701c411a41500d8050401c80e8980a41c00344c480b1061040d83c000511042c200719180d00300d01d01c0d445082c031246919a4048030007400703020419000840840e0000c1002c07184d2004225a68000d9001c015070780c10601c1903c2c6400202030800c038264908981c21240d184607010703940c01859000d055400601984804545803c11341000546201030142c1d061384580582c19442c0216805a28049804800d691042c00160707601d092504102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 290741232 1250 290739982 290739989
    0x71205090915010807030506120703050102040501020d02011404170717040510030504030801060e03030c070305060609010f060c032d020d080601090308030412032403050c0d12180b0703050301 84
    0xc0d81c070840400d1228120118a030703808070301039440700c0c0f0319a203050b01140540009072001d508a40001c440c0e40c0c0110742481000040c500520016964a2420300020701d02145a801101164503141e412100c0c40640103100741c01c140c110254400e9902170078418031117481415801001415201460002440180060012240212001107c5ca00d101d0420344c190f82c0202d4004001814000045c002140034894007a43c140c4007408690810182100003850148650001c0e01c00707078412070810800f46005103545000d04405e09170501c00a2401c0e0000d04240c10280006092046050724070b08000c810440d000c51040d007a8040318810049088041c1d11a02151074141c0082d02080008030254010265032040700d60095000c2d140d80d6079500d918031710b100d401200724105500c1d040d40080c0d580701d100c42200c1e4119004c4080d510a4510b1030810310740560215014040c1c09030004510100701c00d410654207014090030102030f010483c200402c2a1b400703a8004400b0341e0804110f1100741640800030718141d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 290742482 1250 290741232 290741239
    0x18030206090c060a080a0c050c102f040308030717010314070b09030a080d110403080d0f05040201050f030604111c0f052a09090a14070c05060a090807120509 69
    0x519040c40b05018451040c4030b03866000c54203980120384090300c9039000910030005454610f04244030b00003c01d0800d46880c0320880c0700c41e11110030040101c0200000a0341805003a40c9929407042100110018011480090101080800050340140c0502e00700108a54081a41c101568691822101900c40d8001d07545044c03140c10b41c00306501c0c01030802c03103d805800800418030346199a95101c22580486401400703e80c880c0c602c030340d20590000c06440510f1140d05116203414020386083c1c1111080041c2a2491b81003d0502000d80d82000c2120700484010103da541c0341d990201040241070f020300c4111345004002004a52424a081840b588010b204070a1080300a11000340c0159107040d10400711000780390b14806035880b540e01d18441c203140d801c0300e40383c240700a034400200c556000b21150885140c85407002807264801490181d800342482c24005ca10f40c0c0c1c02d0b25020750b900d800030901d0740400d540b00c031b004044c031104d101600c00c4250301682050314040010b0009002d900b01404d801d02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 290743732 1250 290742482 290742493
    0x711030d03021c09051f0e010e060403020d08070503190e07090c11060c0a180f0f0f050315160c0b151507080a0302030a0603050a050c03060601140304151803020609 72
    0x300f500d140541c504480e0008000c2a2410900308501c414034100401c030354245507202038081c18500300b8015034404d401042c01800f81864a4180070b401c0c003507070303003540e1080005050800840f15006015281c002e0054148101c449940c50511001880d03034a070305003481d100d40c0c90b0000b0215201c2d000758001040c290780b08084e29440c1e58405958060656074450706180611410a00c0e511950000410030b0ba24411803044658440c1c1c0d6001440c4c0300d0308160005000350340180000050000001d00030324013500145608002c00c00c0e0781c618021302070604a00c800f4801d0144141502c1a46003480c00ca030801804011400c00182c00804c0009801d0243d01810110441381d94160751041625a400d8000b0718191901d0302c0190b04030700030340c800ac15850700207589040100205004103c202e441c02e10400042c0708555198040601d407c10040c4403504111500b0503400d10000e810044d0394100d0781c001c0c901600804040400d0014141c1750316551388400c00070742e89605250340004d4040c0100702d200103650 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 290744982 1250 290743732 290743777
    0x506041112070602060c0706060e0903070b07090e041202010213061701090b0904120311031f0e01050303090103051009140a14040206090f010c02090a0e010501080f120711030d0302 79
    0x140c40780803503c51540980c1000001800e04030010000746a000e206140000d0b0369600e51140081e515401d84801960741e00215201042040d0101d05940007070b55420250b011610340f40003a0100c2d4402813004040814034404d18840c103000b5010b842d1442640c1030040d00e01a2200c40007002108901540503000b0a0b10000003020b27100c0d44914031400002504581c0181d0791912120051101000120300b01030303a80c6403d00300030402d00c014600465001240d411060721021107802c0700d035500c1d0402142102894010825607030000101c5888913820b007400b045942d100503c04d190182d440d44131404003810704a43c94003c404500754984100b4481c08104041e600070b003021403d10390100d4000350008010000920301d4501440350200c004014948840352600590116144002c19105081515103851341451242020700070300d409808004000c003d152001001641e9030040c0702d84c0080c040c2c2c130008110080c441c0c50480701b42620700c0501145c0b032114407000010003d50005610000031400d52410b00f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 290746232 1250 290744982 290745019
    0x20702041b021908070c030b0702010b030c060d20070809031005040309090f0209120c18160807020f07080304030309050d120e060705010f0504021002120a03090f05060411 75
    0x1c0250001540105000d0341400d00040e00c001040b4802c3d255901c0600c030210001c1d59448a11b4040c0d8801c48041c6841d081000010342501c14481c03219101e034211401003826074076064291010384243d18004a50441e80351074503211110701040344000360000040007030910071880010402c04105808507a601181d600b0601e080390420380300100040c52000e01044000003c4d002405003a0210034018034200e40c180024800302111504810603402141407503c01e4a820415200a03602c5413284034001d03e0010052101c3c0b981c071030000b006000d4942c0c007040c6ea1030720030413144031000d42410032104000c0e210f90700706a407508140b2007100000c405000c045a00d0802d002030710242d503800040c2100d140c4495000307944603028400d1140d0021000d11100022072400d02842c50490552000087c142c100f9005101c5030918603600365056512240a0300c2001018034103d440003101440c1c002984207984c903019981c2e00a0001c0680188103c10500c000d0024100d4023414001040b1410304584003040f035034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 290747482 1250 290746232 290746271
    0xa0b2707020304060e060f04052d03030c19030e09040c090f020c19061e050402040606170a0905100c020d0e01030c0905090411150c150609010b0d0f02040902070204 72
    0x40b5000502040036100c3c150030031b8000b801194030303a01100e038105612800441c0c40d646040c0b00c0011003070f8050362580116400b807113415009003001d070083c0d0720740300c0c071a443d0982e6094605809281015102e2881d003e040c80390103200300000c0c0040007071406040c18104500728019034000d19034480d14003443d00c810710005100303c848503401c9001620b221000c05800016010019200380c98280c0c44d039004848080398000b25800d2000b42c0e10000032070707007403900510040300c1c01c0390010802d204400c841c860760b0010140d111503200410140114400302c0d00d15105042101c119900d82d201c41c2410b03c641d810980214072007455000d0b5a0760304401040200045042e90703d44160384020441d01c1c1018803040c1000d80c0c6240d07100f4000c000c903022030010800400d4001410244041d8589004584d43c104110240290400301c20740b08040341c114102000010703d42d21043c86101400b04000a01d0a0a43c072950041c002e0280ca80e0011034a46031340e100500c010313500001049102da8609802030f42c184400d00c82 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 290748732 1250 290747482 290747489
    0x12020c01090f1215060b0d110301050120071e0602010c0c1502090d1202030a0801170c0402090d0c0905090d050c0705013209130e0c0105030a0b2707020304 68
    0x40c1504651500c203e025815188410076501801d07102c07082070240d1460701460005004031040159100c01d040c40880441d03004404031601114100010801c0340e84c4500d01c120704900c10140318400001180c1858a410500d502039140644480e1340400c014802c002043c00321103140d00203114602858000b2501810218802800d1650120140c030721042c05178041d0404240103440c3c0fa0101d04142c407504c0000d9001848400140e000180702103035154010700c220f0041c8010782400d04c0d10801506d01c0d82c0c0350007402e069240600e1f804100d95a45039268900d121000e0381001c2c4c26000f140e04c030f07810407010f000700300c42003241c2e4880c8903a4001018450f40c200c070016074544003d040501e0a0100440302220142012a00b10580c00315a80111042d0400c2c0031980d40e80b220680c1c0d440d107051007440104015840790740c010360300d01100b036403070a0008658103a000f8000d180c03d550301e50340c03140c20400078011010b403540c1200d41101c8508110102c658190340142075a96181c0007591807000881e81c074404d500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 290749982 1250 290748732 290748749
    0x120607050a02010b03030705030a02010608030313060906020f180102010e03090d0f050a0206180915060a0804080d0603080304060e160e1b120601090801020406170c0405040912020c0109 81
    0x18405511940207040d010340c00788008030f01c1019880c002407854202da1010703201c940000070402950350302442020014100c10025500390b1500321459600021000740151220791145026010440130b94129004422410241511240241e0843d00001e1000710000d0241d842c0103541d4005071400000d440091500901c113580c125801d070b4540d1541d568540044503d0300c00c3c002e04c04016500c0f0b1024007008000c0342c0302510303941403000c00c00c249080083c000040c192410b40402c1a0b545825007124944015402c1620942d1154600b0140a100c4c000c22840c04510384030380401081629802540502d001e090705101104141c2003094407451202a0622407020701d480030481802000a015400102c0e0a900385680340c800c10248059072040e202225981c840004110035980c1020b20301019008202c0210308040c14408003400c0f00180400e041c184c10034480000d203c00c882c3c041207074007404025200780424079091030245840c8040fa08020054003503803151101a510800040f02141c41c0321 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 290751232 1250 290749982 290749993
    0x6020f060f0c090d021302031317040f2310020309190f15031104120201081602100b040f0e0106170307150209060d0606090f080102270a0305010c030203100512 70
    0x200c200140321300c203a03200726001389408241041182c020306c00346218100c401c42240482d542440c0840c881c05006201072000fa030300740014000844e99030801030507201c01e40083e000303002c03418400013003c041b81a15245e1106540300310300b40c00c5601001415403048161000e0840c2c02d4560b0054008a0702805074140c00810360804110803501d030014000f0000c4e141c00d0000307214030428a50f10340c1e5445500104100a46840030340304550384000f40c640e0050344507908134103681007204001d44680400700071025060b2180c050b4486070380d0306d6100b0300007a01140e800f002440d010400050180c00248100b2005110250302482c00d00c0004c4100c4841c5a4401c03030102e03552010700c00720002504030303607036054012000b40280b10014605100c1d00c8058030040d00e8040301c8515080001c50913030310b01e8205410030390040c49442200300c0c00300a8500d80800c10021070300d41d01e1203080492001c80300c0e980060165824610000d000729059402540034200705610306a0301354031a01031250f2403068400981e510b6010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 290752482 1250 290751232 290751247
    0x7020f01080709031e03090501081e090717010c0305072a0f14060103051212040b0606120a05090706080108210f1b1c05030a110d020406020f060f0c 65
    0x60001c00e503010303031242008025652240c0380d17484000d0760913012110308100d6590039024140c000d80520000c0c82c091070420341030b150086840c20704108000f103444480940e1000300f0740002d8244003920140186200d080c00710741c4040d46403801380440704030700030100340b40c0b01c003207074503075200e0078401480b100c107810650b24180351001c400c03104007010001955100060100c1600248030300e55040320503c4c3e050300030070351541542001810f00c0c803c1d50056010550401510854444645c80300c0c1c2d115030458050b007440e9960740c021803031911882210071007005e01d01040140241c05075220134000c2142c07008503942c95440d8007050721031000c02e016412031a80080c0c17040c0c0c8120608070312034030080c10104446080080c20124480035030000e2244a150707050111030200020800c0001c0240711070540418603500340e141c80040d10601c0041c0010110640715850f80c007040070081d0440b03096030140501191340380e641d220001d4030703002d011400100c240030306070120704003481d550f007002d00481e0f140c034840d86051178 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 290753732 1250 290752482 290752487
    0x1415030304031b05060703081605030108070504050a020c0a0c03050d020102130e04030201090b130201030e12030601120207050607090e09010614060702030c101e17040212010e0a150e0307020f01 85
    0x4100002a803c0c0300903800210b81a02d84402500640e4400e440e40e01a40c01d1000707030309012800914041c001c000e4240010024808000390250445c0d000f0340b400502c40d110b0412580182c4a032008200b21449400404400c106c80e440941048900a400341c5d03034010ba0154049090b03206100c0880420b5900000c00d21040203083c0c08580c010b441f900001551108c3d80d03a80c000c41c503e0032030f4003d204030640079610041d0350305801004407000607403000d0b104200380c840185602e404064501410001350b0031218001c101680c2c101c1d46000d4200c0202e51091600703c074000c20b440018010590107503c40030101d41c007514140100d0041d1003221b041800d240420b41c081c0a51508407040590707040c81164010020303a1243c110b05d01d01a4195078030b03000382130f48100c0040918903180c143e0b2410490650754040700041c1c10028103401c65411504000b040c121841000d000d8406040c01920a01030101c12504009584604640700c91910400b440500b4144c08000d032a4015003202a400c00d9081007400841e61 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 290754982 1250 290753732 290753753
    0x5130c080403030c020a060f1e0b0603040b101a09041b020c0f130f0b040b060c07091125020108070f12020a090e161b030509040e0c060c01141503030403 67
    0x131510446800d880c15445035000e8030400d086c1020b03100d69903005808450010040e1410801099500340b011804001c0031442d540b01c01000030701340d0315021000c100110082030310b81000f44005525100040c1c0c102c0e0300007071654010071049101e00e14040300e496402c03402c000e05241a101c1d80c0c020300028403401c0103200803001910070f02548240f8581010b00401c1080c07040340040282131000190040c9400217100441d50281c0915208078810711a01000c1d0b40000390100035240000e1003c00d5007060084421240e004030071100d50310090044440d0341c0c0030103407492000001d000340d84428244e11a544c068602d880a40c03071810010350116030103030030141c0c5a00140b207503c8191920b21141992440700005901081d5001d0007800036494000c99419800398083c10038540180e6070448103062130798054280d02c1000c1c4094055a1034050500c000007007840000e00000019201c1543c81c00c0e081d6816000300f0041d502034008000d58001700342d1010516078a00310303485010300158038081c1140c80e100b8004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 290756232 1250 290754982 290755001
    0x8010e070c15020c07050306091c11010914100506060f04030b060a03050f03031803161b09020a0903051e0d27030303050106081807121a040c05130c08040303 69
    0xb01402030b6044030b224248001c0035807480d0754000d0000642041c0405050000190210760703558007c1040d1103000d40e03400d206002c00301090404031614610101e0303442c0900700413a406402904442101d0403003101c0803c00c0d44618055001c1004560344042c2000443d000b552030014000b5030501050000460701c8501603001f001c0104480407082e030725640c2e0f600d090708103042c020742d1b42c00101c24400401a0008100e041121030005181088124002860f0030905100c0280074200c002080400500100300c0800182c05035550544d038480300d02401404185042c07004482600c18942d104260791a601c024541d44c40341c1c007024040c0c128034038034210b944001a850300c1d42c010101d00320a01c90100d030b4a010310300030b6100340c030302199541c58108080c0100c0c100034454031000c08040000c1c2003079170f004242107099508d021030740740740c1e00d500c0c1c10f020144010303155080d43c080c06640140300522011002140c1140c80440d03c40c224031900f0070080d01a02c955003003401c04206d14001240019010780c1100001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 290757482 1250 290756232 290756243
    0x8030703240b07030c0804090204170a031706120609010e0705090c0403080c0304181401060305090703060f0b0303041d0112032a0f120e0d0201092d080102030109050708010e070c 78
    0x17038083e20f480d0303a16141e10503403142c05002e500142c01c02850050150500f03400e4a0300d0090400c00103291000f406458240701c81c4070007803100c50002403d86d5a400302c042a030501c4d25041b25203901d801801603000700603040400425200350000016580f504042045c441c1c0c00140300c180c2042d141d03a50301c0344160402040038085003c00e02000c03581e00a15070100c0b150318003040000c03441580c0e4a886404031798068024a0405040001b081980c000c0020054110b0380d0211000500700d6600e2624030040c070f00303101d400382d250100040025a032a110505191540703085001e0801d243d030f03600c074a0801809000d200402141645406042c0c00e0b8840b0200d426030b100e2100b550002032010780e0381c001000c0086100300c440c2640821088001580041006107d8106990203c0010301039000600340d20082c8c404c00122884c110161600c0e0800d00d14508804600c00b480e08042c0c50322403d02138040d4009010b00c8041c68686400507140074400c1840c0c5040391000000d2085545480740126808003600f0401d884 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 290758732 1250 290757482 290757497
    0x40c09110f030c0408031201091802012106150e030d03050f280f020304052806090c15020307050c0406031e03020c0a081005090c1f0e0d08030703240b0703 68
    0x80301741051000f042c00c0c1c0414400da4a880d230410160700c0c12142c0c07003250385054840740440b810040c0d81145420151240342c00c00e0220761113890010002070291904040c1c1d0f080780c00c828603220710b41c001c06e0f1084020700c11400e44410145402c4110210b441c120713007a03d002817414010806d45191490700c2d8004c9041c0d407030a40001111401000260fa0f240500c5000890340001003105000782400750340c01c18501c000304c00101090440411b511083d5004010b42101d941d054100108050030303900000604e11146d5040c0030903d0440003941301d402113402580d4070300600c001c0384043c0c0b4180c41001c050325481400d84030407400d03500c4240c0049541c2d81d000c074190b10425405070025610704088800503c202402000c2c5282101655002d8803070160000c84142d010707905c2e20031141c1d47c0c5a0308000d11039050003c40d007568a102c50450314001d0048403190403100400b100d405204017100158440d00303507920180113034040080d8542e00b0220110520b030740540700c10824808408440e00901e00745000e071034a0f25 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 290759982 1250 290758732 290758739
    0x50a03150b040503011506020d052203050a261c0f060f090e0102030103170903070e04060204090c0c050a151e090201020c1e012114040c09110f030c04 66
    0x3803400950091070804a0206080002d4a424010001c00381103018201d07100b2450310101a550b61000e0480301c05200340481e00101ca443d240301da00b900d0314079161108200c41da807414082d89421a0b2401561035003200004188108061040d24540d480410070b0a40360000d540481d002c445040c1c00c0e045100b47e00c0b001555801801d50040001a01a86882204181c540070840044540350400ba9041c0d90040c801040819184022410032122a02d0a80d85c3e42075044006030400f130b81a00f190704110010f0702408144441e41c0c0c042c0054902c00c2e4401c020b0904048010741d1107410705080107000b40e00001e0080e000402440d00644090491301c008114000c14028140300c8540d0f0600800c3c11aa0f540c50791001c0d50b80c1004103900c4038000740c0e625407c14121031420915003220140003414441101e03181440d1300c0c4c81c909541e4441d800007104000d680300c0a1610b03a51401c090b2806e4560090310400442c031019144950600640b040840714030f485144141030542e03030001880c642580c0000d10002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 290761232 1250 290759982 290760011
    0x307030209121606090f030206070501024003050a1103010b060c100507030504080a030902011404031112060c1b030c15010603050106051806090a1806060305090d020c01050a03 77
    0xc1d80c21400310014015001c3c0c00100b042141d592503025804001400004001c0540c0010404060329010388030550369020909010303004e4814907102e03484190020405051092401c03491142800001c0a0310300102e0801800e1900f9403c1400050004d0f00070407010000106280c5081104a4001e00080340703e041e5140065100e4015000c19085034101070701540d040c655500c074641d0f000d152405c08008900301034440040501480b07c0401c1415520202c0109582c0903802c040e1440419542c6036540b01c0c2c60746051001c04441d50300803402144007502007004201e002c42c9a0384250303505070340542407440341180b0180c03181c18410b0041c1a800204004001d070581400071403001c003134544051582f945005402011071f28140d106100f0000184510210801c1454018002c1641107844603140d00e005000a47d61107080d0740642c4c05210312502c42880c400311070f08400c007150745980b400c0140ea9688903006031614001745604e0016048078409450541c05803014000004252400040c2c00d4044002d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 290762482 1250 290761232 290761249
    0x708010c02010218040504050616030f02030109060503010b0f0112090f080711031504080304030e040b041b1409030307080a0c06141b1905031b0708070303060b0715020307030209 78
    0x1180d00503500081c1c102082e9120582202418005480400403407400303031501511031502400c440c0640c9030709902c0c0c5519610a4000960281030448210f5076942d40381e0078003004100911030300d406135080c800c18212030701d0098030030030030140d040e11120828910180c58000800f0b02980c1110340c0901030a6840100b0008409001d610380725001c0341d915001c0b5441050b16044a40007040c5c10100c0c41d104001c00030710200c05413038200341c0c941848805c950388940001c02402031303507a030b00e5046442c20600800d810384006402941ca0115103c070700039070b59512140d40c002e1080c3c1c0641905070b801000b00b880000c122000030040c0c4642464614244500ca55802c41502e41242e025031064140209014107160114242c005c00302002801c9440e014003e000f092100740e01d8040b103001c0c0000031001500c3c0f600001081c04e40940314090580c0c2c0e401d514075141e91240c118510580000340317803517404691954446d0440f01043e0300410301d5409215400f122034080e60000300100d00b05502032010f00740a460320b00300c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 290763732 1250 290762482 290762501
    0xe0a080604080c070e0115050a09080d030501150906020a1415090a05280b04080c0a0819030c0903350a0e01031a12030f030c1c021305060309070801 65
    0x465503480d0360745801e152030b040c0d658000c6541501e00740010041c4047ca486865614005801e025860b2917201300c0507200814140e000800a0040c2c90714040900e138903a200c24162000000c40000042c8640c00490705074a95004180242c1e01c003005d1703400442c01c14100742c0c49060f400c4c1c3c1242c40b00e0b03400c2e62040c84d4852068510010550011501ca010000103018001201c07884c10b1402c0050607400c0310a0343d010140460240105510710045070511540c10b0850740740304801011200720003c14070b00420503900540000071070880094500207a035210703000d030401e421800e542c1c405419003180c49501c0101e4003e03000b19128118025400700d05031084094445052030b40f0354164960650150141219030b1500c0c01f9030405192521382c00019a40b006c101907135250035200000c07800f10a22b04640755103c1d220411480290100400034514010801004101c10304514452080c4080c4a00300c164020581500444040034400303102070b04100019590010310f08046880082c0e0380d008041c01c559801300b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 290764982 1250 290763732 290763743
    0x30a030203070c0902090d062013060305011508160e04060e01061b05100f02091206011a030c090d0312051f0e0105060d0506061b070e011e05010e0a080604 68
    0x500c0c1c40c28803082c103800f10b009090b0b1040c250706d041000307000500010b121450042a46680c1c00d10b000401000f00140007079a04074041440c0d588415000840d00910213106d0000040e042600208208100d9184c070001540c9a41320030500c0d4581e00c0080c1c40c01c80796010b100003040004480c107075581d075a030b0040700c00510326500b843d003075541040e200800d0603200c110a40f160a4102240790300040c030000b001140b41001c1180040c11110740450200648281e03900c10ba030000d02081409240c8101003100c2d0704940b14200035a00100320840000b40a0004583c903200c0030b1414090030403241003051a64600510074904000000d5054030903204954081e66034414504281a508120318145c41e50741e4043c0250440420481d894100010300b144203c0761035494041d00d40c80821120b44a55058401051004032202d1f0325842414030280d50f50158400c02110302526800003a0400342001049001c0300c0d0071640203040b90a0a00541c3d07060803c58101c0c2c0c11120101002074078545c140b1015000b5071058 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 290766232 1250 290764982 290764987
    0x90618070818010b0102070b0a02030409051f1205060a20030415110906070f060608070303020309040f060509070c0201181806140901270606032316031a030a030203 72
    0x103182e40304010000141d140d01980c034000c002c000c16178002aa04003140c1100e844540d0b50185c0d504120f02318061540700f803c10b80c0c01e00040c08840040c032070038180800d0413054940821030751003107510744c41e000301031001c0d226402041c0420042c15680d00444150f1412042d94500ba5010b10000c00d1303264021501911180d5400b030740c00480c0020790060a000e101c61500c010f0910907072000040c3d40d4032518000502c0c0f41c21900c508410440700b60841002440120705503445e06035039090107500c1e03034442c0740e0f603e10451074146524107916440c4145000e4610140124810703a4500c40241c6030144c5103d4141d05100540c07001541d08200341000780050311040c0041503842c1da0f0f01007030800b03903a4140c10583c90b4150000e581e2005071100311056044455120010013641d100242540c49400c0c2a101d00d40004c2c141140030418a402d60403a04103284803118040c80f0150841408007800c1050700c020388940c200c3d400c1c50201c03a00c40d400000011522000c1a80f41c0052034000a1400540210440158102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 290767482 1250 290766232 290766241
    0x3101514070f0611090a170c0406031514010f09050702010b0307091524120f0510050915060a0c02010525050d020303070801090c020319080108010c02070e04020906180708 75
    0x850080c0b04c81340d04c04545650502c0003000000e020401c1d980a00c0760000190301e4600414001007151340d10408014008121958490400040c1d640640c0540041035060509400e0801c04545800b41226100700220010300e08183c07800000d00707400782c0440115922030304011440c1c0e900b8003204000b46455000080c8400b56480801c0b4064030303179848590a0124460171420342030a100f542c089480082c5080b04152145180c103c0041c070302418034a004034a00b00801400c5001c10a414040d1a8200d420000c0c581d00c0580301035261000403004c0750014414803002e2025802a00b030b5414080c030504180381015055405411024208131148012400c00c1424009011040c402e904032411144051440c61a001a0203402a0011700c038285201c0d68030313601400302610074000daa64200c42c95051100400340590020130009081c02846170b19440d06415003200383c00007070544100c510080002082c2c3d5135980030030a91100003800c1d1500501043d25250303603009101402071058004da03c803001c60742031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 290768732 1250 290767482 290767493
    0x90309040609050433140a0501080a1a0a020c0a08030a0b1212070f06050702070f0807030f0b060d02060a1107060c05030318010b04020c010f0c0503101514070f 70
    0x7415480000090700e08024040401c0c030170206500c0c100790000c081e245101202c8030942d8613008008140103060b2526951002c0c8054034a0320078010041c281d002d0040e641c07120142e0b501c0340140107004001c4c1c880f0341420b03801c41001212140c2c0c02011090011b04002d4400d500c1e90400d4100d031400c03101c100d400410807040e03000c1882080c0701d0035000e5403426060710903004d81507030b1241060100d290705440401c880c010030144242001840d580201c09005e1410a00000b0b561010741c0c0c0241c01e05802d058101045000001a00c10f040741e0b0483d030b84030700000c91a1075441c036102d4040e2206410181c444404000b580300c0e0001441108460b550f00160b0f8032858035003034140380282c2c01000800c441540e90001160001080e2901f261141d02900c011010380400b20340140505185190414000b041c40e00c195a41944136816000650700b00303014402c01e4480454140c4422900c4055a5511000a02c1400c0b0814040d000003a92070400004041200d248a12550408801124071080302c0201004000303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 290769982 1250 290768732 290768741
    0x1022406150702100e040f020c0d0806030f07061b0c060f17060604030822080a02210601230301110d0c0201050c271002010e06010e010503030405040f0207060509030904 74
    0x1159038511500305020b60b070004070305409049202c4100003462041003103954032a8400b0a840c00c11240071507417504400b1541d40c880800b28007500101c4d0045000135030b5420045480c900304003842001e032503a241000010f0b140e00c07500e0001030342515100c10a01c7d00180e41082140058403203600d90301c607a50301c080401006401140441448900031009201d26500e968065070143c951040c0d1490329a03100f10300d80c59030400a84010702b181c0c0d40234140040d0011002c03d1010120340251880a10f0381101c1c5d01c004004568030881d883d16610200040010050300c0090315044000c480141d0060207280d40044d083d44c05480d400d4103103000000d05003410358454800c0c04108005800240032074541009007000c41d001308208000824401a4450400031501a143c2c0d00f4400052850381d1b18045420020300a120180c440c0443d4824540040340360b9940740d880504880006004500e014280307000d2001404600580055950b02070092800064580c00b0301441348000c0340085031100030180421050343c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 290771232 1250 290769982 290770009
    0xc0d0207050a030609061b0801090b09090613030215070807032405011206081213050a1404020a031d0f07090603032705031006060915050a0e01022406 66
    0x550009100300711030b88071a5511421250001000522070300c2c60708100000c0c0c4800a03001c0080c04140000325034107a000401141683d101c07070030400044078030005010740040160784a0015601841c0091600c1c81c0701d02860030514030a2040e5071801242e515072156a400c15610b00010451090400000c564184140340960322003030401045801425201050741ca070310300450341000071100c03140e41d5104080e0458001000c1c044200c84100c2040603a01e94942c0010365420710031401c030180028a0718000c1151810796200c2d114001659920004020095102d02400301c145610b8000704500040d4a8544500c2d41e89900050407240080607015030402c441d036040207602d10300d0600c0c14404280d01c00942d000d034640050304010900785225240f0804505d950200b513040c407805588a038954840e802980880b00c21b502e0307010b0410340300d080d0a108103403403a0603000056428015051200c1c841c1c2c0041080c8501801a40d06080403030140800140780c403880341c81c0055440b410302505082800810615 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 290772482 1250 290771232 290771237
    0x60f08070518130204050613090b090103120c11180f3105070b220605030403080403050711030601090e0639090904060c030b01080f0601210203010b0c0d 67
    0x10b002e264200c0324281c124081d40c0d50700500c00c0300c0800c0c3d1122600d40c1203d01400000b003980e83c8402e0703e44140428420780340105010329003001c001c00f03050306102c405a07042e04ea2014860f142142800800c0f103c0801d03075442500c0700040306c0408043c0ba01c840c8082c0c01c1ea483d190003800507924110100141c0740c0c6010340740c0d045070403800e204034111103601840e10504015040d80f1010645440c02c0462801040741c00240700c5c040700041000e081e18030040d0380307247c0c420040180481140c0e140300a4a4500046134082c0c0495004030021740003a100e1001084543d224454403405850864003181c54002d098002d80c0c00ea07075a503941110004010841c0c25400740c000c1c84115103c0ca002c080b501c0f03407000c5404603458052030705800c01ca98146144d007030314104c40c8040c104840520b03040c100b032800b1702040541a000b03c0d103002020700103544115411440780001e83d18554440e1103620044030300348031544440780b0b440c40350040d5400d042c500b8001580200141c82e04c00d521030b15004942c80c02d0000d162030749000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 290773732 1250 290772482 290772487
    0xf04090f0b190b0f070b0a0b10021606050c01020706050a0209030c0d02030d080c0c0604050307020109080a0b0114030307060203250f020a080f04080d111b03030301050d0516060f080705 81
    0x4621182219aa0540740301800c0f841e1542d41842400101d8043c18a0040c4110a80020000c2c4880c040d800025803840441d1049216403074a4416a142d43c01010f0000c8001000503091141601a20007800c0c403042c8280014079200782d54072544c0803281c003a14002d03421500010181e08600c1d04100d1004d40e030303404803405008401c0d90740c0080e0762030122010007010b10141d0000260310f481c120040d2180350114109a07a60751803c0e151080d00e981c0b017100100c0c01b08205040c04261032000040d003161283d03202406041e640d0138400c580b2003141c00c09030513580c903101c10444400062024006103026032040540441221003602d2240c0040700018883c00c10031509620140020f5030008041c44841c0d00040500d0740c0720700c0c0340e0520002c2e1280d40c01c84142c500c01e940d03440c0c04c1d46501000345c04046c03030041c2c1981c180c00e110003108240c802003c0202941a4828001841a40307065502181807510810407540c1190724005603c650503199802800840ea0540054550b141c000c4030581e80919649482031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 290774982 1250 290773732 290773759
    0x4090305250c0b04050607020909010b09070e18061e03190c03050f010c122f1201140d0602031504110d05010509040b041e150f06140a120303020f04090f0b 68
    0x200d16008a00c4007038882d250030b09c04250760034001e5004030590a409000b595403890b0194000c0c0c504c0c0c4480380c410740102d4070503600d500c0584403602c1003030040d03000074040c1e0004452107405980caa4102114264140034004500c85000f400f07071926000d10340704548180c2c88500d9802c1050800321140304019040c1d040528034076880707620411501840b400928000352210412130380c409a540c41d041034200c0c2d00d403814280205140d03010080c10a02d9070038001201c160307032111410026861040b10540e0894089000c0340c2c00507903ea0083c642c85044034a00241d002d1807280010261042c0b401d081c0c02c0172030009140d4450220764090359014200a984111150809654013a4981c100410150079402e249248070340c0f001c80d00003140c030505e41101028251a056510380401052161485003606241035400034241040611403100640c004001c00070f0a80b8001e134180c088003446d03008030f040507400c02000e40100510f00142c800b6140200000400c0c049071411001210120017103244140d06981580 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 290776232 1250 290774982 290774989
    0xc0212070e01290f03070503041103030f0309010c2307150501141003060608061203091504090c0c0203030d0209030703050f06010608060603060d120203120117061e0604090305250c0b0405 82
    0x2071b6040546441c2c801c3c0d80ea40d031805c04902c5c5410b0340380d68503418040080c00c4200d218060000e1402000c1c148000c1150f968802400d540303445120012040e4148003804900030604d40b0f0000d091014054005c403c044143c030395011007150400d0f0000800c82c1041c0640c0b52460070034801451041c0030606040050743d0408001a25400b002440c26110f129800b807101e134994000e0058443e030b602c000c1d102040309800145280e0043d080ba001c2c0001440c0b030030074030340e031190701c81c55691005940140195280154003210b00b03020758050300705540c0611803007400000182c0200400d612510717100c4050800c650401380014503040d0701928242c0b1807403051091200990780c4000c0c942c0d1650f1b1190500d00101c5440c00c06a00f103000d0644031040849100300001102442c61001030302d0342c0c5500080d141c0c2560303a00c00c1c1141c820200a0b10b14401c80980000404c9424581e0010402c28060f05069080032421404803000c071000d0002c4442c1d91b1000420f003c1004014500301c4050203450703182030b05103824800031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 290777482 1250 290776232 290776237
    0x5120f03060f040f090c08010f0212060910050d050f061005061813020408060103050705060a0512060a0f06020d0806010f050a200604050714100c0212070e01290f 71
    0x38071620b842d9508040c1607403640d11100320090901814000ca5015082c400320701e8205115902440d400c0440c00010444544222200d8031010385640800e61038440510460b940d006200d103282c501900380200d000e40d103401d540f99106d4401d100400c0891151320b81c4904210010344804040041c4610038445a0395a07010f441002003148010045c4440c0140000c0c4550300d810702e2103080920004002c120004003080300e6040e00d000d1000c03107500301e0740c44092003441d120349440000041c8007440000030000c00c540b082034001c07500800030340940c2e80f10502800e07680300030752002000da07004440140145411060450b030104017402c0401c03140c621204003510500c990303141c0740c04109040b403058138a86120300711900e41035840750448509240a190803a42e820f2180200d000c4201075841400d210b03d808030022910001c00d035115040f8100b26828003990421440c14004070340501c000200e1065400c4070310500034420320315012050324401b03940c112548440c21300c580010104110020640304500b04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 290778732 1250 290777482 290777491
    0x14090c0a050f1201060e10051503010524040801020d0e010c08010501090b090a03080d0c17060607080f1606050106090b0f090f0a080d080a061401210207020901030b0405120f03 77
    0x4a01c0700c15648041d400b8010f0003070760040710600e07140c6070a2001640060210000351207040e0b489c4c5541000c40800404580424808c05910556020039004980d40700f0083d00006945540007a003856106c41d0300301c1c2680c11040c180ca00941e034844c11314820305000d008686290709903003000d5449504040000b492103001c1d00940c8407a540006680d611902d502c0c06000c029500b200f009500c0f0089000307a040070f2311411207040001146122600c114000e0b00d400c003406000028a0f581c545449580e0b5423001e6002035540d90079102c0284600c184501088500014203803055100003090b6040c4000030346108041d802c8600707140c80c140300d00040070300c51104581d01c2d031500701e075012150342641c0300003050002160806410b03030207441d216204854104101a000d03d06c01e4805100c42e98860040d075500600710102e1600254495051140b54600c54080c0b2018016006000d483c00740c840e004142c0151007a403003221140001d10811081c0801803119010084921091038501030b01c41800411500000c0c2c13 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 290779982 1250 290778732 290778739
    0x907050307090308031602120c031204030905090901050a05070c050c090c07080403060609111206040f06120305031503240703021b03030412020c0d140f0114090c0a050f 74
    0x7094446010b020154000e583c8428030654030724120001a801c6981d1034080400340c07080c2500b1205103d6220250f0395102440c070300641c14039003540b07040700a803400980103406000c421343c80400ea0b9141e9843e164402c000c4000081a107003403100303600f41261002481801044001d0200100040c000328075070442100842c1c0c00b050310b0700c5850144205100d007003401460b411000030000100203c41e0804400c0f01d11100c410417582c90300d041f40c00c015218541034000400d0300d020009141e4500746d4450320803202c4200c00040c0303207601c03032000c14010600741d84190003050020007040b441041003080100c03c80c805030040c0a43c141010041050301048054611030798452000003070400b031107541034901280d115404803881c0501c4102c115280e134800d81d01500c0024290881004c0341d400001d4a008000020f0005903511415450310b140100c500030a8112a004852560701d804c2d000340503844505003c00ba14003101d0410544403464040c980582074000d440c0e01c0c500300616940e80740c500200c002c00741c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 290781232 1250 290779982 290779987
    0x101a07020f192c090f1204060903030503181009021903051905030706060603090b06010f0203031515181903080d0f090f080c0d09050a0b0c0a0b2401030b090705 70
    0x40d01c41e082c048843e4030f19402c00500da003048095103000803155074148581040d00c06100070007110381d9162055005440100d40c10b4001000044e128100850b400b540300e92407c1c1280c106c5010103420881c515256099040d01c1c0c400307000561408040100b5444103c960b01d5190b0392070340c2ea6542c2c80e0010072411001d211000400602405014070452b10400e03842142001540d8440e840540103241040040c0d4040c07120300001151540240c003c02c4105142d60019811556040d01c040d440301c00203103904d0341050350014114004c0c10800042c005855029440c06010340220051144d00d0744000320280c8281502c5104101180c40081111505004010042500000d05580b42d003d4041c0140c01030441411541400c00d010303600000c1c04c0501e03800d00645911000e032038400c64826030640a12a0b2042e0060000c2042074a03220007082c84800e02400c1d122070a0164071a008200c0e4215021440211128555081483d582c4121010743c002401d080100000801c0410b0020304010b040c2c20a21100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 290782482 1250 290781232 290781269
    0xb1e161205070c150f050307271a120903190e1c0507030302010b040b0108010b09150d0b3c0a0b0708070c0f03020612101a07020f19 58
    0xa03800c4415898203c044500166a18904040803602105050000070790030740b11245007038030450849014040b0b42c0d54502c0707400900499040110942050300044080304000007030185242e62801c1032480703041d18150788603001e00072440142c810003010020783d83c0080100142440f4500c003085d900c05050b00c0c10540901003a004100e00005445010b10000113001c2c1a0041103000906401a00d10a50081c8a0305103400700b80300a650902400c0d6021400083c018007003402002c001e091500002801940c8050300c85107000c003141d0000c1c03107400c2501d448510b840c240c0d0420b8006e40480b86505072070140103086c00b03001190380701441400102028101c0e28000d0b4596a52642c0d40050711002c0f228542c1e92507146021002c82c0d01215003110b071140c1e6140d0020307000012060442c201ea0700909883d02e8448902c02050851074014203030344210a1198000c5610b8203c0713821091700f000c5240420703940700101d004008500c000041007503c54039112081c52441c041d401040d1007240c0310f0b50400b4603221403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 290783732 1250 290782482 290782487
    0x70206010e090a02040207080304061113061412090f06130b010506030703110c100506150304170c0a0b0405010e0105190e010e060f0105090f070c080304050a0c0b1e1612 74
    0x43c00e560203540f050000c10f0b84024441684000c6000d6031203000e00300b1403003c004403030389214001c14480b202c5161601e141000b00c02c0c00f5081852482100d804800e01d851000c01c01310510420554a00e8229480410404059041000b0898003e0719014414406d5140c9541e8241c000105000f01800b4003404804116214000e401480d00f20b441000c0950302d4007010084640e5441034401e091843e41c3c00d1401181c01403d000c03162070f520080e9142058038503590350700c551461084400140c4d4090000b0000041c50341002d01c00050700d1445004207121a040c2030030601d0a643d012055072080b6403401c4140007405220032000104e000310b8003400300b80b02200c1c10320035004001c5004207500d035018a0781042890380d042030b1910306958040b282d61071507807612144202040e1003241e110700440c024165510128040c00c01966100344150100d40c0e0309031099031048848015a8012000c41c00b0100e11640580c1c0c000046540c06000720412600f0700d070700b1841000e40611b8043c0040c00015680202910262 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 290784982 1250 290783732 290783743
    0x2030c040f02030709050a08150c1c02090915090712020d06090c030e0d0c0602070804051002010b10030b03030301032a06050a0f0e0904112404031a070206010e09 71
    0x80244200105a8881414000782d40100c1341040003540c00da4010459103001d0144009650341c507402071007441384101c00d0070060040602501001c8100348414203260000c0001081400b1105d0009600c4201e558280a6814400f4106400074810400700d01c240e9100d200d840c0d0790081c058500301d10061400c001000083c4145550075250500301000451440110741140025203d10340d8100105c4c807501218a45404a01c0a840005503042c6400c001090310341c0c000e454070b103000e1440705240541e1a80083c880c1480740900307402503510b54243c0552480c00b0000d110b42006a81003e107c030289442c0029264071050000800b452103109001a5002c001c0000203656001e045030100b13015165040940140c1000c050040060b034001180c4450501c982442c4520800103407000c0c409449644e1014041c98a0300c0752030f42c000d81c204909445104c004064840c4070201d45c1020307640d03a81141400003041d0041943c000c1c0ca10210004c2c01302443d400100141100d00312825040740d52501c452450411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 290786232 1250 290784982 290785003
    0x7080c0111060a092a030c05010f020d0f050909011206110c0307020d080d0509100509010b15180918070905090a0b040f0804030b15030a02060901030207061e090b0a09110103090203 79
    0x41d01c45c008034580340da5400781c040c0e03070262800441441da1400112103981009007003100680044150000e00760007050825540d50075820403508213180703176003c94403c4609912555a41142d03512180030700126119104401c07400340e420a1070089041426982e910480c0d000901560520319200103220610065540d820200170f0140700500340101001e035540c0f10307905e44000e0140b408010500c01101442043c02640000e00340e00d05800c00d41c8901482900b12042d00b03010b030491440101600c1d034400b1200b174403580080b68011019260b1203e280c3c5400c00c90340082c601c00b89400107104180c031000600c40505076104076030a200341c0e11032030104d05450f241c9000810b40781011078003000700061410560704c255581d2a100e40c200b00071104040d600c03c20801d010303401c28001c00a042c0554400d0300103010190082802154010741d404030011008d02d0942d03d11b518a0380c1300c0c214410490240721941d00325600d0304050008500a440302c140492109040030f05040c1d4990848085460600500140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 290787482 1250 290786232 290786273
    0x100e0f150d0509060910060e060d020310060e0a0c0c08030408091507300c080a230901023904061511010b0d05030d020307050705070807080c0111060a09 67
    0x154100314409958a00050b241c00d80c90b40591201b1207100d200d184600d10841c3c064084512644d110708003408400c800d02242070f605406184900d4542d01e0b21406407000401c1407041240187c94580d69a03012500038144010070800646500c80c08104c610040d2a00503030030401180c1d0311849200050f05d0020b5598400a020a020030410300388510308000c510401604e1242a082030702011a40711a43c03002c0c04440040384e40300c44000007060105010304010344081c10800052000c0c0c0140e001c21b283d0150008a003500002003021039943d052010070300509042c1100c48900c5030230350b0341c280704001c3c001003070310011950701d4540c0065607980c01020040c030108264001604407017100410380b00701c1ca1150141582007405070800c40c00c010440d40398254012001e941040d42c1180f0f030310702035440075088008000003480440040368061024038005d03d500350040c104075190144550810706011400d42c1801030308140116150f001181a0b6806a2880c8001800003002d24202101c0940c44c01c00c81e50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 290788732 1250 290787482 290787491
    0x518070b0405210a060b0301020d060b130602150106050f070b010311040e030906160623010602010e12070219030c08010b0102010b1912151406100e0f150d 68
    0x4903044000000d2054800079107160b4102d8140e142d0b4181c003060a40d160882aa01041100000c00c040d13500c4401200401070000d40351140300f08480003500c10580099008007400641d0400300da4542050350010a6079002a2003003a60002c40c041041d0014840c0340140980005e0560400d074400301122444e6030f01041c85415942c49007840142e61074038107000e40c05940340100c65058200000207031a50880010f024500d003c10031042802e24660301c000403640300b03803103503800012001c2800003030b1300201071548010582d600d414002801d40e030301800b0640c001d0300300210015040c404441254006034050b03e010300d240c00c4110b80d8a0078540755500240c50112000f0011500b55010341268490003000d030700910007000c2040030001b280e8801040d0800da00c1c2d02500070000c41440c0300c50200103502800c54a40040d01c101d5621003907849002040e5000b103446004c00c16549010b0f40e032403901c1102807800202c00507041d40810b40642e4181499071084032a841d81349a12503d120441d04010181c00d014070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 290789982 1250 290788732 290788739
    0xe090703061b120908090f040b030307050c0915010210020730090815060906060c010e0a0b280b030703060e030a020d0810030b07030b090f06100c080904051807 70
    0x80c1c200c0c40e007200140015203c001c3c1c4982e940450155035a55a00000b40e030b450300441c0d00400070401001003105400c80e0300e1b024919501d507400d00150040500484c040c1940c0c51141080010090000307050303030130100f00d0565400490346d0004042031840080e41300160350f0307002401c10280c140c103104050b01c1c4003515895100d203591040007000104014a840d076000107911520100e4032280d40010340e5540116000000d1007070328204400300d800040160000c0d01e800c0d6525221801c0d22145444001980d024443e50400c1210b0480b0703207517001c55811007800c0450302c4440c0c84100ca800440e844812907403074228646043c0e6003400450001c55200804000070740701041d409481e6000f03107959401600414003800e0246008844992240810000d0035140c10300316564140c1054002e4941c40405607210800507464480280280c000c20110045804902d840010480f482446030500c0e4200030200a010740060000d1054400502d81104c01103000e80c0e44807660300402c5100407640c04a40318528002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 290791232 1250 290789982 290790011
    0x2102070212100501060207060815011103030408090a09050613090309080d02010f140c0415140c0606041d0c090421050c010b0a050a03060c0e060a050417070501090e09070306 76
    0x2652200c0c0d100b1000c1c0216a0303149010f989400c86842840046004000000e0b02603014003200c0c400d00c001410002c91000e8110307050342c51900229001c0342c82d000b001804605a2900303c0ca06001054005014040f034a400c0c3c011071000e100340480c2560560f102c0c0d400504160088242c0000313442c0d034400301c503400750700350100a0203400040c403458483c1e03117081d841e4411101254803991041440071a218601454030030000c4210105800c21020804240c1960343c45180c140010000515040003d04142c100031040104a030303941b45050488604801d210a00d40c9404900c0001c10801200d000c611070751a07041459010403141c640c07074a81d00fa45207071206a144c010000d495030000b458000c001040a02040c00001c05040c05116405200c0300010000194980c100d035003140034910f0568007103804c1c840856101c5e00030640b8000441d6001c28103203c40300000d1020f03441e041038a001031070040d00d0f02002801d10003040c00341c04000440d100000c1d014a108000c0d00d0001c580c000340422401e24219000b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 290792482 1250 290791232 290791243
    0x1e0f110109021e01120b090601111912020f070f090c02010228080108061b0a051303030806011704110d08070f0308100506070c090c0c0609060b0118062102070212 71
    0x100740c007082442000320f00d0b001c0706100e1b041c440ca1024056150320b488150043d503400088009060381485504c44d510000003000c0440c483c410321a85180c001c00400c0040a41402840b1002020560100000b000205407a0080000301c0c0c80c4641c002468416100b005c80c0603100301140090310741c40001c46040c042c07100600d80d842d101107654502545036207800105403903010035194501e400d00c82c040c0301074030854140024200c017000e9080040c90401707a00f031034502c0100e9a81c8164041980308080184650b04100c034191030803802c0d500380000313150585c3c0c1c400803059040b440e14020644405510104181e50302142d018981180c140c0b840d1040d50301e0002d0a001c02120450f00001c0182000169401c01c82f094640c2c0e640e001d4034107400d0500308014a0020005458804201701c03c0002d21008543d1034030400c041d4038003404020841040601c0003403c44001c07107400d02c803000740410007001401d5004e4605140203c41000400903c01d1112251010380140c0314003a5100320303240020701805500140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 290793732 1250 290792482 290792539
    0x308030105041b05030a02280c05010501060306081e01061a0301051c033c05190c0807060c031409010504050d0513140d0507151e0f11010902 62
    0xa00380803107040c50341c105003c0b0b207541c0540400300d40144041100b884058000e02281c1500b40002c1d050b41100c0da84903020000450080d501250052010409010b001e004a07805009141000d01032075141081c440c0d136411490001058642030600000c0c0f04140a401100003031000600751809040011928402540301784601c034401c02907100448e8041242c00c900c070038816019240e07010030110b40000c0591110903501c0721038450250034500e500480032004010344c02511552816141c1c840007a0581500c0c154810b11014030403011b000000140102d000c070b5901950105002c10281c0f8140c80c164050a44011440d20840c80c003020800d003d0415403100744a107014804035001c12048000955482c81b405d106034018500940382407240420004202c80d0034000541010600031050b107549041035070b60b8003d000c448542030210504554002c601200d008072128450480740c5200300042c081e5288035000d2800d2000903007104600c0d4000707602014003190040d00629000704105656100707907a0480 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 290794982 1250 290793732 290793739
    0x318080f070612060605030c0c01060e13020a17070323010204240305061309020f0a0305070509011509050f01020c030607080105040f0221090a06090f030314070c02040c09050603010308030105 84
    0x5500030f003c507040340070b131004654403500c4480c619210302e05018a10f622840301c1080664031207500160145800440302d1280400049200340094144100441c85910f40d02c201150f182440c6449031048022403510308aa5100403103210410f910841e551034440341c0601c0007032951020400142080000090340c04908030b0105104405200301c4040e8100e44007a11000c0e004020010540c05003082c690140c001c060005000604d1501240c0000c0c0c103010858008503018ac1110381c0802050070200185030242408450502c1100c081c07c400401d488198807425102700108036503004280d0082c02804c11000d0007a05807500c9142c10b0360080d08454003031046500a920b403641a0341000954820307a020a10309880b00240c074080c1c0ca540303146803440900b9a001e50b000d131864140001d0b000707118016400c2d01ca00b03001a034100c800d00f00a4101c80702000c1c015442c0959008100025502001214086604032000a600107804800b10b8540c01507401480d000040040080140b01003003024604854045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 290796232 1250 290794982 290794997
    0x305040608180a060b0604180606020106060c050c1e04020d050108070602030a02031c0b19031106030105180a021317100b09040f05160605120f0705070318080f0706 72
    0x5464500c001c1d00b480c0c05807880c0c03c6000c00d10009a0f40350800c285803d0002d01d2181041d4980c16000301000d420700f00032000039a11803080100c0364080c0140c8006000c241048080141e2a4540e0754541c80414800e510030780e40e49007075500c255480340d4000b07c5031130040e00840d180e040c0b40042400508081c060001c0070311448030b00013415480081120041c40003070380a0360504000c600030031303004c250000706200310549650070301c0d5181d1900300c008401003030710000c1d00030440d107181000000181c0c8010070600030354041005000540b9004400005464803400c1d0071140d82d206541d00c4000d001b03091441c2039407030408030009803440725031501c803000f4601141522010403240c0d05580032540305494080c0c200c04d101002a011079142a21030702203078010025504074407031901c012481c0703803100d41000001c200c001c18034801c0700308a5100d030b6501c5030b020343c02002c1d6810005406841801200c1004040051208004003127240f0f00145070020905502152500c0c80c90522454a030031250041800003a80d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 290797482 1250 290796232 290796241
    0x705011a06041a0702060c060a0605040b0603010e042d02121b06070501060e041a0a05010812090f0909071e050607030c03050712030b180906070c0507030c030305040608 74
    0x21030018260024006141600d81440d040702c0c0001c2c3c15103401020740340181406050003607201d620082c040b20b042130015000603e0503002c081d0890302c55401060045161005151498442208517819608885038518080d0307280d00e80901e4400e104203c89a501104094101c0300849841d0606c4a50348225060100380d0304020741103550340300c01d000b5480300600c0c0c07020b00b20060809000400040e03018000200d0040d443e1400c1010040c1c003600c1c1190045500749105e43d411540209103900702c3c401b00c01c00d02280d498100850b030398a918002c2990b10000010394031480f0383c0c81c0d90a645090301d002d0105200c620706101e440751a43c80714490154181080642001c088000413007000c10b4540040030a400c0c040e40b61812104221a030f40300301c0501c80d0400c01c020100b00c03190383c2116074202c0380e580441c10803000b0b000d00c00c4c409548003031446641c2400060011020300841c0141d4415060300d0001006141401d20304c0c030b01240b50b4030140004941e00d4021050551180061090310865100c458450707c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 290798732 1250 290797482 290797511
    0x605060a05090f070f11011401140102150402040506040b04090c05120a0309031226180109030203071106040b0a05030f0f090307020409031e110f06040b0112020d0611070501 76
    0x1000c640d518400342141e00001e10607401110003030701130305ca240b03484030030040c0400307406084030ba0511084c0f0490001da4010800c0420307600d5040c100c84000e10140c900120045200215441301400003442180c940c40011202e84030369002050028005005200c01c10040c01c25085410700760143c0b90203000c4040d40c015080000282032608a907166481d01102461516030200814018100004000c030a20100d500d5000030310302000348802c0c82400d00a18288072900503131001030701c81e220030540d0510503203e000c2500230042da802c8580003c2c1c51403900d494174000a02c607100b944c0081003041d50200705810403550010240d8801d030740c00c46e2035000544680c44680e9000c03a04407000d04032940100810001820540c2001c4080c520a044c03402c0d01e00c044280c0c00e400300310451518400158140842c0c0410b0790200841202d854158014019500745511500050385050140ac114844608486d000310345416200301401600100c041110018020702002c4990280c41c040d035040d820417036200d071010b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 290799982 1250 290798732 290798749
    0x305010509070e090f0603100e010b030c0307230301111318091101030e07210510050606040302210604030302040305150f270f03073e0d0f0605060a05 66
    0x220024050b41c4d85a42c0e1a6158148100080ca119094020030031070790880400d41c0602004070a5860000c41c1542920b001d15240c88622031101d8429404084204580c21061a0300594000004440d2840340a520003081c0548a5200803400c8082c0c005400c698403001c5651210940312010442e104001280910205690301c0307080160018404c2c03880d0402e40d42c0654003440d01040c1c884280c964169403800da134500000e4014448420252500c032200410409000039802014800001c000030304190340882c8850095003c000d004800150720700a41e00b04040760220340c0010041100d40c00d01c0c052078010081e41041c80704944e14070030344036002da4107420140440d2082c1200c40c150002599480300c1600d00040700d40c00a00c054054040022160009010b044503d8040e0001141d40744024a083ca520b15101524042d042d00258100071a1080720400030f081c50704102800c2c1050b83d10007000a119080c2c0c040000c1c09414009124001c10240f03400180c40f4250880d216510f1540d0f60081c807074900d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 290801232 1250 290799982 290800007
    0x18010903090b09010c02040c050a020c012a03090312020a140105190f0b0913030807090308070204051b0c0a140a020d1b1e29071113020a030501050907 66
    0x194076080a100070b184500280103643c0c01450031504559064010400700c4480c0b840c100c0014000055114409070100a1040c0d0301200380f0303200590b41d0290075140418200095448400800300300001c0c1403501c1905058081c607001045800b0381c0b8000305010755a0b607192901101c03248040c1509440110061044500c1142951404140c40343ca61031a10300a106c00d0301e02c0005c0903919001000107445103a07035030340300d010706058040315560300d07090141803003400400100410a130f0710303018000606400c040d90071a50341a140810a41c841d0044500700241c8518031040d540c0f07020801d0600c0c10310000d010080e46000360744900100c44002c041e01c1d00c034841020080d40008880c8010030008040725924504e03003d42d0302d0124141512002c12481304d10346010341041000610354244007030926402d01035201c0d03040400c1f08031040d0010350b003801c00313000742c090192000000918846464807190610760f0325042d049000c55031141e07030f0803000d40100000e01401d801a0944000181382070701412400034407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 290802482 1250 290801232 290801237
    0x6060904210915030b0a051002100207022e03110c07061805060708040e06040b0f0f0301110c0109031707091211090f0f07030903050405010c08040b040b0318010903 72
    0x40d0030301075600303a4071a800c4005182085550000040c0040c01c1c6005492010400d6501044468070481040040021904164440c05001718180c0905400103100400341da03418078090f890f03680d98000a00e041360341600d22610000c00c1031425032000d10282c8843c080d00344a4508116591003210400503d0003900340c01c040e154042c90062020318019683d8070788442c003850081c1401c607140c070042062754000700c0c401c0b52041008503083c02442c229044551348114140c900708026810080060b10b20407000a206024512200c42e80d8910388003900041525000740c402c140eaa00c80303414038240205201501580000d400f07031090401c2e82d60f032500c1580501303425035500d40a00d04100d0f011100140403c2e0444143c401e400514440b074a070b000b0300342d115407140c100003201c500e0901d465881d40e41b401400c0004051074203090ba00001e0700401960150340d030038a0b085000391128a0101c60310300c12600203009000340030800052680c80140254800e404c9042e04228004010b0742c550301340d420f2500020013 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 290803732 1250 290802482 290802503
    0xf05090a050c0f06041802130605090609040e01090204060611010b04050c0307031508060403030f18021509010210050a0504050d2c131a0108061c11030307080307090806060904 77
    0x1240d103040c000c00c0030078840c004c000514056581001c2413001091400e482c0c1c11070f8011804e18040000380c11004020704d240d0400c4c1d03140c5071010000031803601c204070070184119520706169212440c2503101c1102c5c554094020456030340c48000c0901381d60b1114091803a50b40c00e01003010414107243c040c841c000c0c6d0f0880103050035900c81040c00d901514058a500584512100c0e0015582d1401c200540c00340b401784d200044c804942b0341001083e13540f4140002034400c0c0550000006031200c0107000800d040302c01a4507100c01400300100d041c8a4401c1c0c051600c07074105010300040d0402a40054001d038030942c100c034041e94482406a0f2400c0e002800c00d02c01112001104401c007020180160300320030020490604000090084007c4a00c0d50240008098101000711000d580064095070054002c07030f000c254892001164440c980c1c03950300010700501c5020031003003081e10104207460b446c40d401340400d0f40341d160103140100035455910404c40d052180c035010900710f09009840c640502d8000c9150f06 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 290804982 1250 290803732 290803753
    0xf0b0d110904110a03030503011d090604030c020a231305040f0f061b05030703060501110c01050c0705061603080c030c03040b07020c130c080604180f11130f05090a05 73
    0x201c40c08010300580701d410302c042c0903c1e80c82c0e84511802003c0e6100e5181e554495040405000305c0359421201a0303140244542805400c000004505030300541c0361600143e5200f00e4404a0844400e80c7d0100d04400341c0290b488002c10311138466025070381016030344004810480070540007510400d8130060315410030701c450f443c003245881c03401220060042001240c1d01100d03550b100c0c80d083c40d0015500c002100402800456580341c00345e28001d1a00b441d00600407480400e0b9561280b4105000b203062041c0014414100c00d01070003040d000f040020203c6488503a81d1000f46c1c504003041204500042241c000148000c403124152801b80038801ea66600310343d11661403501d100d0010f801102544240e881076030041d5a00340c0d112500458190b0b01042c4080700c07000140c034442002e044d89100707a0a0403100011800c2170142c0c1c2000a8001800b00c000c00028106518480d22401030f180c1c001c85880c4200c00306c088690030003607054800040070000c65071403460b5151103a5009400034515003000c034116 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 290806232 1250 290804982 290804989
    0x102040f081b10050c03210601020c040b1c030e0a080a05061003031202210702010f0b03030c0a170d060e010302090106050c0a030f030e0109120f020d05090913060903030f0b0d11 78
    0x30a1000c1a44d0200c0f864841b1070207800e900d080d0000e00c0e06000c081f903041040101d513814082c2d40d10018080d00c0074007401300c211001a0343c0c0d0017846c017203134042056031100f0020b2500c00c090340d04441c000030341801d12807619030091503200c02e40c10710309441612819010806420b2910f90345000c90f60540c0c2c695140c608181c4199000e507000038007141c00b8402c0c01240758400f900101c000c03400303050250000900b00c0c88880e5100151503115404d244280c105000307450a4002c042072810a80d503219031280301000c1c540f103144005020b0304c230040241514155011560141003400300d8162802150001d05982c1d823420100c0320740c030404080b01101c1c1c200710030140000780507644071910003c1a0401140342004028154210350501c0000c1e507188515003002e880c0c86030000490408540717140f000d41007984080c4006020351041c1e4941a0140c0031500000300d6041d80454064812a8412028007090006060040250282c8149400510710b0103c16121900d000c070148d03182c26030700000c2ca60140d49100300b003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 290807482 1250 290806232 290806237
    0x40e131b0b0a03110c030a0c0b07020703030c0b1b0307050a02011503050a0b0a1d011506020c0a031b12061a1c0602030a09050303040b0103060e060103020a0b07030207080102040f081b1005 82
    0x40794500b004c11311400741544ca0900140030848080d80c0d604004503c82d08110602c0c9001408220654015690502c003180d8405082016250018a07940d090b0315081115203001e143c84046e21032030070b4080144000c2540c000002c01d03025041c1e900902c4010410b10384800400c105200c0104540d028000380c2001460421800d5030005007803000040001405404000c2080f10100f840c01c5a55954156034001c40c0961901c400390042d48000e00703207500d10314049100443c01d4040500f242c0315101710000340242d008501e81c0074254881c540d2104e403010345031034406061106044020f01011544087d80e82c14000304409903098a00f50420000d280c035106c9000a61020708182d0146444607040c00c0403c201b0002140036a2203000e6640340c5601d9424080c0031503001c0201303a105500700100410150355894074000c264ad41010780b0039510396440ca002e078600195a80444030550011030b0000d0a00d40b42c00d038000880304100c0c00c0e107006c541908041c14bc040341d11001164031006401001100d588039402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 290808732 1250 290807482 290807501
    0x3110f0d0f1d090901060503060a0b24090d08091c020102071701060308071a010b090303031914070e010e040905030d09030203040b040e0117060f040305030c040e131b0b0a03 76
    0xb0722100c0c02d07014804079443c12000c54203a000c5130345a8070100030908041050302d50045040404005d01c09644002400165980020524000d05c1d2900c50b82c2020b607140440b180d07040000c1542504480d5440c0000158010440b028400d041c4414410f56120000c078026008580c168060008603041031a481071002c134810f4884601c2d075a031480400060003900040c200980201d813501030551a003102083c410700140c104010865080c4110078843d20000140e0790491011006002c0801d444030f2520002c5c4011740740d1715038440500c0c00303001c0c02c59080000068500310030307600d035503050042c4018082a42c262100052a80e0310810a41c0742c604401c0c0d02130300c00c1c00c2c03103441034a02d07003a514040d040046c5c1194201003040b4a049004004035400c107142c01002454440150801c0e00d860700c442a000d0b50004e0010302403000010020392500b11500841e40503110034411488582846100d100d40390340c000c442107500200c2d02913041c0040d01c4103003004080390070001d00d0514081d4800c030224090b201c0c404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 290809982 1250 290808732 290808767
    0x1e032d080315031501091104060e04091106072018040b040206090d03020601060206010f06080a1e2c031e0f040312020303040c061b0b091903110f0d0f 66
    0x1240b02005980078004810072261455600ca02941421628411140d03010b001d10305603107007000708000003500020590410407048030002103020007810140b09582013002e03182d511840004103101001800c085c000c517031111105000340c0340e0076440140404640c070b10f92600000350f44d04002400154113961503651085c03003d8441400c042031100461100380c0e00c1303801200960402d000600c1080d5041206a00401c1183c00c617409682ca17104024104e4207014040080680e1074805210400981502045038092244000c000c1540b80ca8007030701d070185024502422201084a4130b0580300800000c1ea510840b44010300314400401903403045a40e8003080c0040c800003001e10000020440c2503c04020b166410307006190b032413400e0710b03080300d070403030150001003c0c0500032030804401948040d00d120202d80c044200c07401901d542003070628028100c030907401240e0580c0402010964026076503903a0408103000c80f03440001840e031003038860002c01039a42c00a0750545002205074070a240e4062000c5484 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 290811232 1250 290809982 290810011
    0x61202030901091704090b0901030209010b0a090b0a0201150e160c050114070906020d03050405060a1104080d05040303090914040b0c0c07080d02070e15010c05071e032d0803 76
    0x40d55036100d0b440c204c090784000741001007070800481215000e6001546000c90300d12441758110b500041c648001030103044445075011071544100e600400e0320002030803090070b540361603814100c0020302902240031111840038540c0700006409400605590081401d941009500c02141c1412110f046c903a9400f601c0720b40d229211101c86613241040d44ac0611711a6035103050a03400c0c00001ba180040020301e0100b014603000421000c0b4901103443d60300080b80701004a042c080300000d5000d503002d02e4110700620701426007030b440b5060b0420020400ca91180c1c6075a0132180da9004140115415107030185c41c07100c40d04002400007a61b43d80d6840d0f01920301a100d5040c00c403140c83c4030307180c11019004400943d0000c40c074420030070340400081d4010405000007510714908001c0c50745c016041170008038184582c0541000030414184184070250606e40d0700329405050317000c2208a02c019038802554108030491160110005c10105d06020a43e0601d5601900007265074200182c0d00050800050342c510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 290812482 1250 290811232 290811251
    0x50f07060c05130308041d040c06031505030f010e0105060616020609010c050d03050a0e0d02120a02150c0913020a020619020c0d02010f060e1e0714190e0a061202030901 74
    0x28524560013039402480000d071114200b02c00000401000111000c282c42402c0070040000e40d1804060150341c40780c0b5010035030360743c01550250034111a4004035414011110281c84810055200110000000000f80700540380c00e03080c4501c43c450090044c410400c2080110007508210006141814040c50040c000c0441511940c1c05c0c408010300c0040081d4a60040c425016000c2c010101d83c8404200034006101030711201a64032941011100001c0c80041241da41d002d0090100c200d101416258501d04c41c6080400d91056a12000305507100380c0c101c08440e40c80f01e02c0c920030741d03801101c5d41d0024242d0b43c403040710800d000c85c00000031054080e001c04c6140303400b18080c046400f0041c200e80000c50059007500c248000d88007030b9003100716130302201d404000070f00150000031014401624803452032600c0d4200308a4403145903440601c8118400503a143e140c0f0450007802c1e035614039a5841c0700c107045456041284900d030f03e104840c0020078009071410741c00c19690082d90007558600001417820013 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 290813732 1250 290812482 290812507
    0x91b0a050f04060e0f06092202090d050a0507060810090b0d02060c28080306010503070513120212060c09010e0f030106091d0c0108071d2e050f07060c05 67
    0xd42008000a105692411300c2d800c100017543c801d054222049420103174240040ba0403410b044480c0d29401d2061800e03040421102d40c11075005010140c510071981016040845e6101116001124248510ba1000070f805125050301405080c1e0507900c1912507203491b0b007800103043c841140507400314203d406070b00142c1d5400024072103840780e1000380c0800d81c2036640a4120380e1429407101c1b40d0450003034002000901c04e20840c1d03407055003400c00c1c61703da03201e403201200d050140d0154100d02242505000c43e60340d404004016540d88202c40d0036000800074501591548806d03070740e80840301418011964698000c82c0c40c3c4d042d040d00904111804050000000d0a4424a900c05074960b40d407003180c0e044680251803007031102e80394100200340d840b41001c002810080020038403400c114008e041d074500107000c848070420403040141080d044041039160b102701c80782000450f9114940781002642058010003d84009608038051141410a2900c40384003625203540180700300041080365280c00c0c2c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 290814982 1250 290813732 290813737
    0x5030c011a0f01020c030c04020304170d0902040f0b09070e04020f0301150f111b040914010e0d09080c100e0a0f03060b060906190e0315040b06091b0a050f 68
    0x140700d80c10082001c084041481403010701091228110742000c0380080e45500d0000d16840031240c00c0d140107070b40b40d60b107081c400c003184c100b000b200900446c0008d04040b00d80d940e400c0104a180200c40402c51529440304070707011520050825500942c0c6180040c160f68024090f583d03d01c0809031006d490201004803100890f0b109070002c0c170310350140d01d403041c5503581d001c04a005208024104201c0300c881502943c0d40e1200c40042c411502c0c1e0a40d21b00d01000c0e11982c02018201d540701d4100d80381481740071049800307030210340daa20b60240320700c041900010707100741d11403001ca0300c1420203001d1843c910802d0040c2c0c6040e1900703810601c00e482c8059440b5403250300020004080819041d07200300d04501d015816104155607041c0304660900c429002d603074608048803800c0003003103d94220b569904006841b00c6d0b8034516225818041c09640352918510440c030079101701c3c41540414240ea4070385080240c1c2a070240c5029040040c1d8600c3c1c050b01016210080011403c5403c00e83e0414150200d01060b80d03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 290816232 1250 290814982 290815001
    0x5120403030206150d0c09050a020409020c010218030615010305250804060c0f0e010c17130e0109060812210a090519240906060e040c06050a050a0c05030c01 69
    0x581c031540130020f051501c1c80080368030020850344055070071019140c1c0065400940940840540d0b1440865041e069a030b0450380204800700080d900c030b11a082d41c05000b0b400c050300c100429007080580c80170a03c3c003c1041803055030034031102408003002800440080400510f4100c2921515240c1c60b000c000021034451408007603507540000d031a01d468030301c05503880c9140d2034040c00903008000351103940050b41401000000c0c41d250310419068100300303041000d00ca850701c01316003001600d090242811100038082c3c401072000c44800f42d9840b0310302d50807107040d88110945500140c0300c03920800302d004001d10011000c3c0300f211140c948084500315070780f80c056414000700ba81e940701100070024240000b0321030040b500580c007001d800913111039490b0040e80303008103500d21041001000c0c11003258072400c0001e030041d20402501e51a0b01c858501a0000d0f20150f030405500207000840c640300394100c0b5400b042c03a603141402c00440301402da0b10a101140c0848460006111030070074804248150902e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 290817482 1250 290816232 290816237
    0x190f0507080d0f08060a03080703020307061103010501020d0903050304063504020a05030613030f210c081f270c030b010e0312070b07110f0106030215250512040303 72
    0x1e80ba20800d0242000c0e11801d030100502800000300100c660318110420100c1c0d402c68862035613880c6c1460202c1c00c510480c0d400500f01c51601740110408420000a541602d0382a0203c0b0041c079440345050702d40e80031174032001b81181d1040100340034552182c1d028601d0041c240c0c41504810020b180101c990406510307075103911045010030001076150800108008081c203a019007081c0c140040c1179079100707a80d0880501408040e002d0248040e126990030700401c0c0e51004510110b0406148020280555212210004281402181d42c0e00100c3d441d14180d84810707001e0303520300d030328104041030120344150740015a840b40312590f251075050342c010007600d51015940081c80301c03040341c005445000400310360b80c000d40c0100030b2424044a403108662025800802240740b60f542d41c00b0854018080000c0c503001d502800c03080400300e6034150031030300c140c170720844801001040c40f00d0b000e2030030700644640c041c0b040343d291030740c543c0043c0204200c00c07031038058010703100a90281302000d2107039072181d03104a00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 290818732 1250 290817482 290817493
    0x3030e06040506071707020606090403020f011a0a060e011e050405150d0509030405010e0409050106081204030b0702120711010c2003060906090a12020309031204060206061002190f050708 82
    0x1010744d0003d41d100288545d00c1c40001181480d0b803009586107002480035001e445114080307400c0c5402008201239003003a1000a20280203601d4034036401800f50524140580c0d8100c502160390b80c0a88180d400c4414103039540e85810f203c0c4c180011403540b006100001344030f010040030a10381c0b608400c1d10720301c0501840041d90303240e088103900c2c11248002d04a4005030020701084c0400e82c0c1c0708420000d4544200e0f0041410306107420100d004041c1a03005c41c0d45449202c0c6489811a5080b01800440740941e51910090380c030841c06036211003000707200030303070b0781a040203848001101440c1c00f00003035006140805010840340d440f103c0b40c40d40c10300226404042c08464416601c1d040107203947c48140322000d0b0881d81045100941e40d00300403040101040c030295581107042d4400c006440383d450008080712040c40c1e020700c0c2100341d0b038428000c040060040a00042d81818100124949a5400d90040c00d40b070b003001900000320401c203802221120301103040e02c000b06404000030f50281040384068034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 290819982 1250 290818732 290818741
    0x81308010515270c0f040b03042d260c0604061b031104170a05101407050c06070e03010b03070b0d060f0308030103022125050a14040903030e06040506 66
    0x2c001103e80346624081c1c1d44212074034000300c444070f81a070401d90750440a9111100314100c000c0034000e6030070548a0241c044100810320441060000c000081405404c80d0480c0c520406251065042d201400504074641c500074070391400c500c00460302400c44509030401c01030040e1141065002d840c10b54000d52035600c01d060101050f0036101c10074410f4141007001004110a421050249100d101c03507203d42c0704219610800305120701c04100c5d50100980380140701a01c8604000c0c00b004240b0100e61100800148a05010b4800c0701c0321040d01100600c8660b480c1d0360101c81380c0314054003060f003654a41e100c040c86500c007040070b48054285145130a44980b08148620111a12070b4440c003d644141c0d00104003003102e241c100e030b05481d01515419800385201c1401856815400250030031441040940301e240c8880003080c008074048240c0245100d070703450080041e03c400701c2c021401d0080702e403150800b90345400c0d40040001480bd00300130070095070b032003101e0303040541c100d40c291401e800c501c0400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 290821232 1250 290819982 290819989
    0x12050907080d171f030b0a0e0c1c0b0402150708120601030618050a1d0a0c05060306010f030e0c060c03041e060f03050703200403140613081308010515 66
    0x9840282c2e4907010388500c801040610102c0d801a001581c11300500b505802d600b0114162038000d5074104001c41c0c400e003019140302c1d008084560f0304401c036015182c0380f00c00914103c0350751074221401c800b141d14030410607142c1c129901000f5204a9000f981915052010003800c40541065030090058a44a032010720410f014528024000f40c100351820906000d03655100d420301090b14545a400a0590f58402c1140018051101c5009032410f07001140030b0351030720010f40004004e126403400713030496560f8070600030300b800305580f0603000c2000302d0283c01c8614460361181074000c1d40d02003146d0320406450302081d2154041d11640c0c00f03d8000250a00000075450907020f0f020b5411054401d100380b908400800d01000340200f030b0205519000800c3c03501c0c0c841d401000da03003002031150315000000030b00e4954440c1d019100450780c0f003802d44400c240300c250110b001c80c0710f01d42c1400340400c40d0190390343e482020b60050a800d03841f18071600002c11a00c40074800e1a21503202c0c0c100600d0119010001c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 290822482 1250 290821232 290821243
    0x170a0506150a030818040204090c0f02070f051e15040f06051204080a020c180a2003060121020a08070e04330e0415060b030103050703121205090708 65
    0x1041c01c803419141541d070940355030b40781d4000c42c0d401030405504c400510220200c1c4284484001354014004103020a4106d0b091780300880007111031f180e078050307080d20701400d80c1c840f1038510440e107084d50070f00d004128072b082c40c4051910800b4582448803800604200142a581400450700207400020a00b400500c0c1c1100704200504081d090450a01500c808103e03002c0390700910041000502140790240c0ca8020032003244180002040745092543c96003070368521700d42c00c40f00c03407080030f04000440401d040070100700641e40d0b0360f81d603030a8a103036601001501c6d2303d002c1c1031608040c44d4041c12070800c1000301d8809030a5210142e5180d5045080c01c040040c08508032400341e501c5146820400704903080032165414811000604020340c65081c14510380442d05c881c2d00641d100000700b4100402c000000c03400d04109040100e0400006840d101c51030703880d010034080240f0940c003904080c008205a045560058a03031460505240d1180350321200c00e40d542555840f950358032260040c49464400d009 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 290823732 1250 290822482 290822491
    0x60e0604140f070e120604030201091203020a0c020411120109050405010c0f0806010e120106091d07030305070305090d021003050a1d0a0809120f101103060607080c0106170a0506 78
    0x11425080d003444041c01110b428064180d070203000740140b41100c81d880d805103150030143c4420545082d0700c0c0c1814042e018200300c8038111000c90801c0d00212040d80a4030a0310078008160395000300d9511254284001042c600008501072030b410301c803401205441220031400fa000d102c402140c6400d15191107030960783c52075005010301458001051005074400016a4800024a0f107111403594080200391080c4901320f106515500704800881c4070016a0010550059650041d10001c0380d0b8147c020344644641c00b005002420801508000c603200d18084c3c03080c2d400007001d1448841c1503078002214100c0c2800103a000c40d0301d0380100155580b07144680f03030903008241c0702c106c5800f04007515035032074914440c2c0040200c0000b00791200e080d11111349650400301d0703075000c9804a14501c445540d655a60302800120384d41450343c40039800240c4019a40142c90152403c6c2c03c040c05542c40c030304150042c005c0506e0319035aa410008520500c08070040c440c2e10300c2c001500c110302d030a0a003d820b2820080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 290824982 1250 290823732 290823761
    0x2d0f02070b04030b190e010e0c0109080d2106050d06230405061303020c040c080f07020d0504090507020c0a06050a09050904050d08040201020327090906070804120504030204060e0604 80
    0x3c10124a966500035405450050841d08585480b03050000502c914140411990701c0c040242110301c0e130010b403281182c002601c2d40c0515030340c4c503401140d4610407210110001542c2c1890500000003002c10741242d18038451011410a482d81d022952101c03001c6000e03119140c507901c2c05007140d80c0041c80003003050502141e0b00d082e41727070986540ea82d607480500104c60744501401c00c801494400e00455030000c00090007401000c40a21000b0003068082c0c43c412501c00488010074002c9000180305c0301c103038900b030301d42c01c4c14035141540900042c24001c040c035003540240100400e250390f50840c104d0140090b42c54054a59150381c0e8005d05012540e000503000394015028440402d20004055200c941c6c40d150a100030364841c0b0040f4214020244044c1140303400d40700010030000444040741c40c44109441c200b2069407601440341c0c2d40d410581c0c06002003941d040124011401084c854114280c650070240d10706a900d074041000c4840c254003199040c00c0580921a0354034050140c69800d46044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 290826232 1250 290824982 290824987
    0x5031306030506010f0e0a0302040203040b1015120513210201240504110c070303050309100504020919021b0a0c08070b0d09110603010801090b180d2d0f02070b 70
    0x2a40040d00ca000c1c50302000e020301c80040b00d280115a071f224440b0024641c094025501c0341014036000043d44d80130394401021170202034010a180f203000024803804000d0303503191000da000301440c400003400c0190082c154055401c0031040420500c00c00184040803d0002d0030321700c1c0b1107005c0282190321160103211140032075030070b0f00c868031000d902c4002034580c03c50300040d999040403295981c3d44955031101d0102e00401500200f8181c01c40301452169041e40d0550780032119500c2c6401c04c40d07800301c500a51101c0242d0205d1360742c0c00f000550a034084d42d4140018603110f136500c90700e198102080703440030b0a6405100410304101c1083c060318002c04a80c8000d00806050510b0002c4a005140d00c0b101000c1e641c0090340107001105800e141c1a04019290503500c0d40c540490341d02920301000b01313480d48018503021030700c800b0300142d05991044901c40540709043c0501c03402c99a014819406003600031861081c03005015404374448280401d6841d020907500b180a4060b0418483d0b520180d2a240c09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 290827338 1106 290826232 290826241
    0x4120b010911030c0403030503040218090d140316080a090209070f11070f060f02010e0d05090109141003020c10060608060a0909080f0c0712050313060305 68
    0x42500502c981441001c1c480c041e40b10a42e54100120f03010001040481e00c038801958206100600007100c070b12200800c0800e09506070340c0c41c00766401014a0000098002056122181240c5a0541149400708449500c0b0b6a042c0a0b4004d114166002400742c210759070000950760342c0105000c1e0a810030a40c0103002449096403d00801e81c180340b50030005100044030b070202c44498812130021400c150007100c0c1c1c005203e5421040d036481c3c001101000509114446010074a40da600e601c4400c20b20006020813011f0b070200f0454009641c4094503510380f5440c55039855443d040241e40d4070741d90440380c5d280460365404002d071030b4642a800724015902c00f080343c4c043c510803a04003c12913110003084084403d82c810050625500f04400010725050001401040c01510156040c0c140c1d00e02d9124640c0304c031403000311825000001d07a20b0302d80402024000160402c0c0c41c00700190300c0c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 290647482 290827338 := by
  have h0 := BRFrame.cov_init 290647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 290647482 ≤ n) (h2 : n < 290827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
