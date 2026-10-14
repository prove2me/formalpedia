-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0695
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:11:59.400983+00:00
-- url     : https://prove2.me/submissions/7593b7b5-a77d-43f0-aa52-63f4d5d4ea4b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 124820143 ≤ n < 125000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 124821393 1250 124820143 124820173
    0x105060f0a020c04061512020a08070513050904030c03170c1e04050301090b1801060e0109090609020a180623010807021203040819020c01021e03120a060e06010809 72
    0x411040207103006640900000e600020300300e580ba5804840d21191011050004d5a8000320459080254200840c1001c010b028000c011005c014046000e0150014800c566004581a02401804024500d600c60b18203840e00402043c05940101e010401d0008030003c0c000c0e9640059100d071540070b0010303043c0583ca4035104074040d0a440428400e072020070010905850278041d20250500070324a0764401c1c207015000042072103200b1710482c1103924000702440309041c0c2c00021411600b030700310042078007540e0381002c40c0100b03100c40300294050800783c400605034088940b01da00303076075000a042000c156a5502100240c040c5500345024282d441d5142c201580940c0213075403c102c462045034880c2c0700342c5020b24240e92084c1c8094480080200b0303c21800000344140740000501440940090010b4000103962904488600c0c01035606554034400c10070301c100190360900054002080e42c6082c00000c1c0001040240a458440b5030f01301e00094295006590050180240b10014809c0b200c2c90202 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 124822643 1250 124821393 124821397
    0x8040303020306010c05030310060224010b090111010f0e0705010507030c0f0f050d05030a0c030b010f0309080d020f040305010e010c202a03060105031603080d09120203030901140105060f 82
    0x100f903041c040c4120301c001c0401e004001039441035100c0801e0115607403d008019183c0550040103c4669204900c2800018502c00d94281101c010410013900d94501c4801a501800948103a880640c80d00c0c3d02c0d070481700303426040072440c4800c07101134648254403407004640a1060180141c0862500480f103800500090040343c3ca460045106050758400c56a0307250404030308030410000110302006006d48a0194891041260701500342009040709080001e414070510702064018190380303e40ca2403c0c087d080007114000160204110350b104074003070142107a40c00c0743c00f0940b002c6d03192030341d81c0280d450144502c0c1022070700c6884810711403440111040d0540758080095805009a08440c7d076481014000680828000314103c62410b40b03c1051500c0e094050348490700c280c0c000780c98040c00c0d280706014441502e0b0001600f5960f1301c3d01505030741c09450380200081042e01e4034811600c02c190f000c005140921040340092140c00c0320708110b01101d40c800e00070580c0c00780041000e0803840c190800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 124823893 1250 124822643 124822651
    0x1c110114090f040f1103011a03040f030f020a050613050708011503080a0e0904030e04050f0106050a0c020a080a1a010b030903040e040204150f0603110c07060f0909020c100c050703080403030203 85
    0x4000714041d00700760542415508a0717155012918404001440000429410480101c0469100d2419850035444200c403402c1d800f400513040c85200174401030098420f10185031110740000864200307081c50034030000441044002600c160044d2000890b50610601908038440c0041030f003409070301e00b503840b10380350fa9000c280ea900503c001800c001c1035035240c3d100460311030b034003d4580706000d60b143c3c014030041d00c1c0024000e00d04841c420b0700600249421400340e8400161a10300210408038074404512141455003101c4039a2166407602420000c1801c3d00c00704240e4100c40e0912aa6071750404542c0e030b8081550340d80101d4109000a200c101854882c1e15032081c002072001c501481c1d501c9500e61044005d030030000c9007a05025081c4416505801031000d00701003004480d140007205e58400380c41d000c46000c2c400400080c2a011600244103c2c0b40d4000b4111490302103503960040010255114015200e58440608100203801d540d4082d8003900d070010f800d81c4500300c1c60b50341ca40c2c0032030003980014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 124825143 1250 124823893 124823899
    0x102010e06180304090c0c0c06030b0109360b18090d05030a11180a050604120f060b030d0504060e12100f15080303060306010e0405030f0307020307021c110114090f 72
    0x1300001803801001d01800d4054902900c480c1000c010310305124008410640003002414100b011141d075a0740d000f1402c00c01c5508601520080c0b1011500307418811120281000307074180320100300c4840f42041c1d44280c0300450b0894003d0641d02440d085040030444c01c84c1c80c2465a040395010b07900280c025001180d210f2104003000dc1d1003868410720060304d400c82d9035540400c01860528080380c0c10140305100140004903125030520740f0b0040c054146d500f911400501c010b4941031398504110013a0002c44d15904014140d40b4900c600060090030b50f0003d1007600d0010307288484a1a050034110480b903144d070b6440b4080e181c00202c440c1d1a402500003440a03680141d559006194060300b40c070301900190060101640c0d880c1050800c0510f081c0c010703001070b502902220305201c0022800021142c3c1c0070f00d190b4039644c480d40ca030750b0280d04600070380c10007a4000d0b00f0b00c1030000620b554205c0080740648502d00e0000500503406c011940c080340c1800300400854100f0070000a440d21704124643d560000b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 124826393 1250 124825143 124825147
    0xc03060203092a0315060f0409061107150b040516080403020a02060f0403050f0706050712120504080a08090a021c0c0f030b07090803070201020601032405090601080c0102010e061803 80
    0x51003e043d80400c03020450703808109080969083c1c9800e100280304a184640c21408904044c0001041040c0c0c4100c840d115560f502c014204200581c0c0114a150704c0c0c44178095181c034418103007805c440050417030801950f0321308440c451641c07505110700c500503208120041c0c12070000c10302c25074880303002610a500f9171041c990303214010b0380d03440000c04090104420403900c46203545015071420002000d00380881d00411420b01c00564400265079802e5000b4890031200c02e03803904240c030013003100d0358003e0390241400108400e2060100090010b20002c3d520845950350305003c2e03036201c82c51803074025800384c1000c00c210b00215030380c41c1c41c3d1040741c021404029403a40c1d411110340380203640c5d40101c0d00607000c0740811424540140d030b070000801d0000099441c2c0301140d40001d4440005000003008844180841c0044000e42010014032000500c0104264140319004907641c150911505d5814441d14114031743d29481800b81c85201c41c3c07080001d01254031000380c40d81d00040760aa05040521007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 124827643 1250 124826393 124826413
    0xb180105070212010f1a04050903070303020a1101060909200d0b07030f09060f0e070e270a06060503010c05091c0218070e090105041a0d0206130e180a0c0306020309 72
    0x80c4070f10102160450302c001a1a00c206420411142c06e9050b00c0e03104901d4141000b140700b00100840304e9050341440c1c0183c0d1100c45540640312181c40d4909156158600540401c2452050b80b00040d62402170b80e640140d200241d002d0400783c0302a46455030884009941030001400d41c440190700400c03181030100d5084030340c2c0700c044201ca480c00015600c007a1140d506403441d1240d0310800708440940d001406803a420092900949407001d01051002d6140304004003030450040c10319141d0203581800e0380c01840490902001038031190051398425407070039150900c000e0240702240d500079030181662004141289414580d81e003005801d90b040400c85410010f1040507907000b51044040e1740b22004542480420b0056517081604824042d915001c880301d14001d10810028141c030003100c031548d000c1010310110f01640511603411452008080b80401ca400398003040c01d10a850302074180a0940c8000c4000d5a144c5141c0805030640040708402e0020604c240c008550148000040b16034000f8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 124828893 1250 124827643 124827679
    0xf0e0102070305040510090308030c130f0b18011d0409060b092712091011061504050a090b0c0f0c0616021b01141c0203070e0a0b1801050702 62
    0x1c071505040700020000a0244254500051102d60103a490301c0c00c17012040c11a95101658400500b014000d280b0100e0442851107281080320098080d081c038102180d40d0361002c01c0c010b90021188607911a580882070541944240d00e138440c401d2161480c04801c2c0d000307900380701c01416100c4003620030703e4442e04110200d440f84032945000700c1c2caa00c0248007403001d49007800d8408050004100d4250085801c407086c58528105845071318208132807004407800031050070f44c0c280c002d00c4007484040c020383d020401104805c0d61001e050800548041c0000d640d03603601c90007164614480107203000b5104000c28134040140f005000c0706440d51903040d28141c01c0502c52490400704a4031aa01c0d13040c01e40403640e01d20703818410b0600c01c3c802c4000c00d001454400780040e00200d0703481020045030030049a010206403143c8440b0021000c60b0b0b904550342e00308004001e010360380103452603001705000400000c00003105c100300c9480a26150310700d041caa10190044810f5841040c069074000542012000661 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 124830143 1250 124828893 124828897
    0x405070e1c031e0e010f08130605070512040c170a0b0403210e0a0309090212010506030606090a03060902190303020304050906010908100c0e0d02011205130b1503120f0d0f0e0102 78
    0x14a00c1e2030b08413482c500341e000103004400040d00b003020480039034180089481c4800140b400f05030b0055001c1410b03034890500729a28007402503501601a0203000384001e008104a802d0305035903582502d030030754603e4004119940c088200700101000e0050700000c0c007291103504c490f00c0301d4600302c1600d140c9540540c0701c035003030b1041d010440401d0b800c101103060400d074010240200038016184298104075010b41c070724518000500c03c6501030000000000c8869550404407500458020056042c1580700d090201c02051405c2c03040f030090011441620750b00c0031074211202103940c180c0c0150716060802e0140140b0746c00c090452414400c05500c0481e071000240425802c0c41c507456070016041c450030348010211a6032650060045903101001310150368003842c5071140f9010603070b011941d61100840c90b52207909504000c1c01c00b4016070180410703a0040b816080c6512412401c84094452000c1441400c0c40703242807452203050704102a2175680642e80112050031908000000e070944140e40781420380e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 124831393 1250 124830143 124830197
    0x60b0d2307020f0c0a1d0c09040f0204170a050a03030e0309090a0c020706030209030a110a08060709030302060c090d020f01021203010b040f08010c0203071b030c03110405070e1c03 79
    0x26030401c000c0c0c0044004104881e100881d0115030f0049040c6c5044a004240c426195042401e06442c0d8001400b40d00180203e80502d01d001d0010064404c20103000c100030b40190107182c00e40500c1c601c404075120390020315089100d800c4006843c04140a40d000e50007050881b589508a01040c04442080e1703403801c00851160324020307404150450350300c3c802800e004147e0080018184140060011070300c0000e107900041d0b0307100c01d070000c07080c0c010400500c2005d02507211058a110302010005180d91041070001180d02c41d808079072182d156000a1070080c028160030030780060310750410340054542207041e9130a80e001030050340ea805101c1d0b40d8250300780c1d00980051046550010382042450002c280700001440315200802940c80c10900007504c9200d0440040c1104440201401901500b02e12202c02181c2c01482e0062056403840d18000e800841d440d074602c15443d007000079003800c2c0180081c034203801006010041030011203d540781d0300005100c050701000361411001c8da00045034400b241d10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 124832643 1250 124831393 124831397
    0x902041503110a030c06030b060f040906150804150207031b05010509100e030d05041b090507030f050402010c021c0c08101b02031c090203030a031b03060b0d2307 71
    0x11260440c1841d64407020190b4440e400740c1e2038110100007003100e815004050b07507120315021500880090018125014119558400902c00900041c507100aa8009002c40f007070081034010074016040140c0e0442412280a42107035691030030b10680344015030040905501c42d081086035a0840283d264594003c0c00c0100d61983d036406c10302c031003224200510101002400e00c240b02d141c40c031035003e0341c0301e0280042c440d04584d00c410200d008c004640804103c0495030520400c03999540b600003001421082ea10480481d00e0310f13800c10f0400002d4010319206030340617141c4071002403c983c00d1040b141691a03180041070680c201d0b4000207020054400001c02c0e001000703082611203034640c6422207a50740b240410b801a10180c500d01a41c001c004d454041e0342e01d41c01d4042c01d02c03014030010f0103012450b8009615020008006141d40d4069200034a80a805403103158142c265000c25002c4034101d02804180900600403845900801c1d00421403500a400c58004021550a0034203024070040d507450300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 124833893 1250 124832643 124832681
    0x10c080705060711010b06041401050418061503020901050a0c0c12050105180f0a0f0206070c0e0406060f180207050a05120a020120030402010c030216150e030102040605030c0d090204 80
    0xda101c4e03003c2815106004281c00811142158034002502032140c3d21800403a000785c070200d905503a000341d00344e8005150100382007070a030255440703c400070032483c000d40324200700b00c2d080c0944580c803038401c0d13030205901a101c96207800c01c102c1c0c09807808841c1c0d010850b4030a080c0880810381d05608086548003e201c1c7c0000316042c104604100003504844940306019400180000c0c040c0030300080c0c0e03800303494001541c040703684414000304070280314005001c0d112034140d0100103590f19451558a20030b500a03841041410b8654159803020b207194800c3c0001e03409110304850500ca01940101f03e95445031003142d072445800d684003424444070119444520303c000c10307603242c515020b01030647c03881d000750340c10b0f0325100d048803a110050201030400303810084100c100c00100b50080219070003030b8000c02d0203040e0b1a640e0750406001c081d003000305140040c04d40c0058281e20309050080d0b80940c2c50036158181156641180c12265402801c41800e080303885048003805a202d134850601022402c10240c0c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 124835143 1250 124833893 124833901
    0x905070f0305070b0c070e0414030a090305100c0e04020a0c0203060901052505480f070b090d05030706090c05040b01021b0402030703090c1806050901081b010c08070506 74
    0xb0341030803065407103440d4142003004203800c0f910001c2200000d071600710003c20b000e03032940d0802c000c4c1c11704181e820480e0340c80005110454990070514200c2141d00c500d0880d000301142c0403507803003130320b204d840700b00085940f08650140525040d000361211469a141c0280d0101c1b1540000746480c3c000e80d0b0000d2140d5581c401d004800050400d024080c400c04404051079220140c00100648601864000044000c29451340c501785608501c020140604400c0300441c04e941a2a800d0211404102c480c0c074400e00341c00c04800030020402c00103c0701d05446190401c40348009111046c80807020840d8140002c10240c00022014400c1102013406807540140392402e01d0148022643e160315000d05540c80540d040d4050981c0443d407070758401c410745026842c0d0316030900540280041400050200ea40500f0104054201c11280015401d6240041c040b05036140c050100000b800e000342c1485800c2580f20303030f041144100a60f10340c2d42e018582404400410b8440710000d810146040f1010342002c000c2c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 124836393 1250 124835143 124835153
    0x103080a08070516060207240c030c030603020906210714100c0b0411030106050a080102090301140f0708040503041502102009090a091a041406190506040905070f03 72
    0x450380442d042c00c0151411600d007002d8020400d00f00c60003040f0b2a00050b1030800c000902140300302200d0402e060035001c00b03460850b1800f50038004a02d0000a1400042c203001901c02d00904c0203c9802070700300030080d2035180920243c000511458a9228a03400ca130705407041040000e41d0041c0713000080c4620602800c0c041240e64100179070144200b041001440010070680114240c109a008444104003420040428050595940116800300303030003d000580000c19002409041c10450081101c0000340940d01c0c40e21000b500d901d540d50340020000b9400c2c90240c200181c00034081c80450303007050390300c1091135004103001e1280700068114420405600b880c03030140b0540031000345589140510b40d424569018004e039020148a036000002080c407441c600c0c0e02c28004a500b00c482c0b490410207034004085088002d45044451103150005074036050700100784107000b480c80d10a40b41a0881850003100a0303c4041e0080750f00540d00e003407101c0080d0040141c24000d0140d0000d98081910718101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 124837643 1250 124836393 124836407
    0x507050f0a03020714030d052a030a03062405040b0a110610060816052b06030803040506010b04030f020f030114072102030c0f133206070c03020f03030904050103080a 73
    0x2480c2c0aa440b00e004040500c0d0000e00383e40b0b09c0f029072042e0043c1e00c105400d1844071060762400c41d0210703000c00a40310702c02d02c0d8150001415035801c04020188141c400605441c039181c5000348000280051200f440783c0410100108880a030506e000500043c107165614242441075808001d283c000540c2080155001001107174000c0c1090400c0c0c0c7e042103486006071083c406c0400b4800f03110074600022420000302030001344c0c11584660f0030424107441e403501e483e96602c10703213096030b0314442d02c400007401e03840394003c80b01602d90000030062302e01101d5090001c44100b500a841d455529103044103000080d030442648245030550f141500c40c9031251800300421a420303ea44030b02401081044851810300f001c841c480070184c0030081e92111018150034000c405500004020f010034084983c842d4046016505150280040851034450600c10403620303102d64903000f040507400880420161405a0080c0ca0108000d01a24036146d982c1e4002422240c0c240c1080721400350110712203a400d584001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 124838893 1250 124837643 124837679
    0x50109020a140c0a080d0608010e010e010615022509051509010f0303050910032a09090b01120b01030b0301021c150506041514070f05060f0112030507050f0a030207 72
    0x954203240500d0000f6564603003440040c05403880d079001810225850701c1d40c0c0210000d0000c00000c00c0201041c4070310b1400784c4407052246109609021000c20b01d20b02406040c1c0815400750000c0a03803c1d407000340c0200e2982641c4110308114140345002500c0004da0184611550641b08211a191040400c2002992040c0c11480c98849003600a000094204044072001481181c0c090410004101c08401420135604000c06019241c03050024944091040311402c00766a104d80040300d440c4c02c09035089406103101c00d4005014108050501e0b00030390300442c81c828061402113441a500c1c00483d09903409650070a000100c1c40461002c50000c51003024280c0c00e40c0d42c0b2440e042845c04001900c0c9004d41d024200920340d0707001c0b18440180c01808064074456a4440050b11031444e4100300e041c060380d072241070b9a680150b030000340c0e0110451882505a46c0c120100c0010165a03072030889594102280840f540e1207101c00b2541540b404022042403030740300e0390041c011182042030300070014529030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 124840143 1250 124838893 124838927
    0x20f0c1e0f03072411030a230402060d060b0f040305010f1404140109050a032001090302030a0e0105040302060310080d0315050907021903020105091605090103080a0c06050109020a 79
    0x20102a42101e010044500b880c0e001a00540c44200c59894505030480c1660125055481c0034072241138140a040514401c50140b0b4040200702c2d0a05203070051070010781030800f910403a034400900149010400360071050401d0000084180d119000304081d94003104003030010800100b010810010240120440603103101d10a000f4030a41c0d81b00c00d407400c1c0c40544010324804403c4c14042640000350320144180307070071904480020260f403d01610550070700010f05840b038600004c001001105016004003141e255008519101ca110343c219059820056054100981008000096a2900059402081080c05803d9410318145d00146002280707a81041850b0800e00700303070180761104120100b2500c0c1600c0601460740c5000c0102d0403c9007000c1c1c00820414030417540410f160b8150300083c40340c1c1005040f98a040007038080762107007281c94800c9540c06038002c00107200082404000c0d1a0395011814000b8045145588040644100360422560f46601140ea51001d42d80142100c281349109 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 124841393 1250 124840143 124840153
    0x30d0c0804030305070f0b04120806010e09010902030a0612060b040e0a080f09010306051c02010801060207030203100f0b03030c0d0e300c030d1d04020f1c020f0c1e 72
    0x1565400d109001d070b4030020701400800f084102c00c0c0300d1645803041d20568000c010060341d1502e413906005c3c1031244083d41c8001646100001d1595001c0c104031200c3e080c004081490503032030b2445042c080c0d80020304240c01141c0312a4005044d01203141c50387c550a200d5613010510b502da020070701003103650307070141e1503902e81c0f010005001245400c0c00f15071050f614801e5840d500e141c00c0340142c0281003070341e01c0141c108001c5148070721031000c10340c5200000f5100b41d8032210245d03aa1102281e0b00c2c50b56000c00b03941a0004843d0398608a03080d480742da0203030398062000c10310645050000b030454200345a100081d0708820601030285511030342d541c004840c11194014078601c00e00045008240340b00c400c1c4911044810301e502003e90030006d500313980350020115901d44c03602c110000d0561226902c0000203004e1035143c24074a2800d8002d6403080c42003004224100405410001e1203246241250300202d42d0801000c0000d4140e58014818111850000c2000b034000340100c2e05080d0203803d40e1750080d000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 124842643 1250 124841393 124841417
    0x60f07030c0c1b1203050d06060201020406170a0605032a0402072a052d100816050c0a0b010e0a0b0f0f010e060a020607080903070507030b0421020309030d 68
    0x3094059400c1a08160201d03441584100e2003e48080035401465407181c00c0b540a0080591280c000c0006010803070707050110540c1e0b910240d00782e019600845010502d480c4c411300c114070455032100d6201071700300c0001c1107444d51040848d042c1103124518000c002c01001c8418100d00710916014851030050741d085103441040e483d6900c1e02e0b007030800310381801345000c0c0546031541a0400400b014000040902051900c83e00480c8580540d42a0880392406a40c00d1404985001954011198081c2e114050345a0310580c0504140d15201401814083c040c06002c1c201705042007601c03c0b662040062107099414110940c0590740010800a001da042c501468525291a12039050082d81a1750001c4c91000d103100507580100c46005440c0c000740c0c04181c0161035907000980380d0046006403207200741f540700d00d541c4a4403071080890151095010044c204006860342c5002907200340505501d4148030b6425140d0280740f41c240c0d1079100182e00110b4000d9151809209407140704455003041820004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 124843893 1250 124842643 124842647
    0x110c01050909090102130f060314010b0405060c03040e0a0b090c0307140306030a06020c0106060e010c0506190f0c020105100501090e1603150303020a0606170c040b03010b0d0302060f07030c 83
    0x4201d1581d50301a040700408544108000d406503601010303c01940d01c030142e120000130600c4c1c01c0910641d00004d08092040036142c50103140c40c0e0681d544d405030145424240410f103c1a60301c04c400d42442444208400120503000c0160140100c0c00f64501084140035141001200c18024240001d03c0508006001544e500102002400700c100c04441d612540c804d00043e0a003151100060005030002408000d50030041d0310003000e407401c0e40c450000c0c04244400443e00c00d045074000500641c0002d01251005582003045102801044004610030407600084d8080e1501c0451220150b911882440150040c00019030003030300c02860f11280b418641084402c104501901620b25012030b0924042c1e1b00d8400d400c21402c00301c4c4070448201007507491400958510300710100307482e81441c2010118095101801100d212440c140c000c2030807140c000b003040002c00d58801456410342d609c000741611a280d0128000000e4029001752407540f814244030490140024a03060030585844200300d0519 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 124845143 1250 124843893 124843897
    0x20f070b180a180b010e1c060f02070c120f0204110909010e060a06140c060412020f0c0a03060b010c0b07090509090c030d05032a030411010207030510090501020702060a0c0201110c0105 81
    0x116103e440410201c030b42e80b00595155481c000240d030030503a0881100c845000401d50124014442c86040005040c096226400c0307005d1b405008100710a5000c0400c8502d0101009201d80d80c020f002c802000308030781d40080c0c102d07010801624a484030124202400d460300b80a0716004200340c1d5000d529510301308001584101090040c0810300140600210080450700f0070f42c0d202000c14800c42e8414100340c103184405203003192208006205081e000c40c03144501150042c100b850207030000c0700050941c1c1d69a000303440c4401d891410490031101000105140100ca64000c17011519080f021905201c244030351004010250002c5503c071100c0c0301490f4500103980020502503103002074682d00c40c1c214501200079104070071034004c050900541c14184466000b036000c2e501c900507101e40b41c0c100a00590b01d0b0011440007504076001213401c0036407292660090f0726003506c600001483c3c07004944c0041c2c03682c3c000580840000713169400410841d46c000a61786d50741d10704980141480307016072000030028 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 124846393 1250 124845143 124845179
    0x1006030b0109020a050403020d0503030108060c0918190c050c0c01090503070308030c0c010509060117010504170a09050301050f0414030f03041209120f0b07050405060d0903020f070b180a 82
    0x603a43c001a15811148100103960155600401280c03003040c1340c0c2030481d9a03409c28080e50362140906000b0602e50600714044481441003e424130000c440016507049c50048000d00e17003a141c0000c0007000007824204d20500e02e000340c86232226034031100003e03100d52426801340349403414001d0b0300c8414451650005000d9080320342c4a60400c0d642e42c1c0f0442480c00340c1c003441b01401012360030541401004100410a81d0590f01c21841c400320341000705020b41e003601e8003079070082d01c0d481040350f0141e0412404002014581c00714100401c8540c1e80d07201003801c441085130707298031028001041c0001c000b405410066200700c02d9000318245481c48000c10054880075000505110494400d42202d07401003200800074030f0b190500c820504600d09041042c1c640c0c84030304407042100c1c000055980b41c02401945d00b92070015140341d013401450241c2d40c0003401030b0441039040d841502e04070742e1003035010442c1401401c496451591a000b039120001e09000301d14105510540f203400d0305109410120300c1c0100700b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 124847643 1250 124846393 124846409
    0x5070e06010c0804080105010518061f0e10030b040e0a030f030c0e18090f0d1b02060706020a020703060b030c060334030c02071703120903121003051006030b01 70
    0x503269600140c4405102c0d060003441c12402150004c0d81c2001903100d0b43c1250b1b800c0e207800500c01044a004c604100080300c4c01e51348045030b02c940c11700340404039003810701d030150714204100714800c038400060f50381810014400c000382c0c8aa56180031030903d402189c07070100c0500028a8490010358003d890802c06040000426030b07035085d2000c085109000c007a00c2208007924014a040800c41d90b40c00842040f43c1281441c0300380c2010092801001078008413002c059591400000f0a20b000f041c00007480f641c080e80e00010920450011811074070003072202401070340080c040f80d803652411406444030143c81c64440c0d006801c05000750384030181140d0b0301403036100c4509050b0841031700181c0e00d80c4250304003811201070a20302d1110b0980562002a0300307086502102c4040c0d40c0d902d810ba500c3c100f41220740d07400340c00601c800d003a0150b0820303500750082e1010b02940d0924402c07050400200e9030485a0310550074111100b002030010500c81d00301c4c07401000c02d05000442c155140c1500940e018802c403e0f07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 124848893 1250 124847643 124847669
    0x2113020f0a030f2006040f1409090607030b060d02031302010206010f03050c220f1508060105030703230d08070906031404030f03020c03040f050406060c030c02040f0b060a030501080c030a0507 84
    0x6a030404152048000000c01010191591344803c0402c403111341d1f5000d0785000311008107410000303103024420b643c4914900340041106585801f0120060b240410140b90001c0d01400030503188103190000d18490074a14000d6a2440c0341800021302c0c04506a0241e616a0b80140c01840496004200c0c4103441070291041403500b64405c1b4001c00424509051044180c030740300007000e400c4099041003200c00110100341c51415100c12846031941000e101d410340c550301214080001030a0200c42034000f0f81011220f2083c5805901014205a40b82000400243d06d030401c10407010f802c51100d8010f03003407a242c2000f81001e4400742501c9c0c10406130014080c131038a20408103089200e501241c6200400009903034907541d03149158800c84809014140c420750421401040035841b409403101804d4140e034a60f0844802030b001c0c0001008000a542045a250311441c03095884400082061294940e000030300796140c00f004a0604007441314440c480e41100706e00d840031900c0010084151818024151 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 124850143 1250 124848893 124848923
    0x6061c060b0d02060304030806030606100225050307030501020319090308060d140f06040606120b0a1a090c0a0207091506031a03010501080304382113020f0a030f 71
    0x240101c0c148202c02940841c00004100070907501100160080e10b080e8115030081d140c1c0e208003d80c101080e40e404d801a400200d4482c41111026121483d011310564447d00b10358917900440d00380b9070325030020358180e9000024007950030003d800c20120720605640c104602c80c15950700406040e0007419075889000c4000e144024000c640003190b0098078001c00300e544200181006948410f0f003100c0036581d140c40d00c00002031404015070039494240d4003842401c40741d0303030380305070b42e00280070b5911007a2200c1c1d40804400c019445080c0f45c0ea002e000107a035400e840d030080902c002d240800540140d100a0700f002c031800f042004a00c0b45c0300079a035840c00c006c103030b012410710340d001100f034401c644076815800c0200014071450040014816580030b1000400c4200d9500711002100c9103030301c1190b40e0b151242c0040700b84002028003a0106200d80c4d80e9083c1007504483c14801051000d4a8020f192481e0501c607204502c0e16400c0c2c00741c540c9040e505001041e02d1601e4140b40e00351518000303031140b40040001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 124851393 1250 124850143 124850149
    0x50d02060f0a11060108010e060c040e0f0903090306010605070b24040e1c0905030706030c02070b0a121a10030509060c0918130308010506090a05040b2106060306061c060b 75
    0xc3c40034007074901c08490310b80d039442005902902d00746a01000600404004c52154841c070742c00c840035074105051002d95519441c1e100b9180c900000c0c40b004c26404284001101c5075018000513000704642d945aa032030301441e00303202c0e10344440a02000954803001070b11460f8503000240004c0d410038100d40c0022003041c0c46008034209004000454203042914400003061a0054050300c184c92040d02207a10303058403800283d003102c8034080d5403401b690010108004003910309008100022441c42e1680c1240c4460103001c0c20f44041d20400c082009440c49800c00a0130702300c90400c1458100c0ca030070722441c2480107409882e54005403110304109800254849641c07190f031600700015410b61303040e111380d140001c181c0c43c14035800c01d411800180c9441c00094245802d9098a00c050700082c041d01c00580703080c00b0007000f000602000e0340c0040c05000346009030710f603141904469540c100041c1a1619021080606001d401030070325101b09003c400039050741c1c80056800c400144c1c401030004081c1590000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 124852643 1250 124851393 124851407
    0x140403060609060e0601050c07050f04020712030606030f092a03050d170703050408030f09010f020f1902070e0f0a020712020c0405060603072a0f080c07050d02060f0a 73
    0x68085030900d24005401003070383d40020200c9103070b520b11110903100c80004591a01c07460024560075408482d0900c44d510b030158107543c1da4000144010b280000329900d40710840b44190701d8002203a0303580710070007449401d400380e054401e460040801c107140d0141d40300369400c045140020200f0f569080b002c00c041002e41070b22009950482d0844400c070f00004030007001c1c48106a8408019482000800c5c2624003a004590040381d004d41c00c3ca003986d88401e810045040000c004603000e649620325000300f494248000c0c9180d5400016255841514501c841c00e205068540300b41154072841041000c0e190f43c0440355000045e242042045442d41505480640103914000d00040c4001c0141040e0503000940d15406001c00e56082c0a103986242c1005075074081224843c01060300c5401600340f02c0240c042074034031045081d14420030015a41c81d4441c3c2035110314022140d01000003000082410100b02010042c0412120a20060b801d40d020a8050040704112000c007200841c40401c1c950241e20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 124853893 1250 124852643 124852649
    0xd0e0f030309030a11010912030209040b120a0501061a0405010513090606030506090f0103080306010521010306150b342a050303090907081f0305031308010207020906011404 76
    0x3103a8036814405012516540401140743c00f00701c03c814805007200e018020948107a0700907040c400f1444101c10290b000e540b0459a060303100c1e54071142040140e0703900d0010300341b01c04140c005041c05603280c9005800c403956508081c000f4441d80b50020204500f0344115410ba801c207182140d1141d00d0118444c12090b2242c204039a00750504030041072456166200c1845081e048401101a480e10000c09100310f40078040a0705d03012041000031400e5000c1d02c020420080c2010880c0312240c0c40c4060b8040c4280280c00441d0001c1d1940e0403101c2e2034410380d604002a0144510040c84c190444800e2440702e118000501c5907064540142d40707001311240405200950451060301c81d04c6081056100f818044981002c00c1030310041d001700d000c0c2000015180ca004014040036402e0f1a042c03c10b8800c2040103011010b4480c2c881c0056a076603600260500046210748002c640312100018102c45601040d048020203030710510910015070386221620b90046c1c02030070514481e000c0300e41c03c0c81851017a60 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 124855143 1250 124853893 124853923
    0x220c030e0c060f0c062d070905150d020f0310050306100e180102070c0e0a02160f0204091205070611160b1504090803061810030b091005040f150606050d0e 68
    0x81041181800035846e0700705524452500342c030b182d030608014001d090007aa6180c3c0007645104080c4106d080068013046081440020303142031814a61040d020303607003c13103000c0b02c0c040e00100a00549001141512014150480c0942480d1600200d1705035100840c4c400c5400103030303070b00020601d8040307150104001298800c00a665030181410514143d00441c45144941c107603810015040105078030969903140542818058a04d0300d54442800e0304800a44c1030340c1c0295902100800101d041c4904d40030700d18143c03207850725402d035401e0280454601c00c0600140d88420064440d541509034a04103001e80c0c0100310b1111901c40d24013003454480f0030300d4025042417500901409020109014520071013007207841c084d200e154070445000152040e00c00700a1015500011300010300c10704407440e4054000c0089401581051200300151101641d066036090881c2002805000800c01884001140d5880c2444010700e071400c02041440f52024916102d0b50302d01d46843d418a09000d4a091440d1700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 124856393 1250 124855143 124855153
    0x50a090b010608060909010203070c0807050c180f0f060f1003060e0702030d060f060507020d05190c0501030506041b1107080303040c081018110f220c030e0c060f0c 72
    0x140b1809020300206803403c80c0700e50054400140000c20500803240710300b1040c0c2d90000354074480e0365124040d4212a0046645021301c400417495511004805052003864030718001c1a4117052100d94416640074210b45071030720031902000000e8461040340f1784000300030347d81000c4211382140d00310000c117500e801840703a001d1803405006203e90f001024160403500c00c00204a030302c0d40d480d0a150030244500c00c03034001c40d105002c114094a071000400030700360302075020b8982c1d10b01c40100c19107102d42c80000448169452000078485541d061248550050090310100940860181070000c040000e00c41c0c2000c1045100c85220850803c1c0000d1000f401e0010031251a07080030324000b90780921701c0c01221046c2c400c4c0025140c410751385015200700b05c1c0384810802e0086065449210000c4082100142c1004030340400500d2342c0c40c1c034141103080303814440c0d001d000759510340c3c010429543c104c0007d50070141807201001044201103400da142c01002c8410701c0c1e0701c040010501c0810300540480c1d030114001c0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 124857643 1250 124856393 124856399
    0x15010306050a06080a0f080a090b0c0d1101090b0402100201290f2707050c0a0b0f101406070219060f020c04060303120902061903150902120a050a090b01 67
    0x160070041c000d00082c0802e100e0562102805030b900c1e035012801170550602142c80354003180509005081c1c9440034035102c1101c42d100c44154030f641e481640f901106900c021804201903520078501d00408a007080240200303981620f0780800f6882c0a003000e44110540509001e4180c000d5000e4006002490104030320035051414554980c082c030100341c0d0141190003c4048030f0329020858510740b2040701503c8000303800c103041a003a5110014400d0080c8481081001d40b05c00040001c00156441100c0e501c0c40d40c9000c4404000c003c1e001340103a0303070700c8041800500009079800074100c02040180c03440e5032100813600000d07004d840005240100c1c1102c6402c0030680da80d100311705d02244c1c401c903022a400400c0040510040350345912001d07000803405001d8100d08662508801c00c81e600040c801c0381480070100710403000400d0300e04000042951145007010f02e85000d44920010f0000301c00450515640003a8003e40050007400300c54183e0795980064903401c440c2d844605010740084074252950f031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 124858893 1250 124857643 124857653
    0x903070f030c06020c031b0d0b040b04110114070201080c0d0207150506090f0103060b0f19050103050a022506020c0d050702191a1b1b1201050603030a050c150103 71
    0x38a0100b524401c02e10007002c14003070700005421a150f28050010110100140c20008040982e01040b991025180c540300c030120700003d10031400740d405116522041e04007850100700c1280500070340d0f03040c0722108541400a120800648820b590207003401c284c15030318032451049600c1040381d0000c41c3c500c00b00d000d90900442c05045030350249044c030100039a4075860204207036160119905500e03081c0480050000440780c1e0891011103001920408450030f00000140d6505c0c5a81105224111001400c2025603454050f07190030440070703c0210f1800a500c000e01c003401413940d144c000c0e5441c2243c138140801c481030b412910200038400079100c2122100000520560110358142e01c0351400030684102845918802d108480d0500c514005a80c580c0c0c4a60b415504803a101d29114112110034800f030140038000c0707003a00107600310710304002483d6008004c04102c88102c1c0300001da14000c03c2000540313000007221211105814616180c254055001d880c021030b400980d88002005400001000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 124860143 1250 124858893 124858919
    0xe130b0a031410020306060d020c100c1e080103020d17040308130e0a1406011d06030f220c060e0a0305150402041d06010513060323061501020d110102090307 69
    0x30084000340c416003554030041c0004d0b40801d0b200390707a01010400010803140f00983c01441c4440581081c0c500c80c0c00c440001c00d040b24603503614100440c90030360a03411060540700e01083c8640150400b0181541160003180f8001101c00008101103802d4040741d44030044141560010340d4071240843d41e40c404000c4100d00c111061040364500c8803800082107180d01c46016060751701542c4c500b44c00d465070315040110ba8400d16216510144942243c540da801e4a82c10021481052120001105810201c071005150070f0004850005080d814a001000a90007160b0703100700c40541c0ba00e10140e00e084000038110040d5940000c2944c0700d00003121900e01c4450800034407581c000c40e410018042001e81881c0315aa19000d1442e694101000500031460492090141610220400190240c60350b03100c1044440081116a1540d040c1c00c0c07140062404000c440d034440410f1950003000d20140001030340d1004404003030001d0016100c074508680c00c095043c0c0300700c260010308aa0020350b03507191740c041203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 124861393 1250 124860143 124860173
    0x30a0503060f12121c0603020f010305040c0909141b060316091203180807050604050103050a091704080d0e010e01050318010f02040602010e010e0304232706010905010e130b0a03 78
    0x114030301174040300c0b020450312070903080300e802406c0c100b01e001c9028011401800018400c4800c030381c0070f0102191840d024441c600040d031007500961f01c1c0314030b0541628030303011a07200200f90007400050203c0007a12014107894020107058415036410b0b0401d44c05071880b421a8010400d4948070507601030074103510000304010b004804003488002500d030300c1580c2e240d00e8a4044c0d20780040381000100510b51007948031542c0100c0c6910001130440c4603903112602c03156000000741088a0101d010700c044082800908920f01d05810700e014009007420019202203052444c3c1d505200300407000036800000c144244440c44104c4d4000c2003075200c0748540030000d4200b4002c01c00151710748010ba00800c1014428194461080ba00860410345044d403035042244508030368003281809000381503415207c0049064a04144101440400b5416541c4001e2a640141007604103e020b910820035030340c110001e851802010382c0d80001c043d00201985018007d682e1a01d0342020b100c030000400d20003a581d2000311 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 124862643 1250 124861393 124861417
    0x60903080f0603030406050903031303030c0b1f050607050102190906090e0925081605011b02130506060912030c010509030307080105010c0c1d09060603030a0503060f1212 75
    0xe4691000390910703041c0071039109426600801040c0005070054014101200340202100c5c41c000d0a98102d1b003200c0c6446d401140032600c50f41e49503041100110b04903a2001682c050b0711644980c214004200e41150710400c1d004100000b0a10306000081d01110707507114040440c042c14501010300103001152500c10308000509a02d070225513002d220740200e00070300f0003c1c0201030703801d10751402c984094417810b651280d4213244100051400404c1c84400d0b00c001196000c803000c240b800300090000e481e881800c0007100404645140140d440e0007103408088148140020300e9911040411498031036100755070f07400120341a110501d10b40c00001410a10181c0700248074170780b0750043d110765034081640c0800c08224514014800c0354865554980c900740070b04000724030550b0340e202031801c0c0c0d00d02220800811280200304070544200300724054126105400941ca4039000b561300901901016201c0c2d8803800254540300b0003903a0700b5480240140300c520559181990840c00080036034020712100403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 124863893 1250 124862643 124862657
    0x51c03030c030c08041e020d06020c0706050c0d0c08040504020f070210080106020d050c03040b0c0c040e07080304030813050a06020a120e0f010c051f02070302010e010605060403080c0a0f060903 85
    0x2406034030a0007100100c084948890016803034a55920382c04140745906d0303042440100642d040980d44d0003041c010500e0040e90f0060703996001044481c146800d9800240610808008422103840c00003000e9051028500e42504001c0d9185480c0381184656406a035000d030020403035020b60000c610042c549640b00300ca42c9044042c2c404000d0b076021800b44103400140c1c00510007150700c240184010b1071603400a030160f910f41600d4103180c0c21160440b0720046030b20f80c4501401c0c103150500788200ca1a091044009000c03142c038007101140e603445180002440b040c40842c4489176004030400c1f02c0050030340188201038681d1590b40007513035031003000c07010394040f4072514a2070301b0540210114150580041d29038190368500600560740e8525032740d0211580d2103013180c9840c0318a00403801441d00b00e0308410269450341389003402420b450719141d0001c19640742c1076040089644800440d8122a4005540da4403400d008a085051010362040036200c400250112020002150b2146040d00c0c400d4940e80d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 124865143 1250 124863893 124863911
    0xd180c0b1201092a020a0203011a10140301140307030b070201050403140705030405150d06060e030f060f0103030c03050f0414090c03060102060f09010905030c0d1b08040501050310051c0303 83
    0x1040d910810218569620f01c0c9103168146540c0207210715000307a060044500f0588030751f011900b160344005848a010740c0300c4245426074904501104500d40281c602199030501600042c1c0461006216005d40410890014841601c2c00c3c801d080041d41c003e220003080e45000b44019002e0002241c00b100081c20101142c1040103080d0186d600560700100118100360400c0c041c404d0b8916003d400300e49a1006101240d200c088601681c0041c2142d6903409038441c0048040c1860600c040004020b5034101c5001c02050002c0030700321604481d01441c0c0140d8686003800c4c00d40b00f92085502802074034000007404903961040c0501e40910326025124103c20781d580e200e1031480307800280d480a00580105020503000030004031500e070070890005c00014502070980c4c40350716580c000b8850710303103035007101c155500f10540142c1441c0c0041030414070400890340c00e55822032244214000c9a06110f0302002281200c1013045010b405001c2c080c0c09040620703901c150019000707840c0360045002a04000c448 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 124866393 1250 124865143 124865159
    0x60702071410050403140706020105090d02060c030a020408060f091b0310050405070b0a080406140402010f050a0e060a030902041a01090b070602070503070f06140403050d180c0b1201 80
    0x121085a805600050341d040300d180030080b90100c0c6001280c204031040c4000310120b2800e050508070030200308004c1c1010b6107400300280c04d5039170040c80d0540a0f000301b140040802e03004611785070f1000f4116602941e84d43c8040c500e0000b4025500000014403800c01000011840c50318a64016015001194642200b60746031500191080081b503806400c1032200b001c1404564002c41c1d080ba118006440d10030b61180712540313003500005e440a00042504003403000b8000b0394490f80c5200a01d6007055000e910300307600040c028040c034040315410440001a06110640b060440c076543e984014940d40d40d41c80c01800040141c2903c0381c003607206520740882d00d6035110301d81d1242008078234103071a035603901c5103020a41c0c01d079900240701c207036010b80d000c120150020314140010207840e845488071020341009818201f080711403611806602d48501c0c82844040b0781c1183c2500c40c188000c9001088050141d205516151450240184400ca034008c010804080000241000b050b101d8095803183c0ea851101c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 124867643 1250 124866393 124866403
    0x9030f02060a111605070b0d021305190b03130606060f0215090c060c0703021009030506010f050607110d050601030605190b1f0c0b0901060e01121104053402060702 72
    0x100403e00810040200803003d0f40e00e003000ca982c001e40607140b103955a40044e0f80c00f0b0f404000803404150703000030b481881d4000c00b01c01c0d5000e0700301921081443d50410460304c62140c424041c07100180d0002c00020300041c80707260700b10b01455000a0900075241e4441002e802078908a000d80b001d801084c403840b40280c510380714644550140001020f40708114030501900da03000e0700c0145050b004800d00400942c442c000d00c1003007201c0315652542203600c0c5003042801d00d0410780001e006014040410030040d91800b0598001c180c000030520100d40c0f141700001d02028102600034002d0103400000001d00009500692080c5100742202e0740700080c21581c94201d920b000185a4011905642c004620115020400002110b810301e06040c990341e4444407000340c8111080040d0369111001440107046100d44680140080e00407101070410b256104403a402c01c103980e2502695071400010340c8400d4841c3c8103418110354485494410001c41020000400100b100101500c0b0703100c0452140b40c0300141c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 124868893 1250 124867643 124867661
    0x5030a1407081801020408030f0403120801060215061809010b090a060302060d090519080a0905040c050d0c03060b070309030227190207060204060302120105041b2109030f02060a 78
    0x2d100b40d0a503035459428411001c0c1400103424565007400046490101000103000101c0300103130040d196841c502e07084902c1c2d003d0140343e40400c4402801080007540011f59440d024140c0030f2060b00e29a501c20124050b00305000b140a0750107016002d00804540c103501004052205640190880c0d0f142241031065503400e00c0000c1d005101008251100643c0f503001d1440e0034880c030240d41505500300030a8010745031000d4140c27960032001507012040c03a00420240300a05003034609000003803000c10054042e0265031460314255480c6c40142180e540310781c1c02500504a0520b01a498020f1070a008120010f507020482c0117540007000144a400d5486001c1c41c0002041140c0200d0317a40e401422801010801c000070004d81c09016240008026002500c05040540c3e801a11816422400c100a072410f0380aa070056150035030002d0020300110340f9119412035070130504d2100518030000c04401d82e161054680320b41c5403d18041c02c0540c0701f4110300c3d100c04651708407810303034555200900403290843c2d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 124870143 1250 124868893 124868897
    0x2032b120b100c0212011d060901180305090a0905070c0204060503010e0307080d060e0a1e11090f010e1302070c08010b010e01110f0604140d11060604110d060605030a1407 75
    0x41030400c2c1d201c0c80303030300004081c510141045654026241c945801d465460b48980c840d1f882120b54281608010464968031508150007030000451048808815a200f40c1000d002c01600084d08445922101d072440020f00f000c9204105d2480e184000038000f00b01d1660880c400c40c14000d0020720b61a050113500b482d56a11300c00343d8074090580d039424900c1e500140b002003689444420009098a01d0908148101031080f400300301321784034842c2c070342c54003486a0a100081c0d146c81c1b0381d1034030b00d007440059507040102919001c40c500750f0750300103a07101c15901c00299848a20155042c0d80d2040c56006030518521801c0f104003020b850340d0031b182c2030f10b04041d40e10707000032000000c4240c150f1003000400310742c40100040c1c2e0f008100f941032850825204072401c1d6500d03401c88000c4418003004202d11401110585851003841c0c82d040e404031740303030680600514803032500c1d0001784081e810084200d568800404404004a1f561b90102030f0294204483c00100036180c428404480380b09110310034801c501d42d07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 124871393 1250 124870143 124870159
    0x6030506100c0c0506091809010f140f0705030702011d101503031205040c0504050f060a061103030f1b120a05131a071b21020d021902032b120b 63
    0x12045c0852900800035039a402042c100e030014070600d0a800d1036000e015000004170700410050350b49010f507141c00022080d4001e0050400c0b05440e444601260441405e11300302c3d55035150020128007401012070300b42c2180d240108a1030214200250b007107021039861f1424070804083d000c1411540c00184409030104c0e0000240307400d900c419611217039000d403145080b040746075114400708003159012100c25411203400e02c1400090b180c0104404000c0a0501d0708403811000c4039905504c074000a0f04a03165504244003180100740c22150001420401501658171059282e2122540c107030160703900a915803500c00072846441e481d0080582c415007013600c5001006000400c03606c071601c0101001d0811115908000c8612220440c10b28040d000c0c0f95043d41ca55950640030101c030003080c3d005000e65000890320f0720b10725000310384a2380c0c1480301051707140341c40702d0f070b001090034000d40c81d54000001070701c511200046400c80d5400700b60110390b6600c0c280034800c105d24034002c641e180c3c810241d02c403903a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 124872643 1250 124871393 124871399
    0xf0324070e010c240908070c050307050f1201090f05060a0c0504030c05010507030e0a080a02011b0f0f0f021504090507020a03050f090103090b090a032a0b0a02070b0106030506100c0c 80
    0x800b41c0680c804c01000d1400300040c80c0c40c43d81c440881c1c80962048400d008009803d00030300a0514004010701000c0b00600542894800041d200ca188038070f40902444405a840035100020b40c01003200c981c1160a441c0350f11118030300681c07950012242411000d00c3d000d14200440c0c0700d00b0541e004d40703501425000781d4600305001501c054202c000220204141d4881e01903c0391207a2580400924200c00184101c10075031001500d00300c25210074801041040006c0030109103030304028a03403180c0081030070742044500c0c107000300e45455424019402c4182d105008000b01d00d03800040084507035a6404100503102c0340c4041b078603103616410140020724280042d00c40580c0c0e050041010900c14103001840140b2603441110280701104c2c40c12540d00518011414182c104101c0b11035440c528a00300c03e00710344035001050b07440c080700010306108007840c0000c03c0b40c1000d60450b1203881d0080c20300c0c4902c1d81c0d40d29009001c0c0504444041c02090300b5100134545501400000707114580c081b84003240241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 124873893 1250 124872643 124872653
    0x80403020d051c0c05180301020f0301090b01021207030203040510020303060a0306180204180201030501290f0c060a0c02070501030207050c040c020712060b0118050f09060f0324070e010c 82
    0x40701d00502614040240b1800c3c1800c4a0b101c2c601203038185484190b11100340c0401c14607503052800b40e142c060303401004240d40012040c4201c0381910800840041c0d492001c00040b4609064400301c0d005041e000075080051640000141c000c440088480401d140004202261030740820f940c029007050390075406000140580d045140804050034101d0b0f0648500e8000a007550200d00a040113040d210742d1075070640d41c2c580035560241c405660041a8041310300c402821103240c6481c4d0480c074060100f01490203401d00030031a107500e04031a0884410342049204400207100110040e00035200d6807038000b503554082d00a50714100d0b080b04c050000c00702d402c41031101800c2410203c0003180120440443c5c0640c0d001040c04015000b14000280002441d00240c07038081c40040300c1c0036554184a0402c403175901c001c40b01d0a4a40284d42c0200d0070307222070300464207502c55210510b9160003820b4031a0703205500b0b810ba52140d51407081d0f4580454072000300c10b54840f01202c601d580091200700201e00451 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 124875143 1250 124873893 124873897
    0x2010804030e060706020301080606060301030c0b0913020c010b0a0806072a0807030f12091502070c08030301180b0a030201020c150c070b04140102010e0d030b0d06050f0f07080403020d05 82
    0x1600900b030007164501200d0026120303a1041c0011204968084014080e144081084541c00306003650a1351555046896406901c02c152003401051900082d610f416920f5a810b2a84414a421419910303600441c519501900c08102d02a000d480040000902044000360f014010740881e200ca03090301c0c00804600026a4041d840c011082181800d18000211101c0040400a000c0d40d2244640c0c60001002440c5080f40c1e004149224203101e00800030412000c19160806404030b0016582c032210318054405401a91013800a030102000005600c04680001040c1d0300f031402c0c0401140d010b50b02002040c2016000181c01a03000060100260034014801c1206220100400d8100308940c5556072514019400c4042d600901140810400d4001006041050004d000031320024510180c4a5525025240301d00c08042d12001301c00915147d600c031060700c4c207410180130f028034601041220a58081500e480841c0d412034800121000d07c10800780d0b02440c3d260b400741c82c803810510310481d596 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 124876393 1250 124875143 124875151
    0x8012103020f030a0c1a0405061801090213051902040b030105060702031612020a0e1519030f08030601080906040305070201050304080d0504111002031606231003050c0f0d020108 78
    0x26100381011104500380030030141445003055a9603401400d01c51a101201e46c0c0324600c038242c490054014000000c1022494590168403120001d5010440d040e40f10b0250001e2100603400c05c940a0409085101e00d40010340f0031565000d001302441303c0300310b04800300d00c20780c8141c075000c1d0001e10051100c0c3c034200006084640c0001c00326903140c014640120906502d541c032110840e80c030000c1c10002c44c10a8103070078005000340780e481d00da20b19068a241c2c0c0b2107038032050854440c500c1510714101490f4002844400340d60000c0c0f44450b0f2600500d0003e0f2294000e8079505d000ca007800000a05034580010602e228661654519051000690054030250806002290030500c1030000003041e09440c85918802c0c4c3c00303120303000011414482400031107082000c050085400030403900a6580680400c0c0e0b020350b910000001c0d4134003400340c0b0802d810351100d0840104070406810720880401702042101620701034410f89076060b06603410032036013050321301f00b0355040000c4046100166018801c5141c0c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 124877643 1250 124876393 124876397
    0x5010605060301120c050103020a050304060c050d0606021006090e0a0b07211d011a0906060c1c0201060f060c110a0b04061809090203032208030d0e010b0108012103 72
    0x11103484000050040d0000d8000408001c004000c3c00d0030b1000d6606000001e02082c24110329210082500901c24071000380060310381501c4ad0608502d00b441030742180c0b44012108420030106455000003134580c1e82003440e91180301c3c1840d03000b00740000304c1c4c41a4807029032020010324240407507682320f089000d0002d10714828440356030781c0f491081001400e254442080e4034400034074490320031540404c0004401140d0750390380c9001c50700d809040001500e903408003800c40b00d1526658030040042c07218030516001c200c079030003404410f0060398800c004212080c1426002480f009880300001041c00c0200d220340b80000d9545e581d9040402d58500386110214005001c505c0035a8440381d9a40071070740702d5403104000a10711010915141d50300200c140280c0f4040c04d050020494a4002a95038020844a001c140105898036811581142c451100030840141038940302c2d14400880e80c020861a50f54a21a500f400340c4c2d0030182d0f11404225060b138a000301003d01e030906019012441c00c41c61241101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 124878893 1250 124877643 124877651
    0x70306051e19110a08070f0305150f150a02010504020907030c080f040807050a050c18040203070b09011b031206060516110d08070c080c030706050f0a0e120a03020f030a0c06090501 79
    0x1401182c0f04020001d00d591500c5140b12800d00799401488064004100e41c101840d1005000d0400101c206100c15803a04071200303048100107500050242c03a50350072104000300009510402290190042c47c8154002c58584180e66260001a029581030303807000000203101c1d00c00035881d1480c0c1750b18513030010f0040c1070040c1003140e107641d00f524110850106a980740c1c440e504182c403d107441c880301400c0344106420002d040c2040e5010036615806406801015100404d2804d516440740c502c03549000c645824001c2c10310301a040140c0300c1c2e100541c1410b00503040c0a80403503410301882c12114020700381616034030168080d840351141c5010410304a98041800600d110206d0042000ba04555004000309032445291400032407900e420b0b9a241750190b00f06904c100a519000015603a0209411240c203542c0d903409281102c10b0984000015401441340039000d00704000010503c1c141032090b0212a0504244100075980340280400480082c04000e400c0001900c1d6401c0070012030300c6003001003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 124880143 1250 124878893 124878911
    0x30f0a15050d060b1903050705040b0f03030a09052b030c03180905060a050405040b0117240405161401030e030405030616080601050a050904021c0e070306051e19 71
    0x1441c00c056180b000c0d01d22a444081510303041c0b07041c454040758401007450000c3d8052a690f16a40c0300e189078401c0c01c3c0f00310b0350388023002100d49a0a07181100e0101c01030507265540c0211401520340581405001e000703601c5505007450b1035104082403a00030b003660044019480300d0799412142c014078070008070f04001000e03200078068042d440c0c0800c003808107154040f440d07181c60b805010782401241e0181d481a41044103010104103d01301e05810354400380218480700384003605d19403500c00e0071000f1440d0182c40d410000e400a80240925008074400c9060350003000c1c100285040c1882ca41c05215a081d0612240010640c0207501c922042c2540b40150703030515540c2c000090502d403003152051405481e161582c0c4c01b055101c152543e0260b000d0907d6410305400c0701006116018110219008550000c0c0521642941d8600f1008100c2540020b0000c08114405d03151280d980e40b10440307155050001141c0c0b00345140002d40120703410529007055658400b01141c0f041d039080541420703180c0c1e641c007c1c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 124881393 1250 124880143 124880149
    0x60f190c12020f1002030f0c03181603030e0301090b13020112050c120a0c0503011211041d100203130308221230050703021c060f0803030f0a1505 64
    0x1c0c2405405034001d00196200c26001d00c0c1480c05002c3d1032000c86104100304280d000c140403040d0741001c00302c400c09803130b41d940c02500900c5940c0e5030b103080300d18400c1900018951200c0c011141c1568070031741d40e40c0c01061240d01451300783d075250b00000341501d0150001134062500c4400108000d401407402e445541540c0700405c0440d4400d40b002e21b4100f0b07000404201c09109000600e0300f0100c0c2020400c00300c001c40c40005d24901042c014040070080130089842840390700045165201b20041c010898040c0030031051002040b456010309450140320403a503522180c034400d8a2042881c0b07480c0d451605a55541100c0941c80108400b00f02800d0b01c800c00010101c034441c2070400d0b88900b01c000c0d03c41389485c074042e2030302c036084080500140d20704130080e2081100910312400407481442c04200303600d0304201038010b80076051400040f1190414066005003c5410220440e000c03842d520f01803d0300c40014903241e200c00ca4466194001d9080410049529540700800e02d03d0081182e0342c00d030f40c0b54800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 124882643 1250 124881393 124881413
    0x902041109010206071e05030a0f0212060f010c050703020607050304120b09010b0d03020d080a1107110a0e100308130905070201051f0812180a03031805060f190c 71
    0x14a154500000c54420074950301000016004221410580354420140d0045450b00030030304504420000044042200d04489410101107107501480c00d545440c0130044e10700e003100301210481c1c03044810181c9000315500801220750042e0300031b00a13040312415902803040e1a40811f0040f2950301c820000001c8040d0028901550140705058500b403d040c1415401d00b520069900c582c441c6405060f0320000a40010b040c180075030040c242103050740d03250300c242001805500060780000700c0004190b410845662400510404200d0b4982c0c5000e8585400e1440e102c0200c911100d402c41c0d0700c1e4240045503881c40644640c10140c8007901c40991229109403d6400a66280d00540c2d161014091a002d0b8103100e80401100c1407107140301070385864141c959807000054030f80041400014200030000190000410090303000d0561000d10303a0724a001804c0750340c80900060010920000410355260050468585142100132142061700102007000310680c880c3c0e840c1e06002104c03808200190020711 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 124883893 1250 124882643 124882661
    0xf120429010f05031207060509150705120c030705040522060f03060509060601020c0103020a1b030f11011a01110115030b070212120103030c031107030809040f0c091404090204 77
    0x24400c0e5240600d610988106608076501c20b0300001c021100e8000c1c04015508180d81044021560f61030b00c141e20750519102c2c03600d0042e070641480801055036048002001c03944000c842d6203461796500320b80f18103603000584000002074020041044a460131620104500c400a01040c04029080030404100d600e5544040c030b4a003c0803900304140010361250a0b0b0100d0000003501d030618001c0c00003074a80b035404146605141d800300729108010711030506000051864440c00c500d0f0a9a820050500324184010100143c41000c0800a03048180682500036151400007100000e4000065070b18480000d00014550b503202003400c0c07080c000e08841d40003540516081e04460904c0b0754000d080001020320040000710812030403010104c04400b1a0441e81c042c074284240c1d00385440c00301c60219005035160214422014003000b80320303403000140a0700c0001c4908002d0010034080a5080d64a40e40d074180c0812048001006038641c41103494a020b00018000140800542d0000782160002c03c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 124885143 1250 124883893 124883963
    0x203070e0612070e100504091104050c0403020306010e040209090715231912020f030408160206190305011d0f0a022502040c0302090a0603090302011107120e060f1204 73
    0x134140041c0a007040ea200c80940301c1543c0a0000303c860707845164103411248803130b500699907100003600c2e404010041c0e80185d980142a1b03140c0b569249030b9449844401c1e40d050388038800718008200c9072000000e440045410490380d402501132568825030b900b0700c480705128000200003030000301a541c860001c201d544074140c0c14018003207003150300400005440e4000c00760544100101000030421105030baa0081e4420b185a640d40150507842ca03001d1120075000303403c2a804118141120740d04051004810055902000b00c1e82e030b00ca44042d0800601008081500100070214542000c0011184d0707000d0400c41008d0b02c4c2100b02000750265407a103603060b01001500c8042c0b8421440c10323015078250304e03c1c640303002d506140c0c06500143c0c0342001c40c0709002c1490350703ca400ba800c140c000e400c10001000d8034001e0070380750ac10f503042c8810507051b511303119000100014207025203840c01c0003d4580b0214541000c0e0300306809817040c590020400380c02a20b2000f401f0100c000542d103100d41d4100518107407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 124886393 1250 124885143 124885169
    0x1202060703050c09010e0d0c030f0c080c0301140a020904060b041d06030105040305160302070513020d0506100813050c0312040e0106050a1403041a0708220203070e061207 75
    0x518024100c80b005400e009405208202c0751203a031381c0c040000520a002250b6580f02a10300d8903109070340b000142e02c014880aa00400c1c00207010444218000300d5065800340c448100c510f00800d0308070b0310401c580280c190328031400b013019400716502801c01e01c00041d0000424076196420f81c906078002d0b0340010044800e02c5040040001e00c2000c440d0030070415002409a800c00359005410f0340200c40c00c41c400142d1018054050502c204050350043c400030348407154261500c0d0b41c5030040c0d40b00040344401c050801b00403c200c0d04100111644038469642d50183c0341d11820702103004c410786403009440600c1041021441903800380700d20300f580020107a055030b41d24540700c2c0340380b61200142c1c0014280074041c84460100d40e001200c0c0746021681c25091503980d41e6501c4c001c200060000d0303a40f82400c6251080004498102c0403039401a5602007141e141040c0b461481d64908140150007074040e00401e41c108070103e101500300d0b4101200520703110190090542c0f01e46000120760261040c00c8032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 124887643 1250 124886393 124886401
    0xa080c03010e150408071a0405010605092422021b010c050a020726030d090c0f050f06030606070807062f0912010f0f02040f0e01031e02010c120206 65
    0x100b440354440d0840150090620f48020740d6194541c4500100040c1021800040c0b10b030800c42d80300b0580340c0e070180304405441c6a040604241d4001c2c406405144c1c010b160041c0802d600f01e160442441022115600c0419000340c1b8000740003512043c004540a139103401000311494a1042c006419800e00300e482007403217403807410071a5080d181a1002c410a101c020443d0040166000c2640e209654600552000e2124104200381c18145501e545000f540070100d00821480200d0b04100003a07401a0840d01c0d09544950070380c0d019131a1803003002c1d4402403000284100f07040c682c020396805140140020705228003038888014540c41254100ca000707985180154026600d150345c1b9a0554040c46801c50399000580b1701c56107481104180342c03048a4054458074695002d40205404a068090074840e8040040590b070103500140156100c01500740c1000c41d941e1940ca0420341206d400240700e02c011144840ea81a120b07010600036410040911079480225024581c40304141000360700401040c0380c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 124888893 1250 124887643 124887649
    0xf0903030509120702091f0315020c1605010e01080a1103090d120515091302330c03090d08070c06080f0a090c0513060e0c04060f0c080d0e03090a080c 66
    0x183c02d4524021000c00d101030b030003688890b140203510101c0040845840070103a10000d176034040680c0014544016546521555203284d0003910752414540129030598080d000c1250a03c441d03406140c0c00a568940580c00b80d61141810315009003501d0300004400c81500d03a041c8141c3d2080381c404403503502403407641c44076035801a107684841061a80801c03280c00e0051141e44e900c0c81045da15403003030840c000401d070008440c02c0200c82c540d500812002104408550b5103070b00110641c51003107500740000041004029a40495151245c1e5802840c903200e0101c04010000c016144c055030b990704144080d40002d0314540400d00640010744a190701d62401c80c0503922181c8008041c2c0c0c00d413909001080001aa05940d40003e503401211222203030481c0c82101030050000381d0004030313a00405424006090069002003040c1c03050b42c3d803050030101c1e2014003980d0110041c50010326828041051000d10384082c0e0003070010764401001c0d28600145540000c554002c02d400901c1d05030040b01104c0c255103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 124890143 1250 124888893 124888903
    0xb04080f100504170304030e030d031a010c0203030a032a02061504021905090102010e0106090603021002060708060f040b10170a0e1b0406050a0e0609010902090f010c03030f0903030509 81
    0xc09005052002d07140c980d40e6221400d1541070b004405010210220741014002d40142c4140072025084811304a0036803001400fa08a2100c04204940c80c0b110f01015941b0402c032400e01541c01900844c43c040002c0400c40050000140764610000030100003031003124502110081d0b14569401020a0305080c0008a032800c8201c4045200d184100b0210341c06840341d2844103241ca0290a11507101c150407001130340035103e4520300101e00c0d460120040b9103400e455001005481c0242c0c0c0300c08901c0325560059a0300c3c8410f80d08200403410280005019142c403000d441c90030710f0f02a00106210783c1c5040401c0708880c03078030055030125041c80242c423008034010703036040d5201c2d5030f10500b8841c450030900c030b0b00c0d00d80d685403500801101d150a0003030220b4071150880001000060410601c10b40e80d28600c0415000c2030391010701c03c114641c0000340ca45064000c0d0380e20319500518102003402100d0064a100a080b40220141902e464050314107501c1341c0b0442e024503000c0d40700442e003450308038030f168202 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 124891393 1250 124890143 124890163
    0x80105010605091e220e0d02030306030318031f3620090f0411010305010f0e040309081b030115080601050111030f0f0a11070b031306060b04080f 64
    0x2c0c01c3c048019a6540c50745515039802c5041c00000c42103081402107580d800101d2001c0350a90100c24031164200703019440010b003040c400090b40c0c46e03024103e00481e101c5c4410368129a05a10610001505c4035980d4000035105500070203c4481c14207580c1e4880484001c26201c1c04200d0b51480c15544059401010001d181104510501600a02e01c0d03c07046c0c1802c03c0c400034000c0fa401c68006103103c030001045031516200248a440c03d86810940ca03000c4200494040302c1022094010301c2c00f95000b40682030584805e8105040381c0da080c0441c415019200400a40402a554900280000081c4161425202040c41c1085e00340c0700c00041c5030a6980c84044c20b2004491520204841c82c0041000e90540d50241f9010745485201000389203540508882030125900008000d42652256030041c9807412480d16124907a402d03403440ca03038840f40b041c0300e20440e40d182080003401304502000403109040c0705200001d1003a46441c10350040d0741091b00602c503076902c0089c2c001c1c4036580c00c010305080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 124892643 1250 124891393 124891397
    0x8070903020a14120a052a03030405040504020612040b070e010c080a080702030f03090a0b0105030a02091503070e0c0a0306080d0c020402070303020415090905010501050c06040b06030f0d05040801050106 89
    0x201861075001c24440111842400030f6503404121080003990f030018121100441c80e000c5413960562803c105485444401c65100141c0b0208000c49000e611440040303401c80d0000c000c1c500300f03072a02d000e20000d401d0040040f030b441882044002c07911021100820f0059010b0008a01e41d403034201c00140c00048030148407814001095449030000d5010400c60300c13050560700d0701004644030060213034a903028410b90301c0d6012801008212000c0400200d11301e00901841c06003e2030390b41e81050544880740840c019400036581c00c0080e0741c04180548c4031801003c090308403034216039220b11f8007030300000c142c1d10b95003981070005410b0f0000e90305000c1d03600580740d1040908a9042c3d103030030251543c00100301c001e000355000314850701498081c0d8190f500410441800320420440341c135000b400440d003409401c41c22071a2000104040d4803a4081d101c1215200d0010503a82d1190b8680301e0305c6a400801165061107481144000124144040b1040202c5601d6160300c1c1d508048180c0e007520303016045041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 124893893 1250 124892643 124892657
    0x203011802060d0c0903120206090106050a03030e01141309060302041103101406120703090201030606021204051908010603080c071d0f07030e240f010b07120203090301050709060807 80
    0x141c0d44000031520203140f05100000d040d00000016a49100d40d40c0c03002e4801c481040100b0015078011420354407131071150307000300070141e210000c000c085070684c000540003d2100140c18007650060585200504d000c01025040030603801424101c500580c01079114103446900030021820540180d6548520242486040d89402c40402840042611603442401900c0918405139202d034070440d01d5680030122a1541c0d417601200107000f0304103409040780041d180503c0050306e10706c00b01d455010400000721180c9000d18200400203000e207102e041000d10183c1d03a00c0010f9522091040900451182040984030b0a002c07580a080c01c800b40e00101c10260300d04c03d2021082c500001d46a40f2001c000751000554456036800c4000f040b00e0420003d1900c00c15040d520309000d40c2c000b00006e01d121180c964040d60b01d9503280c144454080c031070040c06000612503070002035203220016516800c6803045074180800400000d094820039204240410a82c4a081c01110f6000511550002090401c80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 124895143 1250 124893893 124893941
    0x201050c030f06101205040609050f06010b0a0e0307080102180a14060f07050a02090405100f0b210f19060f0c1706010e150a031413020103020304080f1204020301 71
    0x200b481c8000800461184040000f503440d0325001d0b5560091001c1c50a00030022440c1c1494003100401080800356004e105042c0c1440340402c000540c10306860803088806e0401c50040320079511400c0109000d40d250003040741c0130030a40c409102509040c0d001040794071041d040303642841100d220a812410103103500511580c10341c2c446408855610b00c1c49651169107600f142081030034010340840081d4041d10040911092000002e050380020b001000c040010350519840320040380c1d0214480c540240300114244140a03450341c8191a103201c1c441030310380704141a400030341012b480d00c4040080c9020481c444080c0300071791080b1710303035164024020800d07140b103104090300d485c0070400790541d10b004100000c1c0c0e19074802d0312180000d0384e028103610600d82ca5080320103056046950030380000b03803400a010807031450042c4120300841c0d0100d0101e610030256001100613500040060343e2520f400c00124130311207010001400c1d21940348141c509142060300c1098291001092000d03542c8400302594 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 124896393 1250 124895143 124895161
    0x302060402010804030c120906110102090114030a1409030a020c06030f0609100f08061e07051c0212010b07170a05090d020411070510060806010f1401020703061b0201050c03 76
    0x1500150242000d0040b5139a42c58101c0d815040200010604000400031910154006001710305950b110380350000c418440c0d02406081b80a40c03a801740c00140380400260381160202c0046400c4600d501c004641742d490140700e0246505d054030800a59800080d032003e20f560b044c0101d0305050801c8400505d1800d00014010043c407000d41540c1c0301d041c46201068000c510030f030b0301c1d9005000ca00b61101c2c0095031080881d840b4141101d2032040b004545280380c0c3c0e90b19040c1560703845020302e51103907070512101c403461a400c654660f04d03116805908108002c070400f9032034030360780c000c1c0a01142d85540b40c4503031803c0712812003000910002248180904005c0a412800741c921905d010346507101c0c1c40016000050140c1400c119108440340700040070b00c1801000701b0400c555145071035003030142540c5e460280790341d05000d00ca42c501e0442e81043c14041d1082d41000c400e191481441281d10003038680d1592811110341e1003006410b58820380c2e1071441c194080c06070503804007560f0311407421480e10f8505 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 124897643 1250 124896393 124896403
    0x10090218061b071211011d03160603050919030813020d0c080f010c080601030c090f03110306090a020108180109021810060306180c02030720011e1d1203030916120302 73
    0x3203503050140f5000070700e50325100c0a03001f00c84040010b04445981442c401c803100f411035903019030b00000b4101000200704980005055000d860480e546107581d810301d4804448000c4050103004811422584100140c0e0303c8040e140c1206004030403144006240804a500c0c14002d081e0500040c3d040025004640d60000c203020b911100a0038080385046000d982142c0880c11a0003800409048a01c04070030b0006031114165032000031b50440d0081e0300d0f4144c6c80c03591903000d00d038024005000031002605000084600310700800140c000800c04030095400181401303406401d00220440d40e030108121281841c1c0d81e50000d040c0c0f03050801080741480c0000302c40302d00f210414001c0340d440320708003144684200126a5003e4026906415080304084031115204050340c0a40c0000c041600244013015002d02003030030f02007551100c1001d4010014121070404043c0100c550241c1050b89244540e4000d0000b140703c8c0202d00301400c040009880030183c80c1141c1d402c40b140c0003040d810000d00081d00042c1d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 124898893 1250 124897643 124897673
    0x2040e01060f180611030d0f020a0f0206010806011206090203061f05150f130b040303020307030f030b01081303020118051e0a030206070e0f040606030203040201080106030510090218061b0712 84
    0x1034410501781c0194401c6203180304180f07440f05041d00d04050840f00e1740d02c65001c2c105030040c80c0da91165408850400300d170749100038003034008540c0140b0010016041100c19000d0001c1c0b2030600464803909a40010b400c00c03500701da4110444228101e102c0360340f04080d0010000d008110f810070401619180b409280f8016451072415006000420b1900d844400c8031180041140030500d540c0c9540342d1038025260740200204801080c818036550313886d1030290142c001c001c43c041e59161002d50b41d1807000603142c8440b0741c00350295540c1e50090074490301100200c1d0b58581c0124001d0412004d9207003401215001a40d08142d9504561115400640e020603080d4000806140015100700802d00080c444040380f851070341d01c18070b080800142c198058015500c10b40c004d8852030401e0ba65110b09805603071040328541c074104080001031010f460560b0151244404159003084407040c5140812284d510995502d080024020044ca01030103007004414090900102c0a0950f581039a8441d07042c1d0140b51 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 124900143 1250 124898893 124898897
    0xf03070609060e06040f0512040b09040b040b04020a11070801060608061212030f16030c23070c030b010f06050901050909130605040b150105040b070206031902040e01060f1806 77
    0xc03814414080e0700c0d0007483c405550401603a800342884c1c40e110000f003006c040c04441031b0244d800380300780031000c0e041620200c40c082c42d4200e190249000c2080002d01d044013006612545c0e0b202d880840d5141c82c405803407151015104c210304c00c0211400784c0d14080243d480a070280e81040014030416503c628001d070060810303502200c58108040c2800e0034140d000048004803000407081180c0d00320502445406007030300311181c1c2007031080f480e403c4090b075428041c01d4000c55442c51403501d80801505ca052680b214561172242081241d554007085543e480d0700c00e65095207a400140807480382c400f5a030700240000d00f48a0700d003050140010700039025000241c2d106040756400503d00c0d249111142c41404c2d4084400c001c0d5103001c1c03402e91552a0291418a40c2892130801540e0a500980880c0e0948a40e481d02508020441d400c00c01194002052500140105200501c12145a00250010b0040d13441307a51807944c18034100a003100340001e0458200812040307291621001c101d070101c1503232018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 124901393 1250 124900143 124900151
    0x10b1906030b120105070203071208040c03021e031207020f220506042d06050303070f11010203091002010b0f040605060702150f0a020114060105040803030121060e03070c080f030706 80
    0x90001070403ca900c10001886500f4a0308100d0300380c2d40030000302190791044c002d004003240250780445c0c55031402c82b4010140c1e0708000007807000d4070b400c6004090700c001c01c81c001404541d05901280c1820303284542d460000d0313000700f40f0004500e070013844801c0d0114250b403030350480c8508803c80034050405c0500ca900c0155240041107803600c51b038000102e00c085ca40c030300c8403985400348400c0740020914014405007502c0d15801207018034000c02150001034101034041051900341c1c03207940400c47c0001100b81035220400440780705450389003841d0480a56034000084848044050214408884506510035403510200303000a594030025950384d6030301590151050b22038509550307a07600c680c2048a070581008185503041da6070540014002c601102038050007601da1400641c1c0d10301450080c800560002c0c030060001040c0802500c4003c8004140145503025036100c3d082100c52503c0d0148241d0400542001441583c0200c84d00404121004290900100e464103440340130386100100441e8807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 124902643 1250 124901393 124901411
    0x3040f020f06030408030a0506060a0210020c01091a0f0108030405011205070e04110c0c061201151b08040905180d050702010504081006030213090209040206090111010f0e010b190603 80
    0x140c281c8980d540328014103007a030b40c1d09041c10942c106030012268203010608080c009900c9050400955000c56500d400902440c01640743d2807002c1d4001c503042205e10341d82c450254010071407001c00740a42d41c03110082000a410401524a02e41300c0503003104009620800042251380d900100e501d0207403049000000300b5841d44a003c803640300c00c08070400c0d0300c00c1c02c0c14640e02072036046500600c400d49030720046503401a510070510169005880782c03103004940050042002e5010314003008814205454a44052840e41c0d00c1142c5401c1c405005450406001c00c05024403110351103160740051401644404115040e1545070f9558444c2580342c0805c0404120307402164062001d41d00a0880b82050751075000706000c0d41c5004046620040e44100f459220742214040b043c40386041e041d402174162103040d51203800b4050594803401c40d40381000340a15000d040369a0a1042e60b040c1c1650000128100319034040d802d0a560421030341a02c680311001c40148e920707409224413400c450282c100400d00c152 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 124903893 1250 124902643 124902649
    0x1e0402090a1b050a020c040911040203040f0f050102122211030717010527031206010c02030312060f0618040b060f0301060c1a0c310321020303070503040f02 69
    0x582c41d46014a8a5601c2401c20b261908480946410810b6030308980c15038a04c002040180c0b644207002514078101c80e0f13107903062801c281e0000d5901c01d01901110341030f11196582c400a01c00d00c0c003400c0d50a40d5010031344141d604802d1280503040010542d0318821781c4005400345c080c0b80c10840e0018840241c4021b1000d00391000d100f00001858450040d0528400040105000e060700321410001d5041c13103590360720030b00c07122031058030100d480d40011420002048080c20032604044c113114140404d44000d200113075801c10043c108055582c02d083c0b514180b900a1210305a000c0324028480d0105210f0140ca12042103002c0f034056404440c04176400307076442c0102d4120721960350b07641c07500d000010000c00d04542210003540d40510811000181e2040c05040b204001800d64060075800c004200100703480300b2080601e5505840f20304d000031074103580d52200100a1003640200e84104080a00d1070015441c440340c0380c41d030542c600203186140f03001c005c010098400104000c1c1a10801a0349405540b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 124905143 1250 124903893 124903901
    0x6110607031a03030d02030109150812090f0a0305010207020405010501081501032403030503101a030720030c010906050f09061b1309020301140f0306011814011d1e0402090a 76
    0x200b07001c0d0130380769503000700e07084038001e58802d0007015150741c1003118051440b01c40010341c4040326020405000f9051030301c40d1041d01c652140703144a03401048182e074032009566543d0100c001314424800146c2e01c2c44244148826034005a01c01d0f418441164200a80b10307004400c2034003500c2c002d00c2d000915603807500100c000d46040040c549181c1406103000710406420000a50282403c1c940030394800350744980f003900c42c1100002081d207a0406001103081c00e802aa00058590348161081000980c00c215880c616044030510301c0715a91a0f042d91001e21a8a21410b608618404e012000c80d20309003a40c0c40e5909005031909180400400640d54600030260555a072000c140e2105441c542e582e403545400303034000307025a000c64500300f940c0091501d0300c0c1c102c2c850340c403202074080d0040341c1c80e0440315074240c0c20440746449156210450400c02204004409000e170407140d00000c11001451251280d404d0004c10001002001008014007900c8c0d00d008c42d50b1080e0704440720300041c6d8581340900c010b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 124906393 1250 124905143 124905191
    0x160522090605070807080c0418050c0c0a0b0a110721020a050601060c031b05072601051006140304080d09030e03010911150a050304151104030c0806010611060703 71
    0x75602d04030074800304580c812609406040b0541ea590000d80f038841c02c4070001c2c403aa00c24046200700740c1c1c004200c5201c1680100750b0000051041e942045400b8580e1418490700280441d0a8003c0104004070750003130b03100d0740030900b44a10400d030030058035039524401510020b00e06081c029614041c0b40506200300700c22485c1da60b000e0155003503544e440e20301274401001104210041400075522280070070800d014244001c2c1c210004140c2a854010300d08002d60059400729582203d160030489019024056180610706641080a165280810003003070052914000340c081354040080c00086180da209560142101c503000160000b40e80c90f040d14414425101903805509041b050818447d0002181c0001007050710358001c8140030455074403541c401c0311040c2002c50350910206020840258140701d07141a400c01c0050b01d0072040c0401805a00709a0045941c403c0070802484050300c01c0c010349004050f1800c1440e0f4901880c0030858503440010440c0040503079408000800d400c80c101c4100d95 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 124907643 1250 124906393 124906403
    0x109020a090e061605070308060604091d0c010e01020706030c0903061a040f0605010207061202040e010803031e07090b1309021603020c0f06070222051302010216052209 74
    0x151551800d4801c058003825603122450300901d0300107414038183d0030401c0440500c80d601c0500c0c003a681c3d81c09071a15003016240d103030028800d100105251000380b2a520074081d84a5101390100014021185400c2440208a0400500248229481c0d07000500f000554685060104100c1002c00c0d0445107260341780d00c0949030a092030a44072a001c1d12641c0200380c5101544c050103400f071281d4440c001e0f15024406c1900583c40300d03408206c03a40c80381c3c61140502203844e40c00b5141c103640d00b802c2c3c154031380c003a000300b00e0b1900004244560a49070748000440c0c4800300b551490503190114000c1d05441651203030008054002905005401005101c80c1c0a000070280441d100c0c0c0411240600d01c0d801c034070088016201d402c4948103545090040032849260041800745000c0284e400d000c41800b0803c00141c0ba100500429500f0f00d860340100743c420004001d40321410f05150000900e0030b49103011203521403004920a1106480f600468254100340700c00041640c0c3d007103d0040b008051010003e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 124908893 1250 124907643 124907659
    0x503090a0c090e15040809040b0609040606030b10140d0902040b1002030417030301051309230a020405011e1703040b04140f03030c06041e02120109060c0e060f0309010902 75
    0x21042d089500050b452008181100e45507610794100401c002c034142d40280080e10184204540c1d4a010b81040d071700418060400350500b8040400302e4181c4030150003030300220382ca0303009956050074180d81144007100c80740b60003d09020080b182e40000d00c151104214810385807034200d401e41d11070750001c0e00f081a000d0004584c0f0280590002c1d00c9402601602c3d14031111088401c101d5440041524140c60004142441d00d811101045d401088220740450b100c0c4021514801e851902d21444202e0703860020240500114a104210846105030400c0108010841c100f6487e801409600703030a0703d818480b603940e610a001502407644c0203550154041c1000000d021490507030000714109000b000366202c10039103482e070b000c140d10b9004e92001c13010160700040c002004203001c001c40101d691004181c43e004442190042264440b003145d000c80140e4682010000b00a014852484090707082d05d840d02107600214002000da1040701d802e02c50b019004030202e50707050820b500c15523010f64010500c0b8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 124910143 1250 124908893 124908899
    0x504030f0b0601091d13140313150306030320030d0e010914060106081b04090f050f010501030e1f0f05070207090f0209090402100e0603130203060618070503090a0c 72
    0x1c0d44108894241c0041c0c04030381c00103942c04c080f00c500c0d03c4c07203010001c0034952030340c0320766285088001c1094190342c008080105407426070001e00c02044910201004a18140d00304040179944807030f0024a4003c140c64100108003095025043c001200d072010003501c4a00209000380b46980240d641c0d0b150074a10b8080440554081580314115881c8225006480300220241c8591148024030804020503c0d076000503070030b80480400c4c07481e5101d2412a281c03c2c60303100c4031a00d0803504941940182c840e0b440081c4182901d8040501d0700401091905000f150000300d9100c5d1111098a51604000c2000328094480700c01904040c103448403e0908100c0391030880c0c002565602c1c2880742441851401c422420888140c2c02116407091000d04000003a8482e80e0910440c501c41447c1c0c2e104024003040b0481c080da641c50010750081003840c10b4050002010b00415003007500c00b9099038805c00b403001d494607400841c844116444007050400980304d82c0e4080c1000d09280150030000d00e001400030b004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 124911393 1250 124910143 124910153
    0x45060e010f0501051204231e060a0501061709100606080a0f060b19030e01090317091605060d0902030703150f1a04020714030304030306090c050309070510020a06060e06012c0f010504030f 82
    0x10307231400e4281e4084404540303a201c522070880b00300380103000c001070050507021112040b218034560013071026002c40d1303002e2280000385030860b0459040200090140800e10003602c1c2103010740141c5101102007007001c18a480112035440c45440b0b080103186a071070007060641e500a0344510300e80441c3c10024808080702e840c000349014115000c2261005280d40030504030380c80050000307041c803442c50411b40814108000c00c022600b0440700b046603603072500307100b80042c0c40c1800010001c612540380001c1c0700c2c2640f2f00c40c60558504060507141c1c1032401061b03c45021400e400004034503815200103075184028140072031585c12801d040a807902c0f0003c1848100765141d40803004540801e402040112012a402c5400f44000c1c2c035a84007551201c0002e0109140080304944c02e01180c1c011115084159030b50750b030a64090783e0046d010540044100051540c00074525441200e1880c4800016040c24200081412022440f540100302c013504030011640101b084402031070300080f403040f05001907d80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 124912643 1250 124911393 124911433
    0x7051204060c0f18030f23100b01030b0604050d08160b04020f0901060c03110c03190b070504050913050c0909030c0745060e010f050105120423 63
    0x781000100c1d00700300216803603c03a40180200103485038041030b2131440c0d600d640646410720326041d503003640305400c80c00c0040e055035010a100030044001d0a490900900f892003224075403501d01c1d0500d4200701110b01076a983e0070441e8143c6004503090343e181c01140c10030070501c1c01045a800303076900c12070b8141420321040c80d981038405c510860360441100d5040042c0541c0030710a02c01c038000310b40200500c90000340600d43c9602c019031440c08030b40c02c9804640c0000d181141c841c40103104810611700a5041c4106c330b0b0310f0150f0040c0ca5003012441c00e460300f40411507200b0010400320313820100010500c10884144908103042c840101640c0060400c20842e6459600010380e1400f02d2080c240006103002c1154002c07151003a8031920011901c4641035000310324000549822202404040d480c03e0307000d018440e40004d0248492120300e25810510545016070960f007045040c082c0500120350306e00843d0038200d82c059030203003203040402d058031201da940c08622466865540a210b511203080c03140502 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 124913893 1250 124912643 124912661
    0x1e03060f05120c0324060402120109050711070b0a021506090610051306080105040c030c080604090606051801030c0906030818030309120607020d0507110409140a060c030605030c090a050705120406 86
    0x10045c05030300d030311b0104800c074400c100960624403c82c81c010407204010394051940f001080c18000a85086104403e09101031034016400c0042c01007540b20b803ea0703041000c81c015007182c4606548500381500061003a40000b0b140364480d2043d4016240b02a1180f4140c90b5092565904172110507212400038148400034050b082c0918030301504d400407035109004180d040380454580040c00c1d2030784001c0c40081c150390401510203549039034000455485c2c405520103c41c0d00100e40780c01d554150315002e105084150302020b80f00341002c805002003440d06003140c2120b1000d9024645007001800440d0642c0100020136610101510b00f1245501c0c2c0400c8041c401c1a0580c02d071145280d407060240c403540140c200103000710f0030a6900103d242001c0d0312414003079010301111303a8080300c08050686040f40d526030490b042d80d2941c4086403070a0b0140a08400351804902403c0e4400f040c001241c11450020856200503407124081940c1c0c5009904403401c0c100c5242d404143c6240504041c40540320003a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 124915143 1250 124913893 124913953
    0x100207090c020604140105040f060b030717060403030518031c0f051005040605010f05030610110d0e0306011502060406050a060902040b0702030c010c3306061e03060f05120c03 77
    0xd45e40002078180324141c0300c1e680c002c4080711124000c0e16028000c2c01008951038061140b01e1000c03c8104400c512000c028000c400108058038280c6401000c0d41d5004c2c0554000b000781c3c1107580e070350800210aa84080002c1c11410f80c902a11689900240c0059039420395003514000501c0010aa01f603070800a9a1096500303129003613036800111405400715481400040d01032011800c51b01d81401e84111101c824508200703150040500e150420301c4681300c1d08045100803109640e03600f005c0c41003500515401c040100314051045002c0d44800005000605e000d81d5140011081012030344140c010385404442191180d4442c0d0503c2810350011400340c4c807a01c5034210a401942c450410400c0c0c06074884452800c0700d02444442100746204485140c07021011801440d446116200b88402403400e956806c008404a0000b42490110200b0f01410181485402c0c00340c0503014a10030205c2d10203503045542580c4030b060311800e225640c40f100c1c0d81030240b0341c0809840201c440611030740451032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 124916393 1250 124915143 124915163
    0x703020706050f160501090503042706050108040303180b13060f2a031116060f090203030a0f050409020d020c160602120f070212010501080f0703020a0302100207090c020604 76
    0x503400598407409418440f9016000411044140ba100380c0c01e4200410710410020030a203001d40c0e82e20b8216040758115010f00384590010403e4000c4a950710300c0005400d0404101c0c1606210008017140002040501415100d1000082c0e9941c41e0068040305500203441a8813400d00c18103059841703100f1300c805d840c2c846c104046245020994840c0c0c8482c54400101d02510b100da1102c0c228040f5004c20410050541c2c0303041214101c8031120007081c0300c40090205074003082d060300d8070008860707640b00600b18261034000c030080103031000011201e501c441d0313040842000015000445a174030403600809007190012558400072503040e0058084100400192852000c40004200203201d45210341d0300140c1c0000b80c0400b5446000e401001e9a80718004658604016034000c140002000c00451803103a40d03400c01004810401d1019596422410010305450f910b19000100c02902e18003010344503081080440640c140200038030300c0106400607013405404941980607469040855054801c2100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 124917643 1250 124916393 124916399
    0xf050106091508120403020d03021204150f020102031b16050115090e1c050a300b0a05090a020c031c0b09160516060b040608210901050a0c022407030207 67
    0x1001c035002c01301000011307016082518680801c20610032160701902907005031249000104490380c024005000125411401c007200c56000405111030541c6003000c6901c1401880700c0d2030380740002c07000c600b07180102e895203030200814000403141d102d401c010b003c0e62900610089401c0c03081e00c0401107510480d4100103c1c034403510700710345901c5401c1245603004001c00000c00c031540100c001d402282c0c142c0c50102c0c0c106400984c0e0100030740e103c2a2403040326440b50031017180c00300f440c0101c007424a415101c1800583c03424002c1510128094225002e15401040c0e01d0103000c81081a04c00381501400e42c0e40c038840c1a151440c000b00504400341e40917214420014503510740a0080ba00c500b105030780d900c1e2a10031400781c15101001c03905011202c0300c1d1030381e80c1c1840799601e07801030101401d80400981048035840341034408800d0302d80101c101e003e01c24811900140c1c0c021064440c0202c45081c1341c405880a88000344191038a92081409407444112034003d81d0010301c041c001d0382d48242c00716031082d52 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 124918893 1250 124917643 124917659
    0x4060b2206032d080a0c120c0516081b131104150e090609131202070503161406030c042402060a1515020703050d08041a01050d0b040f0501060915 64
    0x20101d50814440b56030f80c00300b000103100f980105942c8031503190100d02003025549403c6070002d8102c15000049440c48174200b80901407203194440040d60030500141d41c90082c00319111000c503040816801e0001c14441066110500c5060000c035544400300311845002c0460500398000e03000b207000114500010105960095030070a10400000b0180101c070703135401d42000500e00000300055242d0a00d42c000300001183d00e03115850900080c0c025042050410301810b240c07405050480b180c0c44c0310100200110300b018828100c4070b03002079450726540d41d1a0703102880c0341c0c0b0440c0c0c41058401c140018400203880444403030383d01d10b18144d080c0e03061911a440502c0c1a12a4010522944d0780c20060400032043c01082e422241107450050320401035a944a250600c4103400c0d00c08082080349041004215a040010040181d40c0f1600142541020003042e85c2080b11280141a06030040c042018007985e0020707a40d00592040c000d200302525180840046c044420208514075a201c0010800078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 124920143 1250 124918893 124918943
    0x40f060302040605090405040f17031b030f0114060c070b1201092d1503060509190c1202040f0203070909061401020a120512150907080105030604060b220603 69
    0x10f5440d6039058245100342c820040202000f130011121491006840400200c0c401030348840c030079021100c15203d1a15088404055140905400c0a07460420810002d022408031302070660307509423001120304001a01140e0b00e0720540840d40403a104407007000544c80144801000140e841c614009030b142d07643c034410016502d20011000c020321a11000c034044846e680c1681d40c1040c03000030049070300721080e10051000c0215030410740e1fa9544079020800c4802c010010b04d034a201404402d4680076000751101e8001340e0403030041d0341000100088820a65949400a505030441603004564904044101804170000c5d07220b40c407c0c1034140100012019030f10059901034181c182c0242c0140c010320395071038111840c2c4e40c075050140402413220b901d1540e12000f0300c92203107001c6214800308440f020200401c9510040c86e0004200d00040140000d450100b0080e808c41d600c9040031030103101a100044100b40c00c44031803814100c82e25003d01e480d100300c0d040b103070031280103080c5454990030160206440f4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 124921393 1250 124920143 124920149
    0x3090d0f051605010225020a1403101b1101060b04050603040c09180302011401030c0e040311010e030a110705090f100b210601020a1e05160902040f06030204 69
    0x158220021261a29029595648003054039180480c900080005a05040391000200b0344507a0350216076051400c1070f19030b04048152450080e0007011007141d000407401c42060003440b0780c0349408080d1036a280c0303041050243c4000084403e114001188420030449001c0a1084001461000034606202018414a0140c4e1000e0844c0c1d0703e003604200501c1300c3e55101170401c4400d0900003c3c001150440f41c420040720608043c85150400000d041c0242940c80c021101c0c0041d40382c1d0801000060a5094980212520070030a24010380d103a0506590700c500c03038451005103500f41810404180340c048014001c00f022620340150348051000c44517034031a054029140c0100c2e03100c01041d81500728400303a070b501014a0484810403900c440e4070040d20740140103400c1c440c1d2840c000400400041c441d18541c8030001b840140909441c98940141c0314009040c0d003003036101c100c00c1200500105102515a42c100c84248d03601880da69000f480096200c4e10410711404002540030071014400c0c02100c0403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 124922643 1250 124921393 124921411
    0x3020304053016050109050303060102150c071103030d140106140c1002031909031214090a030302030907091103040303060f08060703110d0c08010f05030106050105030a0902030111030a09050706030203 88
    0xc580d800020201c1c02d603025241c22030304a1564100c46000032024054000c805100340095a12410f0080029252400d4908800340003a0660108024103c0301e00640301456000300c400040750800c200032a0540c070074007249425140c2091421000401450b0031641207800c1643c400042d8500302c0ba410129000f192100c070b80c20b4101e040c1c3e400111201c0d80246800c8820003519910307645950b0010030440b1070000c4100c1c04201c8030401808000c440380300c1da0f000d28207290064005441d14800311904c1e01c3ea504001002c0c103034080086103c06c1c6081000340054080d00c9002c00c05d6a180c080d9802e45504200c0c0c1c00c03400079050031804124000110f244030201c030700c3c0c00000c01464132240800c0e00034055610321101700da9028007060040a20a0140d22745921450301c4054955051201c07010904480360413040c008ea05203002040980d0380701040ba9400705880400007191280c910001c0e0243c11900e0744402c19100c00310500600181590049404c540b00b4000c48059581e1000242d06034001107a100f85 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 124923893 1250 124922643 124922713
    0x3090501020313120302070815090705010c0b0a051009021b01111306050904020d050a0e010b0103050601020307060b0d050718050604050402090609070201060e07050a030e070b04030813150302030405 87
    0x6101d2046101c1c00704d0504c40e00540d001c2ca500c407041a4034102c0032040303180c0d0740012a405d001d4071000030700c04e042c0503000a00e00400d800031952124280c05901400e1001c04c00d55440c0000c0c505030f500c04401e8040c05541500b50354859914a40410b0340b900160001081d5207000c2c00c0350144421031089440e94078444450003689460000c1c00d641a400003001aa00241c0800205042c62180d200c1c03148a01590b0030300107842041c034020f040c210f400c005801814103181c2800d01c2450ba0b000029201d10726402701010451015100c04100c0d800801700000748940301d800404685042c0800c05140e020007882e01c00c20165031880200300c25200140e5000e900f10000ca40450541d080106019a10045900000c60302556500c5d02141d0000c0031030308480001e0000c00c0718503d0f10340c107000784040d1509140062a5640c2002c0c40383c0c046106d144001090140c0c001032002480582c420340d20010040200344000c01c44407214007402075441140d040302c0c00c2c01520f80742411480810110450704001d060503403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 124925143 1250 124923893 124923899
    0x3141807030f05010b0303162102060109020a02010212040605190605010801060507030c022115060604120f050307060902040e0a1203050702120712110316080a031806060303090501020313 82
    0x9600d209100b00b0641d0a0f5413643d081000640b801c000610204225166030401c012890621000e400300e041280362981803500c002c062030640c00030310541035981c031100043c2e440d03100080503402449182401707c203038500c0704204403d10125074441445042da0500e02100d60328841c468a00f00c440d0f030b0140a010446080c0180580c500c5140500715840c480e04244150050740e0700003881140c0321501042c000c0c1c001a4038107048880a012640860904d191054024103140000a0003801280208040018480441001d000949040d00c03000794121007600d03680c00003170905c40050511f41005a000e2820030105400480001518566003604841d0b0f0740051040c40100703d025060241c2903004620442c000c480518801000400c54544034082404414000d800080c120388580301d11242e1580040c840b01d003d640703401030b080398001d074801103582d0b07115034210080c2c0080181d65076130105403040241084c108929681f1580989000c1e8a40340d48032941c80004a039244941402c2e80100700d1845010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 124926393 1250 124925143 124925153
    0x6050a15030b1c0b01030203010b030a03080f09030708040905010602010b220b150d0b03010b0108040302030f0f1e0915090f0409080f0a050406030605030307170d110a0314180703 78
    0x3460b1076030000340000034114000186210a01d4003180507202500b0080040003180f600344648118004140c0140203c0301650b1000352400c24001d00d500c9204e00791500190000f8000e000315032185a0101160b40c5590321021a9002010240a0320700950b01c0c14010313200c2441e00751442507004109940700b04400215401c414007500806403515000759055801c207005840c1c0901904d081030b1256070000b08508188105401c2d2035844400d0340c10301c100070051002282d03002c0116920350101100d81650340887c400300306014401c40140f5507000c0c031003441510200c0301003002842055802c4402810000c1200080300c894032890000325407283d00d0321400b03e02410190071083c011809083c16908110711061000026402580303050005038000800344451a0184141341c060319042c0c0c01542026020f41d02c1c00d1209000000740c0840140100c1c4000c82482c094015450580e01341a0304da484000509015020b010301f207544001f20003042000981029000e007503030856050240040807000c1c503540ba4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 124927643 1250 124926393 124926401
    0x6010507020a0f18051305061b0c01060e042604150c06050a050609090703050604020402030603210c0c0f0a0308070c0308040e0717100512070306090b090106050a1503 73
    0x1007241c10040d005000107490225905031001401041c00304000c61182e160000200c40c1c004100d9002c00c12a001e403400440e070009180707588000b02540700c00d001c0700003c5040c16280102d00200881713600b0140040360313003450016164011880742c0d91298216a22445d000203600400c40081c0c100101403008004200400c4010504551036080500f40840300d074454005840b0b0442c0e00d4256140c46070180203560a0491040e0391118004003e04106410350b85c5441d1201006400a03205a80120101c0c401e03aa0a00031246610389a1000010707070315070701d61701d04c101e504541481100f40c091700d0b07040b03002d508104c00300d4809604010843c4ca41c1500355030b241002600504001d0305c807002440804000030b440303140200060301e030b40b212411281c902060018102304000f11040600710044040c40710042c0035600c0c1005991081303503075001641e0544201c0f031038807042e60700280440d81410445818020b8401030705000384010402404026164014098502c03214410440ca0141e80da0003401080d02c2584 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 124928893 1250 124927643 124927657
    0x80601030903141308060903031f030b131103030a0815100203030406091e061e020a0e0d020f041a09060604030201020a06022209020a18050f01030f0b040213031208040803060105 78
    0x760b0030145e100c0c0c140c079180060445200501d40d00c004240003400c0d071000340c1c0010554219681e0410b03542595903420030080f02801103003621200c000040204894012184500e100c050116601c1d444180e00081401c3d800b50782c910300300000e0b1502c1d99018189030881c40d80440d60354004500d50303122a07030f401004005401098a80800c01c81106451451048008045a000c0c500c041002901c240301d040c0c100c140085c6074aa881c1c81000240106c540060701c881d038401c3c0c100c0c0c030094107080600114001a8051075040d0784240742070303581c0a490b00840c2d10b4050b8240c041c0c03040380003a0ba03042d0034451030384610302001c0e000da880100740748002526a0010001e41390340c01743c07010301400980341c0942094010341010542036000300303031002160b030720644000d03081c19001981c45c40140340c10003055032600114010b5040503201e044032040c400040e004101442d0b070142c800c40d515000c1800700c5c007110656000c200e40b4414215041010b051190040c9405a904201d02a2440d101c40006407503541c8444 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 124930143 1250 124928893 124928917
    0xb060301090615090501061806030c02070f0609030c0806010302090f0403020f0709020705010f060513020d021b0604030f1412070e090a0c0f0311070803130c030501090308060103090314 81
    0x180d04001803460091005a0540c03c8200820a0801d4904025568160050000c000100741100090318546548008a8685080c00240710800400807414225181c01c04260f008500b4000103c5543c4501101d0899020302c030b00c5889aa143c9890a490b04420310020b50700a1020f0041903481003d56502038000e44a170040340e40c030038a5104100d0614001c1c0c3e0016040f5039004c03808005104080c003400040c0d000d80c01d410400c0500f00b0000900d070054210a250010b030740402c80c082c0100c0554121005d1440161115540094402d085503440d90112030490000703c1d40c0501b24446400740343c40e501c1c0980401d4400d424540c40380759280803a80d00504400070004001101072990b140c4410030740c0103050110020a8101101c1405020162019954000c2518011040c008480c045041c1c03419698008000360707603504c600c0032484e5400818800a80031071700d1a0703800001c0180551101000074030030340706c030502503491000540c121540560060045562240c89100742e64101e802411001801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 124931393 1250 124930143 124930151
    0x8030406050c03040e010303080a0b040902031005100806150f0303070305190905090f091b0102060117071a0703020c150a080a0e010c09031703090318010c08070f0605090f03070b060301 81
    0x503009070b00c00c45d500ba8019408201c5000900c0749016050081100410f400c0c3c50501111384107038007080d6101a28015010056503800108012003040d0300c914006100c00022120340d41000c0b000540c00300c0c00c1c010414070032141c00d62a281c1074140401a0b0301030b250981c079510300b014003002512480b143c1059405040003800d500c00706044d0b640d1306105d03000e508904030b038002c00d01e00845c815107820714042c2c160100014034403441c02c0f140c3e400500d4a044d00c8c0c0810801b0502e10082061514003407003500200c00b0344030141079164010360701c500503100480c025400c94991000150520076907030400d50101084620410040c044507005008494001112403c00240a0f02070300840b82180c50340000c040004003840030801c1030060443c0299002903003022071a285040c03d501c13207030390313845460b088103140d8800b110b54a8039030380502102c0102d00e820000159a9040c01e03d0628121042990200c0310140b5040100d440b41000054581c0c403071600b41d0055140c03240940702c52250030b20042415900d5074035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 124932643 1250 124931393 124931399
    0xa18030204020d05100609050609010516050a050f0606040c0903060c0c02041109040615090302090714071208090a080a050d0f060e091005040f022206080c0f0a08030406050c0304 78
    0x4501c002d042601d807040f40001c00c0d04004400283c0b0314243d5100300d00300581c944080c44107685543c21280d0b44002400d10a548804c4003011101d01d1040078405811030142c440d441060000100d1004040301014017998040c1e510b040400040b40e038207a100340300090b10a903040c0300280f03a5920502c812080c0c1d040c5039543c0c000f1030f40090309880b442032001081907008500700f0040e0510b0300a03140035142d448500500b110000d030006204084503c4041e2103207444001240703000740a101e03200241c01c038910300d1542d908840e041c40040c865841c076084c030000d080c40d00000c400c2d040c04a100d4003a0b552003c802454031003190011101038200c07041001500d0703a10b90003100004074921a41e001400100c200c01e55134505214980e0800031074494100aa608010070130002030f5170340707200d080900c1d030496411600c00c824480081c290742402901c03d520382d2034030b40041641c60f0b00140d10320a00303100301c54501200c201d140511030300c05654880c001301640305000500c000c034010005406025400011203081c996 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 124933893 1250 124932643 124932649
    0xb0306040c08070b091807090b16020f060901020706110c040e0a030806061903050406140f04020a0f0308122e0f2301030c0516150e010605060a180302 66
    0x160540341140e0040701d11004208102c0c080c41414001e00415400c2818803624501050418100204501d00100704800007120b160060f0081c0d4003800c81c800980f030300c44910a14940c07005410810a82c85019011420340591a2040c11540b5440c0181c1c090302480349400c03c16a0000038040c2c44140d1405100200d0045855503c140c03618004248010006810b607418042c0400c0c00c007610290041e68204020380c0046004200810302c1c24461034001401d80d41d03410814005c2c944c040c499188062005c0070710940c0c211098845000e14022204072401c180d039601244c40b130303a21521000304108810f000541c542882000d8131640041040d40d00740443c4094040302a0100000c80c0d091611a0103403414000135008003040c501800c4256212030744190301240413034107029120310817810191511044140140b00c0d03000c0d140c1610500451f40310340c08551801d182c0150482e0b81100085181404000c04040b0502828045410242240e403509140c800111624003c14445540742882c8002c0040161 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 124935143 1250 124933893 124933903
    0x4050c091908030c1e06010f0e04060603020909060f091b010c020a120506070905060f03040f0c0e0a0e0c0406050a060c05210406030b0a050f0d020406150f021006081e010b03 76
    0x5910040d0400c2c82455484041100a51003001c2c170315405140113010101801e2080402c1c0d56004141d60020381e100d20346003000d45401d8100035004103d140a200341000c00291260113003c8048100200b0369a12140558170200c180200280c070b216070b007403902203501070342e07205031031900240542c005152201030324840014a010100c84581c04441008501c580c000c62007030240208440c100e150810f403006443c03c9000c0a08058480c802a26070b00d0108040c0b050340d10014107420303030441c2c414903001244400403c1c0c8004141d1090280e2091294035190600c1120240d480041440100034200001204e5001d01a0b1044545100d51911905c4100d00b0742da42c030107a800480354a80e6698101100203064518844020b802a09c100805004541e59074003818001c90098540c0c0301800e034a030000802800407a406400c242602d5107410f8511540800561030001180c0c08450318680e09120341b80031a00648105412604603508101030803000b641130400c4500654001300704124602d000074101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 124936393 1250 124935143 124935157
    0x403061a1009030c0303080a020714030d0609061a22090c0e040e062e0902070b010f1404090c030605070e040c0912020d03030908042304050c09190803 66
    0x2064000300044041c60498003998010455207058001c05185035504080e02d242800000e080c17140b204d0014500d070041340e0503248401d40141d000c1c110903a1542c00117440c1d034050700c083c80714181040c03004907092143d40205400c907042103041d0001102510601c0c0c0c020b4104070580421080c406c0c0c05803840c0580110000040d10844800040c102c20f404406401d0b888a5100c4a0249041c08405180880007040c0d075580800312046000c04580088868000e00b4415041030b00c1000d95038002041410643d400b40800700e2080404146c0da03601c80c03d28a030313510410300c1401420010203500c04007500380740c1c000d401c0c401c1c45000f0034508c03d07031280c0d50042512000c9500e82c0020f080e54045003d01d1909014440300c02c4002e0a140128500b403803810300c880030501c0c602a0055140303da5442c00c051283d808904202e03008941644ca40740c44684480040d200091288691064002e44600c0e0389424443e66010b02000e5407500d241600410030311031007852801c90440c04001d04040064111030a000402c0c40f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 124937643 1250 124936393 124936421
    0x5010e060409021e0403151406031c140409050108010b0f030601091a0d080d1d070b07080408060108160506090a05010c06090209161b0b0402090406020906040b090108060117060d0206040306 83
    0x14001d4524104045444945448000e2003230042031120750303200410341912203008060341e0046007160050541e20905240c1c40c020240c8070016002038480803692010781a100c002e4024450000540c0810901c012500c02141c0c4c1a08100010070940341c0640c00005002d0600c4105c880200c0c5545c00075140206215095408000c009649200d210b211300c41c88070045c03544a2911418100103403591365808244c0184a00c4042c000762541c14040003000303440c0108025070480340c02d0368481803100d44590301c0d510300382c0102c0113032100851146407000550b4800c001c040d040261103458900111040341e00d803101594105e917140500d40160b100c2400491007038041c400c00c5000307045030020081401003400e4440c0f482c030021740c014000150360302c0d889a400c00d8045030020102e40715070900300c00902c030b2604565030040002038000380503501ea0004d08404031003602c030001581d0360400152081821020181d010001703e60002c2c0462400401b0300c044c5500141c641801c064603035031008102e8020450901c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 124938893 1250 124937643 124937663
    0xc0203011407020d090b0306040209120102030702010e120a08061c0506090601050a0f080c0d03090f0807150302130510051e0408010c110a0308060409050604060f0605010e060409021e0403 82
    0x160340c0401001300c2c810294038084a8030341c41c2202e080c1840c040078105a00c1a0340004040d00144c0c2c0d1515041010110320000710758905003c20043c1c020001141c207502580183c5402001022062096818184072078442d80c0e0f86a5402d800c10500c85400b00d44480c2c002507803100c1380d0106404105036440350b84594008c00d03003541004200240d00ea0150701400000500d21410b12131040d0100b0700ca4140c0300c080c0c62141203182545070585034017402e9004083c851038204000503134441c0000e00001265050381c0798070599922148101d05921170035028006198469004115505240c4400802105a0700e4220b0600303203445103010b1001e00e00948022802c002007010300200c40e00f0300c03c40e40b1484c0310b8104100d04041c0742e6102070700c440c60b4480241c00d0106890002c0c156440d9a040807103010b070311078240d0704103280600d07041c1d000307000041c51000c103a0316044000c140303035004114165501200400301c50920349003e001e00040d41c05240c0031111203075812064114048000040c002552007608464 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 124940143 1250 124938893 124938901
    0xb1803070510110f0f0315090c04060e0d050d1809060e062b0b0604020d05010b032e1a04090501080f0d0509010507140c060a0f1421070c02030114 64
    0x100640f4041d9080c094000401c1140695121034602100c551030200b024550b22603540c00048140e40b2030f411030850b041a000c3d420070103107058000003441501e4564482d40f006003489810f0205111174500010080d90042d01078050f1a8010325602454940204242c19a40d480e120381078143c403140d81c890958070003503106102551030107005410b0380d00002c600500748280040110211444004c00142c0402120f401081c484d889a07012200700032105841030284d56500d42c1e400380c090344104c8082c0203410a41e40d140c03040200c00d0314983d0340c5a12000b84100400e0502141e0080000b624014136040403007080300080e1003140703014032030080054201034098801010300c42c501f414413441016007081420404030318583c1e000001e03280c80e0760308184007020490030324186507c2c143c804000c0e50390181c000b056818410340c2c00700d0007600440440c0e48807080e40c60b01180700100d078040e240b1080300030281381c00b42d505121800d0030300650160b074a00c1c01d81c400904940200303003180d80c9c41852121162100c4104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 124941393 1250 124940143 124940173
    0xc030903020c04050c03060907030204030209010f063b030a0c0f050109091526011a04140c07080a09170615010219020411090406121109070c0b18030705 67
    0xb01c01907000070380f4144083d1625041e03140d018840203100c244039035091004116500d00c00e60655002d103038040d107200402d5840744001044045548269000201ca03680b212403c103042102c3e07110440c01c90b04680c0015420300d01d201320000b1801c08100c0d0507208407180d1102140d200606000104180400800c0e001c1c10704000400b200d1691704090003150810041003c1d15050501c0402150200e40b440002c0014811050500911a07461444190300740750451300d00340031701c55a4202003030f0111402c20850b0701050b944410710104640800803030324140070b8240410140700007410384110f42d10309011003c0e111846c01c003040e0042036195015920840c10004464005001721069910074002003004240c00c0d1410940651b1080009014030b4840b5142c500010200080d200180002417003030051544800410600050420f4150789041e440c0110000c2c90500c020143d0040070103968000c007591150f2113004414001509070609140480114480091709001600c0c03d64800c10103840410500b81407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 124942643 1250 124941393 124941403
    0x40e0610020304060f050904090602030702010e07060f0c060902040908030f070315050619090b040605090306060a0302011409030304031e030e030c130b190f08060f0c04090902040f0c03090302 84
    0x540d0041d940200018803145401491102001c0e51603d8040d030382e200481c0114001d40f07800d4600501e42400402032181c05501034100015881e101e500319640c0580c0c1d004204c0b0b01113101da031150041b41c400702c01d62010907043e820040d5490f00292010441f01515520b1000d035920866021602244540c1400201ca50600841001103c0300307854080550a120001d003513449444407404002d812505141e002c18085e018010042940000c2c1c41c0d100d607640c80014000c0c0d0300042469210780a140000f6210b481c01c514800103594069507051525020341c1001c02c042d41c08081c403640d151106110000c006032840d0fa202207020060784050080c0b0003249000341204280f104410f01c2600020f29a14a54541542c0242d90450444000c00c0e405148070115000c000c2446414192002d00e84e40801c8428104e255502142c00b0f8030301315101c50381d514a0071000300707205403004042203008000400c00040b05030010840e4900040002660461080404080340c0c5405441804a61903100150a05406100e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 124943893 1250 124942643 124942669
    0xa08010509011508060a0503010606090602010501080d051603020c09010f0905090a120507020414071809020c0705060d2910020f0c2701030b0a0507050909010b0d0b0402040e06 77
    0x502900740d9410501402c2003c01c6401604080104400c00910740d40e0f280d107003900041c00e02400800c0115202c0d4001441c0c15064010140558240000050301c5c0da00096460f180c0c0d00c0503520141007184c5025240c8154014060a07000c5108011681c0599a80c4110300b6008200105034000010714100341802a1003006045c040950001d150300780100303501c2e5140700894401c51404a6940d4040e03c00180100340c0c070b0303155540500c1c0360710411175000c0d042401212030407280c0240c021415541c9012909911a1064111403904111820040c0d42411006407404200c0c20707001049581084070002a010702601005104150920321041d0074203000c2210819898148061f00c0340091240d00756903600180e4a00038003545260f521172500300f0704158000600500d10448400f01d5940e8105000b50400680305049043d01e002d01158209024034100c4401900c0505882186c0c0c1c81c100148020360403e407100d1103a951990b0340c0c044141c0d1240300074005010b8071580c001090038148140090140502 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 124945143 1250 124943893 124943899
    0xd0501060f050c06060f120312040b24101b050a020103110a1403090f150402100503090a03120e070914010504020733020711100206011a0304060b150a080105 69
    0xc0050862400411010760294050b06c01e880d042d5004008503140d45040c1250804a010101d010003c840501140e6400349025010903030203a22200030542e207224203100411210000005040701d10b090640340c22032443c0060034042e4816024504813a81c100c070400080743c10750841c4158404541e0140b06034820317541c1a042c1c60b402c00bd90a00301030718603541e0b51802c030300c0d00402000041c1184820410014150030200c25074508090440c41c04850b0040bd039822841400303004042281c00d0b21510650348900705a100030301300100191002e950407a82111000f60341611210240c0b414003080240a00400ca069400500203140400681031501c4c10781009202d903004000b43c02c0494080034031410304683c031500c880800c01d202d03003400403100d0420610b88503c5001150007000c0c8036509039011281e03101621313101d40d01c8008640490f210b05c001d0250030004040003450350140c144610145038068031401c800940d0717907881c400041c0042d29400c0c100d6a10603001a04c0c070060b990210781d06006003015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 124946393 1250 124945143 124945147
    0xb0106050906070f1e0c1a0a050304080d0615020f0c03030405010e0907090509040c030317040503190e090f01240507021e040608030915030907060f11030d0501060f05 73
    0x900148140c481d80c18040c0c01c264000c44c4000074422520030075003141c0c108603680c614403251880c1401c20a401485010211620482c10300c010a04d800c00700d402c600c4040c0e40b101e01d503a60f280d031020016040543d5442111359141c8011900b1080d20110108881d2190000c051007070742404032078a4001c1c0080198000d410911041001d640c00080701490400216440000e9a417424070840e80718495a10441e401103034142408248001d48400c2d800781e038041d40c3c0e0f02d9205010f41c2c0840c420020140c0b001815980204800e0740305200030808031050040324640851090f400c0c90028588460a0352004410480c0400402101c03502c91202c080c20761040f0203c0100c020b0030355010f0814054220041d000d201408010758014800221142d9528001001000390545404a056891300954409801607500522541e102c0f03000c501620302c544040d0004004107402c00d0011500081500304c00000d012440c02c4084202d5403d0010b000314085c039990000e043e600d0f1440003030010020040c464180320007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 124947643 1250 124946393 124946407
    0x315030a0210030207031404030f020f0405040c0b0c1e0c040b03060403230c0d08040330020706140103030f0e0d031d13020d092a060809280b010605 65
    0x94102c585412031514140107071580c1c01c07801d00703a0700104c2a1500f41c1c0441800180881009400da03c815040d82c000d6844c0b4510001403018003049a1058030041c1005030074a004104001501004040010700003081c1c0d1402581d2100480c1401c1140d4540b06640d040b804080c9064100b074860740a107070600314003e203007500780342d01d02034400842d1401c81c3c202981c901058400040801003125030401210040300c0c078502c2410001400c0c1d820a90342200060740f4403001800c8508140c09480061030900b141000000ad092000e00c002d510510341294111346031511159030103449481c0a0003140a5100c0542003c08000010140503c08508500c20160214035401203075002c801000c01002c036100c82d010310042c280000d42c0c3c02ca4800c005000e62800050f1900d0000d80c940c0007079248078131411054490074140d03884030b502ca00100448010603060000704100c000e21503941a5000442a020785103620031061800c0c607106502d5041c814244d40e0442c040c401c100c10089424010403070342c6091814845 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 124948893 1250 124947643 124947649
    0xb100302060a030c090f060f0201060503070501051602030c04050c030906010911030106030911040e0309040b030706050327060703050f07020f070b0f2203020111120706020304061409030315030a02 86
    0x60b03644500d0406580b02088210740c2e0081c00060098103076400624995952450014071200d500e0384800019400c1c240e0009450400007500016100e0503181d907070a02401420b414980c001c0803000380e906101c1c400c4200b0044d160340c45031600800c059000242d580c6051000c1c0341c5440010381c000442d03180740c1043e210b201a03001c4181e905468251801007841c400743d08161400c0500108009c0d0b110f0320344110041d158000100504010f40259014403080411800305a21194148100c1d00030171010400a906001231107101201000501500e8001d00214440c0519200d801c84003030000c6503481c8140b1a8072118541250381c4001c0900c01083c164900c20520740e00e078011841400c41000c00402c14201000c508400e850480c80240c1140c4211681004404440c0d0103910081c2e001c50800740c070305200c01c030012a242c00b103004401a81407500f005503840200a6200a00581c2c1481e41c0d6029a0710403503c81a525000b004020000c0d9224148102840e107801c0306001418426031207814000010b031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 124950143 1250 124948893 124948897
    0x20307060c0305040b030a0f0e060a1d061f12060507030501090b0d12021009060c0801120804180209040e0a0201091e050409030507021206040309320301020409060b070b10030206 78
    0xc05d00340405459880d002c5680002d0b0207601d2880c0c03403040c1818040707128210001000c2d842000a4002480070070043d504809e1502e141001c00c03200e40d003007400000e05040c01083c0c820031300300c2d0880c80490907585da2404203d0b0314540d00021500701c1d84400900220302e62601800d07001d07085c8a603042251800350300014511000500e001410302c0f9030030140207203a80c000d02403030507200c43c0380e501031206550614000c4014012041178101060f103200020500e6502d10000201c140d5000140c949024105288505041071616a0011564081040c04401e89482c080c2c04801d1220000801000d04507200140105003107821108820321040a103100c83d40891a0000031150700303076000540509a402c0480e4144603555001e50080f54903444030039090400501940700340c0c0256a0010104d440f1160314003665585d01550000c00c0b0003020107001c10303045e80c840c034180d60300003000149000c1d03440f40b2071003c0d54610b50150315042070100c1c1ca82c0c10f020481c4035203903000c5070685801ca0704906641c005182c40c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 124951393 1250 124950143 124950149
    0x21040b19020f12070509060d060503071203021506130207061e15060e0406030204090b01090c0503010617070917010902032107350d0c03090203070504020a020102130303020a020307060c030504 84
    0x584030b00c030f001c500c440307000b03404956003000f000e08000d9960442540040241c0814070a0500a20402400103403031654100e03000007140d4164080c200b0754680080d02c1880070005403d2a0344032000c0d1914604041c3c4500c018400c042c400e982c0480c2c01c07804030052070405081c0c1001c2c4102d45042c51031200007040d440c918281903400c9810240c10f030046400218005050540000790070600e40088201448165241581202c00a607400d0000743e40096044409000a214803004a08107405000381d0401100c2583e51010441ca072603d40d06503582c2081a029250003110900d40e555103a0000c103500b030501c400341003150940580304865888000d112031520a9043c05881d001029400303080c4280304000e50468071078100403908100c1402d20889561340e0088182900c4c040c6041e5085201500074011512810b4005020b84001440c000c284406940015010001c42d54200042d02203405012504005113000354024488140c0600c1854074003030b000c0d0840c40500c50720401c1c0d800001c3e408000c482c16 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 124952643 1250 124951393 124951417
    0x9061807110106030501060803130b04050303040b07060f051f0f0f09050606070605041209141003050c0c070b040806010611210c06070e0907030c0c0821040b19020f 72
    0x7000120302050041502d03800007006075080060014250600002500c401503c5030742c1035401a660b13070030300300c1a07208a206035a00354009100030010041070b000a440500d016240c08242194600455803c480c000c990008042410704d0010110b6990686914054052840845007150411050610545441c810248031546400000d03403261500819112a03a610100038045424149032506405d07000e1001c5400040038076400180000c1d5005e00303ea4030a40160032000c41e8601694120060980101646100c0b10100114491240c0c01c1101c0001044003c502545403800c04001c2c40c00c1c4601a80400108180702007202a01721011400f4031940900f00c440143d112695100716400e8002c408015500d801036804205d45640c10110300449000100d071565129030f1012015411203007d0752400c2d000584031179503003001400000003000348801207a4410131030540d04802d1061408100c4045840b0943c6800740401036440031524840400c0520080d424810b2a1b90f2000b9540108816221 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 124953893 1250 124952643 124952657
    0xc02070317070f0305030906060a1211011b05010501080114040b070e041103070e04060603180213090503030c0a032f07030e04050901021e07020901050d052a09061807 73
    0x925100031100311442c07558042102c200049090401416a8004a0b4191403902032100040d51620b00070780c1d03031802c0d07800c1700026010000c11a103070a440c80711900c0c17000b4140080c41c000c020151420340b0034000101d10a00c0081000d6040404460035502010480b4034010741c2501400000f440041c40c50340c0c0b01100780350003088011118001405014010031024101c1d9000050240c01c0d5440349403452001804d131001c0c0000da82d2880d00702c080f0f55228081180302410400d401006180500c1c0c28596040c21802c08500c5c074501e901d5084c2960300941d6070003001c103400540110056014025200040c2440e2240c00c60104400f00300d04409501e5510100c0c10f040018030702040500903c3e20258000000d0004c1000d4a03060100300c2c002c3d400191142a001d4000d417a0028200d0b130b0b00c040301e958640c064215001039203001c4c2844200c03c4c01d00c100f100d042c0070300000399004a00050340702d0402091000c1d458561801c0e0400d0202c41000a40b503d80100c003020421a142c0384c0340400307039401c08114a800701c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 124955143 1250 124953893 124953923
    0x40c060807050708040f030b06010908030d09060b09010f0609080307020310020304030c05010603030206060a0b19030902150d02070606050904050a02060a0c0f1a07050715021606020c01050f0a0c020703 88
    0x25540d100e0300f1030040c003000f0007003004a01c50b40114a00d10a0368401c803201c0401e9264417005440254140c030408809600810030344100c0e174140d03005030800c288a001d000c205950040e00182640b8000d0700010303e03100540c407081007030507030012070400200005000f8501d0100700d138000c030342c44245280503140c6050b00000458209403088070040080350700301c0000c020b4a03440e450025160380b8162856482000034400102c0d0104c0070000b00e4421031280300d40c1414003010710030140c2c058004540c3c01da9100c0d042c0c0040700e0701822602b004011b4400c2c0308500503962030080c981a000c0741c816403c800e00a40042d0208400501c001031004192a01101d6098540c0d400c003030210780400400c0801040c10384d40f0301d060f4080000c07160865180360301d08202030903e5918050111610700580d5405000103842e11032124903064280d00903d58500d400381d000111505584840701682e101034100c4005039541d40070012300c43d4845104e146c00c640d00c450181300c0c0b464102d600a40d111054000a07001101081c0e80c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 124956393 1250 124955143 124955147
    0x8010b031932011508011a09065505090415020421060605030a020607140c09070522050609041a0907090f0509100303120b030712020f09040c060807 65
    0x2150b414441000203028600c594030b44000050740912030b0900079800d22822100d005250640514101d50141c1040240e960740d60412820034400021240140d21050811152950503003103950050480418804688003504103541e9010030030403c4030414040e08424441599491507090b0025048110500c00d44542e00541c0e00070301c01d941c441c090841017040c942290740701030040c1001c45800b0f00000c020309a510004d00d9101c440c81038009503c490b00704030f0900011002d042443d1601d5955045a8010700014007203001958103403070820125202203140c4821014410300c0400c07442000010070103051520000c2440b9000d05085a0f00c5151100d0341401c50010244501a541e00c00070020303541c038104601701030481c1045004003124242c0c10342c808134540c01c19146540c055400c900b100e81c40c1d00d2441d14101c2e081c410301110000259260580080c0c199005c010384005060510140014855a44100b241d02c4032090801c0b40614460700401c000b058a50824004460641c01c150600f590b94501c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 124957643 1250 124956393 124956473
    0xb1807050a15030e010605220204090908040509070e09131403160209010e011a07020d0f080421050c09040218040501020304020a08010911040c1808010b0319 69
    0x8059008040740400003041184030107030000c28a02614200300d01102600711a090b60045c1c003a56803c01c0750042c503100785040300901981503074002c23000181800d0b03d0749290800c0e200b40c08006c0d039003480003080520140c504890002c0c0c12400350f060501342e451447c80421113507100104036184d408010202e110030320000301010181d10700c400080d40d95501001c0d0090030255450719007a4040e082d410004034081c002c0da40e80d18180c07400106a00d090390000ca522440c41e40c00184200d81100b0042c2070080003c80c17103c14810740f24450314210340c449090410203080038170340d002c106400404010064000c0341c40032441180350b1400f51100c44040e5106d0010626420180c1c10852020076800e04100c00e002e0103602460181c2c2c802c40d801c02c210359540c0000c600b45d816040020f0031144000c403114a29280990080c2d1041c4140e007004222151101081c210401450348034a0950351150010301350303884d05111040c5100f20f500b500340e4aa1409440b0140c44160208400d0100c640e0344465107400d8060f284 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 124958893 1250 124957643 124957649
    0x4030e0a08030c0609010b09070804020d060212130302010f0b010915031806020741010e030c03041d07050f16020a0803120109061805040206070605070c050606030105040b1807 77
    0x10480b5070720009440c08564070f1038126005d104652800c0c150340d000e86050140e40c0e00841c0d40795600c59160700c0c1c603020408034007440c40e03040b034900d0303820010f440c102d00e12010b04034852401e00010200c5c10780c90f0704010b42036824840c81e211100340391140c800990780e04094840161220352102e100421040b800580040a12013100b0003500c502212410030001103070003c1c001360388103080100c104040300b03d4104541d48901a03035a43c41c002502c1450000045800d002d000d04602c60001c1900d140c0c0194490650703210007a5138020f90400141409148002d041d0005940014901e0b13021501d00030100500750301481c48541c0d0707039980008980b010115602c412860864000340010070490799000560380c0c0c1c0d84095024540e80304c6034400011070800c14032558040360014110640c46c1c40e102600c0d0030060800801c100d910500c10702c10380010411510501d807007210035072222083d0201906000e45004402000d69100741c2c10b0804010008492601642e003180f04050f0303ca5030b0304010500d0720b0134101950 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 124960143 1250 124958893 124958909
    0x150f0501030c030303141006120902101101050c040302031f0b0310061511030f07030311040803040303140304050703140f06070305010911091008060612010f0e060301021204030e0a 79
    0x40001c01405501802581202d110751010002c14100869254505c84c08403040324082201071400c201e030f5801807040038081c56540384000307202c0440c0c1c3c1c000b8581075111240d280014560010485c8100424400c0c903400490b0380e10520b013028074580c002a035910a051031b040040b00d401240c202090840e81107010304460040541c2d0b1a141c2038030988000307000307034400c81542051280d40440460b0242241c28225998403024520742030400c60600b031690700810040701059910492140035a800380060300240c00034002440d641e6186003002018091600400d0b68000d07010130500001850005500f82244d900c0003055416042d03041e0114100140c104808015000f05c404110314181e0541c8914161b50480c00f08009c00225100760b81c003203000c2e83d115550424150708003c2d03008c174043c20045034001e000522081c0f074081122500000241c0031f91018146010100c800c1c044900d03c4014140d02c03140c04c0d4021420648041a10104c001001e040901071100b5601c902010343c03a8880c0c01405000b180b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 124961393 1250 124960143 124960151
    0x1200105070806011d0d1b050a030606050a081902040f020408190c1703040b030603190501201215030f0106030308010e010815150d120e0103050c0901050403150f 71
    0x140c01502c024400c80384640052001086017100e00103902048004440183c5003109461107543d41e1070b1001203860050041c4202124001410303680c015004015500c200c5000c0760142c0381805005480701c164204060710707008180c1042c9403980c50071240100c103404580101784250482005002846140c015007828082c40b0021105c03c0550340c14050401e00c90382c0c461500555845600d90144084022190341d030300204410801d00d0002c5001d103811900060a5443e200603003450f1250b2444036231001c503030b16511001050204118200039405405004000074601600760000035840b82e070040c4282030b4014400c07d060040d4074108000002c080e13082000b007009a03160309020b8842c405c24403865240d05085000480c5281d00402c9891422020084074110b03500c80075045194260302d481314941102e0b0244c0420080f9403032085800000004d500c840782c4515001d130004007500c100402110080908100b940c6d2140d0b07000d012642243c1c0c1090820311402500221030010b00b00c4001c0311070a40f420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 124962643 1250 124961393 124961401
    0x6090501120219061403090118140705011e050d062303010e0c0315071101020d0518070302101b05060103060b0909150103030507022106070306050405010305030901200105 75
    0x40403080800c1c45000310b40030702074100c0c6501d071941d07038075294000d01d0000782c0a0b0203007a90040c91000915000500c0c4400440c1d41c03c1c200c400000d1025a000c01642c1c0110182d81c00c40c0260300511614016210070328298800034900013441040a900100c0c40040000003d903000c0001150352168020302a481d51170746000034003844240100340341c0b2200d90f100c1e500c0d28112251314140000c100300e0400340580505640c007080848104503c000800003000d019100c9018008450203200624003203c1a490020b020301340100164000c03d00900414101c0e40602c40a01c0940e03035245402200440b103140140b01039840300d80d0410103100d03440005085100d0b101c004000c005450b00721903d0b276074058030420303160f0703a40c03c0607240c0d104180300e42d10134083c50f940014404030744548020403c1c140007a00007041049402900740080a495260881030780008052040c00c03581400399000800044409006a5055446171a128814486089d06100c0e00b0089040c80c15402c0d0f4000004c105078100070803003490 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 124963893 1250 124962643 124962659
    0xb030f030c0c0108060904061d030c032812020f040f12030f05040e0402090402041107200307030c09150302091e06090c030711030903010c1707140d090606090501 71
    0x5850003000501802c810b0240c25485005154840d420003001d200054070b854840e20b00401120100c0c4d060a040d0300b421100e40001000140001b0304130070001e65544070503c0c8025508105040d43d002100040c800c060383c15a40440c42e100c444062890050355181c0e40030120585100302d40c80485203104e002c40004008014000401d000c0d8000c1d2603503401440c51a200f122203204502450b0568006030b808200075052809555601a10240000400e81c075403507210902d5030041030341154801d0f680c2c85605144a28286500c1d0350a038160002c180141c110b54800c030203040c85001d0f0001055842c0ca000841c5006e60000c40d00071070b009000090a41801d00003904040c803804005070700301c41034401040310360600e81c8a03284100a04049641983c944c00421a002060320700515140e110078004606a036800f0711070f1850f550200e03281c944003848d070b4610100c03e0100041c21f0f0301c00d03c03611401d100038071000c4c1e4003203466050440c84002502005450301e1350090034070342c21144102d4035000021034054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 124965143 1250 124963893 124963897
    0x9051201020d0c03110711031005010e180f0c090c0d1e11070c050906040f06090204060e09010e0f090102042303100504030e04180501020f210f010302010c05010b030f03 74
    0xc1608005110100c000300d400d0703003a1703918a41c00203511082001801d01007103171090004031042c801015a80d145100c81e042200342d072001c0e000b2a038507441c50018001080340500100b02450b2451020f0b254010021000989440000b146240140012000908030f10080d81c00c5807200c0703104680c2088615034108844005680b82c080b00f0603114a06042d04ea50007803c001038649089e0301211401040341070109020100b00080e00254020707803152002c403401c0903180202c001070710160000584543c5001c40080ca82080b101c00180165001c034010710941c4502d04d603242d07001c1070840d2800307403c0d110b460204d8020f02c2a03900c031400380b120a80060003054501c405420001c4021030072900010781500003042112403d40f0002d022810710003848025041640145e90120107040c0c00303124402482e2102c90999018640e01c5e50415030004548440703480180c522030748890310700c52103441e500d403c441d1030301e0018060002074144406c41089400708082504907007a031180241c01d4599010403489450351301e03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 124966393 1250 124965143 124965157
    0x3030206010605030402150c0a050a14010b0603011a0c0f0706030606120c0e01080c0d050406050403090806010f09023609240409170f04080c0d02010e09070905120102 73
    0x10302400d4000640c0c0c0744190180c80c0034980060914805010a00361000f490b44400c1e400a0903001d00718180000c80c10a100ca01c1089010b50440c800024a898005003120745220005e841048103000500c44061101c48020300e510300e00316225074890141c03296514104a000b428003007480f803c0e0000c100254181c12002c01c455154880321310300c007005008074064502501804000441d410325101303096108800c0300d80c03c40c088260442c503108030060124265802101e040d40c1082c1c96005020405501440c0f0400514180010b440342e941041c5036031b01005c400c0c0c45000682030300820702e104c10041c40c0d100c200c940c001e014003000701c01e03e480b0841a070021414000c42d102c2d43d6203000240e1015500103800400c8400015582c600c0e034602e4007000700030900c1c150265100000780c100301c0303c2004100001c05010821922440e202c030720300140b003490590036880c00d0380141004101080140d03044154402c0e00c0c00212070610040e500c0500482d441c0c11154040341d440751a000600c002e1200641c010454 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 124967643 1250 124966393 124966397
    0x2306090301110c1f0b030c01081b0403060e0708010903020303150402160f14010506030c093111040b060d021e0f12011202010807180503030a0306061101060b04050409020f06070803010303 82
    0x4210b11844c11481110740c000c100b142c064000f0800d500280d0321034025294804424842e1011881e0580d0310410706810a81046a0150740d462050054040800c0b10f40b0083c80c02c0d50003484000e807aa60025141c1c000036100c807000a104001c0c5441540d84c84d010f0300c03006043c1741d003498040d024504214040080c103900503508040380c281010441c80d03040c01010f116030130240c018042004220240045500001c240440380074a454650903550f00005540d101012000c0301d9501d56007490a06a1580d511440d1203449079252000c0d642098030758100313860455121010041c0c5540740e4041000182d1100c01c0007050744a4001240d0543d031303000c8009000380c0c1d02000380d010780507a01e80e03080d400052005880070780402c8000001414251007180b081c20001604480200090f60b5a00440d1550700301c1c4d0503580110f030f2200c00a0140031351184040c00c420b85640000d1000c00d2420560300c1d0f02c0d100d0750181c40e0050703481d20b90340000c0d034480e5605c2501064014144540da9a818241448641c00070700040300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 124968893 1250 124967643 124967683
    0xd090f060204450b03010609091a0f06040209010513090618020906030a0207020a030b07090302040c030b2b0b0103060525020d050a030b090901060801062306090301110c 74
    0x1410003400040c00004030408000401c183c407840c02091410148042d4109044d13203c08aa2190351428050f0300300a003684403001c20314080c1e03403800031460f060030f400311501c80c1c60300020086d00096445e66541c108030141e40043c0d071411440c0c0101c56038818680303030b010707140e01403500005c17148a254040c03c01c031952400c44511050384d141c0d285059101c4c41030b000e50f1050040c00815400510b950044c110300d40300401c030504030b0fa540d54075050111800c860b04e03000716a564600300305604244c000c0740c0e401d1034940b40810001d1032807400540115844a600c001401c03c0c6002500414000704090218542021100d00e10b50b82d01d161000190404035207941c4501d4000704048840d400301c0050b00741041c01e0741c000e01030301c00b08040b08980940000c020f5904042d1509002c102039140c01011078014070031080085819030070180d0300707801e4820950003401c00e213010342c049140c0d24071403040396a86004111001a45c40c07120a000901410101480710036003440020110500500051100c0505992301d419131 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 124970143 1250 124968893 124968929
    0x160806030106030506010302090a0905120a080f04021809070f090209120708070909050325020307050907050a0309080d0c090303020f0c0d0210110d030e0708060601020a080d090f060204 81
    0x241c2665010b11005005a018900500c0107103058103506a00800c1c80300005001b01c0d85884040c507008000c1c40c401e241c600b000624009850744a080c040c0d00001c0c500540c40207080c0399001c141da2044519051400413000ca01083e070000062008070020002d2040e802c0d491500c2d04103c8000703521120394a480f03103085001540b022180450143c044032843c4016004444c07411444c4006007480203011660303400100848402e000d1710400742c5020040c03021540b260f041c00d92040c1460090140c004512816034001049202c6600904803003100c090b904d40030035088000e04c0d00310041d00404c151405003a003005001444254440501400c0307074007035803c07102c0c1242d2241070180c40700c6140b0303142904003040c1041400582030055605100c1041c1b80342032840b00000750611030900030010768000000380c0301c0c208029807200c20440340020700881d1000c0c24003810010b00107540d0301402c0c00000c1c1086800b0400d2003c0320f0541d400058030030342100044e181c01c00c840c6031200080d4450300800c800d00c00511000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 124971393 1250 124970143 124970149
    0xd0b030c0d0b0601080702071805061c020a0513090f0b06150c0c060901050d05010314010b0f100305090703080a02030a12020c15060d170a03060605070f030f050d05160806 75
    0x70440103410426080250321104011141e0850040c800b000307501c0b1b0b181380041c1002d001c040140952032103880c00503a80c1402c200300300d0940d002c10b58108042d4103902d1050003603a1203004450807070704122000036440d0084000d000c00b50001040242211649008a509022082603428400d0780212000906003c80c1c0810400c60300030f000b8a5001c070381c0407064040b45802c1000050920b4203050612900f421000c0c02003806443c0e00760170413540c19001f00c80d0030581c01c000340102e054a00c0c00f2030f001a0420401c4c00803030072081e00c166101e0105501c0e4070100c0c2a5050030b00401000d03541001c060f036600d46442c1006980e0350b00c0328410b98002000c400c03509000d000e5a03c29120480ca0b03000c082e14070340680c400c10f119000380107000580c0c0406414070a00000e41072030300c072540f1510746c1280a5103500c004040074041318660303844441404001c0100360b0006440491810713095606083c5040c4100050000304c41d240191000d8002052030441444240c00d00e5912041e44051075954840b125550b0f1014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 124972643 1250 124971393 124971409
    0x708010903020c06031021150605120a0f0b18030703021507030513020d051e07031506050607080304170a0210150f09470d08071509080d0b030c 63
    0x1000c500c440704081c81321f0f00702c4105006841d00310703520150500f001500e409a0001d482c0b0000c040a59842d0300030070480c03c1000002c81c004e8140b202804100f00c0c0da0b110303280003000344c030030060100c0d070354000099074402d03668008001005520116500e0b45136600c0d010355070b80480c0c40500ba5842066000412117841781c02410304c81d44032000c52000344000799091001c80b032131800f03040700e031409010005101c81002c41c80320a0f1201c40c810080104a207941042c00081c4c0384c0081c0740d20310a0030440c082c0030603200c100444144c2540400102c0e50307603403141000313080d211100390405441c0100240c4821a168005a1105940c3d0344d441c08101c040c5a400404090030303058800c809050480b43c0c400c00010950782c3c0305440c1d10a0032008485002600f1807030740051f26002a0000c0441c02c040354041034141d0384030244500080c141c484a106a0032900c1e09025030054210042c981034141c0e500700b6039850382d5006002c1291b4442c0340d43da101c540d501a00b1001e0300e00030500901901c210b0703203894031520b44410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 124973893 1250 124972643 124972651
    0x80105010f1401030b040c050a140f0322020603040b040b0603010b031f060510050a20030f0304082106011202030f0a05040f05070b0d05070302090102070608060a080708010903020c0603 81
    0x810481c2145092000000c540c4007000560501d503a40802e00c4154581e4001c0070031034281541d4032030340d41600c10005040002c0d0a07d8512110000b84420802c4003441700460341c00003003000d48403000300c56080c0440490790196074029080344002c0280b1080060003200d03c3d0060b40320390800303102ca0340c5103800d0500322080c0400d0b0a91560180d80e42510400c041d034109401c201107404003107a05501e90020410111042d6031000000704000b8010542701d50044c2e0201418501e110392200b02154031880d00d1b0349010743c0e10f1048800d030001011508100c1c8501c02ca650041d80f0400c8080c1c08040e00100090100d000c540c00d6000c03403219200b00301038510900c04c03a03100d40400d100075030f0180c94850510005020007003040ba03001c03501c04200400320304100f2002d0010203210206981c3c403070740b4078818020b03240090a910305160050106102603a00442c4000688855191002203603030b95000040c0085229801803400703014442c80030a800c607064102c900e03824027035000c846910b0851001e114041c40200c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 124975143 1250 124973893 124973909
    0x6020a0f030503100302031e06070819020a03140709060f02160e060d02060f07060b01080105030307060f0b040c02010506031e101107060e0d020606150d1e0915050108010501 76
    0x81500d40000c0c0c0190055a0413030b1012202580c0280c5a50201e86450f81103a99100d01c546400c0c21103092450421484c4d0380b1201078508508141010b040029480401c00030410110350040f07905409544a907001041c0e50a00d04035105060a103e107014010103414002c6100041180701d644000c1400020039806641c00e1481201041b031801c030b403031107d940c4080e15255008041d07680010141c4c0d6100e000e0081e46d500c1d11a000c1d42c5100b40e00d8203a00311070340b0101c014180706c101c01c01001540d8000c0f0580d03558603003107140882d6048105455000401c0e030300089940c01490040c49444c43c9605511103403180b042a01140c01c000e2045c011040c2000b0035059880450b8000d55591480d2880360b040003184040100b90181451510303910203003175881d0450042400d502422007084040e0b810000c96800070415250700c007544813140d035620022312030350041d00d15003a00c0303042d401507880c035000071484803050181c0100b00b2600186012003040d00c00080603c41d180c1800004507040a044c443d80317040303c41d01d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 124976393 1250 124975143 124975163
    0x3090a0b13090b0d0f05010b0603041407081c0809010b120706090f0302060405060a090b04090e0d03090519050c090c040602061608040624030303020913020c06010b03101a031006020a 80
    0x2d6540c2c005403c0405c1e8212425502c52508120f20303242c601c060341c019803080307056901030b40748040020310304815940014010380c022442008044001c41c1c01c4240c100c00f80c80e000c401e03030303075000d4400d805846e202810a812200744540c80c500c450b800f14135a000d5449030342d107861509540c0e03954520600c00320b01000c3d40c071640401c0200214a40300004000d10030b003a003410102d00e0303610280c125954001d5072180300340070384595442c0d0160f03030140000382d20703a03070107040400c10540705846895480001011003140b03100c03000601c00c00d01c2401c12a061246200500342042c5141243ca41202600540310354805881510081200c205081e441c5021548d0f15a46040f5160b8071a120980504a1080180d91502e1440e440c4510600b0840c80c0344007450190700c0151344d03070200f8070a0000084010144501140c818400180b5601010407010304440b400c6070000e03181c2c1c40300a4a0010710031950f100e901004501000d08225018100140d403281c2c481e00b41c0450708603555142030ba01c4070441c0a00a0408ca00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 124977643 1250 124976393 124976419
    0x904060603090525090519060806070e06090102030f1b0d0f051c09021206010e071b021003020c0304081506060c06190213091a0d030801150203090a0b13090b 69
    0x400c0e013a1081840d400801030000941d24203105c0100c460030b640c03d0900409050741e40040c201d05000d014000c3c9102001449146404e0380d0040c000c00c034001c919071051a0000d108641d5a10809c1624950700c0c1903074034190b48480d10600d08150442103e918030460007241c2c00860480d0040c40301c0c000c8416551510761820030086548800d40d10704a98800007195500180d40260701c0380240501070150f81e000030308031541030115010075000700a100c502089030480501652172283d51411a00d140d040e40c0700460706807440001e80181c010035941c050700d840080740000d12240005902140c000c46070b642c0ca03100c3d0311410248401d0f072060b0308400c0220307801400403910100c0b4841401c2e01340e400003100141071282403103050011a2684c0d11590003540c0341c5580080110200440e2160310354100d800c80000307102030340d0180010105110b0300d13a021701041c4013010158028401c0b10081e1a00420121915841e85100c40c81c9403c40241700c0d25030710f46050040b849101da44504401d41c0c000800040210344 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 124978893 1250 124977643 124977673
    0x18030503060d0b010b0304030e0f01020a1103030d02031906050f06070f0c030501022209020406020706080a090501061502010f050103020f060d0e0d11100504321209040606030905 78
    0x30000c1e0210b504850404a000e01083c0c00b48440e41c00303003405050195590900341001801030707035201d007000e110341001420100c4c00ea800040012601d86d00c2541c0a0b00c0c0741d44440041c0c2180910704081823254000810043d00c11071350300100200c3c1104070420411961281c0a2140b48036015105a80000c0200300c445d01140e00d640b5541c501b2481501400310094590b610207003aa00f2400d80c0c003290604504905152608060304070340070340702c5e820046092a00d4502c0080d9290964414003081c059503001181d00c9500b1900000c1c0019000f0700244000c039602e2040e0061102d2181e81e020065103071102d803808405090240c181243c5e0010809070b880c0021108004465001c0d10380c210983d641c483e001d00c014013045c00080c3c41c40006444681182441c0c1040d1740c102640340c41003203440c520b0b100c20040003820b041c01c00214100d40000310900c80300000440e10a201d04084446c4083c407030506080d804040b443c000340b000841c1075070203001040e9100c46c2a020b86942290040c001c1c0c02130780c48410281 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 124980143 1250 124978893 124978897
    0x609011413061803050306011b0807080a02030c0d020c011409030c100201020c0708160e010303081f09092004060b0301032a0e090105150105071103030f04090902040e01180305 77
    0x40c002c42000403400c52590002c8070240420008601140001c010404550380210600310549021034101c1c50000d20307030b5900700c0d4600c10079030000e001e41400700c0c142030314038420001d0b1407141c0c0e03088044494417090f18002079078032002c0703075078560001d443c41c2050680884a1800d95680d020050000c00015101d8020441034540c40c40d412011594280802c407407107201046500300804d11140070b442800840c1d210040107101580120b61400c40b80801040003d42c81903815901c0304543d540140742c1c207800c07000e0242c000c00790384c0402d40503400c1402c000207104800214a001c22040c4850040e551101824401619003e10940720300a10520042000c1243c2c9203a24621031218a80c0c400f2034807429245090380b481d903400c0200001081c01c204545200f09120306900480c100442c21684120305000804074424120001c01000b1501e51510160301c040007907038021000e40040c55113541d200c400b140020000c074002070344038905000003501034580600c81c903200b008686055403e00c0949031401d440603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 124981393 1250 124980143 124980181
    0x2060a111002070b10150503130c030803010306054006200705010b04020414100c1e0201020c040506180c040302090411090609060105030109111201060c0506090114 72
    0x180180d81280c0540a00d42c4000d00550740304000d00005070502940304040801a0f400030790040030038003081250300f9000002c3c0c0380c0c4587c1d4807840b001e8000e440c2c0f5181001e08810350008141d240044004000c1040c45e810051040b4120448010300c0000b407e400080c8501103007214284110809240001090b41c91030550424001c00d4080ba00b1201c060342c0c09480e0724504001201e005012402c60304200c4203000b5200000002c903000d500345410411540c1e0022901800301e031041403d044810401e5020b829005080340c0c0240c00c0c01d0514141d0702004020000e405812401801450803011040c03800744245406094003803e0792000e451034070440c2101000252503c41600401c0c4400001030b0707526142c840c4102d1007007024a220008960a00c1300418020f03040c03034440c180300410005141d07071000c1524119094a0804104070301010080340180c810f0b03141841020b450306002058494102c0607034002d5910900071162079075103005a403801c031005c43c61104000e0300ea640114106c5201c0da0885042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 124982643 1250 124981393 124981427
    0x50c0d0c0603270f0302100b130506030a0b04030816080c12090a0602070c030b0f06150a030605030708030a0206180703030c14030304140c010c020102030f161205031009020702060a 79
    0x41c914500d0310031007002c3e24100c01212281450f180010070182d05028800032045401c0c418408041c0040010303040c4d508082450448941c0d510000726a59400c200700c819040e0802c20030702c01c50401d41001060140201c0781445640f00400c40300701c80901c1034902900c62014560303c98106031541e00b908801d0503011b44200d01034426446a040418554070080ca92988144a070b011032510310718001d05403100040200c4c4402080300c04101c070944a400445101541c0320f031580396605120501a0010441c0d60000c1e034161150420100b0320900020050000e0180c41e000c883c0780e56103040310400300010b1580c044076030f500010700800c0028050211510070511962000c43d10342c41607070480f440c6400c2103806642880b040400506924814000000ca5800c00e02c0c00c5018002c058002030360b03034403030104240344402002175407050140200f080c0c0380031603a0203a210240c4c0310450f840240181c005461411551440a50000340d6030a00d108482006901808290408903a0740c4203452403c51a01c0d6254 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 124983893 1250 124982643 124982681
    0x909030207080609010516030b130b040204150c050c0a06140309010615030b0414280209030109050a0c0801150521030a02070617130803090a1e050c0d0c0603 69
    0x2d20001c0502c81d8a22400004c4000105841c00480e032200341c0d041c11100c00e080c140b8015182c1c7d4a611100d039240031059011501140111030300000c18028800c650210000c16001e442a0280030340c4001100b01c0c1034022012140b40340d41010400010f011a032140741d02050240d001100c01e200c1174000356a100c01c010000149450340c0344005254510400b51900c00690790f400240801d113014843e08a9020f4000c84000c0145030a8400c142101e01c0d083d21314110a05010020056081e260101c4204040280080c000003d20b0310300b4603600c1154220031201582007103004101458148198525040c0a407041110945414141b03e4541c03002c0ca03000d100b4001c24080350b107094400300010300342d103045a8010141e461038010000c03c0014011360b40940784400c5801d220301d00c0214000c0081c01500603900c50f41ea80c0398080460310707010080788010100d00301c00705069401d070303240305201c1100c5001d50191517100551004006100d04603820051403500142010b0210610a600282008144040d010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 124985143 1250 124983893 124983899
    0x6090c0f0301030605041209060e0d0f02041a0a08010e150403020a02030105015013060f14060c06071803021302041e03080915090409120905030c0108010909030207 72
    0x411181e000340c100756040d5803150107010400030a0200501584c1192a06200f103505042c1e0003019000800384641c49010b400d07060380240090030040c2400140d000f0400c210303020402c950011003001d062540340c4140065940000c3c044018024000d03060f00b0f41c80508400c0003840851400183c010740300b50f046218110700680161400d01c5400c0c040c0000320581c12074070b051a1842404241d1107003c0b80c048680700c2d03c0156005007000a1407415004888410740b0b003810041c04034091100c079104494002d82424400140d881c90102c04405441ca07110140c0114203120080c003080e44500c040b03810b2244e1043d00000c510501c1900711800d4403180e61441007034140d8035000148644a0012000781d03065000404020850140002070210090110034081d803900c0e40e281c1900c14084c0c0c680c00e85c002e02d0744100c2003500020260445c0e00980d4014401c011240d038505050740307000c0805100801141110a010429140004012605410595540368140c1c00c1442c4400a080702038411020751141c12408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 124986393 1250 124985143 124985167
    0x61710180605040b1915030f0206130608100501050705030d1d010c02030306030c010c0506070f020c04061206060501050f1806040306020307053001260d02010209042306090c 76
    0x2d103004a00800d03100c161170a084405081c417002d03030050b210041d45000c4034107001115a907181e2084071b03003001b00d9804035903003400407076142e00c180c2992040000c02600b000c107400d6040030400b0b00900e41d04615002035511000107580d1031242520103803440c0d2051015081d02190740d00200d12001c82c0045c190762606c407a141c51429510041e04107400f580000c030820805050400182802080929244101071f105032034054450001400c480c3c2003050178050003413594000c01000d030300d030200544204216541d880b40742c0c60032000c03c0b0b42140d04074203144000a80758030420035a00f603007919041c440e180540e2225003551000071030115503000391080c8800400f1403520b1002c3d43c401e000680743c05649004c0079500031012020201c1d40818140c1070b00504031032500ba030300c44e503048d110101c07001c058806c3c5240c0080c00030540a41001010f109070080d2404456040d0041d01d0032401c161801e001491000d500c58030200e111906040c00300c0c5890300051202d145c1140c0c5140c01144c0c100c0020f00d030202151030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 124987643 1250 124986393 124986401
    0x3020a030807050f03060f0d14011a03062806030b040f03030e061b0901020a080a030e060a051b03060f030706030c0212090d0201210908040e0606090d02040c020c031006090617101806 80
    0x2c0f11000d40d40d030750641100c1c01c003000401e080c030bd40120041c09692078030104000e28140d10600140f030000842400010201182d441a0302640e08000e450001c1d01e01850304115141c1b0300308048000034208510440d81c8240018080d02580013450f50180380a031a03047e0154580100040724114400c14034840046000031009000c40300c0c036a03602080c00c800300d008091800c440500716020a40c5410200505901121080442d000292001965a0319244001408020042a81c6602d806013800000f0801e0300340d0b002c140200001c4e025507040d048841c20b480124052001d01d0f40e0011800e410070801136202d803030700d1180309000007040e5a5000c9503103079034001ca07184180c048900c0c00000400340701c1803092610056000d07504440c010b1070310300c201022034070707000c450341000f80600e40b01e00006000703900070b005290b802e40c03000d401c03103021080c805100030140500d840384040140c42c000c008076011000302e01041c1d00744205001060304000041206c0002c15001c001480200c5044880384001004d50007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 124988893 1250 124987643 124987673
    0x130c020c0105032d090f15010506030a020d0c0f020714010e04050c0c0708030705100603031709010e01290a060801060f020a06020c0102190503060d2003030703020a030807050f03060f0d 81
    0x50b944506150400b0454903081280c1804402036001d95042c038030b408047c06005040d06c1c419a11140c890b218505004064002d940c1c518084038100000240d59035401100b48107004010703030071551015070324211303c0d1041841c0f040060015200c99481c00080c20140c02982e0480500c1441502c0e152400300440d003092040e0b08004e10355000000c410080c464100085105074001190401c0100c2c031b1990060100d9182c1c0032003c100c44100d00001d00030050070350140c0c094801780c100034132400840310008941e003420210b8004c80840b01107441002800d01200b0341050b0b40c0141c0310680a0707420208150341071000580c8400c218421341039010002210340c0081d000b1100c00c080017580702d121904220408420b41107852081010a00c02c0000c0c0c0d59944240542c0ea40c0c100c2c41103103103a5118141d4800301408048400d40512000400608065000503250b81c094000d948001d41511098000c9a003807050055600b4032001c2440418500c1c030389600040d4040708010901038000555a59400040700c80c84 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 124990143 1250 124988893 124988971
    0x1b0a080304050d0f05090d0302070312051b010501060806062d030108010e0a0c090c020a1a01050a091406010e1201050109020405030706030207021e0a08011406130c020c010503 77
    0x40305000410008000c400c12075001424555428881d0007402000f900441150920621110240c2e009050092084101440c0c114000d048400c17900000904154021084c003036481100711601c1480010600c1000d040e101a40c3d601e0030651243d004028030b94021150b828514040407101e50380207034500700020465a100642c0399220b40c5802c1c9000e0844078103220400c900d8001044540c0081c00308000241542c07009680050ba82c0c6180d03408a2601120304802001c40e002c01d8100c0d20004c8520803600d048403006c4600307500301901c030041b03503054030a03c09030042d080d06502d021815641c0a2600181c160303401030054880301c014502c0c500d0a48000b07a10074140030341e0018040c085801d00344000c101410300b9007020b5240c000c465000c1101d0b003040104009039174103000e05600d82981e8054912004021480c000e2100d040814000007021905440862280041e54960780c2c204416005018030252560050920a01e0440c010f482c0ca030b000404544030391060740110b2140348801205404401694 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 124991393 1250 124990143 124990147
    0x14041706040209060306160f020106080109050f0d090b0706020d02090918010506010203070503040e060307030f06020d0c09081504021c05250e07030e010b04020a020c1e010c081b0a08 80
    0x282c014050030001c050402d9001e504090b040010094041c000401010800e15280700e000844031001c0f401020160401a00341d400c1c89898028050000398201800080c01c084d560300203c032420641d001802c0388a5825021014800280441d0172a80a0141ca10342d00001500c2e0061907000126070106c00c0394125090241966620302c440340901c5a80d500c90000c1c0025071521005886007660b038003803840b030300b074001c541d880016520f40c409001303002c0207560140000f00e80066926298000c2c2d04000400f18a03203241c01032410500744070310f26040840d1082c0c40034100d00b1884514000007058018016600315108038400ca940d41c0b01000c14a1030039008001412440001d03000030707007000c0d070190304406d1004118401844111701008810303400c10103904000458001d0444041c4c00f5103101c0411310380c405e1020540c8680550040360441000342c003120441c1c910300c2c460100050303040e0103100c59030000340d80720700d4080001c0c01500280400b0b10300194024400002008030b0307240001c5580221850100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 124992643 1250 124991393 124991401
    0x51204080c0708010203130803040c050d1208060a0605040b220f090f020304030e120c0409080406410903060109060e0703020c060c220b0c0c03060c030714041706 71
    0x18070030b90000d000e0140c02903207541440884c0130b41042960700c018100740b0300040410100410729001000605000d0308800440745d1b1340c206010307a101100020701c0401d0844000a00501d0165007000030307210640ca5050402d82840111200c0341c200075030110390703003010001180300c0c400d0803014940107040c0c250f005070f400741c00c0080081c01d441503503c880c190700c0e0040c000d000010f508072441342074050f41694601c5800b5440d003852031800c2541e90000d60000c1ca002e41010a00009600601c203036401c9440320380a10090220b6084a04003c4800c1620301031000e00050013840401020990030b0344e407100142c00e05108500007420588203a001c180b8096541408010011540c446c041d4010410b040446c01c04000104050701d0300c20040000c01070240004d06401070746034100c0c0820007010411202114a600c0d19000c13540c1c0d44c442ca10b1040d840c0304102c0b800c40300380f6000800ca4465904500000d00b991a01d00b0f0070b075003075250b00c088207009160138400030641030090104d500809030080c3c01010503080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 124993893 1250 124992643 124992667
    0x1e0109020a020c1323010302130c050706020f070b06180f100306060806010e1003050c0f0418110a050d1703060a0e0f040c090507020303070c022d19080d0f05120408 72
    0x2038541541d014403401000400c00340e554107040080c4540f0100d0700ac6850134541d6021241840f952000900d514804520020103070501d1028103030b40c5126544e403111f40d071110010000d617107a0b1040350903100c001842c005546210340c428040d030400300c501c14800d50252a40d1380c01d400d448140d0400b90b0184d10080040040d500e240d6a6140c01215080f0025141820354580c02e0312001150312450245004008100850300e8036842180d189042180031100d2104a00d042c0c550300600c10001481858201008642850440d4500c0c0700194059600000c406098000302d240e138000810300380e1b004010300d0001510303810305172074584950b018060a620b00d240074a000414400315400c0000c165213020100040c450300003046039082199802e2000401650b0b00c002454800380a80025091042e15107003d21303140780e440c44166001c01204c40c448001c0c1403408002c00c1032614440c0303445a0740b1040203540d5140c004c200e58142010140707001e6242508042c22480706d510103807400c0300c24500000f46030340450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 124995143 1250 124993893 124993931
    0xb030d080f100807060e06040e0906070201050703290307030204050103080a090b090105070b040f080c0c03011b1e020a06020a092909040b1305040b0603061e0109020a020c13 76
    0x4407441c42c424501e41401c2d001e03a954582070066809020081a0a030a07070b58a840c1600c0c002c2409244c1c003207103031412124103616614280c50b600302642c00d00d80401c6100340139005d160910084c041107901d10100d0500350241554208486a4141c06440400b20140e126402614040c3d0700581d4460b03a04c25109100620082e0360303a00c00718400c0000d0100842981c1d00404841041e0b802c0540384e00c550b21681081220a8661140240101000030f91656005000701c2c240c1030502c0200d00130070403030321003401081d0611070040e60400080c0d00701c040b400c030120401010040070811031044910a26541d80e40c04200d03400052078401044081d1030410142280307508036034120215580e201c0400c4a100c4c10bc01c018003801c1109881561915400303136068907140007400c00c0300e64024080c0300b03500746420042c3d1092415240e60f4000d006000c001114401420365418078042d0341180c103019070303182080368802900808a0b5004601031000c0c2203045688210484494180079103001401000071840c00105e5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 124996393 1250 124995143 124995151
    0x302040e15030307150f150504060f05030c1c050607020a12230d140408040519030803060607061409070f082b02030403021909271101030b030d080f 65
    0x141e00c916864541510044161501d4562001c13481e6500c070703860840440901104031046d1b070310900d4008002c007903a848003050012507005407030802c505500c40c540044801a94010315806a02040103c1c91604244c2042580c16250f855002d691484135500c441c01d00e80240c80c03840040e4011140700c02800300301c00d101c0089080078140050340e41c0e24507c81092003190342d40c0b5480d00c1200807910701e000050b01d4015030703540840c0289115051905203810f170310b80d40081c040d20740101a210707608242c80080506c40c4098a8000c01000d00355542d5800704022030703206940489000303407181001a00d0307009903400e440c0a021440b000d005107601b0003001e440c100800b5441510380b42d0000840c05000e40504002c40c030304800451398155500300640080c2d2075442150300c000e411141c00f41c1003140c2d0014110303204050b1420741205106080d9041900d003903101810205481c0c00140c5a920300c0042c081c0201342440000604010030700d8209140021305140c10f40880c10003080b0300f8002c0003900303e8429440360740 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 124997643 1250 124996393 124996411
    0x50c060702030d0c11030102040801020c061003080f130f03060e0105070513030f1b15030f0504020f010c051005011508090d050301151e0f120b060910030207050d0302040e 75
    0x1821201e0700001d82e54140c0740881c0040c0840c40035042c00344000c03401510510030014000307565590b0359801040c000e505c60250b202c050300481001c82c1c0d07801030302884241200d801410250410011488000c16584050821448101e00c070b20002650320502840714000c600500e40050080100703000103007507070801445c4108000041049003c0381c031028400d4400d8030b4000000c0c420394800d6241250240c03c203034210702d4286410302c0001a8001156210020120309070341d041c042a201d00b800031007540c02c10303a0000d5100303069441c0010715502c00c07495040154000c0701113492410441492408a035401c1e00f01d0354400070384000801c01250401416604418101d0003880c08d407008540061050006008095015224038140203040c1d00c03500300c00f100036500e441d610351303441104000a0090b200080d03075007012400160308013290381a02d20500e0195107000e00568904038900c1b0800144c0e2180422003828541c0c04e120602c0424010498401d800d041c0b034400603540d0b401d01080d200d105c0750040880d50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 124998893 1250 124997643 124997647
    0x11010216062f160203031c060602070b070b01050d0f020904060209011412010e060111060c0405011202030609041401060b03040b0603010b09091b0f030d080109110a1d0411030c07050c06 81
    0x40200280003100c02e440c0c403c0b503100b845812280300003030651264841103402440704d4001081c1421096000c2da08841940d02201c5c40d040c0e680309100203600544201402d6400c003240104018181740d125404464880c031405820180654002540008107542c01e0390507941c0032402c0822540c00c50a0240c007020403180c01810112680f044030320030700c0c0500501500c0c00044010841c181d003da4005920b646509042c0e07029480e00500411460b0000d20400e03000460801c1000e40304c0e0898402c42e401800013501c44561513907661182846441c0014410080d5907071b4100c0010241000000b85000780d04c14941680b150070404209400c1d00c154410491060a0000a108103e17000040045604440c4000030f51001841000601060707480d146483e0940108015440b02652125040d07050300c40201c41003044d6110540c0000b00341c090406000d02050b0881d005000e00448640340c49a640c4004001280d04551a041922903030802d0710526254a00403e0a10030461706111001204c0000d9440034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 125000000 1107 124998893 124998971
    0x51e0625060b0409050607081f290309030a0e0d0c0801050a051602030d020d0615020703050706030903080105090405010e0f030403170f07031101021606 67
    0x480c0c181d842c0140e0848140380911513648510340060050483e541c0e40030040d100b4181c083d0050041d0381a150000c401841c070490040e010380b0320b810403800020f01103031442c00d201d440140465149a414020060001030000c190341c0b9030900791a0441a4104c044045000400da01c2c901409207510000003048018054200500604841d801006242d80b040d03111000301c560081c159005030820059580c200e4a00d8001d03201c0003040040011305150307500e200795503d101c40c1c0401e00c00368122240c02c2040c001d00340003060080c642800c042c410744206680080018030140a26449610740f1000b18090000940c8201d1244171504205c0c0e101c2044080c02035901c2d017040c841217500804298422141d03007040c800752072550004c488440d04241b46a54283c4100c100c0450480032507609000315440f40c0c068500300b01d07205006010000d2900f110350002a030429402091081c9081095050 = true := by decide +kernel

theorem cover : BRFrame.Cov 124820143 125000000 := by
  have h0 := BRFrame.cov_init 124820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 124820143 ≤ n) (h2 : n < 125000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
