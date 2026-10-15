-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4385
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:27:11.155138+00:00
-- url     : https://prove2.me/submissions/1680d003-143f-456e-9fca-dfd43616c83f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 788489208 ≤ n < 788669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 788490458 1250 788489208 788489231
    0x5070303030e03040e0901140603010b18061201020d02030406050705160b07110307060902041a0a0b2a15280c0918090b06041817040f0303170c03060310 67
    0x2144629400898020703034401c00d000b501d006c1074100c00444040d0121800071600c45108250889a102e8061903101f5140b5141601e00300d10440c3d142d81c45a4020b04559540c0c0d2008080e900307a03030005c44542c1c034295000007000200450380c4a840d400c00c2d5203141107810404004420720420f860110050130424000c40058511440342c540c070322810007542d06594880340b151410710b0141480b01c034100d00c5141045280036494410510480700c8000082c58240e40d281307084500240c5601241462211400701301495141d10b11000b038003480383d40d24800820b240c403458107a6201e141805800e000704007984440301c40351001c413014841c4400c400d4040018118020600990304800c03e94462180c024082007112034680f03460f40075142c0a800f803080240c0c180c0e103560801048031420100202c142d60142056000b09005080f81c81c0e000c3c5000d116146400d8031001c0400a003510369004800141c41c0e08850f044240380070340c4254010a020003843d046080040000ba02d881d40d00306d8102c4030300d40c0d0701009040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 788491708 1250 788490458 788490463
    0x3040b090703140f01060509060d1e0615060f080403081f030c080c01030e0c0315040303020730030605030c0d0305040906140a060f1218051506130905070303030e 71
    0x2c59028403401020844000059210350403075015245551030020b001405091076210130348220401031010b003d072041680c0300700c1480442d002d1051140d882d12042800a1110b104807044820042c024051003858504001c01e45001410b003c0d04201d00c180910001a0300401c000e034004116203c002501d40e01c082d403401c4014166400030381401c01c043c20026500300041052400c040d402e907014000000705c10080b5988212a09810f600366000440c01c1c00404204140b441c3c015200e4030b400741c0b070091980c41d0f13000d503002d6440741244041c190440350a800c00c0b46200e4180c100106003428844a49030600007070303d07203d404001c1c40c02403551003540810517102d2001c98001d00151041084826101c064201c002406070850030700a000e00000030601900444140b25006055136481180142960021000d407100e0011000b0140c42c4134146400543c051101d4004190200c5059120385000400c004450f6450141d5041651134440750501241000c1030307880c1900c0e0181004541c1018140d04140b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 788492958 1250 788491708 788491723
    0x7080703020c030d18060806030a0605090a2a0e13080928050f0607080a0507020f03010c020a020415030c05040b030312090a0b0c16030f0302040b041e081203040b09 72
    0x81d40f50140040c0c0302105a004110200c00c440101000780f400c5484402c1601c1451064403429450780c020540d000c0014441d410459000c1007a4042da80400d1250340d5000c58041f140f80080498a8403071040340d082c0d244618108001c1c910848004407904003011400c02e03218890401802400700040d40c1c00f0251550030303601840b0340c46940300f1020040aa011001800780c0c90145d24484c4640c075460750302c5890181e05a518a9400ca01014503100d007010301a241d540c0b0102c1c0480e00144c01141c41e071103d640c01e1247d800465500e030081c1080c00c81900c1007000700d13201a0066403c0480308007040c0003050344510504103946051740c001808030441d00029155019104800e20038102c07410070403c0000740880e140904074401c074000015038407980303803808103405416515000d84110100c81c0d030110703128800c1800859440d0800510b8961500712017241a4000e80001c0c18001c5000601401030b401507014000804100015103400305090110014030b01c00035201a04500d07001002c0b40c03201c0d07003c1c491074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 788494208 1250 788492958 788492983
    0xd0f02090d050a1205070213150b2d18090408073207050d030f14031302011101050709121406011701050603011a01121503111507080708070302 63
    0x1400340c6840c90216aa40303c599001c8468081045541841a0141c4142c502581d0300815008000d0718180d21f510083c9440c280d00d64000c503140200042010070100100303003c90481714803501c6ca004060003407110700f071450700d84407403410104a11880c55503040c101595a0b8002c991f600165207850070031904900441c0f4000c3d0409450800c80084155403000d2403800c050406070704005d000d03c1c803100c10703291347d90781c4030761a04410b802c40244c001a22401303c817111103080741441d1440c2520b1203540e10407500200c0318511802c0c4901600c070103540e040048020008400e10003880f9514154000800071251841002c1681c0c155001c950100001528103410b0b14458104480084d0380d61104554540030100015445510f0300d8003013582c605060003603040700300d0030310f6004034a00d920b0401110265640b8a5100507680e0b282d0402440f407500801940096000710890b0804030080ca0070801c0c0f01d0070708840d201001c04104015070001d1b40d054152240f690700030001544450032400d090f403c0c00c0031040c20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 788495458 1250 788494208 788494219
    0xc0e03070e0c0a092c0f1b2503180b1c0203070c050d0201020307090803070506061309050a1b06051c02070c05041404050705040204050f040218030312041e080d0f0209 73
    0x44d2a101084500c3c01180301e851004040a1707444040c0c6e668a00b800c1030ba0300000b4010850009100c100c99080104003088004061003108481e441041c1c8a0340c01440e01180059003034407080d8101c450421024000d404e56110140c075104c55281c02c8200c5e0740180360301c0200c02ea004400980e0042c003c1c0d41ca11003040e0840b007a00d01078542108024000d6004907041d01c04201c1e03581c0c1c0032400c04c00000c00e45540950050044c6000e80322941000b000b9500c280301e22801c9916501d0f4103000410034405214400c1c8104110880a4400c04481c090400541c1114080141c2071102c4000084611030254000c01036810050340c2e000325041540c03204100360007698009080014130f40b241030350010003611441c000d03000d940c80d8548407400c00c401c0c0c0c4242d1052a034011040d00310304200340b50a6009000606181e070702d1400300c00c1c412021070304540002c2e603045000ca4881c0b08100030f001c41e803100b600103441c10580105000d0072554640220740a40300f07200500703540c1c42d44946100d014a0381180c40b030070b80080c075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 788496708 1250 788495458 788495489
    0xf030e10110c120309070603060302030a0308061c060b03121e030c0d2c03090d081b0a050a030201200307030c0e0406090903020f0c150c0a12030c0e03070e0c0a09 71
    0x80400f000d0340300b951148110b00c103038100094203078424070403101078079802000b5040d18005520211564600035026951140e03403071104000030450b8036a41480d1621030100401d6140d0f00300101400d20340300701301d01c1079040010088507407116651041032001030720004071280c0725140c100c801203c5000702a00d241407140352000c00b000445200d80603040c904081d0200c45d0940060040d401e849014030358004d40c010180168040018400700090b14110821845003200e0310900700201d071802c103e2003415101071308900c84800506a0a0280c40c0320454401c415180c010140e461030b00c1e00e4031005200c0c008069075516401400d512a014a40302d6400080c824004142c42c0e007451002000c41d4903044005d0b1050306a070080130800400c928103107010080c10303840c100c60302c40c2c3d00010541c031040e481192402840c2c0c3c1603000400e1200e0150031486c5640c2c1c0084c809d40f0410001d0855400c2d040e02e10b121354002e05040140d20500340849600c050003c270030f241c88941415059419810b5500420707aa861201c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 788497958 1250 788496708 788496733
    0x304110604420c0303020903011b0809030913091a0903190809060402240310090506030f0a032a1505010b13061409130b010f030e10110c 60
    0x1241007511100c1000c60b64400d400304103642800c2824050000501c03003025031080b0040c0a20410b902c043e0190034007624000d40070340002d0171101803110041c0c8403000c26404d0340c05103074031003645680411a84029464090300070000f800800000d42c603480207541b03c02d0554104209a285030f1000080ca2000d0041400c003900000e80f66000900d4501100c0d0b03290014520b814170131800580603642503405050140c40d1602070081d070b142107124150315254004640402e110b01d0100652040c0e03103554200036114100f0002206448028012520a5205244088202c0b030082010113010754541801b546402d8070707000244819920710900320450216040f843e050103200c0410300d2243c006031004001582e22010004880d000d060440e104110425405111700c80c00344c01c04501400518030340c04e0414501c0000690300c0152a11195003064980c4a1420f155030400f0600714a202681424010002885841c0740d031250103140105000340c0340c1001c4008102c644084802608468040d14801201d16 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 788499208 1250 788497958 788497979
    0x1306091404061a090c0d0908040803091008010302031e12120621030a0c080d1b080a0c210e0307080a09060203030f0f15040e010c09090603020906060304110604 70
    0x880d02074481504140707144044034014160705103006801800740c501c4c3c1c0c5540e40780c1085600300c0c0c0d64410f0b001d85d84803903050100c0d2142d00640018890903004540d02c0c403003141401626018000240203100c8050018401aa40420215681c21036030038003210f103078000040e8a1615030043c00c0360422910005a00301c41084800c029880350209a6486085d88022210941011948811020035420510607000035522988500c000203000340c1e8407900303140c800c1c24408225581035400c007040d03070100054416a56085100180e208125090400c00c3c58070211000d41100e144446c02c1d00d070300d0101d00c042c20001480d82e10200f11040d030b62003120740381c1810385840c511a03031210240b5030104d800c80600088007440001224420940030a0080c05038440050b810b40703014019041d1403039550104940021a00c5500c209074080c2c2a00c00081241d00c0b0304c090281c400d0019402562140d03007085400d2016845200a003074004100740e407500ea6942e03c60500082c01130844514651281d000500003070004540e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 788500458 1250 788499208 788499211
    0x30f06094903271e08040e0907050405010b0d1505061c0e030a0c0b0f0105180919050601061107030c03030c08041d0613053612030714130513060914 65
    0x40c8084c9140f56103c04080c0e03114404020000c0802904010501100c919151400c0d00000403004581c50035071640d0014081e130b01c00341c00c1250621008a06a00400214054854409186074403c101c0034140f202140091203502d0120b041d1800c008252803801c001c548c0000024104041980d40b00c840205004085078081d4605a0b0b201200c10003007120f41072001b000d24101c8400404011030010700c024030020f50070000b080d07204140038500e0605407200b4542c10b078002d05031140c40503150790b47c100344000e05241500d61b616180d9a00c03008003030000a001d5a002000d6a03054180316000440ca40b03001071062180e0b80080b03080600e04001c00403000845000030b03004181c1115891000a400e80500b012110100c41c817110910b0003d012119100f0840d0300580310602e07400c0440c41c00d41400c08614500540004140000400081003021190740328815a6048909030036a91611b40c040200c00211001400307803d10440c0d1a410f501c1d800c42c1c003680140014844890244120458414495030300c210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 788501708 1250 788500458 788500463
    0x12030601111f0c0914090c0909130b070c030806060304080c03070606180b011d0102100e0615010c020a152f01050c03130b0402030f0609490327 63
    0x400281e203e00500507204201554007103e500100b80d0b84603810001a01c0024090300000d000400195601d9111321001a104800c001da0086004c5850325082c4c0d103013800200810b0800408400d490002984258070b0390300603408403046d03174032522139041580c014071032801510385511002450f4001c2220503049038044407147d05103183c410440c00035103000d8442c405a05070004160b074000140e10005080d1403600c0302c006104960460102c002600c04587c00300030035043c240d000c082001040704000e000310854120a10300301490032519400b00e01d000c0d00c1806941c55441100030b4615015120b140407220341c400829840314258084000448500d0b0301c0c4464041c2542044002241400f400f01120301507a1017030701105030018a80c0700c000c41c07060060400c0b641401014540d004c20502082050300450700f44000d400c0c901d040b0307550f903024515034150b4403454605130080b20000d4002044044007415641702034070700042c01003204030010061074032007101518031a1021a044162000014090391 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 788502958 1250 788501708 788501711
    0x3040b0d020c331e0c0c100c0509090901180b13080301033905040209220b031902090103020411070c0603050105190f0620060405010504020f01050a0212030601111f 72
    0x40f0340c0c0c990007030301e004c1241048801000710300c041080744100700c0003484506c1c1001d05590802403480031803030aa03a050f005040c0000c1c3c0c04039403004189410182d0b150814400d038020014040d440207021030300711080c007000c1e00c60b80342c05001500c0700303185c00400d01c141d42d4845140c556940e104c0c039020595000b0407080340d4103290f0302c01ca960710301c07804106440d49004120741442c010605d8507042001a40c4640307400c07a041041a51100342070074030161b80c440c0401d5401c2005c200c0184840501d49495180305040d0301c0d407190240c940002d0384030000001d040d2038041d200420b0a041d1105407642d584038502004000790360030f03d4006082680b540c400350584d00c044038646030780c80d41c035009a960b5007468041c00010354000c1c04100061400345034881102c00c40700003101020750ba0620303144c0c02d01d40c04440541c2c40c0d075101c3c0104003c51401d003501c900422402d00300b081c106580303000000c0d50351401221881000d82c0020101d003003607024540a4050b0002142140c50b1140754030801505009508654032449 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 788504208 1250 788502958 788502961
    0x150609070c06050c04050d0f050f06240a0b0a1206060c21030b0303070b0103020307061e030b0102010b030307050718110a050d0906060e1803040b0d020c33 68
    0xa14014a60500401907907454203411980c94407041c0c01004060440241e1303000802000440e600c0b071010303402e0b0040c003070002d1440c01450703030a105040c1440c1162035600d6400480c10005c101480390001000080256031802a0148407004034052280c65001007034505800301d01d6503c041d40c8400d00c0074540202d10400d01c00c455465070b0070740d519507003410000c0608501c03420070441036a006040700908020b41c6004140e0b48180c0300481d003958007504090390000d10030401032081d41802c00c1440000c0c80702d071800c450340c03813200030006c10181010130b40c0c10100340d103500c02192168400d41191070b00c0a40101035903911811031901a039210700611030100d4a00c400f4460b800180390382d00c90782c14005a0205c13801d2900103080800c5070103a000c018102d00b020f039525818808a82c10740f0408010f407040c0c150b48046802c218041c1c94103400d40080e1880d8540c401c00c403c2c0700e16001e0f175007a16000c0d403905201684413a655801c0b50306150f1000145034024082041c00e0b51540010144800905040c00c07400486 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 788505458 1250 788504208 788504221
    0x2070609110616060203041112030a0905100e0409110402030c091512070c0311070b091201060f180605030d0c120f02150601030f0e1f0203160503090a06050915 70
    0x1406031030f012401c100102c1c2800c1012070b1883d001903622600c503c8950148075a42c00001c1c100301103185002d9a59800880c8409a558004185e08007400084540c494090030916005201900c20403090380910b84035841c600400040401403031914000070802c3d501c1c0d2400c0f030081545604810b0f0400c1c850040e400c0115a0314102104842c2c010700400c100040540d103008050325800e81c5030a0403010404140340194800100307100e040054010040560b130f80305074560400c51080d4890161043c5645855420420001c2d0445030742c04450340150340401801c00030030040c004007129444650103000c3c030800700c103449502500300130348984180a09490000d4001084800040011911015a1021089070303001101c2000c56a800700052402282d0844400c3c03280b03095a00d01c46a105507680420f001c40255101c0b443d01030003010000d0011030071884c10000505412003182076100071300000001140c00c0c4c9500b48080403115800100522680c10f00140c1c6568412101610b4030801c1c03010800b1904 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 788506708 1250 788505458 788505469
    0x3110c100f0f1403040f080403051002032410273f0201030513060e0a020126310506010e0a1407080c09040e060a060902030105100c02130207060911 65
    0xc184081840050031650740342c4d06c2044400d00b102c01502c901d0404d020010002d00100010506a599044013586a0034503065404041c201341010820802401900c040f13a038076903010b114031031702107442c00b803040e8001d804001d10480c040000e1000122084c54011a500540ac01d10348040c60110144100b10036040441c02034400040c158400048503074501c0f0000342d84139400054000c0811a0a81500d844c05c0c2d071303020226007000f940000c2d00d4224022030302c15581c00c01203440b000340e0700c0400303080c240d40302d882c402558200c0201181400c180c09020303481e45041c10320a84403100c4401d2245c1c01e00620500b4019a00c100034810850461812000140c030840107001d040d482c0d02d40c0307034180640e903259280191400f09004001862241042c09000404d03995030180c03884540c2600080c05a0b407c050710319a06440e89c5412145920340100010002c0343c07107802400d85004141d21342030031401110f10000c0c00c0d1074150006051280d0010039824240207c96000c048450301c2401344203040305c040e005014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 788507958 1250 788506708 788506727
    0x60305060310050604060519080d030e033a0e070512030409110f0c07090b03031801030518061003231e03130b030105010f0804020a0b07080d020d0b0108012103110c100f0f 75
    0x1200d9003052244801250380100c04890243c801c3b14142c003000030b50950700c40600c805c0840e82c14200e89514042d0504141400031001030035065031030312a40760380024425030324441e62180902c906e80e2060804d01c201e0102096034110010784030300680c0c440c0d140d2801540d50455018159130a4540316148582c1d01d80001110400c0300c0c180120380096024100560080c240106584050803040c621030701c1903802808140d10035046094000c00240c1941000030391810841c80003024941000000c0401d41d100144000c0c081701d6104400303901c0ea82c00c0054a00f140607480e03100706260741e03004000c41c03000d5004014506075282a0785032800d40d001d80360200c40d2401d0594002e508980e1419043c04030182c03000042c030a450003024114a0a105080410101d91144200480352640c1d84810101c5681c4142d145005041c50000c04c1c0481c1541c3c0400ac03000c00c24000c0c02824054540200200e031b200501402016190041200317480c8801c100002e0300c101c0919181400194108450100460080401c0d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 788509208 1250 788507958 788507981
    0x30901090b1201180b100f03061d04080a0c0515060111011b050a02030915040609050d121b02090f07080108030a0c08090d0506130c060305060310050604060519080d03 73
    0x1c01c0b503440d00b00d881d9184090f090340f06103000e8507018280e44644a03603100380050141030b070324074000c107010400050898005411132015a141d0900c139402a5000524882e0400d030030020242d980c101d110019119000c01e0350006000f0b000d1000c0e580b1601510500c601d120b0342003030300c0c3e10302d510841e0f007a102d003201d009414000ca40c080c500d06446041d4420700141058203070780d004a0b403a00703000c540091040001900c8441c02080c0000d0180b240d83c0e8040760310402014251404c4010111545c0c0d001034016042c0000c0041080078941000d8024401c3c0d20072401640240c21034903d030400001d0069141400c5030502d0224030b40100029000c07000008944a646181d51015031a010302c1e5501086139001d602d0040c1c0c004070302000b000c0412005d004003130042c070f090060144074028a140c408080391003070380500c042c1803616081103c1601c010405210450041e440000c0b580d9038a80064014010f03900055005030b2800c04580c40d06c149901d100d401d48040b00100c40105200076403c505131800d403a10b1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 788510458 1250 788509208 788509237
    0x170309090a0614101d0316141507030909021303060908090916021b1908030c0106090606050a030e0a050111070c050a061715040f0b091038070302030901090b 69
    0x10038a171024030381e1158002c0b0001020764103489030359110510240c0c601d401c21140041150309400d141e1406405660201d00b0391041035040c040141c42c0038200d1040d40c4140d059150300054003641500d6680704810107958046010800400f4a05103481143c01000d4818000c002d49004242961180e509100c9035a12560080928100109400c40c240040c0301102d038209031440e55501c00e0084a040c0a0090300707a82c4010358460208041403800c1d61884d40c0880c11881c134050062250540c410200c420030015801d01042d04541c1c21403080c60100c1d0090b000c0c001d54684512100d0b00d1071080002c081040c05191282c502c0d540321800c0200c808804c0c03103454042540c060305203100881541d1656846a000b108919105658402260566900c40c905005d025034030409004a49041c2e08240e8200074401e008040b424141011000b070500c4511840c417107078442490703403a00b4600f07124403102c0840e5807d81d840c0c0c41d20760500d400303507030380d0030000b1002e0116000400204510740d184040d2001b03007030741c0f041d07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 788511708 1250 788510458 788510477
    0x240305030a0e0f0301090f1208010b09060304051908040521030301090b0a031e0c0605030609060613080a0605010e2503020703090e070f0f0e0a170309090a061410 71
    0x800b80e500b04500c818258102141c60b4058046076820f109102d10320703008940f1000880c04030b207016038101c81030710913560a0100000042c400d0030400410b4800c900b2055604940e6902c69007401880e050764181c8256858000461100401400c14090000c450041d074400c49902086814103080148401014449610600041050080a42060501d9840608400710035078507501c0c2d041403518140c401809900401e001c541c10801c440c4510002014149001415401c200c6c00050181e10041e008138894100414051041c00301c00d000d200003000080121800715840d403034048081c201c2445641c030604040e800040c60000c0d020303000f801420281a00c244914a200815802904041403d40c2000b160110200f41360300442491070080625071162080c0c0b003010000201185094070288040041c011400700d210303210500d0320720540c2c3da0041540d80d01d00201c0c80ea28514000d80c501e0035400080b540a000e9007080303a031b100c070040d2080d0442c1c40507811421005c0c481100008502c28000a41610 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 788512958 1250 788511708 788511727
    0xa05010e150708030106090608070314040b04020114120405010e061306020f09090f090c1e130e0a0c1a090618010c0602030901140603060408190e1324030503 69
    0x39030301c64031605024000c90610100e500c0d049801d8000360060400709140030710520016800c50b0380d49900040301d16040c0071000360100016406103011748010311507010640480c00310f80c09186e146a403800521070766602d40408040d14105014141c40c141c42c0c5519200645680500100b03441c0c1c410084180c4030810f800032a40e03250025801300684510310001804074005943d51941c42c28015038040c401c10207141441d00903141411142c0d6981c81c8500403c064074005400c244134405801b24045441141c11620102d20201a00c40046401c25038021081130100300070945130820141d54400100000f49007603900b000801d44500f10045134031a0f024000011040341e2903911090310035040c50b1812044203599654026604113581c03002c210394407031007010301154070b40c0c02c41c40c0c0c401c40440c020000c504007600d40e03115074400c00d2501c5d0907d02400c00f0404a59003c1c5250b81c443c0200504030840c13050140e8165002419100b050000c0108015083c10b90980c00b11400c1301034a4200c40550f26064102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 788514208 1250 788512958 788512969
    0x80f070f080417040f1701060f140105210702062a160f061b02030906070305030402030a0804060804030806010c0c090b13061403060108060f072d0207090501050a05010e 74
    0x14001c0b110f0f143d03152103841280c581d90000d007004050b0030528001d020300b003030070300696030a60a10441c01c607850103d0801030308902405c8003046030050340c80c8424184004004a842d84181031004265145001000d4980c0040d0703520588502902d50a69225840e00001c4000c0c17807480381d40415114135004080c18500384c400c00280741c080c0c0c100c40c1803600f01d2810350b980000c5840040080c2d9450355108250003034501030315090700c0440c0c0c85101441c68240d0002c0016101d000308940501082400700005007152001c1180c500e50680010840c1d840f82ea903048020710301c8030200c2c3c0840001c2d8001012031519401519003420141d40017010003502c0c1c3c28501044024401d405403a60312000c0640b10f43d151504c0380c031444002c1d02d003810342c8001400e080802d051500e030701a400003006901c10420021418000740090f6045091490000e0014070904054000c0000c00c410003282a142c40b24030702c00c503980001d102d4086405912080c800c60b83e9640070003403480a284142800316088000780300385850316 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 788515458 1250 788514208 788514211
    0x50c12070609150903140f0d050c0312180f061512030d090507050d062004050d0b070e100f0e060a020a06051003060212010807050a0f0512010f05090c01080f070f08 72
    0x151915004c40c030781d240c60381c04294820b4806441c0ca5007110b07061410002c0180111283c0da4a1070415a291010281100e87d0760b1140504540300a40c0407804100304054641c0c82c000460000c40444d004250340b241040d0711654203603210031038000400041d0f2036505100d120f5480941c2140003840c14844141d280300060904060200e031b0f54010500c0106d11503507141440c0340100d02034140011151141c010f030b0b110680c802030604050719001d00c02001940d556808128855502205040c080d486090302a01c030301d034001130052342c0007038105200c040141d07010101d0842c040d20755443d05184403441d0244904d41c07003209104401078000781f202401050340c46d007100303800022118600540e6903480d01c1d900102d0300f24010769245181082e00401643c00b080080c5006400c0880e00610454a003000000a81c1003a200e280d00511000c1e003962101c203000e6006280e0041030b02c500303000f41d240c000f03107807600c0301c014410b500e0208145401140c0000d81114695119060307503110301a0040040c94140c3e44040c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 788516708 1250 788515458 788515499
    0x60301120f140709050a1a0118090903030b0414091911032e0204050d0b06180a06180b0310091511030a0e0d02061b16050c12070609 58
    0x2034080c00100050072080815020040d4880540003113810105680240c48014124001c542d00b130071032560b00501c03850f06250826400b424a5001482083c05008105155a02400480f4501107460062603050b8000c1000d148040703808216021449200001c40c200554004115034403c1c106013001c04100c140c140d40c282d0244a5010580c60b4400020349010341800d0030303c0040c010046517901c11020aa0144101c015480e0306500705410a804154201e040d0318002d044814020301240b02c6890b180100601c103844448000341034a405818003010b17162030302c00e1281803031004280d0080350105104005907108028007030034a5803d040300c03540280c00346d20740650301c94560000c800300c0d440d050f21442c0c40d0112030345030194882c41d00d0070b04402111800650500c0c1034011030726940000380d0114486030b008040340302c0b001001140c1094a1020b0094040c812420349458a014040c44800580420580000ca41201822110f034414a449901ca0b201d02c0011a42c031082c14011035454583c46200402d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 788517958 1250 788516708 788516723
    0x50c040e010b121e24130c0210060e04080304080417010501050102060f01030b040b091e010902040b0d0507120f0210033806030a0e121201090b06030112 67
    0x64803403000c0e8540440c00c2e40202060040061520300e9400d400c850349a001211402c12403890403007804980c00d40c5002000e0092400c20010445a21aa4041c2682c01324201500340700c0d0852540008900806a0703590001c09445140e040d04549240380c001c81c001d464088465914985482e541c2d2003850300054003c0f200c8140501000c10030401c1c25000c140c0084d41d4200109695140900190030440d020f00851041e0b80c1000041c0045118081c080d41c00c15071180000321550746184907030b41000d182c5150f0440160140b440c03125001d4054015415080c0211001c221102d0350004020400e0741800008104ea0000401004810745029180d80c881d40102d0184054a203980e000861030035108038000c010075958501d2080a20741c034900c40f0101991808580360246403160614a900c8801b56003501c1010004001082c0ca4000d41002081c1c03100b0108890040a0341c072402c041c0743d0880e60700825021103013800060b00b0825030085011445011340103070b15590814220120403040071200b80d4202 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 788519208 1250 788517958 788517967
    0x20d0e03030408031204291906150f030f020c0c09130f0b010e060f0916090b0301030501240e160e030706030f0b010c021c212a030f03050c 61
    0x10f1800744010500340c01c0d00303440300740c6a19045c0b400a0341702200103010503002d0b980402c0001e4404942c0f072200c4c1c01c40601c004000c0c41000307080025000d00750036000395041c40103010380803201c6608030480214443c4940c9060100c0105602070000f03d0041004004039036114000b00340e801e040c401c260942103550660004400045900c80350745007078462404a41c040714010042001300306071070f40982c0140003201d241e50040b021800081d45a003026206404586907600070500702da0044204130b004040310900c0684a60b540d00301a802810381c41d03079110400b1444594070502603400c0007101d003610082c001002c0d06458243c40d000a440c51035114100f0b00644140400c2541d0741005650000c180300e41c0c002c149021600140350035600130603000c2d414000091481c2340141c1c3c2d0362a905044400590824840744035604101d940401051040c09000502100348091940d101c400a014959540e40d6500700d08030f030301100c181d50110014094001420b003446441161f110b9003101d500b000301c61484a003030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 788520458 1250 788519208 788519219
    0x20f0c031e16060c03111605060904090f05030309150403121107020d150c030e06040f05011b03050f070804200f03010c030204090e0d08070c05071d06041b020d0e030304 74
    0x78810f812000124005402c84800c02d83d000201141c183c0042c005094031030154a9280491040c5005603482500007043c0b488003034440342d02a900003900594a54140a65418600d850398000d9480300300c18000c00b80351801541c4015032840c0515819910260006007010352740d03004006007105101c62040030404003000d40e44001e102e144640c02150309041110002950404a1b01a075085009050070980b01040f8900d0104402e94016041014444507d01031702d05640104281480030a20168980341520204d0380b640c041882001054440c0425494548007500c4070074003190014808001c49882c078141c450103000161480001620100300d014440d8002800e4800e480350000000707901150803c2030070111b000380f45010b1456030160409200002c0002d11084c0c00408250620036800c00c90740400900300326240c0100600304c00c089500325107184540c8410803d540c02d5101d24240030001c000703041c089100703200111942c1c0043c065803059210a4605c1030481003007581c140010300c80000d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 788521708 1250 788520458 788520493
    0x18030807030f1b1d040b0a170c06040b040303020d0203070f061a090115080c07020a060c030c06060312031b021c170a0204080d050705031b1615020f0c031e 68
    0x401004540f144401c1c240d480b840f0703018180e607813898580b0441c1000107810250300ea401c1c6120903111894452400071510b14000761401d030718003030701507042480048c00140380c049200142003070b60b11a0742612801b4081e40d0040740e0728001c40c6005094441071600201c00680b940e4014021780d11440c046803041840000017038608982680641d0880742c06030100a901a417222226910030144040e044c10f040164000c070300c1c40f903140d004041c00d1001c04015002490301074030010680c1980311700e061040719101d14002c41d00e0f408403441c0c90003007414481900d40c41c0024880c103403480d510581c0100750b101c10701000e5034006954072286c1000d200c10062900e100c84100d034840392042c84010409031f6034510302015945003d80c1450500e00b04001130004000280b07000c8100c0e095110280507441600000003212820420000449060940e2980000540190315401680e1108050b001d60310200d0f010101c05490340114034840e5450b8002440e150451140301c081c114002218204548220810300d4200380d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 788522958 1250 788521708 788521751
    0x1c24090516090605031c0806150d020405010f111c0e0307120309150509040b04180c030c0b0c06130804120507080607050a050a03110f07060f18030807030f 68
    0x2000700c801d110140414103850042c000240b009600a05d0f07819408010f4118000074048000d041068100c0850025503d981100307210408000d44242d41d120482c00b4440258800d10038240411400d02c040c10201d8013809004807103480c200701601640e030701900861034940c101404801446262100c2814a0724104100c01c040c024440c4440ca1420b031070b013400360400d5440c0d440310803e01e40c0d2002469155a110083c0e0f00008002c0d500401c41d0b40740400040c01410030031030b41d0b8a81d1900d011150003072216021070300003140d024180701c03210552243d01c10f81e403500c40d081c0c243e00560b0007a80440e103240300c20846aa01c45000300d011604058075500c1350308204414030300a8a244c0d004000912480400b88400394120306035050852038440e040801400a0240d000d00c0e6052640e10b0781005900b036180c1c8100d0714041c040c1d5400d03e980d41401d203030800080008a500c1010f40d850001050768a408101078029850b4060b142c000c1e0b10741d0784138800c402810350728200104e41d540f204094401403e84003841c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 788524208 1250 788522958 788522983
    0x141b0307020a152007090f240b0405010c1a13110f0d02010e010309060e0328050f0c010908180301140106120c1407030e1c240905 57
    0x1503a0328000c50042007140c00c030a412810884640c0140e03d10002e412010000724003c8500002c801940003003819800c003c015170150014900300081040d0042c3d00e6842010040321408030500203440c0850304007880c00141c0501a480c1400300000c0c0314540c0580314005035103104481e040c005035101da80c00301c9562001e95515010301c04107881d5404104405080442c444d44c20740d441c0c0b104d2000400041e14080f5103000107810b1000311100c07004c080c3d10a8001145094210b0f000380a60040d0b416810354941c403003035404052000466180b500f5001d0420207415200d45543e80609141d130b012410b00113903104100d82ca038203659400e280c400007030203030024141a03a20450700c000070b0144a402d16094480d030040c0210310b100d0000061042c9038000d6030f0b20042240608001591070301d100da099595000f21b0f8601d805003000400c03041d0405a00c50880103510b071096070104000703c21207103401c22131209420010608640d0294800c84120b8040030000f0441c1040c0d8007003031140860b102c46007007401101c2807 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 788525458 1250 788524208 788524213
    0x11d130b06040b1303022b060b0607020a03032001090c090506031c0503070806060a082e1e0b030f060103020904092f0109180c020705090c0a080c030c0a141b 69
    0x4100303500d000954074550340008051f5a2014400800244804002007401040d0030307500c0b4045440c135107440c801d8031162a0301815100d007150303c2e8100079004c1a4403080041c4025103000d044000418103014210107035510003051500b050400a40402815006012503007502c5105403c00005880210b078000c4049240c4656070381341442c582c020094000100200d000c1d0004001e5922034035407003000075500c03c07003000002c04cc4024010980c05c104071050880389070301c0070f4903a000c244816601c25804160600c14054561541e032064981c0050104507001045484003c0010700c095000350000c08900b500240000781d0079805070b491441d02580c10044900c90349075901c04030120b402110b0b98003a81002424241019483c0071411001c44141411082c54540c4030700c184124180204000409404010180c869a103015404609141c00c9401400000786407880868030708003802044030b00880e00c044001e807030b2518070407081e110095012503801c0404410484503d101c010f188100c43e1a4580c04007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 788526708 1250 788525458 788525497
    0x103060c02070b040e0a0c110304030503031e01080d141308031b0f0d120902030d0c0b07080f070c170c070608100f0e04060e10020702011d130b06040b 66
    0x14028641502c5421801c203c460400060103048026100190300688546001c210075032541c00459403661201e40407520f40c8030118002c070800c4000b00180d4462803100420400882e0f012446007000ca10030300c94564140c210210703261080d4401c4800301c0c0c54030307000c01d505480c04903820781c030440900f074540c0941295000401c599001e448041000c4231f004141c00010000d020b09624641e40394500c0d1031010062040c6c803490744440808503000b00030816002015580112034082d000780c1558500a07048035851109000200c105024030310640c0105407903900042d071a85c92050603940c010b41000c0544045c000c5000181590100e80007e00003212801c0203020711615121026104030b0018081d480411408034007408280210321140d821561050315174951a192410064000c2400c0c0302c90b080e060207181d080400c40e0103560018542103101313a80f0640e440c1803c400c507030400348440c11000d80c49844c110303c0c1c4440707041e150440401e002e4000d02c0a851b05a0307503d5448402d80c0040c501c44080c070486c2c803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 788527958 1250 788526708 788526731
    0x305161a0411040603050c040e070510020115080d0e090a0212070905010207080f1c110a1a0609040308071808061e0711120706060b0d0b03060105060a020a020423010306 74
    0xb031400c64070505039028010306040d42c0e2205e80300c840c2076030360790f016942e64900030180113010410040107150180c201d082c0280c0018000340603000da0040341242d94841340b000651800d0000356200080c3d00c41ea03c025031594075000700007032035102800b002c103500e03001d000c070ac00c04480c900b14141c080c0355151100c0d1011f604d05000a403d180e030756405031484e908030114080b9024000b01d040c00c6441505c410828800c4102142911140201d903180178451003002081010402c505a90f145100c5c0031003141031840c1da411042041c8802e0071a0010f0005101801060801e800340c61410644034059254100c3c140c0c8404a091400100302c03075280c0b00035142900043c030000c811650030f0704604d040c0390224000c03a42111031a540c0460070303c410b54164000440b08240151680700c503014151004200d651040c10410000161610315034440c07090080d00000501490280c0880b0b5000030307550040c3c0801c1c0c2c2a502080003d00501c111440070034503205003034420421402416029512443c0001144840e16 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 788529208 1250 788527958 788527973
    0x90a0203010f230702010e03030f04020112020903030d0f020c030a0e0a05040b060a0809031213030315140409021513030302011127010207050307080c180408070305161a04 75
    0x2010b41e454403860030503600b003503001800c0070541110140802e03844035100d40d01c040340180400344181d40c59010200610107200e49480809001714000d1340c6540c03407411520716501c05ca100d11801c050b4594410480d250b4103101c00d4102041e0723030301d10700380040c2440d070050a0709040d648442c40110000c0d00c031603a110024500041c0c038a01400c8c042d0380411200c81c8410104000e4413a54119900788600c110009510b01400c204650681e40c28a81a00fa02e007403100030a8031402d10981c08401007814040c0010b118064071400400700c4485007016581d05102d28203100051100140aa8101520051319080382c414240100310690031019400d482c0c925504000342181c441086000620000f006011818944c04481142e103100e001079485007088c0c040300613032510200d82c0c009070b094000c80c0030000f00360901040401c85046c09131402c1400c40542c00b4603a4080d401110014803680c03060020703101007481a00500b2184000d00042c2150a01c65218285010701100e43d0b04a801d114800b00f00401004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 788530458 1250 788529208 788529221
    0x5030408010c230304021504081603030f03051b0f070c120c0602011a040c11070f09061403070b0f0427060603150509070c080d06050108090a050330090a020301 70
    0x2000b0f4880380d210252a5004410310010f030000c0c1c480c0f01d400b010181c0c5400e441044030000c04c0700c5800c40d859849156030864100c1003911083e40890303101c0e03891590850080c06400d100c1d0242c000c0448180031450b0380d00d00303d6000f0380c2032266815014000325000440014801c4041c0c021a41c26801000c2e4603e44403110b6041c0d5003041d002c59050044214142c054400d04242c50a411100424a2419110225040c3e81d4002180030306218828002601c9200b0b2040e0205079035842006200c141e484000d05000d10b40c40c2c4504581580c0922410883c13a296a80500302013001c0003441071505940c2d141140c03003001100002185000c00c6511410710386000d20514000700043d0805101d11410350785502c5c4020300c84d210707036800354881a0010f41c065124030010b8041c0d03903000c0c404a4a4180040c400710042c01c1038021540860310020104898000c0003c0c1d4905041c0d004005500e048030160303449c03180a000e41e08280b00400c40c0c2d40b01401480f000342d0854813800c001c10040040140c2d038010542516007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 788531708 1250 788530458 788530487
    0x614030a050303060103110d05151e0a050607061404051b180402040b0102120c0307110a081c0302090d060203090c011b0b150a0f1e240c05030408010c 66
    0x11200d9100000390010040d00d512103800d00b4001103080c6040301d0f002c803500c100c200e120308280c45c2008100ca240760213203080580399000c0ea080801d444036454001961508900c03915031091003c85c04100a00d841c0006105440c4182004907002c50406a15085c4120a950455694106000800b880c91010410703241d402d004a903061404e0708031070051344100202910180c0515110969150f040c2d0080043c2881c1c5108400026610201d00c24255165004510112103032880b100055110746096400c001c180e4050b1806421020500b01c0100345425844940c4c03400e154080c0844c0713900e03a0740c044121500601411001d6643d1034180c00440c28281410380c01418401021035003a588000280003016a540c0402d03050382c6030307c1e00b545518504207003180c899800f00402e10040340c4001281070b64421121030054050640101c0d10281100031014013480c041b142c1d60607410300e180c01c4400003408824070720781060b00c04400741c1d0b125682541c0c00b80d0010500d1fa0b45882032000c1069101866025892 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 788532958 1250 788531708 788531713
    0x906140708092107111903021504052b050304060f0e01031119050f0d0915110724050142050f0c0303070306030b06031b06161401061403 60
    0x1c0c07034100900364403083c000c1e90680c02c4402040001c10088100918001610001c0482d002401c410240c40280b00e0180000c9002c0c1040c40400c010548003401560700ba0307440201000101518240008408a00c0000c411265440e03480e01e100402c00a03c0180302a084a50741d980c0b20b88807160000e040c240709135042a0405140c811007001c02da18079002d41d00d01a00d030308409503428100c150100c41c680141d920340030035540300040e200e240001c25805844030078458990042c031070340f00b0f01c0c15a040399105002000b010808001040010300400c0010070240d03111864001200c0302550b42c01c08880c426001003d80070240c100c18420407200201070300d11020070b44030b4400c610f6003c100c810f450800c4102d1040c1845008035101c81e09000300c0f026681d95041c0601140c1d124500314000501610040c0700a4801d0310707030749010403007505002ca2580080280c008a0209800070242404010b90002c02c0e8401d18248030700041002520480e1b4202101500e00000b207103182c10003143c07426030451150038500c2075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 788534208 1250 788532958 788532973
    0xa17090607230c0102091c08120402040204090203040506071b170a02010204151d0f091801020f0706200c07141305131119031401090614070809 63
    0x9000095036941c0240245010001503148407480740100c094460b4a052505011a004816190560142c405d11104840e2214001c9140a1050089001e00400f0380007560401c50036046c04102c070000d60b00644090001440e05546a94500407070f0007d4a045031280c1100047c400e28590102c030090b400c41000103444001801e6642c2e413804403020103115158502d0208100355403034003c0d4107a400401d88100d04c1c0c0c115040c0c8640007010300d035650725003d0106400040b0502c0b6420454100c00019401602d030480c076407242125190b042009035861036a9640810115135845042000350a040344038402c085040303440084400e001042e488601404040c060000b192100710001e64030040710700300e07013001800b21001d40c04903641805250405007001d0616091000c2c41700b4451000b201180140040500301ca5010304204000c4079404d00708110700402042400400c05000305904054145000021503004603500c050541d8540f011400c0a0414001000885500412207940c44040c10000d084103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 788535458 1250 788534208 788534221
    0x40c0e01050105180a030f0302160b03070903080702031615030b0607020102030421020406140103050601020a1205090a0801060306050106020d020a030c0308070c06050c13120c0b070218040303020a17 87
    0x90340240000c140c0d1030354003001100450f46541780a0760156400c100c00c405440c04900b0045d40d203580c02e0810814501c10100001041645102a640104c8003582c030000c645145484029040d0041681031343d141c05a00e0800c81c813a26030042c0203000300b01020310705031a1010318038040d003101c92005210380510b40030401540180e901004031020b03242e00b440444221465428806161030307008800a410078a0048085240003036038441140100c0709030b0782401a6a600c01c012038560112000040010704440c0c0e458150f0780c040c1c0041d103280300d00906a8140581da80e10b9590039103000c0da00588080c3c0d6500d0060081c5503040c0141100041c40e07000400d00794041d540c0c000d0000180303081c050304000100001ca030842d0301c25441224015004401441181480c40051009902104d40f45c0c00c0d0741800800081c41a216a078242a0141c02c000000a010b150070b84058040d403046501b2a0b02a4200b00040c00c5c4074145040240254000c0d40c005845180c40c074009824203030382c1942c0440710913038002080346 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 788536708 1250 788535458 788535467
    0x150b190911250507030b330d1412070f020f010810121712010e01062f1227040b030309011d2106010b03100603020a0e1305040c0e010501 60
    0x21402c1111404a1081800741011403e000c0f06410003041c0f080404140042c02c240a5503541c1171100800e05d416448000d0006216001c02c0582c200b0b030402032500c42e80d408104005001c000b400416416100c0344481a02c81702c03c05d50044004031a440e11000c01c041c02d41c182001c0900241030207083c07440243c20880c0b803500000c06240320714410907001050350004c02400f012070100070702d01505004c0d141d441c1c80d156a00b452030240682c1103c03650f03010000a0251003203403814060354114010607010140c0d800024500d44c00064004401d02c210745107120540f4001e4001d03c007451f0342d40300c0c100d0184400e5611022286140e166103220700d04009507111213603000b008403440c00c002400c116101d01501c464020940008060040d0b0060800e010840c4544500c0304502c807080b800e8056403c02e0b0b0b29039040180a00080c1c40b080e0400640110900030140203500816440c042c60900b405088210400280b44100d03810303540c4145034683c030601c4100494181d00001074460b85800d0303402c56040000081 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 788537958 1250 788536708 788536747
    0x1e03090518011d190f14010312030e0309010e120c03060c0c07150504090207020f060a02010204081603030806190b160218011427040516081504150b190911 68
    0x103e000e03030317212120b5103c403459620500b2000d6085080c5480c660f9a8100308841c4a1500042c1002c40c2c100078a07050b150f24080b046421000e416100c0002d400c1101050010170343c1003e50b01803651188075810420340c0e074101301d014070801e10503003c0d540d0f8990302c03002141443c1056101120011403031402051a0b078000090300c0a42d40520390040c0c071072049000007011804110fa41076000000012340070103855064005105940810007290213024840448000c12070062101400241011001c2489440c1400c51840002004055070b2074803500d5880c0300c03030168000003c4034100076010000004509180300c407007800700c9070b00700001000d41c0f4102021611000c248201441800c03502245c0040750301090a500c10300021f141e072124585007a00e8099510308038246800c01035040c0200006403907030001220010180a80b000c003820761039075507580003c084450002c080c0b40780c45070314010700c58881086a14030022686804512540351041c60b00c2100c0d10040000d405000405c800b0f07021103100203940 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 788539208 1250 788537958 788538001
    0x10f110717190807030f06030302060618010518191a0a080607080f07050c0601030c051504060c06151e05131a132405090a05041e03090518011d 63
    0x3e16503070341c0d0310a0480046c41000422441c05242c20000303c140350b8001440303440f03000b05072082c040d1100f41040c400001d2009218869208403400050704040014500d0550002c080a5481c1d2041d2141000002039989101402151400c0c00c81e104e9410701c5c101c10601c0050040b60003429550600c134400400003003004110074041c0034000c011600040c41001111428801c410546095507101e140c48071030b01c0750900c641d901c0f807911104400d02c20407000c4102c1d002c072055a00e907008000b580b607644a02074000b45003500401400e24000080082110401c0da2907140003815203646142072104110349c5000602c01c010b4034600c1d089101e0400444280d1024514100311621002641c1484000340a03011070000000c03000141c241000010080701c00c00825100111144101a603519130007030704403082110003501e115903032210805400049604551424068604440980d4030345000c030b050b403195540d0240071031031198010404203e0381ca014540080c0c40c1da00300c0c0c0090030400d4004081d010340b54404e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 788540458 1250 788539208 788539217
    0x210a140703091b0801021210060813060b0d0b1e090d0e0402130f03032303041407030b1806090a080f0307030e070306022107050f090102010f11071719 66
    0x300010b004442d032907291900c03c05a1001962a260740906010750004801c980c2c545100002081102462500850030f80700380c0c3c0e80d11142a9504407043c542143c840d0301c240d0f043c56465004102036184d40c070201c2c0181d4000c140025450030040705900c54006c22a00c80c9031060408802e00c12961008900c02c0e46001d205e15240803c420b01c040060020300c0790900e108410340705a040092040f00840350401100c2c040c0d2541e45040c07110101955425402c2084441001001c000140001c1c005100c52103c5100d22030840b065541c680c0e490060a103010703240114051007048454a1483e401c10082e41c0c0320800764050b10710980c04d541c80c0701040c080c1d0032a001c03102502100288102e8807135032000e51351091203801c407002c240c0d403410000001c5d1300210102031000d456008181a13252118410341c0500150f80d20f0501c2c0c5440070142c1d1286400421805046540300c942c00204426180164404401c4200c0340c6691000307030b4641001c002501d48050800001300380200140284016a031100100032400c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 788541708 1250 788540458 788540471
    0x109030b1302130f090b0106090e01150201020c0109082208030a0e24131721070b0109230106050a0804030917160803090d0204021806210a140703 64
    0x940104041d80844890f40c2c41d06150000f01c0c03403590000580280542e15000e92a62903072821100304400340210117142503410010000e005d545501d0754019016032000609109104440f18255021800240e68004005c141024444070181038031a1641031182c40106840c9440c0d200303501d0740541403900d0705104c80f240c40310005844442d0191462030f811084102048a403050103030742600004642c208494510302e001c914060414203040003100c131800181011852400380306017a09010202c00000842402984c0c0060058080c1074060031002d080820ba111498100305210303140d082c941150380310800010020550820100c8006150601d40070201eaa120b04080d42c5681199000c00850406d45645425903000881e102c5039015030078500500c6140e40358000c9079a4007a40f0b68299100030300e481950700502d420b6004000162220040a0f03120000da00018000d0300040000d600b50001110010343c407041c2d1410140e401070045d142000039012484509004443c02022a010325a40e540d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 788542958 1250 788541708 788541713
    0x120d090f17340602060a0b06030f1603020c010c08010815070804061802060a0e010e190501030e0c0409051f0203041505151003020c011506050717040306020708180109030b13 76
    0x80d5104601ca407009001102c2c030f030b0b454000942e60102107071500c0e601071414000c600307039141c041c0c103da004004d81c1c2c640c01825221503050010070f0440e6203941040c5542007002a5001d6406e004240c005425522800c0b195850026071078108100c52074041c20082440b0f0810220542145206070016005040042c442030b8110b0445c41040b00c40c1f5020b1740c00000440c440c0d0507954021080600d10700207903101e01401c10b11105105169020114917001d440071420180302951095122409074002001124241c01027132020070222200142c064855030811009056040c84200c044011149002011407451a09440d08000c1e004400802009151904c0202e004181d10302c42c00d0920041c020f0101607807070121107000c0c0096002200420f00c55003080045000340015190a40c00c83c3c1c15610780501c4c003a400e9403040b5083e6100d16007800424418400440455a075102520081d03102e21103040d0740e440c2d00c0e01c5400030380f030b0019500c03070401801d040b091000510705008207070031110189201c80d1044e50b52 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 788544208 1250 788542958 788543023
    0x30403020306100513060302010e12072417010e010504090602071a01090b0f1f0908030408031308030c0703110a03020909150c030702030301060806120d090f17 70
    0x6510180d07041c031560003070000e0300c64031003160000c07034104496982c2c5600d000d088034000e44249201c083d010032119280042541050400000300000781406da0b0410341d1280000404824408002103480c02d42028284403260800e000d80e207400e0030843c15041c40e40c500090200340c2101400381034011a251003075042003003695015070325003540c050080d0000044d0341484101c004800d100760042981480715240303580c104411200301803140074140b07200e00c01400080846294604010b60100f20f0701000c0020b103140140040c1c005051510003440c3c0c0c5401000d01103a0004041c0c00a0220350410001c0c6048030342c0025440c01241e52000500c0e00c18004480011210540c943c0041e4000c0c0006040210292010070140304200c07609041030244d4aa0605007031071404100c0e101070140e40700300010f00c10076008089817a840380000305151041c0510103445400d00003d040c0314004505403400c14045040d00c03a02d507001400003081c0200d22085401c40150b41d0b200140701d0407541441410407412100c0c00b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 788545458 1250 788544208 788544217
    0x30813030501020a0c0309090b010903080f0403050708010f15050303030f070e0d0303060e01080c060f031312050a080903030c07391d1b03093405030604030219030203 73
    0x19000f1074880d2070b01203005e00302c903a11302002c1b80012a134103c0800e10300498400da07854440107948400100f0309580c1e8447c255480404058844c0b0418040007000031b004011180150030207800201e0580e44202804007a42c0da1190104007540d0290350038012602d0003c00d0702d50000b960500c8111603160139005032040302040c0f0010340c10907070344400c04080c1034140e0042400c80da01c08070310725142c0c1c0e81c83c400340c0c0d2140b060740131940e40068204100b1060903c54000b8540000505001d0210182660740b60032444214401e6040800c3c00400c207982c08982103072009a00a5482d00910b14500e015a249905031248030350081000100c00034103426030048020003401148800003008039911076040c0144495036070300c07a0800510f129040c4220b0340c4420b00a5030b000e41402962000c4210031109c0d056000d400040c030103050f52044040c100035483e01020350722260808410120400c49040c0704408070802c0c1c0c0d0b0003090013584000300b0f100c00658001825042082d950001f40000c0d041e80c5412802c5100c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 788546708 1250 788545458 788545463
    0x90b0f060f0a0b040e010f081207050f0106060905030f1b01030207110d060e0f0d051615060e190207262808061f0302030c090d0503030610020a0c03081303 68
    0xb5004004540003d03814010320a6035a40d6a58068583c0d0b41c0b1500d049900113401845081c0d0421000e2881212048015080592240c400c0d42e003503000c0e10040500319421540a500007419100b001c0245050901608070f4038852000907040c001d1a203020540f1070040c3d0620b540c10140c1c001038020502044c00101080701c0c07001010074080503058106030b00078081100007215a07024034010a400b641001640e080041c1c900c0e1185810003080030510030340c040d041c1e8002e860f0b0210720f01030031003105030903c0717134001500850245010324208901410618980c2202983c055441000b00ba03011505c4090080850b41031411040d8a44002c012031258034001e01d04580754029028440b032080e00344002c118440140269070f01201a640d400410038141000000d0803034007904600e00d4181d070f5201e5002582c0c1702150702c1e886450301e4203c001013099014810010f40b910341002c01400103600c3c0c0100001041e1181e403004180081e83c9454043c640010b9100090a00c1000030f42c1240710145020120000c54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 788547958 1250 788546708 788546719
    0xb030a09080c060702160e06011d03010f0c1806050d020a0201090b1008010c052118030a0e030115030515040302010906020c0a0212011112040f2112090b0f060f 70
    0x925882d407181d5100015200500903000758503902a0004050b8480d008507003003941c1142e550f88810006440c0115441c2c00014480008041000952024000c10150060328840080c2d02c456010004180c616807203141e644203641c0c8103080210305e50140a07900f4000a40390010783d034108942d01a8018110140e0040080414000b000406610600c40c0300031204880e00034089035101d40781c120b545105495042104180e2408020201107080c0700556000041d003000d190b80704250180c8034a1341e00a99500c00001f058100507040f0740c14280189244441024450921607003140e450b6500c6241d041e00700c5508000000000d02454402d41041c00c0c030700d0300034000f1503880b5420301c099500c2c2c8030302201c142e00948002101c984003440510440034440050010b403401c1c0341d04603005c5007920380003a0042e680000d03255070240214082e068180018030080c00e00d40c0450860ba0009000d108201c1020310009140080c17240c04104030450307890303000801400311842c641e80c98002841c5200504402500003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 788549208 1250 788547958 788547967
    0x40f21020409030908070501030b061206011710061d030a03081302130b030c0d0503090f011101020d05160e010c0210030f050411120102030114090615030f1006030b01090b030a0908 79
    0x19000082c41d8241c550b030005039086c041d11000107500340c03100d105d07044c1c1d000a400c001000d030001c0c0c90220580c10490514210480b11113000840c0c2611009541e2110015680c000820510750060840c051909580d0b2000600d58070900000e600c8250305140130f4280158400002e407113140328190201065401010078100b07050301d403541c100600101101c54041e218666284603e89480c4030219080f0343d000006603c0c0051100520441c0b202030b400c210305001c034050680f003007100280041d24040004080004a501e0802e00c500d0100d40c11420b00400e011190125a02c1640e00c00101048641c05070f840407c03d0022910480051018014241e0a540703090103000030003500b2810015600c0c0120b40b039221120852040c2405c03880f0030310811880d2041c42811041c44d050840500342c2c014401840305c09a65100d01500b03030603034002c0300c112818101400030000300b280214150400740005160800c201a410300004c2c00c0002c1502440d82d11460100004500c5441e80d00180d8455a001c07400e55250b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 788550458 1250 788549208 788549213
    0x1003060c1707020d03141009021318020a090506071a2e09060f05090105040506010203070b130b13080d0b03010219081909120509060d060b070b0c040f21020409 70
    0xd1300c034400400400a03050401000c1044daa81003000e000300b0b8841c994501281c5410a070307000035800a865204da003168100006071780c22400c5c64010f50300e002580f0159844c0c031018002000c400711904031910403881070100c0760114034420400110740c2500d02c004495611207204000c0c42c1044040201441d01401c0c11071801440c1d040320a80403101e10b00ca0602045450f9188284001e07564000c0a402070718401c0100800e2800c3d030403003134103c4810300690b40743c00d400b511303841c000100403648120945d010328040804c001008035240d40c4019544400b00f1900f14039561800507104012428040d1a201c2c05a820165400e50464401c884152107058541341c1c61030001d00300303010840d020380e20402803964001005204c0d0043c2080035500c1f0440c5071244498202c15038554004c00391054000d40280070000040d0150b1040304040c1204094a9848641d41d103444907819034001c240541014050100704251071096004005403046c840904010441014503210b5580e444d400c082e40c45400c03d0700300d005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 788551708 1250 788550458 788550463
    0x110115271b02030d060512120f04050603010803071709011215081b0406150206011a1306080f10260a2001021204211a0c0901020c0102061003060c170702 67
    0xb0300070120a008170340e0348404125202d002c4601801d074a400c00c80407051040304ca14014102e1142d0711081030f00b4291074801240c00d07a01b00f60000b0006a0001a0030824404500c403542d030305c44120940540381c18640b4000a01d42810f05035980802512110701034181d1139502814406028500104d03003005510118802c442808800b40d903008628010020450483d2800c1064a4103405c1e001060181d00e1308800751906100d05440d11094041413010790210440c0014040c000c007681d58482e0000d051120f14040c525a024041c0882100016403c104040c68440801c03541c0e80a07041082d000365103600c16604104441c0d40c020100c00d00c1601039405484c0100c001b01e010b020071380c01c07a843d00003034604408241c8502e000d10104206c1a00700c0c0614400100344a0600c6485010301003001e502500084106003270a69543c900d40c0c9020400c02220750f41005207102d400403d100400d01424030303401903651041c55003c003406d69602ca1500d200b00d18000d1501000c0c1e44ca65401c0455180b40101c0002d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 788552958 1250 788551708 788551717
    0x30c020d031d01020a020306041e14011401090207020a03080c030d05010914091b060702040209100c113003070506010311030706050f220b0406110115271b0203 70
    0x2208038260819940055200017002d00290750301400820301c0361a141c603003030f4080c0c04d803481e1300e8400032000c9000c0300000c1d0120000c425402c92040003241d140b4141448030900030b01600100b64032441813100d10007680d5128103a00403283c00240c1c1e5640c0c1ca40840303000e400c512500b040300e6034850800d000080c4c4000d0342d0b8800c1420710301d0102c0740b103006e490f8411159204e01103809400a05d52007071a800d00c0700e20b0114024645c0e0b5100400c010300d00072160001c42c50012441d800034012500c40701c018403e0001c04400c441c5811002c5541801c8400c040000c0e01603074001c481441540c1740702a042c0c40946004108071622203421800b00c82840d0780d20305d8000900d101d041e80b030b107000740118a400070f102401603058500040b181d5000604041003110706122050710020070701c807004680100003848004c0b1030020030261141d41d80324640750507051500340c25031341d09898040d140b4503410390400103c0080a500f00c8004580031441c1192446104540d02501c0c03013910b44504010130300c4409140a40010003031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 788554208 1250 788552958 788552987
    0x80a1d060c030d050a02090105030103060510121406010b0a051c0b030303010b0a0315230a090e030706150e04020105030405010212131407050f060c2803080a020301140d030c020d03 79
    0x144520355805d007001040e4000c401045012075410b01c01400064041d401140d0700042417a80c1001c5681d68103003001c078050f410181a03030303072580400910351042d02c03d110950241021414203890f08503550b000411900c07800900801144014480310140d5020350440c0721491401011a074495840d2100c250040d408100480c6c0802d10740407151700e0440f42d001e10a01158007213100c8110491100d640c5540d01e41c0203039001a40301d50f009002207144491845050010440385e0f0040d03480341c0f0305141c50400c984c0c41035080c00008a803000e04110001c0712034034840c1d2142c2d080c41d1443c0c1700e031182e24045000e030081c280d00c3d0070280440c1c42004920801c2c00300b48141580140310f008142c0c0985030300141c031505103028581e00108210310010721818150010185140f114040341c2c440c038800c0c0062006030131112a1000d200030021000410b05504c104e089030003182084007141341d545450858011004c03290314080c0503541d806910001d040c000c0b804031021503005000b91074007440c10300d030090100c0c85c0381c50034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 788555458 1250 788554208 788554211
    0x121808031006030513150f05040501270b0622020406051e0c0c06220b0a080f0114010c0303090219081c0c0f02030705030307050601061b080a1d060c030d 67
    0x42c1244203002c4c5600591500815401c3d030182600c540c8604c094a040007541c40d5100c0c207071100303240b180340700746485240a040000351002d40a0b403a4128001140b0241c10f07000d105013010404640c4042c00203030403207030440d650064401d2480705200100c0000c0640003209101050010344503810200801880d65010b10b403c0300342e00140b1343d83c0e0803806800c4e41742c0031642c4014208546030030128010701c203448070500c010a50382214405448001c8980c1c0001c9025840807036440325545e040008190000c0300c0c070300241025030400d841100d11200e5402c0c0d050400151860000505019a000503000d42d0054400440285e080540c603410100c00d1240e944944540994910311482c03041e2000d58900e15507507030403c405042c2c0c8030a14034604070142070380e150007002c600003800d990420050000f180314102a10700c0b50316041c1d0140100d070041030014480e4044000000001d55070030203c51305011141000b40100b60741041120700e80d412404501d4100e100050410483d400000282640c034601100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 788556708 1250 788555458 788555491
    0xe16080604200d050f0c072a0801060603060302090906010e040305030423010218100e0f130507020f1902060a121e1a06070321021207080702161512180803 68
    0x9000020707c2207180281030004e20080f42451034158400c0b03414104c6e400b0180503069900d682101d030841e01c0300d078022404640e44231000c10450406182440e80481840041c2a031585400c81008190034010401010040000b00240c20401e20740002d80c01e5070155031012070503802e000000e074004c2d801000f56421030391600420b02d081c1c1ca0401c004103294140e60b0b580d0100101c411042c40b01d03069a107508942d105501025903001c41040b40f003001e00c1010346034000e0860f41c8240e003480741018045c4070517200c40161404000050789030901201c40d450154a000f40030b9912882c440c5005080d01c0506c2040b852400c43e0070b1140481c079800c22900c0318480420482900d802104001c038a11a1610080100781c071891481c14207680c0a0062000c1001c0103009072800700b00c009020f100c04000c032000800b10340b9140911621540c100221005802c0425101d55440d003026040c0140aa1450f60b42040056845408170b0444c040d800108240c069010900c19100c141d1078070300103036001200c42c030443c0f210405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 788557958 1250 788556708 788556721
    0x30a0f051603080402210c0d05010e01020304060b0901090623040207230d051e28210203092a06190e03161202210105010e16080604200d050f 62
    0x4e250318550714501000306086680c7c031051140c03050082500f501e40b075503210150944030f07600307000440c0b0580c8901000036602c00346408001001d141030b002004a180303054810301000e601c8244030b8103041013404a18070034100c04c5d00003c0280c85070303d0b001410308070010140501003c0038542d030742180801200b5103400c1200c0038000c5485000f04480e0340301502e8101000145c0c104c0000051041d002d210420402c00c03d0300541d10f401e580e00c4800240700003090803c0010000040c200c0030780340200328200941c60b5041030100345544506901c00b901d8084504c1860300c541003150102e070841c0c928043d081640340c0946140c2030040c1404074003050301041d001a10410503241c08143d9025a103240c0800040c00d504041da000780001600304100d8001000c03100c1000950419034107094074009a10000c1015810100348890a100280c0341e0010700d840d2018481100b9040510039920007400d80b00010050703038601c20145400045440309040ca0400900c07446c2c1078030b49400540c80707001c0c4078a00002648810703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 788559208 1250 788557958 788557999
    0x8190914011802010215041b080a05011104060e040b06210a14040b0112030212030414070501031118180f0a150302061b010b030304080f010605090405030a0f051603080402 75
    0x708000340160080101c1022034a0a446d0064100340205589400659040e40b2000e08243ca900220b03010b81c0101c00c0c0104000f002d014494044c001e06130401e04203807400341d002d0034410f440074006101da07031100c0e90003103103031212010f484038440208084100442d500c0002e94041d002a141041c0407414414003508d04c01d081c429403406550302c00c01d2145a60310b4101e100714402c0d1a1f6004a00314020400811001e14143e006580103c0c0240c10901b600803070b440640781350980d103071302c01c80c149410030040014010300c55080d503200d03050000074201d40d00c002c2000105600101d031300d500d40308941e010601c041182d03884011807043c04441400c1001d41c0e400d04103090290f4941c8002580720208100103040c00300c40200c0d846502060600200f0898403800010381150000d4120608a0f8000c901c018036682090084074010a01500c941501e0b00b00342c0c6403191280b02d14000394061140c100c0044440030710800450f80ea5008001c642104c451180c5001802200c0031382e41a44281a06000880a031101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 788560458 1250 788559208 788559251
    0x403020103140417070503040f030305030603011b090b090d1506051201020c1218130e010b010c080414011202070605010f0608090d1d06040e1b0c060105010819091401 73
    0x14201c21098519a40d08130026880448100d401d0302041c40002102407000303001c580514801c2d140e068907031034120141800c540910850b1849105100503070110175070400e8902c02900c2e034a480d090398410013200811542401ea4078010002400700383e56610100d650b90101c0c0a40e08100c6a541c0d03600d98540c4010700b41e015049011880b500031a0381840d100b12800300a0071043e162654141481c602ca5001030508200103080028a40c3c4841c01c089001c01d00784a500d003515400d0034440a044190340b41c0c1011801140114940017501c076078106116809a419519120100c40701596900f01c01c2c034003003000d02000c0c4141d4200050740600402c1c120b00400c001d5200e81e2841c0010700b144100c000d0215008070002c0c10f00005081d005421403640c0e00c9010040015190b412030414150409520b1848211140c0c850406100e9081c0f290003603003c008201581183c000b460207407960f448000c012070101c11200003802d140740c50015181c00308410b0310060304001450b540200905c81101c0c4a02640240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 788561708 1250 788560458 788560463
    0xf07080d020c22150e0405100c09030f080a0e0d030207030b01060e0108040b1803160203070509130b0901180f060515030307021311030103030801080d1d010f0c0203011104030201031404 81
    0x103c071042e007480105680c07120410010700201102c0b0281e0b00c80a80500440944054074960010713500010000c0803400b40c204420254070f0100d214034a035171200c000320256030710002d242800014207683d80358031603031008040442c000c0246d5003114403403401a640e910107200441e04040f107000000f40700d5000d581640c0c61202e0603180c404059403203548040020b100140b95210315440500645284a01000600303180c0544901c02c0703407002e031640101b51500955905c0305104490305801c03c030700440a8150403404c954040c1c3c6a5a0303544540c09020f0140162142c082d05440000840c0f8003881710340c000c0001c14600400003046941c54a00e0210741c208205183c09401d9030040203014018104040f404030490100140000e0041800c000240c469001307900950010b0344440041c0f0044006014440404080c0d04040300e000308482070701c03000d00041c844254180005841100b840034001d001c80ca80c000e44c010300801c05a4600c060a181e1900035020581c0040d18028070b1281041c0c802036214060341c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 788562958 1250 788561708 788561749
    0x11a0904020a09080706050c120c0a0305130506031311030a020a120c0b030c0403170a0e0d08091f0e031209100908060c0d05090309210f07080d020c 65
    0x151180520000e540812003140070840e00d41d0780095465024001d0030050310041e52a83e0b9184480309060f440c00c1e2108607500316002d02040350071985600080c900b040d056060400c5510707400000d0b100c80c0c00600e260b00103500080b0000070440303400911141041c0541c0f0611503c0d01c03185204091540c0c0e081c192100a40001401406000d6025640c0001c210648200c250b0503138251510500e41e42a0400d540f07a58a2490104003072042120061603503009113402daa00d04e0074101511300041c8044d940b40c11480c01020154507000602101800302c030781ba280040c00ca100380c41130f1440080f01e01001b440b880000a141e0002049440c0380214080008565010066092212000400205002c1c444507407041c0303d50090f0000d50410140880392107004060882e42e142c4038210b10440581d43c0080c003000d456003003040100417070f555203140f1000d80d100920880c0c212518545455203058080748540e0010701c10391000042d02d21700020104858421035080e910151424014040d80c400398044030407458 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 788564208 1250 788562958 788562967
    0xa05100e070f2a0c08070803031e0a060b0703080a1b0507060c05160b07391509050115081c030b030a1e0201080f06220e0105100905011a 60
    0x218810b26828404180001c15581c400c0c060080340f10000c4005002100e8120545004001c50181030090720024003851020311301d5841c2c60011031007801d4000001d003004004500119410f01c007581d01080c06000c10503a605d40e00d510f0f41c14041c1a960301107601d4000b070fa051024582301c191b6091014a07109003652200740c00c1a10300e54a40700640401c2103250100402400f040110411804204024a0141e0402c0050b81021140105100302c0c03000c291004590f26074240d004c070303081200e1401c1e896244600c4901200d0681c58150070310b55940c040ea00c00717a0300300a13410050110650107400e03607015602003040c0035a52642c00079102c009920100386480c80d0440c0142416019800c001485900107060302c1c040c04007607031801074504e000c6060103801314402c000710003156004101260040c102504848051400c040000e0031031005142445800498805512281115400c0703401d83d45903c5000b40082d140404412040c00c1e407903c03410700c58508000000a0b501d10010903080715010307882c0d055142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 788565458 1250 788564208 788564237
    0x406180b010e0d1509020303030709030c05010e0a14030a060516020106092703050c0d0302120a060524042303190f03050a121505030717030702010c0203030f030a05100e07 75
    0x25080004040c3c5500d0348417019440140e40c00c1c001907101c0c4600d615200c900f50700f90f0500024000c42900800e05220300302e40742ea0100c1d03403034110080031520030030a400c0600c551140468240921204000e0010342840180203040038040704030841030610b40d000b0001503968a01c3c00d02680c0804600c0c20034101860080c00c4181c1139902c2c00c12040d402800d01d00e00d0440e14110161602c1070441c1c603200040e034080366040012411604403508a00c181c1824000c0384e0401c030020310501400c800311501c2c0d00c00e5841604500254071b065800400741c0c5000031114105907400c071f8100c00d1100c0c00c158802e0050303c0c90207086500442c20302c1030f6640c0001071500c06900d1aa02510b982c2d0100c0d80c1d0700184108100740c0c1c010043c45010b071824140030031100308a003500c0d110500d031400d5031030342041403050b02000c011201c401d800025141c1090b0246000d080303a5000b4004607085200e0b515004060710300010030414a0840c40c0c0200c5c2c00ba920f40040c0b00703156652941c1d100740c3c490003550f11b48006503035420075100703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 788566708 1250 788565458 788565473
    0xc09010b0c07030510050103020a27020a12060e0109050c07080a121d0d0f051e0901030b06030103030c170304030e1e0d1b15050a110c0406180b010e0d 66
    0x4054414504840442d03850740c0300c152800950456140d000c5403514014800c60801c02c401c200200f4220b88000d2403d034022950340c1ca000100000640301680c0420000d400e50712403441c03c000010000800c009854540006542d000000d010359560182400d01081a40380540c0480e4882a0409405420840041c030225400350101c11168689502c40704410051207628100c00780c608040001080d100c4d00080d40275017071101800e00310047c0203040c414909012003808190806010031101640d44940c41401a0010006ea5004942060740440044105600700a480c100b01c0e02598000010302111034903c200c85c0703c01c03a40200003030045002d50145090003051480124a6204c00043c122112008a07440707104001050301e4446032407482d09000400c095005001e00803a4000740b10744042484003130311a01c00e030203081c02000301038510b8640194091081d0b10f4a40350007801440980d030740f02040c0c03010820000350816140e10300404011290301882003030242e25806811070f00c1400071601c1c2d518 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 788567958 1250 788566708 788566717
    0x20409050108062710050f04020f010f0c0201110a05031b0c060403020a03060b011e09090b090108070608130605070f1d03062208030c0307080114033705031b0c09010b 73
    0xd89204460b00000f18440c40d00803107100d01c18400301d87c0042c0ca81401080f201d103014815060601414407148880d00b50702c4200e0890564081c06d01e01c1c50068204a0185007071f10f4a07801030218000425503274000183c0c000142c00d599588000c0344c442c08584030402c02c05200e50300c8022340c011059001000010203980085242000505002140030b880c003001c129400e400c810311600103024418144030301481c1c1e22a03402004001c0d0f0b00350700c04d50b04040c000d40c0d03200280e005030418010180b0001c1c4200e5456000030b04802c0c0d001906110301e04102d127000e480b08004900c50300109108112a03500104d031901c150101d020b0040042c80c20f5105c41010b041306010011200c29100502d1209401094000d002180140d0811800740e60728a814500146101d106030090708040c11640701551056500145000200c200ca4000000c0014000f8880301c8d025000e01a00d4842c000c051070704014041b0100181c002c04010080801050b00045d41c1070380c491602144181c2d00544003401400038010220107031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 788569208 1250 788567958 788568031
    0x1020c010e0c01030f0b030c010e0607080a0815040203091c170903092704020405060d0203061608070306231c1506090218012a0602040905010806 64
    0x14501014200114291901d440d20580c075a40802c0040200d56458415121440300c200400c20041c00308000094503036101c2c0c1a0a41000040d07142c00409a5030002107074002a4800155551001c030718901a0510a0803102150304d112504a080ca141c20640201c0e442404888054440503509100c0e00c10401c204801c86030402880c42c03103510b142d8402050035401564207100440d151203072002001009240844803020801076050f4000310440c2014449070001ea0481340450b00d56210b002040c502107032104c0181d49031045606020040e20302c44030780103414a0554a000040e600c00c00107800f03032550351298406440e40120850080701d54108194002d1400400b1103900450406d51841d602c41580e01c02c0d0b414803c400000c00c11402107100311801041350240035030400c0e401040c05203112050301c0640d41800b444080c030403809111020078548400100c0c80c0d403041c944a80c20200000d41090250301e85652030040040340c0175400041080c4034120074842c660054203410004c445507224038511 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 788570458 1250 788569208 788569211
    0x1141c12120207050c120c0904080a0509090c1804230c22090f0603030507020f0a08060a090309053f06010303120f050118020a0c020d0318170a110301 66
    0x1607501d1401540002d1445502403030041c51441c80000403c1007082c12080030182e554800e154000c0030382c40b0301c2c0c2c0a84d80542c0140302c0c40d40358141030800360795030301c519001c43d0f41c0405210708100000d01c441002c0d00c0c0003080e5910760444860108248411a189000354220615000d87d0b00d4201d10b010245050740a103c4080484c10300d44107008408040c0210802d501d00500721034800d1003c03d40f24451a8401811f07040d0034004e00c1d2564070003510764482c4103401b0b8040d00702c1c0c515211240c1c42d0300341160018254102168010f1611410a1000340003401045000804949000426140c105100300c00382d0300c042c0d4090b00903c116409c6081040f40301c44010000061418034160050043c05101c2c001d43c0a030303d5a014020051180b81c1c2112000c45280625038039000040c448901a06849540e03030700d12110040c1c1e1055450410b803250300b07800c80000e501103116154501055401425207000c08950b2040c40e07000c50b11404050420390300d0040d1404207030f12441d43c036004551004044940d01d44013800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 788571708 1250 788570458 788570477
    0x5100b040f0204060917030406200f0d0f1701050901050f01020f190204060914061306090914010509030c1c091203030501140f030a11030111030a0501141c12 69
    0x3090007070341c2140e4001404100c0711501006a486c1c04c12441c80c094024001862a042c18000043d01c801e80d04011261010700c510540740440404100c43c1c510360106030211a40d0040000000300185804000c003070000e03550300b9103c840d00c014008014162040103040d800540e080000f400050000120300c18118450101c40d9400800300b44180501060710001e031039038200450041c40180c0d68103501c4032300150702d001500001c80d001802810b070030800c119040e1100c40c102c410350f003001d0100d07034000c500114138082e05141000f00c00800d02e1414280070f4000d04c8595690b451043e2640507001805202e504080a0040f00b203400e0440070302c4600040c1014205543c56442c2c600d258228004e086010903503c000501a800f1881c6910290710b4040302c44040d100d1005001c0f0343c40305207005c002031401502c0c485900055500303422080ca01030315012550b449142121740400a40000e203c0c5103c110a65150441c0f142081d000500b905412020620100c40b660356940f8200c410307907906031040001421 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 788572958 1250 788571708 788571731
    0x909051e01080607140304031709070b12040614010312270e070201050f070c031428080108150c0310150203090a08060106140a090503070e2205100b04 66
    0x604035806000048010001494044000780c0300b0084182441c03510a002d104000000307138400030301000c20b031400700d0b441c00310b031100c580840c9481c41b0f980040c181e207800442c3e940b5603000c181e459644914022070041c0304405d8029400c0c403400100b8080505152541c40300b488049015203042003132006454090034030392004a00c002c207031500a4112111008110050207000c46d4240110340c3c03c000c0300c444985040c01c2803280942114000318006041c421100c031501410f92a44040d500c050b000c04c1c0d0321034440900c0360b09611a018540e13800001203800079001103442a40000e1002010b00d0504840420b501d4070390100c2550781008100d202030722442c0d4402304500048050394208411150000d5440d00420000c201c071036801d03038011541a0b4080d03001084040e42c003a0f071240c01050f8001301d0660310300e200c0c0811160b510558001503094030072404d00062444e0b807031145521840c0c083c400003289401c20b8070700d0015600008409092640104802200d01c034040d404103c3e203001c02040081e1000d8002c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 788574208 1250 788572958 788573011
    0xd050705121002120103140d05030105040f060909051509010b01090b1c060b09030d0c0b13031815030f09020d0318031707020307080f0a0b061309050124030201090905 73
    0x11002040484e000d40100104110300c03000c1080403146a02030040d00f0291a0001d02038001440b40301c0c450391b00c41c080a10034040e9584540050003010805201541860070b1660340c4415200707035440c8030111080040c1d0b550106115050416605948050886160800c100945c1c0c014041c40303080380084450020074101c162080c00c005200802205441d120b81c0e40c105402e01480e9030501081c001c0a9002c00002091810300320352200802849958040d050300301241c03484c50322028000000144080410f01c4502d0b02560004a015980e00344440d21006041c0d505507003c0394002900034809031554800240107100400c800f84000c81c00c0440306035207403601c081d1401952040901081d00183c54410b6050611000014000350802000d0580181550b0b80d580d032a1000040d080300340c030202161242c0c1c0c501030342ca20311700740d1088144500741c1d050506c0d6000300038008140307515400f10b01c080100c00350302503024000c40c1d80503143c05172600ccc548070101e0040c000081c0b043d48821a203200c10103201545 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 788575458 1250 788574208 788574217
    0xd050703110303070e041a0a030b100312080f070f0e1002030c03040b1e030103150c030b040905030a0206060907170a09050319080c0301030804090207022d0f0d050705121002 76
    0x51755422650303119034003403108451707620a5081d0184000f00c80301c0c4490711040605000c80360300800e40e0300b60390764122118000c0c05043d01f005060510425203141c24070360241130240500c403c4089111071341c03500c44050f50303514800302c3c081d40810342c8600039840d0b41c545907920f48981c044500589190034159805542035038842d421044500d200450f80c001010b4100d005042c070400041c10043c61035065890380c007108144a0418031031240c03900c2504090620a4002201020b00074000388010f10b22803034443d440b071300481d85840041c0308a1001816a140c4644034034060015501c80130712501d01c4102036a0300d41d000500308003606841c2c114550000708100000c1c0740190810880ba02c3c503503501600105030060103810049003100520043c00400c81c4c0208403800c40f24a20070041c4d5400d8a03102180e4403c540f101d40d540103191521030103813200e02d01d800d4200702c03100460f54100600d900d80f04000c10310303c2020010380070b81c0c071030001844076003001070512100854950071690f000000c1810b02c0260b031301 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 788576708 1250 788575458 788575471
    0xd030e1f032306150921061003032001090b0a0204060801061806050d0b0a090501080d210b01110f010b040e1c0302030a0f05010b0a0f020706020d050703110303 70
    0x1258103980304440e0741440344a5100340094204a9902d08160014030468030281c107081c46400c072035024800d5005030300100c1d240c10101508010360441c020304030400380c10800c041c4401314014400003c03c001c031818001d0b001d8942c1602c612001c000c2c00304002070801c41e1001000c903959030781c00000b408034111890240c807070307007150384050394643c00c00100600340e07007060b401903040c0a00d0700d0b01c01070f00d8031180383d442e01a24118607003180c4441004041e803000e8002049405e80041003028040b401100c3c540000b41a500018102c0740c0c0261109400ca07400310641a0f0020740100303042860400740c241d80c11181e030030001490510049804a01900d0030413103045000050350303540d070100180c141010300032101c1d202c503810054000d858042110548100c01540d0341d40c2090390010000320131100b0381d84021070400c0105010845583c4407501c02030355900c010010408036400c501c070070122510000e0380d1000d0340d005030302811413210403090981e56038005401c214288800613001c40f18454041005d10301c90034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 788577958 1250 788576708 788576749
    0x180609080304050f0f070b07060f1503051c05030c0d0212090307020102060709120318090c08010302240a1d0915090a05010b0414042a0e031b0d030e 65
    0x42c60300d04980b422080c13698407035043c0c000400303242c03280001203849411100c02c40c0d419540d400e142d10f0244000c1c160390619941c0c0510344440a01d010301e1038808503068a11486c00c450b6401100711540d00807400308500c04e00040d02c00c1002600300070948020301034030700580ba0301500744441c00c5a940c07182c280468407aa40d079400401c103030003950f0b03040280a8001c1c040741007142140e402e11080800c01b19411038040c00340131030b9480710250383d698070f249800100f06800781003202111100c40100b00300c10030311041e0321410320301d034244a0507400c041000b903070805500103003894030b1000030003502e621485403c00040c0a8910318801016224400d03aa03200780801c0000e80c0041c10729004022440c840a0441200c80c0d14010060110100c04000c80703007680d81080340c6008696140300080c015001a0340c072107000b440e201080c503850044110084a0b20a081e4640410300e04c00c4105042d5150081c03101b4007090341c41a4440c102d0b03400d00d603411044960003840c001c103900040310003040c401c0700d0001d4100443c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 788579208 1250 788577958 788577961
    0x60e0a0311070e0f040f02010c050316050c1c140a231522050304050a03030e010801060e01020a030804030e040c0509010210060e011412070b0403030906050307080a1806090803 77
    0x101c010721490000e40500d40020a15092149607040407210080004010300d102c52664819603008a040368841d5038080b080340d03514944482e02000f41a01044211243d200e2100d40709560f01d1b01410303000e0190750201646403100420346800c4201c003840540c1c5007080c050140000041040b441c69903040070ba251010f06042111031500900d407190b02e10a660121003054248242c01807000f4207002d420352003841c0c0e104048070f14200f250440c4a20f521450b40001000400000c25801503451040c2d203c00b40ca0348100c0303a03618581500c423800000000360058102c49a1040001d00400c2d0181e0064020300d02500210b48140c08642203a10451511020603c04110003c4640e0304200c3c0071650755070003506101c0239180c110140c10301c45060041c40030800c5030315594031312501c8501402000316110011201f40555494a681d01640103000a0f000070759240404036155006500326801560669900d00e40e60f9950500c202c0100705d1a0b84004801100414101c041f440b98024110001d0094070501c5c0c0d00d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 788580458 1250 788579208 788579237
    0x1a091b04090209180402011710050d050c041d030a050d060302031609151208030a020705150402010f09061209020301020405030d1710050123090907120f1b0507060e0a03 74
    0x11a42013000180f5080c0081040010707680301042c2407440c5503e15466000740c8403001b0f500c4840200c3d801254114260510036030a000700003410721102c500c2030b103040100103d281d08030030600701c54101c0e400c0c25500410011220b03a1041001300aa04224100003a226480b54002400c02402c0d500d59208110041010721850303016204500408000c0d00d1000000c41ca49040b40c1c21413407a900f4050008a400320005819035003603012101c110340d11009540702d0405c2c51000114460044d01c0982c00101c0e62070300304401a01681181c0b05980b1540c6941845a07131031070403c4080c3c451018200d030155001d000009441c0c03010081485226040c0e2904254036655421080750308000401c00141070b0380e0f00104107c1030740c10290002480103da072002004e0100d40f1410001d6100e4441c501c4c1e00101c5d40007c005c2d6055204d0580544030711840350038000c2000d03440c0d1302003d03110b0124407481204451140a0b52050280d402001c80b144204030103e17a200c98800414185003065500760302058244030b10031503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 788581708 1250 788580458 788580469
    0x20d08070501050a1b0c05160312080c03060618030a290604020f090918100903110a1e02040e01020313121404180914010c11011a091b04090209 63
    0x780041c0341c0d04100b11110484013503005e024140c660314400d000304145140c080c40802d00c40310b2803000e80038040e1554560b4a00e03010b0000703c841c00e4031600294240c80410822405c040031280a068010083c42c1494903003002c02000700c04205445a06105281010f80000c3c10030705e440c0c01807050849180c0011104d95aa0441e4480052403144200d00c102304d500d14000c0311509441c040761080c0c1c0c0d40c486540c2c030b950522242007400d51050705681300c4e910022551011940003240c0a034030076503585a501400c52005941c03000281ca0042203011b0380b0f2150355040380940c5a45030414002040400c046504040c0142280c0c400c0d07821042900e003003100350080c411003844103402c0324020718101c00c1400ea9000c4451440c000c600508020f0030070002c0400d441040c0390050000710380c005000e2280700310441da0260003440d144443c4404910381c075450440215040c8a95807100d806141c000800034001403c200c45101c1c001c20074940e91f45800c58038250426010090b101a099030312006039943c0a0104001d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 788582958 1250 788581708 788581711
    0x7050d0504080d0c170117120d0609060b1614160e160203030708010605091f030c11121e250203120910030906020d0f09060f1107030e010c020d0807050105 68
    0x90243c1a050300c1e1005c04040c1038141104d80d4607201a03220800d071500c0038146070101c0034028a04d100411030640c0e054107503000004a074400b0300c0030004503a80b608540400d00030302010781101e0240a034590b02080758200e1540d5014424020ba07502c44094010944495440c0e8020340e07290000c0300c00304480f4840784110003580908600055007907240c8040020918141401050104907006c10840160340f20740f1600d401d803500030748142c480440c103a01c001303000780942d10101000030010f44a4001080011a80101040c0f00d0188a450700005024424110a0a04200108030300402c03c60500000c9800741032222005413031078000102e0b1500406207003000d05c29034446c1080c01040b940d122580d40e1a030b404820201410081071840c0242419030003400340c811040e40c0203091220205031344450b54010300070f05100f804104072480c1901c0d04081284c00c0005c06424a1004201280100e07001d81107010b44280140340400000c2c0050380410f00300454050f08490203200882c014041010a000c0e20703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 788584208 1250 788582958 788582981
    0x1b04111902160f050a1a0a0f0903061a2803020918010513030e30120f04030c0b04030b0424141501180504020a1101051008100c120507050d0504080d 65
    0x40c9031b04140d0040c90034906c41d5110384802d0040281458444501404400c802944c1141042004c1400d003500b0250b03200d80c00c0c00d424450369a88101340c0c10060440040f8000d40030880b00c00305158115802e21407010400f0f000071070f4022544000d000c81d00d10034091940f08991501000c25908207030f1402414000144001512a00e100b10100c0341d0203040c0c040c4d000300340458581c03240490803c51592401d081c00c1c908070700001c1e1400140c44e0b0f0f00240010050003100d202d004410480782c1d445094904034000c50100a00d107840300130106010071085001c0303011210505154502d4410200e5100044a50f0b19000c01e40500c4640204640004510169010303200d0a00703103501180301849102c2c107071005501a41f4413032a8041500c018580c8a0b40f85a020185000020002811b244201858100c0180328040c1103114504441030070b00968042c0740e90300c0c68103481c0c4842d9290540039120141000410481c1007000c203012942407403009003c0d06002d940a03036500c036511090b5000440c2501c0060008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 788585458 1250 788584208 788584229
    0x209011407020d030f120f0e0f01150e040203031209011a0f0a0504050a021b060103021203040602070b0d1e090b010503120306040203040212030a021b04111902160f050a 74
    0x2241c0c00758403200c80200b007840c1d061a000d04640ba01c1c0c40d059440070f80000c6c1c00c903d2280740a0f41c92210740c1d91544607035038042031101100c80c0028045c0d03070907081c0d45030000031801c100e5011104205079610801e09503041880103081e44d0400095250310307102d485044035080326680d180e4902881414461960b6400310f20305540c03c1007116a80d0001c529042144d214050103580c1e5074000650104643c0d05803000202c8108128004402040c03c0540c2c0d0300081c00107071310489201c0102144500b000041f9001c90b00c894015019441c540205201380d0740280d15040002a01c805d4210f04071180445130104642e64038000007002d102c0340c2840410b0040c140c1006010768030841000340d10907800000d0301d50040d0304542c05a030729a114404640c0355504000e206103144000701d002102950040355a070107442e280740c2c10001522200040205503095811000003581040203c40410b01982940c00010303172007801202d4200d80c414050b19240481a40040326500a1060600c29440c0c0f03a401a801031899250 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 788586708 1250 788585458 788585467
    0x31014060109030203062a070602090312030603151312020d02010b030c011b02120304030b15030c1c030e0603070903020901090b0f0d03090e0c0c0c180703020a18060302090114 77
    0x8a50340365006003443ea0341f00b0171510303800101680e10b00d0000681150f02480e0383c4649032460f2000180d04240b20f518481d0041c804440c00c01d0040d0340c10340744220b034010028510341d04050710540f0344039030141c441d04046051401d802c02003500c6042c005d8061006038000e0054040440001342182c0c00e55542510079040642e2641d02ca81e07125141c0350b0003403100e640c041c3c620549480001d010b50124003c1e468203010100e00001400300400d00d00b4031942d41d1740110070110f5410f004050312501a646510b600516000351600f4020789000324203426807180c180340100d5004270001070410303041220500b000401c0980306004600340481c410740180a016030604c010b8a4440c0002d0700302d07091058960080100d8020a801d0510400801006040d048201e100a0a200c99148410f5201c100039203018400c1031080c18450903e101c661850700c042000c0c000700360b00c51003022006503000c0045102000000400e003140c45100071340304001481940c07801a0b07104400000500140380c68a51035800c54070900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 788587958 1250 788586708 788586713
    0x601110d0516050f0d110102040f032003071811031005240403260319021e12070311040305030d15030f0f060b030a03020705120c03101406010903 64
    0xa810a008203182007054032420075030032580a100c62482c010303090744203291045400001c0895a842ca4030083d070307102090b0658585a4a00b80d20540c0b08040382d4640420b02040070078030100740b04405c4040b08001c0e451220b20103000038a0f001050b0400d0010070100030f811617005e00b01c2d2184030300ca1100c80c0c0c0d0090075407401c11503059000d08a881414042e51422880041400240741c0400c400c1d40da4000c0d0588482d00da09240d403c0010003907070701401841c000181306101e003c1c0c034181d034810580c1d524001600d50307010420101a40004400001c5815160203503e0407450b09230280041002c0c030103494440e0325107008020b05803400780031000341014007000b050000c10004011184000c40e402e0021a85c0e840d42c00c011f48840000d58406050207803a03070064002c025044184072840c501030b030000d00c90305d0003d0f070406403035406068004000d0b038811202003080f41031107428411800c1c2190305030f0301403030145404241440218580c4618040e580d80154004803107540420341c2058085c42c2c15203800d0f0455 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 788589208 1250 788587958 788587963
    0x1002070e1503150c220815040209151311191403040303051005101205090613020f0406090507020f0d090b0307121d03071e0506071d091e060111 63
    0x2074031080f000105640006040c2c0c6111001c50f0302640c11801c0391000b2125005080140c0c07030345030003009141c0c040d088012142200700c800c03013800b035900102a40c00e241c40c0c2035103d200b00100000781c3c64218940c117452030ba01c60850f101c0e05c100700502040030b5a0b80d01100c1c0c1c5449071418050407038000d01101840e005601d1101a05032907100c2e6040c20006006c1d101d00f00300b009000300c160300259105131440c16070324050307900030280c09462845030030038000c9842d00b241183d150131048654240d1703c200e0418420242c5051800d40c0075105001d040001c44640320070b80c880c19240c0840d05640540c0c0a01030f000c601c014100321074100140c8510304114200e05211500b1150f10010304035008200c1c46005506071989a648100a849070441c0800c2d5108a140180ca469401100701650307250b04261072400c85c103262030301001e0210b5004022341140c1d69862016541c008004c265a1009844021000320780d449402003540240f03030841aaa18998051801c007040d034800400030303070410002071101c282d0300700300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 788590458 1250 788589208 788589223
    0x110418063b0616180f06020f060f070309020402090402030c03040c060201090503030c09121f06060302130b1e0d1b0e0306060f0102030c070905060306011e06031a1002070e1503 77
    0x8032a0340c0e000380480701100b12808076001d0701d080402d0400342c900007541170022220740204e0b0410703001c0e01c0100e1000008641c0741c1008540a502c40c00084000031420b40c400c0e0301003045980300401c01030510350050089000c9800843e5856900d007000810b120501030b0300d045110050130148024070210a180d0b54a80e107a02002e400140300c5040491201c441e43da0301c1481040183c144d4007201c0b002013a080048110700095400c8005040c0f4054000ca0348610074022214080c150310010410185409106541c948c4101c01d0503158014071700340761030202d002000500c8800d004c502c01250317040c01c0001f41c46038000c84064500a0000e40068801e59032401b0840319031007501296200240005000181e04500c2020103410250103600c0d004200140180d0216000300e40503800c98100f0f0303032510420030958072808500069440c00035401c20100e8440d40040d441189041149054603c069010510b449220100701003d41c1016200b0311032120341c60b4200e58002000c0340c405850055107800300ba1203520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 788591708 1250 788590458 788590471
    0x8070204050a02090303160c060c020d0f03090503030c0c1e011d041805060f06061e03130c0b0712092715080f0f060103110418063b06 59
    0x480720001009a24154141c2d203030b034200607094a03915210062010f408802d0380400303d5840e0744c2c558003c1056842040210001680905664400382160b1250101a062604201d040105589010609031000d00140c200c1780d080c60020200480e14408121120412806078500d000750b10803a005541c1e4404109140e02c907008261920f000c0c01000440c1c00303000b0015025403600100b8144004100b00059078a1140114407041003c13a200d04003003014601c1050054200046513480c4661424440f0b8001d50b00410300e060200c00d0b200182d5120380c04010b803130384000c0150744049204400d0000640e00342c41e400703407a868003070f601c6420300c214440a00c84200c00315240182d600d1000160082a50090542076044405400201d0361500070315581e1200b01c582401c50700139489042d046090001d0494103a0760300a50741d840e00d42c803801c140070003001e80c1c40d5040c140400c0c03000b164001c52403e216041c40801243c0065000850b039045400048400841019100c580c0201c090061040450801d40141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 788592958 1250 788591708 788591711
    0x20d0c03030b0118061205060a150503090f1603060f0b10030f09081201050a0e04030e120a1b08240f100902042405071a060301060806160e03060408070204 68
    0xc1021004807065690340b103010f18002800880441c2d1aa000301100c6c1c021458100c090109075901002d20601a83c94440e00c0303004d420b500d103c035003035500a0020310f510151070800c0710409140b110040b03140400c11400842440c0540c207003481800180c0c05490f070441a0745101b8452110350b00d000c01e4640f800452070804061344c50f02940e610864a4000000c0560001c000940310841401d42c6150500e00307100301407281258010001c3d200d6000002c9034480c40d05600c0343c0f241201901c0c2445074020072407000e244180602c81205000036040c80b801581001c51a0783e0150a81c246141180740140c0038102e11141e90303e4061803c1149205040742c1d030b01c1441c0040044090310b804040003141e03c0c49030082d4400c62f00100300400c0726407402440341444521040c450440e40c400107000e95552041c0c0748064100716103004510300d940c205100702c81e000140640002020b550326401c03542089002d0724804c01100005041055a41e406500d5000c1481d048000c0c107610304251340d50207813500c07030490028002d6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 788594208 1250 788592958 788592971
    0x102060c0f1201180e0a080702040b0f060a08070324211e03090f030203191b12050f01020a08010603050c0403080d0506091f0302010c06020c071d07020d0c0303 70
    0x4000c01c0c00d4071040c0140491610140d40c41d0741ea03d0b00640041400420fa803450b000381e4a0307100d50300003104c6c036403141c02600c0585001099020f100141c40404611078124140809120440c0c540e600144481e41e01a0749411050912141c0101561402c5001c101d00c1c03180c044900c4c2d03103840000c00a000322003903c0052a00601c0c15034104c0240c10a001001d8081c1002d070b429020a07191007e803425a007482130703807800c0007151507488840c06440c407800060340503070100c01640b00911000443c0e0030058080d5104042c0c01200b081440030304440c0c0e8225622180d244902901004070400c007400204420300d00950800c0c3c5260301c02041c180c130500c00c0000301512000840c03503182c140401c41d4090340e000350101c0d503103011055024002d02810f40700f040c0035660400000b17072604112044441040030341c407820400306203540c00448004041100564140364200b01d4103800700010081940202580680e1082c03a81c2002040d02a1100003858481507410402401c0d103515030111007607800e250b0608000501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 788595458 1250 788594208 788594227
    0x30f0d1b0f050703030e030105240f06031e0c07120f110a0809030d030e1b04150305060f0a020c06060d03170f01050f010c020a1a072906030a020102060c 67
    0x103544103030005041c588081c0715100c144000483c035401601d00907214450050520014182207460455480200c0300e000014110641840c0c808505070316002041c203c6d00064080001c0d03040d900a440e824545241d0b2420301d0b00c2411130b0440c5d60f44c88010420401c0c145030752512095110385000b20680d0400099590310741415000300c021703040d080c030101c04275008440c4038030f040e84a0b0750280c245140329101e40800242203078800d02a01f8541111040030b00204041c4501203501d29954a51040d0f0243d200c0a8140d5000c4982130654020f500540c020300940c10140e961090000d00581410b100600400c1105010750340001c040d5000b180c107075006200c4d407840d418121001822200d0a00c1c20008032801e0050280380d41ca100c40c142d4a044940c0700359030803100015141d034407850300d00035000b001c4000c00300b000b01d102c0070700c60501c515824401803900d800c1d5038641039001074403100c0404c0654080801c994075004170011b25400b042c00c0e402019040c1040d00040c0d96401c0041964400903000900c402c0d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 788596708 1250 788595458 788595497
    0x5040c090b07060c0801051c150b030313090c090e041113020c15010902070c1a09330c031206030f16051906052203020a03081206030f0d 60
    0x7014044202074940e40710b4980034024181c800001000590018004212440c1040800c071480070020117403604008a55606850036401001d15980340c0c1d5150340c0d2034407644050006003407410700d102e00d00c0e18180c24110080304880c0d03120242020480c20f9034051043d81c10100c001a005031b000f81c0101070b000840c1000a203d1040c2c1e1000b18580c40c00864070300d00d01000001d081148103214005041d03140c2c1ca4510241c01ca003c1d0283c0682900304651041161100c0012800301a003a0400d0700e03803900c254440440c10070541030351107d03516219480e03009104049148480441100c1d01c42c000d01d81b8007000441ca81c4d9008180c5c1a107002001140881c0056030100145a182000308041d01e45017403940302c1d07841c00e1680ca032040501600729192030b03a130410000c04119040d602c1c1c0d62500c5042c0031203c410450320303031718000384500b8401c154080400541d80781444c0500941c4a0310f01070740c0e80d091060031302e00c07a0b100c090030241c000e40c40300596030481d08001c610398401403801d15120302c820304c17081d10050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 788597958 1250 788596708 788596727
    0x12030c0412060f110a090e09030d050612010603051c0f3518060f0115080a0905060c0403030f03050f13110405041a0f0f01090507022b030b0904080405040c 68
    0x300c5651130401200000d401c0c51014140510040c1c480201c559510080110780b040116000160f5410030402e0551010f02644061f401240240c43d0400302e2070a100e6003401c45000d604140c9440d40722400d0b0440850a0100201c0590310600c0c1c00f21007090702800c0605040070307030031001070a4592000d800040c0c0705030340162144010907040f13008050400d10340c210104140001e00913010701034080040c04008840c0c80d154103c0b100b58400b840c08a2003500200c68200c1c002e03001400e096190003001c0c0206000300302c01030142e07485145040c0d5503480c5150250005030700103480d50902d410302040080c202403120300c5070781c000c5114202c4d900308101c2e868000414000a8201544249801c4c248000e020b0001001c410741f03031075220000a16220344c0c10b2031080300c1c0200d0b840640c004a030341c0144034602c1d041e04002c5d00100300780100c0b200781c000304440301030300700158440d030009400628107884480c1c0d06007e640c0d49c0030340940c0d48607a5410a074580802500c01e90061500807a02c07030700350483d454840e00020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 788599208 1250 788597958 788597981
    0x20a080928060905040605060703050a0c290f1911070206070501020414060421060f1b02061e151212090a0b03060d02041d030f0c12030c041206 63
    0x1058244260200c401c0020824014000001d2100c400881d003401e16124141c00d8400c020401400c24025640031035513580240005030402c040312210900207224080d40c2000e8084020840d11440c80100038821017050040905250703c9a19061001c421418100e09003a0146001e01003100100f16080800610840300002d4108074002029400e110065020b80251440140c00f030140e03014a40c20040140203078061500b4100c4038031800c1c48442001030209884503c00c0401040307130b01c0810146011980104100c0c20144d0f80008880700c40c0d54103102495001b03454110a05034001d500c003580000388002071a03d5800c0300012403400380c5076240c1412a2581c0da41800300d82d4001d2050002c040c480d0071102ca42c5003c0c0070721000218222060b03400380ca203c2d080250404a4000d460340801000d045051030510b9107201020303e07010001da003072005002c500741007074146584105030050b035840c0031011841c1d039259075018030900000c007010a0458048551440f00e41042c003ca85c14003900070001c3c10f084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 788600458 1250 788599208 788599249
    0x1b0f080c04050601031b03050a0609090b060111010e0c06090a0f1212020a3207060e090a050103080708130f090c030b01021615090510032a020a0809 65
    0x5248a000980c410240001e44081c44103407076a40c015805d4515400414004664680e81040100c0c401e41c0101c2e801902c0d89000b0030f51594810446084070000711096078940340d40c2c8100f1040d23581164a0140085041000300411100c2d0b132030054694581080c40c6200b800300045005031541c07031280c0e440180c406541c000c00d00558654812801000580f0104e5080c102441107090103400400c00c5010340b904100c982c10706041c180c0c040003680381102c144080d0651800e800400303800341040104041c08881d21005905c5101e1410012000b10042c1680442410310006200207a0090103031a03402d03600041050306c0303445801c600c120240540d000100e2060070810000745602c07180d0400040d02d00c2c252010800340000c0001261602d00c0a04c0e50382c202102541d0800c0419540140c62100c1032003403821a000d681c0b0760000032108486118518006a00c80100800003000d60352003035024542c00c036040340d415a1f00040a03465001c40200030b400c1071004118031034280c40d1202e1400005100c00355 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 788601708 1250 788600458 788600489
    0x1213020307050f0d060f0510090c02030a03050a090501050f18010207020607060504030917060f090c0a05011b1722060f1d030a06051005040908070b070203090d1115090d1b 75
    0x5607100200422280c42001c4040c0c1c0c140020010ba00d8401cac044603104640c013452902003c50010f80191501801522000d6698007090000c60000e2007100d018031030a030030a00650505044c51003000e4050701d03040d07a40d648100319060050340d030b00003100c0080e5803000f07010510350ba450506880d00c941a600980c1c04030041c0d0120081c2c040302048042c400c2c815502c0e0341150303403103100c04190b0fa1252400344580181e5220410300666001d481c001b034440e07904481d080c13155202e56940c0084c00382c08800110620b180070940c40704002c81410108402c00000301c0c26402a0300e0002c00410310032094680000703100501c802442c00c0e850700c0c040c4042c2164050210303410301805160000c0100001c9403c0d48000c3c02102010840b4a064085e0071140b0b41c104502504110040e25510390b0204080c0600096100030080c5081a488407802158820302030a10071010300b03080d80c00e00050f005854501c000313103070081002c0f101d40d9a0f041406110103400c240d52441a40c4000368001c681842d9800201c070b240441d28 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 788602958 1250 788601708 788601731
    0xb13141f0c020306070c020919020d11090a05060a090303180f0308070317070203070311030d0504050f06010524070c08030f090a081504080d0906060b1213020307050f0d06 75
    0x40c2004480340c800c2d001c80c3c21680e170b8440c049907900d0544400035401110345001c19040b440314513104030004e81004005160444408415044402100c1d8001004a01064401940c50b040185034024941980c4440c900700c0340d520001c00444e03c50100a00340045070002441a448600d03444010b010b10150f400781d100d490b802d04210f0780c0c000b5901140000d025001d800744214555000c4c9000d01c0c40358008600308030081d0350a55400441e035603480b5240c0300503c0014040a03c0e401040e01403030082018240054001c070500d401c0c03040503000b040c0246054080b440002c194404800500d0003000a02034403481320380b401c0c6c240100b255109089a110205180402c102120014241040200d50440302c0f682d4030b400302c40d115442d04965210028000d0700140115503240000c000e10044240b0014181c6401c0c0d4602d012150160044030404034081020810741707940090203600111050b00c0c0784200c2c540350340082d9442d10140a0107020303104480030b02c03829460705d41c0034480d0316501403c20300980e000e00307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 788604208 1250 788602958 788602967
    0xe0d1112030c370509030a02090f10060305090705040e010209040515040b120a020613080609010213050105031005120312010314120a120504020a03020d050c0a0b13141f 74
    0x440484035401c840c3c114454003250300314a006031000f454440d941e042103002e815206600505841501030189104a00041c2d070f442000520401b820f240603200c5003048052001007003555044441410b1400d420700c280608001810801c8520443c0c007c00c8105013000c2c1e09019005101d88030781c000e42020140800004103410741b840202c000d9a0400601d49164100a18070394003075242003403504440c51482c05803d1010042240d5003034240c0300000d043d0b0302c2000614114045585010701c0c1d6020501c901e10300c510440d07400040c142441d0460660900b00d5080740d4031207403842824841d441200e101000340100b441521421041e07151007a1040da504d082c954001e1800171800350035070081d9201509480259030644607007520aa56150403100106000c01c010003020340b0a030390100c2600c2c000401681c035590244074091082020300481012030b0f0900c04501001d401c4020400c074180f18150f00719010710100c0c021a4014150450b0401c420004a9180791030545125020343c0032010124031103401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 788605458 1250 788604208 788604217
    0xb0307030603140a05010b0a0311041503050706050c0c010e10110c030d09090b0109030f0f020d1707030e061c111e031005040b060a120f0f06180e0d1112030c 69
    0x51001f4002040e401e4100110050780380402455075111a101500ea810141d01101941c6041ca00c5c00e6000c0d9102d80302c40d881c0c11000e9000c000024000a240d0400b040c0c140106408024203091080b20743d484540000d15000402800808105613418000f020901c2008420b0722040090180e503500c41c102c540c0100740d40c1e414015a09454245501c201e420351007158044202e0342c101c3e104207010311056031104029000e00c40e0507640095036041c1f80c0c021a07401c44544054101000b0607944d2a6010b1401800c1c0c50100c1c01200d100318010320444040501c07900801c4014085140b00007520041c10745041300758001c0c4a0800001c8000150714800e903150303d0019070140c44458501c0c07200da0740d00e0b010007043d500040362882e00500d05010303247c640c901812400c01448503441c80417488003004483c000c1103c01c0d415140c6002c68a4050401602e84002c58500c58070500c4a0144200070280d843c4a5860512144090402400c0385144022003020711104c0851181c01020f641d9a0a0002e00312566412 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 788606708 1250 788605458 788605463
    0x1514160c0c0f062703140715030207060506030105010e0c0c1c0818030703020705040e0331080105040209011203140a12050a020c0703021504080307080d0509070f0b0307030603140a 79
    0x210913014800890f54144285040560f07048440d503a40d0841d610402c130485800a219160b1003407040109600c0d41c9890120442c05040d80c0060701d0304500c0c14601d0596038054050b90180c2d1414005119484185001d5544500080502542c5086050480f890132030203019841100c5801101e00342c00d83e034005642401410b000028440540141d81800c3e10b80c4103405008015900400c8100990308050f000240e07030f4502e01003640d05007030b03001c02c1403154140e00f800d40258602c611003124a40700240f00c441c0b07000e084044000c01c400d1506501080c14040c041c0a0328403a12010f0421404043c46601c0074140794048001d91929022802e00107401c0c1040340c1d5000003c40c1c201000140d18080380c0c426118401e40740c0e00146041c900d10340910007001041c051052140804020110340040b0810041c2111440b660500343d40d214800c0d024030488001501a01c0c00d0740003154204110006452010160f0b43d0701e160680d1740780c94503041500201200d80c402000190a2890740800e258046140040c5a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 788607958 1250 788606708 788606717
    0xf010e2208120136020c010c0f020d0207050904110d080706090519050a060b030c060a0503190b030304180b040507020d021c0909110c030c0601031514160c0c0f06 71
    0xb600c0e8056000d0b90000c1d000e410340c098144120130700320000d070300b92025022500300f240103203069401e0080f40e0035140085190700100d021407803d00082ca50400480071042000e201030808241000009442107102a1000c0c040400314101d000483e5518040600384a0384002400e603660701c28030b041000360581460541e11802503032000e8907a1018603100c0490654008003400d6400c030300d5500d8030300404050b404150035106508014a031625600001c0410442a0b146d150f00ca160019248184500c00d0001c95244c9090018001441d14008181c8040d5902208800d450b05100003201005111203039403e6030050130b05080c404c807031f50040798545000c5106da0a450440c0305211310100540c81240700c15001461114042102c500f0940c400d02c04500300110403071034001d07135440252458011000902290308848010000c000a0b032030011b54402e082c8409000c1c080d0041500d08134580010240d84464020381e400001c840c1c401c26007000e1050340005204c0100d43c80d01c000440005650240c1c20214 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 788609208 1250 788607958 788607961
    0x3061b0d02070503221d04020f01110c0603010602150a0c020307170d020409020304150e0309010c1403030c0a091212080606090406091b030e0613021302030901020703170f010e220812 80
    0x30032806d001540b2854025000c000780300c01c141300450b1a0000000b5484da1802090b0b141030050b91044000d500a001542c0200042000c032242d2020403600071f001c118020b4500001400d507070b50003209542c06607400044014810003a0016030b005842218407090f441840080c0c0400c0708149039003d103020b1401882070000c2c04100c0030701d02c42203501400e0300004550043c8a4844550301c50040801d000e845401c02135050f02d200c401c214559042074030042407d140114642d000503a110301490020b05a010610440100c10344a49203e02c5103c040700003040030341030010388140c40320360031941a40c40182007042020f9a401d4a80000c0254401000f100700d260302d1414002c0c2c2c07003402442003031000440a84402e4890880c5010346441414080380c0040740c00076803610701a5244065071090140c04000341e69041c0e60300d40105001c0701d80a0031000200001c00b40882d800000310000e0540d40305954031622a1650b4503107400c0d1060807103044113028200d28029040080c8580900701260f040c4180d400103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 788610458 1250 788609208 788609249
    0x31101020a050d140402090c03151e03010b06070b04062c01060603050c090603010b0d090803010e0103050709020c060a0e011104230a0303021f060e040503030603061b0d0207050322 79
    0xc004017513801075805000344010030000c0100100450b008010103124004c1c40c3d001d000031400141c202c42e005810707030f114810320211a040038060500002c00486034185040380a503244689900040c0000e008e007540c80c140341e100d454080101580d0300a00c1000e9404074580448458003900382409003030000307401c5c60b001c00c050f071a201c801d4074054507005120f6421a0f007008941340813502b024065901c1c00ba100e030144404901484003c5000e89888440030846604505003c0c0c82c00d400c40d4070100119104205041c0007800204405400806548001c40c0c10f03030380e03244500d01421040f010354000c4080058001200e10b165000c0701080b80e1582d0760302c016200380d141080300640140c8400340258100d5012154556140c100c070340481504440009034007070701c90000504001044500310f543e23074800010b11940e4a410030103150b203d40b1182d01004566002010f007d154000c1c0e80d261f0030303c42c0d004501c02c0300304035003030041d03075505540041001e203101c2000ca102116541a4442ca05080c03400040d484003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 788611708 1250 788610458 788610491
    0x380609030712050705040510060f0206161d09010609061d030d0503072109152f0705120a090902030408040b0309031903050709080a02090105040207031101020a050d 72
    0x88000005018000c068038000402c1d000600c00311084802d0b0084401c0401e17255a940304850003881c443c0694202e050900c40007610003054890480250b40c05070082241050703040d40e40e43c1d030320100c601e1708601007403410000c0703100141003044285d403242c80769001040d20307540220f0082c2115807039a2807550680c5080380e038540248079a6010fa800d0381285200d45442c030b003c6c50055420080030310b80071800140f044502031350740f030800c5a80c0e00c0480c0c44011070070034031501e88030007840e1420b204010810381614040b0501103040a044485000e80300894503030050790081c0945240a4100302a03801043e000544006580e100702070b2500481c019400100302009a8820740e0f206650050441c0e2806003004140c40303841d000100508014881045144501030f4242040942030485407408101e40c20900c0340a8200d401d0f41d0010b5407180c0c031524500e4013582d90201010b044610a40b001030b40c1d0003203030604441900e0096800755440d80005122611103502900500080704e2080080080c03241d071590032030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 788612958 1250 788611708 788611717
    0xb0342060d030f0513031209090203060a170a02120d02060f04080301050f04060b0a080a0b03010b031f18050a0b100e15060405040f020714030a02100f3806 68
    0xa800902500d5030000080c003c01442c041c00c1103900308682444800c0c11a25501c255640044034030300303041c0c0c0380700150030703001000c9030050000000d0540c194500800800d4103036030b0b98445d0810f24014900e00403000d4100344000f003022a0050141e40c007041c03480612a5a800c00308041000501c1820f0004502000340c142c40e6000d02da1080e80b4524507480c05003040f60582d20900040d41c41599003600080410300c080080840780540d4940e14650b103841502403040701c207a456041d00070b904002c845451a640855961581200c0404165050f00c1ca42498002080000510b20f820040e0720820024400009005000b15108a2403620031784d407040e003010b00a808a1003140d0b485100480403842640740b000a0001e001c001520050610340c0c0d50300000e0545020075800c002d03080c2d000900030f0510154a200c40b014a0006000394a803008801c0000c0d84d6103401c14a0350401980c81042c1d0b40050110b401c00300e05545e11187c0039540311541024038468203000340c1f8480c40141e1450b0710520b80c0c1040c0e410784 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 788614208 1250 788612958 788612971
    0x91a0a1d040f02130f0b0306090d090e04150c11100614091305060c2206050313150c05031f06080601050a0908030a031d0601030f060b0342 61
    0x411040e11155200328500324a008201c4e8410350041400c02d0605413445440700e42c00c01c03000045600311144040c9800c00341c0107400132610740c0010701800c1c00b03e5041080c1104450040b00c640706140c0d114100022400014041107000e1030404035107001241d4080b98500a500d41c0e1020b480031608804280c074101d810510481100400f042c0040d0a50b19046552651040141130785011141480e5681c0382011022241004e00c04400303d014107000c40c80c0380c1e0110180d5552842511010b0501401a00602006101d0030919442a0088040002035850000400740c1c030041400a03c1c082d10000d006030b0000c4a00366800318800c20801400c01c00c20745072200701c6226440e84403c60f02e4240045441703034400721480051042c071200001da0103600b0402003515040d82d036030004a0a422000d1041080080840c00101d0f81c0280010710100346541d03001d615465000f0000100020154007103414051012070581240d2003204014400aa489c2c1140c4031b0880000e001d580200d40d418000255590140e825 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 788615458 1250 788614208 788614259
    0x2090a0f06271403011e050108150c120403090e070c0b0618010510051b0706020f0609060a0213050d03120506010221090d0c09060e101815091a0a 64
    0x3c0181c0343c001c0049043c19203020b000891400220403480790390040b0310b0301020341c442d51000100040107040c46030030400a040c00b00c000403418038003103e103200e0281111000743c8004c08008a400c050203000b0403c01000b91054480d0b003407800c56009002c01c004c1903000e03984031030007074005140c518010302e006c1a01d0958110a007816400c001c01d01480650700815401440f404021566047ca40704004260b65040c00c4c2c010040c403070800d0002400e000050007180c1d0181e202609200e04200d002c00d056034400001d40e00141c4454070900c0c1c403090781072540d0041d904454020034480c01c2c150702c85104600400c01403000d0240e0345a4a00490340e515054201920180e5600051180015000c0007024812001001200c114040361031f02e00c3d2400b0980d000443d969580e2070708014200121040b00e0380b1082035070003401110701d00728446605e106055445070074203540c2c41d2011040e20210f20241d0160100c01c43c01c01415a080b80c0d1035149044c04000c052203002d41210018142c07942c5100300610300c03948000f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 788616708 1250 788615458 788615537
    0x206150d02060a0c06110d0e0c0609090c090103150602030309070f05010e0126090f06060301150e0709091503140c01140c010605030105040c09050601020601230402090a0f06 76
    0x2000c449009840c04100d51040d01d6841c0707508686e84c59805003c9501c0140d00005000940c030f00440c0c60202c81d80955401407400b4072450080c0d685017083d055100050300390701666006001c00480043c2010055400304c08414200403070f001d6800030103584038510131821038200310384401040b2201c05240c031800e40010100a001c0c01a54402d0003a122710512465081a02c14100680e40511000c115015441e03913200c000032005458040100da07402c17407400d90081064900c00c0c600756500148a000f2454507000c00340216207507a2103048803500804504030100030f88004420103944d807070380340e110940d206250980214013561001c5000e040c04241612400b0081e00c45801102103a00110480ca00b255680c080015064600380501d40c400c2d8422501d01b81c0c01810700d803914040fa07602034900c80c1198840c000500402840380c140660541c80e2050141c4101000000180644a959034080c0c01030410030b00022448400f00401056400a0310341e01d0b007030300340e02074400d81e5084040100d6030310007003150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 788617958 1250 788616708 788616727
    0x1e04050c060d06120f1a070816051303121101020f0a0c050f011107020a060309030c140f070803041406180402030c0f1801021011180607120206150d0206 67
    0x40c0104a080490301c0c0c04201c40313688440c159004424550709607104003a5403403810402a03025041041c010f40e42d40e8a044508103140000c00300c0c100101102102041e81c03030482542c1c1d004106940703030700785428040410300381c81f0b14100310f003138284452030030229000702d803400307101d20040c02510300c100300c02c0045605007511070004075100303114981c00355190300501d4480d40b9869028015010f054108050310b541d11481841401400d0b50254800c40c1014a054012000603902c40c00940005812555220400041e05805402d14410812114040c800c4c8080020022008005001107030030b002c0c040020a0340a2062025034403c010b102408081010200040d6192a901a42d040004150b0060500d080b0502c3da02c0c0e264428034010300d040c00b02e05000102d0703690420412100140541e41404004181c80c010002d5005124009140390650700401589480d1002940c40b019006200102c0f8030303c0701c0ea4044d40760801030364410001d00c080c40d050135603400c140f030516400c0d542c0500050b14004603807 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 788619208 1250 788617958 788617969
    0x510020c030c10090e1501090603050402100e270f0601032d0204091e050903341205070507051009090b01020c060c0106080c09100b1b0303010e1e04050c 67
    0x140d090f070b000c1c802c0c184004205004020300c100c0c0710303800085100f0b50560b242170024020300c0305640a04201030911042100607200c0000f4038070112a1800c0c2042d8030389141e40000c904441000c1d4030003004140d00d11241200004410850040019a902e80c0c080d4840400440a035012240d086001e46040044a400b00219642d05842001004401030801d616000c200090351040441403a0202091035080551140b40c401d054000c15410b0086240500001c4505525540d000d4640300c030241030070300240180022100030282941c002d241c800c114010100282c400d412501094986214180c40402c00c0d0904c0d01c01c0d0081d9140a80b42c0c68510f42c607122050007d000140c0183d811030213550b0f02c0c43c002e525050064500e0412030400070030001d040c081c11034a004070310322801d4465001c207030034050030180e00281d80c1c0a40d4010b01225655613021070091404110321082d2107400e11000000256181b514018980101c0030700080c07828517035000300c150414034001e46018015801c040422641481d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 788620458 1250 788619208 788619229
    0xf0608090123061e0f0f0d0605040303320402060d09020a08012007080901051e030f04031d1e0109080304090f1b14030a1d070510020c030c 61
    0x254008240c6292a0240d6540301c0b00014850000c0260b01050041914080600c5860601c0c2c00c404d01601e80328000c001002a0362100b407060144140041c02c0440d911180b64805c9940e40000c000d00443c11b082c42e008000340048103810b4030341c0800d145208596210381c00030bd10400b110404c240000d0b281e0b60208401d59000100d90010f0991340c020382c800503110607808a0041954100010700b00c2080c0b00315030b0342e6455002d82d1200250080000c07000084c00700c4141d03180c400302881c0036910b8900c9464000c51125101c6c01c0e41800c2d000100c100815852501d0900344a144a5a100008031030b13010b0130711030002c003d0300e4050352000007000e6040100d0805ca03500c1c012100c052500c0f4104030f650315040ba046600680100342d005031a1480840250040d02036520301c00800d090500070008032213401403002c5482501018180000004120540501d40040328100c51071198005c0c2d1421303080384aa80c824a502c1058003a00c13008000ca0409030002c1010100c6013405000f0b06110400c0d40f08010b00c03a0203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 788621708 1250 788620458 788620471
    0x120507050703021507052a0a06230c0601080d2c040902061608220302011409030a060c180519060c140601031a061e0111070e0a0603021302040f0608 65
    0x5021740000325104001d903181c2c04900c01401e000381c45096210f81c000441d02c49043d40512501e04040041e9903110180b0741c49251400041c1e89011030024a0015601c01c074402c1e04094460240049032440c0046a104503501da240c0341c080c1088030403a80300c140c80783e01005200c05041341140120003810990003400403584010030280c5440401c002c0380207400d0180600b41d80d0303a1008a46c40c40c0c420112940c02c00e0300f2604401d00740c801e0b840c55000918031001030070501c0c0b03140c601050000c6d4584040081052981e4481c01c14003901003580d078020300c08241081690a41e41c2d000c3e00c00113060400c08003542c41254152a116003240c101401030303540e1030b02c1c00000c0382d0740d5a10712200d40b1083c009002c40ba0195104020402d0421403041482002e060040c040510030303500215851410306d50101d0b200c80904080c2082e12102c44000015402c004156010003420951442000f02001c15a4085420b40b44201d4803100100d800c0100700e000ca00503402080d081400c0748500340100c0b401188650350214 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 788622958 1250 788621708 788621749
    0x30207030309080f2502061903231501030b010f0e01090b0424050906030720060705031f0b041a0c0703080403020405090d080403050f0705070e0412050705070302 71
    0x480d00c1d80c507200c003540041100418918041001c0400c805c2e1084041d0356094851a00b50400249800044040c4200c0700c074501c8421202c54140d4400c0e009400000340f444801441184145882403544100b5400700c0d100c201011039000804415030091243d0403130a01706954070140061241300c10390b810380c40240014144450828001a5000030000400180580f5007a480d9944100540015400074030002c3c00e09114090107809919220401a2640061389240000c044e54203407601000d501c0d554a5101000d00941c01080300c290f8004000354000d800600c00e0444910b60b01c40810324007007850283c0c0d10503440401082000c00060000d110808600306002c92416644440d01032408005501c12200141d0201d8101305600d4140b05540c1e03c140c016002d46081e8402e03400040c0f000310001c10040078040041421000e2803620300580756125405822501a6511400360603d11142114103e62000141d1440d00d40c0c14401c0c2c040c0d49000750300c007005000c82c500715030811410203600400c160b0240c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 788624208 1250 788622958 788622971
    0x130507080619050405010b0c01050106050403030c15090501020a02010912020d020a06020306031c0909110403080a030e0f0d03151535070509120c0319060e060405030a09090b0609010302070303 84
    0x40d40c40d4403801c0d0081c406401038948da110054400c07825144141e00000c00d2003c14481000400d03081455189101c0c0d00800c9010302c11800e8815600528510401400729032010598500c203980541c031180c541e500550210301c01000304041207980c0e2171341c00500001178000920540010301c40f80c010311780011006098074010a80d4507074107001c052080f0380403000241c8011040081c100c4501c0b46141152041c13890600e05425501c807680c05100e8071104001305070365900601c00240c01445200301200d07000d0280c480003000d0701401405042c510307015031041e40440e1000500100b072010420103202c50391300e890b00040b0020160b000f144207c1c450660f100c5a001d04404586030490344024851030f0191a02030700d4850200070b00c24064200c40d48084554410100791400d9500024800c40c02110718050410328035062a2040103008041ca400c03410388120303000e20040180110160601e8040347e55550111a550340c80c0d901a1081a8201500044208080c100707070751182d002011824013a04011414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 788625458 1250 788624208 788624219
    0x6051309050c120d0e010c02180a0f0501090606080c07021828020406030507020c0307210c091d03031308030421030209011b0b0c0912010e0309130507080619 69
    0x1c843d000700005200c2e08816a0804a19084140025403490a1800c418017910310f6020440340c54a03042c0603004c000d2500c0000d044043c2c01d40003e82d5400078210140070a594804031000a40b1142c041c50020600c4000014080d02c02001969000f0b9001030156080645074004014100400f4044a031801c02250120100b007a46003807000c0c509281c41c200580d40d80c500100242121303005882c0e04215001025202d1443d83c00107007000540f0344000440b030400c0c40d40800700254000d040802000c3c280c0684000400b0340550303010040083c3c0f04d102000110046003c4103841e44000c80b461204070a546040c5408542410040c65215129040b0142c07042c030720b550181e4401840198100000744c0014900500b96402640c40c880b01caa0011040340313890f11691501c01c07040004103100703981b8070042500030259039241c0340c002c0864212002003222038680769801d502d030b600164020707000d01020411801c0440c403c1c0f01da184640c0951b81c403000e4075100c103000c0000c425241c00c0748070341c00300074038401040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 788626708 1250 788625458 788625469
    0x8130801020f0405280b0f1e030402010305131a0c0c06040c180e060604020a02010b18010914090303132f1801051302130b18120106051309050c 63
    0x100c09421203444070301c1e04042007580301c100900301c4041201c1400281c81d4805200800043d1148040c0c000d8640c4407d000224080c000d500c80c49081052034002c104420011300f006500850003030703a090010b039881c0c540400e0b60465004006180d20400f8814a40d5414500070140e00a80340c41c0026240a058021480c03a0100c1501c003941c00e50341c03401d0b08100c0d1201c00307059820203002e21081440140084483d4503201c840060046010b10340000324091414401e40c00880c00c05801009a007029060013401541500240101c03011549803110500c024a000c5900c1c41c031550086005510315904d102021a20458600d401c0742d5002894865134204481483d182d0074080071403021082001d401000c100d4841e41c00042002800b11020041c03215071905042c8100520341c001c1c0141e035540e43c1402d401013050302d076840748440c10f501185851584401c46011941280c04840d010310280500032036a003200d150303204880d8840d605400030489038816800c5000036500a50640d441d050003500820f1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 788627958 1250 788626708 788626717
    0x32e0605060c1b032d060f07050a08060a0b03070f020622060c1718062202090415140402031c020705010c0203070b07060203090d09080a02011116030503090117040b01030813080102 79
    0x2c4134001144040d45e10114200250350340f000343d0b00c0b40000c5c0d0742031400c00601540b01c0d01044904020042001a038a6118203807180c0060802504090f82d03480e042000904514a14518a006000b035102040c00c08503c08948500c03100d140345000c01c3c044455407008000c1890b080104144400c03580100c80883d9103c000b544101d004145550b05603228511042c2081401001c00f00c040b159035822451182c451101d001c0190f074156142d40ca291a2400c1c0250610081d03030074400440d0030711202c6403d14808503640c034000e61003030f0100c460780650700c2200300d050851c001c40035006a1022504029035840360034098011800a03050300d602c20380b210300b000f5503544103100c1915865000030a020b803081041184802503403042c9011566181010795a545500075003030042e04102c5200503c04c540c1c201440a042500300d441e04445801d50340b0f1030401d40f01d03000812024003248120520910000d820745641d072041c2e600041440075a03085954841c09a0404003241d840386440b1640801d55090910040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 788629208 1250 788627958 788628013
    0x14100308121314030910030e060703020921150604020307020c0f040e16031110020a0303090804080d0e031612080c01150b040e01050d02061206032e0605060c1b03 71
    0xe545c1c520301d000c180030b60182810151020545015144100c4203008900c03241c00429070f203000759881030310f00c00240130204d1401d012440404901e1902c0082e440001d001c0c01c1c05000d404902039540d40350301c2003200701d0104031840b90168014444034000c0e45840c521486400c8030081001030b1020921081a185c40008003403941000000e540500078030501182040311024211064a501040400029191200320000500380b40c1c903200c02d1002c2014440a5501400d001c2044905240c0c2c0781a0003411040f0003000e25020780030749a0610b07501420080b2080541d80002c91010b001982c541d0351030455480811080341a5507071f04103501144000642c1c0500822000c0140e540b2a824006018501d034810303070050707100d007190120341c000513102c0b202621030b82c0014000c5540030baa80c0d4000700f82451030f0b941d150700142e901000400c0c035582c0b03540800c1c10b1020b01c4080802c2620b80380d00030b104080c400d2072018215680043c0c02c2c1c6004021001213031500540140135546541920a0104540107508001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 788630458 1250 788629208 788629213
    0x201180233040603140901060503120f042103120b0a0b1b0d02060403110c0f09060d0204020f07031d031908041e030302010b041401090f02040e0a14100308121314 71
    0x11462481005c070807150880400341c0200a203a140c400004d82d11040c80c5501074800101044403884c1004d508280c0b00144440110326084d1501a00c60702c1020ba2084004c07404200c5103403201801c1c000e6031103910000c200c050a41d41c415030401c03c0d4052281c000c07500300e0300c458185542100c400d0030240312484445255800a02c22414240750140122051410709082903201211803215603440340d0800c04801d005443e090000d44880e030205203820460103000c6d40050000031034028901c8050003d210312402076a48a50310380542c4000000000d660000c9941544224601701c6400d110201500703400e84504030390340c41c0c82d94602c41c100001d4080e411629035403004003000c106268080c0074141c81c050048608204100c0b001044604810041c02141400340e0b03100500000344003654100c0e0701400900e00d03000d030245000070000300905141818142092400404a8000c0018110761b50540303922143c02c44c180712802c00d1074102d000c00181110003030344030002c4010104e54484a10703105010b070b440c007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 788631708 1250 788630458 788630471
    0xb030a03110f1b010309030c050f030406031505060d0510030c03120f0302120415090b040b04020a0f0b0f07061805061f051e031f0203070201180233040603 68
    0x1c0040c28400842d20921854000031811515200d100d00b41c688840c0c000d00300014040c00e41e0900320b0313100b802c04100905038460a0705425401000002400172548266401c3c031030305220f0f12107210401ca0a1298981080d018001401c0119041d08415400407511031542d03015541d0303031140380340c0f00d46540c01520065440300110382c407168400b04c074504015030fa0030300b5450300101c0c4803031804081004101502100b1003000c0250b8001258114000180d000541a4914200f60070032541c2c00405030380803403040a000300000f5801d014078601404417080d02d02c05a040440c92150f144880e8030041c0c040321025035a840040002d4040b001d00300c001801034005240c1c51a0880380d880c0c03403000440380d00484904d070750010002c2e5500d1107040c1d40d910044c204070418103500c3c00042407410401002504400790710520303441d501c406c10f0340514822440342d8000e00c03400b40100e442035403480b407604003e900441c6440310301e004d0141c42d4224410040386110280603010900c01c0d0341d54140c2064105100081d2120b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 788632958 1250 788631708 788631737
    0x3030103231911060403051903023c120d0216081612030e03070303020717280905130515120109060501051c0b0a11040e0402090f1b0c010b030a03 64
    0x80309801d2041c159926441c5c54256143c2650b10030012144440c0180c2d4800101d081501c00c0c00b18950030401d5030200d412102c4001004594400680314243d0700f810101b40705001c04000084203440c00c20414405880d02a402c100c1801942c03083c1d041030224039179050b4400c001003010700200800714441c2003980c102c0105c0d00e041d00d40740c1c144143c03c1e0201802c0c1088282082808411141a181d1600300140c0e140d0081c13512400c03501c00d02d10a000c03c00008551000102a0240030078091070914103a40d102c803412850a8600c83ca0034060590080240c0c0070203c001f1000d60b100940150b504445200055408400a2052200411047c07400d9440702d140c41d040200c5406640c1c003500c4216820a00002102042200781e2920203019002400b034202003442c0039001e0b4003642950284664560b9519103501c007002841e032041d0f40490056800c04002045040d100d10080d0190041200602842e042e0b00c0640091750421500c40085540e01c12a2038240c0e81c1c1007145441052080d110700101c1c8030341381d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 788634208 1250 788632958 788632973
    0x90d08030121050319091a030906010602060f04060b0111060705091201020301030b0f0711240a0218040c200a030801050105031519030812090706020a05030301032319 73
    0x420a241d00b2030308072401c0000086011042c1e8910b400b00c1c07400340c17041080c101030444070b103850b0b503121580c7c255840c401004001c42d45001144640d00d080e040354040e07603a50070b049a48003411101030300071240711400f08001421507041880205014500745040e0003002d8001c6040c11000d030b9110010440005080c7d01500302424010001000d500003141190300d5030729088001c20006103a803a40d001e50301c0010750fa150042ca0041d03207801845040ba00c541d081c0f85c0200000c14460f0310507c84050840001480c0814180215144404848005401c0642440600001d0080d600340300050049460031080003001580101e24040402d07002089a1402400c01810081040c3c01050400800b042017158038864004a19914542a500c02402c0c07100c20240c10401d80890704018120000094440100000711710b21038007540b80f401c1510103c5a84001c203981d9503200034002801ca80080c0010800300b001c40c4102c01345014209003448040c14014130341801c0c04032601005541040180384003080c480724 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 788635458 1250 788634208 788634239
    0x914150319110414150415050a020115080d0c15091a070c3c2a1a030604020c0a0c0f0608061e040b030610140d170f090d080301 56
    0x40c0800e14041c1041320132440ba51100c1c1c1c03d64021209040d03103000c1d4105640858008000311410034012051080b0010600d50140c103612006608203600707024189280b2110f901210708000c000c000395107481000b65400004145c1c10380d04101924440c81461449000703a01c0c4441c4689a85441800030742d082440c0440090811401c1000b185102e034005101060840c0071109002d0583c1014154945614500d000c4806284c000b030724841c00c541d081014032500d803d100c40c00e06959100141f001105006000c40b144900d4015440307008a0307440103c4030400860300250068405454549074100c1d103032412241ea8401c030703034500c2d01d01400c01c06c0c010b0325004040602450b00d024040d41c20150001404002c00740c04802c08800940640c4040c0e40d510b41c88680c108030054144c8006150104440c0c0d805c82c1c0c10321819003450071050031600c40d4544841d40d0842190700508211a4400380c015540c107940141c130703070010356080070044401c0d04d66414002504240c070859603940d90f0360503d03200c0f4600c00302 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 788636708 1250 788635458 788635481
    0xc1e0c170a050301051c0f030809010506040902060d02090a21030908060705120c070b01090618050c0703140d050a290a0306050c040902070b0f070f0914150319 70
    0x20140a00c504241d80001180c0c1142c17001c903129030707200321100514001042c0882005103c542c1500b900307410550011038141c4540c0204000300159030350401440305843c48a075000b54040007c011800351a81280c2c040e050002010340003541c226154118005c0d403200134a041e641d01c40d0000d88140405600601080280024801902090038455030181450103200500d03a80000b141d070000711644001003da4111079000300b001c51b1a541d4502c44180106194083c580001c145805441d66800f01070043d14080c100801c07600740b4100b1039490484183d40070113030003401d40f5006c104848620030701d030003414055810820002a0301f403105103003041042c040d5034204405c1c5c4401151000700c0da00c0303900003411241c10440200ea95645c0020701134180c4100c1d004112101e1001c1409006c1c085600d8480380300306c0c804a010400340d240c0d548140c1c0d41e003607202010780014072510810b01c480d4400194403562a0b0300030744000d80408007403a0300406da410858814140004402c4045840080d50254282c80794 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 788637958 1250 788636708 788636753
    0x150504060b07060506190e04080c06040c17190b1e0c0910090501120c0504080118020a300609020a0806070906080115080c070c0b0d0b15030a0c1e0c 65
    0x10041001b003044410034895198007214030b0000900f4003040c10215600724280006803441460075141481000415000f010800d44d014890213408440008003801c0d0000c0810b140b4000b0043d5907215508074500800b609110841d100801e03a135000c1030610b06009850000415032580c103104140000fa0301e074545031004000c260b09003005540d03000045000030403080c40022a112105901c142d500f4400e0f940a82125860240c1611000c0c6541317642c0b01d0928800c484648041ea501e00d05084901494801c103106040c3d0f0852407150315145807141404540310700004a50365005400041c00503140340c1c000000341e0014000c00070348c1740e070121081c40a85682d0400c1c0c1a1035041003010300c402c954940e224000c1c0010300c008542d00c003207003005a500e85640301018203a210388507a00001c17240c0040c00e40703501c020b080245100d55450031342242d0380703690742e0b58a1260440e42d54500503809480004850014001c2492620002c40c829004101448040d41c031039580041a03441d068200104030140c0e0220366 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 788639208 1250 788637958 788637979
    0x90c020316030503070e15040e060a051503040f0c0311040c08070503011a090a1d070504050d06050a090c060e030d0309171b010c03090212010b0901030303150504060b07060506 77
    0x204001d4440018003030701850601c0e1a50340d260026248040700c040e200d54010210300003046010000f400810680c0d411000ea0016615100c0601811000c2802901d40c400380754041e032246481e910340550740c000d0041075081c140e014562103802c105600c0750800e40742d501030043d00201b1400e19000d80441d184c00ca107003448080c07509541c0107100c0d00040c041d00e0328292030344040c1c91405115400341d800a840003041051981d6407038014501c010320796502480708403040c3c00000d00490240c8161380880301c0c058400040554107a1743c1c2d00041c00700509141d1520741c5e401600c00851408864000640850b482c0c00c5010030320341c01054680404043e0207000c240c113000300300c00064172a00501c0b10708500d24000b07d4441001c0441c401009015071520000e030340c07808030043e9001d603041e0042480c4ca8000e585980c80c3d5800c4c0c00f002400d1740c5400139002d400c29800c50040000a109a0007840c1200fa8144491502c607144c9000805580760f580c08007880580218a41c0e081c030225100f180e801c800100c4006421 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 788640458 1250 788639208 788639227
    0x1815190c0507020d061a061b06070c08120a0f020a03090b0c13031509020d03020c0f09010b0a0f0207050a12140d0206010e090304090c12060b04050a050402090402041d01090c0203 78
    0x4a200b090401172500d03840721401550703104142c1a19004400040459803166184c20301c0700c0d440712120b04641c41c10301c01c110100e580203003d1900210b079240c2115030b092602c21481d12803001c00fa0080c000c03009190713031442031104a8170305202900480f60307142d4000c070342c0440c24248420540c4014111300c00c00c0c1d00c10041035020007410201c00040b65800f00c0b5240441e00c42200200003881c612401a410204001c0100304240d0b007c103940b49415001c072680e20200e0030010074407003011002d005190007483c08100f0602c0d07890292581071401011881101c0d501c0741c0700d0000c2851011607600a03510300d00b0507203030340c01007003400ca111461041c00e20000f0100c0281c940d20081d510541849a1100c403100b80011885148060048401420401c0804c1c40004038042c4020000340c50891401c40c0f4601c0c0440100d10380c0e102c14125811150024035400b6003d00741130400009511070f156140d8410b60030040040c003020340c12011142d14604040011440d85410407035400e40303404100420443d0000c10101c0e00303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 788641708 1250 788640458 788640469
    0x1050a050d0204110f070c350f070b0c011a010f12090501020f0711120606130e0601090606110a230309030106140f01030b091815190c050702 62
    0x11100112822618400c00b40040340080c42501e0718003601d00380000e1900108111a001407040d84d00c6041e90964040d40da58150410b01c01600b415a6944081b20070440d5641c00100c243c110707046910142d8101200c0105400e141c2981984a802c02c9070002c110f410010310288100c0c403017400102c1c0c1030640c4142d060b000a000080c0c62641c2c009000e40c0010384078132076000e94868a64258484021580d0348011606110580c120321011601c0c1e034060156840705040c03900c4140a241d40340d500030034182c0c461604100d1100c4600c156040400e51b070704034801e5480000c0096500908800c02c00103200c030705140005080800751400580c2d0360780310000040c0040c0389079402c540803d84502e00790040315081d01c900e50540c82031540f882d900d036003850000f04040d031240c003650980c0e40d030883d8035000400001c001034050b0b030101034103554020140030008640e48041716444900072030200c256440040e030103031003105207041592144008903080803074664030141e62140300341c4000f03141841410580f65030700055 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 788642958 1250 788641708 788641729
    0xa0305030709080a111e03150702010906060f0617101202060705030a0801051c0b0f0601020a140a0b18030703030b041e020c062815030b0c0a020709050105 68
    0x10100600000020395042c8a40021005000c8480035034508180c2410b05140c2d40e1541d10700350b4070913152882283c201c4500851404690500907014003d0030001d82504608250b00405c010295502e0f03003107800003d001d910070040500349445071594214180b00b001042501d04400c00201c84270090244090220b00c009107801700d50086581c04400701d9944080b070924055103000400500c80410100d1a258200403050f058400136a15910803036400955603134888804000901080d4045000c070300c5040c001e07106140e1207038060040721001c034000d54070384081c5410f045c3e050850782c1286104908000d901130000b90480034807014481c182e80040c8000791644500d40004003070540d1900081c0c0346860b29004010165100e400c00140c041401c81d29001030751100e81d40c90361034010400003800140c001d0750741038591031000c0c1c034180540b100001228001e212800b2000d0700b4124014002000691b034011681c41041b148202c0c43e1501d2080c40b0283c035162480c0c1001d8090b038104030060005031030350001030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 788644208 1250 788642958 788642963
    0xa0504080706090f06020403060b190b0403080708071a0a0506040c09060e01030920012a0201050c03040806070c0302010e21071b0f0609060e1327060e1504050a 70
    0x1550f00c01403801314503010786040002c002d24000304000052007203e40c030123910310400303440000c00743c07107800220003801c45503006186c9000e805110074000701e2586c101500209108004041c036020786600c030514900966009110f10841e404200032203004640911034008001b6101031140280743c4402034540c2c102030140b0801c102440540b01b010707a101e50031020b000758001d4000b81e010b001001c0c00e00c01c45490b8801d4503010902c400c242c601c0748915412800b40c894900384606400b8046075004440036400031082c100c5500c401e11000c1049070045c4040703802010b154030380000c440202c0c40d019003520408003519245400449540f03044000d8900c1e80250305004103039290392440c40d0301c0c048400e0010184012080c40429001040c05000d0f1000315007a5291501d8006041c0c0e0344040c2103400d030300803241850b000401d801c0300d03110084881c0c01400c60300d44d9204400e41004020452030302403003594034003607802d0b40d100c143d2201f40080a010b44140b40711290080d40c51071415440b419075941009400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 788645458 1250 788644208 788644211
    0x3120614060306041509051e1902030403020f01050109050f16020a060b03070f0f0f1e03120c0b1e01050109030803040b130506090109030f09150c33050a0504080706 72
    0x103a403940e2a175108241c10402e0010101103d921070039403400030070048418550a43c0c0c000c6110285408201036584601541c200484e84a0720041c1900e0117904003800c04c6013540b2814a40c041e10702c501f80105030280044541c000345515101040110881018100c0800420042e07407812199601207407500807560459404140401e2000c0420b240c014039501c190003083c0c01d800c020440702c0500746458119804074444d081d22548a42d03140001001d02c0031905110300c1c1021080002405054094a4448260404000c4400180c072988402e11044500100079400e030424407854a6800e500180502020302e09042022b04541e580b20381440054000340050a80d81c001620800701103101c207034030f10384c0401942c406d0305140c1507d60181421500860100710404106115148242c0c19081107d1800b103449468542580054411a0a40d40e0613910b10302c0700c240500e82a880e1000307a66126800440da4106c4013000d684440c212900070703158001031b80c1420140000b203000c1006607200703560090300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 788646708 1250 788645458 788645461
    0x702090c0408010c080a0c0302090a27020a03020c0d020c030d200703050610150c021201110f070c050306070504050618030a0606092a0e19080a031206140603 69
    0xd0340d4654096588058029030900d01101038113540801d503c1d0040030407030800c1c00140c0d010302c010b071709a004141400ea00812446402c004040c0744100400041e0f91002940e2000814260268103070307401004c0341404660001540390001c4020804030f00542c1103840a86512205e180009840703011a01540302000031030303040c080e0300948001c01c0e1406612441c00b00e9243c01e9aa1800a464020403648600c600c0c0b011a0300090000c00c0440043c81214245e541c0c5100e1800fa60030030160b9540480c5012042d9a82c407440b812000c907107402403c41d042d4040b0074640b550118a02000d4001d49900a680250004001c2c440c01c01e4022060350203856003281c840d900c8500820820300c0702c01d03c0f0490103030315200346000c08051211640c40700c7d00780d0300320160500010f90000d898110800c040070119010079510080703403248501c01c01c507160006034010941850604106041c18600c40c41d81c0115400b50003c007040c108241c0c00c01d89aa4444030546414041f040c5820718003840340c0507c0d40101e004490000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 788647958 1250 788646708 788646721
    0x809120106091a090f090a03050c03090315270307030318080310030c0605070203060f070314090f0706110a110a120f0c05121b18010e0a05070c08070209 67
    0x412481c040e2034807030300030004520340a4141100c40380c03165045008030703003807004959101c2e00c02441d50301c980b910b40000d0807240e4540d6011100c5a12022401c0032a01040c80010b81c9650244103540c038440d0b8402004102d420000f0049d5000c0c41c11941048159200300c000d07400802001c0140c56100c3d401d8280041d1144c1804110120301c00341110092542100008201800b40320309021415a800364407e40703410343c0c0f90082079400744920540698103901220014004085450402d40d009143e8903002c9518500303075006c095034000544446402d030b04011303840e44901104000c2c40008044078648001d06107140d03500940c50302c10342c1d40d024100b680080d00d01121074480382010b00050540b080c800c0a0030b0700c81c0c18595407105081030103d47d02005408006410314181d000c808070826400701a00502076046805c2030100280800603805c0340c8040880500c41c412030396040d008082058040005151444003281190310090441042c400308010f00000b10b01000b094500c020381c1651403001644964 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 788649208 1250 788647958 788647961
    0x307210b0411120408030901020f27060906120a021608220f030611091c17030705250218011703030c0421080c032205031f0f0603031e0305010308091201 67
    0xd40146821544c00200503461282c01c1c3c03941b0203510b031401c202f2340e070614020f010444a032152a000076031054040c8200c08140302d4030010b241d04403120180051612085120740c0114601c00d09003070b200707400c005c154521401e41800381c2e0303050003200991106245050244c181803141241c0005800301c6e5403030781311601031444081183c860040c01801c801d0780b0219848807072204038040300221703007000d1892405140c01c10500181c07070242915440b018181521070036028281440304081140d40c00213a14204056101c180722800700b9650034a84500079070428032841d42c605030010503000160700c05c10400901880d0003080d0fa09807205483c840061840c000b01d43d018840200b60080c00da900001400d0340b0a660000081007002c1070074628040408011464400c00f001d0380c41855015080102003a008401038912005080c080501c001340c05039105100310304a0303000d83c208501044200c500e288103100710b548500a0b82b51545814080b560460740d50014030302618400d01c2c042c13030103000005202d9400b03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 788650458 1250 788649208 788649217
    0x8010f081e012301030201024303120809190f0f0212060106030e0f0307020d060b150f071713060f0c021f0f020a0302060c0307210b041112040803090102 67
    0x11164400403070b10543c82d121806100b84812405442002d00c40240400309811015007149401800340509188400403801c0000d804c8044215011014000c00022802c980444407a241c5682e4003d00d45007408080b8507143c48100041c51140c41da02110001a020550111055500c4841d00910b503025201007007403a074968070f14100a0243c0c1c030001c101c09a042e4008902c00c20303004101c40100d5640725100b6107038403882201940003c051039903800401d560b500b09000071080548010b20204208585074000e4106500b6406800350000c2c03141c05020700754042c500f044400507440c91811102584103018440d0034410441804100c2510a03803d50141c0348844907650050700d1040c002101036210002e0785031004901000c106000c0744607031580d1000600c4143c041e415002880151150b108180701074000810036010451100c41d030028500b00e00c2450080410a4580030510b240f10300c04000649100315040c0d0315206c42848526601e00e552100903401c036070801c0e0441d0781ca444aa600502901c00c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 788651708 1250 788650458 788650481
    0xb03131b05090405060702010b040603050c0402031807080a050d081e0411150702040c021207030348031a15360102010213170a06060603060608010f081e01 68
    0x51442c2040306010f8041210303031295403164000c104c0b2081030300802003160100c1c000504241d0000741c240f1114109036000707540140c0c009444088181c01c1d80c0c015440d2040c660410135080d0031003a0740f0342c10840200880211040c003404d150480740342c50500c5a02074015941000b4920420344085020711808030701d030b5146104050a0782420b034843c0455a40380b0b50050408901842c0742022100c0080c0c8082071004000000341d060614044143c0c4048010309481302d400d29590105489409200300983d01076400200c0e400400406054036030403810884800001d028207040c24032100c42400c0c1c101a407000001c050465152414035002410042203000300d039896011030100012504102801c2a14500b4041248071640c60400026004900b40d002e600c9145c01d9204842105000d601c403485080c0700040b2549080314000c0303c0e00d45803402a80c507550f110b04046940c81006000860740902c0b0203002d0889010303400a51840c00703060503540c140408119038194401440302c070f07900000703410000c0e4016 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 788652958 1250 788651708 788651719
    0x702032502120d05040e130201023003190507020c010207090f24030b0a090b06090c070b01090b03010b04111e0d0c080f0702010c090e0619080105100b03131b05 70
    0xda03c40c40140c055402801200c0c40704400c1c42c0001d20146414103241101903040e4003418000001d4000003982c502c1240c244212440190f0403c54000b00700000345114450f032148050986404260750340881d80090720307200071074104035816002660001402021264640000a917071510000214028004480401c134864030b14201c110381d4018804080301564000c1c3c21011060300c1d9080000101ca15010b0000c0c0000300321000981c0d1868100d1503a03920061458a092401d0847c0c1d8a01c90004e6090f081080843d54030f070060202820240b0070000541000d030340401c0240813415902020740138003000c510009004c00c0258610b201150158ae04c0d41041c2ca40a014012000070044d010040443c0c00356503030b400440003c0c0029105025403a04507106441e40c0010504103040c00503180001403407150800b03520240c52050140c003c0c001c0000742107000001685003020b2075080c0040705141e10140e040b41e411f10601114200b02c042c040c02082d0b00c195100d90065480c007004110044651146501a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 788654208 1250 788652958 788652973
    0xa021002160b0c1c0b0103022a010614010c080a0504120c0302041a0d11060f040f170a0b0f040201180b07020103060e15130b1c030206070203250212 65
    0x3101d10301482000d00d21a440504180d90707264003404072401a1000704020a0003070002c0703a9002800d6001001326401890b0140c6400c00071300d01031265014200c140408521508400200c42d10284a21f10203070980700e101c0c01c4241200400289030140040010b400c0080004440305201c0c00f40003190010807100041c40300e89074150411244220051000f64000c0f414031244100d80e0003440005c801c140700050601d40244042d445031582002c0a008154009400b0081d590b000c00010002c1c10080c007010804203022400c114840040110107401c2d0383d0961b00c03141c1404005480c0305401e80e884654203c411803655200d000403a03084903000d0b92401804000b103400302d001c00089004004040c000e0b01e06010459955115a45604048964501030412500c2800040c07910105400c50442d1102005c074850070341c5400502d0700501007203503403460031503074078407904040d0103001e00e6030311541500203981800c200c0c500c0d4001c2d803090411208050503038025008110b5840c2c40014100c2c00d465411280305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 788655458 1250 788654208 788654227
    0x90129030705222c060306040c120611030a09020f151b0705041b031b08060d03030608031911030301030302120c0f010c03021305120a2d06050a0617070b0a021002 71
    0x40d0f42604d43c19016403120400020581d00b0000303016800b0700c0d800101c0c0c0440b43d00c3e041d820b4485850285084030903980300c0203084117001141000c0e500036003403000e001070202d400b4410841841c0c01d00c0740135406448400c400b901545241c10556550407106001c441095260900b042d0602c0700c81d0304007603031203894140141304880601003440800300c099200ac0003544041ca14030232003048404200e00000da040400654281842d030680305000b403080c200407850540f6401000c2c195005044070310542c8200c0c902441c441503100d49400301d4055007a018505e15411524001d480c1c5030101820141c00303a0002e0103164440c810803156424040303d000801c228496854024040c2d8014503511100640d03149000c100c901c0e00f41400510300203000c2c021700113480599a80d6564210906103400300b00c1903000d0500001d03030307038400c28a034651080000081514100d0707000f4003100d0003904600e148a109a400700b40030700c000200503041d500285500b40d04e034980c1413001c074a04400e010100c1e010500100710300d0319 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 788656708 1250 788655458 788655509
    0x40311121902010813051c0207081c08070c0807061808030a1d070e0a05061f1701090912110712031806030509120a03090209012903070522 61
    0x140c90300c01d80c0c03031500c141c45900d03900c60245c0c1d603031a0180c03083d0031a00303447d00c0c0101c0c1003030340c610381c866140107541c4000ea48810103400c0420042002d9040c0d071040309441f1010f80e01c0710440c0d41c0300b00c4a040c003111002481c2c444405134000c1c0780d4020074040d6180b422017a1400420440c40a469001820965a181c4445d40708080d04510501610300d29045290940280c4045100f2054070341c02c034130400c116a0303483c8515001d40b1025001e1078210b00507181ca542c070b0794407020001c890008580c8400d8810540044000400b45c2c050744200ca18620309034034003000520400c5400f20608080c03602c40001420540181e04150315070340445503410340203441e01c0c10590803d025101c8006001d00178014903a982c0000c0d01511003c8401402da9089071140380e12501e8403c0141c800c004240c500068411801d0380880d600c440c0c281c0080d03000d80c482c0c212902110745c81c98440f00000400604c913a00390304000304040e25500903c002c0042c0c80c020280c02d200f5240003024850000c0c4040c8101c0d440115000701d0524 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 788657958 1250 788656708 788656753
    0xb07080c06010603180b060f0a08031306050a08010303050304060605190801050a0e07051002010e01060b03090c01020a0c1403030f070303090b090a0b0615090915030c030c0604031112 80
    0x540d07801010000100180644175140319034282d9100c03026048410b40d02c1c0c601b0454020883c41e0300130b121a01050303c507242c0210460240c105100116500c5803080151160512198403081c20031808002802d01749070b101200d641103c4d49414102d0326a1154585440640f1003a00020380200385821540a04540c44440900306c8201000030850f64864980100640e511146000001d0b03108520401050500000c05a00c504a9200000d61505098407903401d40302c0585c05590b1001011044c010f1810303081c0600c05444e2000d0000305103849042d5902840128648a6504401c1d003491406c4001d0f1130a00403500c0d0303051900d009070f5a803001e5140240c000c000360744041c2e0f601d500381000244c1e8410006178001034680c200d6039151095a410081214182c2c00382c0c81c0d880006030901007000315880c4d00841328060b400e9514940907106011007407500e0f0010340e5600130300c17a0b4402c042c814601d4031080104c500b502e403c1500c0e90500301260010400d559040b140444003446000d04080c1018034441260 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 788659208 1250 788657958 788657977
    0x10203090d03021c110c060a0c0f111804031e0306032f220c0e0d150e0102040509041103010e0604060605040b060702012705060c01020309060112120c020a0b0708 71
    0x1489801019005c98040f4000c8001d01225032000b200d00b54546404400b800ea0806646072510035082c2c0307552000d40e1205c44400850b940e1903003c001c580680b81100c101c0c04a446900c4c40c10b6185e01d4143c030300520082c1c074440c26004031269001d1325000b1a100c1c0e0032020146230001003001c5100c404040c0b80d80e8921040214490001510020360321034038150b90001d1410051640d10105c5107402150800186501800c4030244807070018016640c0d01e804005802e0345014101c41e11035000e0583d10032b8242c8078448401c1c1c1d100d920420081c8040c0c1d8810140b15081500a021480188a0500072900400c02c140203000148034000070801044100c2d007000b001e49000341e4043c8a13031003c2e0410712a040c0a9001c0003400310308900d28807011140007000c1488540c60052507841110383c3c07500402c002e98040d07074044105940000c200141d5070710800c440e03801060704100746a43e405c180d8030741800c02e02d40700b50a94204128103502030300350b598003802440684801990550740384a50f2070810559480789020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 788660458 1250 788659208 788659243
    0xc0304080f101103040b060402130b0c0d02010e0a0305030c070b091b01020706050708030406090b070203280c170d0203010f0503060a09150f090b0c041a0f07060209010203090d0302 79
    0xe590302e40711140518200d003080d40d41c1d441d086484950300c0d107103ca00000c02c502c1d0415403d200404549050f07400341c000030509145403540d2034100e60041400c040c103000031a419a0b05101401910b142c0000300c1030b0b10640c140c50500d8032600d0b80e1114003607500c285031018000c030010106001c0c02d103002041e0414070450121594111340300520043e620761b0b4080c07158601040052007032030003080e05d0a00445d8840c1c8104400a44880d465860200d20324080e2000e2005a001083d4072900d100845080c810b00c1141c034841690356400440014408082420018600c610303014007505a558800c00b6100f240381d00f030b4410364603903071107040e400716a01e03a074803c0512034030803000882c1030020113101d5001e00c25000192001c81c0700400561001900e04500c203954820740e261003290200d030715147e03514050b800c07407617800e0794540c501325141c1074490050b032850080c244100200541030741c8220888075003d90044001d61a44507840041c0d0441c02107000d5035070445042e03814901059404646840460410300d403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 788661708 1250 788660458 788660473
    0x6010807081c1b17180d020f060a091205030d050c0306011e141812030a0509090a0b130603030305100303230f0d0501050a0510020c090c0c0304080f 65
    0x141680c030244500c9440320428012504400c040c8a103010f10120196041c0c80c0e010f0600c0b03940d410302d13070f1080f0400000c02da041c00f0404d903000700d060f400305080110040314042008901500064004551400c00c1482504001142050320340a400e170341004000e130416000d4550001d0511741c2d01e0760f02c09814032414500d02000100d0611104050b00c0c0a40c0b0b06035030f440840d0b0416001461141c2d9803011013010f0052403111600c02910040007460400b07950001044d0000000c01480704444409041003100c0d0010300900b00c40a0703211060300d03104542103411440c1503d582e408035000780b1100782456044410410040b00c0c105268021000b00c9120359070801455a4a00d54031042020300d00001300024107043c0455007249a50703070f401802d1320341040c440b1710784130550201e001e096000643c035451705603d890040040e8a8644c1c420710041c80b01707076040703c44d5580d0b8100c02034031030b0201807915126454490104049060760016100b141d0200000c070380e40c8507140c0c00540e5440700845c1050195114000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 788662958 1250 788661708 788661719
    0xf01061d0403020a030807120e0709060e01120b060a15020c01020709060513051b0301030c031a010501141c0510091d0a08250b1e25180806010807 64
    0xc802612031501030b4081c105942c42a80c086810320b00250203102008004081e9440300c000c2d03071080001c0d007186000249481e926096028081e41c845500030382c0349405d60700041100050402103001400e82c0290010508e55400c0001a079400294100d0140780c0c1c864030300c07030505a800040d400d100d004243c00701e8003002d0340ca60301e0f00c00b0b45080b801401d4105e0303000c1031405c2c4002201c0d086281c12003a1a118840c4200506100e1561500242e000b6615001c26000804c2401074041418060308601460310019604000019081c03424508049030000000968010021030402c061250a201840c0501c01814403d14036020000b2a0142d002d1841c9480e0074896202142c031020802003503c007003e17241019080e111031000c0d4204101c43c0c010f01008a40e841013102d40c0c2e50301c1c102c0d003500c100c0c4640b99506003c004041014045d0002503c44c0b4284010720442603030a4055490704003000c0d480301d00f415071a00c822600c400c0701514400807110926030204403080081740c001c0c180c035000c804507111181d441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 788664208 1250 788662958 788663009
    0x4080304090b1903031e021905030307170f01063002030a06080105041709011b1a131a09011404080403030e030d0905040c0915080603070f0803030c070f050f0106 71
    0xd2000501141c4500c43c01d0754401880086d564020020380190350a00500f010301790106400d02c1c1084409400000412060316040200c0100c2403003c01004c80045c90718001c400600d00044c080e410911a07154120490b02c40c6c1181c02840c080381c0d00c101d00115401e000610f1002e5001a41c0c00c40711542018400700e85820144641071055410244c5103003080000101c0400780e9000b4a06141001008031000f2214204010b0302c400c0709125819500c05117108410244030741c400034040d25410303200051650081503d800c05003004551840e19540c00d0b40f101c5642e2030041c030050121074104c6d15114104018845408003a20403240a91201140310f091001015195549480394401080780a101405982007035481402003000d14180950301d281c03a002d640c44e00c4002c0410140c00a41c28a0403c5a9401e0510841c8010030311403400315010750900720310310b03124040145001c0b012100401e110061116500015a1090300501503c003030076041c54403140680840c1c01121812a0114405c0c100300c000c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 788665458 1250 788664208 788664259
    0x5010e01030b0f040b0a080d170a2d060519050315040c09050c040b0f13170d120b060408160605090603040f0f02060a0309020f0405041e060204080304090b 68
    0x800c4108401464410070000700008070445d1303045401068081101c3d18100304d03c0501607220f8450607070301281402d480b19104c1e402001031b01e44a0801c3c43e004003120704d900b2501007880c0c04d001d044210000c442200c0004102d103900c05540306a600b1140d1550f40d804404900a030307201641a1203c5400d0711020424282042c0c034000c00981e82c0082c10002882c0b00d41c842900079050100e56032902e640c0d581d54070407642280d451818140c1d4001a050003004120005a00a100004414240654035841d280d06c4200b4020001c0a00014a4800744081069800340c944480b00501942e10340341c84190351644c0d07105070340b60668a160034900c0824070038062400e4480604000345140d1540c0c2d1103540e00d410300440f420f1f04a51071075886001c0001a5111001b07030000046640e00001c441c411401001685000c0f250002e006910b000c0600002c07a03031392044040181c420706900c42e1203805038a0444001d10541d80a82010300021502040030f00140d00050900d00c0225000103404148402e00200100e6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 788666708 1250 788665458 788665481
    0xe0906010510021903050d0c030e0d0507020d02061201230d030f02150a020306011b1e021504090501180b010e01141605070801050708040b0609040c1e05010e0103 71
    0x115004201c20b2502d0b2050300d0b010140e52041d140a280c604049007225501da090403000319a001c81e1010b90a50130340b09000c0401054a81402510201c144844d210741020064004100d80060800c0541d16000061104c02c2d50161a01f981ca0820340d2040742110028050340090710213000b88211140400081c81129600003001c0b01c0c40329400740d4042d59169200c0c050b010941c0100d02d0b004a414202690441c82001c070040096540d18241000620a210250781000e80d981035240c6480401d9800b605c0341c41c42080c0c42c0b00341680842c507000241218900040705800c480380010081501d4916800c404d04845401455003c29147c120410007900c5029800c03900081c10000b106001d50702c80d00340b22100c0322080d4646450461050482d0200d441024816a19640008410007042c030742407140310760052045c1740c01003950500366103848402c00b0180c9001d200c0c0d0301c802c0218091254840031f04000303004640e1041d08a00c80e4080c1c1640c0e800360f0384540c0b4081094000b0b018000e50003030044091819 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 788667958 1250 788666708 788666713
    0x50c0a06020c130605030604030309110a0f0e060102010b0613030219030b040b0a0609020c061b160308150d050a030e0103022a0a06090302100b1503060103050601020f0105010611070e09 81
    0x900407414030201c00b4855200c803800f41c0c2c45060000d0651414071185005900a03a4046280b000c9401d10228004d0890702c06402000c42807070401030f80e00e41c103441505644820414407071135251000101d01500003d10495404900050510030034a06041242d08507407080d943e92700507004002d01402c0c8825540300c00f1b80b000441030000380009801505440e4016030703040d0000b50481c0c81d0040c000480c1c10011403090194480018003610145114902c3d0001848000b103501d80744c000078240700081e0188000406000420000c42c4810011500d40384541c000a010086d00044508220355505241c1c10140c010803010601c40020703510034000c903545604061040309040310b0381c0c40c241e03a05050180d10607030700b406a5000440090725600500c0150340c002d0b030007050100c0410030070358204d032441d40b1400c1c03142410000b40e038003106014007607a9014500f402c0000b0251788120040c1c1c1000c8161b070411000d0352070030b0001328000c0d42180c404c96244881500b00d51071305443e001c03280ba80000984070460701d039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 788669064 1106 788667958 788667973
    0x60507180f170a02060417030f190e010c1e02060c011a01080114100804080c0d05041a040e13030c14010519050f06010513050913050c0a0602 62
    0x20003081c1c003030302d07103e1480c2d070008071580b0a6100704d60403034a103404548804482403007919001c141e010b507415920411211040910b109654000c000b0400d01e058200b440d500c2035041592099000100046500384001e0610918800310030490307005208002c18040300c9020b00410940002c1c80b00c40080b010b860100140c51443d0503002680021a0606100155030b00c814443c0c1c28a60182030045042d120303420300d4402c6103d01d003a1a105c030300c2880800186194800010011589032901700100040d42c006192014460391142d021901c4a85c0041140d81036841c2207000020303c00e0820309407080300ca07a80c8111001004105024595682c400c11810300c2c0d40c0002a17802c4104041c003040a864084588601c881d0041c1031141000070218294000110f00340708071002d810001d0128246107480d1803001042c40da140c0c4112901d000d00d1483c0800d43c1452a481001c0c0e07103041c2c002c1c1504 = true := by decide +kernel

theorem cover : BRFrame.Cov 788489208 788669064 := by
  have h0 := BRFrame.cov_init 788489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 788489208 ≤ n) (h2 : n < 788669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
