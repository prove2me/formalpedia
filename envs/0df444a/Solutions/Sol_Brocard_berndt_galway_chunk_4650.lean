-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4650
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:18:02.34897+00:00
-- url     : https://prove2.me/submissions/fd9de3b2-84e0-426b-a66b-775c4f5c8c8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 836151079 ≤ n < 836330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 836152329 1250 836151079 836151083
    0x1d1314041b080606040b04020712030e0715050f0a03200a08100605191b1112120d0911180603010606030c1d0411030c071e020d0f0311191a04 62
    0xc0000740c0340c89050000401103100b42c07d07005a000c02206011644d03410b44640035407403035600007a952007120781d02814000103800891540074848140390107664004156a184011004000e5642d8101d880680c02001c4000c1e0f0802444071300382c00e40d0384c00b0481001410a50303046440310030095481074201c003c0d9101a0240f000030490600820b181c030304030b2a8001088200e2030034034076a1000d880c4445003116021ba0803ca51607094124624094101104e500a210030100020140031002c400c1c492954086c92005902a5564000c9030003441030109040c400314a015140404d001d08030984020921401c840f43c0e400b941c02c00c4800280b452288c811100806a555605a40802148401000e0102c0d200c000359005840f08843c00900c50721800071030107482880c50247c2d4075125454080002c170400807001c03428542d00003100300940c0b59410145440b661007284204a055249001d9411020205440880f4400e040e002602d042c10708103900300040c01890041340114040e20342855200080f180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 836153579 1250 836152329 836152333
    0x8061305010e041109040c06030f0b031e070902090d0b15060d0b040b010c080307050a020307021309021003181103150117100504080a20030703030605040509030a1d1314041b08 77
    0x10421600307100764409a40041707552b402082c0c481203440024a44181c00d9070480074006140030700002c0040810080009002e4500254105002c0c60006890080e60b80f8002c0c0c002c08210703001500d058003039482200c207a0b4000388040d84603100303510305500034044111b8082c01203141600c4441550b00034010038071602d0f407102410b413075a566044126007a4200c6008a030640c481844088010f0b078a403c1d42d071081c0000b110b0000f0300103031103004001000480c1407088051529100180344994005109803204030341110307820702c24122600c0170900c0d02c000ca40358070140c1d420703d1001045450308000c0c0e0b52103d0803864100c40c01e22a0301d820b103804031502598000c0210101700f00c11180c0601400040d42c0d00e120003485c000d0504118009641075601c1000308400181d034501d0180300e1868548240e0f0b8002907281c0085041c0280514060701c51011b04013a103801042c1840480d0b565610303140c14540e10010b40c5424045d0500c800d44000922005407021505606c0409001e01d8000c03145020b038085806042c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 836154829 1250 836153579 836153603
    0x190c11120c010f1b061506140703050f0403080309070e07170609150a0e10090b060711040f020a031d0606100810210302070902030c0a08061305010e04110904 69
    0x8010b50350b0924800c03040052001aa50f00e000300b130541140c86100d24022000491801074140004103039980b99000407050000c0c202c1502e440f11100390136241155070500b402d41c2da0f110350803c0d64600d400f0300d9000424182000041210000002c111041101d1600f100d00510740c0300e0010075104170014600e0f0b42c01c47d13030303110300040c41515101c020f41d0740103001c0501480e0301e01619804600b03070b051182c0040040d05015400d10011b1800c491403180100603002c02001001341c1100000c2c044d116103003000c0c0c60341600302d5030010241d175103030701151021403406011942c801c1c01c0507014000e030150390120b4651a00d490071141c44103202190705849600000c4c030181c0c2008900c2400d8540e840050110003100b00c09810101e208410071451041d280014491844400500c1c81c0081c41d0200d1900300142e0303280144140409800c5110694055030801d09005000350764000200382d545540020310107000341804000201d04800c0b460a90103580980014030720300800c0010711003041c4095500401c013a90640e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 836156079 1250 836154829 836154853
    0xf0d05070c1209050d0b0a0f09050a0c05180c28020c010801090b0a0b0c1f0e1e070b071505010b030f0906040b1b1e0a18050a1505190c1112 61
    0x404059401192001f00180d04d42401e1005421601d065070102c42e01da2040d01c0c460107000d00c00f1180c80041c50210b82c464180c0400c11004403d001c1c010307004c85040d00d030100ba03140e0030040d001549018100b00c41540450312010440c020b60710034040034141e0116815500205903100309008100d0b0025000c0c00040d88103250400390700107075110300e54444043c05010300c1c42c00004105900440041d00c01c80000c22174a0300c0d48021403c2c600b809040040060741d48032002da0300d0074046814801c0301d80c210601034075042d160401403a0a610306000358200b5141100208065008101441c00707031211038490002c0307035105954281c0d50a81550702405042c540070000740c020340404150303000068031140c03503401c140c400d00490004951132a40070340200000306401c409550310a0068480140040c1c0c0464400d28080c0865040350040c0208641c426040104507030084c090b808032041480c90b88028101c0e008a24401083da0070701440c00c07110401a6140180917180c401303604d1030b00701850805080030001407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 836157329 1250 836156079 836156093
    0x50309060309070306050114101e0f02120d0e01063303090f24061d070c050d09091b02190219030302010e0f0f030f0f0d05070c1209050d 60
    0xa1503075102d4401c074000840040e4440c0180c0b802041e00d0341031400c3e1f41201c207040206a4050304001070400080005086440c0c40051a2004007405810248d00c0140b025200700d090810040100812030800614007025240b10780c4558009070044000300322041e12081d1980f14100d0160300c0740d0f045404081d610165201c100b0090040b0f5189041c0002d40500c9583c070301031b40b19030000e001d54bd010041c0c603d0320208880c2c010541e18030620f07030f103040020600f440100304445102c0e010307551070040a07500080780c050007406060082c1d60030000701d480e003a03010782c00148103440f240070315031206090440c80da1014004103000f40c503451590b00607040d0400b2041c03040c81e04c103003904c900f41d80c40900c54094600c228102c40f4140041d6010350b0022584092140c1143c0c9444025444107079254000240100621000300680b0305000642c050980c0d500d031109502c014a000343c0507500001361410342805400ca4001724078158032072203a04800d03e007030110f03c416030704940a0700c42e0f940c1100d0a503007010005004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 836158579 1250 836157329 836157331
    0x906040e06010c1709032b03180f0f1106042102041104060509011e0207120507090c0c021306050102060610050c0613170307050909130f121403040503090603 69
    0x81031403c043c58003001d885008a000101410400303294001841c460641414807075810b1044020741c52540e9448211415006c8045101040c0209a5106441000c070f810410811800355080741c50600e0045940c1400c204091020780300701c8129502a120920381d00b883c0042e03c04440c1482055a08000b41261103c80619004422070744145d441040d60a2131240e1005000904459500c2540300c414060014001e052001245400303640242540701e81e0550006d00141625405032400e0740c0c01d505440c00519011154008001c03040c2807a480c82c100e103520900f0840114022545444860048900c500440c0c0c10790203184d006070081000034800341000b071000c003020202803506074a040c03081d401d0305052501c00d80b105100401210010030601c020881c100459200e020b62071440c5080401f00a0030520641e87c80c41e00400f4544002001540038144200c0c11343c1d08002c0c07541e89104507142009101710b403000940089403407040d04034a0281e01c00182c1c0d119980c06002149480c21081c108070540e08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 836159829 1250 836158579 836158591
    0x3050903120408040f05031629070305030f060d020306060f1504090617120313080d020705010e060117100e0f0d050a080a090f0b060f12070e0702030906040e 69
    0x48200041c0000c06240070005200c1c40c01070300b0460300c0d21304090070701d42d4400d1258070681c4203901c55078140824880c0503401d10111600a4001440034520349111620b80f01c405100b00a4083c010903841c1c00d158001004511401c402c174007002c42c6a0718241001042070813400007a405038014000200395080510b4044a01032004101411a111421607031075140c0c000d8000500e060340346e41d800c21807040c08104020715220504e018003109002c3d541c42c007250707000080c03c0c2011112000034400c01d0055450854546002e075050a641d61510303410814081c1c441040e0011052213403000000b840c00504d00c80e44844000c0801402e0398804002d8a9009803c810a4124090040c039400d00084c5604100340706404449469882d1243e020510140c02c00800602c9611494101400100041e0a1642c48031b14540c1c0046826402d403601d00c04241840c01c1500a50b40000c10110100001c444c005804000c0b640ea41c00042e1403541e03005002c9840e400780c0001150000300a200910641c540101c500f58401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 836161079 1250 836159829 836159833
    0x51005040303020d0c0c0c050904050303150103020d09061a0901050d080c0f01150602120901200f10140618060d1103030a0c11030706050d090309180c08070e030d030509 74
    0x190a80c0002c030849885c0b068440c040340c0d8a4070404204008503010030001c000c1116a05114a40754481c0d644911004140e00301724000102c068060361b0082d0706881e0304510304d80c010002c58a9900d8110700615110f01509034802c41641d854000d0301d04221094141d071409030542c180f1081d5a03480e102c42da00103010100083c05242240c0c1c031509000d01c43d00d140340c0a0220b0440a4a144c190080e05100803070510b50786c203032400c10156140c1d17604031094013070f50403c0722020040c1c0790200310007500b0001c100d180000ca034041c01103030140204003908074540d0101140b0980034540ca136001003282003034682c1c0c001030b0f01c0381c00000018046d14198408605007030185064040e895001030002e1f0459001c0c08020b408260b184149100740980d250b005182208254002c00c1d090342044c034050840d000d031343c540e50a119181c04020781018495040c185c000c002298803105042e0942c2d2062010700f10140d16100050a0000000d50f49407140f140c02c036040b800640900002d16408004802a24005107203c9041c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 836162329 1250 836161079 836161087
    0xe0c031209040f050412121803050a02011e0501080d23031803040612060909032c0901030c0509071821020607051518100c03060f0f0501021905100504030302 69
    0x1101d83d60007240c0c07240384114136622960f2980d440c064258010b021403c0c0b00d05250001a84640346500f1148845680500f8002d4481c4145602203000d8030a030f01e0800303204282c2c1070f0b046500019582005050340c41c10819a25070328944032048401844102843c0c5200300e600903c881c07180c210030002d5402102413240120382d05000c85401d0728541c069071040c40010250310386c0b08660f45841c071501c0c1c0540001a810300580305940c800522594a40001c00001a09101e0800c1c800d5070b1083c191000b10b8010b40355003010b40e960b09000703114200a108980c0521074a83c0022641031040303100f00481d07002070240010840c10704030000f04d1500717178922144030440c2c0c0701000c401580c0c52501401c00c4c1480f07103004140502400c400180444c4018118441e100e2920021041910010940501c5680d4030240001c000710000012400b40401e58080c4049800802010400001d0050520140c44003038003101d0300a022010807140000c8201805401900484800003040446400407a0020700078170340503042c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 836163579 1250 836162329 836162351
    0x10204030812060f04090203060402150d2a18060309050c04021804110412060218150c0c030303132a0b0a0201050c120615071b090e0c03120904 63
    0x8154002c91881c0704002c0d001042140c2ca00c1c10071041c00a441c41941c00340b20b42811640400e0f603034003020304000c1c0300b90034038140300c00068842070955032074620081042c0f002d00c55080c41e091000398140c04003883c407407452401481c254091140351a01c00c1158105501e070510f0900c0c2240241401d21088910380500320702e40d90544c1e9540081c1c64041c0c1406c3d5844107003400042004100d50a6188110a49800b0b0100700f10038241e1000301604107808c620050b0f920101d0300d01c102079052030010b5841e8030440081c28180c424210402a0000368094000c03100c542029104069907404102c4840c04400c0e6031581072800240049030210781d461440b0003500201c0b09110040041c1e100b07941107241c00007404290091699424002c0b0b03500040c5500c041c504c2c01c0c0e500c503020903000d0f900602090050411440145031000f10200f2500f01540101d602170864043d110014040c1e03165201d040c0205e8200504220058000304002c00b00c0a8010020302c0c903000200d400582c5904080051075000e940e40c0f40c0a44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 836164829 1250 836163579 836163593
    0xa0806091506161203020d0f05100506130806040515071e1d031c090e010b0415051b1e0313091802040914070e040c060c0807060e1f020f0f07030201020403 68
    0x8488510b03905c0c0540c40d19285041801110a80445031061505081c24888124082403e11042c5c0d00f00392803440d43d40c045000607039400c40745a403000c034051140c441004244000420041403030804c024404002c1e446812040700c00032a000c49000c1007200113131a098038980030b0348035003031200060b5440258400051000071f0800341400b1070445030751001d088640180381d1000d080f00240640560081840d41030103e042e046000c2c03800b0780d90300c0700d001040c580785039070103001910303c0040c1150140001609542126031035902e585e404145d9070114040982c015100801030700c0c502990440400e51080c54074080c2d0015003400d00f0200340402c21070785080096140c502802c0c400900414a540c0358042c0102880d00e00000741d07103d5000c408641041c000002c0c24103140f50110b82040c03070150190071b401d007400c040d00c0c400c0190081c101c1e441d00f013405095060205090440d6079140394880b41e0b0702481c42c00c81c8164800c60a5490781a6810042401d4500b007101c041c1c0318840c0644001070a084d200e40e5200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 836166079 1250 836164829 836164853
    0x5030601080601170f071206380412020f0402090d02010e010315120b010e06060703050a17010305010b0a17030a03180b0f0f01080d0509060d090c0b0a080609150616 72
    0x500c802c0b405410400039075005280307e11040c0072104200b01407407514401400941204000c608840315512248108817a10705910314424481d006560b034440d9151110726040342c4809089011f00034940c214403003440c00d4401d032040140302802002807008d0a6004452068107035200b0f506159a59150103001c445244540000e030005429410785140942444209d000d0b050780301d07506400e0780604201d600d40301c01056801450741070610a8617481040300030307142e040c55034012003442e9282c54000410f00c5415000406484402d40e204c0c3d10964448008a9014081001929440d40104559513140e88244d112501200a040c1c2000000c5000d594410717464034190307030b8500d2280b002c0d0300348100c6641403100700c6d004000100c020b00c148008040c01409a002ea030010911506c0c0108182c201c146664000000c0181c1c8641203440340303500e905800401e5000b44800c10b0014000c00c00140850070b05441d454095800d0081c0602400c034100304000042e4046010300c5140089403c0c00800140070007040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 836167329 1250 836166079 836166091
    0xf020a05070b060a120b151c021c080315030f0610060212162d120314011d07050705010612021c0b071413080102030f0c04060503060108060117 63
    0x6981d41c1090a110411040103040203201c0c159821040048214030a09000119400390310900c141e605e45031140c1c4015201200f0641000000004404912000e0201e08132540f0171a0380c1c190840d1251441380c0c8242981000500146081000c00c1030010545c581c2020b61000070101d410042c11810400d04051059959055141c03030303240244916034052058900b4900c221080605141d80c0d040302e6200b070401c02001605011070103c000e4400c107005001e500000d0403200c01110903480c40e2400303044207102c00e500d0f800040c2c500341000d5000e044208440e03040f07031806882c0f000c4184c491f1194412402001d005101840010842e0b900010b20a00440c001000c800940203140302c0b031401400003650030b40100750313054904100e02c60000b5009840d80ca07081410340ca00f4a14118109144500a225500c4881c6052003007103c00241c2150540065200d9000959078401544680d000d01c8168040da0164002248040c0b00141c0c0e00d51107140280d911201c1450801e9840004c507034004194007043d114 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 836168579 1250 836167329 836167337
    0x20a02120f0118021813020904061d07092405060310030209163020280f0801030f173907140301020408030a020f07060819020d0f020a 59
    0xc07440070351418010f204104024904421540d241c50044140011441d0306e0081c0f00d55880400b040034803e1590244020219600c001d46144419810495803202544242e200507400c01201003040d0380811030802c6100b0303d29900c60180790820081105c190402802000c0c03540e160400040903a4500340703424013818003002c00080c01506044010060307080c0340201d80c01c0d00aa000307081c02c100c558074007518010110400001d888485007001e2501c50f503a88100001c4d01c4000b0900c222a2101103201c56241150050818041088a403003910302401050206001c81c03000001000422600161145428803800e0641c020803042018458039400005c1d00098056200740c9a254075001c44d0240c1a40003110a100211503007242042540c41c4594050030314035614010440901d078800750142c1e00600020327025280c0b10003803044000e5460100c1c100c850f10078443c0c070300002485809810fa1501880851005100c801110410300d40a5880141d50350225599080b4103440c030003031440505038103000c503a2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 836169829 1250 836168579 836168621
    0x20412050105060301050f041e020405092505060714011b03020901020c040b060913020d020c0c190608060906060d0f2013030b040c090603031701090c020a02120f01 72
    0xc21508441c002810726009a02d08410711600c800341003a0f184d441030b0b00c0450100d000b0401080480a006001d074003c0d0003c4c03e00b0113111000354007040321000800c004815030030040c2c0141000d903910010748034554019030304102c0c00c004952501c22011810356000000314103000751200c0300c0c44440c81590342d6000642d01103620207056030b061009030080103040b03c042c00000d0341c20002031400c0c070034403e086108024075054030030f0300c0c82942c0640d41d070380c15550740848d00e03a16401055911044240d044503c142c0c030b034000305040711858400380420348610350fa800c4180d50741e09043c0320080d0000f03420140d00082c1446031070340c1501d1500450098818006010507540e080701107407400f00500d400500c402c010140903100ca170804d500501f900f1240c000c4500c00550302c4900b004444154640c00c070382e01d01410305c5004402d058100040020010490b600680d1a0384c0e038000d0801141d485d1000c80d401038010041007005450603d030409803e440390350645040d0540c8410042c21180380440560741459248 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 836171079 1250 836169829 836169833
    0x150a0603030e030109050705121905070509060111070317090306070201060e010b0702091504060f0b0702010e0402070203150406020409141f060f1b080c010207050c0f010c08030c0d020412 82
    0x1010b050100c8805400a100e441c426503526a1149040d004841c00390840607600780605504209110014280c4a64a01c54030721900f4099141c040d10300490740115100710105d103003540b14829120001c1c1d0003038090a1243e041d0303a07074480804c0458803160441d80d01881105c0322a6810700c00207010310080d400000701189482190985c3c070505a10014808005000040158440e164070540c0701d0030a4000107841c0c40c954000078011b142503000840b441038003031800b1a201d00305400800119000342c0314000640b110348100301c268410382c00c00a40542007c45980007601d45a81202d030086e1046030054201170716603a5507402c4400b050b031040c1d083c6414200748a4038041e5420404168901054281e0a00b800c0130030140200320103071b001c04108a0490352800c03460559908000c866540805800d64032800501c0e898041d4002c80c006071524095510210368a00d4078400a541080061f103070011444126203034040e0b10f8000409400c0300010401810040d806684010700180c102c2410703a6440d030b4468 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 836172329 1250 836171079 836171087
    0xb130b0a0e0d02120f1308071710050c0403020609040e0f070317190507170a0906080a0c021207020a050301060f42051c020d0b0d0f0b0405150a060303 66
    0x582c58480030f541010904c00d2030b220f203d004694500c0a40001e6640d80c0520358445141e02065910040f440d0154420100e201040c91140a41d2490306904031100d010341e04241c034044413015110800d44510403c410001801e0600250619000040c000a42d12200135051814440c103041c0318403160700521400d008010f03442c15201a9101001e10090074040008000465200a143c01c0010702001040f840c003000440f0070120013154081c3e01d1243c030348034080380c05819001a4092000440c0304c1c203002030320340c007011721409141c61891790003801c4201c1100340c0d01d607850380100001d0740c00c106110000701d91514240110300007031000ca5080b2145a10f00005803041c00480101c182c403980e070600600403482c900c000c0c02a0300c4000180d40003071030784840d9425240c1748100d581c20101c1c5007504082040008241e40030b03000d8021800414082c80c0314000801450040404008099034140000c00d004a07559031061030b8054070071411640b0800c0001c2902e4407001080700c0b034406403900c1e90024000c060340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 836173579 1250 836172329 836172343
    0x201030b130c091d07140c0d050310120b06041509050f06040b0d03080c030c04030605090706020d03020a170c0705100b031603080a031e0603060608010c0806010504030b130b0a0e 78
    0x59010030105080c400726005060705006440131040207000c81014140ea80b0320800c647d0390042d5002102d810b002140005000d50300215664480b140c0c3c10b010015820341140441ea111551004414201e56a10f50421000b842032030040b10750740d01d1440001c54450400e1042601544030340e51f01080e503140003810041640d4070205454010604c007880710002981040c0640c1c2c100344140d044d01c1d120751714558a801503000c0c03607001074100390a03c01400302e40103005c00c090050707540c1b039801e41d503a1a40d12501601a4880c120000000404200442803401d40710401a034000750107998407858450103840307107490403d2104007666610359402d80c02d82e20386010410f10b01201b19001e0174451079407035602ea0240798098105c8210501d40c840a070348102c2070f540c1c00ca680034500c0303190701040301e5178803402c05000500043c05007001640c81e240f22442501d0082042c00d1041d40165240c515040c1980e695404001d4081c1c800e222031150200008001150007190b548540742c1982d0000d02c03503840300d507890724181c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 836174829 1250 836173579 836173589
    0x20f04080606010309020d12030225020307060809120c0a05070b0a0e030106060906030203060a0509070e04061a04150302131212030501080c01030e070b03010b0a140c0d08040201030b130c09 83
    0x46041e44805c01a00c2d80c5c256041450303040011540c0803c0c95001c00d5010384116211107040340218925410051441d2003240f0200b40240c0c01c94804503145c84054030304003003da40340c00c004d40c441e11445840c5d000b90740c000c04000180300c0544241c070703c560340c031f03a171400300103402502c02da8101040e04120150300c040c03044900351044000388010b52500802401c1503070321f400b440c010540c00000080d11030704ca400c01c400003804003901084052a1441008048010b044040b51250341071081c001030314081c1c4544120300404411315075140c03514000100c080d490b0019010028150240041913201d0ba09800c50350040200e140c944441c10380e20f00e400c1110b80b200030509020b043c036050040c800079030300050034800c4000070308001405d20707050910035190000a0307002e0000310f0300000020841040144c00751040403002d46074203460005850180240d4000c105200e00b03140e000e250502c41c8548a4604d1581044c010b040c00100640b00f1008203590f40d24200c5006021a02c1e808030900319548a503205000306 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 836176079 1250 836174829 836174831
    0x21801150509010c02010f111606170417130f14120f07030213110712030c21020f090603042123031008030c010f0b0901080604060c02070504020f040806060103 70
    0xb00040780064401401d0b84400381c108640e020411194034094452400b003000300e50308449000348011000b4894055601a10b00041e000b9030308070014610480f0802d0084d5842006184070310303102c2c8040d4a098101c0e0304810b03084056502d002844924440410014201c0c0c0c42c0c081a01034180400c0c07003980c8401c11403200050340022902142d00602080310b60580794111408002400c01032208000b60201402c0401403440c006141070401040d54a2161106c1c0c05882c240441101c1c8c0006558502c060b0b6890f817500c045c0c9415820f14090b0300e60040603100c8540030041d04086004010074070343e4200700c40880b00c10005003001021440c10212105002da030b03928140c15890b503a800d0031440c80d0710114990b030b504080400070514159903121064050000380080301d8a4465409803140a41800942601c002e031030040803c40ba414680b2140b41600e015900420641d151a43d4040c0203141000f0118110300603841d011038156118001040404d402c002100e40300c5042155040c202540604124141 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 836177329 1250 836176079 836176087
    0x3060708040b07080403030b03010c0305010512070614030402010c06090312110c0d052503120e01020f090f0a0314010617010207020a030b1e1e090622020307030218011505 75
    0x1807054a42c0755000e0a00e2905400c0f0751900d00d0250082c00034410013591550030112002c2800c0d600d07510842c100d402c00c0702d100742d10b648005050368480200340078040c0000c40c0b510320a03060103100801142c000b0303c103140816401d029034603600d0440300940342c1180041c01e558003c06204029018241f41e03440f0401da00d5160040e410805665a042c6409140501a0100b010800c260b0001c205a4402c41c24010344d9843d1030481c41d00402000300f44c0c01c0003285920f1302e84c541040100510030765840e40407004000b40303000821000c126010002500080d8000c40400c0048001032400d03032444001e801100020801505040ca683c042d0402c42c00d5410f01603105001007c007690b203001da254200c0e0303009160b1910703507110360681d04060600c10301219a84c0f4050814071070001400d10380a141d00703001051000d01d984503009410307210039040d07869071a504044d40800301c000e103807004000307070b80d070720080031145010740c1c941c00700d1403006603030f4040c0c1ca80020703c000400c580400e043e02d000f440d81c1d45203401d82c50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 836178579 1250 836177329 836177333
    0x706050109240f060c03031103101a09060d0506220203070906020a1106070c08010507051b010b1509040204170c01020106060c0305070b1902161b0f0e041a01060207050306070804 78
    0x83c92196210344d00802c1100ca01000a05000394007131390002d0502c0509070341d6031074581802c10003940d240c41030444c00c00c47d124004070082844415182c12240050489160407440c500100142c00081c004650160300f00d00d080083c002600a00c40b900152a100540c0324600950003510380ba034035a114509541000c4191000290440c44544206400303e59640c2c6507100c41c106140d81c0052500140c0c015841c0500740500203070040f0203041203400344002c4084000c5400307803407400d8030086041c042d0000b4110020802c81c0b28120f01a0400b040c000e000107051590781e428038202d04803c070100400c6034100b400c2055065030b083c017441e00034200c281480110300400e6078000b80640f00f4288040c2440107002c020070801c0308100c109001000000750700795140d1420010348040c1b8130410078110381f160311401da8103220040c0419102c04641f0f200080400c0d4514088070024041f030014012102030b51011444081b0401030001396004e452164018401d050030003040c5483d04401a21520074040c03003004102c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 836179829 1250 836178579 836178599
    0xb0d1d0a031814060703020f0d0507150e0616120c030f1a0d0807030306030206041707090507120207020a05040528110901031a2d0409050a0314070605010924 69
    0x603e070381500e106540d2102810203d06144840e00c001c1d0b124001d0804103040994450058882d041c041c80200c1001e0301c00110060444100c2d1700000010303040b6100107154000708820410070f4000b0781c10710109400c080c00d06c03041110301c1c0483c010086a518041c0100c40c011038401d01d8818228040c02403031440150000800c04a014880103048000000e406020188241c1010300103550160036641c42e02d03201c0000e5a0301c14514507071050300f8030454400007100106800f80c6070007070b4610f44890840782c96841c02c010281d8801c1c202640c20800405001409899911a0522420248182250958065040c2c0c94100103441e0880c8d000d50400c84100620700e0090100d074011102424000350003441609050071409100351051703400722040381100221b40300c100224038210300902080c126013843c202000b0441d030f98280701811a522400f40c0318006405807003480400c00ba100d001a080140503aa62029100c0980110032459161028221403100020b240056000c0d020f1103100402d0400c05400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 836181079 1250 836179829 836179859
    0x408010e011a12031e0a02061f12050f0610081b0f09130203010c0e041d1002220603020d0b220203130f0609111206010b0d1d0a0318 58
    0x43c440c0c5451a0100840d050400c2243d40300d41d486513060010040b900c2082c40c0d15000020001c0141c0100b50005a1681007030485002180d505010280040d04251500079001e034040303000c40b400d108282c281d8051b03003c10040d10b1311440602c1300c0303000710030308010106003800107582e80c45d84902c0045100100301e07581c801101c0d00c0d422054503a814941c0e2a00903e01c05148016070181d0035510f041e80040342254407125269a02406907000c0c41a065910185e1030780c1d03032998101c0701c940e800501e1441d407500e0340d40e001442c0b000c1c00f0490058051340f0110030401224643d0384404042540000e01651240d150b0158900c1901c04841900c4140740d82071410402e8440340c11040d006071f074000001001c060071448404841364008107141e07080c07500d0f840e0180044c00309a02c107035032401c44050402cac140c0c5040007a030340405409001400305a46009016062500600d02120b821500e5001d48044d0f1034504400b0b50041074050020040769505080151202c003440d90740007a1040075910520071010b00e86008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 836182329 1250 836181079 836181131
    0x30a1404061e0504120615060e0d06020c0106150810060309020f010e130e0a050118021309051c1e03020c0706080c0405060a020d1101021204021309170408010e01 71
    0x1c42c0c40a40142011a503511554000750041c0d4010308403c005c0c8089503001c6011031100c4241c042040d92211029100c074546d1880c000d42c440b0700320140304001405a009000c1d40c500340c400102c2c0598580c10340502809020740c5800019014104102c00c505000e44908000c0406007420012500190085091882460b1a2905015602c40f902c4026200c140e24001c440c0d0001d2810496050090030483e218210500180c60542c00c204580041448a0800105140d0700a000f1038003070110208546c0601039144081e070f01070040c2414090b000c1480c0c00d42090000e196078840ca0480d130105000110800c20ba036414040520500046146000008041d8213850302402c20076003d03620380e0131003050340c4581d070017180c3c005802240c120032450f0002410310b880c4e0405e4031040142c85250300342c2800c0340244135411400d0010900402c2c05410300c0c0071407200541e5901d001180195481c0c035181d40c400a80c40c80403c80d070200150400ca0f443d800c2c8104014850340d44001e0285e48010b00c40740d01030b20855041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 836183579 1250 836182329 836182367
    0x52112040303022a152a03180415030b07210509160e01090e030f0d020c1005090703150b0909160801090c05300c04060e190e01020702030f030a140406 66
    0x16a0042d8102e5141e00010340703481c0000c4c404c51b0905c4c95580c0c89410480d210b040e0a030310051400c15a00e010300030240d00c3c1c910041189019440c503220064213181c081c25180900211982c10344a54a00a809812850102078049210300706005c8151605074492034160088400ca14140700d410303050003800c0d044a107000804580c104070200101e0451040d1000f007482403000040818820040b03401800510079540103032030450203020b250344140e03501102c2030503035600122410710002c4c00d10458504020400e0f100003d10345a42e00100e04074000030b5a5102c0709a028148000034180c2244c0071002625460000b80100015940d43c00390313520043c080e05203e01008000a82e0524419001003a06000d9884510381021028070980e00c8140c007196050207541445404900040c00407805030160107080c02d01c4c1c2c02070fa240b0401c9030050003d0089a6003954080054002590303080102e415a8040c2c1d80c055591780440c5c0f01c0282c44000c00d60500c01c0415014441003222a802220b150016030b89070342 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 836184829 1250 836183579 836183587
    0x60d0b0a210c080d0e0910050613081e0c0415090212060f0f0108012610020d051608060108220524011224111801030204052112040303022a15 62
    0x207c44a4041b0745810aa4102c000480c0e415103500810b0f4180307040726401e000761000c1885600f80d0940d00c10560200384000e43c4400d0f540706960405a00c002c1c211013804001110483c0c85161a1069034803d07000d500440b00d411007401461701d04208003051900c0c007111005c030007030390311300007c1c1181d0740500c80c009105100d4200d81d411a0003400d53a45141000032003e840592041213808002034000c0841052414600000603240310180420012200c0180d2595084e60b0b40d02c000440d41c03180014081d0740745130351a0144600390025011802e00c1d003481807024008031089010070b404400221520580c0030b06110740100940155000e0407901603401174858580502d0300540780342e0403800e42c0d805003801494220f07203084280924018100e8810907009c5018601400d0300110168002e43c0141c1d50700017504c1540d81001b258031644002ca14070800141c403500000d0700b01d180d5260b00701c1c4d44140d0150300015402035140c83c1100420319004901c40c405109070301c0000210303044143d0318240d1300e81510005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 836186079 1250 836184829 836184841
    0x409050102040510090623030c090a03060e010c030f18140a081201060f0c0b07030c03140c04031703090606040902040f110a021b060d0b0a210c080d0e09 67
    0x1d01110040e0101511000d180080904020710210b00b500c01c2d180012061a412030014581c076103001100300865a445045031100480e203684c80d4080c800c0980e2010411100000280240c0166001d182c9d003c03000081c401110309018054811501707202110301d240c580748041700e103400e0015031103203034000f0742c4c0d0141d000c0e1070b150340c0e80740c40380103a0007510455010910288080030f84010394181e85403a62500c0d105d07030f40c1c000e00b80c03000720007500300a01010310240003510a03031080d400075045c44d046150120b8001e0080d04985526130b019110703400300038030000e070038801e010101086042c0039400541c1d8074914a028840282c0390703140070f05160300c5a034960300c1040a40d03a883c1c2103a240102218401c00403240100207a24055000006103005806040e100e03ea0790b110856262007071001c00390046241c1241000610010001d010000394810341ca0a0042981c8a0000e030460300b07c8619682f0103040701040c28101c101c41880d6000ea2510352100015600665001d0b0700c90000480607030341007a407900c0d21 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 836187329 1250 836186079 836186081
    0x15090310050112031202130e0601090b0301030b0106020c0d0507150306080f070306053709051509151512010b12010b100c031e180303050915040f0504090501 69
    0x111a910000900700800803940305141c0c4008a070320380c400d03200d00e642c00811201500c1640242600e405a00c11444800c01502c000c0740480340c0d00a8052400d1384005884020300a80d64000781c2042d940c2e00d030758030014010183c0400003840881c40407a18544c80b000ea80d86c6a50ba035421a0103007500c100c0e07802070040302090081e0007007000b401111003610300c186005010709076645014481524503505017404110240c0c100c464800500c0070030604c03502204641c120400d2001008404800150360720001800452414850103c40e51140c00b03613210181044c0059a20b0030380d03d2810b11003510170a90a06c041c2010903094020b0020b01610003070803180844803070b2801000310f007540ba50864031224540d0440300301075200c4603e41e00c08945800520b0f000c40c1044480f030601b1840107000c41c0852082d10160707400c0c440c00602401561600c1441d8044040c02c40b22070385110350080780850004922190107140240040f058003c0c0300070317413030b013044d141c00c2040707940e030392a40b18090140e0780c0d40702d1401c140721003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 836188579 1250 836187329 836187343
    0x403061413060c02160603051506030907030206031506031003140d050d0b041e06031a07020a02011218111e09060103330f06030203010303020a0803180708010f0b01050405150903 78
    0x5c0e0a09481245603210360290103450201c1c1c1c1d107041e220070006585404d140c06001e80b03000c2d9030341c007008220b40c80c01d580c00c0c00b150f40e0024000fa03561207621340f1030140c140d03201c60056210340d040a40562106103180f501c0d8440e4000e04a500341c280d000340c03144808035540a026541d0b100c1e4540c0003c10b48801180104008000717050501014042101c034511801203036400c150200c91240c0007901c9051032440728282030b0402540d0f010300582091b19030001561140140030340300340d0085000620440e95204100445840001c110741d0100ba0f0f0340710078110315001780300e13402c070300007000801002c00100d5000030400030780207100c9810706a58a600008007035018168035000c5490a13581c807109400b0341010640d41056106d101c084484a50000c21818030900941c0d04890741038009010402450340e50a016400003001c140300c00450388500c050081c001c0100c079008010503030001504030025503180d000d484038440b220b81032090800003040075480340c000d0621180c0612061f180c560106100107810900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 836189829 1250 836188579 836188603
    0x1504110307080102180d020f0904031107060804120507050c090a02040b03010f09060b0711240a0c0309060c0206070f030302120a020c0d03090f0b0601050409110403061413060c02 78
    0x85032581c04144020154020f210074000c0c41c2c011100c46000d5400c01262442c100b0000750460942c0100140724100301d1411a001482030400900c0c1d064a070075401c0c600340d440e5102200046001d4240710034084940c40d010b000128504d40ba0b443c00185488072076582c21070300c0d091806141d00d41c0018100c0d100c5035040c0c0d8040d000410f825613403541e659203d82080490390081d084028900307a00000c01c032200c030040f203800c40c0e4003494100418201030200207d440600190380d011201c1d081c081520700502c0f00080c82d04511315103901035080c5650400600d052019002401404110751400c40541e40349420398558550110002410f0a82c9260840190140540300305010120b0b20600c180c1c0c14494024000d0b00166008450800e0040c80040f426500b003240c018041c0c107070140c2118007044100700c00b2680300c481814800d113825031700e403c000308403480c51140f40d490000c00326060007004024014020500b0040400c013425060155845840004a1600402c030641d100d1003010064024010300100c00c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 836191079 1250 836189829 836189833
    0x5040e0412210617010236130903030e01110403020f1903030906180b0d020702030c221b0806100e09070f0201141b0a030612060e070905070215041103 66
    0x4950440400040c14407809846904c0a03021003451040c81c05100f43c400720b840c041010a8801c0c2e800481200b4810180d808141071030000c40c0c10201c42e251701605640900d001c8100250510850034004e088607160711808071180d040ca1085440401818280d40540b50121402c4620920010000c0e0607200c0c4805221a50041000c00005050f046080d10040381d003030f03440e80300350360600300030503a40d01066010320107051c98203100944458005901a0050a00c00742c115201400300b07200040505d00344c0c882c2d1a040030050784030800c15010600038048a075248422400c00c01920000242241900401c03503405601140c9a407050540300f43c4200c2c56010000e1300065850404042c000c051800c00507183d8099800c0c0340c5030002c0c00405105d11440303009082511071400e0701c031aa05034680d904c00140001050b84400e004103002850740c00506515104007000a2290764081082e4101165503028030102458030080284558000c9a00c40f650000040b40289558580c03400c0f1152050a016194041c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 836192329 1250 836191079 836191127
    0xc0a0e15010513081e0705090106050c03070b1009060603110406110703080a121a030d050f04081209030705032406130c270501120b0307050d030306031205040e0412 72
    0x1c4040400d10200b02045e17809a0702e00720403981039459940e01e0901c00d0607080b0800200400619101c0c20180c08003034903002c2502e1178008241c459440c05101595540410b001003030081001d00100c0c4111401000ca9040a000c841c0880201031001d00480c890401400814003050488003400d0180070302440c3d001020580300c140c1064000c0080b426a100480040d15190b40c2d004c41d01c2c00034038601c8400400600801d981044113004840c5500480407280880c070003880042120f030b0b000c0c002c1400684003002120748580c3c1c0a000c05280c01a180d200700d00a4110ba1504070300c2c40c034904041e0400700c140040590040c0c881c000400c50014150403516200707807030036000c5102190701100d5426988000140003408542400c6501e007520ed803031003102d010400701d01503841040311035007101c000d4105c010165401640e9500202d541c80560240443c0000d980c0c12045c0b04000e4a242c0103090000585849802d10b0305215080d1101c580140010346195110314a01d280340f0300c102d00c0c11005140e036000c20081 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 836193579 1250 836192329 836192339
    0x405120a02030d02060f01050402070206031902040f080a0c090b060406050c0709020a0e0307151b0c0e09030406080a020a050414030a0212010914010b0117070c02040c0806030c0a0e15010513 83
    0x17100c505880300c0c03082c4035800300005030741d2529009450403070303400500551464840042c4001d6030090b000e030311080c0315000e000009490142500000041030360201030301107d003441c503140d4040102c942000d8156840c02c403040c4d0f03070b0b41c807010103560aa4501d03052055540401a030642c1c6046496400540001e0001804484130303a4440410380d000c803415011140a1a100c0000b040320b1003550303044100040b03031103d40d0441301001d4082074a0250040c01a0124503031a0907500451000c1250b002c9a160310010b8200641548594166070044840c0700840c200280b01000038410300c07462148203c1a08038001c038800c0c641e0140300f03070411140c4c01025006d081c0c42c0081c500e8041c0211450540d5048035000003c040340c1418002e10698000c16135504140e40348904580c0c0540c400640114200a180c24000d00107803141d2003410151803194035007403c1c07480d15000701460956034403085170082c4500c4504100b8030100f020b2490700000103081901c50340010b030300100c0e81405024039805071048800702c0014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 836194829 1250 836193579 836193583
    0x11191707030f270f03061815110d1b02060901091e05150a0b01030b0114120c07060e0c09090a0308370207110105030f0601030216050f011b020a0302030405120a02030d02 74
    0x1017200c1c0304200610220115246417160580480700140800c80c040c1010303001003c2c0d960150b0030411290560904202480f09605d0032140b1f8500c1140c6403400c0c40040c000c40340d404018440d48203038801e000303020a030201c0c0d0381d411404490003045000c80060308429400c11105000c4812078913031500c1c80b0602da1508900f03070009000822003141c0800d15040c0d400c0c0d0994032a8400d140710741028050b91380f0b841c0c0550100310010300c00421602101105001d00030005d03440f405811a5807810000508212030118100320350400060328180e40d540c020824180020382241656900c40140d07420544418a00380c00c001ca92259003291408c0c1036a460f98611074030b1001d5014048103805401003c655406800c01518284400c0d103140a04601c03020010b00c0303d602c65001040c03088010020105141b003107949440c42c2c0144010100302c142d4648944207110390051860815542a501c002c0c1012005614042c1d20380c856802503900500806940d50341c0000d04011044050f1b0740601120921192040002c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 836196079 1250 836194829 836194859
    0xe010908150a0606022a010c0b040c080c061207030b120f0f010b06070c03080a05070c150f1e1d0901030c1a0a1e11191707030f27 57
    0x1061520f8800c0101c0e01520001e100c4400e0980011003252042594091107446010144d14a04116506143c0e030005900a040680a00c3c411400c4034075440c01c000a540c10043c4c00700741d903070059a0502450100110350702105800c04102d0900040340121030000c550f002c40b0341c001c8154140700306028540d08600024182075801c141c00000c12041c60b00070100011032145481c00340002142100510118441a00030309601200341800d0b032815000b0b6698032001c840503449400070818100032819800e42200e050340001d809454102d1100d000250702d80c43c2c280d01da11000d010040d8400000301881007429507901c0e240401030200c8555a56441d1000d8074402ca030158841ca0140b028500c00401000001c0d03c1d00d0a4064441d881c2080071505150b03403040e081421001000348402da611a803100520156100411142e4154000a8981400741d0000740031290000d000c0010880140800d03072001c4e94250b006203030316125100040c18048101e0035450741d0314925003c1c0c4985800264020460001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 836197329 1250 836196079 836196091
    0xc060b10260108030702100924080f04240609050a02030412090602062212081f2312060a09020907020610060f020f06130c0e04030f0e01090815 63
    0x32940c0c95800740035400d0100000e21440e80980d000740100001460b2844a0658240c5140303015514650b60f62426800c4032802402e05420514010703900015a902100c03513640107040d100c2082031030074035640c1d0420002347e00000303138a1084001e0062440d811030350440300050055139803c3c032550408141800003540b050310b080f528503005002d0002144c0c01641d00000301d409640141c1100c3d03640c04800000020b0480105110741542c00c2e00d40005407981e2528a54048503a80c4d400b0149007031903090b607164450f44403020300d0802c41070741001204085420814229050454680900700c0003002c103044c202c0040c4c8013000d80c0549800c20120078929848149c195000310342614031074a41e90b44c2a80c5800741a0f83c011566801e045080c803c45010310910119500f05104641b14554004002418244151a64480450030320b28a43c140521760751843e0140058113440c920600b01554040c0034000301402d00020310003a03081c21400c2d40e02506002c401171103514280c1e400c0c10840900190042d2088880f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 836198579 1250 836197329 836197367
    0x50f07060534050702041a1909060b07051e070e0405010911090732071a06040e030403030e0402162316031112032b020901080103030c060b10 62
    0x1180e440402000b182007071064903a152185003428640038007019180241c05080081014031962601c1d0700c400042d000084068845d140c0603074240054501603400b0742e0702c41c00302000140505004507101160100800d80118518546506908605800c01d1000e500810101e00100100414450103411108201e486000308100c90b18801c01001482e07003064031f02200142d0340750400808100706401400135810054111032464595400451083e80100d5044580c1c42e80f00c1000c0c4d5680d01c810a0039500040d04039014822a5200341c12251b0724007841c4000303001c200850b0f155240d0751320ba96040701d041642103a492003881d035080c2051482c000c00d0b000d02900c1d034042001c041c2c0307035580040341c50101d44510003180c403a480d265444541d120340c0ca91403400d500c583c1c1c40761341401c0b2040800050480d1441d604018001c45905000c0c001c07902003200d0300e040c03140d004101e00b0205aa02156180c1034950604101d002a606410040c0080031007400ca81d41140541951b0310040b604485a0b42c1d1407401005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 836199829 1250 836198579 836198641
    0x91609050108010b0306121c0e09060307081c030b030d1106250c03020c0d0b0f070807081b070614150a050307141f050910020c0a0303050f070605 64
    0x4484282d4240b19803914103d040c408034900b4030300003d410103580711300320444144461030040520441c264500d8a0081140c1d034161030041d0411f1003045602c000d00302d000c2d04101c0d1038101c9403503c480c11010400312114203140820441400fa5101400d0b400c40075084406404503403202a06a50f040700d1072401c18442d803000100b90091429140c41148000110402c0400c01c1481c03e03204114408812800e5000301081d0010644036041c0c3c140980b03005043c92481800e001c104081060806011001008402000c22508030f800c00b01c2e20f50490000d1108003540d1154200c2d000c400e0180d880c004194a04200200c8e0811045040d002c2c060003c08610310b00d460404410080c407d44070740724180d01034011030030400030750120100e0182516005040c4d40d50f01030f00807100c0707040c000e0501e80c0c0a0110750049001c13122801c08030010813a40806000a1036882ca580707002821895841c80020100080020000c8802030403100350740d0855440310045c800c0782801129800c50200303150b600011041041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 836201079 1250 836199829 836199839
    0x3010e060d050a02130f020d0212130f0f1a190c09061d010c08030a0917040302030613050313170c10080c0d18050a03030f060503121305091609 63
    0x902000161580b0100900c6840403030b40c284041181078940c05400d240e9502d18080c9400c00a000404195014610050369040c04007901220388201402c60480d51b40c2e102811000034010303a143c10395864009045440005051604030904c54540c0b09201c19911681c080c0600104050b401024400031404180080c642684049490b180c2360321032880020900c14440030310b10440c0c0c1c000c4c8104070f018075200101030704586885e0103551050791302c1544559035010481c14040000880c144981003140c0c060324140c65074000035a03807c00a003058807007543c0c4945000801c41b080048076614a410000100321aa440c11101c005d40f912100344041d50040c0204410716290180309641c02a4440d25130b0019a00d464503240c0d4580c110243c8040807950303980d460301c0072550000091301c0044c46000200101a20b915009040da54042100d0030f4003810247d0510041e034020850750940000c22007210f440e03e0700a80002042d40c40d960042da080107050052044081103900c001e040b0010035115039a0a03a079170 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 836202329 1250 836201079 836201089
    0x604140c030723030d1701050405010b0406050307021f1409150f45163b0601110c0a0302010f02010212180d03060e0c070f05100203010e06 61
    0x4035411592540241d101444006618400c050795108411101c4101c03081c0d400201e0310300390040b42c43c0b1000c07807103030800d03d2404059606c503140507003c10354007400b10b945414401080f234000c901650003817100100001c0c4038a4400c111170202480c80c02d82c1e40d0320982c0c484e03159030010a400302001c0d140c00211030019948000001d113165042c11281f45000b02076650007910a0680c41c040d12210000c85404200003450f0080e42d400d504115000d0803800d001000c142010b144402c2c101c85401542d0841c900035444c030400c00341e034030044800d00411340c42c000071050781303124061007003010401c00004560140740a01d82d90484042c45081d00380c0313a980000a40c6004280d950340b0300000c0c1580310300c0300310341400107520072410700f804c1c12468000036051a1035149011070504007142c0c03866006091312141c003e40d0a0410030050031004504080001c1424544d006c4a0144000d000354908180012120304001056030f1400e02d441d0032800b6180404405c910b204060b520a01c00c00709406000030200e0002d02d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 836203579 1250 836202329 836202343
    0xc1727100503040b06120a06230a14040b0601030b0402070b0a0e0715050901090305030a02010b030c0f03061305070b0304060c0e0f18040c090617010c0e13022505060414 74
    0x88401c555242e07030782c002080800072250076141041d009a03d003410010300d680c0071302040307040703a01901e49d41404541d00303041c0c0230a4014407039090030341480180f640903030017041e40a4206400100c0d01c1e0300c0ba510071005174060320000d21420307045071002500000317006071580b00501820100505201848040c9a40c40c0e07200440d00a1a8840020f01031440042d80540f0060560100606021381801c0d5651107450070b54000c184080b0141c1d4442d0101c0308180fa003800201860281220000f103905e81c3d20700400c4c0d0b5058001d01c01c051f130007a16904041441410091000142460700209603285060b281003000b03041c200c6181408150a020882418a04901e0550b02c940b005401203015000d4064010b8540308042c3c030540e40300000d402c001c130b40760003140208400340c095900302c8890790300d03090751a07421508200d96420411105003d00030065590b9104801c40c000c0719040503031942214004080b002d982c1902060108600d04c168034100b240129200384503902552135180443c20060f54140c43c0c2138 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 836204829 1250 836203579 836203583
    0x31b020619230a0b060706091109010807140303040b2d0304021005071524140a05220c0305010302240a030c0c020d08280c172710050304 60
    0xd602c500240001080020300c0e0f6100203030403400f05001d1261008100154065082911320a84803060b0b60188004161510a454800d980d4404558075041225464161500404240c10404400075001756030070410b40b4040c010015500327588246010011701c00e51002c40f00c0e03a000303038581015108406401e80c1660320880c0c003e0710030684032007010002c4849a000744000c4a074207a00c25404501015140305030040c0308202810050819005800240d100086521800400c205041c0c040e00d03a4403204c54080845001707407080c601000200401200601c410003448840030f2400300c42c0c200789031f81500305a04032030094603555041e51113011990501c5c2010007141c91214810001406081c1c0300c1d501c004001c038128a42000c1c0844507900059041242206c142d981100205141c00d20b0340300919a0b01004850001c060400591150003404003503070001e01420103001c010a54820b2407851307080f505d07000146800349146000503000a4281840a28124000d02d458800d20304041c1c001c10803240195 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 836206079 1250 836204829 836204861
    0x7081005060d0507050c0a030305061207031e0f05030307230a090611010906060902070309050117040605040c210b0c091c080f0a0c26070303050601031b020619 70
    0x50150b000041d2a000e07013150104a010025420b8141043c440038a0326442a0760100b08d80c1800c03420410b251270b8130062051142c1080030200300140301c040b140d5101c12080503a04165001505100070700c010f25070400b50190100008010300c01e03a00514450a040d14101d201003080a2003182074a0740c0912086500407c0c80004d050114600030140d158081c07556038001300302510f5955170281aa840d65000e0700b42d950f00400d0b6141016041444600640b00a10300000101c0c0300c0828440000005440030301100d41d12004035080c008010b9891340545190542e034641090b0b000c03180490503075020019154041000d0102d01e9060480b000c6500300403000700f00f150300b40007200c114402030505002c200c0e900c443c20007030001c1d803030040005005460a180c03614181c2140b2030a01e85052486403401016051207151000c40c0e000d04001500c04030750301032800140c955141e400682c0240580c03007084d202414605090b120b079130340c005140c510444443d001d14400507014040d1105483c820100c1184c80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 836207329 1250 836206079 836206087
    0x4150c3815010c05010b030106180e0a120e0a0317070308010b03012702040801140108010e0c150702240a09090608030a0f0c021804030e1e1504030204050a050708100506 74
    0xb50700c40d02c582c40b1101d008200008400c16000b0001e800c60359180e1042c0c180d02d01d00601031190b4401c0c0d00c40c18052000c00005009284001d90f02c0714401002c1000c403c1c18814a42e250916035100c8600310070103940c4c00180f5440045804520360709a0304060340440006020358000700e000c2880d181a207048980e07503c113945020520311009503200d5a01030b04a070000381e0a120001300080240110b00004000d20340c92030040d410201100d0954004480f0b10400c3d60249071090f00702d4039603d80d502280403450a02981b20345851000580e0400f1044e1040c41000710041e03ca0400782c003107001001603442c1d589a040c8400d540d1000c3c2010b490143c494150103400600c00707918554080c0f450318410401c10320b40140c210145600003035500b503a0903000786070b002e000320402003015089401d00c0098501180c0c3d20031917042026000000d1840954030724010001400c180200350700b05800c0e2405154018424042450f2890100c0c0003000101c4600c0c00082090300400e2780703510700110701425580090b1407240b030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 836208579 1250 836207329 836207371
    0x8061302010e060903010e0d03050105031b06040504020c030910023022090218010f0206060d02130905010e06150a0e040b0c040306020a0c051605030304150c38 70
    0x3143c2084d900a90036540384e0010502e118030500800c0850000d6881c0060154140801d0500c0d1504604689003203c1880a021785c0f1680d50704d0507541281c82c12a0003598504100c5881400d43c0943c5181c0f40d040224035142508030750300481e00700f082c20340801c40700044510b90b0f040190481080000c0d00340c800f10030043400b800c4010401c2100c40021415114410b0a40d4074000c020490b0700200c1140180416940c6107001503034000c00014080038540b00900d5181828000203584008103074009104000550079068500c420350041500c1c2904a0000c200c00101c2ca140c907510380e841280c081103011850724030182940307403c1c40024142d03a88a501c00080760344680c0e03541d030481006441c400c200e8209010000000741035000601d41989142d035449901040361801e1890030398110401c41c10017070108010b00c00d0351000000d440807200c01c050081e8600f000c4040a03580c032062618090103080e42407202e85040b00841c5000540303030000720f144002607081d25000a441501c1a2100901e40d8850068885 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 836209829 1250 836208579 836208589
    0x5060f0f06061e07020a0e071806050a020c040b0111070315050f04050d030e0a080406021f02190e0402041a21191a0a14090901090b041e02060f030108061302010e 71
    0x1500f05d05c041c1080f442940c8500910907511400c171113505c00039170320340c460b440b4490844c2c140000030b0200307040c518207040c034201c00603444811050006000700d0b690f4031000f49030ba100e4840c6080548110046d00c01c907036104e007440c074050260101d0100d161410440410549248925424801c6030820b020b40b48010700d10404402814005080007040d116400c170340f030003042c0940010301c000d001030b4006001100c8443c0c2100d1041da06511194151417041c083d14981200d83d815500b6040400d00d0320301d90a13150400060024003d07500260107030000b140700340880002000007020264445290703040307000700e0a04d608240700c01c101c69105525444901c500076a9015400401451004030320b0300e0f40300140000400c0c0310400540c0000c450b041400d9003000759081100c84180c01406010081c48488080c2d241d0868414002d80010107900c01010503a05080101c0703884c8070740f81d500070b065654400100d00301c00d020340c20078007604040707005600108007401d08560350010003e9068403030702a07138180002008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 836211079 1250 836209829 836209837
    0x102010e07150c0c08010204121a01033810030212011a0f040902220e03131e1707140103140a022212110303131a0705060f0f06061e 58
    0x40e1441a110130203c0c4220080c0064405041c10148000781100f49080540c08903241c01c0500028070418401840461128105a081824090042d00c0751001525a1030325110040c442d004451001c81b00f07210b0075591200038101241e0084900b01c040302e12001482d400c03900482c1074000c890b06034102000860078004200042e00038000d0002071440100d03004104085098041010038481c401c0c1041a034014920604817003500765401035040c00d02c400544000406140a0141200b04070a849001300c68030702c01c1c5c0406005442442d00e22500ea0008681d03540290303000c0c1d0294450b460395580c03013a510901c03581400044100355031285071500000b10000f580003045660754103c030b03c02201c0c184841c04442000030211907424003800222403c0605100c812003030103500c01e4200b00604181c0160300c48032441900c056060014151312228a444045d1041c540020301501400e020822103074002c100491088542501645050b03803040101b00b254881c2480c4031a1585402150420312846100a8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 836212329 1250 836211079 836211083
    0x2060903030c040303441e04020405090a080a0c031d101d1c0203010501060f051210150816141204020d0204020403080c010b010203030708191b0309020102010e07150c 73
    0xb04000c071420b441101c81b4050440c09074803180e403071a08403410001d05041c01c2130b0703c030194000340143e21241c3c02450000c60406000680304640b00c20229202c1001448088174055105150b21b544091100c40500034111000094002c81c10208034500c0d09100741c4114444150300a151110920841009607070000a14112104115610102150a4031004840441c0300c00c400d075058002c0b44144101030a50754160084010800450031952401e60080280c50000a020203c00842d54a080940e0301044050780300b019224080f200702c1c00c009401240d91030140155003100541d800145c242505c000d030010000d140100c0303042092640c441c22005490342c2140c80148500d10540c203603000207041c0c0e0459002503522940000710f0402ca80d60134440c0b0340740c581e428005036086160433130029026410051505074040b00d50001d00060792a10782c03048282c908100421031004400c90001030013810004001c0740907601e03000703c20300c0805c00000c030075003140d0b291821501c1c001181030003200c8846100c281 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 836213579 1250 836212329 836212367
    0x6090f040311100f36080c0a110f01021204060f050405060c010203220515070507060f060f05030a080906070c030602070308060f22020306010e09041202060903030c040303 75
    0x7240c2c400402072056102c0b01001c0300011450003400510030044501c1c54070020541d05003990f40e00c610031001c000180d5403061842000320141c0d143d00741100d280c03107811611a0203008a00a010030001400384001c410300d070503240340404607401801039a88410400500035815011f0004000d128071503056109212100e20b0714501306035039000840d2560b0487c84d96094265004030400c0507224428940e921201020080c0c142c8110341e82c1c80d01911078213540d8880c400d582d01c0c0000079001e54050411030b1080f40e84a80d00300181c0700c540b90744030020310326401400c038241c12510300003505160000d5010f442a03080202d540c5809119800c0081e6540070300d400720344040f51001d000010480c04e10203061528007035140c1704201e1418608002d00084078848852055a08074000c0e0f51106c0d020750b0f82c0d601e80c813402c10016584e4890340012b80e040100701580c59070140b203441c01c0108100021140019a20154088031801d44900c0d000c251640401c4030090030b010b07401c0c070080000c01e1051407403403204180320f0030f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 836214829 1250 836213579 836213597
    0x1b0613081b0304121e03052205091024081501090b070b01061808031603030e010606051801080f040b07091502030913060807050103020f0f1c0c0806090f0403 69
    0x1c090b0564000b40d0001c2440c0d100050b104080c010005a44030b09500c40210021403651195009801801141142c408510050421b40184c000264242c0003618000b00f0801c42860000007140d0010032500407282c6d442c1900452804000b081c699071002c590241c2c880800503650300b81c04041c52480d4801290400425000000b58103035000020b041c614000c1036441965810042c0151042621003d44e8403051581041088010000700c113071001b10840164030b15400301d0070304044020b000b00082d5030710103529041000808a81150042000c1e44041c0c40e14202c1159243c015141b01c44c00301c40c0350b42e00901d0800010000b8042c041c03e41e62080c201c2c10031107186038543c2c0280603c0a485074600025a0000420304010301c2d210824042250325420140581d80c10700c201c25494400511503a81415000701d40d520401816a09413140e030000072403000e0312040081080004550100c0300c0203805481c0220401c0400e1140d0800c0744900800f400c02c1501c1d8030b6030071100300c9860008009404001c0f0301c0c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 836216079 1250 836214829 836214877
    0x705090705090607050c040509030c0d02030a12050a062102091005030309011116030f110301060b040b090d12021f0209030d11010f09140106060306050d03200102030103081b061308 79
    0x21003890b0060f21010012b54031201c4a5440618014405d4406000c0d07520500c514103c0d1540b2100340c07451040c108a01141503250b070311642c40504016040001c00982e8840c031a89600010100103407098021200a540c9803508030501c50000800d024054054008000c21a61940150340c2803e040c90391101b180c0c0e07070f020344005006001e01e882d0011541651140c14010030301c03507400d20b4121070840840080003114584800302c030311842288544405d0380f00c04103c1103803a6a400d8080740c2c0d100d400c40240d0308036400082000303481e04282d0140c003003400311000d03000080707104a200391200440d018000b031030300300c1820303074241d4410b6124042a0700945d200c0c1d08a880343c0740c0a00600300711600c506a4082803041103c4000c1c207594040d00140d04052600f102080a5030302e00100b850710035050304046040401029044074021030b4603001a480d903000100000c104411100189940f08030300b0714509070070310b03050901521903001352803200300542d4440341c040100307000a00604600b5840c1c80c01b601081303420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 836217329 1250 836216079 836216081
    0x3210e0a08030c16061d0303091b180a1b020a050a060908040b0d06080c03012007081b0625170a0b100c06050a05060603011205101b020705090705090607050c04 70
    0x2a0211391541d00c0d61582509445010620042c280c80c6c80051411880c180300d18a507034640e642c034580225505504049040d131a00d42c520210041c1ca4800b005180c0341c081202805008a24140030184081542c049180d910103d042c45c00036030b00c100601010401900c03001c018002134401031315001010040003e007400c044004000175800b1f01d60200c1d14038035000390300d0b081c00c1d202500380b40a0390401c4e513080040881c4038a03e981400303200c007006860702a1403d241410380280302483c00d40d20710003890444440400a803a5110ba403180d10181d8170003c2442c80400440d424040060214002c0b4510500240c0002207066100c07004003c0000e810300c0c0d007000a40c215604a168034082440c0040c0703030342800024080c455001801040c148401e080071710104819110522404400100c2004024100b02090000e442410460041440b00101000c0c403250456801065030002d48540346000805085c80c15007140319507880c3e16000e041c08401c906118055010744400c840c40d003e001d05118655031a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 836218579 1250 836217329 836217367
    0x5091228090b160314130e1f030b01031217180c03010c0507061505010507020910092d0e1902040b040507270e07260403210e0a08030c 59
    0x4a00d5003140c3c0c954500b0094543d420300401820503e0003000b40286e46e44480086030219400200640a99a41c62000d4111039090f000e80386408004075400100f07010701600c3e0300c0d050340e00684075808c0740c036070340002610500c00f944555007210f00c0d20b800003581105400c161041c40407042c02070318040810840064211100890403001180c0085800003e201181c0325585000c2551140f01d100c039400d0074006441401000d00003813240d80c4039400146043c4400f0b02d00002010001414040c080003170b540311564a82c040d6440100e00344000003140a61060f02900b4561202e6101401e00f00c0092103c288800d825001d041e600320380c640b07000400545440c030690740300d41c2650361010301c904002c0e00c4008901c8031495694614400202c1c00348420b1960b2074040360004081e050000d21400791070003100300304e030b0011113420302941d00b41e0401040c1034000011812011102d102c50a0047c01c0303a0142c800c850503100713002d103684e12065080b400145010019500040c181c00041e0400c9201c2110341e9000032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 836219829 1250 836218579 836218597
    0x1200303070e1e060a051303080406030b0402120606030606041a0307030608070e010b09040e03030f180a05060c070c081e0105150f1009120605091228090b 68
    0x4800020005000c2c0d11551045281204071800e03510509111404074809440401140c8030301c40001d40c40c00000c0c000c9086586c070f00610031465102c5552030502c0c0d04541c01c80d11541011a0030440300f810ba0345824802c035010014000300c002140e45690041c0089500000d007460741008040002140c07841e4034070a41100308240c0004181d59161241006003502c0f05640700800d20b81c000b41d004c2c00301c84200801541035855100005803202200400100074051039080d402c06070100005201103440c074601400c0c85078241d10800040b00c3c0a24446a540d0403a8582c0501144c006a0119070b101d0850750040130310900401d4280342d40c58039500910306144002014071002c01543c030300c15146010078060682d102401035040c003c52140308011605102200101602c00e04080e0004190b032400380400401502013654200c81d10916440d0080042c14244c0e4081e25034400c440c90b0b810f0101c0d442040324251075040d0043c8200081124454540031030780f030764400034440e60b0800419a51180809000501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 836221079 1250 836219829 836219833
    0xf0f051f060f0e01030b07030515060d091703331c2001050702040209040e010606120f090f02060d06050303030406050f06120c1c080c16081501050f0120 67
    0x1610340b1141802d00102540209002d14100e0010130100d02c103c0b1a19030712039120300700400d20b6550b8410a90040560304025540801c0210300d81030007880075805460010f105000100c038099501d19008203d000844605816510200507c3c00f90100e92900089491f120480002a603007050001408644c0c500601c14a4102c244030321303020b1004c0b04207203412040b6160a54182483d5480008140b80314206010b0b020710707000182c040d16615107500221a0820f104000c00c203072515260010480030101d0303090043d00c4d082c05404890716200b841010345559120528800f039801d40e81c04d00082e40c1280c40241c0d450ba0342d0702d40019040d10b0900007544142c2c810742c0e0005592400b851b2841607040c0141006000341d0110109003011800080e206419000803071755491000309060b19115015400c41c401840e0000115000b001d00400142e1b6231030100a15a84040d1181c581c40020350b11b100c882c0c031b0b44113030214100c0100440d00340384c44a01811441854100700c035489150307490030701e401070301b0b00d49a0507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 836222329 1250 836221079 836221091
    0x14040b070f030b030712260919050a0306050c0c01020705060618070819060519080c151e09033007030c060f09171e0301030f0f051f 58
    0x1076110103402119542420300b0003684601d0400301e0b590380c07000c1c0030340c441003101a410310050182494441c201e40f108111041c00007002d80365102d41c580c109856a600503620000e1000005c941d000305101520b4002d040510354034599101c1501401018190200b400702c104510b0b599004203000038800c880c010350003800e850070410107009000040c101c10007a421829400e2126540d40700713443c0380e0408101890300c4481e803034145a0100800c0c8507480781c0d500c241403642083c00181081403481c01c80d64104141d601c00484c51040c003680c2000007890044010b020880c00200d4050124281280022180c0250a204480001c40c1c90204000050307600001041d804030645010b0491180c242010f031001c0d141030000f641ea0141c00b105000d54014202038880031000c440543c550320007100700d9000728080010750101602c6150651040b551040035101304081104041c2c04d4104a03412241d104150044030200364a4074011a03400001c1202d00f8003401100220031000380d0b058410310140d0741c1c400110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 836223579 1250 836222329 836222341
    0x31003170403020d0f02060d0c11070f0f0303180905010b0c0c060f0d0b03190b0103061a060f0a170903180f010206060108150a030c180b0616030314040b 67
    0x1280c0000c0314165800c00c000510060722240484110355500102081c003403c031520015040340100900e03649403600e0140040c005580c02800b01c408501400140c640c400c0c0c941d10300220300754050003501d1a045c0030a00400019115030001c6003403002c0302c0810a174080c1c60b44a40300640b2420303803101e0b01c4600e01040020740d0141c14032018010f840c1c203c0d00c1c1c0f481d090f00d50b00004030780e000c2c4100000f2003c7d07440c07400c0542510203020031000154990302e2900d0700c1c0f440c1c0c542442003c00a00041e2480d07841d0021640b03811601c01d401c0c6980303000080405040c01d04080c85c0d0b41c0300e544015044007c01400c0b805107107120816901c1c0a010300394540140d5110500c050307000e441d800c3d03035501c0c10744180b0b00d0034000300d49a600842d0668000a0030701c0d000d0300310350700d81c54203002c0600350380785c00c54019085160000c144505d0445810523a8002d81c0c201c1e1031380c8240003980080d9400108040c0e4808002c11001f9401a21001c40d1898240700b401c001c40d029080129a6564a82c12201620340216640c20008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 836224829 1250 836223579 836223593
    0x1c0e19170d1b0309121b060903020f0d0306050607080f0d0608100b0a05060f070507030816030f0f120e0a06090803090106291e030a060e010b0c151308031003 69
    0x90710340c05890300700001030702d5485d5481e50303200c0080785505000c0c0550403000002160075242c43c00c00e8001d40144502c0c042490025511054200304131650f0046926611485200307028040403110003c04090038807040307441e42183c903480600304489103d4100b040f001e0003080340c0111030040c9444400752080c0481050103a05445070701c4015440340113406000d200c20380d14034041d100c4201c000700c501601e50380545486031034907a2030341001c0c108103000301c0d5912440016403650107013075200e030756007020303600a225040d1594500c440d0160041403600a140a00030555849421000c1d60041220203008054a680e01129001502511078005c0002080a40402401810003c040c65020480110721905003001050414080c185512000007460141c145141615185402801000c1070b03681c00c2519043c4001c224030b1169400c0c102102c3c00010741d4100d40c01c240d491369204500501071040e0000c0305030292a000501c0e00c90712612800d00c0e030020034050405544206030502003070010a041d405e00d44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 836226079 1250 836224829 836224871
    0x42102150a14070507030213020309280f020f0d06020c0d050702030a060b0607020a0b09010f030e0d14040e0403120b0d02150304261c0e19170d 63
    0xa44400c0d810045807048a81c05142c11180d0003110b00d9803500c400f054644507003004019403006c0c0d0320104a54030342c481001d0340c1e4010341c01100c2200480d4504c3c00d035400380962030f59071013041914490200361010007142e54480b510b030500d48018104c20009006900155601022440a8803a1503003c074540e402c43c00d04200c41184602c050901c0b40c1000d030b460380040ea4607003000800034221620f900031041720743c840c0310540c1c2c42c03503900404c400580c58951442d441150400c0c0e0b85c4c20b00107015001240032903406032150716401607800300078001c4d803c014402500c241001e066111201d143c01c0000003204640604024010361080c0d840c488146c404403a001c0c25100c01c0d60802c0c0c4070340d00201500c0010795a800c103c0d40b45140c0460000e841c2e65442c00c01000080000710b0039071804003124204000444414010040c41c20171018a05075003450562040849600d480012030715440f04c402d58814036414140c800a03c3e1080700b01d000210740340c0d1303914940354202c0d00f00d903155180c8641e541480b9200c650869 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 836227329 1250 836226079 836226109
    0x5120405163c15140417060f010e1f080307080a170c03011a0d0f0f0c030504050307020607020d0f0609140f06071101060909083703050705042102 64
    0x4000644000040008042424860f490340408594020003820f8003a442c41e1800b401d8074110991034991320043c40d00d4002c4541c3c4401d4860240c240040c20510700354070450b040c3d41c0700140303116417503850086400d4000c0c1001c5640b050048102d80004041000300002c005c50341c0300d050b0442d141c0103200c00150065001e05102c40e240202c800c10407118400c0941960b0454403003c002100d04100c01000e1000740c4180380d6800d18031350414414030341c44e01058001303803403840c01140200540c013040701d0120110350059034010510303007040100c0009442c0900c054440c440c0001c042d6100b60b0724a41ea580e006920f200421641652128a501d00340040303a01032841d005201030281040707100100705142c0700d000080c800e40502c483e20500c504000401d60001c0007030100140104041c3c5103030f050803800d40e0010500c011a8200035055050280300c200441240101c40d03003001001c0e00303801c4400760040d00703004140d1130801000b0310001542008180c0007120390600310016100e480c1481c0140202d00c1000140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 836228579 1250 836227329 836227409
    0x510090c0807210b031912020d1b030306051807020706110a06051b04030302030c0c01090501020706051813050406111614070801110d06050d02010512040516 69
    0xc200b01c1c00e0304000a50800d03407801441c8115094640031040041a04214040c1c040c80780e05422405038045c13020118000d070207a8980f03a00758032141c03c1240e8507090500343e80005200c8905e9514071039000c24a02904601c00d0601042903a11031000c100d0300c1d138042c40710000c000c800340c0601032141c2d0140500c501400c807074500662248090a40d040c1c2e9056402001801c4030380d904002000e40c520304c2100051004510030340760740c4d00d45c0ca08000f580c82d0001117501d02e81e406050030385501980a108503901301c1c0d6060b0050020640307001010789054114510303001c0c6070100052400181c2d5034201420407000034841b4001110b0400703041c40f4040b030743c50150341c0380301403020800721110110522404803102c1c6d02094103000e02c0c0c41c000103a07003803204a501c0804150300f008545203a40c0d10303401c05884004480e80040050513600d0041001c50100303018042c1c040703079041042c4c2c3d40314400181c04941c0075004004030382400ca0508081850002035621806584000e0800d200030440c0b403039006000e2884c0d030340c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 836229829 1250 836228579 836228581
    0x4080307050715030606052a060a02070c050a0609170a062307033b1b0909011109060342150f030403020712030c0605070206070815030a060510090c08 66
    0x80041d019118042188c10141c50550640a155040440c40d02c9001801810740b00c450034442c00300b4010350070841003222000d01c03800021900e0305003d00500b0407504966600302d503441c0340004404880390500381c2040f19015201c0b0714408601d81d400740d0340c54480d0548440340500310681d43c00c4207044001d0442c00406d414842005001080300030450740300d00000340410600d428024207806000310500c00003510380600604240c0b0000e506240030020329050707400b42c070540d80c0c03500a5801c95820381c4000b01030b590103010060342c50400b00061540240381c5044c0c065039504070b103920070a81486004150f544003007404140c21000c0045c001050610041d5420401840d0110185d0075a021703d0b05180134100c0c01100203410300d803080104c94000d000a9586241d00001c2c1d050040200d600350800352a07190405012801c040d20014915100724241d9650000a0b1a224007211120581c0b0303607169414456294200302162171071150a004498500e00130011600c0c20784803206840c420301d92202403002201c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 836231079 1250 836229829 836229839
    0x4030c1815090c090e04050703212f1005090c0411070f02010507020a0803030a14040b040314040f0e04120302040302090a0506180702010b0112061415040803070507150306 75
    0x580c003001520628800407802000c825821640c00425610803006504040e0600090100200303004055038080c2b46192145440302601c00250008c4600c0b250008003001200720000601c1c0c0d003800322440042c07500c0044440e0200005180402802c0039800d610355840500940150800000410103403d4a05006144048030f0300040c5004041010b012807100325150b00031a88104101d459082e8018680136801e0780b80ca090b07958075041200c0d5405c6007841c14891400b012001c1011318411b079480314440100d5651994111500c402e40301298102541c2808042414084941c0c80c002070001e017402c840807807415040c400c503c1c0481c402203005042c4100018009a1552034501e6440b41040b80e0200300d60b200d0b24041803400701c0c0b42d103c820b1020038103424002250b9041d005801ca0203000d99900d102c0840801224040310800c0c0f0410043d0b001000e006207090801c00800c10ba8010018100382c10a41e40b02c0c0c0c581c0c1541d10810b41100c1030340162505100300d0806040000c0c60f10458079007001014201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 836232329 1250 836231079 836231111
    0xb0a17070807030c14070311010b0d0b040605061c02060a02101b09090c050301260604080918060306060d0503040312020313080f1f1503150f140703051b04030c18 71
    0x2d406c080c041110303184c0d10f1070322010b09400c403c42220000d040d0b40314420850804000034101650100c072400d041c0404200646000341503c400c0b030550041c00304554a09900300560390740014150400d500070310700da4840fa064030f8072805141060110441a07a02031520b4020a0b071a40d5420601106240c041807003241584072040c0c03410754070007a0440298102009003180c10301c1c151301c0c00d10301d03074402e800c208404c00c110a000b03491600700680d081d01000106000640d00c0490842c4d40d182c1640c1310758000384940c0707440600f030081f1502404c1583d04d820b450751103031036552100408850140c2c1c00081c9040b880c9100a4940c3c000340140b02c0034001807400114a19101c01d00100c1449506d03076400020601045158441c0d51201e4141021b02400350740da140644070882160280980039240a80c80070551040e80104800190f00d001003060396640c854007600141409401d04501030300c83c100c1f002a40703c0c0100107001840c050180c1d688902e1419800343c01d0300848140341200341d818803607440b00020076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 836233579 1250 836232329 836232337
    0x140705030901030c050d020307020c09060409030e150c03040905220f020d060e03030a060816210c0b0c1c09080a230d0903060609150b0a17070807030c14 67
    0x424038000c544d80092000c00c840c64010041125006840001400b600030340006044070074620590360005036603513540801080b1880848040d0104070700d050b80326082d1411000b0f0303c0c003e000c0c4000c0c050901e01d500701700380c0c51500709403c000e4000b6614000d1140f07007040d01c00c1d1801982c041c01d144102800c0142e403600311980300441c00134016800001c5003c10002503070001e1071b4409040c4105da0f181c1ca003060894000d84294422400b9500440500000003140c00c94010141c1d1041a818030b103c5030046101050002d4181064496100c040e10104400ca0b00d20010640c004010000301010400542e1117650003c8000c90b100500030b80c002c1c100240d01000c1000c00384160401140400a80764004100302211151055045400380002500d035140d04010b0a0003a02d001d840208000b80d1036162a00843c0c1819400c82c1d5682d1441c001003000310048402402101624641003030452682c0303c40300e602e484280c0d40c20000c101094200402c090b411701c11540e03403007150f02c0d00304213007800314840c05903500c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 836234829 1250 836233579 836233597
    0x60b0603190f1e05040c06031a0108041103030309072c0402041a0306100f0902040e01050d11030109030804210e0607020a170609060f01080309060d1d0d14070503 71
    0x1444401e0840e01c0140d50380f0042c0c0c00c80c801d9032030840f1030700009039040c0100800c850848403120103c9002c02e03414420321a00d0805e0340180032000024180c000103441c02c0c00b00600448410704108640342064500f440518018180d400c010141d40341890210f0040203010008945807451f0326011801c0b41d00800e04890304250182c50000d030248801c0740182d24514000b051300c4d094490041403284100320310300c1802c01c03941500d21540c2c0107502c50003108140e10803403180e1000300030b124005214501d86800303c20925440344540c007126194480120f03095401c03201c0240e02081c9020104000e11407010b0007184180440038031401408122070024109403030081c0d15901818010510704219103a09120031f000d441c8913140c030441d03070000a02c0705a40c5d00c0b0445000f00d071400341c000891804030403c98524144d0705100051801c000c4c4420038400b00e03401054558244a464a80c40b04280449100c41c0b0034400e840005000024000d14010b0400c0d0385120200c025001d0801103000455004429500504 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 836236079 1250 836234829 836234831
    0x803061507061d12030105030a020907092103030c230906040e131a090601120c090c09050108090a021e010c0b07032901020a030e011107060903060b060319 68
    0x40c400c5880e00c0300a015404009000d10301d8401586075010000c1d410601207880642100c80c09248615103403468002845440d80541c0a21b21800040c07600740301c401d41c046050718120004503610900304c405694944220350100380320325100c500703043c0c0c1401030008090107030400e411a006c904016041494102540540301400403070454a5651820101d80043c60010b000d04610b08010b544581c10843e0f40e081110308140c041d00d402f0440d000004114885d001c0b60015000503032030001000d90b20140703468100e03140c0c61542404284115503120300c82520040b07540300d000081c10070002500b424000f4150f022580c1c081039520005a5034203030100340054021034000399040382c0307000684d60a174a40758018401428041044105603155110701d10000251080c040444211040c134064540b120440030300680004c189107011a005480100030b5407418507040754810a01445142080443d0708040c001541d503030310810a01c1114000d0300042581140c2071071541c20007404405c03d81c3c81c2250300c96012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 836237329 1250 836236079 836236099
    0x605031f05060d0f1a0901030b130b0903090102152406161b060f17090a08130f0e090715020c180402120f032209020406050307020d0c080306 62
    0x3440c484580001400d02030101c5845980c50215400501280440810542d142071454201140e450440c01c150400282280525909581303902d4544003004000c40104002c10f0440400284141a003900c22800c3c1009580c8541c0c0300342c002800c08410b203113500700128201c0240005120190485000c0d40f0342d8551958070341156070085034281c040caa000c80c2070650982c002c402407265581030b1001a9404030220805580ca070642a41d920310b00b048c402c00060403070351012030314082e40d94540340c00154210840316010030a644840c0240e0004501507000d400c800070802248803d4103a107005091100c80e00d0b111440d101050300e039220713054425580700003940480780c200640280102c0c0b2242d4000303011001d182210204140040801f0340b41280244003040d601c1e00820008103919040e041160080c40c58a9414031106c0088042c500705030782071104941c40000c1c05c505034401003009001948803140c0b207184c40300010307040081544420041c0084c0c080485c0019442e2801c50703a00c07074001c072044844 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 836238579 1250 836237329 836237371
    0x18300912021207061e0f0e010806030307020301051807060908033108010207020108090c01080a0c02011e1a030303010605040b1b010e0a021c0803040204090f1b0302010e0901060503 79
    0x10900c021800c402c51400b9508001c56603070790040f524000c40030044d20408140b210100225003118482c4103081c0001d850a0301502d00e0340c420202d03941c100e04018222030038440c403500081c3c00c448003071300c880350b451a5000e10310b80c03030b40024802d000c006c100a042040b01c051800c540241c03a48100d104100c03603452984030080c100030300c2c04410014044140341c00c1c2d240e207481d400841c0c001e500c080400e070b01145841c00054400c03c400980715002a0044e5503007102601d030172680c80082c10f600c45030309066540394000401e0456000da00d2080e0040c0c44e0302e020411248c0600c104225901403105240640c200300014003403d41c2003c00c59013180c8804000350350711030911200040f041e0100400c00810350808005000003000000d03100f070094000c03951543c088000007550421a44110402450920244005009440d1650100e0410741c0600d00080400300350340d8074001a0410716045001901c40c4850600079560312541004a112042e111090035504241c8040c29500004055108400e0054500c200c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 836239829 1250 836238579 836238589
    0x604050a090f0b04031e052a031c050a0b011b0309120516080c0109140a0b041d0901050601080a150504020a030e190b010303050d1830091202 62
    0x5407240e008280707082c0d200c00510b0024035245007a00c09400040600a44e041038010503280502c007403601d03480d030030314001036240b03000b404040c918040c1c80c18001c1405103840108051006240000920810030031f07001e4100110400c0358009418075540610b0600110b0103070360055000782c0b003072006104000e4900a186000c41c2c01d02d403a07400005442c1d8906040508101d800180701c2c9499041c0140100981e0b22405955070b01c4d9014030001c0c3c000780c2012810400d40c1204102d4030000300024103008c8059841c0d0310165000d91003a40114000e25510381c6080e0350140980c0d043c0d030072802050003401241840000208128000303485111429070741c1c0600300711015240140d0f80100809003081d912220714542c041d0042485908040710350086a42e62560401ca000742803204a43c0808201105d90850301d046400350844a4401480b683d41d080100c0a607014940c80a0758910a801d062840c03403c400c109040c0d951415802d01e44a151f01c5000380015811940c0c0e43c00340e600c41c980c200102005c42c00021 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 836241079 1250 836239829 836239841
    0x60308070807050c100305070809010c05030a020c2d07061d091e0a270f031112040e2d0a02030c0d0912080f0108030306060d110309010c0e0a0b030604050a 68
    0x251700c400c0d0068103166450301038108034450b14951300c0d001c010743c0e2080021820f03569034035011000100200002a241c0450f82d0280070481030400c210394401200d001561075695591303440003501c0400303440420310b20008000d40c001402c0b1600d00440d104001d039405034200800c104070540303d034103008005207503401100c3d00c50f0a4000410a050b6039070501410900050001c1030360041c609241c882d20780c00c42034401881403240d55111481160b03038441a20100d9030f8020701e0300049000d0007404680d8004c03100d980302610192030304991048090a0140309500703100d07250103041440f5201d43d510110303842201c66110380d202010400150b56543c5120841c0074901c140e07100c190100d40703085024000d10210720446182d204698407640d14a850b20803100748800ea0174071640d0f41607481040000d4080c244200075140b01034480c4ca0109544c1c0c40207401a1458004441604013030703640d16403003050158030250f030406154094941801150800b003e60070742e884001d10041c082c6403143c0100b025900c03140c0c420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 836242329 1250 836241079 836241103
    0x90d11031b09010803120c0306010306030b090d0207090902010f030b03070527010509060a17210c120901020a0b25020a111e01200d0906021006030807080705 69
    0x41c600303080c08940360320180c2160300c00541c0985824000410b10307840000465088291944a200c695600c0341e11304600c0364401482c05041540320140000022003004031103002da500742014118100d40401c0080c9007440030740c04196880e04280303000f800350740c0260320314100101e58a07000c40e86060501c042443c103442544071a806c240d0311054000885034010045c2c8401031202282d10899a0b10010010182410340d01140d03c08001070081100c8000e01c8505980c0c03e086500341c8444520504034100009142080b040007454001000c01d00c4050a106a2200c0e040c280f4110303003070804400000790b5410f05032000401c1c44220401040b12001c83c01d00142c0d420048000b016804c0e441d03038000035182c0146581c00c4404c0c00301c603c2485201e14102c50704e103000380c00345030591500340b400000465609100751800c00e0700c0780c00303d21940c41c81a001d00440c811134145850f80c400740380c17034035400074035081030028a41e2110b4a040c0301400040c00c01c0c41110102d40d00981c0c01511100541840c0e824034100e00e1507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 836243579 1250 836242329 836242333
    0x8040b041a07050a1215150c150e43120f0201090b190507020f0d12110102030c0a050f040b0a08070e0916080c07060510030224090d1103 60
    0x402c1081c1e82d00900410f03166010740d4559452070340c002d070171805032043e0030198803850b80013540501024521030722001181c2034518091541480070344900c128150135020007440b003519100a40302c252020001030320b2001d0388540c0d510880e003003030031a070321034020031000b00d41c40d42c1d14210b09404d400360941040010300500e0000044a6102c2c0ca010546501d030030204a01265141c0300c0000d140c0c0700300c0203807076441d407010400c050a00d80c402c50445156000c03400499001c0e04088a649007610350203048803a1134442d00a00300b03c00b0f038669000c2e109603407180329400580c0c0100200001c0492490070740721165480e0410584070030b800c0c5d110304200c1c000c5411a4256510101d00e6540195010140c01d000d0111911500780d402c0c12442031140c0389004032242c1d80c2760101750041c1d00400c2d120300007095000307000340070481c00e0000310740d112070580d179040c0c0301d0501414190074288294548250b805085200300b03074600030001d9640480d0300c40c900070f0f4040b0ba846000010350a1042c84404407511040c03c1c00102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 836244829 1250 836243579 836243581
    0x6050f07171017060f09070f03030806012c0913020637080105240a0e0a0911180109120b040201030f05010b071b061b0f02040c111c08040b041a 63
    0xc07455540709002c1741c2007054502c203000400c14040300461143d040c1d501709880740c0d4115065032010b95039030301c01a2003907042102e00440d0400c0c49004004081c0000c6c2e601020b103000c000c50b0803c11a4008001d0401c4100c01c40c680c03d1a40103030760300b40485070f15004140307884800e41c001803d4071070903404c45101e12100b14610303d000965943d2044825040e180e0031600846543d2035a10014841007a80011140300b010400441d10b0b0b450045510614412000748100011600c544080c8150341e841c2071401d85228004c0340d8410744803a0741d54410703c00750080ca031200460b4138017203000c0c1c4207001e160005404584604040f1b400d691280d0003020103651102018452035941e4240301c20194042c1e0000e4825003c980310035880150003401d207904560301d40c0d80b00400e8400b00c045210001d00c04100031944107102d04800001600e4600404200c602c0d20b44818008084802d095030903e400446031400055022001047c902c1e0014225504036401031820703022a81d5600d055944880c034038440c2600050140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 836246079 1250 836244829 836244869
    0xa05030a08030405161208090406090c0302040501080c0c03120a090b01030c0303300b220207031206031211032101060201061d01050132030406050f071710 68
    0x40c0046003d039109500b160800354101841c0d0140001c030740a0802c910701140300d54804280750780050184482c000340b0004010796141980320441d0506124580441d402080030065036800a540340c2d482031000403c5d91078034400031003080d2a441000110403a221241000c00c40703140d000c9d44880c003034a41c08003480555507101d0030046851600c80c030084000803c81d0914010f2841c090900c1450010155000201c08100700715020103000b03481000381e00f0910340702100c0704002503031464807050344800c0e0006a50b4007071070070010940800002e52500c003038141181000010b0088074003d85072440d1307150541c00030b800b81442c68250310594041101c7c3d0820300701980c14484401c40e0087c120b0728070350020400160344040311003c0c0c002c0071a0304034819880c01e004014550207502c44100c1c4490701d85241c070f2000078000260f604010182004c0240c5a0080304210810242d8462030350031500d2050849294a0300030f0004103001904101001c0300d0854001107281120041088000b500074804442c40084541c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 836247329 1250 836246079 836246093
    0x71e0503040c0b13032a080c0307050f0d0206030a020a090f030503030a05041a04050f010b0f0f101404080708010b060304110d0c050423010f060c03031113120309051512060a05030a 79
    0x940710070611b039030301c413500050605000920f0030121200a005001154980700402c48404000322506801410441d60348005079079510046108032183c000058850003020b0700185420080c2c1c000e0881e0750503548003400840c1001050b40c0d80494071076404100c030ba51718038040891280712b1030404000300d0100309001c104500480c0c0400e01c80c80a200030000310b4207450800041c0e40107401c2c120341107040e50306d9010041c101039032034507111540b60410307450003620340000e04841ea005521840c2c8582142c6020302c8010000e001d00b40c1000710448425056091980340e0070380d2012a05419445001c078005000100844440900000c280040c8100b210f84040c070b00102c012200f00c040c4490642c12500041407003500c2c00950010340b09680d490491380852a40c0540040c1070401ba855805101032242c3c61440c403e824104c006018441c0142c8103010141c98094601d42c01078011503c0350003074404800d04818070100751210140308000b520f4281d110200840d00112058003c180c06000d40c20840e4241b1100e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 836248579 1250 836247329 836247383
    0x3020706050a02090a090b030c180708060114030a02090109030b0106090e130506010605070c091107060f06141903060f02070203060703050115050c0114071e0503040c0b1303 76
    0x2200d050009075a60b69207202240304200c015a44030190580034014038002d540300c0c185454029080b62001902c020000b0402d0f00e003002c0700d15280c04004104489107502020361a0055020308203d000341591200d06480c40c000106a5032109a000c03c030020681e20511814005607040540340d4429611000010034000c10390290b220b1914031140401c150b0950074086907990742e08000584400e9003080d000700c0e840d5000000680700340480d4480850101041c3c800c2d0141c20502210040d60703840b141c9400b00c00e0710000000f00c01d01600d001010410410980340425041100311003000e40043d251508441c200c54070340002e07100503d050443c60703460260354010000d40e40214102c43c01c0d9554030718102c1c20b0302c2090040c0a4104212100c2d03452860140016200000c40040041030707000c07803102c00c072002d41021200c0b400028062481c0b030348081104055510541554a019031452600c0d80358404006114410b840f416180003c1d070388503c10701100100041c2d80e0102458409a02e070710b4600e81c075804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 836249829 1250 836248579 836248583
    0xc12060602011b0e030c010c0f05031602040e010e1f020d0515190b041e0810050604061d010506030411060a18060c260d0e03030a05090303091c120903030207 69
    0x100f0001c6244400d030140e0764094524600034014041030001400450780c0f120b41a90459507000040880390004200384040d000510400a007103200d01500e004000a441c0813000700c20703090f403410780c030800d5041000c103c0724900c0c2501c4600c0c01d0500a03a111a000030320079903441d0360106162000340140c51360f0642d440400c480003101c02c014201d20201c081802c90103144119400c0741c608010820030926901038801395003001ca8030100c100740d40d0f0310840b410403001e08018441c003a41d9404114183c07615110712806010a078907011240040e8506404040342c041c05140c1c400e040120001d401c00401400f80b110084d0080d04607610b42008903005881c0c101c08040924404d806e000b00404c01a1042c0b0407240c5207600300d0301c050604a03c04648154031b1b0005d004072107110307100b0041c4514000313803401102e4504a0f030400031960b034500b14031310200300c8d06c0c00381040600b50400c005010700490b0009615079642c0035542d04201c03843c607a11059880420090303040c03001c0c40c207001c1414249609540600a518 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 836251079 1250 836249829 836249861
    0x11120a03050105130c09090903020307060204080105060117010b0403140705041d070e0c0d02090109051e120a2d0b010b070b0612210904050112020a08120405040c1206060201 76
    0x4402013a0034042d180310050050006034840341c2040744501940280100038040d0064a1a19511391110803e0f031f4020741004880743e441e10280080d80d40d1104108014403030302c1e1001111541009071003d901d1180d840050050800c000c01c030140d00d0402e00280c401440002e00c00c0080c844078092403030514101e00900440e5000c0c00340001049020180428032a8982c8081c0925254a03055118001c0d04080035407410010784031030104554030b0340040f0586901c482c0020742060705446d01044002030748107240b5005034005581240000d102000c00c3c00000090321401114a1240c0e108800d141760f1080c0058113a003540000020302c038019900038010f13140181040e440a55802c801c1c000c6c0c6611194001704164808803250b895400c001c00b4004000120a0007289070100c010005400c0d1a000e03000403100c145001c20f00000c520f44000040000c129482c05001d1000154025031918016480303142d000701d0f100c40010702e2081c400d002103610141c0382c0c2000c108172900c0300c000900030b00c41c07035031010108 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 836252329 1250 836251079 836251099
    0x11151902210405010212070615090203090c2403340e0108090a0210090503160608130305032824050d0b15190305030c190203060711120a03050105 64
    0x158203001114241c80f01a001402c501c401d00c05103040310343c044c240545002c4e503140e940c02c9035004803401d50402008a418090380f02d080c100c19250a20300d0300b01155110b0300314508000000303080c450780d4000042c1d070208126280c3d42d801c441a64141845080400c0d904060704012806100c203614001e032040f035580d02e0081c1d4101d582d005641c4280240d8202d022503110390348540051805280c425441003007803501c0010039a0301d01c0440d00c2c08801644641103c100b1101c14403a03964030280080d072006e07900302518401162510050481c0c0f0024010300c1c0051800c00c584400320a840003680400d1000601c10040b501d0043c8040244184180b41c2ca00001200c000019491030000440b032a202e8000406a25544410707151161400b207e152180e04071030500e480ea404250801c0d2040c000f107010788040d5580b903801c00d002c3e40c180075420104014451580c5190009070b180000d13055403000550602e0f2201c0b43e00034a00350314001000152b40e200e40c0c0005809403120754107030409412103206868000032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 836253579 1250 836252329 836252383
    0x1030c0911040b07020d0201050c01140a1b050d0c0212070b0a050a050c0d05040516061d0301050c1c1d1605030a0b06330903060a0911151902 62
    0x1072840380c1c0c4118269000c1c207100101c05403904804992425105041540c0380c03c0e0340340d150a0950300340c1c04980455500c00b80421000349020b0083c001266240404800203c1e6041005041c1d13014019520790710503079680300f003224075008018035a80309020b6040710752141704500e011040880129a0224403500741740100300d1461103030054502440989202e6428030304104140381c01010000c0040d540c6102d414a40b030b469040d920b8007100903004942e51840302844004000113907001c03010105000360714110800c404400068291554040802c403e80d4400450102010103803907620213580f0752a890400d50124107000056002c0051301c800c0051801965078010145c03150340b007002c068044140d080001d501c1d441e241c0400341010b03201d8012200b03044001c202c0d503d0b915010112405000350005009061440d0410070b450f40300e6499601401075040c2c41d910380c204481c0304e10030140100c03a0703894030704aa190402c0540382045000c119280c00c217401020029070755021900e81c5008409001c98400c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 836254829 1250 836253579 836253611
    0x70e100e1006021e061816080f060f0610050711150a02121213150e0a0209010b090102100b0d051b1503010e06130f05040c0510020d171005060301030c09 67
    0x4c0a428100082c051956407803580301c8000315500210344041c05410900c0d103c9540748490000907204080050070034500601c40c1d2032030204050300d6440b405d10604100241a610f10700c050011240500e41b01d40c44050310319207100d5180c001540c0c190700c42380303000e000c071441000c04c4081c010707106040c0c0c212000170469200d0b1104038440c0c1000000754004034000941c901045440c8000886d01c2001d50940300c0404900b440d0441e02c070a4030190140c1c0068041606501d442c00c00326000d4290740c0700c1c1c6454004207000103560741405117030301400c00c0c2d202c60301d18040740c0d100b0902c0380326136400c007040e40c04030312090305280070056007181d100d07114591880406108507d01c0d4141c9040c1c80c0d00703c1c0b941c545500d4a1042015a00c54511062201900d80482911880749409014000e52103080500d1859061804200d01c0445581001d411980f000380620b4000d6480025100706004500410382d0544441c01d64010401007500202e030402c100100000401c152589102c0440d05440c10402200e000020800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 836256079 1250 836254829 836254873
    0x50718140105040308070c05032a0105030105030c0d17070305030103050709060b0d0b03010f06081c05160b181608010c020d08010504050a0603020405070e090606090102070e100e100602 81
    0x3600142040c0014400074294000501c0c69034085d803040c0d43d905580d0000a4549102860310700800740800d18001048001e40c1010140010709013403103801d540c100000310b542d030754002a501c0d00c180382c03841050040c400866080e000c42400e03c109141e4820305400c018241c1d5000f032104940b40d11070110000341c0146280305120507142c4c0c07a1025031822840d941d85030041d00107900080d5045d541e0b1004401256242d00c2842d005200f59400380a42000340c2d4141d07002e40411000d40000d00c40100000c42004d1010404070071001d80c00159a1010346a01c2c00340220040741400040f11480362400c04001481c00d02802c2085450342c1009000315000c41074100e0b15010407405880115000000501c400d1400760803090344a801509c00040e559580d4000074140c54007980d0b014045203210305004c4d00c038109410380a81c889003d983e0149000c62050000303640707048a22176801e41c034000c0000320b1205000c0b0925140101185441c0110505111041c43e820b044180309a00140c031411070303415009a4030074927031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 836257329 1250 836256079 836256119
    0x1302090907060816171003020111010902150a0903021207031b0608070f26090106050a080c09061503010305010b1201150e070509060c0601060e0910120213050718 71
    0x3143c56a210710300300122000041c1c0400d014000c41402c552905030148400b20300c100b05100540002c130b031841c00013402045e05444c3c40e0000b03905240104c4003603142e0100f065000140c0802096454403056000c070b943e5031003034100a60003074440c05c501001c1c0000140308004d0368015079803000315001569402886407014407403080070910110000e0502806442c01c4005801d9a0030001e01780503c44204110044846103941010021002803140b1440244620800361078103441d0690100e040524682e03035007240c50505803040000000040841e2161044041140c2c1c0c2518030a88a58581c40c0c454003801c03801c89268080c42e03c8100500042d0814016032407082406007041003031608213103085544d4a8018103420034072a00b0000711103145ca070720b001480d0070a61440500130381d5040640052100c0041c4031000d106940360810322604180c2030309140210340500c40b5400807101c80c1c0c4003051444c040300e80780302c00241c58101004110340d08a40f40c0390007840b0b001b8042400d11303181ca50001e149019502e807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 836258579 1250 836257329 836257337
    0x306070507030e10031d0d08100f0b030a020708070c080c060a080a052503052a16020a030206030106030207020108071b1e08031f092d090605130209090706 68
    0x700d00d0036007400071007000034032000d18006c04c045c200c1d02c0da0b000110710342c11070240140d4441612030718080d61020026030030180c84207000001610b441c000e6090400d603401140240742d00040468000d148950480e0402940105615102c1c1400c1c01e040190090504c1524246c1c001c4503040c3e0203618200041b038920399003070b0f12100c0d81502c03004180e00040c18001c008150054814190294580c03050b2038140c1260144c1d58080360500c6c003408502060301ea4445015108a00a16010b030440100410342303d4035980f9039400e0031004030500000b40081565800650817203c0000003250969140d00104000c41c000e0720f0741440b680f07074401e085425134040404860000089051200080c030b011070303001104168104484070846094803520000e0b80140d80140d01c4031400c0d401d20004210a80e941d1004142070300040111080320400d4090f0044054811487d01d0000390104003403143c145d000c104259002070341003025151101c0c00882840b90200b040e0301c25450030000610a8030005a00c409640180d95 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 836259829 1250 836258579 836258597
    0x19060b0906030114040f020f040305010b060c1c270509060a030c051203091801051c120c210e010e09040c0b0c0a0f08040512010b010903110402041a09030607050703 72
    0x400d009105481100c4907071003515203c84c0401c00c21b660010b800c0443c0994152595545140740a60031038281400c45030041d14180803084600b803012800d4003005c50709038181640c040080310700711005030822400384980c001200c1100036104a4a0008003580c10968100c40320b501c403081002121520362000508004215506011904004164080e94004402281d040042c4a80003074a000c07070039030300b0107200001d18004002526000c4071541c806021011106545802a1902c0c1e40032500e1b25001010700a08090020802007440c0c4d030205030700c00a01a40c0b5420645880c014188202ca111560000b40401120820b44c900086814040c0f03a2040104c21900d10781400308055820810f4075000e01c0c068640001c021a05194500202510500556a4850419081000203c141ca079042c01c1680740c42078041090340c025540700c1c20340340c21200200045000c400007070040d1040350005002410044010a026001c000103044440003c50586d1034607541c418045915014004020740010fa4050f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 836261079 1250 836259829 836259839
    0x3080a0e0a0c05061c1103040b0f040803060d0c051906030605011103190e180901050a0b01020a021203040801020a0e1503191e1803081005030a08030c0c0619060b09060301 75
    0x2802444c0661030044420550a940a6910200e80d55070300b05c41d0060000004008c2082413444485500c05060440c0c0491400c2545510717200b400014140c50184a00c048210b0902016640701c00003003200400b00c0340a0415401d105104040600c18840881d0a04a0214a80d0b0103030301134640b5144244020b40c180006c2201080080a024103e44184802c05000d0a400d8465110350202d1035010f1100c0b184078203100c0c003202c0c02c4600040010000c149490303095282aa8046202c1c4210382c0c04841300c4c0c00040040d240582588101e0744080003661000410122076a00001900303da00001c45c0c0850a45a250180d0145480120340b51080101800144845100700340c0c002c540551401031094500d8803589803000848421a030b80083c071842d503207500703000c065000b88051f50040442c5247d4855030320300342c042540c41d5080d280050882d4008000518619200000e40f10201c2c040802c48140c0d08100c4040c5080844e0240001d00e6903060280101c1c8240c059001c0700c0140d500581610b156a01c1c2c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 836262329 1250 836261079 836261089
    0x15271401050310050c09150726040603410115080f0a09020301020d0515040c020304180902030604080406020d0314010510112b020604050606101103040303080a0e0a0c05 74
    0x103100d0302c00c05000740002071947d1200308021000300c20800ca8641c0e10300311824003001c80780c50590301c03401c071062800090f041c410a2000340ca0444541d41004a03044c0c0300c06401c60450344020984464441080348070801d0305d03190250300150303441d005130101080e03600c0715240c032100100d41c8080b00110301c500000c2980c40076182d44843e4440e11500c400165140982c0c0003c0c00da038000c103100c6400c645c0f10824412030031040d6903038411001c2c040381d00300014040400069200c0c021841001d20b0804580c402c5207a06445e9004101017503401000c0d02c9440c58140f4003003400d508103000d070380d0041c0b284002c1c0c001d1840c040d00c2880c002d4003820a10a10603840d110800c18030804000c5c2c01c1003000868402c08007201d80130400051900414603d40801c0040c002d00c000c00346801400c0380c02158050814070011610101d140d5400100980d0b0101c400c00e0721010648540081755469100c920001600100341030748200d0b41c41c02030503800018001030390110071540da00d40380120080c02c4503541000130007061a003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 836263579 1250 836262329 836262331
    0x81608040804030b0412090b0c1c1103040b04090e03031b1e1201060e06090a170a02060304050123010308090d03020f010204061d010c0b0a1527140105031005 69
    0x440d9040354034243c1c4a90301c8800c0e911041e502140c00702c02d0b861071050019080b1010801602404600030b04260841e5002039807110301024203c44000e0841d03101c24518130901407000d01031910812251f80b207542d5080100031360b000b031048048042c90b100c240381e402031300070040381e00410741c4441d00c20480481c102500f42a5001454007441025080d034001044040c1c2806070262003c5502514000c3d80341a401804010384c038403003d8400c410800030040d19036940e05140065901000009a40502d00d00b003c0b8640000000040d41c001c2010042004002054100c28400e0b0359254441640c00e41e09100041089002e00005100007800e00044055003000a080c1e0074460092049542e0048044070305400c9a12070341201000405019080c2c0080c0e00d05094a03000f02e80030329041600034030380c2d140c10760321074800f5004142c00c81d101c80c282c4011601d28944040548410864015076070320002030240116044110070030420704000480c0041c1021101c518100c4002030701074030b2a40001c008480c01440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 836264829 1250 836263579 836263583
    0xb030f0f07111e210f0f0d06120302070e012718200f01120f06170a03170f04030f050c060f150117071214070207030c0f1805040f15021908160804 64
    0x1010b07c0326140754182401141c000b440e403403a100d480714080d810024201051500030310201c030014401000300d202d103401040303141e031001034007503100000e00d2507040c0280c020b51841cae0403268914440d03241807006a8540b641d80244000c402d00b2a50b0508042c402c0191a01c201035001c20f1444444404140a60700815206280d141c0c0000c2d41d1525540f0351180301502c1200502954010142241003640011880c40141e01054140c0114034081ca4010b00404008000404004503c10b04010142c000c0040e40d110040c0d650950f2403d190404d002d1607080011039149040705001800c050055000303c400007a1580344060308001c83c1e079154425513000701c013044114042c42d074614800c80c00d00e0960112a00600442d0b016114075461414110b46c1495240c00070419440035200030030202060342c2c21081d400554040c04a4103070794034140340e0b21001c00380f000505600c0b01c05151500201c01380c1c0c000d0910f100c240706082c0000da501c44080b103044c1000c66001758a9404204400c0a0500800380954098 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 836266079 1250 836264829 836264857
    0xf14060705060103120f020c0a030f0c0308270d0201020a020103050606120406151707091d0f01091203060b07060207050c030a0b07090b030f0f07111e210f 68
    0x11241d0362020315001c001d920a48512a8000900203980d070b1043e6010091881c5100401030310081c8000141242c283c2e11000740b48807041061701c820041400d00303c00045400c58030541c0c44980311102c040070351000b9980c098880c1d2082010607a145420601c3c0c0b0381d0f594040e402000c04144550054000700809401168010400e00c04e0003180404100040d1003248106000301d44016456000945a00f06800280e04c6080e04080c04002207000108030084805110001c106400c1c2980341000104e11081d40040034000c8090313000000b42d054208007003c2d8032911502090301500d0000324200d41680c0682150980b081107410f0200d1400d40152001c64000c0c01959186043d41c000a851300140c00000c6944004503410000b60b681c10a843d080104050b00c00c1500c3e40c90710031000d1402c2d49000740907010b42c0d2001c40c08203000a210300325420300c0c500f9110446040b9218500807000203030040008424510075408004103082e040c940365800c0032006000340b03080000d01143d40405400c0504514010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 836267329 1250 836266079 836266087
    0x3110909010b130b0411090d15180b06100201020309071e0504060e0414060103020607080a1707020102070605160e220204171b010f0c0311070e0105190f1406 69
    0x980d6a49100403030f48020701d00000b9186a070006100c165041e07070b0342041350301d2814401e9011030388036694251911a8042c008040b070740100c4a02c48000c090a421508078000700e90130400800036919034003406030008a40c01c02440c8600c0740102d00389d00c02203501c4031141d000b114040101c6681101e07861004041d2181c2c030303149207458801140c111038680d806103402001002c1071005100d0543d9454004022410141000758110740100f4020300c906000181110070003e1304d0614180704410248542e000c60a01001e94104080000e0103034005410903220b0301c1c030385004129075004440440310b5039a559180c038541200110100301d8017200f01d51399640c0d21013600f151103144803420320042001d041480810403542c481300e69401c2c5024038000b00e081084c0340e0407412090300da070800c282540f540c007a441e290841c003425140031a0000140c010001c2c4034400c50102280c40c2c0c2c2c0850550307044c1c55081d14203003481c014030040070b840402c1c28881c100b01d602442405210342d082025500c2d00c1d20101404040c98 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 836268579 1250 836267329 836267351
    0x50a0e07060c0512030903031e060a0320030d0e0f01090806060907050412080a030501081b041a030a05070302010e030d0906030f060305030a08090105060402090315040f080705070501090b03010311090901 89
    0x86035201b210250303066000081049404402c00d003240e00c0d40c900b1070b41940c0840c5420004604040c03058000034140100640300a0f6017045540c400d1700240790040d05441c9c4295140d01c1c01f5007110405104c840c8030342c0d80140c02c050315520500c441421101c03000700070002e030b896017014480c1c1a20041c140350b00300a4100b0012440d20b01400e248040680303da444140d46910b041c800408480c4103070810465604619035000601080e1802d0b00d0341ca80c0c0443c2c0c0020209803401081980380354102d50240c00d0300484000c0401e200c000328080c0d08a034002e0f210109801101c804040c2c40c1d601003102c0d000414140c0740c5c1441407500c240d104144080130303d00c000500e65140d841d4903256400c440014070000d14580c080007040e880038002e0701d801030380a0b83d00354180f200d26800039031103110300b4480d4448000c25100003000e01406900c0683c8058210030700b41d6580055052a40d00c5105901440707020074043d007c0056212ba004040768101e0f50001d420551180d400d1003040380001d0041e0030f1014564039030b01d40c1c1030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 836269829 1250 836268579 836268613
    0x6050a0605120a0515011103040513090b16050a0e04110706091211030904020d09210e030a0b0703180501020a030209030c0d02092a030705030a050a0e07060c05 70
    0x240c14991500c584503840d40258002c070150051000040b182400e05110b03d41c4401d403d10803202c1c01c2403c101c0c0010260142c40c070710b1801b460b0301c01c550165403030a008822552035400352402038014015544c2c03942c1c4400c03c0340700310590500403600091003000701810751351140410483d01c0ca0003d1001c5000b124030303020440340342c0107140161081ca60300c0210504003c0e0b03281c045800e0340854106404010490b5001c00d86a004040702c40e4011a0000391401800d1915401a43c8803648000030356070120484014103074084000f80000b001c1100c00809050500d0001188185560f201c21040141c0d540e42c81d08034043c00c15800940c0b070410b19903404000041c804e0019225060166a00688611420041618040b1107980050140b4400a004805030f1078044905610450003044040401d41c1060380c140d0110f003603002d5501850380402841315807070f40318008601030780006a00744004e8944810007405ca80c001c07956a0010381c4031a00400c40d0340e0048000b1441b4500400a0f1082410480d081503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 836271079 1250 836269829 836269849
    0x28050a06020910020f030301060f050f03090c03070902120103060c030e1507031113091e020403060903121a1014030109090209071d0f0f040e060a1b050714010605 71
    0x652658000c91a4841070410f041e0940800c1c0e2184010044e031102c156007642c032403206000d20400c2015507003090b01264020702c201c0d0001448c01c0c484617582d00d811100300d61a130701003400c458802d014028000650000600a607100d414100c098050540d19680c0c0f50b81c003e00042c0400d80905846410340004124107010803070000e140b000c598429031401e40d01c020b04070380d000c2900c060300e0002440543d8046100c64000c0059400310100045c4003502000480b4039030f20600ca070408602e0000a0100400c1025080a5800c910903280c107141c05541c800c02c0c2060f1040c1c0350034440d40c00c4040100120b10f282006101c240d5600504001d42c104001440d211000d0748241c2210880a465001107001c605041000a6110100b2314001c3e0019030104600d075100308500701818811182101151043e54030014100b603041c000070301c1004007034000c4401340d80b00c0604440c004001072400840c3c600c43c1d00084502c1c2103214560355a28030302001507407a40c0c0c03c2856000c113240c01c1d44d0b0300c0801042d1a11000141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 836272329 1250 836271079 836271083
    0xe0406050a05090703050c0906041119020d080106021903030b0d060204051201230907050d200f28030b1021021e03010e031b071202010228050a 63
    0x2040518140c000c040c240da1024080000e280c0c41302c041040071a0010805040c40d14044482010746e80700d040c000b0b000b034400384080d0303500700d0070000348a4004001c80986565401c200d800752000e0103540700b41900c00f540300340300c1c101c00758010392041606685594401c02d147c034800e0900040800c43c00010400d4501d98290440d41103500090520540c60b26055024408124a000b8042c01c0c0e0342c541c0b2994104190004118002440c0001c50620f00060000c100a028054055825404103040c104c0300400c80045001d00c03090401d810042500348800d119207e201e01400c980c2c0007042800045114444c0030320540c1040c4011030003c000030f8014a20716005900455600c0e2045040100c040c071941c039502650031078130513580c0d911703030040c2c032049001b845403460510900d02a07144940424050130660f141e4620380d00001071200304c2c4203a421030298039400c2d04021103e100e42c031141284052a19070401902580c403e03490748120841d4601240ca556005021244240300d8582e2501d04e000085a41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 836273579 1250 836272329 836272331
    0x6010f11100216031707050910020a020d0f0209091615052503080f0411270f07021e030d0e071203030c0e031b090a0e0f030426030d020a090e0406 64
    0x2c1c405155000300042110240358854185a08000741c0117072480c401c0c4c0b0105802782c00c041d0700c3c0481150003030094002c03842c1c025040250841d440d21b40100d04d8006c18500b284100966000b00f40c80b01c1d4001101d0418114010259070301c54205500c40c00d140f81a00d0001d42088030821528040e501501c8003060600880c03500101d4802c1185400341c5606002441e018150580b8800c001c04078003030544020140505580f00031034051a12410307001c3e8407202034200e0f0303c0a0400140300300c0407440034400e8440c0c00d080d82664100350000c40812811103018512000d5507000380300700300010f03001e03900040b41400098102d8403c00d41c1e074a5a00c1800c0c3c0c40301400c3e008079070f8074004102041d0304107903042c004880450181c00701c190103086840c003c0f5811148907000b88035013800501d1801465024000041000e000c071503440041a004036070360380c080e00583d000e4102207005041e41a6000280001c43e01c2460050350421170b281012400941240a14004220102c900058050003c00981e4095400b03008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 836274829 1250 836273579 836273617
    0x16031b02061209070e04120e04020d02190806011403161710050a210b07200c0f0409050d080705040e0106110c0906010c060e0304240f020606010f111002 67
    0x7601d6810100141c0c00b50000405900401000516034580352a541c00e09061162300144c42002050082c004d0100c1101d2551001824400d040714a500301115a640307550794402c10750f58000112686080500d1b40e510266050010030028000070010001c8032040e032911420074160b512290403281002c7d180c10741446032411050140b800c0100249014041c5001d55524106031516080004480104042e141d10a00000b06134120b114001c20010301e030550491400110526500646810801c02e1441c45888840703074600b5982441e0081510032038101014104026218078159409000240294100030080102068810501304454060f009a07a10034169240c480d1142d032506040d17503449803042010b0010446103a900608600d40076030300100c081b504030303c003680503413450082c2c0c0c0141c990384415104406c441c20300c0b24030880351052103079a00e281054071200180d8030382c0025190280080c2d40c894040c00b0482c098000403480d51014405c94481400703407101201242c001c0001c42a00355080c032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 836276079 1250 836274829 836274841
    0xd050409061a030406050601020703021f022109012102210a05100909060f02181306030201120c02100603080408010e010212040201030b0a030b0c070c0b16031b020612 73
    0x4420780c40500081815226030340300200b0040680e00000304010001034441c00080c03056442440308c00020f641c0039120307120324400d10002400c6802404440401489844e110110032070100d40813026030501caa048528001d00c4400441e42c401007001c00100200704450171446500c454801403e0b200884020000d40681905103011307291009045444028200000c1c4101c68840e1000300e401c86003441d00008160040d071400c01c1c082c102008140420710300c081190a00c950f510082528400e07421510101d50000c213070508001c41e005400081c1c002200e034107075401021b0b82e5902051440d0400e0044a070b00b94036004030001a2205504116400200410204404442402090808142500251b05103010049048101c000c01800030b4105a01c83c00702c44140e80701d4007013060256401c50005a810300d081d04c200b800a60200804550f003200200c00000c03018131040c00d660b545c81d0540080116502306850841d00654094800b00b0b11000b651a01d0005079201001043c0d0006480c1c0c942201e85844 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 836277329 1250 836276079 836276081
    0x1b0f0515010e06041a0916020c03031c061217070f150b09060103140c0310030b07020c0f0a141504051206250c12180303020129010c0b0603010207050d050409 69
    0x803204001d184841810619081d91b030b248000742e80f20440d6401544003201c3d0700c4080307142180c14100c1680500001610b103070385071108032865444010f8860144003490740c8092031486a00c900c10082e0102e1a40d80c454000104000014080c0c0d0340500a042d8003580395443c1d40789440403011180d00d034590350780c0c0d82c5545800e2a420042c0e02c00c0d0242400c10040c000301031141d1180c0300040091140144c0013001032542c840c442915009160000c4a141c7c01c1e140146001c2d643d0344000740918807813403443c6850f803220f103000070b60f6005484201d11501c1118119a0a01080007030300701c4000c41c1c0d4003050001040c26110074468806c0401c8100003059a42064082848801c0400045000c62400c09681800480d0040c0c0d4011003164840c84040d04115820301c1110842e00c40754070340481030441031000083c103a05401844050480c100b1061204a843c030000c10801421122076010582041c130a03800b28906a200c9a4450b0001d4005450050309136100d508002100b030000010a2020400307000e6684a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 836278579 1250 836277329 836277341
    0x16080d09090509191406010f060219081b0a08030a020a0801050a0e18070f03030507060c0e1c06060b04120c211104150b04060f1b0f0515010e0604 64
    0x200d07081004181040300b0020f450b4413820750b00c452880f1a440313440003082070b01e0304100d03000c6a0b10b101740c036015611251200c4901e110b5103c3d10005220706207080111204c002d0000441c0743e44020b920749803402403198600d0000603c210903490b070040c02c0901c0c010030349078130096120318818000180d4031150300d0000f03003c44c0010380103140210704582c410f11180c3c0c9900d6509030000310240420130364010424460b864407009810440844000101c00010540c0000203481941d129220501040040d9001115220200c80c00309074019042e54280c11002c0700144150490790041d80081401e6807102101e05075a4081e600c140c1f0740002c059034440c00d01013007110306800740030080c81c81110302c900502024400d070f040072300140c0340d8a6185800000d6503a181e204146811420300d40302c0c00241d0390000810149c01910555003c22540303800150844d104864040032000d4084807101c2000c856114080d12031405507049920340709404280e4181c4070b017041a28000d10a600d003410302460188144001e840c0c0e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 836279829 1250 836278579 836278589
    0x60c07080c10031406040504020d060c09032003060609060a0e011502010c050c0a2d0302010f0c03061206020a050903030706020901021005041e05210702040509072616080d09 76
    0x80340c44030140000e131420b025280c101404940101d10b94480c1c0c000039080042c41d5000030400c5241401805080d500700d191641100d02a0420b0b84d004030f11140070301622510b15500503410b8001c6000100c0d6172401009041d00880040c000f907031340985941c2c020040c403100b80c00041c00c01c411605102826a4240103041072074800d46003107414143c030446069034130252803800074808041ca0280e040001003c3c8035090401c481041c03154400807143c28040d000740700110040443c2401e000b4240c80e140d0180c01420200c4000e07000c180c00725181078417054002e400c100241000c00900b00140c40940e50108042c010150084000680d03400c48003002a14008181a50070185402c0404100c00f00f00100f01114a06620a000c00140d10940c0707015400c10061400c000140c103120307a1622141d41601000d01b103058800c0d5420400e40c0c0b55184600c0e0348007000d2117405228090085c4011141104400d40c0000044180407500d510790449424151126590021045644030040d00c0ca003850f4400c8054000300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 836281079 1250 836279829 836279831
    0x20c130603140f07090905010f05070c0b060907020a020d082101090e120301050607060b150403020307081209010f0e0a06080f07030504080904091a041208010b19030b060c07080c1003 80
    0x8001c0c00c880e4840c0700310b1040317000b4141c2d00c0310390405000302034001d0884e100c0030440c100131a242003000540b00c0181c07600240c070b01e18203010006080d810525442405680c3e1500207212001980d401c0020a01032240211035081045c00100944001c0425844800c414250350341d40b02d6041180640444484071a85411684401b52141b035220885003140d0540d10306581c40e0f5541d07019810080f0281c0404179032070b60044c001011040b0300244041c081c0003a40d200b181590344940e511100903941d840032028240c0c1c0502c040100b1011580500901e03000f04005040c002a40c0f0106030001e40200c07042c1c3d00004c0843d4980e8100503502d107141600542c0241182400c000c142000e44844001d800f44109240c0169a00c20380e85080c0640b0140c03e034407104112148560030724040c42c1452125803900e02103004101c015001064503000b680541d0104400e0850410001c400700804a001c0d08401049a0b00190100000070554100b800391001600304403008100c0315a40703509029544492a06400400d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 836282329 1250 836281079 836281093
    0x30402090408030a14010902090a0506040e01210b0901020703172a0405040509011409060103080f0f090405090a0302060612031206190f030606090b061207020c13060314 74
    0x50351031840c1580c10a0b04000050340b2651005415002000c0d55203480c460502ca0320000260a40250024840d1030025581d1491055031042404024011030003011055000c00b40113000c150038803600d441c13500c5020301e400220340200d0380f2001040042510310340406c0e50005010024560800c01c140322000242000c0c0681e450840703910b59240704004100c0c0c850840c4105140b2200841d4020b80d00134050042081107542414108a40202130005280c0070085500002a8004401180450490b40c2001250785000e0f420110003038283d111100000b08644207200041d01d0780c544d84240c1d4803c03840309004050940030b5060107403608000901d15031244042e8030380403014803000701c1170302c000200480402e9499110135000030781d105011030f08103401d80b40c058800113094802400c00c104503070040400300041d07521150740300d081c1c030b00a05140da00041c042081c0f51070f26188105040d4048020320581b54003c0045000a00403a1808802403c40b9102c150900901414801d85031510604400504403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 836283579 1250 836282329 836282333
    0xb04050603040b0606191e021f0207050a0807201f0c1e0308010f060201050618070c02060408030c1e072c0103030f1d06030c0d0605121f020304 63
    0xc01d110090000f4a400d040300040754641e2a03450603502c00c40300b89900c0080d858081c141c028261041407690400c1c0c3c030429442c62009074000304401c059450b0081c034150a0300f01804080b40a94032250003114184507213071010020500c1000540b00f064882c00314410403107241c030b143c82e481010840b0198407031f0034400100180400c2c14440e400000c03a150030003600350354141c1404c1c9412000800e1a40c00031100f0140d031400c140d4401c0c982c50607070b80c45440c580441034540c0f07422401c9410840e41c030b6821400a84020044155561408c0c3e80008613240800c0141c00545c0410740c9500a82c0c0300341e1441e0700c01304140c03003884024820808004491500e100c2100d803510146a17555040344a4074000c0d0030704a082d414413041409a01e850700a0700e41100b040d550f928500204400710441c410b00004404a5103c50025094120740c0c040b80320081025041d500c4070201d4075060307445000c802d02d50560342c803c00101511040448081180c220002c0c0c1030440c03c0c44545400101140280e1803018410010400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 836284829 1250 836283579 836283589
    0x20a12121a0f01030e01090c0b03072c01110f07061112090f04020901110312010e090d08010314100f020a030b120307061a091311100503010915030b16090b0405 70
    0x1030720302c10900e070100b81c20854108450041c402c8801c0988104620b140200714098100d00550160b2115603030700b501e40c111300014825911070484141d00210151101510640c0b0801e104181000070034283d560100455800902d0504a86d0184000c00d4040307103002042c000a01c00080b8800c500c2d00c01034035000428000805010100e54168400d650206080b09164070401d507541952102c030303007100d507209040000e00850b07001c00d00c940b041000c80e0342c00080502d000440e1107100426151641c803c280d0131980c0d5050200084102600c2c9071240c521900c116a14502900484002c110300041c0e0f103400342c0c1c00040607502045a00703402050700011a4800b03060001c110f03000c9039001800003403a0605900703048414a214582294800305240c140a440201e4036441e80703015226000012154159100344004941c0003041c0c50702045091004000d00c3c51660451540c03c01100c40e402c0081da242e03610b014036610f09460005042e007000c00241505078210643d02c014000c41081c0d5420580b5104c000340c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 836286079 1250 836284829 836284849
    0x509092b1e0507051509070518060907140d09110a030503071407030206190206010503010c050909040f060207080406094a0a0c080a061a0a020a12121a 66
    0x2004191045064070319280c807400a88000e0355100e004e44084008401950084403025078074820203000d44240040e5034505240341080c0080705e501c0c0d9011680d949c0c0300b0404c0d5000003e02c1003040c0090815210f0030704480e039004050030880400b00080c8880e660078a480f065040442c0c0a0140d10321400c248042000001500d42990b4400382c90005c0c054041c03030b0341e8280440c81d80004c0d000310340440c2c000d41c2d08110000703824250400c0c4d401c13114203a030f03588105130981e04501c00000205108100140a034140000c200c2d52080c0220f00646855205d9038400b000c9030b201a40030748100c540030406104240e1b10080481c01028040d00c030ba84034209820054540c0141c0b100340d6001c1d1280981c4050040c4c0e0307845000c03001c0c0c02c03150030843c2085c5450790b5513801400504003244006070f120400144006454440c0703000b81d03080003401c40320305a901c2c80302e10b455510031030601d42035100d04614500007500c080784981c0360080710303540d40c800401035800c004260f0b888511043d010b00c400403103e070600e031224100300c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 836287329 1250 836286079 836286107
    0x6180b04061a0c070b1308010506030a030e100c120804020a0e010806010905070c060f150f080d03090203032206140304030806061309110307080f04050604020402070c0509092b 77
    0x1169988068950080ca4620181d002d1a00d030030022503201021b11030200b20408540c0400f001740200e40d81d071020151100c1c1d100c40001e0219440c6e10b07000c2018201111000c142d68803d0401034800380d85500d0303035801400307490000b0000400143c10042107023001c000701ca008156074110603010b135041104690301c410050203050020340e03440b40050344851148100001194008030104403101458181d000500042c012110358110540400500d1542000a010071119464082c010907400c0010880103000d140d041070341e06d88001d0100e1031030740013000c50100704022100e68080900749040c20141101290409580354803500b0710401020a400410150b842141102d92a41c0c0d800140c0c03445020320501d0304425800c900d0b00d844106502c4442000b103015034001e8a81180507510010442e0a10400311001801a0070080100e0b005081070b801400d50507100c0e072680005c554861020075501601203415590950140c1c440340070a4020076422008010b00900500c03048840c41e001800801200900d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 836288579 1250 836287329 836287379
    0x3030a051c180609050c010c02031209060f030109090308060d2a0f060215011415090103110304260a1704052107052e18050106180b0406 60
    0x900210041944011107070040200210480c01c82c5081120003004080001c84452082090f0301810750f000f00115542154002d004020059000e96030400079000820740c0da400c11803e0084940c1d4111080245002c0c01d00e0220004140f4458140140407100107403600380035203111203440001c9094296101e08003d40102c0e0b02400046806d000f1201110543c03288242c0a80c3c500d0101e0781c00d03800301e210320f4120820212250b00d640c944039410012441e02000d1603024160464200703540b4022405020788100504001440070110203c020069100b250101d804105c4081c201d00000c2c00b640d288480d41208034107050400c010014090094a03000803240030064210f0000b80400c00b0400100f07000c01030103007900c0c02016044080d29030350340040004580c20f004801d50052034400104044050710301c400142002d90100480c0080240001c0c1190001003107034440f0600800d209004600040184500d01e2105007180203070342c0202d60400314807600c81c1e400d06104000c00c14a240c0c0c1c2c05051669518 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 836289829 1250 836288579 836288617
    0x9090f16030317130803090a03090f06020303073221160e03010b04090b0105150a050a0c050c03070b030a1812030c201f141504060906030c0306060503030a05 69
    0x2a107014100813004006010741c90010410000d00008541480c01c94400e8a41c0642c0c9610b0310354a8110301c07001d00a034001030f8030a00004103201d204901d503800b840c20051a00800c280d41d06014462101864070311080304200141062a0304005072407071600781d6031485081d0403803c0411021000d901a90301107000c00041840e114042d903400c0d4000802c809000348100402c03200d03450000d840080901c180c078455003501d2024540152407204445c00c101d020360f00d0604c0c10151210070340d07550403205d03010b450511030320407000555181005644058401c4030703841502c0b8901820541c0039106007900104c0c50280405419000034962110b0a00c8103266090103d80c81d40800022150024800051105028840f1040e0008500440d12241c0c1031506603600d04000d00380d04200080d501e120701010030b10f00399007000960f005051608218102030050012409a6036620320341e09a440d00e0304281c5103006421002c1041142c6071085900424081e806981450800e44014143d40a04401c041303080c07003446 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 836291079 1250 836289829 836289841
    0x10c1706031006030b041127041a0a0608120702010801091d2406101b030909020c0303190b010804080f040504021c0e010b03031c0b09090f16030317 65
    0x8420b42c00802075002c410010240d6a0510301c08418003501c00751981d00326610740035403605007180313403128000d0349101515261501e01c5440b041008024000d5416421039188501200103680020380141549000481c04505080e0080d0800040c40304003561840308101800c0140d030804149070440310007200014002c0e61b010900000c0c08409007100d02c2600420b503041c6105c1642441c1c1c7c601c80b03181c00b85142059030b503000c20f00400c0d0801800310404070700c0c10068400c0100a1920250103a4406e107445000b0641d60102034060b6000040040718980001c020864404441c080c002d00104003140b00b4000315099000203003541501400140030003c0008401102ca001300d001c8400800c00a0011945c40c201385a5941c00000100d1a9401050403c07802c1241d011050103203244c0c0d01c1c40100658640b940b411100318051a0303450310000d021b5112182c01c0d165945000006105501520241085040090806080c10503d50360701550000d80034040c000f1a5020705410180a1864011045910b4070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 836292329 1250 836291079 836291083
    0x4060b03030316211b0e240c010b0613082b081b16020f121e07050d030206060a061b08070201021009110f0607020f101803030201051602010c170603 65
    0x84c03030400280c0e904250b24500c0c11482240e400c40c07402d1003550fa20203038888080802c60003000080c9448007030442e0809034003600c7c1040c4010070402c41140000920321034514041913660b0000100d517902c2109212003004003810510590200545072000d6804601c0c1410764000225a950320000400540b0b4000070b0410b40f80c1a2814020000116000d0712040308180080180d01d46c018224004d08000d290006241840748102c441e024841000c0d1501182c200500202401c00840d03d940c5849074810014075030f141d922440102900a5018049503e410000d000c089021031f48042c041280c02c2144490300c0308800903c50071660321201c0c0e160b6401d01c9000407440c100007260740111f05898046070400300f1403400c00d0603104440955041c0103100300e01c0c0c10440503000c2c0c404040c0d08a4441c031911031252601c0d880802220085003014588011400102007082d591608101e001d41e644000f0f00c2402c0480c0003484948841c284020b1182c540c80e000d000b041c008041c011882189100340c00b1504d203a0301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 836293579 1250 836292329 836292377
    0x601050a1e121502042603070c05040506220204090e030408120a031d070f080f0309090c070804090903090f083a0306180203010303080f06040f1404060b03030316 71
    0x9405544494692a990180240600c4600d403030f0607400c80206c101e0319021040d81c40503508203030b031440503d14140612010303003002003e85920408a5660b0340041d0504200045c07003075040c40c40181c80d242070405880407240321880c01d0829038010311003042201c400040d2070700241050f00c0c0340d17901e40719244004d5000e0300d110b01480c440b0310141044086869000601e5404941e401803038511103550b103e018540302c01c0d0350040051150000c201c9072507076052403405030b600600340321142c80c40c1642544a50350340d50029003100b04040d40381d5003a001859844880900545150038111014070b10344801d00b940d800b404000b40844417601c00414820b041580c00d00000000c12040c040b000c06502c001c01070041c0607901520201c45d00c00101d01920554074825281640da041c0c541b0f00090703c555902041401c4000d04c01c07170380039845030400c00001030305026108425003111045c6030b19050a18111040d02c1d103403442107009070b009000f004403401715485828030303c0d811414000d8a0034140001c40e580206 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 836294829 1250 836293579 836293613
    0x406020c12071b05150a050f04151d041b120f0e0d1202040506070201180803040b18030a03140a17010e1e040f0201030e100e0601050a1e12 61
    0xd01082c918140602030000030074071a40b81c54000400da403940100a082481455140c45080b02480600c405501030340050040c910900141030800365035201d290300505e0180201c078006a20300c003080320080001d0341403681403942207409100c0c9480b255180d50700050101d83c0a42000f07180c100f03041c8140266400107003070b01c6041d10184400d21884801c0b55803544110a0000040d541c0c00840d0182c0c4180e02c00e44044c0c2d0801000d01d40303800d55603001103d41d0f241c1054080c08004442e0800606141d04000520045c0350700b2150740d0b101c1704240364050459240402d100e0080c0c000a031500c0000ba80a01c004490401036440a6211490120f0854030b0000344070b903001d1141100e5001081d0300b0300400d10144284a410020b6000c00c942217607006100500756401001195003050f9000150b0198011440c4811020700710b50080d440072600c0015652055848070701508503100512150410f900443e0241c8040019248914070340c03d10b14040207018070070194008107115100702080f54240640c3c0c0901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 836296079 1250 836294829 836294863
    0x150f0f040e0721210509040c2007150c0305040b40030b1018050a0b150904021e070f050c041104151103070606080601270b0103020c0102071103100506090406020c 71
    0x71444c080280940000e03025610702079089e0000b448000030000b40c41029901c50840054240c0d070300b08800c0d034001100c04001c0303082c4481030101250200d02d01e8080c20150540444030340410750449900b0054881100c46420040d101c0040c5046c13142c02041c03403404407644402503451a50b103d243c0c400000007030390403101c01480b0004c1c00301c2000e02c041c1c000034001c032845a401c00400300360404000d191110044c061810030814061b1011500d07095001c1c1002d11241d25207804126075800c00c181481d802488121001400003c100f0240b0100700403460b42880180c2c0c080214400c00c40b19401030340610310072415091600d05210700114414203a01c00b80c1a051012a901c403010307807a00d60090706650084c440e0354480c2400000c1c0c50228600d42c10000c405490701c0703044807841d002200c40a80419160b003414183c0030400040c42c00b00074030007005514000c0d0b15183d001048141010308054441396003204090800d810700000da81c1d0300d030910b43c20030b60104005964605101300c80d07080041461201101c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 836297329 1250 836296079 836296091
    0x210702101a0a1212050a031d0303070212040f030215070203060708160806060306010f0c0b130302010609022a07030605041a0609150f0f040e072121050904 68
    0x35411141c50408500c5003164004042502c5200d10000520102400361001e20741030440c0c1c00342e40c02174004200000d01460017103010512109043c0c40408802074000640c6d10020404c031019034103003e041d00210818011514041c40c03d00f412031107984500003c6e2041130803001c0784105055410403100c2607075000d4259000d80c5040840680111800c81c2e402c59201012032001c43c1440c46600d0315071081c00f00500305411f5484500c0116800e4140030304800070700690359001804034891a0742a031062040021110303240c40d031403030001d0039207109a11041c00c15005103c090402d40c0700c1e20107a500d21250818220b090021404841d10b840c0c0198000b0f0442841c0209102c14400b210108030905c42185030100e01c0358840200f4003899040844520000c8904c0c4003924480c2e2034691500980d01000030050194501d84000150880701d0742e08074804140d1044c8400c01030321058070302800344c0003c1c0d005114001e600c0c85d183c00526001100080080c1c4440b001e0b190607007400341c019515500c1010b0402c0100d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 836298579 1250 836297329 836297351
    0x3010510080619140702010203100902121b0c1c0201060f0b04060c050316050c0405090a0c051507061404020321030109020307050705011a130b06120901020708210a0221070210 77
    0xd500c01e07191203500e240006c00204bc05184c40c003c64050b10403080c900200c5940310078102c3d240c02040300d00c030041c90b402040260282e80d410810440003141070000002403c0c440e06c8040d0864a076035010888141a602c0108440203901007514104c1d8031301c2c1480000c0e282240342aa085100e1154500e6039000c98030081d0061040006600031106c2056038208256294010210759403440e610000b0001c4002c954244001d0601009039001607915101d4035042800c1a070314001964120769120390402c1c040d10400c002e5240810074498095a0b09980500e102c100303c03840c1c05035110501a420916400101080c000d0303215000300c40580350000020000c0c080000d03d01c1140b40d611003007151044034904c24010350300c0000e1188007909080241400d00d003c10342c10b0140c080110081c1102515542032101c240031840c5000180b0380303100d083d8403801c44100c41503010f400380e000180c02c03074100300c3c4181b15070003680200c0f4a00001191030003c1e00d4520b9510070304200d2809003100c04d0307142d45506191049003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 836299829 1250 836298579 836298581
    0x15090c0e070804121e230f07050c011b0803090a0f05030d050702033612061605030f04140a200405090d0527040603030c020301051008061914070201 65
    0x7000740c0c440c10744d5900000d019881101d40550998916540c10511181042154002c04842c03064007000205c3c0c005410240d054040e4a0b0030a5854030300002001500808019003800f50381410203017401c0c0419440800352540d140d408007120f000301019800000b1030003492040142c43ca4480d170144100b45040d4007454659242e411241e8280b004c9070800021a0000b4000b0003500c6500c186038813051400c0c0d982c0c1481d011300c228564144c2249d01004d079518106a203580c0c03484074001c540d003402403d103428200003400000503500c2d25801005010310a000f942e04414542c2c640150708100c0c110840790014140b94101100210010708000085003c0380020b00c445140184004044a08001e25502c030f0802d903031107902c940310303000010304e040081900300c0680050007601c0d085100034801a900024011804403a419001030700811000700306442185801d0241e1540820031901c2a4512442c3c44003603a65400d018003c00b4081000354001c8010f03102943c01504081d0700625140e82e141441e50000e8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 836301079 1250 836299829 836299831
    0xa030e03160806061509060a02031c0b09040b06041b11010c02030f19090308040b190c050d0f03020c1504260f0d02090d0510060f0315090c0e0708 64
    0x18000e010307244040000d001c045184100b110700c40800b030f2289a81e428104400042045000c02107081c040c828404140c440788041e04034418160019550340c0d0900340c01c40c1d600b040008510b02244d041640074a16a1540c400e0503820a6002208092603161040000d01402e2140141c0c000e42000ca68a451030541c030122038000b24521078000c100c5d80c404490101c0c0ca034800d503c0e4507840504200403041c0d41c404661120100340b1010b00d002441d20f5200d80d01c184196210b41d1004102490200d07007014046118044403248501c0780c10048060082a40c40c076441d800070146182c1801b070038074092840c060090f01116038a442040607a00c90380c6031250541a640000c1d03c0944074003a19800b40d414889001c0c6d888403a88290b898080c3c00d29821003201d03c01640604481c454458082c42600031035110003030030440452041c80a05076503482c8002850840760075a11202c001c3d0706018040010641e8032407000780070290804007180c0031a16041100104240354440340e00401c143c410000e403c0c4c0c0c0b05c151a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 836302329 1250 836301079 836301107
    0xc0a03031d0c0f060702030a02090406021c2d0216081809070512060f09010806160509010e0f1c030908100b0a1403120f09011b0b011809050a03 63
    0x50109001d01800301d903200304007914603400043c21080240b55140607005000141d100404a071114a030035800305000b102c0a81d0210345440c1c000c203400032807154401c40070064402c4150200002040e2100340d0710250380140015801041c2110240b601c0001354040346c0e81c1c00420200740707040603034911b4614101d030703c500d40c0c401d40d0708454042e1100c1d81c42c3c20107103180510b00c25550075061032504690501d0300c180244c801e0394820f0000c100c1d800c0035251129558001c01da0f50003e0310152808c2c080a10a9599007554401001401c1140c41090313138120300c1c00c0102c16000d031156000000110b012811100032210b912000d05241c0e0405820544e0046e01001902e103181e00396643c501810000b40c0685d6000401035600c51030740c1009100c42800103d115440c5100101221aa000c01d8070086900347c5c8281016120fa48001482ca040e07175811114030300040348050782c44840702199440306020040107000d1f00142d05501c46130040e003d00e841d0070401c00250020282c1e40c2460184c0340203001e01c41c0102d01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 836303579 1250 836302329 836302361
    0x170c0705010f050c0a091202090103152a030c0e0a272d090f1415040c050102070e0f0f06150301060c0204060503010902012f06010e0402040e06090c04020904020c0a0303 74
    0x10108801200b52010b078201680940b02703030806c0e42181c2d6a071818200c0c0e601c3c1c0c140125034030700c1010203c01c6603145003d00800780c00c0b050a54032070602c0c801016292010940d03024010700d41170203401d5849a200c45412180300311275541c0c0d13414000d00044401d0031150340803c1058141201c0e803403c40c0e01100c080058007806c419400252122580b10010341d0300c0c146021b005841c0c001ea00c000070880d640e2030388809140b03030b00540f0307411410034540c1503800c03006560a54100c040042c0912880d40c0401c10310000e4001c60300004501e1070403284262166000a0001c699514101c02145250310b070708150000010620744000c0e220341c1c55180003000d503d09414168840c0742020780c00607190078180300e000f80030b54048e510003c0707a91070000100f00301c10050080680e01c1c440c20390b400000880074041d450180185440c000d540c2d040c180100010380e00c0c0c00405c822190800014004c01941c00200d81c0d0301c007141a80d000d0b0f250241e01c40054020b00440b0800c1c2c58031702030980038500709941980802d0780c420002130 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 836304829 1250 836303579 836303597
    0x30108030a021c0f03090204090b040605271b0f030d0e090a02040302032e2f030708011e0e071824110304120b070f170c0705010f050c0a 60
    0x92510b441c5140f12864401090004c005030030050310a8201d442c501d4000341c000b06208409179945018504112800d0301d080b9916003d006145c2d2030300c1800034407a0302840b80900c2c6002d4441c101c0c1e0310303082c4d005000c407038200780355088030720544440d002c50301404002400e440c240f10001501a0512000c0700829100d0806203001644240680c401e40e0140c07500500201881e00d64605552941305010b81c54040e034074180c0b0181700710440c1901800c2d52082d0f00b80d42058500c09520140301501c4d400f405404400107040c4104150380340e10800450441d820310208113150601141d004500d0525030b0086856402c007907080040d036540007540c1101000e000035061045907910f010680d50900e000080071100316903600020081d40c465805007107401000e1040c0c030b240a41d1351403203488081c00800d0031150029424100100150001c024400114084c2444080306640880780124cc1c58024403910701d1000c08901d0b181404025408940e10722000c0404105a003000c008482c0b0941011041c1000201a40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 836306079 1250 836304829 836304853
    0x2150f040f080a0c1401030b030f0d09120b06060a050f0a0f080f04030e01050711030703030c02120a0803070c0f05070e0a0c020f03041205150c1206040216060f090503030108030a02 79
    0x103030f00e42c0215000309951161506168a00e0390350545400964101901c85200302400c0d64180006240107035080c00400b110031141c08040c0c54030940d80c0c80302e1079000009981d10085061415550b52050003100c15030b540b614014400e46031401500300607401c400c40801c0440000340c026405007500d10058440881503680d03941e0302805041c085500030300254101c0b03c4071403c0d50040014141040c4500000300500e64810082440c02030941d0060307002540288a550650400192140f81c46108074094924810b194844001c07910020701102c04000408280c8000c0c8080d00303500300801680030050f036410640e550401c0750001410b861140700c2d80c0c5414030b540140f50000400b02501c0d5004009103040500e800380726041681c08100c1600e540c00781084102d06054080d9000e481040d440d0707400d40d210307401c100840411581c014200c50040e48100b0000d240b14495444a90880381d0102020514075500c5601c01d0261907031140003029131002000106103040c001c00504032003104d5a0845110100132 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 836307329 1250 836306079 836306083
    0x10302120109031d0604050d1b05010c03020601051512070c050c0a0f15020f060a0f0f270204020d1a09061008010312051201091401080102210402150f040f08 69
    0xc02c4004000c102c0d4198407441c00003800b00500c034000c00003044103080c41d64460124074816003480c022642000c40300c20b000640d211015035440900000e00c0c081d101c11030320742d41c044e59908060040038070402d20600064501003030344003100c00720a4000c1040c0c46034100340e50003401c1001d04030400c95040c0980c3d030485c40329040524454044810b0400c065242c24036103100501b44c807410050f0601140503141414000c03c43c02c02c243ca000c0e840251001072582da07018000400c03503020805140c0c940d03040c014508485105490b20b403250311f08803ca0550600721900c0010028480d0f000e424030707101d081c420070070014401c00007100000c9200307076500e1115945290030020f1038402301110b01c000c10945801480459400341e0300401548045c28103a18004d110780c190a5a040309910081d8030544583c8100c0300c0c1d02450101d01d005000c000001d504020f8001c0c40e20b020140a030300c61240c100880300010b030565070f40c1c2c10810b80080064a88998804241201901350752103030141610310f0010000028840c000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 836308579 1250 836307329 836307341
    0x90b180304050f0402160506040b0901061401050901030b0a230f01200703051c030e06150f03010f0212180d12020702180c0a030c080610180e0c030103021201 69
    0x210014519090a020030844107401c0501c0c02c54009609100346501518031041186049020b60010004c514003031608210b00c4c0401044100aa418074100700802841c583e44001c0c00c3e0001d0030b1454032848c1540c0124010400b00fa400c42d0302c46030103a4000340c04800d120071110041a070458401340101d406060050700c4a034250003500240141c02520381758003100024003060089807050302d82450385d07074545514000c0c0643d140300003200e42d98160503c080d098403c00c10144500000b501061802e140100300100d00080f44a002e003544114110560b0f03420f5118141945c0340c58811501c2e0301c009203559038032250403555014400402041144a10300000d201c0c5c029031016651360400c61420008c2002942203c0c4007280c008088041480403d01c11101e81c41c4158010140503490300c81104009013516003107003040051000301302c107001d065107900d110004403007903508241e02c000740b40d43c00486c02600c0c42d47c01200c0c09141e00c01800300c030301058001141260b008440315610310048810450803614 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 836309829 1250 836308579 836308621
    0xb01020d0302120112030513090209010f0e220e0708100e1c03090f08030f060a1d0402040c020c221104180e031e0714070506030a0e0106150201090b 65
    0x1103500411a001c09441c0840300c2906c240703080303400c00e0320405100078030702d4072500312035a40c5030003245040ca6543c0c0107241d0011311140b450300301b002c60b2074030000c6105c8a101000d2401c0302191a842c4070644a4980c211541071801c40c012078201c15a41c2e04034a4a42814941c8486d440d401e04036030804001c400a01a6426018803600180c0c00c000381100b5001400588412207010031400348003c04115020040d52040b0b20b42c000750079081c507101b8104030454142da00214169020118a212a03004200605900907416100010a1074508200303a18140320250150783c8a030347c0581e150081c60941d10f410070102090714040c03052403040341200340300f0b006d02c0c000c030214100d15410071204052980c00a0301642c5102058078a1301140075203503002d01814840350180c860001a14a0810114146400950800c071010b0301e252801c00000941d94030002c2c2140302d60b035032a004041c80352030b130a500600003000500c480702030310f03084640060301030b01907900181c42109040c00011403e040071551a08480 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 836311079 1250 836309829 836309857
    0x150602010c1403130f08070605061c061e091a0a020a1d0114030c0c0f0303090a0b040c0e0f07020607020f0c06070309121b06050901091205030c100b01020d0302 70
    0x1180b40c1c1600e607298000614103040c0c00190384065001c1680340d91000c3d02c9a00440c441d650f1400d050800c4010b58402510044c0101c09901a2405120010b0920b0b89a03da00c004082001d08508603031000c040c0c0b031004c100483d5484c10b8500810402200d45500009032030080710825541c50300b11440807406161020300100303607000b12a00700c16100504c4c16864290504005004480042c0c0008081d003045400b82c440910020720601032210400c03d071403803211201c00451075482c01da2100350301c0c0c8d25100001800c981545004c00d0410080458480150030f0000000e1102c9c50280d2080c501c1c02000e0302d0000150241c2004500410b10120701c00c15010030a000410f1091001818000103034007007041982089440480030800742c4688000c0100781e4040c15140f0180c0c0c0b020908400d0325044d941c440000d00c0f20400980356580d030003122590440301e03507950700340e214021030508505500c42c481080c4194004c0800d542e034042e0301c580c000d480c0214203134212070a240b114a010f80480c450114290030003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 836312329 1250 836311079 836311097
    0x17030103150203061e03031c1d0f150c0f0d053925050f010b310b041b02010615020703080307020708030c03030f07030908030a051b0a03150602010c 65
    0x30b050309060b55400034409000c80740342040f01480341c4104003540c0c50010f0926100c09000b10501a40800041d0344504003000e840d6240c00505d03817a550b18401d0140120b0b209050002840079033455054a218a589040045d82e4005202e041c80052000300d92091070300a81b8250403c400805000540404a0040c440c1e9031640c9a01d2020490f500696000159285200d180c1c400c0b00a80c0ba0b158402544100c0081c0076080c41e0180f5182520f036403601c21400703030b28510000301c4005906070250b44010300454500d54450b00d62400c3d1009000d1042046e600b040c104512403811440342030440d611420329900800400e51070b400c21300341102806807548016401842d041c030100e05050011074014405004a1742000c0c0c0d164034003400c40d000b0305580741c502c2e0008001c00c100c0d032141703c1109600401d50711301001459055541da134401d010150008140c00e6540d400100c414603501e491070010700100e0410342c0c5508510000501412030395205c0c580501c1d40380c00c000f544500500800003d990103860710240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 836313579 1250 836312329 836312359
    0x14010e040c0510090e0a14271e010e0313031707060207030804060507050c030f0d06080d0c0605010806040c0e07030920122b051e030f07020d050414010504031703010315020306 77
    0x62008c1d50074108950386003947c1d03090a0084200301e034801c040540b00e01c29079145403141c000e500b1a900040c0e01150341d08100710058881d50b01e221003030b059136413101200c20110008411f844a41c01066801088a8070014042c0c081c950000070891046120b058140311035642c5003421609405854110344003540184001145840d0f15005880180c003190f40c00200740d81d450842c686000700d601c42c8030001c60540e07403501050104900856001d403100c00002d001d2810305540304c1080003001d01c0340c118408402c0740450001132190f089100f04c81d400c4404070320b4000f2000b030328800002c0a03500680c03080000e062001581c86010030121050303001e003000f9450401511400020526400e03600742c0420200b00068281f4810070101040b9400c280f1620307640b00d14065000720074a45001d85840c3c15903114402142010b40e01200f101c05860b200c8542c1c0080c6240d94005862078012030300010f1007500340403001c40382c000507034006d14100d9005215030b00c12a02c0740419101248410b45615070030410500013000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 836314829 1250 836313579 836313601
    0xf180a02011b1a16110d0e04020a0210050c04060f0201051510051605160608040b0423030d0c0f05040b03070e0f032506020114010e040c0510090e0a14 66
    0x400e05004503c5203003103000200e42580340d00c004a031241402805610040b45143d800200480701d59560b400400d106222400f024088007503925200d40b1898000480c8440a0f10900c195500224211010f020f2414028445040da8115001d860f00040c111100500200e10500130140244240d0f0503a80c2da000700c10b814488015a915507050902108000581d001f0b0b0244100561960081002d403c0a4000c0200c0c1c0c1011400307a070100c010011110184004200c414130520b4206034032005960381618243c41e01d0004401003810312000c1e00000c1082d0034003441c103410070350340d60841d81d640c4524640f5040060307c0d280501d0090703034004a01440065040e0f80503295a180c3c40707400400030315080042400007840d0080646505920020700708801003140510135501000d0300c03241c0005d001d041100b03040d48030200c405125440c0b080c0031702c030081420300030a030401c4001780201406103068041c546002800c1020188900e480c26103040c40050b003040d02e54072840340b0014040300044840c0c0c8032040219 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 836316079 1250 836314829 836314877
    0x1b0d20190609030e10030e0d090509130507150207030c060201110a05030a0f05090c0f011d280308280806040207060b03031c0e06070801061112030f180a0201 69
    0x1e061200401d107100040c0d45482012803010845c1c0c6d00407440d08260180c09003401040b0800000307101d046a014462075030748894007944079036100c0143c01540b81c50300303000740703004111751244c4011800b407401444010740c04a9058162400345045600d007a6444030104e0881300340100501c040c00c414851011b040f44950000c42c0c0041245801046542c81c0000c550b048482c10340d1a01d205a110340042a00e43c24401c20381d0800300380909149816401d4411003120020300e0070f0b42d592243d00c01e10f5249066111001807079110170141003800d0212510381c13900c20b50a42c04100303155400c003030181c400e04403e100d410741c42400c5841ca40d070710f80d00b607119103083c0030103500b0030300e001c1300c442ea1144048110b40e1810000707003c4dd01484035050f20080600000c030011940182e510000701e41219042003002070700429600d04480c1d2510380005c18a040000c10f078185004001c0403001090000148071000d408810040e0045100905a074901c4e050072500c1551003401640c020302140c0c0d681c0c01c0c4800e0000302d05d600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 836317329 1250 836316079 836316083
    0x30809010b060319150e1306090506090f190206040303050c24270a2a0306060501140309060c0a02010209090f1e070903081b0d20190609 60
    0x4590039030840000744007500100c2d4981a9601305001841c07404055000d800c4058540c01c0000421900b02908199244002000005001400c20420080090300c0c0e1041c40440d412a098440c282840c0140301c3e00c641880c2441410342c4904c43c440c0340302460071580c03195134503401000302d840e20346180c0c0e003910303a600499034484150240c2415030041c01298a5064500300140740c540d102440c0107801903d000348856018a02c00b401e000203010740440004420347d07075a0300b051044000c001c00418140e111aa0803004410b03441d1480741c00020485c0507000b5600b61102600c030b414441000c28004181804201c54041c0e05900c54004550541ca2140040100031000d20000d440c06400401040c0840c4090350f6051400e40c40208001900f005006000f080ea4404664038200c1d060041c030042100c48240009002100000b07008250740e00003603601d620503120401a00d04215118001a0122a220b010740300009412060f0300f29640020030540c0101c1050700203114000490b46a80004195441003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 836318579 1250 836317329 836317331
    0xc050406150507030c140613030f030b1507171803010f02070206030a05042f041505012102090409080d0e030a090b0903160f08070605040f050409050703061e05010807030f03080901 79
    0x2c0b002d80246c10700c10756105020000c4141c1c100c81240c07800400b41c6084100c2e2070101071501d6085045691855091803405010030301c05601c801660030302e0b41c12000030300c2d440d030074000d0300180034a610025001104040c803002c07002008560380b0f00010b0b400764811146d0082d40003c0800c0022021051540a980c01c1405a540d160032004042c01c0b2403651003d5807030700301c6402c00078441d80381641f816000e00c0d080262620004c504003468440041c145002801e400303011082800390200955415505989000200400c1817180f07094904040d1038603808400714040d0141442c4510084c401c3c000101c4130306030010780d2005a064600514506c00f5003020040a606000c0c0010405007c40e04000010182082d40d030080f4000b440d21108510b40f05090b403044040c40000d01c410003084010820b0f5404840007610041000045482c000c0c1c00c04900380c0005104a00c2d140d001c45180032020140c402c80c0310340701070800080c0d0301c80554540c0e5600c5444010003c010344102d4200081c0702e0080da40d04401c817400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 836319829 1250 836318579 836318603
    0x1a24060c070b0c01390f1214040201021b0f0409050a060212060a120302121615290a050613030c03030819020a080a0b060c0304030c050406150507030c 66
    0x50b00000c503502902ca00402c50391100c40c00510810000c0c03005860814140d030341d031460490001034030034114461085009000b00c120324650501d00a149015046004040404c01402140d134981c8810f642580e0581c0103205102008201d00300d44051110500c000501009494800b04200805001c0406007100c0b035004114110f0001000740c0060804420400e919064030701c3c144050268214196000102031044a070001d0301003a000304540109011042031a951941c690440c500c101c0c0189100800c0c240e0009406d008082c91a1300c107030b40040341101446140010755400100f01c210f0300035a16403120444030100603d1400b54006c240580107500a02481a030b280c84144a0519680c01079000c80d08010030040d42c803902140911407040007040441c00c02030030364002050080002d000b0704005a0f00e03100d104055980030180c4d456561040101d83c1c0c1d50b03803246006021149188260b034019410020046220b120f440780c440b510b80100e60394a81001507944049800d41c80d034131402d03104008218 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 836321079 1250 836319829 836319839
    0x15060907022802270714070609031e27081018020d050c04050f090c0d030302190c0c120510050a06050d20031b06030415091a24060c07 59
    0x70081805a041000c501480d103111030041c01601d40004207560700b0800c070b040100340403103540007d0f200300035001b440000705002245015201900c4400d0940c0d4204e48019080d40304603805141c3c045004c1e1282074080304807020102d04030300fa0310f00b80100c2129070440b8182d00100c0010380e014141d070056180040307100c09141c1c0c011400e1100100010746494110034056511810940507107074010305071078204141e61400000594445d14849009485036101160071001e145c0709806641104036040c084154002440c00007403d14241140119901e400d010030000e40d50600c0d6014405558010300500034003203d00d4161001050018940c004280c2e5a0030f000c14181c640c1380703065414902ca25180d101305c0864042c100c06020148500620a0344410000303403001c1902d2401442d180026100580c40791114a00030702d11220008094007024541034010081c0042416805180c580061281625444d034011408600503801102e5503419249a080001ea040084c001d20303d220b83c0c0c00030359080d6a110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 836322329 1250 836321079 836321089
    0x6141318120504081504120c03120608011a030102073801060305150307050a0603090f020415050901080d02030f0d0b0d240603020306062701060215060907022802 71
    0x2284400001a0302003418813001d0010460429001030410a1320040d04e03069640d0241d40f104180c200d030400070401d0003402051302452000d100c0f112084014004a51147d44003402045031600001550f000030b00f0031131440c01d0610884114603004601c0070b880396000751400384640184410301004c490004100d0301910002800c1038080e000a980c00305450030000d080300351245849105c0d5100342c10200003009560f40e0007402400b120b4440c00c020403541c0141c2000e11042820030030181d0041e00302800120350f182c0c1c0703100500c140c070b004603000465640c0302d010072580d6245140700140541e004110030380d40c0180820240c108c03581c15030004110342484002103100f034040700c00101d48a044141910380380c2180126800d00070503401d04200034080c46c54001076600c1c10003608282c061541c0703112200090030035041039403101c4a407007100c1d2044d582d070b0140259103242089407100d4060314000030980c0c516140d882540603000590090415118203080c48440d104446c0605111400d850101001a114 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 836323579 1250 836322329 836322353
    0x2b030e0a0f0302060a0f1806110c1204060f0f0215040f120221133b0406060609051020010f020912070608010308090616080c0106141318 60
    0x841e501810003800c101d691741007510144011689105c2c20078920007880d4029200d51540d482d001400480c810f06205180d402030700c2170100444050103008049070300810002c0091088410750b54981e614010181d10495045840d11903400058012071404150398600c10942c9401600030464140421940d43e500ba940d2550364400c1e4000d60401b10f40d8401d200e18000d0385081c40700b50000828900300e140c804101e94810180a0002f0b80101035090300326548144030205100100090b4011110718001c2d906000d07480f003250102c4d255420300c0b10100381e40f4454464842221009805400404000c90341950380c44048141c044180c0b20b0f15004640031502401540b050b804078070340c01680c41c0c00b04c3c024000d1390105000e50300460340c0519410030900341d102106604486d00b11203040d07150742095000880c2d61203003a01916400b00c42842c0102408a8ae400400301150003100820001d5500e085000901d61945103079503028905500c1a0240f840c15003152040d0303825a18900c0016441e5a40d8080c8108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 836324829 1250 836323579 836323583
    0x2010b040c0f1106070516060908030f010e0912030601110c0418050f0607020307080d0b130b03061602100209010309052422060f1515022b030e0a0f 65
    0xb04000801002c83c0d0080d6035180c0201c1000058110b0340382c8200054083d11034410f0104105c116240c2d03403401d100c0140d1100c03d40681c402c004540d079051507003100c00c05100c01c2c020f80802d0176108001c20413a00001a60609010255100c9070855403614015583d9985a0300f803605a030003140300c0655150303981c0c424011508610b400038035142c800e0381091031514244899036900b13070b400f031028448250740001c15110040e03441000a81e40d0140f0081d004c018103014281940c201056400207107c51510750088ac160403070650807500e255661000c0696240d01e00c0c0c2030100540c00c5203400c481c2d0124640c009000100c01030501055200c0319a48642c0f8041101d000c03000c06030400119110402d42800000745c200c0710520070071901c0381f02080518040c0d540401c00514040e0395200c1465000103e4002000c0346021301c1001360515685c0c1d400081ca01c1d81100c0440c018024610a4840a5103034884c01d04552109604144410381c201c109400502c4540047c200c01d1140585000010b980c400021240f54 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 836326079 1250 836324829 836324837
    0x906150e150a29130e0613020a1d0d050a1a010e09070b13090203090c011806351009060b0a2f0f0c0f0103050103050d0c0302010b040c 59
    0x110700211001c0c1d8503065450280d00c10029000108165034010300c1800c85410a481c103422a000300c00b28050003481101480c28203040141c80014101d01d460b05424490b240c169600e50405c003240203540104e10411850301e01090311660301c0e401040f2800002e544455010340400124800750300c4040c94a82c12410484000d100350302e5240d481c000f541c025038010079811031000c4090070101402c0e61120003502074400c000c0700c04175401328250f601c0c1040d4401052070040441d40c81c1808001c01d03403640303800c00c80c241c04140700b00d811a401d41c0d164150700d03080710345c2039580304580c01c103003201411741c1040d000e519640c00c131054250809410107031b40c00030300031500000000d42300c42c0740a0521052b104250b21181c2400b006014030240c01e40c10076008034400542012210342101c00c1803205000d04c1070340c298400d0900c03c0c40e04e4050319010000d5041c40e003040449400310070b002d0b42e0004609484c0300340002440c82c0c101107412200240940b4403085658442d000101c0c801e01084042400c86459980c40310000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 836327329 1250 836326079 836326081
    0x6280e0f0307290103031d24090a140d0f06090614040501050105090c0307081e010803040305010b0607020a033c1202010c0522081005061c030207090906150e 69
    0x1e0380f00d0211507111a0400010903a6541c5151805030a1041001c40c401c01c0d00010a1900746c95070760000030551103400300124070180c0050803600c107110b8101c00010b501074101118085a407081e4014141c2c48690018200305084503581c1c1c500d0600640c0186c02c540c60398603080804000745080c09040821905d18640080340d183c00d0034442e0960b6010b030f000d18081c52401c8103210304c07181d00d40126680580e6904000b0645d032180300742840c0c40b850352507900354810f504034000f1400000200061040303a01840013480407040000400c01ca51182080c002d42c0720703107031140400c00076401c1010f44c09070078001d030149159206030640c1c1c440320800b1000c8a08014050341200300402c0620005000e00c02d404c0d100030003085c3c56404015040e48980740700754200540b86a641c00c0840c0000c110700000d841700d002565003040904001b60080d01c07090b00d10768829501002d8040c041003030364104100d4190940d00802015280145803401811504c0081d1204c948801848000e144518032178030080081c4408000c0e1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 836328579 1250 836327329 836327363
    0x120e0309011403041e020d0204141806090705040e0312070207170615060c030702060f13051504090510031232040b0c0f0a1406280e0f0307 61
    0xc00c1024020207500e480007401030001007800020401013807032600c40031303107000d407114000110b0721f241041d070082d030190403d00c81911a443c840a09400f031490f00c0c2010040c5002c1c1060203407180411211803d8035400600c0802031403820303400010304010907100b5030b80790615804a40322414001ca03070f12009688512400c020301415400741600321400c00b4040e00c89818088401281b0300b4111185c0d5110310030114182c1007010f001c2c0b04a03242c184d0b0051910380e50b032003078130640340c5680c2211980014841601c1c0000030f1500b040c640d081d025245081889150a042510006c001e04c800f0f0710320f840c220800240480040d0006811041c055606e4550360302081c2044140340b0b41070030000c01c1d8484650724020301400d102d051701c01e94041d1000c146000b42c48940d4854000d160004030341d5103150900c00c05405600b0b000d40c0c5100c00070485001801e680e05940c3e00c07102c80000c107548000b1403004440e13900c6038a4091074203610540e000c0071050282c0b8001c440d464003c0d407079501300c0c080603503580a0100c460b000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 836329829 1250 836328579 836328587
    0x3130c120506070822020102010615090302150c03070f05070f091415010c20041112010b0a1215030c0801020a0306050a0e01050118080102032806081b01120e030901 72
    0x43d01030014a00b4a040c0d14007025128000c0300310320040c000b1180e4142080045a000703400080103420441010600f001850100410920161000380d005a80580740041288d250790200d440b9481500c00841c50500943d03140300010301c12101c00e5072503000f041e00100308150440c5400700100b620310b801042c22401c412141d40000d20151050014407110307903c048c07659070040c084041c0c0907000402e6240380c254032000440c9019410803400e41c054070385581c51ba0000340440c050f015810304a00c41d0083c580c0c8031003c1003034920800d16420081007203680c03684110312498012800da2140d00011000341c1b51707607645001c801c0c5101d07040a6000c0e50046800302140394140f003440000c0c90b0869405030b402d0314111141c03084920600400f07041040c6a40072540703448051054400400000c0000c5641e49086168071901c81a00c201c01d002c00310038040300145211a5000701d8040c0c9915402070062417440904145002c00400442810f020304181c844101d40c0803845803020900102010b140d030b0f4404000014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 836330935 1106 836329829 836329831
    0x20d110d06150203040608010e09031b060105030f06040f11190b0706050c19052203060912083106020d140105041109040203130c120506 60
    0x2082522544040d0850302c101d2400584a51050790403612489503200b00000110420010300c0312084150401c0d400c400359400b22450121301e015080a85422600c080380c3e00e4100000420071420107101442d9146002d502900240c81c00f0b40e140444c06510842c003900040203030744101e460ba2502010342c0e44035101c80c1b90301d8084035074607000c940c0c495001034400c64287d420302003c28036482144060315982914400b41e10710041c0003180c00c942030740014540348a943d1000c100701408241140310403000c1d601400c400714501c5254288a07002445602198040004200130880c1141c1040038808609404021780701a100316490032440c415994100a46a280300040d804510149035022443c0f0389410700c100309842e0380e01e82c104812030b6441d01c000f100b1500100049002c52a00303900541d4441e501c0408070a0000c0c99071100071b1f142001e9001181c1c1100880d00712414448204001 = true := by decide +kernel

theorem cover : BRFrame.Cov 836151079 836330935 := by
  have h0 := BRFrame.cov_init 836151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 836151079 ≤ n) (h2 : n < 836330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
