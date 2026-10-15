-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4767
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:40:00.437685+00:00
-- url     : https://prove2.me/submissions/c8d0c86b-c1a0-4a79-b70e-0b4834eb699c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 857194244 ≤ n < 857374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 857195494 1250 857194244 857194271
    0x2030408120315090f041403040b090d030905091608010e160c05071a03190c050d2d0c0f091401030c02032802211909150e120312040204020904 63
    0x300c100c4961205c46108001d000500030034401182c41840303440000c41c1b03481c0c03c10980c4039180c0602c40d481401b0320441060b210415000d90720b050701500d000381c0700300e8251911040c240e0000640c036030000c02003050240041080040810381d1803061040c1c00010580d00803280c02101c1c0300510744000e55441c02040400b2801d28030440d01c1c120316450705102d49407281000501d84081d0800482e501024501d002042c03070005400030184ca4280100501c0007900c0e1410a6105010008651042280f424420840c0646910319808a106c009440c2e0342c40c1c44030409158190780c044400d01401c09100940019040658400d0304495840354083c4190b0b410070b25903000a0b03421404d041c00c5200c1c200700c100070f04e6407595810070034000c00c40145074001180702e09081441c1d4051080b90012060900d0100461000500a418001c000e102c1c0380c2065a01625401c1c00824180d949010b0900c500800b050b208140c40002058520200a01d10800b4a0741c0b40c0d9800c02009611914410f85c00c2920361710416100c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 857196744 1250 857195494 857195509
    0xc11280b011511031305011b0602030c130e0702060f07210b101b0f02040209060a02070914040210080603010f1406040f090b040f1a01080d0e0102030408120315 70
    0xb0049041c01200700c10030304001400c810007043c3c1e001155072040c000740c02941c51950701c0300115032083c01d007002030b100139410180f140044800c01408540c00007061040c0700f00000000c2100003101e0030121031140d1660602d1840480a42d21240140d100102007a11603840f030803480d40200c10790030103c120030180501c1343c250040c0c3e81034045010307564544401060134020307100d0350000650301d400440252144001009155100c10140801685e10711380c40c00c5480707550480e007042200401c100c1c0c40d1481c00400950756411402080c039140d0400c02035000b40010740c0c810501480e801003516001c8442594221340d6003d00420341c03585513481e50420340f00215580716203004000004920070242c80e0907828003054400c280000341003d032a00c0310082c00f05201208080d00b00f030f404041400418450700380480404d041c0c04220000d41d150b4000003900d601d0010701544040146d450300300315900721200681e01c1b4025407140d0591a0414800f003600c00d1004401158054052900509000d10090104445 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 857197994 1250 857196744 857196749
    0x110f181518070c020328080706140c0c010e010b15073306080604030e090702100f050103112d060f0f0c10020c070e0411030105040606090c11280b01 65
    0x1103083c60000b802582000e1102440448005115607510510913503030001041001c0c1000e40005800b1400307004108445d007110101402c0c0740c075001c4090034098600d80c0c41d90302000c41300c1e099601c3e0800a80d11041c041c044e05030682c000400101c107800b070904840303000340e0202e0011580c007100c3c0c0c00038581e050701c004c1400e0082c07120f080c0202c0f910360800c03190100300c4e410307a003081310103910460800c0300195001441d100c0d00d40042e81c0c501059101e2200503441d24604050401240c4e013004020662844180e001a048900440b80101840150018001841c0119031135483c2d0f40d550040005800710300351800d00b0303000d102900c114640036142d482c80c0100c0d00b081c0c1040300304205c001005088400c08105109002045c80400c40c41c103003140701d480c2da44500502c9803603034001160000806010403c4814001c2100290091000740f5282c500380c401440c55014030750080d0710701060620381912840d034104480310020003c1003420b20b98594001c0b03031130300814960341d4281c00034042e00001c0c440d400031a00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 857199244 1250 857197994 857197997
    0x12070f14010b010905090402090a020a02030d0c022b081f09140a060f060815010e220f11070f02030c060d0504171911030d09110f18151807 61
    0x800d00c20b20000100ba42e5019400749205412941c144005640c502c0a03880d00704280310b44c0181e0b80d600480c0c050303043d070040090207100a840c103040c990030181c0200b50556004040300281ca441c4800681c120074403031446591100040c01d01c00012000c5990101c100071040d84c45a0401126940d202482c040d940729035420710f003184084050204a01d00c600420004c0d0610b02840ca0202c0c1c00c015004041c0c42e401800b510b080c2030014910201ca0340500d052600e00c60002e070602d5010920b6550309100c441d005030711050124070300358007540080410b1140800a18140e0f140300e20340943c0f030705c5200c80000303850790070b0b6414058280641e00a0791900020150103014500c0401c0610381801c0110300300e071142c5141001c42c242001581e001000d00740301c03c0203202550800c04090b25070f00e2200752840c064000f4240d6030525044509040c4250740b0601d40c4610300032109141c25203102c9040c01051341181c444041c14860000102d940c540358080300c10040300000d094030056070700c4c140c0717030b9203c3c0c0105a44000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 857200494 1250 857199244 857199251
    0x507110d0c03020309040c1706041103070c060b0a08061609080a03080a0612140c01030513030f09030209151c0b01050d14100c022b121b02030901110f12070f1401 71
    0x108e2100c400201d40e5124000302c070308100d0040d003202070044a2000800c05420404a0703040c10742000070399884205610310180525100c181c0310b038011545c0b007405039580803444442540681800d88180844070070399018001411566103955020b86169a000d0301003c2d9071a03d648012800404c40d8984040603402101c3d4a01e80406088003d03007881e10b42c8031418105818407041207200d803a03d40b80d078031005504d403620404034030030000700f11043d440940000794000c0d261400d00c015003030a85060120780400722290307460896000c4440e100b11400031801002e0032a00030040259250650418007032034000c41e14050041101d41446041001c4156003003200d036900c0303400106050f81040220100a019000d881842e00c600d0115020281005101d0040003c601101d443d01502a0802d800d59115841410100584c0f180c000e51640c20000526000560034041c0c1d800084c400620400c058040401501e0440c4802c1c046100780c0e1700c40041946e0304c8039002506000a2510130402480b41000d40000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 857201744 1250 857200494 857200517
    0x302120a02070c1e0b0d0b030f0c011b02090c0903030d0207031e0305060a0504051b040f0614031608060103090206071104060807060e04020c0705030703050d030507110d0c03020309040c 81
    0xb15611081600036107140f01a1602034901c0c41440613600d81540c0c15141c04079290790903ca00d0b00301411003e05000d805024050002d0f420200000d21090021000d0b200c110b0055810a0000f615840c00304000e9406140c0b0b80104080b09030711b400401c020741c070250943c3d103801c450a14280c1680e1181d01e0440c001001080004804404c00c07012421b030744c0c0645024001400c1907000a503c5210382c2c01024440c80c1e403400855050302098203000c0c103440c01c81d0310283e2038582d1440c041001030120300c118030100d1151941c08032070306410b1007164420410f07a80441d0300250003180440700300c0030040189042c940d03507401e400050f81d5101c02400c01c051240c81c0031498a50041c06100c141d4105601c0102158488502440950740181c6911064002a00c0040c0c940b640141980d1400791242d005607014002d40c80040107005002c94111002d45140c0c6080c06192540c0c07000312403010f844600020160403118540c0318840c421540032840601a2044a080008201c000340c22510240f022001260a000e02c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 857202994 1250 857201744 857201753
    0x31d0d021603050309040b0a050a03061b020d0f03052d070e04020a05161e0825170c0f030a0302180301020c070315060e28050c09100302120a0207 64
    0x20201c03118000c820489561459541d01d680340585c030f40a610481c1c40b14440c0050f03032104800c5100400004220f0319a040e9030303041080090032190070f0300d2801030b2244540000340c1d00000341468800019560204080f0143c58100e009003005030030080c40140c1c8000030314010290b428060700745210600003031200e050280c07015226845103241c1a010718010303c002400302d6000026243d000401d000b04e11800c40051a2491070060105007940f0b08440c9800154140480407014010648032600d600140e00c60400d0100702c2c4044029005120803141d015140819071990003418082e52400103e07600c1451400b4198219000000c1400000f0740c0032036030703403804810100301c0041b044c4260002c42c54101649407440d102c92090001902041c83c0300614070105401c1c3d403081d001414100b0706103055042c2240c03400140f981c2d4024100d00c0b4882890b14001e18155441400d004524203006146841030000920038840001440701e000d00d503080c0141c094240343c6100b11845290642d4005075a00411b150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 857204244 1250 857202994 857203003
    0x1202030f0703030c0e102705130b090c04080a111927110904180501091b0819142107061104060203090d0f050312060301110708070b07031d0d02 63
    0x175803098503101e09045205401117801071801420300c0d544100c40d81000d490902c842065400b0a4001d124a61a0150650207911500c4501d504840d0040c064680e0519841b19010ba8000c801c0355400c000058400500f4103401c111070035030040e1005d400941a001008150902c4d42c0c880c003c402e440a0a55100d00c14000605008241520f01008108605a005113030340c01030307900841c000d070ba03109044600c1c410756903950441980c1c0200244100c89407890700d00c0008c1079000032406c1a0b1205400415200341c0070400e40900402041c8d8130849400c035840350a4400704404400300c0740d0003061114800c1c1c0006001200e40e145034810920360300e02462a10401310703880c407040916040820700c0705000040e0702101300d41c0d191000722503160914000341003041c0c20702c01c0040010014440011001300c00e0002501c107901c1a08201c0081040c010640070003009481206002441c114003080600c00085040d405e49802030102d2400046aa05e4110104c001c00d50740c20b10280942d0059040c181c00d20360420 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 857205494 1250 857204244 857204267
    0x702060601170604090c030c1707051807140f0c28020a031103030d14060f010315060305090c0306040b040501230408030438010807121202030f0703030c 67
    0x80c1080c030b0030410300000c014001e00a440103109030f0b140d0040c142032119202440c4051500030710b8000c1c0c40c1d551503070703501e511200d40b0a91055602880b08005030915060380d65410700340c1034594480960f90f500008442140d0080c0360044510340c18000070031903084c071402800341c0107081c0d0020075450060b0f4a4006966050000d0072200990715039442d40140c4a0750400340480f0b92041143d40314a00c0d28000900b580541d2001103011482c03c103960031409000707488c8500030301d0150b6440110b1181880114182c854103118800440d140c85000c20801c0e01c030750b225940c000b105c401500e0f01c81407031b540040c2c145642078800313960341e100705424817041c44000e1048450755520700382e030301f21520903080c0140b82e00e01e80104007501c20000400084d0074800c2d0701078503c126101d054450813040c510001c1c903c0b000b040c0d026045800c0120f8000120302040005004170641e02805003020030350009540b8101200c078030381d6080e000c5000c203220074079a01400b40301801410348a80c4000c43da20303220310001409600b050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 857206744 1250 857205494 857205497
    0x15370c090911190f12020d091202060c2506090c1e0f0603021b0d0224090316020109090f0504021005090904060c110f0a0b011e06030c0e0d0b0702060601 67
    0x81110901070404aa00b00c180c101103802c060307000c2c4c002c0e10303810b850380c1c1c41942c41e1291036400050030400d10340290740048100b92203629540812503c3d040203c0c0da80340211074040400c4000c001003040b54800a0403401802c21489100c04140c00d5580c0b03c1c0140d4a085a04841c00aa1001c0c248006155441c1500b1a10200d04c0403100351454464558468251403081070140359002517950920501d403200f0030b40d00300c1c14004947e05c201034504020766440c0307905004821003800081030801c0c1c1e10001e48040c01060f008000b54100803c4c4a080000010520402c0741405150031000480c009030b405a070521129420b000030750361610307005129940040c0300400c020800c0c10040c0380381c40e554400e2101e400c55001500000c08101748042a5a200041301e84968203200704030a1808150001910380c01c424400d5a4502250360386c1c00c41c140744850415006600b8258000092041c0352280c1e02c824840a640d1030025410304c0c280000c55800c5200641c01d481100c0c80d10b0810401c2c035010803061340c0100f0207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 857207994 1250 857206744 857206747
    0xf09190c1410050a05030c0903030c060406110a0212030c070b07120b0f2404091416170f070215160207060f090504050604020c01050f0915370c090911 66
    0x91000400601c600131090b000d001001c000302c0e08150040080e5841d290003d000c42e561020072410a0303645e030008650882e01c1c9814803402283c1c0003a002d0171780d4000221a00100149003c0f00340f0030b409504010400c0e80c2865080c00340001050392200c1d0319001e030040782c4507140140315032001102076900d44032a4600504103000f4410054854080200c00c64402e00e0a00640080900528420344603591204c0155130901c1021003100518810041c0914528260146c02c0b07036802c0002d0381d601c82c44107100c2d2103403101100001c502405030181190700400920694940300d20300101082460f4007503420703072050104441401c030071a40401941d03000c2d0801e818181030002130140c000789030707502d24002e030740c007450301d9801048003522142c05640c1905083d0b00284820300c0c00384290400000100c079844a60300c5003000766540d41c0803c24425005606014440c0c425404943d030010180e10403580c51007608507141940d8200c0c41c007904c100c440e201541e0303444405103840d0015074400d0b2041c00c0c5000d03140080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 857209244 1250 857207994 857208019
    0x50403110103090507050303030702071805090705090a020c0a080406030c110d11010603050304034e020c0a0b0d0c020c03100b0a12050304031a0f0f09190c14 69
    0x581004004040c502440e020521200d18034000d41041060b91116806110110a002c0c0382c0d0f8010502c1e00649014400c0c05000360003a4102501713640041d034000c00d041d0005802842039013402e02200d1351001162001516105038646854038001e88100241e88901c3e010500780040707603041c02440031030303600ca18007000404642c000113900c3e0714a0100724400e2040550403950812000e4000c3c00c001d5420030150381d01d0fa039480c18010001140d101c40424031030240170700115110542481c0e6048241c0c10f406441441c655100d204a00d0a440c1c9080c0f410342c800d43c400144560380d40c1c081030010b0450000c0e919140c01c0341402e0b44c3d06503235110803210155008007842c0f02a5442c0000c80c7e0388a00b0b10b0400204c0daa010600c003260900f00d0580000c0c0700300b00c440b0005401d0120000050003180c1c42105030095000030403c0c016200a400d98120002092400205492500c1440c02e0381e0444800e4007902c0e094880c14400c05811007910a04075100c541980d8200a81034608401e011004410b885480c43e00cac0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 857210494 1250 857209244 857209253
    0xa140c03102903010801270507030201120b0607050a020319020108061e060f041503110d0c1103070f020306010f05180c0d0e030909010b160818041515050403 69
    0xa08a0003082c151201d890050341d00a865911032202032429010103907a20b58441050901130160300b409040c0c001c15034080310300d20b8040301445080b0345801078041c105081c1150300449801603031161049190b5190010400140c0d80c081c01080d54030310a100502d03003958548140350400b140d071018000306000b06d00384400580d030490012640858116865003e65800440e200140e20a0310240c540088001c10114111104074008000741e0b80c80f203c20400000c08540d0480503030700c00700058014002c09010341d01000303146400000c1c040d1880d040140b0624a032207459459500410820745010140038485415820b00780119800f500681001e50420760038034011500c1c050f151054444c03824090710010343c54901d264292100d100083c00c0a0280702c0881d0354043d5242c000e440460300c6114084000107112103994101c1e60b0700030f0014800d4910300e44903100d03180b45800018981c4c1e040c23170001d800c0b910349039100c0c4034601e01030050076514042d060401080c40d180300801100c10302032000411003030001c50b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 857211744 1250 857210494 857210521
    0x30301050f011103070b0c03071103190c020111031c0b0405010b070f0c05031c03050a150506070611030f07020f01110306310b12160303180b030a140c03 67
    0x74982030074005184030b031207040759141d84145040034000380300074020f110380610010001d500480181d541e0004000e1203001903074a0340306640b114040c60b084444104041030040f40030502c0140141429010b0032001624281582c3c01071100c041e002c02104900303400000d41c1c0c03003501d10800080e20700b0407a66061400d00d038018410301e40c01404010006400398100034500144c103019042c081e0549507aa110105011110200341e050140440d04120001300d104401c1e1041c100d01c503080c610f17a102d64528280c20f02900f60310546090311007580301c040c080d007030030201c070002c601401740e04d003641c100380c6809000241441246400c1103600e0341003114005084100c2015603400c4039084804501c4d084103c685191900001000007a040c203c04114a0b2545400d038000305051700d0594280d5241003080300420b4a0703424510b800302c45d004480c002440882e20402c860205600c503072081c281305644841442107181c10480307072182c4d0780d03032039884d00b0590b03c4088401c43d0308260720701ea901d42141400c00921051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 857212994 1250 857211744 857211769
    0x60902040e0a0b19060201150501020a0201090e07090506070c080d0c0809060a030b12010f0506100c140c0a0e01031e0b06010806031f1b21050a0b04050a0b040e03030105 74
    0x4035407a00f1542e5960350b00c2251481c4201d400501010b2050390740c407006800b905080600400701c41c00703100001001d500102d00c0305012070b41652a060654104000c6502c41c00d00500000104070284030045540d4681c00300500c50180a100d840d298039140000207444c0c40316401d810420840d0000740d840009902d2401e5504241c1300b00e49143d102c5c10803400440060600e503419907800029080c64400501e419480340310407401e015001c1c0b103550380700c005020941c460140320300c0006011a03d1000800c0c507041700503601c540b902d82078408442a450024202000c1d54001500540c050401041000403a00c40d03068680c56010302c6030004c00c450f440301c070b000f40c01c018001e605000005002420301d6400380b00c0c00c03540c0d280e2182c6c20740015085111001c0100707400c010000f4540514041442d01074050720248040d1000820002284180003800c4809440058004400680c0759022501641e50714081d040c480c072302c3d040c0009030b000104020082526080284120741e50000c0005002030780302d07039a680c0304 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 857214244 1250 857212994 857213011
    0x909050303060a3614070512151c0c03020607080c0d020a020105040311010201140109020702030709141308091f031a0a0915080706020616020309090708090f07080c04060902040e 78
    0x2120082d50f000700090900180c1580c00401e400c401c008901e03030800e001c0d100c4140703081c8c20341005595000800002c040180b03000e580c480c11072080300070b108a0a48500316482e12a5840440041e0b0b640c3c0400c51642200c60111000600490b2640310b04a04025150040600344018141099940c0020302070384564000903142c10500d29025600344d000350090700b10360f20700072a41611982e4421800c0000d40264200302d200e4002c00c040060750860a0161241c1510401d0051200e40c1720000b450f4a0308610b19402c0701c039004c0900c208500c1d41c4e00d00c6008543c1001482d0a44081d060101c8000e0848031070080300941414416860812500c0b9448828182d40316031000181103045c0386080206100664000740c1640b09a0802140c429408a2000c1c040c0e203100003506180503000c4410390300c0b4041d01c4051900a149280000c82807071080b03030401e030010310b003400f40c80e12603100c0312226081468540102c60160321078244014a41002d104000080c000d0180071400c003400e0442e5080d47c640003828080c1d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 857215494 1250 857214244 857214329
    0xc020f060c0f0f0c1c1d0f0d050a05030d0f051e010306020d0608160911030f0609181c081315050c0405090a090c09110d0c05040909050303060a 63
    0x401c0700000c42e00b19111864224100c1d040c40e50100c0346524602c018070504000507040c0c140040c1303036001c86c034006030b5003c0004219015070480c0f00140300c2800000102620300740b00b20340c80040450000e20060a0120013407a010540d00000000302069800181840000000c60f49005034003111a00303800c0e06480e071088002d655171142440d000040e000c550414070a900803c58040300350040c903282a02160400d94090250b03405094001030b10340412a04200003620280c005000ca190030540341d0790200e031040443d943e00114015040c0341c90b45282808030300320a0b410003582c500303810544256000280c91004d20b06c545031951031070700c0300c0c007907203447d07414141c542002c101d11000c0002910080c1c403000d0b048040d40d20740944904040c02030352406440c014400310010800e0541030150410b05442c600c0c0407841c0480d01e000c01e100600d10302c811101004014800450008001d01a94003510301030402562241040802c201913540698032401410b158000218446c585005510000d54510038401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 857216744 1250 857215494 857215507
    0x12120a12180f120327120801240203070b0108060f091207030837060603110403020f150a021015120803130b07092d1404060e0a0c020f060c0f 62
    0x60f0f0141001900110a0242c0e810f20016910190091780701c5c158018060241140c040140c142c907107907020b020708942543c14421032400c001d0740c1c50000d81d40000074812a45401e01d503440d5138403403980a800c0303011507170012002d00803440c050020854000d0169000b070010382c1071005903140c551207075403030040c03c2c00341c0c0e80c0009243c1014948040c03510310348008035005211800521441140b5001074183c040c0d4039003040403582901c2482098025004042c5040c94541507408214a244001c100a5070103406280001650703000e00c0c01501c3d42c80e056030010481900d03603280580540b980035502040e0704101d41810050a0f03404134809a4450304943d0469980c0c032039043c07031f1625804103100a011003901c44107110781c480c1d20008080441d101030303410000c18843c0f0600d50b40e04014080464409a000500602c250700c410103c070b400e490001880040c0c002d82d40c1e1100410b08a00f00c9000065541e15000c044445405001061601c040c01c005440036241200c2110380500590b00011407054001c00c08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 857217994 1250 857216744 857216747
    0xe0405071d13020d09032a0b071116091b0e06091c06050106020c09160915030e1209010e030609061b1204051606090e0612120a12180f12 60
    0x1290b064440040c403d00c0f1541460901034180b070980c41f46101d40b14021000610b2000c2850098198182c0c000c82c60811521154800c440b81da070907103030259003406403603e800000c1011500e0032000785500c010118413840d002005042e9900b2141c01d02042c8080031040d9101b560300ca004840c12035904035100380203c21010040c4405011503040200b80b1450000007141d01a000a021120075030119880c0107281d03240c05129803540e55440162020a043e16400d000e41102c8012240040fa41c92800042c11172a4032060f529001001d500300b440e255000451207981d50b03000c0416803400700d0680040410f41002641e40b0f0342c40c80010300403010310341000d0301078460148600480360400004120a810f9052504140d52103006c954891130601908403000540c040c010503d402c200d5101c854444c410380d070f41c402031000455081c0d002424501851309040048400c5074040e0103070101c1691060000b00280b40f05004440200d44003240c0c0403080403001000a00598020f254070390700090704681d001d0030440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 857219244 1250 857217994 857217997
    0x80f0d0507060e070b03040c08100216060b031908030603010509030a080a021c0e030a03050a06060e0105091504151103190309050c090109020c060610050304021207150e0405071d1302 80
    0x80c0d074031705800100340401d02921240b0a025101c400f000e03580b4260340002070780224400d44c40d102c2c07200198000e2002c049406648440002d0b10040d054502d00c80342000c0c0c1c8110001010b108540c880004028800c081c1424840c0c5a80403654000a510700700d5000b50203485c00700003c00c3c1e01e580f0398001529480f5100c01164240070b0041d410414410400c803080b2440e100d4002c6500e02c40003c0c074001c0040c4a1880c0ca0080d00222581601c400c0046940c1034011180d946c401502241c00030075440785507507400180401800141100d4a910300e000700000d1005241e071040d01d8601c000c03644240711801031300c914400ca16a561080d4200028400c0c218078000e42460b45468400741c2c4054000d000107107220060b001041c1c054031400641d030060344c0d42d80402c160704150f00210310001e01c040c80060010b050080c0c21344101e0a03804c04480c2d400b6502d9604400c0c50b0000c0e11020f00091182456039824101409026001106410200c070402010b41002402c02401c0d98418459003880110410744c0b407081c0d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 857220494 1250 857219244 857219249
    0x30604020916050c01060b0c06130b0703020a02032107080109021201050f0d0b0a15080307110f0102101a2707030f06080a1b0501050a05030a090309051306080f0d0507060e07 76
    0x3009001e100c0d994190301c1f800c4c0c0c100c22031084042c0100d50016106401185051003000d03400003070352025481c0c1c904d04030f0081d0040e1a940096100400149940008100e10607054003c110707440403c41c1b5140d1802000100c1c180d020b041118018040d0f03c12103840c4030411415241c1c152500740011440ca000140008400740010713002c1c40080f424005212036941080051031000881d5420043e0b0313a27040c0590302c4c07146c4003002e84542890031111600d4601443c2c1d00341020300510449400f000c007416518229840950100c803110313440a41401c1904203107000e08541e85049541c0356800c07501c0d0800c0001084010426001c144d66051010095101540540302a0040d04100c880d641d01615000350143d440c0340f40301550800c64100021598030840c1101c0c0300900300d5880a040d0348807504040f01a2420b9003040b41031080c02c800103e12503c403e000702c110b41e450342c103010030600d1408070500d0078240306900d449801d0300310b034040c4c003a011340010488a156a10010000703005500001d02800c1402a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 857221744 1250 857220494 857220517
    0x50a0206040b0c2802060c0a0519030e100209010e0103290103021b0a0c09060302150f0f0c0d1e0e0922080d060e0411040c030e16030c0503060402091605 67
    0x1c0d22035980b034130a4021250111000750219403550700c861002003000d0003010030b44400070b1020403451041c9481e07400c8043c80390b45281000318410384000130050400100041e184821580800c940e0010b603031010410803000c1c0c01782410403084064840318901c2e220720001260712620b411452740081e9200b42e048401d103031400c0215200c007264020540e40c503521184000c3e0341d0200601000720f00440070f8450f80b42100d50050108805603201502c10180d0380110715800a032900074030000b1481d842a0300103007002c01380b181c041d002428042001a04040c07100307000b0311412020040d2200159040840f5100c404022602441c0c1659141000034100d6025180c101402d80c000c96000d003008050409080a2000c85c0c10074804a511544500c035044422038025008038000c1d462600e10341819400025008004d240100e030001c640c9100c140740050a000c45003480200c180c0420138003a602405001400c0120042e082e04d04003600081c400000151120140e105030000e4454442d0190301201c2480c00417 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 857222994 1250 857221744 857221777
    0x315010609080606090702031b030f0414011704052505180601080702030310141906051b01090b06061b0a030915180603050712110702040c050a0206040b0c 68
    0x40d00001407205040303200d840c169204074400700d20f103860241c1446125a800383e00030340c106811410003408494a0aa0480b181d00003000000701c60b40340500100044e08107096690316407103c050006181040d414600c4200b00b0218050100165012804030340031882d01100240c48600c120b14184401d1003a402958419081c2e084000d25441044a82d4441c1100b600c1d010700d030381d0b100c07001642c1700e00c0101d5200c0f0840d12031400600074148400c101548040c4054203042d00c2076003105110406c200560040c0002c60400b0802415110043c1c440c1e0508442c0c1030001d0003001915a6682e203040805003025100380c070007003101000c50071020000302080c404401202d84092040c100588900f00702c1c000c0e0404c454000084c0164140240045d440d550262200e000300c607440c0c42412401040c014010100b003107040030b10030307c1c4c0081c1401401503503200d80c0c03600d582e070720050b104200482d8a603003209400d01ca014803078000030b030b43c02058043d4850b8000c030441d42c0ca5580c540500b8918030420400c289035200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 857224244 1250 857222994 857222999
    0xc11041409010501080c09041a0703020d0203071218050a0822150e010f050304061a150c06060a050d0f17070302160503070b040b1815071101090506030a050402031501 73
    0x5401840c120f504940544483d118200706000c0c1708442110302030f19580010030100e01ca0244221227685c0500b1502c4d006041c008071180311f600f0382e44265480320000d41009000d041c840d80d507101d02c1c01c1e20081044490901d1015a0b181c6841e0044e5180c041c15980b03004c11000503c90783c2c108507030781000c100e0360310303075466038840544140302c80200b507076030000a540d84510911540139031011014007515031545401c650b1296100c2d409000c41c0d401000318842980319044a40c0c48083c20310100400d8180110380b211010b40700113140c080000c000030302c40e0701900d004000710340b603c0c680103500c1d0342c0048d240300f0264007504000211070408442a001c10100040c0c0d1014180e001c51340d214021280d0600341c15042c1e4035000c0594519490007141000d0008110802c480f506040080594203585004007a003101c1800c000b40b0300100100b40205510b000013406002c00c000f07600b4540031580f09003010b07090719081c6004a030313860200402d0000543d036200041400d555003040013580d0b003080c800040c1b18130768 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 857225494 1250 857224244 857224261
    0xc120a020d03020d08090313030227011203021213030312110406090509090604050c0f031f061d010b27150406020f0a0506060d020a0803040618060309030c110414 71
    0x16100c4d0341200161101c80403540315a4080102d8072a2051124100e50b010300b183c08120749000b505a4901c40d51461941c001303010109101407038000c0c1040452030b600c0c0030050901034203107445d4040c580e80e003000c00c024110020151441160659401d441c0c940850149176a82c6002003280845000350090b01050000782158054080c00aa070000c1c2c0307400c8040c2c2c0f90300f043c2e070390b40eaa420780780102170380c11a262841407800c10701074a2007886802001c442c1c4041c0c0c8555110742c10100c0d00c0090b071465880e01418854240000140f6500c400c40460100e007940c9801603034000c038000c0c10802d085007102c0c440981110040c00203031200c0d42500500c030900c054582080c0c0c003025032003803040c0c0015019030100318035003d202286d28900507800c040500075a9543c903080280703900741107070100da02101c00703c000b1550840030006400608070303548a001e50a407058004040300c041f01d50080e81014101210600082ea0209902da81107038080c005600030051280010050075501d0003400710761f06040c0030041c156 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 857226744 1250 857225494 857225503
    0xc0a1511010e0d030608161707031e0b1e0a09110918070b0a050d020705070b070311070b031e07050f0d0f051015080702010213030506060a05060c0c120a020d0302 71
    0xc021524100b03c010b655044003a20340c1c807c0c3c1c0304001c4040e5000003c00c8040000d00c02c5564001c01c0c0d5082d0ba409030340340e6450741c0c020010202c2604d003c01924521b00100300f440c26400e500b01819013241602a08201c0d001c00301c10400603c4001c1852700c1d9821442003022000d004060110000e20a040500d40a9003c0e440c8860905001d007043c41030020019441507030100300d03001d440755682c40900e0118100c20710300203507010600440d014803c1c2d603000181002148054201e1910940e5512518610031200078070304a09508100d5030341034100244514070301840d100350a05079000ca240186079403280c4040d00c2500480440101805002a002002958603030000f030420302c00d0081000241c6441403d0a01c0c034049000e00580c0c10301c41500780c3c45160290480715071010b5503100162074607503160110044000e203a401140c5c80d901180c1840179a1a001d0f0f40074003e040e0941d000340c1481c0900340e07810383d078030101c0d1402c50080c09070b21038006410000380550350b200d82d0054043c0000220324503000703545 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 857227994 1250 857226744 857226763
    0x30c0f08070209011a0928270c120e0a050607020304030b180a080f09041407030f0b0a1403150f07180e040204051905040818030c0a1511010e 62
    0x104070b08400450f103580045c4505d01920002120306042c4540003050101c0c045980300303c4e62001c03030290084078102c0480924040030302040030b0081840c404803440306200d181080c6031140c0d1941000b803041686544001c03a0b83c2416282c5101250081c2d84d26640ca04200152001801c5400340b90200300e442c1e500000100100d070703c1490000842c3c0d40b0154a2400288000e03084055900120084008070706128060304001c55403450b0300745448600320000b0b0840e2141403442d0701540c6420108a40c99030544103800b681d101d491401d00104804000080940d42c2d1402080c074440441c0380682e13041e840030000340c0050a0307112001c001c20708207544003550343e14040310070340001039030741d50001e650715a001070500858a14103415482c90f01c1c0d9508000180c078004066031448403069000105800c00d60003658081c5005000c2159200d4136508c0710049418030981e40d6010303034481e1103204120346942d038100c81100c0010094034054043d003e8220360000c11920a18000e6080c656031441420011032503110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 857229244 1250 857227994 857227999
    0x906020a020d1b02040e1005190c0302210910090507090b030f0d030c03111908010501090b04090c03020c1b0f01030e060708070311070c05090109020f16030c0f080702 73
    0x402100e0002c04984500b02d1012409a29000d00160b10040c24a078019500b80040728003520050f000612901c000c44a003202c0032541e4078411031119550304d0b0148100c8196400518056103041c101301c0e81741c0280800840850340d41c020a1001a4840f08148076500482031515000d000c04403031801d000b9611102d9005503640d00345040d060541c1ca203000501c544407212514064060321544160540082011288030018191103c4950320344031400c0000704083c40c101400045070740480000106403210582240d0f050014810b01481244580c00c217a800316401543c010030b9110551500701c010b801400c455032558410058442c2d584508640150a508801d54030504041c401070011800c4ea03d03000b0a004050b04500c010514540c0320700b000b80e0380012036003008204200540c0c1d001380e0940c000700d425160100c00c20010b101c1c0c0c1c0742000c80d41c5d004004501c01981007103515981d50f0306a124000100c45580058503200c4201801455071424040d00145245105540307400c2003100307a80f046100b2031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 857230494 1250 857229244 857229253
    0x40909140d020102160602180a1503050906070203040b071a13210c030305060d1b08010e0307050c06030a0608011802030105060a0312270603020c15010b0a08190906020a02 75
    0x80c8810310504c20342d02074900c251000c4d003001c000c58032020700a43c03025850b00c0390190711558044140d00c8980d019402000c40c806a03504440c6c07881c03c020f080700c4001d000380d00c40303400078424071145907030010a40d400c4d1451180555559811480d205548001d041407100e00070b0b802904105000d80119100e40c0441e01600c046046d504c6281d1018481554861101020581c0003a500300482e110743d00403507000602400200d01042c81781c42d10700b4081d40085a98000d0240c44809110300076003030040700d00515880006504040290790b07990388803556681c4060140c03101000090344400c89401c907034010b04410b0000c0140e0b10540c80d00803580071240a0990081d0300744008940304d4280110300200b00da03017111803050b9040000c3c1c2c040718900031401c05040320f00c1c41c05840c042441ca80200010013883c06072001a03403000703104d0340d03a410214440076440e50840c40d840108000300858007218a41041c80ca050035403507444141400000303c8440b10700881034640300c408000c00800ba40189400035aa40884 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 857231744 1250 857230494 857230513
    0xe0c090a0204030812040201020a020d0b0912030105060706200c030301150809070501051e031005030706170c0706061d07091505090f03070302180f010e060108071404090914 76
    0x40081c0d1041c0d110081c0500340c2084a640f92a0380350907400e400501c14030668840c2c881d04c0e000194010941881511303202030340c1051001c14541001070781e540c0041c0d4112282950f142070001121030280d0b0b40b011300000d44443c00d48004040070300d400e110b11000008095151000c11107850fa494009019104c9540a00b101100f6140d0080124501c10f07c90b800c01820000c0c10207004403016000405c410544030305044100726080c1c05c0c1c0c00a540706402c4259800900c504c2e00d0308052a00000798088020300108640300e004210b00f101005600c4440e29624950f107152515241e0b00405903680114580301da0220360320080341a192179540103000d50ba84032101c0c41e888480c003074200b18185200780b0100d001084002400e080803442e80c00d2181c4d006040c0c9170041c0d0b580d00440c9a945041201c181c448d03c440040040b60b0070030440403409883d40c80b100c00850b241800010308940c1000c1c14200500c0014000301015000440480d809019404410301150841c0d2400a000fa450b0b5552860740e4040c0e000c24 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 857232994 1250 857231744 857231761
    0xf070905061f26060a05120601031704030c0602030319061d101e060f1b0809030109061b09080d0c080f070206040b0702181b0d0204090e0c09 62
    0x440740160801001001810921601e000d294600d09482106100c0743c0c1c0d400421000c2c3c0324448024140d1108845501482d06904008244000f03400c154410034460700b0512421600080040c10f580d4004000108201c0d900444071003402a0b620041603052801d4001c40c0303041d4040040c5005000c80200112041c0c4a408800d0030340d0014000c64401451440703000300d82c601822807854000c20007600c180383e901d840b01900c8130b0710403440d10540d00c0849840810441142c0c4090816810b030018a40f000b03000000d00c00410741011580c0004d480320b60f0102d500a000e607800e51012061940c0048100021000f080d02c401d650143c08201a0205e90480d00c0080c40e03e0010901141c1c00c0b09582e5440c503841d949603200841508007034141501d80c0381c00c0c0301840050712001c00600c0608100c815064503440c43e80f04001350000b15a0101d008070034400144011440442d07600001c900000c075000e0b480340d1002440100900856100c00ba00b28100540981000800700b0140340c02141910100d00700d6941518 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 857234244 1250 857232994 857233001
    0xe100306031a07021c1e05041503150302091e04050f070603020f03070f0203070f0f0b090c0a05060d020c1b010305100b090d06140a1506090e0606090d020d050f0709 72
    0x1200e02c056001742c43c48514010040c40020410001804c104464110210b0709101c0c0c0e40e0030300e45003030204d18005400c2c4041140d042106006900d0740c43c0a010340341c0e03012201491014940b100a01403038006003c01c1c2501d00500070007951f40c0c04204491403e00d0541010ba503a0001d24212742c45034051000089901f5100340215840b40c40345c540090701c0d5848840007124040340c002e00036811030205104c0c160029040d0503100d40e01c07900444080c2ca00200700e05101d00e000c10044c00040c41a4806010b4808989035003504004681080fa41282c0369030481c0c4501004e813040880c0313142d0f40c0c00f604800c01c00700d1840c240303481448102a42c1c200115a28a480d08000411078001c10039043e83c2840440518648048414800d0f880b0710404290b00140200315102d03014150703061503038980c8039904a0450090420640020a0b1501d0003012440c0b4009144a000c4c10180c0600e001d600000795001090300c03240444100755034080d11103082070069042807a1902d4082040401d0b03401042c03800200c4044900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 857235494 1250 857234244 857234251
    0xc0612230f010605161103150910060b0a020c1e040906051501050901020a0803060a03080a0c26120a06050d03020d0e0a06120903030b130902120a030801150e100306031a 74
    0x341c40c0800e4121766181c281622940d03600341a418450340e000c0308000e200c0780f4031b464001c80c0b19074004c09644020150789810b650721703600b01005024083c0701c000302441d030014424442070800d540040700ea50020310428840003165031840e4019080c58103943c1040542c3e80520b01c281644070500300c0c194280401190907102d040c00090050b44440705000101741c010000f0b64000c80d00a246081055403076540b03e01b180c0101000c0c0c0003150f611407004040c072141000028480f080306600c181480420408d02da4103000e041180c92002152030700194200360140d100101802e4010040d90580f0401c1c907000b036540b0340f012070550005401d0301d00304000c1e041c510030b22030a65103182c544480c03510791f80a180c40203000c214410350400d0b840305502c85207525032400740c4501510707410010917040c0180c0144030408a6041c0c10400c02c0d03001030605e0010a5100ba61541552122191080055852442196154002507101d076120031030292226805405611820807244124050b1201c160490380b0710844d01400c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 857236744 1250 857235494 857235517
    0x218100501050c190623010f090f110d09020a09052a0909010f1a0f090f0a030b0c07020418020d0323040306051807030c0612230f010605 60
    0x40028000ca40c02400a00080c0102008842ca4465012410300380012108000d40b01e41b55141140c0d144021440007440d0000664210070465524101a03102c498160781301e00c0074002c1e940da042c500503412641020303d4030649000041e07114288202c6480c020600700c02d0413881100c030442c0000f00420a80078482c846c1319000c002d2002e6640038121219039440380c041c2172074821820001a89a941d58a9000303020304a101c400d140003a0400b101c100309844441100c0c229010700f444407007540d01d089000c03030700c070480d056500c5c00940114001054403041d6641009003104000c0003042010328500300034244150084a040c00b6039031152428000401012401940045d0749000f0302c80400d004038036100d1200804080c0c5925040f84220103050b0b0307003060b082158040d403614240b109214680c00d1402401113100c001d0000145155141d80300800c4600c9018280481030a044007021916800f4801c00440020048200c504049280105000448030100c188103800004600144600251259011003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 857237994 1250 857236744 857236771
    0xf0b09060319080901030603050303090109140a0c12080f180f061218030405030a050c0907020d05220b0403030c032a0f0206070503070c230d0308150303040f030218 72
    0x440d100c14001c2c4c0e00c03007065641032580300e11300080014005c10083d403180e0385100000aa92905140c00c24156441e01145070045d80315101c1440488d900114010031210410007144094080e454001c1c2c050013010300990402d6004030381d1000480d003018405a40460844140b800300c0c40002c10000070b0700951300340c0c02050585070005421021101c032922507101c04201164105603407880003a20740a05c804c02221203030403110a042c424100f117000c554001d66140090705071504101802801c50064090a0503207104c1c00341c1354a82544c480503031f03802030034214104c0b5989a80b241806000a850244204c00062030100f1800000c9049001c214100040e000100d080d9580d544420707001034181d01090b030388413204100110010b00c00300010b04219100d50308169034149482004482c40903000c00c00c4d42151180100940706035202c14014000a926050040103501e4480c00000c01901039100180c0504c4006408240ca03100e4007050000c0b68422118400303030b401e8403285111308010641d03d2a0a02a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 857239244 1250 857237994 857238043
    0x52d1509010b0f210c09041109060a0f092606150a0b0a020106080312100b04060819090b0c0309011505060a0503041a010312031433040f0b090603 64
    0x4040f0080001044140c0210700c0c416040041200080055400300c0720b99900041c61a600c4c01c080c09000c4200c4503040c80241081c44900c0400c01a01c2408041d40c00c1008142d44e071200640aa40c00300c0140ca02052500c951080b018a140300307180381500510b09520904002980c4c2a0b10451a03031050040500758192482c0307414130045144e080301000c0c00641d501c0b0880821024020000b403e040c02046004241d9030a0242c10715140a006400400d0049410001070000b103420070603440e0010801c0b00140010712040c41c0f24001013030516001400850004140310341040717100040c0d4040d0210100800840c140c0c03080d090240803040c0300d1650420400d00408034814000e01c05154800c0c064a400041c0d0320000059014151098004030340d035065003540501050390621a07c0b80410003100c0400d403a0409400200a01c1c0760b180c07150540590344040e5810001186005404508028100380034614003880c003c0c002d007200c1c400c041e00402d1040c001421b1032400141001015603013501850b0682d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 857240494 1250 857239244 857239267
    0x30a020a0e0a231008071a07020d0204090f0c2c09010222080115060c021207090905010b030d090f090b0301060b04060206040605070905030709052d1509010b 69
    0x5000414411140b80c1c0c401c1c000c00264105040141107010f16002d056a61a0401c43c0d0104440740c0d40214600c1c2c0d00c141024005050b000d40c1005103143c00a070344544514440c4006804c1940c510705c0207400c01d050100c01c8080040542c00305a07114452100c800c0d15603101c211000030820a141c64140c80c10441490b540540d280322141500100c41600151500921075000c00c3d500e203003020b0741c071440308038a14100142c140c00e1050601d54645452904456450300300001c1c0002e080302000303441850f0b0004400b00129080061900400c0171902c140b0114445041c128005c0001804040c0640221140601403a101d000c134401030741d4160000c04400d07400d00481c40000c0114210746034156507200b80c040385005c040400f80000700103d0740180380520302807a01501303032031028010806000d02984140400d40e0042050010745846600c0003415565418042c619103000305400c030b1000c0300e040894801c0c041240e4441e4403403c15100d03c184010040d405000c0c071500300b44980b40c185d09080c841d410703081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 857241744 1250 857240494 857240519
    0x50c0a03240e0f160e121c210209010512070e18090f010923010f0203100303020706050c0a0b041a070e01030e0c0913140601060e0f030a020a 62
    0xe0040d80807034040041003070003841c014040c0382c0048180112000800c01c0601602140c40d81c41612550303203110390404480c01401d10b50400003802c0c41000d6040002d0030300301c0c0410082c0300e403100c86132152040c00c442480c060300108496040704604604000032042c1810b00b80225804410107070b46051902154001c00280d04a01074035010800500142d0020b072035448000d840718204a6592500481c1071100b00ca03841d280b6035a072000d600742d04000c0c0e10800308004043c05e2903e280d070b00c014480302d00c4600c000c86004000d18104045014408801e0005440405601600381c911a40840f06081e840e070030203940c1405040442e0708103901802c86000000c128500541d0404d01c54250011400f500705a2454004011900400001c9168030a00c1c900d6a0600031880400140340c05000c50010300e201040742840c000700709070000120060f241040203a0388241413036100c0440c09582d110758444a00030000d60a12580320b210380390344401020030f46404640200072960081010320203034074210303410004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 857242994 1250 857241744 857241761
    0x206430e010912110a0f1d09061504020d06080a08040e0105061201050411190f0206010f081e1204080c031005060303030a1e090b010f0803130e041e031809050c0a03 72
    0x21031710381030000340745203220b65480c0503200c210350301ca401c504012112451924020003d4440e07034005414030501884081c9050401e00c001e9501507a100640d03c40369019252079400818241320324400c000c1440032400140050310b120a440e255542d0342c1320100000c501400400c4942204424010051031030071354000c01d004404100268181001c9841c540105491201c4600200d03440c0035204036440e60500006001d0f1480c402624030712820a40910390340c1071503014000510100400d189445041004038038108040c10710010ba48688414960391208030400030f19000344901007070088100094041c0f0780c461f5030064000c41c115900c0700180350141103041804c444d041003442040c01c5200b082d00038100c840740201d2540500b94500a034500e03c8020b02d6003e0361882d0000e010002c183c0140318000c200314be14940d070190807502c50f400c3c001c0c1182c1e50b80c60303030002c0c1d00800f0031034500301900400d01101e1400301b1502c011401c0c2d914006039094600c200c443c0c0d0078070401000741d00d0a0b03c0c02580710822 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 857244244 1250 857242994 857242999
    0xa0f0b090a0c1e030510081b0108060319030203040e0c0304030c021c020a0906051318020d14010f060816030503090607080c0706051e0a0206430e01091211 68
    0x603025400c443d1421009041e510300000e83c0764000c12100d034060100745401481d51000400750719034100384104040c20326810007410480d884c008101c4a503810001c0c00a964043d00f80c0c6460b50045141c041d50f03a92240c4680e01c1c40b010903c00241002140006503442990181c1b40d00d04898002c1c0c4c00c00100105160380c00b98140b28000f41c007000b50b1038122503075001e008a0040025000d00f00300810500f0072213100110780541c10304a0240c1144141d66010418075810b44850000924031300c3c140c0c0b492146008203940961038656403005003112a0050400c5070051400d44e00c0c002108403601c5085403c0d0b004c0641640d004211003400c600380440105101b5008103409820701c07030405c08980c2000c003241d1010001860210b6580004021071090040c0482c40b51045440c181c0c5540c0b01039100c0e10000e00080009550740c0700003016904240040041101c0c0002c203030b401104210a451109000d6419000003881034442c1441550064086d10141c0340004100e402e00701c5c041d50313941460a01040c02c140c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 857245494 1250 857244244 857244257
    0xa050403020f0708030901030b03071a090a03050a0503030105010f02030c120c160f030b01061704030f0302190c35030403021c261603090303230a0f0b090a0c 69
    0x20b40c0041c041c0200d10240080401840d0765024880004060340c00740c0080a00c40c1e04518030400003202840d0300b0105510000c4042916141c141317000800600039640301501c0f90241251003800c201c400b000035416103000f41c1f1490b81e00c120303940c803c83c0c0c0ea0113078916083c0203034011005050315284000107095100c918500300c944c0e96040d203080d030510403050f0b8046007100b016400140100200321035100d004d8201860710404041030b82c19000345145015001800340010b0403002c501a500c80e804441401d060f13040030b0b40114000c1d00340182009525070303044c1c420031201c00442c60042c45901c00302d008032245200c2081466400c050405180c0d00c058000c0302544510440704800351001c5507402020281c685a51440c4280394071408030fa51040c0f107001c06524040c20030045004e216050b281d0b15a00700340780014a1030003510702030340107007102c10924084044080346030107405c0c5030000003441240290800c0c08180d2105000206a5200350a0194048802000609134100727a40c0691410700d034a15141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 857246744 1250 857245494 857245513
    0x141912030201020c0105010b1905090406091803020c1c0303051009231e0103080901030609050114040e06071e0909050705030603010c0f02070b09061c1d0d080a05040302 74
    0x846415005140440c0942d4001c82c200900304400e10549006019000c0e01515000501e0108000c0078941403003070b024450041112a100e86450748060040c0c14004d2040086016503041c0c2c402030500303014120b00600c10b9025501d030380d0910150303c800e82d1540800386105480700d0303034041c2c0c0908401010080011918140058410b0700c40c05060004049014805e400c4c0501004045101c4402001090351404580010f19140c5280c84501d04507030300070f0913498403030540340012806418168016104136051100108149409060014458208031000c0049000070520682c030b44501300d68010101c2c0c614001402c000700301041d0110491001d16101002075141c01424048a000340c9209001400100800440d03050900c9032206035151428005549124900001c0d075074195070040b0b0003104000300b80040e003601d41c00d05644030020b07050958a2480c1c0c2e52562140108500b69018158401e405507002d03405e2004104180900030a6a4141d41035a504030060058980904102d0840c41484446d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 857247994 1250 857246744 857246759
    0x50702010629160308010503190f061109040903030605010f08041106030c0c03031f170601060302160503070605250f2d08100906120f1b1410091419 65
    0x540003d0302c25154015a541440c09040c0740c0400c800020003681211110720300450844d100c100c0c0180da00c45c50110304030390150652015030143c2c3e820300750030a06002105040503099005801641c0c82030740d960307603c2c05c11a5000c494001c816034000c5c0c080f042070315540e803090511000542d80200d1205049161006021401d841d5501c01c03903500e60010b080c1c001254599441c51010401080070700c41c0e01245002a42c28242c540206104001c1070660004080411000044001c4485a0000252500c460403824038902401044415410080c442005002100c2c42c00004200422440c1d0352283d5410900009640c03800d8013561260a00030411140030440903c50b1100c40112016079540801d401c04010111303c0180365001055010f040000a00c4480114601c198150743c005050180001581c2000908160440c545c0101c0d655a0b039004501d26112240d81005100183c4848100c02250b407011204903a01d80030350001c1c10503145d01020380d450002c3d031030b030a66000000c43c180c1c03c551704c504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 857249244 1250 857247994 857248027
    0x60e10020f04090c200a03120e0303071805060c0c090603071d0415020309010b090601030501060e0114070507060908120306060d0e101b030b040b1804111e04050702010629 75
    0x3403176400c3d070b10030440f0604241c1d00015400996039100700a1015004106156440b4080280450108003c0e40c0c2c0c241909600c05001e040280300150640b642c4605140c10a500d03800c4030507075607019155500104590b41000134612045580c0341108009942840745201c00f07110002e002601c245802e0000302034400d105100450150311448000119500900140684c54000034003050605141100402c645c030707007151134890024400d103000900c9035468101c00c0b155008000300940315100f1450041459034200c2d0106054130507420881d00c0003110000812490302c4215082030f00248244448030704c2ca440e5400040d0344142c5681555602c0111494400c211081c002c00032000200c030345c07120351010303030103200b0400414401d40b010711105030560085000315a0100924640400080c005824881c09a90101c00a0802030911141a0b4841c05203410007201c00700c550320451030304001c64a202d005205000c02c55000310340446005271035520b0023045010850f001d1268000401c44210074044505 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 857250494 1250 857249244 857249297
    0x2120a0225031a040c060318120201050108102a1205040503091804020f090c0c07080c2830060e01060f030317060406080a060e10020f04090c 62
    0x101c40005a9103982001ca0007600b001c03440ca48101c10801c10320002c1144280440f007940c0060030041130004490a1021681c0100540501654a84c0c051011880e0b03041d0462412198174404440a120703a924a0b04129004035000219400d0076104e00f01403041d051003203240030074940c01c00c690006010740c410010340c0c404842c222500e42001450840500c1d201030760307109a99031800007140c649801e6000c10782513600001d01e00d12070190341000800101811086132158425882a2164076a5900046035030380100962a40b1507044540c402403a001d00e02201079005e005155541000ca00d4010b50014044428021140703081a1074480e114108010081c8481c0b540710f0782c0001041c084507208142110840c0c0c2201840d910030380d108001081d8010940140c032000f40c0f28021454481c08000b0f8001e00703113544041281e010b80501030f003d10250303504c1051141900710036141120340781c00f0030030308a00c540980014850000d100620280c003003944a28401c880600700b11030b24000d0301203803920740c94031103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 857251744 1250 857250494 857250553
    0x30604060b03010e07051e061c060303030c0e010206071206081f0b060405060d0510050d0501090c0509090d1214040f03171302060c01110c0c010e1002120a02 69
    0x124014410740c20300744980940200030101030904c981c14000003a0b142d60400c51800705003c50351000c00c0c1d00e980c600d030440b000410740c5a01031003444c019610204c041d290500c800d4000c20710b80440b61401c50b01400080c0c90b00c0078168003a04590f61002d40a490402000205a005075604c000c08a040541041100103a650114100c1031046501401200750761514001c02d0056030180010009529440284c0c0c6e03d203e00382c000422983da6007800c0745100001c42c3d02c41d0382c2c0460a10f40c2c02e0180803044d440016886e0044801c1c8000d191100180300c81c0b2401901e08100030740c0302142d206601c034403070581d24400c441036030782c00f01e0b103007113040d02e00407102c0310665007a11621f90094100301019000800400619240038500c200d03858aa00540384401003140040c1c040e08001415102001c0300790b200306124800c0c000402e4032074100d01980e0740c0d03401821481030301184802c10060a10321f800c260003526124268002e123421031400c1000c224a420a084107410751040d07a14981502c510003a000b540d41d100c1c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 857252994 1250 857251744 857251751
    0x20616021c11102102071a04200f0607032d2a0206090102211801031404121e020318011b11060f0c010501090b122a03060406 55
    0x1600b081c40c0d524904620303507440f96183c44001020290890403402d000c0c2000780b20707a801100c92100040c041d1190b203000800d01d0170300703d5141142d01c42c1a40040e011b10b0280c04c8001c030180042c00c4507542410311010320340c0d1040c00340341d070071400c0e103041c03030041507060300c249080c000da0902c6220445a0081c84900314640a0811411a0704164000301400c421100d9070000c181e6000541020404058402c4000e40110800110201d15074000c0107815445040800d100102550b202c5140c075258002d41c04d50300c40504040e15440ea030758424080d0050070040207a843d1810b4456a6072121680400b841940602c0000c0241882d0f61005200b05541d46c1e1980d00519a108030500199100c4843c649410307050180e2814a445d00e0418030000d0314100c0c1d480039080c0d8003c201e220000340075000b036000c41e501d4868002070041d80c3c6007064204a04a400740c11041c080d40b0360040420100718101031401041c1d52000742d8004444100d9140302d1021140c3c0c003000421681c0c4400440d0800004417825141d60f0348 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 857254244 1250 857252994 857253049
    0x308031317090301050c1303020d03170a05061c0203061f0506040308030709150804030315090e0318180a0f06031e0b07090605040e0c040f060206010807060e0d02061602 74
    0x1001c3c01413a503c82c0200030340915011f4022a070f403403152001e02000e802542200103100c20180107588000494000c10b50300300040c46e1803610729000c1e000c210b84050041400d0200e210f8001c100721940107130300d98014082c100550700c1400c00d003c40700244404941810018000182d90b4803003c008101071401050350540e2450983e82c050540e00035940720802100b07140d00030148155020740259000f5034145008940100c50a8003041e500801d81c0281184614001c840d002c184000401003184138964200c09800040c400100203015000e000c016205aa0a0b030000300c01c088564040c015181c15070000003011034070781e1118440040d00d241c000c541c422110401505004c1403500d0240d01c48a249440d900301410004024001d0007544101c072482360601002c103201c010b29005840140c80941e1607400015900c0000079501c80d400c0c46071204601480d0000300d60b00b03202c0ea5014a403104040c01012440006500380011940054032042c40c11116000ba440181d40340e00c10300c0e07207010100ca22240c0500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 857255494 1250 857254244 857254249
    0x904090b0a060f03020d03050306030c040612051b030a080d180c030b0f0402011d01140a17070906091502030d0608070906061e11030705010c0f030b040b0109030803131709 75
    0xc0c1c254010703c020b404032810403c0180d0f5181b82c4c2010031607240c6803103070b200e4480c00046440d1400b0459241d40c4142061000314114201000c0c100c034150090041750001121001c42c1441000d03d000c0381c83d0160401c0201c9000319100340b00400c2408601c003800502c8103440360b030a4200ca02004805c0303c0300c1000b4038003001130040c4009080d401c528421100d150030f003011b50000e001f50300c1095a41d48041d5500540601c540e00414078840588040e00071b01b50380304c8800c50014020300305a030480f402c01b056a4041241c46105140d100152415900c070655041e0501c010021614501400507046200030000210391001a00401c4000c00d61a802070240508002145058403043d03040a0100b05040c80060880501c51aa080d03540c0582e04002c11110040303459141180f1072424040c19540c03d026020003440c0d0b026031580184040da0382c040210703007068400c000030344a81001d03660016051000038004104200c00440d0485580210700b1008007050f6079280c401030000c03801c04c030b0401c800319903c480760 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 857256744 1250 857255494 857255501
    0x190605030106031d0d27121a09030304080f0405031902040b010e0f0616020d0c090b010804080703080a02270a0b041203030c12060e0414030a120b060904090b0a 70
    0x10b100c4c01031544180112103006035443c40145044410010480564951400c086000b0f0160352007680c0c22190540e00e03581401010341c940c40b401c40b94000a0040390440b1250fa210b03442c014140d65020f14555200d60302d0740b41c03590b00031800d02181141d04010001d06940c1c1000700c1c1106682d880340b4108000150f00401c4101c03180442501d060040c0c0080f1105a903a8030450002031401c201c03066a11041c480b05210f031004c4400780e00a4104990104000034080518105d00071240e190303006104040c98140111040e20040d14001c204410900401002a0103111440e5018120000040c00d0694400800b0903000b002d29000905003c604030f80030b50343c2046c0100402502000d01580d00d4031b480d1003180e000030041e040c000b9081682d20402c00c141640303d08410320b0020314074181031264503161541d11001e0034041d0703800c0780d0200840800042c891808010740720441019101d100c4030413100300002001c1e00340d1294056114100301300c0c00000c0d0340c0781c3c4a8940203a00a20001e0514608058104202c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 857257994 1250 857256744 857256761
    0x30a0f0e040f09151a0f012025080d080402010c050a0b0c22060207230a09050f09120a0e0102030d09050c0307120c0315151404110309070e0619060503010603 69
    0x8060400d1744140b20792940315040410f00310a2800c20040c85062412140300b5401c0f518a40c950301480c450800c03c851011810020400c0400c9070b402c0650355010410740c1c0c1c01412682c24049195072001402540c0902c0e4124203040c0100241c64102c0a030350307181c40034400121454111260041960003181c40c02e04021160f4002050703003d00840d060000295840d042d41c880c00c2c001c041d82e6440300d84005519101000207520181c50381000d20303128010003007d4035040b204903030314002c10400103170180740005031000e03e1100c0c855400d2600c82c03510000c54041b015240c0301815448200500720700f9101900c80c1c0491180100083d001980700001018140005a809000380c82e040d28042004542d840740c411040302c0d40204070303060145054909002805001e04d480b02080e0320010006140c0c940002a02041503049404021210301017a80d054240000d80e894241c03039016581c140000b0091501e01900900d00134117503810601b0428000701c220740c42c0d0b0007140001d400440108100358150003200701 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 857259244 1250 857257994 857258021
    0xc060c10060902210613051012080a0305060d0b0103080c07080616020c030328030905160503070b120a020903030c0a03030606020705010908100c050c03070302070f08030a0f0e040f0915 81
    0x100b034204070002691031b611180502c02a165904040341c0803c214410502c0146541d800c0002010802d05002243d0b400c51b4007d140880c0c00e01d000119149131420350741280d99802513160080e83d0071038440340031a40020f6010a500c0c80740001c049100403081041da4400c0640043c05041203840d4400203050000b81a00e180c044d50003031084079181d880382047c0a00d502d4460000c401c81050308103040703000d801c8151015240703000d1001c1c40d494134500314024006580050341154101584d418450949110b0548200c0f100c0300d900e008030383c0680c141c0d00101400711000b070031242007420941d032681c140350001c1c1045020175030f940000c1000d2501070080c080107040c2402e061501c1841c1001c2991a02900d003040c1c00903542d00c03405450658099010b0360304001652045945600280c50003940e41c0e55140280d40f40e01d044118006110b00303000048400003181903503030355640708403190261000d014940c40c8540c46034403080c41903489139140c4146440c003401400082d04a0000400078021200300f0035aa84 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 857260494 1250 857259244 857259307
    0x2001050708030708060301140a0507020105090d020c090402040b0418030806060f220902040602010e07080c0315182a030f06070c030201061d01030c080f0c060c10060902 74
    0x2008900014207032980040d607810704c8140da03582d00002034010040c4407002c401c280c5514050142c051801d5103c0b43c80390003140c0003001542c6560b002a99101c51000241c1c0c0180e0103410039030418144a0f041640051000e1f10218080305554001303002e4448600c20402c0da42c0d032400203d82410307404000503030040700c156102803401ca0030702c070302d02404e00c1b40c1044103a69a403503101c07462120007058441e000400301d401e411510b807500c900c4000c0c068021410380001611501c40045416040418500c03110000100184980b886101340483e84100040c084810904d28003c0d40d02c02d19400c0c4000505038803c2d00030a0001c0740d80c007084200890044220900a070b10041d0304001c1c2c50b03030010700250004d06174280b80da80749019140c01c90150105412940a020740c2d00f8918a0060000340124140c130f201e6000e031409a6200c1c59040d5840d401c08042006541c07081c0750f44181810120b0083c01010b104005a0b40034480413034000e0b054942c16440700022a90024a10318144082000400d14081703440d14003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 857261744 1250 857260494 857260507
    0x402010c06050943180506060d060e0402040501061d010806280509060d050705042703020705090604021201052e02160e0121110607200105 61
    0xc19005100400500280d502d4002c160a02c0c0108541d04804803807a010100070501003122040501c0c10f89500d0400341c281d0000e07030380f0038120909098142d507582c003100240d0268424000b0301802c00a80800e030800d00420003200440f5581c041c0340702a000c0060444124180346c810310003120016408207007040390030345031044110000b00030824001024030f010701140c1c5480b40003e90a4515843d12018442000584102d542481c8228011140116100300c003650310031091000303203043d00c080100710341c0190703074140f0039450291711684540b0001e012160130440c454a2580916810b20401d4016a02005007000646416019075505c008255001d505004a2401840c528030781800b682d40f03c0c1040c08000d11810412000000e121445400c0c0d80400483d50342001c0d41b5100000704a220b02105500c001c2021405a142c55040790300741d81d1445680e00400213250440c66810308204c8483d0a5882040b107166607503006030030410f000700c0c41c000516868000c446500c1505807005810300800b408030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 857262994 1250 857261744 857261747
    0xe07030501121b09020408160e0f01150c080d02030a0501050307180b150403030c0b07021908031008160f050405040f140f0d08160309020f040c030e01020d02120c03040201 75
    0x4244440d5100c226001c00c3c0009011800ca01001a0007101a642c80030600040741c0700300080b48101c1203101c402c2e400c3d0460b2200d98074a03151104131014420016100010002400c2c120a06040e20510340380c5801020b140b03940340302c980d902400c0703e505003a0300031060050180240c45600e005000c00c034010407400d413628080002c44d0041100b00b1040c655182c0b000340e07007a2104c01840b40d4084261302c440e40d42d144c4034900030b08540c01002d4150b8002d0b840301e000620f0503000084040c0081c010300b900c65900c000e90307501c81950358002848148082d00e0000300060003041040410640c640c00141110b0150030050301c0380c26007400d0f80c0310921076400c00090202040c1c0021180c4182a040005040301d980c00540e568135200903e58249224171409044a44032580714034124021801b038210b1100c540d0161400300c3c15210301c030a01a41c005030b1412030b0710041c6007030741c480302d0720528074100030850803950740c500ca089800c00386001100540008000301e48401c0c0c0c0d0591640440480310302415030070103800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 857264244 1250 857262994 857263019
    0x907080a0209010903021201140c03010803070f02030c0d050c030d03090c350109030e090f4611030f13060b040203071e050c0a150e06100e07030501 65
    0x3410160741c0010954516445007056001964010f4507080385904401030090003490300200490540340400e000c0b64650803468202c81c103c8005a00039400c00040b81c45a01c0b016a10a100b2640340c41072000803035241d124000c110748028090303409800c081e160441854140812403142070101842d000030000003500b0214007000b40c0f80d48002a09085111200b008014800038000040c550404100380601c40c905400c45d0000b240f19580d003180c03c0081006000c25000190b5070448005050b0b03002950503c9003109601c0800082c4918040f40303c85c540003410690601c4c443e074416070321101d00c41c00305460540540d4400200c0d03c0406803451804007440d4a002c80e016145108108099800d10107004241d00000201100248215520b08007024054021800c4515442c482c9409020205020303000340c003a02c100703c001d403018042018680c1d07035170800080ba202c550610a9503501001d8021541005254800d01101d4000040b041c1010400c50510360010403603800c05040000601c150344a00300f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 857265494 1250 857264244 857264251
    0x40507030c08061302100c021c020a0504560f060712030c20010506030606030304120311100c0c030207060207081b0315040503030a0b04090807330605090109060e0118022a0606090708 80
    0x7003181c0307603080500b2585001c4120300d0144900010551140507511900c4ec0c0451114141100c5442412405100b845054050208080c0c85a103540c0039020855020741c000490303c054502d8401e0754a01c03006034a070200001c4030b01c0c00a15070b6582c4100640c0d42401c02c4801d4000c0800c40054ac2801d24210310710440f03170305d0307020001c0c208108018401d145690401c0303800808a040d0606010782c09034280010420110044160010312441000081340c5001181c110140c0c1c4542d009480041c58150740c0444c1c880d800c4840726018882c00d0141e10001f4620b002140c0180d22400103183e69003062481c900a071403200e12428030549c07501c5440e50008803544200d45405a05c14030603044e040700402c1c000000c0c0d9012000c043c41c42c0307916000c0c03c2c0c00801d641c00341050790021110803440d039880f002c01b201121218042c4550800a090060048480c141030305280c09025540240c5040d00310345141400300342143c9040c0c10841c0d9190b00c0b0903c1e56040c0a0194409001c0c0e80040c0e8929024400519500b00036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 857266744 1250 857265494 857265551
    0x60408060621010207060b10170601050c1c08100801020405030607080403051b0d0921080c120a090e07081308031509040507030c08061302100c021c020a0504 69
    0x20b1002400003500d10300140e15503288a0086480e013803c0d080c86400f800e07070030a1031481110300091500007180a400102d40125110310300c0a07040e9181401514181d1200070700502038451241c0c9602100e2561301000c0228002c3d80e00c0303035580d04012800702d000c1e0711560003813405640140400d0000303072400074105a1024103840c00034002c2e159130034255154450f0b10b510440c0b0714403c040340340c0b44480c001403010406c8030729521360b600c5950342d000600903050800c02032410b80c00c080c1220008601034101400101c0c4080d01900d440c00900020084103500000b0104082041060100560f08905a185501c21001e040510803480d04000340b403545040c0910081410b60044082846607900c440d64107100d80014280440c00d041506142d80c0c1d403200e1b840100c6803a881c2074404620118045116401180854030030380aa11030f550800040c484410440c2c010803000d90741c0c0d200565110002c080a82ca04c100e640900061107005211403422150041400b8a08003011045a03c0c90011220300c01c4d80d50f03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 857267994 1250 857266744 857266759
    0xf17040b0606071e02120c0a0b030601050c060901051e0f04020415050a080114090a051504050c040903030209010e0a120f0f050f07080c090115030f110f09030c0604080606 75
    0x941c00020028042c002d07025108500b041c0c0144004002c0c00040d504041c0200c48500101c10b03010900b507074500d207400150740c1022400c0d2003041703140c9015000d1340c0c001c5414100349040c151a00c40da940340c540215036000c0c0581d104d10a100102c8204500d01002d1211500c0040ea5031404043c0880500005030000740034540e15040b061201840c0c44143c80609030080000c8031140d41c07510024083c0c00c801a1400a03110444c0126245000c005280c0e031038503500c54050140384241d03c40c03000004a00500c10b444500410781820712980d21480b6022a4a00c039880041e229821840010098501e42441d58064400580180082c1d079002c0842c0341500c1d8001240c032003040a91070410104e10440c0802030080c46140700303020800e80089842d10a4480003022078003d0380103602080701503c8284555a01141c000c0b500c4959039200c1d8004071031100c0b5601002c9200743e02d1060148665000d10501c80540d1703808111080c5d6847c0c04d00101c680c01c24102c419908150501e2021501c03040c3c040c00030b900c11140e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 857269244 1250 857267994 857268001
    0x908060403050405061b100b1f0903030c15091a070e01080604090213060b0403140705010e10031b200109120e031609050a0c1b0308090c0607060c0f17040b 68
    0x30401040055035111b03000392101e15903440b12040c054010700c08601d1240059030380c2d402c1001200003000d6805036250762002c80b2685913850946d120003000c001550030301e41088160003404050b0040039549407141e00b001d000c00c0241d00c010a001da8000e4056001c04c80c8080300582c142c1e03800301f0f066810100817100020404900e200151581111400010a990070460000b9044485002800450303001d490081f5580b050011a15100c410601030345002c6042c6003041030082c01c00b001c00f5000d520300c078240040d481041d80d00f0b007074980c2004042400012240050314a555095251512400c1c0b9021b0083c0f00b0b1641320740d50149404250101c1000304010199880d00301d580404c0303c2c00f0030341256040301c944144ca80f80050080c04044403500d00b01c44c2804901001144540d0545590307021010903406c0701c440c0307507608803201000640710041d90b00c6003101c984c0e8150b0f0740c080103003201c0c1d00c240000221742130080c5020b484842e40804040a00541c49032142107440d807080b45652003a80b11000d64003954 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 857270494 1250 857269244 857269267
    0x609060907170c0406090b03010b0322020603040f110d0321020f040906080c012a0624030204050f01080303040b0c070c1206050c19030506061b0d090806040305040506 73
    0x10300b1144141c0302090000c3c0f09034192541e000340203442540d0381d0a030020345c5a40e02031f100c0d48028420403814030307003c00005540009000b01c10824000303044035030f180603105070005029904141c40950764086e40300e030f0030300400000045c0c151600748180c6814410078016180a020740d0015400794a07950446042168215084e074100c802158210f00302903100e984602c0484010001402200b10510076a2040352040d0302030f0300c0146408421400c05807210304d0003c5401204d035a00c1004403030302c07601d50903a00c900f540d900300d01016071041d050300e01074120325500401080c1c0300042d0201024001e605d0062090030350100840e075000d82c004100c80d4841d00c810b4941c03d02480317050380c0079004030215540402e01c84080181031a4460051300103100325102c0561401e00780c40f6070f5003034650480e0318900c1c900c03506010b60411684000c00420050070a51000307030f60079440d851000c464400b504000300768220b1a03080034030700d0060006180100780515140d03401404c3c030311460007403500c1130788082081035080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 857271744 1250 857270494 857270507
    0x613060b0d060606020604060e150105100c0c122607020613030203060f0123130b010c060905010b0907030c02031b0f0d050a1b1a070903080a0e13050609060907 70
    0x8582c01682001140e40d82e031802034031107100b40e8040b5a000c2c00c2080c03095540400003620502070070709240b5038a039031b441e00040203c10110000414148440e07043d54001084e41040442d004050003a0200e03116107031460554580404103404c100103280e90040080700540d84801d8039030240d07041e211306544595010b04600c501c8180e50000b9450300c42c12042020b1414103080e1036041703800410aa8610307150803c003d02e41094020b007040d40003000f0345c01d5902c03a04682d8008030003103101818003510002d61070700e82c8401d5442c0c00303a060724540e44440c240b003018200790020542c4250716150030040d00e03c0c0d4039802500e9200b41d4030b8000c40d03402c102c0c03c00d00070707400e007400f5101c204800172084030001070a071074000d44580c006c0382a40010541c03041240300c40c4054030243c03000180d03004000d80c110001004180043c2200500341d9010003442050210000301300000070000c010325511020040350510701001050401d01d40041107490406c002d0101e9521561220b542040040b03070017120f250707035100c070454a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 857272994 1250 857271744 857271769
    0x7080414060702010c030516022109030a0c0f080622082a0d020309090a02031810020403021e1003050714041409010e0103210905120c040e0613060b 65
    0x16001e00d0041c0301005405510592040c803180c1c8042c03245a032103c0090380c0003c03c140401004d40c10002e0b18200101c580296400e04581e5a600c941c20000d0702e00200e440c0c0040050100c0d41404004420b0112440c5403c0d41001044114000d182e6890a0a030010150311100d036810a64104d40d85e0600400c06d000c0c059685502014010b0010404162000880c0c840c044e005210540105441071400c188048202c61301000c000d4101e080300d45800403608000e510041170052001094030702003049503000d102800c16175180d904056110303400c0d0300411140c40069513110002c0e44800303003c2500b54a0303101c0520f00081043c107002400369a01503042d59507401c040c4000d071800c10001004644900c0310090f0000000007034916400c10303038a516051060001c20300001d4400006c1080852401d01004080d24a04003d443e09e16a019620008158a103610030300240352504101c01003041c1d401d2510a82c210642d440004044900344141415401d6003e2780014081c1a100d501d01071283d01c1e19503c2410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 857274244 1250 857272994 857273033
    0x30a091514070308041a16050c120705030301060212190e014103040b01050d11151b0106060912020117040605220209061c0501051f060314070804 64
    0x2a0b452051a005014000840d400c40d1000c00c00c1003806004500c40750014490300c401091245840031250050310650013022401b540c0348601005500c041e400b50000d0312480d44542c000350b4603541803031006401d14a0340150403142c0d55003032140214040f00007213a107043d00380a082c803c2c070a0540c000104c404005030040d0b50300b030b0020004a280c0c4001d0f8190614202d810318000e44c01d45251107003c104041c403041da0003504900100005010798544151000503903441040136402c210100c401003125129002c00e00e682120340032031203a503491180c010300c44009064400800102d4104a40a0000c84680c010a9102c0300c40d002d805003164081c0c000158925103254911080707191038585040075000c203c43c0d03511221040c030024050041403450182415034020070116250742c0d450f062000040304014a440343c46c00384e0724084041070007032041034020039424040300e0700114249a00d0041000c164041c17003c040c81c10703c1015541e01d081d100700d81c00041c5407070000c1e41a22a402d01e2945460940000c11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 857275494 1250 857274244 857274247
    0x309050606150d09200d02090114060d15150527030a1b1401081003080304020103270b010501170105040203060409150b0a0f05010c020f031018060e030a091514 70
    0x13004c1c08403045410801c43c14202600c60355005003070501c41140d0402400940000c0341e403006000c2c0302d41007182248a083c6c05005030b810040009501d40685040c000814422541c2c2c6006100e01102454144a4181e0b00d0030460310b8410007041990400d40300c0c0250036100c0e0105101c40f00e41d55000c1c06464a0717035400c0400e0040b80b01c041c40000800e40183d1045100304182000101a15406035000502c21000da020b9203200074959110400b4690000340124101542d80b2003120789034203050010710b403070400a204003c02010f249040540302406821480c180041c20360004000e450582c40c40381900c01c25a4050b07140e032502004031307029002111000308000824010305d9856001a881102d10780b9040303507003140302555240140300c400751501a4a000a000380d0520002d401c000246401c5e26402804407401c48900902840c100c80b607441d1009003441950b8403410522205004107240d002c010400317903240041c8030b0307400342c500407151042441d0355030f90110b02d2003124091701031008680708800d0701c01d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 857276744 1250 857275494 857275511
    0x60916110c03160e090d021005040512030901140106050c032a01140f06040903140306180106030c020606030d0e0112020c12040504180206040b0904020708160506070309050606150d 79
    0x43c118882030240060190404002414a4100003070443d403e03c09500540101c1c907a441c412005040c0041c003d032a00e100d4810220158080d000c000c51103002081c0c000a045c42004910803280030060b84103a0030040c09000b030082004000c4201c41e812030420204610703010003080321007040c2c400e001413489254a080042035952401c0508280300e0300983d1404400c03661070500700001c6482d1648007a0001e03c40000300405100c0c04401140c2060004089000d040f405905151040500360440c50000e92610551f43c1c5d25601040159000700046002d01510480000d0050202c07100650041c1009100d208841c201f2500c5d904076040c60040c01c044d12591885000c0c94045648944500d900841c544882034282c3d11082614614031540240400e14041c64240d056030b0b6600401d01e090350080e420480c2e0000111100024030300ba11144480320360880a50506500708003000f0200c20505003008900d50000e139001c285203610810484041d142041155030340d0155005098501142c03910b4841c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 857277994 1250 857276744 857276773
    0x10b03180c060703050c07150903060c030e0a050705010f172a1603122a031401090b0f0d0f0f060b12330a09110607080c06060916110c03 60
    0x92255403086d00441c0c007181daa560018041d00345104104002503040c1c4401e03c0050003641284039007174030614006c2021118451207a04111f4004011141a070103c0740402855811909d120840500740c142586915490042ca40ca50070005044c0d100641e040140c00780300c0000000008110001044910307100d41c1032010031118013a0320038003500426a002c40d100d880b400710340601e01070784090220b0f00d005200325004550712071a1280c1c4081c180340d02c50407000311070810707078142600a04500030701041c40001c0805001041a0440150703001e40070344411440070a07040307100a90b0255000203101d00031651418003800420202d0215039116172051a2a841001d0001e400c20038900100b490104190180c5841010b04855440b0990f08103801c0c0001040f03100e960380562400c034000c0c0998403c00d5405c3c00005c1c0c141c0d01c80c44085440000218002c6241c15041001b158403440c241c80503840350400b04200100e0030100000c0b241000340c10803443c40410303800d000703500303186070301400f1521142590389a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 857279244 1250 857277994 857277997
    0x321040c1215060e1302010305250302041a040303050403170d06120212010b03071406040f0b03160306050a03110409080a050706050a2a050c0a080a17010b03180c06070305 75
    0x1100800070f041110200b0315802141a1600130340050f004c07421091441e50045d8003070000106018007003d641e0040031842109200708420405c41d51b64016552400c02c540340c0c1810304105c1d81c942d44075006000900000303070848102d4055981210301f801494041c03200d6075100d03108002c619940340d41003c00000b03000e1902c640c000c0205100b01c44c2c2c0c107081982009258201c82c1560010344e4513074002081003168201081c100940840301034000d5141540f62441c030040c0580c15806040c03c00700c00404c209042c0d40b60100e540d080310761481c1c10b0080c145030030b00090405105000142c643c40b9406980d54650741c803a8411480164001041601d071125500007800503003020406996140c08c280c001136100803507202e258001511450480014212811108143d0004c0400c25081c400104002d440c0c56204100c0300818500c00d0000554542c11408014009155104c042c21710074850700060050314000d50641740d012181103407020b00e4003424000e00346860050030340341c0e401060000c1d503841410762090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 857280494 1250 857279244 857279273
    0x3020d0b01050108071d0d08091f0f2f0a200109080a050d0c0201110604111002011e020c030405040f0608010b011e051e0c0604050c030321040c12 64
    0x1c0300c4001a542d070f2102520b04024411071b0084501c4607030500c0a45140120000030305c140110245410700782551302140112503400302c84000e08000d0b602d4550499131009080000f000745241207030700c061600101100d60706071000c92007001180e80b0360301c0b0f8100d02d040140d0300b007460700f00c00703828048481200200400d40851000c00c1c0082c009101c0800e003120300140c42561150f005e4028200c0103890001100c0402500f1001c904200c5100d12203e00c082082000901460041c1090600081517604214107a40000340b00015039061081c2d01c02d084001d04004290032100280159950300800601ca003580b10310f811043d44140f83c0302c501503c90310236510102c140c3e2400c00003003220112890064a07100502e4101e1000c1c5140c80d901d80040b01e1150010300070040306e410000c1400342500803035031069081143c0900280e48000d04120500c070003000000b500a105802070f500d000c1c80403105100702a58020540214580c80010501f04950984440d004000f0101403001c40111864840d0500c201c08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 857281744 1250 857280494 857280497
    0x13020a080105010f0f0527090a02030906070c1e03120c030b0406080303041721160f0914271e06040204060504090e010f020a091d01030201020604170403020d0b010501 73
    0x441d0100412405031544017401100c949a00342800101d0030b681042c5280c446662081580c071040311006501e0b800011400707105241000368132868081d480038584100140380d00200034600c4020720116048207841300c5801c10188030144040032906080d00d020700d0f8035003450540c40c07070642c25125060340b6610207041c1e801c0481d4103020142c0e84000b59640c07804290b9000e0200d60000700440c02443c1400e004011000c44041e0540020305d5a05e8509210a03040340d100440744a04468040d041d6404084810a0341c1141814070030039041c1010500c0c40104052010300655000c4008042c860f080c840084401410003580480c92a0017280c0210540d105400c80340c030311844c100850024030381402610300351803041e916039003400d180ca42c0a4014240ea004041d00710f541c1c0b005044010b11860000700070b01d5105807120f068107442c01ca0503c901148007519070381a844100c1c01400141e078049400c0b0b800c81c0d0015220f184401e9191129482c911540c1d10080d44801601080c0c01000107240056040724001d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 857282994 1250 857281744 857281757
    0x60608010f0b030106081902120103060f060303021c0210112703101113030c1404020705101d060f01060905040e0c1302040e0901020403120f0c06090213020a08010501 73
    0x2201c8000081c0300c59402034291014007400180b0146100b0180f150380000149030801d96020f5070b5015908991000c21000407500c5124010310a10259000310282d580d031201040050519640340251103070354401034600000c2d0380300c10045008d0310030409040b41814541d010045c00140701e4266005512407d2503051090800c0068980c2c00340603425030302140000340182c4054890710620500070b00c04a0145100350106011401c0e040f900380105e18040c3d84070720b050150890030007154141c05111000c005100d02d00403c148000500046074070625001d0300e0f03c0c08903506d5071000081d1036040e5070b683c03107001e03a1048408200003600c948000358100d035007940b51213421540f124203000944049000c0ca40d096032114020030b4042c00c00c4c0c40c1032400500f90601c010305240d1103220151010000741c0301c940c45c683d004030703051081c000801ca10104041c1581400340005400400c040c0c490245210040c0c0002d81d101c0d030240c10340d107401d541200c2d0880c540c1e02c110340e101d4070114082e101c80428020280080c04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 857284244 1250 857282994 857282999
    0xb071b141038060d15060e0411040b07060b060d2301050102030a0f05090d0c05030d0201090b1612020a17071404261218011b02100e0303030a06060801 66
    0x5000002c500c000505002107200c52a20010b28050590b020005822440821a4203580c0c42c20b8441c040c80c46018050140040d450b007000100801032822140b80300d2454565041d921500c1310341141c0c00c80b0060a1a151508400c1c10900f00400f080c006680c0c001c10005101c103442e04003070b44140c50b0742c81100340300444092406550307410f85409015407805a4800c00141c03215600809a0301803000c040d00d04549000700e0200480c080500060044600490283c0c040c00385240501010785030300b0040c8000c0181040944851481c18005410703450030f040c0c02d00c81400700e6442075082c1030300070384140c5095540c0d0400901c000d22400305010a0100c00b441040801e1126220b007400c5210280c4900225081078141603603200700c0807030886c44007070124038402c0e944c80f922014000c0c505134011100f0040d4072241c5c0f075291a182c0400b20702501d0f04028040003080159405404605d0310140c054820140940700b458054a01c40207010516034148070101c01c010040003203800101c00d44000e5a501c80f07590344d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 857285494 1250 857284244 857284271
    0x20d0b010f0f0f0e090a0203121b030a0c021017011d0a060b03240910080d03050c0d0504030c0f080a1211161e0506060901120b071b1410 60
    0x46079000b0b000f07484964000800405101d600000d07040440901070741c14901300307a40024640740040c048860b0268001c00d007544101e02213184841c02c00301c1c4801942c41c050441d90010a0034420180c024490590741d1807120100344100340319041d200d4500300c1c0e4070a55031070b070300600c82c1041c95150f2921100c460300e00042c0c1c144114006c03581168194949181136032503068503461034507828032401c0030042d40814404031a6943c004158004c0f0152191030049609041c00c2c2030404043d500310034241400c0030305202d40111510102e0385005a481000159516540303000c9a10a0860101402c410071910600003405800c074000c04202200e601e030303400c5001ca8070044e102500c1c15480d983c0600070081c041c00e10082202052010050721604182400d882c40700b040d00030345800d501d402d132495030101d0300300002d80c20070f44801809825003c184924001e400c0e40d8401d04a038005003e0010010a403140c0030303070b10307108610700806950b0082448418001840d03c0d00d40c1c581c800a40d04a0721818840581d002d407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 857286744 1250 857285494 857285519
    0x406060f020c040518071e08071d07050f180906010306030c0902210a020d11070f060b1c0f121e2f06090d0801140108040f020d0b010f 59
    0xc0c1081d401410329222440d0821004100c010521100300e4500e848040c02c0c1e6106000c03e0011385081e949404c117288441401e419010002e0b00306442a44c0f14801c00e201da21800b690444038202641d8440380e25030303185400ac0700c41d80180b40000c2100100401d4540c0001c0c840f403c88511064252074400555079041e0044094412902c005801242c50766001c2c0691301d6950000c00b500585003849140301d40300c4071512581c03401c0807255004240c1e800300741070346540980e004448070744d01442e0b14036041000c00e07100d00e85200d0811900418a81c1e662360204065241e11000c9001084024035510f0020002e00300b0003201100307400201c03020488840071540150040100d0407002540c0b18507415002c80001007511044902d1008000d08190680015054010340f60a4010710034402e010f89801c4c03c3c0881c12034a03109640c03042d4010700142c5001440010a041034a08400109181c010200e8446082103004c500080708013a410804a2480c2c90601c954039a20504035480b4801a209982ea03d0036002000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 857287994 1250 857286744 857286767
    0x80703022704090203070f1701020306010518010207080f0d0327080d06090207151b020d0e060c030a181403070902090f0316060f030209280f0e06040606 67
    0x5900c040610401c00450440325041d0002420006801040307400103841c101403136010300229075030000e0600014044542e0485c2d420310480081d41181030a1300080c0c4140212074041206543c1d00150315240ea00c20480503000b0494001030b60b040480300e00c810b540351000719900d080804d0500b02000a004a017001c1c0001141094282d19540b081075a223226281e8031150824010030380f181c03c0130801c002184020052948520040c06c01d80c030902c0c1c2444243c403541009034221a1407064552441500401c02941c482040d1900d501c03039200c803400040e014040d40c2501081e510010480c0c09241c0e800607201c5121418581211a60039520a080c09503010001d01c01601078204e820b04211001c01034011381075442c802040c4c0c980b01d141c4080460f01d09001805003d40b02980340d003040181c90780041141228280c14942945440d40341000300d80c048510a4103c10510501000445004002d00708040038060345040c5138080c507983c264548040b01c1c2074030501c1c81103141146c0041c2d000c3c09032082c0d00700f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 857289244 1250 857287994 857288017
    0x902092704020d0302120f090f061206041d01050a021e0a05040e1306021801031a0904022404031110030501140d08130b03180d1b0f0c0e040308070302 66
    0x50755119070a1180c104800c44040b41940b18240440040b00d04c4080076080c42c0707035042e658503110003c007000c00c10038814010103540141d00802400c61171148510a213540050265000314220f4a04034401100c08444000c04001394030b071900740000b0022503001060480b00071043c3c00740c151800c40002c07119100d403540da0000310703c00308810081c010000d2102d07a0321140c490034080541d0007130b0f01c0d040c0c10399100841d40d4003024400226181190b03007512801c80d1900d800020380203072a0648000c1550744002800186c820120a4030308400e481c1404840010140201d0005413181c2d5245000503444620b244110f100307003c85401d0034001c0e4800c1c4605412030b003911fa52510700f0740c488010710a070842d06050075030300c11000f009111143e002451005000740140303081c180c3e0705c0ca84074940c401c484450b010040703000d40001468403103440c2d114111017810b05004051301880c034500d1404a801001e5400d00a04058144038001514140700700d0042c8030b14000e8440d954190b40310b0004500b00d01c18aa61000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 857290494 1250 857289244 857289319
    0xf1b0f0606100e040b0604030b0f010b0a09030305161e050c06070b0103060b21070501030501150503040219032003060f0f1b0f0c0d0909091106030c13090209 69
    0xc060b100710382c2000f20400140000609000c01030100d2035680c41600142d460706200e50600c582c50005100c07071801008a002903070306000c48410002d01d442441d1001404110003c2200c011142d100d15141141542c000401007001e03d12203000c17162303408095000d40b030754054145803001c0c03800c00400711b0303a80c640d014040300c000e0780c2540d480b8802000c400307200c1c6400441ea110741100150412000c02c40002c0110010441585043c00050686405030025015844040c02c07000040740c02800740c0f40c01c227a0480d50f00d8070003000d00c480294500c040b0b03840038005001c143c0c2c03005c0d0100117050b03100c4440070050702a141c080d6a90300e80004840c00076140e002415a91070b00081d01c0b940c400c24801c00f0103d2560f4101c1c03400311344004030f042c1600315801c003851a42042090782013181e0852106002000d89020510090400b070302e0351407031440c43d02d0b5503c2c06101c0001c0000c2031080d04804940c100e0040d24009518a504e13108150b0094000e003901c2402250400f03d07152100301b66180c0c3c1c2100032840c07450308 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 857291744 1250 857290494 857290519
    0x121a01080d0c1401090203060a1d030702090103080a021c03090614040507091a13150608010b090609012d0e040e070b07020118030f0302070b0c1c050f1b0f0606 70
    0x44500f6821695501c025580e0314000070040c1d40601400b03003e20b03120b100103d0303080c00608211ba000a9a40100c9070345500c20400076006803070303544082d411250442d850f81d0b00c90520840990508480b20b1001c406155410360812409805501160a0034050130701009601e5203a44000040b079019603014105a00002d020040e803101c603000031120103000e1211018001d40030001c10700065a18118048442d218404845111310460070701c0001d0250b4505030045514244281c00c0c1c0e4452424598041e5030002440b16299010b1014140742d40ca0b610540403520000d500c5000c0d010b40717900014400504403458050041c5440d006200e945131909002d00b540e51b1520180740328542c8413640413814030412020030440c0410400e1000d00660150f9510705000c155450001c0c203100031a0081041c8440a110106a450001419002d60300414011010700d000700801541d1500554980d941c09280000d69000502100040c4a00090201e0100c411320040f002c022502d511045890680011100085 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 857292994 1250 857291744 857291753
    0x1030c120f260c1506040c081308271f092102030d050309060a090c14040f060b1b0a0b06091906060503041b032109121a01080d0c 57
    0x100c51482c56401d41000554400d0003180045030801c1406030320750b40000075010307a20f0300c1002c1070742c0d404002141c04002008042c0300c0a0b2402d40b018100c1130309000b400141c4002c22054000715400c0c41503075620300f0050303440031030507208020802d402607001c0c0c003403030b001c050000ca5060400080c4108a4540840050a0404000d080c072004246064441103540305900507840911400081080a0303869aa80c1d2501801551904902500e42c1030003500d8400b1010108102070030080a41e400c0804540250f41a200001e001d442d51040c0052018641900001d928413000018440040b181c40d25084401000003415140c008404c400340800f961000010028a40400400da218000c130030b4910411500b103004408a4401d50403030004150004103100900440c0d00711207540d408840f13078851446042d40e4801403140e4505500e652807910304414074090a01640e00749000c0d061500050201e03a140e0b05240703507c04a6581a0403c944150002080c0e0300c401141010585541c0d44074007162000540d05e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 857294244 1250 857292994 857293013
    0x1101020d0e03061f03080a0c200d0212010f0516140309061b130e0601081321030f1a040c1d010e060c060723092206031a01030c120f 58
    0x410444452007104c0800004c0d880c4e0702604001d0010341d152070481115150001d07a01700d00c80d8202034a0079108003088429950080346003400b507810740d106040c0342e221103050b9024060703006000c0030b91420030741007044046032a420700c0c0c2228400c1d51003003180d1a42030040c08061200359680c4080d034200c0c400080c4603607a460400a0280180c1d080369140047c40485100b5802c074941004910f4520b9209107d003079a440318010341c21100c10820f40000c9100d40c0e030380a0700403140403401c5081820b03807031100000d180a0b82c0700122008102c04207000340e01d00e05151134142c0d00c0058490303100c0d600d0a0a214500c034410b80f44000e90140c0494007107001002c2d40010350301c4c03e40c200e90641d8405070400c90345c031024006020f4140580307402e458003103468080755401100b800030820350740c21016040c018041180c6d85c82c03040c004001102801c1e101e403200e42d00c4982e0042d10b1103800140000000000e40040c00d03251050385030403240a9100c02c0c0c8003540f0348c00b0030000102d610401900354032641d03e4400c04900c80c04d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 857295494 1250 857294244 857294281
    0x5041805010f0e19030509060309150601140304030c081b0616030b0307170a060c031a1210050a09170307030b0a050d150615030606020f0304062003070b041101020d0e0306 75
    0x345170f4141003004000583c0c9500840e036031400b030b0b00f054030034bc070300f0200d2a1075103900310109091200790000000c94402d9240001400a01001412a50300d41402856405c40d128651040641801e40c9075500c0e0203640c503201903a0038540301507507480201c0c4142c801c0c4181c0e90841c0008002d0b0912a00d807032413100070000e54950a020740c0c003501c4000c00010324948110030390007900e9100491101c0074038651590b00c1e095001c0b880e01640011b803c155004c000410803004209205000090315105e002840f00113046544005061440105500c40c120004102451003070030741e50f40500c00001d10340c0c14000d1040442c440c07030350800d81c21071107800040d409010006039961107030340010b02d4599610b407080b040c0310825050004660742d0b0400f80001030341809003420400c51a80290b2402c2d10780fa0780140245039020445061010410712103011380c0c814021036080300d4202aa41d01c9508003424004401501440e6050141c422584200f07200c9004001e100000307100200035088540d00c1c0c06000d5013080105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 857296744 1250 857295494 857295497
    0x3060d080d02130311040c2111040306150f05030d030905010e01051503150606030406090c0b0307032c0a03080604060f03050f160b09060a03020405041805010f0e1903 73
    0x740400452200d040c406048019030903c095150340e071860411a215030300843c41e45014500f0540400403264022507402d078143c004031151940d0120354010b203401401008655040b0020001d00002072120b640c0044842c50385990041348410354520200c4c617028940c0c4985609500203000700105103010f0303400500220301960001c52040b0485081c40d003121170403104084035080600021070182020000c440340310500038456859810044001100390000410017800c294840c00ea410030081a1842c0300d00038075040f100e440d16820b103514054040d1480454015400710100c81c8288941410705041041000c24009001d000d20283c03000c032540c220003403582ea001502d0388000a4801032003c42080214020800303000c05034503207401c0e00e041040010500d1981d26000d0418001c500c10802203070400002101c1c040c0d9070791003091058019004030740c0032640c05440d01880920f04041d54050300c50a510480017084100340c402c5110b011940b01004003242603000f4940404609131904122407024080d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 857297994 1250 857296744 857296747
    0x40303021810080403110f0601181506080703181a090c030f0309030106050a080d030c0215090a0c0803180d02030a23061b030708060a050411070314030c03060d08 71
    0xd01001c5151003103104140b0300000c2c08141080305265100701d00b580d04a01d0640078100040d01610b203150740c0c100600900701101d16820070001d00d844554000001004d40031102c0d03044540c4d07424081c01000c000c64200c0003003814907004400d00202102d84445556000051403a1150055240b07043c24100401683c0184100040c1060a68081060042c01aa813900465455200308103140c20740c0c4442d804540580c0e0840000d00801c580805c8880310700c80540303000141c00c030300c544080380383c10b511260340442c10030a00700b8800540300214548400340d020720009183c4959682c01039590784505054a036502000c580c03e1341c05881d00c01c0090044a00040854030000000c4d1103120103c00742c001030300c014be018a0300b5503190160030303c4000c3c4e2009000c8900d580c0700c00c02e0201106030f4400103042000304a89440011441da40c0c1550450140c04050b00810920b6a00c035203000440c3d110b11029004140a14156088459000300302c0f0301c5420720803c00c60450715540c0511074425070000d01150030710b90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 857299244 1250 857297994 857298037
    0x5120c030a09020a0b1804020c032205100e091005060f070507030b010e040b070309021e1f030203090f07052803060f0203070906020307020a03030815030a050d031104080604030302 79
    0x100d00c030071407000c2d10b45c0c031038595500d580340c402004a01a21078441805075005115420b003c01c004802e440d101c00c40c1d503040d403203500380c0701155029040017078100740c2e8003038800301c400182554018514202c0318415200101d035516017000701c44000f6070303d10a0307030780c07003074040040a140202c00c1d0302a0954500c41c1c03040780c0c151500ca580e0f0040c2c00320260045030f4480329031010001030108042c3c845070443c00504041021f1901078010480c0c241e0f1110400c0032074445124103110716169a4925010714403200100300c0001c00100009000e54400e50364110140324a1214508080c40840c080c021268028804c10700c1700d4640d00048035450000050320b00c004e0042c1c1001000c980c260140390400c1e5028100184e0b44d00d8480e0380540885000d42106085510a00105005844001010098940600300f01e0f003295600020800c140023180e1416815008240c400c00800c40c000403403080c502c0e030355281440a44052240f4202034000c81c461002180c0c0032401040c0402e0180d030040c08400c4201124004461 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 857300494 1250 857299244 857299249
    0xa0212150906060415140108151f0f020d0215091e010e150c090f1c060b04060509070203040312030204170c0102010c030209030705130b0a080d02070605120c030a0902 73
    0x104111603500d015000b80080003240e103400c0c80f50003046803402216101c501d0400b603080f0b8101d070341e4480c0c9034123218400700070640480007003100301000d85000344000712005000c4040a40c490440200401040314401041c03a820700106202c45104581c0d40103000c43c16015452074050075004c0c00c401c84502450345400c02000e842aa03400c070581032400042140b560725400940f0f4290341c44401c10b80d01c8060800e2002800c00380003107501c0180d080f1800b4404c40b50100001d141c801d12000c400d4080170b500e80783c2c402000743c030341c1003c401482c3c1100e08110311030703443c0b0900000724011101c207401600100400c5c0300050701600c11116842980c80e0042c1442d4407186015200c1e0504170304050b80e5400910b4550a81da0309000340d1050385190314055040544040c0441d03038070625401014030492141010492a000c264000380c1800d80090200f03408542c1d54a80a07120350f041800e10006002c0c0383c502091190003081142c40742d20851907060740640e030340210401c040d0000b820360354181c2c1d10b604040c4090ba = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 857301744 1250 857300494 857300533
    0x1202041505070b0a0507090314161706061806060304140d0503092a120312010e01030c0608130b06130501030c050301060f0b090f01052215050c0a0212 66
    0xd90154076059921549420a03070f91198000744160300442c1004100f01d000d81e8010007100890794441481030b4102c140b00d540d141001c22100900030900010b90000814468000f08511801c005000351011a12078a083c04040081c4000380c20100410f4070100d4080d090110003154400d010706040c0c4582c080080c0024100100c15105200150f008018050000300c244140c00c010103072a41c8014800d0040c041e0f030510903034030469051003840031194882c3c03800018030450b1b50a070301d400203800e92503071200008007800c0c901380420345880c2c0c0ea40b01c001c40c01d00c0c0903003002c1e4010605900308989020850307407a8040c1c58401070803603400a901d50910540540b84d8000c41c1e029520411050314401e007070170185400c40b03c455110010316211460200200d0250740e044502c0328405a43d040080350361500140c0e0948501c48064201c40c084011070f0344040840004a001d0b5001c4803a40240031000a00c1200c8500544060301c40c2030f005000104018585001d81345020f65408040c2c1c1ca01201503941016031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 857302994 1250 857301744 857301779
    0x8160c020a0e090a06050f0f0402040213091b02120f040b1803160915062703080d1e141513020c061f210201050405040f0f050a1803120204 61
    0x1980d1001d000d130820000c072805910383c0718580a03420340c4240340104682102c0a030251011340566400115582165904641c81c0090400c0190030702c0329094850940411906e401040001802000c4402902c2c40c0484122232001001484041c1000c0c14441c41040ca54444a44c000e500c0b5402c00d40c86500e514207001c100b24039011907100002c06458100c04030f059606c0d01225000d1040c1014051000c9500001070300240e090500c07582120401100c0f10307001d0050240c00242c0b011101140c2e00340700200f980c100d0403014030f5103100040640482440141074451b0281c00081500303803072f00084c41410400705081601c00000b0911045440c00c1c114520072a0302038591040c1c1034100100f04215214802c202034480c8480d030000e1588280303403070107980081da0301035602d9081c4ca03204281441075a1180d01a039020b0706006008121031030303c4101c50001000d102400c00791103420440020100c0b0802d21612030340e20200450b00007040019070702140d05e42c802c0121925415420302002ca03040c4000c00c107168a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 857304244 1250 857302994 857303011
    0x14090a0b0d0605090121020a030f080309010b0316030f020d020901090204290702010819020a0306080c0406060e0d031808060f15030d0f02010915150608160c020a0e 72
    0x40d9207072403090040940d072541d0400c50280e411480104091115034503115840c0141c0901d00d20281154030010301c04030b415500c041c2045440400c0501446242c0300154007441c901c80c001c22112140c1c8080c541c0310a8800a003441e0401101010804608c003004140d0104c0e03c01403681d65494015400602013000030381200490f15030204003031084400160204500039000c500c1e480110b800060041e4480c031030303090001d04005e0725001042001c001640304083c03c000340e9000755100c10031104010700814891180c1d003050700c2030b500711204e281030520450003518000e43d60704000c601d19200b070003507080d0f90b14030031010051012107402c8503070a210b001c0806000410041c21007414103450110296901404100000800b19070f0864a60f5002550070080407007410109194240c201c3d00782d00500142e000600182c0b1a04d262503c41074169110740c0d40300d00d0700e4244804191711880c08480c4c0817000c4401c12000140036201d07a151034050742554000c0762006000704845515054800401daa0a641020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 857305494 1250 857304244 857304247
    0xc03010911040f09080d020c150403031a0105031608060a050d0f260d090212100b030f0102361005070314180409050f1203060306010905010f0614090a0b 67
    0x6419140c240183c2d001400441c07014050301c00d01e07440b450f256200f075a1000301c03155800111140590000d02035014246019031100f50b40341340504000e809842c00c090f0403031210503155540141580100140ca00405112a402c80c3c0180501c40039a501400034014642c8249038050001e0b0340d54461901203040d9120724a80b1184412500e0a540e03280c050880210300400d1000040c00421581c0c400d039080040c449030041601e4425001003415448036050591071405a618856208201d58000c403001c0700c025400c5550f1441042035946c202d01031f68007428401e400541c91074035080069a80f00c405100003d4038400a4000440042c0d0341c05c450000020207d08042202c80c00c0c982c01503c248021030380d4200c15450b0562840c01030740c1c803640a003200d501c5196142041c0c810300c04100400ca82c070305203181c1120380c080c1c41301c1e44440b0290412680140300e44580000812544054050f080c121580800c02c64411800c0c0401a20710902d804240c1e14030010610040000d55980084840180300015216 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 857306744 1250 857305494 857305523
    0xa1502070e0901020403050a0f02042307020c03010c09030204091a0123040204061b0c081207110607020f0d260702011704020109180f02040602030309100b010e0108090c030109 77
    0xd0010701c100801050300c69106103c10004681c01148002c03000307030f00840c0d600e07400069100060003402c103207030109400d2011921002d0100e03445150f07280500c411307408480401c000c0340b08060a0b100c4005224001441c0c0c10307402c00050030190802c1d907800388503c880c240002a0b05070740a01011007648071200501440c0e00d081e01302c05407009080800752080e6400c1d89445d05020000e000e80c030001200510b408064600503091001141800001d04103a5040e20700c400b00c10261910b01d50002c1000b554070352032168400c415441c00d00201c960b411303809404025040c0c020010403000c00107000d0142c68101001c06540001119000c480003e5000c0003446074a4510900004020340c0c1180c042d8807411825805010151380c0029482c000ca03100c40d41008240c0c00510004006400c0030f0740303d21691400420040392040c1c0201c003440c410a0910215540e0036000301244042da428440c0c4680854071612861480354428000d00e5030001c010705c1244d818203e491b01103402c46508490503900c1030a420b006 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 857307994 1250 857306744 857306759
    0x31e2306100b040f0303050d02160506090c0406031109090a0507090507080703090c0b0d020904050405030d0e0312010303030b1c1112120306060a090e0708011401030c0c020405060a150207 82
    0x1e94018085001c061420035080004030000703011180406820300c580480c4a001501254040f41d00300d0741400c0070100004524904103a0304d1009032001c5465000f250001142424144101c80440b5000320380740c1c044540b0748081c808042c0020384903c0c0c0340c1c0600955900032880c20420780e401440180c000007031070315040300024100d2401420b0442054140903000001ca10302c8140d58042e06c500152090b6140c022088400091040116071038100707061008100a000010000e440901d220900074000e50301c1c1600c4407038491103500003019481d02c41c0030040c40400d2199101d440d555001603c090703102a01d00d0804042d20800c900d003145c098040065540c2681001c9a070b806140725080c004004010241c0d070380d00201d00005103424064000483c45000c07444c030580456001303100c8100007001e00d00b00b0801c002d184040074020110012207070f40c002c0c0c4c61944644903c481a4515603079142c011640d5608100107414041e000e1a48854550408601031190101c451700d4501240c00030a0610b00d894003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 857309244 1250 857307994 857308021
    0x100c0528030501060507030e010305060f120708060a090c0905130606140102010b06041512110c0607031815050a06051323040206090607080c010612060b030601031e2306 74
    0x4c460100030081c0044d5000030b8100075640004c0d54242000305090341c90401007021080d051442c030b40e0200710007110018810003c1000d0341031fa006003041d10390940d2420b25400c1550300c05440140601400380d810880c081d05039000b903401810614007800d42d403006482c0d08003610300903006a10f4050004070004443d40e024070a52407540344c1a240181401d01d002d64000302b551100c41088288640081e45240414081c1e2189145095100220340c403000c084090329512202122000080303403070f080c1e51004084060008028550307114507080d07240c40c8040c60407006844081c000b601c2075900d680c40071030150b0340c4424144516100482c0007454a0148214040c03110402c8458907940c80b0010500c00581c94160455400c55030a4881c4c2da075403a100e14000c0d919219495250342c07d5482e000d0041848250340340c0da802e1042c0585c405000c840481c20030507450340301c00e220060002280800c01f03801c05811119848030b450007145104038110040900c101002c3d44500c60415070741191080001c980c40881 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 857310494 1250 857309244 857309249
    0x160b03072705090f06100309140a060b0118081b010e030a0303050a0b220207021201050906040c0b030601020c041e05040b041b030302060606180613030b0109020903100c0528030501 79
    0x4001045508006020518519121401b1004c0545490308001801108850303120070a245008035086c214990410000900341c4611030b40c000340c00a80d8645d078480002c220304040d00d8040f0060b24445060f404801d0400720400d0f20366041c00f54000082c4110b641c1440008c2103d4040e45000c102890b00b460804111898070218610070742c0f100c0c0744c45000406015040c4880030a80300300590310101e500001c0d030300c40c040324481c42e840d6003800100720b840400801d00038000d030300c80c1d400c0440d050784a071000c42c036030301044a6071401617000442c020383da498143c00041c0603407186050800c4c1040c50401d91000c0d0703841120242d81490070081030104008294400501706100880c0c07501f51141141e90081d01c0302d0b4041d1000e44510000301c0c6007030811004001c0401010f00060005544000300e03254821217003502c0c40166800c00403413000246401144c021550b80303010080141008500c88519040280010100c0408001c010720000242031b8907681c1c00f69075400365024000c1c1c1070b164503200030309031007058 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 857311744 1250 857310494 857310511
    0xa030e0606190b0a030b091005010e0a030209040b0c1b0703050d090303091a041502010b0102100506130915051003060507030209130b0d081308060108160b0307270509 73
    0x945808902d8501008042c0c1030b5107403c04800c3d501c60303409104401606d50150400c0d4070909100500902030081003500003155000c0e03d4010541c0805010001d0541ca5484042d411046000004000a81d10f2008a0b40610503040a9050000d85003000c01d8041000000002a0344031030800d00500c86d00704100034078030180f450201409401d580e07000302032200c0d03840340006000f070144103410f83c030549009460141c120041142d03034421007084024007a105501405015010b45203400c84600d1980c0641442000c001d00307104100f40c0c0401c03201d001002042e000303884000001641c400c0202003400b85c80e0151200c100000034441c25410000e040307410103004c0c0400e051041040d0f4006440d580001d0303000b402480000103905890f440801d03000c0b410640003c01c80344000030300262244141c0010016200500d003102c1072a07032541890355854007030b4400c890182c0e4240008001100b0305130019a0b020a540c500049200c07401c4444212800c586140520803980140c4180128100341d68450380c407030402c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 857312994 1250 857311744 857311759
    0x3110906030f0f0a0b100f0611100f1a1e0d05031b060103030f02010e060703091a070306090f330b0301271a1e0d0803040c050607050c01180801020a030e0606 69
    0x740750848100c0039403449400c0274400d8071007030114019028440f000016074010b0003444071601c60601c0f0b9004002051b240801e02c00301080580250603c1400b841480c08800b4400d60f0181c01002000001f43c03001d001206c452004010b144400c00c8245000e6205509580003005c040d415441c0c00f502c0504508418011607150017071200010500080e0181c000b107860800180c8125241002d8511401138903078240440052002d01c2511507050303000c001114446c40d410800c000410056000342c8099410a02488440c01d0f41101600c02c0e40e1124030540220034170b2a0b107031994a00c8001c01940090740403a1104060840040b48031000c0e030a24245084128810006094000b83c52028013000d54540c0c1d016032034109054030000442d12540380119002080b922034241c6501d021911a40119000c5903030301016200090181421020f80b403040354450060510b0718840001115041003400903040d650400202c00a605182840181403081c41594041381e0405411240d514116010b00385500404a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 857314244 1250 857312994 857312999
    0x120b0c030a180c0e0711060f0402150c070515040f05040e190308091c050319060b070f05100b060f0304080d18020f0a05010f0809070f180c050403110906030f0f0a0b10 73
    0x402090b1f65074032115499102c4055102c0c6c0c00030403940800f00d81628484030001a04600900c40090500100c4008039803022044000880c9600203004a10840440b00c0002601f40440d18040c2c01204d0a0981e141c00c49004119046c03c25848035550303103068012920304814808070b45020f000030485080d1104030700828205460b00105188002005083c03640a12440800c40c0e01d0140c20103001050780c43c05641d2a1a46400e000d0f00d16044200c04651620801e03601040d1a82e61303004480d41601c3c018116800c2c05003004207481e456100810840e4601000c05c001078011000d071181035010904000002108452441800502120b410a140c4108042c4104003c1d9a038810000e10f514107280c0343c9200e103600d07080a81454403049070490501c5c0f82d10110b0104d0700410b0720b13040144604000c14144043d05000c2019240361043c0c0c003024048458201c0c1c5101c00e400d1004059400c000c1c06011220300015058100d07081a44100c41240c0c2078010b0f660440900400b02c20709900f0200d1054004220381c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 857315494 1250 857314244 857314277
    0x603070509210d050a02060f0f06060a030f0507080402040e0601050609010e0a12080703350903071b060e040b06040905131202070906120b0c030a180c0e07 68
    0x380d550151107900c10086071600a00011212011030740b250040314910854410082c00310f82254610f94018410700d0006020700455580b898010044541d498411b5203d070f01c1840070540c0320040c65400d058440d10070400d40c184d0762180b244079230308698170900d040c14107104100c107985013105145907650115005002c540c4e10132007241c44c40c041c00d0a150300c1c20ad2024011401150050348882400c2c04405102428086010300803c0030394400c2e540c1c0c45d155540140507031080414001c0c803039003003451840c5040840c07410346c0040341c12600c100c4c1204c0c02d007881030b0f6601403040804413180300c020000340c10420100c6e401c6455020b034510100d500784000354000020603224000c0e80f0485680f141c03a140421004200a80d0740141790ba005207128aa0030b440c0f40c3c01a64030003042c0b2440c403e9614001e400941c0501041284054651200d000600b5480c0c0101040c0c06810142c4035413071140d034030302c2c1c180c4241c0d000c884800d08041c800e1181584883c6007180d4040c140c0c5c40201500144401030f00d4205600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 857316744 1250 857315494 857315497
    0x100609051e13150b072102060103030c060204081c0210020f120a110d0506180903071407090903020c2106010b07080f12040c05010201020a140c030d0606080a0b06030705 74
    0x410341070b0b410000100d00041c0300d80240c207588100c4200d0340c1802d00041041c1e420580100301c120b000b0000c0c001d20b1044111007800b142e03c1c1c95080d10050300080d0041c400a441140342244c482c0c0104005804e080d103500145d400c02e030000040e55900c805003450b411803a078041c4a00020210540402c6040c01c2d00386036803021520648140d81408404070000032805007141e80042100c4500314503113615181d024861100801c030546110740308103141e40c0ca81804072076622800388600c1824001c0c4d82061013903907420803800400c00b2059994001c02c08080769501d041e1141c921458060f9000b4101d0703610690511400303d0525031008403101280d04207980701240064030504689411722080d644807010700b0504654015450200c8806100003002100d11121035a81d034000d078099480402455617030001a8201c0c0718014a44000c102c41011950711480c000e000381140001c50000d0b01e1804512100c050121001c0d50000b802280c9003005100030585184540d00300c241059910a16600f01002c002c0c0ca207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 857317994 1250 857316744 857316799
    0xa1a0d02040b03030c060708180d14070c03050607020a0b0c0c0307030f09030204060b0301150e0108160903061b0908011a0f0607060c09050f0102150105120a0b10060905 74
    0x240c1e00c070b01d880072954800304200c404064039002952014141a00c004120110980d120013240800d9107210200b4070b40030481c0c0c11140195101c070400410703003141c0001a60442c1b801510104012400040400d000b846420721070801c271f41c00750010121030318101c1c00d0f011018044140714070b814030400c1c1d4180300010490701e0385038050600b0700f411044441c0840303944000d030300006e4006082400010b01002640003a6050b00c9035502040b43c1040e4140b02141d21340c6a2111040c002011980814400040d40701c01c5c11352800c40e032605000300c6440b515800c1c00d413405128070f40d4038035030741d42551803100740d000c0c19001c0a400020300a000d8089a041c0c0300c0d100101100820303205030300907216082c050740c490040721a0b050340000d0502054240142c06002c2c0b421034801c003400f803011052590300e0b5604c04202c415562407030560b201420390a1000b8042c1140541c0e19498051050101070f201180c0f5003030115114811000100c40c001e4100b0200034582c0840390b1007030780a6959942420300049075541c40d000f5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 857319244 1250 857317994 857317999
    0x110a05031605030d0207080a03141b0a0225081207030c030e01110f07080105150901140424050f0a06020607030b0a051503010311031f020f090a0e0a1a0d02 68
    0x540c14120b081c00c906500c9100140c01c4031380d200162180802c0440000350108003101d80701044800b02d0380c810303210000c00403108012500d800552002c1c003006418058207078005248100e500c6800805100d45000c820382c44d0481c0c140004d288104282401002000381410300300c0c10345410700310165000b805101200000905201509010410ba64030822043da001c041c40d80071914405541302409407202014001c864081d400c020004003e4258504181e000c1d0b1320140003006260b1030110711002c0f219518000980c450303103850026200070680c172443e800c0d800302864071405480c0313000100284405038008450003aa0f02c050204500c0b500414426400303a003605021404501e503400168052003980c11503940071500d80681594021000d0296050300e11406811071182a20002c05a07221521010312060040c07040b400c22003241c817034002d0b00040300c400003440d04051480c00015050100e0350850504110200b007004004041e5000300c0f171803079003c05400c1d001d00207182d000c10701c82c01560101a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 857320494 1250 857319244 857319277
    0xa021003020d18140106060806030a031b21030513020f1002070e1905090111030103030f030209180f0a0615050a180f18020a0503040f02060c1c110a0503 67
    0x503a01d040503000048007080f04a240da1112000785007108118451645aa2142d80313020780204e0b00e035000d800e403940654801070083c8945e12507550200c0c1c1c2010010320402000d040240c00c0c2c400503180f030203401103503003600038800000d00100c6002401c8500040000c0140d9022450704800b580702c03d4092548100d0507100c0060960110006910340305d03aa81c001c100e11801041001040060320324a01240702d07072148280015203e584a0609031010203440f054040810401000000d010f54145440384000e4100581071140e010001012006000d500480d1101c1460801132005d5071a00310941c40f4a1000c010081c007400c2c1030406203c1c20b03400154100f031040001d08008001c2c005c078a18070309204021070040b20140c40d9406500f80c80810701c64024003046007455810014014003d0f105000c1042d078400d421950789850390142140180b8041e41c02c51410880d0b0801c0800a0241d0b000c0070a004246141c4154a0380d001010a56615103c2d8640d40207180c9000010700040112800710860f0712404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 857321744 1250 857320494 857320507
    0x30b1f1a0702100807090803040e07080601020a05030c01060f09090c0e0a0207020409060e0c010504060e06070804030515010e010b070317060f10110d030209090a1d10050411030a02100302 82
    0x422881407100295001c0c0b20b00100514166000001d203106001513614070308665a90345600703030b690080f0b0203083c001d52103110024040318800c965180d80224148126080e0007d207480302c606690180c00c5070961350b51600000c3c03100b01e6014078044010b1200c801d0401102c0c0030b58a50b220440040e0284403215a440004560081c09580503640100d030024000c1141d881c89142c90802090015094060f078001c154190507198000c01c161412120b05488114205458808110042e41310303141c00c44d00c9032424000840428010012b240e0618880401d070212541461000301a07428160b0040c81140740400c08400000ea01103000c05a0061503002c0704074607260b100c00103100e0034140c031081c3d4000c191700d810350550b5980001d105905c0155030050310380917150180304400f03031321401c440c103a040003684011400d16400d81d0b022800c3d1184400111402da8140303206241440c5801004000c5079072114180b10600808880018011314120000c1044502030350200d88801c85081000090580c0441d4a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 857322994 1250 857321744 857321789
    0x3090b0901021015051e03100c390b070908030412020405042a0923071b170a09140a060507050c0a18050f0c0f07050c0306040606030b1f 60
    0x30070000d800010140003400140500706e22500c941503480d6031007485040004c0301e10f1000c52080c00c54a50203a580d14144d10205102d4116880301014001580c98424031100b100510500c651101e4520980441c02c96003440710005002603469089060300c0e0b0020030080000030504918103061650540c0c010038030790798506005540c2d548280405610f10041d8607651101121a03000c2000e8520340d03002041008071810902800c0c6014100002c2840782c181c0118809a0290500f40c8507003500204240c507041d1603980e000041010300c90001d54a1001007a01c0146030f8202c000603014000054540e0b04210620340003801204c3c4900c5100188800041c408040c000300b44070209000c10050406e084032582ca0072880c840c80f00c00450788501d54940070101d252113242c6441d190140c40c40c952030761304020649000c00d586501c039250442e014400c00b0718951186d1005d0200621940c0102030001c2c9076482e504150307207896001040c1710040c0d41125090500703160710843c3c0c8070030389282901724103c01a40680 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 857324244 1250 857322994 857323031
    0x507210c03020c0d02030702010207060e030607120227130e060726190506060712050f0c06130303150f150903022e02030408120a020106150c03090b09010210 69
    0x1100f20b1a000320b40380001410f400200a01c00a4400e90886c2e00701c9075205c1d821100c0210400d680d41d40b541085001c07846480c82190788030007901c1420001032070030b8440320729554644420b0400300c42da00d6481e0440d001d2481d00064951121009100034000d80c44104801a162180100710720180008013040154000141072085e03c803840c90071410000703042441c048960740d07080d04100b10b0320301c0c00c207000034280342044010b554950b9803040c035480d0007118001040d81c42e5001612202100300091210114404e810403a460080d070401010b0b540b032804074140201034850725910001c203810b40300c2c8200a2140400c900d442202d41c0303950070000607203450130202c2e0325100720f44c4003a42c41540d14400c5040a00581c0c150100210f800d5202e9256114800c1c0c280d03102e010300c0c450940c0c4c54201140403d041c6549100512200c041e5100010f040c50700c6002c204000441c41c039111000404289880c0c04158000c1070000c0a4454408413a0402641d540001d560761003007452045c0b0701c0c0d103c003100e0741800760300035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 857325494 1250 857324244 857324257
    0x20c060a0c05070b0a0e01050705070302060f061f050306030d020c090f0619140f0108010503030f030402030705060406020a1e02101d060d0c08010b131e0e040803060102010507210c0302 81
    0x80404e0b903803e0100f40040940f051841043d419460320001c10007107400b6100716105c06505802800c03a640c1d400640b28105000244800d4021806510792130404544040306d4008608a450b100c2c0c50b0b0802d030302414a04100c0042510955000482d4844545d80c0c1c010840d074001036584080080355258004941c0c480381076405224144098203010074580380d40202c0c40220308040c1ea040c0b03105207001c0011145494203108081d015003003001000c101070078000c019a40280050112903085a484002c50000e41c056400840181c002c41214403c220009203088980a4106d51082000c3ca850300050103590110060f034051185803c821907151011813000c103000b504c0203013095111000e029202015041d460b0051000602d8000046074070f00028054031140300e00d0545100b00e0034182418010302c039130b910400303444804410400080d4500c00d06000340c80746108080c0c103510703424002e002900752900549441e05000c0e8108815901c480050094a420194104082801555000d080e0024403a62 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 857326744 1250 857325494 857325503
    0x51503061b07060c0c03110d080a110408150609010b0702031e160e0a0e1c05070c090207081b030c0d030c1709010507092903070e1e0112020c060a0c0507 67
    0x20b5101c0ea130140c0040300344214038060b0302c03001c050309480c0c850305444007031100c000c80104440f803010400e00e0240754130440d4a006c4114490f0f18242d1a03442540c9402c4040f00d03241400c2d90910108030b0130b810f18802650050112011260800c9601c1c3e000079201ca81e804400c8040c1c05448000c0c1804442c100441c0d11880c0740d00c40f40503145500d400c2034108418049404100c03107420503000c580034010005400040301d6801c0c4840b4180740d4101e4003190b660380140030507144502525800f0405100d14402003442510800d0015602c812052021a0101d841040c1824a40080c0120264820003041003608004a0f00c0c000900c403500c800c0c00e81e0340041e0207007200030502100c030030450b0104055001d18080d50082d110b80600a58070b1400f42d08044207983c071483c4030044800f84851684010002d5600103109040404542e10301001140b2104001480c40d0551074a03103040b10342030350304001303808441c01003020150f1400f81440c0c00a41c3e50480606440b550603560000c03000e40c1c500c260103454405900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 857327994 1250 857326744 857326751
    0x3020d12060b0c010902041b0c150608070b130f060f081b0c0c0909190b270d17073203090d18060c030e010e040c05040801051503061b0706 61
    0xa120320f01c1c1c0240701c4810100d02541c90103031a0090b00d0f51324117024203d1222951640711030405a070b21000307280180c0508031400c6484150208103200c041c071445000e81210300c5501d03129240b201105c0d030700c0803407940024a04900001c09009072036000c0110024800a41015503550311090086c40c0409045070100c000c0c075202086c40504a400820360718291401110b07551059251103804546912408490402c0a600c83e0700041c002102d003210280e105c0b410320340e0001080105100403243c21042000d20072030303803c0500c04103030707040c0c00554640302c101c80d283d110340d030501d440c603005880c0503d80001e074590402507000004101e2103a10f80b00f1585504202d603e03442c2c0c14000095030b51401c161004201003000c85142903400b5858030141d8080715001e0795080c0741340c07407249c4040c1c03904521080d030281004103285403a00780341c441e4090351045100ca030340c3d5260784a240000c128219040035140c05400c000c405006000e1f0390780007a50340d8000705014803500d5a0b001d401c0300302c0c0c0c8621814a00811719402c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 857329244 1250 857327994 857328007
    0x30114012105040515241e0a150801331112041e050a0501050706060b0f0403020a12050604030e01170c130501111509160b1206040b090412020708070803040f06090303020d12060b 78
    0xea98540510349404ae0300d60340400c5e6201e941d11503580101c0c1c0e01c0c0790f46060000c1014004210401d1311003100b440d032030030b120910716452072006091014000f100000120006000c020320901d0010714100c40740884e84594405040000040b05140c50384141d0b410014042a090107114660303000a00400001821a80d608429810114203810030710090344107030242e210014106690007100120035900c070028003699940c070b560a4a502d40d50700c03007990411003442a03003107041d0400d0402070f0160380710327404060312a2400102250100210740001d81000244001040319081c0007808500c0341980d4445441103640300c00310340b4908400c0c0040652004c02074100001d41050389001030102510181641d8007690318102804103541600c6c140a400ca525040050040707803600d206c0c5603006c00c4a1054801e860742c0c500d60140b420140e07402c050303074503040054100400001c0140c2e6100400c1c0605101004c6071840d10080c1d02e03034401a03aa0001d111010540480006a617840340000d40340a50120f81c4644 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 857330494 1250 857329244 857329259
    0x20408010218030f0a0b0712110307030e071a0f1b030414031005061c05010219080a1404030210110f0706051605030114012105040515241e0a 62
    0x86102c1018024010b202c0460700007000419500c85660b0060860b1342c4a0300c030050103c90055030480401d070181e41d0341c403441d001c20a03000002e5000c5d20352a0341c081030704480105070506110f419484012009098005803008080d600255600f00c4c91411945444a18036600e119840803420071604041c0400500480d030112007016030541001d05404070b50307881010b0714400040700c0040d12042c2e4004c500c1c1070103007041441101d418540c548104000b504150706c00c1140c64034240e07604042004141c02c1410070601a1030b502c01d5140780200c02201002c039050544002e51201c4855002007410b80d00c801010b1021101d51701125850380950410503a6444181422801014151003032401c0c01c404048160f10f0610070400e49042c0c03860a488080200281c900654031007603d0004512007052603000e118105004d481204d04c44d50194000c1c02007100c40149503240300c0030050600300c0d1807403002099801184001d030116031203c3c05480308240e642191100340c04900c0b003201d003075902101c0110042201c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 857331744 1250 857330494 857330527
    0x4120326071808010c05091c0623060d170310080304030b070f09050a0501110c04021225020c012a0501020d0c0e060f0a0c051504030e040c1706040204080102 69
    0x2205801c03100b510b10303215499142640e20132522800000d8042c04160300381d150107a450305008900c00040100b0411642e901c0c402d6403090350040b0545011502901d24a00103448800d6000074200d239064980162507403001c1500c0441c0d034060301d00b02c03004000955210648065030000d0b0800d2021240c076a6030343d00d441e691011044501c40002083d0f07202913603659018604107029510018441510b107410440111029024101440642d00c51000d02e004152198030003082d506440c0009001030b460b041c202d680d100d4120f0400706050602c9a000480c1840d404109032080500910300f1030203003050030641c20046402024603206e002400c510364410008154001c000444aa42c0c0500540d20200c01c01e603140e55a840605400c24020484030111500d008000c1c0442c0d0384508254440c003103642c0b10300b442c00c01103044e42e5010346d00d0a800e000a05420100503c98104100d0302400507002405c03000380780000c2800708a001680020200d6007d540e41d0f01650090901c000c021912039071180c80401c0113 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 857332994 1250 857331744 857331767
    0xa1d09040f170304060209130b130203090c130603021503430906030507050405061b03071506180b0f01230c2d12030604110a02010506090604020412032607 68
    0xf07050700c12458081d4440500071027545040c010310710800f448894003254080e51004040030268025004c1008441e541c2900c004400e0650b0000001d10a046205200382019809801c5003003031400d00030011000c0c4282d0301000082100301c0c0392200224800c10752a1180c485103910840c2e04504100c92002c0341d40000160100c9503669030501240c1c884030390948140c881c0e802810b400042c02c000440303e051002c804075410b441c0c440203c85c034003152621202c2d4130207901080481926166039040180055403040102c44c540400800c001070550540019a0300900b218000c0c14404c9030b1144064403c903500c03685250344204111300c0d40e1143d1542c2210b44444d084520440b40d40e482c1900e00c0c1004260185507101f2182c44001409200b80c0c040c1034403180d4000904071544191154401d112105c03000d4080e1803e03007203640003c1501c0c14041c08000340c1003001070000d80180d10502040241812000c84412071036050305000719140641c04140c00d21100030080031002d500280140008103601c100507054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 857334244 1250 857332994 857332999
    0xa061107061407030309141f05010509010b160201031103010b040f0801020c03030708150a0306060509090c0609040b0f0301050c030103030f050703140a03150602030a1d09040f170304060209 83
    0x41034986200350786201c10900004800b010a2110a002901903400407061a01035480d6002c10b1480b1115545041f164802d0701d0700381000d800b0490b0309003a11707000309405490300711039000b095070500f840c0c04000d02541088034104d5180c180c202041d64042c2c0d00001c205c000c4461226507940c0c66086007010760b480ac0c03240701400075010b540090faa58040c1300b034a9003114a400990300c3d64403001c0c01110030040c05000d540601910b00710f10030950780c410011400540c810880414404e20b08410071038200402000310005800030082903600d9a07030710f4202d41000008443c00500c40c020f03180403c13240035103405081c0c1c05610304170030b201c00300007240c0c003a5040300d00c2a5602c60b108089104202c540b4010102e000300404d400c00442150700f424680a0b120700e9a0518000940d6994442c05e80003410307003135102c1c60141c0c10000344009140d60168500320310b1048040c5110384240312101040d0011002807020b00144030106100c01041694031000c40708080120019032a401d090070104025400016120f2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 857335494 1250 857334244 857334253
    0x210050a1814030c0d0b270d0f030c020f0a0b100b040e0603071d2419031506081f1503030e01031a06090409050304050a18060905060a030807020a03020a0611 69
    0x9645c1c81c0082d2034100b11903014910315a42d40b5541e513004100341c809500450300c0d6402c007400d0440c91004109840781203015980e0004500c582c24409011070303064080080464001c17501e42c0d14440030016038141c0c0302c0d50042e01c2c841c2550351516840510200e5810165005100090025403060b4500005010300e10881c02c0e5951380e03a94a144100800c0310100031f4100d1440e03000007036148108840a00b03d4480854501120702c1105000200180401d2240e5541112041e006000b1300091040401040e04801d008115070360605407459501d0001310707120038540551710403440c01403d80b500128607150390070400102094503850302408004010300c006000034030b4880b5100c4480654001c2d123400c0e4201401562400401c06c081c0300c0904011031040c0d4042c801000001000e4541c0505c8400800102d503085203141040300240090b1a1998080d076030705400d00b002e200c1c107581c03000d401208690740051115a1030400d8030219450013a96840030354448050300340010030541154111491850b204d00382c6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 857336744 1250 857335494 857335513
    0x203010e0322050319060b0303090607080a0905090c0d050c04030206040608012111010c030e090a020408150610081e0f010302030c04060b032d0705071209030210050a181403 76
    0x6584213001550030485d0070440050001054069121000c00500942030701d00d04841c84001c96800e60006034105c50480c000100c1e0700c0b1980d481003110024103400c80d4440d42908100d0761041e403074040d02903000c4005550300042a8404404000c46004503805042540c4896441ca80074040d41c20911504e480e10321940d61502c0c4c4600e01c00b10410002e9802589551203004a000440380c421291208038140a205030540304140d50b01c0d15528840d00d03107090050b07075035400e003ea40ba0505034043d1651881c0280c0c4400d102983e81c2c1c0c0c1c00070120460040c0381400880d9611881512103907241000c800f5844149030074041e42050340d000440c144c0f0b009800711075a1007041001d10048500354407400ea1014401e00218403042303014802964206800c220710f40403c800030341c0d1800d02c528143d6141000c43c10016055042100c084400310101d800d0307050103d010752640c0c0100b22980c0400810408010001a81c510342c00c0c040c1306440c0c1c841d0158019040c0d038640720810000d4038800b9001d054480e12419100d0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 857337994 1250 857336744 857336749
    0xf03080112080a20010e0f0d05031504230a1d0312010b160c090b0909030c151e04050a05010f020a0e060a050408060c120a09020d0f0203010e032205 65
    0x80035045600c849203d150406004048904140b1901c031400c0703880c442240f103400140c0c2400b81c0d4030580d504201401c1d110700500d00703461800741c01003181c006009092041211442540881c22459107081d07030007141350008a804508003141041b408412460b42109001c1807c03811707400101540290440302501c98601042d0700ea49015064143d0000382d41c0c0801400855211000f0303152551950710090498455a6100d094191035030b080320720f5456640011345a5460041e0942d60031100001c055407403e92030010044d1501c0301507030002e103a02c28036030201e070201d41d2404a68416036a50b0544170b0513820320785000c540f0380010308025225507080c00c1101c44015464400c51700300c0301c00c94684800184002c020700030345030003400c40d01e024001d0074440002d00d4101448210f21449a07078a0140d503c0144620751410b000c00504100007180c5130045580042c3c94012800c0329040e001400304c20800040e200017405082c7c800301c492414000400c6110900c2444164000701c03010751840e1a49980d00c1c0c80a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 857339244 1250 857337994 857338019
    0x9100e16020705151e1b061614030a05070905040203070e03100203070c0f0510020c0d030c03050123040615030b040608061b0318031b011815020a05160f030801 70
    0xc4241c250f0350108000f0345e450584005040c8030802d4880c0550810800e8000e0540d200002c15580d00c69401410410865440c0440c0d9030000d416036040030b2010142e5406107408500000704409212681c1b0b00200707032090702070740300c060040c0b0001380155540d2415080041a62110000803402032003044070200070341c9018002d491156580f507a480c081c1c1d9005803141c0190800c400b1050b00c1e103008130b41a0840c0e95005000808060740c1e243d004080d0382c541110b0040c129030a010102c2d042602e04001844500340414001c0c01c0403071481c0c4007408004404c00010300a002a81c0181c802d003c05100104103a13030160881c11082d00d00312000c02c2041e40e03031102d86458106c2140c918005030038007690b240400c2c8400c4040c5400c403002546680d040c4405c1c00a451940e4044981215468682c50100700e600c0400d0268030341042d401b1440600071105079540e600c45034007040c024960160089884190140318509072211500305403884002c0182e02e060113048881c070400d094000480c04000450500e0145c0d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 857340494 1250 857339244 857339269
    0x2040311090415020a0e030d08090708151314010c0e0a0801061a28021e150411030f01090f12020a031218020907200c0a0509100e16020705 61
    0x407084012007a0b2a000c443c0298000c0d6104001d21216000400d01c0d910204800b07070074401d0b0344e2900c81d07040c144007103024a05907482d0720086440d0721000300094444207940c43c0700d820608004001c120140c0c146070424141c840300340b607a0203641c6001d000c0502180d10004401c1c81090a4540d140d105840e4840e103400e0340c0c1140900701f42955030002070421840010024a8022001000c40c1041901111400e03000140d9040c04001a4021490322460032030100c1c494003c030000100920000b001c61002c0d40d0b070054000d00251032440f0070360712041d40740c40500190444c14042c0008010442d60341c07405580d421000401a10240310291042141500001e4002c04c1c007900340c1c5600c1d40309040c0c02c2444018050703101415215541800f04800140c075200c02a50154405403561003008420f0303000c0f024401d207a020303070b0680f40d03112030210034450300c81881c90b40039075809440d40030aa0765038900032240c20205510404c450340801040144a202d0b118684034a215030707500340c4420580d103008102c240303803042 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 857341744 1250 857340494 857340503
    0xc06010906060e012c060309030d140103030813020a17100c09032d02131b030501050a030b0406060806090a05061509010b0d0615020c1807052a030a03020403110904 72
    0x101c034407200c0110340c1943d908280d024001711201341c2c510100c0d11310303002950401055400401c5140051481d800f8844010203c00145202589541c41c024100707800544482d180c000c41102010564030755030107407000342c2f4482070220102003414409a940b510b0346110300030358604c0c08450500c403502c0355050001701c81d000a1282b58800e100c9864a0420000d00400080904080318134401601c4071400031210001040700020705503000380ba000320038590101020f081501c0c18005000ba550b400a003802601e80000400c1301c1c942d580d04d80707d0000d14071a046904c0c03078401c0c802002480c0e44005a03449001c0d21030000ea402c03980305e040800c0420b505c01200c2543c07140a481c01480245840b0010304202a031952021a5640e80c41008028008900082e100181c0200e0711521050800841c1c040300d400c502da2103056686003001006020f4002e8013020340080448400151002411511240156a032503083c2d84e03849806880281c003d5206100440702629004502b040a01c4c0100511303100e039400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 857342994 1250 857341744 857341757
    0x301060e0f091f022502010f031107060911100801050f0f030102090d0804051509030c190b0d15050405070c06150306020f091c05250b0c06010906060e01 67
    0x45040105803000020840c2c03070b843c03080300d4a100c41c09003540340d9201c00e04504940180c1c4c41d04088a9880740d0b100c540000380341d40d010040c00c180181d9000d80c0b503002c110568a40000c0032a203810040e42c041c81245006400a8101200103084c0107034540744040d45181114000308034a0760410a88480c0130034402c4503488000c6401446950034820b500a030340e2075008000600c0c0620341c00001b48e18080030142583c14034230105091082d0305100ea0340d22408689460120700f0310001c01e0000f5a92441080d019008603040a000c491500e0785601c0000604141031840340c03a4180c5080d040e0041641010140d1410220700300000c0d43d042a104d083d0003402141c0d0703440b048150585034480603080203007444040300c075090000000b207015031014101c100180b810150340c03010b41d0f604001407220380256a565445a46110500241000401c900089030400e4015040700e1034400466614031203a001c9020f0700c00010703950303280c07a50220740e003810303114000f00802c640d60311403400b290071080040038640070424 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 857344244 1250 857342994 857343001
    0xe18010506091315110318070609050d020d021f0503040c0e040b04030f1e03021e0f0706050702030403060c02060f0f3117040303020d08060604050103051902180f0301060e 75
    0x28000c0c00c45188038500c200204103410030101703a14860340104c8540114596092a6542846050103503000a0629103060740c1c4041c2840c0c0042c0008802c100300902c1740071071100c100d0454a610306055152010340c103464005681d0180060441d500480342210344941c070550104000f1304500d1024000c0d500703c08880317516550742d03405880004403900d281c0705002480c14051415500401c407120f002040340d40c017507201c1445011050021711926856180302c18240a203007442580c88003620406a0020000b190603101c0440580c29845540c102512a03420801580d100c180c002440d58014603407041c3c090419611580c02180c18101076070f49001d4115408a00811a00310701303c50240701024000d03c0c1045d6450f070790f03110080b00f0700300080400080046001c20078035406000075500c1c202c02d818010070a1602200040d018429401014107140d40c070700101d0306281548a00410034120040219526960075283c80070744011901d481e4800ca0040318220224103041c010101110b0391b03070f154001c0b56203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 857345494 1250 857344244 857344253
    0x3140f0a1e0e071a040b0f070807020904080315041b05070c0e07080108070b09030d11030912010b040b0402090a0e1b070809040f0b1003150e180105060913 68
    0x24140c0300840c58904054004400750320910548116003100d0005000f4146029003402181000011081d0711040c03c5c0f004001e60200c0c0f400711010b2040c0c1204c807580d11181c614200364035000300b03100a908136104c102040201300b0396100440c022200301c0d0400c1903466651080000361414166400400c01d15400d066000501900c0500000c0d8498418000f00c503440e009900040c18080722010001003640c001000003040901c400070150400010661408880a02103540d0b00e10f5001c0f4141040325005103048041d5050082d00d070040e0707006064081d60543d0850580c0a0605444864800c6180c0034295401b0b03c0c0c0340c401c4612140e405811440700320b14181d854207007090000d05101100822210f8038140300c18240003409038910075854030742c540b2070003020b20084a2038040d42c06885440c2076050401d90355014080d2510750f803280740c0864201841c003400c4400c03690710f911814180010406000944140b00303204500642d0800c0200072507580d500801c2111a801d451134242404410825800704 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 857346744 1250 857345494 857345501
    0x10030b030102040b0720010c05030f03072c0a06020c0f0f040b130203040b1e04110f060f0915040b0f070204180f0201080612070506030402191503140f0a 67
    0x59802000107041a40e04d40e00c0144c180d00942c421581440c10400b83c840340300e00002d140084002c286069a0031601da9910f140d80c0388102d458000f481c01006c400a40703014402c1d1b040300308014102800d469014100b2400a2a0402d41e9017480c0c0b05000541021921520001e554a00c0300780062004110001100600050784102100c058000342c584820b44125100d030300c0e0854825802620050ba64074003030410040080000d4040c040c0e87d2042902c420b40358000768002d5400c5a00680072100300c11241d000540d104c0107446406400042c0450030303203540d0304643d01600c002201507980d07083d21644402060b91a1085004140c5006002e10800b61540c4104000d4429984007610000b024444008000d040382c9049600315030401000703602000715640a01100d03000401520b002402d08840c441180c0c07105241c0c06068080c074000300000d0155501c41e5203542c140780000d1420a94181c070b40701d0080800c1040c92510010038182074100300c5190090a0161060b41c002e80840140e44034202c0a5026 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 857347994 1250 857346744 857346761
    0x2b02281104090f21030c0e01110c130e0c0402070f0311010b06031305011b0f0f05090a080d02060907060905040c051b0708100e0703030804020a3b061003 67
    0xc5a03480c000c00c400204841180d083c2c0e0fa01134800b031002c3c130003002d00150040403144044000c0500301620740c407005070802150003022400b401e10607010520081454034192020b0402644030351542050300088089a20101101c90000260f4804040110602c0180d2141142c000c040080c02251000483d10992041041f44a00400803803545001310000b2025001925002c01202040210348100042480362000c0c44001d040000b0310803c440e4805071210500d003880d0000c0c040b4503080c044185125508032105580010f0402101e5074540000782d070f4a0110442030700141c41070310081074a4003400100c413000c46d5184d030b85200160342440d0a0002400d0b0030b140c20401c2c41001e0140610a0115441d043c81c805200310040448502d07107925285405408040c401a070351400341d040603880c002240c1c5600380d030307010308108031903403500d201082125001e540003100300901c12041c2c9407100803080c0e00e40f0000c2000b6400360705050540703e151000600031b5681544c800141c11a503617003180030b0b40203580d2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 857349244 1250 857347994 857347999
    0xe121b033a121a0f03010507081b0412080a0e0315041b09020d0c080a02070b01090c020c030d02011506140901180b0c03031f080703060e2b022811 64
    0x281548508820054800c940816190043d4440d24900d007814040e20403071020b40c0c114001e105504140001a10040014019011700e44003403a240020003a5030b070841e402020004200017144183e401c05228940007921601c0c001212000e04030024034000851000060041e8082100da407540c0d40c4151106148240c18a888001d074000000e030b5070b004c2d202a0603494091031001c912000201c40c000c28403607004080d004401e1040c0803060100f03c00c0081030307041d180000000601000b4003501130b403600b15034040301c41e854031404140407901135042d00072045000361031900d00c00043e212401510300c0d001072280346d112404240400c400640c480c08a040d1180312815186a03965203c015810055000341501d1826034400010302c82680c50b000700a811260250f60602e03001c9040c8115142c40b0f000318800607090a40b0340034551907082c030a01009001915404016110501d011180203040c55403010a078054002c0d0160210b8507806440401c0411003005210b00c10a1035580c2c070344402c0440500400d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 857350494 1250 857349244 857349257
    0x306060114030a02250b1501030501150e0a09090807030e0d020607033b130c020607050f09030a24090201090b070804031203060f080c060a0e121b033a 66
    0x7401071105c5c000c3c03e4009000f0342c03901c13140d442d0040c070b0700c0c0040302d03021041c90401d443c100c010070900520030105803121f010342c540358005003418400200b248216400c080ca41d1460b241c850420011000000c14aa030311940358544100041020408842c90303a18001e034101c48104003540010344643d03400e4040d1090440f001d01055165019280e001c80c9003070f00c0c00803005000c008000b02e8640410b0038442c81c03440e070714207101302c4034040c2e4000e44031540076182505100700851246142440d10301175418418025044a0821740a1305018444c1c81074482420b0602c80c0b120304c0450002c071540541c1d403e581e010703154815060302c0d2013200007456129030819a24800c0501c400710001b001c00f201400319890745d070360100b80749040001c03260601c501c0c1d9000001651080003038004a44501041c0c40000400d4104034014020100c04618200445102031509000e4040d04032000105130080c06d021070b0050302201e0055044070149004404a0f00501c04449000f400d40d0100003040b401040081c5401c0c89d000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 857351744 1250 857350494 857350537
    0x6081312031d030d0e030c100c050f1201060305060d020a15121d0706110706050a050f030a09061505012001180b0109050f01050f0f0a0b070305090306060114030a02 72
    0xb41c00c4004070268000d501d40001131310411003600c90151100c00103001c0701651401120554941d5102c140c26410165580c41d1450880518050300581d4040011400c9d80361362500c4522007030410307400034010f0202080c81d00c00816201e06088000e0301c03013284d0207002101c15504000e0b008443d045007000940070442e0082220705185054080c40705141140c42010205078220344c0820b0030020a034002008112201c0c4100702050400a1800c00f107500301d0910a80c1d6a02d0f1003011980340c456441c0c2143c03a448000140070401c0c00aa220784040c07030246008115510000c002008400641c0c89003078001071490045c05102c900e008030358803084d803850000040c4007065400800403003030080c6007506d1100b41c9200401110750940206503104806480c0207542c0d40c1000000784400307644011090044803803142003090394a130b22201c0c4c0054aa0010010341325401440d00414542c03220707102502030b00170302006c105154059641004180c03a460100750940d41d8100c0c0000c020b4200d141c86100085c0c882029 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 857352994 1250 857351744 857351771
    0x1060f1b020310141006020f0709050c2b0c030c0509090a09060504052107020d03081003080d06090b030a1106070f0c1d090f1e0c060c030c06010608131203 68
    0x68010030600752400413102d1500c041d008014002550058055410a40b051140d120011400d0001e0f80c1d03006100254a4803181c003140f2460141100e941101e500d0981d04082030b82c0e2444c080c910354141004140f250450304c01044042c2ca07525414000800c00074000181306151060351107610088404001801200d5929450141c0d041520191220b40010385840500044a11070203909030074004601d01c0c0c243c080d80480d802010b0400007804008034000130403c42e0229510440017941c00001c0c1d16210b5020100c100010651846001445403807e4403101040c1000f0911112550700f2405d020a040e54400601031a80c0c065a0201c90310401c00060200007954030003e1805422010b841e44c014860b14512a100060040c00f2850980d104d450200340040001480d10b8110401290700035802c1d0050201c10310b40b04140664581c08000445c4001104500001400a00d051002140c601b6640c581d016103656905440703d481c20f400080303158021540c024030f016140045880c1c00034002c07241d41e14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 857354244 1250 857352994 857353001
    0xe12221a0a1209030801081501030503030703050408090d031d090c0a0e03031207020a0605090f06040201030209011205010e060a06081005040b0109050402032a04140d030201091401020a0801060f1b020310 89
    0xc01c9000c05c40c66001071000c0c03d01001002c0303142012031520a895415078480990b28000280b90004142c0c07a83d0001d4100101e240542d000d41c0d0001e0113100e111500d40c64050f01c061900c68a40100154400c07002e840c0e032402c40006406a04d204001d41d24213100441c085802d8110f84c3c2510307401d813001300850407030300c1e4403862181d200780f9256010f48600a100c0c40d041041d9000500007140d90b604c1080204224840807811079003140e42401c00503030740c03101c4c8001601c400841d1480726070020700c0c04000144a00384034815500c1410100c070740c503e426450350401d885c681401c0d241203c5903030140c0c2c000d010030f060a40c030200403414141410f0303a4043d52800094281c0e801115502c00350454100705c074840c492851003c0062001301f0190508180c2030070000e075410b4041e0010329116030002440d0b05c040c103000394064600d42d604014541c28000d01c00c10030901039030010040c0000076200b80000100548280e0350007149600603520303411001740741000704649007900201030781d040c0140075225101074501e21 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 857355494 1250 857354244 857354261
    0x2a031403040e041401150503030a0e0f0a060309051e06070e0a0e09010b040c0f021002070204090203030304120801050a0b0d020a1707020c040b0616080c010e12221a0a12 74
    0x2194120964104ea12090a55030344100101c180114100c09000320b0f074021058410ba4921440c0080000b50600000780c2040300c074118050308a8100500485d94540c5500128140c41c050f81c21241041744020f0381e8250200044500210381d00400080341c605031042140c0c00600c04000c04541d026520303421581c0001c502600c200c51980e54070501d10405083c135001c0c40c40c0c03132030345800c203800f081c0308490002c0d4480420308801148250300149a00440d5120361000c0307183c580240480c0d03120710341440d022180c000010441e0020625490000900c0c7c0381c500790b280103869503003140300d0510382c040391407901a40000100c0801e00c55a0030000c14407414543c002c51088a00f9402414101d070070340c007804102c80f142294940109820802d1540031100085241c003a1940b1400701580c03480a8402540101007654841000c2c0c091611004010b950620181c17080001848550540d80300c2c0001c20000081907200e05001c074440f00c0c0c00990404803070030150a00034850704041e000c4000d030844e40c078219085803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 857356744 1250 857355494 857355503
    0x80a0213090b071e020f07051c0506010b0703090b070213020a030e0d02032215200304060903020a09051605032d0a0b030a0305090607060f0e06042a031403040e04 71
    0x90b0b8500801c504c1560040c01c00d24260000d0410350807000111612580720f03004041c00f51100009560316402c40000b491401c2c0c3d00801602c0095840349400e603880d62141340b0990024001c800c010802d2240305044a4801e94020100750280082c815050040d4014150410500d5a0b400303403100f1130740c410712100301c2c00020390740555511551841c48498454440307d01c86001c540004040c802e0f071049402205400400d0f0520f4020002d040b500204100640000300c841d601012500107031481c1c000481c0400d0b41e10880b500c80b03a1580f41e2408108841003150342c480c040c01080100c440003401000103540280350301030411a9113410100064581d007001c55070302c04005180c0200f0004220381c1c80351400350141140078081c1c0003010f40340100903000c3c0c1c040452182c8030000703841d0208625584a43c071100d880e00001d1081c10790400c0810b4031441d048909858080905000c0803005047d0b01302c4803030540c603c401e4071030300360304580701e090f04161a45c3c803405091000300401700b20850302c1500c151046219 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 857357994 1250 857356744 857356757
    0xa06020d0e1c050f01051323011b020307050705180a051f0e041e03080c0c010b090910050106020313170703062c0a02010c03030209210a1704080a0213090b07 69
    0x19403120b6421100007d1415080303072490301d68600003440b5400300e0b600390300064080700c200d51414480d0500400c504410810401000300d025050b8a8012001e0010f00d80130340190340744c0d243e9070f00a001c0c2e80d2600d4501d0741a03201c40000051810074080e07000c1500042c51070400040d0324018803038030300b980001c1e0b00000032440300d01042004001d0350246ca40d000b44042034903043d00b114640e4000e0910400502040100103002c298030724464002d40c020044020300400061090800c61081a01c40f88803181c0c80c040300e8100070010a4581c0000100c5200302c84c0c0c10310030f030141417900c3c001d0007009801c003140410500920500002240680c00b0b050400c6108200020039025410b4500c00854450070012009400499481e00540e03004511100318035014140540d03501090707000a01200f044001c1102c80040d0402d000100020015440d450b0900c03d01840100228069002a45000d40d1040c07500a9012000c1c490040c1009603400c9001c94800d07501003101c06081e5902810b24030112030841c0017502 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 857359244 1250 857357994 857358013
    0x909020a09080f2a18070e0d0308011d010b032404090623010501050a0f02010e1c02010b060f090f01021218090f10051002030904060915050a06020d0e1c05 68
    0x401a100f21a0b0b22082015000131644400101e030325940d0a05a5002d02e50440c000140e03528000c1d0f40d0286014001029854003250902d005003050000b070185805910b125000400a080c64149090684440d07408103411940c500c02ca50801040350341070a001d00ca4500032021a03500e59018000645d4819003010519444c4807804200e80c480b030038ad0229409582c00010480c90742c00200303c41c8070031350b40c0c9032060140e95102c5040c1d01511402c0184495482140c01c000c074402030506403060a2070565000b40040081c036801c00c4010301500c2c8210054040030044221149404090f1500d00007040c0107884160301c0e1041442041d0300300444820000000d0790318003d99103400a51700d50311600c810091003090504407030000c802d00160003461b014140c41102014440d00800a0703a40d03810000304103010f82c0f5202e800c00030192001c0e4145c0600e0824940020401c3c0c54140044400d9030103541c02081c4001c52260300b21224a1080c0724540c1090816407040600e080800c14803094900801c001c008422 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 857360494 1250 857359244 857359273
    0x4020c03040803040302180f0f04170a0806190311060703180611070609030809040519020a0e180103081c15030807121b110f06070c06080f070909020a09080f 69
    0x1010140c6441490f20f40c000f04068900c3c20750b8009d0b0030076900e500d10203003541c03a45800c080260416480b6106e85001050102d43d017a44a0080f521940d000c1d00c80c02002307142c09840701710903262404000c1400311030f1000740740d560900c00c0103000510301900c0e00882c3c1002104125400000c00d810190001e24020300170b8107484c8041180c9001040c26240c040000351544d245c0d6040c43c062110001d10880d1204081203d510703080c100c096072000d414404565800c0510009400c2d0500060705c18094520b20308c0d00810304101201c0d0504072908111200d1501081417a4403151a00210602124541c2e4612004031240d1841804c8080d610811105969030502c0c18607a1030b0481c441040000c000b17040c00342d850705a40c240ea1a140140d880548101120141e10016150146010209030045400303d01d00042c000400c030070004480f62500c03440342540324000c1150540c982210704001041400303008011a10040d80108140071142c0b40030340c08113880d4044941001c00c0400c0c134140941c400c200103071082 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 857361744 1250 857360494 857360509
    0x6010f06080609010603240b0c010e06040819020708100204031104110a0c031709150901090b01210b0108010606020d090305070b16080a05071514011404020c03040803040302 76
    0x10219800c1000075071400c0000509090014000c803010551250182c008502e441e40c1c44041711464001d0151082da261881000c81d0b03006441007003203e609010030130203d02c0022448500450f0044009442c1c060300b0800514002c6052246100314802c03400005442d94090100b11100d80b42c040f00503a451b89982011980c5000c80008203104502d02150039101b9400d10007101c0c0940040e00385404e950400742025155903800034604590410004100300094030301041c40411042d9060529040385c442c40003083c204e402e4400b00070090340f03041006001c4002070191010200c0c1001d0301e00f00c1800245d55500550500a1340095403980d128641400015014008110f4880103440d002c4001481d607121503a5540451203040e80c1170700001740d42e000d508550f280e178842d0346410140720741e03036410100401081ca500c120029110000007a001c4400e400c100d00521800302507484c1400c802c0e90900c1a510b6540b5120410194490b500704010400340400388058801081d2a001650719541746006002d540c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 857362994 1250 857361744 857361749
    0x60f06120d0804030f0e21010501060503040b0103170f0a080727030b13020d141e0d120b0a0e01080706020d0f03050c0f070f02130204060207090f02041706010f 70
    0x58200050070740e06290b2100d440c66005030540b4103030315144400102a2510000064104d80290a98140071456004603c1e100c3c000e803a044003c2029a1b41c0754811205c5001c00d46c5c00902d200304850042000c90f400311201994a2130702e281c00e03442e103c00c103880803a0540c042041d48010941c09800c00c40110713008815007141d02e858148903c80100071000c002080c414a0100516044c516008607100c40c100c4103044030724076130140080f144204142400001c1007184030f4910311511500b0505203842c0c00d00e11b84200c3c030110f039600410012080d00030aa6801c41c0c43c1e17100d01003a070740c0e40d0031041003562040038043c000d29820b1164042075042c85000d90030801ca41e046182558030491444040c40c0e40714104910b081c0070703460006016100c40084159a2041100080340c0542c0803541a00780a0b145812038503451080343d840150030828641141a03005902c14203000d604201c1c000c0105c603407150401c04542c54107900051506440d5003102030f00020615484849902000050295a10f2001104003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 857364244 1250 857362994 857363029
    0x3010603050402131803030e120f0d0513170d150b130e15091510030506120c01120b06090a06082403120a050c010c050c010605010c1509080c060f06 65
    0x1105c04034404104403804080003d0401da0707540b0201c07000c1281071091850050f81600c52981d0390400c2504400c07603401c40030b00340120502e0b140c0403500c42e81c0c000b48200130301d5074880070450810064200c14039240e0080302e003200b01c00e901c8000c280403032180ca4200b81c01408a44c0c510710744402100220303a00c09600b40c2c20070140d8041d60018801103405600400307141c03040454504003203540d92001110352030248072030690007904040040301c00c180c06411440c81401d00391a0b040110040c204a59502d402c0c009415003c205800000c42a104450300900c542c0e1a0142100d4584801c100100e0569230b010f03840a800110700d034040c00000380d05998013910542c3c0b140380381701c601034403080025141c40d00d1700040e64216400082e205801170213542075840780c0c6035102c000c1120004040014000390312121f000b000039441c0800200e01907005400c50810b06401c03a00d01055280d0701d485007030080042c0703c4203032145070042c4400381c03d00004000007482070030b032400c065645040417030606c80034401000a004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 857365494 1250 857364244 857364251
    0x60f060f0f0e060a0302040509070806270a030f030b2b02010201110f0901051806071109060109080c1215010308090103050f190b041503050a12020706020703080a140301060305040213 80
    0x8200d58802c0c0d1304d9000d0f680c04650008194544a4a217403400030650b000c40a140500d03010030207540700b40c128089005500300c080e0721008510309042c5450303d12128004000c508022400a02c1621941c0321030510140034012140400c1041802444607241c074008984800d4449040070855a0a02400900d54920701816040c009484001841401400798140c10814081400198594040109410650041d1000390340b101c5506200464106040d0900c2c041c0300d8000201e00300c5d500c00c0c6002d10407294214080d001c0480e40c80200919800b014911605510034013812003400b07040780c070a0500139032051031181e641e16000000501034580c010220b036900c0c3c641c40b040004040313003d000c021800101000c0040c50100c41c038002801040d070034101520070b900401d00441046000602d548a08c0e000760031a05c201e0255403002ca0f607800d007034000c400c01078100940400010340c0c180050076100540b803d1010585601c11031384480740c1c000742e0000000a49a00500040d4141841c10f980300d420000802e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 857366744 1250 857365494 857365501
    0xc0103050c0f072d06050106110c04090809040213060f0309030f031805010510060305151011120a030603140606060a0e03030f0c060f090606130504060f060f0f0e 71
    0x288180505114480301000c001010410454011002d07150011903402d4070304265039080114400d005000002c172207880c07400d4008210315015440282240d80f05200411254100c50103003c06020000401c03514400140003c8103a80e80d14009402416103a00c0305450840c40d1480082a071141c0c500310f2403d145c50f0a0b08100400d0380b00010b51101d15541c00c022408091009078140c90762809039003d0030551030a410300a03406101c9041720b0071518555001e00068070b031340082300f400041c10754440e940459920302e03c082c5540609460180305082d1400d40d4146101303042190025032042c0b40030350000c0ea54a4007030040000c4204440e441c1d0050400420143c606880807a049100c0d4580d4001486009042d56450340d4081084a103a0b0661102e075035203030701051041941c1c60105a5042d024544081c0c00900c20f60b03000103142d44510401004140005419400130004140280c01600c10503141c02980d80e0815950162400820794001a42c1510380f4150101000a0403900f01ca240a071144051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 857367994 1250 857366744 857366761
    0x3040507060e13021606090c060f110703030804050f061005100503040309052209053a050901030e06070f08010605040b0403060f180c050f0f01050a08090705061b0c010305 75
    0x243ea00d07a8900810050350b89040c118102d1414160800c001c00550800d9006002c1200e40d1000c44200d880589603000c0908041109840800e03008090040a0b0f2002400300007103807250b0551500035001c0c1c01658030910004031740e07504207941200c048180000c0c3c95010851824980341d100e200342040d00d8440d04608050750300038808070043c80303658800c4618048a01c005d0380b800d020401415007112082000c0a070a01c1d0140d10740c3c0101d40c2c06100020300c8418005944c030481c12229003d150112120b1020801c2c2d40b041d41d03160828104281016601e0800c02d6900e841000800d000789940d44444074405440703100100105816002002007083c240010046031410781b042d203080d00c0d40480003103420a000e43d130b6600100019440c02d5084801d042064007807004042855090b500256041c0c034807802c3d40c0080c4121861078500309070010700100035443d800c5109940b01c0344c11000403c141d80354169114001281034101c0004403c07409801c0150404c42c940070003492003210400e080521403440d20121 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 857369244 1250 857367994 857368009
    0x40b07061a1f0f021f0b0a06020c010f0c0303020d020f0c1605100c2109170c06030403080603010902030d031a030a0c0501050c070e01090204170106032a031703040507060e 75
    0x242d00d0070b102e0144507042019009208403960429000d030741c4a801c0c4480752001d4040c140c014071190103410148804940b0034030208000c0e000020685441030f01d68908072048440c03014010040c1c0030160f080c014442da28017107000403c54980f0b641c0c281030702da000010681d802c0050180840e45954003004040005440e40401026000c2850619903454401030a0403500b0030b07441461004018101c8001d240070b0380d0007010701c1c07081e51014030325886c942041d590349070f658071b03c00d842c95903101e0310501c00500042d200d010500e03484500600040344400031640070a2526090030b1920001c03e4641c03c504020701303d1141490b401311004c400810301c41040d03855040d4107415501a140c10403c00146004050300300b00926001044030058241007036a460001400941140c00b4010228003107004d031103802e00c0e050080e501035a402a08800c12000d80300458400000d03651501c526170344c6201000404a64090742d9100c04148042c84269203150500c1c03c0790a00c1d015401000c207100790250503155540b136845 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 857370494 1250 857369244 857369299
    0x40f090c18020706020a02150c0c060c03040f061a01030b0328020d0b0c030f010b0c07142b060e150708070c020907021501171b0105040b07061a 63
    0x190010760421107010000080d01c07400002030303d031a000207001418a030f0300042040341e41400321944003494585000540c040e1050a40c120947c0e4400c40100d035054140100550300b15200d49a2080b8107181907440701c042e1444290310354904989908550000d58040c0520002084201c024195205003c5440f00f048458080000c41c4904103192a00c219100d00b88140400c90f0459807007002e618120503900700faa8411186030101200000c00000c0319800601580c00d243c804901400b4440c1c200809804001c0701c4d42c00303060b440714402440c142ca05c194024260000100c000b10644010700a0030200165003422101001c903a00804201d02c0b45020200d0041d045842d038a0310004d191034140c070481d041c1b0105031000c2c0d8080c4002080c0082c3d40d4000444000040700c80340d2140840e070303840d80a0880504162103030152600a44441901100b00403080d000143d81410240d081c65115440000c181d040400b08441d0140d035120304101c909218003030aa1010700445103100c01114120080d0744210a28 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 857371744 1250 857370494 857370509
    0xd061406100314041b17010b130b0d02010f090f0906051008040b04240203190b01091512241805011d0403030e0f030d050115170a0f020f0405040f090c 66
    0x800041c44200fa101d4191170040040c002581a24414507454900905c81000a41d1194181c50780da4a0f8000140c002c1281881c40100a0b0010b0300c1c4503001502c00d02c1010031040c003004824040030401000f03034844e020140603a0003000031414142404e0100724812444c81c101801003000c1000009546001e241d6805644556080c2c0c10360210b02a0303034070000c01102c10005150010007006001c1074070b102c0240043d2001281071000e0030000c401511590b0281c0a0070301c08810556519075000c1c0174150100e605040380000080421200c501d621049108072429019412500000c102100d00e0340c510401c1c24281d5002000694034102c0101c000807040d0311141410310841c0005000d05010781d10000e0f24206070b509903903501d0056003441d6200c8d440140d0602029192000100d600507114039043c4001d20b254840b06a039a01505004440704801030a0000154590203501c030304108500280012100c000c4106d5116800c0c50100801c0c2c5210004400c01e06103420303980000319544504600495982 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 857372994 1250 857371744 857371763
    0x40b0a0302160b0f0f0c0a140405330408100e030904050c13210303200a0203251a0c091203030f070c030203030a0b0d06140610031404 59
    0x6648080d00640180c0008084400040241d6000d001855541c60310401c160001c0210954500342c1030300b080402552400902c00c020f10290404038011142e080036407400080312414a82d8840019540a0440c0c01c464195684094008100020307031248170316520103014203605003401c0a504c541da0368400c03004140e28549800c988402d489041c4200c401b5101d01810503c0139261241b090781b8281d00c003028421003154594400075620036460a12401d41e80c1e03946150f403583d1174580f0101c0c0035110301c0e12036080c4a00c882805030150898207004008826842d0044c40d1a10a5010300c4800c04400700c0c54514240c80100c488000900c844c40c440c500312203074445400b0240c4840748100707c00c0c0180e00126800c40c1400b0355050300398074000055803040c0300e00d4040900603680d01c9000c80b0300c80e08003900103025a000b48041034510040790400700c00303405c024101c1440c00c0300e145c40310010b554484005001031021101481034904104016100d101b0381414280070721004503904910800d4014009003d1064 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 857374100 1106 857372994 857373007
    0x1e12030c0408102a0512040c08030403110a0905070206130c181a040b060414040902100c120e0102031803122125080603100c0c0224040b 60
    0x280e59481d5810a60000e012401e00030029200b180c554a00010102724075a04101410045004140680301e1000190601c4224035503500f082010038284410001c40c11f4000842c607070842010a445400b00c0b04030b00300140b44a10640000096000e40c000703490389041180c210840581c1410990f00000c00520100300c2101c1e0000f50081d04440240020842d24601c881c01014214003d040450b500d01c040e4001403400000031110b401191500c00c5150034030103460300c0102040010309141c0a104802302c0081d5880c09600309510342c103031824080d480c454405100c1000b2120360300d0260740d01d40585c68081c4000e0381c8e0001d09011000860300004400021401c3c0000c42002c03140401250901120000c4070180c81c014845d03501445480c03036803821480c06d442200040d102603510700c050300f2201d01c1040269041a0464007104041d40709849011590000b1103084661a0043e2030742c80d803 = true := by decide +kernel

theorem cover : BRFrame.Cov 857194244 857374100 := by
  have h0 := BRFrame.cov_init 857194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 857194244 ≤ n) (h2 : n < 857374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
