-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3556
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:00:21.708016+00:00
-- url     : https://prove2.me/submissions/240ddd25-d499-47d5-9189-8440632124e9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 639388489 ≤ n < 639568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 639389739 1250 639388489 639388493
    0x4090b0906070c020303160c03020406090c140f03010303030218040c050c0c09090c0108060d0b19180b0106081b030c09010201060f0f09020a050919050a06020a0209010308092b 77
    0x140003001403402d03040101c0c02d1007440050740d003c0101c0d0805030079511410103800e4241001141950140c1c0002d500a203042400108003500341c21140800c1d01c4c684a9002c0b0410300b0b41c002c03c161150303019041080c40704000500000b4042c1d40682000169070048072410403190000c542124907002c0c803c800300d00b000c9540c08100c030003000600c01c1c01e41c055030b603414a803c2002e00c5c8d170358610303040c07941b14140600c20002401d0f60316000c2020310340035001000020941006060945051146401c46600d42c0c01d140c0e84084c40c620150954800780da100d10240755aa180c903204903145a40035101c49081110840084d00240504000d1801100081c0c002652650030360006821194240c0c00103401e0044108108551100702c0e29080854650341000f40e6110800942244e0310f00c00c0c0f44620b5880b0b03014449400c100e0a00041947c21745078160f0342032500c2922200181da8899010f07030020745c004403035001400082d0000c030113400300f10400f07005050311078004001d0304074901e04c1c41d00d6626925002403403501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 639390989 1250 639389739 639389743
    0xe010b0a0902070209190e0a120f0c05030a0804031107060e1306030507060804030c06060e0907082d0a0b19060f1a07020d1e0c080c061210030204090b09 67
    0x60044074001c600d04103999000c1428401c0042900c103c00b0a0700010000c0c481684e004203280c07028413420354200c040f13145071140c031031950040300c103000138001141c0804090188421210041d00311005500b00409130801f11030302e5a00600032030401150070148031a00804100c241c014050136100c80441d5211101801181d0750214000d00d04641441004c1010030b001140281c1030b1001c91400a500b940c03a0300b000d4880f8141421300500f10307441c1c4400020042100420305018048501c10340380c0407035480171111b5540100109020000724907160000c0710780100151418181049030984084900325214008400c500701c8000b01c0000c0f03c0c992241291500c4d100380c5001d00b151814a00446040484143d0781c0383c000d2810001100e00010507809540d0b403285e050140580c0120707400201d51900d14582d501c1040d00300121501142d04a000c0750b06403020942e650740d180060613407401d1031309890f088060504003a10607191903941c0d11010000d81c490303004490100340900305040490a106039114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 639392239 1250 639390989 639391009
    0x2010b0f030a0308190209090f0402041404020f0d03091502010501060906180b0702241b0a0809041d0703121103070f0803060612270d0203032202040e010b 68
    0x34865049054240006034010300040d4011a00c2c0762080c0110320440b22005c0203100d0410a60341c0030006108126611039001d8030309210324401d990500024000356a08015041c01341e8000354441d50407440070103207081011200d071580b80245010042c4544e0b800c0c594a20440544500740107035102d000610482d40c000140c9402010340c2c1c0341101152162401240d54400725001e400094540011040259550081000e43c14148818041a2075070600a0326600c0d034000e04006d141242d600c2c03403482029a01107000101d8540009a2625292140e001c01008002c40e0103806000d051801321040940d000b0081500954840c04807404044c1c00b84c0409003032680c1b0008075526a41c800c0104d42c00003039140116881c8181d1040c06113440b51206c80c005a5140220001c6903840c2615400704480d50071110106010460380403144452001003100180d101e240c080c08060142e071040000c45c08168030050240304540c1180c1405402508940c0041c0644803c5240b11103940e4440b0000c1c2451314000410f4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 639393489 1250 639392239 639392269
    0x625140d080405070b13051c03120c0c11030a050a0c06120606052a030f070c0608250c020607061b03020915070807021c0b0702151501020a1202010b 65
    0x1038460345029501c8581d203035003a000324041740c040820b1b5600c40e040c50442e1704000e030400504000400c101e03401054641820100280c0000d24140f9070707c8030050f241c0c4511002500e0550f90700103402e4107515400c0e03408510b0310910f40c040c454890107c1c0461414030035500c20600c904480c200c0c080c5040f10003000d5103c10009116440c0c900179040008a822000710307031412940d100c040c100d00364404100c071030720070004400148600002414030b6400d001e81c40240700d07140c451030305160a182c07500011074100004885001c109034000c0c6004940c6040c07010007034036042892400ca040d0702441d9010401d0f85d085004101d070029215004900500c4a000d5040c180c003000c2e10741141040360540c0082d004000684d011072a11a000460030309000c02d42c41151080c50300985445c41500309000000480e500301d000581d03241c01e148001c01c901a05c0420b028041c080d05070548005920741c82000c42c25607541009160552166240e541c00045070b690920307440030a035400000d8803503e8070042c40480c82658100f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 639394739 1250 639393489 639393497
    0x14010905070e0108130f210201060b040b030f090a1208071e140a03020d05090705031c1d0d0b27070807060e0d380f060625140d 56
    0x600d040380da01c1340b0002c0d07000c20725400400306102c142c1003005014586074005030020102048104100000070482c2051600603802040020340d80c940c0b030782c0280100d01912110020070408554900046641c1541001d260002c1ea10010030564501d011004164544004910352500300480c2c85e0f0416201943d00c1551800c2c10303421940350000070301000c603d9503031075012040400c143c42194882c0d41694010014803000700220b003802d1083c51b540340e480b803207000d10078031815584001c21445522500c03070701c0341c160303c900540c005940d9122060f440300707140c0c4a0700400e0b14090400854443d03003265020b071061003500d40d0500c845c0c00700d900c880700c120000c00702c03198090a400c100f00080081c0c0d02003141c4052501050b41540d8200056603080700c010b010b0700b900c21024000401c052128074191101030400c019100c008103200d500c1500c9074007101c445001840040001d03005060520003400c00762949014034000c562041442d0700362140700002034801051085c202c0802c10070410180f483e128031414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 639395989 1250 639394739 639394757
    0x50f01050f0a120f02120a020f04050a1d160804030c0f0b0406060f05240307030b1017070e010e042f0306031009120c050304270b0a0609140609041401090507 69
    0x41035880d22030050031f2100b00030b5001400181e41260341098602400c00244501500d941d510124140070340f2001c000c1e100803240070003160801c0001c07101641020407648480706566034607182911745034082034041c1c40010007074200d480055031076003c81c0e110310310805c80010b02d0360404154811203e242c0d0401030040c070152030800d1440380302002ca41727074011103622803d55a9036018401c90181c1000c1d401240c0103501d00c6559140c03da000700c8411030600007222030312000c0c0d46409080b41d030400e1030505640491070460752410f450401d9089022651b24003001c191507814840c0441c40000c0c103001401c8074551000c414845989030520404480d04060308040c13005802d02d03112103c072810f443c1105010b020100070320b80d04200c818015103000b414060740740d007124400050950313110b4402a40c604c03000d91404410b51781724a0a65020401e55600e03640c1d026070241801040c84504031000324495102c4c000344151021a43e55020301d10707184c078810700c0c296000d52611018070300b503d40241070714060054100e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 639397239 1250 639395989 639396007
    0x604030e131814060c0d051008011b0e09011d1e1905010b090616030905031f050609190f020903070605120a140412050d0c0e0a1707050f01050f0a120f02 67
    0x1700030f60350401e18104000904c0d0700c2e0411050039102c51540703c12030a500f0002d042952107031144a02c940c0010030346400b100000d00b1010408450030902414040d101c6c0c2c01c5006044001c04011355510200103582420b40d69103581983d602c0041c100c0c0c00301034000c1100c8400c8054035003070003118010030012303c080e0704110003180050100c0c000c040d03c90107503c19260404007403610404002d401004090280e400000c07001040c681ca80c10036040c5482174504150200e00c00d400c3c0415000e21a000500107132140c241c9015215019010550315034400c10307000d005e10021035405004410003000b82d9192503980745040d00855034101401801c0d104910320b80005071851290151280341d1182d4031401d02c0203e105140d105944c24000c501804030306070329180c0703a502071941005044210f0702c02103504015050352044900301c0310114120015080d040480104410704015087c11002c0030141092410001b8007148203c80e80c00148040380018054260305031004640d12800200e070044060a500d084030350 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 639398489 1250 639397239 639397261
    0x903090d02010c29090a170c0c06130e01060c050a0201050306220b031b130b0a051003051609030f12030b120f01110406020604030e13181406 62
    0x624005000e040351616800440e0702c81c48080405603403080e44401100042281e07282500c03121042d1040c880c51901c01300320051344c001a005841940240c0040b82079980004030392071900405c0304c22060344038600d60340d0116a50540502001680400c0d06030030b40e460115602954413040e40400140802480d50102042010030502d070910340a007070407a92074840d80b000c03520300ca103103103030140520340c4040c001001204140c0015030718402c11000c45110f105403081600586003061f0707a848d80410364030503a01004402e1381040003a040c005001c00c0000765510301042c9001402090440080c2d90b440c100861280346902a00544505103441d4a081e821991860300031030380c034003003d03000c9070b000c19070142c2d030b0b500c2500f001121031000340074010070034109000284e4a940c0441e40078142d50030b00012030000f00c00300054404a800c0c03503004040c2501c4a4409542103400b0b400560781180c807044032550748106a02800101d008905009014200c040c14130b80700c183c4a000e1070302d02d260805c0c0f041c840d40c0592 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 639399739 1250 639398489 639398497
    0xb0406030218130b1003022a01021603180e04030c03030203090c03010204170c2b0813060c0311060702100b0117010803120c0405090c0a050c1b120102030903 69
    0x85420010703036800c0e001d540304002c2c2180d100059070020103014541d12095150300a00c0e0616000d503507004110700c200f0700980a074080c00461000004402e1625400e00500d0b20740320668040c50303c00149400000b01002c0501124220103a0100320901190078501c482642c0007402048401d00d5004a07007026034004040d48400b1070b000c1c007010707000300204111071014000451400f070002c00031907449585891425071004010009801405032249d540c0c0390b8180190502d041c0340e00409540c04045c402030000038540c810b1001524001e40c02c6c044210311a0b02582ca00000c0c102c030351101441410a4580107040c0c403c44a040340c825000b91052041d455000140070113144103560001c202c0c0440c5000480b0101454041e400c0c50511380000000c1c842c3c0084010080340c200f21042d509a0341e00c0a14001e40344c4907510509822558410008803803c889101070003040303c0e1443c00918040140200710b00d00385d0712503524600d25501c07030a42d0b403292070001c2c041c00511030020001d600398a007109010361203000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 639400989 1250 639399739 639399749
    0x30b0a090b031b18010e1f120803190e030417032d0f0f09190308070f03110a0b061e030a1401110d0c1b08070312020d0c020a020315010b04 61
    0x200f020841040f030b42c3d5000080c034121008100c1d4241c55030350f40b40002035812060310040e0040a95064481003003040c0b1601c401999409a21800036625580da07401e82c0d81d0005201c017000781c1005e020596064080c0c010710300e600c4c0c070500c021601c484c00c04120350150322411800c0e01031b50348100202d102c810b81c2204004081c11040c036143c1c3e0354004000e43d41c1028441d140200000308000150749500011480140144100a0741c1c110b9810681c445e2100740100075001c06406100d041c000000000d128424202e030b80b500c01d181484503c00c805034584e01d072074241c40e0300300c3d03107075184404200060030304613034400e4404003810b81c5a081400c100d000c00e8540c40c00038400350008203460b0b5292030a800035008280e594800e00e81d61980e0741800c210b40d400800410f4180c20020346164440606424400e10075807255402c10155464040195001c2c0d5080590558840c0c20300c1d001d110058030741c1014415035a00d010650050003041055104060818855403204480a20010300501c152044101a941510 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 639402239 1250 639400989 639401023
    0x50114011b0c0504090302240408270a271503081809090d0e01090e070f110706020a110d0309031b23130b0f040b01030605060307030b0a090b03 63
    0x50494108450760306503d40005422a00741000c0c5c4040650014140040205a264816076404031807000b004154041e90058841d040501c404a080d103900341c02500070141a4580b81400d9000001040d60580154841c4149160450103088041e000d4101c200d1840c0c0b101d07108000c1d1440414082003480040e000c0038014010126406401c0d15480c0c185222011000301283e0452070070341d518a070303181c00000045000481c41030b06040154080c124990030303603540c40c20024099898050403201741d0308000038401041642c84407501c00c20802c0c00708901404c6154007420010307009040007440200004505030003510084010300110350f100841e0000e50303600910049003508121b098525540407600100d842d031404c0b41c0e5500300840003861046c030864051f2100300c0617a0030500c414088541c103120b000d803c403025003081d00d503510b03003a8404124000141800a8183c1d211001705005800488614004c250344910b40421071800d4154400242440c401c203000c118000e0000c661910045560316405d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 639403489 1250 639402239 639402287
    0x1603050709110904050f0912070b0106030905150a020a1d09010e040822051507110120060c03010302150f043b07091e1203031b0302090405011401 64
    0x59086807044500150008005110606058206600740301b0141d504403000d1052040f080f800c140c0070390503102440e07005400002d9030b0780780080030340141c52800c1c01101d41d8002c0b180482e4444d078080500d24010140d10f100180c40300c43c17044002c8c001c500038400054540314801000c0002e542d0341c1e060241541c2c0c12031010840d0740c45078903103400c544c040c44040c00040400d550f071400a40172000960f8007201c00458600380070001d212802d1007e4807455002400801d00841024901d501a000001700b40d05041200c1c004102044005401e1810690390310b4240c0c04004010411740c40c0000070520842501e492070341c60695500005a1716200324800c0085001b884068803000400000400c40b004030041e40b40c119a4960744150201c5440488010000c94540310000c0307040c205140c00801b205100003460030b540e50408819041080d80140c081302059120308440c13103c40c15000c40d009480c4116180981c0390b0901804000544405070461541c0c42c00c22402c48005130b0b842491001c036955418038503502c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 639404739 1250 639403489 639403511
    0x60a0306050403110705011b1e021005120c030105100f0e100e030609030a0801090504240b01090902030105030c130f0608060f07030b011409040b03032a1b120a1a01081603050709 78
    0x161809c000c0103035200b410345160b40b5580e40c125009010020034500c1c640c070a543e85110841e81400280102c80e0000381c2241100010303409140500381030799441c03e042849004000000e21040300341e01d404c078002403040d1410400380c103040002e140c1121003e000340d4282800c408004002c0d280c14400c1c00d02c0281c588001c0b50070f102c400e031441c85460411044040b40718142c1c144aa01604400c5840d80c002002008000364100c00d5109032030584200074040e04259401000b08454040c1c8083e0685600d6982d41c0700c0000074083e41b10340b0b402400b807000030f440580783c0400710310b00f001300040150b404e1508200200403941e1380a440c0c200b126802810654541340302402050040140041958152000003076402c2a419222030004509921010320b44071005600800380e1a5048151410081800d000c821891864180d00f081c1b05840320303d044a02490050315000c20346200e501c846010a04450f0050210801c10700c40c0051034a0401407030300e02603103151340701a62080c3c248240e00445030b4426110345 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 639405989 1250 639404739 639404783
    0x403020c150f0d050114031f0209060d0f0c080a0903080c0703050c060a0204140609030d0302031e0403080627041b0909080406020d08040f0605060a0306050403110705011b 75
    0x78405008070250f440780c0324400c801c0001c00c400c0c010040c030024603d002c100386190005061003220300000e04000441220450355000e50004000345070701c4801440300c030402480b030344501c0d8406100b02c2c0b00440c080c62280750103003079400054001c504981c02e0200c41c0340130980000d00d1541001350101e17021303503c3c4010304040341c0500a4208a014502038501031048440c4c0c603402900540300904040145041c94504004043c4254200c0716010703040341c50141d05940c06030703000c1c503403014648000c00b186c8010386103e00c502d00c4003160200d0100c1d45070028070602e81481c1c0034401050128081c0c500590307028818061034030350020002041400d4509d940b074650030700e080314600102030b070110601405c545481d100c0c03060b4026002e044010311a039809100070622920784540166007010780840001d0b09900c03448060034000305060340009030101c002000591900c0f4440c4660302950b100ca081e10f03d10f490290910035140e00043c100602c5e00c0c1150703d47c0030303000ca111008680c400c0c0540001888850004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 639407239 1250 639405989 639405997
    0x103110103020705031209100c1d0604050904080a08010e0103081606180f0605070302030132060d05040512030903090402070c0f0621051303180f0b0706140403020c15 73
    0x18a117010204070203c00c040a00011402421280c090f00c0d4418001d04c2c09400b250640d0b25688000b0309070101c1920040b04505440010300e42c00380c822172419032200081101503a0507101128801c200044480c40d05034014030f201d0241c0340d000040d58065165441c0c01c00140070b089002111003e071110300104208080d8083c00c4143c0f000d50402803483c42504201e180e454041c08141d42160503c1c000410180c46482183d042e0348800c03180c90711513541e1141031000d0707801e000580c00b1400c01c070100c5203065545400c003908100c003209202051030300c0c0c680360444c28800c00c80b03041075058030700b0720a01c14888004001c1d1851160169401070311903035181006500030340c0562051040a07030071000450080d03030211061034000461100310180c0703095210000c0031070304211501e04c0ca101c200d20312100003074426020261241d1405c06006007168542240d149620b1595009401b00c1070000b4142e0104040c0c0e014100c3c000002e1b41c408903441c03a158501940b2140d035a50701d184140100f100c84030500d42d2460540b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 639408489 1250 639407239 639407243
    0x60219030c200915210d180b13051f0516020406090c03050403350403050d050703061e0b030105061e0316030605030319031d150a060b040e01031101030207 68
    0x2101aa041c80e010780a0308204044400c0c1c054040540700e80002d1038002a08441024010014480f01205402c116641504181480460511f0040024461200314060314101100c180b14064243c1740c0002c218070b09a0326006031050500300080d00c20f000e0b0b0400140c0d0304a0031034900901c000c00311480014000c100c6500402841850107504200381e50b41503105612a44c480d480d42118108060f0b0302c080c0d0b140d101c00c10f0540031000540c1408041581502041d00315201c0c0c00c0c128180351820881000b07840b000c03200c0c500000d0703441b40c04015109149120303c0041e2036000501c10b4850500107034020381d02c814051039005400c0082e103d41358110114510020010f00424151207003407440b03883c4420700c800142c1c1d100190510307001044a00e400710480d880d0140913017113410110031230901a00601150400e40c0e000546144103045c14007414410030501342c144c85004201d91800480b10300c11513000c0d030040d480c03c0c0000c1c0401d112201201d004103065940150521484001542c0100d0280c40354400c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 639409739 1250 639408489 639408499
    0x30a05010c08060612070507150c0c0b0c0a080402060f130609051302030f07030c0e0310060e1b040303050702040f18050c15090919060f060219030c20 66
    0x14062090640c81508105803a40c1c8500241c3c940c401003125070b000701d0454140320266000460310f101c0c09030004002c403522450a640009804545100845045910b40004034008082e900d04122140007001e0384890103511190078403407000002000040e00810080c052000001c295201c0e00440007038800750350340e1103c00d40d2095240c007001801c800c0d440c443e0754000c60a42c10074500b000d00900030359108500c85c404200d2159110340c030407005030007044040c43c2404092205203000e500c0074041104a150501008242185000406048104018103800540103802c0c002c4485031141012141102e070545000341c0c49002c1c0e400020300a041d0180b005081d00e18050110000060342c20000c01018061f0083d61444c8d681074080c04882001184240200b200c1000041860715102c0f100c2a0003811680d203509214500d0301500048664580104100300740b40001001400d034100181c20320340010301c41d11429000345540142200708000002010703016502a1000100c200c0c40400091200c0200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 639410989 1250 639409739 639409753
    0x6140c0304081c1d0105030a2a030c0912050a020d03050f0a03060303261306090203120720030607080718031104180c03020d2a210c0603020904060503 66
    0x2490401da055100c030720901098105404141da0f2102d0026425110713130613190146980c0c0c1c1d14404400503c0800040c3c440c22a84200354585001084940c08040038103480026910040241c041d0200507103910459285440f5a030038000070b2404240c0c00c170980c1d07064442e0489902d1510701941c1501480020300d042440109960000e981d064000d003048901030340312041c2141103202014a2062030141452a00e0800f001280303c450303561540f1801c10f80a0b540008642415500080c108107100740004410341c40840ca941c2480a404149010700c3c0c03110354603015008940c40030903100c14000308020180b03c12200000c807024041c1900d42e1280c0440103082088544a20f0821150840314882e00c0c01a86068004c0d0300400e1a2a000301103543c002c1c0c110205645542d081003029080e441089900b03042c042c4445109440d40c060701c1e03800241000252208a0400a1140c101d00040214034002d02001c42c0c88004200040da2201c00ea035454a0050b83c0c81c108100800c1c003802c2c2c59406a80c0610503e9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 639412239 1250 639410989 639411013
    0x1b080f25080901090e0709060509120105100914070e06091c031121040b0904060308040e371a12061909210c020a0303020616080106140c030408 63
    0x400400e8002d109032101005140c50340c180c1c90b0940404c0b50f000d008a500d145003400141c0c0190060140d0f010007c11982c581c045c00c4a181342501d506030740c00d07a511420340f0024031521045001360b800030201480940c5070307880c00312801406c1c050201e00b058001c030800583e41c2084d803585100240c078074500c480d006151071918a002041e030035580c0d40c044028000c800450300c45801051561040d10410040942000e0a0505611742c0e0f0344030103165a4800d5583c0030010000c2c0041d001391000300701c5c41240302d065227401401d00c50350300c00e0418841d01100d0340d00c03081f0031421811090030024403240440040c80c0c08494040480b060301554590381e00c041940302c0d840c024100040d0081c41105080146d908600000c026001074500c140f00045c1010740180028a40d40307201c0d011011144540d02c3c264207820134a030041403c0800e103800c01d6005802c4001042240c05500b800d580c1d6150b110b152113001903240010003840300401216035607400c00001260b8045203c204281d901a020840c1640d000309181 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 639413489 1250 639412239 639412253
    0x11506180501020c0102070306051801060b07050106060e01140c0c09131e03051c0f020f03040203210d1a120d1205090c0f0d0c03080a1b080f25 63
    0x100908005689503010003040c00d510200301000c2c00d40c0182c008041039425940c8030400f600004112003c0b510440d03c81c4100e982d400d01501000b00f0000d65078a964910fa0309119007540e4031078201605100f40350711824002d9910031410341550045a9006807140300f0b16903158109030f80c01c0c00c1aa449111141800401c1548010b60700c0c90300d1041000303030007641e030300303141e40603444000c07580500440e030180308694601d000095000c0b1603400410300051003181d2043c50700c040340c01c0044c0d001c071511404401c001c114282085030707002446000780070418507002014441c00314410701c20f510250070345a402050340d0000034403000340c0615000b80014050100e007540f550391b07142070185020008070a03401260308a101c0e4440c1e5405040401d018041b030b8007985080c0440122040d003019044181030b000b03103021401260b1194003440c0b08021056888610981c01081860040320080b4035170328240c1e00800064200080b103c2d80880350a8407901c034210400982c11024803107503a001c00304039000d2980100000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 639414739 1250 639413489 639413507
    0x50c0607081509060310090309080a05010c03060602011a01030b180c0304110913060b01050706021201300f08120106020a0203060709083d0506040b03060403090b0309011506 76
    0xc00c2d088807105a4100c0704100c4801c50a40d2038540540001c106150b60449641114540c80d000c0e04284040c9540d0300d9009203001e82000d0240c0d00c50b5990041010745541c50b001d018020040d501c002c2c406200c5281d034124545600c0d001d540e050641d100d10751080d98484000c200c421340300700104485546000c0200902c44d6000b101c00f250021f400b50056a80791070034a0010b40034400b001d100000da141656180e50050500300d1681d814404140034440006660f40014501242107401000487d451f00c10801210348200c0142e50a0a1840c00d4103c1c5800050b00e04100080d00480800035010303107400c2118880c41071421020003511680004225241c00044d1101000d1007034003110343c51f5481030700440c2c1103003690240c0d007034540101d8103941c82c07000c07070014a242da1040b000401c80d41e5001c2070701840842007003902c0f2100007600c8201f0080545418402c4080041040d0050215444c056500400381e00c094002c0c0c2d00c2d07000e030100c00b04102c0c1c60300358400400765400c3e0640b0352035141c40f100050300c1070388 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 639415989 1250 639414739 639414751
    0x309150608030915070803040602091302030408190801060f2106030b0405070f031101051b0618120f03070f0c060c030b130b01140f0903010c0c03020f16060f050c060708 74
    0x84c0784405070300c3e12502c00100c0c0d41280c0c002d4600b9007141c4640e51000081e44c03020b8925a44480c00d07030b1b5599111032051005601451080a03056507c82c0d00300c90000b0080e041c250300609200c40000100113568002c0c40303011240940386407501d070b040345140010201001c001c00724246285801004401c20181104850069008070221042c0c9030395820440100740c141c0c0001031511010169510300342d4025006010303404440e80c0c00c0c494801c01b03110098901401205c80074940d44060b012400049420721944240940304c1c0791091420780030105a60345444054011400c000d01d125003490054070464030f0440e01d6500050620030514201e80050203000d8400c40d19201c0d005580312036036207000ea845030550190041c2c45404103135080e40700f4110141c0000b508940c508404108a0744d40b55801e102c0c2803084400798588000314006420300078035040000001c002d99510000c01d0450038004400701a0407a03901d0f24010f0200054200c0846403030064070020304c003e200d4034080c04034050b0040c042c544521 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 639417239 1250 639415989 639415999
    0x21c0c0b072105060a0311040f140106030f0b0f0f01050d090c09110c0a02041805030c0717030a0c12030f021201030203010c03021303140c0d050c181603091506080309 73
    0x2c140316001c02154025130b203055004990020800010302c50308504050102c00810000e001000d000841c0161400d0410400114090000600050f505403041e03080c4030400c00000c010241464000c1080b51401424080c840c1443c0c9039803800703c0c3c1c0b08008413610341d040803800b0301804c20b182c60803c03c00c1031035003e09900c550070052005001e1451000707031000381900381c000700a072000c00e4092000403d030408240c0d03a100480d0711000701043c020001020700044080081c0004c51401d00740380d000007546942d10499800400c409503640764461040e041e9507812444000d01490114420340041c1a40401020218000b01ea400148421011594102e0703000307030001d001c0c02c0c005010440880c40740d1554200c10200d1400184080341c490031040c80442d5400d030032640c1c061804000982d602407501400c03501540061030303015007803d041808641e00c1c07002d55080007441c00c01c1c0c034000c040307242178640d444101540c540c0c0d80b03030900c0b505a0301420480c01140080020b5503e0b412020744951160411134055 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 639418489 1250 639417239 639417287
    0xf0d09051807180b0c060f0a060506181804051501090c27030c180e0c01050403031209290f09060402060c0708011104080d0f021c0c0b07 60
    0x24100000760307824403118810800100c1d6204402070302c0d154080c5221540c000d030f40a6000c2034110fa4100144944d130a000e0090070b9500c2d203180c1d40c0581c00720041030707600300c03c1c103040082009450700415036000c3c00c050000700e0290440d44c0c000c110001c0100c0da00c0e4114001c03000a01003400000300746802e1480000308410511780e00d5000f00c0d02917075036000c0c003500003580852200000700b40786083d0000405546012402c440d599031125aa460140c1c2c1040d0100c540003800107044206a100340343c080640400542800420030b000601240210702c4040c0a000c4542e55004e5040e0343e6a000d2030f411175009a45841103c0702d035400c07400301f0b0702c414104a441100d4502084405c00a0034110703228003483c40003042e05580e2942842119044411410710500c9019000308002d10300707014540e521340195800701e1702d9510381015141341c407207404d00c203030240f00c083c00a081c1c03c281d000c944611008640d004003080607240581c110f038100b40701140034140c51000760500c0400c5500c0030028034054400e501c1e02e521 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 639419739 1250 639418489 639418499
    0x5010c03050c03131e050c130b0901091d010908030601180e1803070503280c0b0f0603030c0f030a0810080616110102030403031b0f1407060b030f0d09 66
    0x101c40040c1c0d420140c0d02c10600c00030b0b0400e44210110600c5178072034108040e802c052801542d980c041107980c1210b50750400381d03d51840f0f06200d4480c2214512910041c4030513426000031980b0014107014031040b4640710441c4440c080c05441c00141c010b020b40d80200441840750501c01c0f001c3c5c0064a10900040f038841241840c2032500e100d40007500c030700c00c0b002002600c444c1520a0285003a2a4241e070a00050184a010030001d1028000803007105801c041400c0c02841801d180200d50420030041c480442a5040450045030b8401c1e4041e800303400b8400281c5500700002d19601820906030150301c124905c6034034840004c4098020722442c2c1d110040f02d070312003003041e911100e143c0c05913080c1d40e4440c00c0001e017040103103006a04545154201a80c050601000d08ea01360380c02200c0580101c0d88502c550005150700d017080c01e018007002c1c64403000303a0790750702401001e248582e080420720039400f00350b001c14448168031002642100400f150380010440d05903e890707040c10004400854000c90000170 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 639420989 1250 639419739 639419741
    0x705040501063908040e0f012c0402030c060703210b03190201360821071103030a090e0108010203070c12020c12011a04020c0c011d0d0602030405010c03 67
    0x100d03812014451641000343d90350a4203080d4070010080d8490080c4048a4003242c1040010f201801142141d5902403904e031130407492020069101e07891883c800c03407400d1044110384806100c0c4403080c03655070640c1d850304d0001914100c00341c0ea180ba84000c0006081c010941c00144804c40466030f0141c038004000000e4a60003125584408190540c0003c0301001300710000c0d041d0061103d105050090044003104035025403020f40f2114030003007a403000501e1540303003034081e1400300504980c4010503241000305148441a0f00441210b0b0f0b420f0310204040c01001140c2d8000001450044c00b26916018200402030154109114001400319100004580c0365010b0088900c600a96180c240312000b10f903030340a20540e4441d41c118114080c1c3c0d40802807564541144044402d0040008501c4a40c50102030b2484217001803544c0c4202c2c410400c3e417810580101e05070084200c03d081c2017101494012007004003000d0342d400d980d4404a1901154100b0a0b5a0b02460055005030001c10403641d10f174105034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 639422239 1250 639420989 639421007
    0x2330112020303192d0e03061b0d091704031214120a14190b0a03050703060e0708030c03070c080a020a0e0a0905030c01060302040e030f030106030f06051002070504050106 75
    0x40c0d0550010816a4100c4041315621001200f440c170b002c40005040b9034500c0801a0812641054155806019401c0541c4844082c4128034110054075083c00d100000451055400c2240340185e440404e662a1048041d403040011542246034a032a807030742c14400f41c005600601040f03406080e4256408000c038403802a0300350320014001900d160503e0f100c441c503017640d4010300c00000c06456000036550700e8254000c4c9801802419400c0c5400c144005205041d9410340d04040c1c05149100001c101186000030040d0440303400010004902824140c0241012604e40007a4400e100002d00d460300d000c2c3c008000c0865030b006401d41d03180d4985410500c0c4e281c208000c03000c3c1d84803024a00c01c0c031041c207107480d5050704243c000100181131201a40d40b103007140c00070b40041a0340e03591098104250b003031600500805842800281d46015404107034282d0501040c02514205039a0b003481da1040c0c032207a800400580300081c9002854100c903c8003d55414080c000d01c2e00440c1442d00015100380580045c1c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 639423489 1250 639422239 639422243
    0xc0a03081003260c0d0309060e01091721040b010e0a0b060702040e0316060b10020601030f0f030228110603130b0c04030f050708071a070308040302330112 68
    0xd08110468001c40014503401c40040d1001d4070810021030b02135500400c05800e030200542c4000c980011607003004402c546100003200703031690410030703c40001140783c0c0b4110248841d035001d60741c58009401841100f01c000b03001d840183c0b42d0100c2030009120050b030200d412a00c12002e40c04c40c640d1859118000c0c1c0c0d401044c1e060700904280f0034600146030503000507448400440c11a424031503035040041c6803a4540000381ca1840d610b601e106800d0074205104031024415000410b07065245560301d508003482ca04e80a0301c010010160700d000c0610030b00901160606450310f113060006450100010340307140c030f903088030090f10041841d40541003180c02d680c03240281003c8a034448049807a55804200b00800c102c0c1030380c004010100014039540c0a03802250b0246008200c0d050414194a1804d0b0707607038000241c41c1e0208004100407808207000c40e50354540c58074021480c0d0300c951500384e2030070030b006041d00c6080c5030350000740700c00c0b030b240100800399860700d000f6103065641e88502600100840c8000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 639424739 1250 639423489 639423503
    0x4030512041a0d0f06140a0503010605030d08180601090f1433030d05040f1a040b0c0c030d02010c14071709010c0c0b0418021c05090a020301020c0a03081003 69
    0x5502000a48400500f04607500740b2004140004600805412104130ba0000000028510000c800c1814000c0200c0040d240542c020421207060000080d036614201c15004200900b10300014030030115440c0001d00c0b1885c1c0000c5132083d586130566140a071081803c1d07410305900c0c100320b103d03240503001c01030307405400300340d89588203082d4508082460307110b92281c9051028503000703d01e0343c5881c00c000c07400411300265151512076003080200546850541c1c0080c1c1e5450b246000c0f400c80c0c00703104085a00712a12121401e0351105000103007800e0401070340c90380354140035080d00020b4558040d0446102d00170b8554802c100c4c0c1c1c1400752002a02c0c015081c025105001c400081d0100036400d0b00108140041410001c0403009a07944031494420300750083d881c2c0c00c0300400c04201503080340c031400404498105080d07040c08441c0c12140580d4081420f050401600c503008109600403d2001072407403500a002950ba070350115001701d944a07040c0404a0008100c0d00c0000c00002952600310192540004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 639425989 1250 639424739 639424769
    0x17150f0f0106120e0714242a0102030f15060a02030319090c0303050d050609010303020d08060604091514030303091e101b140906090112020f0c030403051204 69
    0x40407203a540c1071801c40c0c9183c1d070b03961200c411003000c00c215480040c130380c0e0307090019129140740078003e800540c10310800d0b480c007441c840502d01d56888004c2c0c0300f003080311a0464004030344c0801c2c1c00c600344401c050000c00d00d52000003800a9801401c0440d44242100301c025008a0010800e002003480340540c2c00005810070300110b05051001404690798024844010404080b9500d60454011b8107600072000b003800020091540c030a94000c0303039806502101c618129600d1500c3c082d4070740b00051015020800710b035002402e1030f9203540c00c0c1c9000c0c0c000d4550070800c215403425894945440c81c026880b0988404900d80070914000048134231a07907200024001c8103070f584000c07800740c0e4401c403141c213480d010700760b9441c0101105110342405444080003d8100b100c50810140440106c829240ea80700410032800c1c51a803540c2e803ca6242a1080c07030f1030044000d0280d20075000b130080b94420a508800040d903506620000405001a01d02a82c00d503203414082d0000030199118500c103042c04184010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 639427239 1250 639425989 639425999
    0x2010302070507081c02100c0f03090c0806011805090102031e0a02071a06040506030a03090b0d02041a041d01030b01060806040b12010515010306031707080417150f0f01 74
    0x28001c0c016661250301240c25043d111140d641c14031104142001ca08003500640c1c441540e410003840409850042c0c04020742c18a00b18000c1010025070194004e00d61500c080500700920000c054004022490560300c143d41c40e04408501032010b8441144514185808258148810710031240212640058402904a03000d1804400d1900510503c01d2550900540340807415501030055070b191021452505460503008100c103c0d04040c090a0081c0d020320a2400003e0300142d003035003512001040603444180c45484040a0300c10781c3c002e040038031030074003504002e00c4030136010303005441c079150046207400c40e64580752102231003d12003e0900d45680300104810790180300c0c1e0f1508100051f10119803540a0384c0850038103641400f128040e0fa550b002000040f0100407640c2400440903c3c00f88281840c503201c0e00083d841209048542c1c01c00040c000c0c080000c94401c507130050500408000c824501e0080440d200d02a00081c8070140b148100001c0d040d003800545c02c1d10461403603100065603400c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 639428489 1250 639427239 639427241
    0x9010302010c020310020a050301031211060403050310050a03050d0e030f1c0306120b0a061a070605070504030c0b12070c1a04020f12010905010c090303080f272401050d020103 77
    0x40b41c4166010300500801906181c018001080d4941898458603540e51540c07a1280f0800c620789034200801110144a94010b400030420542180d010300d0000e031251180c0d140310382d0101751640441e600c106d11180000401070302103440300d03a0507403541707489140724023810905031628400480c0700425000702c81d000d00d51008680d2240000c411920b000185251140b4105104184641040c0d0b0781c40400401c01151300c1343c90042001405912404c42c81c1c3c00140145030f0080d02175060000e058980f1400041c462500c80d4040c4c0d4011030300006120075065441804201a0340010070040d260702040c400103440c14001e95040444950010746542c071041c0c01100d014075048050002c0341e1280110f46000320541e90511a01885d007204800002c51a500e450143e08440110ae0598180010420104003181e00030408991102c4420441c08140d03580d62250300510400c880c00e1454400740914a02c2960360025422031280c00314006242c4040c64101d1207000e4447c2403140d039601401c1480000010751203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 639429739 1250 639428489 639428507
    0x60405090d032c10051f0e0a0902151b12030103061a130209030c09060306070516051b09070306080d030905010f060806071e0e0f0d1a1803090901030201 67
    0x3c0a44031810f00c600b00d5142c1e140200250340202c09907104d2031040000c101984038180c2c018044012100c91003d140c01c45441c0050703d0b01c40d03c99510141d10008003000190f400018001e58001d02c0c1007210300e8a41c001c03140b181c000c1607804c0d01f001490745541500c203000040c07680d100880c13802d030700342981c0c0b03103a89840141105008021004007e142a4081c589660001c080041511030700507803160415020302d458103201c0e440d4540b040c0f8501c01480a951400303e10640c022001d450140e44c1c440b1031411440668081003401092841082c007099601040007030300d800404000c8070310b41110740f41e4040032005e441c80350041845d20b804c01d100c681000350003684444a00361140c00003240c2034030810000d00c22200960702043d1607070822020058110b038011000740c0001d04c41400122080c102d284000c204900c40740d880f50240b24021188640307640c80e6008440f640c2e5000b00700b4240c144051140101403c402e035000b1440f05030021035589003c6022055601516002e410f000035603107190011268918 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 639430989 1250 639429739 639429761
    0x140c0102100e160303031a0303030c0d0b060717130e040b010e07020a020a0b1905040f0306050604110c0d030b040903140f13080c030c0904050307150e01020c0a02030105060405090d03 80
    0x41905500f0b07104000a0400d40c009600a890004401c0e02c0c1904500c41440040d03e2140300b604100100710b07000808006039145507039103001c0000c00c0400c1038045075481c41042e901a001d03103580514040f41448030360040142c00204071154207100e0b51004010003248007618010b00341035449005004c1c4c90301881d00154030415520481d0100c21503a008511139040580107005144000070740b91305190600d14072040c440c1868030308140b03414074012400c40e02c40706500000305001d854501117107455489402c00041034484101c100c3c0c4d24014094460742e100c00c06807500f1302103400c1c40803c0b00c030351500d442402c40258141d00c1d101c0445048052420545c0d20002c003503d02041c0a0100c1401d2000c4100d8020103814110004d1102515031340425140600c90000d9501c05e061030020000003c101100361080d4a03808000104010781020f03480c030240021448080d401d6202041c91a43c44800140600c450360003600204106d80300e003001d00c801d0381c030704403405810703a0b102d084000310b004c0c4a03a0058043c28 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 639432239 1250 639430989 639430993
    0xe0a0b01030f062d0504020c1015080d11101803020706030b0a03111503041b150f050a03091b050111010b09010b03070203040305070b0c060f0709270903080103140c0102100e 76
    0x9505c46001800b240c00c0501d5100e516032010640324215070303481c4079022008841c0f5801c0c0046529092aa66852014540f114208240c0d00c21440105404000d9154000c0b1010b006104916503505145c0d82294a108181d0041c8036040c8001041ca001e440303440006040035100341002c03411030b2114180342d4240b803a10790704548002d804650520540c00030310f010340c0c403a4000c1350303900343c007010701c0800c2c1c00080e040f140d012500c45c14860310458210307010f000595040c1c189142c07500b949034815030081210110251802028101c8400101d80c581d02c21016904241c03115103410789003202103400c842e012071a07103400411290041c8076041040f80a5075100203584110303483d280d1241d90f224101442d0340d0000d1001c0d03501050001030407005101042c1e112503074640c803400920341000c000b8402d042921900e030f140240c20b81302140388000c0f02d01e0780c088004842814010380105180040c15684240704c140da10703072005180f805541c0717804103c0040583e0141c0c01445442036004441000300f9407441c02103158 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 639433489 1250 639432239 639432329
    0x111233011103070206030117150c070303050601180902041e050306060108041e0305070b0a09020108150a0b0408060601020d110303010504110405030f0c0a09060e0f0403090e0a0b01030f06 82
    0x40c0d6481780110701916807408290191000112403a10b07005d603c045e001ca40314920020400d0f8401d882007500c42040d05894003040380c0d16400c1c01aa01000340c900111003c40041d40041a901858bc0041040b1000b40c1d00966110341a2030300e0f030f48800d809014040d403642114010569941c40ba401480e0820f000301b01150002c01d03c614602200852031004401080011440b0400c0c8030148031f00300c4c1d1180034203030107100c0303079240f0b42c0024440900227065140401007499031b0312850f01d615900c0f0000d0540700174003e694070385844802e40d4900084420354018400c450308480002d04c83c210100c48405510011411642000b0410019000c80e41e8924000240cd100000709654100312201c4010002805018a40a518188250b0701c00035008000c8031030800038108040c50510414a50060204d181e80000c5d803200d1500304c40011850740031809024850b0107028803125540c1c0810059070b402d0300c040050030301141300c41c820784405114906101c140001c120840d0719140d1b0f5024841c058851040030a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 639434739 1250 639433489 639433493
    0x7030317060319111804050a0b070203091305061201091205070201022e0e0d0c0303150e0c0a03140c0901050c1c03020912190201050d11123301110307 66
    0x605600703c416103001003180000c0006007003000c601013040b040010420f4a52810303440c0c4035520350942c28000e10700c424038000204164802d20684040c2c52004003031200d2403030241c0400000e048160380c400d2044a40417400207101d00144140000e80ba8442069820000f480109858582013440141d041d8020840314101007020041d03105e85c85038440c891038142101e09165070007201d01d548244481c42d800044a160400e4101030010314155040c5004242150008805c0194002c1e540c4041181c4485206000440c048030002d4905c403a1150380801100f059000d024186a00c103440b80541102c1c10081340160354071620081c030070985d4501c212030100d0004001c40040c200d005c0c2041002917801308052900385442424442c011000300c1c024580d08410700040c40c0c0c4200c18483c000d060045c00920306404c021075030400b20100c982c0c0b0303001c681c82d8552030004003141c0208031646500c403401025a03500c80400c4542c850206182c410000d584c12003608015902c1a0107443c4610b050701c001e0001c100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 639435989 1250 639434739 639434773
    0x7020c19051f11280c0b0a080103120302030601081803120901060603061703040b0310090504061533030b060408010606081308070f0204141017070303170603 69
    0x9100c50b0300c5089001c2041d11504010000e0003000d100080503005501840195003554040441e203219040c42d0004440681c0b03013034040c041c42d40d4010340c10701c4008101c10301542d8025040f18102da010721402a0803074407045048040f880f0071075041b030200381d0441c082400741c00000000b0350b0007100708040764035000710842132042c04c180840303c40005039118141803240541c1400b8000040c03085184003200030000c41c84240d2030303010398040e103040c0310000310008907038a08a0607080001d26900c0010086401c2ca414040058000f8800d02d803a01c075803008000031703140180c45c00d030a14071400400742c1354610341c00d003c0d160311410211550340403d0748a0000b50b407940e42c6c04d80200f001304401c60000134420700e00907000e82108002003003444030420302c440349004107290004840f01e146d80104a15022107003817001800a001094242c22036a00103000c10190315680e25000055036804100d2105900c1e201c242965524071034080100003c4031a0180c1c5224001c000c1696000300000b800c0d00d031215410050301d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 639437239 1250 639435989 639436009
    0xc0d110406080c1e0904141611070e151807050301091b020a020d03030e01140a140601050f131d0a050a1a06090d05031204030e010203130e1302061306140307020c1905 73
    0x6c5500304041141c041d6070354100e270322488401c0042000d031290514001031010000d0000b4032500026542d0141802180d41e20314840d424071140f001c551005080403100202190800d003e1204628034240c090052194441c060864455595004108084040d4203000903846916411024075403a07068465115a080c0918180c0c3d035000381e40000d4501e840c2450b0410b8410034011584d03840445030512040e640d2000c2152116010380008030341c1c801107581c48400718501c941c090440ca00750740c4400c44001e02c401043c103004102c0820705014030345540031480d00320b41100184802d40940c4031036480d481e00340a0040c1032020b400400c040c410001070b81380c60f400d540c85100c894000d8540d41301000105070300100700481c0401700784029810300c0140c09440024040c1c0e40200265103844c400024018020f909021000710b03806042c0d1510b498013450382c000030442e1801031102090110842c001d03004020003d6a10074000c40c0d004000b1060b6000921001a1144400c440080311302740011416840e030b41206 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 639438489 1250 639437239 639437251
    0x30f0f120c020414160503041a0a0207030e030f0c01110a0212010902090a050f040f050316050c041113090b01110d080f0f070801030303050c0d110406080c1e090414 72
    0x3001c00300c4050310400049403885030b4511109100700342404180c03030b003100b080703568855641800c43d56903c1e00e09000c94a51106a48070000c5001c1e1b43c2005003007985a00a0705020707100c1e13210741c04180403030301c1010707210b030b0010001011550120440d0b040795071082c00541803103916038081d03a103220426008194100004c0a6082c016074490360460110b080c000e420903448440301038104000d00340b80e099501d500700c01400241451041c030000030300703106050044a004990f0800c03424400b01c0c0e14070f080741c0c4540303902c10035a100f1443c1009200d46500320303800300c440305007901207260303107490034102d4101c007c2c000d449089040042402c5202c4100b03000300030803181e002d06612880300c00e180c5104464100030b801880c0c1210398100318140610300390010005415039030b040c1070108083d0307286100721a1901030b1903921021581084404041c480c80d50f001441036441c0b03542e40d10721550b113261440c4414440d00a900311610028540160303101c0c0300300007511400c0c5004002183c080c2c20a000c45100c0c5c0b40903980 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 639439739 1250 639438489 639438497
    0xc060f060111070b03040b07030f0e0a0201080108150a2d29060331030314010f05030d050d06050a080d0e010f230903060709140d080301030f0f12 64
    0x6220030340d81c1001050728a110304070000d140c05802c0462030f04c034501001d0001418101d200c00840d90b581d000340c1000c0d486e40000d050812054210045807669003080010136804640250004110103d01143d201004d0684406079121a00c07034180c1a80180020107103080002103035002040240314860148407001e810340c1012605151924068000544107000398004159000601010340c440000740c0b50311042c82e00c01c0645148c0e1310103022003442c00e50014003584040300c1190350101a05030340100e12142a0143d09041d90780c03280c8030300030f00c00400d00850b40e150f0300000c0084002881280103090104104001180060b1350340045600c00c400c94000b20706a40014101208466000f14996100002483c2002c00303120003540180c40110103a00280ba10040c0d444620425030036441155a0340c10050111880781c07030039510041030603200d030094841494410070042c1440c038080ea040c0309190303000300c0400c1c510303443c5071380724012007806081c100c0d09044040780000126080e1500b402c04540e0b0307619 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 639440989 1250 639439739 639439741
    0x21c06020a050c0c010302070b0103110301060803220807030b0103080f090402040303031a010918020c1f0510080a0b0c0a0210060305032104081e16030903020a0b03150105030c0c060f 80
    0x301d001d0074110f81080c4d180c10140b05101e85400720700b60802103030460790003001c68034801150101090240901d030700192854480041e65000804030001c507243c0c2c800204044003004e540342e82156850700c8032448090850b40c42c400040c008116054014420301d82150345c0f039032401c0b0850010805a801691098001c00e58807030480300503001d01c0d025925203910074a4008482030800440300e05403003000c603058031030543c0400c0c046440f4a00300000c1c444948505048040e00e80c1d590280f6000e04400c9414450007190000001000c2d600040c54000e40c582c400745810181d0358800344482e142c0c102d051008118890b80c800b0222541e400d114600c050360042d00a0b50f615043c80402d9007501042d0511001c840e00701d082000701180b49071041d82c140c0810003402d4071080b0000070004a050061800f060400210003541004140d00000e01070100d07031080c0c0e9442d07117590361001e201c4542d0104407403c040740014007010715942e41c03044c00216403004100303c0712420418404007040c54900200d03100d00442c5c075114 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 639442239 1250 639440989 639441007
    0x3120806040c020d0210021e0f0306030d0f020a12030b101d011d04020a02121c0f0209060a140c030f04170a1a07050405090a0506130b030a021c06020a05 67
    0x1002e40d900b80c455030b00041c88160b100c03110083d580c4159030700081c41280d0100c2d13010070701c03a60500714000610075130401d00d132075010702880d610480d401a244c580c030070700c030b0504c540c1c171f5041c001d5145001c88204d54014240c5c01241307440e003198030107010b0715400415550b40307000440341d0f0b110580154091004d80d9044010604503120b01044c0729500d8160741401401c421021000740c48181d4140f804106036009a01e500f801c00007640741c03040d810705000421101140c40703c605289200b00c103030310b00ca00c1c0c3c800b48108091064180101d101d22000c940c1c202c402006044006405610751040c1d5039280c510030f038904515107e02d0341c00c40c1c004112034032805000040400c00e8161400084404035015805450800078075591a01d0b42c12003684628410311120b40010f08060103501910000c010140c507002c206c0c42c1c400440f400070b103c100d03a482e11944541d07011400c4418544a0700f0100c0030f000d0001c001054032a02001481c010060b01505c52120880481c0b0000703901d8000b41c9001160b0340ca0301d5455072224 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 639443489 1250 639442239 639442241
    0xb0c0409020d090c08010e0712140d021b01140d020304020112020c0c1509010f120605060f12100302030705040902040b0607050706140c0c090c0705060408040513060e0703050606040312080604 84
    0x85d41c070030f4134140c4c103001c00000500c2000c540c550864108283d9206110b03042d14014600c0040820f03500814040c540c48010348031b40125680d01d022603a01d21103150071460500542d1404841d1125100d450014401a10b01c00c4d0380782d00440e0050b0050506410b0781d00d030000c2c00010384c0d2000103032440b60342100b0a10006410041050541c00c0c03c4d0309586428941c2460000b400c280802c8890401c2100301080380d101c0c81c0c101c1d03201c3e8014003806025640e5409543c43c0f90310711b0f0380c0700c3c29004c00d91902500003c1e40300328880212030180c80c0c0c0100504503c520300820000030b01844a002c0ea0f00c1903940110000740da444000a00d601031083c1c0241c03804030301d050405081c070051a2010340f00301104124116403c0408036020031303251406c8070311034a1516907610032603003809003200052952280200703000c00c1c0000c1001401c21100103d801c42d203009022102c060907a8400e01c2181038605c2c1c50b1011032642030090f0000c55001d4000361420341001c1c0e0765120b04c00740020384550301001c501c074002030010a0402d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 639444739 1250 639443489 639443513
    0x50411130203150d02150703080709140a050f13050a050108061b160305040801020c0f010501050a03260c0706080603010c031b0e011202040621050907030b0c0409020d09 74
    0xc044400c50031854088500c6440c1402102c440d03100e83d420341485011503a84a420400d070104100600c1d48500040c640075003958011f0750300c3c00210b440280d0008802c226103440030901103002c3c01980d5407d28100034043d408000b0801540e0100001c8a4080080450310620b03119881991010a203941350090351030400102426450b8031240806078004404401c1c0c04458001900030302c01403090a2608044440d80920b0308110344c15400005c0607481c074840065152904485003000f04426640c801c104507200d40301c1e01c4000c1081c1010040441031041c1d40d601d03400e4010002840710314040d00b81b0251030030160076411070804161410306006e2036050034030032421806030b58142000b5494515802c0c0c8510110080400100101d2108042e8641d1060031a10b4940c88040c4041d91150b440b02030152050704107155807120200d9140450001240c10302806000307050b050040e110460131901c4c0d1550300d420003002d500030780743d0400000803010543d10092229200c1c2c020f000441c1c2e00140341401c22011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 639445989 1250 639444739 639444769
    0x90406180c050f01090605070803070c02131b020309010906030b0d05010c0908010b040614040b03160801060602120301060e0d080f03040b040312060e0c09010c1a190203090601120213050411 83
    0x107107540c0301b408029040300459034025004200381d501d9680b002c204403509008414000d404c1500360b1300060340d40695811010046c5000e0710101e60380040580304030380d42d0107001c18160001c0c1c11800c003046064000d5105000c0618094001c03200700c5110388071075081d5210425021700051744400e0070040b1440c01c2c464001d080000701e4060145030300e410754001c200204042010f00c550383d5520303202d00e6940c04200c1a1485070280bc84040c0c0700d0380c2d905100f4001c0132a8810700000d401130f031030300070000507c800459060f00c445440d0040c1c00702099003030140840340c000b011204454100050101c210000c8003a6119074440c0703010002e10728091078010020001c00484803851418101c00340450442d4004259100402d081040e444d00d030385400403900880d5042000d400400c0d925640020140c6201416226505000550800e958040702c113000301d1004450060503174201c0001440b142c0b00c20441d02d07907800d000400130703400d555048000600302c0d00306850484003200086000350582c181901c112010035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 639447239 1250 639445989 639445997
    0x602031e0301060c110607060905061504020f030a0905070902070507050a080c130f0b040609020301061106070807120e0319021b090411032b1d0d02090406180c050f01 73
    0xb502d468800b52014032020703002005d0656003044481d040d200c65059900d01c58002100703022145e0700d4100940c8962007640c5003948071740c0000c00c1251500b0140225254030200d0701c90185140d99a508004c002c0070031140c11200d50080b40360000c0c03070304407900140075918000c00c0900505460a0b04110954400350b106200c84d400001c10703207445607240080d0808a090180d80804d10007001c0d42e171080181095540030758401d250800105000c1100e50145042c5c81207905c9418009040e8401c09a03a840704480550000d0403120000d1040d520403440382c46a90590304000c41c0759690320042904680029030354008000c0b140d4201c03055554100a040f03001d41c03000c00e5010480f001c560200c0c018040c01003001e464120f5500100d071983c1ca0400c0451807021800840c501c01d41084805080e8408843c1d0980001840c06095401c852140e4002a401420001c080d45450310440c1d0a000082d00000c0081c0c80b0a0b0343c1300d200030000307101c2004118082c4d00c01d0300c82140150609040190f05241c1c0000da80c104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 639448489 1250 639447239 639447241
    0xf09050a03030f0311160c03230d1b0c0314100204080c01050903030c0102030705040e0f07050a030f06050405010f030b0a0c0804150209031209090a0905190203160602031e03 76
    0x100b82c0200d4904010800f03842d0108034a003000c10125002d10071002c2c1100c0c500342c1c684001c004d2050000341a0700f560310441e05012a1110441e00f04040801c0e00c6503541036801180390448490300a000c0480071054038081e411090f0426183c410072655150b206942003681c08442189130f0300e05000302000381c07280c1c103411810036082c0081e003a62448038141c00340c103010780002c4241d4947e6007041554130102c81d80d03000355601e1030078000c010450341140c422290700362a04808114a074051364401480f420a907502c0c1400c186090004038003416076050b5151010b65166004200c41d2180d000c1c1d14080c00049641c188410700c3c40ca0461002d26000300b030300e45403a1901031810611036000b010b96070465000744400002c400001000c0e8000c1c4201d44855070301d4440d03688074507500400741001d44010f00701129401e030303540e6500b04003a0a4800f469801091a08504d50001c40020005665003e80c1d0001d000c5441c0814020245092443c0d00e80001c030140c2c0c8040307800e4030140c0710304401c112206001001c040c19 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 639449739 1250 639448489 639448493
    0x30115021209120703020d11030607090812030606211e060307050f0a09050a06060e09060102070308030a14090102090301270b041416050906030127050a120f09050a03 73
    0x31a0142e08441846014000145452035008129907009950000d10820042c0c01d0f500d01680c400300a407129601078004c400009000364019605d160455118101130a421070a0100c51101e40d40300800c07440c1e22503401d001c0004141040034a580c407803e03250792400c416062a40c0ba0891003c060200c940c5015024020050140c80c04142c0804492081e9109a120303c00c14001880c1c4103959080f90001c140784c84104240302d103454128400f101c06030348420032100880014400c00890403290366026900c803035030800018403200000c55103c1d0102400259a0b0504030411001a8003500d400c142d5a40110f55001c8a01e0700b0700c154400290142030745a858040b42c031003040400040000907040d00d4040000605000000b6541f80d540316071030068a0001804028010008005000d840d024560901c0080c50901f01482191002907070044258100c2c40320031140a035000031848215242d01034040214001405a480032218141584884214800da035000501d11403171036000505c114442081080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 639450989 1250 639449739 639449773
    0x3070605240612060414070e130501030b132a03020a0f030302150702280512250515010e04060b03011a04020d140915010b2a12070803011502 62
    0x25418510000f0301d034680d113500c0090000e042d070b031b00080c001c040060704004a041e8050000c11100000300c90021540c3d040b0f482a4044502c2404024820070044001c5408014a4080c100742c00344100e103c60030200409e120b418820314580e0b0f88651040070382c501801180703840440d84002c0d241d00800ca580e000c0c43c54030300a6584958001043c424418100824181031007070002c84801030108440d1214048858040b00c1c0001481c00c0c1628203028524100704400c00b800120343ea04480481c07103c480f00001c07880e1345e010341c803a01d104498620850b007a04207440000094240200180030b28840307070b0715240c182181600c0d0300c41c01d01407203640340082180f00c500043d88103c8020350305075001a21142030740c4820700246800c2c1c80d0550710b0b44011040100b0b90380006210340b20f04040c0b03540380c00980d9a0b5025445640224080c0550600041c0b07d150320048030f240d00312103503250800480d44000d0000c201040b4a40c03061800b031b0b40e00c0c6000001845104452220040320022074070003040343c0407903414004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 639452239 1250 639450989 639450997
    0x301110f03041b080118230c12031e03011d10120204020904091506140d03050a17040f031b020f04230c12011a0d050c040305030706052406 61
    0x2003e00030042e040d504107400e40400300020b400c03000e00800205406e820469080703114000116500503c502403002401da0146410208070408030042403411844400c103c94602c2103004181c141c80b00380105504403220800b40c001c0e4580468810781e4950501000b922002068000c0c0030551595000348208000500324030821140303e00f85040c410011840001c010744180104187d009003080c18242c02d0140c0341b8440e407000313000c001c820001140e40300346043c26020502c54081d401016600da440110340280003d000002c000e150510040100d020f407144d800e43c0c251020794443c41244004010540c00c0300d08032200c0820840460400b25107a80069814851502c01074000e40d22210706845a181400181d009009440040001d07403030010403045050f0844040804071003001d07400000c44c1c86082c0315120000c2041c114083c50304060103040b401a1a000c1c0c85c041c280300c000c11000000c503200740050402507100740380c0460503050080407105100f1030040340c40300303e43c12020b064886a5600c0119 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 639453489 1250 639452239 639452243
    0x310060317121f030204050709140f0a0504090c360216060f111204050607030b03030d022503080f010e060a050d060209120303010e090313270f06050301110f0304 71
    0x504103c0501030b2400c0c010381600ea03c020340060a0505010a1a400140e10015901301d8020082c008800d40108074403010500d09240d0403084402003400b5505140d0400490300c1d002c1d2003941c09040d9034100000961403000852400300c0c1008481c0c5c00c194000041c00b21a0002d40002075082c00000c031304500b074010405a0080c50a07a44c1c4102c42046401e50304000c044105c24961039032143d515034810750b82c1c42c1c0c3c00c5600b04c0310340c0515800940310501901c20b01c103540ea0041c00460400881e111040004e601c14052400ca4510400071400201c40016034503280600c2691850705900b81000000710754a0b045e0030a204080d003c20030003101d91100c0c0344520032130304221240800c2d0b940d2410701c84020f205030300000307030440ca10ba010329240740382c0040114104c4914401800d0103503140760815880e40102e5400c4e419000085500704010942101c00d505110b6160141e0744020040c12002e40407a51001640300303842d41c4a1404110902c1d081c031030308030302080020b0749615211210010781303d10f200040c80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 639454739 1250 639453489 639453511
    0x607023307120801052b060f020a110106031a0a0b0607060b04180b0610110f0106050a14090c0c2407020114010b120c070507080604060506061603110a02031006031712 73
    0x2910429055498078901e409810000420000300104500002703941300300140c038085030600088604000d014491201140d030000040103020300d443c0e4441d00d0307003540900300700b1805481d02411141a615003000300b091501c54500060190254020700081d20380e00d090300c107090070510083d02c02144a000c00154410170071128500c0d010300d0700e40d041c0c0309400314070107880580c46445181540031005501c081c0a95404480081d001b50ba120000714540c000b10002c19005002e00000c00c42240c0f501001e0f0260000b800103682c2444c450344013110606940b0700020140e0031200040c459565028440c1d90103851101c0303da8002503040c6100942e0398071503c600012480000d100081c0d2000782203056909490340706060320703005941c0c2e2031015900d0100342d6050b00c15a1a10f0302050080c6442d40454588459000c6140c032191060f440c2501c0c401c3b0a100d84140c0350240700c031080011703942445500b005482c204000a4090b003541820525107841d01c403006d418100401ca038552081021441c1d40e442044844 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 639455989 1250 639454739 639454789
    0x90603030a0c150e070b030103032c0103020f0705030703030b0a060f0c331a0a081b030304051809010b040c09091e0903020c09090c060702330712080105 67
    0x420f4000034104070080e03515034014003401103840480080218126030203036440c18010440e04078070803030f602403002a04410081c0c009049109500940191010704030f840c1c10319062403965141e4034196408124110002661762004941c1441c210032071002070016031170203050031103104c4000751510405501c007810310354041c0740882414003c44840c2c45181d0038144480400d030455805d18000d0080480140c6084030300b40c00b051084e00703112844000f1204da880080900e0307090264005426101c0758111a0140020000840c082c3c4070701c02020552004882d500d600d40c50000f40c100d00b1143c1d81c4071070a10813400c2c20000d00b41164404000707010303104400c00009581c00019100944c2c00d103400c1101d9202802d001c1c1035002d15402250000b40741c281510f0800660355001581d0741c9420b85d070810568003007402e0001c134000d41400c0300300054800c020303404445201c01e003e0220740000440303042860100340000f104020030040e82c140040c558000c0c1855803841d414600000e0410454150182045003042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 639457239 1250 639455989 639456023
    0x6050d0204050301020a050c0d020d0509010f0908010e1006050a0b1b0a060504140606030f1213030f0c082512030201090b07030510080304150513150e090603030a0c 72
    0x541180d0080038003c008542d68404454040c08580001c212005580034a07054040e00d14004904d00001e801603569042c9004480c10041d95648548500a002c00103040300106400f1024410304413114802402020310250f0943e03100b0640e001504803a02481c000d01c01000802400700030744040c6101350707410b0b2440e048443c41d02858404030300c502404280c108400e0009100b001100c410134881d4050a4880e2540c4860905a5a174244141d8120650041c241e01c81c2c038440c000c020700907914800d50400846952516090b94010b03d291082c2d51030703400080c0400c041101006012502e800f40c0d5481143c0c410004108140308c1841d1098261142c660749408082520130f5105852050b403042c0c10b8843c03030a021000070700502044814418410600402164020000003618122103000d080d607400717040e01c0201201c0c40d070000c0c034201d144802d400402083d0342641f0230340d258007220320f96500e02c0c4010424003080340c0c002c0d020304500c1c042d4004000d10b8a0840d442415004080d8004042e0710f20303074042d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 639458489 1250 639457239 639457241
    0xf1d01030807031103040e0f010506070b04082a06010e01320d060e0c04050a0905030403020d080c0604060e010b040207020f041d190212010b0d03080402041e1d0c0a06050d 75
    0x8400310948a00000402161308426424000d010780f01d0348c00024111382e21071003071000b81e100d90140904090103500c0054009540c810003410140348030b02c003c0d03e02000c1100c001d02c0302c0100e14111b004540103000188811456504168010004501c11143e444c2075400f4180100c03076a4a1140720900ba07564003150a0303120b0595020005034080c031304010035084a42516107600da01007070148101c0c105400f14401034118001d071601e9680000155140515503404c11105200840c411181c503070303041c817054040c00002c0c007809100c1c41c0960401f0803032a00c2400c4e483e0858040300c3e02544160710500924003d80c441070100c0a10290503940040d46203032001c1140359141c0504005000c5100e00c0546000700b0920008440100c1e100f0f07201858989400f201c21401d0300d014040f09a00020144061800710740f01d581074940080c0003620000d101110f41510142d05120174401800403030f03c820900103039010b40d240720200404148041e1841c119000d001901c045650b128080800c200825501c0240c90b40d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 639459739 1250 639458489 639458507
    0x3031412010803071b050f0607020310090c060201050c12070f0e1201140a02122409100e090f0607030b18100f09060e1605070f0305040f1d0103080703 66
    0xc0d4400c0d030121503940c1c6400a689904c803141c2181e1000309402c0704012203103901c51035801c2d2040206980ba51041d04030600541e0707000030406903418410340c0b180c0318410102e4032981010320300a203450018039090010180c01d6400c090f019411012082018040380d13501d40030029007045a074a42150401d1030301e0011550304080410041d4820081e102903034290b0015800240d5260354051b4410407a075906c84d14100300d0040301d0348051092002c80000700b02d401c1706441e940040b00e40c07100485900040d80c020401c1110100c0c0d41401d0580a280f0601c4440110b1005a521440c02001031030000303e042034482c1c80d20700191105040c1610350341e1510090f0b507a00113800e00411580141c001a1034081510b081c9607059200309444400200f00100700c40c2d61a01503207055410070980400c031138503024821b100204880076400d040020a0140d200018501e40c491590030740607607241c94445007821a0300b40007078032f50f41c0051401c0752400c02400c03501c03184030300c80c9045a8102c00750b1621b41800e410242d5503640 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 639460989 1250 639459739 639459757
    0xf0601081e0c031501150804020a090207020d170414030307021f050702130b0f18060d020f060d0605100207050a2d0806040303060b0901050304110307080d11060f0709030314 76
    0x41c11310704032051604001828100d910040c5d400c16030001c81003098032506010f64000c1d42000c00c800c81806074004a0300140303801440544050840007950322901d20182c004006940c1074100007504105000040c803e07942424030440240d4541051070303000030100700132000300401203103a00180340c0c1380e03034010400d507040039801800c1581c81c1c0380380d030400d040108040c041c0c0502c01d20100d015114075090070600300545e49025491400381d5141e0004010307600742c440c441264400e558081800d034684541000d06003d0002800110300541020108034402140b560520119404180304100f11b6591038402d0080740d054070801d100b030041240c0066685158030265100803100c1000000d001480054614481c40c001e94080021585440e2640c1e031510600c10200d001034807d20104010503070360b9118682a0078001c2c1140c1020781c1e612803440c02c1c9186000c1480114108580e01c4066030001e1014591042d081c080c80d030403900d04000c02070701043c1c0a01014040008104413010b20880660441d42d0a107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 639462239 1250 639460989 639460993
    0x1005060d0e0d030b1f140c03030906071407030503190f2c0c150c070303081608041a091018060e030406021f0b030a2108100603090507090606080103050f0601081e0c03 73
    0x60001f800c0c0e59941c030a44101c0c0b01031060308009008140701d84903032401208880d00c018944001e944084855400c050a40d00d05000f285072004000d0100e446075660b0420a1000451340010a004c13440c0801200da030185203400512810030807105001c150811921800c131070b0003004d0003030341d20395041e5805000b14280991040c0308011040c550000d070716500c14545410501118406020100e0704241d00f680c0092011400904007000d4000600c0020781c807100c50000c03100c500e80c000507110140d403c03021100007980b800d0101401480100d0180520440061008500d880d00d0244003e586203000150034075072008403446002c19a203e900000c608000040031640701c4801802c00b44d00f144080440151501d0541012100c01409642c44030720801080a1640c00b0910f443c42c1a4050000200f0440d018003490380040b4003007042d88500307009040a42e07541c51241d0705610740240703480c0942202c0c43da142c3c0600010072072018001140710012010808038000324103020092490944088601035041c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 639463489 1250 639462239 639462247
    0x30e130603050613080d0e162607050a1517070e1c021806030708030d090204060605160f1113050403031815051005060d0e0d030b1f14 59
    0x2565603000001624080c000395806600c48000791a05200c040c00e0082072101305110307115248070968000040054410b080d030348007600340d441310a4039174a690030030701e0300c082e180c048484048203145607405008020402800741500740000242620348a104241590720741021030440c07d8410101454165030b502910081802c08020141080001c01070b514014111140c2d50101c908064900709185a000b0340014032030041003040c008646c000800c2c641d01407241070782c00211001d04000502701c0c60420070300054a04400e104000c10358400758400d8040050500c2415556010048035400f01c0ba402003141c03042022607d0002038000d8042040c5910520000f407080c0d1910403504036502ca10301c6580c0400194100c1240c4070f803d0502aa0040d22918250300c080c1c96850b0594000c0e60015030001e50540ca1642d108000750340e80d0706c034a83c1500170f2a03d6181c1c03460f03800000c0080c0c0172b152071b19040c144218000c0b02c01007100d210070f0950017403c07440340307040c451407640c05000b002c1055034003003903000c0c0c0e2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 639464739 1250 639463489 639463519
    0xa0e0f120307030b011d300106050907050307021902010207030b190f0507090e06030a062c030405060a050d1506030911060f0a05131508010602010e010902060405010309030e 76
    0x401d40040340d8940c08a07040180066440d0b10a01c0c508820b0b004510000d07074441d8400d001c0c041c420340e10340124907507010200d1600c0424807511151100310f82c0250700206426050038240f00c1c80120183c4400107011090091124041c1c0200b451580b010455000d010380c6941790004078549140b075803000e040c44191a05120140311844083c0d52000d1039071078280b1510039801c40c1481114000c4a00c00006100d0700800e1101600ca0704140d81c1002008044450040300c584801d012512010b0390a00d004840c00e4050042003000c1310384406441c84500903505240c0760030301080580c0700d10311000c410000000307a004000700f000d50108400a04000076482d0b02612400041d0040c500a50159915800d100000c007061518000321420f100b600403185d8102a400e08042c0c459421150851540c654181c01c08a60420700e00d01414402145548040c0c1d15403600401a0841d810000040030b540d0410340c81d01d0250b2030740012241212000c0c60300044079106410104c501e182481d0300a0740c00800e1040e2010707 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 639465989 1250 639464739 639464773
    0x6090904050a020907080f10060807050f040b0301080106080f010603050c01080703021c0b310506030f0105160807020c01080c0a0207051302210f0115030b030a0302060403090b070b0a0e0f 82
    0x40308920100c1f00d2513140c1c07150300380f00f90341501c18807c00d000203c107103001880d5144150302600400c0041d428690034030342c803000c43d2645030b0802d8200e011240c0d558841008010300c100300e444444010032008201150441d01c2d03007030b2510101e200f61814444048040707000c9a1299045842c1c0d00810140284130300b070000c1c195400352007182c2d0618420320320740b0040245988284070040c045c004030584c1c0200d800400a060010f8840100090390601614949001d111020b006aa2045000c41c40c100300300c00d500c601c042c05500001e0a0101154003030498800700d40d81015189030040d90100b482074840e2004002280f030141940c22146d00001d40307041d22660b41a140d0082e200030322000c00c1d5403d00080c0d07080000c811034011a03036541107072b40040c0100070000122501308401c02c414600406c0d5910490046880c02d15070f550111700580c05001048289540080604090425401880d2425807561146105180f01400701c40016955003c0d040b44800101b00002c207800c1c01800340e40c00510441c000b60 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 639467239 1250 639465989 639465991
    0x1707030b01260f07030b0904060b090f0402031b031011040801050f061f050708030f0a050123061b0708030a03180c0b070528030e090606090904050a02090708 69
    0x18085203000785002ca0800c85076103040911110030030b000309259906841c60121250241616040c1552102c0c00c02c495110718030a94448c501542012803c0b20b02e003002e103c5000300c01041500c03440000b00602c1300595000c985e0040c0c0140341e40c450005101140c00090500088420b8240250304d415040203c12540f04064000c070765607074000f004196101e030004006400110341a82d400110a0003800e0040c81c009e44030044030300c143c504142808095602c1750101c0d4010384041048403210810402d410035640a500c0c05001c1c41c0084d41d010101149129403041768041c1110b1140c20085101003062440b140480c035007000b00320841d01c59664a441850b100c1e4010009500000d0401410610301c0180c4c1856410007540b008140000d146402c0701111541c108440455060103480e41001c641000c9120403101d9080d1980c120115240e1031030041d2905545d421280d009030b02d8203040241540c1c421081d40c0411101741ca201916588034501a82400401000250300c001c40106120143c2c1d40080d05c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 639468489 1250 639467239 639467261
    0x4141c1b0c121703150f010c0b070c020d021503040209090a11060703020f0d0306080106050d0c09090c0905071205070203090a0303050c01090c0306140c0f0d020307170703 75
    0x10001684116203032404144069601408118160800300100d000020801c800d80d40284003032503900718684454442d560041d030303107241018807076034100c4140c0c904548004440c40c0300b400d050031a80011b98804203003840c008d00440500026520100039910344420f0b0480480d4020100c1c0000e4a207040013503e03030b07042640d05074052107881000031440c110000310081c07040d0304035040c00c401c042c0040070888598001d190440c1103018070241e90020050810069560210585012030300300c0c2006641c1d801c49041d86c1c0a684103a20904074140407880080895040c0c5010120100f110308582c1400f0405000503480711808034039100421580940c000a4810508803071002404103844804080b80d80b8006c0301d480360341c401a4072030100700203401a4002c01e4241180c8001080082c581c2c3c0350500d116000e980240c441340d803114000400c10403a01004c640c8040741504007428451a810300307a00c140200300082d42c00790340c000085500b01e03000740070389560b0940211144210745800c2000401800d411103413 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 639469739 1250 639468489 639468497
    0xd0501030507210507030b0c0d050403020c030105091218010302070c061d01080919170a020a150c020a0b0411061b1209010c1e080307270f0306020304141c 68
    0x70085800d840d0b4420f40743c400d0b00301d401829600d0035a01c50540c41d040c080c0c1007074200d00041202c110440302c180981441039009801401c081000c1000b4035003941c070014000c2500d5000b19102d42000c41040e01a1040c01c07085003000c40c0d038a542580140d0003803281c0381000c2d2102e8007000c40010781c10360040156060340c0c14480c903003850408290040d50b00c0c030010f56582520380c01040284001516131340e15204154011072038020651000060814140e02201d013a00060f0801103010040c490b1241440c0b100340c119030420880742a000800940ba003040b044020440c9190f400404c0a1050302e0419500409000748540c1d0303905c1d1100c440c40600d02000428440a0041211050541c0303c002c041e18196201030f1240194072045a54464040c0480d132150a0003840d80d59134040032a01a4019601c10030185d00c81541c904055540c051910648406c598104400d1400a00104910380c180c401101d900080c0580c0300d840303900c0c06c8128041442c02d08141c034031803004520f00b0f03100f144a5801d803810054036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 639470989 1250 639469739 639469769
    0x1e050102030f0304060510030c090c0206011202090f091609061e03020f190e0f06031501032f040c090927020d08070c083405060309030d0501030507 65
    0x100680e100d02400c007a004a5403001d20024020a0081d0001c0b5881001d0105161101d85c6940d01c00460100d10380202c09001e0b610303c013541c201034042020381d01604d0a0523203074000f4000342d40091107140b8010840240125680c000c510070510030008440a005c24a00c40d1f03c05546484240d001040760b8454414100c1c4c0041030f40c110080111070410135030390040c01105043c0c10404c00e00100c04140305940174a00e40c801c800240b805507002c2064003030341102c86400240c1c10018201454001521400341840d60340e0401000002d20710b0505045100ca8000f01500c40341c1054141000058001c0b80d6a030854100300a82e2051680404120269401c1c02410401085410403044076402c001903880360641d02800d80d0350152901c0e840303141e841d0340b1483c0c030030340380c00e10b10b80d25078070801300545c0300300840d03406030240c020031464564699541841d210904d03502c50100e0103500030f61503400c1c41418040c0100001064800000f8811640f621b01206014000c5580d2441c1081e510941c5109040303009080207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 639472239 1250 639470989 639470999
    0x18240801090c020601031e0f08031b03152e0207150c1e0609170d0c05120a0c020f0f030318010c0504061209140c040f022118071e 57
    0x1214150b0200419801007840d607003190789603960302401d40e4070012041207141082c000207103003e0ba003142c214809c0c440d490300c0742002281d50b840b04031242061140f9810510400182c090524064070781d9280841c0c40000c11020751450608a01c610760f8880c01080f107500401c50600d800141c00c2d41200c2800d855820b18524035030701121220305100700105240045003200500c40540c91440036500e0180b0b400050b41000c60343e48010700c01000008600c15003000c0b81c0038101e25020710a4466142c801d083c00d0786068501e000c80c40340610000d2203d04200d03a91402c1ca0700940c4200f0192400c45643c100300ca4000d40c4402096a0300e41085400709d170b4100700988010402c10045c0150002c210740307611180d050500301072040d240010506151020b2903910f030304910101e00d19065140030300158401400310003074010b00b4001030311140409100410300410031102d1846514040008102c0141104950b54440d003020440b410303446c2a0381006413044040c089144d1024032545109401d1410718007480303e03a68 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 639473489 1250 639472239 639472241
    0x50f0c04060605040b07050c0405090d020c01020601180f140c1b1203040b43030b03030301150201180c18091e0203190c0501091d01061824080109 64
    0x1d40110800500280400c00c009010703080641031a510400581380d03c80150b00119044580031034550710181d00c2006510030310b940501001040389000e101a040941c1404007055510310034003100c64200c1d59498070120311800301d50001070980c8240203a4005410180c16102c007030780010450b00441d4000c02e02c2001448000100013180550fa940e01504568a5032100030144c000100350440b4034208149454280f0107400c07080c4a442c1d01040300135007440c1c60401234101f480440706c08009040c42d0145540113941c0c00002d07241140c00072500032400e498011030890143c131140303002d07692108042c44100c007001108e04118040c0c1d1403940c0344116610009101c7e41c140c9034003100192030444c54070103000701c90144401c10106180050212010107145054070480750341c2801e020b496860700c820080c06290b88c0000f009008103480340044500c0aa1004c44491541040c0702d50f600b44116400c5020341c2001c3c0b064008010080004410500c00d442031400045880341c0e88a2000100760707500109801103e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 639474739 1250 639473489 639473501
    0xa1e021602090403020a0b04030309030905062809050901170d0c08030a09032105240f0d030e0d03080105010f0504120b0903190507170a050703050d06030f050f0c04 72
    0x89021000d0004107038082c001d1a4030060419400c50103541b00c80c10104807901a454003a0f8800d41d00010b040b2280d05004005000710f07003040d8828a0104401800384c00d0750781c0c0c01840f071003014880c60b00c1651000d40030394407840a41d01c21600716145100001d40c407840c5c64014903200c428401074801070522940100c1d00004000d00083c110001031021540b80e9100c1d40c042e40b80a8480d040c03c01c4200c415030ba05409442d08482d003c580e05031200d08009000b00c0342e121703d1000b10b440c1e01e58002142c0c001e000080c0ba2035151a40740d4010761100d000380c010305214907900c19102c40040c110604151613414000d10002090041501065140e1240600751f4883d508440803100b17804400c91000610381d40d0b104032304c0e02c05442610203210031b210b0300490544800b004626400d00b912901c2e035031580da14090340c82503620502c480748800300b403001051003508401185e010a92500d0100e076591000c01d1650014051504060300b12062411800100000010f00c2d00200006a0807110103074510000c00040c0d800c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 639475989 1250 639474739 639474757
    0x11090307092301030b010b0d0b0904050307140d120f090f0c060306140a271a010806030111030712090632010302100f02030c1501030c0603020a05041a120a1e02 70
    0x1403005c2c010480c1c4880c1c100580041000c114022824070b0301e0030006080c41a0a0314192145e4000017010010072041e510110b120102000280c280601e07400c2c2c016000803c1001c50b018496102c5a55180d0290994010f10b8400e501144402082d01d803410981044480b60003200d0220b4a03001c00850000301c00d124a42a4400052100d18210304011000d81d001c1d45151101e82040c13030a900e1625804514011300c100c1d042c0c161a5511440300c0000014800240905080e001c4e900d41a12082810144001c41e80e1044443c1040d081e00200c84003074400520300b207100601058548a600d030350542601148940c4903e000c9020400c6911180e403080065500b840001d510100107143d0400300d60143c41c940c0c2c1030031928010b903820888005d444505084800000d900080382240060040281c140301001c0a042240360450500417511000b4101e0710840c007070b12625035180c8003c07402000c80b4608590303140409011421240c00c3c240044009810685100c6908010070103c0c041ea880e0385100b0b030b4604003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 639477239 1250 639475989 639476003
    0x604090207150603080901020106060305160818120904240e190603080301082a22020c06010f15140c2404200d061109030709230103 58
    0x91504a05000030740c40369200300c0740c1d900c0603441c40d079200c40c82e40b050100440c062000e05d41e072040704000082c212000c0783c1000e400d051510040c400e00c0104040c0c00c90b4140f506050240ca680ca60640d01d145c0c5401c000905203c51103072850000b9103038461400f604000c80d059800f07021403a40b01e03000705d86641052215042180040740d04100c0300f403100007a90780140103907568220500100c484541039500f43d80050b40d0341c400000040280b50320400c0800e00903102c60103041030104c50a5150400c0c0c11980d0201071058501800b5042000c0310b420700003c8034100800e0442d594025102d4840d103440b82441074039444c12192030300080b40301e1801c03003580702c42100b90341e40c00b00150820200078075038012100300c810503c40d03220503134012501040340b00c0541c424600c080c0c0e55840c291800d07400704440d4100d050080c407498100c2001c951210352400341070b01d60246010400c1010908142c1440c010360005c80d074548103800e000102c282d2280d0028144280ca04901540321320f054410403407005003803000034441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 639478489 1250 639477239 639477247
    0x7080313170705101d0f1b18070f021002190905040626030906030702070317192001050c09041b0207030311030405030d03060e0601020715050a020c060f040305061506 73
    0x11421a0b0300c8024041c82c05c2d40c165990544441017145082d46100100180713074000c0b5110200c006010303404c0000c8400443e88005001d104055040701c54202170700c00300512203c41038240499009104040961100c500110b46400f140900509400751021f00c04002c50b00c91000890303036090601400741074481c541e00d406071884580070300e62a654142d5080e440c40340814082d60045654450045004c0c00f842d43c01400035500310700300259403103d0489000c951100030401450070101040c03c1d002c0301c480605150382601015522030011158022054000d0b510703100c00c00035001c0040380a80b941c03200640b030804c241c002a0140f001031004140481c009688103c0e0201700081c425503014505400f000300362410941d441c4040703842c10044550784030110381c0300e990502980c1c5011a98581c030480901c0104802c1d85082c40d06044141d00e00c585008210340000c1c03118685008103c1004021030280181d80d0f1031603141042e103115005804212803030700410005c1820040284102040a4002899a403170 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 639479739 1250 639478489 639478513
    0x15040e03041e03020402040311010f090501140319050c0d0e16120201180603050726060105160b090616020601081009060609020712091a090f010507080313170705 71
    0x22036032441009800c2d40400c0d0110050300e6038000341c4000e40c030654403000c0101e090400900365681c419217582c10030128100801023aa8449007074040100c01007400c5030303a80c45a117100b101d10071501100c860580d051606000c4070921040c01014903802401c02041050343c1c1042117a203405595a4000400c461602c042c00841000c26100b2081803050400e15810510520003080b108180d80c00240420354540801400356008590048000303440544400602682145910100700140040f4100800480c120a090030103090720000580c0003411500c1342c1c5070880850390303100340848542e64904031401e0703000ea9841c00050501d050702e4002014003034141034841490700400d400102a0340c055207a80c0c00003807900030340c03000381380560041060030b080003070f00074000e0300500d5103a1100d1401c90704000001c0440c9881820b403030380303110100d69608035481c4203c012210343c00f84030405090b4002c0007040c8280384040000c2c02da8424480c2818900c8088002a000050f0280e07810290041d08000c0340b84c40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 639480989 1250 639479739 639479759
    0x1110f0d0e2d041b020109020a0e010b031303090f0308030a0f11070b06030c0d030e0103050c04061d06040e0f01080c0f090a05100308030a1d010627060b0d020315040e0304 75
    0x7480b240240000800a0703141d40c12140c18811101140007503550f881000080d81040d0038200f010380f401c40500d40303083d40740c050a1061803000130030f0040304449602070401018440c14a040c0101403a00c029012a40c4a0400c40c0c0545d01c19211481e6551800f00e60504485090048120b02c964141003182090180d1702c42d520840302c0140a1a818020b8038000d01480e9641c3c10b2a030103407800781d503812000d042440b0014040700c0010f05031a1311035400b80300c10401c6035405032600800c00c030102903002802e40c00b04003160f07070b501554001003503c240f00010448071341003e00e81c0c1812280c00c0403c60700203c601206105801511201c8a034100c0c41007000200052115002140c0000100043c2011a99291114801c0d81c005030b5680b41003580344d146015a40c0d60304490138280090300e00c0204141454400c40c80a12142c986001050003000c1512b0703512185960700110040c0010345035140e0b203089490514009602c100e400400d4194a089240020305081c0300c2c4c640f0b030284941c021484d050518400b11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 639482239 1250 639480989 639481069
    0x9070b030103080f0903012c0f0c130603060c0807120509031602180a0f1d0304090e030c0a0c051507030909020c0109081209010b010816030b01110f0d0e 67
    0x1900d03200410981c0006e4030309200d2402810104241017030305c0d444481d0b0700c0c024a0000c0301003c0300ea07401440102940000824545c4201804496080703400c084203403040080c104030b0340090032151420044060051300302d810984030307014a54440e514114002c6040381101d9003500c0d2111030350700506c01c0f07032003008015011407117241c0010000040324128641c2001c3d00d034401c450a00d4195103600384c008004650f0702600c05820b0a00242c05414454141c6c0c41d03a0760300a910a00d81c04a0302c0f0a071f242400c440a004881c1440d002d00b090360590800d5040c04501c2c9030784d91082034041c441d80d240b00244450000241c0300c0c0300341d06680b40200e0070702c0e005610010303410009988030310f95030701d01c0202e0000d00b520000b0590b80448075103000c0356180528400e401c4444034410241400300c01c104120100c40300040c0b0324240b00042c140000c41e80ea203480102c070307620a040c040000341d00c940b496034054100005440440031040d503942c1410402d840301440b5911005030b004445c0c06030345120250101c51040445 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 639483489 1250 639482239 639482257
    0xa11040504020a2d090207020303030f1f080c010f053112030e0a06020f030706050a091707060b01020d0e120a021c0c060c080912070b0c031209070b03010308 69
    0xf041c80551210300400c1844400685400d100440e040c03808000802c01c010b880003005080821400c1c0f0200d5008a5200c2c84002d00501d20100e10a00040c440b055030a8442c4a52603021581307282162206aa07036599600313111440e000c00d2003180c12003c107612642c01c48011403501c0d400b00410080017001044503420365080c030024501c00c02c4020521500d0740c031500ea402030095492101003091002442a2003245400400c03c43d004a00040e2068800108491000d940311400060a90350f58a0a000034180004014002c50504006045074888040584052406002c1c10095a0010801079a681d000481c3c4800412030350000034901d85010f04046004040f62420358400100380d0b400a41100d4203d0420007031560344600d00e10038020300c01c0700c0001618950a007142e805149480d07450b0103006003c44248660300071580c81c41c2140c4140700f0390f8002d010005000e506c860525040c40c0e02c9030000200d00e500c1450a000007010303603100140480488640e24551407450b400c6449098a03903000b5100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 639484739 1250 639483489 639483499
    0x6120c0906200619141017120703080718140d0632100b0f0f0904050f06041103041502090a23010305010603020715050a0e010203090604050d020a1104050402 69
    0x40b90064120034003280344503030f0680300d010043c0d02c025030f2018226400d640018018498403001c0204814020058800b034a0b140350022514014001c0400e281c0b071282002c401c0e0702d59000c500f03c1308142c2c2000340c0324003031186070b110060000c100101c00c2d940e1061500c240040403440300008545400c14030300740210240100d201241704100305143c0c00da40500050030329101c0c0d04125510072620525401a500300c2240f00500072031901e0081e103080e460103007210080c41e60340006151049501e0140c2225404d440c05071080c400f5141c00300e07801800207001c8503c98000c5003441e40b00e480c0c1c0c011900c11248500c1c1e1050b031114000b503007160018001d42014a44e5030700702c54181c0021039220482035040c140300e20a0341c80c5900b9604003038001002e4490607808041894018003c0400040c403a0f02d88042c0005004c01c00180340d614160b040028000c80b5501c03a94551000091141016001c40c207188030b54000c1040b83d8101c07446503000ca9071000002805000300c1c9446542850034034242c0c00040d0440d000070030b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 639485989 1250 639484739 639484787
    0x120c010e0f0a0e0f04141b15070203010f06170a0201271823010b0a031a0a090609111201090e0a080a08060109080d05040b070f080f0406120c0906 64
    0x500c6a143e0340080d01e040400d65004001c00c070030400d00420500485c1e0113800505082c150700098101d00d44541030043d8421000c00d1103000d40d42102906443d00181c000f002400800019031084004008a0045c90290820921008012280024001d00d01355040c0d48515460032045820031141c070844a10007000318104400241c2c01028075000c0307040711380d5084000f641e0304441d0800300402030f05034540007000c4c804200421440d1a100151a145049402e011800c0c240045040004010030300c1041e600043d20380e40441c017810f65510000580380c02440070404e404240b080148540140c100c0c5601074090b0341e00601281e0304c1c41c0c01c2803ca145214040380d0a807800c40e0b56541040c3c2207000d003240003a884004104066a1000ca480d00400c131201c00352407511ba12010043c501d103ea4000c5044c14000014044208908403407000c210b1134010306082d448184030075214500c1d510034820074000407100d03010311052717018070700c40d800402e2244d44411580510b000030540d0b41022081c02c8001640610b1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 639487239 1250 639485989 639485999
    0x110f12090a0f030b07020c0108060d081804020f12060a050906061b010c1115040203072106240b120109050a09051507020d090807090908071205030105120c010e0f0a 72
    0xb50000d409584104802d660511700002d0080c5000810380c012410080c1c000f0901103d62904038212240315000030010741d5441d4289010b012115400f130049030854400aa403585070340d280805040412103035040048962913482c04c003d042d5180d800f030315070701c408c03100007103a40742ca0110020302424081040d00c03400100f41107522405c5803588190b41b40428060700d08100c0003c400d019108000a0301c010070342e858102500031a9842e07182e4003401002c8050302072801d480001180d4040306140d404a001d10141c00720913483c86006112081002c0d030307550002e001042403003260f0300351a100030250040c02c0b140d03868042001c0c050400644030700481583e80d1050700c08a03106228012681d07810070840303074143c00c11040091401075201104000c2141c5e051042c80202e42c00f0403814221408124003041400850404446c4d52088050003031400e072801e01e450f8801074108010714100c900c201d490a00602245403030a44440d8020046030018400303113007002d41c9251002d0100342100c409440d032405c0319111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 639488489 1250 639487239 639487259
    0x903041401091e05040c02010903020a060b010318060f06080d0f031e14071e0c0f0c050612060f1c03030518070b09040c0c02010c0b0a1e0203040201110f12090a 70
    0x1d10040883c0110000a020504150041720070401c1c081c4001c0043c40990346000f5110503c4c05c00050038140c40c7c05016020fa80b09400c410081c640d580c0b51110104400d2800e02c00807d1102c480108d06c038241580052101320100c0ca41d4103022450301c0d0108e1181032800118000c02c40c01c138070360110012402e070000b5490941e1092000400400107031101e80c1c100784601a00001c420b11445c2450303d0002d00c285c00030350b8401146d170f0840d40d0040304200503007040d00d001509881c00383c01070b03500140003064040c0d1500c2c124203803601602d0142e403800e80c0810150300303101801c52031229114500c2104100e94001a100c2d0b8012540311210107440400c034100c034202c0d1400c0c0603940e400300034602d0003c201d0301d84c94906486040d16020280c103114105011030f50028002c0c4491100140c841d005110025070903e400350842400800001c00e1940d4122085c1001d500940042c0c0341a0300058410900c0188107100140c0c2d81080c00c3e802d002000c5100f030b07011a0200036441540c03c2c07504150542c0000a1004903 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 639489739 1250 639488489 639488519
    0x60f0c031206082a0117061302030415110403020a06050c010b030708030a021207050601030b1305191b0f150c0206030406020909161b02040e06150406080105090304140109 75
    0x501006090901880030a200d5601013280310320002021074001c584282e07800144020b074034042c4401c9001d107956508001907014690030b150342e070703810700020400c420011000007074500120540b500708014041240342009030300076408029000410f00400f886840d0080d00a010f00030081c0c0c00215850002d080030034101180307513000c0440c5620104040000a0701071101301148518400f5490034212503440b040e64881c810300c0b002e05000c102d800440c5092054158110010360040210b404028404110210301c0d0f00303c2c0c0b401e0700d251079914200380841880540d000201e402c000c10044015041420b103640091484042000340f0421003246001a03d485000e584114001d440050f1121070000a2000e00760004150000398a130614007950015001810a4110034620484d000d5500d22880407500901040f194400ea40c4030b03803230410001c0d01100074500c500c01410389d820b00c421a41d404203582078400680380e090041d00284400c1c40310300c007680a910003d00e81450100714207641d415141c400002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 639490989 1250 639489739 639489749
    0xb0c07030f0e041503060c0905010201020c030d110f041202100c1226040b0a1d030304060c110f1c05130b03060102070b0c0123070206040204051015180e01060f0c031206 74
    0x1446401051f50103800c8026840181b20a000070b5241c400c03003100c51138580c4240c1e4502981300b6601c2000306070b41194078080e06d45014400122507a115164041e800039002005012403155280402001c0407610403881c10010f594004000d001852001c402500c101070f00c41c00340390341c000105400720820b9804031040c1b40541e0013030590048505000c18014103a81d031031954203224403219049070022070400070440781e000d0307008100040c611011b01c038200d410040c0b54543c4045031003200805d2415010102e41400d80245c0041005558650b40400f42d40c14061a050210390183c284001c000d250211030081d035200034140b0598002d2600d842b582c15050b003100c911060203a560b01c003101050140301d00959000d100714503190b5024585020025903412004100901454884010480302c601e2480f182000c1d16207010640c2c000c48803040c1c010310760140311203c015511140c540000746e1401c1c84070001d050351042c0c2d407101034422911806403040d0841d40070803410002140c0341070036000785501c11180944 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 639492239 1250 639490989 639490991
    0xb01081501110a150c0503070206043305070e04060b04090e0312100e0f16030f0b13090b01140a030305130302032e060605090409080d0c0c0b0c07030f0e04150306 71
    0x144c901888030100c0707643d0011102032100c20020b01014a800007469540244e0250384449002c03210400c40da200701d03880141239402c2010240702200030700a82c204905c146c0c4166506201b81421500b08000e4a106102c0e403145000c04201c180039004242e00304000600980040700c0c07400005261600c2109411250700f4101e14641c00c05024191580c540c0c00c2e000002680400c4030343c1050003183d03403c540810707018070a040c0d8402d1480f0095840c1c0e0000041241c00030804000c580381071a04001405d501841150500b0400d0008110a040200006000c210140c445c00445046a0f801d407102c0d4491200c3c0c0fa82d11454940c00030050b17404201000201908003103003424052a00b07140c40b4000111449605810709240d02440181e0748401660306030a4115000f040660003030810340114418240c1c1000303c50305014400c048075070802021101d1324868000c0d07074010740d500754042c00b59000e1000c000340022060600c140c2643c1c41030100000702c0400810001c0e40d1160340c15402d08149131a4412900c43d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 639493489 1250 639492239 639492263
    0x8030a0b010212090303030115020f01053c04030f0527040c051639240906080406110a0809010506041e02070512040303110c040b01081501110a 63
    0x756414080c51001c0007100b4290f60400303580200017030f00e034001401004480103910380b15081c00e91017000514004500a4000c0180d802c005242800f001c1c03000144c8400c548022010b000019404000050b0900307030031084240f1a2125603044500641e0013041c80d0030040144101d600c000c0c504003010040020607200d0300a00060007090009550116880d02e0a2200c280180400380000040310181150f11014000c42c1e0464039400c40c00d09005000a001415801d40e4031100c504080c2d4010700546501070801c11070510305915292280210002032400541c0c0450100803160140c1e00d01500031303225007400701e180006400b400940d07070032079460080000c1070042403200001c401e03c202ca40000d0155400d00206100d42c1039080d40100080326000c041d940016880c0a115060040c1c084101d45500d0095a5a9a07402e00908440d81144078031010301490014060b039180c507100e1002c036072606848040c1281c2d41c5a00c0002c0b91109040c99034140201808034603400d0710700780801143c00b480350a100c4d600c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 639494739 1250 639493489 639493511
    0x908151f14130203130f06021308060411060f25080307031401050a120803060321070b010f150509040f020d1d030a17040302190b0919170904020708030a 67
    0x660400916402c944910400c2842a00c0c410102e140318200d8200b120700c3d81404c580c0c50709030000c0c071505190b040003100d0880e000c81c2c82d0f400071031310a01031030140c0c01c00d401c0e0042c0102040324170b200e058406000346904201c0b003614414030b0504042c004003804000404003642c1e8640351055401200d031400042d6490354180f075200794000d203041c09031605480184034681040d0360101c0c0ca46d0140704c0500320807001b0002410a60f020464903640b441000d002c041c4001d030800e10300e852074101000488220400b071001082c5030f0340e84100c2d901151070340b04020500d26140390094a1651102c21400e800a442d51040c1079140b002d40000e18103020302050004400c9810300c3e00c1e0312102c100d905220401d4000304444c1d104da991000e2103c01004407003c245505844a280c2a450310110606940388111812281c406100b10011540d10510106065410048910070684240348200c00700170a4540050f0405004081007406008034180181c001803a105031902c860400781c100b2a05400a281c0b1007110002c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 639495989 1250 639494739 639494749
    0x6160f050423031c09090b041d0a02011b020d03080a020c072403090203030f0309070806190501060f120e0c0307080d0e03030a08010b0901200705100908151f14 70
    0x80ca00038982e040b6081281e203254010b28945d183d105400d07031141c640664041e0780c0c3c1c036a031142800382113100f410540103c8550302c098980078200380c00d030701265020a0002d400344405445e105915402468450340c24440e580580b1090300140401703400341d5090202e080860010480b01014054084441254009030b008405c060300d00a0a10400c05080c401c1010043e180002641c5e10130706100c203d16281d0f070320440001e252840d03981c8450304902c201818024000b207902c04044031145542004d011507a21404203592075005c108000000621130101000402a641d110910b1b80d0450400e8036546141100005c0c5081280d0704941c00d103400102a400c00c00d90440810101c0c1305003500a58100042c0000c0a065142e0510581c214204002181d0486a00c1505034001100201041283c5448600a80741e80c0c0ca1290080600540c904008501e02900174030105045800310350003842c0d800242103040c0f40e50130014100100100c0f0282d0700242034201d110441000d000103052582c2501d00c0342007081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 639497239 1250 639495989 639496003
    0x90a1803020a0b10081b040e03030c091f0509040f061a0405090f160e01020a0804030b040b22060b240c060a0603020d03030b0a0e13030206010806160f05042303 70
    0x80d41c1ca40c460000b0401000042400320381b05000d07804030341101a0700b001050150141d000c0003121400300000304040d01780480c006d45040c50701a2403132001808184c1c06500340001540100010480900c00c1047e82c0c60142c00002043d44040804501c03103a58054103240b40c000d040c1900601c0000bc00c3c14441c60a141d40280da0000070403c69041a040c42d03180004901c040d1254178040141444021825900801c800c021740c5900c0014203070f56a41d2410040e1400800f9078044941241c0f00c000b00700ea202d0fa0041c1d41c5071441c4440c2c3c4600301d0f8101640c030540144403155041e40c101510f00d511a0b400d070414084071803108400422140c1c1c41014406160500c44010a2481100d02c1c144041c4056200c00f0585802c0d40d6041c1000a41c407650140094401d07000d681c0715015020006082102071200c142001e0034a41c4a07808aa0041c0d80700c1d8030403911014211032240358500030702000716103e0310403501070445200307500b0890300c1c10b41c030340c01103401c8a4071a020030955081c0340a10100c860070104045 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 639498489 1250 639497239 639497251
    0x1d280302090903031b0304030507050d09091a030705040207020a09020d150602070b07082b020a11191b03050f010204031a042102010b060c01050a0524090a1803020a0b 73
    0x18520714a48115185d800780c4400010050001c1c01000060405005004440340700f034125040311003815244074000d20030070311401525070060405910150940ca0a81c01001030348005000c2c14031142008188002904000001d9a0041e001e02000454151a10017005641c3c10440e01007580029a00f030403004a03071660100045502600e000c1124500442c151010b07558886100c03643c1320083d01c0b200c50f0224612001107a44801c3c040d00c100f0364403243e4018a02801640c50b4804004030320007000e0b848440c65400c0d02120010300f1071107400520070710003426685030a407054140c815204d4660070b28084c2e200b1503001091f036001505005210614003150500c04900725110840d00e00fa87d20200c14842d06181401c0e86800d0340c0e6031013040c500030340050801090180181d40c03101c144200d40c502030001907915a0000b46054013240c91030200089042d44200040d50749040d03000e5040900170083c10051001d00c16940d913000101c0c1a84070340c031050503402d02a03070050074101240d06041c900d01c1c0c070142403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 639499739 1250 639498489 639498493
    0x90108060d0807021905120a030f02210708041d0901050a0c050a0f0233070504030f080c100203040609020306060f010905041802030105270d1d2803020909 68
    0x100002422030b004a40030346a05480c4440d2407a500700040c040a0041c1c4c0109600c20ba6801803030425440000b058491980242d4410880d4610300b0410380c0c4a50103400f062016a0170411400c408448030001081e0b40352140c6401d92070640e03601010080000d0100c0003819410b4903006000e00e80c01c00b40280c2d50484c014032410403168076010009001c51003040302900a1181c40c02100d21203a0003401942400002e10080c003500c00c0d42d08400e07280000c09000e01d00742c14600e0001080c08a4411000d940583c2d17400715144c2d103036880a40b60202c0c280c011102e03581d440d00c80c600f00d1000750015400650f004520508c40451242c0282c410075050500c002d00643c000e00b020901c800c01681d00c1664141159010f03500040c441d1544684031861130303020200a509503081406106a081c071952a8502000c0784841c0d420302e418141c06540e44540384588250f00040d0100c00c0c3c0410a510801640440752000b401481c00c0900840c03098811840c11450320602c45210304200103500b08000025801519180 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 639500989 1250 639499739 639499759
    0x11070806012c0105060a1d13020c070f0e06061b1603140a08033402030919081f090204060b0a0e09040b04060221100f0b07150f020405041109010806 65
    0x1005c40d620703025069014042258130b81481300c1d200f100a111881000c0d0203040444190080c0c094030004e58400032958610f4403540317500187e41000c411041d03068801401e0790031a151115010000150007400c03510308454054088444c03000002c0003100b1a8035019642c03010541e11b982400505c10248094116440d0881441d8600055000c1d045a5108444251014605969084800c4003840444d00031001195118141000b150004040e15880000f00c80141da898408101c02c21468070620a160165002e0044220071800c240881098540a007a00040d04405d5400050560321158080014440c0c00203040065991054078411284820307204404142015a20307003c18150013840a8141a07010911a8000e041d10519980c44201040b0300046c80c146000380011b00d50162140c4030351401c1e81d410010740185083d054549064014140b40364a880e02141a13025150a41007016160b80c00c02c800701d50b50ba21846005144604072030110f4440f401c11002500042014090a2280341006 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 639502239 1250 639500989 639500999
    0x703140319030f0e01240f08030304021e09280213050910030b09010f18120f140a0905130b150a090504060315051501090611070806012c01 61
    0x2024201074058034001030038021622005009084140d107128880d420a800c030301496076050f188002680f2603038216030009a0791045040101403501c9860110382050001901516089042442c080090503510181d0011080000c0310b50704101c42d041c1464166a40746004820458100c500400086204502c0c000e4803103100107a509880c410705c1e20a049800004020b44420079031840110317845600b01105083c520a1795019122800318500584d140001d01400882c039880c6170400607030440700034a490012918100c94036203071507905400380105a40d617a448005800014400c0c980160b0354a00070303500301020880c4103180318803c1c090300c5041c0720180e00182c0d07900b1002d50150500340c03515a5190004242610303041040e40c0416841480c0103000810300c204600c0c5005065030504040181d545c900c5000b802d40c1c3e44040d01140068945c0d1000d0140500500224078107020035800c40b48001d994408140c40d1900982080da034041c5980304a401d501360001480d400341ca40e254070506d1030360500d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 639503489 1250 639502239 639502267
    0x1090b030304300521091804020a081218030313151404030303090209060103151a0706090f0210050309030901081f030c1403030c0c101107030507031403 67
    0x90181c040000e040800482264030344050003800d8064507240c0b002140c03c1402d0140d21030100d46031034000704c0e0812009202c0b03d080c0004903200c00c40000c15462a81e500409000c0c0c4092000744100d800c0b001c1503202254083e0200100c0c0d84042d08101100e950300d9804a40303000300e080b00041c05010b580b06106c0194600399106442c01a02c100850103da40b201c9200220703400c0d010702c0d004104004000070040241a1f15403c2000c0c01c40c003c0d03a24982030340b00c80c4c00450446409a00d800490b80301c081c018402c14040e01d00310f0040640f004542405c0c001a0380382c80c81159980402201e0860040c0e03003102c1142007011002d207000c04c40e4100305065190520500d07842e440f40382c5680b8100001e61001840c4a003070080179203d880301c445000b100c1a61240341456400710300d80251020120b02c2c000005145c580081115000d180c1500900300000d074403018040511549182801406550795800012610410105004502800c02004114954241a03207440300c07807880e44845030800c000c28001c400c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 639504739 1250 639503489 639503497
    0xa02011e02030a0b0609100e0a030b071e1b110310021801030b01020313030221010510080c040209033f030f060a03050c15040b0c060105041d0604110a1802030a0501090b0303 76
    0xd02c0c00c12248c070101001c00a1644d0010f50001000f2100310b0092000b0f141c1d01c5014403030314409003104680022481d25080c0d03003410b0401d441c082030620301c03060100010b5484099001c608403380448070030f01d042458000036038110f4150402401180941c40e005503074980151082900c0030300166281100c00c80800003960741500001e070043c1101d00c885100c107201c003000040e400f2928802000142010b058001c8030011702c0c40341051600c140944551549080d1080300d4505070000c00901c081456000002c0c0402403080750074546424540d034404440c0c0030380081c42c40e040c10700002d00e940d0707160043c0d51048500012300741502420382c00005000007400000c0003001150200c4e10b80e110185010728400082c481d0360800e4071200004598a2070380b860000303109050f54011102400402a007010f480054032404800306400d52052010070046092020401c060319006008048081d0300da880d0f20942002207441031172019800810406554514803405000d0400d03102e00748100000c2c8000203903a402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 639505989 1250 639504739 639504769
    0x6150605071a250e10020115050603131502040504020a2106120809120706030b120105040803010506070503071b06030e071a0a0903060c050304150501080d050a02011e02030a0b0609 79
    0x42c0308000031424090481802810001070000c1d0a04042c5d90000340a0451140705035804094400c0100e054607000054900c45c480291a11407038802544680010f20412640046625820007021032241c65a000410030fa042035195402d1800003c081c005501740d004031900d5100e4a0040103000d0410214a03086582d82c018002c1c0340c5400c071610008811405100c428a018030540000041c0d40780c0507000800191411181c1c401e0f8085060101401d0300c0044034024843c04003000144014540240a420503074092400c80b81072110542e905101c1c001043c01e400172428400c0c0c0e080000303039810f00520058500c10009004040c0c80e11400403090301d400101018410800f0a140d0b00c0280315501d07030320042d40c000c18144280c1860301c10141c0a903006172410744030903d42003c0fa4100d04500c0c05518103c42c00c08008004100000c83c04031082e401900e0035800715500c40d107400400e1b8910781749901c014440e8640c0141e42e4201107410703204440f606416030303008400074002201e640e5203945100e89400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 639507239 1250 639505989 639506041
    0xe01090902031218220605010e0a050103050702120708040e010506180103110d021b06101d040602070b0709050109080a0b0105040f0b0d08070b060f061606150605071a 73
    0x280c0154048446403c00c0301c0810307000580e00600030746030301c0108105c41c0705080203001004566199001121030a5507071403510b420010b40c200c100029446940b1550b80119644103468010f18880c002d40115030044409031820304d0082800c2c00341001d1101120300401c40bc9982e68500b00c00e40004800d40040c0a2409060644da20303101d001d40d54011040f01d03001241c0c050115990241000444c0002c500304100624a10800002503501d001c142e43c48400c0c3d4007880405070380d100000f5074420400000030b208642a42d0280000000158201c0b8801d02800064980141c1d00e410311000500c0c2c4011584071803515440044d03610f003c100d50440b01410341d00250307804150300c1e604c01101400740407800038264019401c1045c0354140401100903100340d500c00c05501d00d80340c03105406c001115511f10740207680403004110b40080f800054090f07040083c0b26620204502925141f0340d840c100d2036500441c00301b10006414070810031014011408a0204081c524450411240e19800241c01585c100c2d604 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 639508489 1250 639507239 639507247
    0x209041103031b06010906090b091506070209150306071e0e0f030a2402030124090812280f0f03020909010b04051c0302192a0e010909020312 62
    0xea00c050003281c00444661040390304007160610080e0740c480091050000c2a40740040100f04a41e8030300032417082c1c0400420304050781d140c4450100350b0058880103d40d0090b000c014180058032411903082c4034403103020000e00d514414030241030901c0e030000e214204000c0891540d146030300c02c0e07180082401c1a10300e0445101125403010030650070344001455458810903040c80100141011403207540c01c5044140303400000703ca007082050707000038002c50039404145030200c51900280502e40b50700648600d814040107581d03011003420000d01801084000c07000144469601d4144094070710340003d56510718060401d40e9030001c10003004a0541c508000480d102425010b2082d01619404100200b81c05003c0d41e6600920714581e0107440381c0c3c4e0180722030782c9816801d103a028918405035601500030380007114240804240c543e82005049070031342d030070130380203002c0e007884140714655a1061500b00301d06030301342890b450081c44160b00059060381800f001600580340443ca0040c201840c84280b030321 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 639509739 1250 639508489 639508523
    0xb030105240f0d0c150504050a05060d14040605060415150513031703010312110601170a0605040501021b070812071109040c030201080105010c0f0b0a06030506040308010806070804020904 82
    0x8034095a02d0007944019900708010a228422500804403140c1c6001c8005400e9000416103590046104240e0301c401030380003c01043c00c0c910700415003802741c2d000004018040100020b98014182d90694a4654400c100682410311b807180d01d11042c0002046044185494000540c40c00c031101540c0030481e011640c1000c0010b81c951a82c05190302100e41d4190140501c1400b10f541c10134403064130706800011405039054000c0325081c00d5104108040c29035a1308081c0000b503402c001d403c150400c0c0c0b0403220300c0800f003440b601c5054000d520606c00940e03a01c60010307d403413400c1c02c0514501c0080c0c00001040100c04000240c103ca950002101141c494170281450700340c50b0002203209401440d01400c2000b0850140950408d0313a100b41c03070700e601998841c0d00440e0003c1d20322400400041c0345803414000300d180c0e580340b540e03c28121040450007c2c1c480d682c0508014091b5802c401082104005004000c814045c00e40d002509103042140b42c5030a8000a00b010300c05040503040c440d00f8010201b13 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 639510989 1250 639509739 639509749
    0x9060702060c1501091509020403030815060d1107150b030304170c09130b0a0e100e0703080406090e062b050a0b10090b04090302030a140919030203010b03010524 71
    0x16410109000f0758280c0da03407017041401425003400780f00b14228084102154600403442647c0580c1d82540d0781c0c81480d5170b51200d00700704110080d1031075841481070050f8840000140640c034100c4041180c41c50f00e80d0005d00d4042d81480c0810003c1da042d5040640321180e54a000090314102c0310061203c5002e07411400200d0304105004601070780001101d000c100c54204c2d00e1012104a5104940b6040155035208030002103510010310360b4034a41145044070031400d1036801013507980c41c040080c2c640040d41e070740d202442540700e81e11540c00f04902c01c40401500c00c1031105154080b100740e4254290003545001802c01c110b41c0c50301c060b019504060b04800380b10041240f81c48041e400072415409040c00130802c2a06031003031082203585401c10600c043c0c80d04181c0142076030540d160300110306103403082405840843e044020054030810902000f40380b0741e80c0520344044040003500ca0302415046005060946400081150180e8188010701003558004020400c00508101d00d000142c411580003031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 639512239 1250 639510989 639511003
    0x40f0903080c031909120e040501061b0203100203071107090605101d120309210a02010c21030b12030a0e150f0c010c09050a0308030c0a0903021c03090b09060702060c 73
    0x1c603070503160003181d101b003182140031035000600c00e072070b0401d980d6824410007003501c0f001d0180c1c0f40016507082da0141c695420044602100d44010300f901d80403c0700c80000002c9030012950307640012508141d104101d20148500c0700a040c0806040c003c05082102044221107942d0300301c1e080040304501d00310000c0b1180c032018540702000705030300160300d142d80301c042d07894011040da18852034180a030000c0e5461041000b50074000e00301c1c00341c07400c00c1c142d07001520030505042080e00c00c944290500c1c1050a204c4a046051030142e880024416143c0c00038068120900d02c14400d4550040011403002c130f03000341203101902801c8450081c200644c400404544c0134101d1981c020b088003161801c1680e0064202d903003202c0c29941c540e200f440d074400410810505038880a0020081040421203d2010b00d005005103805403e04901541d0b4907400b00d101c4049034942d211800207584155010958010b030740a008110380701d980c50429000400041c0b103446000710091081900280c07190180760706100d25 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 639513489 1250 639512239 639512281
    0xc010807110d0807081303022d06010b030a060e090c040b0102031603080108160e2413140604020307050901211e180f02040e070504060602010b040f0903080c03 70
    0x103605400c02d801c90280020a00341c4010000c1101000080d034214843d05003c544d454041c1c0c0100380080c000002324000020512841c030b0b008405803840c0f40707a2241001184d000705a54403a007681d03407030844c1c00c00e002c44040b82c01480360341c0c904100b400300c84040029000002c69003218005400124040140d04d14480c520007200190851640b8000b03140d006607a640c101c40c5d111090f1a0794405481039020880c43c43d01400c05103141e000007207007548008900340c034240d548400110400c80350920005161492a840540d005034a483e082102003003000e1980c2d030840402d590a50543c1040d01c03000c1d10740e020307803c051810028a2103100015003040c9000d00504e00ca5514100301040031344507541060304141c16000411402c0c800d0008040f84200700015001d5081405d0245c101e00c5c40e4208030190104210224440c82010004a8150341d40c0c0316881c0203090b6a000000c41c1c44140702400162090264003c44940c41e2001c00d6011035003012281e54000e0850503455541e40e2001040c0c000031074101c4070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 639514739 1250 639513489 639513493
    0x1051605070609090b09011d19090809040b0108010501080a0213050901080f060714070605090a14061e01030f0303020a02030f070602070312021905030a0b2806110c01080711 76
    0xb00241c00c45005800e488640f041031200e1140751040c01003144083c82008804200b407002c2002a1251001564200c00a140c120320071441003440c03c0e0680f640070000303440c88040054170300b1607072406125082c0c0c103880a0a1049996240c900041d2400380010020f0b00d89a0700000d51414403c0c03040207a101600005047d225156107c54059a90720781460402d1050b00c076030070200341424003819802044000010849240a9440e5213031400385c6409403094410f44a10b03600040000e0b01800c400221010900041c007280c176002c040c43c0403e415a040c803840c40203951005101056805141d84840350f01818056034030400302c0d104a143d8480c0600c1081181404280241000056001411502c0c080c0d51083c019051290500e4100d1280700000010008500c0c0f107030260900590280d07504c4000204005081c0380381101081205130700c00114100c19100203400c189500586130040068942454990090104078803030603520943e852703101c1d05201050300000c0015201e02e1381c030308000c090902 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 639515989 1250 639514739 639514753
    0xb16060608070305010e0f07260604030e091806151210020408070b0c030a030f1118040c020109030f1107051002030307031b090504020d090215071110090501051605 72
    0x115480300c60501081302d00e542400107010b400840005d00a600c5084079000d0103006240260000e90252418800b44800c41d440d00b861001001c10300111f40705a0180e150170360840c103030004101503400c005043c3d000c4081c1c25943c4400002d0002021030380f01641640000d8042c141000240380300c403001d0307822441c40c4101308000c2846000c42d00034008a40101045600d1a030f201c44504000b070141010002c141d40c410b00103102043d1003a0040c0c6105140080000344201d00d0700501030559000c1401d5182100c5900300701d804600380f9128441d03289000d40300030800f070543d0703a800815142071060020108089038101050740002440000001c20009016640710f1041c03a0000c0d480740c00444000000c246003407424031754829000a050880400ca6499524003410101000000d4104601340c0004690b24080c4a0040e11004100c1011301014403181d52a08070b1071400200c00b074044101c041c0a4042100c030820555001030b9040d040e80c400f400c0c450340b40c407054406050b0300d0000c00405051482010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 639517239 1250 639515989 639515999
    0x1e03020d060e040f1a06090a050a0e060a09050f030f070b09010e03030a0b01020616140c0a0c06080108060a09020a03060c020307050703140705010302181903121214040c0b160606 78
    0x300b1042042c418030060002903014025000a08806c4030310b950050011000038260520030b50200c6d92080f03100d00001066694225050f20b0160200e40f4007028580e211010350a01c40104600101030851400541c6410000710504001e0701503e8030090102d00c120b000f054450b0029003114140e001403e08070b80e10ba14000120f007018089242c1c1d0103025010302400700da0240c4440c10110041050358445000c240350400041503180d101210861075401441030f644005242c0c0d00d0a18020250b80d6989003955040c03000c000e04000000d04004070302494100c8071401a254002c095007165040031002500600c0c502069003144540480140759000d50b040c04400c01c03480d0303c41c88101c80303e0602150001604d610040d012403180ea110303519000d003005080141c074034003400c52410118004165400140c0e50f070741c410041e20610150107003c18080c040c2080c0b60b001600c00c03030080c07060000d01c0d400641010b484024140141c0e000381c40f40758000042c0300614100c8407140480e001d030f1081042004582d54 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 639518489 1250 639517239 639517253
    0xf050a052e1e1d10090f080d030b0901080a03140d1b1d010509150708031014040c0c120e060a080402030609060115180b1602101e03020d060e04 63
    0x10040c0000002000400b00002807107040000e0103440000b40445012910700104030a03560454440340410010f5000442c03200320300030341034000700014030007003d0b003040109010b0301340d070360035441307a806102614010000020005a0300325001c6e01420403035080009408007400e0b912400e040d0b1804d003410800400407001960342c070041390000c0713a600c120726030f1681031011220440720340145001510038400351109260803404400c2000203580b400d8030307108290381c1d407070556003044406a2204407140f2040140849040d10104080c104aa0810043d43c5a00000d0706484881310090030650902600302440c6000340700c45451020000c260035160b09560380028070624044808a0180c040d5a004c98000480092194180d40b0310003608640022003017000c580200c800d1014401c00480c0c0c81002424400540080c43c080c409401c0016148440d40144440c01140110810400c91400400e0030480484840484041c006c2c4c900541e40d94116006200a021280c001048600c01202840100082 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 639519739 1250 639518489 639518507
    0x50f0a0908091c030f03050c04090b04091e0b150a06030203090f0f0703051626100911240301090f0b04021908010b0304021008180106080c0102070f050a052e 69
    0x210741d0365117441d000800d41c05c03810317680300b510741c941407000611061040c2c050310741150701e00c100003800000341c501042c2c8a42ca00da0181d20f48900e4512041400310051040081c10542d00c10804412400c00520f06000714107038401034447c0341e08066010000c12254035050110305249088601184c000b2040360101988941e00303848221400d2180329028640c541c00c01565104a68200d104079187c2ca0882c40000342c91a0340c04000e070340d54040d2001201c11481c0901c1001d0b031890103501141d11007031241061241d030703584614054007132241451700142608604021681520021040400c21014822140002e401c185000ca64071a002203071200f0902010030304038100781c006681d90315051f641c441d002d0000d8803065070065040101d1001e84900c0c280640462034000d00003d203d295400c0318507a031035007151140d400078000d40e042010b480c041c640e41000a5406050380d54a810102c0e46404000b03034498820340300c1d40b401001d00d919440c208041c0044004050032410f249145817030300508006001c102 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 639520989 1250 639519739 639519743
    0x4030c050f0319081e0702070b22050414061002030c0a0b16050f0d0207030e0303070c0806060a0608040b04080c0d030204240f08040c0801090b09010f050f0a0908091c 73
    0x100680c2e10720a4203209088845c06a9401015840c2c5c0400010710350860840084c2500c041d8841c00b44d0024900642c00c004101d21014101400c2d03085100940b10f00360105954000c6100b1818080082000312180d241d1641007002101e000c00030404100050741540034688140b030190090001107030070301910402c428820341d104860050005100e16040e0b4180c003030740030031002d0140c4c01c0c0542c030555080c03903004240450003401c20310500400c00340002c1ca580c0c0300d00011104849128810030200500308082a00540d04481681010b800c0ca00c0050202e4070040002e82030800d10300c003181c18404080126030382e410203036040e110003030420140035000c1d40c17040c496209120340c81c00200d81101840c800f0f5418000ba5582c0325170155030200411503411501030070a440b00d030201c0c500041c1810092160380048e0707218894003409843d2080040d421100441c0c1c8061680b81490200004100c1c064201c990101d01c0110001c0c50100c2d0703040040c424000c4591982c1c0150224140f101491101d2840744040740c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 639522239 1250 639520989 639521017
    0x8030a02030c1501180507030615110705120c0904170c070e090607080606090a2c010803070203070510020106030b070c120215060d02030f06270a02130504030c050f03 73
    0x11468140ca1203020320900c105260740e002e1900707505c3c040c90950043e5400001514001c29141e440352031007a414044051014040760301c1d194041070001050081800a00c0111000c40d292024503d065441c0c0d007441c0f001074440e4a1311000201085441c44022417112500350b0501d0300d9200424003140d0302c050f140203a05c4182601d2001070141c44001070310758450886c070b50b1121440d4641d2006e22030b044d08100e485a601c54400702000c2056150200c4001c480443d001840300c1d04480c1c01c030008080c6030180c1000c4400d800c204845070268500044c1c0b0b0007100c0060300c1100c142d1402d444201c3c014009508000c00800320740c0c080c06070701c550041e402000c071402000501d00306a01031005aa0b42e142e00002105a49000c4001410502e0108200e503401030015040d0342d92408801c6e04541070130403ca4440243c950018540640c00c12800c0e40c8801a03d84140184003085043e000980852030208102030610b44590000d400c0510640b88900350301e51110480300c180d18040b2100341c582e04807a407564106 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 639523489 1250 639522239 639522253
    0x120501050601121104060813050609060106030b0109030c0e040f12080402101b021c0507080d020705031902040b060d051302100309020d021014040303030f05010e07210608030a02030c 80
    0x35861403003443d00f0440004501860245080001e0747c00c100014004141ea41000600350041641440158450210300c009000e040d81896070103000c481c8202079850400c0b208010030300000300601684d4040c3c0b000340c940703980a80e4032450080c1103c01c130707040300821600c2c05130940d0050307542203400180200d2084651060204070241c08443c42440620a20008420000300c1009410940c071114000c010504c03013845501059181c441c9415829404501c039903000b01000350040d40c0c14002c034005000c0880103462110075050860710080d2800c10b0207480f503951040b00c4111135a038001101c800810b013080c01e102c0f52404214102c40780301c0c0d404090380915408a1071210352842840b410000c55402000320001c0b10740c40d0248101e166601c1400024080080c104040d0103071050301801c0154400d0b0790100703c402100b034031002565010f80c007581a408507802440070290300510011520b503a003003e2140046004c88003007000d04141e500000160000203440501c40b580440140f101041100441e000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 639524739 1250 639523489 639523517
    0x510030203132a14100201152310120e0c0a06050c0102091816080c1611060307110106080604021507111305040b09060c09060a09120501050601 63
    0x980c0300441e10b200d0a188080007540000d40003407440905000052190a690001d280000600c0e885035001050400258441c08070281342c03035422080011914030081c040980100480030200e1a00c1c00b50310f480384040300c517114503000714803d21a91401c00030120b10312605070b000c0281c400c5031780ca200390381c07000c1c20a034a10303d842c00c000540e107480d204013030300d0481d42d00d1400c00c04a4568000500d0840a550200034400c5c0507940d20f001007500c0c88406005205500f0100c011900104803003200c001480080410040c880e8200b08c262045800480007140c08000e039481d001002d0f01100c0e0714503500c0780b0b021051103e4207911040c0d000110303958034000c02c0000e4030b8501d243c3e5500021a402584800e050014640d050b684401a00003288200f890700714040040b80012070009800c0d08004100341d0320303c2000305000100980302e41141004018100360f0428a203409500e100d030004480c0100000120402c1107072065815400502800175254002c0302c0614182e40641026501d4500051845041c0c1c07038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 639525989 1250 639524739 639524741
    0x7020a0201020303060d020f0406030302030a110706021b040207141006050405102108041212230f0f0c010207060506010503012405070219150f120b03010e030705010204051003 77
    0x801190141c00079070865449004006401c0c2042800300c0c1c00c10b0b0b0141203000e564a4902a20b00914400e40145455402c00540100462007803001c81c400c69100384000c006258000c9209140b1029500e002445040081d0101d0060310078204014142d01141554848844010039070240d035035000281480b55a590308100016101e0a86825070526141d000820044a81c486140c0030b01071180c000300d1421044e61958000740d0000c2d4004880e460401004d08100154020b040700743c40c03550f00b00000c6000c9080c07010700691003a0b50248141080005050080b03641030410387c0c00300a036141c00b0760703669100980400d0103900306100442d40b0303600381000720304598010425207050700d660340c3c079481d80e0710b485105d040f045000e04a0f540040c05410807030310700561a150941d4540351141c40181c5145850300d8140010010380050000411500c405601c8402d58425000c4280e261030300000f00d842d40415001a0043c07032185010a40e510001442104200040d005001210f008460100c1c0000744554260 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 639527239 1250 639525989 639526003
    0x7090807030317040302070302120d080c190e03030c0a1a0a02040e1b041a090307050406050d03081b1218010c0e0d03031104090618110307140706050a060e0702 70
    0x2c01041c016100441030308a00b1002a9000b070080c4121034004c0d139aa000300b10140803480100322160490450302228075000742da09500000380c0e5118529083c00e842000d1500101e0107814810088078203480c42c0e0995003002903808800c080d4081d10405145480c090aa0001c41710440036420455000100311401a00c203031002c40c5d02200782c1561a581c0c19840500c0c65032150340d11309403c8000d000100f48801030401c90759990000c0b00300307036541d5403020040600d4410158050361081d81014020f00450700d03090020490b0b903926050501158035001c030954a00d271303030b0002103141d00e11001c9242e10240d00380c3c041403406441c481c1c1548140e0740204e903585003680c141d0301c0500081003000c0030380c89071814144c103d0500c0b540030b032400040d40d4078005040c1e00345501640c0643c0489803210010704c41003130050601e4049405146082245101c186040507603808020285018010103082c4041107144a200b03c508017548108100450b1504c1c8050f0002400507004416444203200005540c25000203924 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 639528489 1250 639527239 639527243
    0x80c03091507020f10020306041406030c040b04020f0d0914070803072a09150504200c280b0711070b0a050903010f0209032505130e06040b0709080703 66
    0x1500c1c0c140d41420451414040c05008103045205070300c401e4152081c1172106000000c07008501580e070703081c800100820f48d1002041e85403691480b80a01c00b00d55030020341020303200410389010504040c10350010300203000b070407041c1c08164000100002d08030030b43c1e400103040c1840340c4026020030201c8407181c1c3d0b0310015801541596801000b1001c00f0843d5020000782065440800102d171110304c84c074000d215200d030790040c104107468549404c01c01342510b407001c0c00781030260b0302041002c40c003081100c0c0c0043c25400107140c0d18400114007400d80c1c0103101c12503420740c04008000707074070030000003c88c03400d9020301c000c0d14401522008030b8185840b03002c100704003055048c0244400d90800e69140c0d0954085174640c01402410050300c00981c03001e0060304266090f405005854540102c1030504001c40b2903048900c0c20783d052459900d40c940e0202c3c0000740c90080e05c04d2600d0011400c058001091040a01e91142c410001000f04002458082c107118807169944c2c070300219601d4034200c2e40ea0300d2078000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 639529739 1250 639528489 639528493
    0x250305070b13121a0702160302130603050d1101050708091b0109120501020c010b010903050d0503370b093306071b0f050f0d0309090606020706080c0309 67
    0x208000300d6020102070700322180000c80d280c2c1010341e00d0150100000940c0c104031008610f01800407200d0665219045d0720208034009041401d000313241e44000c00c0c4050000912904400c0c0700d45607201856401030b4091035008045600c01c04048d4030140202900e00325118040d820000050f0b4030a114850f20760154210f68020010801c0c1d0440e94440c10300310310a074a0401c00c011000103a00300310340001c1c56400c2c2c055400141d5690340d50520a00b9250540011070601209aa007000014800125048020702a02e0469102c1c2c65982082d0081e241c2d0307240c1e14158218000207001100c40c16940c2007004031000340104081c940c00024003880d210b04440d40200d08580c0a048282c1c6822022014000d14410a9850507560004000b80a5400c031120a503400f680000241d4605c0721122048400340480e01c141e01d24032032500d400581940d52104220b4015480070030400304142c014500440170b454503c0f024041035403960b4000356038031514400c01001513010320108240400d6602180c0c020070b44100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 639530989 1250 639529739 639529753
    0xc0c011803030309110301060b090310051611030412140610060813030c020301050408090909030922090f06020c0706052802030c0607180602011419021b250305 70
    0x4058000b8001c078441170301c4180000400a0340343c0c1d400c1c0708060284c58004180c58031149100e040c5850020034400c0056540e20703010510941c44000811940d004505140c40c140c40d40d0014106400c0d8082c0d54448860035001407040f90400000c07001440302c9011010464645d5641c440d8003803104c20f0103200c0d031400301d8407000c00304204103805d00c0002030250203400c040341401ea4950200b82101c004642c151044800800c083c00c0c0c1c2c0c9030481c011078000c035000d2700440c280084c0b2000500d0324102520b400c0b0b88103808100b20020282282c00c9807013080e0300002c0001d6000100e04116029501c141b81441082c060b0a40101d181384c081c00a807007080111703101c008044100c5108040c03441407409035074019480240408100f4200400c1010b200f41c030281c3c0e4200c01c54008802881d112283d0350404400c0d641402c0090401305c00d80103005074040140803402c9a400744828000e4028401c035010503541e41c00d62018501240340c0002c082050031032500b41a62032079000c1e400b6400c0325501e0301004110b90024070f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 639532239 1250 639530989 639530993
    0x1c051c0221010905220843030806031207060b0105040513020702130b1806010e100305160e010909050a020409060905091c0f050f0c060108030c0c011803 67
    0x80e0240c01c200c641c848060149203007000501c248400240c0c4581c5849440e00c04000e540c1166121100021144090004200340f1665800502e4040c030201c040f0300b1400d42032031602101e04000d43c0e40600c2201551aa40742d0300310407021071040c0316020700b03502080030a80810800d0900050b03850a151401c0d085c1400c010259841201910023207540303504100f0240300102e06951140710044412540b100c006940e000503205100c3d04407012241091400e01d0700c2c51103040707070b1030b102c01005185601d40540034490390380310016650340c110210815000550300001450607901584040d0259500141840982e8032605048076040c507844801030000f1004e1a0402070301c0c0c990340080f038202c2c1c07000c0c1003d0f0a25031608038a00c00c403945a031110038010744420910642450600c0f80e43c0001c0d0101c50311952030703103c01402516540d0003e10351803c1000001d11450302e144007200b5201131a40c2074055030403559450b10030a99a401202040b0214007840c1d800061a600800b01d402c40b0080c20301c406c2200d2480c503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 639533489 1250 639532239 639532241
    0x5060f072708030408100b090106080c0a030608030a111b030d0f030609141e281806091b080c01030f02160803070912020d0f080403141c051c 62
    0x1980c080c0c81c00030184800880e482d00140003500c09440c418004104ea50840704d5500d0607550b002503094051030810740140b016a51002000c2c0e40711004a0040b6a02c0040410480003000c2551019641d4000850910714155024080300504412203003101e0007250b0f040304e00d1500120803190540c1c0740d400a540022494062520301c0504045030074001030340c43c0d441e20750718240c1d0f4844c060781c9219001c00c010000d49199921409006900422005030350749041502d5440c00102505203e89060721118901580d140b50b0b000328800341040401e50510f03d4640c50b120001d441c1c904011194440c22080030030b803038104111140100c07a840c40c001c11074000d0410041d0002c1040714480d21034183c0070050030007213503610018840243d2203207140d00d527a843d14850040108039150442d01e10640c2ca240070601680d14000019249500804540e5141141c1d14001541b0704c641c1c0d00081401e01c500c4c1924125441c08240104082a651050045200c2000b400ca0b418410224001189031745412464400e80711 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 639534739 1250 639533489 639533537
    0x31110020306420a030c050a0207182003040b0903030c0a1b0f0b090609070b04090b0a03020a060c0308060f010804030e0301021c1a12420405060f07 65
    0x11408a111614032110803c800810b034600302c2e000740b0080000c122640c154144039505042d801854458204075043c90001e40f5079860784100c0d0f10a02c000b5440d4083c6d0880c56110030b008a0b90755050116041288404010a0300704440603034a0050000008071800400300803240b08403408181c4600c1c1070003d82c000c1c1d0f09d20208035003103036010041000040029001180d044070b518060404819a49000365100e46070480041070400e02e9040603908000030151582070f0340540d8061240030502041d0140411240025a44060350020421000094080d081506001903034080d98506006076107071800e2294603160024410f0000d200f060001d8046031060b0609031050300c0c018001340c5418103400031030002203207400e8800c0d80c480ea12181c41005440c400100000b005068230303110500b459004515440d420404075a182504118103080c1e940c0c0e28681c41003103130159640c2603640c1c0120019103251020000c0300c0c02c1326584a5840410498501095454440c000c00d60700e41d03a9080c0c0303103101e507207070529 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 639535989 1250 639534739 639534799
    0xe0103031e0c08030a1422150b06040e07030b0616060f0e0105090127170a090902030412030f0605030303070e0409050703050a0209010603020a050406030e19031110020306 75
    0x102ca60398000050700040041d400381015810215104c2c642501c0d6000303640c009019010f41d110818000009450103c0c200303904540c1001c2c1c0d1010400d4048110030180255200c216888800010b0200722400700900d002c2c0110002e035003c0241e10300313031000d0007064814180455600d0090f1800300340080d0311604200c00003006400c0216101d0950b030100c500b590801d4650318401d9458500c04400740420406a015503c0c000c1c81800400003162101c2c40180d0007940c14400520b0001006d126182c00f440c4054010001140c3c02c40d905d00d020704028103001140107082001900380246180c1c6008103006002c29540c0c0140170310b1641e126200180c490a490486154100c3d4680508001041c0e00b40310342001540100041c0500700c11610400001c0803050b04400240340c410b001000c00b8541c41002c1e00c080e1138207801c0005500b0510b101892508a0700d103605004183c0b0600c00e4000c05a02964251065141c8000c40d038450320f15015002c10f074001190195004000c0507500e20b46045011620203c2003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 639537239 1250 639535989 639535997
    0xf0f070911120c18010c020604061b0804060302180612240301050f0109050709030b0705070c0b0327070303121a13020903070501080708160509030a0c0305070e0103031e 74
    0x101c0324024611070b40c50446200743c01a00118100c2c21244100e5000c0c03d0607102460070100b9081c041c0e0029506014901514007084003010740101200800c20300700040c29004402c00fa19203035100c0c0d00502075440340080c1901581c0c00d03214020342d400e100c000d89401500102d0081354030395070909005048581130620000f00f0f075848204041d00d440a11a030f50183d19401c80c22411581420705050a842d0060300d400100b102c010010408103030314516460b04161149403143d43c50649003030060121115030409100404000280304032610f004140c080365079500340b0700d81c03e944920640682c48440d07610010f4040b0b8101ca202c0e0b1204503456100700c5d8816100c21914000c0300341080400d440990b03202c106804070307500103101107080c0360410805005220903e021812441c0046005002100190a03c2c184030840d040f0924030901a5081d681546000703002c0b900b4401d01400e040e0200e00052100740c3d102d000d10303040481c2ea03004100201c1d0699030545ca88100940142c110011554a4102520200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 639538489 1250 639537239 639537247
    0x160f0f020d0e03010230070804020a12061d0105100b031501111e1e0d050f0304030320040513110a1d04060902040302091005010e1c0b07030501080f0f070911 69
    0x1e00d920f152001c07204040c6c2e21094003100749050224500000250640083c0008401040016520700c0c0c1c0040a03541c8044441104055914154020b071840095a500d02061540100c8200d081580590301c1122907038401070000356500300806580c0b1040d21100d40f0203c4095400c0340a5008502c05209442c0d1201112081c101d02c0907911054410200e000c2407070382140d030ba0000c0d5441000c1d1350740804c0480034003420020740c0d800d4001c1e181c0e10641c8983d20400ea400b000107001e240c025441019080c0807200d02410b00c0d4601c10b100b2443c0c0d4014010148111100842c000e83d00c1c0303441c440c40014180c1c400d10707607151802d13101041e0781e00d03004415615804c3c44030310b03100305076900c2d140940002000c5103070026807035a05501c104502b9001c0100014a40360500c04100110780e4003006120850500b9a142600210407030401504903000400251094080d5428048501d90640c86541214200c50941e8910031039000e0680d10341c01e90304001481d5500c01032007880041e8048d401103001040300d440492130 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 639539739 1250 639538489 639538507
    0x4110c011b1409030a02040b0d0f050303010911030105090612030f16030e06190e030a0204090822030f15181a010902040506070b0915160f0f020d0e030102 68
    0x3958050407510380e6192140d1109040d0070b4000001c19040700c4a402840e0910003260007195a80c440c0c10800f904c550b0300e5a07900e104c252a030441035114150400c01b1918500040e08002c0e680e68028805d200d88503180c021102e80c0350f1100d805881c16500028041c142d603490316400c00034544106400184903000c2003001103468610200204a5200031440e0554250000d0030003030440c00e00d141456005500801003901000000d500c0d4020302615400c103800107480a90100340b5244507044025003043c0743c203d0a41c20b22481c02c024004450b0540000c696141c0da03048004000d50031071100900140019400c1030005030803030f010b005500e4090800143c0d03515404003012107001031650907205803c030401c0458201c051520287d0140000c62415880c040c50480440e4052080040240c80045400003240b038868050255a410105403008602c0b00d003003049200d4031f0668a0045a008214042031519080d0700804645c0045640d54000d0041c4020078401603030300704a002103040d07043d5400c00856103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 639540989 1250 639539739 639539741
    0x4050d11062119060602101d0a0b19060f14041506080a0f020f1b03090a0e0a0e24070c050319080a0501052404050603010b090103230604110c01 63
    0x15042207001c40c10a4205181c110003c60140302c0503042c600d0900406000c0c1c3c94000655001c484c1840600240e040100c2d480d0fa10000d003910200c40c210301440400300140205000080d0080500c05050302c81b4000407101d0a0803100c0b54824400390300403009003000000c03841c0c5062003030203c0180007c103000c24030344203000380307003160360031038808602c1c1d000610101da002031290a083e10590711003113280070400441c0540a0203542103403c0d202440050850700e44000740155203900d5006003585a034552982052400c1441c11610420702501c3c14201304007078440001c000c0d040b20b02c03000d01040081080d60100104120003003401c2c0502042d0018080081d400300700030b10b5240c2c00741c0e0b403403000c44131100001428200c026000c041120b0a00780144007541d942011050f15014030b02122816084001070300c0c001d40a00d60140d9404a0044000190840140d00600d5041d1090ba000c210320308078048001e207120490005506402c07035210009440d402c207039006042d40c01949246509015101c404c1ca8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 639542239 1250 639540989 639541027
    0x3030c0303061d01080d020f07140301111201080f060114060304060b0a06020c010f020615220f02071a100905072a02010e100c110f030d032004050d1106 67
    0x100c0f42d000354004101da10000c4c4002d00074518030348041d11482c01d8034001d032030b610001405409100b500c0d06002d60300c682c0d0b00350b104603d1019002c400c141c980301c000c1d4541c2d49001c001d00c0350190f1801610100200c600c008925603043c0c440182146600081200034443c0a400003072040f11071a995007407541c100c2d81d803e1000d01c001d061540c010300c903c044000005040743e0203140007800b55400081440300076103000400d0030080d0420788400c00900821181c2600051202c442141d8480c13600000340140c0c950b540040000b1401441071144074906012020501c10701215800200288503a0905c10720200d5001341ea080042d034544101d001960594900700c00f5003020103001a6078500d0b1683d42107503040300780c094560008861885002c042064041c00980700840010f009034a050840d20070755540007410032051034050700f1110340c80792516001d002400d103a1074102c04000022124440c1d800d1500031030382580c3c070142c16048801e4495950f00811100350000d551302030382c140078451090f400301c0640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 639543489 1250 639542239 639542279
    0x150304060501170f030301090c0c02091005042a0c020613090f0c02010504030507060b0406030c1203090f0501020d12090215070611120114010215010f1a0a0903030c030306 75
    0x80c0355142a0a4484008000304880503913045030f5a041c04000004c8207032170444141410104101502082c129000e8642d0311000390700040040c24000305211886600c42580c2058404101a800c501200107003003c6901502c0e8240711401c0c01000d100b4450f2000d0120b203840509045d007040c4007a62a0032070865107420440d90540d454660602c2c1e075926016664000400d4002001a420540c5004000e40329074007025194540700d041c00e0032903490310b6011800443e0070510059540391244804c0c40c011261100560025242260116400e04000a5201100e10507002000920f640040603600e00b580e000450080503603c0041402603180d580c102102544a045441d0f61740ca850b207003500465024a80e45401c00d03105021300800c1c3e04c1649a01410340346512004503540c0e02c00d00040740340c03849084070304120006040000441c14120510700701a20742d03040c036040006041c0080700711540038510868001400c01c180800c0030901807101a41028028035021680a4a40007016240411603081f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 639544739 1250 639543489 639543491
    0x4120c0b0910271403040e0f040308100b1e04090e0106060f08010e13021f0e1e150903071212140310030201050a0216030f030206010515120615030406 66
    0x201c0400081544190745195100107440840c81541c0c000115401e40c8105000b01300e010f52a034000c410741820019500103082c06644401399240500d0b0302025160103541c01c0700410f41c03880114405190203010b030405e807085c51010a003425000041c070b0038010b54907103403001002020000070808085601602075810003450020400d685026401046130030b054020004000e4840b006100c0d4078070000119410442c04c0508842d00d886034000952004080b05640d2010b24084981418140e04910038818080080b202108500f2825401d0420b012503040415404203140c0c610724200360385070001d0701034003001a04a52850383c0760400e803045414119401ea55151880302540c12650344100c215130f603000000d000e5411410b088041c55400c40c01804000d05101010844000c200d1082106000c0071000301e00a4207150756900304962044102c0c07009034014010b010004c0b4540c01d090007022040700d41d19010300d1824000303940c410300c0d08202420840c1d002c1c8481405002d417800e0700f07019501603801008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 639545989 1250 639544739 639544753
    0x1e010803070506010f0b0a0e0103020f07030309140f1e070e010b13050d05100b0102010b1c050d0c05150c0f0d0c1e0e041a06040b030a0b03011404120c0b09 68
    0x2040381c90407005034044001c41e644020305000c0c0140900070b81f1400c014a051210f45c3c41040c40c0140c0c0039004000741c0200c4070340045041018998103070426544203000700e6280090341c2d081d03038229484400c0764404108a03403100440014840030f0805084802c1d490506440303040b80c55802103c282d600c01e90045108500115030900c0301d520000e03034030b8002c14088800c4444000d40d5907940d61502d2259107101c1d50030f40d48544043d502c0e4004e40015007042c10003800c0d298140c15041100040380042c841c252120320034106001041e40c000c1c0301c0d40803138641101c000c0c001007900f92040000300d20010710848a201c800e0002c1006429441c0282c62804481180864560080d4400400205e2030740d04005200400703405550702c180d0031108101c01c00070162030101c1c0042509007140c40c1d0103002040960440c0300000c00240c10f180d4000514000c9410301340c14008000640201030030780f034162180030362070180400450700043c03414003680344400140c142202100c407540c4400e10104800c546400040d00445 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 639547239 1250 639545989 639545993
    0x90a0812100504140f04320c030a38040b0114090c0307120617010b01170103110f121515010815090709031b0501031109090703051e01080307 62
    0x701c00c00140c03106030750400c00d940c081050400c80d8100582041c051101120200e0140b000c400700c4c00a240d0750450854922101c0d9030b2071621181007462407401c65000340d08601116243c0441c2c048501504005854403013000d00100c00c1c44c40200012901315809840780e4109616000000e19100341c0c000e10322607045614240344074146c2e901e4001c00610881110b010080f80c24102001da0b600107d2a00e03001e81d14a810424980050030103400003940041d03140c1d1035076120281504661910802a41c0d1101c0100070315100c5902d002e001e0000034100d401c641150b1290742032003440400a43c0000380035081000301c45680380d0602d4041444801c484d0540420010104240010510001d90030300e0101c9081c41c0c42b03070011510806d400340305486180518042040203101b200d6070b4025540100d4829040c4100110006000d8002c1c801c180c04a0300b00b80540c68111125000e0355401280505150516034405004134000e0100425504a60135011a040a8800c0c084910303070213031080c8401150703914414 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 639548489 1250 639547239 639547261
    0xc0f03080f0a0c0c1b0302030f1e0a11040f0b06070f0309060c0309031e1a06011803050a0213110a020708060f040f080f04030b090d140f12090a0812 65
    0x1c10070b10740b05003050710380c600e0341364407440c1d10325480d0304240f9800401c1c0310300da03100a2500480e032020f0f6040c410342d610140416808120018800f1182c0141003410301103441d00c50300c0b00c0c0300304030141040d07008249030303865030500b038121240141e0300c01d50005443c3c1908001440f260880e101c250b500606601e1018100341c2c0160b4144050150344c1041c0302d002d0401c0e130f4000e28181c1c0600000340700804900e80c0040145d007204010103015801800a84030303042d5040c903101c112400700da280740000c00000c2c00640d000c403e698407209403600030307001c3c042281c3c458085c00001d005803098000c0450366102400c1c240311a11014081440040d4080d10301130740f902c0c200030325080011b0510700f034111000040c000015403100301084020703489080151a50700042d014015030203641e00c094648240501040445000441c56040d0602c054946c81211034250304a5a0580103503010b000c0b45100411030f564175186d8413120740b9440b00c070a4080301c6d103030b0315a42d0350445039400000001c8540b080c0502400b0003403040f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 639549739 1250 639548489 639548491
    0x80106020610030221030a1112040605041712041d1f050915060a0c0317010305030d090c35030c0d0c1103010c0e011d090a0c0c0f03080f 60
    0x19510050000e0704080d0101000700145110003441031408400380f440d036488003030103180385541c0e0300241c2c3d48680400c4800790001506100c01c1b070b030b54019084a21444400002500c00b65820b943d19075003041e09000310040c441c1d0b41c081c0728003c503220b0780e4a1138030406079000092010f0506400940d0b92030055410707911a003000580300c0c00c03503401040540310107050000c41100807200100e4854881e522003a0095500d2100366220a400810028901a020b03800c90490318607103100e9614180c902c1c0b0020a1404d00000a01000340660400c00c00c45291800c0c82c0c0044401c1c078011180f81510955500f6007003905072400002c00150501c0b000d01d95000b8220005811030620080059480c11003200005926110400c12080622140031101c03001d100c01002c024400d09000b0340200101040032001800b11240703403c1d61170004003c185c0443c50800181c41100030313180050b01001c03c03506c0e0001501c0c0038214080c4010108001e4241c00d0740031595422260007020301035155071145c0c0c201030740c40c4408084 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 639550989 1250 639549739 639549749
    0x24130905060d030e13020301030f030e040507020c04111c0b0307051806010c03120911120307020d080a020111030a020304150603050d030e010605150d051501081305150c0a0801 77
    0x8509001c00c9207544911002c0002d0742d525141043c4074036024800108201405a40442c1c80c0d407001c80003104210500c0920304409000e40c850422020042c0e00f0030069034000c59007280141c014514000c190308040c1c00a819800c00898064141014840c80c1102940c202065982c0c1e2a04d6400e8522241010b00c0704070b0240500741d451001c4003101014805005001030a451b04100c034514404042c98070592108040310b0101c1800d00c130b0303a1078034106688035090241c8a14402c1c2c00c4c150012000e03020000413184601c0c0c0c05000060340f00101d07181d1103034582140440e03005554071001529070b506890f2006610500c1c00060041c2c880c1442d080282580003210300d002252440c0580030b00c0450400255418400b41a1601085040340405001e016003007581c0035079040070010300c401d000682e500700078011036000c80d0020800c030703940c03400faa03403100c1031180e0110302113020365021070f502c0d04042c010700c071185004800b12100d0003843c158070740110800712111101d440c8045101582c1c00e13030051304180101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 639552239 1250 639550989 639550991
    0x3130e04020d110a05060a1d01051e090d020415030b0c0708040b130512030702042f0a1106010e072706052b0e0d17060906241309 57
    0x8a0241e0108410040c0100080c104061000300203086944851404010b8070010303080a1304d502102d40701600402c40116005071402504c0c4210074154800d80030303581e080c0d103140151041c3c0b500c92251250a9401400596004000300f00f4010243c1c8940c06405050342084100f540c01910354280010440005469a001c1100c20002c0c507011880000548003a1154050115139034100746d0394a007040c0d0010703801b09401003405101b4152100c408405440028020358050040a90034942a2440250344042c440440071802d000c844480040000d001020400d051800c01e00a071014401c2c0342400c240e1001c041091004204000d20b41d0010300c2010000501c90000c2c5040c1c1103c290b442564054091274042101c04030304540c0352440b010501c815a4910020945a40768181098002d420b500c10744491500c00c16034a400450702c00c17980902d40c156011400c0005884030303003c0242010000c0c00c800c1c2d11207140c50b044c113421b54090009200c041c608055007551f4816012424007041e02c1940410300203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 639553489 1250 639552239 639552241
    0x20706140906240114160507061404030c090908070606030c03200a03110607080c010605040e1903080a060b1602040b0409020a0308030a0e0706110c220b15070503130e 73
    0x90b01443c3c2403010b420405d00706031612040c03141d14481c107405002c0081c01d01c41800098001403000208145058410f107541d102c07580c4209950b041d4480c03085100041060040e8103041022920607400a50308034464850280780140c280c507200c061301d0039900700765604002c410040007041f2f080502907014500a4590581803490080050b101001e24407018200d1034400f041c45026540300b0045410180d8854500e80e160380e890690b46008020034000c160240d4030b441ca10000c0302000203559820100041c90180d006201c90707504442000001d4000700740c298640c0b001040241c03004000c1c10000c2910724082008200794010841a1a5882c514070701551401901d0009a100c072401d21040e01e4228449030b41e26100c000c001e20041c11b00141c40083c0d4040c03500f01185150f80480c21620040681048030801c00110041090091001190084483c184024a43e5a40e1150021440d214004040010300d2282182a00c00c9610840341220700d0340000980701e4090742484880c0000c0d0071a0070642c100303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 639554739 1250 639553489 639553531
    0x180405030d050a0e070303030b032514040f050c0d060e070c02091e0708090d020313170c150403150b0906090a09020a09090308071e0c06020706140906 66
    0x5074400c01c50740400d003989410005a900b05a0f03040400010b604c0d50448441a540e4280200140f00500c4041c1c8240180d0030342864801c40402c0d2220343d00901856000424076090400c003116405030380042d002030b160107050403104c541d4070031103109216549155039580050510001210031581220440e800110309011070035078842c09400d26103034143e450a00ca625540306410b02d0000050314050303c030a01c0310822001e15440b500c800d00403800c200844450301e20074902a0780b40e000381d4071101030b181c407861020001c40d034100c001014203850036020b607589034041c00040340c070030f205a611060014900080802c10808061202e4515029801003009100701800c0010305e0110050040c5200e0503503040400d0b0403410651140504540c0100042c0c01035a03503ca5040180c18030340001c0d00443d031081c0c001002940920301c000200d5019800c50103580c24134040030b0314105814001a00e8841d804d0014034009001c51240380c5098500d028444000c0c0703070600410340b5299008180148140903401c2e4041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 639555989 1250 639554739 639554743
    0x180415150302160503070807170423040e0706050309121905090a0918120f0e040f110d0b0a05030a11060f071a060f030c01090311040905150105180405 66
    0x800c2940307103000b40c1e5400101c0d0f070301c0d50b0300b031400540507245010002d070764420040300300e0081c40005e10552914100303c600c40c00118641c042c0d4400c20032100701c0e034560f40203100b000d4035411040700b50040001880180000b8000c1c07800005030400d00100f80c00009200442004010188400312a400c84902e82400c0710114055003803102404000c3c082c012500499641c0c4400ca81c03005051101d400300b107180504a40c003651140c0d03800e41511441c14280c003611100b84280f8042601c02010f440d0075111880540900c401081c1c1961f020076041e50303400c50b20704207040e0840180b40d841d140000104a4540700310810402c0c901030b0b40858880e030b005e0340c0d002c800525400001100150221215500c480c11621001102d201710301000302184540c04034080e550004105042c0100410303640100030401c00c1d0203140d0b0b50403000c0510380c040b0744032140800015125400120241001920200da11149540c4491908900007400060001003d0060219040281100c24102d0310000002c906044c240c039055 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 639557239 1250 639555989 639556019
    0x605093009040e0a12090608060907080f0403020709090506100e06090711011808070c0603020306060d0e0106030c1502010c030213050d26041409070905012003180415 73
    0x1601854032000744a01a030b0b014030010381655001500c3d61204000b640004280034021f000312004940c5003070203e0210306060701540e10070b01003500d035260701e0b8980040d841c0031084000c1046003140b14144002c140002c0d18021149014410703001000641054140300310055081e0b04606a00b50618041114076501c460409800c8442420038a4000200314002c502524014041248a511415030f0104001d040300042013458080c0d0185030b201521680200c3c1a48000d654090788150140702d200300c02516035004e81822111040009040396607695030180c18030507a4130101c0c14901c1d0104400c003003078080c01a2141c182c01494218945000310b40d070401c1035015401400c0c000c1d00a440d614003001210340c0d01e10002130700c1d81080c0c80380c0c04204c0e029251540c0030380508202000051480d0390b80d804c00426060240300c6680b030715002c0c00d0802004441061001074060243c0c04040b000e4559482c0c05e1006041c4540340d1581c10000d07041c0c520502042d100880c0642a2005000700d080200c1003940b4000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 639558489 1250 639557239 639557257
    0x20306090a051f02120114040f0b03062706150a082e0b040518010c02010b1302070c15020304090b03060708070f0c08120105090609090c04020306060706050930 70
    0x140c029001010304200217000381005a9000b0807500f00208020344d00046000c02c0c000c0c06c070382c01c0c009800c0700d540270700c159101004803d404d80d00c4880801ca0300344118038031a480c0d45054070048480c3c0881c140c0a46003060a032450070400d2081003800c0c0c1070b810541d030454040c0120704002c19509d0105110002098139003804810104541d0000480c500703009e8201d40c00441001b0320500490902c0300d8241205480b00066280c2d5618082502c1c0f00f450041c002d8691450307000b0890490b21429040a0011f540a040100c130800e1801c4000324100304120080d01002609600450304c90b418121140111008804c00358800d0b132104003005040c0f68002030296000010b071400d20b100074a080360944004000840003000d410001c2488881202c9032003143c1d040b96001ca407860312948981c01402001e41c01034840072240c0d00302c0184612681029001590444400303021030b8604501030b226003084403010780700000070b80c01080c0e808141e043c00103405e01884d03030710302200b40020341040745901c0148500e90103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 639559739 1250 639558489 639558523
    0x70f08040f080703050d14042402010515150f070b0c120a05040f0609020f1302030a05060402070305040e040203070f03080307080702010c17090a0f0812091609240909020306090a05 79
    0x903030135104070750380248d40c01441208055014010700e000301003c40d15003420f0860041d0b207400d000915100300420940c828040241070b09480e900c10418144117503129030000074032250100305100000d51800d41a80c410000c681540d034072103803103071410704510030090a44c2251700d0800d0280b1000c20301c0034840985840c2d0095000481e02070a10110303004901060310180d010360f50703184224107141135400540c0b003510700c001c080229980309410842240241c01002e400200e00b404240308506102400903001070005045a240a556404c108011580c40d04101d030404808424054610b80082013150480242c0c0004e01221440c1100100090420501c0d00c80140c1c4100100310160803d008039101141c1119000f5280c4906080c04805684130181d4426610341c030000242c040d01c804500030300d0b201ca46850a5090710314202062002d05001d28415100c082400b01e10314061924503a198010030b40170601103000b01c5c20740109410b00e54000c000059540080007030b10b000900100300085455400c0d91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 639560989 1250 639559739 639559757
    0x10e0f0d0f0c0b1803060702030a11010b06030a0e060708010308160204020408060f01030c060503061f03150f1503060806040f08300603160603050903070f08040f080703050d 76
    0x205000504440340d00075015050b86000070039911805802000c108610b002254404012a01410b9460204603002c40040e0418403082034100e21400e545294242080b0002c17510311000b20000d86143d00c256030780c15184d9529490b42c20304140520a00781c0c02030407410549801e600d59280c081e40c0344a010010001c01021009200c11555954142e078064a040800c440007490003100d4400980f000703000c107032103994007280005019440341084912851001c2c0c503405601e0880201001980020701c01e51062640300e1404412424103906040002c140016500c100c440c07400c495007012840303082450003014101355040c09100300c0010110303007060784104c1ca50281d400c1070600e540306e40115002c0b6494000408000004a9501d82c55507101c03082000c07100404e0b4844000b050350310302825039450480000090204070031401383d401154003504c0b250582e4640a05d5956510342c0001d0600219491400407400380000c2c41d200070710380c1c041c165a000402206040d500d41075034802c00011154100b2803151 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 639562239 1250 639560989 639560993
    0xb03120c01110d0b030601051c0209070c0209130b01120f120309020a0f0e07030218010806012015060102070302060f0d11030414010c02010b100804061b020d0905010e0f0d 75
    0x15006201800682c02e069455800884862015040c4003100c148240f0489002085619000c20003a040351031600302240000780d954203101d10111700606510030310840d50602000350310741e06c0605104e802c20410960420126180001c070350441078020100a09800c100c5800180344d0100c2140155003001116811514449080f00a005107100082d00000340400000c1c3d4100d0b0480d0403400c2c2c0d03400c840e0703091441d07444031421812030080c1c10480700d207100c9207001000254003814516070800c406140840f0384020000e40c2c0c141c10300443d2000a9154400c0004400890b99000c22030340281007440a0904207143d41c0000340036000c0c05008800e05000029101c0039440194401074a900008210f40c4e124a06414a4a80d125203001c04012650800c4178401c24a441031040c8011140300610170b180320041d044084442c030b50001d108a5405135200c0d002002e510702e01d100c9607c9684075500400520020038401819020325501403810702c00314540e450202e40e18440a0448a003090f1a0000b08010318 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 639563489 1250 639562239 639562241
    0x10207090f18030504030b010b0f07020f0114031e060a0812161502070203100b090a0c0203070503070c0501020d020d0f050304020303090405010b1b06090304061115070503070807030b03120c01 84
    0x2c400e61a5a9800040180304268100001e4001c403409040c0d041c40c0d5a07a1000c03107584c240318010401e08019030411440c801450682e81802001c0340c103150040031a601210010f4aa91040da1418900072030f582c9155009030072558100d40c045029a00c5e0440d503442d001100c4d9075010b049001e0784802d1400302d500c0c502e81c01e1540c5041009500055804484503c1709a104001e40c04560300b41e020780140450b8140d480d44034000c15000c035202400b94002d580d104d203100001007550241040440c0005c1000001090381080503000e102d0150850300d103c1c84c42c1c040060720f48203480d14258190b40005481c44442d40c2c00c1010345d80504d038a414140e0b500c0da11840001d0440c41044116507100c0e10301400031411f25800c0021b848003648641e0b84180da100640314440c0e49a03001c5170070078560307403080000344030031031086e2000300b1020038007400c83d604100c0c0e4450907142d04100316041c10001d400402017202c500d0388090283e8210383c01e810208409000f180100c0d80324065007600c00f9482d074002405038620002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 639564739 1250 639563489 639563501
    0x1309050f0a0b0709140f04050606040f081e0d020a0f02060d0e07090b062d0c03070b06010e0409020d0f050f010c02011d0105060d030e21061006030506010207090f 71
    0x1014103035075030601d241c0382c48408140c0a640080014818800108900407114507808202100034003a82800800310100f00192130003d0000780c2107039050100049040e03c0c180d05070041c1c50040090110303292003401800801c00d1600d514401c9a10410060105075004549010345c0b64121a03044159031813070000c180d003440b0780892506170518040c00f4100c440e40119440c400da680c001424089a040d500800200c1d004800c500b0001c001801e1240e0b40101081001c264600508a445814426100406404c42e0445001034071589211020041c6a69220484102c5020304440800c150185038011814094103000014a0110b90340c542400b4040c0403c1444606844000244034a100c40c681c003d0180012841e0107801c02c03028900480d0440041c000d0600c03451000d4005140440c0f1500c049505500e404500c51300031002004036020888000c524441020074180200b2490400207030301032001c002d0b0f900c0402010f1805042c081d80d6a404a056400c549040b4408076178180054003c20081c0300d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 639565989 1250 639564739 639564763
    0x109050d150207170309010608070644100501090e060108070c02030f070e010e090d050a12020301300215071b1205070b0322030e0d030509040c030b130905 68
    0x555180410f44c10a07035800154032810b11000240000c03a40c805001d41c0c0c0305c61901a501c0803490249046085540420926511640031800c0341c0c3c0000303005160403c000c0040500546c02050901001190b10400d071655008000c20311f00f80c00042c2c50111804034000010301202d04100301880401c04842c407407803000b41e01c59001800d80c1c102d0590807581581d140410700c240c030400c201110001503a02e9a031003d0314417031005080904900300241c41c089410358402c2100c54240880b1281c0e00c050041c17540701543c0a0060001d00140310008000c01d20a10410404c0c0c1d01c4160880c035424100584442c0c071011808250907c280c1e4032113582c0c1c5404024184071001030a854060314400054240c0d40820071348c8414010010740d40110f464142c84c00e86440110340f402007400c1190300803001981c01c0301141c1c560034044d04c0e10300603000031480000d44940068a00760001100032607454103900d41485160050a40f9080400c094055900881d104140348424445016621828002840001c0c0a00a0000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 639567239 1250 639565989 639566003
    0x1903090213200408120a050912010b040f02070506060913120e040f0207120302090f1917060103030813020d05010c0306050103230105040509120a031e0606080631020d0b0109050d150207 81
    0x342d10000301a00810403482f80da44101d09141c0010220083e03442201d00c055001400740041c1d681c0d4905204104c4000b406540400401c5210000821401618134003044c90982e5070342d0100030a4004c0100b82ca0400c0030900e100340c41005400c0018041c5011810b1408041c140961106100310004071800400c4458603008801d0f080700108030305c01c1c251914180ca200e04225502450043c0e80309540750b07401d0100902290444010949040324118000d903140e10080c01c1803a040095038545082d1154582d020000c252201002c0c0055138241c0664050a1507065040020100240c050000c0354410300c00c141c066640c3c0c0e000b05149260a201712159140c50349d01c190343c1c515010500070018001c10000002d03444107500d00307480e844194080d400c101c5000e07594182083d00c41408020405013050907102d81c0c2001da00343c060740c1e00449000c520b4411040d078070068032035600c8100c1a003620802c0c08424100407031074006000581e9140215007100b5045034107041c10f460046401c000a206034200504a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 639568345 1106 639567239 639567259
    0xc0a0611120c0a1208060102121e0903070915030c080a0b04080912190614010803190201060b030a0501180504081903090213200408120a0509 62
    0x1e40d040c2c0c0c00d4812004603695403140e02c1301030210a00105000d101001499070701400f4001510444010640c40d0805205116094428207a00e0060030345011480180b252800c12065010b007a0418041102c83c1c0c51000c01040c1108a04c400c8031205940800420071441c003056035244294071000e41a0340d40c0302c943d41ca10b4142c006154a94002400080c107004001e0100405d5240800c4c00c2c5048034906240e041c050165410141181c081310042001003094410000c1120b00c40040e11000700d018450000049000d405030740c2c07080360300c5180482480b0f42004580e00c414100c1e00d819900d04580e41d440c00c0e10009449040390098103850060040141c2c1440102c0b200c8001040c03480e00007420040341d800a01001203003041c13420100e644d661001080613001d2a01c1c0c0b01d512030700280f075042a00d44040c441d500d1408228032000d001000c40c812944038051000d403010008010100102c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 639388489 639568345 := by
  have h0 := BRFrame.cov_init 639388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 639388489 ≤ n) (h2 : n < 639568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
