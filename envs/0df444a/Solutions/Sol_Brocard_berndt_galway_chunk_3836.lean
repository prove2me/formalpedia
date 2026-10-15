-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3836
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:49:25.379985+00:00
-- url     : https://prove2.me/submissions/63c2b96a-a332-4520-8264-aad0b32efc8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 689748201 ≤ n < 689928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 689749451 1250 689748201 689748211
    0xf060105220e04020a06170a020309070f080109020111060f0402010c1509030306080c04020406050909060a050d06061a0c0d0f30150b190c02060307030b01020c0406150507080c010203 80
    0x11090ba1031a1a005200100e48554805402c111002c141c220b510340c4a41141f40e000140b0000240e070300c1c1c40f0010401c2c9007901d0b5401c050b6a9804080000a40000544c003d014a903c02e032103100c0d142a0711100c0940b914021211200c01d09000b00000b4015803080c00c0740f201e090301c40d0980e00b0000c401512544100c80044c441140883e039241c506000481e420402400102800c450952400307003003001c024680d00801400502a030380d0301001c0342c065540c402c0c00d0400380a000d8184106080a0300b4600f010b8a4140b107004045e54050f40c1030504c07c100320085865510b541c1d0000c00d0361014011088406c002240d421b40100003010101c01a500c001076400d01007220054005800300076403a00f88008c5038181d03183c00ca40da10703000100b007000c44880c10981d09060440700c906140441c500b0800d541d6940c8900f00258825400020451500c3c3c1550083c2010f0500380d08803190112842c003448115900d03802b071404100303950007082110a1280d0020700344103204c0e0b201c460800b2041a629400d980090310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 689750701 1250 689749451 689749469
    0x901090e1503010501080606010903060e0106150816051806090111070b0706061502120717040b031503010b0a090b0f0406090203011701020703050d05070c02090a0b10080f06010522 79
    0x40444075460240a290701400c14030000c0d00c914241070300060808201844001d00c4541c540c0c071489683c0d034003940700c400200204074034000c541c14124002000d4a108845080850744103551651180b4811401d80c0c035992180b810410750010324204210310781d0041c1030b42030304102069076000710010091000000401030903000ba0b84400031850100180c54240d0050400059070803480540b42d030780040c0ca000e40c8603800540c0c0e81d40e03400c10b082c41c04052001c4840741c0042c0d00005000100c5042800c021445825110704010940d994001010309989203030805961120105000b440340c100070b0b80c00b10b014403800500c0b00c4080300003007003c01c040e03035004c3d070140340b01960210040020301608201c2d042c9025418008510300746165030058918010220100c198a558400042c440f42c022240c40e100650014080c0c940d61a00900600142a03101c41d2180078207070610259034a01c1c0155543c6000780112484038000c1d41d2010b0046580360130502c401d0b81c050700303034101c0d012106001c1c940d0346001e461042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 689751951 1250 689750701 689750731
    0x12070609060603080a0e090c2208010510051003020715020c0c3d020607182414090f0d08160f050c06040e07080601030608010e010f0f0204050d080901090e 68
    0x11809030003c1c6c04441c8060003210810200150042c069007101c0c424034007001d50031003528410210190041d01a00320400541c030b0300301409514a00d0100d000211201242c4041d04015440812410b90040c5c4000802034154844141a500e038160041e00c0300a8a082c04c0b60a081c461000040204030520850103d02102d410700319044003110603581103400344450100c2600030340d02d0740250303114001402841041001105641071203102c040401c0203060400c0c6c060280511911003c904285030040ba0011500740480390b80c08001c10b1040c0e0300300ca0002809848401c0814080c0f000c1d4401d000300845154a04120b114071803409800c5152825015584550303c2000c1c51501e50314140c0008d08061180e4024001003110014901d4180c0c0d00c0049807515080d07a03280e85005802520007600040f400d94200b0041c0801e1550540c4003c10003064008280b1402c1e03151100b40c0f0032271060307001e10b41d0401107040c0041c010520a80080c00c4050b0b043c501002c420341e651500300040304042d10141c180402c4c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 689753201 1250 689751951 689751967
    0x1b181a03011103150901060c0f1b060324050d06050c16050a050d020c0d02120f100b04050a060302031c17191a0a050f0415240807021207060906060308 66
    0x210440540980050368a05455414803901408c0c0103c07c0d01c3c000c0c651008400d0b41d40c10819031220380601d14640a80540415849031400340280000744014200b107a80300a0034001c01c55084010000c44402500c0049054019190b2030b000d050003c0241d2035881040150707840c590011404104124051409080c011019290603400c20320412941e00440d44804c86644281c1c2d5004202c01c0065030446021801a003442c40e81070510800c100030f8090741c00b130103869081e803a031290030201c0b01500880b001c1001c0da40711502141224040e0001a406178440c000a440d4003003c0303810300d46d2170803c50a1102e1440c0c2c100c0c03108000001c00300e91420072107145082000f02c1050308e000e034980c4540d190494200d000e1500020980c1d04a15200c3d40e03100b20b00c4400348080d40d45850303000b0b4030040304960600e1480c544520348041d070200302d0141c507503481c2100800119410320900e6003070300a0744954003400c68202c00e80d0640f2226007200781c05503841503032001502c0c001803152041100441c0b007410340c941c6440074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 689754451 1250 689753201 689753221
    0x20f040915062307060e06100801180b0403200a0c030201030f0b030c15090d0b060315160503180a05010603060f090c151107030506041b181a03011103 66
    0x3050340a070301800006108803254402548520241c070038030315030413601c4d2282d9040090142001341c21070250b07800341c40305010f5254448040342e01a103103824028005c01080066a4070302403070f01003001d02403c8808000c0b0300024403400c0801c41c0030706064216018160b5040080d42030000d0243c04890741080c622080046581500480030301e0702c2c81050803c2030031700e04000300b41c54082c14600e0f5403040300c2c0303541c442d611582c00300243e500c1c1d030b100505140d1103541d092074034910081d010b07a500b0344a4800c00ca103580c030051500798100e100702122044d00c0307102d20340031905031141c2d0000f46c2a00c0d80b0035030081d030858050800b008141030a41c0285c001103012895410b103d0100c1d201501c0365400d4038200411038003c2504109108200da0405540501849400c0030031074050042e0750480c1224022000000140000051001c2c041c0303010304803030400000b880c00076040324140c9108411012112905461100038690302c84030180c4080710b040802d00200000190860706401058144080080140a01030b60 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 689755701 1250 689754451 689754491
    0x90f06010f06020a1506180902041805190819080f1605070f020415080a030f05040e010b0c01091e210806131b05090306060306040b19020f0409 63
    0x68070003180303400c0ca81030640c000c0d200c48640b00054902010115405d10361a803aa001e00c000b402c80d000004268581407010401a241210040e48214104182940301a080004a04006038010300412031000d8023044616000710f0340c042070365141e40a0041c0034041c10442c0f07140310004059034a200701450b10f03903c0044e8404011f80001c0c0009006c0210b01001c3c0d07000b0041b16410303a04603840310900d40303080c800030380035180e545a042014042c0100005610b040095040311092190700c0399449000200350480d00c50081e40314401205400c4001007010f01e59580c0140000c010142c004110701080d900d404664100c1d4450002c0c1d4500000001410f101c00b50800c1c1c4480081e1410b50205c41201c020000c21482d0041d01041c130800c1d0004111600784401c5d808817803030082240c0c504402e0b20320820058000e4102e10b20441c02805840e000840c10301d00419250b108581c094011032031600c40d107190303501c090320030000c07a101d9a508001403d100704428010f00010600e004001c1020110221000030202c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 689756951 1250 689755701 689755709
    0x506090604080307050c0a02030d030905060a0b030705090604290111071a0f070c09151e090c051b03041e060e0402090114120912070b1f080303090f0601 67
    0x3030040014040040d00b15000c980e040300300ca24140f0744800480310818140680b04000035410310030031207603c90444c2c054004100003801034007990400e42d607858284c0151600c0043c4154982c0250000b800715140c0980740303d4024001410010703098080b40101e030f1480001013403040459240980d0700501e983d1210800ca50040d00c2e070702070130015140041c02c0445240141011510110100d200312a83c02c0784400c1d100ca03981c10010303207040d4030f5550204000070190040d400d8084901700d200805c00421241d80d4008404886034800c080601d0100058024105040c00703100300101005080140030041000303d06200d07007107014507551403500040722001020003544010911510000f0071000d60008a0341d00d001c00160350242e41e8594540040380d2035021007100b039283c0e16000c1401c0720400c4007000070740d11030101482261441010248511a0341c0601034009080300b05060000b01900c00f03082f4201c0c5245552450350f840d050700c42100070b0658108880c030245a034403070480d1206c165001c011030350040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 689758201 1250 689756951 689756953
    0x2070f05090c220302040c0c230a080d021804020c1b040b0d03091403010c08011202011206060c02010f05043602030103080304381e16030510050916050c100504050609 73
    0x343c0d030703656211034540c2021894a4065150249c0f00714007d401401030030345c40d544c00440da07903072080904d5007c00250003d00101c4212882a9020748050409108640c034508114000b042c40640104909443c080c007000c1c03498100da1140c42d61f650685441d0300c0341e109240b1a40760560251308003500302881070400051140300342c3c10003031400c140700c2c3c104100905481a500c181050b0050070b000581e145500d6104c218500b518041000a8980d84011800d85941c806d81c0e941c1d80801d00800d0880e0301d40164040d09140d6411030303849440c81000a206030310054007203c0446041c1e0040c0d84040102d800036032068540620000402040103c04c0b044c0301c034200c0204000017400461250030220301070708840350b0010981c1100100b821592001e01048a102c1a0064400c66107000020611121054110000440d06000100b080841c2e11800d0030280e58003d802402259524a001010800c440041b0400c0c09410003d0960304481440303000c0c003a40f0400d5000ca03040c20b2920380750789030020041c10084a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 689759451 1250 689758201 689758217
    0x513051503071d1f03120311030103030314071110091509030c1401020a0203030a091e0c0609090209060f0901050705070f05090703020702030a020609120709050a0c02070f05090c220302040c 83
    0x13a52a03500d02101501d411140900d50302580c002c0030f80082c140b100d99006a028040000020581d1541008015a01c18500c0d00e62584a180d016150410f4110944074280c0082c60038200034485a400a000079000302c0100040130000108981103d03880c1400341c000420020040c82800020030030f50165003083c0008500d49406d46000940724000a81115401c0c0d4480302081d092080c0c42c40f000c1c403402c3c54104840d01c50700301c91804094000e0740c0d10503440132a14032000007452108034401c1e2041000090000f501e0480100362810f1035a00404d01d260521405010f50b0021440400c000c002030240b1102c2c1100c90382c20300f010003c60300001803001c0101801005108016240803031020499076068a241362107012040001d43c50024030020004c05100301000090700620541209014801015003009420094401240c4800707960003010030090001e04204070b58100300c0541a130140d0102d5807a800c25001c50080b60708035800341c00b02481c4100c051014015443c142c0f042100c0343d1002d04041d54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 689760701 1250 689759451 689759491
    0x30602181801060c020609060a02010b040b03011a10021e010501060318020d02010c05031903050f0907030201050304080a031401150206010626040c080a0506010801150513051503071d 80
    0x108007101401900f080000e10011603045450b0031090700c1c1c443c2401001c05842e00d8282ca40280209070000c82c4512650401103403e96070304041c8101501c0300030440900d54162204414803102c852811450b40031403003100c590850003451109510304007106200007148035403411400400760342c03007800075054a010385d010800050350340b135035201c0f00654207003003d0030483c0d00d07810440e080d4082c220788a4440ca21000c0c02038038856040d88800e1003485801d0030035060340c540368189075482c0e10034000203000c03407000c0001c10045500c041c09805071100d14900461106180422240341d04000c0e4407443d0703280824200510181d405001e02c6c1c3c0501110314113500c60840e0060402186854400180700700c0d0308101c04039040c08000081e4030060f000340002c80301078404510b04166614024881c00c402546029a00704500d8003a00c902e008482000746450803d0084d020701c2402000c02400015007460343c0b80c4a080151402e02061005098014000048050261003076210358002400307030b0082c580312000700c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 689761951 1250 689760701 689760739
    0x40c150503060409020102101503170304080405011209020a060e040c1403071b0206030f090d0509030c0f030c0904060e120f07030c080d05010902180621060d0c03060218 74
    0x30b80c0c800c200f00c90219500e02d036130005078200960001c04075100c0e82042416150080392203441c0c2c007224800c51440f03401d4240f03240080300324001520005e01d2141c0c10001003220b50301c61a02c01888602c0d41400180004040e40021040c100960042004c200100e082025070f1800f440703580c00c24004c41c140203182d000d80c0c6000340c03824800107080006208680c003002e041c072080f55182d07482082c2e01503d00d0340d413411b00944c0c1111203202254084c0d110b00c9031b44a16401280f0442c15255004400760007003000a60550400c4045035403001111341522841320525010355170301c04041e000c0c46c01460300041414281748040d007800752024880d0200c075420030014a61a40c040200d030b600c5a054a0322224043d0589048003507403087c08920140d44e800c00e80041800c90301c59005050054001d203035481c0c448824002c0c030545018019005c041c01c0f66641c1852403060b41e180c2002d030b005100800260701c40700710b641c81c244070160035041914801d41c0440d07204001841c0492a1080c80c000b1100c80340e000b42d20001c85 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 689763201 1250 689761951 689761957
    0x90412140705030301080303011e0806040b061c0f0b01050103060315050705040b0f04150f122007141b0d03050f13090b01090509010b041205030d060e040c1505 70
    0x200801425500d0001000d0346602038449869010b826207951356515a101940c80d04280120980f412074005800507140d000000801220147c00c05440c0c19511500c0d00101c02d000107000a80020015201840d5050320708061817110344201d1140e0101115803c0a00c0c07202ca050300004c0c18149400001d10125800c2940804005008000801c3c5030b41d802100f00d582d40035980c804461502d02081c118018803044010f04181c596034850150760021950044940c4000d01c0180d5000c00c209030390201d5640c586400c04003281607608804d1036070a03c4038020400640c0b00520036903658500445100e245070741449805402e0050343e05440700780c0c0404000645903ca940300050a1003000900c00800b80c804809031421326040c2c0e00504806a03946000320702030010020030740d00013009448042420b207084070200d41641c90f103800341400c1c06d041640f525242440060141c49510081c403640200030102c1c050180901142c540420030303410545042020050250442c1308980c800b04104444280e0000a03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 689764451 1250 689763201 689763233
    0x10501020703171905040306150e04061a03120c06090607020c010c0f17040815161d0405040c030b090a150b06160b070e1906030b1302071505060904 65
    0x441c18400710603001e200390324407aa0300301d142c0b641d491020a00b1300540040107030040b00d0180d20280040304900b1404040340070280201c02c3e003e866000820b01246940d80155000310748804103800c0070554a001a1802c4150040c07520803210010386540071000501801d9048070642c001131803c1c0c246143c0203900c0369900c062a904019038000b0000922824104041c0c025402008912900d2001213840500e64040c0c022200c082c4145080680b0820410107190b02c0344614010310000c4000038042215030803c480915000515403051402c5140d0f100d105090041e0b1042d140300c24884d1441c9401d42d0032460003840425960000140034001c2001e00020038883d02034100005141c4c900000011242c0c02100711002c14508034410003003c1055408070305005410710b454058406801c50104440e4200e00c4010f0240000c00003410050ba50180d0821209088014250000c0b2140d40032030720f007240c03c60501a0f0350210092010025100148521a0458015203c01c80d281c40c050b00c1d4a201c8041f01c001d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 689765701 1250 689764451 689764463
    0xf03020c0a022e03021306020f060406150b0309010b01031107080409020310090c1d0321090a031407050906010e0607031d131a09040c0e09160305030d14010501020703 73
    0x220303500700c1034072107001e207603410a402003e4450890420028002d4102c0c0c122025488081900880e8460002034102040740311b40009101c0d80e0758a0342c1e08070180000c2070482d4820f0341190381c0440c03520000784c09144544251000080c501c25030100050a41c1c0075203005001a1100b00000404110004211019114034903005030342d0340c91b012001d00000080c0d902000303c00385002400e0601a03808540e10301d041004481c045030700103242c01010b44a4031458042c00300510f11081142ca5a120381c0003410004070002c0c04100d0041e40c03a10b80030502d610b0b0310448203043e00410380520061408075400c54000400b803800d511210035401c00b1503100c0c0b094050140500c0352000b0340e440d884101e01c0100510381c40240822070301840c000402c20240c84c070400c0203809404020380d80583c0d41002c910581c072a9801c9040514032610b4aa552841468090b0220400d0f02807585102c0c0403811f082d0302040150300c558015a0380348400c4e60075034111000c0d8226460f02d105001d004205aa034009000d8099a81200c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 689766951 1250 689765701 689765719
    0x100509030304030c110402031504140606070312180b010f0b030714130b0f0d0f0b010207030b070507020301021201050f010f02030a0f050d0c09081e06072105160f03020c0a02 76
    0x4181003039100170310740d05241c2c010b00020400c800c42000501550768014103940a002250710043e10742c004000c02c60340326802140c2804030300c0110340724850800c901500f01c180040d0442c009900361155401901c826a0003201c040d0040115082c0403039004020315448540505500740a54010002021100c00307403101c01010550310b10b2804824070720b4008016107000c80daa01c80041100020b0b0740c11620031b1079003051400100c0308221109010b05031001d00140d015007500d80c00c560324045098005401a02040130611440c0c006840901c010601d01d5000100021550f24000820060f0488903400d241000b44a1104140d41da070000241c44d03a1072410305003d0402003055008481b24016003500c810f1742400d241003400000c2c1c10003201b00548504030155003034540700c400303040d2040040d08c6000d6200c0d440040080d0584d482440e0038007000d80d00405110758080001c4142c011355000341c0f0200303801c2d03131495a440d0b0b040360024040c0c0c521440d641000d508120780302440d6602d03084601400381c0102084 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 689768201 1250 689766951 689766953
    0x30206030711100e1513080705150c040e0c0723030d0609090203060601050c3a020606030c040c05090d051c02010f1d0d031d0703080c100509030304030c 67
    0xe60014100820941c00b00c0c2c10003088001e0943c0900310840084186000f0b80390034500c0d5a171840b000c01e00c24a031035032000701004003c2d03481030050b50042c0825280c3c0c0c081e40010440c481c91014001e801120000445600d172400c2140c00c8080d134a01414a041748042040f42c9000121040d045c00c9016891046024940030401c4c680c83c190b05c00c004642081d0741c50310ba00800c0108c40c0b6846224403c0c001d900703c0d41260b036034a0041da0580700302c00508840d50702101071480c6150140701e0503101d600c0c400401d40003100e150f6001890f215008a481c40240e04402c040041d5420200300521141302c0c1110203100071111000d016001d4455001d07076900928031305c140780e420300c4001c1110340c54440710861614003840b0700e208000d00a220884124082c5820020202d02052204e40d00c01034480840700a041551880b140c16401031694001032102c1140c2556004110b20052002500941c010200507658208628040d1f04196010f0a14a003807450329003402400040042a65800359050a01d000ca040003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 689769451 1250 689768201 689768207
    0x110d0e010905120601090b03031e0a051201090515010e0f041802090f01170a08030703200a05070b093c10061809030e13020909070c030801090501030c0302060307 71
    0x2003030b00400d800810703481044101110015105049801c00d10042150b44402000c25450388500300d8a541500d0003a00304100e4200d44a008200c2e00b40103040c41807605c0c0403440b0120700170f00264040060541d070b88081050804100e0343c2c1c1070342d0400910f4036480c0c00182c5000034000700074550b2402c0c0140e5440c1c248070104d1910050012600d6001070011100e46040701d11820448003d002d4480300f0303c00c42c500e90313018030380000e29528090b03071029105003140d0301c660085009010000002102c0301c00354020103241910701c4020000080b4560718941c2c2c581d100e09001500e03071405407000d0519401340e54800f0715800403140d0451242c680002d8040f1078140d09202080c44440e428814465004100303d4079040605588000c088404620110807440380400103101120115000640441c19541c07880001f440c0ca09488481e50403000d10050400500078041400c840044450101081c024030035001896001076601d401040410001c0c400d943c110b55601404030968400240118800310128040b180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 689770701 1250 689769451 689769467
    0x3061a0a020109061103090f0604030212180d08031501050403020901030303020c0a121e0c0515060109090f0f050906091f06150810080d08060d030302040308030106050c010c110d0e01 80
    0x242043c4144807190b481d11417400c06070320640c1c43e8291482514502e110407200414828815500354004d0440c41100d89150b88080d44944001020034a0041e81042583d03155941198814024031002da00d91405019800300342d01c40103000c4d814414144400c00040e40c600349961705495046c035000d0f03110001040c40038980b00c0e082d10b00070000c00454107075450842e881052124144111706c1c81c0007032107400003800c0c0c0d020070f400840507005800500c82c0c6824410300a210981121043c5005640305035284143d0007201c1268017498400d0340c46003c040b12100460260b140c002c404034000d40a04e042c1400301035503500142e404c00d5200c1c031492981074450541540300c14008c00c0ca80d0303180700e94041d0704400100540b400b201c0000500281c03074004190310318000740780c090543c1e1a407a283c1454a0721010016500b40c528811010180c080101000140c1a04003070750081007a42c4600d0348a264000e951400d60704002004002c120707103400203050745940054900d8840800741450303450b4042820040b60041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 689771951 1250 689770701 689770703
    0x307060f0b18040201090605071a04020109080d050306100203190807030b060723010203160503040f240b101b02030a0b011202040b090907270513050d03061a0a020109 73
    0x812101003102e01441c156401485103100b40c3e00d941d0080d455407000e4800d401343c00400741c400004652862802002140941c0e0454014108280056514000203282c601740016003000900b010081c4202e0303003026400480e000728a4009181400d240c581280711034070200303184c0c1c000c10420744041031000b4029030040480b0b18003c3c0c03100351b40d076000d0300703240603075060001c030302441c003440d51103107004401c018400d0702d01400a4074252559600780340c40c110b40942015109a4011381450000400146c006180c1044414908001107001200240d190300b1502464840b0307005161341e0010031181a80250880c90320300d01070814030800351603400401e10f41000f00364000c0c02d4040321000461a88482c1650030401442101c090140e010f80c441805080241516280305a900001044c00880404002d601f60b07004c9101c0305a800c209510f410318141c440075601c40030305007422400d81e02805000d11900350500c845040511400d4641404165211050141e52800143c0415030071f00700e5100390003800f101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 689773201 1250 689771951 689771959
    0xa050c01060632090103020d0209090115110607080a111902100b04021c0507020f0d0f0311090a0302061e03041b06080108120702010c120201090b0112050307060f0b 72
    0x24030344480300500700c40a40381d6855100f880003030f60030300404480080580403c806001c0c00d400c0c02190300054010790403951003080740039020720003001030b502c820100740d0080c224000c5a014420364810041c10220001d804a00260000c1d0100200141c0021074503411041c898800550a40700c00c201551078001c0c103001524900f064040202da10f5030010315a402903c40e0841000000f80d840d0420049110f08440025051124406441036241d41d60042e640520680140d0707050010030a29030f0700f4240c0b00403400c00841c00700e020501082c0da140c8507d40d0a0320880050600d0800400001411014035200c000e106d0080041c0290109070410040c0028000c00d01000b500c0b81000d14007001c0c121710608503681301e4a0018000a015031040d101141240e01300005440800c0140710030654a5108102c16410311012031a52400212900e150384c0400c07410703500000b4100c4481c41c060300000d4040e4000700210340080014000b0490200c21a44050360181000070802e121941d408041c4c0b80030840a580 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 689774451 1250 689773201 689773211
    0x51006030c090e0c0417120414151308060604020a0804080d06080a080a021e06040b040507170a110901050109030f06021201090f06090e0c010518040e0d080c030403050d0506041e06031707170a050c01 87
    0x505044d01109005442165040e10303c0c650f101013f000480c003c5400603030015080c103000c03502041e5100000e0001210a1801041c440e031260351441c64491400011600e00d44002200304046a05000e0300e11103480401040602c0c0020065850340ca840251002d842e110101c030210381000070070000c110082c00e120f4072054496141e0710946844105e007802c10366a002c0790240303038105880d00e1444030303040c0e0300d0586034028050f0075a16032407001810380740b040340d40660030884900d00700140c0898030300811a82d40049054140030000e04155030090b4400522582054054440c10700045038517007600c0e0b001c0c0303889030b21548009101002c11601790545a006458007103c426104e038003240c00c1418554540715107101da241c03103000e036181e88000c84010700002c505000e0140a10314681010b03801c0600100086080103000c08144100b100040c00382a1459031381c08100100024882400391501052031150304100d40c3c0d45a03242050308540032080950350020303020744118002e20075140c240c500c040c02001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 689775701 1250 689774451 689774467
    0x30e0d12020705030c240a0903020301020304150e060c0901050a0e090403020304170619090302010b041109030f0c06162d0b0a051006030c090e0c041712041415 70
    0xd20b03920703503000d02070290059046508117420030f140d10407000484a100c42d40006450280351216812421007802002900d000c0000566824005940680e01402074408411500030030b50b412100f03501e6030110705801c0842000038580e801800d4441030b040c282030290355240300d030038110b4400012085050f800600d046c00c1c00207055000001d401605c0302c2a070349a155038003070709049a40c1e4800320b03079071494200c1c07441d09126021440d411440c1058443d000100340a44404005002e540702002c0300030b42d00c0310119200c60149400c00c00c80310048590400303080100e5501340407031010f02c03070b0100b0307004030240c03400c11030f4200425a8042d203c03101100c0c40c280d0b807000d144045110460201001903a20b1600c01d400f20b40da0100074400c1c18091075070a15800c6420346071980035009800e802c0000c43c14460340314000940c031140300342a00d108140c0c01307003850740e16418142d1248907070102c0414100642e1080290b00400e500d01012a42603904d110f00262a20180ca0001003074502c0851285411060102d500e071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 689776951 1250 689775701 689775703
    0x603070c0b010b0c370c03050d0c03020d0c030c0b0c070f0503030a0f060b090103200a120e0325111002010203040203061b07060b04090c06050a0207091404030e0d1202 73
    0x40710030800d10084d40d00d110514a242d40c00320345c290411050380b940700114000080800c8000b074a100780b1400c142201d2640d00c1d00c031142003440ca1030507080070440c1c0d071100c0010141e05010102842c0140c0c10003488842c2da80d100181381200c8142e00401146060010503401007601c070541e040d460784074142c59910070152a050f42c503a003051f80c1d003100c807a09001e100513045e15107010b21003d940340c2c1c02525080844a0004501030800307480c014003503407041201c4640c4c0319042030003001840210380307038103150311950b0005c541143d085102100c0140c005024005903144c1609170541d0f20340d03484032407100c10340c02418070b80c0f103000c49000099404050765003429030164041d0041e520890080b01a1003260355459422103c500405100c070500c41400c1005100141040d4003c01d072021002e0800070700703640d00c0e0741c03828109a220b0300f080c3d002c2140418a13400c01c1e5810007243e006805070203801d00481c00360b200b03004035124000c0d000906201c2c00651030354a6440d02c07401030510a0f0407a41d004409005c0201c0a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 689778201 1250 689776951 689776957
    0x7020319030c0b06030a080307180306050711060a0b0102060403050d110327010b1315050306010b1c02090d0b0402030c04050f1009090b010509060121140a0c09050603070c0b010b 78
    0x843c0d11901110001e2804c1c40c0c045035080d5000d40003454180356a032100012102d0112074500b000005101240100c0403c41c90300c140c900c1085c0e6074440c0c0c0c07139410022044a1601800070210f030308140c05d180116106d66404540103030410780c1402c0091f00c4140411000000c0c00418040003911480403040119886003401ca04003e10780004c28034480303903240f00a0300c1c20390300b4212603030350080300c20900c41ea07034110f80c0e5001400c038000c009035003601c5a488500080c1001c1c0c00ba80248480c0c2c0c40820b6034517a8043c1d0020110280312118011450071000002040c001815941f010300b50708010300004065440901580c00000d4004001300640d1900750603441c80a102503444182258101d42c0200b05901e683c0b060030040ca401c41d02e13024060317280404114188070000c0c4018100184000000307820b400341c90841c00d40c203115200c040b40800c50301c8a408901d4500401640229040108405003580c0081c00700f07055690590703030207940c0e603180a410f91b60301c014898003d06191102000040c0441c0b90070107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 689779451 1250 689778201 689778203
    0xb031b130c020a0312141803090a03050607030606020a3c0303091104060b0f0c070e0c030a051608310302160506031012030c0606090b0f060c1207020319030c 69
    0x810700d007401c82810340400ca82d0154101b48842e00c403400840d149400d14001208180e483c035040780d140caa02003010401010451740b0441d0300b07610000511002d141c00d400f03948040e200f01c5c801441904203544910f03050041c0401c1c00c503035481e1040c0d401c00c0e1070018806903081c1c014004001c2d0503540007a01c2d00400400004a094500003000d81d90b0440300c2c9018001d0380210741c40c0f559010b05201c17440030000c5684c1d010b85503000c1148903400001419034900300041348541200040700f6120300e00400c8010688800030f03d5103002c01d1451100f0482142c0201203142c12200a21f418910b812004641003052070200d141c80b5000c010003610300c2c013050703400a01010318104038000244e2032542d50084c8980d030300042d00c035038060401a85040c01311140d5698a030030158000c0c680002c01020390b859081c2241c00d036070042204651240303a000700c1070a200e414072800c0681503c010740740002800800da1240404140505e03c90000a022020756400b080603d039800c8025030a900708116a2078003400c0c0c40c25000b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 689780701 1250 689779451 689779457
    0xf0409080d1506120f0b3111121503070b040f0f1a0705160f03060b0f1f02100501080f0610060f0c0201110f01020c0f010b031b130c020a03 61
    0x28100340c61a0060014201c40c07560302c13481d0602e1080c1100304042d045140c184809140e44003519183e503543c505542029200c0c1c0f481850076285044403244840c04090414074a03d800c10020317200702d40300350049500c224207041c405610b94a802403405a0050f4040e4055498840c400300821665000c5009008803181441c5040f00a40e5540c00000d0100d201d200f05411703140e000e0444440d420381040280040c07446107041c1c546040b2039604800500015411440e1820040c1c4c100340100441e51145044404046428004104640c00042c503c00c3e208200e10550440b5120b510b40400c0c02005081c45189614500b4001c40d83c5681d44603a40d0300f000002e561140c450400454107001600e032180d41030340d40c1c42e612180603560045065800d1140c0810483c104070140c00e158a03060f409020307018041d510000003603a5403080c0c164592402840c1480030620b03916005411080d5640082e4403840c00d00069041e80e03100140c50f00180c134103030f403600400348418200300c10102c1c110b41c0466015a0103200f62 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 689781951 1250 689780701 689780711
    0x1b010f14010e06010f051207120b010315180204030b1801180b0c1e0d0606090f051305040501090506010e1905240a1208040e0109020a1d0f0409080d 65
    0x55069200400c2846484520120070000c1000755101d400c1800740546035003891840c10f4040c0301219590701c011a441000640c2154102110b60b03a1401520b00103070b400d180c2404005a03140d009903100c2501c1c440e01c01c0d0204014040306044400d030701035600554000e090b03180745243c095500034405040d291010102c0d4a048040c48027111021703015070b901d6820001450b80380d0360b04240010103074800600c07a01040c08402445400307800c0c44000340f0424003202004140703185020405060900c07950040c1003c010702030002c4c0400d0b115404102030480c50080b001ca09603c9506002d4010703c01590301400e0760061a0001c01c0b80c02004154900940398800030303580c401a6040c8500c22104260750458006445000b407108005410000e075191540045c1080c81580d541e2845161050307461408443c084d6010408101c03916843e468507006082100d015490800016001040d00029614001301401c1080c075502e1141c40d28400300110b140046e208110003c014180341105400c01d540c1c0d525154181 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 689783201 1250 689781951 689781971
    0x80a0c03060b121015030b04060207060e210d0b06070b0f0105010e091302011806090f080f070b030c0f070309050f0d030e060a021c0e011704080403060b061b010f 71
    0x30120a00d01c00d072000002d044041c0380381c0035040241000300006040c05c2c082050100c041040700002c0c0303000c0c910603040103a5506a5107045401c1c0d8120100401813a0080c203005900c024100003a4004084808a15980d03020540e000c0e00080c0741001105030041d5011a030502002554a030301805000f014818a8540ea41c031f03001100c82c45820411160815070800218468008540f94140c51900c141081d00306402002240111201c1075407003a000100d4440003000840e10090540c4068803406014286c1f02240c2c42980e5655002481040391040000001414001c0001c00b512440c0c80c0c0072100310755403c1d5a083c010076406117400b030203100e804120302c0d4144030701d410b030001202180d0646900080c1d040e0138041040c90b400840d0543c3c09d502401c41e5103000f0700113610129001040c5600d0b0818100c0e44a0f0004000c410259068814021800184404901035030151400c40c3c0d400180490f0061400300859120300442d03061224040048114648410042d08400741400503003c04100d14421 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 689784451 1250 689783201 689783209
    0xb0a08010b0105040320130506120f060408031b040801060303030605010806030c010819050f040b0106020a03020c09060d082a010b0f04020a0e0306161403010e1807080a0c03060b 78
    0x1040701400f08604100c1080010795140e100050541480d80180541c200c2c2c10110f500100b2139002c42c01d0055580c010810309191200b00000e40780307941c3c8000e280f415020300c101d035034aa00140c000307070001c0800300016010200c119901a00100c5042680303848a5035504e046003c1d01e554001203010a00741140030441754401c50019206070070090007003401c003840344019180403a029200200d995415044003092400a018280c05800c0314000080585010f081c0344080c0e00b0b042c0c01100841d0840a01d01000c2640003d82c16800c81c02190181e0f071940b503075000100d80c1304080d1001410030401080444225000c0f45d1844080780603104105e05c0340c0e904102e071908a80180307896981c800000d110410050400f079024059030542424003d0300c803d01e0700c0004c0c0c81c00c00b08803450240c400e501c2c145841d03181d0340700c0040c200a44d00007214034115418100310250780300005298103880b00d07108028940e20b80c010001b41004028400035111510032a0910104082e09030005480440c100f0480d0499810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 689785701 1250 689784451 689784461
    0x11030c0a091a1c021003021b03070b0f0c0301060e18010b0a081f090f0f05040b0a110405011e02010f0203010609051f05030612010e120c0d030504081b030c07090b0a0801 74
    0x7403150b004429049a950030040031801c0301c817001e01010760900c030850a0080222000d04900c10020013107480302c6039131034806017103e00203280a003424003080c02c4c00610880c103001d482c1035403410300703190100649440108000d492002e2605e00c16011400000544942c00c2004102030701c425a2506d819994800794400c446261080703000c0c844070800810422042144c1c0540b40c020300c0c102c00414241e071100381d8181505c1041d2070640c6c417188070006000d100d01030341c03240740119040040000d040c14078210000e040c01c09020018030107080280340e0b2490241c403e42c032010141c100000e04540702c2d6160b80d0000d261041078061326001e02c00102d03500400744400d09454031301c200c4030303982d9078a150384030020f1259000c16610329050941d21110601c00ca65420f100c040248420080c15a40fa01016500240351820350103403402458074240911010654103802ca8000110010051907a80c4000000d9491403142285e005142c0c0640000840d000050350809545944c045074098031854441c450135003224 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 689786951 1250 689785701 689785729
    0x24020d1404030216061e21050f010e06150a03020d09030e180919030219050c0f0405041a18061317030c160201090504050f0405010617060411030c0a091a 67
    0x8159a0300c01103201140c6c00c022030054002c0c901040302d2100c8004e401e08504245c01d21420390354490003001a43c141044110313004140c0403050f07070300e1401d14001080b154119000790042c4c0c0b51000884100b081d000b034044400c244103060f1b04110007111801e0040528800208080c0b04030561003501c000e83c1c10b209080e9004905800182176076500700485882046050301c0e088041d40205410341281400c03010300e9180f59406040980100314805041001301c0136000b40862046113080203110124100315035114056840c002c1c030400b030342c441030650f4144224032021248544903940401100010a2811b0710500344241c001020a14000019041d10f0200715101c0815030710034400c02d4007890710442d0f84040d150040c1003a61010752240046416110101c0c3d04980121654052204100b024402c92004110080b002d811181e190400152500c3c1c000e4000b82020014010401c050b6901740034124405800401001c0c1c0650f035407c1e881c0191400b800350080c2c0302484d0700c080035070b400e20b2140700781d01c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 689788201 1250 689786951 689786957
    0x40605060a17030306100207050603070503091c0815040b040c0e0f0d1703190c030213080102040501050d11040504051602010b0a05060a0807090503010f02071e24020d140403021606 79
    0x183d61708820300111012800c1500c0031071140e0755000401e51200c00c0150300540c03603a172302d45681e071502c40740c528900005000360309035404608641042d056804440c40744c01150702081d9840d02c144100c00940030f41380ca002ca15074450b2425100c90000d5401610400300c841055034503100c40c034615010803981c81120303640030785400c24a00344100310b100c0d031100465000c402c06402824a5050805000440b040000c903000803a40c00554a0403004840315148000c01d8140025440d1605003000200140240403800c6151611404441490610a01a074001d044094010001840d205054040b040c0125000700702651070100038859609100e10702000751400981218038091001200302c2d1550030090188003080504817000c607480d40d00703004000401c00e01d000050f0b1900454204990340010081d0002e000440d500e20402c0013034071182c4002c0da030004410080240b05041d504807000391144181c2210000d141c2f009405601c2e5034001001d000724025400c4400c461130300d25061620041d41d0040d05e000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 689789451 1250 689788201 689788207
    0x120301051f030f0219080907060e04020c012003180109170a0e100806100305010e06060906040b03010609170c0f120a05060c0a0e091905070c0209040605060a1703 71
    0xa4040354085034844450070b480c0c0000e5603a107980d28001240c110302c1518000f8003440d6161008a9840103070150000030180141c2070303c034548140903008a407081080c80c02560040342c0f41030505029072180151840c0764880d00c0303000340303502e44070120b692003203401001e046640c041c40141b2020511442c0081e660110104a40c071003414007405403a0010003c003020010001c031490215180c0c401125904101625181207a05101081001d4005102d01110415140100401a0400c501311aa402000c00c0e1450340c1e6a001c8040480d040e8404c940010303840e04400800051501d900c1080141103507003100300c0c40707900414590f0b02900d07004440340c0b41d544102c50904076000d40c83c00741d03074400031100091704455070400319654003404d00104450340c840c400c101103129102980c01102841c2c9600c000c070b4040d592481c10030648030030b1090311340807402429900c10004000070f01540e03100c84000d400801044070f500e0586070900140104580c698080d0310080780001d080b60103c00b00c0d1790481d0840000d141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 689790701 1250 689789451 689789479
    0x7030504180e0313090e0f06040b10032f0d020904060f02040918060c030606020d080c0f0d09050f0c0a05040b0a0b1c24152d0212030105 60
    0x105400c040749030740c40d8503960302d242403030b940002c02c01040303081501c4201038410707468006558202d0302c400d041c1010139080400c00007110440481c196600a50001210040c1c1c0c0b181a44580143d1036504010091150300c1100200120f450095420f880c00384201c4d095540c96003800d00c81c0d9140044402500014032101003800034890307402c5054034903e40d550040c10507940b2014002079408880788544010401c0400b8814072001c2e0003440f90901040c142800140d143c0240250781b4084940c2010805c81c600c800300d4103988441c000c554000c082010119101d0411200000042c40c0c90304044605e0321a09070740c0350140b0300104130300c0784200c1c0045c03c071000203141c0310900014000748030104d0341c00305005001181c1d40d0030040203050b5500300325040003c3d01200035480000ca9288035420380e080d5145074541212902070980150598500c20405400300303c0c6508107884c1c41d4181c0480c286004002030302c0001c1e440c0c04c0043c0e0b02091a21360300310340c050034451401b410300784028061642c1042c0601c000300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 689791951 1250 689790701 689790719
    0x12090f2103072d210203010807051002030d060f0504051501020c060c0a0b040609021306051f11102405150a051b0705040b03031207030e0a020d0803160507030504 71
    0xc655240b02d0402142d12008890b560b0074400f481000004618031408a814151240091140c0e4481d01d407011807855042041c42c80c3d0315940707032052074415540e84c0d0920035003510900c251000c00310168002e104942e1030b410000710b1015180581c5008600d400700140c3e1004000c8a00c5c400c02c14180c000c4d00c600c002c03040c00e00529500c1074140441c0f9108040344c031000103031080a094807540c003c0c1400120f6244c14810040e01c0050213010b5401c8a0504006000d15036628040400d0700e80c40c078038640741010036050180c5a00c0c1d003c880390700d29030042e007811616500c6141c002c014080050501d080d03500300c3c4c40c074075440e040e201e80c010290808a00845498a00c02201c02440314600c0340c1052800c11041c020f040140c0d100d00d9000c0c04154111404c204507a051a000760b4407141e03001c030051400c11103015209800170900600c0d9508150300d070030889841e52001e00460102580141210651603400c1c20107091aa005440260050340d020000c07110703641c8240c051380c1c50190f240c1d44035443c003072a0070550 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 689793201 1250 689791951 689791967
    0x32d11010924140c0a14070b13020d020303120906100612021e04030326010b07020d080c12030f06010906020601091a0a03060e010606180512010212090f210307 70
    0x520071582d554140c0c20f541840750740c80b81c4590a90303419140e4405168070b00900c0000c8450789940620802d000c40c070000390329000e4aa50102c50900d003001d40180d20300009650108144010790107010000b40300d07458400b0741d20242d124807030f10800c45020f40c44070700b141010003002d0700c1850006038259215039a00d802c83e8004202c040704000c10000d8580805022403030366807060f482200071418140355081c4001c0c9200181d8100072603415004200d624000c5400c099200390b070002845212411030710420811410260340a40045008648000910400485560340240c8900301c070160b0307410004803250311880900b81540c0b115409000e1992800c80840c01401c802492001c2020100750002240d880702c100340c00085010b08004698803940403001400c45002d90403200801541c00040041e141c41c4048030740031030340d0039192900702e1403c4495950080c020025900c0f407220444080c020b8242002924040d031001100995620180d4943c0141c200300c141242000501c0c01440081d00303440c010150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 689794451 1250 689793201 689793263
    0x4080d051b0d020304150e070e0703020a09170709061805010e13121b030503040303051302030d050c030409060b0a0207151d06070210110d14030402060304032d110109 73
    0xd00c1d0030b00c91007614100540707d503c08801e9a40c0e01c4080308100103440700c03903041d070400342908045251034242ca40081c0701e2500c6004008112003030b4444003130340c0d24080040c48002e203111341042224545031003404030a104401c010200080c02c00c8000724000790410560780c024120b0000b107000103099540d4400c0300402031541c00c4284601c8401c00c50341c00c105915000c803600d06c650343d01c940c3c9280524014040300c0000d03041c05c081500c0c0400c00c800584002074082d40e00303811400c0c459125007a04d42141e2441c455600600d1001e410258005140080300e0080c0440c20700070703026128101e450f9844000050801302c0350a00240040c40083c200c0d803481004980454406089185001c00c1c40c3c000c101019400884400001c0e014071400d81022400c0c0031150383c0c07207664a8140c222081001071403145000143c00644a2507000001c2810180270303803040d0800581d9060300b203241000d10344290610448000445020440f003d44a4400b10303410700c40d404050b86d1007074076144030b002e890b445132103525840e0034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 689795701 1250 689794451 689794463
    0x606041113050f030a06060902190201090327090e21120103121403091e160e060109180507030b040522020f120a2a2106020304080d051b0d020304 64
    0x205e0383c020030f007a8001c03032028004441e00981d80e01104801036440c014043c502c0001c6908d0a01001c1c002640007203030500354074847e03c2d11a00d071010707401462014021640804800c43c0b900c400c6010780d100102e000c00d43c90030500c0e142c0d19201140e010450031031281c0b080d0351850344507c0c001400003800e00c6a1340080f080603441d100d16510005500b1710344591003520fa04003694041c610807001c800d01d502c030710641d44200d02c0140841c1d03910807144c510310810500910341c1d040c1516001500b664856000e01c07005048000f80c80307070080750b01b01c1850010501521072600090420031001c0c05400d00740219401100c15030401440045220030110080b04c07221400c991201c800a00c2034115910000c1091103541083d000d130180515524000e144040750803a81c0900c5000c42144800006844000008070740d154541c07000f1043d803070035030588240c80c0c5900c02000b1034408010f00c000e04c4949800b408880036031600030055502c640c0d00b4161440d05044110b921b07241c003000428000411231300a1904941303e45 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 689796951 1250 689795701 689795713
    0x39010b1f0e040c08060a05040e0d050d1410030c060c020f0f18090d09080a1a0405030705030d1a01020f030a030209060d0c0329091315050106020606041113050f03 71
    0x405844912030124001130007601170080900d0300d5444000100303c100c804210181c0c462000725201e69405400e5014000d0106240054040907046104801d031821f08016031031801c0c0002c030101180b81d02054030621850100464664091042980c0d080e8000301016803d50b041c904001c0f80141d510312054002078601c0400c4d50019000401e54050454840a000c442030700c1d00009001101640c80034141d54080e21003000420602003c07056a1004458103550030b58a41c14201d00e90712581e8002040c40c1310006130320510700c02c00e6000001e86101190906007160f0640d0049a41d203074074031452500341d0010812454820f000364010031207890041c00e0740382012881c1d00c00030100e5600325034141c0440e4444150051001c181d00f80c210500554a01c411200a989008544c204800a0100300700b070a0384166042480342110000400840a00c0144000c3d0f840d014001e44905041d03900740e0085041c01000b4654062000550b41c04866106101e504146804104890100c5070790119806000c0e035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 689798201 1250 689796951 689796977
    0xc02240115030b040525170a020901140d0b040b030610061d0316091404050303040605130b090c0a0609030b0a050408070c0312080114060a110339010b1f 67
    0x1500841e4031400f00386c0c50740c0d4a160091884102d1490000001070100690380c420f000030742c0214403495030050410080161685200c40040e1950042056199600000820310602507480e5801405404209072000d00155900c01c0c01e0568400081c1d0b1040311820b800e50b024841703188602040c00500e060500300b0404448440007090400c40c00440340c013000c15208605011200f07050152000f00c070006041c2000301d00c0d1913120b480d01e80c000500000e0200d40c85070080782c0140880c081d00006c80760080c43d000400d040ca14241d581c1d80711039540301d0b4043d0800e140b00046940c080c4804c801180d403c90700894103a600c1454083c004e1600030000c0b15643c1c4140120070204051122181c0a94420f0305050381c0d000d0b180d4070242c130700700059001d440d44007407461481e1010b44440701644c85401031030400d02da0a5544a80b0241580248000700f00c06600705e41d609444c0e201425103558071983d12821511141245ca42000e00b0780f0305820901c3d800207244010401c0c483c0174001040380344201132810395001620 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 689799451 1250 689798201 689798209
    0x60b1003180b1f060903050c0609060a110325050c011b060513052e020f040302041d160513050103120c060f020f030402030c04050403121503050106090c02240115030b 73
    0x135082240051210070007030080290404c550040440111030072420841c28100154043c82014425400c002d910989213070020805c00c103448040b09440b0740c001c00c111003041e03540159a50000c00b51494450001d01c0311465014015859181c030000846c03400d9540c10303403940d4000e40030107402901ca5003030540301706002c60030a0141445000480e4008844021028018440d003a12007a0031106103104204101e9084a2001141d08695060390040751056440c1211100c80a5410845460b4003441e41e00c0d0625407401000c080c1500c00888105440c01d26003800d41c6e040b00c40c02d020090040602d200301103240c0b40201c8041c2400d6100b054007084624110429130140c0e0012840d1041100000c02404114a030501c500141050203880420a507c0c041c3c034000c150f024000040d403205999070300c000f201c505054105002454015000b800380c25903030016200241041841c000040c090300f0303000341101c2410f00034540c3c40807000720352000ea80d082100d460b0402d0a490304400074150717180190703441611 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 689800701 1250 689799451 689799511
    0x22090507051207080706110304180209100801090f090203030405060f13080a1703090705060f0d0e060708061005070b1003021206010608090d141b0a060b1003180b 71
    0x1082c02c0a0800140b03800f5100d4900b00207500040e09200c1400c00c031880a60002094400302d902d281e003589251481c51300e400c0d00034400c07030201c02e8000c1051803110003c10b400c0758030241200d075003c108100c2d80800a0305041111580380d0000d41c1501700f0030041042c2d1074200046e001203101e10001524050010411480342070065201c4001c5412001125080c0074180100b2a035021501d04a5891031030071041c4191945403600900b0710403900483c601e5986c000500540705a110306050412000816054207a66440110f07201c034001036902e400540035080c5040400301082c015100c1c1400c0840300d5448070300c2040d0080001400d4204148000007594680c2200400c01d44007001030802541002c0c0b00402444008018644980c042c4c0b000b403d840c0c0e4498090301d20040d18100403601c0b501010240003d1900d0b00c1c0c0420624801d2240e86401d000e000d50240c0040d12044860885003000c258050303068030341040501100305441c140c2c08020074503403664141c5c030a443c2680228102c400c04a4110010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 689801951 1250 689800701 689800729
    0x50711061216030b090606190203040906180515030a3804140c0f060c10020301180c1e110c10030c0305090601030209040807030e130c0e2209050705 65
    0x440c0b084406040c507003500c1001d09629040d10300c032055107050008200d040c41031520b07500d947e0085a8a04003900c0c82801983c0290172044824044640d035161007035013500403d00e10f43e40c61881d10010072040360158003c012002d1010300a0807507880e4589514400d84404070700c401c49240d02040d011618000101d00d50040292020628518181410043e104040401c00c42d400d50340885442c003502e90f034480601004010171200309a84600c103080440c10900307882501c0c044640080008260502410000031200f172110100300140b6011a0080ba0070f200c0c82c08294412170101c071125060103105031010260444028212540040368501007003101c0b042442882c0044c2d40c8500c0744858560501940307811402000080141e54115000a4000500030b040240107500005d0381c5020075004210754003032214000c10294100400c0e0854501034003481e00c4000006804503a200300518002c17543d82419a400d0320f030403241d503d503c2d03071032001407500d294107550380d206030440021141d40b812a4901e1078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 689803201 1250 689801951 689801971
    0x50d0f090503010903081e0c030a02090609090f1b0f04150224150a03020609060319051e0106110601210f0615060203040806041e020303031e010801060302010507110612 74
    0x61800342000302440ca0250284200c01d00c1c0c00d01031044c140d1148c0b00b42da4000703600b950016628201030300001c5c04d5100342c40f074054011310b60078100a4807150300a4a513126102e00300c0148d800300015980740c041c030300c504000d140c40d03088244824030203032841c009907004000807401101c0070b15460960b400b8013081100e14007050b803143e4404101d00c1008410341d0030001d02050320b01080480c21039002401d14041d60480301d000e003038003000060700042c420040040702040500100500c3c24840d1101000b81d0440155107007045070b400001510314810440340c0d61000207040601466420075138040000c5142109010140700310161100200d4900740719000014421200014000724583e40200020364a501c031b4010342d08140000c104071100410081d41c49507010034164034240c01d400c003038854451002c00281d01880007108124204902440103c3c00f03580c40480c82c0603581e42d032807416090310014000280003a0741408110001010402c030b40c180c52600808560818051022000c0d001d541100c0040d0700b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 689804451 1250 689803201 689803217
    0x3030905150d05150306190e030913020f1309050103020328030c030203041505090a050f21151801050603060907121a040c17010612080a030b0319110d050d0f090503010903 75
    0x801001fa00c545260210b0b0352016605110303103100080c4504142d10448030000e03400250a044442d64102100da0b10300312005a07600294030360704018000c0000340003c070b000f841030304c6c442d00580807411004030f2031018038100030020005940e011510005c1805084066200034800031600d1951050f44890480c12a80c800d40c42d601e03018100078480c28982e00080c0200143d803d010882c2c4c441c003400440d404260407400b0100f003240c2c1c03181440e00842c2c9e185040c0421002040c4090840c550411000341d11038400280007035140c580415031648030aa4083c6440d40c0040d60070495080d440d21203c000a0048010400e03c00c2904035004824004407822140a8408841400035496065020f00e80d0314a080c004c000d200d00303143c40310f4180c0e0035400700545500c0c00424500c56251003904540803d56026003520b09a030014111107140302d880100455024414103562516828000e00546640f50003000a00720401c2500d07094800046080e202d40400c400d10304082444e45003402100c6507036120350b0b56004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 689805701 1250 689804451 689804491
    0xb18041512150c170415110714010b09071101020c01050903070201020f0304180207050118210518041d150709060f090509060d021201020403030905150d05150306 71
    0x288140c1c0c884009842c0c5140540c0c010906a1007907208030312858400b101c5680e61a181040f40d000007001000740c520b1070810300d0b820b0000c140c0401400003244a407500300740b60030000d0380084c241ca08010360507170001c1c900d0002900252081440801603a040d00005280c1414683c0007400e40e00300b12a4800320b9803002500c1e80071540d04000803024010001c01840c10302e4104410541003101071807a20180d070350040313039482c00c2c0502035104940e090300032281d03100707244181e1400101e829005a00040000000c01f0f907216034a015a040b12002817501e000a2460305050080000408190b4803048641e08182906620258104100b02e140c2c1404002c140c03036450520f07001450406103800000812200984600155801c02403440980780d0850320918140d443c0300c0400c801c5503044101a5000c2c4803d5250400300c00706600400c00e49004e03507594801d550b150300c1803001e024001111007402c648100080b90a005043d80000e422000300c0032900b044840200000380340c04010b951061b0000c030307204030703010f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 689806951 1250 689805701 689805713
    0xe10050405031b01141201030308180d030501030512070305030117010204031403030f01060c08091302130303090e010e040218070306030b0403050d14060a0902090609030f06010810060b18041512 85
    0x5c503040003050045490300308620443e40c074040040c4001001d0204400103e43c682001e10554149028103804441c0e80100345c400c000c01600702880f0650f0a8019000b90b441240c02c410201c5460344d0305078542504d540d107080000e1a507540f1104074422955801d000107c000303080001c3c40103444119030000c541b6418a2141401080011313801a0180100c2d00803600008441405030b80308500100c4401103204a0b01d03d04030061b1103480b091030780d81c070360009001c41003641141a0f241039940000651580d680c9813030040c1100322007a100654003144191600c2208200c1c407001a600445515011803265a40d60381d4540406094804402048002c1010320650b517003440366440600d0903c880c042c450800401080015141c0d0154010301c94000440d6015900c0342000c0305d42c141d40c05401c40b030340e088000c00429210744081c01102c110740101401c60403011803e000305000c1d9240404581d180804401a0131840c0b05e4581c40c003500141c0754146201c003055038107001d1009040c001181c04201145281103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 689808201 1250 689806951 689806967
    0xc17030f041b051c061401062601050306160c02061803061b03132a1707150503060319050c280e06011106040602280e10050405031b01 59
    0x1040c60007042c0c10042607989800d0030305105034028030342c000c0d00110304052001d007004101e401c0c050400302c4000510942c3c480541180d8401e03103004005400030081d050503064000b0710480303034140d000c02c000ca152040c40001101d2000d0300d904085c80010b0035680410603d8200b142c5100200300740e03040041403420113018183c1e01c0265052840c0c03ca000002c1d040499004c040e109030000079100c40d66030200405207112120324031620411121041600e0050520041d0a0141241c2c510b0700f002500e0241100264030401c0d241061981034080410713500840f45a0802071095905101f00e0b00e8112000903e440c0c0c1181c07840c0640c004d84204041c42040c400b0340c402d40d0040030500c81004051200c03512002d1110340950340b07965003001c1e1584600340100d0358074040070358120050199106200406c8155401001e040c0310401c0b000080060200340d02c500d04c072601d000d0002180740b140d003100c46803506410880000815044c103609050300c03100440d1610301d82c00b030503107100f0324400c03200744140d82c0002c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 689809451 1250 689808201 689808233
    0x12180f06040e01180e2e06082b140316120c0c02010e1e040903110f0a05061803030411031e07030b01090204030819030212070c17040609060c17030f04 66
    0xd06c01d0f030b96642e140304a2010042c0c1c00c1d845100e0740480340c00c825101a040307076000340751000440306c94003050032191a225400d1500000310710400c0888001c105d000b406030b841029114a409400c40e03450303048940d90415140c800c8401c00c403030300c5041607551351544901c003204d8245541c0c02e0000c0865100140a107080e4a40c0d0700d00c074240300c0d00010701024410508140700f002c1030f100881c1d03041a6107819100d08400080f052500e02a130310f50303010308001c000b65400c241b40c0030361b041303c1310b176107602060840b189107003015071100790810800a0046541100da00041980150460b00c440d0500090f60350540306e001c002c85840d8102030030800034070080000450160180403011072909180d075036102103500c120a03a407aa5440850408002c01d406036043e40c55207800ca90000d411445e10b003130020714851200c02e0460300501d0400c1444440042101a502078030401d480700c008550134503200b0f803050784140d032040300c1d4081c2611440013400301180c0a94001c070842c0e00d8030005410300307203801c0c40081c0031004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 689810701 1250 689809451 689809453
    0x50a020d030509090a020f0a0c020d060c050d050c03040b0402120a02120f060603010c090519050a090506030d030903080106210609270c0603091e05060912180f06040e01180e 76
    0xc801c0d00d080101c0454230700000c00d003800c0c81602ca451010034032001c480080603248a25102103211b5107504a4000e103110160014104926920102060242d01064501800e01408000000c0050918031b100f0703903100740c000048480d014a11b40c009100c0000340c0c4c6550394a074000300c00300341c0c110004004141e00032504130003e0180c1d9445800081254076603110b400e200d1100160500400030180030408040d01010b0308450000b921100003501038801902c0c5540244158082c03201c03490b01c82d20508200d42d030f1581d42e03081923900e040f07011a000014600040e0411307000002d18140034801d031292030000c1c5113503c0b011400c1d151513941e08491030b01c0c860041d983c03409042c0070718001480c00d40140c020344450f8100050380e0a000d05000402d103054a55116042080000000c1444400290944181659411280c184003010000d0b80b007401140d912085111003081e1140103803503c80400d5407030380300c060580c1d81070aa0710301d074035a95440203a2004080c0074030701c0f9180040c40e00501542c0301e9000144 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 689811951 1250 689810701 689810707
    0x1c060b220506071205040b0c030909010603051302060c010212180105070819150b0a0905090a18150b0303030a1515020d0804080d060602011a10021504050a020d030509090a02 76
    0x490b02c2c80c820850000d016081e03046030460711a0244064034040c2425400c1a078454101090042e9290300c003034101071007185000000941c0368401d0040303a1140d422018110028640313030f070034024075411910010885540910482c955200001c00301842001e09040c202d40880700b0310340720303800c50744054001000c01406008101103190440140c40c0c0801c00c070080000c4100071304426425040d01900054814000000c0341418143c2c402c150100f070310811103500340c041d141c054002e0101c4041c2d261352040440306a0071080459142c0c12545048641408003185c421210000030303045070b01c100c8180110075500d2040e01c820400d0448a84040d104886807200e86aa000c0c0000c1c4d6252520011001001001c07000142001910002d4400007010140e09120441e1107403000303400b074200c05501917040b250310450760b8100d00e00304283e0400d00b004c1c0d801620b1044402040500200c000134130540b12403103003000d0000140c40e05501c03d05414040d41d20692a900d041301001042080a4140c11b003c80c018 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 689813201 1250 689811951 689811959
    0x602070b130314070501060f0b1207030203061503040c0302060403050a0b0703050c04051c02030d02030c0f0325030e06120105010305181e0f12070c0909050a081c060b22 74
    0x481000d052854500141d5500e074042171134100d0160403da00000a10a030b028000100c4401c1d4a002d02808ca10300c6800041c070355242d410031400c80c00102d038000d0303114851201d1f800302d07090701d000150740080c0030b20503008495480ba0081042c0e0390081d0b004450560000d00114144143c03180c50700e400c02410300e0184040d04103401189400c1c0598001e143c440e50410316101031205022803440a41079010b000d0310000d50140b80043e441c2d0b0401d42d40180107014002a80c202180080102e50a40c90407a04120034007011600b07990500030091402c40038408000380d000d01503035403100540403100703404001d0003c40d8100320005055400c06040000c0d1910080b10b0850040000300e018420180c01c0c2e41750f4050191358407170251500c00400b11070100c1d030046108014450744810020442a400b440c0c1355004580d8800146048400040d009045500300d00b0f00d0343c0000e15194020f201e401e1210541588100302c5414600441d83c1c907901c1398211003000203410421044040d9080807403032840f640300c841d0910f4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 689814451 1250 689813201 689813207
    0x216031104020a02010207050a08031803090d2301180611130b03090c041b020f0d0e0f0a0b0a0314011401090902130e0f0702160501020a0f0c0902070602070b1303 71
    0x400c0e18594030454011400509052003541901d500030781000c211080d6194501702410303a03604c165000c0d00308103d110148080810700208541142c000a1710904001d0903a445090741800e0039414182202400c000d90034014109008461145d0040b14030031502c86180d2401d0300481c2e14003008090449018440120300e582124401c0c01100c0740c85441566a980343c44215007030a0700440660b5000d407030310607070f0650200c51840050384062184c08441ca40c0a0001c0c049586103034004450b800690340031913011860401c0207042008100192011454a4890b01801d181d80c0140c0041e1300000c0d52401010060f1102c1c0380309134014101c01982c1c1d0f00d80707140b01000801c9031043c1c1c004d0400c0240c0028080309264507540242c0c00030245581c840b8104e0400041c184040f134803c1e1031400061141c1c510100100504145080c101c1d44142c00803c0884020381d82c8035030400c1c0e04c000a4aaa40220500103000c040701c1c001020300621641e40165507030814a415062200e02900c07410030301082110500000e60 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 689815701 1250 689814451 689814473
    0x3010605090c210411100909140a0b030307051b2d010201051b0406031a061603180e07080a111801022808030907050607080306011d0310090c080a0c0501021603 70
    0x79920341c81031111b00300040e91401442d40c88020380c5803801d501c107440f1041005a05008070201e0310107001000d5160101903603409140b401a116803c02080801156a10b07824102005c0001c3e00e00d801042003000308440c00078030441040d11350f030f4000070700c040c0c254303828481c031680000b41940b1540c0c80e585000362026103005130b0040d20181640c074458240910088060320700030120080040c2c0d910b00303120090315941c2200820807004a80b0103240c01160710aa09956420344000c81080c602d103643e401c03402c0710030003000b03810f06850030f036500c180340000604c4e60003d200414902c85502e901070550340c0024502000f4030030140703030507684103c040c03480d403c6200c01c80320380350300551041d40325181c0418a504160305988034541c0000c00207500741c04c210755100514803400007626002101929034180442c02d08140203007a41c5600911000a1401c00760f80c403105146004404004843e42ca6080c01c0349041002941135a010319002010091507030704014800260401c0f1000781c2d08249542c0c0c515100b00c1d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 689816951 1250 689815701 689815733
    0x3030504060f050904022d09060a120905060103050d020d0c0c05240301061815020c09100f080a020307170d1b060c0c05010501080a1703040203010605090c2104 70
    0x12200c0c1282d00b90701d200e8400d680050344010011542d5483c0a12901004070803a1242c941c04030911071a49614400401510b01c49140901035602c4c0003900705044400c01820084000c441c0e80d515014804a181003003040c0c044d6100342c000b007180e01c80300d00000e0300c1c040c080403076401003007003050002000501801d065411910113490300b51704014403e105032490f5001110036028071401000001c1c403690301151075540c0b84c1c5940070070b810303843c0c0318800d10340700340c124500d100c002d48e2000c0c40c854a00d040100c034550340000a0551428280c0d00c40300600c01c840145d07802501c90381c0c001d0b51b81406603c0c080c482c1c40c0040140f005110200e114104000c1d0301c4101c41400c460501c85c1d884004400035103040e00801905500c43d204000e40f0341c90354800340019034003940a0700c0b25841c0c01c0c0003044682c00000c030b8240041d0081040400348000380b0004a040e400144201e801d9521103000241035152402158055440c0403031082c0c490440c001130b8518851102d005114174400750082c000801e0340c10460380811 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 689818201 1250 689816951 689816957
    0x6030f18060c2303100b21071407050c040f0603170a23031816091107050a1a070e010c0219170102041a0f040b030a0e060f1f0303050406 60
    0x1212020000340e0322150030020120520910709641d06042a82000a611510307617149000740c420385078400301560f409680700c810801a04888040791141000105a9106043d881c10107002c1120010f082140e801c0794070300302c81590040c03100b5550751415010710200ca002c1d9040810040d41741d62101040da1902040d072840700803000a62500d007910075056110f04541c02800d0148105441400000c80da200715003c20b83c035820f0404103d0101d401180000035920990401c4c03032050309040900d03000306824001d039100790310700300805c6000450038410030302c500327009a5210081e8107140b03d030340c0c0c26448010b251a04000c250350a00d45240e0300401c80c5116140c0503100d5808124246070040c5140308950080001c0300186410800f081d00150010015164441d5030348080f5040f941294a09008450f04a841e841042c407040c49240350f444051135003d00b40c680b0104010303655002d25801c00c603041e541c60810101140030010f030388140800c05000d281d910005420b10902e140c0700208140264010b4400b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 689819451 1250 689818201 689818211
    0x110d0513081902011401120317070e040b03032206081605120c07020909060a0f020c03090409050a0807110925120e0f0a060606111005101e06030f1806 66
    0xb82c41c400d41c441640d20000381074000386940c442e0440781c041b44642c3c00c103e00181500c414140d042da1040e5085026005c59200c030080010320504000240607032811458040c4024442e000ca40c034004c1c03505480b02c0010050203601c550902400608980c80108046962a5902400b0740c01c0c40d070141c01c4801d841c070b03035140c4810545c5848c0c2c1180103171301c240600a50300078041c105100c94564041016400707924400300402c2055005207100c02039020b100b032030718010741080c05080b0307560900d50860100d1b5031048007602c5810b10180d03681d61894000c0b46003903c03045103280c1c0021143c280800490340115007a108a08e1415000c02075014010400300c03071404100e0080d003681411402d540280b00750160f05401d5602c01410f0301c000d241d035014051001c0d60f026040c4540082c04034042c540e20521130f03c290024200d1500d104c441100901805000030b20100c03800d37400001c40d00d0203590541c810480c00d600c51394440385000c40c001c0c1640da0100b41852128034205840d4001c0704111262644c2d180d000c00f011407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 689820701 1250 689819451 689819497
    0x110607031503050102031006081006080f0720030712031803030e0c0a0b03190e0a030c030e040c030f0608060105130f0f02070f03030608070b0301180e01110d051308 72
    0x1c0352030110341c0700418960001c000d020900e00c000303000e0801e40c0c0380c13643c1ea00c0c141e40d10340d8908038000e034a038071a0a020610080c0484c2550760860002584004142800001d4000c4d42c408090410008401078505400c0451503404004100750344400c86a0589014440540f00b03071000c805440d0003807801024540e580c105a0144007040c0041904c0b940020480745000d0368a45129000e940222001820312450000c01d032000d00341407042c03500c84d070003504c000c00a440c2165010b80e40400046019000c1c4544e040c400704880e80c0d20300500d40c00d41d12559001c0b605005406035002a900f035900003001d00d410403030050225445800310190709030074852001c10100c0319542e08500810001c501e00300c000307000041c01c03c1808032041000c2c0b0000d1081d44c00b0410240d84131221134452045000720461018100010410f01400703075501e03407100003034940000d0b422051140113400c41e1901c0d9030f0003054140105284d0001c0e542481990b5010980c1000304520100d0791f0303210720742e40c030a006800b854101224002d507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 689821951 1250 689820701 689820731
    0xb13120302031f1409010b040b040b070606150e121c0f03021204030503010f0807050d0206092206060e0406180213170c0f030d08043306060e0111060703 67
    0x160f4060368001d003100e01c9600c8050152000c400e1a00a602545810000040c1403c81104440884884402481c10581003091000040c0c1c49040709403801c80e219540461085c030411040c3c084ad0151f0b480340c000404014040c000306080b03008648501c0c3c0c00012000043c005880e00b8445101c1491801d81100c448407001940240038540000900d501000108010035801c8401503059460f8550144002070396138805d42d65801c102c0c054650001c0070042c80e0401030608030080c2c8138411b0000d01c03450001c4002c40c0c06d0102814680704070000d19488480c204076282d00084011201c0700b05640a05c03e060900526460711ba00e01e4210984a0f68005417030410120300820b0000900001066443c181c5007035000030b669001c0c50b010480c828011103481200c0d80c5400954000741441a441e64400c603030300c540b18000c01c1c185502150175004080c1071580b13010140aa0800355070003c0c020b000842d00d0802d800145500300802929041c070183e14100c0081d940c3c0019038980c07080d505e14001c203005031003d083c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 689823201 1250 689821951 689821981
    0xf050702090f18150702070e13110409080d05071d03070512010b0306100f0e150d0303060803070c090c08010f0b0d0209060d020d05060603100b21130b1312030203 71
    0x4501e860144c0f103540e8910096107510140581065070894034003a4076078144450584058030400e1b0240b1603118220f0018031715005110510301d00030000102806640c4130910710723a1001f100c1640e00b590391010015115044480b10820015804a00c5164041000030a5071883e643c0a01c9204118a10382005071400035080300c5082400601502e9035420b0140024140940380d010303051403420351140c081f0701400c01e0a0410321800e409a060604101d0700f03000d0000700b445500381a01010b80ba0007001c0fa10b00010801021000d00c1401c00104652a03c0b4010080b9806032452400700000c000042050a42c43c143d0002940c440e81200c030f40c0c4002c9441000020700c180502160024008241004d415078a640a000521030710302e01030000b03039503c00c10400c0c170307101c00c941c4001003145041d418031070200e0b000c0180c21801d182c0d88044041429800044031300c2c41e811030300d2196205040c0881c00403c01c244a0a81e00801180c00d240780309050303503403488844202601c540342019804000100c1e1034101d0700340c1c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 689824451 1250 689823201 689823241
    0x60303070618030f0509090a0c0201091e0c0905151c0c0f08060a0b010f120209040207060c020d030509030702121f0e0d0e0a030b10030503030906070f050702090f 71
    0x10071070b240d8890001e5181c800d842c5016000b2404042c603e81289002d44102e8200c04401040c9407155a509000c40004180c02c1d85e08504541d03940e101800000c005180c42030303031090300e01c5080c20700581f18507201180b281a81c007c020700c40e0401060011814104a207148e0385c003400c45040710141011030300002d010a44400140900c0300701c0171300003042005000c190007643e0045040e103d0540c0c60042007400d9600310a41540044c01099001030828802c441541c48a51050380c05858021018005016a0003541c4103a4407695512428100240c0411030198030300b009040c203018614154110719184d0150072000790240780d41d2800c3e5140c1c80c8080c028041024032891808448030700b50300a00000b0000c0b1081c4208510809561051190240d4820091104018005588075007160382d2204030040c0540001d070b0860b103070344004c40011002d001943c41000d400740141014500324030001e15040fa1100a003003480000c005110141e2a00e422196100740e0100300340300c5989481c040c0100290030352103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 689825701 1250 689824451 689824463
    0x70507140a0f020f190302060a05090303040902040905070f0c080f0c0615040e03120a0b1908030702040b06040e06010c03140409090b010512070603180c15030f0203070f030506030307 80
    0xd1260104410748240800d801d000ba1104e020a052078410700074001c0700d000d1130500424540b4010130040c0b518100800b400c81440c90006c3c140701d00e031008685950000c2d00400c1c20079402040901c003020161050f640d020f0342e1403415070900c0f402d030b000c090700d1001400c0010b0b2007014009914104940303c0d030102c56807800e600040f1a101e00c3c1c02c8120189070350b5805ca10701c0c4a24142610000c181200005403141140c1c0d036400c01d860f40d01c1d403880309001030510f024000c6d0440204850f4030342c3c910003525100001d11071500036681e1021140304000c00c84000c0c6c407403240304910034042800022503000420742c1c40402800e14200d420b501d0305003517070002d00580f4030380000e000004010a20001d1a0008000ca034450000f01d40c075640c98074100a20303102003416440441c5d101e414100a02c521980102c44030701081161105400740c913840d0003140700e84035009090040382813900b00d12203503454440c484804000210440c01d5017001d400080940c2d1200c501c802c1050384450100c1c0c21542c0a01c1202c802991180c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 689826951 1250 689825701 689825713
    0x40506031f12081309020f090105030a090b07080f010504060b0d090309170d090503030c190309260c04090308011202060c06160f09030203060c0f0d051503160b0307050714 75
    0x214021503c0c0e0f000719042c4805120000000480d80d80b24020b4445e441400d1201c3ea0800c03652000466603500000c003204c0c08140c803402d04201107442440b0650103801c0f6561420702514091015510184060340884d00440c5098410041880104240c40e075000c6540c0d000f05900e00c0c6401c00701d0b14114542c001148030720000503002c2d805200011a21061602138076181d03010390303036817081548a0142c00740600c03054020540d0f12000795110303281060018420f04010700b0450700c0d80502c0401c1014512000d0004400c81c0490881d024108480d1880410445040c440d102480d50020901031040c81010a4101220292421561148244c0d2805c0034414200c072a2890070441640310010640c0c42000031400c02c00681000912030820309080d00d4000e00103007c03a80341c0c2100700a41c1c0d80200c00008441e1024400d054a2007401c1c00f070203019090540341314607036924240825081c5084000682d04084408904214040d500429a80c0c401c0880c1081501e1340c03c03505008050038034141c5405141c0c0206 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 689828201 1250 689826951 689826953
    0x20f06010801020d0e0304030803130c1a040501030b0f010f03050720071e1d040305073c03170604020702121f0b0d020906121504050f03040506031f12 66
    0x55000c1d20100a204006201c1d044c06001700545a00c00e9000c0500048810000211b424521907a0140d85a110310103203152941d88a207100308400301c000550501903c001020095580c1c03500070b41ea5080c00860710814000c0d1194006811014003610359018107803100005091213000341550601348c180b00101c1d040001e00b03040800d807034040302d00035084505101e10f81000e0020102c503500040d40d181e0040c000610881d01500891042d0040c0110100501084070304009440d100c00b5101c0a81c503651101280c1203150b080050001c1c2110200900c00112030000002c83d50082040c00d445224200a100075180c800120b4080d03c07610a020b500044500510114024001a40f4100350142507001c0b00c0190f2504c0150160342e41d0108080e40700110b0320355040945020324030a81c20040080c42300104452160120342001c1140f06004001801c590410042c00707070078444004c2212545018502e441d003020b000503203500001e4149920061180000320300c04030090080d1018084080c041c207444403207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 689829451 1250 689828201 689828203
    0x705150f16092601050907050604060806041e0504020901170705010e0d170a0e0a050d02010f0918060e0907031a0a0e010609020903010b030109030f0c0f080a03091b1202010807020f060108 82
    0x40c00c41d081c030070f5880d05c000203032a0800030480300161180148210b2400d440c1180c11200c20501030b00480d0b006a903089001e500035030040d24100340a85082c00450740b440c140c0100020342105070b01401d00350184402c0c001c0c2405010607120b0680b0424200845000c100c0d0b0046000c0200400d8001d00507401181602c08468030f11028003142c0340309a5405500d102e42d142413140c12905481030580040e0f443c0e08940040d03020b00021900c2021900d40301c3e44c00d0b03649810103611100301103100c41c141c03940d45109020100000110701c1e401241c04d40184508e40c910b680724030440004602a48908071020042500c4000310b810051503403083c0402444002d40b5600c503103000754010b4030542c0c030940c40c125040c1440d00b01805030315100394058030f80024241c09418252415404410f080700c0c031061200b60540055808409807000795019640080c41c441c540c5070044501d450141100500c00507003c003000358406100600350710030fa080ca0700da4555100c8440c20b902c0c1c08500c0e0070b910458080c2d607002080d0504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 689830701 1250 689829451 689829509
    0x1303021f02031f0303121e1407031401030c0506070f0c24110d08061314010f050604030f032f060a05100509040212030c0607050705150f1609 62
    0x2d5100110075001c41840750f0050082e00d10710000380880c0081404c07540c90b50072580600d005c1424000e20b011002c8894442804031805550b030303107458544d840e042c4040d003549445103140b82056952040b02550550b11141c3c10700c03801d84203092140e44000303500000c010550201039203190340101e64402030303600c0b0203400c0d102ca00140741083c03a641c034148032030004500c1207220300144e664240203401c80c60310500c804c4a80c2d500041145070080c0c501d04030342c1024042881402181940740f001c1382c10740e505004002c8109611540107510480d4180b0081c404120302101d4984140c3e818100490041c06c2d15020103034400c05512012150040c0c1038440040e9400403031010b00c12200e0781c0c0100410f540d0030b070f07400f031401020717008040c0c006500e100010018100b0303e940b0841c040301c540403a401c0a4150081c1441e0075000c441660004401181c1030042100811010403040032180303441c14075147c26664144000d81c001c22000d43e4108000c6850400c50043c040300000c0d0106100c100d403140c203004d00c10301d2488 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 689831951 1250 689830701 689830711
    0xb04081e030a140f070e0102070f0b040504050a09120e04060b070807153308070807031a16030b0f0402030702010207051b03070b0c0c030703030f0f02010c081303021f0203 75
    0x1402c003282ca030307034200f842264184034400b1440d100b6a551950042150a4403507007880e5410361041c0c4602080c07205640744403000604500c602030f40c2d02d40c1050140403d80f08068808000103040024140c009400700009019865103481c0502d0011290340000d005403507144e10003103022300001040c0b407d100500e0020001c05006414803040c1d8056004058111954080e68840f030400d010140210488000d20008554035403100342c00007a52034111050801110741d03c5170f6010b901022040007004607081d001c98904503d4081d4481300d241c2200541074060080044004043d540c0c0450b00381581e45a4180c001b508001c0c008644034501200041d00030350241c4010b03507c1344110000341c42201c0307454080e51201c0201602910f6081d14181a0481540041020074401c0c0220605541c03540c03800c00c030020065002e60340b900502800201d01514020901d2204821039060000d0301c99640d400801903074210017181d24210506406003822801d100e98510003281c008100901c0c030030800c0c2d0383e0300614010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 689833201 1250 689831951 689831971
    0xf0f0e061314120606060708071e15020f0a120e0d020c15130504150305010908090405151f14070c032312160b041202010e010b0d0b04081e03 62
    0x2550b00c40401460144244042c8038583c00000010300505020025024161051034458100400380c0d0b102900e40910003030b4203103200f09107107145003800000180c1045ca5104544210b203425603001d909440c42c4211340600060110b5003486032103400140d071004002d41030385829182c10301d513680e000a4654203424803075407094000c001c400d80000341440c00c585110a000c101d5050051400c400d100190920742c00d04650305000d5000000810702c02c0c0149004144500a00c0342d070740c0031610400044400240410700c50f40d6000701091420b131282c41c480c03c0e628060317682440c0c00000090f402c560701006107161071921140440d8003c104101c2c00d030780d0420ba911680c40501800101030710107440941c00202003030301c3d40c80a01109150350820005040302191184000038800d051380300d46071303001c600b564121050445040b0070390314541c1c20301c01c10803a014140024440b016070b03100003a0000300514806000c2860100100e010460300c8411034200415110010038080300f412401e080c1900b003100e401c445 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 689834451 1250 689833201 689833229
    0x5031303140a11100c0c0b061f050a030c0e011b1401060e01030203010f1407032a080709050f060d15080105091005130308010b0d090b131a01060f0f0e0613 68
    0x1c00c0507140a03a440120140c1e486d008480d00030707113441c0004240a48843d42210003103000072035000d54049007000b01040b81c3c503001c1d6620f4000000400b107604400907a020080c00403050301d0380b42ea0260344d02e155800140c240203200c101c542440040000324004441d400d41c603091000131860fa6010002e030407240210001c1241e411001c0300c60050381c1d50030b45020203104259001034400790007a4403811002a08044840e091a00c80088001c0405501001d50109140c0c108100784c482c1e000013000c02905098034240901070b4840089222401603401001c8200c0d26454510140c07140c101016004041c064020300c0300f801c042504a45924483e00c0c07900c5024104000210848000c43c5084425581580c802d2007681ca4025804030940140c03840300411074464071030501041c4000503140c0030b2080308410741001c10484c40d18010108061959451200f0f03c0b4004015594200403c02150492402e010060b43d071035032404c590300320640d0300707403a442240070554003091050990a01d060341c800682c5212 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 689835701 1250 689834451 689834473
    0x100c180803030705030705070305090303040b041e0803040b0a120612021809030301030809031c11010b030703080904020306010908030c061008061003060c02070b120411010503040305031303140a11 86
    0x2481e4403044a14001145082001c01c00182c4640c1c0100800f60207443c1c000d08000300c04000074115409030f8400c2c02c000101080034040b5408042d5130f854104001c00758030710b40e00d151420094a82c0640c0c8140b16207041c0115003410b03854020110441072984010003004000e403200440d0f001444030303420581c000e540c025a00c2d1003d501c040b0b8100d002d0031201004604503071842e030b21541264080c03845140c15000e2540b030203428100445a8004006035511030315075040c4070070981401c65140d0a0014442e034429041040858042000c035081c0c1c400c02d88016980344d80e810016102e03c09a07074041c844500c400204001c803d0804140c00b80140f0485c015000910b0380d6040241d0307a1602504c4122103010034113000c2001078482e510981680c007140c019151345030750307800040840380c0114009040d103000c1c4400704410012154140c06401000342811829400c054400400074040140001900100240581c0c280340c00354000c0815400b075030800a546000c400001014655841c4018001e17200700070b5070b40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 689836951 1250 689835701 689835703
    0xd0e010e15040c1401030207061a030c06130e06040603050307110108010f0612090327090506010507080304081608160c0602030405031f0605030102270109031e0302100c1808 76
    0xc1d0041c3c1c2c10244401ea035600f818a00a40c13190904411410b059003003040300c00103015406074561032805580e1000074072021a05242c108031442d01080d1080404000e044008408001820300f520030201c10300c4100c2c2e540d5030216000345000d82000d40244404142e070010415601282c0519003401e0380d032230b40342e40d0341c41891405600c41d900031080461a1800b501c41030b000075a0103d48800c0c0a072800c2641440900d00486901c1f608071201202010151420700983c000350045a4111130280f030a1458942251114210f80c000540024030143c40016031188645480d07450240c400d80180c010707a5258181c040f4400408000ca00843c2c0f40344528000003440c50010081c0c904503030020700030b81170034040070511022041c03003000580c800720b9644401103815142480a02181c044d60365000c1d600c011101c042d1b000d0103420040c41410403440344414000034651070300034290900c410040c444a0700c0585004d0781401f41e10710b0410505841c286035800007540c0410766540e0095024442440c807500e4000d52 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 689838201 1250 689836951 689836993
    0x19060f090b100915032c010e033604021206120c03120702210303010f0e0c0a030507030902120c01110a020f0d020d08030a06090506060a02210d0e010e 66
    0x402c0802d40720501001030440b40000b446000c801c40c0340004140c4009482c0c90012000c0398580510400043c561614101c4244591250100300d10011401c09003113210f040004001103c4211880313440c4580800b016022041c0442c83c50401842551107000b080c444d1a0a91421241107210301c230350341821a540e030800325081200c46c202501070000b46c003012158030390903405840c0803a0400500c400414a1408101e201100010740b6409140c0c0c1303509d005c004880e008a03542060b2000c0d0b900400703029410745450300b15000014642001700d841d98600c0001e500408200341c4c045d41095901981403882100490711260500e802d0326501d0110801c010015601d610303040e0000e401c4411a07110200c140b401001d140c0d034061001f4442c056172100703955189107903081910b805c1d4400d40c855030706001d00c43e03141c083e440e0b121805030307451402d15a80f408029514450100001503000141c8250601190038a00b25541020a03507018802c01c00142c20240c02020103400c0703e8900d024075188102c01d003020880c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 689839451 1250 689838201 689838229
    0x2070c12030905041a13090b0609010609061422030b100e0606030c0403050d0e011d01080414342112170411010818070e19060f090b 58
    0x150310b001e141404184801040503890240403029030221400155480070081700443c80b0071000460041c115140050040c1030191040b4800e030a902c0050201d09e50218480c0203c50891a001010300640300000c800b91051341a40000c0807650007400c00c1d0000030302c01c848110f922072984200c10b91f0b80d000e00350040c5115801900b042c0201240400c8c014503041b000f0359040b090a0301050700d400e80d070780c3d101441d108a6005420100d43d0b13020099807507680000070300e0803e040001c516040c4400ca41c000900301040100001d02c448111480c07000f619008000031000f018030000c0005500160041340040d52448040c90b0910f9004690081010309440321510115503450900e0b820710007060361003407004150307900b8400c204400c1c5664454440d8141c4d0743e041c01240210501c0c890304846200040202c140100b0b4110301e210310310122422000009035080c110303803441085881644511901451400850303030743e8000c440c00c0040114004403e01c007a4403c889552100308114800c2c201440880c1d0035440d9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 689840701 1250 689839451 689839457
    0x1e1e010e061f0e04020c011401170f01060b03130314030702070e0903160201050706140c09030f010b100e061207170a0b090c0702300c04090c05121f02070c1203 70
    0x14501980c1130a401420b05103020701c002041c0644040749400620b4426485054202011140102a4403082c00380040d8100803c0003801070500b00760350b0700c0c40c45c4006070894035032a1503125600f09040c440c1207039803041844400d180340d032401c1606000b90f551000b802400340390001c1402250302400004103c03040400c400c040143c0030a501d800558994001c510261307034090b10360428664150130070300154482c410020358140c03505044424145000303081c05141515070b15203052070480d6a01c80e041c01300c0b02d841c1480c115110407140c43c003140072402500c9072418000340080602c1401c5400c285070149031403107812030a00b00e0792410a9581075600313020781c2c01c1d0044c0da4180400c4020080d20000c0a50134000703004030b03009050a240508010607601d0740c100103688200185e4506180c10f108500740c1c00c4040702c0074042d0044984804400280c0c1d442464425541c10240c01d44c003201c00c6c045008401c0074014000030305809482018060b5011041c2280c440001001c0440c3e21803401500030300b50354043e5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 689841951 1250 689840701 689840717
    0x30b030601090e0f01060b31090b03030417010c021207080f1b030a080601080703090203060c090f130c231b0106150e1203031e1e010e061f 61
    0x1c007020300200303402c3c40c3d40e0342c46002c0c040b180711114100740281ca009107a28204107945043c40e044010000d50850000b04400d483c1441e140078010072035070030b8401d0751207801c4005504664280082e255124562014069413180140d02030f040506510120b1a4011902035446060b001e200d411454820a00c000f01650014808140b0280810028003e40c44851503a6400d1a800d101054030310317044022240002840da10400030b031135038451400d80d04045503080a000d02c000300d40c0002e0322030800509217042101d01007205512542c0c1d00161403400503000c0d00b0500d6605120000c8400f821100c0030581c08103500395094140c003540d040c039242c0140603072100c49041018030f0080e040e14541140b402501c96486002c0030904240100c4010340c0c003036594460000e240800c20030301072500d140b4140303e80d45030424002c004819000e0a182c41c07042c01800740480c516500c0c0c444007049110313818140e0300081c2c0ca100001c19900f2030804064010102100d200800d248007080e402c0c000800100b0f032a000030070b84 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 689843201 1250 689841951 689841959
    0x4020f1b0c06070506160206070c030c11120604140c4c08060a030b0c031003060501030c0e36030d0e071502030406140d090501050124030b030601 64
    0x35844034030480c03040041d1600c080c07400300003410a4028580c1500c6035000300e000c0c407107128455400c1d400c0390203040c0003a0410b4903004001500c0142c04a5000d4103001c45810700000700940b1012081500200400c0000b084d00984172855440741c0c01c4034115540c0120824070031340150005082001540c0062040501803071039801401051540050130701c030312180140c41c0c00b0301d485c0c9040d20341c46c1400c2030940201c0031501d12001400c03107801910300c070302030840c0d07600a00100c0c0024a02d00c1c0d10aa2580050340c0e40e442c1d4105900301026280c1c00a80503e2030000003104021350200240103c450038010100c0c50345415810b0309010140616020030250013203541920640c2c100c807003007120b650450940e41841a84c5100100341d84004902c1d0b54560424a01401104030544808011201d184000e42c2028104640a041c1d403407002101050044085002d00c08090240c200b00c41180d0300000a100c00d5944501e6800010010311404501200c400c01018400e440781c400d41d8011103000300142050391034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 689844451 1250 689843201 689843227
    0x6060c120905091501020a0f06020a0912350406081e060d0b090111130501020f12180a15020c0901090c050f090307051e130c120e0304090f0504060b04020f 68
    0x81382e5210707410760241e092090086407601000f1002c4a0081002503500c80c519480102034421503003282c0c4009030702404001c0440d1284141e4074690154a6202c0296007003d8070a081c84444008100c03c280784c00207020804039840a2060700070228007818601142c0d96482c0b180517000c00712441c580290111250a02040d00c8010072500080c001c000020740c01c05200c0f071200640e2150304190400424198100015603040202a0112a01501406010b1041c1410391194814440b920640002680d449041a41e030710303100700300400780c0c0b41000240050400001e52583e651480240c0301d0346200c40001520001401407603064401543d9492500310b1400c45403145401c0100c0301a0544115503002c40d1940380c0c0004002c407030b030403028044200c5a0020070851440709d155050781d002c82c01c1c4840c2440582e00000c58400d42540d07a40086070100140a41324614090b0798072074a07065041c481030045140003644024050340c00741c03900b0b1200b0700000c41800180e204580c00c240384510200200c034019a8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 689845701 1250 689844451 689844481
    0x5060a121104060b07111e091302060f070506060306160f080c0702090c0c060a0207110d050f01050c0d0609020403020a031b031703090c010908060c0706020d06060c12090509 76
    0x3200900c002103813a2905050625a0840c640450f0411521a0300d50400c1c901004607403606205135148016480300c41c40850035005010f8640500c200400b000c4200315a00c000a440c0c1c030b40011044541c4414482c2410f0ba07807090241d820380e00038000c003400b150012410300501c983e000080e4544a07500d08a01c0801c44008800030300b65100c54070700723006030710040e40c4469005000b03500741c060550311134241508890a0a001518402d2420300c10058500000c08640d100c1800100c00c80300f60000300100e040c00707400c00d00f1005d0002c4c0d003540703040c0c100084400c4180280100181103c8101302e0140c030b4155100882c842d9001c0a9031203c02c03001c007007000501404460111048201d82020400d549603125401032040f060981a084004010080c0d440c804000b00c1c03103031007824608803c59900d0025040e0b200c230b6015121788500c40e400a9010180605501101e4103100c05100800135903070f840100074001d50090004a0b58502401c182103009071280c0c1110301581c80042155040d0b403940280304160710 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 689846951 1250 689845701 689845733
    0x1050f07170d05072619091506030c060912020603040201030b03010c031a0a081002070f0602030403020703110414060907030b0d081209070e071805040c030b03010b15070f170a1205060a12 82
    0xa81f1401034000064141d00c0d000f010484e1040c0100c0c4050652400010090183e00440100520f40c40100094085015101f940c01e405461107642da032a5400100c1c0a0400c3e0090160150301b00080c0124042d03056000c0c1c50512122004441101c5116040044406640c4110710f0254040d102c00c0c2c01c041d803583d005102c00c030701c42c074000841e450300d076034915060741c10880e000d40158210444c2041804070011801114880450b810400c0102203002c641c60810080d0415024441c0c0b000000c603014080e520008000358010842800643c0c44e00d401c1c0f8a651006001100c4a0b0850020450b201400150401910030f00d001d08000c0d541c5030301d0704840071071001264480442c000d000c0001c103a00c9921a040340a080b940d80826011444014142901c40703000c965800341100c4400b4500c01481481980c001da0b83c044051003414000d030600409401c10790342c034005042c000080c400500343d041901880c4a40003803905200b00c0d91400104256882c4c81d02c0303103041403402014040001000e042a4000b20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 689848201 1250 689846951 689847001
    0x30909130c150212090303030f0711030d091e0f03050703050706050108101401080327150705191a1b0417010f050601050f07170d050726 60
    0xd006240c48010740c030412503100c8008512600034018510390f0501c030f61100054a0210f103440c02080c0300110365a44001003004210102c0c110200300c2040c0324000b241d14844c1100c044036203610080701490001d001e41300003202e803502c8501c2090700034051001894040d50308009800c12103c40c46d1820b0b50158080740e021400c104082049000140b81e82c070a0a01070f00055000713141d4030030039203482030448113940c0b104d4118454401c01044000c0340042110500a07103000c142c142c0d0840c0c0c1c0315159002c7c0d08003600551042039101400046601c04c3c0141410a00940c1256060140343a02705542c825900d4001400c3c1c0641c0700140c08101480c220125080700c0c6107504240e600c010034880c0303582034005820440c28401205145600213100740202c1c400703000440320422080c1004da0000c0e0152113000701110f4800c0000c074001003031040801074035081e03062100400e581c5d080089a080c0081a0449000740416110300b01600310038060b049450b6070240f0704a40801d5030316940e07407255003c90360380034103009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 689849451 1250 689848201 689848231
    0x30601080a021c0e160806010b0a031d1513150b060d05041103100213060c0309080102130e0705030411010e040e030d090303060501020613150f140402040c0f02030909 73
    0x4622840c090012070000b00024440184d000b42400c003150359840f116011086001403106000c00300f01c2c0d50446100020031641c406a0000a602a1804404001900c0c90b04e4a6403a0300300b802185540200052592244095407401c192140010040380040c1c2004072805000403003070300e194881003032054010030a905184d03281381c80f47d0688000b2101120039140940c110f82c0181070402006230300a0040381c1c150700f40021101c547c0040c025611401040291240b200710030705024a5040c2c000e00000342c002d5540d0030b001000310740b003542d4074032904800c00444800500d0443c8143d0a6a004591100d800070741450388200441e0740b100400d4407035610550b10040018624020001050081038181e00440c0501da81c1c240034048515039444181550800001c012040e00085111010130b5400042d8082d032a600841907002040c0c0340710320380c072810b290020a88010800c0c0301414421482141d05011180c5405800c6070390004c003480b00c0700580c1c0148030f41407107890711003051540300301c041c800604 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 689850701 1250 689849451 689849467
    0x10318140d030905120318031306140301060c0b2508180606010804170d23090d0903060b030a020409080d1401060504060509010207050a0b250206030601080a02 70
    0x408404480a84440e1034442161906002505428400341001c01400020351903050716061500d0041d0340c42140040005c00d00174207444d03581d40c014528405c807500c0c1c400d0b0350074640d21004103020301d201040c4240080184440008101d0381030703501942c0c80c1c464004483e0750b1038548030f07000342100032501c85100c414038100c0103000103c8100340882d035900c0c0690400701080c1d01d500002c9614060280c01202c01c000d040c3e40c00641094106a1100c40c020f0405007084184900f80110340360381d00c0b01030410284442818500c3c0501c0600641c1c014400283c0d140c103ca86941e42c100b445108000c1604440c042000c02c0590703100c14400301015090b01d00e902c82590004044410680e4101d450b0309003c80d407408021500d1040c40350005150440c680c4a506196003e000c5014610800d42040030010380404a83d10034481c2c0001081c016000710340107611a081c0c415550031010000050320704002c4004102d02c48090350a4134980c000d044c00b8070319101c440046441c1c40b8020080b0070555000c0000740 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 689851951 1250 689850701 689850731
    0x30602031006090504050601020c01080403033c05070f050f16061409030313020f18010e1e04111009030b090304060f0e0906040e1e010b03011d0307060207020103 71
    0x51041c000c05620590701800e224002d0b2004440da048039001c0c0f031034074081140b00e90b00007800c00d40320303030013404d01041c10b07a0340303250440203000c40c1000380d40c412050302d036040d25000701040b11085c007101400689014042d030030449000c51354206c981200266200300c55030102ca000d0002040a001a2010380b480e01951085103507501510070400c4800e180d441200345c20707200c0510500d03038010340ca90000e10700e1030030301ca401c14404c68801c22000e80f08002c44040f005542c0d607240c020002480500006000d1581c0d00c0304071540700b40b01114580c806220355031003494106100c00010703208a40c041c1d46000b018245138240301c204249038442005100f10840e02001040c3c0e140000c0c0e1040551f04000c540d01c80c10030720001c2001c0200754540b8107002c1150185892035484200940c4e110106580024070002503020251801401682480c041c4081c1c140b282c24031101034000e0011500700758028090101000c42c0c1003401030761110348080390340042c014640040c81c00e40041113034500514011452941d40300e500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 689853201 1250 689851951 689851957
    0x501031d121b1207170a050a03020d0207060c020a022b0b0912041401020712031b051908120105060405090f1f060e0123070201081807030311120322020406030602 71
    0x202c00a03250225401041010480060179003221800329107040c581010000b61450283c072641c42c0a040c0c020900301e50f0b28800b5410385207010740184052140300d0f40d00802075110b4101c01c80036801840004020010340030104c042c020402c0c0112840585510240c40d006002c280280005a0324020401c103c01c000c0305a02c00b40024000c100110140b0244200000e0302c0c10250384e01c41811000a80841d9010a402100c040300c151040443e00d001d402c202d1810b54200b0452180c6171900c00c48150228092002c6d11024080452410402d129580d8860042100074080e0344901580035441400103000241080c142581001c9400c1c400020502c13108204212000d1640202000800c09220a0320540e4890920319880c50a00f04082c6003800f402002449441240c0c0c0290511000781c0100e1050045922030910307000e0103909440b01c09490b1300d00100f8512500007042c03014819070b0f55414090841004580c001c04048810b6201c031480b070320b050801204500301c1607900a585c0ea1002021600c11300003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 689854451 1250 689853201 689853223
    0x60f0612080a020105010819140c060d061706163519050106120209060f1201080f0d090504090813030602271c0804080f0303010501031d121b 62
    0x142c0c850341941d40003400c40f00140d1041007203900031452010700c0c841c58100a50110340040300b0030032010fa03404156290030441c1c000320f82c020b0000130b40002d0a680d02d038004415596179110881d4004281145075688900c15100002a04010314503200d5a90003001d02c0500d603d0b04490f0f4004c06180c40041c0a01e0310900300e40301c00040d12074401c200e000b50b072400000710701c039412030030400865041102c01801c200203207810f090800d9001440088c2d07691820241d40000300c008480070f03034500f01043c1c803641112082c4907280c3e4602c65400700c680c0042e4045600c0d02d0103992965445010b500d0402044050001800251171440d0200700705000702d040d484110300075500801e0003580c6c9080c5a880c0c140482400310b01800030381a00500107115603902038000c1035280641c0c4105400d0091410010010310841e40598203600c9030384075001c0800e2011020758100d8001742ca00b040840040200d41260100e030300281040b42c0c001034221001603100501030b1600000000d5040c0d00c10020343c42642c544a80800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 689855701 1250 689854451 689854463
    0x61b0a080d0504060c020604050a02150913090c0b1e031e0907140d0203030d0f06050303070b010603050f0103120f0e061b07050a0806010e0411090a020331060f0612 72
    0x1c01c41440340b5070040d40c0017843c0030710061006107001e84900da143c811000d4000d100c0c42030051b22011100334034040e24207252000707280700c01464088078018010309064074120340e9030310f82e0301c3c0008180b2000c1003a95082d201c4078000380082d04030303c0500052540010024841074010400c880380180f0300c04000da00c0b84801000a03c181818500c03500120611005518490140c0d41946401a100403040d01c41980c80400c000c1070340000110030f2400381c55150080d40c0c00d80702c00b19804041c0309007201100c0c120381c0300e51020081c54888264514051000340009081300e030442140109c2a03110710240e501041e03c0d4034045492640c4840040d00039070252001c501c3c5d01d0441400c298900702c081c4800c0e00104001c07100c0d800440d2804000580f681814411032030300c41c0c41d540010f41400f02c20102801e040000400104580c0f6202d0b14610081d00305441c43d20703028000d0701072840c1c0303c18940d0a6000094503c0003540e806000c544e5500081c0200d44400d0301c01c3c0ba2501d00010b0302c2c500ca48001c01c070640c80340e4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 689856951 1250 689855701 689855711
    0xb0c01091a0613290a0509090307120e0a030f0507030b010f0f1508041202030f040e010e07142a06090102030f0c03060a0501080a09051002091e061b0a080d 68
    0x3804003c1020303103a50210704060301d0300c034040c19003500c1181d5182c034100d01404411034101403103001811803800d903840190041801c0c41042000500800140b5400c2c0c800c410112528500500454103802003080590300201c7c0c003203090022681a148076805184200120340d2110b440e90344e00c062504081e40b1190058403105e0302441005512140702d0090f050740c400e6403050000d02030f0014850791010708040e000240e00b0140009851080c0100c40e100248111066130315540c44c130f440d420030341007442000865100c400105034030301c0c402d0705005d855501403110b50b03042000316003610300000b120241203107011f901059a1001154240616031141c03003c034000684038a005203000c42400d4004005a949280800c10400165244414041519000e290031401c079941c5a9000005144a00c009005032040d5400390103203900e5038000f0700c0101070680e04d501c58203620401c1d203d00540380400c46940410280004c0702d48551082c0381c00e0024220342d0840c1c081c040c86403146180c90b44052a40c242c0c00f40c541c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 689858201 1250 689856951 689856961
    0x1020a020f012304080d020a090e060910060e010c0f05071a0f070f2901060f0f051e13090b040510081c0e1507140d090b0c01091a 57
    0x14020220404000402441a20701400c400100c00240c8110f0b000e0340c038400c2000c036081c8071625060f1114034604400441d603074030f9843c10241c03004405214000c0720503030810014001e8204904050301480d804440d0071405400c10303000355961303003820380c003d8104084203071404041441014803401e030340d000d6000b4040080c01e001103a01c1d400200c00c4000d228110401009002c1c981c3c0344111004540c100060000001e22032809507250801c124282443d200d0010001c2031544403040514100c40180d26a0078045044000030b07200080b00fa0782481c007042042c84a6501c01d0000401c110794485603003155813400d070500704003001510032600400075141c1e03105400300d820705080c881c83e03030000078440704c04903c00d240008665480445404c800511300c00700d06450b803103034001e401c3c1c13841e81c2d0030050503903040c0f10b00c0854030100c1e40c00c543e40c25a07070ba001c00c44951401c000c0c00320b800c40041c03580ba83ca2420050a0103050b81183d13110b4040000701d5075a03180050302045031b421090b01a20340b10f041d0486d6030304003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 689859451 1250 689858201 689858203
    0x604030c1a090d0b07020c0402071104050702190609020d0203150a060f0b09040213080601080a210c02120a06020f0a0f03050c03150a030506070c0c0602060402010509040f02190201020a02 82
    0x524a00480800c0200510300003662611085400f41e40d00c0012011240d031001d6003241861310f40d0301459000b0340049421801c00510220790b002c50034069404004035654044100d80d074158402c0945510b41c6040317180b0000c100e440d0040a03600d130000d041e0f1100b0400e19400b0914180030000e00070031000006090108954075800350707070020400102500038540c1480503c079118490003015038819070340012124000c201040340200101500400d0b41e00541e5110006910389800c0c407000c827450a142c14421480b00640c4510020b00050307907440c9000d880440d800c1c0404240380454409241c450340c0b45100c0000c0144c0000d00c080101d20301e1140d115014403002500190b1042040014581410200310302840f41005030f03a07100d41ea84500c940d41c00c4c0c008011803c960056000030304203000c2d1004200003183c100144407506032007001442c00c603a40d0381c0022622220140c5009001440400a040349403500390065880340304000401484c0120070940541001c00349110040940d401280a10000d50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 689860701 1250 689859451 689859479
    0xc0311030f09150c27031b0f060f0304030c080d231303170c04051203090114040e060f01030f15080709060602190302031e12010b07050c0108150604030c 67
    0x800c003c4449003900702403101c0c80b645e0080c108914060038407848001d25080c840c0d4041080580b010f003d503140144000b0550000038809100e80340160b2040c05841c3c0e090503ca4115042e48000045a07401c607200c80d44c0881d00b4840b2990180d5840009002e4030000170410700c2120860103112001c807030a01150105403008030b00042152290003502c180000c0030a40142071140b9410704104490480d40d107025203446207029507044550851040380240303102e0000000105100c65090b22261303240ca100c4045410640319501601c610001102c0100e02d050600d10327080351740d9001c14140031a02c400100141c404465203545462110a0580c00c200011041440020084c001c2414144040c03814690003175503500c501c42107241000ca2590b0400d00303061082c0291200824421071030300e203100310b83c0d04641c0300d60007545468810b020320800000750102081c045400041d4054040d004920140005494004006040140d5450302c001d6411a80d40c0302801000514403031409030040703d0410040c050300710 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 689861951 1250 689860701 689860723
    0x80604090305070b0603120d0b12031306050904021b0d030506030f250e0708010603230601050d2703030b030a021c1e1104230a0c0311030f09 62
    0x54504030111012a5114007200c4900360010420b000a4030303494080303850103110b003e0781e0603071503004603400c625101d040e0080a1800c0c0c0456100c40c41c403003250b03000c988a100341443c1a411800500c0d04110583c06200900090100244010305003051200c0e10b4129815510801051390050554079100b15050300c00c040e0064800d80050a01c00854080b16545d404585085c21000c00720b100311200340e440d0030000790050000702450328020300b00315401600f4007400b8001c00000c2400e0040401201c0c0603805401e150980a0b003111810792103d50047d41c507648070002410b1001c0d100e881c0c04521080100741707184146050701f0b60a1010400b818010f0464000d04981071003500810300c5800940da41c0c080041580c0000c4c900a08002600c3c580340c0c0400804a4075102d5103807032404c21005020b0072400c0b4003000c1c40300341e0301840103e42d1501d21100c03021120741d90104244580d40820140781d4030307a2240c000010075003800100c040200550b01120741040701d14513111807401c42041440c68080c0000c0b0900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 689863201 1250 689861951 689861959
    0xb090f0a060f0c09050a17010e0307050d23040b0703020129010332060a080616120b0a0b0c0a0b01031103070e09060f13080c010c0e01180b0d060e0f070806 68
    0x89043c036002900d803415510647c044001c0d03443e1214a070311400c0d44400c00425407002182d565101c4d51030056122404c0c1540640410380322111003401c940035510003181c448904015524142c200314072000160080c0c5415000c5660f90b414000c80210664240c0404958085804034a00c8241c000103095440744034485c1e0408a40a451000c07403052900c1060000d268030039844547c0e980c14001c1244941150700010051003075000707002c90003030105000f4000003882c4d0341e0954035400030b00140059400503140c690b0809820001002400034107400361150854000c203030303500c0c441503071a40c108100080c0c02c10760f2840c0450100c888246020059100140b201400094a07864801703c82512804010510744d60f4180d80d2000940701c00e00c806130011281d91140005072503a1700005014000d00f00c0e12007000c0421600e801c0540c42c0c0d0b0143c0c016441c002600e0045400312400d0858459147c1c20071b14010b415207031602008103041400010340e5105201c031042c40ca03120720344040000d0060002038195405 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 689864451 1250 689863201 689863217
    0xe010c0203070c151e03061406030124090b040e01090c02010509061b0405130903030b04061214030904020c0d090b0a082d07030e060f060604030b090f0a060f0c 70
    0x11800b42c2c105044400100d100720034180c8104040d00d00c0c21401d1017031501510b268180c07010503030305640071206840c0040381c00e041400c0ba0005002492000307005800790300f064901614128003811612000300c40c060324024007016034441c00701140f1f4009420205110858000503c45550244604c101c0c00f41c03103100074813060a203181c900e500e03024050054502d0034018800d90510710202001c0350003c00010349036581031602e6000040003007111980840000307041124202d9185440d00900d025a0b900103203010034000b4690315a1209001c41c4c0c0c41403804e0101340070f40040c1d66100c1c800382029040c0c1c00058651071081000c0200383c41c80d02e800c001c1900000b070003d1002503600c404030b40c0e4031910fa044400c0d280242e07244000100300e00d0080c1d050102c11b5510802c50003e0345a002880000c2100d0100c41c410f0311880320901c840d0108840031600220180400c0000c03440300f5030001d0300216a6016992601c1034a0100e50600c1501c84003690765903102c0d5184903c0d6102841244841c6842d440e150507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 689865701 1250 689864451 689864453
    0x3020f0301150b0c1c080711010b011209061b08060a06080f010b1602040609020d1524171f0e1006051e04171504050a0303110c060702010e010c020307 66
    0x2091650720b0240c5100b452001c1001354480e0010412826050741c0304440c1102061003110041c82c5510031176001d800211400c0047e144000c05010310300d40301d40141c440d400340414901c242801406411825610710f51181c1d00400c112512402060008041d941e400c2c0191401074140030602801d980101c081007072807000c0140307001f00c1c501414195851400c0c0d1940e0f07605e40e10107482c26000540000b13075000f031034614005035104039613000340000300200c4010310980740d50f81d4881e10190040c0c07042ca04e6010703201c207030741c050501786010b1103d0104c041d06249881c1c29810700403007481070b02211078000b21b103002c9510b038140203504241c0000501105482c040306181804001a4000036440303841706009022851424102103041112400c032001d100c6640c490795510039514403e00c0744180400705000384541000d903081c03c01d000b20b100b10382150050911140c030303650441c002c0400f6503e81d0f003c02814412040080014480c00d4014501e55002180308500100c02c0c508403540030079a10705540c401c104000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 689866951 1250 689865701 689865731
    0x4050f15070806010507081b060412030606050306040b04110a05090a140d0f061b0c0b010801020301060504120609021201020c0f0706170907050d08030405150103081b0f03040f03020f0301 82
    0x2aa0200c020b107040e50f214600741c40c180d241c41c020701036079a072907a8803000010188e01001522034407450040b0b1402d031010030419070503012200240202d038002881080020001e0030705401071940c540010740000b401c8001e14400300147c0d08600c0800000035130001c2d800703110389401c0403040c028000d200e0107040e40042e1440020840c0c41e900360018a26488001c04400f0300180340c0c4581e10f294a009540e410349414440010400300549408581d600780e41340000c2110941403003a03a040c0c6030b558807901c0c600750500300810a84491074208603070503911000c0070001070311180720350302408400000158692501071083c500344041800d014400b903111810030407038264800481c5100c0c00207445015001c3e201c1c400c80a003405540e410070742e0030403509003821013045a442c004520450003141942d4180421982e207464401c000c0c80060b16100007482640c2c05008075000100d8040c0c101000c46080c00d03030804501c0d05640196000700c2d403001c0138020030000e504061103102c40c00c103012002040007074441c6c5a10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 689868201 1250 689866951 689866967
    0x1801052d0106051c150f08071409071d0a060c11090402010e0f040603170a020708030a050a0e06070605011415030903040911070b0a06140f13020d1404050f1507 70
    0x2000850403060f2000c1084100b5501070b17003210660100a444564031410403072240c00780e601c604907142c0304203d80011000b00350380302c00c4e0751110002c1403a8401d460312401100d20141008182c8501015009032130815902d6225a40c000d101030303221142500d143c2d04140403100100e8070001c0c003e0018008104c010303a4892021045d04408980440d0340d80c4002d00464001c0c26160002040c0d00c203110000d85034817489601074081c40a4540c201d580e1141c031050001d860b80255460000418410711900405a0141d0008550031798050542030030850607860b1042507420a9100d0024440d1404840c541c42c14031710304a070400340e0000e005a103141031440c0340d50f90300d21a610031002c03915038030020046407090303031001c07a85550b41002c005071040c106142c480009203010b10500c420040e06000c01303e1103040c00d58201004d071034000e040ca181e0300d4070180200d0180d400900703080c0c4295564420203c001c1903003202903006034050f100812480415501d01450240052140030f2444104020001100c3e448501 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 689869451 1250 689868201 689868217
    0x9060403050f040b0c0109210207050d060b1f080601090308040e090703050f0309090f01030b070e01050c070b070210050309070b0f120127020c0d081801052d010605 72
    0x5580d510122104107600740682d4211350480c060010b8141c29100d8150096900140181c0307510701900c00c00f229191114420003040c4001d6009103000b00a07600d4a0070340c000c6503134080c3d038011400c0f60410000034840d90480b9903040100348850000c803845a8000541070384940282491507034941161580703025401644202c02c40c04d8260800600e00d410140b125400441c0d01504481d500b0302c8440d001501da070400360145004001010002e81c25a802c001154107d079003080500400c0c5d00c40c00e50448103407ea44030483c0c1400010012400c4a100030804000103001910306251900131510421610481e00f107410000c0150610520501e0400881c407041100c412015a55486241d81d13241290360091a460601440c428400040e070f0903020a14454845003100c0c0c07840341d10324060f90303c40890050444080140d4064405c14440501504096408c080290780304248540c41e01040da003542e008072680d051054109145140900040805240c2c3d00c894500c080903543c104640100a4098005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 689870701 1250 689869451 689869457
    0x152702091e0d06050c071101140901081803040f090b0d03140309010f060e01060201051f17070803030412120605090f04022205150a030b0c07150510090c020609060403 73
    0x21070364016510340c1800003540c3da003e081408149003d140040e01600030501c240d9840c010300c01800c1e03481d881600300f0910003000c0301c00282404804001111041c2005080111309a010707604004540c1d42040a00000c082c15045042d82d2403d2103240c0060b54070b01200c0c2c07401f6100154820780001d40180b1000000b48035240070079100d507a2042900d02601c15100d05100032490b010000c1401080c4803080e47c1a140940c0082c41342d601c03103400d030f0160300503e201561094458500103010b100c120f1928085c00320807440c100c40c161911180030604560054500315145180310740b122000942044800d980f03065008000c010302403030b200200b100c2190040c07000a2100c0381c200014110340c0c40c6250180c1448420706d00c6510b000000e141d0308010030058840300c131035004800345000903103840040541600c2d401306400c0d080c0d0300c0d80f0076100d41c5a08406000c0310607035450190250100d2180c480c2c00d11414140e40004902c078035040c40c81c0200c400d20702c540d03000c54021000300500c040000613401d81040e0f040c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 689871951 1250 689870701 689870749
    0x100306021309050c040914040f060e0309220605190e0a0f0c030605030c0616080c120d140606070b06090402030705042f0c100f15270209 60
    0xc07200d410203807500109403181c506014416640513040103007003600e2551504100b801070f011209405c41c0401c560090400e00d5580320440020840d401540721000503404803030401c5d10b0140000c0c4000c02102100004203110001c1c503c0284a5014000040405a9481070b80100484000c03821301014081c0343c02058219010070b1610078950300683d9940103405040204285603407004014151521031180319100b0400f9407405847d101084800c2205c094030349414040b5290345908030307a04410308002c214001e2014803141c216920004014030781c030550000452081010500e120303d07601821050144005001d40e200003110400030b55003040c42250007283d181c2e11440082d04d002850b800190704141006262a000c40341c4440c60080c621114024006d50b01c50091131171824015401d0b504020782c40300d03054540d604083d501202003003d2812002c2049601070307a00e02d007000d80c1e031340c48454148811080c2100c4003100c000c0034010b010031544150320741441d840000c2d1845035011020344026000c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 689873201 1250 689871951 689871967
    0x90b101803140f010b04020c211e1c0203100501031505030715080c090f15040b070c15031a010e011110020703110601060c060e0309120610060810030602 67
    0x5056104011940301100020b60b01d07815980d1900c403c40c1100301006136080000040c0b06103890b0090b16003201e404401804072441002860101d007068802810000348200500340c1d00100720704040040e040743c081d11a542d503000c2c03685010ba045903829158100ca00c1401840940418030100e141224400d01e004603a62012042000462040d41e0110340c0c10b100350200010059454130301e0b40c80440c51600d940d03000b69a003a1007041749120f00384980340d0001141c00e02806500d448901110b0361308002e40b1550425881c0c00a240c01035100003820b41c3c282140120401107190304c031042c11800c241d249001e124030007095640d842c0d1180d9002d030f86410b00500039065403141e441064100c8181c0c0c1c03500101c821560b00c4a420400035441004154002040003911a545070000110281200e01560b514a04940240c4070817000744640d210f240003500003001030303400940c0d03080000041506d240c400781c45241442c001721829052542d210105202060041020714064040030800326500300f50050398421715 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 689874451 1250 689873201 689873237
    0xf0308070e1e040f052e0b040306050c0d1112150904150b0a140a05221a030d08010608010807050105040b0a110f0303090601140d06090212030403030302070507090b10 73
    0x1030b02c5211040ca4503017070400c074a40030b15611102a0017010450f84400f00400326080360b109459010b02146a0001c0200b0000071f441c55100603070240043c0700c964100380088a010301541c0c076034a2218485100400c0c019140208410070580012a148403082924402c3e80072641c1c07404001c1000d0708142c4403190045400703585420a40402d00c005080ca030280e5140c010468452290404d49800b4040342200440c0e6420048000c030340040025404031410b464956004003d003011034142c000c2407218214416817610704000b1801840d00030f0716004450b60500c00021b0440d101607000b40710507030184000700000e036081000c0310b0588040d031419941d24221188255000303074581c4e48428507841407555851611401101950084030b01c841039854a0340c1c3c504070740000c0003a0b42112640010000c02140001d001940550505840541000c04103060160b00a013150400d501c10b4000c41c0d0000761800400c0340c10f1210b000501450360040110107800c02c049410218242c4580c010301114900039184a14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 689875701 1250 689874451 689874461
    0xe09070c1202070b070c08010c02010908160f06060e090c0301061401051317060708090c0109060c030c0b090109050f030414060310260c15030c1b06040f0308070e1e04 73
    0xc0506150360b15600b601d050030f4250b190740318050295189c116040350051060042ca10b20320741005a41c5c3c1421850480c0452007176800700115070b01100c004540700011a1400340320000d00c2000e652009518011000c00e0a11541191a52081c3d06d0940d0a0140c00741c00c8c505c80c1e044000078030380941c44100c60300b0102c000358204d070407081c041e1045142810148100044080c40303403d407540d4a0907580c035461003440c0d56440c01d0314258049090428140090303481358080000d294024540840050f46688484d40302000035035034906113944549094051120400085484441d440011850645000d2455600703220000381648580c5000004c20700100b01c41300180041d0904070302d040040c0004071804810300401c0c0c12000214002c40079440b40c54a07051a2a072000009000400d05e199104465516540d02101500d417002140c444441e4240e901004010b110301e01c01c0f5001c0040c00041d0a0151065030010300b4442040002c07840c45a0640f68185c0300240ca11044c0b04600d030981c200000100544 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 689876951 1250 689875701 689875709
    0x20a200105090a0801020702010906210e0312101508090303071809050a09021201020304030c12050705062712040303030f1e050a0b0a030b15010e030d030c0e09070c120207 75
    0x83d008001150b2040c040d0300414545100340c035000e11442e42c0d1130040c0d401c54848440003040150300340c061740b0701b110340e03402441c146210b08064a291070f40b0800e02c0c182004041d51180202001e5113000c0c0728009401c2c042031500d20507070609201c42c0c40c0c19011141e98dc440289941b0070080b41c7c03c400b0400e604105003440191500d02000d215502d00003d03948018100303601d09074800c00c40c80d807841491a4040c0300311381c021601039942030784c201c41c10380b07452110307800e42e601031003c00c9020000440812000d01c00c50b80200744400000c1201c0d11011700d440600140702c0e03445002d41d0824103100f2010b100ca90304640469605007404a541031340e02c5814802040c030255401c9640030000850b0700c15085e03a07404507100310051003082109440c06400e01c8a14000c0d800001c040c02e103000045440780001c201d80701c1c0203180515151500d0a5600e001c203041040310310b074240100e61546403040005800900c86100100e069440a0381440d24840050115a0001e4060b00c884100041c0c2c881d200d20a00c5414054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 689878201 1250 689876951 689876959
    0x4110c0f010516030b0d11060405040903050d0c260714040803091e0a06050c120a021506090403050a0c0c171e0a0c271805010c020a20010509 62
    0x8a500c085214040c1008441a1016880388031000c01d40c54000c2c0b007281c2c2ca0b9040580300340140d60550340d03612800c2c2d01a0000c0381e030002e018440003440f503441d405000d6105100340d42c3d140c0c0359801d045000741640c1441c02c000c2d060283d4400071081c044845840e24140342c031110400186501e07801e41c142d40b0032801d00e540380549600080c0100f02e0143c00001460b4640c004e03900b001e14036101d0024412030110382c148180e0700c40010007040094601c20f0b4042c0860180080c1511035000c03005182c0ca80b1580042140f20158006840240b41001813014240d4814800d0355540614907041e40e0061691140305104c000f4499102800c40902c00b0104140025104e40080b600000d5400805140c2c1c0740140c903024081d0000c008012030311710401184d8603111540c003201d9007100d0750800403004003464211407254402000000b05480390802c5015151100300c03c5001401c1c030311510b0130090b0035905904280c1d015075001103c4030000419202d00d080c803294444274404400c66003800100c07254400e441c111540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 689879451 1250 689878201 689878213
    0x150209030105012606070207090b01020708070602070515090d030c0f0c030803180c0f0103020c1f0b0a060806030604121106040615120c05090a112208150604110c 71
    0x11381900a100c5075000c1c681403e0440516a140280c5550b26402c03100100140c100b000100581140707904084a1088140140c0d10f455031100340301741c0f812a5030b5129000503407000b039081000d030921440c000708020000d000395181c070070b002c40881c08070804400300078100b01f8540c80850a0180c070021294405a01c4003540c900d0035a203082c41d600c540c100f9122241100b6610b006d0344400b0300700185100041d94041c184803600c51160006400a40029000c00030a016004403140c500c03498000300c84107282d013038a000414510090502425805035004030081c1301c1040d050003650b940005181c5e5105610041e003107103443c0c0f44136049420511045442c2c08a2050006010400106401051500f040301102d021641d5841000302c240e840d1203031015180c0e26044400340102d0400144481d40a9a00c948c0415903c03c444408a4284d00a0144071042c5103580030740c0412006210701b11000381905401800c034100041035000481c407001d49214455955250092000b02d00b2105450305041400f00f40d0340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 689880701 1250 689879451 689879459
    0x5160f0b1305060907050a03110402040f0825081011090406081e060c0a03050a021b011a0f060d02070c0e0907030c33091802070507050909030715020903010501 70
    0x16201448540842d124082c58000403111100000c59000b05c0704000d0060315010f1075504c4020300d18110000c0036401907020000030451032200602c40c2c2c014000c41e0014400c50740c030412045615224003038a480c4540000708204420240051044403e40346010002840850405ca06503144504209190400d00f0300c40300041c2c14002040350f0950303540c0301001d205c0d0307a0302d20680b00c0d84030740d01144c03020a80c80307091100348200c5209601a41e80542d202030700514110b8a1500c2d00710f12a800d800c080c0303450791200120145021a46000c1043d6801036071442c90720906000081c059004500010710f80c0c0e9070200d030700001d1002d0900355900078122000e56070030909201d442035444440030700050798822480803002a0604614100c8590408101400312100051a00702d24034207000e0140c5e181044902440070a0219102c02203030081c2141500041c0c2d540070600d8a1428524954032613486500341c1010012400760220841d2211644580801c80c2035072622040e50090040e04d04a603090741c64040041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 689881951 1250 689880701 689880721
    0x302030714090c040806010e1515030103031101061a180402070303091205122d0f091908040e1f230f1003050606040306050a0209040501080d05160f0b 66
    0x480030410540780d42d5003030703591694040b032180300310310944185512400040040a030054005d541110304201001c1c1030300c820b040028618400c030400c451034640000010010190084010705802400a0083c00300ca494102020b000030141020184007a400064070b420303041c15440c0900101000420441d01d800786404c008000300b48800c000c80710300700711001540c903160045041c0c4d450003644c4120b40f03056558162100040310040c007024002c5001c0700908051395034003c403426100da0058a54942d00303142180312a0325180010300341c0c0303200c0396503030780d5840114113030303c048400f07540e2908138840041c0c8403d004142c48031a1541c48400e81007821001141c120500c0940c60f00b00c030200452404070030807180400034914a20407500e548002c5020303032892000d01981042d82d004030001e0009080540c0d0b5111501a65030494003810350aa00044403e00c0f46450703c01c90b13024003d0f510060055644d8002e001d007186c41040140c109011125400e401000458045040c403985d01c04440003490802004c44 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 689883201 1250 689881951 689881979
    0x10e060402010e0303030103050a060f020706021b010507140d15051003090c05090c03060415050d030806091005011706190608160806031e010209031c020c09191503020307 75
    0x301c0c0014190500350070f892500206490689030820050300d00c1d42103503540c21005000b0501781100f006e8090015a0101d550b41c400340c0300c090001003034483c020350410074213400c640b0014038403001e00017100c000c04103c9202000781c8030090070020000411486200d00829010013070740c40703e40d00005800101402603459007041c680e551141101123031461f2540300f0003c0070801100e12846020080c07000a080f0f142c1604000800c0018058210203180c50781c0c007080c0d0f0304400301411b07000b1405550600c0120300780409140c1d4003a440800b25103100d0f04000008001000d1441c060b02081c1c42c29001c181e01e6a140c400c0000075425403c0402d4040ea03444a028102c071074101c545c200c410103881107051401d03001c0c0c00740c14030802004000e03164801401541643d018149500300310159400c5c07005140710b0710100409141c2100fa514210001413100900078174000e81800e0040c002c1c1008410303c528400d00181c52002c46802102c0411500c1c441c140c2e40b0140c14160f0f0001e1341c10301ca0b0a5002403156040c400b4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 689884451 1250 689883201 689883203
    0x20306070519020d0c030e0103091709090901050903030f0714120103050d090305120d09080432030604020103181b06090803040e07140706141602160620010e0604 71
    0xb09014030964150705a845194207201c0c10041114540d5020000e031040d00581059101410001120a2aa151f500505010480c0850b015a00007014412440c08041051f0720081d410003d002524183d8030560722070202601c1c1140d00d0030f9640c0801e84003406403014240488500c880c0c079480f440b20810340038150b1028403043d1407501400c0d000141d5148034140f418182d98000000f8480241d40c5d000e40f800c02d50203d01002c0c2c0300b59803082c0103170009812900800042510b00d0b004214400c0d840401c1e030702075034100b090303050b0508402080c020603200401d00a03805902400c001820042c4c3c18842856452a03a0004084000c0c5840c4038005041c003401808c06c1da6629900c02d0307422520381d01440c2d624440d50082c5041a0269000204030603c42c60f040e11844c4158102d0760f091600c180d541000b629001c200f5911902c8401c003c00c003a090030341e8031601c140b882c1480103040100502d0100407851b503032030255404101c043d0706004500c400354141c112614040000800c020801d0560084c0c6815050310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 689885701 1250 689884451 689884477
    0x10906290702274c0504060906050a08030a0c021c020d0f21020601031122020a020105075c0601091e0b1f030b0a05040507020304170a0203060705 64
    0x300702503900d50414240384030b61007020001c4a0080488031600c0094107426800881e031650104080751a80346d90190200900d0101400700d0726500f82000c0003c500306c1c0781c11500e016441448002001540319100c942d1180d01901c145d861490400401140c1440b50440030307401c01e5600c1c00c200108901410200030260240f001800c0d4909404d840b00809220324105000683c400301c014004a9070441c4805040f00c001403504100307606501405004160700500004050b90201d000302d403560302801415401010f5140562814100c0c8115520b080f00342c5404c401e134a8140b89500c1d0300d640ca403650320701036010a105d000c51907441d00a0f070000703440d80b00030040f04140128070000900c110b0901502658110840340c10310b4440440c110007009090506a03541d0104001004030001c80c601041e01c5a8001c0669000c2482d052040500035280d0541c1d1245020f00d141c1810400135941c00700aa41c15103c40c4240803440c0300144207818a41440c894000c0c0d854000c030828409000e4103d40102030f442d072002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 689886951 1250 689885701 689885731
    0x30c020a0209011211010503090c0906042403030f08060d03050a02100f090201020c2722120305090a031202090a1805060118080d050f130b0301090629070227 69
    0x5c0111954002179596100c42c0d444400c510300d043c940700442980c0300310b009e0700001c1c10080e6021006144c0102089046c07103d05000010b2040c10303803152490803141060309000d1254104400403030040d1500c184081c00308040481c50b03c1c0550f10910401c0040c14814005120300072002034410020042d61108a02521030905d03103066500342200400c062a0141c055081d81010038246030b200c44200900c0c082038860245c0c10200c5042c3c652001000403801800c010610354000030014040300c0740a84094903c1d40a110020f001039031003103442041850072140980c482e03110501144c001d0440350421186501c4202ca0f41032400c40a50040b441803401b680c400100050f1000c100c6180a01402504000e80103d010340c482035020300002c21000441a421034034040b010700c1c0c9840d91203030a80001c03034901000001005002198010b0750050160b041c0c83c60318050103a010400a04016022110441d4001c03038020155520041c6079000e4900440c821030708500081040c5001d4903080790100d0800d9820 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 689888201 1250 689886951 689886983
    0x31015060315050d0302150f0709240f090f090b011803080d23040501061401050f1204050a05190b1014011d0a030507051e01050406030c020a02090112 66
    0x1c0d009402d402d000700718070a404141401e0502208076032510b000d50551189030140b4503648000c406040c0b1a040c0010342da00c080c01d10341c5008250302080e5000445d43e800114400707508050300ca68a42c0441480c2c244100e4001c05210281e80c0700000b6030200c02411b009030070008443c0c0141d04040440ca100b61707a612503a0a040c60f1341c96030044903000140242e50180910365041503154400c6000c500900300118480740348482040c00c4200441e0200d90a0351600f8080256184905001c0102e0318242403032414044020305000e1a030007903041c450881b9a640003c01c3c107000c03042c032920b07031655000710540341c2350340502c41004449180700340c045800c040c181000600c01c04442c99000159031012003810030003c070311780045488401411035143c080c1c10598220385665184403010b0b008612410113083d051789400100056005d034031400f000d004490800c0485076a074400101e905441c0181000208042070f1882207140088180000b90809941c1c000814907004507028070780424440c1540002c24460 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 689889451 1250 689888201 689888207
    0x70914070c06020306060d050a0b0405011a16080702030307140c01020109080405300c0f060406090e0a021306052206050301090e0313032102010504020a09050c0903101506 75
    0xc8600c0000101c01c844003800107006500255000f40e001452682001001c4441d0000c0f1402900d04451070341d92020300d04442d04080c01a0ba00416521807500e8035054600e510500720301c40caa11010000c0030000600f000c025105c420340361040d4010382129224605850308500e0401c0c8440c580c91070744105100464603620500441e506a035000c4801c0742040d06d00801d200200d892003409185100b9103000e5408150100b031a01450554080c004010300c1c204d6205004c040009000f42a001e00b60403c4144029500104070804480f030043d2080f10710f80d1201420b00080c05004038645282103500000200702da030000c098894420102040c2820744031140014551441503c034440201e0f00c103000410003021180d01004420314078006482c503181c4402c035082c0b42c10b00b080e0800c5501d0240031440e648074440001540441240500080241d0300f001c0d00020201c4000340304241d5025152000a18268900c2e01920741c44500901160b9048400e0400003010300300102a40c2c02c01c061903800001c04030b01c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 689890701 1250 689889451 689889491
    0x20d0609050129030714122b08150d030212030f010f06020a0b01140103020c0102071b0b031e040c24033603020c030304090f14040302031b0106170709 66
    0x580180145038651400442c049078841142c24140e2040007c043c001401c8002c0c4184124031400c030302d01c00800c000040583c0318181103040d08004110740301c2c1c06c000200740d00e10200d4408100c119444040030103680b40480c40e00d001007600301c401804c04424050307a9244031401070b058540071041d8442094444504903034540d040c41e00034043d220203d004001008202010750004c04040c5005450720300a00d6000c0d0a81e44a1481111055144401403001e074880040e040003416840c84a01e00d5030500801c42e40b41e040c40c243c5400d40c0c4030740900214080003903c0c4120340080045071069140301501802c00d05c0c1c84017541140c940801d0401036541040c03072916804441e601000341501c0c4c01c4140d048403a5510103c01c010842c00d40c85400d14000c00caa4040000d0703c0100604a8049903a4640c1b8140700b0903601500b054101c5682c12070705000000b82c02105071b850300818818444800c440c6901c1d017a0240c003441d403142408004640501c1003148002c1200c5041d180312560900103868002c2079000007030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 689891951 1250 689890701 689890781
    0x501140a030e070b040b0409050a0b0d030e01030902040504050114180706050903011d0604050c01030203010b37030c0e09010305030307051b01021c050f040809040207020d06090501 79
    0x894104000c0c1000380c003a600008401d4001000c95058540340c0c0d41e0121290302c01d4010382c02a41d03000c1001c200c0542c1c05d009413135000008510600200c84e00e01f01158034204118402020b0052440c0362400d1070344260701949016400400c140550b0030582040d6000f4442959501010700300d500019040756188190078100781200801003120f5403030050115038a400c900446a03240d503c6035454121003090000c2340341c4240060018000d00d080c54130309185401c090f51102414140144010050044003a094852080518940caa41e50064074401c08240340060425401c034008400720341ca4103681035010000c094003036244c01e4040c160b07050410000c5002440000c11550007080045c1c580ca04c55006440220b1110081032420b03895450928203a0f001400300d40c4007030080700303500201c1c050a40195a003101d088119800c003420240c0768030046204103481e080c0035a400080707503021925082c20b583d403a1a0404020000300300c403403400602800f171405180d81000242d006040303551000c424468400303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 689893201 1250 689891951 689891987
    0x6090e1b10050f27033703020f070339090222290316050f04030b150f030613020904020d080c070e010803090f0411040f0308030906010501 61
    0x3050302602156141d0000b84800f01c2d800c01030210060a007120b0240d0342684d4142400444528802c1c000e051410003501d12852030503a02d0004034900c032088220b0502e40381c50905803101040014203060386010001c41030181c0d0791140050010a01c500100604106c505900080409451411121481e614412030340341d02603a50200030000b030303201a8000d055954048032040200c40340f004c0c105000030341561200b01107c0c000480d09884406062040c0040841a8042c034210304200300840081c4038070000d80010302c0000074100d50887d0711802079070300440e803002c002d1200e4509521400600c002454015000300948200e84605180c0130400906ca40341c28562030b59085010380030018110800b500c10798004882d04e4090b404103448000030081802150001c2042519141030b22001c640140e002040d41d0300144072406841e030700d03078500220f0b01c1030444000c42c01d00c82030340760044035200b00c0d0701405142120f002e0010400020202548c801c60f10320054411580c1d90307000565448103425008008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 689894451 1250 689893201 689893219
    0x181e09050601030b0303091306030b15040b2d030f0d0210150305150c040504090305090109060809030a08040c080a0f0524011214030a0c0b1308030708070e0406090e1b 73
    0x2160601100300e078200590508d01054950380d944440e980610140c510a070b200310707894044c002034182409241d030f0f454400e540d0030203050003950002e03240200100d81c0d00b003171881c003910810140d5410890300407081075100a0710801c0702c0052029607107129840d6080c2195080c410103648585003035811900b280d4020000d4025940032980c0c0f5846110014402c00e2109030500007c070315501c481c41a80d00041c031945601d41d48075100700015001e010990303c5101000004010000012400310564100010320b0030410050344403440c2041c040d403510f8003c22128410000200d0030321043e4104035030902d000e1003ea0700711403a00104400b2001c02540800e01501c072601c010080e4003292041c64200900603511144c80b4852441e8050843d0322200c1008001005e0440c036a05208854080603000a05244800e280e010956684001c2c0c0c04014200d800740b020b6200020f4065000301001032080780014403c2081a84403d1100700601c1561599409440366060107800721170540742100e910403001f040706031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 689895701 1250 689894451 689894467
    0xb1006110a0302060c0313060c0305040219030c06050d020702040e0604210509010f031b0306090f02031501110f1507030e161802090d0803010305120a0807181e09050601030b0303 78
    0x4480d46c000b50810499100310890803010a901b489140c103000029a00401c4034103041c0100081e4100340b0b80400707111a20038404200040c008825001115564200a030300c03490380702d41d0340700280214040a504035040c034580544c2041c01058180c031841c41020010b84440c00910304012181030103404001064013082468640d41c002c0f45400c070980307120318011600e8105154004106200d4900410100343c0b02c4005100d000c40d240038888481011410441c110b1500241200070b0003544880136040c840701a032041c071500c07030a120184490040b078040b9903a40d4610035203040020000c880c0d92002138030b030581c050f402c0c003000309039003108482d040780130303030409081c5811550b0001c03942002003001e590070400301c40580c64042e011818540a0300440d40c40f0340c95402c0040c108100341000903122281040003c02d500e4210380a103410001c2860032440d40c94250506074a00b8441c0e402c010111020f0811510031041a403000d2811345070703090b405000c580c40d010010f409856004401d0340d0700d03030000e010b110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 689896951 1250 689895701 689895721
    0x5010509210304140d0e0a05060a091202060c06010b0a020d0806010f030e030c1002070b16120504080d1107060c2f071511010c0509090c160b1006110a030206 69
    0x56001030140d1148203c140300f0000940c80d001702d4600c01d00220b403001d018240e9505e03000c00070000808040d207246182c0034101400400381030b02800340301594980046d800041d52503d10640e0788640c1c4140840741656110300c00d450040c2c010590309401803041900d4500310503c43d048950041c003060f101c4214001c4041803c0d0060410380549803141d1000f8488102c0030031040001600c0b501601c14010307900c004034144400c80300070003080010034140c40420310341015481282540243c142c000001401d0701d452500000611514200118940c2050392984159000c54018019a4452401003120728141d8400707075681d0880e00001c50000000701c00808016400e6911100c545494400b07580c14070303448905d00550000d01c0e4000400184080c0001d041b01d82091007001400c91890800f6403c209002001600541004003006541880800e103130015484000011004581c095100540c9240c0149401416011407160000194000d00c034071603030100100309024440e0305940a840c00b9a0384042c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 689898201 1250 689896951 689896957
    0x10f18020a0909020c211c0204081c03140c120f0c16020d0b0c1e090d0f2931030305060105070b01030c17160303120e06010806040501050921 62
    0x281c8a94000c2002c1b00060480d0302c002008552424145180c07103104406004003540140c1b01c610130810700c100b00a110140c0f0005040e01e844e1903002015819001c0c07410210007070b1404620030031001010005100c001903003c3d01500010b94181640511a580d0050441c050181503070380f014510410040d00da1140200e441000149002920000001031599501007041c9001c64800000d00404286030450544440700145001458610f05003031440709000038404000182c0014400c4031601c0414081005503000d8901a0240f105400180c0d01984000c0f1035603002100e10b801102d45a04c900c05902034900c071400d010701010200f150021011344e03816402000301422040c1030000602c0131400080045440c68040c620130b140b0b00e5100ca2400604404046c3e140218100c0354020442c0480365100740303081901200d4051070290907440d540e0307000da001408071440d1071400f8042c890020038131250004415003c0c030312480c002c001d00d03035a01401a840b1045182800c00c03017030446042d0181d4081c0300c005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 689899451 1250 689898201 689898217
    0x40e0c0a0f030c35010816120c05042a0c030f1d0d030504170a170a020d12020d15290403030f020c0607050d020d080108030405090a0e06010f18020a090902 68
    0x140004000c00c1385940041c4442c243d001117a82d501c10000c483d6040312001d9510010700e110f014180200f8503580d9071103c8104107000300390103140c1d680c0e840550341802e4000060038840f01ca01d551102e40c004040200108103845068000c6011502040d6805103c1d070440244403100317011218000523001c0c00c00000c4800c0e03036402e408001c014040440c181030301d0318812000d01f0a040041100010620348644a40400e60303155016a409101c101c0c0d01030b40209504515543c1803800f17043e201a0700c1032a0b8024041c0580e940038003860b00803030160000942c10340c0401e9a00031b0601d2070b034030580208014080300c094080103074844000d10081001038014040e0200d400102d00642ea42c00c01c14401080464100380002d0b106923000040704074440ea01440b041180144a103450000707581040c58941c0d0b00d100e42d02c1410301811358400004c80c44400c96010b440c0f825003482c1902d0042d60340c1d40d803000c01e02c80c090140010f201700c803003c440c007031410034400c84401c40d10640324041c030302c0d01d4600094029004484 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 689900701 1250 689899451 689899517
    0xd021c120b0607050d08190216111203030a2304020a050d0809090406050105010f0206060a05010f020a0f110a0902180607081e1c14160203040e0c0a0f030c 68
    0x2003400c00081050050481c17082c030b82c0c0e4542070945072003100194005510f040c203210742c4e0310400401e002c0104601d1841d0706a03401c00700c94002c01007284c0218012074000444e0807114000403080c81a01109038010002441c03501103003024030b406040510b2050301d400d07a0000c0d44050a00b030104082e050482400d00e106014591003803c1c4050318000c20340e0381c40d08480844883d40d580005108541e0425210024660349100400c20ba190105c0460501c0003140549814030920004015665208000d1040c409030310101d00c520b0788080e031030148026500714400c0d51254414101c040f0759200b05100ba502c0c02c1101d4503032100c000000c03200340403030f60748076520a44000800308000030f0782e018900544400a032205800c10799a10000c00340d0401a114504002c01d240d0600c016400000c110403502ca400442d41c0d03080724000b200c4c40310268610721840d0302c51207020342b0030b004100c41010b010340600101c8110f501c0e9100c06050854044044071900031680f0f01040300300c10803038150591030b032000f00d0400c0b05003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 689901951 1250 689900701 689900707
    0x50423041407090219080402011403090703060e0c0f060a0503070f200c130e341706180d030b0303041805010f050a0302131a120d021c120b06 62
    0x1e0915049800c401c3d04250001400c0c41d0807540601d2100c108803182c40c00d0350440c2410b0b80005c1804e44c0b01d001d04241490080041013120a046c88900000c5601ca0700820505d124503082540711b4100c002d502d0703c0381d419844070350000d05025040703a1851100386c1c0d80515581d5003103000ea034071070b0083e6003130010001c002c000008100d0450b0030581003142548018401145a40e0030802102c940b011030300079031810801049404040081d518864403903044510141c1d284003041243c0b5041d0324882010082422903001a1500e80f90480c0c90003c0f01d42001c1c4d0f107075aa610407200d101c85038522016036541d8001e254101c0080e01c6030b4420b00342881c0007000e407450240d99408041c28014183c0c03040807150b07580e4004002c0320210f502084e00a06081e55650006461030300000c94050503800c0b40b00440380ca0341d80e20100a408101c01d0035401000500c00c0c2130000500c1e5013940e80b524404101005846070040c0d42c1e14551503030a041010400729902d0401da00031a1044d40050922610020b030014018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 689903201 1250 689901951 689901983
    0x61e1509011701050a0623060723010b01020a030e09180d0f0e150301051009030506130b1e0115090b030f100b0909010e06030c0406031101030605042304 67
    0x100160314020301c862090341120180c2c0141440c00c40314003501c0400b02e41c0c581002000100d01d01c0c0c4450348111003252400e038040e01a2408580144944070300141700a010406114076000b205034105090f5140f81c00803c00c10106031b0041e070340c0340d82c0c0d0310024021814041079400301d4541101095401082006d803194401ca009074920300c1c144181c81980c0101e0354013880084070b5035011999101007041140e028418078000b1a00821610040c0200d5000d040c3d08020341509500800c00d40b801194080d00301d42d440d180c010400c06203441d80034001c60b11002d0210100f2100016400000d151407a4803000d640640d107848000341201040212080074810410f4000400e8990600658421010103110360000e1400e05c1a03407002e07900c190011a10366006002c801846c0d1161070a1a064035400c0e04100d80070741310324000903e4000c1c0c550550383d100c1d08001c0c0c0031040020708001031030035a5080e01c0a0000a48840c200000e032000c80103840b440e510340c10128001240c0b181c0f41ca030340044c021198100e4042c0c803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 689904451 1250 689903201 689903209
    0x22050403050705190b04082b0b100516030e0607141f0510060503090c03070906030201020c120309300d110a0506040204020306010c0b090303040203060c04060c030e061c0e0f061e15 79
    0x810341402340341c0c43c1d039001800300e142800c0d4210ba04114051411516020b030001030306070440b8850364098100034803000c41d0451600d03514200c52049404c5800f0501c40b003900820315a13204c04041b002d0800d0003903044041e5111055001d4103000342c4580052440c00d80c103201c01102c030303504010100d00c800c0c42003400c8044035840c103104050261030a041d001c91158214000a450440000c00302d40c000c41090145000381e400110990740958811202c145001015501c40c0081c00300201289544800400250094080010710000c5900c01034564a40d44207509940640324201d880c0c014109800c2100010014946a0b00440e404101410002020407140e101c2c400400400c450109240d40300000740000d516040000383da101030040780b13491410703040c80c4000706114103c001c0201889881d801250042d500c1ca020b8402c45600c181c02001c00d4016100c410b03000d40100d03900c002c0d107806252080144642c0108003540b0a580c12203100d03100d901d58540740ba07500c1000500c61461050b03420780740003199603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 689905701 1250 689904451 689904517
    0x102070f0b0304170c0604170f0f03090106080d0203092b0f06111602060d06090e0c0f0f06042105060a0f05090105040c0522050403050705190b0408 65
    0x40803070901c5480b441c1c140740000f40c00c0843c0318411310941d41846520040701000034615842a403080204050000340305118405001d081018107401002140ca9500b400c80c0d0409188101d8440c1d000f445115940d022040d115000810a5801600208165072060800300c681da000c010700d510b07400d02d51007500000012481440081224003141c003244050034800180520b03640d00301c0f6440900c0c50b1486410351a03005e0314181200a020720f8020480d202000505e6206c0002840c140005000d00201c250a9a880d502d9241c501c0384200c582040e09200342c145103007500d058140150015160904004a03c02d0500021640103100514a6044400142c2c140011405928401130204050b040c41d180c54041d1000180350700b00a0b85801c0030030020071040100c032012902c058514600d00005210105035050303400e28841e8041d030405051100f0954468018034443e0b00034000e42e510002030701d4201549840c0c9020141c030b882c100c1c03c042004546140d00400b0300c4007425200e61141c1000d101340d104005c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 689906951 1250 689905701 689905709
    0x2040609031a0c0d0506010509090702010c0f0201140705090a030f030806040b1807050a0c06060e0124050712031e0509070b04050d080a1404170706030b010f0c020102070f 75
    0x244021410010059207404035030800342c50190303140151812405202041c01089202c000441c2c40b5000303d2241e90052088035030b801c001501d1100e20345801074001c0c0c042c01240796040c00083c0b0109804244502c10310440c0e403a408000d2032607990b91541901143c1d5a0442c151141c0d03c08024039000000644903410000c00a00c2a00d40f4581454040c041100b1a20003c120a0196001104a000700c41c2c070b016003039610008505003d41c454107940c02c2181c42c4890707904000c041a00e0014045480589141014101c0700300012410304913003404d09407045511035070084004500184608dd0000344d0513810300004030120320700025041151007440c400003007030114a9515a5942c0140038141a00b481000060450707412001e19017450080894200306049c43d020388810b40c041809800c09219480c1782100724180241160ac441d1a0101804800c044401004892003000d000103001c5010340180901ca02c8140c582d0031417034000141c103640d2400e500c2c004a0441c09081c4010505120080c5580c000d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 689908201 1250 689906951 689906957
    0xa023007030f0f03020708070201030507031e02120601090e131716050c1c060908040b040b1201062f1513050606090103022223070806090f010605090a030501020406 72
    0x40d1081c010043c0011040100100400d40108250701c0410707a0001121302d8039a0a107030028090780e0f6082300307d00401c03c81000c241e4400c001511010b032100d854014000c0e03c0d9907418840c880342c0322400156008640d40c4234a40c0e0002c52040010007000a10f4040d940d0180198030410034004681008034250b40305050048100215031400010711a04010100d410801603840f485065003070881d803801011460b034000c3c002900c1d580c00d034041141d01020303680245103c3c1c5103252920348480514101e034120725140300d00c480b90b4000001e8902d20450024000750710303001415107524251581d48420074611051102144075080010744007204110a4a10030080c4251091700c0800e68500302d428080064041c91040c08080014000341c1c0c0d85c411310f1856442507c00d4201031103096030128005e0f140025400c144180c8000200e10441e80640c00b0b58802e03021a9a8910301d95984010455403420070354211580200c540b0050007014020b00042022640090920081c0b43ea66601d20782642d21903080b80c800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 689909451 1250 689908201 689908217
    0xb09010303080f091204052110020a1701060804171b0606101706122811010203120415110d0c090b0301030302030d0207020f3001020a02300703 63
    0x24400052609811140c0c02015000e038251a4550040500450042921031102404448e81d030b15018820b1160204480040e81d29055844421030000c1d0070194481c0c000c1102070001c08100118034203403505035405900e4504181e15607460308400002c0e10100c2c098100b00421a022076a003d501c0003e0204404100804940c503041091016908500140d80f040c440740034005c66941c1122408940e1100055400b06d000314441c01d051858400c00f01d00b2184800105150828115100b01916040031f006418402141e618080126580d100340e144d80000030140320f0218000400d41c0d007401341e4109200b000401c0718502000c1c9401942c1c003500600d042d15944580d220641c0380c005814034001c3c003080b50682c1c10340d0701d1910080e4136845610700701100701e41c0c0040d00c04119516840e08158500024000800c0c58800c0f00000e421180e06050701c3c43c0e103140c03810800c1010201402100e040680c00c1d805802c000441c00007080c00e42d003030480b0b0079010703040c03421601c21444d42c2900a000180d0290b654228 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 689910701 1250 689909451 689909461
    0x24021903081b0c062d01030b07030603200f09090a0b0405030c0106062c0a17010f09080a02010e0c0f040e03220f060801051008060a090204180b06090a12060b0901030308 74
    0x4403015400900080c0300780c85d2054071000c442034902203811a031b0054141c0b1003555132940700300c0007021035410040030100c41b8001074404401024400e00c002c1c0c41a103610742000001d4003085140b40c0104c4100b00254060205000000c5152480c2900148203104503800c155480102c0f034290b90b19900300d01c000030b8901000520035011261804c1042d4042090342c464000e0350b001113807006c142402145840c0b40e40c03090780151002d0175445003030007514001041150300241d19020a9030303400a100c07500158203085000b140700d8408544100040c100802840e401d18003041444050301100d030b102005030109002025601c00140d580482805807600240c41650500302c0003820b500c2d2580050b0200035071b50b0010303c6581c5403d2030307070340c6e02c1080d034100030b41d030717690f8010010300c40516507001901114000701c1c00140500e031420402c3c9019003050014040200303600300340400d5000e100b90b1907078024418401003042c0003080c550301407461301521011400d000f2100100d0502d1300282e0003200001c1c660400c0003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 689911951 1250 689910701 689910721
    0x3090b1303090e13031808010507050c0f0f19020a050604060905090703060605030408091c2301021303080918040f0204050702060915060a0f24021903081b0c06 70
    0x30000d00348030190f5503403500344040502021039000c0401028804560b0240610421401d0008000d101400080c441440d01e000e0052040d0040e50007113225100f05651070b035203003170041606108401080000d11403d40030a10765461130041640c16070300039402480200c1c080c1c5840c0002c10207084940c0b2910341c610b00d450180461803000a0000040615041003481040d51101c01c898009402040f1191942c800000143d403041041d07044200c42003030250750344c040203d00680442e079100a0343e9000f1000c0c95000380d0900b82d00c90301c4845d002580010304280002400440030f400703013000c050078410050f1303483d042e5001d960b68141c400303603444022450700808524160090950201c1e0600c064049820072079080c5076260040c40c5401c3c1841d40c0000050700645a0b50f882c0402002c0741380d00d030300034165105411003210482043d6000d480e803404240b2070f0030300c1c000502d013020951000144078420006480884100c003002d002c29030ba0040202c0780c03420304070a20014201014900c000f4000f1810640700305 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 689913201 1250 689911951 689911967
    0x12110f0f0d170402040518010207060e0609070b040e040303060e0c1309090201120f020f0d0e0705090f010e0919051606080c161b081605012d03090b1303 67
    0x4504108615920400c20078002c20010340095042d9030114080c1c40760303d15004040c4c006a9541403d42c80401c84030140701c60741c0c10820f2000561800ea03000c1340c80710010146c5607040c6004941520104000800a01c9907034014242d000c0c1c040e1800007603440e12030740328809070782d4280e4601003031000206444637280c3c44050b40c1802489603940411103110a0ba00207040c42c0300b151396091007180e94500480344d400082d0111040004a00441d660b1102c017107088030b000f00049030102040d032040000c042402d00b03185410300e00440c01051605942d078685911855140c40c020b01941441c05852051044c00040200000f0901c1c4100060504101e1402034044560080d5019000704010001404039060254048480c0c28400c0c44000c401060641084405141c4400008061486460b000221214081103006034295014008080b10307075503100449a407d200c00014040c0d1041c10f54803c1181c14a214400c1c40c01c4141c10003050f02070071500e50a51030780045500310070b40c02c00c1e100c400081540c09544 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 689914451 1250 689913201 689913223
    0x70509040c09050c03150607062d0b030c010c121b120305160e01030207030203121003050f0105070f08060d0204060609080f03070b04020609190f05100e010c12110f0f 73
    0x13080c1c3c21454440a00441108512003050103070708002080f070280405500441a10700203c410711440030b103a80780c0c3c841034807400b800b51501d0381e00d0824400c0580c41d020805c0f0382c4c207800580d1404008a101e07181c603407030300665008400501104001c01c1100802403a00a1005070140700526001d4000c0031014080d284c005209418103a10b081d20f01248a41141c4a8810709900b03180058458446140036803461003500540504c0b03040c050100000840100252015a4841e5007511080783c5031100c0142030b01d1066555001240c484416041018400c0400c1c80d40040c005007852403000d003e4012a00700c039220340105000440da20f000348416041000f2143c0300b0505c0d903004600e040c01070380b600750071982d01030b000038841c0340d000a64510583d20b640c60f0030605005401c20300f01d5141d03203c8c0b80000c3c29040b84241406900c4001402d0881070003001540c40c034a01c1a101c00d1205c1e04165200c0c160030301901072110030710500d0003280300c0340c0c201040010410100c1c40000d0040e402607002c420b10b00705d48400e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 689915701 1250 689914451 689914471
    0xc07030f032c030f1902011803080114040f02160b0106021f020309030f0d09260304111507051e12040b0307051c2a050417070509040c0905 61
    0x100544003008040049100302d681c1e500d50310300c407881c0c0c0060350461040c0c0c040318900560208020100c0b500340103500c0943c0c49190020840c914a4060100b03006c0120200a008143c000004000b828091000c0c25102d003402400045c07000940d03203945040340c10800d0707035003a034440d002450810005492295400b400c1c03140000c207030040f4507440151280e01c2d28083d0000c2c0c43d8000c004981c031003000304291013100754010b00ca1900d50280070382000c010072410f001540d0f88440c28442c42e50600c0c03011420141c0d148610b00300d43c175565494803100303854a02c8018590300b00c94a130068107070029410000d001010301c540c0103004095003503141459511000201c5003a181c0050041e0802002c0040890301116010101d80f0380780da8850005132828015204000a408007031040004a5a45580301215504011140e003000e00d060504a41e1740c440d44400140220710104001d028230840300807501154180001120f0340c007a00d4001141c10200e0558080b1803030361250f101070144a429009060b44191418 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 689916951 1250 689915701 689915711
    0xd0b0c09090a111b0a02090c070b01050904031205040507180606090b0c030301050d05120714010e2e0b060c03031605030601020606010c03110d020d0e04061206230c07030f03 76
    0x3101e100014840e80d03a50740d45080160b130810780c90100500c1058407098009003105028a030103002d10300075500900003100c08039040303000803509142042c800c9004e203400d5075614490708101d032140801040050802d403003d00c03070400e00040c400c1c032100900e154106c480c034000c90080d04c2c2400250912515800400000300d050100c070b81c03850000003d07a0704540088680000c6001e403070520745d0074906060b8a007440610300250640502c000c0c011340300035800c4000020080c9410b200c80341611403854401031802c2c910b80c00d1a4510700301403038078882040560183d00041c84036010002940b168040300c2e8041d09a0030200801c9500c500000d0b0611030003059040a6107180b50910000351a444000c044038144001c040c4420203140c41940c0301c102d40502c1000f00c0e66001c18152003c1c1d60f0b200907401803000161480e1011880341028014801221008566228422459641c840c058007050000981019409200721000b035100c02c4400d00480414641c1035030307075015041c0240368480b28415942454285 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 689918201 1250 689916951 689916971
    0x2e06020118020607021519030507110a05070308030603010b030312040b0c160f080904020a030e101e090302160e0a050a0c17060402041e0513110301140d0b0c09090a 72
    0x1401200c4e811681182e1080d07020707a00503244000c600800030017030710a4161012020010390194000c4d4001c9103030780c403242c046c08a01c0580e41c0d999000b212008005401043c0c0800014100e00095a00240001e0011a1100d212804a842d6800240c5407c03540e031440401d000611503610790322034010081c5c1010a10700f42c941c0300a0070400024110041281c01030400c1e680a12a40380c041e16a00b072002442555948071014005018001c0da185512090050b6041751040382010322850240d0081028480d10607500c810040005101c4404141d0950242181128158001000c0394019054140520405080824020089400041160140341d2400528000c3d650f00242e181c000100b510585020a68070031021401900888e480702c9100c00071001d0a600441c400c4c0000d1090360003d0700c1c41d103980c0a0b1204500180e900d80c002500c89a481040140b060a0382105c194941c540c0150442500f6516903660716a107500481d00710803160008508800307030f031030071100d1b207038000c80641014007004400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 689919451 1250 689918201 689918209
    0xa0b151b030406170a02120108100605040507020703030e1314070201050604091a060d02130e01180b01052e0e040c0806130b030f0d02011401090e030703082e0602011802 74
    0x100910018001c83c0340c2c0005c403202c00b650119104040c180484034520351395144560f0751180038140c0c148032181400b10101c0d0a04042c400c0602c00c01060b1300421800e86551810b503074040094502e04d400009030800380d11200840d000d800080c0182003100d08079442c1c2004001c3c00c40b000031301500d04c22801c20030003d011400d1100c60b040c7c3c2500d040083e403420b0300c52000185661010820007508040654401540706226500205607140c88500a1000741c0c40703c03904040d401d007018001480242602c006103c2401c124030f044011003407400c0c0c1c4400d03001e0030500c0d1105120301924454000707400341e0400e152500301030199000948007810034a00c1d030b0030000002224941201d95a005c095a500744044150381d041004607010004041075034640d605408009010340944003441c038100305064000a0070700302c1842801c600c080c064020f181001a1958101d404041c05803801d20302c0d04016500360b5003002d035104840103d401006c01c60303021074070301180a030a40e0701c290107180d03c0146408140c1c0158607 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 689920701 1250 689919451 689919467
    0x3040501080a1d07090606020705041e1107080403050c0a050409030801150e0a0b0409060e0103080702010f0e100e0a080708071a04080607030905190312050a0b151b030406 75
    0x81080c2c04140203503c583c12811002502d41c2002141c07081c03080001d040d1440d5406501902d0113507083d0b6452a803108140700c10341d22010380c10301c14030b0304402c0d480325001e01503400344010491941d0b44514003c1d468540010b6500030f0b41050300c190f0010700e601d500d0b62070303c803a07071074003c100c207840a02c000c1e01c00c0c0d14050000b00d014031415080c0d242c05c02c9455881da20a1002d850b6001d002054203c0b15a266513140d21150481d014900c0c2140c0f43c40008a00d0703000c2c0701001ca0480e13a100c4512443d107c2298011150803090742c1500c0140b00304000c503020150b80360303a0402285003607940c40c0b01c982100b0342c003002a0040c441d404012141c0007014107014080340400c0a200350348000e81e0700003c00d840008800b1a0f072045a01040300e0340034802c00c1c0b11486038550484008640200101d806030011040c03214111562400300401003000c01d000920030400325041668005035030003001821200010110364134001d4118400520240002d60f503907041810310303000c100010b801e00118200ba0600c0ca014000300c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 689921951 1250 689920701 689920711
    0x20d020405040201050f0a050d06060c12030218180915060a03080f0d06060504090f020f1611040c02010b040f0e03070308040c12060207030f030c1d0a0e090c030d020304050108 77
    0x41e21a00001c0c156400b81044420383c0c40c551020a5031886c0910006089030000036900d101f144c10420002400d40c4a05c6034072f90003a03003106030003600c00c0c2c0d0f40714240c0003507105012180e5005c82d4800c000f00130396030703000c1400f46260418050074124030f0017884141c140000c0713a00303990401006130188940c980310340c0b041d00305807035100381e2280c0e80740d950100e10217031030080010403d2018240300d0003180c4542c0c02406002100c80310101071002550f1801754405a00400c1d00c200f110210500c5040000100c102c100c42086004002400410711850027003030a417a10f062010000d41c1d1610020015400c00d440788004628241c281080780480312000a0b403a481500006020406810042014031048030520001032415501c0d05502c0c0c10186810006034004120940220f400460301002090107030040f002110310641d034107a4601c0c00d0520700d42051342c50b800a10342041141d1004034003c00038103080f60107100c440000308410250142054074001e10300000a046400521041203103076001590a5001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 689923201 1250 689921951 689921959
    0x6090f0e10110d02130509070201020c031603050d06032015030703090201110706120c030b090a23040c0806010605040311040b181e07030e030417011d0c0913020d02 72
    0x500150b040e00490051854071001c5503c00903a19002020700c1000804848065078150007036560342c40280d0807805020044025a0010009004224032088560100c14842c0c100306003000c4200c0201d01c101d85864204590b0484030501341d65800c444142103126000301203403154009003138201101e50f00d000c042c1000c0140b58503540901c1c21a07000e41100c0c0340580c0000111241c0350382c0c03800020401034804040d140c07001e141c01000030b4801d10a009035001c2c40c0c000b6100341e03440e440b0322083c14000d02640d0300040d004044403601d103442a10b1030075402c0c012802070404021403400c004d1882c4c107000069008100b8031004110800004042e088424405041220001901000f0002140c80f507880d50072460510007600080000a185640c407426084a4440e020a500e95032400143d04403241c00c6000071096205000c03c02404481c0440c07481c80307001804c004101040c640102e0114880d5010001c07100e50042459000c4605200000c164003041a0402d1680c0352025004035030140d000303800183c05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 689924451 1250 689923201 689923211
    0x1211070b10030215041802120426130f06110a03050c03040b04060507121b0b04050102040e0907090507260402010c170a080603030328090807030306090f0e10 69
    0x5000050100055030050002c0b14564445284c0200c10b50050241c040d03412181d1800c043c0e100701910070764001c1303840548481503030b44807600c50b010110004c0400301c1031102004801444000450040d04190380192201d510f0fa80c180072640c0050301c4590442c10410111680f80b07290030b4400621102140c0c0c050070f00f141e442119114090441c0b080350009034403110002400100c550707000c002040745600941d0741d11038003103074824100c0306001e4542d211164000414801d5000c500811603042e0007070300c41c0c400185803542c2e0f5802d003054490210340b503030078540201404204100f0a8003500303510540f076161020301c000e00000d4444e00e183c0004180d130200781681c00003400b1a4080c0041d40000c6410211080d0080500084208950722180005000070070480200da02e0303080000c207903400351201d10b9031704001000f0301a5030610800280c030021034554030342c81c480c0c01003283c003801801e4103406582c000c40c5541c18140240c0c00d4660503d01c005180b40381015a48694601007240340c1859481400030074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 689925701 1250 689924451 689924461
    0xb030c090a030c140d020906040b0f040501030311061f060c02120a0822030f1e08030f07112409010603140606030f03190c020105040e0411011211070b 66
    0x6809a40e120039089003a604010051040440d2608101c400407081c08062041c0c40c01800400108208002d4025104801007115032a090b08801c24068001d8003e14541050000282c1a210282d0040c3c0100e407040100c03e90080d800e20000b40c2c030200107003500542c042c03800e406004a802502c1118204840315980400b190f0795200c050303002c0c401c90400c440900342e190030000c3e520340c4041c0c90758840c0d1000c0c84000c1500c444c141101000c407900300c11007492030046602c0700d81240140507050805010703941244000504c68a018600030304610021031040e143c0078201800c2e80c0c03000c2c4c002800341e500c2148000c61401d500d0411140d500750b44060030180d916070050250240020f03420082c010303400d032106140c10351000503071180700b103008408036a9010403456489441e442400011002142c03840000d10a040c01003207800c4280340f042c500b00b440d2550700d603009a80004151030803908000c0124401e0815a88040b041c628030507800300401c43d52445410300c00080c45003000050500c280100020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 689926951 1250 689925701 689925721
    0x105070b130204110c28030905040207060b0603010b0c1006140d240b0405060603240d140616090f0e2a190801140103021602060d0b0a0b03100b03 64
    0x110b0b03040345031041326190074524100f6521110411150710306801e642003c5140682c2000650f46116010f8540006450400c41440007035804610203440c0503440e1800c80070140c880400a41c001c141c0904007544a03e070302070809050100366041605e40710306124042c000ca05005010120310032040b160100c8050b6035181100800703014400074612030a4082030f1a504940356001012800c5080714100b2183d0385072000c000b40c600042d590002814400c0404e0003140c032800c006101c00c910018420203410703150b55a02c03106240c568410307900c250801400c0c401c4107130f84031214001c016120b08180c0c0c4c02e035040c1841584c00c0c01e02403181380851a03001c80801c1400b8140a8000b040f00d07900b46888a036007004100f02803103540040c0300301d10103290604901008030300c99030740e642c10799410400ba200803185040045000e900421000401032003054884001603440c40010000d946141e4004181c0466010803c10060b41319844400c07161400c000700403d006405529809840c074a003202e9440341c40c0e440c0a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 689928057 1106 689926951 689926961
    0x3071b021905210c01111c050712140d020a14040b030906161707030b18060321070b100305030c0c15070203072105031207020c0105070b130204 63
    0x16251b11440122803400305400849003100760003c001d0040b4082461030300081800000c0040c10030509003210300c0001074600b04503c0e880a009038002c4203100301c03641242c0050380080c40f040c4a6000b00079480d6484071220f0240d44581d1a1022140c4c4d0350300c00d8900a005107d103a00007a01e549001b5400c039058002640c41407102005002088000103000d4a268281510f03440816071545070700c19606044c179413200d0780103d10f08068040c58108005001038207010006d101401c210325060b5400c41d5403050340011403036030959400300d00905103502900004e0003400000b52807210b10a0004090302c60341c0c0d08071002c10741210012001141e07407240c00d40003034045d00b044a0810080742c0b4040d00c2410180d400b00b91900c1c550003552120b056a21240104c1c106201180c14130195036810840051410003c0c20024580310640d118441240d070000e014015032201041280115107468003c = true := by decide +kernel

theorem cover : BRFrame.Cov 689748201 689928057 := by
  have h0 := BRFrame.cov_init 689748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 689748201 ≤ n) (h2 : n < 689928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
