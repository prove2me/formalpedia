-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5226
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:10:07.109145+00:00
-- url     : https://prove2.me/submissions/96b03240-f0de-4948-9146-cb5f2cdd73e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 939748201 ≤ n < 939928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 939749451 1250 939748201 939748211
    0x2160209070806040b040603170a050712050403110f130e07050402210f0f070804170318070602070f0308070f02030615010f11060f0613020a0206041101092106 70
    0x1030356035440d06401204156a202d500b824240200000c813541c80310303842d104525012003000020040052180a0040c10404644400003108207454a21403c400100003450300b035400c40007035801c000038009403070082d40c031f07403003855075440502c02916184018107620004c100c1000003241c4558104280c03464080090740c00e400d40da80080b409a800c550382d09550981c1480302d0300d00c041e0b1034007041c135803040114052103502d043c100302c4c1d000f4885001d450402009880800141800182d608030070390080200b400d140d6a150042ca6945c1e2011044c0c109a0b542c042c49a0004400d44000b13034260664000070b844052071841c550b54401c01e9400340200b100c50071850760322403003d65000d22000740302e031814055541c1c034980150001815140e072503580b0800d010703400c502d10301c0440001a1842d8000e28141c011405a210b82c00010748100d03960100030b520f03500001c0e0130101164013084541c000c611624445250500300340040d42c0580381402629083e180f07005c0c2c5100001055405880640d020b2040010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 939750701 1250 939749451 939749453
    0x201110a03020109060b0301020702060706020a03270201020601091e0e010f15090501060507030c020405040f08040b0706060b0f0a050a034a03041203020f01060f060f0c0b07030216 79
    0x3061082803982a4050303591000000140101401a09003120044000f18a4220700d41d002402c24003c002002d0078503070780411109070050081d4044a40105064654500c2c0382410408416900f80c0a104a005005900c00021280c14034054000f0581844414081d100c1c0c070072515200130280303420b28414035900d80a0350091000a40704d007000200e404850544030b5030400e0086010780701d042c2c0c0302d0300030410200b01d05008aa4030141c0ca9100d154120b5011410341c440341040c108012046601038400342000030001042c0304130500825005224400a100150380e0f40c0c4a000075001e00c80108607440c0e01005480c04181c880e1000f44000c95050030001142c03580c90040c1019501180b82d1850400342c1e05140402c55000001c14654801c0408007000034208481c5440d601c4c0d00851180003290b900240300030003014001d001c52018002c9510003007107104d6980500030340ca60380e02e11804020850401d405104181725106036070844e80c00c500e01e000141c4581004400035488540c2410341001c40c0d84443c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 939751951 1250 939750701 939750703
    0x60f0103023708040b1810061e060c050d2a200405061f120219091a041401030f02070c031e0c05060c1905010c18060813020111 56
    0x782c400449400e078911440c50b203202520181c0d902e42c001a040c00044030411001949168616034005d128020400055001071503051806103c0c0c4a041c44442c00d000000c100c00c01d0405c0e10240380a0f01420751307007103c0c3d80c0d1141500c0080c92883c0c00360140d0800c2040000131130050000c4010156603000908100031040175102482c408414100c0c0c1d030100c0701c0c50b0003804d0451072082440540c030032101007256040030380014600001400c0609035060b20350080340c2c0410301600d248003201201480940d0340307502000c80300c4418000b0200d448042100d09070003155410800d503014599041c0e619201d85440c0c00c0005c4031802c002904e0f0418101030f180c441400445031140007624125119001ca003460341c0c06c5203000510054021901e14401e42c1045510022035680c10a12003160707411f40f200350741c844901c103059040606a165100381502e081c4945020000150f2041d410b20b100e950341c0550b0a40d031001541e84100c094411031000810080102c2c40301000d410a04070150f01c14101300c40c0da080500c1d40d01d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 939753201 1250 939751951 939751987
    0x40f0b090709150b1c020d060f1509060804080c120d05070e030f0d0507051e071406030f070e2206080714061912020f1903060e060f010302 61
    0x68020768800c1001d010180507108002407030b040121801c605010b02c0610314098034465419105114010000b550000d504840c64409280d4081c4010350301c64012108448946c400e4085424240900c0021507118a00b030340240c1d00541e440350000d40340c580b900011500644850ac3c0203000340030b5100804a01030004000304607099001140c1460704140180c2601c080c450542d001c0e80003c85185581c031800710b0507404004442c108507496001c1d90501d6840d10b071074529441c1a8088450f20615098400912a8202c41c4100314a0418522500c00d1220500090b25420440404500807a542d14000d02c6045181c50000d000c044144a801c0900403e030300b18801014013580c3e42d108284890001805000003800c03902256258220303074400801c910b03110301d01d01d0b8041d6a142e038802c0821035109000031024108074840540d2034000c440d2260040b503011240702d9001800828002c0d207074034000e006820856072944680501540c42c0703401c1c0848410318402e40d0f030416a08102c00000d6544034029 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 939754451 1250 939753201 939753211
    0x718050d03031d0f06131b09090507060c021e01020c13020d1503050d030c0212070501020a2006070311091306420306091e06090212040b040f0b 63
    0x4041040d103030415200307401d01c0c114401002c460f044010509880307280081d0480d00041b4034000a4030610550510000c1201c0c24141c040805100a0b400a4502c0094100c0c0341e50b0380c05035094880c125a1110309684847c0c180000139003140d0103104404808540c3c2600c14580601801500e82c1110709100051440c42480c070018007103607010840104907080c40c80303504c1554450070a0360b000d1a086031906641c40c812581c100d01095100c0919040f1a4402d118020030f10030200132181c1c895009242c004e0107500591500800a58010fa011a00740940103c00c2d0b558506000544240e80702e652040b0060903103800404a000d50030171203110991070328520705980c180c1e461000a4084e040c442c665240c3e0741040782c0c4040750b0464814130240c0e2100c2c14403a550919110b0040c00c1d000e950484141c024110b254480014240342c11403090344029404003204200080080420bc040d403205541001c0303003d012081c8500145010018001030303585640b0541017801511007441409541d60b40d83c0c5200e00c00c590f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 939755701 1250 939754451 939754457
    0x301060f201e0d0309030c0605070c05060403030507031a0f1e060c0303040521250c0e0f0106020313050402070f060e030c0d03020a0f0c0c150e030f03070b0718050d03 73
    0x1101050720406002c0f184049820340303400c0c050403845440c018000040001d010b0401c545d00c02c0030800135401001185452f55014003620600c0c545810040c0040108039594808642090719400884422000340e0a070640010900b05801c150641440040400340011804062104000080300c1e560800078020100307454008654904c1c061500b2410000a403072107071001c250400c144109000e07043c094890320096114250740001400110b1000403a51003c00703007a060000340041903502c6651740301d520540030304a0b100f007075999070300b0201e0341c0e8401c16800310164500f03101c044c800e9103050340052079124091403103480310a100d0f840720b030215000c004200040354800190303034203010b03002d05c00d4001004945c1411420101d19030406820b004000074801d08020035495098100201850f1030409018a0140300e06500007030f00e0080c001d141640c054504c03a00c01c03c4465042060000222121075501c0300000a803612510402d81d00320009010101400680d2280421a0748500d0041c6280c10f00a135 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 939756951 1250 939755701 939755743
    0x50105101d1e030f060c121015050304120804021516021002030a090b0c030d0203070309060504060b1c2d06091506170714030c190611030301060f20 65
    0x1082504e4000c0e80508005260020380800c003150b0207400c1031b103a20104001d8001d010f40d4504490408000b03854004241001480c4201c00001b5849000346105522444d03040200d05002501a16071580840e0000e42c4103001c039856100b1110702c24064440d0740383c1040342964444c40782d80050303a0544503490030340050b440424043c950711b031300101c141c3c01440f00c010741c43d02c2c141540f00400c0d140d101d600c080d4250280c0000200c0e0300c181c800c2c0e00240b845c0d504108100603a081500d40200540f640c1205244181410b01300040c4003160107843c0780c5059070144c3c001c8240100403150160f1441510840d0b4102e5115000c8400855428002d24050034440d044100410500c01c16600854000350464417051150701c200300c402140000e4984203070b0710503804103190710390b251001a03d02076144120075080324500b48500d11003004030710400150307145030b00d60b9a80079506080d41c65880c0424403481e00010714600700001000e0180714458096528540241480c1948608480c0b92110000254100001c0c0c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 939758201 1250 939756951 939757009
    0x13030e030c13140609010f03030822051b010302161704050d050616050f09040b2b11040b01020a110a09020f0706110a090e0a090c08060910050105101d 66
    0x103c007110740c0c0000200c030301c50055410326003940c00682c0b080c0002018421080c0c0420380150200b010018000c210805500340d0404a18219440c0c001e01208104685240303140072883d580a402983c41208540c0702c07856005038551510110141e03840c2040c280681c0c01c00020030261903c802661846000e500104400d08102c6800c80441000011250800105000100c0261601c00480d504100121004202c1c0102e41d800100000d45540b803030a83c86200800803e07030a040324038010500d0303010f0104d904986925500344002d03292850443d90040e081124280c00182c6110441d6000642c090003401c4001d85841da070324100d9100040080641c640070420904000d042d01400d9403848403022014107021103400080d1242500b400b5095043c0003000000b00c507000c051344042225504a40d030340010b01d94440c4840d44801e810744892260b8080d03061954800c00190081c0f078129000a00300d00d004410761081104d0700c8003108240d00315642074103800c0c0382c0c5a460000c40508804000c4880b5003207190 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 939759451 1250 939758201 939758231
    0x120c0d1a1507320f0c060712090f06121a030703080d11030411031006081c020c0604030c0512030a051602130e161a09060702180a02120a0513030e030c13 67
    0x40050104c21750012a540c49075031501e03001d07548070640c8101c07114602030011a090b214804a600404c0c40040c0d03400000481941c40101c1302c4036800140003c005c3c04180c5c14441d150350034142e031001c0e0160301454080000802c12002002004400c010001e00c0b101c21604d0700d45581c0c410b99064400d8030784041109003500d0140000620300c0060364041040c1803a00c3e038155224002c5400e0061861100944016a14003d100f0020303047c500030200fa40d580e442c0d20f04900d85541a00500e8080e1546010705100080c00000b150b544017050780fa55406c01084190001c07900c4e42105040b0380241c0d03007002c80700f61420640205002c5400e2000a0000d60003900c10383c80590341030343d121144000d0001040081c44041c07404440c4040d000341c44140c1d981c42c00c0e0020504202440c5903a45220881c8400c12241981d81d07400740c0880700381d0311105042030719a038038170805551050301d05d00b0f1701080b10403403080028007072003200b0000030b0013900ba151507000c0c000000d4036410501c6080010592079055035084081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 939760701 1250 939759451 939759463
    0xd090b0f0606030f07080c071b1509180203070e0d030e130606080414120f0a0906030603151d0d081e07120908120c0d1a150732 56
    0x101c15100700b411460485500340c08240702901d00710a00450801040a4014200466134400e422010f440316060404a50fa000442c280c41010000000d150500400510556125046444608216041090052191000350310281c80c00c8180a0381c501c580255072101180b081c401400786d114040310038011307018001004c80c41c0014840092170400c09200ca00c1c0c000c006203402c20703040f40c0640c5501c0c5d004100c0d00d00d0b1002c61038410300c5c0c1c0a0003046603013400305500000c0440030f00640d98000c01c44d517556019030030b448030790000400440c03030058000a109455400240d0b800900b003421f0001e540301008203810000d00ba091070002900e01030070410154480c205142440c0301c41c91103030f999840c00140c02441d10627580310b00400140c40e80380304030922080e5429905040d0004205403d541481c01c0c0031005544900c8640d2000c60030f00d075000c20000c3d4686003140812002400000d4401c50301c507000d48165100711821140c070301d9003440302d0007001c1007c0740c0c10010207942a0000e0044090b415005d140003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 939761951 1250 939760701 939760711
    0x8010c1205160305220c03140102030c0d0c0215100603060509161b0b150102010f0e06010b0703091802030f0a0b131a0306090616050712140d090b0f 65
    0x207003001c080c402c00300c0341400e0b02c0601042d1440c0010300b41c0c90344603180351039002c00c5a1400800392410700350014464514610000c981c03050ba1a078503203040e04502d0a081c1e0004a8001c903014509101c040542c845e5a04259181061031065494500840d0030008030384605540100311041001c600780310300b5401d849420f0103050111801c4105207844402604c641804043c00c00410407016800da0210008005000000d0362045202020f407070b000c1e4511031140783e65506280190308203034008031000c0c5244580b200f114901c0000e0450b0768207200d50a1b1079540145400c0b02000990000040d002450180344240000c0340303d40941d0381d0905494281159001800c000c101a01d00809403445665a160404100b0b403002000304980b450062498014011200500d425029040c2000411200030550380d215982e00310b02c84aa000824400700d07102c6c082c44000501500d803184a825146000e410540c0e541142030040fa40f03000196044d00090b00e200315030450390315583c0b806002100b5502081181d000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 939763201 1250 939761951 939761987
    0x103030e030d14040614070b010e0f07050a080106181a0307020111040e06130f0c030b040e0a0b011206150f03020130090c0b070809040b101e120608010c 67
    0x10020003d0b20248511542c410142400303900780c844140e0601d000e05035605141c02c6503c4001c0d66946803e906441c12040b56003d241c440794100086400d0b00510944500c10358030b0780c80000c9682060810340c2c8102403080708480810104c0c800007266850801d91032081e02e03091260316120701749070a0180c2501c07011018a4108502400140500b5200c0a02c0c1a485401103c0e00541c5008090b00000140b000d006c4807904941001d50b294801900754210908076001074a0400c001e4034a0010191540546607006107140e0340840100a24081e41002012850185000056a1508018450203014594040800d40900f01420425507800010100d050301d1641172450b5501865410034140300c5401105201f85643da00c04001407111a900c80780c0900204d03088582d44000342c0c20900000e03008100d40f6031146080c0742030300d543c17804c080303402c110982c08a13220000e82c1c0c581180c4c4500e080384003000039000c00018940b4070a200307045010301001040c640d00009501c3c810340d030f0000d22801d10940d64240c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 939764451 1250 939763201 939763217
    0xa020f090f0705070609060218090c2719030c09111614210408010f0905152d010305010b040903020d0f05070f0b07090905090c010c020f03060103030e030d 68
    0x1106070010030380c1c005098a04a9076841c50341c070b40703240103000c202000340280f440815144907500000901c90f0b822013084034900140e83d5405801c0c41c00303100d0070b0b140b0407001031481c14000000854402d141c0c00d03094000e000c120315003d61001090100c290398016079a0340c002c1481000742c080981304103845084202c84851906004030320700888540c013080003c089074690703029103080e4481400b149141e6400a1002880c800d6620029003c6801c24028207020354600104004406118843c0480450340315002d070600d2000c420100032061001000300c042c1a03d4103036405d0b0404c11403407504400900060300103070380b9411030034440c3c00c44000c0f00160380100d20f01100000403d40001c0c81c0814400589000024170360000700c112036500030301074014100c0300301900b0202000701214041c1c1c0b0420880c0d8846420715920b802107400d440040c1d0304004e90760000920300c00c0c1544a04440b400d02c0340094140d1549620b0031012920f40a003d034130540003d680d030304180d0351618042c030034a203d810081c944501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 939765701 1250 939764451 939764461
    0x117090604021002160605030126060a1e11071101230a090b0d09020405070801230d150506100c0507180b060a030204030320030d0b12030403050a020f09 67
    0x1940d0342000e0000791049104084211426100304030b40e080e25101c041035060700341d9403600054002e030028061248600c03078661001c035104140e8110122500b01e450001d10440c0c0742c806c01d2100800602460420403841414006002800c50007500000307014206140e81c3d0314034a092003070b0841109080f1f10b04000c10701c1890705c0d03581e40c546690381030402030000c540d07501e2042210035115400150700c413244038140800c910103545002c2c4d1002544500983d0240700f150f8800000321401c840c24007802005074415031007a01c481c145400b240c00704a20160500c1c1200d01d85456845084c00600300100c19980c03100d0410075a030a11680d4480c50348560b0410718918101c40d40c1c3c054691660b40200260000c0c04088048031080940041906510181c025640c514920b203000b070181d4860301069000c01d03640255046581e501d40740c1c07100361400d41005541021043d407a0340c40600021480207510060a1215246240d070510003000110b2080b0018050000340d0310520050140c2100601d1043c2c5100701000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 939766951 1250 939765701 939765703
    0x3030123030c090c13080c0901062f0307020901092313080706090212152a07020a09020c0a0c120b010521030a0e01110d0e0103020a050717030402011709 67
    0xc15909000c60f40c0c01050b07a5480e1208402e4001d54201600c21080020000b440e8200450707414401d24054450310303910382c0c8500f000d88200c0c464441c01f506a00381208003191f0f130381006070f9403144102c142050b17074541b03481c5400090b28000280c010490143c1d68505514050640014a01e00c00303076802c0c080351241c0f40400c0400118a00d0201c050461381001800c0b10030880d40f680140326803540244036280c15405d0444d650b5880303d0150608881b2a00c0401045031008001d403084810020f54181c01b8011800c1184c4c0000c03508207110807a040300a40c81d0104039201d0328006000302c02c1e8943d00524640b443c506084075070120a0b800806c41c0e040f02d01c5001c020071580000d06055130300989016100400000480c6060202c3c03032400840d034000481c100103045d500c5855000222002d980340c0304032a80d01407180741c03640c5840d03003aa0041140750000c240c01d54000c0d00900242c0226090403410902035031034006211888404400440900204002c115a0480640d0a10700f907200781c5450b0078507000c0b1500e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 939768201 1250 939766951 939766963
    0x2a140915040e1204120b01080a0f12020f0d050c07120b04060e030408190b0f072a0501150306243309060207060c08030609060409050a050303012303 65
    0x56800381d9194030780840c0010041103034000d541e85100b40941d85039950f40c20000c10300b584550844010140341c000003038040c00082d0f14444580c005000c0a03000c0100c0d81c80c040020805465001580101d541c0140d1080e414450300503420b1039500c1c2e1955460000c1501414944203401541c4040440c2c61201f001c644680c00c4540e00a90080c00014802000d409440c514021070344410040d00ca0100d020303003c500d0012070903049511620750010541c4550b030480310100e004035a0400082c041480100e011000c2d03003854031000c4003044c0c50101d040740e6912014250340f00c2486000e009806081d040003041020311881c001c10141011460482001420f003007080c07481449800319401900c0b1146405110b20004540c40000b4007142d202c1038041c030003014058602078800c02001d4041e1340000500fa41c02400c00300c03403090348944041e1030356403090304020351580060801e9030001e9a42c0400340006100300300c401820360141004588940c07605503541c041740c80f107181d00d8100181c1501c0b01c0010362000144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 939769451 1250 939768201 939768241
    0x5011d0a0c03140109061a07081c060515031008011104060806150d1b140904111603090e07210b040e0313090e0f0d08042a1409 56
    0x2089030101d911044010700110205001c0c00010b24000140746481c0b58806030489108000703480030a204901070340840d003c0d008010f48460000c2000c0d18001d5110700020790520341c1000e0004400e5100c2c00420b00d105803000da5039507490000020b100d101d0342400483c0c030042100c44000e01c00d103000e40c0c522442900451052030107010030480810002e50345c0802c91960110010001511030002c0a402d03000b802d5040e81d58500c10344510910400e1610401c1c0c80c44a29800c5080c807850140341c503050000501c0f19142040c0100d9042c0001158607106882651000f800b079601c0248460070070030740b07048004010b440881032251f486180701c81da0716880b4107010058420b036400070311711035401d0104000d403441813900314041c00f00095030009416403824070700a448902c041005202a454011540c2d0740030007076100102d5101c03100000e8224030401d00140d0244c8280e0041e007075410307258404454040400c84035201440c10b020280b10008164000900000d03003200c80c1c0085092402007a902c5802082d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 939770701 1250 939769451 939769471
    0xa050a0530010c0c0b0601030b0604050607050c0405071106150a031716142a0f0d050703030807080901090c0e070c02030712030e0303031b07030c0203061905011d 71
    0x1c151810380300310421421119840a0080c050001d0044004042d19191102200c6083c081c1c00411002d5200744290080441d0140079a403070103080c14104603182e04103c10844044c4a24843c0c1302e91a1540e00a2a01903542901c40e5274002c00d50b841110f080200042900340b890071803600d0101d1a030b403112482c034100d0350890b0b03e000000a003411070703484a10030b1708144410101408061402c1090300c210030156500b54000b61400103030418500c04940d58103900307081404600031450b0085107440e4013074403c200c000030010780d40d44507250b8030a0b007410300c5503005a001c81d0703000d8108108241c20080082d4881a818000c11022040343e0703d04c01c000c0b516000b2400045a078500141400d0300503a0301c641e070207800408031000980d4030442d103030512103944801c030000361665580591034140042500c0c000c008600e503110b0090102c0e400c540740c6d504251025010801500d4101d405038405100c80e50198064008403100c10b0b8081e0b6280c01a01e40690012078200191999034680c0e200d461055500040295 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 939771951 1250 939770701 939770749
    0x160b0411060703080106020601052d19091514010206070f050d15080c0d030c06150b040605030601030b01020f1b061306021c0e0f19030b01090b0a050a05 67
    0xc00c0c502034144903035210a0700264000341c8407040c903810004881c100c540d1a400c4446680e02c17842440010601000c00846078604014030506403103048003c035540c0c400180c100344007216a0718280c844c414155004005280e41e134030701100003190b00741c0f1700c101034502c100d9184d1070400070100003075441600404c85400c004000c000103175a14461380460720782e4424584240421200c01015240c14161031007000c00780c0c030075402c2d520b10394203010354049074498054450000700700e00354903500050b0040e0306840018a80102d004104020b10002030701c0513040a944a50301c0e0301c0c0100001d41114066030310241075510101141d08003110002d040440c19990000a01c2e4011650021491034092164007042800c008040407401c07550004001c0060012444024020894981d00303840450a484030740c2d0304004800065101c0e801d00c6150074400700c0b41c1c020500760003542c0b80c5030051585800c0e080b01c83c0f0213403102c9100c0043d10305041030304068002110140714051522001440040b144081d070000e52000c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 939773201 1250 939771951 939771953
    0x2e020105040b160c02121e06010503120a091d0103120309080405010e0f18090d110d03180605090607030b04020f03220b04032c242104020a0803160b04 66
    0x20780c40300d03228140d01801b00c01c0700300c1c0909465902c41c032031140407003e00901600c0064481400003a114100c42014019200036001c02c107400c2d940f90301003682c1d60203003d0740f4500000c2d4250381e205040f142400e00940b9482a504600c0d0510211000744c060b41c04040c102440702e408030700c070001181c1c1203d10900b4141c200205141c04901410311050801b540018006040c820040001d10480d00c10407010082d104e403c401d00209640d040c80060401c0c015a10a11010000a0207948001065503007004141c249041c02c1d600d000c140c913000c40e010149904008188440e0507018003d000e90414121070075402c0134014505007251b40801040000c40b920814401000d0002030810080d8541d0031110a08540c5000c2c2400f901807500814140c81c0c5803810202202008000c103580d8100080c000c1c1040c50103041c0652a0300801e0244420340d580000030400cc80340d40341000009c130078400e240860001d451816004111018190ba4025503250304200025810759040051414099500904101d8141c582e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 939774451 1250 939773201 939773207
    0x11060a1d0310020301081b10020a0b270714030c09160c0b0109061404060e07350108011103060d0305030a0b120109150605010c0803152e020105040b16 66
    0x411000e80b1250320003c0045030b12100407400321105040c0c1c5103107000c1001200c0c180712460704040c040e180140c102040000c0020b2104030340540001c007480c01c5880c69540024042d0b141e01c03502e0b1048007035034005030080011441c41c0542c4000e288044014200f1821001c0210b03028441c0109554102958140407034105809208a01d074030a0300314440c540d01d0340e1182003000003001c26004468010150901050721480c06000300b42c117840e0360f11455603a6445e188003d8420140421003200755030340c0b04914070010000d144840b1480764280d1030080c0c140d4544030619003104c200300c0384004100d20400c104259a103c140484c40703070560502c0d207144d40b03684e0b513803040000b0001d01007090ba1082d105400020f85603c15001000014007a503184e095419000003a03408481e21485a10302113000c100c040c1010880c40c501030b560080706503907101c4110700000d0010702c020700303a00440f40b03040300d1806140080e030030703a0340940f624100540020016810603885440071804000e0004206150a0301200240f605c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 939775701 1250 939774451 939774463
    0x1302030603010905070f0f120c26030d0b011106040305090d050f07030f031b1101050708120103080310090b01050403020409050a0213050a0b0a1802090109180911060a1d03 75
    0x50080240d500c070940340d1006e10352818142c4105010105d1b8072001288058400007400445a4455200c4500f54903009202c103035a403414140c0d095a515800b0500740d1614144001c0001441024000502c0101d0784000f61203118410320718152607100c60b08010020760000c0464107134800c100c40000d00544a0302e4101c0ca041c2c80340c40340c8265809023030800801c1014160076149150303c40d444801150080c5841e03003461721076000307016210081200c6c81213181d500603001007d602e405103c4280c40c04075200c1054030700103c2a8003c403920b0800208000d01e00306007240c0f0354040c05006000b0301c100c04070000000c2c81340c081da01000c0d20131583c50b032000003001020070482020f5a030107031490440103440300e0580000c20b0100e030441103240c2881c6c1c0c1340d8910724101034030304180c0300000c0a042102c0b0102c24488000d4102c1116181444448000402c86204440d02d009801b044550080394148540c600f0050510650b441c180c020394060290f1143c46030040400d180c1d241117810099950300e03004001901d458 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 939776951 1250 939775701 939775703
    0x1d010204030302010c0e040905070501120f060b0301081507020c010e060d0e0c010f0e030a2006030c03091507020a030f021c0203070b06010c020d080c10020d0b0301061413020306030109 81
    0x5880010000201601034100a400d02d10580303800b2900507400f404d04c03042d5110302000402c00e41016600340710960044201c100340a4128000080192068041c4400c4861030740001c144403d01100400c4a01400c2091460030b409403108656a820b0205010350788005500e40141070103402c000e20003460700c41c8020398514103014103080c0042c11a001040e61a41180e40c2a01e00207240503001b400941e001302003000407118080c0080000001e9070f103d41240b502c5080c0c4032404140c030040361842c0b1740e5924000d1400789146d031400980d44d003010344c503051400c211030f4039003015042614104004d054000c54800300403901130030400da1354000351030100c0c240b06051034100207007604004042c0d00d180d07001001e804500e101d4240c5045c03c0d180e5100540b4145c6118000950103980200d221001076040c030090710122446004403407510500d03035081c50907a040514400c90496441400454510742405640b0040082c50345c0e00340242c1c0c117400814050ba10f80026030b603c00750004040f401e161005d40c40140c8071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 939778201 1250 939776951 939776953
    0x50c072d140108070201020c0304050103090f0b0f010f0807030807140f0601060c02030708011a011d030706031a0109030503090d11060c030a020d03151202010318052118041d 76
    0x925165070504036400500c24440707001075050000100003134014421034030b007060040021410545000300450103000807003404c54040b01007545a1000450414030303a8001d20b0032003289a000d44c18411a5100d042c69039100380c40c039038400c00d0708001058508045400c1c81d500003880c003d50302d8041903840e1500c0c11b141c4100d8903e2203003030000035017558400c40e102c00c45807003181500c4115030741e40c02e001d0a031800070a1072021003291880c111219030054902c822012191070308144901000c4000a0500c82107a0007000880d443c1d03d00140d54000c0d5549a400c0d03031809003400a54603085032503207a9a409000c00060003402076003210010700503c0303000e0700807070a0b00820b0316985072040c1c817030a030316600300c0c030700c0d090240c03050500ca40d29035800383c0500e01d20b00502c03060004c0400d140c010701080030790b44100113074107060340ca40c140541c42050300004421580140c0c003c005101c08814080352a098055110103206001e110720001318007040e601242c610f80031100850190041002481007030589200a881 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 939779451 1250 939778201 939778289
    0xe030615030f010203360303150424050108060d0f0f0c0e040305121513150f1a0307031409060f01140d060f02040f03140c01050c07 58
    0xd000d419440308900c4140540a444482182041c01c5080c0d000a03071311070031703402121141c10018442c80d032440f102e007604528491402c140d0465140b421030703005941d650300d01405084440611f003064050525030022141c0e207600085400c1e01c44074040d005902600d410403003c2004111243c1d100000381000c40d030001220040407240f0f190440782507030300200c12100502058000500f8142c800525486a40c260300c4480c688100603075084200c0c1c030f0041c2025044a0140b88004598803001d0008500c901c481750f00044150b41031844400c00c42c0075038480012a0745001c014884c0340340c00b01611340361000d140003140d01ea899028059002e0b14044409900d941501c2d0f0810400d004001100e9000fa00088800e081b266243c200509011150041482d00090811000000101c06900119a6140303c5030010300745a2074840c05400203803580d10544848200b8580c0240510301409041051b107800d081152500341000300d400e0300d410103407094140f01060791114180c044841d0030755500182c03450380f44c081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 939780701 1250 939779451 939779461
    0x3020709020c2a0105040905061804052d07180905060f1b0f0f03060d0c0b0d0f0501060c02061615020a020105161b02060d020a03022d0703030c0e0306 66
    0x683d80018007007026151032103103a12400c071600c1c03803804500c0800603074403035113001e0030018030134003422000d04040e0700401b030120300c0354180b00740b050014007540c40b51018240e00046158034035002210700140c0079000701020140380d443c16002404a044a2000e8080081030201490980041081c80d10250a500807402041362083c88801d4180c4619a40486005041c8400071007001c40c3c0201880000d1450b03003003145034003e0310a070001d16030000005029281040441e92001d5901c08944d200c1b6003a4400490903403200c0c00180100c0100c205400d10404c902d41c50701e14018401c0c000c40d07401900400c00000d00400b0305807804200c46090b900300d24404020346402c01000000e48c04030325a60019440c200200742c00600f1121640b0b00364807543d0302c0105502080e04140328030382c050303001242d219070100101002c01c459400645215506034034010303203665500c498141c0780303004038408d100030141c250091040703605050141c170401c036014a0001844000c503030040e62424106005103501d031055808000b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 939781951 1250 939780701 939780703
    0xf010309150606110607140708070f0b06030d0309080301050904152c010c140a031404140601080609030f0d061e030606170a020906040b10020705271303020709020c 72
    0x488941d039440f1131400d02121241511220207035403500028503d40d0003107d650243d03501420311640541612444d104d1295118001c0750151282250003603904001c008440c40c007404400200840f6081c107000144c0640c1d241082440140145c074071a00d0040003140921002c03503c02c02c1c03150384503c000c02c5109481c24030980210820803010140c800e840707001141c4914180180c1d1150000d6861b0611010024540014a42c01540030202015962106824500e000010440c080c0d4000c4520420541010080506004058100c041c6a90010081c048451300001c1201c403c2450b403410307151104000d01406c8082d12182d03000450450180f0f101c480c282e002c0c0c500d40021284101c0741009000e0f912801200740e44d84080c41103c154100c480c1d0a400360600b2185961b100100030000205812640002010090000d600000680c0b054805100f00d042c0409060041c00007009208400c01484055030070645006140c441c5004021080f081058000c104a402501080d0010f54540743c00300a01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 939783201 1250 939781951 939781961
    0x1512060908160c0f241d0402040b04030203070602060903031626190e030d0b042c060c0310090b0f060a0e03070f0303080c450a05010e0f01030915 64
    0x40c0e10302044903c4c0024800621040a41c2c242103810958039600c0684582aa99030003000c220001d1200720140c40c880c140c1d1144000c1c009400740d82c40380c40c1c446040d801031605e4a449900a0700a40d4880070500100110010035030741d00088500e80f241d020485414100e0341004449002c000e500115000c0303401c0101200c8020b0302c282203204600340400187c2045d48140d48800b60042ca00d50803c1100002803101a04640d00c65403024001003006000310111402507031281d840388004000c0c80c950702080e85014000e00740c202c1c0209103068110304100440f00c03480c8410b0b20640d80c4c0d540e80c1e0004c280140c2c44001110100d400c1c000c0c000c0751a070a6109003e02200340d01c0c0f000702e01ca80210300707010643c07894444c0c0c00c40c1520341560318414955034088280c0c000d42d2107040c1139a4035013040702520b4070581c01d00c402101da00361050890b90040ca88118020340100060708858415110031106226070b992181c2c031181204000c0318201030414902c0b0041e401044101400346c010010704850320318204c03168001d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 939784451 1250 939783201 939783209
    0x14090402130b031b040c17130507050306131704031106071a040809030114010e0f1305010c0e09060105090f0103110f16170708040b090a081603061512060908160c 71
    0x348180c6d92420411980c40c448128103034800c0001740d004c504042202c8400542441c450005c5a40d10790721440041c1c5000811205e620203114141c10460800c169010803c4480700703004000341c2010300315500c19095602260305d03103000e07400220f508804c0c050b1b41494a4070300901183c40d400982403a00300301c0102d0740000c404038041e609006c8800c13030031307941c26150504031121480c0040c00390700e4500b08503900210151580105005407121000031a900b0b10036442c484226441d440f09114419041c402d9004004201c42d06109051117954807a0f100c00701044070080b030034a8001040c008580c5642d55034000d0f221f2484840001068003580d80f86100034942000740031320307880c90340000c040700d0740d480d00d115101c40200145414802004240352410280940c050f0040051f4407658441a185140100d074112010002807080c1c0d081060080d144110302c12081141e03003007c0064100a0102c40c20200014000c09145d92864040140304418007034448013144a190340d0004209070410b0f0302c4519075402 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 939785701 1250 939784451 939784459
    0x41203060815060d0f0f060501082112040c05030706091410050a0c0507180911090c041223150604182415030b0f0105090c03090109050102040b070c14090402130b031b 73
    0x28032250bc1c41c0400400542c00c1c209488801d140c819030010480034804003400480c3c503201540e80118142c2d4003801a0400350500755204182c00e0710305103200384848640708066000c5c0c80103480640f40e141d80401203484107407071818118103280c601e180040c500030403507000b580040c41000d076120302500da035006080c40b640607403942c1c40145999402c1222054081c2c0d04030010b84800c000070003803c0043c000d1800268081c03041000310807081d48012030303820302d40b10030040103401c103140001c00e40c02c24840c81c0382c1041043d83c0801516041070741000d91101c10000280481540840300080301d07411800703031828002e2500b018002065641c131139040694050208403a0502188005098101164042812904024035460540c1c8580107422140e47c006080b6030040d5480348062000715409000030001041d07207007021a6105168209007800d40d10682054082c0454090902d00c1569284001c075040b5030100e4688080881c52440e040c000c00300c1c0e50b00319800d070044c00c49a01d02d07030007040c251150000c0c05175 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 939786951 1250 939785701 939785713
    0xc170109050f01120312050c03071b080315060706180b22150b0306151c11060c031917060f010f0f0314041203060815060d0f0f06050108 60
    0x803590035660101c030076a00d0080082c004204588814245000440c024202401385a0407020782d90b040d14011121b00340e114000105000748030303078031044911100e01d1106070700d002e410481d920703625244000f41c900007040060103810001d07075507007000320384020f03a00003000c020207001c49031107030b1044104940c10349040034541c0005409607440209414a48040000d1071030300500c642d070b4415030040d070b24040030040b5a11451034806840c10001e50380205040394085016104d01400c0120035541407030400d4440198010140c001075181c01d4482c2c02050072a000b035101e00888400e18918081d2600414141c0750041032000f034a41c000e106044036900003182044513650703c60510000248030740c18107000544101d406043d10303214600c80080300c00c092a0204d09d40c4120801081c02d0b1405440070f4410244c10f1104981054052240703c0080c02c3c0d00f8040c04041c0800324a14241480c001c20141c084c840070f4010404024800c007502e80340a6100c20b04260030405420b10780000c1070240540c94880c8109 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 939788201 1250 939786951 939786959
    0x3070f0b1f03080d022101080f0a0f140a0c031109010501031e0506011b0311100c0f1803171e0408120d020c0102040b0712171f08010c1701 61
    0x707907094000e0001c4000c1c44460546141c1c0da541490f842000c0d0160255400d00201c07100c024020602d07942004458545020355040c45495801d1426009421402d40e21100b51040007408e10390f040340016400039840f684140e06100c030705040c210002801007400e032510310044200030b0440001544401d064400b59010f03a00c95006404580010500fa00007110a051405010071250091a44448180340c5040386000c5043c0c4503060b01049603048000c43c180c17401c030300c01d4448104040750340e095060701c00303000d1620005800740c0701c0d4000012540402148030036681d03440403456501401103500485075100c2d8000202c030242c56400c10700b000c84400744c030f5802c4001880d01d5a401d8906850701d52001d4482105880c1955125070300200d14451a190240a01c250300c0c4804c2c4081c00080684840b41c2e551100705103030040040644441c08000c0c0203240f023007080444a07151020340e00181242a00384a0999601b25600c100080d51152081c0d6003440540030b60954040d181c14400741c00882d01030b11036625 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 939789451 1250 939788201 939788221
    0x4230607020106080a150515061908061e0105070611070c0e0601020604050d030b0a0e04030206250c083a0e150c090d08041413050f0a0b010201060803070f0b 69
    0x4c00001a15070040111b03862503200c01580000e070040038001091101e010075501081c09078106201c86021216031105404200b078014459541c011700c1101c9034113000703010141c00000090183c1025041080101d462401c0285540c0610340902c508404141c940c03900303282200b990300740c0b40a01c070413420580d0041002e039400010313a1402158004041c01c00b030051183e0450040c242104000c0d40070481da54001501060186014001c0e8060350142c0301d40d16000504409503800849984101c410b90108448210346c4a96007170328240d4482d540958550506955280d440100540e807105600e0840103101e02c15207c032907a07503841c0b10f525000d001d01c8140c51003c031f480d50310401584d41c01c804406e00003203e080c4076100916030310100034850644050503031119942c6800c181c02c02d4200c1c20702c224182c9458606480c101090b00303000401030146141191040701c0c060700241650103601d40394020b2134603aa0003900584003030140a03045030785030385d0982407022038105045030071f8400b6041030000c54a0045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 939790701 1250 939789451 939789463
    0x90606050705071e0905011e060c03050405010c02040915051f03021e030304081603030e0402030712050a180b0f09060603030403080a02010216031d0301150302090423060702010608 79
    0x3410001600d48a80784c03000100030001c5403512101c4a001c0c1d40c4022841c40502d12445000c1c107030560a08820079481e011602c41d800d410b410020620200142e51800079512004880c142d076001c0c80d003005803a00714408200684201803000b0842040303844412615600317607200d680301d0342c0c204119881d43c122009100c0740007619404060741010010360008040350582c1083c004400300501101d140c956621f88280c2840398400d2412900070400c401001819840400f190600004407402c51840c24142005040003c2540c407140b8010b8503800020b0714140a13510124000941c81d441e11102c001500d85020340700c50848039152074001da0b43c00720340c50107400122203108250107001107141505544850700250004480c000c2190b408012010146030400d06080700c25100b6142c41d081c4200001c0900e1403400d00e0846e841c0681e00d4031030313000e1208980380710b4142265015943c0d00c6440c0c4580c2070906440d0703c80745c1c07125800c06d9122501e416902c000501030b8481c3d8003603402013020300c0c0c40705e4a8a031104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 939791951 1250 939790701 939790703
    0x20c041e0209060f07051b040c0801060305042a061b1e110d030507211223070804050706030b101209020909060106020f0303130303110d11040906060507 67
    0x30a803041550020195a8020020544018200d40c14421150501c904660183d401140d040e0403440307520101103801c220100c000e031000c440900c0910041c84004142050500c9610300b0551103201007400d00100010079001c01c40c085014441c80c034030311b0301105021150f9200e00740028060940b091080014461502101a8000c03102c50000004542401c80280c0130710341681c000003a40c02107a4990340e090400c110181c400c1e2561038a840c0d090518488194000c0f6001c1c10020200d0350310252154002620128525140350000341e1020100060302c0703050310020700c4014000400140001c01d0340018500b8455032042c0111490140c0741e403001c6042c1c42d08001504d811442160403006854080c0c0c1200010703004681d00000c80c0039598000401c189400d0303c0c01e041a800080041c031030346505101c031030f440241d01030003149141400d00a0007449071b5031000c05800c25646110900402c1002002c450341c0d080c040c0401d2001c0c00c441e000041c5a0b900074403450f079005d0f1a080001a80a0041e02035880d12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 939793201 1250 939791951 939791981
    0x20913151a0102071e05010f18080c040c02030702030a080c010e07081015030314090609041e0501050307060915050c06010605090f010f0804140c10050405101407080c0304030f050d020c04 82
    0x10501c0c00c001034030752488c0d00304c0c4c1006021034501451415800d413000c800050619400410300c6040c0f55013880304a982c1544910304541042001c0c0000d43c50010340049202da000311240d0340e8a131440e02c000d00400b10900f40d10352500852100061022001486480e4140074400030002d84416007098109200103200040c003007081070f81650b2000721480d018014000d030140456203810100e40000d02160300800040d421640c039008411040c0b58188101d80c050035040d0b005108060038141c0240030300c1038600c103680c007030024902c0040100744100c055070a012080b00403200b1550312a0b00c0906180c0125a20030300038076040756612015803060300303c02e10848564a410100791659103580b00b4660440480c2d045034850100711401c25103981001d28140b00c1c85568140d2558109000c0104100d0400291004c200300381d041c043d1054041c10403540c5c4242d11100a80e40d83c80140c04250a5024a40c005401c034603000380b8141c184030300402c0b00d000107035641c2cbc03d90300301c0c500c11410803003211420100420700c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 939794451 1250 939793201 939793259
    0xd03110c0d030f050304081e030f0c0f0f09030a021903053a1e03060e010530010e070f06020d021f020c0c19031e020913151a010207 58
    0x44034050b1000b9600306d4002d81005d441c0104000726080c0140d91000007003200c113400810810361201014180c1e4000207000000b40c504080d00342d0f00c1119000d242141003044500103001980da603003c006100c103441d800b801e20304d408400c400b55541c3d0070308a44800e948501800f103811742c100180014052545014220b21000101030442c1c005464428258101c01d200c0600c040240a40b150148080c45100658020030081c0c1842c002c00200c54040c0c4c0442c0c050b480040d901d02041200416050f800f61101820032100048610118050041948001442d01451001003050442d0f0f4240f001901c50b95000c0780d9a017107844a089a4810104030711036581d0140c2d00401c0010403484d0002c0c204503807000221645c06001500040c0f0503980520f1840070070000030030800412484912402a4806602258049000903000b0840080d001040c80001c640f80302120300030000c01d4144079a69000800742088000c0640b1a5110602241d5102e540175100300100007801002070003100a025130301650582d6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 939795701 1250 939794451 939794477
    0x180303021209010c1506080705010e0603072601030f1e02030a02061308030f0a0801060f09120204060b0a020c041a0d060f022203120e0f1e0d03110c0d03 67
    0x8035500100201410000b000403e0f40104183c044d05000d55843d4045c0014681e1510041c68581310403584898140003550010021a54400055a504c0491824608412061413150800e88001b942d000c080a40c1500008028402c10030b201d8001640b01da0500d001845140f61448070000540b10004e525a1110b502c400c0182442000340040640080c8051142902c40f00fa140c15504000652202e0b180041044501d0a510040072801400c0500f0b0003207202e015000002d2041c040d900481c0c6003070b01d0034500401191225801000240380011641c0d03200d02c0f0f100030003515408140700d880c1c411802c00da0515903061000031541103406000300310058103021079880e03402501081c082c40305446e42c28008900d05021049000c428880c040409248030f03803d516080e5156450f405250741003100c0680840340c241c1b01c200d541510540c1c22544000b040304010211420f441650200b1500281d6000c01c010070075400c124603c11901040c01502e8403e203c03c001c0c0411510b007550090001008010204 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 939796951 1250 939795701 939795733
    0x16122405040b241207120b06041b020703030f140706090c06022805010e0d02030d0e0102090607081309021c05010b0a0207031b090c120518100f090606030b0718030302 73
    0x442040100c0650b225031340c0d0341420030024543e814007500d21b480c0c1c010802005260078801c044407a02b4502da11881d1494504c4020764030562400001e00748251701d00c0256a4030301404c1c0040c84002083c0340c1966138036a602d040d40160134886802c8951017403404022400a00100d8211054014114600e06428680440280e00c0038003030419111556900c0720340c1c01c0b00c14180301ca8040f006e102c1e0011a60307103000d429440c0840d5603d4042c41c4a42e4418041c1c000c45640300d80441c0e0346150003a00b0507444000107540d580f02c81000d603019807100c52000034420716004407203546100348002200700300b0aa07a07841036521600d105510640c00143c006031000d0000402a2100c0d00204026201045445072184070801c21128000d0040c00424295000074030380c8166800340c44d5110348815130b40314404201c01d4181e6598209411090301e62910364201c01d0b50810241c0c080c040301038112200f4009a6a64204920000d00070340d58400002c19604811020342c2d28203042c1812030341c0c19401044503842c608044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 939798201 1250 939796951 939796969
    0x1170f01050705030a0f0e2d010b0123091f12271a09030d05090a0b0420031002030406060f14010c020609130b03070816122405040b24 59
    0x106d5801c503074661a091610320108200d56602d18076041d81e1a0210f42c181182c00046500c58000b0b4090f0b042034009141643c0c04a544910040354407141c00c0d01e0407041014903164051000155001000111452820b0082c601d04080d199250740301d440c0200314444a610968801c00d0402890207800d120b08210001c00b030203007000c45030088203191881e240501088110407000d4506521a90000c14010088100c52061b240c03c03808010040220300303010307501c01d6038000004201422041c019008c2241030111000c041c3c214440c010107995400420510510094009407402e8540341d2800710b010440f1852030451005840074004103083e0450076400449001781c0d1050104e802c150700307000700903d030f8035800f00b113560340304034000041030141c40003040c10314203240784d4003500060340000c60b0074400700300012000007620380c0004142107038096410004910708008000860352000c3d884a26030312165980711500440c4036240344036064a9200e440d00000b5240850243c110000c07000d4506e00e464a4821 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 939799451 1250 939798201 939798221
    0xb2e110d02190503090d0609020405010f1401200d0201090c1205030409050406060e010b0306030d1d04090206120f090106060c080412030e040513110303070f02060304030c0b01170f01050705030a 85
    0x702c074504200070011034201584031408442c7c0f42e03120b65901d401c5240500a01d405007040c07004c8400c040d858140e4249084048035a02810300ca07814040c402c01c2ea083c02e0001ca0207c06041c121000825001002030007003203012415a0805600d44011400031890700c1c1c4032103207a4000000718100360420407143c008010140040f1011a56007100044081c010464903000380001a0000e4807440c0080038035042c0303440013403401e04001c0070000c1c80200e4103030250740c0b52824000703a40009103440c00b807001c038076584591344906c25010014000c0001d401e103000f26040c80351039418003c0c01070330b940380c0c0281c07900748c8410001008800d060005200059070502000400b900038946504450441400b00d801c440301070b50300300c10b05008824030800740600441b4400c074410040e00110300d86101d586450400c00c808800081c0304640000206051611070300c5980403894100342c400089581d84e0109a42d000b00303040c0400c80d00d018007800c0907484501032017042e10440260312083e14540d64090744a00030100750007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 939800701 1250 939799451 939799453
    0x60906180901270302010b0123070203070801090803010303020d05040b040b18040f06060e0105031b030405030c030a08010e060402070c090c030e0703060b091f090b2e110d021905 78
    0x2458000e0001d00030041c3c1c2d03000d1521036041d00caa0595040c003d080d0303006401017905100206000e50b07a80b071282d00f114028020203d40716900c55080d032001908000003540b0101680d800c2902c80b905005001c4000e5041341e00c00d8003116402c5d10151410b40c0c0e075010358401c00d1144d0300244420080e11015100426483e2560109884070740100c0d40010200c4540148030f11074190740380e07018845182c0115403400e200800b403c06600750302e0701c51003c0022001d05900c020782214084049030802100308240c800030070313030102500e4580d4403016000b850080e0910551034840310310008100300c3e08040c4202c40d00583c004000b502054100000140500b080b00344807010141c1d00c08205030024410b000b14070181d8440c6d000880c09003c21710070001ca0b0070003d030040b4480c040011a00c2030594200480c1811034075504008201c4480e00b4001507019104414090701411f0b240702d212030b0019940c001ea0940031b0030754507104c143e01c3d1003280d029a1420046503e0300580e100302c003001d2001850028880d0a244560 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 939801951 1250 939800701 939800711
    0x2814010b2d07110f0904031e05090f06070807140a0b070c12030528150807060210110714030a0201050c03090c12030f0f0c010e010203040c0b0c01090206040815060906180901 76
    0x120200340c507120210340a5001484508a840b4942d0010034407070300c0801c1030310b4072504114040e000141c1c80c0d8426807a0bd4462000050300310304010300141074a052030b4001c2580050014041d15107900c40402c140120741042e0b114000400082c000ea070b1f2034603081e0b00140c000341e22900241c030980082801508005041d040c00c100c00c1c00810b180c10200c150400908404158605a01c03900d0505034455040314541390011442807203a554006813200511643e15404640c0c4021442c00003550b100b50280a40400004091000071841c000f009282c51180c81c0d008100a5403400c4840d42c1c240015141120350340c2200c10010b003075203849242c10180d40c0d4502d007902e1130710f90a1a161102c0b984481c045c92400400460304c041304002c00e224280740030081c1e10096245190503659581240540c0c000c40100007004907a45c400018254054109980d0150070250744544450220303658000e040c600700d100c8a40c14000800380d00301202ca50f4051040070b80b40a00034091100d10658103407000b01002c5140d0b60310 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 939803201 1250 939801951 939801979
    0x92001120c050a020c030a02060a0810050402071124190215360d20070b250c05010309020102030d150e010b032814010b2d0711 56
    0x248110003001c0c009071103155446035a0500030b414145007094981c441e80000d10b0880c05621800c04403543d003807043c507080031941d90708003003024405107a40020340c02610100d160000c10840b01c601a04104044807403495409100b507048050383c54210140c95161001d1204041c0124a01401920421a0b0046d02e54103c2c00409200b5000011154018041850403810354800352848409002d44442100c0c581c4680500030842e60700c1d001e054601040000100031401c40450503050161050300c400180c48600b0b9407035031001c0060b08120941395040700d02c00303000c0244c0e0455010b40c01e80d4a0b40441490003451800b80107500a080c03a020682c1540802c200340c0031341d24424030551400354804414110f82904100400b40b484a05070010314822004100b4011070500c1c2e000c0070300440540d01090a0a0303240105200c014001104800b0111120000003203003110349100030b050000d000d04451040d00c0d00700122a51803000d00c000114a40c18208907140c0826440071900084082c0540201d03111420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 939804451 1250 939803201 939803237
    0x2031c05070f0f03140a08072f060907050d030804112404030501361b2309040b0103080d0b1807030f060506120417131701092001 57
    0x1038400c202c40744540194854101038101c103a04202c180711441d000d01b071401601016001a4001c1c04080c10300c86411314030201400004400124201c03100f0040343c0003030310950020355551040e16503a41e80d0003540d40120311800c007103070441001c6070503076210001ca8407191111203c0003003d400d415002421002020100c0315061141041030b041c2c84012a61a450360820b0b0b42111030301c40c1d9802d41c5000f00c503141002c6007034051010501c00500314500702c01110602d08481c84c030340900c51100c85110035400c009046a01e0141040480701c00c1c00c51030061158600402100d16812034006000e011351000500c045006400a4444c500700344000050f2a500c43d000550300c1480022201c0c018200d8108011240c3d5150080600b502c500b000184a0181404002081030003100030004680e11102c0004007403000409007000d000c0c20280000ea65000b440d400360b40c861320540100002c0007e070001c0380410940500c9200d02c0c080d0030400f049041c60341e0141040841c4118a4003074108002840782002c4064 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 939805701 1250 939804451 939804473
    0x90b0c01152c06090a0c180906050f04110a050a0203092d03010c14130e01030b01050a060f020c100c0209190b0402120a09050f060a050403090e0402031c0507 69
    0x211000b240b00d28001c0a410003603a9840030204801010318018842c454807401d1185410840820b008941e81300319007400c403a001c1040d122207005403001080050800140d0740300c002034400c00ea40714190b0a0202040c0b1090707030f00c007203400001000200a103050213482440901103001c41c138810740b454080020002140811070150a03400b00d8000180650101d07441e540080d95200c05600a000003050920050202d22104108040401300020684203007070316861008007500640c650120156142c0c245088030101c24003605028681000e03011807103d020f01c04030b00c074040c04c80e8004c1c00303000950300501c8403c900001e02102840180703d80f9000603070b035010040384554500f00803204900d8100c140c400668030100100381c000d41c81001005882070a0020b100d80c400c03603404001c550303040c0170700c0c2c064036091000f949812240507441c1440f4540d2119005a80240d000703a0381e9010360398807801d503030140c1d40c415140294140c4c0002c00800340d00c02c5500442d80409041e050050418080c0d443d44051a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 939806951 1250 939805701 939805709
    0x150908040b0a020105101e0b0a0e030610031b0e1f15021b0415140a030503030c0c070611030a080c130f15030209090f0901090210020102090901060f090b0c0115 70
    0x20351100c04018400c5100c0d42c4c500c00807c0702c0c812104070789941d00d14100303c8500600408170b000c0c20015840182c2e900401444100c1c55014040300c44ca407419080030119080c103408100c4402c0b88480111001c0c500c410282c00999803145991042d6446140e4040d40c4510400048000c44071050400282d2081004c3c141014003156005040984c0d4160400701114040050141c8514a40003803681e001100080d1101541d10360405515a0030008000850756809a41b00a22034800081081a410140750160003800c581c84216000740e40c644c0010380d20a0906074030800030380c0c13081c00110f21180c4501c2d980ba03080440803000034070340513043d41c8404440326160060040b1301b54800080040d801224111290104180b5045040c0307041400014510503014090703c080c00d13510b102244c511642940840703016035008040ca03003400da5008010703010750442104240300710203c1c0b0000483c02e0007040b01218262a40c1c0d0740007091410181da10740f954104400e810103566951007050b840c41c000e070f11070310064 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 939808201 1250 939806951 939806953
    0x1b3307060c08250309080c0604030f0806030d1d04060302030d0e03061608070c1a010e01090b0a0b0d0e0f0304030503120928020f1327150908040b0a02 66
    0x3240e24038902a0070b42c000941181c11a400100c03d4000b03103590b89080c440054401d20700814818007038148080b4038000c03048601c0050080340207100415030000182c400240c1c2075140c00c006a0341e08020181c80d5101502d0380c1e070103d000c560a1110034104449680c0034044000c00000b207007074072600800d2812049218a8000c1a4110b22410f00382c81c04020031584a440c00c02900b02e802c04540f4000c2c0030010103000b24080c0002c500f0341108025000346000210384903036581071025a503540c80c00802850a105d012025441d200d110a145c0c180810000159403d60480b10714000042499500130a850311110025000d503880000c03503c503050000384015809040190345500100c0c40c2c03290f8503503014040d945568015801044180409440410400600710298118050301e0020844035078140210651160b441b0720480c0e10400349610504111501c45640c06118641e0005003c800c022080003a19480c0c944241118829007034020b5454103101c6c0d100c2c241002d907510701c04801504106030034405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 939809451 1250 939808201 939808211
    0x1b10030c030f050106091d0112081309050f04020a06021b090a02040e0103140c0109031536050d03021602090405010902060c0a0b06011b2a06030e1b330706 68
    0x401f805540e01f0854441c00d00b800d404a41d49029180c0311007940881d03000780303c44004245054000d10400204004103040d07103062001d441c14105400d0500c0d41100c0480c400e01414201091192001a510885030b00b42c0d504000c10700c49600030000078010040c0001c001039000c000204a4117400c00d160381c0210b104075040512074020010503800c00d10348409250400c055400100049440c003070f0005445100104005000b030300f5031003e040e4080947d200000b41c282562889000758560540b0221009d000310300b603441c0190b088000710181d02c9216100d044080d944450310001d031501c1075010750068850000029440a29804a13000784c01a010801d0503800c520400b605002c914a1401d0703001500b440d000a850600c24658103081000c1c00c3c001e8980c4c130b110310412602c0750410b4000c015071000380300c2100d101c1c0d42e50301000303014102080c0c0f03021a03401010402d0440d0400039502d030100d04d8009100368035904182e9203021908034a503540e0108081010300e410108c2c0d02140081080c9400382c080414 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 939810701 1250 939809451 939809459
    0x2303010e070e0a050105040207030801180f0903020307021f0c022205010e010315060617130c0b0409060f0501300204092306030706030e071e05031b10030c030f05010609 74
    0x484d40140d102600440c0100711007400280e02462090640e000000f00d200505c0c000034004006003035601c20303081e10038500003420060640020107810194400c840140c4520100700042107031000544c1c4a1010070703c501f10000051402d6000a0380520121a1800c202d0502c041c00c0000c0d00c000788c0c004c40c21070300040d005005001100840324803454400c242840200d2902400600b48888400700c04142007041c40407403c50520f0482245440c0d400c80340ea00110b984a001064040e03110348680e526040c54404002000082e00c0040c070100e03074058403418421540a805e484080f1075001002c0310f072100380090b13881c91a120b4409400038001c0300c400041c0d41e48111911074160007000010f480c006600c4001c00226235000200e400c2620b0141ca80841c3c001c00e5290014542070154110080c3c28201041704000041e401c00c4000072030314214100d480010100c4d40072150400c0c68032007a6007005e03016403c2d60500d4003c3e0028000b500451400040084a4803004021280c080e001040020040380e4100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 939811951 1250 939810701 939810721
    0x2120412150b0a050d020607151b030b0a03020103050903040b0301030c063b0d020d0609020306010b0307080718081f110f190516030c050d092303010e070e 68
    0x54000075582000300800e060322800106002c58500c81c02c0d201c1c0d46030042480454880c181552401e44d1310081c09012490000c3c039000c05010514185102d444544048120040c07003401341d513440d003c1c05070031002443d040d600114054007004020509a1208100c0020740c01c071a030004600071030082c0c007858200b40c140b41e00209100110100d0116500942114241c0701d000c07030300c112004030480300c40c1016000c5102c0100c0c0c1c0500c0d00400c0a9030291101c150071042c040f840d00030b170300141e100b107003034400503030b207450031002e55000c1607400d00002608000040c8101e4010010102440c4110f0000b410340765880c10503900e408c0051420044400d030490440b0086c460354002c4082180c1e280c095242400b40c1c042241060740282030000381080016115800030300c0c001c0c030482d4102d1122a98444d4140214203003d40002840c0318208c4040c4110740030301c00400c3c8250440d20a6940a070074680001c6a155040c4280303d1401287c294103560f542000703040c4442c200b007054001c0401d2200f400350761401a50007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 939813201 1250 939811951 939811973
    0x150318071205060115110c010c020a08072c01033503040f05063304090204090c0626060121020c10110c060f0703093906081602120412 59
    0x443d080c840141b82e02c800f000c0c408580d0320038909084ca465505c00182c3c1c000500e0040c03040d84414428080d46034042000235501e550800c407521241c85408180420b02d401092440c0d00f440301400e41c494800615503c030303c1e0101001c021403038500000c6050b4a000050156540c010b407812103184868113080410020180521030b44421f81c003405900c0001d0100c140070290402c1b49a03680e8040400c00302102075038590303002d0030701e003500903000f005665114600046000220f00500001c1072401d02416004081f848825035501290a00703c04181c4034103005481c88000400c500540c01d50744510307005a1034007813001d8020300c0b410030001c0010031910304110044400d080c030a0a05900104030382c0d4502c070000201e05800c100144200050703135580f1013045000700000000100500d06101c1141803803042c400c02c1100850b52160340c0e000220b452940f4803100100361240700e0200314440e00041c1d0203180e1203081105403010340140d8102482501032440303541c1c090740000c05800c404481c50000d102d144244 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 939814451 1250 939813201 939813239
    0x2103051e100b0a03020d09060207200a0918050f0c150c031e160b070e0409020a09180b0109141008571503180712050601 53
    0x10308140c41116512445400707420078102c40050b02e008241d12a904981c042c186140080002820074507241c0040c1d0300110007a80c42d120600c0d01025205031802090325400740050544611501d0b06080d240581180400305c1c2e601ca2032030140c070020500c28001e80c81c0c00c08844d4040c1124083d02c008100c0d0411031040410703640881403215000545000049a038080319115240150103515452401784d07104d554000c885110f014940300f41040040101136005017034585404440d0786140b03050004036002010b020b50320200c0309000304001001580000495010042c8154100c52035880780342c0805400c0e40034200ba19a40c80d200e078000018038842075005020038910050081c580010340b80d850109080303002034560041000384908540f0f0b10307a001101020b943c0441c920386440c914944009071410040100070482140003064589070002454140c400d080403400c0da00c4142c4100002d00e210080e0352450702c107030b001c0810f44404030130114101310b110760700400c03c0d98140a0050301d00810411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 939815701 1250 939814451 939814501
    0xc16020d1b0f0b041a092e020d0503040f0f150218030c062a0c04111207020115091104030c080a03030c0201090308040b091219030e07030201020d0507210305 69
    0x209001e0202101010740303083e1202004240c64640c91000252140c14896845140001c7e14119030018450b00c070311180310740c1c800d4007524904040040f0955807071008480060100040b80d0100c40050f0984a6400c09103015544840103682c2c2e11007900304030b1740880095140111140c40610032403a08004010740c42d007007a221507040c46040d0032600c102c070310507103038a445200301d00524035550441000304501042c0002e10034410440b03a4414042071f548484c40030444809984000b076845401401024100c580034860002118907040200300105220507021040740d20170880000815044200b190150030904080c00da1301f011440c0180413281d10129441c2564105450480465080a0559882500302000702c50903903503000f040342014000d0038580410180851400c00034403040d90540c1e00703500702e510100041040491095552a11440000d00503072282031544101440b450103014024441c611100c0d40c02070850700e40808900c0710340c403000000d9a4504004800b000d0103c00c24140c00b180c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 939816951 1250 939815701 939815707
    0x203060a090c051003020c190203160303080705090f040609290607031b061a0a050411090409210c0c0905090d03020c0f01060305030c010c05030c16020d1b0f0b 70
    0xa034402c0c040020394480c140c4241d0303008000c841100d000f50122441d00403a0340640d8021410585101004003180b90706901038401c11224803424040a01c145c401d80b5059200d5150036a40d0300006c071103d6002c91003040d042854094800c8150b150360003a00b0103441070a80200c1c1d0300001005500d688800302500c1d45400407a141010b0240d11350100b00c43c4210b4051402481d080f007082c0d03417403c0f080f00034480207103200e180240101c804d20748903458007820340e0200c0d44116400c2d503440070801030310380c0700004035440755003040400c4481c03600303620001b17000c2d214002912070085d160070300d43c0280c0783e5014400c003c00c8d03211800d5401c0055600f005800f0b03040301c4100300b0450426441680d9035000c139415404c14141d0018003100d4050b020000448200307000c0c0000c2c019942ca0b45030042d165045480c41005940c01e00c44203040190180c41034a104a08580429041818180d181da440100c030103001c0c0d0b080858403030301c807001c00d030017882c034a00c441c0f41c101070801424501a2400c90f174600503400364a08600038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 939818201 1250 939816951 939816953
    0x20a090b04170c090c07151d010606570b01180615030f06260c0909191b08010902120705061209071d0907080d090b0a1e020102070203060a09 62
    0x84016500380760380040841900550582c1c0920080901c0380c2c10348c90484549001e8149014150040d4059900550717828803124a490849403807204181c1007509681401001c200c0341c020381501d4082112984100c1c4810200302c11510311404000c0501a155024446c005201d100115192601c1d0003002c0e940030031400c0d18081000740c01d08403500070f1300101901c1d4801e00c4640081500200c0203455a03222844003010729941144500f880e038209803045000c0c00000813590300c0e00c600c0c2288100012030140429542c4d591505030125080f540807650140d031440401071001900880c00b014190000002440d2a11401008191140040780d00940d5010703a0b0180117907120f60040d200c0c540c440048950b110780324030a40909060150304030f0110014110255a0301c00103520740035004440183c203803801f0b40e0f19070090545130b2008402070b10214030141c1040052a0210005061001c1c0901e804200d00c0c1903091009c0c2c2080c1000e4000005070740104544095150034092990002501403003000b010000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 939819451 1250 939818201 939818221
    0x3060b09181306020415092102060f0c1e0f06071b020109030501021207080a0216020906030c030609070810060503070b09011e0c14060415020a090b04170c09 69
    0x38509204001d25240420321910421558907052607100c4015515903890751031094035005003050384000280001c00000e500d03506000307408821903030016044010300d15602440301319485120861800e031801c00082086150502240007601100c40c3c20700c6c440100180d41d5441c0410039800780b8603e401034002d102c000e642000070060800007108094060029900040e107030070242e41c0c0050850750000581c3c907480c420340300046108008030303110b410340d9031690000d4504a00540707880c5c0b072503214000e10f40409482d14104280d48820014100d0305c440800303c0100b410f250b81950f119040d85c0c8034640a114105082c03102901c40920303440100090780c03411000a17650760312071280544003d40050842c1d001c1c3d2146800218004101d0007000d1010700b0b842c1e004161031801c11040d2404080d1012401c8030000100301c05025541010300521001a441c52043c0258002d9443c20140404000700196904168015200408034680c14510400301c03160350794104022581c00a100702a01c2c1f00308292440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 939820701 1250 939819451 939819469
    0xe060a091401021222080a0b0a02030a0608010e012c0601050d03140a0f12050106270801140f010f05061e041205010c090504020a20030f0f04030303060b09 68
    0x201c90010407400c0d21034400140e0900011400d4003150150005001d00c40e1060300e40c280c801c81586441c01d4000660300c8800b140c0b01d903515038000702202083c02c0410040c00458002c1e580040c034104d40003c000380e07034040c05402c40c0c91401d02d0320b2241c1d4460204071280d5400d00c1c02c3c00c010703031a20313008003c54020b080c09241d1104e105020381441003c119804606140c4030310b550072070060b100c65030303c0e598181c100401341810781d580d07481c50000340c9001107010301d00003c0d0190a048541c1501ca0a080e101c0309038604040c10029035412080e2000f00c0c1000400b0345090240243c041c0090a4800060031310103104502e21a05801601020601441c00c2110780c40d03074000c1342c1c00325640400c0e0150004000c400e580321031186901c070900401c41001d0704c00620806503c580b290100c1030b210700c0cae41c00381d81d1400e00043c0d016080302d41010070001003400007005100c0c4003680403440b040098924012400035842c1035500700820b5140c90400c082424001c040c1c05110340700180200303240745801c1192620010300504 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 939821951 1250 939820701 939820709
    0x6130303110c061303110406060f030504060b0a06170906010302090606032d010501030e0106050609190302060708070c0e01080a020d1a0f391c0e06070e060a09 70
    0x82003040040840070074451507070071010050180d5030303550720340342d142044243d0341c0410798500c0c032050040c0b151172505101e08000c444003600e445000c0b44840314164002c00c0010400e441458840101c0210b5940e242d01080180c200c54640c0d81c40c40082000a04000d02c000300340d0600e0368001c40c0188007607925a1685540f210041b60707565030b6940d80c408131310752040d013581e14041903146089120114880059903a41030700d42c01e80c1d0800c00d100c1d0407140e01d400d0b1003840c440d2a8101700100006c080a00700340c00b41c000003031411000c009400c1e90703c0d0b001c240d0a0f4440030043d9980480401c46800304281c0001c110020803d118245099504084800d51200e02c1440001e1081000d040c4880801407046904410101d00c52610ac006160600024410400844881103854419144500d40c0c807141c00e003107140c0300809c0d8400a42da03045a0780d400c90b264401c2e5a6400c10b204428542c95401c140c50090044008906000e4031042c10301040c0034103600c96009a80d03118050501c603000901c0d5111b070580e0121 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 939823201 1250 939821951 939821957
    0x60207060912261b03070b0c0a080c090402040e0f0105180114010c02040f0e0d0807020d020718061205030d0b01030908030406050c19020102120108030301080703032d021b06130303 79
    0x4120701c0640b100c641c8100b00e0b40b05181d04e07031074502c44840300c4044007404c0d4642c0150b210605076580c400c103000c0140300b01129000414200b10200f87d4040c41c01004d007004a4000c0c0005103015210300b504900c030b44041320a400d00002050042c0454140848007640c1110100900500d550500c0504007001403610078550410910804210035580d5a403c43c0d15140640c590801c0550141b5401a803038101006604000c20b00c600003041140b072000541a6103141c04c0d5024050150406001816504101c0746d640049034a0b03600c086111a0810b0401c203215104000035969480d6007003c03a4165020100403c0c1414540000d107404203243c0401c807039105a1000c40051345a84003101c8540b01d0042c05507a0303400d4115000d81c00c0d42a80c05500410071050506261b8110307a036180d041582d207100174000c222054000c11410030004c2d0080228103d500c4509640c1e030000c03903101056002500800b041c0c800140c0c0320409400b203044840c1d1020400b01c5040d5101071400c071000d15011100403148c8001410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 939824451 1250 939823201 939823253
    0x90313080714010f05030c161208040c050f060414030f0d0c03080a1109060904111323031507090b0f030106030c09050109210609060b0109060c020109030b1f060207060912 75
    0x1440908d4449016003940c013201007005105e003040d0040c448030342214100ea003e902e11178041181d181c03150700c400e0807800081c07955280904090525001000815006815210311111602609820300c42400722000d1030fa1402000a12810300402d407030405403800740b0b21850010321102458070fa004a510644050703c0c6d483c1d070388807405c02180084c900b10384050424900401e00000142442800108440b15401200b4202c1c102d1000380c000c5524014080d5403640c04408141e0780e40708003166070341c0c2c48a03590909551482d82d401190140398080b40030801c0c50440000113011031034040c07042000b900309514002c3e110364141000a02010524011041d085280c1d8100441003001428049101c591000342030056420628102001d4211841c0c0540070031154000400c840348107813448044560142e685510451564840648480c8082d010301d108003040403040c1240d0300d480841c10010450303680181651450202c00038003030701194012082a1811400398004100d01103403100c244029194000d00d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 939825701 1250 939824451 939824467
    0x30d2901140705240a0605040b0306010509060d0b010902030402040e06060d06020c0304051201020405030f2b270509010b040501090e060105190908060a140f090313080714010f05030c 80
    0x1301c2c000c016542c02010440e6140341c0c60003c41c40c0a851070194110314424404a600c034401c000c10342c2c07440803041e9007503808100100110b1410310740140d048840942046181d20340c40d120b540300000240c000c421078940000610086084c00e10800e0baa03440700d00043e010500305100081c0e8040e070031a101800143e0042080a0b4001c01030044500030100104031014a100e902e0405008c0c1d005072203071038030034007800034419220b220200705881d60000268207070801c040050300d00e050440d0310034480810000985000301400b24014280403c0b007511000d071442052800f01040280da40580001c41e0001c4284810030a60760042c3c1c5460980d0039003001c681203503464800407a0300b805811803070010f1102405894425540112202d42034481d100103507505076540b04441d00554404190500f11120a2000200d180c44188212904030030018180e0b80703403081420401d01c2029664100d4030389600420b9042001800c007141e041c425032002e003000d0812813200e45018120340402400038540cbc1c41c000076480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 939826951 1250 939825701 939825703
    0x1710060e06130e010e24060922090b060307080c0306010b16080417010506061c090227040312020a0912020103110c0d020f01050403052704020d020d0e070305100c11030d2901140705 79
    0x205070009e400c0e0304000524050808004002e030581c6d2060182c0251480030402c50b1021400c20905c0e030300a1f0003009a07034a48044503001d07903c10741e0322441c1c0d58110003041c000103603900024402003410b0130560a0001d86402010708603400074048500c104810000c0c03d8101c4094191642c0303101c07038400009100410360000c145401484810224010304840d0451503a103410480240168000c1d980d03c420b0041a0401d00101d2040345010360104200e0842040380a82e0b040b0190030652061401080500004c2e81141135034000b039031203d003a46c0203007800b004280d504000354810f8000040003072000d410709480c043c0003446020b0003100445807402840c8113908002c0380d0203540d01b4010704110340c1e0300704041c40800207410846014041c1c2c0d040000a240ba1480054054103890b00708004d00850740d04641500001c10180400c03034140100d515100b0f803019001d0014108449901e0008200c00a11418031164042031502410058580461034501647c0c03001004e5070701c402c82402c856481c2d00d182041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 939828201 1250 939826951 939826999
    0x80717041805220f381e0a180c090f02070206040306050c0705100506010905030a020102120306030c1305041e2d02030109031710060e06130e010e240609 67
    0xd404170491500d0400710051409915510880b0b1202400c02031220111248502800703071000c01c000781e416807803003208400103c0e840c4c1d080707402410001042e000c055506482c1d079074601c5003500c404003014010018007285002c0d5241c265810380c000c514000c0550300040c0c05008500000c0c022650301c000041541c05850210f5050940010841d1106101c0300c502c100900001c6580da030000d148000c001900741400100c0c20035496058014040082d41001d060901c0e03000200107681c03521400c010610251143c41c8142101000840b01140301e103800e0070882103440400c3c0e405200844e520924101240150310b104c414100800c52108550190103c006a00b04200704042e615503e06443c5508041e00401400328412640d1440006030340c07007460205000096216280200342d04414400c10380c98404e004180c15000040e240d8500c6454041120003443e090b0006183c0344503802c103201500c0c084210900e44030301d91031455902c7c00440c0c0301040d820b00807501024021280d125121080822213555 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 939829451 1250 939828201 939828203
    0x40b0f070303090206030a09020f09091522150b060309030a0807020c1305060906090c0901030519062d030215070213150603050c120103020904080717041805220f 71
    0x541740c1c40b403c204001400502c25290204d00c03994400da21907006081410001d0b100752120780103032460b4102c401a18514820040420140e183c8281c603000200300c041000c041d40b00e028220b80d6540d070306400d03840000c9941d810400c902c580010302c104141d49800100701c8400d03030101d191150356a280e40f64180d14210f0341304003107640500c05180b010400c00842c2d201c90310a4004640d41d1071075450b10010300009400643c0c5a104906c400c1000040b594080d030000c94010035103403001d0b40308007010003042c000c482c5075412460b219a120303031ba100d58940d8481115031390500da141c68102c0c4036140d40c2c0000c00710820b8072a4031105201c003280941c10f544e02c0814929071401155001e01c1b200c43d03180340d0081442054018000464600000720b10010340f81003d460b0880b0703000c540c040041e400c0d5000c10040400c001c100300c0c1e508a0400a0000140c16490313040a0181c0003603031540c4032410503444021909640c13591020700340c9090100680d0103000c1d40c4001d1302040d50129004035000034100520310051400c1c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 939830701 1250 939829451 939829459
    0x2001020403060c020c0d0305030a1107020d050c0127060825180b0702090703091410060302130c120e0c030609060703110c030423180a0f02040b0f0703030902 69
    0x40c00009100050700081480c0d10f4641c00c2c1c6003148018010081011041140500040d4003440002c21304600740e44038440f031403d60030001d030801d101d9034000340402c00c08060490780b641061880b01025608001c80d224641807018800031000194203008406042a02c148c4041013000404211441c076403400351100421041d0b94584c210b1480100500041c1883c1003c042c9070070b68400014039622138000755420545c1c010311011540d142e01c202100500400c00302a03030241041100c104401c801003001c01c40342c0c4045040480c40b5490b41c01005412041c2420290401b821301000281c0181e00126101403109045000184041e11210051803c0e0008030724079003500c505001c2c409034800c0020410702c9264103681c24080c02001046845481c040d552503100c55a2041c4010b21105001c500b045c000c0400041030306500031000400621345403a4046004070006c101800e02030010040e00801c9442003c0410652809252503440c2e20701e48201c2410307c1090901051100806200343c00c607000640d0010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 939831951 1250 939830701 939830707
    0x110d08030f0403030e19031107030c0b03091e010507020d03020703080f0c0d020f030a0b01030b0108070f12020f0a08060f2808010555060503030f0a02061806010303200102 75
    0x3d804c01b0000800c1c440aa0200d00c2d10614402d0520000890a007960707444051038800038500320f86030116801c090b200905900650030310040c11748040c2840404044818008a41800c04a40c06404e2400507a030400c10117004002000100390400083ea4001c230740c400e9504002c0c4c0c2da107068501c0030b00a0343c055849080c00010041e21041050018500031405a801081301c111518010340444a010000328082140c00c80044c014900a0745003003018031761414241282104111030342c003241d100c181c803840349100104803803403400d900500140d0f100b401650342101c040c0303217600000c51309603646440c4131032100c00f42a0480e1880c040f452520080003000d0080c0b02c0c5007000e21211041310300102000c0700140c11380045020074400a1401480900b00c0018241440c0484020030b65442c0c51100c110a45500c500c40010340c4d0300c0c200024013611128501c01c0f5280c1c00020300081c2001c90290441c220744001c184688000d000109a440c11070b40d05041c044250050029450441c000900801c50154408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 939833201 1250 939831951 939831973
    0xf0e16030b120f07080a0507061b020d1401050a2f0712091701090804090207240606030e0303090c06070510060308040302120f0d030e01140a09110d08030f0403030e 72
    0x10b03d442c0018010040c0c0300e0864641d50440d5460b2105030001c4c0c207039031041008120042c024288038803202594802242c0010191700402e05504603a071040756103401d440c84081140000303101e00350300500125810b04c6120426002d03610701c18031003c01070700d804840b250300380c25240c040800c0365905540080300300804400b10310068080001445014014040903281000510044c80340d0080c1a41c0309030510b080c01e0410100340000d40140900701c0718107034184409100e11000640c511282450080f01103681800e003a07005003500ea10b2002850650701c1801886419200880c500700b408001b55040c031b4507044030f41001460103443c440286940d0745044004030901180340300801c152402520b602c400c601401c4981940d441c1500d00c206120741002c888040000d110390090360b0307940140c00003c19140b629040c90f11540906031103940026584141c6030003000342e0080f00c03420742802221941ca105045441e0010548001085800080310344030002d000c141c069480042c5150308035040760414014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 939834451 1250 939833201 939833203
    0xe061605030318120304120c05030d05060a050103090305160c1206090302011401030302060f070339020f03031b0714010b04050a05011505070503040504240f0e16030b12 74
    0x3e481c9101482c0c041424401e02d118006007804401d01d880301072a107199225140d02c48042c50201d605400c00c03040c6602500400d604001401001008003c0040c546c00d00504008034074105a22060615041203810404a40c2000039030304910407071104081444c4c12031400c2c540d000c00b16000a108490940c603c0710074404607a0110701401d102c0c2c3c008002008030040044030181c000d120040040e4040340024014060440106030460614280451300b0821840b80081501010708003403a450241c041810070f11290f4201c2481d01d0030580081c0580ed02002e842986034403000340702109186952541490340d180381070490302e0443e08100c2080103040005a002e0180440c0000b0511a41c00c200109d0002c0c049840384034100c50041303100031a1000d21040681d42a003081c01c05850501084c031000600c1c2e1290301500034210000e415407442d090071690310085124241d04103903846034118034144071001d01c80001a4000315926003904181841100031405440c1139480c5a80143d0f4040510f08a008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 939835701 1250 939834451 939834457
    0xf1f020702150c070e0f190906020a0c0b160203030f2206050105130c120f020d0606020a030809010b1e040f09030e030f0a020607030f0c0f0f061a030d0e06160503 71
    0xd0043c0a549401d6a00d1004021862096488811250019010070041030300040e144203d00c0c00b14101003030712003981d1202c1040303800c040312810110b10010801d10400c5511031041e0360014010350900506100e902c1300940ea400700902c03511900c3c0c2c074840443c201c2c3c02c00110041051072040031110a9560310710348807010340800c2c071480d070040140b240d12446500282c000ca080b84001c681e84e0b0420b0030100a4481e019140400c220284550b0821050045001070b0082e000074242940040c8402c00041c50700401d8910001c015040300c2e4900122030342541d9684043d500749956100e9039205640034240014000d15213a110f41580764548250102019001045900342d54821003c0e076102e10f0100a44030746444003410000d500000c01c000c2003002138010031110392010700600e407824040d850340c0d88032180d2400040303003030720b140c405200c0401c10007109000306c040083c07401188081104a0350f0120b551030b02015644001e1280014244440340ca0700c0c03055402109115440454a60240c00e01c20b0b241d034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 939836951 1250 939835701 939835717
    0x1803080a17070c031220030f06030c011d010c0303060b0a120c020c13050916080c0a090c0c020d0510110c19030c150609050405100606020f1f02070215 66
    0x28610740082c2c601805000321990554160b1260b424200704070814000034481400340058003020690101900305a68001d144501025003003190035091400c00c040c5050440d01d6814100050b602c581031086641d4204a014031400782004e2a082801b0700e410b81c09001c81d070300240281ca1010402c402203541c0b2054004980c05120400c20450040d4441262078120a082680e000702d1602d01000041070654449607102d003210b419101140c0704884c074003c940d91503a000a00603441602c207604a841d043c809030000304001801003180e0303d501d000187c0791110201019205980b0f013020041848000d00034200d440d00484800c0000d810099602080358009003040c601ca4401c2100c1c4910010b0130304000c603e2030350191120340311050b8a079190f42c07010440815440c031258403080c3c0000d1400c0c050150301d010350b1154014180c201350400d00e2008a0f80280d11581c1150300040015000c0c0388086081c480b683e01d0a0036616054540d2480e01780a40314101d002502310040d096182d08a440d0741d030250a180c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 939838201 1250 939836951 939836987
    0x2030706050f061011071703040e07020709140f0123090910050108060603210405060a050403120c0b0705131d1e0105030c040905100603110406050618011803080a 71
    0x541c0000300f0407108280004c0d6a0601c5a210080c02d03c8a50b0b084d140c40e0382647c0014003140d16040c0c8030010214904c10075a01d00d17000d680103210a00240c4864040c2c0c1e0310100c1380c14818070b86840c0407007400c00164418400e4104c040c0d4055a481c0100742450034032900081c000d080c645103414400441a40ca521070764604060916140001c40d2040703010070b80b51300562004009000b00a18000041c0030180b41d811319107541c040c104000502c0380c44001c0a0080c84440d40c0320a42c490349941010003480c0d42d140c03112001c026401075007034000b40190300c901e9000016490440d49403000b502100c1c14004164011180041c0d980207007680620b0040341c1107110b0380d203202d0061510340701c100980c0d1000c4020b02849606800001d0000810308050348081c411601502c00c40e040c501030401c500b0100da0540d04141c0304076502159003042424240500001444203640c40351800031000320070140307001d0282a0604003d01182c100301e00005281c845000345402402003507403000a004064004d041e0100c1103540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 939839451 1250 939838201 939838219
    0x8010c0207080a11010216060f0908010213141203040902030a060515030105090705120a091209180b06040314010c0e10120e0319050c0c0a03080d02070302030706050f06 74
    0x4000d1000c50001c00312078205008189003d80d5644200c0721151014840b8114842c003013a132100050988040ca0040416486030400c44041e0b960007000355569030020000c507801000451b0704e0b11941c0084000316000307041ea5014400408000134000c0f0001c0282c101544004100410300400d20340c021802050849010480341d6170b42c1091100b040505580000d2a1000b440100300307504049001c1740d4460307140d02c1c20f50b00d841c203a54101d10404800b940d000c2c0003a50380e1002d900801210184840b09920941004644185405480c40100000070b00013440b89440710101c43e00c0e9180c2c20140ca001c0e540c440c610400210000d80042d0082070350740f500c00d0000e0944801c0c0101410034101d00005a4915640c46050b000718074815405809464224196480304005509141138105842440c6055540d80d890380d551150303002a2411801038001da02c643c440c00c20400014101c1c100703d500100040c08050380315102c0c1d080980c1103000300c05003d4482414102000305152030b1280c0c2ca84119070840740440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 939840701 1250 939839451 939839471
    0xf0301091a060a0803030106032c060403200a1704030501090308191a010e031c090617060a060f020a0804030c03261605070b0406050421020307030f060b040c090801 72
    0x1c01c10f540d8440c0588903041000148506c5209402800c3d0f91560191203240d00400d07c581040c0d0101e414030910800d4002d0b03800d000400d0f034098908203080c0c203040410810011700c4a039013600d4107c48030005042400f94100d18010302d61060170740e8011070b0408000c0015480d1030401a000c0b45040f20541d100c0e004100341104c441107213224007860140c1884480020080b002c0040d584030844030802680341c4140741c032584c0902d00f81c120034500200150b840d44440f51500c103001c1c1420104180754210340598100700511a00d070440124220340c024500007101d42c44c0c0c824140d00f00154400f010b04a0703d00040d0210602107420301210480b1f110768004aa03030000f210b98140c403c6c125085071a01120304200750b08402d40c01e000c400000f60300500c181c400556540c1074500c5030b68041e03403003071000c1180458204580e0240241c50140c402103040400720741411580040e464030a18000207001300011003a42d0140300b041e03480841000000b03401003048551a8030042c210300150701c00c0c04019820401d03001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 939841951 1250 939840701 939840709
    0x30405120106080a0204050c070c060203090a1a030c03271509150123031005090c010809152d010302040c17161b030e0a060906120b0f0301091a06 64
    0x800c4503d040c0c0030b0040101c15030300b0000a442c010b4000d080400c428880700c0c0100e241000140000e24068004654075113400080c0598484030b0f034480101c40414044c00d0741118841000c803544220698500d40d5a940c3d01c8039446094181c86d2141d483c441020320030844200800101800f00f44c0b5100c0d54a402681c41d128100c0e5150a105005000d00710000010800000c40301c0c0c442c1d003041c02e00000010b1607044500820b2500e23441c0000e01c0c2e01c035502c803000d20810341d105000d05441c0c0701d03080c41c0c44078007440c2a06909a581c0315035840966400314500019640468203030080742d191500340c0c5003a91102c00003c0c20240d44c0750038001644140d150400002d4501e002e108040403400401840e60141c3d610b000e0a03000d481c415044140500504500240380104900c1000f20158421b0302d400d070f410004102400042d5840350003070424451150004d0106a400c1111091004070b04800416a65120130204000c85c0703012004603010340c24030301e08800b0016071005809415042110107011030381c0d804108 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 939843201 1250 939841951 939841961
    0x2d070e0118050108031611193b061f05030703050f01120b060604170304060305011a19090806010b090f060f032d0a02090306070f090b09120d020304051201 68
    0x1010055004110300266000030030b1700302d88458007d9622580156041010400011040b00790500c69006075605000d0007042c1c03290918990700a640f24560491044841c60042d100d5905210400e80910000b0740242d440c5500c03c0c00395481180c804200500c00c80300074020360400d684801c082402c01d00001c40308030315152098101c0c0c205002c038008004654490080c402c50142045400c014200004120300000c04204000030721902c00541c0d89a1400c08000e085840607049240444c0302c052090ba0304024040c01c2d43c1c600e603003a02c0061b00c0301489400a0b10300d44aa9404400c140c024800000b8070000ea0b100502241c0f03e096072003203600d41001d010050705100d00010103280c9641840414101c6c0c081c0c0901c64240601000749480820304500c072105a000c086508402c0c40d900002e04040500b428401c554001c0c00700d00b410303402982407010150100e0300601464401100c041481c0c502d603560941005000c10707264040c2c81103000f21700d0000751a54014000c0c02c1c09682c60b10224004c01c4814442e03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 939844451 1250 939843201 939843209
    0x11d03070b13121a1b0f07080f030408041d07080103060f0b120d0314010503030304060b15070b010303030f050f061203070c080706020f0f07060c0303060b0a030902010905040903022d070e01180501 86
    0x1c1032500303621880106c0560030811b001e40320305e14140240801500414011801a800f601c41d00d074032540351502c0101c0d0346114001400710003856005210159411180080c1900d80c014408038202c160242204028034500c0c00c1c09a00580f001c3c040c0b0101400459088004c40c0701b42c0c1d06101044540e03603041d03510042849190b816034810000500483c41c0c99000c9070061400409070a08079402030403401d1150007034a400d0314021a176100400c10190107210b692030021903444240510700c2c02c001c04120b001707001820180640c0c0d0115260600100520489a41c81e80c020f08107116135495810866565000d40182c80140c0f05800402e940000c0c0011490880564100240081420840100c0d44090f86003800c40916881d03510100d00403520300c010744640340b0281d07000282d181302c50000400c82541c643c0220300607483d040d810300200303602050300c1b10840225146040c08100d60210791120b0000090451424050a10b000c6252400c014043d170484440700c511038001603651900004580e42807003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 939845701 1250 939844451 939844501
    0x30209060405090708030d06060216080c01080a200c0c01140a031109150d061a0906180d08031f0f1419080c011d03070b13121a 56
    0x80000d509241c01c0c0c100550001030602516801070b03550480602d182c01108145403290b840b56010701503036504010444034a00d90700000741c80607190200c2503495401041c011410801c0d050b00081001c40c564229008040c1c1c62655281545803500d0015100c1c2c110400b005042d0090301c20589007584900071041400420030380703042c074001818500340c0c020040782c500b080d01602c0a201801490350340c07813202e60380580d4604803d59510030056040080364180c1c0c01015408038030003607030864800ca601c290782c1c1551041d501c03e580c86000c0d01c200c2e20701d8017242d04080d60048500700584108055280070318010540e8112801e4a0b40c2c0103000b95140014a014544c8000644071042260710142a024620404081c140000039065030320130103544115600f006440ba4424224180156400500302003400c1d00d0b41900648000f0305000a9218482442100104107022903815511550700f214040140051590000c2c0c0410605d09072400c0341c06c220283d000c2e8280d0800160710b000d21503800028582e0703210307 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 939846951 1250 939845701 939845719
    0x2301140f06060418061505070b0708010303051c0e0f030909101503020f1303110a0b070c2603070c0f0e0906010b032211030f1c120b04050406050609100302 68
    0x1488116202e106410718040d82600c8010020701400e01d90045060114181c7c2c0d502c0e660082814000c2040e04040c18003400c000c0d00740010000304c1e40c0002900c050300e581d004200120140d282c403001c0900440b00000310307140030707410207110740300300c000010084010150340326825a0f031503980c005007862051248580480c103942000c41054800d500800ca4070780b82e40055402d00d0450150030900751025041280c260102041414903407038040c40c150001e0807500c1d0443d01d84106030742d604814040e18425a00c405041c80360071191440c100741c1165000561400322515513180b0708181012101074813407944e2107841c04001080900034038400521030034550000b0030309039180036241542a40010180c0c500300083c0e25441030030320a20748210700d06a001e09050403010018030101402e088c004500c1017260303030241000204042d02c0450503040314095003040e0240c201241241000b60510881083d40145410100420400f440e484280180f0059601409039601d0b5440b913000c03a1580d001c0030358000c1d240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 939848201 1250 939846951 939846959
    0x1502061009020a0306120b150f0d11010504031407060306060504050105090f040f0c03051b1303150f020a120e0102040f0909080c01060b12060a0509040f2301140f060604 74
    0x160010700c075042541c5000683c20b6980e003106002e5006e40a011601c0308049428450310002c021450b000000007155032a82079407044c40041c440d072124403c02001000c54003c01803a0b42e02540a40d801140c210803401283c8000028032500c89072140160000300e498540e011800c00d12071010b640c00d40b00306071203d81c036011214003007008480c03502807076a610a40360f0a015144c1903543c050034035140080c0e00d010800d4241072404d100c003211800101054080180081d0038414880e204110480360055100324107102c13800080c0703018280c00e6030645074580c00040e00c010020f601c032181801c0e460300d02d00200015801000081e00340c0c412803080301011294440f044c04520f01c940c5c840c46402d842025414a418084d20307506e405d4801c2c540c00750002c200007040903000c80007010354103948580d0840700395010b5410f140000d056014041c4c00640984143d410740303010000d82064a044040e80740c80040780c10518445914080c14058020243d41d80c6680c020440300b41698800600508008110504007418 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 939849451 1250 939848201 939848219
    0x120109050912040f090501050d050309540906010501050d0905010507180e160503060d050a11100327020307030b0c0310060806090f0612060109020415020610 69
    0x1510000140c00340000d545007002c4000020301c0103210b000710b14800c1600e001034150440340c05a0104c2e00520300000f40c6070000d007001c000c480c0180d0080f240e403120040001003809408050440b40b961503c0c503c048100118a0301c1060281c680300c1e42c030f241400180406045c40c181b030050312130040d81c0c0d1080006000c0da6020314080c0c241e8043c407070700000711007000e52221400c2d1f5809603070102c00b24000e22240d88040782502500000b038034046400c022a0b050102034103607514002d510910400034040045140d5580c0d4050840409410000302c45900f82541440007800c01c5a040d250b00c58803103034205030b0040f8002e00640303030200701d01001600030f005a480c0041c0c3d03806000c038040741e140c05001c1d40880043e162184480c00350b00b4909403681c4a00d44154181d80c0d006c1d00740c00003011300480604010301941c50354801903002b40f011148000b10340380c0e0310105070164080c0c400e1800c00e0117148004600c0480d168041c03c201c881c00101c0178040e507900702d000d07a1181c01c00e490524080091140900c282c1d60 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 939850701 1250 939849451 939849461
    0xf12030c1e02030c060a0506040c020a1110030f090311010f150302060903070e090d17040b0a09020f0616050c0405160f0e1002030717030705090d0807020d26120109 72
    0x1c0540142c030f25003044280c0c00c0b404c103030044404424150381c5000303010b1641031910654800540c07900003070101448a0f141e00b40075180610300c091269490310100f1800785d12a4021451905107900c05200504080c600a010821915120959503103400c41d40000310b8041e000350054142299042e0000c141141c0910050750301003050603801d0f11544000007045007000d014544501140c1024004c0c110040c1e0004101c1445509201c400b007108d641808046201c10000c42e401440c1340300001508001403000c1460071140c003041c2d0358001c0d00495400351038090100940b981600c2001562040e070110010082114000c0d2211002c009502070b1081160380200844030300303100c00b820040c40c145203c20015003200341040b10b0344010303000480c1c0541000094522418641e844200c0d9906500d400c2d40005c0141c09214840c0c0d05c03954090003424207001c0150115005039030043d10f28842c040050501044944c807540c0301196100b809030800810601a5050721140c0d98403a0204030140d203003490703040141c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 939851951 1250 939850701 939850757
    0x307050d143d090c0f080f060c041503060504061e050a0e040b04060e010915051b031f0803030c0c07080307120c0524071d180c040308070f12030c 64
    0x42d0fa40d8040d800401d0080c01c4250040c00f4181c0c50054060810b11003d040031411890140300b42c1c030440170f111070980998182c80c191002104007280d42269000c00303e001d02070547c00660003526041c00400d03011400362203504c40c084240d11880c81e480e03889090000c031410501c00c211703000f500440400c00155098500541081c040c1c4404a0f050400c402040e08551000c1f10443d030b49042d46a000c00920101c0c085c041e130048151000180c1e1020340304180a40b41300003058100e00fa100f0044404103001c2d07400340c1801400c000401c89480345009500c0c901c1591107003200b0311981c1709055002590f94000011264450360000c003d41400c80080410786a044802c4401c0320503000e01c2c840003052840074031030082d038400b81ca501c0070180d00780008046e16289011144149101404003619010388a01250614410b2602841100c0303a6610040500340d00490f00014610300d0002502e4080c4040000202a0a8002c0112900d0050b11001c11342c00c4a41044203840424400b42d000c48264a200c02d616600c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 939853201 1250 939851951 939852073
    0x803040305120a0b0f01110a021203040314010501030c05030a0503070b450106030302070b0d180812010f05091b0f0d290108150307050d14 61
    0x9144610340c00b104100c601c1c41c50715644803110300d054a89038802c406801c4080c2015034409031441e012a484054805010f4022006490b00001122040044800858004004207410707a520003620340681401e10003030b2103002c4106008a103e19000c510498400c1c1c0c0040114508400e84c0d40d00e40840000810b83d80b4105400e1844244400300d04801005143c0c3e813800300b0f40d1a100c2c180380e52003030a40d40040f03410180e01d050700c140000380d000541241620212604551034408016100001c1c0c5012000a212000104510f10800c402030300502001ca00d440600740390303603880340812240c04400b0b10175103078490035600208551100000510011f890780003030781342c54103100c00c1c600205640283d00520129945030840c0341c08080708521908607403002c0803040603904802000078600c09018160115600d5036800084159804000c2c040013403501400100c1c0c070f10314600388034507002c184815900c2c1d90f0287c41e882d03a08046a03901d0784202c1100c4405c0c40da030b04071071030f6001c1042c20034040341586603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 939854451 1250 939853201 939853207
    0x20c0c12071d060414040503070b1006230c07030302060412020309010905061c0c05040f080106240215010608040b0708041211010212090a0c09090c05010f051b0106140109120803040305 81
    0x42ca4402000c0d0317911540c0070342d000307550b203141070710344111550001802c4a1402c2c1540c10180a025880005a9010202c00b000d02d07c012b82c42c50f9101c0d40350f00c100590500113104a100000800d80c000c03849500c03840c041d040614044c00b4601007640c50b40700e0f541c00503000590049052005141900123412400c0f112444801d01170000b825042c100c82c4c2c002c210501117080071034100035101c180418580030f00300000080c480345180c01d6082c590422008403202a410081c070f035582d1618401c0040308a161040d4450701c401d5603441801811900c0143d5058801804800c0090031041c018041705000d16444106002400804401100e40380c164580a04103550204038103159410b000114500905000c4080c08203060380b890007182a03501c507800742c400d8505200000020032848060901100c2e02030070516600100100c08540c00c0c80b03034600349d051020103407811303c000c4201580f04405442820f1003e069070075654006580b0304ea441d02c030f8210089143c0b80346034002000c440207075811078464104075003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 939855701 1250 939854451 939854471
    0x507021f020a0912140f0309030106171b060c0106030b1e04030f0f02070902040312081b19030204170d140c100c05041d04060f2703050904020c0c12071d0604 69
    0x30529030080046c181c140d001155940300d0389020321500c0c0080a82c40d12450291109011540c1c441812000b01c0c250017000f84091107454803403808560103540440e000f008115101d2030414100702d01503548a11514640409a6208001000321400740d40c060321a00f155481444085810310340200d105811401102d0300050b100c40340c0e0000e88003070b40c8109812213018a6151008206240040924070088011600d144d42000e481c0c0844400e80300c0a07000c010f010300341003015030207881582d204564a260b902139222031048081040030611500b55140c0c2c900d10720008400025003e03c900316049138101505d01416034480b54001703081e00505c0c1c10305c541080d50755400b000c17910071811030100d0880c00d00300400c82004050f11034080b02041030041001803114100f03140b51156903101400803006110101d405c141401003083d110707d51001001555281005488580c80e409407000803406003408100d50100c1240110b40d00b0180c45c1c1c3c1d00c158261042c0e146110f07140e0b40c03d0107402503070860f40e600c0d4150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 939856951 1250 939855701 939855703
    0xf2f0c07080606030d020d140906070f150b030102250f02120f0c0a03030e090a06030804080a02210c2106150316050906041e0507021f020a091214 64
    0x2000038a540c202502d03251034840d052508280c1300812190031504407680a0005a40081105606121441540c2d4071110210003150803840b500c0e40181500314a40d0490003000000280d82c0c0c0c1000c0741d0b06041c40f0418143c0c091500340d00a020000c03842560090789010456401c5814001017406a401481c0200c1c0303e80202d01d400d010268542c00c40e4200c2104800e000500300007600610000b550000785107461610004c1040da00c400042e0300c1941d010300851141c0600340c1000c4099038010210750380c2d0b10354a81c80c080e0380c2c82107a58120b000c1d00b80ca01e0914503403402c0b004103042001320b0302e0150040100480c02c00c0541c102158032045050b1003215176108030101040030a100300342141c81c541000104c2d40415141046001c41d181e10b41c0c0d8215800e00640e160400841e4000c88291000b00d11040c0401d0f440780c845540d00300b8015144d1800080110321a400900c02c803400c035012100d840300200380e00d0300109074400d501c51040814244481004950200c400400c1218010300b40343d00307582040b01e906 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 939858201 1250 939856951 939856963
    0x106180302041b1701080c0111030d0c030b0a090b09180319030501050406120201121a1f0801060507080a051e0d0516020708060a0902010c020a0603020304060f2f0c 72
    0xd00d0f84102d0180928000fa44c22510210b004c0c429102050780540c034050140c1c1e51054040642070420854040e170886d40c80040094901c5418500001c6c040d080e10340d50700500030807405200c1d9100c1d9010000020301c9440510542143c8034020f01300c924566100b26800510030306a48030307034160380303c100000588880c0390309084404509558010846500d00000c2105548068006010b065840d15041d80180c0c0c1040485107202c048c0400481c0c0b615004100c60b80448501d41481d422800c060b840c3c005010034002c070410081c07490740300c4044503601da08089903e4003a40c00000e203e030100700700155820b405400a050a400156900016160303008240da0603a00310004100310b954a031000c0c4031600581604c02503a0110130700c01011510700d482c0c1500d42e2804040c0001402540d600300550540e48200c001100080d001ba040060056440030010000e52040390165109480c091030408047c0d01409850340040c4401c2c41a03802040b09501980880d0010b0700c01d641c01d960400048860310414826 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 939859451 1250 939858201 939858221
    0x61109031b0907050408030304140c060703021f050714070206090d2102120405090c0705030a050a11030702130518120409181e0309030b2508040209010618030204 71
    0x6003a030148100080c44903090b400b400c802c091140c148010b01030681e0000581e68001d8114105c00318110701c40d40103e0420200b2044070350000c1c00010700109054001580300c401001d00c2000406401c1812540700071218180d40100005041c3c8544004962181c2d000d0700006000030001803421032600006040b82442c11021209442001d040024080c0300710f641080180e5a0f0014048c052811507484516100710f0113120312030b04140c80410100746080054a680680c080c088075610b48a6042c003a1aa030418290702002800c0100307410300e2014017000f5101c0d5160301400424803040401021000341200030004001d044940300500e82070101001481100b4152007000da503600c2c1400030000c02c0d00c043da4420f0781c03582843c42d03810000568a282c00780c43c0c06140c0c05d01d101c843c180c602e002c603180d448a030310141180c40100c3c1403100603104200da4044841322100c050321005141b6806076540c440407140a907208078510010030140d0302441110000200d10001c1d6a00c954580c1d000800322100c000e1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 939860701 1250 939859451 939859483
    0x20a15300f06060e030601030c05060f040504091a01060908060f060f10080115181202031009030905211b151206090603120304080f160b25080406110903 67
    0x1400f007020580051050301c81400c290701030902d83d8156100c00f04092035500c207081c0200e80010b9400725880303600303042d10080c0800a00030b10802106040081c0182d1091003618001d04110000040789801804120b08650f10b08002d0291580c8020040c600c500c00100500d40000351028031f0001030340c130740d01c10150150664640710140d50418030780349424081d1024041c2071207a25184a04542d0044000400f101d4208250900c01c00c2e1a10101e400c00b06400041c0100e18200380341c02c4101034120640754250b41041d125960001503010a18403a0800d00c2d888003081d42220004007a072180e03490b8030541c80c030400703072030f24440c6100e9101d44041984a18410881a400d4405100c0c0a20f401c410803504154203d0007808a10848106400184402381004090440002d24080325080c0c100940c1c1c0745100d2503500350b150100340d003403000100d001214502c40b40d0484513241c50000403603040c0100c092100c0e941c0d580c2d0542c0c0341d546800080407145c0360f40c1b910400500401c0c9141c0c0c3e04010060518500316 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 939861951 1250 939860701 939860711
    0x60706140712060902070309090e2802090f0423030c07170d0e03060a0c141605010b0102010e0a0b101e08010c0201020708071b0b0d09020a15300f 64
    0x441080103e59580e000003110500411414001c01d0780300081170b095680410000590540483e4024035044002230070f156196591030303801030a1700e550291140f61070300070351342050796940d810041c020004c021034000f01228032400c03815180c00c011254080400c03031081c04803894948007400d000d18145030380d44042c40413003a4200e0307411141000d20240800400030f04107049400c8a6100094070707175900500c060a01e56580503400c40051040081d12084644039450070f945200134084045146c18032340c4242c61a40c00c0c000421050b5105105420049290ba406403135041a00c2d503604081040107440340003460b0342c00e0801320b0b504c80011503072800084842d0350485442d01c0c101e840340c20740344007900803010369105021240c040380d54401180c1c1d4032980902403014500d11012a00c24101c919000001d59138004150090400460303400a44014000c85d070388413640390f541c10900c034186140880340f000606540001d0451810030001422500d1040c0202078186036455000070445144444040c107075a218 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 939863201 1250 939861951 939861977
    0xa02040504060509040c03080a230408060f22032f0d03050c090d020409061505010905030109020f210a03080f0c0a080712020f040b09090f07020c0607061407 69
    0x7449800002c0c0f205843c0c100e0149000e4482c45104d5115200180103480001800b607006482032480d40360141d65168110714040e010002030100380c03c18001e2040c0c43c0305040c0881d100b04514089684240e901d01303140c1170080264070041e0000c0040203821000d02001c0408120a040e06010080e0180ba442014640c103000b5007100c0780c48d101002c41020b051518202c24440610980d20465a20001c1511400a000158030200c0d00600d034008010304a20b14104454805041410a030021641c0c00da9400748081d4580040600300c0d0400803000303610040c80700801019041022030750080001c1242e0a42c211590040020300384800d59000f00d000a803a20100900c50045112841d0001c1d046c0c052282000f200c4003000d024030001070035520500498034914115001a0740403980c8070a034580505450340d40c1c40311169000c1c2c11024030244580d821000003090701d80100900d0b880b40c0c4060740200602f41c2158140002c07036104a10580303001c2e4690030b0340f0350f550f110b2012282c0118419a6481448424 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 939864451 1250 939863201 939863209
    0x13020d050c0d1b020a1e081927030b0a09021206061c0b04031404091814010b01080c070c030c240306080d080907121a100501050409020c0f01050a020405 67
    0x400d4120400000c101e02085049681c001800c0c400180e1000d40c0280a00c404400ca07a100c00318406c0092101c500000d003003400b1a0100c80c4001c0214182c0c07903a041c8001c519105044030994404068240003c2171800c001090301c0804003900110085030000301c1040f42d401051004110402c404201c7d0311000601c105030504008a1078407900300591280d44524564030b00c0c2d2402d00c060070290800c008100c1d071901035001c2608845c02011010403c00c4100c0c84c6d4544418280003050081e201d808011079050f0303180d94180980d8542c002c0c140d584030690341e511101e554254100407000d8500e40159580800012584022072000c0c0007183e644080a01601c1650b0341c070b03102074070203010400d800c048042104000000300055801c1c19418164240c3c0c2d0b8010030745150070f0351588101142c00d001600202840303d410451142c240fa500075144030740c0e854102110180310b00c2d1040c2800600204070401041c1c0941c4d000c0c1c0b0300c2428102c15a4010000034aa0b1801e6034070a4034200c0c0d6455000408014031301d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 939865701 1250 939864451 939864461
    0x7171608040e073e030301060f020c0a0e130302100c031a030f030d180219080607080912090f090a061d04050d0e0d0b1e071d13020d050c0d 61
    0x12851811000c004e01e00d8203686010804201c840b50540c2407440349911000341407114001c65031400044a44940e510b22000300303034900142e044009801502c46080041c20403038a13200c2a01d521030181090360720380c00450782c040044024241e0845c084c0003000762078003542c1e002c1c014254103d40e03404115000982415859001c0040740c04d0b100b6400086102d070268404400d80e10710040300f00c0c00007480414107546e00c5280b003081b00000c2d882901c500b40c64030042c038200c02e180282c5440c00101e40760342c1d9402c14280c1d19180295903021141e44810003014115034043d0040007040c070050304480c50000b26102181020720140caa0540340d0340c03200c1091040800010194891500300d4070808d101d03003080c1d00c44540300d03c0400f04280c2040004545081c0e1780d00d403011a2018903601c41000705892904440d52111b014800d0085400c3c0740b404808618100d00c5548240daa1109803840401d6040c018010481805180306540180703036028006e65003aa091441201d100301c0c0020f800541e100411200340342210 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 939866951 1250 939865701 939865711
    0x60f01060f08010509061c06051e01030b010308030a020d0212011526061c0605060112060302060d050a11070302071701063209090c0102160501020307171608040e 71
    0x1c1205441078000302e50007078601e41191400c1e68160516180c180c08503c010461081544510fa0309030303447c1d010820154080b80c07144001c2c0c0e0075000281d90800720405050381c2880080d00c00900b501c0184003080c2074000843d0803065807140189003045000c103040c20b0341c201c903182080e2a140c0100402c2907107012507404a544542d0324106404082090886074550700780d9500001c01501c500c0010800d8965082c42c40311007131420030362a2000403078a010b10152204541290018030032050700d2a60380c405000341010750b68018102810041a02a490001c2500801400f0b8954850140360402c9103500020000030b4041d5019265030740c1001c00c004813405502c10360360140d0385010401c001c038280d80080003c0b60410355124040d010740d9410040d9003003640d03140580d440440a003c0c80f28880000074085d5a41c40c081e029240c440d0392a106005e1040780600c21140543c000300059070010b9080201d0310199030441d10590700b011b5a0200d404c1c1d0514444000f02c4124000123000d0080301c17140d840749a402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 939868201 1250 939866951 939866957
    0x90605150a0b0c1203060310050408040f050f0d0821130b0907050108011a04270c090602100b0d1502210108070905090a2f0d080a0e0a09050405060f0106 67
    0x1000d920060241e80300700c544001d2913003040100100380f42d0765050285801c1c2861801c02480141014100300d0610b9000d40700d411200440c4500c001418200316510030001c10700109000d400ca03020303440b200041c2d40100310350305800440150310b00345400f090f180240211400140100031740541c0c94000300a840250a4042a41c840d40007008070b6030f400803090b41550f0804a41d5401c2c140d00c10050a114000c0d904034043c0600250400000980300440c15800d40e5060203040c48500000c600c1510a40307018080c080c01600a09445c0030041030b56000340700d070070750064041c0384103034896103d2450040400088640c11500000d40d20b94410000c06d82c2800b12902c100440705652401c18101d503900d11501c03c400000d91144009030b000c44e014480314002c660030120780c00d6410003040e1a40004108040c12001707101800d480b203540381c2843c034012540f4503030051036141313082550407007983c00000c100c440e00e51010743c5c0c0c4c6010544400d180155409588520003c21040c200b807a000140c5e400141c0001c810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 939869451 1250 939868201 939868207
    0xa081e01060e120a0506060105130f0b03070e040c080615040e090105040b0f0702190c0b07050114100b0d050a09050f100b0117070e1c0b10060c080307080a090605150a0b 74
    0x700305d01040458011f042400c2081d42c4001101c20780c82007801c0b0380d0040580348901071000410144000003940304104598442442032840303000c200c00c0340d00c41160781c000910240c000442904101c4a4007a000041030200d50410351ba946640e020304004458942d40e90b51542c082c4010071994080d029004074018107000102c0c41c3c0b02400035601c83d814010300022032002101c04041c4200c40e00031001074044144100d642e4010703424002e0290040c2c0010804949000000a0705606840d103440d054030310b48100c551401d414004a07402a000c00307454000340540e0780140c1e000040c000c011443c841c44e82c3d5000741000c007513801c052070701310380303039002542c0c1805981550410010604d05029522480d01c0c00c064050304468030200d8400d0309015208001a03d2200b140028003520780585e52240302d0b08e0a43c510060f4582c07500702c07020300c141c0d031000f00104003e0003c0346c00280030344003440d0712244240d0700140e03486040d1501003d0b1601039954085000c00381038580c01ca0308050005e01c02810081145c146 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 939870701 1250 939869451 939869453
    0xf0c01150f030b040b07050417030703120b01051e0405090f0405010f090201080c0309070506030106050408160503031c0b0a15030507030507021b060706061401110c060a081e01060e120a 81
    0x140c0310f10000c000508880c0040c0010710300500403030030368025201c0420f0402007102c000b54801c0d921b42c024402580443c3c0c81588112841c0840d000c0c0080f00d40c81a0340b43c1e400c002e00b240ca201d1a803900320740300d0180d000080c070010480303884e20003140d8422525041110024107044c2008c0d82152401e80c00c00051505122800b00580d030002c5181ea040140e03010312695079a55840928280010394002c0340d4030510003c0006101c540c02800782081d00d05060594072400360000130280e501e0180c3c414603800d50410b10410a911030468800f5541c0b0803e4030000c106801e540303001884000c0560000003200003505281c4084a80c580302c1c2c02d03441551803d0400403130425900c060359601c951004d00d421301d541d05910408907120501500c0e94650701071818403960b40c0f1401c0141c83d064242c4a11800154030299024048200084c1d04c80b40d0710002c3c00140c9488002901100c00c83c40041540c608041120030003080c00382c3c420601802000b81c1da490140c0c40c3c41d4031041003041500080d125030f10342e2200314410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 939871951 1250 939870701 939870713
    0xf0509120f01091e1232090301060512070504020a09081c0e0306040b0c090102030d1a03010b150a030203101205010906060b0c030313030e030604260309030a12020f0c01150f03 77
    0x101024100d070500c4894441003868581407020b20329019140741c0400e0000c0c02d0302d00112406091f01c500c040f0002c1c8940c1c3d8854050040b0301c0701c1c600c0d0034030669200840803c01400e241d030003846284403034a8400050b9440b10003040c60580080411071041c0c280c0c0a107100103983c01113071201007940c11009005203080986443c403d01030040d040722582c14000988020983c02041240d0011b00c00210502450800d0b6003c10500c110b80021a8025400c2688001492510592141c00007000406850529088420450003074000400c081c5000380142000b09603000c2c54605070340c4451280d4000706109a0614121050714450343c41300308808018008000c0c503500101c00c0d03950290700110320202c2030355181011169044104030141c2c160140605000074420710344410b0320b903030701004064810300301e15080080d050300c421580346000760418801401c00521401810b4039142110101505007030300c0d031000101a0b8090708402020b60756518030329454a0008a90360000d00c0311a171210345451840e200c0f1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 939873201 1250 939871951 939871973
    0x60501080610022805013b070b0c0624210109020405090601060f0e010503040b091e071703160b04030c0507141f0f0509120f01091e 58
    0xe58407600e03442c680d8002142c8200100071450400c541a40d8891400030341c0d02080c403a18650548003035003020b5411030311444103039801c01e41110300302e04040600d03201581d042c1940711400100c0940d003d0758000054030310342040031b404030155800240c0f2090400344200030f9110784001c071400c512245000b000d08a50742d03005c4061880c10410300702e14a1440340c901c409004009296009500c0381c80c01040c01240c00c400104507050750a243c544451a04120b003042d00e03101e10903e90180000d6080000800080c030710640d01e03800015030422030b6072550405210000075003070606074210640c40072404100e840f1108420313610741080400510f150a15a00c135101502242010142c95515118041000c051260590740f510713640203402c2d101c0c2c0c9901c860403a88225881071103907200b10f12804c94000c90210412034400a00c4454582107662060850280c490b50001c03540541c0c482d51009203c02c040714180400203030600030704000a60280d40317140c13401010f8410030740103410006410f91080010020100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 939874451 1250 939873201 939873211
    0x14070201110a27080c0a09140c090105070b0c0901020d1b1103120a02010f05070e130e0f15010e1b0405060d09120c033b120715090906050108 62
    0x1160808198841c1942518030f0f811403040380241128100007590580070550702d202480c22100502500e40c0d90505405545005100e8100390781c07070f4801309606015180040c0348190043c1009800e021160b02d48000043c000c6410500c1c800300015070402035a41800043d4090384542410070306540025a803d0440030441401080026007082c03896081d50100941690080c0341107171b00380c4d28200700700300034060202420380d81e495905020110b401c581c002d80110000d0b90001d4800712488018246941c0504546009542d045c01668107582c6072002c24400c0e80d102c0d04820791002119450803d03d40000700c00108116079505e001e44a010016406000700c804481e81141c6864407003980d028508003c040c50741004203814010003c8840e226004040c0051a80c0070340c540200000700c40c841a840f0000e90b401410304c4110001c4052036020200c0030007201c14401820b1420406a00401c5174501011604948580b00d005404040d1082c1c1c0011818094104c554061000038944000030300742106c0a00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 939875701 1250 939874451 939874457
    0x207061107110918100e1c0f0e06030910151809050606061c0b1c150605061e1e070807151a0f31061509031b05031014070201110a 57
    0x201c03841e46c00c0c42c10031180c800740001590446603511100c3e4040c2082d40302d11602e0012484100510342545091000d8034814000392019080511100030b0400081403410300d403043c842e95203040031400304213000c0504c4070300c1440c2c800002c3d5055142001c2e858a24001c21103840b400c0200062885030308603240642c040c07000380e8408151819417100050502c41e0195030070049403847c4d50090144032410400c2c810204841d24104681603c0d0360a1104502c5088242115548a6038100210010758001005190032802200001005280703000d8420340c0280c809036240040801e1b00401d2100000c0703c000103030361015040142c114440c014144c20707041c41e0010341c070448041c010611107803682c1d404060354445d50b21001e91a10401c42510f64151035081c030381000380340740000208600c181c212a016081038161108000a40303113584045080120a08415420b0301c0c01e07400180d551400c001030f03074007560000b5000c60340c1c2480d00a05983c10b000240030304110ba04003810b4010048a650841d034280207185 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 939876951 1250 939875701 939875711
    0x13052403070e090a0605040e0a0302210c031326060408030603030705010e07140a080613020a03060e0703110402030f010302090a18050a02010f1106010504020706110711091810 77
    0x5002e540c40d014104106821202420401241c50342c0c0b9880034040c1c034800c80b020494a01c44070901755456001c108014050b900c018402045a1901a080b4a805000781401450720700c2c080f5100f41907401c0704802e0502204942400e000081510116040c0100b40205010081000680c3e2030b07510040500080c0c5805000004241030352400d004507423509030841d0091041181c0148215036039a92842561079001700501c03240880d00e01072070324008031141400103241c00d403600c00d01260702986901c400ca910109400d80040090400d0141c0f0b17a04102007000f5001c807900e07600340400c1c503001c80f4480c1403041d481001081040c00c0041040350540b030301911290300a6940c90010001030801d680c00040c4a5100c035000300411400151104489200780c0c1c0e042107510507060b085d42c1181580307180035201d0700b00d04014095814641d002e000198091903002c1800d404031030300e0541c0c41d440108182c1e40040d0945203680641865071a250f007080103600380f80d200c80c5800c15884c0d110103218051800083e250 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 939878201 1250 939876951 939876961
    0x15010503071b0b0405060718050f0a0f0b0903120415210f0b1801030201021906150801020c0c0f130509011506050a080109060b030f0a0f0c020313052403 67
    0x426802e40740d8940c01e407039150180e28604003d0380c03a8070b0403581140c00703120b1000010300c2948102d4079041e004076044619001103040004000b0416400c1c00c000741c000d50182d10001d00f0260003041c80d4001c19262038215510001e4400385428402c00001840c9a02020441044100056958003112220380c2c502004808007070040c0403ca07904c151910400582052452321f0301c88003a41c014400c030801100c040340c801009081180c1110003d00c400b80c0560800c1c040380b0500c032000c01c0000c42c2240b00d003500094200c440700740070303c0c01911f903045241140e6020513007495007441005030251011080750b4681040c9509800203450f003080ca84c2d60301700d564595001c41c0f403c01c1c0941042a080b112040a100099182c0034014072a4101c002e025001888003000054038440c944603003029150706412451841c1c0e50100103000800340a481c00b030009a8400b100c6104020500c03840c03906a1007680910368408201242d000a03207001d400c2288a41200c9807481c00e01405002c00706d104e0852040843c0d140d07918 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 939879451 1250 939878201 939878207
    0x71a0f040215030a090c180b0405011d130210080106080604111c060806010b091e1503150d08090406060215010504091a0103060204170a0b0601111e060f0903031501050307 75
    0x7217000a14880900c131000c5107079030001007082e5011901c0d01042026050402c1084181d410a1140180c201c1c2c0303081400700304038032842200c1d42c8002d40d05544020103c45602003403000f080f030610b61000541c2d0070018081690300c000701c280c201504460a000b00c00c04802401101e01c18107031110308002841d5810200080c00e5040740005164280948042c4d694686c61440d56a0044441910610400031008200428001d420082c010090b00d08440204841e80c900c0032507201400c0515000540350203980c00c0d0fa101c29005280a108040c0c0e40d40350440b5406000a440441c1c1007401507420407800302d400c02c0d00b0b441080d030444004560104511800342400c05109690340c6a800170f154000c070000c401c0c4101ca400920480c4e101c070b54a0403203190040f020350784030300c10f00c0c00c001d002e13640c420081405580715140f8007840c200e05c001901e0400c03108040f0520400f9002c02c3c0d80740a0b4204004201101405403005907100004001030b40c954900005d100c410459641c00a6051103404070215000340d00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 939880701 1250 939879451 939879461
    0xc03021b0f0306090d0f09061d060c010219020f030705190317070c02180601120e0c040e0a0606060906020a0602070611040803070c050f010c02040509030906071a0f040215030a 77
    0x2d41500c449042280300c05448078503011a050200700042080c01c21684103d1a82048032500d54030000501c841d103071901600346240c031006600a50911103107010150170310007412600c4400b0f41040f0742110003840682840d4071804c00d00580c0d0814000c44003c24000304851103030b60710402d514042b40c0102d103020340d0166880c8184d942e02d1420038007088159074005203d11115030084030035a8044442c809004404542145d05500081030303d982d03160040f2040e00901c411140d50000e0b51040580d08010400701c6852a0140820f503201203841b400b031204501c07500313020b08104d107400c100d200e0418001954403241040c0040a4540c0000d044040c000c2950101c0030160b0042405030751140d40303c1100b035a075040340c44252130710b05410100007050b15000e1807200005406840350340c20701a00c1e408001c000e20300102070351281e02080080e079025646104c01400260311490700e001481c08102030b5501307035030801414007040e01c202605000150351142c1d808100702d14403180b240d50700d544543d4040090300f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 939881951 1250 939880701 939880729
    0x40e010207030c030e03031305121e03040302090a0507080c0f040e011202010807090f1707030501020d06031412270a03030207090f061202010c032601090c0c03021b 72
    0x15101080d2003040582c0101c1c0183c01038043e80e20f0724406140c82042640b603104610307860304190b1904908202904050780041700300c841c4002682c02021360224103004840800c441e00103541c1000a00340118509004880d403c4a460401048145002000038044035400350000c0c1022002299030900c581810040310702901c004182c0b4031141d6501e00440c06607009006049020422241c002840c80340f14003120030468000488040e500780c684480c0369159030700c01d003689aa5018507513020001c690240006c0400b80c6442100094491543c207090522103008408061503400c2000c100d18441038500c00d88001d48105414280b28003091071590754448001c0700150f4011490745000818540c010843e0742c11100d00020070700c0f88800301d003040e0381115032500038080d007401085210000755100301055a540c5102e42442201c004882c004d00140c0c2541c100d149010440c00d200502441d541c3d401411b00d0080c0b94202144001c0807540d010b074444483c64204145411210444031480d55490090304003d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 939883201 1250 939881951 939881953
    0xf02070f062a0807060e0c030d140c01060f0603060503031c050c12040f0510090b0c0d02130f0602070b25050705040e01090c0f050a03060e01020d0c05032a0706020306040e 75
    0x4402c4910b030203600760300a160140c551519020004105150104400c0d00070714008014040109994000b951400420a0031b003101030f0007400190942c103024811b0b040585918005110b205292803802011b9402e2904081c1c0260014001d0000c6800745415142c115216808003240c15990111601d8140c09126120212007145009001c144102c41000e0080c4d40d0180f02500c0c04209007030204070a03a100484002c0007003040d600001c140030714a1001e4261900c1030300700946000c0010316000107054850700860313180083c1010410140742c040242400a103044a100342c1080904200c4110010180c3e0130724004036642005041000000e00106c009011700802c104503801c5c10b00b20081c02040d01c0d443c111f509603101807000c41d00d151049001c2d011104002d0091001380d003103549440c050140c426a20380301e50740a04c441601314119004075040c40f0f045540d0306850340b6041ea00d14005c1c11070003c01c0d904192000c0c40c21600e60340070004951005030094400b69030798980d080480c00074020340c80b6103c89 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 939884451 1250 939883201 939883277
    0x415061d0d061d061005010507062003160905010801150c0203030f09030c091506070c080303010617070f050d0e0a02060c0d1d090114030307060501090c0f02070f06 72
    0x3045016841120303c1840b03050000c1841c50001c0095a8a403019a81e541c0980d40c10b800801c0382d0362060740149403040c401d200c08902202078080410448401034104040307480e010080051102c5068400b0229075410b2420581c003074501000601010418012440d01e4107503141140360311402130001070307641540941100e80d211000d0301458110f80201010718401c4c012048280210300e001918140034130440b04424500e252070204000450344001d1080314030303500c00d28000400a0b0140040c600138143d50311900384c107101d0114007001c0801e000b0210010300081400e0f503403005601400740d440c48550188002a58207401e5015403500500310350081d0b116100003140050741c5401701c1c2480781d01c21a610f0b0601c071214190b003041d02c04424550300340d4000490200410504500d2141d00120b1000075040d286018000c3c0c49210980d0402d800801f8595110720410420319407041c281c1d41d00d1f00d5548013400d510f50402c0c0001040f1042031103020b04012602e070341032101c3d00b1060510509042d00300c0380080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 939885701 1250 939884451 939884453
    0x1050a0515120705040612020301050f01050328020702100c0f06050702073f110405060a0b070c050910030b1801020c071d010f14040e1c0314060415061d0d 68
    0x4c21036219020381030004600e18250804802e140c02601d05880000300149001034018004441c5900004d00028110440444040c0318002070b4a182c60b101c2415000541c3d92200707030050110f1400040301e900e040007440740306000440c614450360321011354007180104007600c1d40e60040b4648100e6821100003c0e05200e00c0305202c5050342c4220150386080041109104884042151185440e140241080760420710400240c82c060744910f6200070003d101c0701440d80ca5910040017500724010880e0141300c031610601191800061580e4465080d015080c03401e82180e54016a00e2805480081110a070f0300c104803600400790140c070b00310410f060482d1a0259500241e5100c006610010f042c1d00c00b81e5800807a02040c4681c0303a40aa8007594240c0b0240d40401052000901d22400c2d003410742e004050115100350200814103640c1490f542d070102da2580764840064450502900c09841030f4507120041130480c050066405c03c4a2090810181c1300d00315a0700010248158101c1590060b810745242c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 939886951 1250 939885701 939885707
    0x412110102041e150807050a1b12120e0f0a06020d0e030f070312020901140703020a150f050c091c1a01030b0f07020705032a030304080a020102120301050a05151207 72
    0xc1d0407520403a070b004103131806908041d1140103041e00c0f4940040c4c4104210755075240a4480d040d80103140d0301c000e810340e10b0700382c4541040f03d074509500d00c001080e0005100d502005c60003625075844212014012441c04c41c400c9540e02c40428100a08460300441c1814040740c2941c030420300340c90f80f00700f0760360741d5442c00c0c1c8101015809500c0440108403111490b2842e00b10358403d42c1c020034410384803031000c1d04044804200540201c8800c030308500c074004d05080001c0011802d0851910890004607280103071007642c4064407402010140c4020040c480c0401c00c0d83c9000c1d007180880c01c0070125064000301c0c1e0a20b21080c0c00142c009440c2d2286203000082013001001305544950841e296959903a181c0f00401c1b611801d01d441421351580c086007031030a480300c82400c0c07a181c201c0c519198451101d180004039065803c03640c404203103a0420329410301035503018499450801e10101d0182c3c81c541c1000d002510503c81c0b402a18058802440022001d1000e88111b030850000340c2100c803107a00d0b01807002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 939888201 1250 939886951 939887009
    0x3070b040c0e0603070e04050c041b02070b09060405100c0501110901030518060412120908130506030f27160807151e26011d041211010204 61
    0x4a860261010001880450310241c0b5801010010084c2064903e824901c1c02681d80140060f17820b170042c0207110f80309540c0d80c400c05098189080c0510300d542101107001e410910a03034401454107004101c80c031040d54078a0200c8050741c0c0c0440d0400448201c240c0102c030b0613260b0000c01000c96107840c00140f041d10481016201301c0000b43c0e000d0015640795000510140780c90f590140b1558000001315000542d000482900300e030491400c98003024090f8090025038000c03030703c1a0341c034200c000792450328824422003c0c0050070050300d01d6882c604003d101c40341e03080310040004201d010107030700441c414400f000b0b511000d01a020101c61407002407081144603120144214a100d02c510040002c40346da1641c0c000f4244801d40e01d0b01700c0c01081c1d054004840018a81c9883c2c04c1200046028080141c8124010721a040c401c042852960411a1512001c42e0f043d1103100901c042108010005080c6414034030140d081c1e01d009604600b201000a01a00540c2c00800c2c41c480000c403152410780d41c036003407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 939889451 1250 939888201 939888203
    0xf0f1a0a021504060203270a0f020f0303160605010503010b130e0304090227030f190c05040c02030408100b1e0411030702011a12210f190f14040911070503070b04 71
    0x507c04a01808a208a20841310107040309495005200110081200340740140d45042c005890786000b0011130000a06590204072110001c251000401c0c0610083c0c0c824580541004d4000f04065407a490002e01d0301c901386041400303170310b88460440d012580207205580007040392007015910b500050003c001000e1b4000f1000c81c3c0f9904610100c03000e45000100b49501410540150070302030f071051665141501094420749034a032181c4000a0700da01d0b40c7c807452118034515400745450314100b00c0340504120902c2e1001d00040d040c146400043c0d03a98a0b40b050000c0c04202c00d0304010356a80f400718002c0e05a50740100541100803080080c416019002a444c1c00b8541404001e1443d0030000c02003814a81c000b094040c0e40048980350a02c0d01d40d01ca82d15401c0740f600c4c1401d0528218050740c5046911188504008a01c1c184488501030303046030300d0400301c62290900303100a80d02c02c5c0d100c0c541c42c0075911a0394a41034442501d1031080100e141190324180c1c110080c1c0b41e66000c41d0030452680101076034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 939890701 1250 939889451 939889471
    0x2041a0703170103031e02030405060c01020c060c04030210030506032409070e0c0f0f13060215010801050f0f10030506090d110f0a03140d150f0f1a0a021504060203 72
    0x1005112400842c010309050340d6058481c102080c500b1140c0820036000100c003030007036201c100301c0419150394007409000c200040724005607446841e890050b0a02c600034042c0030f05110144000c0c4010794a414120342090800e1800150740e54070240001e14241da1400c0c1000110480c01e00240440550310205116440c604101c0e0742aa954102c5d600802d4000c40d403400c0c410000307001d8464110408002003180c146046601c3d401c010004801e2426181030740c0c0002d015900c44481039101889182026004004040c020041841c0040c2c0305103035440028444018401e07144001a14030140c03a01c00c4002d10740040c200c4078903141880d612a500d0103040354103000306041c1c0780048a000400141d50700c0300c1c250003003e410300c0e48055605a41810b0140c031a100241024880c8120740c0d0503500c2088400c055040d00036403664903004c140d00e4401d415400100c00a110783c4014007116841034100c803040408000c070300d541c0381002101241410f1088261400000b400d034107000903c840c03500618000c929542d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 939891951 1250 939890701 939890717
    0x601080a231f0b250803011205010f1404020405091906021c2702010e151c022713020406091406030f0a150f120317060f090a02041a0703 60
    0xa501e0019000c070611811030b80c06001c1244d081e000c41c6030103812107518081650a803003001c56548240140e0026004984c03039090079600f220034440c9c00d003da107001e5800400304202400b842d81000e01d40740c42c02030010b40100d48400c04900c03c030000300030840030f01a20081d52440d001e000d14000002e940405040c4030031000190154403ea02c01d0310400c0c14402042071228036020301021803079004415404268140607020503c0485900c07002028050740d4002d9441e0341e559030f03911801541c088001c504140c0d019105000d403000b1580c0f0090f4115041b10000d40b030849207805c000000c1c50204010340c0541505001213000a602600522003034241c42c8490240d4580201d1a41403000602040b2101810143c0c9070021450f1404150f2118a60200022036000340c2c0d6181e4400800b400d07007940c00000b0030054a00c1c44804d05901040c84104d00361900c54100590928000044a000290901e28130404054003c43e01c1042d00d903044400410542d00d01e104d4800000039400302a402c2500b040e00410922 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 939893201 1250 939891951 939891991
    0x602030703061e15080702010f020a030c0f0c05070b0d1b2a03140d0906060e150406031205130f2405030708041407180b10020d080601080a23 62
    0x1030340d01e4041c0c811911007840803c91044c0d0440c0d08440c050701d02c5055540c0c3e20038002c44d0030414001402121400e840c08120481100c0004050612140d45001008160000680041c9002c00e1103800c590441041c2a01c1d2901440900d00900d140c100d582078102120018602c5280c004003003401d0349103120003004094082c41c000c00d445540654005002074003a9601d82c4200b040d84026106d00454040c0025003040345642d0740c000c850307a0b5041b041c40345001004211800840c4180e840004000355403e0084610307550b54147d21001c1c0940e0345081c0040402c4d5620706a551016030b00040a500f0340b80d1000d40d03511006c40c000742d4804559020041000316442e0a458054000c9a00404841d50390300026541c1d51607880b03074021000810000e5005202c0b0000300b0a24004d050b469101481e500010500d070b01801300f0107841e90b440e0b415000d40d08240955004680c0100e90103610507400c0c28a4585940c1e088181e8009084402030010085100d00b820084120003000191141d05803201e407510400c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 939894451 1250 939893201 939893249
    0x1101020d051303112b0c0b04060f05060301090305030a091406010b07050c0f100806120f071403010b0d060b0f04020715150b0d150e0403020a03020c012316060203070306 74
    0x1c40b80444c0942035414600d0007040d0b070306481505e07001e03241040d03028500e0fa035a43c448001c20f541c140c51882c1c82e940074500c403aa00744a410b42288044000300940416942c01409602004200c0c0e07881c00e40d1202610107000c02800c0c000c0d003401c108025620f079581c4500e10700303407243c00c07030070f0709980034403071544d08003143d00b048040310742405001400b1060900d00110b017280e00c01c000070011600461900c18041d01403501304a40d5907207100f078402520301c2c40c2c03c0c40d045030031400c0340c05041c0e80300c1d07030500a4580ca03549840c00710500b081d4014501050b107940c0080850050441150314a030081e100103079072000e100b4a0030b4030341400090000c1c14801040003000101a4052034014001e80240810001c0c03034052450344100f0502c02c1c003d09a00140d5600c03149280c24400803501074000d60800c0300341c00201075050000c1400100c0908029080d543c070311194a0101d260120045a101070010f50721042c40c0c1d85c158030403006984200d06540c0c07031800c111300401a100746e100d480c50382c880c964154000044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 939895701 1250 939894451 939894463
    0x1e0c01150b0702121606020c090a050114010c110a0e190b030318010908151b040e0403051b011e060801090506040f0c0e010f1a070507061101020d05130311 68
    0x1a40040040c201141030b020070890a0401404c0d42c441d00c64002c030340c90300140030400c0e10000c104580182c015240d8840500000010081040f40e00300d2a00006019a500040401d0702014082c84d19401500c01450301000000682c40203540c0100048000180102901c6407240700b1001c1e0001c0024080101080200b580c0b618150345506400034080854001c040c0a0000742c400814540340c0040eaaa4000942c100020401c401010307134500c8041000740058000d603800004504400b03e480e040c941414818060340107480201084800030745100c2e0300c401c0c1ca842100c0082508000c00100d0002c0c0f4060040c0710040d1400f1101300e013810800280f028043c07050a21072270300103010300500d50319540c59286135034401c0750032030740c039031401034042917001d501d44003103002e000c2c070440e00c05c26141424030642d410649034400c0c0f00320343c1c000c000010001d8800700da00421644541010155000c042ca4960301a005000100c44010b207440100409030014a01d22100315000e41c44100700040c4070244e0a44400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 939896951 1250 939895701 939895709
    0xa08040201140c010b210607080c0913050a0510064a041107020a090914070b0309010b0a06051c061a0711040501120809010905120d030b010f0c0b0c1e0c0115 69
    0x60080000230314418000ca026591054080701c1d10741c44c18124500084400040341c200e604419910400c0280b207011a1140c990003450b045e10b448880341c9001002003405140f11030040006001e20004504840ea80e21410b000c0c01003040304400c000100080105210441c50f02584918104003410520a14601c115411281c0140004032201d007450301800150070310b0030040b035107031903401d8024400340020301100f0302a18059441982d2030801d04441c600b50340038050621711810101d4410010301d900071084415140040c075082c07084415803c02100240015484011042c0d805500c505200c41010010309a4501c2150b14038100b440d60400c0c001111001d0041181c4c64030201007420100c0c00f210060144003605140c46141c0c07545502c0031500341d0004030260207003580501458010250580141040003100b8030b040c5a012070001e00c0181403510a100181c4031901020100d50700c0e04000c0704841035034600305520100d13291140021a6643c0c040d0740c019100e546001070410300340c00070344039070001c403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 939898201 1250 939896951 939896953
    0x12021923010810091104030204090b0f01050402090d060b0d06052707080607210c080f13020f040c0e06030c07031704080711060706050903190201050c0a08040201140c010b21 76
    0x314100f0f607070320780205017402550740c003120305220000050741c4900901ca0700346d00c80c00d2842c0d200d042090710b0030401501070b008184036500500607500e0984840448184490300b1600c003090421000c404a400800c0008010706400c1c10202086801c40c0e0784801c0c00c14000c02c4c01550505440c04d000d1481e1280d00034000d01d60540c1100001c5251035202c0c0c0946600c10041c00140c0c1303000b0500a4607201183c0c80182145e020400040c2081042d03119038007407583c03100d000101600fa40520350f000903c0130f01903066941c400d903a98001403002c3c0d0b20134066064030308000b13000695a42400c0c906845907801075070044002510b0101050009076955020030701a41d403100026090031090390b030b00c0501c80307481102c464116005202010104003640207050040903144051541e40300c2d54000d0345c111000c012004801e40e0b0401d41803080d440040411102280c900380361440710764a0380c2c80100d40c1c10080041146d902c4a01140c07900c614401036020160b210f608407114116954076281e01c840000d5084001c03401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 939899451 1250 939898201 939898231
    0x21e070b0309100f1e0b0d1b0806010e06090117070513020c0a030e1c08071707020612060918250504090602090f040e0601120219230108 60
    0x4034000090145070440c0b05201522480410103261404444050341c072403108980f640c0c04811030001400701072007203050800c0e040c84071203032080214140080d4214010144680090101e50a44900096030f0261031b845054800c0b039603460100c0c007c41181a14010b10402611000007286061100c0903800c0140307000292076194940400c00421000c0002018079083e0204201ca440310014041c100105110b42c813580c4602e10380360103000d50102e00700d05090b42e91000103c0403011a000c102503a01065200c00c1041d09003554001c0d503036890151000094000501103030007102c01d0030300e02d40544682403d036041e41e060341e90750480c00144812031264090540003440701d2104116101e215101a40c5031019103071485640b400030404071030400000385c54040d80850051207600d0405500d4801c158120740c2400b8240d001800340303444010601c0383c818812185500c050854491045507034041d10b21100c0c0c1001d00b41e0718403d04468150305a0380c0c40c1d040d01005400301403507000d0380e0740c80d0040c40c41c0e143c8581c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 939900701 1250 939899451 939899459
    0xe120313030308060303120702150f150402071403030f011e050d030c020f120a030315050117070c0206070c050906040908041511030a180f0e061c0501060305030a021e07 74
    0xd680f540140c1001d4150108200e2a0701e4074003403a8020b030045a03280d0060900d1000040e4000d410074010340648801007410702840801040014240e030031180440d0011390b124603038640103401c940100c028428500010042010f1700102070001412070f1000304803400d1218440c2c0344100420078a015040c3c1c40344c140c000307203400702e8400d041100307559102401c0c441c0100e03000b20004802045c4c0041402c141d80c80341385100205503050081d29074071501c0c02d20b01443c03542004006001001d01c04000894000a80005010b440c07051151120094000d09400d80d10340c071604180346a1841030007014025580c1d403010841500f440e00c0741d40140c60700441c446080a00b46000e1200c1c1a4800d4001010000101c4030361503000e00a00041000c01c840d80c6603900414070741c1203105080d020b20741c80800c8002c105102000201000303d201a84007104075500480303c5601c4174410140580321201500c40d44c60301c8000300401800000400c03014406400f228403070990700d0100c02440c00f100000803031580103070034200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 939901951 1250 939900701 939900707
    0x6031a22081c0e060925030b0112150903020a030e0d0f02060a200a1e081c1d0601141219080f0a0201050103110d11010e1504060e1203130303 62
    0x56450881040401d91a6602c1e00d12031410405503401c805d07680255410320031200d1519a40c001c503142d00b0090705401c41c590340310021644014402c0d40480400000503004100018200102002e4000000c10194409007002546c400ca0340d6012804210980700c80c0c0300300e140c60034080d01100c4e804111a040d036101e645c00d011032a00300700203038001d01c041115000075608200c40280d484021220060081c2c40741c0e4104110043d2100c0d000705041c0803030788000808070740d00408072011418000460380c82c8090800d040b0000300080640c03044038040840410249450200b1a079040b5a400c0d541c07a5140070032070702080340200e001814808681d2103207080c2e984180b440b108840909024a901300d040c0790b85083c022019520204032080103075524401441008080564110b200c60142c421450707616856a80307405807416826010705011a081d00800300d656060b00e0048a46000704225403a40e0b51401c000d03000c44014494039114006400c0b002521040020551340d0040c404e5000c40001e0349152016 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 939903201 1250 939901951 939901987
    0x11205130f02270603060f011503150f171b012102040306180c080606060a0813050708031206061306050f0d050114041b0e120106031a2208 61
    0x201d07000000002c81c0002d80e184000c1c0c1c0b403c488070280409116107411070405040140040c0844080d40d03160b0018008086049000c2d020180681000a041e0000d407400d0488200158040545071040180100d0100285144040c0785002c1f14121940381c954850540184500c4559290014800c80e080d014124118a903008081e1640e200c0140703801d03104e883d400251429a40701e000380c8140c0d100e91100b004000d1008000030400344003c0d002e6424a040041d20b24030410014508101d240c4010401204104401c2500150701c030080b51801c503500c00041c3c2e2280c1086501c40124140c10b80080d13414107003901120306209004080c1c0051604120007980c50390016108407207490014030a03250701170b00318421240a00b0724520f80c0c03100c81e20b29008000a941500c0c0034800c441d030300405000d403110782111b00310841c0801212443d20035400d003001140101029800505864080c0c0f075a1400f058140403c64090002807107a8070b15a03120303050790b00b041c1c40301c0440100410410002071058450106207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 939904451 1250 939903201 939903203
    0xf0712021e10090c09020c0304030c06020c0a09090302030910020f12030603030d05071e1206061b1203020c0601030f020a1d130311011a0909010b090103020d020f0a1202011205130f 79
    0xb000300145d031200c0c0b80340101d800038a0903150765880003e050040c0b1a110141e107000344801e01c01041c0100b000004600720b14254450074032242d8032822000c00305402172069400b507441c082c1c9403506661403054003e42da400340c1c0203200c1c001e0060221070803420b40d1003421a48200d1001c1c000b9072400050b01465001000c0040050301000b012150000780302c00c1e4481d090b41c105c0996035490300d0003002d102050044071911392103031084c0000a11550070b44c04850510724450342d0000a400003420407120160040c3c0300e045800119802050000f10400040c00d44502919009403040414681c0350705c81004030003078010708107440c0008540000c00750f4148210200540d03101703140010003442c030b2130082420344800c2030780d8804a07800341040920178207200c205a0341c0800e104000b48802641800411841e04040c00041e008202da2032011095460b14840b06104030800351000c00101e688000c0310b11034503401281240000c40440342e8603c205081d005040c010710403044240325081e4540d48007100030000e800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 939905701 1250 939904451 939904463
    0x509120304020904021215040b0612150c090d0b0117010e031e07020603151224040c0b0f04150c11130908040b1809091e030f0712021e1009 61
    0x1030355801d01b20b0140503800c0d00c10101d441c0c00ca01c1e42498503081c10203480042c5520300501845010660061001039681c40110180c0c4c10a15103840b0700340d0714100c0b4440c0d2003856421106050095041080c0008140e0490b2044000d1130407a54290400c50f00341c0e40d40164083c407030382c014400001c0700440903041c40e0070302145044035440c000059000c505560011510a214400440a9a101c50400300c030441a001d9803d00a0800322981682030b09803403000202000e182ca51711710010301000514515000a02054081d0785e882e4010040300e032201f94841d015140e484c045020901d071115015002d281c102607408000390885001000502848010580084100d142c03140c80c12400b040140000340082c0101803d80c6907a000324a030b004a5075119002100d008000b881c04001ca400e0300030500c84c1504813841a0240c145100e103124503d54001c08040000140300002e0803410007404842074a0744c23200a4003500c035014000603801d80b068203011203c503190380101240102d030841550000e59424401c2d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 939906951 1250 939905701 939905719
    0x304080f131203030e061f061b0204110403120306120314071406070f020a20010507150b010e041521051207051203090a1707060c090504050912030402090402 69
    0x10300b080320100d000301c150046590360b1003045010f1070900c20317030b640203500c40d04140701070702120703002410300060344100410001042c03000000301041c00d0f00300985580090003800389105528090701150301501c01202e0512811440b00c117903d00078040d040840d140c110110030200388a0302d0a4918554407039100c0020a03040004100144000d208040742c006010300800d11850a031030041c00507040c242c030040541d40300000481c00a030000c2c0801c034040003031407214240080300030010b0b1111300801c6401001ea10317000e044c44010369a9030340b000310461400da0f00d4410031008481800211131800806c10800f0084c0401480511250042242c8103005618003401c4800c0d1b80d1540f5086c5002400014159034001500500748141001070500000015440c189981482c1c10300c5503440401c0b05e4002d1082d10410104c0511000302d2042e03800c8560452420f020710038010000800690701405801d204a01d4200480c60800d4005040f61845001e14411443c41d2129020490314000042c4120303880041d41f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 939908201 1250 939906951 939906959
    0x3060c140d06090b0102010b03060604090201020c030d020c0906041103070810080d080421020a0f03051903020901021015031401060902040321020a020d12120c020a06060b0304080f13 80
    0x1900828644007200030000b0441e0528400030300782c9401070341440c11617042c038940c1000c9650202c0d1058001c4401c0b900010440110320040c1e040400241c60b59a01d40903c0221610752500030403000c2e1102e0088650403010354402c0c0400c030480304d600e4224010448180300203141c941c00341e0b600a402c0450700c81106e4038980d0350f81030703035140150141070000001d40780401d100801400280700070210b0301c6211240000044204025a10018040090450540c9050843c2490301540c1180c0f040d00e1075400c0044c2074041e01a0182c080e51180103414010300c03c803c024114181140304071a04101800c09071002c951458403050190903180140f108655a42c0100180391100d92006000030340c402d400c1c42d05002d810000040080d400c80e150401950414034042c801030b40ca010318851881d40c13103100c08103c8103e1001c2241c40741c100b554002052460b009001340c030705800107121401244512400c1c0402612103444200900065038000d059140500c260000c800c245030140c904030410102c0c5090807030b56 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 939909451 1250 939908201 939908237
    0x30b0106110f030f120a0b0d0209070e04050a0b1309110d03052811060f190207050f0c0a0f0803191202280219060e0703080c01050f060a080703060c 65
    0x1c200d184c01020400101c607400202c1015015070b0001c1ca40404005030603a600200300e50f491a14402032150043c00700044080740190004408800060406c000300d14040803039000800707901046521812075103106c426000582d014806001c3e5000b0440d146890a0800344401c0e0407410008406200c401d2010003004205101400c221402d0300c1640481000d00318805001d15040c0c0c0030130003e40d0062410000000e122009458216241d074001c03807180040790311102c00902a81100404900900456400e00d030f00020f5451781443e0111040480550345000640f240c1c400b611442c64150010300228440e41580c401503070344402903082c0145004510700b560ba003281d01290341c8102c0d01c0308090848501010b0034500103c1c12005000a140c0c031100a04000d01010352a20003c02440e11032400c6001d100701441050300031135010075200c0c0c45a0310100300a000e0320080342d9151034078a0050003e20145007a260301d208680c410380c00303080c40b1421615200c000d080d504003500240140304e84c0141152038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 939910701 1250 939909451 939909457
    0x40c0e031203010911120112020103021c05040302010b0a030b0c13030c080a03020c011d0409020f0a03080309190201080c0f0f04120c060e1e15070302031e04030b0106110f03 76
    0x440200362594039814030b131a003c1128610038440140c1340301405005500300d0340d41e85080c107403072842001440030401e5100481c043d00c40d0301d50f445502d20844075055039000d4990082c90246102790000c0c08903000d00c5047c8151603040d84400707071000a500b00807801c41c1c2280401450700d1410031941040b01610f907241c3e2070b4805082da01c01030440d1300c207051220038164107010281c06a05c0901e00400e01d80c1550400341d2100f40000316040c8612303620712200b011541c0310f00200058040181107440320580da0700781a0200d0f00212003c0d400c60144024030480c1c4007144001500f02981611407071455150690342c6c0500e80c001820708850072004003c1c01710440d001d00e001d00000c220a8284072203600192404c02c40481041d400042070041c0c00c000d8009558455481d0384198600740d154190000b030080003d20a085400800f01142000144040030b0681c00320041006442114800c0b801c0c03034a10311640034034800c1c1d00c0040c046c944100014040984a81840103290740f0ba1402c4998100a465041d42158 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 939911951 1250 939910701 939910723
    0x316110f0d09080c01030510150903120f0e03010209150a030623130605011b020105042102032803030b0f0907180503011512021309110a05100905040c0e03 68
    0x15032621401c0141103c01c0000b04491082071800344884d0400c1040d142000595004010b00c0e105a4203600814600c01c4005d10300850300403940c19040103030030101a0501d400100c1c0900022520582d03030340107003414001c03a0045100035181941c110b1918400301030540145005004251301c82030000f401c0c0803e0701240c592110000c0d2003180c000c181804004420309144030744a41641807100c100010713a041424820841e42000c80602c4d80c5601d0302c012a49441580c00524003055400440300302582100071080307050340b007981201c1544644880a070725040c1045101d04080c56075144003c00244242c001185140f0082c000d09034075030a00000912140b02190220300191104082200a50001d18154010001503001304426250404950b003440c4550143c02c0c0da0208001c60748007191110f007040d00c0310841040040104542d00c0c5002c0c82c0c01010b144417580f2480301c0720300200d110303d800080e030111003070a0b07201c01265600d05401c0c072011704080c403110350a2198520b103908681c2c03000d110350030f204 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 939913201 1250 939911951 939911957
    0x1621030e1506010c05060c180913021003111306020d05040f12020414070806030d0318020907110303010609080d031a10140705032a032502060c06040204060501050316110f0d 76
    0x25a8214448e002040d201d0f805251103200400144a0280d692a00b00d41c080740d01907903100b003c0003c101069003d80042031024a42c10320004d082400c8043c0003500b00c040e22415801e80c2ea00961200044400d40154011036907141600807040126110303080f410b07005148007900200c0d98400803441c1040d107030001c4501d43e0118103107074204103040c5024484405030707501c4d034181002608501840743d1801405000d00071b008400e260003160150340103400c482c0151924004aa07960360f1070b068020025183c80c410302910303106a03418456114040e02410403102845802e81c0544c2c80501d04001d003030b5501c005200140130300d02240d00d002d803c011008210303090046009542c1e40200e4125400d09140303070010f020302121000c5081d20340d54808400c5a52005140c80c441c86421000412a1940d0034440c00003513014400295002d0145008200c4500c11030084804011050f507540040d10244800c807a41490030100ca01602d0403240565401c51161307000a0482da1809081c02c02c01386010301820424000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 939914451 1250 939913201 939913207
    0x3010306020711100e0904020301140106020d0815010e1e03031308070e04110108150904030f02011409032502060d06290301030303111621030e1506010c05060c 70
    0x603c50601d4a4110240e02694109103c4814a1004045205440351075202d90301c88408181556025000380b1004003414241e43c8075541c0d1140080d40c2d44800c08035030301c04141c44000003080000c0001611074021410b8461032002800c440c06c00001e04600485103121401c07103801e500d2552130400180c881c41c180c9509508145090010741440e24107150710285044602c2c43c00c1000080c41402c1040340d405080c01c1254031520380d446000c0801b1803101005411000030401c1100303040c0e20103210f40c01e040c3d41da0000c2054801e00c00d096542000308031040c2040d40d1040041c1d030700d034200420055130305400000f880780c40c5005960020705107610074001000030300e0311560f0500614001c11417050310b400e40c55410000503e40200402018041448040e090542d2280d008581c003010030121881d001d0038903046c207102d6082d49842c445100781429050083d045042c0f0300469140a4428081e0703c2d1082c2008042c0c40400308205184000000c00d110304102c508000d036000a20100803141c001d05c40341c10440d407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 939915701 1250 939914451 939914453
    0x20c25030506151305091e01060311300312070e09010e090c0310060306060b0301030c120312023906011806050a08010b030d0c1e02150a090e0903040305070611070b030103060207 78
    0x80040d2881407d41e80d2400c0d80030400156030000f03100b1581d00580c0c038000303841c0351460460524004040070240d074003143c4100220040003c0000c048003100407051007a10340302d140d011030b0407003001141680c00c00450030042c000b020105104c19400000841146c440c4910f40d00401d08003815418081d00c3c140c4c50b44030900810415001e11000703404160b04107800c40d0324541320212821000d100d2000c45080b000680c0c3c0c04d162181c41112005c204008080d503480500101070401e0460301d642045000396401c04610310030179a80030017400f1840c03070401810031342d0070f000b15040d98003048003004001907544d001c0010a0344510701007000070701c2c90400000e040401a400c0c07505001d03100300550304202c040300c144000150350146041404002124048110b00782d840807420801e107400c801e031520740d40801c4444406a20280c5402682c03544400d9641c83c0d1036000c400c95507401359000040c000c1c3c001d0f60080c0101446011254441115001142c0b4626502d141d20083c0340e000303030010b952594002413070b80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 939916951 1250 939915701 939915733
    0x90307170d0e18041a0109020903030a0e030109050a05062212051809011719032c060334141804020c2503050615130509 53
    0x10020318488240d900110200c0d08503a4540014035440002e1008041040a042e10b40380b0300c0c500d104041d80001070103800c2a08200044c06014000109100210000441e8408050080d120032100240085007000e035403500684400248001c582c2e019941c1e4241c3c1c00119000b000210820b500660151209061420354030400c00d03107980c4401d50700b01405084a0005101e0490000910f1041c031300f150f1250f500d0401d201d00483d085001c80c0c2e0002d045c1002140e1040580395950204045008603140c100f01d107911011000815a8090042903401c078190316422011b60049504030211400105000444400240240c2040d603020302c1c8180c08216101c3c0c080310024900c415640085400601d080d080000103140c0c010488071400e55006c0031036124008100800c9008550700014019900c0340d01c92810f10b0b6540b07054507051a02c1e404907a02a0306580d06805500042d40e8000c03018000d16900c401da405030300c030b440d070464581042c1e06040b070074661446846240e00034580d01c0040c1221500c1d000e854 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 939918201 1250 939916951 939916963
    0x50309060f01061e0203120a1b08010e01030b0603032206030e06270a02040f02030402040b06160209041110030626060604050604020f0a0201091e0b060f0402040909080903 75
    0x1d1070041c040400144091038110782c0003110b00019010384104450901c0f4100e0039805520303000100780c1411418084980d48540100b5060401200e002c1c01442580404071140c035003c4c841d900494522a00500104820200456001c680502240c0c60300408050710884411710024186680da00048180403465242c00f402d0103003280403005003510f040c8040e881415220541d0340032030038241400d4062410005002d060000354006108029020400038400040d500c02c813400c0b48141d140c180012011324225056032028007070700c100c058121000d6800d0010800c8041c10a4440032024030310074401d40d448029100b0103030015540407420f24540040311a03202c080054848920180d40218123403c640003400b41c0d032143c81141e0100301e64a600000c10002d2160300c1031505500000920300c0d1030503405400c4003130028410b86a00c1c8421034004001c1c061449403007001032032143d02801141d81c1e40340c283c11541040000a10041c9072981da19110070440d940841c00301c4a8040c0885c580c2c0c010319081c405 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 939919451 1250 939918201 939918211
    0x1b051b0106151d091909021c0803010306110a09090c0207030c08010914010b0102031e12070203030106080108120301050402030a0e071418010e0c0f0c1504060e0a0c06110f0d05030906 80
    0xe03075144c500f00028003000800148446040e0907695030880e00a660364030352000d080d19103030103005003450f203541403082166201b40026600e0354200000e004000e0500c2044032480649540c0e507003000f5007040d14000141070f00c005c8000840c425014080082050303401d00f0070041000c000005441c0c1c14602d88481350060030318010b24182d1403d600c0860030b9030081b0494101c40d03005240780c03020302071034200e00b5000e0003240044141039810404000c0015000001181a0740090302c0c1c1d0303212680ea44030501c2c0c3c1d030b0a5941d04003650b5141400100424105034002d0340e00910421000301d601d5016188292030031900313611030b540030f01ea681c807801c030b5034107040100b845140e5208480303247c01d6042c489161000d2101a0518901290014100f22103803140415110b2075002c41c0165400c030540000340c40310031003042c1c6040e2515842c0610740440d2400010352445c41a6101505000f0280703080c5041d1816070b1107001000041c092001d1004511005100c90515680551071740d54a87c10000d143c20320304540200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 939920701 1250 939919451 939919459
    0x901030314312d1502011b03051806070f05090d05010f061d090309150c01020c010b0a06080714090a080f0a110a0e0103110d0f0507030201031b051b0106151d 69
    0x103800480c98502100b08825518007001020a1400e501310403401410702c0011120381030340608a00c2a15a450f4014031f0103031750000c0c404000240c0e5001d0352500c41c0802da4030f210114010300300514580303000d280640001d200040c0074681c15801d0707407166401e40d5a41d8400701042580c40c2401c4c0300c5801c04441081000e04000380c1c0120618106c028603035a07108a8403103038464000c5c2d4500c4403108403200c00301c60001d483d00000b9902d4410040d40b49001c0c14804401c141310341004203007c517041b4454010303a4071a9a95545002c85e264901e0300c07000440d807000f004660008d0f9004000f0444040c100100c0d003840500c0340c01440314000c2d80c24042d41c0c180ea5020706c03030b210b16804442082100d000c070101301d054070b0700810070800c04090380f00015051018110010140822089860b081c04408207644003164001c0c2c9041c44030059000c40403030441419010140400d00503c000e03618a01241e00520080c07801c000001202c1c0d0f100c00201111401c49610100000c2d0200840300d0514013505000c07400000c01d0b6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 939921951 1250 939920701 939920759
    0xc01021c231b2e050a0209060f2706070204051909080301051c020904080a03150306140a0b0d0f0203100e10060f060c03050c2107020f090103031431 65
    0x20610750f1216050300111183e0300d035004241498000da04454502c0801002c2c680c0d2840da4001e951000d0308148091020301c549811202860034024000300d00002e4000c0500303180201507820400188806407400f250020054205068950309224003c01140070702d042e030392258582420848406a410480c8840004007210100140c40d80c040c0305401ca940708102d15224610131000310020722803c00e00640200d1b10100000c107010050380a114050017030000400141da5110503502901c0c0509290b036084021b0703a0300c2c00b0109030b0802c001e0030014030007025502c0c561071800c0c12900380d618400c1b04c01c0b101d0300703c00704c0d65840300740c00c0c0b041c28000c0c03c82e055500700107450310b107001e4540c08140707a01400740040001c07040b28030307072080c4004001c05c800700040001c92103030300d0341c407900079003040030b089004500a6600f10154a49020180d040340e5261b070b5000050000321382080c806405c900c0d403c1e4084641c8889822684c0c604c1e880200c550200c6031102c00c4402d1801200c002d11640d07034a2a4400d6010407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 939923201 1250 939921951 939922003
    0x1814010513052e2102101b1a090c040605150c0f010f050601121104090f0e16181e0b030a14030310090e060a0e070305010f09050c01021c231b 62
    0x398a090b000e4103034504004840e180e40c082d20305100c41d1260320003003c001d0315123a04100c44840350116805540103070100d4004035a80e10a020445142d13000302e990144001061031802c441c0a001441044c42d00000d440c0310122411001e82034402d50400030300b0302c5407540104a21964403042080c0c000032070040a109401c00400c0e41c010340d214901994403003d89501c0721a01c9456a608080080f43c45d035422107802708030b1110300d03007000d030f910b40140466210111001c042404081c0074417440948000000d00201851203000c2c8001d1600072040d54050048401510200c0d111720300384010303008040082d42d50f80c90001c2002d41076100c0c641215000e47e00c2c11003d4081c0e601d00080e2150712001c0d048000408094501d40540341c00029803000f4000d41c00c1103100c1d510030100750440386415204e40211011a050300005a03214690601c003074a10a0810700e402e440c041c031814031030b419610600d40d244ad02103120850a44240c0c88001c0444109006410b101450705081000449480351030750340c140d1a0000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 939924451 1250 939923201 939923209
    0xe2503020d0c050d0c09060f050315071710051f02061314011802040b060301180b0a0e04080a0f0801140904060b03071814010513052e2102 61
    0x114080603008100850946042101c46080600070f0f00004007203825203106490f00100c2c45840d0701440070004e0500c440003d000165201480c143e800040141c01603404070015104801d038001c042c00100082540c0c0c669403602802000c60107110303c400e0b40d1a450f0705140602800413035020a001403185415082c05038242d010032000c0c0c0003030050080034900115804c3ca40ba04e0440921040901e5180080031504080220903549032644291018803003203523000c041001c90f010900c200e201c4501c058010015214859014102d00b15004003895a41621000426800101110f048840d400c000072807051a54000c0e04448003407006180400c13184d810411030356040600c0c5003025004600203000b0500f04181a0456014a440601240e08030355541a440c0c11010706a01301a0b4402c1c985242c0e42141d22040c00980d069030b101070328060310803140d8140b2600134000200909003004919000280f208a400030548103a02ca842c1180c001c0c50a19111a1803550f108a07100c20b00b541040c461001611 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 939925701 1250 939924451 939924523
    0x815010e010311180703140c0703080f0c04080d030218032a06041e03030801170607050c0a020a030b1506040e040f0c0f090f060b031504021602130e 65
    0x20f03000c40c0c2e40c6030403619400441d0074a000307036900381125040c000030885441ea2641c01581e526a04005c03001c4a5107039000039a8141c4940007001d000030f00d501d070005410080010b00a0340103a100b007074403880c003903a84c0445428018407881040010340c00040c2000c480707070780e5078106426800440242801e00405031800b00f258890b40780310070351090240905601039440e202a600141815100f0500c0401c0d030b40c0540c0c0345d40042c0d001c21004904a000003040f001040200105480d000a0041015494480c0161001d03000018881076030701c195080940144c91324011400154460340d121452800c02c80e10140004041c0c0f04010301030701040c4400c1000042814016400603027281c42c42810a0580c142806003184641000e2640507001c42c00041201c8140e1088009141c1c0c0101040cc0c0c0703403151802441d510054803100400d101c0300541a1452030198011301c040521110350a144041030b9020500c082c08400d540d84189a80c1c0a001d000704030305001c01d02c1e0700e500020b02c0c505141030455810140f40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 939926951 1250 939925701 939925703
    0x30507032405040b040605130902210607120e03120105040612080f030606130e0f0601210f1512120f0801030b07021005040b0610080c0711060915040815010e0103 71
    0x1a04ca9002c0a0280c9a940c00940940340c05084a030b82c501e000c890000184c80000001c80c0100c80d089100ad9450b80d01c1c9000c04100c0018401801503070f141d00d10111703102114040003540c4642d403590001c0f25080100010310540c001e558141a9540c584002c00089a00c164000c40044105801d0307140011084800c5540510070030318aa604e079214000882e40301e010306150380e030300050881804150b46008a9419105806d2003604a996545072401103e0014003240b8034070444aa00c2201144101c0e55000801c2e2404032500010300d50b50b545846041c03c8000754080080003862400d401d05001c04d070140040c01c821103091001ea99007810a005004c42014803018111800800100f401315100344403c10103900400700030312050419081c0001445001d07070700184654503031030a01e1401d40c001d550700ca00c203207000c10306a07003000c0b43d41d00c0c0d020031003a6880c14240e00001c1040300517901d40d110224055140d2065030310548560800420342d180c0040e0700880c400f01021040104049400000d030203040d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 939928057 1106 939926951 939926959
    0x120503030103151b080603010906050c1c0e0a020121020304030905030c010309021f030b0a090e0607030504050c010507020f090c1e031e04020d12030507032405 70
    0x46180780034005513241c00c804145006801080e250703501c914003400101710840e0f1640c815044403412581585c01090100c0d00004001c0345201032031140030142810003c170001c88078000e40d21078a6090017130400c42602030031602940c03181c46801c0c80b105905025912400c103440c000d404000e690040c14003c0c400e1003003c440640c4a03000b42581da0b07402804c0d402c1052491644032103000c59007003404041c140c96081c2c078085c07030300c40028040040c118890002001e9010081c000d06144014090000f05070a01d41800301050002c503058504803401d00b45a41d403003a141c0701041c601c2d2511821154003103a108200010b04036100d0080010b005010a480525140710b11501860700094500c10340900c41029070041c1c080c05012a20707002400200313641a50b4071282e4550584a441c0e100d0303500026141c02c24442680d4043c040c01e440800b51482d4002480c0e03011516106915540c45941d1003 = true := by decide +kernel

theorem cover : BRFrame.Cov 939748201 939928057 := by
  have h0 := BRFrame.cov_init 939748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 939748201 ≤ n) (h2 : n < 939928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
