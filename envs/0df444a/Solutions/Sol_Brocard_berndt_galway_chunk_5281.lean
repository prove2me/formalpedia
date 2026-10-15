-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5281
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:21:19.403275+00:00
-- url     : https://prove2.me/submissions/b5ef4fc8-bfd5-4e6a-baad-e5e8834d6f2b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 949640287 ≤ n < 949820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 949641537 1250 949640287 949640291
    0xe01060509040b0f0a0f031a010501021509030d05010605030f0a06151d15031008031608070201030b09100609060206041203092915042a140d0b04060f0f0306 69
    0x5160070b40c1ca00460b455a0100680040c0c1111b90b5244603030810741a620003070318100740d4a44400300d050044c0c0c0c98035060b01c4041e0028401e40d17140392211302c03216000908400680c04213009041c45a40c0c6809418000c0205035140350310790811801c0360181110142451003811b25041003040225091406480303003202500300240364841d69510041c5c0000c0ca6410300f5030051804019850842425000c1c5005918124148104a4952169665901c501003104070848901d0840500062191300207201080c07040c9400720f10303403544801250310900d064420010082140e28144104c9030f0208610004094910080816041584800c0e0201c40080500790801d500c4070080003c2c00b1080c13030020004042480020850198590f142e440e40809580400707810b40c214034824000e143c240280c80a2200c131015484000280104900040850003240420301c910201c4880014a00b81c01402084400c0300c804180104500c00708022603480350001109815903020501c40746c040e1041d810240d0b0381c01200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 949642787 1250 949641537 949641551
    0x7050703111201050108011d06044209050f0c012705120a050607171302011b0803010503120f180f040906140615070323041203090e0106050904 63
    0x441e9542e0002101c1c062958245000028403050545c04801880700301c07158410350703441150f0104c0e250b00f0b00b40da02030a01030151008654414244072035090440c100412084a03544091954402c90122401e11066136510061030003403210a204034400c81700c0070000f4100d00709443c0700107443c0c20301944400036119074011816220000940c0740f0760250100400c0c2240c1e580d6a4441036070b42d5134400070200d44d140100004903d10038091040001c8052490489400300c1d40d90040b59078010315100c205a04028901c21000c062034403000070984484d0044c074003d66690704040c141490881751800040c0c0d400004c225101c40c2d28407800a60302c0c0131903003000b4100a07404071000198030b901c030010444c1c1d20610700000712040200d15401450884d0021901c000c403070381e810003042040c40700c00030201c413040810030840b00000d1044018010342000204100c0342c220452001d00a036422a07040a2148501021010145070308154200010303c01006004034540c10404000c0c4103001c2c0700102802145c031844 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 949644037 1250 949642787 949642789
    0xc0807140f07031808060f0417090d0f171c1103090c100314070809100b03030901120603060504260c0318220c030f150303050a090b03010f0e060102030705070311 71
    0x713000620001c41200c0b17442c00c0c84061120902019a41102c80c16415011284040d20260560f07110000082039004103091a448006540d0005031003141c050341102950b61010111b4400f5041d29548200d0110410f280000c4860032030301c80c4803120142074410b00803c11f6550000521003140c08007564514400300c007500c4103601410825407611000280402080a03190b40308074030720f1248207910110741200c10f0618021044941046200d40c240d001049600c80a500414914001d40c150610008400750740751100c004403a0190780449000e400c2525069034500e1080092440450718007056241c03500140d0107658170320441044100900d0b074042664480c4e990f56841098407155409000742450300381c1c003100004c0a01d002c001010910744048280c2c648038a1149000312110460b8500159007103071001c1e40c15800840e008410014402c3c2e01044184602c00a54000c00421101e2440716007481200301002c1e0340100010704641c8144440c0e07000c0381c8003755500803203801c80c046500c000b203114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 949645287 1250 949644037 949644077
    0x60414030f0a060507080f06090c0a091a0c070f0f290a17011203140903010b0d0614010b160f03030209040213080c01020d02071e090c0807140f0703 65
    0xd4250300c8540540211030092200682201744910f5135683c4001032075454210f80b02d20f130344041c1c03001070b00100100700288400c4180f10041083c000141442da01003035403078040c3c1084001c83d240011482202040414240b41d082003d08003804843c8801154030f0f05107030950305900d080313107e8010001030420315041c001d0144440304816030988058160b64201400010340070140c00c8003003004030114030000041e42003d110700c0c0030103150b060750740e406603481558400b44070381c110f00c00e071039855503840c1186461035070740001d181a098852074001c2112040c0c204901e80305401640800c0c045202006034008130021144500e4110381c0c0020350070b006001d1410210300900981452680041c400629103111001000131081200c0c6004c1c03c654440444070012a100c3c0884140200980d0100d601881400e41c1c00d1464008004c6102d580c05d251a038803141d00b4242c1e403054450401044440040c0096180d0080e10013101c0c081c0e14484501e0505900b103000894811404090100b0003c2e0a5520b1124a00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 949646537 1250 949645287 949645303
    0x60c05060c0c0a24060e0603071401050d09140717070b0a0906030203070210240503010b09060d03020a0510020c0d0f0e06090105070b0411030f0105070806130213060302040f1406041403 81
    0xc00700170044952111240300542a080d0ba84904c41e00c1241400038100e248081001e904a030182d58150a0140c48600d003005004181d81c22103905d5030781c05107400003003010000c5400400200a403c04a0b00c448034499003010320a40201c5140758042004807000d64111000707000300d46a5180042e501c0d61a10000c03070030701151048959819040c004070380c5904406648580c003100143e440104043e0380c503402c0500700d4002d840c1d0b15407c2160740300060142d151050040742c00078040e0054800800345a602c4c5401d000c5551220103040e540880e4490218108003c0d01c450741d03415052040c090200b80c8405420800040c1c401881044000303021060b40c1d1052013a203c0b600d074010b4400082d400d192501140d41442541d0040c0a481040d00d03501842405004090040c8045d4455409070b07290343d814441c41000510074841401d4081003110f103404440d0403002e008010540c1c00581b11810600e503441e6001490b400444034001964580440d603450400316000c0b10210041500e0507035420000c81c0c203240e81 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 949647787 1250 949646537 949646603
    0x80106080703201e03190207050712080307080105060a091458120311120601180e010e0403030e06040c14150a0e19060c05060c0c0a 58
    0x100c0e49620840690f14015164400180c044a41c694040000b01021800100c651515154002c000c00c41210103580c0189400da01807020b030740c10f444d264204101300f41c0003850100c4581d0707800401c20040507031080719030b80901421141246411044030004180680500660b01c01d00020b24400c419136a98280100140340540169820f90385a40d5240009840042d410b90360440d000985d040c0f0040e4080900c0b50032000c01007456540e11094556801e6080f00381d948034103055a8001800303011200c100500032440f000d1094a03000d182c0540014038210740c807110000720900601c400c1c840310000041c0e960640d41c91080103016035440c0c0c01d049002e0846120030a0042c051142804103001c1c1d0b201c0c1250513114401c585000c0d65540100380800c03081c40a500d400140130900072403540501c129841c444403000184000e0310710444184040d00240c0c198001e402050540c403170541000010f00c1b0b043e80c8200c44d04da0039030501940d0842c10791103640c00800140065920102940b0082d0300c000c0c000362030340c0c07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 949649037 1250 949647787 949647821
    0x90c0d03031406030c0d03080901020d060e0601020d2f070b030702070f120c0605181201060513050601020703082206081e0405030f090f04092907080106080703 70
    0x15141030280c0105068480c00840d07034451000941503043c009104c1c608110041c081c800003401d01e80303044403081d0703005e018a01555001c00904400f00d00f1800385401600b00d000e00046241030140001e0f2501d540d2100701018001d840c00e1015510b8045500c8011404060340544507240c50441e0850620806802a001c01c034030201c14000e4040d0300040040c00d440400c4031501c1350079100c045006114422110007040180828014080e252094000e480700d41e8581c07150380940030054000440701c5454400441080e9035405041002c2c1c90096500d40039002070070820003050601c080000d4541c41d0700c0c040030740460b50001c0d0800d40418182401c03040c1280b500c009801a5031220401410680700781d420318200d0902e80c07290100002c5450900303018070751103c0114178140c0384039201c11183e040546440d601403211481003c15844500131050040d10072050004a001034650b0728007194003400f5500350f82072602082090082c2c00c44007240c15a1020704080b14030755200c032021006003803010401c41c03000d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 949650287 1250 949649037 949649059
    0x13020411121017070b0f16060b032a010309031b030c0c0510080a0506030a05060906010f0e0f01030305091318120516120507020d08030a1404020303070b090c 69
    0x44141c1c1480c2c000c03154040e030092490350b00c02890704a8144100c40301920380050208000586841c0c00078465200701d09946e900700b0004241a000324590301c20283c811546030303035200c85145014045040303003104400d50030710601401d100311012151000a054107156603549501c080c540103280c070440b92210001c80c04108815032500800078090154222865a507511002ca802c0c503008010720f54040302c0d5a9511120790300c2d450204003501c4040c02168145c05100b03403c1d00801c0d8203010b020b22482c802c5c1e00914195142040030350030700000358041c044112080080c043c0c4403418642d1641100d0301071a06507100c40171140041d22000c2448241e42010346494190000d0f00020710a401c1000c3c0210511112451001e401b52240d200350890601031215101c55500024039002002c80c2d00c40d444c0c6404c0e401d0209030f50200d103050400f11010f40d0884804420002d8140140c05440c07420592100a1611400c0c2540131a40c1c902890f00e000b040686080006098507200304008078032250001e210340006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 949651537 1250 949650287 949650307
    0x906010e090a020c011805100c05160c1401050717090a05040e0d0e0102060720030c1501090c03020a0801170c06030a0f06081b011808070f05040b150313020411 70
    0x942c000701134101d02d542015161030310342c62880001070704207400c0006040d011902e404004000d08031011194144641480b42c1081078000700000e104107407142868901c010b0400c408440c0664004540d00d04002c0704010100000301c205002d151007865440e11300341c42d0030f04600000d01000c01070300b005802615000c03141040700400114108000c802d92100c00c1600074003c01280c54102c129480c0020446a51201c869101c1c0034100c9056110303032005413030a1000395454142009100412800782c1e0066030018006146140305000090016081c11860001440d034042c240000500c80c030400001003181510a5100034031240400481c01070200303999260100d415402040164081181c2c28900303880450140c0b0001a0206521180803205145941d458011070303500c140350031059071014a480c130004841d0707020080301d409080191100f80d07106080a0034032040b50101880144501d0110110403d412070590890313400840c02c05c0442005446800460f000e482d101c2201d000c03819001036010781d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 949652787 1250 949651537 949651541
    0x60f0606030c0c1707020d061b260105090a090f03031e1e020906130f03021e0f1509090a060f0605030103031d271602030a020c0906010e090a 62
    0x140d4420751002c0201450380081112802c034010001056203207030000d036001140030900a4890342e44003d00c00d14003104907644003c00d452441b00344400e08a881031050f944103030480b080004003000311459220380c03a040703004100d0101061054500035000f8030080340600600e504000145e0340c0001101400400f00d103401401004141c0ba68400d103440030303000c00c000804a00035140705151040c0d034400b10242c0310758220000d40c06041a1079002d0b00400c18400085541d00a03900100765045116440b5840c41c014001074004040b1400011104981d407290280d9075503604000e100426101000001e8101010761051f101b205c0c001c561000004080150303038407803a000101907d405854100c0120741d503100507540d0380170030300000300440d503807844824018044490900014900404000b01c0100c454144010000d034071003070030120540f2070200000c0d0014a2500320683c806440154030300452042d0081d15481030b240364500c070380c1c1060040790240c2e2164041120440c40140000c0b4281401241c101c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 949654037 1250 949652787 949652789
    0x90203100608060a300c08010b01030c05190e03071d040c0605070507060c020301020f030a021305100f081503030c0312010b040b040308070501060b0d0e06010f0f060f0c060f06 77
    0x910b541e07001441d2410400e08507002c42e12a02d049004a150700c42c0107012440700c4c0a0100c50040c0b2425034030000c5000c02840d039005108080001914410000006040e41e2110344000d050240401c0980306100520349000c00c8986503150184030a42400006802c0220b40d030f02c00c04500741c44401c82d454040e042c1d0404d9000f10b201d00000000303140d90341000d46207030283d00405845034124101c20000940558a04030034248014001490300c1604003102c101a0810760b0341c2080e039680444d1510840a1102031140034040c105c458031406030300c001c4000c00c460381008102c4100180300b0301003250001d001c1c0c0030480141c001000d403a219603160b000c0c41da503034000408038581041810000950408200100e4064866103000b20380b40c141552240140d650101c00c00310380c03965844000040158018000d80366004004078007103400b40540d00b85514096040c3c0150301c02c11b00703103101007104103482a00b220855200d070801c190080c003801700c19504800c610710050019402c00c0025101d03002c1e1540048 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 949655287 1250 949654037 949654049
    0x41704150207090608060f131203050718182406170106090605030c0c0a020301050c0318010e0309010e01090f0e1006050a0923180405190b010306050c0409020310 71
    0x8082580d81c0c0c0e43c160607990284500c00c2e0075003164003c40c091100090003550711103070211b03041d80400d81c0e6645140c01c00041d820408006540c40041c850b00680c008001e40d01070402c421003c20042c2085441c0c030a8100340d820303a441090f0390b441440310b200c1645110100740851b02191102c01565128060119a090038a4030f140508a00010407840c1c0034080340000d0b034180350703225825542d0b034458484456010041e5008940302c0e0b80c13407400051b582406041d1183c01d500c03404686a007408000b00360341891895030300b2032590400c034514502c3c00002058881c540c20034600a5044501c00005840745519508035017400e01c0300c21004120403000a181ca0301449980c4801220107556017001c807118059500c8150020711099810040c140c03804030088a105d0707003c000c441c5008e0004001074600240d400842c40038041c444104814000140310b01401052020100c00081c00c0d10b41da40310906805000040c030650b034038404600c00e0f10340071003950041c00b103004046680e801c003002c614010081c188190 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 949656537 1250 949655287 949655293
    0x70905130605011e0e09070c061812020c060d1104050612040b2202010f1803060615020d05040b0c0a0f0602070215091003020c010f020f0d2a080417041502 68
    0x400e2464042d41c0714400c0c0d135025680705200420808100401c030311020341168100072a105094021854a11655090780609111703090800ca903450145804001c1080ba0810740d04000940e41003510354104580b210034140000083e202440501d004c80c42c0160741105400240104444140413070b0302d40745500444c0500b2031510a662680c54102c24501c2c5456807003a40703c0e01c54601c10041d40074042c2c0c43c500980c1e0741000c0c2e402941d0500d00c801c00808991081e202a501c40c001005040070ba41c03190401c68003144081e080e02c88549401030900d114610a0b00c40741c6800283c900c0d8008414004203100d075910901c40040d05002d07040c01d401a422020040e4443c40d101900c0c0441105141c007140c1071108050700c034205010340e181c4158001d401c40e0401c240c07039540318075000300644058070061407900c061511560303c071006200e00b40304441d902d41c00c0465034003038003c0350356140c05034002c02e044805042c604416a0303600c0f440d10380f041c845132032030701030a108000c540480c102043d400c010403040d0f03944d800c1b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 949657787 1250 949656537 949656557
    0x7080603010204050a0504021605010e0718020a0c0f0503040302100909050609040b07030e12070b18061902030703021b0d110a230312070e01080112150507090513060501 74
    0x10035080344124458650300c2030319a03508010b0b50500341c01402035013480e4440100c00c404981c0b522400d480800c0844483c0303410166052161098a41c031010410340070711011410301004940c0034280d400c08030405400642080c21140800c14100304480c080e560183c0001c031304030840d190150845400d0b003d0406c2e05414200007480a00f41101d94030301c500d801010f0480340d81c0f2800020740040941d480d03a44000d0140f40c90348403610400380c0c0207042061151142642d145003c2d1440c21000c4401e1221804640180060003500c56500c0f120700354100841c140142e40352a2504260001d00c52900d040002e5101c02c4094102100c02040d92000034003075480390074440d541031002546562040703400400c0700c1c40070030001c201400c00080007881c41c001d0300116403502c280c1038110031060302c1c102d03020030020380500501c400550340580c016005002807954030316413005643e01c03150401804484128210340d59000104214454101c480c0108000307040c4003000400581c406c0040c0c03a0302e015080c049143c40d40c1d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 949659037 1250 949657787 949657789
    0x506010b0306060f130f060503090a020f0301270606050307082505040e0708160e0a0c09052e050304050a03081b12060907050f070809042a0801091109041806050708070806 75
    0x42700d100320b24140c017510500d0616420064070b640040f8001e5091b40da00c4904040707005080623155240101c40004076124200f500d0158152089500f01901a0300f09010400410700b0002d0001c80740783d80c1809006000d0035680b940e00c0000b08503844281d0103414000030034071209020688a041c4c0341c0481c00d071540b10a41c183c040303681e103207188141e04800c1c81800c00290b0b040f2040c2e010244601e654604911002e03911000a00d081c1400100349103101954484914900c5220404c2c9a00d8821400e1090961a2588800741c4903012510060180402540011001900792200c503144c1071480044945560081c02103a807650700803201540110512004507600f0350090b01611002030080359018946415566002d00075008800e0050704541c0302c0361804410001115181300304c4954500c00300007585000c00c001c00518040e840502028500750b2245c00d0642d04078211061a28142d501290b940001c01145400407590080a42110310f0501480246a88045c42c10f020310f00540e03811441e6141c3c80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 949660287 1250 949659037 949659047
    0x501090204141902161106070204020a080f060d03051822020c06061c080705010f02040311031c200a06090b062b110105160503091305040506010b0306060f130f06 71
    0x190080280c014004000051440040218070306d001b6140c00c0c10841907501241c1030b60440010000420700d41070030403000c41e07000e084141e4400da04407064080c4410710386002d00b40303104440e0b407401d45102410310500d058460b002e14200310000c1901c1030050000b8007845200039040034405c40d0702030288070b01045c0b091900031080c42c03840ca104840c2002541841e0341d80c6260383d20207601152555200da01c0200480d855202420003140200f40d407080301306040081506001c1c40b00340d440c020700c0482418002440e4040009036040702003520000d071b420940c4040a10300903115400606481c1009100f40030070018013206800360000b580d1605083c80c00c2d10b25060891120103030016030740c81c00e500880c0401c001c8100b6220303803941070600c1482c1100403010311400890810042d10070380d000180c4101c090410041e0400c42d281106810442c3e801c1581c0d49580303824040c410100c0c5da860110104801e9070ba00c0003228418031524142070750f036400d4021113800f810480e1291a042c00311602c000610705000d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 949661537 1250 949660287 949660297
    0xc2108090f1b0118090e07060306080613021203121906080d0807050313051b09010611070509040203120307080106090509041101181d01050901080304060f0c0501090204141902 77
    0x1500e401d42c101c080e0800455070741c181c6682d0381c0a40f88000d140010884880e00c035414802e0b0100300505106410128094103459a941c00522103500410411919001c19121001c0712a41141c000020b40c030b05c0c4210a19600481808840c107070000f6041c0521540580d426440200004000340706030b40c2d940172f4441d103841c0922056030100c0c0700140040e0030309118200450303100d80d004e00000703001d201d6500c035140b424450703281c0e40407500e01211b80b540051400100740380c0100391038644084407582e1002043d1302c407a40b44c415640188289008181155000c3c0b01d4841d070300b0090b681103034880c17400080c0141048428810326000c5503440801040e981031007480a40716075004240d142502103c04011a4115210001a800030509031000315050031a20784031140742d031060300328100c0f55040408000b803014041e44800005c0e4010441089100d402180d040d140b84440d0804151100362420880d01400d06950003d5000d46031280c004103480d0b048a8850007203c0000001038074984e21000c1200303d00c15 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 949662787 1250 949661537 949661563
    0xf0a03051c02070e0c030a060b030108070b0903012706050105031b09040c090507020d091509060503040f0503030112060c0c2006040801050f0402130b0904030c2108090f 74
    0x40350280d289a5140400a075545a204840403250781c3c1403003c103083c409940030040ba00001007400308285560007090090500c1845c0e241c690352418070844e64440301841000701240d004100c580c8190380070b5009007031000c0490405c04500303c62460a1207501d810030f4040b10f45500c1d00b000820a401c0011310302e0b580300250900118601082010448800c400900407603c84281000101d92041d05c1c3c06914000c0d6003d400034109003007881e07009020201e96030042c0d00c040382c254954140c8250300c9a1100100c07000c41c01e11654070703166828910300c4807880c04030141c9203110000001600301094520003000c90b008040c1080420300300002200d481c02c0311100500700391019000c412641c9121184000a41c83c018038507440c0c030340d8908031300c2c0c01c0d15002c03284200c2641d1035000304815800c08071910300300f004010101b00018400d11001031035007403000d00054100b1911414410412625130242030003002c2e1114501c11850607020000c1c24028225140c00f040e000d40c03640c088030140c0009284d40f00d0740f4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 949664037 1250 949662787 949662793
    0x40608010e09010f0f0c02240f102d271a0301050f01080c0603010b0a03023411060a12181202070f2111040b1309020f0a0305 55
    0x1107014030009201c14041c1181820795a1801a0440c0218502c1503034544249082c3c08114200032010107400d040d0090b280c84130134002000c18a0003819107000266010900703558110795a114201d04400b002c0c041e0300002e22658000308441030720b001801c000956003180340441004113443d0b00502d804003080101408140c0704011302c09884481c55005100451104120700021030b0b4090b0000307080d85e0342900c40881000230b050060105060a22100740c85034810340f03400c0e00d076503d440d51080042c865015140201030340030400300c1c0c003020109013001503054014646041010341b03100c640071001e44904116001c0858060300d01803810300c40262034103106246c490f180c03001c2a07400740d800a0f2031180034600314071281d10206070009200c0e00b05618087c829034014400d840c01d081204000038805d40094081c1500000001c001c0001d0545444201b50700015040303919818401003809010083e040d20b602485400004165001540c46010f8660085881da000220038400780170100b010b038000070303100790 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 949665287 1250 949664037 949664039
    0x30c0b0712030f150e04060b040c081803191205060a0b0a3c02060702070e181204092307020a080711040c030209040b0a06050910050c0303040302010b01021204060801 73
    0x9000e0752020b4407500394440040b818a40b11442c15081003003541117440c0e03040c40b4800707201c107102c000c3c8105034540b582a18104014150520003a001d1040107003010f02c02c820549240500c00400d205881c0250040c2c10391405a50030346001401d11900e0000719031a145c41c0c440000d41900d4001410012503d1240f41d031403404404040482d040482c00140c08002e50104207268031611080745044a16902e0341c8107400200000c00b00203082c064060320040465011080600c03800c00100d2000d50059074140c51266000c0100300c0d01c5040080070114814294004900011452901d41050074007100f40041d000d00500b6011002d9003540003980d2080041e071010501c9000200d80364000c0034440d0041d0349202ea43c5802400150035240c0380c440ca100002d03000b09003070b049400e0900443c01802000c68070800320508080000702107014900381907100300485840211a203000d0301c1142c4400e100c02c403c0c1c0c1d030340e80740c1030030083d000c4c01328121054014803503450300f041c000c550002601c00340d071b4590b6581c1c0b00d9a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 949666537 1250 949665287 949665323
    0x30703150b01021603140d030e2a0a0f06260114030709061806140f060904060302030105090a0311030a0e040c030b0402030f09160303052d04030804030c0b07 69
    0x100002141c0300c2c10b6118800000c072040d20500040c00c020361003040158002071703001d03240c54108491413222405040c1040304500b04800b0216100003158100e45081c003000e0350344058200c110010b00c011507004502440081190b280982154083e901c103502c81400031040c1d8400201c07400c04036a0703c044c0d10140c800040c8880184000b440800f02e030001c0c100c603041c58036140301d01e0440713156900c80101700c001e40682100c110024003034103005001220090400c600c83c6c00104501003c8500c80a105120008000d000d60342c40e82d010101450700907001700414030f080b00c0090394805e03e840058020468041800f052402c000040f110320403081da0f0390110702074a80d4144005840300903000c40c181900c50f40200002d480340e1000e948038160905c0000d600e0308040c00007500346101900c01001e0807812420038004a0781000c01c603a200300c12010f000f04001d40d01204a070103988a80100781000500040020074000020003500940b40130b1401c03068030540e18400040203200e603000040808880d840c00500da = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 949667787 1250 949666537 949666541
    0x706150609050f1311210603011505010c061d01020f07050c090106171b120a060503010507140304050c10110d03090b070815060409060305010e01020901090b0f0f03040b1503070315 79
    0x2c00c0d6901c07a06e0402c0040e032001900c2c4403400c506520300c9058402001007500c3c0900400c28454006006a40c4a50800000801c00d1940c3c01d40540010b4440307064000100803007070980400740d4000000c540f07845410346504079607070080100b81d640740b0800004c00705a151100116040b95000c1d1500d0412803d4243d0003845200020700319206071911a480d40c2c101e1040390010105100c403240b9111003403078418044401c8840e00e401143c0240c8c5414200300e40c003600440028049540780390442d440741e80e5450314a14005142060540100310100c154260a40114000d080e100700303d8107a803018030044004508030340406401030240c540740c001103000d8901600d81d80e41c21074468199408100d20072307004240e1941c8260300c1195115a102c10400600400303110749000c07054808029498106100c000900c101e8050180100c06480015011041c00d00e50007100c0041c4950080d880e280c0c03900707007405041c04400f202c10038440076845860424504d40480d80d03009503a800710072541e100c0721018100700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 949669037 1250 949667787 949667801
    0xa0209070509060304060603140f06060112201317280f08360f0a0e19050f160513181a032803050706150609050f13 51
    0x510204100703061035503e40c0c800651055026000c0441c0480c61443d1910000c80050748406032030700112030441c0c0249000c01d06603002a024a88001c1c400c0382c06608000803c820002d0010b01c0c680e404c103241c042d00344c0002525041100c040725404940d40c400c03034a000d140c107500740c00101c0d4001c0620b19551070107805104507074020f600000188028103a8a10b90413490301501a18040004980d0103840c1a82a09881002c0ca103040a03a0355120035660420071855400c0005210b0b5902420b020b0341a101c02c54484000c1041002c400d03850f04190b0780d442c0740140c86007280e503081030400700002c0b0314035204250b441c042e00c03518206042307200c0c03178800c1101e0540005100540058111400007016042e9140c0d81034800101500000d928100f4200e50300c0107900c921200b40a40c00611104441000030705d0000c500c009900401036090f207440c541111b0a00c12510010705041c50310320421050b000d41503110055500c0b54544000103500c0d02d0130091601c03034088041e60b000900c60781540071300302d250304514 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 949670287 1250 949669037 949669051
    0x50a0311070506041110030603020904080d0e06010b03150609030c04050a0b0a080c040e0712120314040614010602010b0d0609080d0c050c0c0607020907030c020a05030412170405030a0209 82
    0x207030410070907550300ca007041800c1d41e058803684044107804840f4034000a0811180c105803c0c10440d0520b9540829403408000f813000c3e14644000c24240034841040d0403131440b02c0e0f10107081d1007681da15a80c20f070b5030540040d60480108020008519824207001c000c890042d20300038010309110815004000140c80700820b5600c084e03441c0d120400c0c260b200c0e1001280035000c1c800151120800c2401440111841d095407103420b6440040204401509060b11294803a008041311650304003443d4140d01512011000c09044041541000b084c407009134400202043c4202201c00240d030303a5441282621035008000c0e502c000c004c07107004006a180e80c0302d03034040c6106209140c18610600410070482d54590411800f14800282c480c5a00341c2c1401490304030002250b000b410080e0340e4001c9100c6203802030600b018141d80d0510b601c0140c0c020403400d00c0311a031100490f6038480c1c03100040c910007820054200d40240d0640d04244600b43c01c20107807000c2c2d440160080250001907002c101c100600a4862 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 949671537 1250 949670287 949670321
    0x60403270e06030709230c090a0605220e04060e07060806060a02010e0a08250f020d0501150b0d14010312080402060d05101404090f14030f0c07140d03050a03 69
    0x21526a80d0040b0244804000844c80c0c04048000c1c11586d01d07400101a0318109500300054002c656a40c90080c094825501e03103252145d040705010880c0c16441d01140100c0d18986000044c2e285061140d6442680702d0101442410806401941e484c01c15025000110b0ba00030005012410300740080c1c02000130034030020401e5440700c0d20490801c5c0742c160040c2c0d0f0072040040c03214900543e503554200044c0c0c4c041e034000c80c41c0020381c0f60104005003602d00203100e052142000e80902509403c0301d005a446034120f180c070a591004800c410390b01940c2c105003201d0034000104526100364041da812a6044007408880d0403004400f1688000f0041080b640505c040c041d62803219801e1103003c0c07040b5485420030b1109414205201c144500f141c0d80e4038819401d00141d07000046100709041c100a030310229082d50b19510451003400c40c092030718217500090700464021080400003440030101d503006612062007030132100610441ca02c1f03005010340812804c00c4050305180c8aa070107605201c1526003a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 949672787 1250 949671537 949671539
    0x72a05060c1e0c0f011b0b040206040902030f0a0f060e27100f0b090402012c0301020c010b150705060f07140406031b08010518130203060405060403270e060307 70
    0x60b102c4803201c0d0380c4288603503c02e803d520348a0a020a2100d0b00300f41c01d0030448400724403204c1c0f008025204810081c4650f0003003010900b10f40310082550060200c0220941d142e1074040311803202c49008032040800c02c0d090115980000c1824480e08080c4e502c01448000d180e0b807140c40808011103045209104014010780303070108501d0a02107030b0121400600049074856403020342d4420b4449803c9440d110316056001d0000607038001c4c2210403000e06100d804c40d462060317501e2111002e0304504085406500000b850481c0c0d9030b0651008000308030031119445018441c480914541c02039420003003407540443d010603211000092300b141c1c441c10b42d1400d1002d54140318400e10f0240c019030302c83c50200303440340f201c0d424003140450740820f1054103103003102c51589403400080300b0090901c040181c80c005100400d901d00040810454099009000c41d41c16040600c1d103907596107001c0724150009040480e822030000d481c0400000118050a9241d6280b401c150789507420310340140c1455414800c0c444 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 949674037 1250 949672787 949672813
    0x271f1a0705070e010b03090d02120a031503050106060e120601320d0609050c01030908180f0d2103020315011b050a080307090f081203040c0806040602072a05060c 71
    0x3e0501030700c51070540c182c80e41032030800d1628210004c0b924200303540000351903440b11040b0105642d011445c52801141900c20002d8900201055030006031155007480c0300850803603004400045031040c01d0310071400100294844135103c3c00280a80740c48694068030080060151840300100d502c2c0380c84600700d009281000250b4100b80c2c0500032504d1035110704042d4140701e400d000204000d1001c3c20240300a0400e82c0e1102e03620b1285500d48140026100e1104600d5141c9440f0001d021001800810004096081c84000c03005111150208800c010610a112500c01d00950b40501c1294a405a18108501c01500d00100a010444150f0401c0c0f0900000c50420803a1940703850164100d20740d2400c2580008142815907040040da001c0210810080c1550019240598040c41d400158481e00d039480c00600b40b4010f0f40c081c004230b106d02c1d0207200c24020503900030900d1a100b5000f9441c6003440c00442080185401c00c4901c48511045e410003060424030020301e50281560190b59005010708 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 949675287 1250 949674037 949674059
    0x3c0e0103050c01030c03141b270f0307120b070509030d17130f080f1308031c0b0f0409020f10110709050405100902271f1a070507 57
    0x19200340ca01c1d0788040c1c00b070502035800d0310540703a080403103140a1203200e1020041000100717000e000c0010188c12402070155140d0f0b01c0054440401854030300384901181001440c04403501700d400c03d4840d000c000c4102205140000d003803400c48401c3c2c002c0c1c8000a0091726101d480d0f86006010300148002046962207580d010f110383c0020003883d444400540c40345542e42c5141100051020304c4804d01c00c001000400c0c400790045034480da11420041c5d4070500c0c0354034001e40c0c0c01030707450600c000c00c00184045040c450101c0900f00100340044c10004614840c00002c06441c0c0280141d80c00c010f90500c1c03094a0304298100c40300c580e00113022003450740042c00104211050018801000030142d400c1301304400c80600007c0700030a20740000380300b542060f866854403440e0005032602583d40d0754810004644800c8024400300602c9907501000041b101c448050700081109d8507858504000d0318404c07035410203100201600c440c046101c0403e14400090500c550100300140d480344031b040400640d440342c02c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 949676537 1250 949675287 949675289
    0x2040302090c07050d02013e040f03050d0305071409031f060302040b060f0421060518011b0203030115091212020d03020408060c0904090b1f3c0e01 65
    0x10301482c41e078a0549080c00360604042e2080b5a0440e4100030300041d02c01020000c0c1c05040b2000c0801c44500c0f511500c1c2c04820107800d00400712000c10105e000101351001e5a0401d00700c0740600e081d204009480c0c17008504641080300d11001043c03215139450038811080015024040c07014044034111901c0f000c50090009454444148151b202e11003801142018040c2d030070512400c0e00d007141010446041589540207070700410701e01031054154415040b2000c981c0340e025540200c01040681021000c588880000c03003411803140d0300b482e00000096900303a1a20082c01103e5010b10308590900700700041e010403c94460041207041c804c0464114150800040f405104009051a107250348401900f850245005081414414402045020f601050059000f2110b85801f60344445c0c500028000b440c10940c06410359484c241080320996004d0800c90140000e00c404603082691103902103649510a1000b64018084004507805003420390750038400e446401e00315911880e00c0d031803624112082 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 949677787 1250 949676537 949676551
    0x20d08180715020c0d020a0911070f0503040302150702093706051c0b01060c14340602030d051308070b0f150612072c04270f060204030209 61
    0x4401107420b61a01045011030b0030205071250349000300b807a000110000c0e003500c0b4124041c1c0c0c4816800f00c4614420f000c071030900d540a550315045074191b0400a50703c1c0c126000c00ca00512a00003000d03503500b08001a210a81c1d8001c1144a46030707151600d19926510840202440c05000b820181d0300c1086640381d0200e00c4030f078000000e6038030b20740740c20000d0a50072004041e482c001c48401c0703480480c501c004130302c1c1540d096003400480c60f00603140c6017645490150002002e8044c0c81d020755440e000c0341c9e40f0024881400170049150202c0f4205040201490b4802d08016901c100441d0025442c2c5800041d40182c8110407040800c40f01e440e400305ca035101c6030040319007464201c1001034020f00c100b6440d808c01043c0c1e190300d840b0310302403010984500c112030074130007902200d400041001d44540c485040342e403200700140500780248584c03421882801d180e201d100300d042c220002d440f08045000070b4144260701c040c018103400e10740c5940200305c00900090700c407250200000710150329030400303c1d401008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 949679037 1250 949677787 949677809
    0x3060e180f0f030d060e072a020d060e01060608060a1e03020405071206270207061d011a061303030f121508010e01050f1503010207060e0d020d030606020d081807 71
    0x1342020200f4104c0b80303950002c03224500d401062002d2a9442190022503021102c4201c841d41d4210440b044e5042c3c0f810b10080d880b600007001d100403c205030300f00800b0002403400901c0402c0e203901c0b007910303807420841d90f041c0c2185000408020108464503050380207441000c80d10b40307842d00d940124040d5101100c401006c03400203001c003c1075000c0d82c8201d4000f0218031003200150310940b00c0c048080c9141d000390500694002c2240700904c0300c103600c09a087d080b2001180e80401000307401e02e01800c41d29554031401c414102c51501c0b10304000003114400707031103852840c854508503501500c4000c82d410307180302084030b103001c0780d4240440d5105040301600040c89000d0358903d8a8840c609440d15a03014051741d9040109104001688aa0850700a00002c5112a6a410542c0464024050120080d100c030381840010082c40c5e001240041c4211000d6081d100f803124609020303002c0e621184100d10050740300c6801c1060180c42840718030f4000002450302040ca052050156182c040140c01c0144144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 949680287 1250 949679037 949679047
    0x90d17070b13020a03060b040213090b10111504050f0f1b01020a050c060a05070209041203232d070f0f170129120f010603060e180f0f03 60
    0x31542882042e405031014819094001d010340c0071820b10040782c40001c040c00d40741d01e10601150b4443d01540c02c0c614030a0a00e2070344071307500c155043c05411080c41850088412030200000395124640e914140c280c01401081e01d581422180000200700800954403800380098211501005120689180c4104002801100b8000908410070552201c400d81035600100319000010000f0034040c002000442c0ca1300e0319004042e02c182c130a44260980258402100c008010070480402114140314480c0d607030400007014424005003245c24202c40160b0910a00b0000406000f041c9a80141c0200402900b07184000c2640d074034030720442c00b580d4510101d0007008050100c10f600c840100f00311406490030308243c080600464050400c1030040d00494619091030028808002c0c03c0401d211030300300103496558900e985044d00c42d09090f04d80c04000e003600070001900c54441d001d80130944020b092407c2e0380c0e850710145052041040f5508000d00e0040f400c114401e01801c0c803070401800002030245a9507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 949681537 1250 949680287 949680293
    0x1020c0705090f060904050705121c03020702010903150f0c0206240d0206031312080907050d11040203191a1c0302060403050a12020a09150f050f090d1707 68
    0x1485580009000740501003c0080c3d0241c003850b6150442d81c192401c15103501c43d4107043d414030b82c041d0812a00010140314015003290005454080c9110181c009400c0d441d115200710103a1141c000042d0001e90000024000f0034480000050304204031440044c0c0740011103164000c0d1001d52213041c026030030800030068503000e03200b00071034811601c00c200000c000307d00d40010701114002c48003038080d07a00403000900e52146003064840041d041484c048220b01c045030001c2550f241128412568002c0c1c5000103014201003100350202584640e5002c3c2200400080c80001d4000038051784441030801c1d60511140c3c0300c0c4c410b4001303181c0002404482c40074604140285154410000a08801071442e881f001c282d010540c25081641490801d035643c103139290441c0c0d010000010455141d01c000383c210161604070040c2002c50300742c401680d181200340c2c0c00c01d44000c1322100c0c0b10307030108078204901c12640401000401042c000200880c0d030410b440c1e19925401808802405440000010700c5428 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 949682787 1250 949681537 949681543
    0x604030c0b070c020d0f020405250c0302030d021324020303070309020f130b040e0f03030c0f0c0d080403084f06050402150a141b0d21020a050f090109050d0501020c 72
    0x1100c030002b6900007003c0140c030200180d440400e001d03001000301d038607160b804251080c01129000d00380c041040d1b45414035513112203800c910074460742140c1c80036007502044c0039500c1c0d5640c07100c0b0807458010b5800c0d5510200260060000d650017240d010000145212490703586944c2d10343c3c01c8541c4140042c3c410800c2782840101e03229030360101555803202c8048210310500104403584080d080103090b880d81d0300c05e102000c8500070f581c1d404c4018054018100d000550080c0d2140c031441c02980c5001164459040203ca48080310b81c2c40301e02000d10f95001100d01c50750358000d514410408030400417900580412000003002c04004a0f02c26480d4001d0205600d0b00f60310154103103a000c10034500e0f14815010146c08450200c55216000801142c4000c900001081805030146680140c8007400300c6200000c1100740004034141c1c14010105a850486102d07100340c03014180280c0320545010800c210b1440f00da0001d544150400c070200102081d246c81d01c00b254078480d403103040050b80702c544890501c1d007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 949684037 1250 949682787 949682791
    0xb19030e0f030301120212030415080606090f091f0f0305160b03181207030f030507030e0d0309080408012301141c14030f0409050105030604030c0b070c020d0f020405 73
    0x3559a100340800700d400030010040700e0464400d00301c82c4031992554030116001d0b00300d20201420300d000126001800c03a0005042c01e00d004856a90301c2c00c1a59071008100150041c201081c2d000a606010482c140c2045111141c10901d000a085083c2000740c80c810300010040d081145440d0000701c040003004400c0055804243c0184621100f85061000040d1240001807204d0200010050743d40c013070f540d0900461803200304100e065541c440b102c0c10041d0008400c90442c070f0009103880c00241109220348a4082210119006800f84554800e011006480f070244280c4101004000004050400348601c1c00b0300c1100085076000d0b43c544946005000005a002c21103c1c0c0b80300c5401d6000d542c0b06100c15070304144660095100c940c45042c800d02d00b055180c070300d400c0ca200c0014540c00040c00c030000f0300220340b031045083c00140e8940c024152075600035a402400f080c282c95105000032a22804a580030760f41e85020703000f002094000036820310f00c04201b40e500c0404030011405608160299035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 949685287 1250 949684037 949684061
    0x604080109020a080307030e0907031112060906040509190305040806010329150103020f0904060b22080604060b0d1502030411011d09090307020a0306060f0e0c0703030b06040b1903 79
    0x1750820200340c602030f100040c5e100110340b082c03d000340020f00c018002d52200036804014100907403502141d440d10028102c0a0300d1403440b414415001902d20324150007103510421200d40505014601c4000b1200401c0441008a003840000d0002048401c0c007001814000c1d80190010361064000030802c40c9400b81d0740080780c0b520f0140804200d101c1003400c8460031203002c01c0c42e0042e070781c81100c54040541e006a1109580c000e00304440018010102e001078a805190901915030303900506000190408241c07040e85d415400003400103010440c03e6000701c0384134001a102a4448080d596102c0300c4d080135495038032a075a40442072006115010301c0300800b0507002e090560248619007482c81000009200103846299443c0004082110520984400d40d501800b0030707400c0d645901e8014040c01d55402028510828090300140c00e4280f00300450140307281e0f107090742c600034032034504a024014844001790450802c101c0044ca1072600380007401d0118007082e092010075803c4000600b6211005054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 949686537 1250 949685287 949685293
    0x6140d0f06170607020c01260a060503190c03060b12100f05010f05090a0c0e1c05010b01030c14030402030309090705121b2a0d17010506031003150b0604080109020a08 73
    0x56550b40010701e0104080d801d0034a0114405008c0a404000ea0400c0c0240803400111041c0102d9225640000c82038820440c01e8a408075100f107412001540c81141c054455103000e40d040002c90f26030b45c0440100135016040e54501c0030fa9030042403808200c1044850740035a100c099000390f42d0948202400361411803500811989000001030740703c00b0180c400140c00d80c0d2003252111f00c41c0101d00c40300381c03103e02600c980c0e1241002018a03a0b4101e1846055613194241090180c840d8840c1c8101e2004e210103449000c0051285010480181c00c0200204d80610040150243d9680d41c001102c0c481c0216540740c1d03584885003a032102180c000038013507200c03811503000d030b072880b007540441078811200d421291007581c001941416204200204201c000f0341c0101a40320740c0040d480000c410b1242c403d280901951390340c81d4184140c07480700300c8002d10000c26000c010300000d0302011103a4480c0c10b40c450003044080041000403000e41c410390040b40560b40d15080c0c4821818102c180070000d150007805 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 949687787 1250 949686537 949686541
    0xe0708010e0f06010f0807091707090e011103270109060906180503220f06260405120d020714030a12140406090212070e10091506140d0f061706 63
    0x2034170141c608030310344081c0700900c1e00107080030f03100710b107180010224000340c0501440b040744c0b4540c6580460042e180d03074a05094104c1280c400c1401500c9001c44807600091942c0c0c0c3c0c00504001c80226807610400442029001800c2c44209004403c007940c0130303400024100341c5d28a890011600c000b082100792400e40c0300000c01103400030081c2c4440109000707038607442e8200c120326480c150206410185080014040100c2d0041e88129020024910390740141040c550f1810904a03000086900420b0303680112544089880400080c0603074680040700903041007050307680c0c19101d0240710301c0e0036515031000c9507400c4c61590101c0c80501c946510b1404019542e010000d0b05090b1800a0001c1c0c001612014208210f4403510390812907d05000250380d03039070b603c41c2134504603210305950314400104504008100b5000c01d10030900184006440d4182072450b02500f6512038840940d00320152006001e13621424600d030043d10741900c05000300107a0307075041001c00719040d20a40844079881c2d101e202 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 949689037 1250 949687787 949687789
    0x105160e090403080c0f04030b0405010b09010b0a1d040e280b0f06032a0910120311240105130b03030a120f0c030506030c04110f0f040e0708010e0f06 66
    0x16040c2c1c21582514140213150703070f000303502c42045c03103280c2d0082c41112002070000300307100301d00c4483e50086200760300a0080114010030051000c2007030051020142c8100100c0895034011605294041e08015814140010380c800041c102c4100d2007001809401c0b2f24007500706112014001000e8500e00e98014150450603140c0091904005125200c403075a10b0010500e0390b42c0c1040f0b0102c0001d03003444c1140c01e04c0040d0810101c00c0f00d5104440b070240c0309500118034484a108050700c1681c903054030319072015645460465003a50140348883c440c2c0a07103030f01c003804d168021020900b8104203010580483d4902414001c9280b1829200d016007883c0030001c042c180e0b008401c4030221521840c09042e07411a00c1c500307000034580c4c040a001c002c2d207030144411149030150441440703100304806866402e8041d605020589a004c107800105180400c4000c8039078070300e0000751042d42c0302d074003207a801c1c940c40b14510081c060041d10040b0119401100411010070310342c01d0903501c607500704501d40050070440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 949690287 1250 949689037 949689049
    0x9060219020402180316080607020a081206040e2410030c120303060f0914070f20030405060c160b1201050f04090f060b010210021306210203090105160e 67
    0x4400240b0a90b000541402d031600c04200c50700521800030240c40004c241107101c0201c1000d540f10381801802500300048402c0d002103118626240c1164034507161505648600e961181d0080042d03520650340d00a91060b60000c0125400243c080d10300c2e00710383c0f4040c5102c8209814000e044c01e4104520800a0000565600c00380d800c480c4c4110b00d01a20028510701500508400c2e00001501c10250100240c2d604c40c5421070441c0540c0340b9010310840c2c903028822214561503c02c04170101d00f040b0400e8542c600c1581d000700c0e01040440c292401c10b600c0d240040e80a9100c6244d0066903400000c8a046001c2230702e40d040010045600f1051401c0f407200d500039120401481041e2182050980c00442510b0300e0300081c0910b6849001da850304005850804001c0c2120101103005100f004405180e5100307a108940c0c1d421030740d01a860000d80380c1141150304080155501114888403125501c03412018000781d4003512907507001182915000407440c0020100301c243c1410004600b6201445860f55 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 949691537 1250 949690287 949690333
    0x30c0212211c060803121008160302040b010f08011503020c030f040e01060f081609080d02010507020c041a040f020c0a0b190203010b0d200705030d0608060f0a0b010e1203030601090602 81
    0x500000c107440e981f02142c9081c1400550300c14121030044642d0340e0041500d85090b00241d0744226000c000c1580c0b0940112915200340310010040749841d40103000003410301e00e03c100780800628004d0301d4260440519410360b0091401c03081201c001040622051070851038940c098011031801700364048540000030030092000c1c0218001140d16078030008003074414203141c0003420b003084c2101e92004120030002e00030301c801c0b21210014000e00311000301500e058004d10218039034800c2d0034404149a441000010503100401d000c1050f402c01041c4c00043c41488460390301c0303025407030004880c6841c0404070240806000540e030300910400041c41072190f44000e9038280702018a0008a460b50740300da540000301d01010f8480048000700c0c0c0c0008001000000b010580400d1005010540e44c42d800c20382d5451003511540c90841c2c40400140b11b255135030f48000141c0c00b051401e0608007104d140824400403500c0001d4a03580c00010801065580240381500213000d42c5c40217002c02051000101c8c1d1100403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 949692787 1250 949691537 949691557
    0xb070503180117160206060109120303020f120c040602010608060403052208011d01200406080c040e070e0906031c0509040f0c020106060f020a030c0212211c060803 72
    0x4003618440c664801d0440d84140700c0030f91003210003400c26003140b40c0c00440a004210040c880c51000030101e5214001c1101111a000c020304440c5c03055035000d8010350069000380340e2018041c80009004020070f0103450043c0d00604a6559842c03c0860003402d542030350b040040c0c194804814000041c1d400000c5880b0340100da00080b00035074107040d985240640c0c03a4001041982030100b840069020318182c4d4011001c428001c0092219940c417003255180e0840c21600c03001c00c140420001280030ba01740c039a10058800d5818034103502c451030403013490010f44003039000070444107001c1d00d07500382070503140d0300540120002c10300414064002a8000040070081e8104030b030101d80c110103910f540e0410321588020782c1d01440903154030100240208150f105410020b20505039013003403140049450003120342c15940b4008400d0390758090020042c1c0c401c00d0341101d803141c02648611000311010403c10206001d02596407403c000150301d40580c6107100020300305280104c100711450001040303403c0103074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 949694037 1250 949692787 949692817
    0x1b180403050c0a05010203070912020a060f1e020102031005040219031a09150a0b040f0b0717030703150b0f04030f081b1507050307020a0f0606080d180b070503 70
    0x258524085506025030075005a540c4240a809000c000e81900034600c503003580c0d91004102035a42003014415100c0e414040c0d0442c0403980309200b001e114032075040c2c0300e808600340850307450108140c806407003940301a0100140d60100610680b1244002d803c40104011241941040a5446440202103003003c8013001d159482a6228000c0c1c0d5403044180d00882c01846454249003804000d0b001100510f031403489034101c0900400c1440040381a901540c24038400740780300301d082c03002144071a031054006944041d0301d400e50055000d4400700444c851030003036030041400e004040c82451801c050380c0004514440c2030024420159281c010b580c01c898001d14a40700e03401c060308103000544620817018034180240f851604100740700103a081c03203400103602c06145035070f240300c411101804107a902c42c1c01a003120741c240c80850035045c1112405802800c001802c942d941d0281d92030680e0740703504c000101d0b05803090010304200011402c4002d04010a0b890729105407540c030262240301e030144110f6800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 949695287 1250 949694037 949694041
    0x6070605101421160f03050f061909170a050d05071b3005120906040b040803092b020f01061a18040c080402040b011107180b030a0f03021b18 62
    0x584100440c4004c1d034110b00039001010340703030101a0003129071808203841c0c41c4190011603018140c0065060310a50a1001200b8204070031400c06010b0000d4400541e451034030a0031480840b40c0b13400003480e000999440d125500e2045003410425038000400080c148070844250303101d28003044c40b400720031680c0164554443c00d442000041e5038032135610400e240c912002140302031a504200100b440c0c046040040e807550790764000c02540c03008104c0c0c00034000c0c502180441d0010300010003440e041100c0340306462140c0b50311600359190003c0b4500070040d142542d03210b40401074060144e1148150500001d06c52142850010104408070145e010b980d040c0016010241e403c040005041180006100348811002c5c144002c0c100c20703040c4e83c107910891408864100941c000d0706101c400c40380b10320260200521301010403203508582494110315540f5603107001e00c99641845804511071040c40000e5050301d003405e0082c60b0030f903848070000d0b45028484000d03500d0360b9000104405811142d05240a44d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 949696537 1250 949695287 949695349
    0x3140a0201021b060f0d05061c200402090910050f01090f0620010905011a0306070c170c0f07080f072412050709051f080406020d0902060706051014 65
    0x98400c5c11000c007440c1c10b0100c1c03c1032048007282c03c03c6005010860310032a41294450300c81020b0007003420000c0040b0700341d0b9210600d00c5a0080d00e507107590b50080005041c00603040200d07080c134204072050010000c0b81c810a01c05480c21100d244610380d000e1038078412850800440550750100c0303000b071000b48a50300e0800707000c881c0360b01ca1240700074560320004e001800507403806901801070090402c0d4081403109010f01d1034100011300038443d411580d5a82000341c403588070240c0e043c803a0a24240c00100820540c001c03000d040180807401d14007030300101540b518005d981c608021205080203140c3c0c1141104004044500303603401c044100d046d000701c9918949006c01c0d0390f00311800c44a0f8000b1804c1c5070400041c1034101e030803c000c442d816250100042c0040b042005010b40e42c500d0341000c1a507281c04140443c11950140c200702680035000101003c0030b40010b40b103a007107000101c9140792250b0800c000081444540700c020107605800c503400490311000505040d0b4060381030041803040207240d04403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 949697787 1250 949696537 949696549
    0x10f091e0f02030d121b0e0d020f0d0506011508060a17010207060e0a05010f020310031103011107150609090f06020a030b090c07020a050a0506031306020f0d0603140a0201021b 77
    0x71030b03402411607100545100001c3e1601c80c200714510040392409402058929200d032101c2c0036000c0a03903c1e030241d6000c0d84104070518000742010b0740c010b10040100c4006840f903078000c40e400c5000f04001c0141790714209054100a101a0140701042818000d0200e141c9841303030508140c40b8525032802421455445050090240f4080079050a042c8410701025610200700b00c10880c0c0503400034045c2c01c0311036000c40203074481542e64400c03100080204001043c00000c210045040040000c40d00b50030380d42100450b40c10080c401d4a0480f1641641007a40707a030f910619005000d000c206001c4440c9589902c0c4c40b0720501c1402400b59500000c12500c0c42c0d2103548103003607407003008043c03500320b003010010401c0ea50494030080f0300986da003403000700b080e140c403c08500464100a014a15655840b49000f20301043c00c80110741c881d400b8048841c00074110000341c0205070070a00005040382c6141061003a40d054560611000d03002107184c840981d0340803401c1c4242181600c10001030030408004559 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 949699037 1250 949697787 949697813
    0x20f09091c030c12060303080a1e051f0f051806060c0a0b09240105040c051306030f0606170619050303070506162a1703040b010503010f091e 62
    0x10003588500400501580c0680c000e0b406840f199444802c40100c500303201088808a00001d80401d5043c800a11000b080d40c2101c80700c0b5068005002d130342048031a5510a5841c142d40d00a25442c2280e40988815600107801d80200000d841e41c4105900d0100410340700e080c10300030407483d40e003a80000350b0152680c2045440041c0000c048810303c0700d40341041288a04166041008ea000e43e01003036030361030258413410002e1241807030158901d0b440d040400005080b8500c01e5010300c0784c14440400d01c00700700a00c442c014005910007040c801e0703144104804640c140c0d0405010b0201280350001650390415250f41d020700196040e203024968a8952806c48200380d03c11581484006503100402c4404210180514503488483e800155044001c0e990790062088103e20f4020083e80000d42e11008002d50003002e00a24803e000020035181c0508140e104031800c0d22007144100041005003001d00c662408050910020010407149030b1b1000451036201c8268050f820398449048180000b01e00406 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 949700287 1250 949699037 949699063
    0xc0305090a0b0a020a050f21090307031a090c10051803010e01020d02071a130b04030314130515070e0904021507030f030c080f0711070314070302040b0607020f0909 72
    0x190b1200e1000100030340e1220301722011913240c01100701c0d01305c82c2e80300018000013420700c82041c00c1d8081c1d00c0d1402c3d01003e0b088401c0d001d626218500c00000401c04950044551200060900704186450840c151501c0403c003240381c05a40030440e400300791907204080c0c2c0e0340d03447c02a103403241005503500002e000d02104401d02a55500c001154403480d0141c0c2d000f000c00a216001300c280801f001c3c00841b5032920126185148011003240290000d4800a001c680c054401c2c2400075211902e440c2c040d115001c11240000716001d000e000c0360a01504005504202154032070f42c12491800071001400441d011400303e01801a19000c2811545c0704020050120b04130341c00036480300d045003002080c881800d1360781c4010030303e0207101090051040c09040c1c40303040c490101052584034410210707405107107000004070b28022007401000142c4015041e0000c003840d40014464203046004100850303461010301072045000700850b4005031a072900500e82c0803800c4916291650301c1110b91824071140000030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 949701537 1250 949700287 949700309
    0x6131e02120106060c020a0e0402011b050a1e0317010b09010e120303150a0b03070e271f0501050306130b0315090a030e0f0d021c0606150e030d0c0305090a 68
    0x301300f95501c4222000b220303008480c0600215600da020452405056070041c0c0040c0b41400e8001580e0007482030341c450076200d0000c0350014842911100402c4031f8004080d00003550002c01c5206140d80006c1245410f801d0511075010740d407502e401c100c2c051040c452400e050100307404c2c4815031555101070035004012894140e982d039203800d4003516050706564084c3ca21030922800b02050000703060080d24854401c40d214041c40344800410080c841c410510906a002110703403400526481880381140990129016420622503640504585881d0780c0c01403410410140100301c49966045580316030b05404002c001880c11815000ca81010b04409004800c20121418095204000524158000d02982d100010329811201b00688000301c480c4059101c400b4601d0700c0f01601d422840100211401c1554250307410050b51207500f560ba01c1d9000213442e494200c4103803c0b694014074122182e203c1140503000c006000c0030b000e8000c5107118000b900708580802c0e400c800f5114202460094500c117805 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 949702787 1250 949701537 949701539
    0x5150909070e162a03031a0607050a05010e0d020a061113031109070e010e0906010e1003050103021c0f0303050705040f1503151a07020f0d0b070206131e02120106 71
    0x1100002103080346070300000c0c0b646134030107101c129141800c5203140f00703104045a0040c3c0c0d40c5045003d03042000024221001c4000801c5060340c9204c0104141846000503049110079410100d08441c1c8042005031103401034181c0102c11760340481c1030030100b5406480041d0040c01e602d190109801140001c18107001102e01c0030062125803904588449022a6245550740c1c494104070b07864000d003c01e050200d1480319000c171462070001212680580b044c90b104442c203c1d0352000500c1c02c0724480168007c04e07911801807040d0b0400050707400c031041100e6041d6203071000c15542c0091324045070303001500300341c2d4a00c04201805c0c1314804483c003d00142042c1d40c2c00b50b480715424907105001c800000003282c94001c10003800340b001442c030b20840d0001650001019011100520701d0340c4960401c030b90200d0010810030070740d92094000240b450041c2102205440c0044002e0720300350f0003619809086030700380c401100065800d0701c11002501010064200e00031a4030100c0d8210070200100c9141d5400c2c200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 949704037 1250 949702787 949702801
    0x62203061d0f070b0f0901020f030307120501080c011709011e05011707051507051906090c060e0306130f0c0621060f050913080c06011805150909070e 66
    0x30182401c0c0200300507103040c20001c2081640d03843d40b51244c81801581030103620074040d580300c041c2c0038041040c0142c90144800762030050075a8012a403080104128030b5404940c00b0070307440f4907405800004010a03c10001c03400103071003884c0e0a014de408034003140c070004106690a40101c0d9207410b2848506d5101c400410101c030262900f40591180300c0000c0040b032080c0500029550300700c0381e01070a0207107185a4140303040065800b0b40d005031414416842c40301e0031188410401c0c04030034050380001400000070701d0060101e00455000b5410440443d4034855250360104060780c10542c02941c28002046034a408201c0c460303001c1014000944410300015010380000340c00c990598200c1125403c02868040c8804031034003801402e9050711020b00c107100744d047c0384002a0304080c025000148110342c550310f03140144c0c050191120140c000100402084c0c0c2505103c1581014040050003030740340040c16564201d0860026a1084800a0200f19401402e00c80b560190a00000343c10702031038210303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 949705287 1250 949704037 949704071
    0xc07030f1a0609060d15020f0c0102070210093f050c150715020901090b1303020a0e06060304060f020d06062601080706080406060b0a020604061a06220306 68
    0x8810301075440104002403880d18181c4510380c81020b00a0010499051584a906c4410b20342224041d415900b044a07102c05007500c0702900e1005c01400002d43d44250710310500a0301442d011000301070110b072400a00510f01c0d00c410b0160f0b0b501103a0320380c200c050840300d140704840070b0003030f55580c20031003680000003807010102d4802205030040d103188264860111207816207100755000030700483e4170000c40380c0380c50f21581c0080c0098201494140d5406448181c41841980216102e244103001c0c002d007001141040301405008081d005642d161924000c008210786120042c002054165640006000b07115070303a05541141411040401c00b6903281c0c0c101900c0c041449001c080d02004400c40800441c0e461701e150fa0603101c0c044090111545864400e84494001900880b04141c035008080340d00b0000c1c00c0a04004c1006a00034079060070b0500380f14080711101d00881c689544801940000c41d100c002c11105218004101c0c018454681d06503200080d99076000200030500344100e05441c1035540d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 949706537 1250 949705287 949705313
    0xa270b040b1021020f090708191122090509030903101b2111090112060503120f04050306091c03050f040305070302100c05041802031b0c07030f 63
    0x51000c42490b07480310740741c03200038520900c42c60841400030296003811803e8481d1080c0d0032440503000040d042e5181e40050454101100c0f0ba40005844008015619030801d0a040310a81524000c00602510121111492081001e507040341031780d00400c150404c8411031701c1c0c40100820041085541032688495490382d2101c2c0780140300c0d100341001c802e0404410701c02e034181107050f4801c4500e04170842106443e0301c2c0c004126400120031000e00c0002c140300500866154043c0803400c1da40c0d80402c00009400120300d5041200d55515200c02071010ba100003d556041041c400d1445031904202d8007668410711442d0007592705030203404144080721000041d82d0704504020300070141d1040034030401714200c41301121071041390b514002c04034001c207004100030720046009106a03040011140c094a080c3c03020405c215002460010302080702c4000a80703515880440a0429451400e110b0075031600c2d90361607040584010000035007010140810001d03079004643c04584083c03916486d05007085030001c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 949707787 1250 949706537 949706543
    0x20a020c060906070b0606070807080a0f0e1e0f190f06050f07150e03070f1203090812091e060105040b0f18060103182402030606030a270b04 62
    0x61040c03010301a182400540b20458070240507241480304030340703c4640340c09018020740d41018040000101049040000b800b007a4000c08a46903280446407000b0641e60071410320000704a05043c010361180d50b001c010302400741c4c0e021001110041510300103018241107508040d40f001101d40b402c031660703201000c0c4404480341034803030303600580d80c400301551940b194039010700280c0c00c204040302c0024820000c0c62803001910100003009032112088a1856011490076102034404600e0300e410402c0104605000d14014501401480740650f28030f601800b806025980c10320844002980030401048051958030300301600318003845002c000c040d1135030028003541d409141043d21860550401141011900354042c04110f01c904001c9420210360a000d8075090405840e00c1310f10928210999103000701030b0040d010100403134071803451441038140700010380c4841c0d0700600421003641c0c0c4010a40368002d501d0703880490f000350309000c2298104410076003169403030481200300b41400324241313a961080d44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 949709037 1250 949707787 949707793
    0x31104030515011e150e120f060903130e1e0f090f010603110415090203010b0d0506030105161101060905240a14040e010f02310f0302012a0303020a02 66
    0x40c8602c115410f400b1a89403100004d54540750402451000200380201d4a04920f00507815a0208000480c001f00002401d1910b034416000091018002e101c4950448a04401503227030a030001c1c3d400800030710500c90400382c44980e030b00064840b9070301d580d03120101300540310340051885c014001c252003070310586020010b80b0070f5420b4408030b400d05102c2c06080da81c00c1607a00d1810100c9108000140c100c0140c01034594045100c0002c1c00c00321030016501a2011294480e11058080101d408503280100f200780b2a078103140a01058828811481c0700720000d41c5011158240e00d803e0450141590707078012440e062515040042d2020441043e01ca0382c0c4008500c420b191590720100038460500340a40354035001036040b808070300d280640c13190064126070000440d01109e0300c1900d004a0700a408201c00f608400f00c0403a5012180040b442c500e5004100703440c8006051260900c1881d505000c001e0500c28081100031481c00d010407441c01e210080c512040c0600c0d041e1500030301035008812101d0140c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 949710287 1250 949709037 949709039
    0x216050a051b0a092a030c02190f0f020607050604050c0906060a1218060e0604020a15122a5009060a0e100504080c1003110403051501 59
    0xb01480451844580201810341540c01d2541400042c102c802c1040c404601e0402c00c0c403010508210075110302c2030140c80014040c0140355002e81401c0b0001d441c1042040c0c00c9114500042c14064114880750300044140e80c440110302c003181c2c0c54851440060250f00c602d908001c1040000100805480c1040d135001e59a5107603841840064001e0300810400301d58150b0f81d03003604181a038444561441441c80000d8000d0058a0b104211200c5210910442d000305041000391b04201007072000400c40c081d007400b030380360328424003c100b044001d5041c00309075185d4011144c9800002084442000e054044400c004891407000e843c2d9541a03c8040031400240d007400d415840d0300c0c02c1c010082c506002000c410041b00c40900170030f0206061000e43e008404d02c481e040303507100d403c00f8244031021901d40300d10282a050801c8101901c034001803040080800040c0300c44000032070f000e0401001a260358080b50b0f010001500a41034950a0240f000000300f000403d20000007070358408400e03907c611103020303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 949711537 1250 949710287 949710313
    0xd050405070933090e010219050c060112081308030d0c0306120b0621100f0b0f0405060a03120c0204050901090302070e072d020c09060109090b040216050a05 69
    0xf41d030a80208802c0e03407a001c1c0081c07a44485601002903000031086000c050251510004000c460000780c5a00050794080f0305003e000030007410604988810b810300d00d06180d110360041381d0380c10781406080f500a10300e140304010445410141d800003500b51160452280d1903450f56940c2c0d811040c5111030081c10a00826441e43c0240716038800e6540c404040c41e500c450700c5d15040e0310401c1c042c00c00c64100c06e0017443d14229a1000b80c0d10a10388103034001500700c0c62901d21442041e40d0680140c054494038180007401640c3e03401c105100c1c445000d443c08101c541c1c801c400103031001c840e54000380c00401c4500380121507590042012030034602c200e40c2008603484217101582201c1c1c28001c01030147c0e1191909000c800031805840303610025900d01205951807100440d1040644140014000c7d02e41012a204464042c04004007851060b03603503e106140c2180000c114035040d11500344030369500d260f02d0041da00d450f01260501c1c5a03455600f40010503a05c1d0045e0781d023140e9502600d090285c0f0b078100c101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 949712787 1250 949711537 949711541
    0x15020c19050d0c0320070f0906080613030318050d0909090b010308160f0c05040f0510051201020c031209160b0702010302211f05010504030201020a080c01110d0504050709 75
    0x8940d04400140b5076000301580642d01811091000e0307040c8443e265010f661402c2c0c50111000511642014042c400d2510001c010401c616400805510303041010501692000140499200c4241d900021041c1d4642c20140e005002601900305001051410b070300c240600010400b0511800b81e03145044103a940c203c500c102c0f001014018484010700d401000400c0115001e404084c20000e11005400c0655030b44848121014000300e86071420b2081c10071061170306100e00d554118170309800344200d242c401403038144e0300194080c8910852246120700744242d404d5060341d203540c9003c412241d45003000400024451030440301c8881d24072a41520703030784540070300000d40100c405c07004159081644070760042d4003075084034039402c0c0500c0d08042e04a081e581c220580c1802907542510844000c211225176904032102a008141840001c110800050340e002400e400300a80003042c441c2ca0f0a0015141d0f8050314a03220081041d41010032070707144041d143d900450046100b42c0407504c90701d84e02ca6500341 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 949714037 1250 949712787 949712833
    0x60708130c0b031f140102060c07031b050f07170d02030703050703030b0d0209010306020318061005120102120c18030a030c020f04110309010c080906090a140a15020c 73
    0x403400304059402c0040e450140043c58100410104119580742540100002003d855203e00b400b905c1041000e00d0a503014460039400255504280745049641e0b14040c0040c034000c49040400303107000700440d060280a200c011100da138618181c4118980e03c0f64042a640410305000c9114000d007901556118000011a0030b01c6a05840d13042c1429010b807400c0e4002c0081c046a00e4001810141801c01071381e0b0203000501a500c1b0f1800142c0b6400e21b1080c200f0007500c14032074003600f58800c1e030501140c43c0c03c0c0024442110300440d14000c401105450311806401591408103080b00c0c89014481000802d4026086080e078524120f4200c017200010107070340b045404000b8021803244240b440150800c0c048103251b0070800b40c0041554800300e0960f50a039070040b50351004907503440c5140092554010020358000002a0080041d0f081c40340b02d550315002d42d000014031902119502d50307000c180911044001581082c0042005000302a11a0103540180c280c90140c0c0105a9200c1d48a409000c89507 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 949715287 1250 949714037 949714043
    0x726030a1401122a030b01180506040c050d33060f03050f0c162f0103060503030f030402012d0305130c060e06090d060603020f0d120e06040902070506070813 69
    0x501101c0c2000c00400c041d04140c0c120180b0404c202c20301101080800200381d0080c6207030a51300200b003012044510403180050300140c81103040124104031a54403405444601440c0da40008501124407604240b86010080301d083c02c00000d0750785044100500d111504640181c0c4844011114510342241258400c40b131001d201c980f500c020a80c812443e1015007000e00c042981d0a00d10481500e0741c18007201d205078060070f0003640b01c040201181d550b1420302d503000c4007824180304050402e03000a80b00e000702e44c0e04c50b1a110001c000101960320441e540c0c01c030101e0700301c1c1d4250019590310030415003030084800c2c0f00101e82801d01141c2e0044403a024241d44907040700c0c00a120604000707048480001c18140b55500010038054180342d0b40e80e40304141001440342d0350001d90307249548144120b42809803c80d07881800c030840c4500116180401c080c685c04180d24085401a800d1000900d65000d2500900020343c8045020810404001013050064103151034050300e55a03035a08e2281e6400b0440d03001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 949716537 1250 949715287 949715303
    0x403080f070212090a1d0a0b040603030e09040503130603051608010b0a20100902120303040804030611040909140c0901061205090a05031303031706060726030a140112 73
    0x144403c0c0300d038801508034104004c3c6011500c130f0341d400003a200044903800300039450400805000000075548244801031009803828005207155403030203402707030219901e6603001701201c4000804000c2e050044504454180c4a84d04109884030001801400d0442d803803c01080c400750500d4030107004101c0315048805c0701090ba40f81c00070001040b100184110ba000000c50501d40072102200f20904c0219540e21a01070001001c1046004005d805000d200515015420400c10701001c668804112400e407038004c070b40421805030468141c2441e10403503210311040c6203424030b60400c010311052160020301c8107000300c401c06202041000351400c400e10546010481c811210b000c403151a8014a500003440025510b4015254840909660100c0005145861a03440900405400502049020143c2d28051651307140a0b4041402d500c150130000c0c040f000082c0c80100c030250301030b04150f101c3c0745da42d074511380300d080148074400640000211415a0300000d000864541c440380440100503400001c0d07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 949717787 1250 949716537 949716553
    0x6070501060f0f091b0f171603150f21060501031410110a0c0c031e03020609010606090303210e06070f020f0309012a08030f060d02030c060d09060e060403080f0702 72
    0x4240c13140240301c07000c6d105012080e0703500241c0b000a0740425115941a55007902c0030b407040c000080c00c40d0886e05018035001140c203000e0001c0b0048035046c2c02580c203801074004606242c8198200a84050b100040c20181404004000c10005a40052241240204641080d00716001d88030940b02c0ba481036001c40c1c00c050211105c0702d4803418803c8250340c052b1881e610f64a4070b90311211202949094800038000c03580456101700b548c108403103548040080001c0007524207105008101c2160b03481302408214980400041c050079101031403c60060701c41c803c11841e0f01480300c4585a2000300e40550208100e410f00452442c00401c0030001241c000d000f551a10406500644040001c580902d02c201d000641308049a59181100d40c400d074080d072040340d200c0c07601c0c10f030f0000c44210040040f401898101354010040e140040c03003600c400d500715100b40e10740d82d500440704010080c8600140120b42810400b69108038041030b80c81c00307070780256101d03204d650318607410000300281901e0202c01648060a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 949719037 1250 949717787 949717841
    0x71b060203091002030306300106150f0c0521041e0303120c090905040c0e090105040b1e190f020f0405030721030806010c12030c09090c050405040b06070501060f0f09 73
    0x1408c1d12500b090a600700303c0344e0140f02c0d5807908481c0d50303070000910541e0102e414546e00e07420006000c0c01c520540341c00c5054003400e5888a4590415501c8052841c5404041543c0c1d080c952058038042d0000031020301d60010a0f4100100c168810704c81500800c030ad11840031800561405505041c24054031521042c030302d000400801480c0083c03041e1140c400344600420713011030980140c1e020715800400400c04d414035042c000c1e910807015000d120803003021038405905102d40030310680e008020304460712458250781c8480018050282c145195a840002d0b08442100e00300b0240c401d0324425000c8a0200ea107c03003c020f00425403075400388c4001c403115482c0c40080d12900126901c02c2040c941100500a9551019510794002c002000400e07103480340c00d8400c42c1d102e0f50f40340007029440c400303026001d81804e002d40369118901403540602d4580c0c00f1009241c0790213040b6410a84c2c020000c10030140e03100b940110611440c000c0c42c2070400c02c0c3e80005800c982c11b00420000d00c60819045550b003001d61 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 949720287 1250 949719037 949719079
    0x60e0705031603111b16030804080709091a09161d060d0804030b1009021c0e060609061e090703291f0e030d020f15011505071b060203091002030306 65
    0x80e18551051401031986e0038601c940280046101b2035540b41c440d4100a401d03402e15096402c0300420303d03e00b10481c404544590149683d02400154921440c0c44048000342044040c80e400f410450a5030000330700e040c460071403103d4402c0c411095121030b0702c41004201e0f0303000d8083d00240c0b240f14180000e001041c0810240b40e0072140c00040d24418543d104094400d0780c00c5080205c4255440e04a007840800310b50041c1c01d010044034026100510300326001501c4680b0180460340214840d07002419860160104940782440040071380401c2e1404000040161558200c0d107201403210161041203642101030480c81003c00601341c1d03110807410302001c7c0700d84107540889020071505841990154406001c4403800340741c0f5601400e4030080c1c48002e42d1400002c000c03011400390703080004000118034002080081091403a02c60b59031a4142000c42c1d0b645600b68040071800c0b200c40001035881d800000402e4400010f540e4210300031340900301030762a400126442070b04282c042c421030005003c80303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 949721537 1250 949720287 949720327
    0x6040e0a0213020c1c18080109021e03010204120c0f0506030f04030e060f0d270222091506030203240a0504080c1f0f0c0c15060e070503160311 63
    0x3000845140013861030404850b225070003528801704d1040c6c1028020006c54103003060150a09034001d021079072035507001c01d4181c0e0140745c240b4503007900c0d44d04c120869035003034040f900104001c00c8005022405030a041010080511440300700c85052040000c0300d0521909030382c4180c80188130345105a4442d10b007940c0300c90481084070b41c00442000001501c0d40444040c00d40680703072041c001250302d00d0044428002454215071058100141c00100040e40c40d180ea9130544900000c021100c440d00381012406011030500042180203800f109111071060b50f405001140c0c004c03070131900110305603030781304040040c1000e5800d03612482e400040d564045603004a90424450003402d464880d0841700341d41084c0d401000c0c3c004200e03c4055681c000c180300e0003800b2844489420800c80011a8170015142008840e80242081d240940d2424292036a902502c020040999034100d1482e01d504001d00c00d90044920010703d103800c440d51809544a8803480c00354820308290700e4900605c0040003441f001030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 949722787 1250 949721537 949721557
    0x10081609240201060b031f0b1905070206040906290304020609010e010e0303030117010f110703080c04180906050709150e030a150e0d17010b0c0307021806040e0a021302 74
    0x1c0b1a00003943d030030817500540c072942c617000d000c02c440c807000c4810158500700b0b0744c0f1038002a0b5052040114068036400d001c410005907041c09542da100c94408030300103002c0d83d0b00528a84e803800b03000040ca90300c0095a50404612448000c4001803041807072006c40c0000d480103500900305104080302075000321540c19804005041404200403a40002403465000360000c0c231214101000101c4800030902a621018201c40404e00c04640001c60180c0c030b500641c80044c0402030304102080403100c0c004101c4007d041b9503481140e140804141c5c8401800c0764134030854600e403800300018051882085484150707112011800d00d000d440340b0040304c00d90800b0103000c0e4980184d05808000900c2d180c4000a00c0d44080008100c404d8140c82d49170904003511018400d0140001080d8050464110b0840c155001d800d070843d11206010f00c11491401481c8000f900301d8a900001c2880c019426051841480201c074240300341100812035944400800c04000d4100d0180e2550090b81955900038100c01c0311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 949724037 1250 949722787 949722791
    0x1f270905010b03151330030b040b031203151f0c0c210b1503010203040501050103120f12020a11150a1107020306010308031e0408091801080a021e10081609240201 71
    0x2150311001d50320601c0300d20031b000443c1c0d440700880214249401410391069084001d0041038003213424040452000074a1919131500e154075684540c2c0d06c083c00d204801040300c41880554214a1018125003030101042d181900107020004043c0303107406c104500b101c006c10020382c0c21051a9200409204064540c180444841501c0b4451b91424030140d440740b4042c0e4000714a0707504d182007001c403011514003d50100070000c944000d04a80000c894403a00f0116600103a0b2404040800c4400c00b4010303440850304d018811103400d055180c0100280107252803641080220700c0b07584094428032a245000750960840c80040004c0b440e0600a182d00c00f81c0301c884003138882121101e45a210f60201d0b4101e41c1c101e804130380b2030a00d00b0700c003044003803000340d6501e43c001950400500c50380d640034000000703106000490b1280c80051148420b081000750140c03201491010416000c4c0100d0003c03142c80043c21200301d01c0c294518400c4914504648101c0b05000c124070595010021110b440c003c00f40c01e41d9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 949725287 1250 949724037 949724093
    0x80f0618030d11270901060c0b01030b04110d110f01090807050d08090a060203030108160e0606030a0905010c0207030317010b0f07110d12081f270905010b031513 71
    0xc921110401e00300c07907180a00c504800204007001170044041c0c000340100f004041c1ca160000d02e0005074141541c1d00705034800d4444d0740300c2ca440002810b0010300680c200c1c107108821000c00c80500d07000512030030115480b000d000119401101c50445600c40d080c103580c0144e02c10456400c1034002d862505c0e0060718403600d051f004101041c441030703c9607c003100580c00000104402441030080340f40101d403a400c04281d86103002c40c3c404881030b01809061158400001080a0313095035440010f55581c018020300040d240400301a444551505c02540410592110700c460103404151a5040e6551000360a080159a01c00d0700305903000700c0021548a08402e424200b1956602807100c4054418501902600a8920700600c00d10001d00740da0084a0040588022072502e00c40b0001600d02c0c5480403100030b40c2885424544920918140390040d10f0080c2c0b81040c001e043d0850325500c0001d501304c40f24200044040701d10200304547c29200c0074001030f28500000c10550004680a000c004031000d0f40d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 949726537 1250 949725287 949725307
    0x15060906070c030c23150918160507050607030c110106030506042109030809010509150714160504091a07031406010e06120703110301080f0618030d11 66
    0x341d8055981500c86442e44242001008101610540a0441510564000100901112401d51446281c240f041026405d07031704500340881c080d90b021103002840f070f0340e1440c00c01c049900700010940e11280740e0354509210f03844e0703280aa03085030700d90741c5c0c4030340189400d580307041c411030041203069103a00810541503160381000c0401d006603005035010701d0103841c081c20140741440110302e030300c500c840a01d00f03014442c920864012086108817a041180d80ea540d550700801200c10b445009040c5e6401034209601e1203560318542d026017601c0d031084841000e111140c03000c02e603031110b5031740410004041440060000d41410b400031000a4458900c007161960403040013001d4120031240c1d540000c2c0e841c4109528031603200300c0f143d0807603002e092049051051201180c010310a084a1507140c202e81404106054403d6104100104080288903104d5840e0f207100c03615490080c64608540c0704a4000c1041010041e440d4110b0702c242c0070042d450040712401c10703401340002c040705000c003200a1054500b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 949727787 1250 949726537 949726549
    0x4020c03120402012601140d02030d230d020903010b0307080d050c0a12020a050d0908070e18150906150105030a1a03030408010c12200313201c0b150609 67
    0x400201250825099811f1044011843d190b25050500c6803480660120240c1c80106e02080e134000c061601c0a104e00d424440c104803588100c1c2c85034001c110000324030300d450300c0c9680602200b1000324000d100e408139041c1019a0fa480502030080d0b00c0c1c003d0a25031052078024002401c004068500b031354a90011504c5419249001642100158016250080c204801400706a1280c105030500b118520b00f8401b08540d5003c03240078422a283c0d0900101d03402d40c3c0b84007907001d44803010300100c0c2c0c0081c509100410181e01c0680300300803584182c9000c54080742d1b900c0055074a41d141a5182401d65896a440740c01902000ca01510040b03548140c111050f00d0900040024104040c0089190601c007400142200c1e1b0b41611102803510301208803074104c0d200c50b0a0500c20300000140b90322919111050a08c544d500343e0010305c46260220000f04403160086080c00300307d400ca0f0001d14400d2003038809144150844e40007080b03518184000703405490740729482050190098025130514a0b05d1000c508 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 949729037 1250 949727787 949727837
    0xc04150c031107120320071a0c0f0114010806060f01051b06010b0a02150c0717040e0112060b01020d0c3201060e0c070c050103051b1602010e04020c0312040201 70
    0x10b206880d02d5800e8181358000c0720301020f0660306040d1040d80010030000c10345414060248c4402c0700745031801914030014400503150070340c81c49025103042030708800050f402800e0882d402101c100c81d110000a81c031401140c481d00c9880d01602c2c0303e01e1070310140300454440e40301c041d0320098078410460901c2006d000f0840c00d4060b14105c00850385c1c9141c4002c0103854a1404006140c03000c9181c01007042c1e0f000c001d010390714a40c2d170002501e945800158001c840c0c2d0301981e080f9003071003207102c000000e0b503010f82d00300308030b000d4000c1c40b08100310303144603004984900300c0b03080708008103a14208480021705505184c0003ea1001c03241c0101803452500503918400184254002d982c2d11107209024104645011b50780000d0000703684d40c6040d075650784100c01201c880c4695030526a4550020300741d42c640136078059400c454020302540c4c5003003001c082c643c0c0c0c0101690581c006011042103e03e02d041910884240e218000c00460400015404c00006000001c00403810006001c07040c09903d100000090 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 949730287 1250 949729037 949729049
    0x81e06010506130b0a080a0f09050a12050403051902010306150e090405010f0608100c0c0203061902040e25030c0507150204082b05040f17010b03190b0c04150c031107 73
    0x104103047c075403150410b4401c00011110407038980750002e0f002403400a0205a07907540040c10392103080c0f81c80d2080d21a4003482e40080d046000f80c0c55440c011704c00e0611074010701c6100743c804000306922003410468400100c400380b801300703505400480360761400a412036441885800040790760324420314103205440d5580e00001d0740d90301c11061208211020b005080e581d005924000503840d01035000240d41e450080c00c40c2550301c1b014410600710010a404680184c02800d00c1c00040c1c1c100780340d500b0828240341e107030312603141c800d5403030281c20030700c41e0007107180e0703032410365140c2d03042c5031254803203215118880c0c07110445503500700700004044000f48000c46504249009001d20450700700780103002c103048400c1860800104210a0000b41c0103a000481a2610000c0115070450119180b500421485891507071510907441c0c400f040300800030480c0001c51240c01c1004140d1142c0c0c900b460300e40a28058212100d00500001845034801c3e00741d40d12150107440e200c200101c4540314141441c620360040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 949731537 1250 949730287 949730297
    0x201020d0e030c070b07050a0506181515010509060d1d070603140c2209152414040306050c04090614010c03030b0102030409020f0301081e06010506130b0a 68
    0xc450656140300e104848404000554a094000384a0b5515102c89014007030800b5000b10f42035080c84400c00c0724003001e9a006003220901c0c00c1c4080302c0503503041c028003130035038501c2050070742c00c0d0030840c2c0c00f1001d00583c1c48100c081c00c0d06032200015151600850319013070300240709000b00300083d41a401100e036034103a01003e20701c013012050509800c20500d5000201410b0900900e01c59071500d21103850f07400701c060002c4035140d142140c034031643c3ca031400702a600600302003500420300342242c0e440b288190368031a582c074410a0340e030f030084102c02109140ca1000640e030032038440c880d203018030700c10500e02200070100c1d13180ca40c0300d640f00401c0f11030a031200000e0981c0450140100145803003160080c002600d039a00e107002100c00000c2c10b4080383c241c0242090b85840c0c0b821107d9000f0030588002c0c0c43c1100d002c0d5100c0202104890701600244149003e80c4541c900345032044802d180c0030003030425902c0241456070b082c8000d2106e558005c0d00e1032013210783c0c403c0340003c04400c000064944030303210343d8031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 949732787 1250 949731537 949731547
    0x3022101090c0212031504020403020306092a13020c0111131a0708070f022202250c0303050a0219050a060b120a020d0f0519030908030a0e04020702030c040606020102 73
    0x1400301260041040041554080441c041184c5490025039034080e4240ca80080c2c4400d5540c0420064007880d070000b50103100382e4051108000000c01c007020401c02020b60080b1440324140145540008503c049811008040c03600074002e503541c00624048038031600115071458001c1500e03403241d220322803001214245078024488041d88a40044042100d29103841c01c01013a0344510146220b455001800c810810343c2540454542d4051240d040000310003200b00002804910f05c060341c80109188054540001001610300f0308011804d00740340c02400400d003d0341550744c15549a8041c80d01c3c101036124015010300b100121100c500001071040d405400c07048618541001500c10312a01c0c1e40c880d0482d44448040b20b4000214010030640465001c2d4a000c46420f140081e8265080701a000b4000c250020f20f22804448130200f00c0b6209680701200070b40d1300d4402e151a030040445180006919207041c1b0f045103060380151102500090a541d040b120741400503080b5413203030b44030340003607500424 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 949734037 1250 949732787 949732799
    0x2d0937080d08070e0607050c13020c010e011a130b030d0c1a0103110105132310030b0105070b1905010906170a020607030f050c12030f130b1603022101 66
    0x2240d03640764606030900c49420304000b40080e00e020440d41303819003c0c0d100410b0700414000100148000008080d041c2c00c00d00d0641c46944000c1e51007406a640250b00b003813100b03190f0b00014030900000e01151080c503801d0071007030420000d07010721420340951a59110b445c0303282c141c1c3d4144000c074000f40007500e810801700503c0c501901074407288030700c3c0c1c076040c1c81c40c40040010030310400c02c0134000b4209282041e039403810300540400d14040c60b040403846e00018030705200011400c6140c43c1c110041100e420b80c07a90204c0e5012401e5840e4400d6542c000340d4180031020004402d403a20641001e40b0354580882c101d0030b03580700c00840304240c0c400041e164881c00b04019001c0d20703061380c9286002c00000340105156540106895119001004007041142c107401e06d04188104240c402c0340283e8801e44c0d41ea15416120b0012030741040c0c0d00040d08544600108083e240c0f18440c42d0000d40e44010708815aa44948200c4484600308012005041e020402126056540920402e05802e240c0c5240c08550400c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 949735287 1250 949734037 949734043
    0x50111090406090c08010b1e220b04031703100305161a0c060c16120c0b060a15080711150f1612090302160305032d093708 54
    0x5480401e01d03031300d48210000c1203540049002d054519079020707140e1314008000403182000c2500c1c40088080b20208201d514002d200b8124030300e071043e20b0343c6c0001c640e44030420003d0354420341c84000c12902001d10f6034034a16440c10003960f880003445615a901d15542c2d00d81c503061174220308560740700c0068024240100381444050138079000d058003205007084c0341c3c4401103640f880043c041d81942d440102300c244d81ea4181c100f42030081039200300c00201182c1412170203022101443d9080f1082c458030000100395007040c0e0b2606086032a0604c690700001459074007a02c8510006d0202d10811100780e11f0100c0d003410402400040c00c002c0d6003001c030b25150140c541008000058801a8018003030750500030340030f52286c141c0c40f42e0003110743c0c0001c0e40081031400764504000c41170b1081b400749018000005000010015104095805051413035144d89007040d140c08400700c20f110074158030705026482d00c50404d5042e00b0714208403a0715041e40904240403500003407942514400c4140c4110205001d019018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 949736537 1250 949735287 949735289
    0x6180b0a0840061d07030309090203040c150909180b010e07350109050105010f1809020d020403050312090d0206091902041e24120b13050111090406 65
    0x280d240c01c4200c0d1204040000418260300e148454070300c0c45030158003030001590080ca0103204c80c9880021410b49408030a4031404c01e88000d4000c070b000c01e00c001a00303142a000b1644103950141c421000c80381441b075004101012020700c0801c00c1010580410296483d202e00d040c8a01d202d5080c44004d410740c603010044100507003100c441c0c17403c01414880310a402805002c0d0301c001401c1c000800440d1a060725038000404071110f0320302d40009000150701d400c03550000f41a00c0342a40c442c131002d0014501500e105022030502d101440000710100705010040c3d0181c8048100d0240c0035142641d0303900c800e03145802000e508107903d800b100612034219810002000c41030341c98000381c0458a801c0c9402621001a034503040e4200d42ca4801d04021580d541e0302c0320400841da00f20550b01a10303040c1c0030900400280091034502d41041a440000381c0228410404480040b044c02e80d5030312080e9904481c0b29400b504451000c08046901d40c0011390038004e4100c40d40d01050030399100d00c81c41c02041300752505 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 949737787 1250 949736537 949736581
    0xc19080c0607020a0b030403020a150518030724060503011a03150f04060f0e06040501060302030705010207080715020f0d170a0b0603060409030513030f1502030f0106180b0a08 77
    0x20001d840040e01c90900b404c007291103e0078030903145e03031b503e04090b800c12904003801418401c07a010713030004c21803090340060700901c450320500c0c2415161360996030344c03032040f100058242c94010030801000c1d013a502031850700c08120140810340643d6600402c1c01d5410300140c3d02184400c440c0b00f4400d6050401981d07000980000340c000140c281071556002c21640030740003800d2692100342624900f246a00241d5002800104845c03051074581131031402041e0074001203120307000300034000400303602c002108801d07610110081c040c002d1800c6c01501b202c00416150b5421350140390150005a00c1c2440300003c82c1e0780c0381d269003203403040e405081c4040050043c04e0b04003447c5007080b05805034a64406a80c0d00107400d0720001100249414165518082d01800141d20f146004010040180402c1c004a01da0b00c41d00c180c1d114810182646010b0380000c40e58003200000e000010002e05119184030b01181c0c0a66500c00b00850b200c013440388a41d0b200070080000f064100050260a00c0c90111303848405030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 949739037 1250 949737787 949737799
    0x2508010e0622030c0804030b0702060a0b010f030b280608090a0b0423010f0606181406130b0a0302030403110d0207060315081009021003050c09060c0c19080c 69
    0xd0724601c0e129200c41903410b0000c0c150000c04560041501581210034110307040914292500d0381c070714040e8000c140132a0300c18014082c0c44040f9404640318001c0084038407058580c034078400c14522040707000b40342004d60282c1c01a4244000e1511010043e010705c180e861b40751110350071030304001d009454540081d200c4a00ca9002c1d006060100740c0d550011604254004807201018100d0700320340c40c0360b800c46a860070042d4a8008403d111990a0f4483c50480301662541d01070410b1000031079507034160702d10580c001c0800c1c480d014900c07868080300805c41c1c03403405d8103000c00c266118501c900312500018640000b00740d0020038041895040036000c40c6134001000188905c512445d0001c1d103512641c07040304140b685800329000f0100d80c3c0d440d1031b8040d10740e03203048079162164031080380b010300072500f0240d0103030351b40b025103880181c032901030a0701c50540c92030040d28124052040c0f01503580982001c00617030007600005840760380d0309800d80610380d05480d8204000750425110508041d46440305e1442a9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 949740287 1250 949739037 949739041
    0x504031106090a080c160e190e0d14070501020a0e0f030f100b0f03030c01090c0b0a08072a0c05010f0e0a030204090f0b040308150a0320032508010e06 66
    0x5800a54160381c1c2da40511030503121140c4c1ca40082c540620780b0f503465100186d40c240402e000b006481c0301449481360020103910480185200307021a40e0300c241d00c144a03000041c070a00240d0190450384000c0045030050742c80c0030215160182241c102c00300980c0000c5080d48040040d14080c00c840c24400c0044001e4096034040022180d43d4441840018003504c5e1a03a5040503196505040c11149940c080d00b0b40f503503004c041d100240203013281c41c0c0458100e08413000201c4c50300402c1e002d072154103801c1d4407090300c2c0c1e44544206441c2c9401d0740310702c80480404089080200d440381401c0303803c207a1062081002072402c040000d00000c85050140042000703c00d64460305603039a094420440760191400078000c0014201030b140d8100219000c0c0c60b0003c00000c0c4401c055100b100307184030380da50f82a010f03441e150400030000503400520005d010201e00c0016011000c066400000300900001d00726a0503480e072003140e5081c072880c2c03540d48401010b2001d042114082c03e0048150101c0c080d009031000f4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 949741537 1250 949740287 949740301
    0x180b010e092a2e05030609011502301c0e0d201c050a03242c090307110a050a0e0709050910030515070e041802130504031106 55
    0x4001c2c03104400d02c240402c02c40c1d100440312405221825070075004003080030502c0d403c006841984107498250180361703058000250307820710070200d01594400364081e142180f1035858141180c01d04800803010700c00411030356041c1082070030041c404880c5941d000c1519001c02110602244c1e0b001784012a5500003007035424080360f100181405c0c98403001000250024144a0903240c00c41d04001c00c3d84c286010130714a201075400002030203075184c180d50203000700c01c0190724280c03069124500110700c01140100500c003803410106591003201107011007052289580a14108a04c41524065200c1e00005a80b4080c00407248244104070384c11b442c52140307240742c50041031901c80d05100341d846104160010500140c8511203250007401c008120081608210166408070882e41c0f00840e624494100342c80c1c6040042c1448030b12402c116121142c1c0c2494240502c40a048803440c090260005d1041d402c00680c2d450010500640c20003100251510706441c01070304e84460b0300982e103040d0348028104102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 949742787 1250 949741537 949741603
    0x309061b12050c100c180f060909020307120c0f030e0c0604050609030709090c0501120e1b06090a0b0c01110705030d0f14090f010f0204050a0504180b010e09 69
    0x141c14070502d080355881e840610030314100764402070320001d03e0f4108074102d00354540c4080e0b4030007082e0b404007501400346d50307030f00c2c00c1802d100013481600301143c1100c2d810803000c0066030155900c0074103410902c490080c0c0740942c204507a021a005e0f0086004807081c1c2d0407150b89849103080e400751110080080ca5a90000180c0030b000d1803040c02d101740c0c00090610b0b056242485190020089510b040c80041881d1400b01c10300e1009018541c0090302040021450f04d146015507001d00c11401c01900c1d00c40f5040e01d89421504940141542200041145802c541c41d2486014000c000c5800c2d59a203400310a400b083c00c0d600c0900400c509160144038900c045840402142c0302d00c0d204450004580181c2d0030304101030908500726498a1894804004d001d480c045030074540c0381c0b982d40c020040b112000e0f0011b0b04034041d0380940798011a5040c014080c80c145548200c01c0d1004484a0361032000b140c3c0da0b10400d0f890240c101c4003801940c003041c080c0000b41004001104a40b0111081c030700d0303100e41e0388524 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 949744037 1250 949742787 949742813
    0x1b010606090513020a090f182913061a0d060608010e010918080d09121b03030f1b0f0806061611010c051b09010503060c1e13030309061b 60
    0x280e00703a0001d041d043d054046c90304c91004110074905041d096954543c0100c0c19242401040000707401c224014000e603104440ca8241400e00411300e030301c560340d024148010131102014401245035502000300d0283d42103030421100b0401503c2040e070351703e0300071035440c00e6514130340c4050706000d40d150041c410f80d01e1074100c1c1030648400c82c8001525184070303203c049400900360809040c040b00011351005503c210740100f880c4d240070f5411103101e5414444203c0d0f130841c3c0c1c15650b04041100240714800a4841e800031550003d2046010500501c22440d550721840b604c1a0300303002c80c4007130203480400c40c0c014000c01c0d4030802c11682e0300e040640340c3c4d80654280c050010300401e0901400c1d03a01207168062403040e03451541003401c039107924450070b03802060280030300c02142c0314005203c0005250314001942510071400c02c090281001c0300082e9240640b20030a2030943c10590604c1040c8035000101c440b140114000e0340d42c1c05100f49460b8015191285248107441d0152403a107010001c5072000321600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 949745287 1250 949744037 949744069
    0x504060b0a051e0406270806060d0201020c030f06060a060503090d0c081204060b0a08060c0f0922090c0821090a09020d0f11071115040b1b0106060905 66
    0x2070ba0f19100c0c0f4016001c0100546500070111502081c0401c06a40c0203518014909002c00244c020902c01c0001003402c542501c82d084c203940c0b09600185290a0141c031840e580c91060044419046c0c0c40c1d00007a04010350003441d11850760011042203078034a406442c1c1d600818150828074034509000880a8550000d00d205005001c0b2a400c90000c2010b10f01c2103d1060101c01124041802c0600d041006024a903050700d1085800c09404544a44003203207190145428501945c07030710840724400b141541001c1d9541c0ea0007004801c81b00000f01040301c10003540c2e10b6280e0f0000d0019920716008441d06d9550f000b0300d5082c2d124815001c40008483c107a084c40c02701100901c0e03103501d034440008600c200c46800210080f400403400d0130180c09281c00c440440007698509200101d5100c00802c442d02405c88068466800c44181c120349003040300c000c0210052040c011403410303885044000c000d5000d5016101958250216400048000c3c0300e0440603001c1841d00304080380c0362000280ca170050340c100e80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 949746537 1250 949745287 949745297
    0x51e190f0f030c1b050a0506161104020c070801090303180209060904170f2508030c09060f0f0901030c0504260c040608150a051e3d0504060b0a 63
    0x28080c103001d01c0008450f2039022079000724079000c810713560204c900e4900c00c5030301915185801003201e00d085001e9402d1001c6c5a034242c6011000c41c1c6030080c1d240000b20031aa0090f03400c02252140300818440310b00a040c0ea00008110104189801421a1140700125a41840c3c00b5000c10059079041031154224500316115840c548031402d0080555024007070b90f02182c08009042440200a900900019810702da180c1103421107160040f00950300048009114203002c00010300340107066405400d03c804060822402c0c0503401c3c50b400302550250202c9616904003089a01c410760b8503000c0d00240400c5444c010b4100f5280c45502100a00d00b9110010081920803c03101c2c0150708002c03d001c00d2500620a01142d41e40c0c184890301d40e503004c50300784c510459160000d00c002c41c06000e071b103010390104c85034002d51008100503c0d149240c040c21807103014566018015a681103285103010780c0310101d0703031500e0a08888601c155000d1460744558082c0b801e040e010407a0034410701c180ca003100214108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 949747787 1250 949746537 949746563
    0xe09040b0a050a06150c051c0806010507030e0904081803010b030c330a08100b0d0902030a2429090402030339030c07140607051e190f 59
    0x103600260541d5004001500a411720050b10180d010a2000b0200c0c01030064400788080c40b0030313122204540c0360a0760042502c000201d005035200d18000d003081406880c1c40c5814104542c00a0b901101c282c1c0c00303032880c45d8007049500b0040084004d401c030000e0120002c01c500b01c129408251598a901c0b245c610441000c8084000030094125a8003170b0032041e4180710741000d124032600360035000815407a00095941002440c404203092101c4151101c4540700c608240a110303400c000f511500404a070140200108000016441d42c0c4c20b05140c80b2060715a003031002200c000208030f03040d0084580c1da20405210404900313145490300c08422a0541d00c12113030b543c0e1800030a185101e2108184841e441c0d4030141c11075061400540c61003204016081c0b1415007040c0121903903400740c024500e1a81d0041130b000c11502c0d607484003800c00c035007010301030340e0038240c00b078032414100f0028400603030080e0720680c100703a0b00307c0e424031601c50360304009000700c5000c40207511000407842140000500400601e0701c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 949749037 1250 949747787 949747801
    0xc01031a03070e1e090a0303061e0b1b06090d02061f03080702010507080a0903060b090603060703050613020a080604150305030a0813021e0f0301061d18070f060e09040b0a05 76
    0x28004c3d800406a0202129802d060302c0d09a500c5038002c4055001034a092008035a008101d085194224004071100070003508010f0899041da01450341e004010403018008580d0201c2401442e00c1401c006000c0c049410036104082d0070450003c00707000c0010410460080c1802040c218442525000030405403034190500c011b9900d4810b90300040e200c2e03080800c4884503140d016080c1002d4a1181505000c40101c28080c8140c80c4002e071800c6a03d40c008500040b82c0b944a64803840e400a00100b03043c00d980102c00c2e244049034410720030180020b01c60b00c07c11030300f030074140944032500215039902281c85c0c1c9561500c41c0c590240112980c1081010408901707800b2004d40c030104d10700d400034103403007521150303094150001d0036401e030703090061481407007409d940d28040c407441d0102d83c2c030f000c1040c0c844001280f0034a6036241c0109242040c8500b800b5100b052101048010301801c0c030a01b22818a60900350003508200e034a44a841c4652160020000041c00020010303401c0318110401181c03d0311550303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 949750287 1250 949749037 949749061
    0x60e1003110f061209010c0c08070201030507090b030106090911091c060b04020f0c0c01111011280908030702060f07150e011d010912050c031306020c01031a03070e 72
    0x50711a8807000c04103104503480351380e95603035000e81d00341c400030044542291003d403425001e840021b000c024041c400540554002c1d0895680600d881c50119205500c1c0c86c200c030201e80080e000320700012003140080c0207010452042c2000e180307203000418181030514001800307400c0000b01d0702c15411a07030400c07142004003540140655920062003517403109003500d180100e40c1c00801400703003130703100e00c00c503c000b254080c2c8000035003003a104000e40b4041c900000c0e0600030349254602207041200c01c010840000161640074000100e00c03200a19000c059a00020000c1d44a604140f100d030f0403c001c1c03c80140e03580c1c2c048805880c15048401d4a0740b419081881d1141001c070040a0200d08041c0d050a0740b100c10b6100b03170003050340605042a035005004500342220180d2038000c0ca1800541442820a07001d100035100890100088a04d86010b4480484900c2c002c0e078001000341c0c0c030941841c402907805000c0c0070f4920013807004142003045544c1c002545d0300940e108614000c1048408560360417510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 949751537 1250 949750287 949750309
    0x1e080c041e090606031b0f080c0c0a02030a110901050603192007050c040c03020412021c05030c06151e0d020105040506070b0a0e0111040e0606090406080a0204060e100311 75
    0x2c9041040415541c3c00c001d0050030f00a450003007611034080c001c0c03a010f80540da00c403505039180e40d12403ca40d91140100141503200044000c00d61042540d20350050781c00b04080d00040c1d20504150300101803c40a0009460042e0481c81c403e5000f40304002c1540c00407800049006500240807808100700210074210101c80c0007611409a4000340d40003d00c14000b42c9400c03440c00640f420082e800d0180c1085049020700e014a01860740320f40c0c1034801614201e41d0b4405c2c8800001060441d0b10496540e03685150b0210b040001c55803c00c504002c03031341112800e6841100030541c3c0e050440c64941c101101d2080043c01054411070350000c400d0103591007181510301070400544266500c20350760401115115084445071149424281c42c103016007018000c3c2c0780c1142c0103a40090801cad081900c00c0544c02030042c0429004003007401844002d6803503014500003403203048090700c0b0f151160300512090719925000341c010189904184101008500c2c240360850b6001a011410900b070080011061498 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 949752787 1250 949751537 949751549
    0x10020d0305070e101d0901051008040503040f1806150c1e08030702070512011a060706091a190b030706050a18080d1b030804240501061e080c041e 64
    0x1544d0040c403900d035000814011400c41c03480e41d05540942c0c8404210702480c0034000c442e007007940c01c14440031244c0900040340d0084d200f5400c1c0ca0030181c84505101d4900440c0d800a043c0305000504a94002460711644001c2e01c02a6000035030781c0c1c81703004003401041841100405500680e42145d20102109044500f2141d1080d0312594900b4000c4009656032024040e586c401c40348140300081040b0f0500c0b0f0b40301188481024031820424010802120b9041080161031003030300e410348440020b907603841e5180801c0c2c4c048444c101e1030030140d813025807c0940038065500b082c43c103111500c0c55500010b50074112020751a20f1595445285000c5a10020002c1510121207044e000481c03400000701c2c3d205050001552419004941d110141f80314501010024000c81e5515000c2808a80c610300025170340906110080c038188600c111440498400343d1102001540550b041081b00002060b058140281d40ca007684450401ca4001c0c010340c891807280c00001000400c10290490b00100840010304d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 949754037 1250 949752787 949752799
    0x60c030e04050403051c151a09130608070f050a1e030804030b07030f23060f04060312020f06100b03071b06090201090b040e060904050f06090c0102100c080711030d0f020403020f10020d0305070e 85
    0x620040c1075022f001c0a0081591500074440007103891034044002108440008000040c035901d000e001440c0042020f44e440215840854080041601d8400a00096110360320003c42442e00302c400908035541510111000d50030010316a01c0004103098880d02c52848120421540e10f0345400615000801015140c1050500078000f0920140d40001c0c0340191058080d039054450511103540c40310342c212031000300a003050300180038910b80c11b0301a6912032424100007000a882511003402018844001c84400e900d0300307910740c03c5507400f007407040c01001c1402d900390170706050880e0021a150003d1605004141440c00070741885001c00c41c2e0303200142d410082e0344c61400c1c402502d6840f110b000a40c1405031040502c0808102206c1c4685010000326503100e4444c0d88503001c04542200b014820142d040c4000e00105440301071520400101c040d00340c0b03006a650345944180144a050280403a1152500c0b1a0625580e43c0118203001c0c1004240b400084c1c66a50b48410303640ba000070341520703420203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 949755287 1250 949754037 949754059
    0x20f0102101d06060d02030307170d1109010e03030406091a041e090513110d05011e06090b0303030402030d140c060f07030e0d09060c030e04050403051c151a09 70
    0xd08029808502e400c641c400d480c01c507580d000c02c2c0030858811800003074055000300101d0001c05d800031a00741000e040403440d203107001404580002030301d0741035181c5400700780300081684042da00300090207010002580590b090038a01000a40245c3c0302d8840d55402c0e4203103018501d10450f5080c210780140104034100c0b030360030702c0401e82c4c88050031a60180d505400c0c54140414402c448140d980c120042d80700d900c3e4800c50b1241c2c400e00869030690a000c0b1295034840c03c214482c141c00170344c0c207107840e20000c03000030345546005148002e889000061a0094200b00140009600d001c01c1038100b00c2d0f4503050100c00c1c05074606001180d441018502c0100d4007030401488445030100c6140303401051542c1c0c1c14000b03150901c2400742c03280d1a800301d090215215080421115000c4c0d154040d28502905127030032048121000303d010f17502e0171101140040c270b0005039694040b40c14403490008038181e4004001c20550781c2c4543c8003160f80b6000301c03080c1d444180d0002e501c80e00b007002100d15881001d40400914 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 949756537 1250 949755287 949755311
    0x9150118021b0123043314091626100507080f01080309010c02150d060e010524030601031e0221011710180b0412090918020f010210 58
    0x707000316001c00d4200f0100001a003010040b000c0c2103409142c000c8030002006c09034100f10700c44601e1308078203002420a50010546c40c0051485000020700d05001e003200c2c5458084410350602c0c0701140001c0320341884034402d1000302080d500b03120902c2c0f20165030f4060800002d01e51864505051141019181440104070a00f540076007001d000c1e110000075500103980752405142c40e806618019070000b040c240c40c2c1380140ca40200350841c19608000007515100300c10301c0c1c56040ea01a50008030078194034000401290078039003001140300e1806191005090381c1400d1003035280c400032780341a0416446104030402c40e500394203007140307800400e130045650f0010a40902c2c140c2d942c000c65a40d00e102c0b1240002900903480c140380c0c1e03c5841c4400500310030741c07080350050000c100d000b40700d0003001680c0074410300090940e0b0440e802640907542024074002940c600500344001038010044040c10090015040c1c018403885c81c070700541c1103945013500d10108004030314080101c21011003590500c01c1810039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 949757787 1250 949756537 949756541
    0x80f030901031802030303070c020a090c110c030114191416170606090d0c0909032c06040312020c090709050a0e0f0610020a1b0501030509150118021b01 67
    0x5101001e80b414000714030850b10300e85004100c41c401035059002000092505031160506045461000300903502030380d2644440000c55075880200008600810510234081c4070801210f004480110002c0c403480c0b101056501c040320000d80489100d0303040e0703d4107034080384464010000c0007807040c3c1004428a4151080c0c401214800e14183c0801c400801c0301c00c00c0e0022041051080780084c09080ca450014024000c40d42146142654070454649002c1a56801409118140e0380682d41d8100ba41c1d2810901c58031040d034001450004521281d120481c644421301900c003240d4104580780815041048103078189080d0300d02a550101d400d004011003079401299004c02e80c0e40c15200c0e400ca19072602d000106850083d18009061901f41d0001400d900d07007503119407820741c1c0a10507190840606d94401c18040342c244040100285006018082d45d68913100303055101c100c80c402031403545101c1901c0c40171401d040c0510842e40c2501910b000035040380b90111a90103c00e0000b4158220301001c0442c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 949759037 1250 949757787 949757797
    0x1202150d0923010501230a050607060506120a030210050408090a0303050a27121e03090314010207030e0f0a050910030c050316050402070309093b0703120504080f03 72
    0x74600d20300048011000b030707051003030506070b030045040f02d001c0c8590450080916404207100795400712002c84007040984070b10015060680c82060301194034140601041214030107011000c440340c0c4441003100100b54005449108404102d10016143d11242040c0209215101e881c0d90082c022070800020540d20200800e00800c0b59501c010300c0c40390000c01c2020626801e10054190fa104544c18003500d0840b018030030040740b160314204a44a0102460741e00d26031000c5094010503035103d0b0070401d1005c88292509014240cc000314507014050781c014014110b4503001c24020010a08070b15035648038086401c0150000420f07880e041d00c0c0c5641c0e0b46a11008070701046546d921ba180c0001064100010004548030180740b042c800030b424a41400000c0d00016419001c020b03d034075000a90041070300c034200ca003218101c14030030458071402111034000c13680e17001020355401041c0098400c0c04046158003d4a51000c52030740300c800c440070202c4080c080e035004040240150b050710340310365800000400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 949760287 1250 949759037 949759073
    0x904030c110a03170a110d1d060f0a031d010e010509010c020c01080a0f0204050a080f06090c0a1e0803280e01080f0925080709061202150d09 62
    0x1940c506000d40c14002c8803030a5200c000c10f18002034001003001c1280401514050300c0c0d92400d0600030b220302242030b24220300a261000030030701011320222000304070001c2c402c015400340c40341c500e84402c0c008410b0551080141c1c0d0400c15036a103100c2c45141c0a0b0024144074940e9400082c4828020119454001c18040d0b51220b03584d841c118403c41c1190001c240e600016105131203c91a65885040c00c1c00980880c200e0600030681c20013021943d65941c90700f2801400f4540010b01c41200480069071a003203020f00580000d0744076010591141d13441f6000101a2080c03100740041d1000f00705202d031010304094104a049000200e181c528903480010502140804200c2442c440e520400d4191402c407181c90803540003401e01d00004140c20400f0201d9504050b0309001c69114803031000729002a0a492841c038050075907180d10800c603001042100c5405020884810454a481c0c000d5512484080850082c042c1c40310040c0c0c403070801000c0040d602c2c04220400203120f1220545868074800c50004a40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 949761537 1250 949760287 949760303
    0x70303150627030809010f09030501140601120e1f02070203060109020c060f07020a0b07020a0b01090f0b0609030c0d05150f100602030705070302040b0a1e0807080a03080c180904030c 80
    0x1002e465044010400b22500302800a140600031030044490703155a45502c0148030300501c0000004209100b040c8000c421100c0000d040d05007c0b00040c4000c2c2070b02c0300001c0c0d8a082041d1800c014101280c0541842082000d640c0f202c002c490b0782c00042d004481c40a940b50040340e000291101c030580061040c000c00c5410b86030360743d888081143c0208015a419001a030003200c101000510628040e50405514012203c040c03801d0780e28050b420030b00340c020f0a0115100c2024079005403035030141003401c81c401c450850829011101081d505c80303582080d03501c52101c0c0900c20040c0301c0140403924040381c0d008003140243c030346000e80440840c00ad0303407525002002c07084002170302880401640c0b4a00d078802e01603d451451a000c00c405481c04104541d844600c405000401c1010b44060000318001985428092854400540d003061350355817001c419034200c011604e0000364030400703903540444450710481c1c0326100541018100662408000c1e000707980007051000b80350b000780c1a0300d2200d10031820 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 949762787 1250 949761537 949761587
    0x5121b06031338040309051924110d1e0e060a0c0b010e0c0702040f0627140403021002030c0942090d0206070218040b060102070b030703020703031506 66
    0x1e420603030101198007600189224074144110f10300070551403501d408106230500880e81300c69803c200c206150740b090091010007411880300035004a51110904042d0010b040c01c0e08601e000a403503500107040700d5120301d0200c1d112420807400703003415107400240034201070389440307900901500d82c40da400f40944e80d02c150403000007450b5100d824014030901e990b00c159800c00105900f440f000c0c0011081007940e440e190703640071440c0421000000400280705543e100280c4844c400c1e407048410001108290a0b800410800426000140328074134803140100185d0702e0341c81075003644950207810891075000100401c5000c403074000745001c1800c45200c08100b0b02520f000c1c03001d00d040e1041e102e543c40300e011040c412006280b5025801420540c00580701a10300401540094062046510b0200c1d00c89026418482440a009296540b080083c001000401d0406480040901000b07045000301500002c0700e03000c1500c650440006c0c4a0b030301072402e0015442da10080c00b00341502c00c505101c11101e100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 949764037 1250 949762787 949762883
    0x613030323030115110a0219030b0a05160c0623150102060103050d1b0b13200105070b060d0b0a0515010c0c030204150e040305030105121b060313 64
    0x100da040b1307604808101070f84e000c120740039200043c10400c401c0c038601880000b54090380f500042d090740068040c0782503a10b58294074001110a01c0948151440351803e006c12030005100c030690315911010313080100c807060261500303901401c80315509444a071002100c096503c64090205800340140d61103d05405003040700480e60758000344009051135004042c0e001220b806022040c8040061001341c12000c1081c1d143c0d801020f0082d00d2032104008805140b00a019441705c1c045d80383d00900d08001083c00c2c0140000f0020701030380758050032115409001c1034030b42d40ea1403c405c040ca640300081514a00c2c0400c09040141011036034941c400d24024a005d0300e030f40c4101440386c4160360001440c42d0050039502070200a080400e0b15541140c82c554010803a5889401400d00c128440e81d1100d03138940c100014000b40100c8044000b1107136009180c00f10b4014a075083e185d6104c0c80c02d959554030780c1e540540d62482038947c0c00300502280d0340e490748608149040102100050f1f2605080481d213003001e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 949765287 1250 949764037 949764107
    0x709060e0306041506050a0803220b0d0f0f0905100e0703020d080c19080405010905010306051c02030c18091c050a050906070819080603030a021b06130303 68
    0x5103040740e05030421000580051011803441c0280000d10a00041c440d49400c04202100042e800c8048a035102055103210031140003c0c0079211102c8049001007107143c0301501e8032a016202c030a2031003580b129402c800c6d115080d0f008a03610b40100d8024480c0c1320b12800c0054642c810445030440c0b250500c0060594908002072243c12240c0c064003103207090307920ba154500c41e40c01c580207000343e500586034020008010303d802c012242d4001c1e800d4507034403843c4c4400504216000d6021038141404c21000308090b40c0c0f00b41d212140c04000280d464010021840020708004070000429440f140014428610442c600e26540c480e01140048070f180c010401903241019000c0307107c0724001030040143d088250710920182c0004d582c0504014100303159595000b109410201c4142c5d400b0050401c0c5d401e01591005040f60481415005180307040840c96000b51900c0c1e01d03609040943da00e500c248510380d203031101180c40c0881e20442221400382c0301e19005014414860b01e0700c64024900300f060741d140e1041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 949766537 1250 949765287 949765307
    0xa060c170906090d05220303050d060504090210050a02150c0c010f021303120e0a0e0a0515131d150726070c03020f011406040e07051503060a03050a0803070906 70
    0xf103802440080204101140c0b0355100e46041154104d140940c8100043c101c82d100001d10f02c00c0d200c2da500e41d0640101d80003207820343da106034401d0382842c684c1c00c00342c0c80d24107401104004c80d140c6a0355031040d0003003c1c1d1402211500b09515041c0c0041007040c005105000390440507103041c02800511040c11196060b4001c1030804d83c280b0b4019541013000804502c006100c034049400c0c2100841070090000e101780019502c1420340300d544008000c640d01c1c080c803526034044c580118030710b600c000c8000407a040f41c50610500090583d180040b2525021440c00010804a14021a1900c5503409080303000103d00355285004503d060528607864031006421708980501910884070355130b103010007110100e1b1011801e40560103441d1001c1c00042081c0240444034044d60607420080c103142c8240821510710340c44440740b5801c0f40c6024400b0f0b03a240c030030b43c0307070340a0a5501d41381c9c6a8a440b400039031413100b40e500041c101e1081070001c02c02c000358007024502c20440c94032050091580c8080983e421494 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 949767787 1250 949766537 949766551
    0x3090609060a140c01020a0e0603040c090b030307150207110603010e06131e0921021002091c03021f060501021f2004081015030303020c0a060c170906 66
    0x6000c0354416040c20009405515142e1810407911800c00403404095070110100c000c05075000121214482c0d081007246200c11416900207280d0300c0c06894002103072100d4010b41c1200d581715039043c0c145507020004c1d0781d0940d170041140f02100444442440c000d5008420484800e00b42020b00504d610784502070743d04a44602d02907281c66034624040010704240d0015404601d030341c600f94151500380002c13140943c3c070750f5580b00103600d80a81c10243c07484c95407013618181030300181c0300c0301c00308503400f24269440740400b0002585a280000c0066440030a88410071601800306040d070b81850742c0014044016a0341c1018900c001c0040f004030000d5407100c0c051607000d43d100010100c50741c40100d00341909203490450018038014171400ca0b4510844000c88507241220101d01405501001d00034001d80c501d000c4401c001c00b8602c40461410040144030141c123065001c9120440c81005022040c0c5003039120b0300c02c01144000c51400707001d0f50784d0054410302c07a28201c1c3c00200480000545c041c01006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 949769037 1250 949767787 949767799
    0x20a0c09180f06140a051e1303030e0c030f0d090603020708041e0b0d0207141c050a02100c030906153203192a05011d03061501020d020309 61
    0x8807076180c0c00b0484480d0705084510341d81e200c021304810f103008039110b4000d01c0204004030305400c00000d80018a10454040c4915000b070702e0034840070210700c0100ba8417807070389810042908000707003007c00e0a01401c000d00c1c0c1e4040c0a4020f00c603d42c1c8401107001c8891507100e0310350325030068071039204804a019180c0c005083c0501000144a000e0040301411000345020720040354076034603040c84c4203050b00a00d52032000d15401003403000030814074200c000b5081d0082c4008103a25140c6801481d02c00d484020401e05114000a0f080c0b6031620911074410714034640c003010300041c55460002030040072194400d5500c0c40c85e100c001d8842207004e40d0f400048504100110311008981c4122004107480d1a4080300c14a0503d0809000ca440610505501d604a22031000e02d01ca900c0c140100c054054081c107040c103404c02c0e44808240d2046003500c0d0b00759075082c0303065000c02c10118848808203009078021641031054004010100139641c00c0b42072070140070382c00c0d118400c04010090740e49000b03015506034000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 949770287 1250 949769037 949769081
    0x50c07020913030f120213030602180d0c09020901050c0307110928020306030f070323030f22270e010c0806040b010314130c060c02030c0d050f0d020a0c09 68
    0x142c814850175103060b146140040c0f41c51000014654120340b035030300446405401150700c410f02d14666144070b00005090322207202c1e002c862b64038600842e0440c000c00424640c0850305c0c08580e44944150317090041c044085903642d07003460802d0640d00d80b0081070b80d48903c0d0000006017000340d04050003c191200341080280c084078007150070019400042c400c982600c100080c42c0740140c001c001860003140108420180344003551501104908989940c281c2c030342c000c1000751480701e0b20500300c0f18102c40d8800d48030f00a8054840c200c6012032964000000d80030300d641c1880c090810070070b01010400f40e80404000000009203a282618100c54400f8081100c001c0018040e00f0540c01034003070f41c0414540000c2c4e50002618030741e4200025900e018801e60200c00c0c0c20f0400680c90881030150a0741c0c1800322018146a000940d510004c0207402e0040e03079055030b00000c00208100038002028010305582c1e6851a062009540f0040b0500642d25894000340010303070944944540040408120400180c01c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 949771537 1250 949770287 949770317
    0x50601210b1f0b13080d0906050706110f03091606020a0305070f242904020d0e100f060e01081e0304120807030305060a0e1f0504050c0702091303 64
    0x908024050700c02d0328441c4540e40b1501e0000d42c0500c2c00303081c1d400c100686585050003000c2d034058070340e04014566404095043d100540002c5004200d805034a0996a1889103240001c050021014000040840810a040103c8201025500c5445204d046512518624404460301101d0b845002c016800c04d00c00300c80428442d000510045006d013040030b09000c800d50303a514100310400b001c1407002c031034001c0c40d6090a5a6001e4a0a400080c1d15420301500070310b03040144400c054210349110340d41c0010a40014803e90300041105c03440081910800e00b0100f13654030183c150007240010b16032031320b0713070102d900b54510b4401d0f41038801400c014101074420105400000140c0751400318144024400080c05c00c0c101014100802d2003045100e403a019685030180546902816007889021641c0c0300380305456204207119448030600070103600780714640c8040c5c00d1050684c1c100c0e27a0828102005c2100b05002080207280b194401e0750380700e445541d008000746101300e10320710040c00070f900210301c0303420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 949772787 1250 949771537 949771553
    0x627060c0f050601120c0801111b0a0215030703060801091e1b2702191b2a0f080a0209060f0d060905010e030913020a09030803010f0305060121 63
    0x20091094602103028200303616481c0c90100e09911042c0c1200c0038900300410002810f4202004100887c024400ca60a0040e00d21a50290400500711011a10b80c00c0700c11060400c4642c031490303005807100c03109000325100f462007980100d07032100109042010000b00e45a051040c19065a080b6001c21910b05101021115410a2400c140d41c00c1040002100100c007120786482c0007448150f110992080e200d03580301141e208240702040c0006e106104816402c420380c0801440441a4900084591790300950144407109440003e0565000304c01c2440c0c00d01043d2014001c4407805c0d0729070044082d41c4042031094040c16001c0e070829030700074000550050800c04585038000b800100b03c989500d030907a0108a02d00d000490903203034583c6641d816007d016081c407400c5125500403028514121209000c590800080503082001756800150600c4841c4510740880180d130f442450290303603581d107070550b05031b8141c07038001501c043c0900000007031418880b4111449403602d1602c40f009018a5454040c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 949774037 1250 949772787 949772807
    0xb15130b090402130f03020102060a0204030b0412020f1b0a0f050a090f091e0605060103060605090d06060b0a0513080307170702030c04021b0c180f0705070219062706 73
    0x70b042502403082c3e4800c000c101c030005024140c0d42454860641c51800028a8100c0241142c1c00b542d00c100700030300100b1080010349600641101044241410a000492811000e1602e581d0103018084071000c002c04034407a082f030781600403030b110508070707403500404034107034106c0d101e030300e6100c1e0b050700b810040c41180780c00c2200fa11050311400900303140d2a80795092410105101c02030601500207604007040424441d10390070000a00e82002064200600a4910b100e00d000443c815041c41ea184401c00c42181c00190250031080b41c069120386030104c014041e0781141e110000182a2030b80702042e0400004180d901aa41280c000701a0b00030080800c44d05510a0200340e0b01800b6444e203101d02034446000a012070050305c4841d400c1140c14a19030b070300f0020b031030300c859124640000100c4130640c66000c80326000b880d040000070042c3c5803404165164400c1d110000c0d005000c2880c500080180030410600b10755003602c070144070409a40c813102c80250140c1403220f044207440b4050110b9403080e03117011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 949775287 1250 949774037 949774039
    0xc030718051906120c08010515160f1703060d02040903020c0d0b100b09090c0a11070303091d06010f030213050a0305100b0303030c031303051c0b15130b09 68
    0x1000d580e2100081008a9441090040d04080d2001d0402c1a1a442281c640c0303210003401040002001c1060b0040406806100b924030a0b0501001006801012070444d00e00895940c00f0b80304e000210310381096002038402090300c072020310092035108405208100c034400c1e580181400603105081d400c01004041d01e95045e01140718040f900c0070b103500e8204040600a00071142580e9924015410140c2c400f0701381c00085614809014a4420b91a2000215048900d118a0507100e400124080b5403072404120f14500ca03200e44540001410b40041075001569110200d909288292402d0340001500a8a03454005009107900307030942c9101e0b070301030403017800b54051500020380d80f400010305100c103940050310203030043c80960340c56022074462f4100f00803083c0c01460862600d040f40e0141d501005080c0c00218880c6544103040501c0761080360400301a9003d05000c1b24040c0c41c44000400c2d205650070f00a000e2026469030b0140c400c0c040e030702641a20300e14088014106546d45e1040c0e00050316035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 949776537 1250 949775287 949775327
    0x240f1003150b030d020c03032706040312020c2b0312020403051f09020d060f0b0405090d0201110405030706180b0708030901180f06021c0515030f0102030c0307 70
    0x2000003a2241003101080041c080042141e03810a0201803c081100a0000a40d070102c800548284c40120648010b0b124035943c01c15280403000142440204445135030782d10000010f8003108200303110845000610840d4221101c0b407501d501400b038603003401204060005d038000090300b5410303940981c100c08988a440c00014070083e000201c82030342c010390002c580c10b8001840624a80e07040040700c404149035a0340502c550b9015401045002169a201404058407000d40001c0c2c0011a0842c10300c1c1d1f50081d100700034502e0000307025501d500c15005004019400c04c44000c190402d61401c2e40c0079240001c001e00840c1c2c0c0f070080162110042110300c0103040341421304c0050650100380160404c5800f54812540d0381c90030700811821900601000360340b19000001c0e1101080b240c070b031500b07665644410b0040c1e40340d40c84030000091039001c1c44411801c50500c0100801b48848500c1c8090f00b0380198121401010000010750903030004031807050340510240700080c2080d1145c0140034401c1409406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 949777787 1250 949776537 949776539
    0xf050a06232a13030c090e0f01062601140f04050613051e01140901151d06040902060c0a0309050907030b09070827010509240f10 57
    0x1a2801e40d03501078900781c0480418803049404403400801c00c1e030b0081c940d60074a201d150881d52250003150b0085240c00010380d01050710315100081c640c0610207103401891064405690302c4440b00039040c14405006a030040e07031151600c8030414000d0b401654860804250040d9105200c0031380d01d050707642080c20390b640342c0d2100301000d103070800c1640c001c1c41308081445240c54a402d1140c64a078014062100f44c03049001f184e008901c0200381440c8401070342000c02400d507400c0c0035042c01b4040c843c4c04600300603440020700040c80710545c0448200800c241998a4031aa900fa20030f1501e403200c5101c51005030707602e001445c203140c1584480d02701391005010f6405e200200c0e100501d48040300c00110003040d80101c06210b5481c0500c5803590254462905000d110300185c040340e05014003402d03000904c010b242c045180d140010703403c01004000b40038007400d00702c02038034840d010301402d80e034070411802551440c1e0910441100c2d440401c464000903600b1a072640080d024410b0070041c5060f4000540c00c0c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 949779037 1250 949777787 949777793
    0x103080c12030c090f0102070b04030605151f12020a090b03040206040b030f0604051305100509030c010c02160b0c1209031005010303031e0c0e04051506070f0b10030c030f050a 77
    0x10146004001d100e80007600c40c004d60061001c2e01c840c403c01c0381d056620108041146844641c04c031020b0300d030310203c04501d64903211285140d82980d401d64a0f0310900e0310341503400c00426a8100311a0142956520880712644041d0741e040784242c65216001130240a01440300f40201d40055802030b102501051901d0360302c03407109030950000d42c0c41d0801e0500c143c2c10b212007031034680517640d00b12000d41c0c05020525400d07134545d5940c26030714407409500d07038941c0c001811080051080d1a014100354000f0f219000b000071009403500c501c2c070300035440d8002e44100441c41a008200761004400000c0c01000ca14006520303141083c0c00804041ea414410244c070382c96000e0711070107218003c3d482501c011421070350140b11020391050403246584080d00e003446440901d54000c2c0b03e404035001c1035500103440d4480d00c800c18a0455000c1d0383e19040440001c400d4200450308449601d41030040806050304d45803e000c000c80014584006440034541040620200d9180c20b0018840d5100b03070f04558824031155 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 949780287 1250 949779037 949779073
    0xa030509030a240c140712090315020417060103030f08090c06130305150c0d0e030c06161d240d0606020f0c030303060306040f030903061b09060806090103080c 70
    0x1250490158140201d030101c3d85424000d0b9070640c065410414020041c000740e03241c641c0113414000d44100701e1003c0c2d03004540c0c05a00c2c01d80141d0b400440071680a04806081c00207584244180b0030080005240e401030404040744071410b0300da05a0b29030700a80902e402c11542004d01629060540c0201030026050341d03079003c0200483c0e510180d46880c002d00d1818240e0500210000b50400070700c01408020f1890a00805c0341c500070781e41d04000840701c410300c4e1014503601400c5141910b903c503485c18404c034807002c000041ca280d9910303615110060742c00320000c10420544001581c1000c480c1f0441c44c1c4904e40308140e0105400030103845070402e8100e0f156041038804c181d1080d00580c0008102142041c810f100007108210141c0c0150b21350300300640861b5413500c00030f0002d40325542c40d0080e60100b610400b1840c00070350b000402403000000d4003894003411003040c0d11410216079100c2d03000070407500402c4814810742000346054a113a203951116a040d0740301304095071090152051000d1903003440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 949781537 1250 949780287 949780313
    0x50115111203161b1104050a0212042d050109020906060f0a05030a0b0613030204231501030219020105070f0804051c030b12070306052208182107060806030a030509030a 74
    0x1e6411417014600c008203100484174042d040e2240c00380100060100c40c00a916102e070000c2c1c1c000c682d07110851100038104400742e50404200d00955031400c64034148201500714090850084490981e03640358042042500d10513907407580340907032041c040404054052400f41d07034021b060803800f140c0408000000343d01a8010a02603004a0b821902401507080c98451002c03060840b181003000b10041c44100e000316440107081c008125221380190b8540d910940689005010441c4207030314000c500c40c0d0103406040100c03420400640e45404007111288603186031801150440040c00d4200c1030385900000710f030f03a50b0340460141906d41c000d500c480d4881001c0390843d035884002505080781146000415204003a1802d140d55810180280384a070300c07004084042d075480986e6030795910740e02020341c15501107042881d03807103010b540c5540704500c00462200f004100c03110a403805540c650005543c20741d0241c81c010380582c04801d0210020340a1401810640750050071280c060f40c1e43d944100f240104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 949782787 1250 949781537 949781543
    0x7080c0105060301060518041b290313060c1e09050109150f0f2f01141b0721020d09120201021f0b04050115111203161b 53
    0x400501451200001c1c841e890700540114024402d052814000462810791017041d000391801540106042180e0405000010510700d5803076501c059540d52540061510000c1d020381a0b82400f4015146e45d0a00044034810010041640c000b45080e0311801c000b0100b1410010603c510007602c0d0000784010141c017051092107503214800030b41485c0004103941219803100c240300400e0915482c0b680e07042045c0c44247d000e1864904070b0b01c2c3d0941c0c01122450b60300c80075540040c0724942c108070329a2000c8490410128100d009210003580e840354484103405c00c503032510a103d40210f0154181c0c0c8a907004001c002d01680c051001071140380707038004840c2040c5804a0241c0c2c0180607400c485504648202e004000750804540c181c81c00d0780000c0d440340d106000100221070107000c00034014489a0000e0040680500308000075a100c0f803802e041c20f00030a40701e00201c0c03003105203080c05040c00190324000c90440750135203056480704002c14038010001c0400f441403104000e01c40c480313043d440a01e406a640 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 949784037 1250 949782787 949782803
    0x15140711090903031803130b0a1b060504171e220e160f08010608040807050a050604060f060503120702030c030f030d050f01080619020408070b070606080303280b0607 73
    0x1800030030310f8443c8940d4542030f901750308140004601004d07105000011a4003000a5543e503030b00000d403c5641d01c1148000d5203210325403131007150a00c102940a00d11644c41a000600e8030341a02074503031010302a080701c1d03124220550303102071f400c00c030400003422150108103660701c9080d500c0305034078600000640140480911344401c0112000d026111018241c040d030505a10540b240c0d800205141e00c140140420700c0b848101050030040000704868030203800c08195000f1b00038510b44192901d4060340d0603200203040500c803074003040b6240700750421950000c3c0101101c8120401841040d048880c090341e1600512040d8002500c007444070151010b2a070b0701443c0d40e4842683c600d01110b00c080c040344000d00e803410040c020f0340342c00108240c01a0b0711501c40c140701031101d2910340191190360451170f500c0c00f640b0700c0082c0344800e2001a007141c502c9120140b0010303889580c05a035a010445007104140820911000c80ca0800110010f140031000700101c1e1107080600440c0b40d42d40601d404443e100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 949785287 1250 949784037 949784041
    0xc0f0603051b431a01090b060304060504020a031515080f03072003010c080103140a02010e06030a0908130503010b06191b0c0b1c0b06030703110d06030503131514071109090303 77
    0x4c0c0c800030440c2c05010743c54410001010306001140041c04001c0c4001e2210f5070b40d070085001c1d075139219450700055601840300013007a00c00c10030300d8010342005043c0d01c04040590f500407541010208501c0d8210382804029810418180c03100d164540000d060400d00020141c006189a1828010103034201c0e42500c038100345505d10714010102ca02540700c0c1c080a41c1001d4141c50040c0c0c0e20411020900c8011901305461380c4880c44850005d0040d440024240706d00083c00511060b4420054000ca8074110020055503d50200340f020a101d02c0c15401c200d070b40001300009249019401d5021041c044c210001c0c1c690040b40c1e500076244105400c01c5c101680d0101c0e150400c0301c42e101d1000320007170b0900c0062010301272500124a85000c090300c002c06241d00c508000342c251990900f91035140d803007000f05002c80350752030404a80b41e9201e003190f00c074000130440001c6401c1ea181c201d40200f58500c0d03550415201c1c0c105138011941d8000a80031030348200d194981e003071150385000c40da41c060b14818019607928 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 949786537 1250 949785287 949785323
    0x14090a05040c0305100e0105090f09030c0f0f07080102041a0717040902070c1707230901140307150509010c2405090717190c0f0603051b43 61
    0x54506540101e40c83c1006e00c0040c065501c600c01d4440c1c000351646803104040d1280031400f030840c090002e4182083c464000840c0b280c100000e400810601c00000717075200141c40314220780c01c0c1c1c80345004402d601007107501c28404505410005249843c000d003403441c900c101045a80c0219441030b80b040b0202ca0700030964005011040315044020000e0000e51704101c405c1940250316207405100b401080301072a00383e0003041c621a00c20580c000e10040007a071b05980c440b00041e020080e5405441d00a2140920105131996031000c0d00715041060348505040106640045885580101d02140c072440c614070b1508100c4a250065080344410300c201041c540f520000035071a1078000d1740b000102c02541020070713004250204024804c0d20a1135403a159641075802c3c5826118440d42c010501c1c002072483c00240150706502c024007418213010703001e5507075070304420344c5c12540200c00f201c0003111414541c035490350800405d81d401c0281868050813013180e82080c04000603515003415145c404841c580d00e494 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 949787787 1250 949786537 949786561
    0x90c090705040e0a0906020c071d10230109170c010e09010b070b100b030c0c190305090409030306080706020a110603131412130501030c020a020114090a05040c0305 72
    0x4004141c0c0781680c2014034040e003401c12200080d02440030290741e0842c0e0014451180c0403100c1c404080401c039040c0e2540e9503a1520500c1c48082100210616200810000004041d0440c2104e40045240703021103041d18280f08100290801e980c14000e08201c0052400341210020110350200d04c003603c1d941d42c184001500007008000710324803507071710b102c01400101c600505840303c0340c0d04000c860b02240d079543c44056054080d0342042c0c008140200c10403002034107107002012544070b180261b66441400200d195080c000c420b0004000c17450501481200341416030140908500900e0042820307542c0c0c444081c100005504802c0c01030700104d0700c06081c0110380350b40c8248443d00b42c03141445d5281c8103118402c2040310880080004041d0b82a4004d180c100b0040c2403002c0381d0000c420791b503841031800d20507080380300e07482043e000c0303400d104651039041c1c000b0600042040e01070f191f0440c0300d035000ba01c00707915501c280ba611354011080380b40401c407501c55102d40c07035003500c81d600c3c00600fa0800c0710003040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 949789037 1250 949787787 949787791
    0x303080a0e0712141c14120c03180c1003240e06150f07020409031211091e01141e031602061602030910050409050a1e0c02031207020f0303090c09 64
    0x40e40307030302c40c004400e1308040c5e640317004010141501e441c2e0b45041007140c0d0000c251042c0441e003c844d0400805101e02c1105080085029520050114500c5000c50042e25102d82c0c1c8400303140c0d07210a4030300400c01904e00940ac40020700c0600d5580c01052385141c90080d01004a90700481380c140240001c000b01828081e001d141e0031134010815905201c61072200c0745081c401c41400030301890b2141c03d00001c15014081704840d0303640b800004d100d83e0b40c9508907541643c0001400d14070412aa408000f15584000c440210046042c0e4a01e26081540c19100040f07501445014120410146c84d0401c03122000c0701450042d100360188511429401c1ca00a1030b0a4020b8002d001120142d010320030180e400000701d400703050302500d000300603111021003601c1d00e002e207602640500382484100700c085000ba0380440800d0a10318503214080381e04540c3c40044500c01c20005003d60300412410784031100003c0c0c0d8a0b070095152048035404240380d81801e041d60002c0d075904086900c000c220407082d1401c01003c035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 949790287 1250 949789037 949789073
    0x1e0f061b0e0301141602070f0e100914070c08190c1b0b03040b0c1314130209150313050d110d020307081206010e0301020a0c02010801050a050a0303080a0e0712 70
    0x1100400001043c4c48140784c1c054a4108a0320802454010003402404070b080208001c9409026085da1200303d0840c80100300d865018410740b980340440c0c00a01440b4443c54010380d0f0300010f17141d540313141c810b41d107206003e4415039581d0b0042c484041380746582c3d0344107004008140c2d500c07500010146001c5200c06040c01245a03100448403060108034428800d41c0e42c41600120410f542d40c035840000394092041220065200c000a070003c9a000300c00c64000d000b940080d60040c1e14581a0306030a0b01328014444c0066103c124010940740f141c04060255401c0346400c01005001d42d490b40c0d51516060101d407503400420350240710880055030501c10740301c0d06e410500140d49020170f02c0e0f8800f41d540c8a01c08040005070b28540114040703900c82e00000c00101c10140003155140d4407100b000d480c541016600701d00017174951001081605095004074107d50b070140c0044041030035079400b60382150000703100700c80300d0f0303a04c2e07221450800d810030038480140444521901006a9414485405c5c0350080d594 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 949791537 1250 949790287 949790291
    0x60f0c050633030a0b0403090e1008100b01020d050a021c030b0a0b0f070803090a050f1f020f1806070f06050717060307060810031b0e01050d1e0f061b0e0301 69
    0x403425a840100d0004d400d1507228960301c907940e50350300d007d44240b07603940c000703800600d224020059029108000c06c003c1da01c202c0116202040700194110a07620508510350058010040c585010b0b8060300c0034040004050040c0c03481015075401102151441d00002d40000c0d4441c4084851410303c80b00342e801030700580300250b01c3d284c114100c1480910807610010506c10000000131040101400440c0f140c5600c901a503481041d4158503a0342c51202c620068041514600d803c10040700d14800c07500c1000016100f182440c00300120a0030494403801c0840e0401800c201d4000004e140200d64800305200d08070025490504900081c03040301c0061488010002e0303034042c061145c4d0300180072400c0711400e00d880c410310368031021048a0412a0b1703000400302415051460400c0300060024015036581c000d852480340c1e80c0b0000c2040e88a0320380c9000d8520384000040d8049018a0200000914000e41100c1800b485076078880003254141041c0d8003400103078540d0004116030064644070314010440003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 949792787 1250 949791537 949791631
    0x1b0127060306050d0f0219080a110a1211040c020f10020c0709061409090c04020f0304020f01090b040b0a18080a0204111c05130f030801150302040f060f0c0506 70
    0x3031480c5d401000d60300a132242166841c08140341d02602c281303402900b9844107075200380c01c451421508a04d48040320030b1168030322031004109007894054182000c3d41082100b1100f5610360244401417891070404001c60240e0202020004070810244400e004905001030317681080302d0105090400c1034010000740390401c90708102d219001d150a41603800111003280c072540b00e01c400d0f545050080f000d1507420a00126050b121152403401440c13260b8005e66203602440d00240045501f0b03100c5004411400c0e4042c00705100211001000c0c1c0350444c1b20b404c0c05070b4031002c0d180041000e500342e40d020f1702d4280d200007455011400c041c06034200f02c040074410503040262030200072901c6080c2c2c5103107411140e581c4001a140608a200c83c0900e80e400101038400b044146c14010140ca001f40100400046100c4520940d5403280c42120704403080006c00d1100c180c2800411280c004006050000300400341e461000815030900030640200300c007441c0c403900b08102200d406002171561a004c0800458581c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 949794037 1250 949792787 949792793
    0x60509010209060703050d060f0b0909010803091f11060a020c0f1209100302070b041208070c02090f0601121506020f03091018151205090105091b0127060306050d 71
    0x94580c4030381d00d8108291503030607c110b80002460564800c0401d11480c0c0400603603a407104005041c051000c1d01c008030182e0701c60280950728402c8d245901d030400400110070700c545110304c0c0c0c80c1030018035a14003c100d506011410901e002c00565450011035400140a841004204681790860400001411001c219800300b103610703010740c0f035a0900840d240001841854805d5048842c11944444000b845040c18203007a2000c9911000c803801164103800421100d40c02115041c0109600074400c810560701c442401c010340c0c002616a50500c1a06690408000c0c3c20340110107a645400550b136100a1414a00074640408a03602c208550410005460151141c40311000000c100c3d00304051103008140c02075403403907034aa102d0803841c0e111740700c00c00c21154881da01502000341d101c01400140c507810030550072150242c071401650750100c40d400e18030603180d820000382c104050502c0349403c5120144070007005015684d5099800c9114003d20400c0e406200c0d03200503100a4900210822a44c0c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 949795287 1250 949794037 949794049
    0x12109150c110c01030c091701060302090f0c37021b15041403030f040b04090f02090904020d110414041e030215190c020a020a050906030c150d140103060509010209 72
    0x7080250405d44c8845d44080c586004d2070740080241004840c00703040020392100a0300808260008034030a82c185030210b080c2c101d90035002c07805512400140c80c54841c42050000e0004810001c3d0b030806d6455015040d4010b00c0c0b070b1020407507542ca503000f030b2038030f100f03c01c6034034070b00514100c402413190981e144640700f0820f902d0262015541401c00900c40c030321a21340000d00c0e42c058504500801400010041801c07841c00000d4800c03981929028000c0c40000e2850005078041d504007150800e50805c002005481c00000580d80c160041c2c908103491640b850215041d11050406605181007220a000070001402e0b0421114803c02c2c68951824070540e80003034540781d41e8500801c101444001180310f01012904004420022610802c0192000304001c1d44460f00c00c4c2c6c059100c5c00030160001050b04080e462113118080040c064243c0031006410000f40e103400f4244072031501002d00010241c8002803080a5048480102c2c3c201d20350b165242c21810703244000c02c90f03c4664010b02c2000c0d52900c4075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 949796537 1250 949795287 949795303
    0x30b0a140c0a120b060f07030906090308070206071a01090209011e020601061d0316050f030109082d0d14090d02060402010c0302101d010c0804020609012109150c11 72
    0x80d00d0400c50340000f84102c000030740344188010b80c4c40000040c01070501080d00c00103100c1c2910903100c1d44100755036000c00741e50101c0d01d84030240058000700440c40c01413400130300906500d807040a55000e441b2a8240500c1145801d82048103101c1e0b001035841c1696800c00800100c442408004050320241c2c0d0100944814041c46480244921400b1a602c46040c0304608551408042d0845010070b2114800c41800d2140348542c80c00341000414920540c10180180605079070040c1007185400c0d1a03034003c020381c401d000005030540d00d104c0d003040020034070400100f40d8a030fa52503010a581c1c1a051200000034805007102e234540d80403012003846540c02040550380b10750242410f006150301400e0690801c4500c07203912402d83e00d0030088519030012603420040c04c080c2600200100e560280081d1400501510040c0d444201804200c0c11588104500c0907041e56008401c15500c80304c80700c103029030f000140c00f101e042444403003030b054071689403180c10700e0150180b401d44010b566850300c064550f012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 949797787 1250 949796537 949796557
    0x10c091215111e040e0610021b010504171005060a0317070303090b16020f01090b060915100e040b090c070f210e0406060203040f0909030e0604030b0a140c 68
    0x75000c80c040591500000c0e1a50b0102c207501c401148000103014081c84d130700074010200b0054829010a100d810f0010440c010894142c000b03120000808588403041e540084080c2e0401c0350800000c1003e481c00c8031400c2d50048044010614081e00841c00b00642c1c500900590048a54800400102e07041d501c0c6840841041c1c01001c1e600c1440c0c6c10300724040d01c030b101e8015151a141070240640300e5900ea840044e0341d950355007a9000454003d215a090780c19224020f42285612000300c2c680d0b00c0d100c00410303003004007000c00503c3c3c02a400007040f1003586042d401c0c000305442c540788480500b41801000500c0c3e2045070302580c0c03490042e59001a90140407405403608903501c10101c01c001c00104000b0075101c0140c0e80060074990104024544075440c14514040d600349140056242c1c0000203443c203462400f0390701104030303080c460403900620000b07800750108501104c0080094640d0001400034500640250401d40740c5000d6000540700314041d2401802c0080c0100f080b810741d807509803807411907 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 949799037 1250 949797787 949797791
    0x200105030907030305070c0f0b03060103110f0d05060d0f030216050a12081b03040906090f050709030308040305120a0203061806011b151a03060906130803041b08010c091215 76
    0x86d424004000142604034030002c41003960085030150044024500c688801d030b07400c1c0401d0151000e04010b5001e40c100320038011038203201080012070190480b6a101d5409072030b00d81d0005071030f211500c9d04041000140e01617004021201403001428807042d000c1c0c501078540c460087e04e4602c40751a0a010450302070300c41140401c0301d6000d980c0c0d2424040540c0c150300110f03600c0715161400c1c03800904540c4542c070300680c03504100d14049600c1e405983d120b00b12986400242a1540c0c6050311403460041080b0308028003000130490f2000f151107803600a0709a1030300140c89103402d509120441c82c25001e01c40c1000f01c442e08020782682d104141c0800c4c0120b1040c01c41340d0325054074100c060404030000016402c4d041c4482d540f100644400390701042e14049080b100652114000a62a0401525002d0950003402c1c40311010440170401190418415400c90745444421741200d85007000c25042698641d4582c6420844140c1c4816500b010700075024540008400995a44800b058281801c2004507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 949800287 1250 949799037 949799047
    0x7052a030d020c01150906091d120a2610061e05090316151e0e0904020609091f0f0b2205031615030621050c030a200105030907030305 59
    0xa411040385c000303001014104607502c810044024040c3d82c080c44800ba840c01081140307181e900850108a151544060f003005071088122280d01c1d0300038480c040a01c084644203006800d00e21101070f40034010298100528201010700110900082e440344081190b01c1081d1900384150348000011120b0070f0520b5a0766203040b00104e8207100040490b851050480e50000401204550036616080c1d02d40c0c1d00d41d84900783c40c81004c440c420707000508200107a0217040e80c240c51f04000c852150844e00003842c50f400c0400400005402070000c5454141d9500b03060410302c03d8007555440c1d0b1025044284412800c1c0f802d1000b0640540500420481004808400301c400020b4000c9048007420011b4141c42d012021740400754001000d610030070031080b0034215a2860a40b0034031601003550000c500c503024007449001d4500001d8010f0704290340502130140505d915960410800c1110703445088031074a0b10188100100c1c0c0511804c03401411302000300b040184c3ca59011804100f07880e450b05000e5110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 949801537 1250 949800287 949800307
    0x60b0708120610020319110a060525080109020d02130312080c04051e06070b1303090b091e031005160e0d0507050d030306050d200d0b010b070201021507052a030d02 72
    0x824081c1400187c9001c1c20030710340301b80415030708202d120f03206280300c8000680c00d40e20380c200009008144013000030b03024001030112404030b80081850400c0711801500308452040741501c4008550b004585003226420320410b0030b81c2010040351301411182400e400e00303141001181800c41c29003240004200c10601c81e0f51660384010660342d049030014a141d0081c6032800200d020f840c0b80620503408582c005000007004000f250440e80e5000c0090411500940c1d0094440c0a601e403000302c0303035414080c0c1028000c07009001d11074648101e0f44120fa18418107142c0d100030340490700341d0760864000c0780c1016140700403480003d04c59080b0340701942c00f4989002a81801c8000340389a4000316400480000101c0610144070b010100c1c140100340d4199008000b00e00300312400989034402400400c007013004101d40700741c0310094521240180141e0f501402108900501484211000404a440490230784420f000c030745600390002c400840d08110b48403901c01c0c0c86940c0d00810884403540ca80010300030a503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 949802787 1250 949801537 949801547
    0x60604111b0f0703030906110a0c09050405100c0e010e1f14121e0108160504110408100203040b0f040b0c13080307031e0224040303060b0708120610020319 68
    0x324a081c065500c03d81d140e01d402000a107a1384101d40c0020040742c580b0035401401305100e0f008035800604034490620303108541c005484010270030342d040d0260310209190b0100038051142c886100d0744e5903403446213042e00094800d000c084d081e24041d8080c05882c002c920380c149140581d107030082c2011400315180f0803000d1010320071080c24405e0ba240000520180d50710388a04400070402d21102129941e0301c40a00e84e82d1020150001505078181c2c07407080015043c0399100101c087c2e40440014074040d00c482d000b030700e0140090b94000202d40e0000401c01806520201282c00825911260b03c0a007059107035410f004a014010140c10b6200160448240841e0001d00d40201745060550761165030504003c0d00342d202071444c61907a0440003a81034202e80c07000ca40c150450a030055070080110300e034005a000110f000b0b0048003815580c800207c0e54014400c040c003041885565240d41d1052541701801c03400001511441c002ca00081b07541c0e000d80d8000c02960300d54020914200c0100072898000c981c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 949804037 1250 949802787 949802803
    0x40b18061303050102040503011d0d1413080703021305040210050c1903080a0606020d02030a11070806040f031d0108010b030411040c020a050c240d06031b0503060604111b 75
    0x705414041c480003082040640190085500490007040034010100030850440c1c4450714095107604507441c102007840c061112256985111080c0901b05446400c00d0700100829400031a070952013040b0130011803070300020125031220715040601c50760401e903020510500c2d0384078941c002d0000208604107003c004000340d01030360000c55540172a041e014100940f50607000d88a50101c2410b107000070680500002e4400608201540107504e0045009030448000c1c42c07071000c0c0d800b5409450400101711038100913840c042e46c002c1024402200c1d0030300d00501003c443d00c03a188010001c01d400502e060380c0244210741119008100242c3eaa59280340c80111840e0004070558094170301850541d43d20ba000401c1c884040c46081150100e230100d00402c2800400002c2c802140c601c0a21103c0c10a075204c0080d00f42c2200103080820041e4aa55603001010036102d200010f03800d2000003082186030402089410480a9400300400c142c5c800700480984502c2082156100100007801e51140c010810b0f44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 949805287 1250 949804037 949804057
    0xa020f010c03020a1701030302070b07080417030405120601051f02010b030a0c050a060503060907030e12121e04050c0f010507022d1203160305160309060212040b1806 73
    0x401e01000010150007500300ba0364050002c0e9814011008034560b20b80041e0613660190024184240b52002581e00d079441890200c900c081c3c140800900d20390310031005040701540c60040e6890302e080c4428803543d8208010302030042d901610040090b625100704200ca8000003208466809802c134030160302602c80c24402541520901c1401d8040c03210b00c1d010001916805c036400c507500381c0c0d610340855080c0000c0da0082c0c0c0c000d5200004ca031040d80282d000820b9070064009940110291040584607034000e010002c035070104803000c102802a0510300c0040000c190140c0109a08054454554030b0381070000d9580110400305044140b070303015005031125194003e1561003101e81041461400c000042c0601000311040381e400300c158680b01c003101940100c0440210305180f0481c0d821000a620b890055003401010410a90b0611461607031034610b2780280c550042c40303450440001d245c10640c12001310084001d00007440317901001c0088960540b02070707a51501014a0f80000360561044071030b03503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 949806537 1250 949805287 949805291
    0xf050313050d0905270c130e010803030a1503440403170703080a18080c0610080610090e01060504141f05090a0507020109231908040b0a020f01 63
    0x50501aa8041071403810b880301074a409010a00107060041c3d211762645808100002c04c20009a0402e0b00300080c1c0122890503010745007280d03072900103041c0c03d80280c00806040c0c01c00410880c00901c10301407404101c0c00d162148a44a1850700e40300700602d69075101e10081d60308100240180048541d20352182e9040300001040404804402c201c1c2d54071500c800c03110380c82d201d00d0f0391070323501c078190183c601d404d406846040d078654600c10145e00030044039100c0c107500b4071611499000700e1491409801622900c00041005040066031300d8a100001d030701c55002d0fa03000c18108442401c544013880304441c0001e8001c112b000010000d50701600654000980040c608601040340c0c200902d6038078000c090149020148011a008582c0c0d18011030003501e40003502c003c081115180e00d948219030041d07661000040c40d0500d5500d02c8a9501c890701c400b404805441440c207409601405030b05030211044201340d0a200841d60340150078000c0b413160f00a4118081102c109480c001c1c080e18201c10026070003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 949807787 1250 949806537 949806553
    0xb070201063602160f080c06010f030b090c101101060e0f1008030309030909280507020c06030402100c1b0b0d1b0e100e0d1103120a0f05031305 63
    0x85010b0040c034058910300465a41004075256148500c210303510011001c108441e4015161285022045150011a61450f0402040101120031300429000e04138002440400d640346003400d00003460b01404c10041c580203942021500e03a91a5090480d1070080e0400752804004805850f005064541c81501c00c2e240d11010404034003406150030f40320f0720b05044034810700c60b294100703507580380800c4840203480d5000300071001c3c030352405045060303200e0000740d004207000701c3c0044c034880b501c0c0d5075003540d565480c1c0b2481441071858040c84100111241950310504620f0980c001854541c50703441450309011940188009000480d050030300443c03560561402e49950310004010304c0c2e40003000024031185007a401803401c00c40b00713103044512421a66995500c001030000c000003c0051714203031042c415044c0c606070050b201c00d044440358078001c4190f40311020000e01811300300312032200c0604548100f00603503904140c1082c10010b0301c0d10341d0314000707480342d40d0404041407400380c00b00041e144d4414410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 949809037 1250 949807787 949807829
    0xe0607020405040510140906061e040c032f04032618030c152a010e0304140103060b0304030e0d020a09051f0803160204110f0403060e0c06070b07020106 67
    0xc2c171000a45038001003006901d00c003024000170310900b41c4102c0c0c413a805c5500400c01c4e91401c041d1911003440c40c1002143c00c402900c00107000c039102c0036001004252258101e60039840c43c4044200090701a0700070902403c3d40c1d003c03006c000d00c05c0340802090600030580b01e041410240e1040042210385000c950303640d074007107015001008520b0003c203200f4031680311400124203009005901094500d50410705210b1149142401345002450b1074001010144486603c142c2c01d0040300208450b06016580d600e040884004404891213010340c14141010000c1000b9001d800071a64441d4241c41d0590300c1406010008024041c545006548001c2070b40c0080790740c490030340c82503001d11121301c04070f103640f030f5101d80000c4d202030b85214080040d0414003600280d024482140911644018000030704402c0e07101415071582c0205034514250b020105083c0200f1819100d000b5442c0214001000442d04400015a40c0e12800400410306040721000c01e410038003d40100c805003425605450402050b01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 949810287 1250 949809037 949809043
    0x6020d21061e080106050915032e050a050705070807031205040809120c01050d15050d051513050304051302070b040501021903060f210501060602160905070e010e06070204050405 78
    0x4202c19019911a0b00c0010785540144102011600081c0189240b07039541541c3c1785551401e03400d11038050260200815100009808494402080070b100075210300d95041034100321040184a101024948420f1058160f0408280d80d400d03a40140302d1565052145011900d81041e046580b1105042209200401801b84007034110084180c8520304494111a4810b0707450048440e5240400d80c2007160500042103600800c81c4100380300600c9501c0350f610404920780d059a50020742d415003207081d400041040c0d501c0c90039004030025218168802d86500d520780c42e8840c038800c1521404d10b00c500c0d21250705c1d25406071058a40c00c070444207040c1c41d217410702e10b020f5404640341e40301d03181009603488078150081c82860152360030410b24001d400d080042706450008012214031040040384002c400040f000d00803003010b810164050103c26040408034081681d658000c000380c5400c14040003451903000400c400700510900e8507041454041000c10040d02c18003002075005410070040005100c000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 949811537 1250 949810287 949810319
    0x11010b21210d0c08040c0e10170706030605150a030b1f090503010b1804081b1902100507050c091906060504050f0603010609060806040b041407080903030106020d2106 73
    0x1011041c80755401c0f0701000c4945000865009040c07218588090140390015401240c0c01600810705400482d2030360030b400c5404405048000166008110901a80c1d5150242070000c24003562401c3c002c02c006e15622220b40500100c681c2015900c3d40c04007a160b880300035000304002c0c415494800250b000c407006007200c40d04e020b014041d60030721107002903d060a4803842d003604141c032800044c035101c0d562000000d61049528034000c61101046000c1030070706001e212100810320050a02070035041c0f0511201c07909080782a01400824820f94000c9800480e80724040802210b0324180e554401d04000254074a941c148614507240ca240881c10b11380000c01841610011240180caa002d50003c010641c8401d000c0c0800140310740c0006c128150103210b1058000c01d00810128440c60500086002c50340081c4910090013008400d000000c3e030403262603a00040c2c81c4c1d0286203950b050440187d40ca401d8846100d04201d01036411100c6480c4010900140c800060300a01000ba5a91202004980740c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 949812787 1250 949811537 949811557
    0x10c0c060c0b06060c100e070521010c0302031e07021002040603020a110106050607021c0204050c04170d080c0705030c0d110d020703050a020f0d0c030501050711010b2121 75
    0x202c6804039040d49481c030305841c40902d201008124003101e440c0f0f008081c3c58040031440c005d1054403c049105d03510390680503081c1c2e0080440102045072041e5803400d40707940c4c0400e81c0c11f01d44100305000001e210171101e0840c0c00410038a6208648940c2170481c0784c10000908080c0280c80402c000c61f501340c0c5a0001c020810703040e52240b0300c01003180c14040c201c41c1d09104550740402c00300040c60050800c0e1003401e08007a9028040344040c2c8051300401e0075070710f00302d07443c00c002c45002800f03206411441401005440002004010506003c40041c05844014281c1c141c1a000803131140200481001182c190b0300c815004c4d40c1c140c0503400e0000e8614607140304840c2560140b80920503041c1e01c00a1800d045070740180040c140056982c09121014060381c0f105604001e0828800010400d08081c0100a5100d5800001e2600c3c104100400740084900080da9030b0b41003d015258580c0c8421409540c074850340a070400e540346d034420a07841e20402d036280030781014200415106c01001500500801c0074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 949814037 1250 949812787 949812803
    0x901050d05040524130b07050f0706050402010311070f020f0f030109050c0139020f03060723040b0706020c03130825081b150f04050f0d050615010c0c060c 68
    0x844040c04c050040c40448001440600144044001c550b001c1d4803150880801e05045181c001c0c0010030001d26404250b050310780544034030610045503418441d81c00740d8009408194240000c0b135840814170100490064810b20494003040c13510741c3c480030050341d104001402004005294a0165194443e141071940416100d01d0660000d680244803100c401c0b40e8003043c14035891901202c12525100407400743d810020082c03502e0324a4400b081542d000701c0c00c83d1500710401201f040300e411034003001d40c002045a08288810442d20604409031146a07078011030242e181c1d00d060030490b2950244c244508110144000000346c1010042801c1c5591103c180d105400001e100740300d12040e060500c1201e00543c45007420b080c0d00d410300c40d05600403100050449c1c03178a1964000c3c1004035084040b0360100400f0024007003141e4541007100c0d60308800c0079541c3e101d55480c030340c640d01d032128001000310759420900d10003841070780e101c1c81d00c00d0000ea42c003220303c080c034a440c1d2400601601c40743c0d2040320406 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 949815287 1250 949814037 949814083
    0x60f19150519110709110309010507140904270308010801150f030b060111070b0c070807150815060406030c020c010c02060f18060a11060109021606020901050d050405 73
    0x510500032a40440b07124082c09481d94425802110910301c0c80c03d58031140e00a82c60042222003e602401c1462520441d840741c507400c00d00003081c00c660001d0221014042407216500d142c1117094117a441c200021900003921540c07050300d01c1840c01501d103010041c0303034aa5008000b0903401900150581c3e03912030007042620210544480c044105000c0c5000d0b8001c403a0040002824424646501c034406240040000185d54420307450800c0b00d422420072508007042e5a810464100201c0c0300030640803004000283ca0802c2c000341c402c110001d01d104005040001640c5140031000c2e4024050000e0701c11941c0d10364030f0100400400d4049031503001401110000c011380d40c86880084500c3d40c00810302d41c80c00c030750705182c8400c0307920003000150140038400c209510703a07840c400903202c002501d40ba10013a0300d52001d0450704004050308507442139481849405d001d200300c1c840000840c0c0c1c0c82035005a8958000d40180d420340a048413001d401c90400b0100f00422402061015151402c854094251 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 949816537 1250 949815287 949815329
    0x903020d0e030304050402090f092e0308163008010b0a020726070e041a091b010c05030d061a07080313060608030a090305071202060909060f19 63
    0x303041d00c694107034024001030000340340550090002250040244500580d107402049030f0319001c4070307030340c5401c085004030a82043c0140e80c140010020410020200350840e66100024007401c1c40d104104071001d4001401c210100c1140c850030b0b0303412142500355805070000009080c10821900c00002c0daa14000074000d00d00000741caa100c48507070040e0500505040182c00101402c18241401e40c903e03044001111205000c103101506094035009010720f02030400d420000c420b0b0f4101e400740038910081203680d4201086980b011100c0501880260015900407908a2049080500302d40000945040322030301c42d44c41242110071002002c0c92081d161407100880d1700030401d014040700410800a00600d0300001540303031592089c01c0004a00c1d03220310b002751841d004500080302084102078140203105040080c600202002032507201d980400d640480c02d540590b200c10740c00f40d070030880401d0301640c900468104c100b0007d01242050000c034010165102d078ac5200300c49080b40c515981a42c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 949817787 1250 949816537 949816547
    0x306150e0c0903100b010c0b100909110415050102061303120c02030702181306020702060d180b010806070c080331020f0603010b271522030c0603020a0903080d0903020d 74
    0x17a41e14141c4800060942c40d0b02c801c00d461400402070b0400303051006001c00c40d000c0c0e9100700380321580106090119040080240812035aa000a00c40c3e0b00c0503a1000b0040d90383d0000e402d690051a16807260303150b159910f81a20382c04850500132044904161400c0c0c1c20540c000b029000c000d000301c0f03090035103100020607501c0381c02c01583c240100d8a060746d8510301141c0c0d140c00616080f803002d00f0941c40c2c4002c03008001c0c00c491036400d507904200e4030b171800c1c2000d200e40c42e10241e01608010003d424141030000b805041c980711038a006007a00000700020760210148905400412807603103c040d15541c03030070440d0784d0503000028201c0c4140e8007120740210b42e003059410380e41030300d21003441185006148030600845041076450000c403101402c8815002e61101840b500c03100d02e81407034071174880ca02c0a5983e5400323080401c0400495079035510410124000d0340d80942183ca00d410016610008000304035417010490f0005040c901000451000243d441e5002c207049900035420b484103840450b02c00c40b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 949819037 1250 949817787 949817801
    0x102210601031103071b0803040507030c140901030204090615061e0503061318170711010318030315030b041b050909100f060e1608060d0c0306150e0c090310 69
    0x140283c82400000c600c41c0c01007502c2d06100c00800d942584106050b51103038a140d108031030489860300004010000c00468085100140480001d030040d806101d00103d8042141480068403490301c0f04000c0003802201d921510110f00b40d82c0c2c01f0700409480c0d80001d030079a01100342028806080e0780301d01a06174469400c2e02e016402c010103040f004501c881c00070015188100e030403180741c484009c0d04400141c0260810401400e480d0394103480c0e600d62b040840703001070340c041c0442c1414202840460003542006038099541d6060500151030003001c180b00b40d540800780c000400c03000d4080180418030040c1c0e000d00701100212078001c0c4003540ca032010f2000c001400c0c0c13081d041a9010b9648403a20548540100c1002e820300e50b0001911540e940b142010040262902c85032050425280c281c003030b6010300f0090348840161603a100079030580d9507050f02103119100140500da42c8141c185200c1c07042c100c2c401c00411030441d494507a804c2c021125621075004800107032003071107401c1548441c0601e80c06195 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 949820143 1106 949819037 949819061
    0xd120201150e01031104050919060b0604180516020307170d1d0d0e0d11030f0307120f020d0903060b0a03080a030b040f2a02010e010221060103 63
    0x100350750440c01158046c2d402c00c8100b1510f00c0340050002000d80044840c22110b210a08000f001010b0044100d94009000100020b03841840a80c2d0040020080c000300080e854544c9442c1060048156100c0540c2051182c0d2000c150500710b800415001010040e1030f00140100e85012201a050042c010136604482c0102942d42000103c40401450820000f52156540001d000d0700103100002c02c400360101401c9541d84003800250764004015080325294010f902d84111400f4084248000282c04404940c602a100140054101442d601c5008150b8150b89828020307116250300c03a0f0304100386540000c0010030003801060004047e03030340003800c042d40c2810030007951076003a03404402a042c21200c20405c0c0381409105c400f4440c56988080309107401c003090f4050703c05090490030319440031a056181d030500038051540f1360280d828000243d650300c2c005408540c1c041c1452 = true := by decide +kernel

theorem cover : BRFrame.Cov 949640287 949820143 := by
  have h0 := BRFrame.cov_init 949640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 949640287 ≤ n) (h2 : n < 949820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
