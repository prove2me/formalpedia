-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3701
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:25:59.46217+00:00
-- url     : https://prove2.me/submissions/0ba16c7c-8bc7-418d-9697-e75211d5c62b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 665467625 ≤ n < 665647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 665468875 1250 665467625 665467637
    0xc0c110109031401060302040e1b131d1606020f0a06200313020f0d080306040c030e011107050c03030703050307030b011b030503090c011b230105101e0612020a 70
    0xb01e84a01c0d10300c010840c003140c0786a5552208008504044c01034106c42c0c80746101410500c0d064a40c030305511949548030030311038910042c00000c0308006500801c10402d40c10581d003614a17032050203658490003241190606004d00500244040c80041c0c0000302007880006001383d01070f1580d4143c0035114007440d031101d100d882e000205040d100b20010314803918090b00300441040d01e900610591001a1800714050b40700302c142040030601020880340c020005850004d24280d401204400428150401c08030650038588210680009900640101c0380a103050b42d080415031020140d481c41f9540c4003d010800038000254054001d80c44031001c040e041c1400b564100750810359080e0307030340f1564003100032600110034000d40c0c2a0420a40d20070740420b0030109864080020b0a13600c4980380100144092590641e20340302a11042c200355035220024001c1c0300a00344402d41402d250391502030110400061a00e80c45c44043d100d07000030480c1c205498a001601e2103414403c060b501001d111414010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 665470125 1250 665468875 665468879
    0x901060f0e061305090a06050901060b03070c05160906080606030309030a140712080414010804080d1a040609050f0c1303030804140708010b040c0c020f0121020d0506090a0c0c110109 80
    0x440d0240921414500d400b8003681318803487d00004840b0060600b2005070714041050050b410300301700b147c0d002121810301c00d008034007918256241408403800701850713105418000911780c000da0886015202600280c0700c260351560185036881c00340300d0032543d02da4002d042007404140d41e00c0d640103100c0d20980c2a00c0084c0c0e03e820703054a10f403001420440314400d000070100301d0a0806205807519280074a0084a43d08040d22084110f0003101c144e515090341d59000311100c1600b445a45905e514048c0c010310605550354943c2e80200400c80d4502c084071100c0000944600e44841150070444640c0a01c6003424117540381121003a100a03c126186100300c1c0580d04404c2040100c00c005119040011030086050400d11082c0d40043d0291014080c072241c0a00042c2d0300c1c4442c82c010080e080c0b80905d50001490300100140364206041d00d8101e1000844103483c0310702e9040b00d4444c0909840320219601c0e203502010444481e001074400086076400240002844a410501451414901154400c2d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 665471375 1250 665470125 665470159
    0x90b0607050a0302100e0114010306020d0b0306190606020307031d011b0c03030e1507080d0b0a0810050601050702091612060e1e07050f0a1b08070b0901060f0e06 71
    0x8186a40c160050b038817035a424280c2c01a02e004000651100b103000b401640300c0c50240c0c0741090700602000380340d00d801146d24085407090764410410310381c0003000c4801600301081d0704038410300401100441d01d428540b01280050001007215a043c3d4540e80e542540e581a00a0403e102c81c041001e0703040042c6152a000071110045544013001c2c0184000322180703140d45400342c0030042484065018103845400344101c40580d000360b031740b400d030444900c1d44c0d2404c03121841070003840383c0e0005950003144814041a15503002501c01c880317a034130400070001d0f62100e400541d00d03805049002580105c599000603904000599074420a95503030511700d03c0c2e180017809041c107640182c0c01840458665104000c00c9d000d05194244074500103411707407081d41c04c1049006125100f0403007580c0900400050200c1301e1807003000100c901c0c40c01012149100d42003880d1240392175000368425140c8a0407400070480044062040c14110f81100604a942c18a0000c00c0b020042c2c0044c0029400300f684c698191001c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 665472625 1250 665471375 665471383
    0xa051917071101050106030b0102120904060b0c0f1519090c030209130507051219080d050a050a0b0a06021906140c0c12090109030f05010e010e07050a090e0304090b060705 75
    0x70600741d100c00d105440c000d2482030840300140e1080c800c1505010f000c801e039076008140018940041201240d40346005408600030380510b500c41d0f201c144d0b0008000d02d1071071004c5071580781c0051110030780c0c07a50071091030956001481a140609403072074180031020441050703409110700a1140602228160b034130303000202c401400722001c9030904501003000c0104141401090041d0104a070322540c005c0d41c2d10344142d038494000020a0040070380747e040e030703080c40b44203c1a144020031041c0c06105516041c180c90001c2d02041d100401d00a003008403e00c51403800c805188181d030490b030300420700310b0305070100310685144038002616981d584400800c031403841113115600c25032010405035518080110502d18180c404041c01c407541800740844849a80e00c045004106e03900002d42c0c40210f032190424900504481406801030741c0b070500c0e002803102000c01c0200032200201c40c9015443d90326070441c026074001160010468204120500031452268004011204050100307400c03c1340507904c0d6894 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 665473875 1250 665472625 665472631
    0x417180307080d0e04090f0b090307060f0605010e0303030618060f0d1b0512060f0a1d010b0f1203160503090a0e010e15030c090a150b0904050c0a051917 67
    0x1a00044402d0521a42021000341307844000d5408100ca640c136500d4044d266049032a005050700c94500124100a04c100b003601c6080e90400003c1101c140302d403026000030080d621842c2d002c1604440f1042e00c80c60302100340e921903100502494040d000c40303075081c030450074000c4c070460384090480b00000541e15607400d50f44509114481c0c0344007000521503072860715505036122503c030b2818640c0706001c4d040049034041e00526030001c4030040791100c10000d0081c02c005482c154129852604000400c44d05403c5281e03540e0b42665141441c2d088401401007402e03902c0070444207640204008452402c843c80c010440e1809002504c1c00e1502c1100011480c1207a507000888403045800140103100c450b0718011b8010200c250b140c1104400c05005c00d0310f41c02c072a1251072040c0c1d0b4800016001603803541101c100f036440c0360040d250440d1200c2c00541e0070740001c8660341c0150300e408000b0364100304200c21141c01c16040c9d101d65040c040000090449005903480740300030080c04c2c000028610484084581c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 665475125 1250 665473875 665473889
    0x3031e031e0e060105040203160e0d0602031e01050f0a0611160305060108060c1303020607060f1d0f010b0a05090702030c060a0905010e0a0b0106050f121602150417180307 75
    0x400808102c4031616002c01a007106100340d2040003800710610100e26821106032441c1000c071007120240c400039010b0041c100c0d02820541c000404c03c1014010454007685840e0700744511212640c950040c451000220350b0a180c010301549000c2c0310050044010501e21170390007040b03c000e030400f440101c40000443d07008a0701c0b9401080144043e17542800340542c41000ca00f200ca04007602d040718004500c0300b6200187c001c0c1400160101444503580110b0700489076800d060010024804a1800d02c0d421a004451b1900070b07600e80c146803000c18010052102d4008003981c0f400b5081204010000d98040c054000703511003040201d05a19082c0032651280b010400005085210f40c10b00509584641e84070305101e41240c1102c0000894250f8078506650b040c1c0f81c80340e00c0c0c100640d0030300c0d0f09200e0b07001960482c0706440104081d0021880f80b003011452590b003914811068200d1480c00107800707860040107624200c03103040b00041d04030041c151b686403001d0320044070013152012a042c03054903002a1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 665476375 1250 665475125 665475131
    0x10b1e0408100518030c030a120902040c11150f040227090c100f02100c0c02030609030306012606010e06070f0b0402040c141903060f170d0903031e031e 67
    0x1141c0c070403004d4502ca14074000310240d89030500c1d00000301d88a1159010074400e002c103010040d09000d011b94030002150368094400c01142100703440181022080078010700103840f440c8100d400f410b0100e4009070240c001403000003080e4442c0d50811004111f044a034007400c800380600c1c90703044210304e40f026002d020850003400c412004507007800781c002c5490421006022120320180305035030f0f002400b80c1c00c0c04141c0b41c00150500009004807010390700c001001c0e41c5441110184881c01c6800f10003103020700700c01d890700c45e1607100b8003800c00102140c00303900700342440500000440c154000c03e01c40c82c42d400001d0855203071151aa1743c0c11040c1c00c1e00a402d40c1d180c580d031030411045040600c01d244001c2c0382401c0454840e0383c035201c4200c2d00d210301050f404504c0201014081d42d10301035080075002c0d04036611134000054541e07100150450003001c6000c0a4414010703004602401915900306480e0541c0d9070005155101c0e0001540042d2183e8041c01c0690300c2c0d840181100f400040e06480c54182c0d0008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 665477625 1250 665476375 665476381
    0x602070804030c0e0f1501200f010b04050105011133090a0317091f0609110c010c0c08071412030a14340203040b0a0903020315010b1e04081005 63
    0x1018102001445d10586007002018000300704480108510b6012091a103a0b8081603010900d06100301403102c50074540c4a13440100d059407606402c08212a1405d4030100010380ea990011244400e1700c80e01c1807201c0c2c004116034000c00241a20180d54540300400c02d864801c004016000c003c1400c0754402802d400100010041550001d40c5c50764500842810710800c0c00c2c1003880c640c81c0c0322084c0d040c050901182d0381c1c0c00300980582d04034400500061408021284034000e170b140b1240e0144c04080c1c0194604100b040354940241c030104000b40d008411142030020580ea5a4201c00c400c9400d01e07003a101c1d0a04801c0c454140342d00541c480d070051b0300701040c01802c540303424141d928040d141e041c0c140c3d01410000e182c2c4582d105103035407000c100394403000d50300c0c60700200768190b2042e03400c04005020300041c1440c90581011a10341100e03c01c2d000c942d26001c1c07807840400c0e18a020300802e940300301c0810199800744505181000c10000c0c880c2c20307519007540e42c0304452070101d8802c1c941035582c6c0c444e810 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 665478875 1250 665477625 665477639
    0xf031606050a09050d12110c0a03020d110c06070f02040626030c06130c23271506040e040b0603280303020d14040605040b15010e04090602070804030c 66
    0x18541c2c01004500d07041c0b10512069581c82d4640480754040300c100304041c0041e80e0250f580340c000144404a80b019182e0321050101b03010f48032020b204040e805072141982c0000101c1c031403000d102c80070300da00c0098819040d0750001c004865115420944610481066a00c00b5a45070300c9044c009150303901000703080003040c01800040300c2d0b16411040395500103000e1007850300c1c00810030f580c0c05441e01a80b1b174151826880c1c054042c0800e500006ca0030100e241c038031a00c90b1102d425646000608030340d880300c28450f01ca1100031000219200002c3e9014106c040f0380070707000604001c1c201c180000c24290800c6e0715a6035000d21524211070565040e43c1660900420f8101071025402030300044100b0001705503406240241c40ca003a100090406900003100da8510b44245e2100700d1340028040c0c451a030381070906041c07018007400e03101603541d06140c1c0003240001c807661028825240d0181c46265007040c09208000007086249415a1800e8080100b44000b41c0c0c00030040020303620a4207213034485428802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 665480125 1250 665478875 665478881
    0xc03080c19080a061203080406020703050408060a0e010f0612031101060911031b04060c0b04020a0306182f04050405011107030f02010506010306051c03031e0b01030b0604030b180f031606 82
    0xc42045c601480c0600200400da20041041e4000e4000350702699440d81450111030070300c900e5002d42d42a005000500050046d15000301c108540703204020300c82d201c0c9001d4054202c0d00ca5104542800110420001c0002d02405031005212803420000802d5030b9100c0424080e145680d4120556102c0001002800b09a10200001d061714080c0018213007418406c01405121000d940644460240c000150456a8401c641030145030300403c00e101d0036090190350b0400c21a00901200c04d5500702c02c221050b55403a49004e90351901e40c0402c0d6491000b01c80c244001840d0207041a0341d29500d4600a065100f03d042c001c000c610f200365208000005203000003401c4960140c222070400d03080c61810003050b500e0485050048548440703140e01e00051f071500341c00510700030071444110f049034071030801d528001d503029405482c004e032802c0c04446c1803801001751600c42c900004210045100101d440c803400c03448030311025500d00b130458400c1d20b50020f51524680105603204070f01040c1c0c1d00301d94104403880c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 665481375 1250 665480125 665480129
    0x60f0402040603060609170607050f090a0b07060509061501050a09090c05072f0f0f15180402070f0803100f0834050906210d0e100c03080c19080a06 65
    0x103000740c0451f0804502c0c650f15140040c00c2a0204000490700341c0c10f003580c40044a84800300200700c030386ea81ea42c03000046165084504141c421074500000100d805501040c414450316490003d010400c0000f401501c16401010a0900f0040d0541c4007040c082c6440c85002001c500c10307100c00351619114a440c4c3c0400240c8000301c4132a40c2241c03440f610401c88004a0500c2d01001c59082c0c07103407605000400d080400061445034085a841c00180e1402407a0300104650441c450091484081810900043e8850118005c20044c2c07913001c0d40d004100c400010b95005150a1050340000369034244601101c0c0c1c054200c0c51003904124002d41180c101c00c0501c0d10540070010400107880341c0300481201480c164400e6501401c0080300181841d81c0d800300464400aa2489481c40000ea090845540e40c0b0301d11011004281c15803075078121803811741001c04014101c0d689070380a401c4141e900700c07514800600015803100080c05813004c1105d402584440021701071b903030668146840701c0328000707440c015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 665482625 1250 665481375 665481389
    0x10170907050f06071110050c01050f070f0207060e1e030a06020a021b03061b0408070b07120e06030103060e01021614061f1e0321140f04030209060f0402040603060609 73
    0x204101c0001a05038280f01041c5c1008485200d00d400d481101034401e0b205003070001110354070781000c106415041350745007801040b5655610280c2140703120140c1ea20262809881c0204840448440903464000e9503508096200c80d101c1d1903145100c0f0100f450901603090480300a50003040003640e10390b0410081000b070802c408044801c050078004203444400c0600501002e800004180c07c0c0305181c441124002c1ca060800c17607216582c2c9500c240e003c1c2c0c01424007200d690324900000d290980c41881c82c44494400100150310703507484c40d55500020101a00040780c00c0d5020312091842134654208410440d006044518500000c401031a041c080e0007043d48041e14164042e4080c1c10f070b604210341040e0303040c40055a6104030640c510350220196540300a094030034508035840c01d5201c1440d0701c442602c243d21140d00740c083c004031400c0c83d070150b400d0800748060240700c20405440e00415198100001901d886008101000854146e03030044d0810030119440308800c105441d4040e6400c0000c00f00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 665483875 1250 665482625 665482627
    0xa06060b1809160509030c10020307050105010e06010e1c0f0b18011a120f0307050d0f081504051504061e080c1c0804121a0c120610170907050f06 64
    0x31540181411400f888451000c1080124901003591020840c0e4280c9800050403000c40c0101014003d40da684401e40480e1513500340030001840300c4909000d98000c02050315004c881d03d0b074502c03c0c09050200a103a04035103680811040d0042840c980c03203103e415014101c1c440040c608003107614401c076496107200703009070715004100000b05007499060903104001c403000300f410404202054074041080103024040d0100040c3c0804204c40003803801060103142d11085001900801c003918010021100d080541c1c46245042101c8d2130152b0200307600034003128040c200310801e40d0104049846980102c03025080758000b402c1190350301d9035400e0013052210001c0c500c25047c1d001080d5240b0105070a926a034103101080c40400090f8815503028104040480783d402c5961b0404403081c240920101101e0070f6400003040790030701c0400803034603100151610300c90152500424030850840d801c1040d002c00403401c2d401544504c207420018052140b8000801c1e060703007040e040262205440d6240c2e481900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 665485125 1250 665483875 665483881
    0xf060f030612320114070206010e090d030c17090d0e0312040b0a021c051e07030215090321010305010c1809020f1201030302150c040b09040e0a06060b1809 68
    0xc604524001d070615220020800e04081883c5042a80e5041034071011550034a5000b400d0b05500c504038a116140325401c6848599941460301c0d0540c009617050007a82c2c0008000456950007034001400384c2c01185007c046007920740a030400d403168103032441081d40d0400d0b03000410042e40496603081a100850142840402c400680030441c07040c0e100c1e0151407900400c801d849a8001e004100508a211441e90100307116084010402c0c1d102006060852000000d8820300f20110010f031201d1a40c507030010410461282405040f140340203001501c1d07440b040007103610b444d820030000300c1c41000742c044907440e035411031410500b9254800701d20360400403c1090185001514429042110f6040314016914060420903403154440d0103a006054400d4500000c1019800a903000d1000c51801000307015468a6038201040c1c0324a110f0099031a4040c03089034403a01e003541c0104140c0c0d40074002c55802100c140d07908000c2c1c074400e40c401480c4420100d042120500319100300d084280040311800818a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 665486375 1250 665485125 665485133
    0x31b03030a12090c0f1701090b0a09020406180e0606030a0f03080406110711030c0d0809010e061c0605100219030e0121062c01030b100f060f030612 65
    0x20140030140c80411246611072001e000b0180d0001c100140c00c01e190f200441c1d1540c1c0080004000c512034102c40204503020180d042d10184515004a07512601440c0c95885010704240980440030069038407903901c6030005000380340c6212840c24440307000008a08079010701941810110000d20b0705000b038000011200010700f6a140c40074115505040c41c0900c1e07151030404000070000d40070401107803900000d0103000c0c402c243c1180d0310804021002ca0f12034001d00b40620882c07500703450005011100038044103045600410f0400001e041c040c100314108080b078030a1040405040b2044101940c1d0b40f0000d000314289408400c0215140380010103218040300d14881a003644c19201404100d0091a80700c940e80c400c0d8040500d844840c03240e4008140d040d55550300030945407085991311250491410702404141041c55204c1d40400701280ea41e078070310b86400071020002008409840d02202000c136148003a210460060421581d806000309445c0101804680c010b42003022090b015148090000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 665487625 1250 665486375 665486377
    0x50702011a09010e0910050103080702090a0c08010509061201021c05070c0c0e070905060a12062c070c05030a020109020f12032b020a081b032a0702150702031b0303 72
    0x190181a12802960307100391145041c1071050004c01b100c1e6060200001c14010034101602d070b201e000b01c5001c0d43c5030301c4000541080305e03c198800310208180b200100a54076000c1ca01603484140a011000301c8940c518803d42280d014041409004809501080301c5004078071945602c041a410021200081502c2e81c1c500354203d84504849180e450f1b00013880580701d400d0110007807a025048507196143e056015010b001e0034084402d1440c60804002003507404940480a50b40650410f0b0804910304203124050413030050141c001d00c48602a104000391040000f401c6000c00c59000241e07101c1d0320701c100403001d41c0181d656840381c0111021202035130340120885000100321403241c503400407129100b11b2280c104621640001d4408102401001c4c2c0010700d580c030900c0311254141c0101040c084c0900745001c10349140c48055842104003010176021081c4079000c42000d64001d08ac25010760000d490810340114038902650f010942108509041120008030f00703113090000001c809c510040390352 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 665488875 1250 665487625 665487629
    0x100e0c090f13030e09041a07031a01050d06171605010e0a060e031203010f1a04031101050307030b0d03090e092a0d2001140313060e1906050702011a0901 67
    0x70241c1d910103510030140901d03c1080c1100c1c1c05401d900c042d11b0281030140642c0340001c03900202c406000700094910748a48a030940044840c02d00a40e8a000d160045405800490300c441032195240703400303d08040c01c80400c4200b500301400800115801c8140444056504d80c4542c0c1885030700d8803035a40d169a011142c40544131180303050440d0002c108006860404074082c5c05079109000030020844410b103601c0c9405903052070902d851103040340c4503a1041c41c4542d00c8090702c10001ca981d10141d640c8035500454000e94545804903203a80001c0000307070219210b40b001c0303010418954080080701c104814140d40000254054014071781c1365843e0340c2840c000841807134040c11103a20070011550b1051008040300f904a4007400c0c81510810301c680e502e9906103441d5020489460408004a5144007240e01c95240d1400e0001125016540c04d409000d04008040381401011211049a01c0c0f1400052140703020310b50100f42030500502c06800c490360f2a41441c02d005c1801c86198013900d43c9540181 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 665490125 1250 665488875 665488891
    0xb0906060f07061119050304080d0b0109090204080a0b070c020a03020f030a080301090606140a020c010c02040209040906200414060705070e040c0f0e25030b03100e0c090f 75
    0x40c1d103400140880318a40b059060040199180540d541d0702c2c103e403503001c0c0289401c40c0b03c0d41001d1070030100c800d03030f140d0201321002070000d841003001400b44c40c06600705480c03e81e41070500403da00e40301c1001400340d1304240c0010b00140d02c00d100c60b505200e040c83d01d06421040b00d040003e8803034440d2700803071619403c0340800703406a0341101c0c1c100c0300350320200401c032441600089010f1312561038080b17500c00341140d441b43c680000c0740700d1000b9000016442c111500b90b080b50b001010200000c41c01564500007102050307074800d07401c0c030560605131514014503c14a02c0f82c480050303141d40d00c0d908210000741a4521510030a000d1000380100f05940260116082080315401e444003618a403080c504049504500d0003440310300700340420400044520700c143d6503049240c07040c0903112825010003003400c81d10300b0403400540d0915100c0c41c815200d000743d5200545400f1401205d51404686014449030345030501c55525664409041e01c14000c100d1519000c032101c0c200742c00e18200c00e010300b0f0b40151200c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 665491375 1250 665490125 665490127
    0x90607020919020f040f05030c0a0e1e040b06091f0603240b0315040b090c1c060f08150601081f03020a06030207050607030b030709020f0d090507080f010b090606 71
    0x3507950085280110081d10103000b043d5913a1422004400300c07174105204203031903c40505408a090320700811500342250020f08401001441c05110124904004c0c3c4030040d108440d420910080c10000c1001e4070a6001d5007040f0014280342003401121640203280569054240f000d00500c400406250001c40740c85180c04102e9080480701c580d01900d0306402c080e03050841d120001203813800b03000034510401c24580c200020034500c400380029280319400c0c20780c0c001100c1000a011a0025004e0002c08a00b0402800300003130360303e08202221019046005036040300401040051400c200170031440c000a410015076040910000e4014500904104000c81502d0080302c40401214074000041d500240a024250366402d030181c02544440c0096a060142800180710309000b402a58040440580140107092070004008025003012468030307491002040007600b401c0007405800f840745d015a01810083e803070301405a01d80000218605a0340e41440c825241558450b80030550140c42070b90750f1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 665492625 1250 665491375 665491381
    0xf0106050a03021902010e07060302090d0209150d03031b0c050c01030c1e0f0306050d1505090f0a0c0519150e13020d0506190b0702060c0a140f010f020906070209 71
    0x40d0080d001d501e41c84d508a801e40c00340b03160030943c1504074002d801c2000c4107a400d00c0d43c07242412005d030f11640c005550030028003003117480141010300c0700302d5002000e101e031b0001508a0b500010300421503000c040d400a43c40b12241010b841311050900c034100043e040403010141c0a5440d11b840e214500b2070345041c1582c03442405a800e000e940c2c1c0c0140c00000b4502c0000001000c10040c040007402c02890001a1420f60045860708001d0740035441c00307400030140071000003043c0034000607140040c40b1185074023585d8500503140320b0820030740c00d44501c07500038910610b081a003401040e104c202003108584070240c0c41006105204820004130907078500e8156004074071800480c41003c0c8144059034003a100040000385d00311325920182c040e43c0100e62552000d1440841401e444805003d481482c0c507082180c0c00051402900070103544581300d0550380c9428075a11000c0115035000341c4c03035105030403105070380f07524941c00e21071040881e803031110450070200b610000c074100b4010071400900505c01c00000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 665493875 1250 665492625 665492627
    0xd08010501020102250c080328030e1005040c08030a020f06060102060f041707170a120b030c061303050316060e060118051e18150c0712141803060603060f0106050a 72
    0x1610152503c0780c22695600b50310074049e80c41c6049078145400d005030448641804900c6402650040b407001c100030b103040c2090204242c000d140281c411941c00f021039100264aa1062001d4039059807107030040c15014225881d1681880001000c030350441d04000100329094070f032906400c2c0c22541001c4007110f645c2c10101e198040c0d120309180a01101c440401c02441e03041140000e0031080304035686e20302e84030524480041a111000c1c400c5a0682002c903810700d0742d081040c06413902d01d01c007105c800c24203a030b207458903070035a88401da003c203818400340000c100340006406501007020841d4003e0007603605d4003542c0c0340c0c840b00c405c0c0100c0750503071100c0c0401d5903610b188215a000001242c003000309800c02c840f5902c04219034940c012950f0060350b0122101d9460030000d1340c85150640d06540c40e1116030303641c1c002d00f0500c0312500c9090214000c3d600c0100510b02028003c10040110715030a4034000070100352501d400113000c240320354401d108200064261048140c11102603003000c60f241c0f102514 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 665495125 1250 665493875 665493893
    0xc030f130317040c0501020d03060f0b09180114010810030803060f010201020c1c27050105091804151a10050a021e011512032118050d0801050102010225 67
    0x10102e4044440c028081440000700c07a0310f04480c0240c080f5809012680800c1c0c090356468840d1001c031105001040200526400c000c240c0c492006202c014851000058805603620a0300806904807001420310003958006c80907a800c05400580780d0100d624680d80c10003a440024039450140d1032640302800664002d406450000d04200183d41040307030103120f14000b035840302c4001301c0080c0d031140b207018134021a071241925604c1c841100c2c4e0f282900b020010340e050360005120365048103c100300d04142083e02c0711103d00542c811207406440040c2400401c06907154600c0f00344014905400b0001141d03500411a00380d001541016a10307001016001d82c24500d01c000315030050381c01c6591084403040c040d4481d03403500054042039440d442c0c545101e0b070662039114000801107202c00401c0c52084440340304030040c0d903410b40400308400007900c0320211110742c1004201d40036032001d082d036185190403400e5180036220a100860400910b547c0c0100e5104d50404d94013180f230314042da0070041c001424 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 665496375 1250 665495125 665495147
    0x30405190b031303030f0c0207030f0201090305030a090614031501031116081902010606051b010b060a05270a09050a0f0e0303090c060a090e06040603050f03090102060c030f1303 78
    0x1441050b203e00c0c0c10420744030910b00d40c0d007040380000e00d0081c00d01c071401001d12501c0c14502c016401407505078115600d58003c0c0f0960341c0240c2c10300c02d20290003c001042080244400b0007a9a10410100e1820b04003420030041000c0c102742900091040101c869440048444801424a80403615141ca61041021841001118108002030100840901c840d2200801c1c814180034618450010003540880c221025405a00001041002800908031042040703d0f012059072000041141c210000102c040d0b002500c0c0b00301251000c24149154250525800380c8228220300407101421808006403d21401d4026208820395507070101c0c108120340e501022404c010410100b140e5645052220303500d81049030318221130310174001c1250305400c18100352030070540380351101131712582880481d010f0400000d0030150400c0d40c805000000c291f0804c0b0fa80b11044000007d1039035441302c100024145240140f210440000410a11204040070400c5542c05080b448510100d6656071400312856070f030503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 665497625 1250 665496375 665496389
    0x14070f05010c030902090903040506041206230115030501080d0507030306030b0c040e100506090108060102010b180a0c020f1c2601060801050d0b01060e0a2c130503040519 75
    0x5107442c5259825901c210034003030007110741d10b65540c0ca2a0a40d5941d208500440390032a4040c40100700d004e15401d1741840c285e2007010003240c2045c000480a0409a038540140300c058070f00f200400400c03511b40a030101031092407a040c0320300e41c180342d80c0c650b603112449e0070300080182c009400f0341414030030390042010b164080600645400d000070041c2194025000c0d514060304076070302050742c2017000c040300c1003107a00280c903140c1000240c50040d0b989800040c40a4199521190201001d50b510381c07400ca40500041e411003404c0c02d080c81c440048955084002c0c05551021081070003611001030044082d403840d48451307490b400312032002c46070260840003e50074081850b00d180b440004080c055030694155540300120390380d0703036002c1000200c031004e806010401c0450050245600c1031307040000803180076064003070b91540d03854074459582c1f011002c0702249888540e000040c1258020258010701d15210b04015070300720b45c60b90354491180d8411584100360025680c40da4500300207102d4010214 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 665498875 1250 665497625 665497631
    0x306010c050f0a1a0403020c01030914060a0e0606010e0d08070c0f0305030721170615161e0b1909020a03050303160305100b16050604051e060714070f0501 68
    0x40b050701e50b5412110f20121261160750006442114041c102c80780b0a44d0140c0c000d024020309071005600030b1020304016589480414290035418200308882402000420320004884056254140c105900a0511070401c10400ca00c0542c5958003550400b142e07422800c0b83c0c0c0c0d5840366250001d8090b03c258041c1e0207002004800106010307010000e0708243c0e01138000315041420810740c00b1404c1b03c0b85c400800106010a84000218503014001548400302910214003445100100042c90704100b982e0107404044c1c0c8042da007008070b94030b510581d04404801c0c1c002602003990b0f415551440c024035181000c0c0190350800040c0c90a50810344c40560040d000c01d010300d480c2d00f001c6480340d00840c1c40e0030007000740b24401d403900b82c4070740710300d41c0718460040c20310400c1e80c10840850300c1903010900d064022a02c01d10142c020403024050381d40100d10950050100030380300000b81c01401ca01800d5a1520b40001040114040d00540402030813124099210356480203403030800c0280c0d00c0c800e009449986 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 665500125 1250 665498875 665498893
    0xa0506040309151b080a1101021b161a282606010e0f24040302090f10030204050612010606051b0708150403050f030a06180903080c0306010c05 63
    0x2e0006040c10a56803102d6941c8078281e84807005498000341e85049892008040a4000104000b03401600c81c0502c1843c00407800c405284080c0e0130384e00440781d240313a00344c240584034509110401c15400c0607046036a00010882c6440d0340840e110781c41810455480c40d001420001e036135040d801d0046031010801070304004900c00340c0d00400300c003105059100f44440c00c401040340d000c0540c1301c2a100e400d050b0343c1d049692401c4014442c03113594450865030402c2c0c5200d00d0381043d4100358803c00204140e24015901d031132950042090301c5501401c2d80c3c1c142e241150078407011182641401094a030103450100d0301c0d45071f2001052066501d010054400d511303000d40454080da002006280c40420074103244d1075000501981c586070442ca00c2076220960040184035001410800d0155200740070f81085410007940080394002c03030b481101c080e080c0c59500c49040c808031428405a0201070000d00f406c00190501c1c0c1e40c042c0c000c4402800140007240007000207001b580c400c14440000a03449016a41148 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 665501375 1250 665500125 665500127
    0x1a0a1418040803060a0806040c0501051318020a030b010801031703070e03150105011d030303181c090906060302031e06040f06030b0f07110d030b030a020414040b09030306010507140a05060403 84
    0x43c0054030513a100c0c41c0c00d92070001c0e14102c005885130150750000058042980382800540310351b4011100c02d54541d610140029941201514494810f00d82c0398001d070351485440d1f002400c0700d0b1030603012410701c036600d070040c0045150b0200d108c2140c805018038680d280c80f002c005503815026011400c2d410311030102c2c2c50322074a0902c01c04504840003a05c44103901540f141c60140e164100301c00180e0980d00500000f8071380700e00c003032075080340d0105807003543c18503103070180390801a41c94040a00c022441c00441004001c00318400c1c50010f0110b45000c41c02d43c102401da8020f00c0c20001099101018200081245540c803588045680300d1900c408001103962860441103600003186d04482e4500640001018940501c0c2101c0f5010501c030068145101e035400268010900c05d04001d8152003100e10083c0141c44612071000791040e5165a082c20f40380c146000341615000408040c9650800d00c14420166001001d80c2d010503841542c1d2103000f254001500d01c0c00200783d101901074815081408285 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 665502625 1250 665501375 665501377
    0x20c0d06090c09021c0506121203010312080705070201211505030c0303072a05130e160b042105120703110601080604020d020d060c030b041a0a14180408 67
    0x1e01c180c0e50900394a50307844200d022401403294030213403000035000420050311560702c02940300000801e0390007800881811540340c485894112704a0920000050040c0704841103034440e500e1152524989510f080300d4020702d41d010b07158009040c818594186400380d10404040c105400380410204010440e1050551400e001841080e0090040c800e4006030317414040120f0312840d80008030b0254105007505180407079817100e06055a03031402000045156038644440381c00c1c000503c2008540f5131006070b0500d08080001c130100c031762042000c1d001c20641313003e1000d60303040b2a0318040022010040c0c04001488034603441c8020803034081c008002c2c00d408086400740c640103008c0c0e40d6224002c032070b074042d166480e0400e0203400040c3c0c0c4003500140c014a004201c039003c10788041c0c8100307040c900550343c180a882c410014940441e8441030312403c24101032080c1c481c42521800c5580002c5001070104881c94034078003424112680d900009002911040c240030b106075148100a00076180600309080d40d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 665503875 1250 665502625 665502641
    0x10e0106090605060f03010e040c080f0703110906100e01020307061509050f13060c030b060a02060f0a02070c05040f021216180303120507090503070806040b160f03020a020c0d06 78
    0x1a0b45402004503807800d25200b95407008044240c1c040c990b03400d002c108030305054000d104031001503200c0350101d0200c80034000c6141451540b0700403d1440c1c01c42c80c204903103843c048912405030400700c2c00c00803180c1d2040b048968190311410b28001406025004034118411858042c1071241440150048504050b240390101c1e4106081006541c4560000340c00c400010f0381e040c412885080000004500142d003c180d0200c82c6050006503101001c1c0440e4044d08564035143c0940c00001c03c01a001052081056101d07103494011403070094556598111031129000d841e00071039585421902109459040700c844550031291050350345082d00b0501e040000e0440759500088601002c0d800d007010180c15442620b034182c27503001c10044054a40801007200401d14410048031580026054600303104000c0540301d10005001c00c1c0c0384c80c3c1080b000c01d50000e0903404001c404080d074040000d070f01c101c0c0e40520385078030302d0050380e121400300d8124541529024650b03032103440c040c0c20b802004602d41c82000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 665505125 1250 665503875 665503889
    0x23040501060f1d0709090509031902010e0a1e02060f0a03061d010311180114030f0303150105160b19200f0d06080604060510080a03020715020f010e0106 67
    0x3071a03071504a6080070b02454420b5441c0c140505841e0000c20390840036281c1d01c054549401c110b020f0b80c402540b4180c5006444007405a0400150700a000101980c00b01c4003904600090150303a00d0f8280e00d9a9407006000f0143c13600c4220300c0001134000c24222100f0030359400600f200c0d11819510101e100940c880e0501001192411000207080040505503c0c404115070700c03180c0041e8650740319202401401c00c5a00d52201d68501c0349816410b000721401e028002c0b034204800a50043d40a05160110201e55142194030a1080200040880f600e0310003c00c0280f8000740c491650f02500100960240342c000c2c1482a10070410000034003107040c0c0c081101410307805002008408010980309080d03c54010b8000008010382e106a030901d00040800c2144100300194045d980e0300a581046000c0d0750032140d143e120824840c040c00320550b50b01c0908107035405009880d0f09660b000e5507a042903c2101601568001c41c48042d45c0240224102c40401600a2281481c40f241c0d00d070003032049006800c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 665506375 1250 665505125 665505131
    0x1f0e13060f151e020c1504140402040506032806080c010801090c0e060307110a1208090616120209040c020f0f070b0702040f090813050913032123040501 67
    0x1034000c0c2e9880480280080949812414404002c2a039003501c1a0101d41c8042d403055003036920140d21000b07800c81c03442c00441900b5468600b0035001c2c86a03403440e104034900c40d40c0140000c0c400b9a070780c0812030b9040500180040342c03211000c404014603040134103645120510b010320000b60700030003058100421000b42d0720025503a8950399144110784034407a07800c0005058035072556150610000440e08048036041c10114454050422450007404041c219034003009404000400da80003185590094030000c0600428a4071b03103220501d9240c010802010407040d212140c1103403107241d04840c40d0503400ba0042c440c100008401a58400642003410307403600c03450110407200b45012070414290341e603469081d80f920300c0c03580802c0054a400203020014590354000f1000083c0d1080041880c002011030809103107107050304019100000505440300c000c000f491050000b0381c85810120016002c424421030008030380c030746100509140c050342ca94103041c02ea2412141c60b0b40b0201d1072043e031140b4028 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 665507625 1250 665506375 665506379
    0xd0507030c141605071e0807060e03190804090c05031626090114070c1205090108042a06110f0d08010b0a0203130f030209060306061f0e13060f 63
    0x1101c80c0c106103107144420703500600c4005809180b0501d02e4a0a900840854062a84852540c000150020911b980a08801000708500b12041c81040010320590400c01d51208884000c039032160f90307101405845000550b116010000b06505075030203051200c10810000d21001000703030080d88213943c4180010804000891040e20840100591014686a102d59218140c03c9072200000182401c0055526644030106840480f46001c1c480c104c5032740d640318188a82c0c204030190250019020003084401c112042c61640c1260b5039035042680312004240c03410b250001e0f0020072426581d40d5000c110a40b0b0000340c1d031913101c0c2400350302020030010703101d1107102c0348080b40d80c440200800750080b6005600401140100c4806004809080c1c010b8900c3c0180444000c0f03082845a080041d03c0c104401080c800e41c00d00170740b0b15501403820f50083c54241044e90024007640f135802202109991810084110340348502c20301e83d04d059003d0000c41024920040c000003034a0f07140a200c00c02c1c4092440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 665508875 1250 665507625 665507627
    0xf020909060a1a09015004050907050d0905061b031501050c15040b0403080f060a05040b040605030109060e010b010f120507031113030309050a051e0a0b0d0507030c 72
    0x5120210f54003e902241400106849000380d03401880030a4140a035001e039224003901c01080340c4100100c04181280ba001640c407851a10751a0400c4003200c0703004148040c41c0e50010f180071181a1b03030080700d07400801d0341c9010701265284103c9004400311814880407004124001130005d00400c1c580c0d202008401201042e01c0c3c403030104858180090514074045003083d401100107008042804040d10000e00700301664000165041e54121010000f06007000241a80100c10907000b0203024407441c1d050601c1e00000c0e032004841d00031a441035659182c04400b0340e5460388004014103025009018552725400c3c454001e0089810300c1d00c0c55400e00500310000c0d803103044410620491071f169000e00303030001405075008100051000e422326540382100c400782c00e0950040d00ca820b10101d003081c0703401d055240040c00514681d0080d03004a4000c0010b02881d6280c80f00d500480040400c0c01e09110403072130000c2d4594400e603105003810074001400042c0c0e0300d230941065202d03030015181032004081c0004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 665510125 1250 665508875 665508889
    0x1005032406060f0d0c200d02010c05071211030d060f030c050307030f080309070f030807021311072010051e040e1317180108132301020d0f02090906 65
    0x501d8042d03601304030540001071140e008108074002d62070080341c10440404c8040000c1440803240b013944c1e200d1781c000c1c51100e030309020300c8000c41035619056060800b144d459400c980f8114000300c09102c004031007100000e0081050b159881c0070708500380241d80c0e6403040242920010700081c0c4455030241004940c0d030a00142c0d900499510181c0480c6c010160b0311202050f41002d010901c56000c0c095000500788a5a0b040202450041d50b10300e0380c03040d4600c100300118495030042030f10369088c10121030b401da402c6429a80c1c01c0e50030072020a0000d01504120001c4490703410000c1d48101844100d1420302d0b4418003812252044010949952102e41040107150059110302100e61080500041c5040503140c134000c02c13035100e60641c0c01c0d0b900c1c940518202e5600604003001c400c80b1031600c03064040d039015078415000841054000c6c1c008502e6254082840031800120026644403513810711401c5003541181d91441c04040301700b00c004030b6001600017a500c19074100744102120408103104d80b074603003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 665511375 1250 665510125 665510137
    0x1603080f010305032203481701020904050f010602071a0a0318050a03030e010b0d05101d070801021306020d021f1401140405010e0408040608100503240606 68
    0x400035420703c01c80c2008088180d10b1440518080354921200000161805d6110401e0828041103a1049030704080f180300e80c5c800706440d07207080d070070341034011310064a54149a4060342e4101c80235000f01401d207950b0038003900c03601d201c00750450f160104000341c00404501c40c6050380c0c801e50a03509c1c1c0c2d9070381c1c481003040900d904580e17404c8402e04000f2811494020b50003d0101001103000c16070b0600a034035134606101100c141500440d0300c60016500c0004203120300c413b25141200d20700b80890503611140d9035003c520804101c1c0e00e13a5500320741c03a0a01804902c0f040005604100d60700952506100c070b01035001070115900203444101c01141d61400401e060f008882a035000340700340c950100658413481480c2c60900000350356618260341c50010025640c1c00303440c4800702d0310604009141400102c0754160f00c0300010003140300500000403200c40031507048034414905500240c40300101c810550480380c0c05a1340c11b00c03401034403941c801e4155000e100c1d0542c3c000b0f111800e07569840140a0544070300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 665512625 1250 665511375 665511383
    0x6240912031806090406031b1403070807031b0f030f0b06090402010e0904170408010608060c031308030403120f2309070b130b0c0303160c080406231603080f0103 71
    0x40c0d981c2100c5803d00c80094019400c000f0004606641d80c0d031208618020140010040510703040014801d0700c0405101e040d01d41c00960003072681c68689603c41d80c8986079404000c00310360840c04e940100307160001042c406000b1030301820050f0b564a280c04d6035003070300302101202e80d0784143d00000d00030b2070030702406480f03146c068460042e95002d00303041022240300144100c6140700b1800ca0308400d032403c0400b5001502d10007000142403410004103d16101c001060744a00d075808004100401042501000b080355001040030748030784481c07806a407020041008402c80e10700d0b00d04d090070a90342542210801e6402c040e00102a002061941e1550010880300e509490380000c00030803440313000700010028000b010502c4403000e6140d20907003000798070881a40d400d42d0b0000c400c0c0075218030315002041c5605140d040c039840640d6103a0312030703200e4002e41c0700380414000c001003d241c01b200310500404c0c860310845a802d543d03140081074070490034100302e003d130300069800e00022040012a0307031090686e500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 665513875 1250 665512625 665512657
    0x2105040501030f091b0e09010209030309062508090f010c11010e0d020604090c090806060109060c291006030504080414270a0b010c03080601080624091203 68
    0x400d030041d4060078080380c0550500b6620b030004400b189400c1c921000002c001822800400d2401075010003480c8007074050012a48108030303601580d50008100c9080c0d82095803103548400c3c1c0344e02c150381a16101003e0700e80c5c04071020841002c0010900040404075400c0312000640c200f2480111900303590380c14001c2224988123000c0c2ca2035800b820320003000c04401080c1c9044c01c8030640c085840b03900a6481001c0c001d403159040a015600400d00c14003805500c40100f03400e203042d0700001c00c074644034488c180600524005403400d11003141e9411100d07002171901d051a40c2540615042005001c8482107005208800c2c01b2803458071a01a41340282c1d08296454100307401c01140034031000420307a0595001c2c61b80220015442030120410070b0f14a80c070716411900d0700d03105020794155250400040c0c10004900c140c000003075000104140c12070420b02e03041e00749648260201d810b655000e0741d035110030220080a10720041003a4010041414140c84031010000c2040c1440c0e602c0c00790780e59840d401e00d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 665515125 1250 665513875 665513879
    0x30c0f050c060609130804030f0201020705030607020a231c030608010b090a1d0d03050103061109011d0f0409061e06030213090303020f28091a03060d1e210504 70
    0x240903200a170f00454114584015a00650348414a96005500c03c43d0201d13600c8554000350360301405241c00420096028121900d4940380094541d150600c000301250100c0e000b4000e9903040e40074400409030b0940c200da840680d415200190456000018000281040c030040b40d5684107018412010030003500c01c405545036050004040d141140c222900010184c104a814401c01c1000005590003510f00041a50440c14441c06441d00e0b047c9c01e80c5068030402441c41166400505081c4003040c50741c070040d000c0341e0800059590aa004c00407036000c1e00b001044024014543e000320340514450940300d40c2c0125009444007642c80900c80070f03501580e0300080c06904980d40d0000b200c1d140c0329180c0185089030448400c0c0894000d030605000c2031402001c0f4500b180c1c1c410047d200051143c0c20078070201890a00305036882c030003030552808038105c0800821015110030303212100c0664442c25890400e4041c0c601c07602e00d4841300c9020359030141080d00c00e01c55220060500d83c0316440c0f40e580c4602c3c141c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 665516375 1250 665515125 665515129
    0x4080307080d020f04180506040204060c02060a112d0601050a050d080403020402040909021e06030114010c0209070f09060c0b04240603141605030726030406030c0f050c0606 76
    0x14000d0302600b100940c08111004e50940c81c1401480580601d88404103c984424441c108a440040005014078810402804182e07000b1085403442ca40c100c071026036a022100c000c5440c0c0c0c50b588541002c5100b0150889510403a4000701c11000f011080c80d0502a95060b211a070303100020300c00d154001c00d585074140040d05000881d10b209501807841c191900780e41c0d07804502241d0055002068050782c83c2480421880c066114200808000c1d40c1000140500c000143d160310040c400e805c600c02403401c8012482e4002d5625021540e0024506902c0b403600e1000600703800f2000521000040e2820000f00d0060700601401c60300981041c1020481d948a07038500150020100644065010a11b550107217045180603080180d1311503820031a225004020a614040c3c04c12900c001000c01000140115200010000c04940c100380305203100785c203410f48112445181c1011401d090000007404a14560150091820104c1a90300c405501d000d410b8212030794002c825100309a5000300c0e011655034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 665517625 1250 665516375 665516377
    0x160f03030c05160807030201142b09020904080409050702030c03042616060905010c0b0f0a0e07061d180a0504021c0f14030a020d1d0409030c06110408030708 69
    0x810b1080003120200c3c44001401150040c0369071104520354400301050085503400b204c2c03003a500c1256844c580c2800315030307a1007180704200031070308d222003491b00d01d82d007a1094101c0d00300700580d94015203100716604285c01c05612a5205001c0c01c480541080040340e00d051001080fa0650110341c00a5410b0904054003101040b503810101032044d0394231308284070004014841c03441040e1000c1a851000d501c0c245001e000300b4142d40c0a01e0512070710311900070100b50b6050f90701d40d000d000c04e0241e000320b666500707040c0002c0c1643e6184044a119120f0f0100340c0542000310018500c00a280c980c0352985010200300e80c60807800030141240a2180c08141d600050360003150300280b00501c0820365000c0c40c11040304104a1080a175030405004031030350f0500151180140714042c0c0100a189407043d0380d400039549070224003d000410444a5640e01e141285201c0c0c5241050005d00900240003a414010041e1400d20400d0b18520b1400b201502c09118400481c2e00711140c550107141001201d40f265103032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 665518875 1250 665517625 665517647
    0x6010c080a20030a1206060e040f0f05090a0302150408120612030f1309020a081303140f0a1b02030c0d03020106211412120402030a0f080a02160f0303 66
    0x188603244842119540a0140d0740148141d500019134440d8403440c001003a400a0000d085d00c000e141000601180d60f110050700310921040c0e402143c030041103680c10004096403d60102002d00d080c05000c0400704c0400c4048a0707a000f90308561900d400b4924010002d04291001001c10004001098501a5190303089038000300003040340d00340400c03041c201c0c0e04544c406003070421000000202c415029010300921400f0f06503085045040190011001d882c1110151000d091511411000e4041502c0740301e03d049034295100e03d15032103070f0210f00800d0007038000e000c8405c0400e91038485011080141c2c1105030440d034008004210801802041c021080c01c603250680865494000224200000080c0c8850060071110601c6902205081100f414030f079242600341e0070f80100d10801307410b850b00320650b580d401942010790300c1c94403030380b0000345014034500006002812441c071101c1404503400207820f4640701d540036142004165244003000c0c441a000c2c0c88640c000440092000c08d10503e0b1007da = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 665520125 1250 665518875 665518877
    0x8060405060d0b040629091506041502030703121e0c030e01091b06080f0c21040c05040617060c0307020703170c16080a031d040207150501050906010c080a 68
    0xc0401c80e581c07249030f00010308450a0710380f0340e2202d1214606001c01d10603070781d0801440001d0601030f010000000c81c2e004019049901982e1901410105079503130313804940c014402005801240444078074060b450307400182003940450b803030309600d0704501654010f0114090391460321042d0300483d0b20703090008010350a452000c06070359080406c4608024480c100d0200c5c041c0403410b03000d400d14039400c54804600d40011003080a0001400396041c1550581c41c1c0101180c00850340b500311850324001c41d07950301007421441c0c041ca1414082030050001182040c1d070020f0b6000c0c80219183e403121a2604180d045400d00ba51220000078449517000e000b82d45c102c0214410b47d200603607603880f10103410340750001c020720190300090340040b0110100700c6a080580b04500001c00c551900c090750f0385503001031710061f040c440050140d000d4400314003525802410000e104544400702d500f848c603442c2c0c0540c04442d2031946410004a494a0107417110340c4900816940c3c8201688140d89031000c580200040704 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 665521375 1250 665520125 665520139
    0x610151103090a0b07111c0609032f011d030d02030c070203030a090806060103061d0405100501060504060201060b030f010614070b01120b06090606091203390d0806040506 75
    0x41d03050f9200c0100c640104591040551079408a0a0010010f40a400c0d024401c104100c50668944890b584110456405c428000342d0034201e0304040d16651622402c5c4801d0b020f00d10103085500c088001600000e40d4520020040c0b424403109600310740b40034260281035a401404030003482c929903001140d0100c40300703001ca41854506d5001c0781c0395402c013a440101041000f5018070203181c08111450f0f000000340b03810303c561480c0940014030001c103921885000014000040d00344a000c00c15541500203d4401704030303940e581c04ac02490354100b401058010b500705600042e8001c80b00c01503c2c05032500070302a040d664070b49501075440600c05600440c0144051111401054050080c540280751520000e10300e4807080c07404e13940b1180020041407044a900062003499103650081e20a8800c1c03c1d03030702003000e419070250300e03146000d941c1c04004c41c2080e600d00c10301c000f94140380140c1800390345c650326075582600c1c3d00c1e0703181c41e40300040b20303d00050040c4001621034079181d040340b0740040c0090021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 665522625 1250 665521375 665521387
    0x31709102007052d04060305030903060c1606020a0507050d03051e1005100c050f0718020c120313021e10020303160c06020d02031f06030603050a060f060503030d0e0610151103 77
    0x201e415a01668402d84654002050702001030900703004040d4001d001080c044e1900ec804e43c1116022540e400010300010360110301c88070350500074000c0b1b405254004088a45121141500a0140c03004560640011030100751405c0b18007a10040140103107100045000304e1800c1905002002245036125000c21000b03039411008984c084c0100c0c0c003040441000f070b000365403e2842c0c01081c042c3c0b10501440701881004411124800816241c09003040070900343e90740d84402c0c60f019100c0e40c1001d4060740c0420b1203d46205280004c0b5801464160207030742102c0c8050043d030060b43c49010444986100c1c0d03903410032a5070694881c4c4509401144509001410442c42a039000c0c2240c100b1512082e5030343c1c180404d469050701d4190810002d080c0c919041c040c2034110f9450640b11000c3c00c40090859859030544000302c406070300643d010b4074000d000c4036110760701400008044e082882d140361490040101161000d200d40900c5405d4580d80d85001001c02180f143c1102d01024808a24010340018058 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 665523875 1250 665522625 665522629
    0x1b05070b04030501062907030f0908011d06070903020a060809030f0a1815020a0605132a060305060d0210020114070302090301050a0510031709102007052d 68
    0xd4805140182c000040040c00c00000c0340a404a0759014a21202d01c1e41804101242c91b104640c00360790b1500e0004442c000584042e1100350842d0084100c65081641c08501005800716003180c1d140a44211502600e851b08180d0f07010240d0300020350045400002842400d000d0041540c2202000049900d0244c222446120715006106010b00050b8400040e01003918007406c0d5a01034600e10140a0a003100fa0b50040d590f0345085c40c00400705500c590002d640704502c100c00f40d003065040b030700c0d89101803410002c0c62040116810420700401c0c410001044082c0700340720301c510954002d40b450781100c042d03808005110780c2c80c1c065002150f40b5444449001400e10100c5400780c5030a440150711b41800c4000c2509483c001800c845440d40b42801300f20020002d840c554040b290403000062000d900140d1000080c45400c0b0141d0f08140c2d800f120001039030b401490803c040d1812540e504d405280000d06d10781303030221881116030203801005031600080700c51012285444900c1100c0c0080c4043c800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 665525125 1250 665523875 665523877
    0x70b070c03020c120601051009090c0314091203180a0f0b100e0907030f03090e0708041e030f0503101d1b0703170406110c0a14030702011b05070b 64
    0x28110009a500009002003540403c1080000d0790f04503005010300340d9004030207a95100500c0ba00d48180011140c001342d1f00c2c0a814090003800841206100c000710f0004040c01038510f00101d005502d10703020010f0883c000c04a020703131810301140e410f02d295407103000310f420300d0b0b280b20700c400340c2d00e4001d281903400042c0c0b06100c0307030b600103106038280c02141c070b02580130520004207a80300c80c11501d44081009880c000100300c640c1036075480080f4035075402e0b01703090844404010b50065210f0006040500c0145608401c80d07500c00d5200b110701c10300324a0000504240c040c1b19220041c00302c2c2100050040071802400650380c407140341030300400642d603078040c1d4095803614072400d100e83d016550248281c2074611508914a4070360503c490346000c4c141d550080c211512002071072111200c410204081013940c2d04200c19000c4101c0100d0344800346031320901d88510b0541ca0440f00f140f02d90811129500c004003c2d0b40132160140c4031081c008824103540b40c82403c1246c0d048074640100c00300420400f40800c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 665526375 1250 665525125 665525131
    0xd0c0503121009020a0e010f090e04231005060f01090e0a0b0f0d08130e010302090a05090312040818030c010509040207020f19090b010e09010303030b1302210a02090d0b0c070b 77
    0x1558000d940746c844c50014042240003052902004190700050203540303a600056900305a2094200507042801250340500d09010450001d89002d08861380400c138072181c10032402403008440a40c0b94580220065407480300300d20441e0703c5c0c0d1044600141d203011b0301e0340c010354cd50600074204002e51440d100004960441c07580c400c54040d140420000c858440003942c034800340c9554000a0b2441d41550005a1039120003800d01045580700d20011744001e1050066a503010400d00c0400000d0030145444083c0da0080d5a04400d2160303200c607500e68a20700006d088030f0001042c0c40e02480c103905001444041d500c260411b982004202c200785035280c44640e8090146051003400583c4c0301d0a2a039000f09440c1d00100181c10070440c48800401e5540780750f002c9044a40c1403c00090100c3e4900129100e008068415003c5a201103602c010300703104911440b1001c40c603400c68840d141e0350b40001e4030880c001c034000c240d00910079044a0002131861600c0e990031100e000a2682050410ba44015405c00d0403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 665527625 1250 665526375 665526377
    0xc0209070c06050a060b030f07120603080a03050a11030a0c110730170306031c03020c01150b07080309100f15240e12070311030d0c0503121009020a 65
    0x280340441030104622411350030000d94141030282ca45800340349a40c9000c003405103451044000c0c085000c09014400401c8950218902400810750381c0c201501250000307924080481d00b000009114080980305160f0317400310950700c0b1800c540351942c1d81001408016028400d001c9894511034170342908000e120000d00302461101d032a0075280c0041c1505284400c10040c04041403051040061140301000204c0b103020b1081da6180d96075000000e240c14429010b84409124000c048030000b5815001024480342400c002d00c40340d40402e5410010708c1d400e120342c040c80b200030300c50000000d000c0c0300195000b480d001d08444140300c401e0305800454455072242c5c04540d03620481450846604020040241005032046911803118040c2c41d1142040245e40c004000e03054038642c4299a60021a006181b10402100c3c00291645001107984440c1c0d1461072091090280d41041144200d00b0b410500741d0041c003640c02c00e01009000a4140c0c40944050401c40f0080c0012408510601c062f001400c41 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 665528875 1250 665527625 665527637
    0xe01050a0e0a0305070f0c0306020c0606210604080a030204150519030b0607060e0f0d02060121020a09020f070204091b0501081b0c03222c010b03070c020907 69
    0x4014101000c4820746007207004140c0150320220082034200b0113132410160021b4015051883c14a00300b44104a140c10003045c481c4089404501d03179a000868034850703541950002344400d01300d07505100c0040780f00040250740d07104000084c000b0b032016001e0400d20440381005401c0030344980410300e20142038480c0c803000a00104510b50f078900b1081ca2088503c9450804006100f90800400c03074038803520101400c06910354010704036650080113a000051115010f03110510342080000352a142c0a11520700b04000c284451110351807880f120841003940200080c410714601082040a5008442a500007e2040c072030300c070240c0c0b02c07806942d004522908050b90524050544801302102d1a08803504008040d420009021b40b0015001400c1d40d09240580d01c0c1c80c4503c1c000741c95072044c450190034002e00440e0700009a6440c022000964100480f061700c604000039488190004100c500c443c4800e00f000100940d080d004000d40d0824101d01e41021001130f65004038041c0c10f000e40f07100001801d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 665530125 1250 665528875 665528881
    0xa0e0a061e0e0a0606060306060509011b05071e0806061804030e06040b0304440d0f0213060302180904111e01030f0e10020307170429060306160908010e0105 69
    0x140d6407003414003406c80d0781820800f1600380301c40100680504400f0505202d0160030340810056075140300d00c40340e9400000c80b00020389458018405c1d540c220001c4098a0303810401043c1c03c4404106c9900c95000901081c1601407030011003030316698080c00580a018030b40b4010b0b245900d40800510203000708107281580c81c2018500301c075001707803000740341100840c2440c0140e4100015086a035070210849003d190110b60907411510684200b25900640701d1a02c50000d80009540e00030303001e0440420148072205a0340c1c1402d034103900c207440c4601481e00c20a40400c000d032a04c00781682c4c000740120040244411104007003820b100e007801000521083c1503c98030702940e070602074010010b2841340305001e180040d102e05651a611880c0600c10180c002c80001c1c10b19100315489400c80c20462040141d41c1440c0c180f5540e49a038014500712043d5068036140c803842d9040b8007060185001034010012a55050488d0880e44800880380c002c103d8140c00000f5100000d0207901c6001000c18000540d42c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 665531375 1250 665530125 665530133
    0x1509100e010b1215031f112a031602060d02091e0a050a030506042a090b01080c2502060904020a17090a12030507030f1a090a0e0a061e0e0a 61
    0x80c0700100840d80d405202c0703040b2041c1c5d840100301007880c0c00300e80540031081350b03005042c4006400c00100b0000c0a40c070109030724100c5510307901e6694081a8070500d4a0384201c0c5908916200d120301028496916803c401003c01814414024148040c20307100060070039121200182ca00640070443d0320700703100c102500f000c03a4074007544040020f140c11140b4500891a580c1d0706511410010409800340c405207001c40e2030314000c3c000c0780790000c445803005a9a107445150403402014500321040c00200304000003001e40c070a0108454030741202c1440d000248081e2150321030141101e100c00c0343c0112091102182c00d8603140080e208881c3c103501c8084110031100402000c1580091001007103620010607040410402c8039540c0070b010180c94081020b9031a140180d0181c6055034148000c02d15110810790800d0600e08100340240d41242c00f0030103511800d111000b9524500c0352a1402d4200c0750001000510a41c0196214004d0b841c04100007003040901c0b00441c0d8483c0f80d2005241c0040308a08200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 665532625 1250 665531375 665531407
    0x50a0c08130c0b04230a1a18120a120806060711010309080c0a03030e0309060a18080a060c02010b03070602030f07110607060506012607050a0c0605180706081509100e010b 75
    0x80300059a001b2103282c5000d006803000c0c80c0710b00c690a40e049002481c0c80c0c140300c03443c0490038401e07000303032080c1c4400403070310142617491f00b0b6070b503094812541c121030501c403161080b00994001c400c010301481c02e00e2500e8a40d000d441100c045964145980c541c0000c0c0002d203403101901101c4034181c0a40000e40503400c000d8281c030204d4584000e9604104180d0030942e40d80010344110079414a48005440200c19140308044510380106205215546400c42001b02c00e400010301580c95078024880d0350b004e0030605668509500600015030070902c00c07000d02d255614054079000f030280c6040900c03046050041001507116241c02e03102c0c152a01c0c10030070956003140e81f511000c010304096150b05000c2020f07a594030507000d003808081002c0000d140c111240329194140740a40c00c007004212030300700b25101c0805031001070141d8509000311709000402c540904040c0b8495401036594003400c0b0034502c1006401a002400080d074a005584081244041e08114901070f01d03400764a079607959100d42010707002c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 665533875 1250 665532625 665532689
    0x30302010e0f010b1f050c0105040c1406070c0317041214060c0403050312061807020604120504031e0f050703080904141e070203041d0406050a0c08130c0b04 69
    0x603d13810104d51030001e1311400c143d00c550070b04540352048100c0d000c82d41141d8600c6440900812582041c0c203000c244140c10070343c1c80840305400c2c40b20340599000b10a120843c0501e5401a160801c0141d04102051221300344003a8481e10141c001d241030785600d07001e004c1e801500b4069a800204586001021800308503064001f00b501050600303203851f6035038456a078403070102c2a2a2007610100072602c1078542c0310154007520310f03154a1400d90b1400460007580c1d06c1e03044074280e13880079074a035051550501030001c8400b5690051030b0f002e0400034402d0104881c110b002c1c1c00b282c00d15020220040428824130240014521544103580d90b41500d00c200001d0340c5200d4a41d02c6003280100a00c01305510816401035200302c504165105983c440700e0a034214000d9074010120300c2c0900c50814038044151000714800d601c19082000551141c03a001012202180341800100c0c001101007100c0c109a00c3d03008039841e1054400402164481c01404541c0c1c0040e403001c042002c121440c0102c400040484040d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 665535125 1250 665533875 665533903
    0x3190c0f0f03022d040f020a020c060316031e020c030c07050f0604410310020a0903020105032d09011a010e1c06060e06030f070303050901081f030302010e 68
    0x6107050868002030003803070000001c0402c0e6020034440310030944000300c21070314000f0002c00802c030403010300c400341d0007a52120032604010300581d84a01000e1070f02e002aa0f020b81206100307010840529201a00184002000c030750a07483c65181120602000e8001031940d1002d0b40091916058071204907403a0020075040a441340c4e03111885041c0b03503140d41c01601c08403403851804030206000541100700e007c0b480d4400000c0800c0903400c1c607000c0c7d42c03404030000380001e041d0201d648460818510004030f00401da01c1d840014501d5608001541c80350000d5038100040c0901c80404c1560701c00b8905111039000e05c8420a4442e10080090100c400c0c4109000700341002e0041481d80c0403800000c004030802c1282c98070880b020455498406103911146603600d41c895020451142c840040aa100d00c0444e1054401d2080c90b4481c02403800110f50300084031750580381c0d42d0600350000700550b520500201200b243d00c1111042c10a25440c3c1c1107800001e500075000001c0300b0030545191403d00000040403c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 665536375 1250 665535125 665535149
    0x30915030106120f0f0e0c011205101502160e04110d0302070509070201090609051006051c0602030618040309030c0b0c0709021630030905061503190c0f 67
    0x2083c2c00ca00003598014140f00d00066050700e00c6001e90040c40004041000207107001034580140100142c519000301090305c81a12100c000c0c03c01c801650000c41c1d04031001c00300c0520800100c2e425692501400f071041c01500c1d450500c0720f100d001d400c0035550007110820903090600051006488d180b50501105072061a0761401076200655078055a03c562801851190001520b580c805e61040c8000d55004a080c800c9010a0030055500c01c003042424031003030702e000400031300c1d450b0941c07900b02c4005420b0500703d0b0080003910303403000179040200300542001f401045062080d00580c2c2941c490351081c1c032001a610b01790b00b080c114644841d004443c0e0b6030300c01c000307a80e1500d20000c3c801c422282d0191001d40d403080d024403030024030015814018800440d054010581c000c610315101c00c140d400700301070840e130052458101e041d039036070a001900b944c206e000801c0f840c4003c0302c42820810300c094121052805462140f040b0048412801e89090101000a00c0440b101c2c600d503600a05001e4000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 665537625 1250 665536375 665536379
    0x1101091401021e030f0c0313150f0305040f060504150c0509031f090507060801150c0b0c07020d12050702090a0506011b11061603021011030606160b090309150301 71
    0x2030b40e10100c2c0c101d25078100702e4000021030104802c004481c903061038888044c1d1548101b20429590f84c01044000303002030011600071600048014210303103159107d54590061865064059009000c040c09c284c03540f00c5040120000305106010701c0d03010f184295a014a11584c0000c031108845000a1000404c074040008a42a58001800c284007141c50343d00000f40c0f001826450700203007200d02c2d00621b94002d1420000fa5144c1005445d0b0480703050b03101200c0c640c8d0b01503c00b1250040d01000040c841d01c0b00a000c226101c5030f03070000d415140d10292100882201a0300c4111681400c61b591200051000904000710b0400071815900300208500c00c0c4454140000003074810010002110707903020b112604141800010320500058000107802c040d0b4942040b24401c80c03128408000307502501c290011030b46101910311542020300e100c0d000f13003400c50312604100003680e440010204810a03070700c08483c0118211680140c020104500155910746489080c010a80c4201c0340140d840031082c001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 665538875 1250 665537625 665537627
    0x80a050f1513060905040510091509020f0a080105010f0806061302030c070b04032d0c081804020409020909060d120c020109030b0403111b0109050609030c09041101091401 75
    0xca540009010051000420a107408641180312807a070b071007401820920001200d024561066010304d0040081e1411100c4009050007500c0c4c02010003080c8150f500510b2070116050b51091401710f00c0100204408001c44000880e002110b40000070300703954032801080b0642d414000d010007404404060242890440b0000d444080380c4000d628010f5000800202d0502e2040121006194010410402d0b810f050400510f036194141c50500d01e40740c5c802440d402c09691040032907406149954551241c0410303640c040150300100001e036412001c080c40a10940d48034000340000c1d0506040061b103580345142004801c440283c0f085021b94042c03448000454112a5001e41c2d040c000c2c00c0007241c100103071004841c94140d5510240c030540c0302c00d0510041603813101c2c01c44560500c01d0200c6a82d00254082c140c802c0792900b1a840c04154000c1c1d0130480c50800c00c001e0500f41030300606640340880d808011907484082103030102c0d000398445207040e61560308504c094028001303c6002178810b44a10780 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 665540125 1250 665538875 665538901
    0x3050316030c02060318010b010c331113091b110703020913150b0105041806090c020a0605010801140a05040507150e0102070e2a0f040e01030201080a05 67
    0x440002100d400111a42454040d40ca180101d0354050082c55586c030b803083c100340e1118500300c41150554200b0030205030343c1d8410f40304070042540001c0000d08404003c1b50440000c0454401521480c0305001030400c6030180c0d10ad100c008110440c119656030194a252552010b80c60b00321001403031410115003054068026050079407025400d007910110300d03100c1c40c03615000559200a600c9122002045000e1b5604510001c03d1072050002001000d0316a07440c1c016180350307101c594000340c0180002c0014031240301546864032101c030303000244a501c1c1c0030700900340c1d50140d002002503403241003003804018141c1700b130500401c0903800800085c50700a80599803800c0c00f82c240b01c3d0f000d40350804a01801001c1c807490f0020801000112540b406a10b00079100c50501da8006000d80604440012101c036080122885000694100c0300c8004a0341d030300703034000400b100ca2031500b04805d002c1441201c103000000c002504481c203160f2150342c0340d840010701801000341810382030390800060111000d0020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 665541375 1250 665540125 665540137
    0x100203090c0d05030702060310090e0109110103020f1e04180608121b060f0a0605090f0705031f1e060519051608030f0a0b010c110f180f01080c0a030503 67
    0x5940d00e0802c40707a410030a285014081c80030790b02c25000003d2000107041110120100c07014008180160840c10001908035940c400c0c0240424a0701d0314811119807095000301071041d9240c41e4503003020280d41340d1404166005075180b02e0150000340a0041f54014011550071003c40941482800c1c00c0606c0300d5101c840210401201d5030000c0b940700000d2412045e4142d150601d80d040718150300e042c40c84400c05090075685040c606140c400040b646013084102d41e88509061800383c4055101d4050898543c2d2006000540b074107a42c000e00801440000c1c0340000805000e24180c610040e007100d12843e048403503102400744030040142e185034046080c03c0b422203511034180b0980b82d046004004148003032040000344140c00000c200114552401e44042c00388900003010404201c1c07543c01900d8625403680003030491168078443c21030311310f08a0024051284064040c041c955180112988044010b80364624482c0b030640041c0900f000421968545441c200c0d403000c126840c586a00791244610 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 665542625 1250 665541375 665541379
    0x1020c060310120204060803160309080f030f0304020f090103060507121a04050a1806020c0f0c2110050c0d050c031006050c0a020d0309080d0309152406030c02100203090c 75
    0x350450025585e03a503012070b0003003a18000b680e6a0b4051240d241c1038520350407000701c0100b50700100105407502c00056005120310200c000714501070800003101026080200300306d9001589000d544407603211280694003c500c207090108140c01c02c03901c050302d002100804003010368034000007000c858400e085051361380041520001242e8440c040c400f8040c000203c0e4081c0c107209004541c00404c00940c0c010040e49520205035100c000c060608107480e031204004040d440303841c0000310b10100124604981410202108680c404a4800103c40541e58122103001c0221300100703201c811840203010744d41d80011640150b91035440d000010560060280c01520100040450f4145480700c04000000344c442d00100210090740d00392900411024850144406134011070141c0c4000b00d002e0b014403034190744c0c00310000c41c0b000240052000101580c1e039402c907044200b80e001c105142140c3c03010801801d010b903000b140000007004060b01d08401004030285641c4100700b0040318181c045101c4ca003503101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 665543875 1250 665542625 665542649
    0xe07090e0c04090f0605100207030203010f05090715030e010908040302041d060a02130e040c03030f08061302090316080708010e0c0d02010305040807080a03021801020102070b01210b04050a0201020c060310 90
    0x44e0326052004188581103550801d425100b058070458001400c5400c80c1e02c00c600038009107250046803415605d0684031103481e94072209043c0800183c0246200900d44580340010350002140f00240c05c1d2001e0100c00e8442c42e80000d01881941803900400070000c0401248003141c54503c8812980d8200007040c0340103150340400c801801455214001009004080040116040c076040045410795503210488c04104070646100506008003003249c0b05840052000b5040d43c0036445000c082e611990400307515018110b2000843c44c81c903007414015110580080413864102211103085603140c0412034207079407088040000c140e507800b031300824071582881c0c045075a84580c0303031900d06400780030f80042c080c0d60045481d02d44180d1580c060701c0f42200c0b400350120070400d01d0005908074415400040c0200b8110001448008002c500501c81070783d503c42c10035440c50b240e84841000a0b03041c1d40441c1e140e0000400c010666a0411000708840d0f812a01036207181804610494041014403c4800401c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 665545125 1250 665543875 665543891
    0x8030c120c030c0703052419050a271104060b09062104080306011704050a030e0f060a170f0c0711041b08180708070509040501150e07090e0c0409 64
    0xc014003d44001080c54000c8948568603442c080d61140300024030300152480541c103403141c0c2140780040600409a1040450882e200c80141d40d000d4840140480e4483c3d03290408a072940d0b0b08d02c8400c042e90301d0b030b19032491500c005034a04507010140b050501072240f41414828819510f0440c111104d2400440300c040d80c07014001c41014242080340c02c41c07217400311b000c0c04000900c01c0e0f0b00d000f10b01c2000240da5a0205e89459005000d659005450103811b50741308221020000b8059140980408401401e41c0c003500c1d144400543c81c0d91092141c000081d44000c0000302010015070f000d60414482102c91960b0325110702501c03002c2c010b2000140ca100c414030b1503501e103902d817070b03001e00b00c00701d00d03c00b08c83d19011088401400d100003c1c0da41e1040b51105403031510300102c002c90040d007507843d22006800c00c1441c1034104101c45802a000759072956072403503201007a101c1000c640d4024015108240114504064042c2150840340c0c803510f110031854040051640381c0c5000c1b0b9099409101000036205 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 665546375 1250 665545125 665545147
    0x26010e0318130603020405040318080303010627050a090c020f0a02030309090c04030b1509280e0f01051501022407030908090a03081b19120c0c0e0105010908030c12 72
    0x8401c0d4000b030b4110340b8007c2400249984108142040c0303414000c41380b030b80c03030b52512540e50300e100902c28440080c00321200d030940c4884148010001a01002c20350008640b1140018150001c1c2d90124014640d02c5a4038072926405005203641c0400740302c040c1446a82940219842e4818040558400c0c5070440015080148903420784001d90303004158015a890041d180032520211003d215200b0070f08040010035084e00158814540d00181d0688030261408218510161804d507041c0100780c06407412200c003050091081034442c40595406502c104071039400a810701889508410340a40c0d620822002c254a40740d400e9081807480c138001440300103500f0714007034500482c8501075022800001c000188040f041c080c0c001000c0c130300140c000c0c10307480260050f52060091018904c10120031000c1b8081540c16070841c6040c0b070035040541e4440007075500c004080809403c030b05154580f50b8010b22595920041e00005400000d0096160105081d06135660300318400405000c0c500000c3c0440d801 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 665547625 1250 665546375 665546381
    0x9210f0105011d07110f0c040f1a040209180c04030309080a0515221505060103021617070c09060303090f0620070801060f0e06060702100f03020426010e031813 70
    0x1055803042a40c018101600318161602200c0042501ca2030030824249d40e104035601c102c8808000303002602c0c244500110500020790040a4001e40c040c402d205203410b121424520584160b610032419036455041d490f001c1c14402c020307000344940b80c0c0302006490019000080b4001c4820052a401d8035666802c0007070b400050860040e83c00030440594036008110f071f01c5a00c0c0b1000aa482c01c1844980e03a00c0004600300e00a03501e070904098240310964008c1440c06125690301e900a4048a03d1301105803035a02c404911944590511075644008105243e0301c041860040e1244034031981d451860304100074160310318985441c550b05000340300010554410003a010080c003660000780100d0f0b035540c454603000700e1144034880303040c0c1e0b5020028600b80b0b42503084a401c0d603030050a407000294a2041200c0400d07404503103c05042c1c4c02c11000c1481c103540c1103420003442031800c9401c9400410441d03682900c02400c40d0300c20580c4207101105603080300d00303500c1c2190b1500745da41c0184c2d0415140d000c0f000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 665548875 1250 665547625 665547647
    0x1201180203130b1b0d050906060114090f06040314030d0f0c0c2004150e0a0603050d050310030501020d0c0e0a0302100e0109030c06050304050d08040506070e030309210f0105011d07 79
    0x913460000440c3d4011802c0c50704090700c114480707015a80640c1d06e0600550300526280030781400c007142000101c82070b29103000e1405039040b003d4040c40c14551241c0d036251100b4035000c5220340b01e0b070011421007049003050255260207499003c05116840851102400100b5400d100400d41c000078641c10649809200508c01d408600500902c500c200e070300320f0705800d414a8000c103658240b0910020341300c1100380c094141201c0c0d22600608840201c0f0380b00300ca560f000501640ea50360f0b401c0c50b001002c120f00b4000f4100681400000103003d0b90b14000142581151583c030902480c041c0d40b04001596aa10f614803020400b401d28580c03046007200102c500109a0700b00812508101d500440c5103548034016611542c0b14000700c40300e907611008103443c181c1041714000d080750311400020340024417503420404850707005411682404000800207219466402c000680b103564408541a842c2c001c0019014191007000200000d504005020341600c3c250305a126500034250081108103105501d0119 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 665550125 1250 665548875 665548921
    0x9090a1b05012a02030105040605150609030d030b0d12030b01030c1b031d060c160e0c0301050d0f050102030a090b01090e070312180602060a140105030a0210030e031201180203130b 79
    0x7000740b43c10724050009040075034000325010422460b900d010b040033300440d54000b80003402001c00c09451003080780542035220341b864102d1342400c42140060104004594519110340307010860034074200c00101160601c181400800c042c80d858401c0e540201c0c1c20039103980b609850b007200015504503585102d00704446405402c5000007404040d0f00d1808241403110403884c04c01010314503940e0503000102d541c2a68143c000e10b400300010005898070901c20b00d4400d1113488000000c4080b40c540c6400c98000300d4446a025484680340700030404040036282c05001181800c004040c1c0c000c1510780d5071682e60100400b1a8840281450118003070400c01c0003000c4429251609a170325807400940f24001952100005800c3c507400b03007900203000d90468161000640141b54a0b015a020002220408551042410360300c3c00ca030807070020203000800d40e150107412688181e5141c20100c6060b5849011032901051040c4148440d09030607640d04908290805034110154541100542106010b070035999 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 665551375 1250 665550125 665550131
    0x6090103090302070b0f03220309120302070f0312020601050121180206040312030c0c17071a07050a020f0d0f1103090306011503200a030207060b09090a1b05012a020301 74
    0xb40b14140591b00851041404265100800d003111604c1d40c00d1001c9618000c0c0072031310098090168425502401d00f074640a0303c121342e040c070341e80c403e904440c1805401c195078849844000000e501d40401c51f02c0e004250a10344090740710900b0795011490340750803540160710341d180e2036400011031142c80c990404940042405a40d25034a181c103040142544944001107410481d002c0c0a81e0f00030500245061b03040058034402d0000e030a6000180d90244ca01103e1510f11a11044200116004040e200d4103c54035202d503542845000689441050a1110340661000c440d07440b40960003213062803240c40e14240b1080c0c00c018041c84500f50b0250112a0b601842400300005800c078814012400c15407054604006469400060800c420603034a030a1008200410004044074031a5001b40706c121302036080003e0701901d600000d0210881030310000d40700d030b0003145200184103028101c0da20300000c000080c02d01c4e0b4503103c0040c14600a41603070108414400d024241403031617900500c511250300a00030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 665552625 1250 665551375 665551387
    0x1c0507020612072307030503130615051309081806070609030806010e0f0a0314030417030c071e14061903091b050d0b0601020c0d03020f060703060506090103090302070b 74
    0xb100520030202c44800004013250059042100e103200e20901800b4642001d80c54a0195241691140d0000d02a13134150111615404042000b82c8910400c1040300100070041e54501810028802444070326000c0313007072924403528000754079001100c4020b21003e1440f01400030a00005040b40105000030b4807060516090008165004c00070310311460090b21801d411100420900c0101050701071050740109440c001440403504100c03448525418000842c0d240c2038a0761140c425030106403202d40e42541c0049500030480106000300006072070150041000440340708028864a401c82c45100d00101000101006e285c441c00100c070790380c0300e50070134060311207064010090042c9400d120907103510030724040c0301030220f0b500d2030104115a801040000141c0c0141c07504010700002401050640c032424010071301d161900b86071464081d0281d00a4940c1d11000b0703403001d0900800500120416141c0001030006940f154140c0303080303480a190000300d6040314a0140d142042540181645040c04204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 665553875 1250 665552625 665552647
    0x41211090a021c1407080c0423090604020c0d08090313060e01030b060306010f110307020d0302060709051f0c060b1c031103130e04080d0f050f06030f1c05070206 71
    0x180010959407481c5400c02c03d140c1d030840101d80700203070860440507011001c948034510407109190409845111903140c40d60350381203c4040c900340b001070040300e0501c04203a46c50f0301d4a580c0e055806041070314250300c0d1a00ca80b85080d16090005c6640e01802001c4005ca07049600400a031520302c11403c40b501848c613180d5038081c0c01d426180a1150000b03040110700b400700d007450f0381a0b03402038406844610014102040546003c080d104503600c10b88418000d441c00369851075200c0300514066000f429070707420040c0000301441c2c0241c10041c020105014a803a02c1045011081c040d100103281007200742c801d61402001a006502c0059881070018000c2171072860749031035580c0154425244e80035107079216039802d42c603401218444e6013030444c0ea100800c01d60219800656100c4c3c821060700f460030305002c0800040318403516490311000c0d40c440422914480d000c00d001e80209048001f42138000300724000365520106e62038400c6509050840045085004105072400302c5e600800c03098840c03c1c2045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 665555125 1250 665553875 665553877
    0x506121b040f0503101401090f0b0a090b090f13081803150a0608070b03040807021207030c051c020931050f07060f12050403120519050c0c03041211090a02 68
    0x3d261003030042c003400e14013501e8540308411591681c0303610006540e21b4040c04000900d0900043c89409448900e0840749a0710890f41c06d02400c42071500181c0c8005441c284010303080024074031540b04c5268814801d558550840040c040d96100c44202d641d04802d0760114000440400c08030740500c01c1454408000d403a110419101d0001030104003d600e56031004a41c0c0d6075070500c280882d03900c0c108045400304107040002c241c840d002415101803004201081480c00045601c181c900000201040c406407405071803486218030100090100c20240da0001882404090b10b483c0030400a014901c1400e4005881a00d02403812111f020b00c1041c80d003402d03912070b0190f407883e010a01401d04003065050040ca4258000c240c0b550300e03035075201000e51000000f024007420542c180701002e031001c044d40e050780c02154070130751030040c0c808610f8009004100075241d001e8480c002102c010700101560004c004141e03011600c81c18203a041911841c1440b040200e494403001e60000307900c504004d400c1156070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 665556375 1250 665555125 665555129
    0x51c0e0a0c05092d0c190306030203100902220e030a020318030f060f07050d09051b01050313290408030708070c030f2025050a0506121b040f 62
    0x260b010700e9203564020140004c070000100546524450890207072900c0440c1072000c0d40208031080031032910902c1d1804c2c0100000d130605030b0000a0300c54030306004504060200c4003850006e15001d000e40c40c8640c0c00910740716074103402c0d88450703a0741134013010794440030b608004007420fa4a41074958071035540c80025100d60003150300140c808101750000f00e043c1400030b07054001038a00e4010307000719211090720040000c0080d00c03000800c40c2c244031001600c1c55510480c126144510020500c442040c0c816646517101f0611440c140305082c810040d072200910840d010b451750012101d507074803c880f001c021900c56003c001c808c40201140800c030801183e01c0040d40100f42540f1204401d54400e40d040f02d041620500090004085645400d81d090181e038000005941e00c0c0014141500112142ca16141803011410340038100400d4104449480d100c9006c003070081a02e00650040c10b220101c0d496202e1419403103100c1040000281c0902c2617000c98240000c91301030700c542c1d140e54580110081000318 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 665557625 1250 665556375 665556379
    0xb010b1305030f0607110a170a020f01050c04050d0302120d0212090615270c0d0f060b040b03060a0f1203030c0c0302060f0714120114010906051c0e0a0c05 68
    0x14440440d00303107400203100c0c3d0041e9040c4010030055036800002c5420450030200b1540c140f0910b00c0140000c0c6401d00d00f00c1c80c00c0c0f152210365840307903056080280740107440b200303040b9642d251805204001030741c401110143c03101078815a041d10702514080703180c0101000350010100010070380c2411f22041d900204410454a10318002d15210880c01c980c517117502361090445000c0e400072420440c100b07482c0580380100641484001c60040644107500c40b03c0480340b5801010000841c0d880b1005284184404105c1e0050100040350a0607000c0b61607124500403c25014004070009240d90740742c12640001d0449011076504465655414001c0300c5070041084011904064005464911070100c100c1c0d0300c0d8140c0d00400194071515008418908080d00440400009010398081c03070f100742d801440340b18489400303580190700d005400c1d07201010051a1904001042300704100e140d80c042c1c00e8402c44120070038503a051607143c0c0f0210006010040c0100000d0048003401014403070084200350480e182 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 665558875 1250 665557625 665557657
    0xf0f030a0e150919080405060711270105040e030c0a1208010e0c03190b180402040c050403081e070c090b03010605042003180703121202040303050d020c01090b010b 72
    0x40c9818031240b00700880d281281607102e0381104035000c088800d8076030100e004100c964038080e29000403886030b0b40710b118151b0b440007480c00360200606004858040c22046a020034042c4480803044090850301031207424441c03601c1e2002100f19017824011100c0714410301049400301c81813460b080d10350007a0480c912001c1821a40005031920708490303250701c24406080264910b0352180c201104004502c20246005640c030081180c994456170410b40c0001c04c9040851803610781441000150b0304a50313520010031809200410000342140d090300d03404c0c0070111a00b0060069040700345d220f07000d48503024204207484c24000a181540340e00012071407000740c0003403084940701c03002e200503204103511a074240a41c1c0d40409a85060840c003554104415265400d0021010562545461141c1e001690b000c2440c01c01612519001105082c00381454101941054510f450203400390240c009030204050b0005031401c1090029030082040e03030b500260075038865865a04154054001015080390060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 665560125 1250 665558875 665558893
    0xb040507080702120406050f0a0315121b060e090403020a080a09080f1204050f010201112101120503030105090711060108060106030c1121040b0c030d050c0a0c080f0f030a0e 76
    0x81c4d07401c0741e0a031012a01c410349070222100101032580d0041e03110000300b5955101d000903844407540340c040100079415001101d00c03030909041c0ba4134084500c1140340c100e0b202c8002c01070690440001c20440078100c5444020741e03101e04060342405802d00c401000c02800241152003140c0010581041d21141411074101781c03401d0150a50f10400800e8274a80c002d001d2000304030310f24001c21211013084061001003492130b0030340307880701d965041050250258107024134001e070626042400240180f07141d810171100c2d04c900c0d4880c551a844103021301805454000d000642043c00707a40c00030f49003102001110025a51074541c1a03c80000f8001d5000103410b058880c400d444c49140550940c10701e907800741061100300002d0f5001c03480442c07032140c001c40d070a00c0000780101c824006001d030303455010080c1d03954810080c80c0c0700c2180c2d4018802c80c0420018854100541d03446450403c44581c09210503541d8110725001194900030010780090600c0e0010070407900030203d400001082d00a042101c002c0c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 665561375 1250 665560125 665560153
    0x3040317070c15110d020304050c090903030c03160c0212010903020d0905132f030601080f090a14121318020307050a080403030603020a1409150a0303050309010b040507080702 77
    0x76840b00b1014008100c1c3d20402820006154404450074400d46480c40c54105a4840c9606030b8100315401d031003035000b01010b000581040545030364046c22070000fa40c51494451a004400d00014011030440480e4500320b05200b4012258036101540080030014504224503c4501900005208500500441c48201d0006016204170815600014880e04030410341c05031240c000c1c03034113414150840c0000204510034060703465294002c124003680070f9650b0b240101c0090641400540b1804055480104204c40c0007000b08040e80c5450344608047c860145a0a010345400410703040501d4001d400514100786440600340c02e002c44044040c40912016030007196012030104440b401d020038020032144041da071140a50683c810b1090500064494aa03008a040f4488581140032183e401c0c502048071490000710095020300c03101d101d03489504407140411001360302480000c052140100100710320355800c0d0000003a039080600100220314268200910031041929104098011214080b442e5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 665562625 1250 665561375 665561387
    0x7180902041b0c1511040303051b1209060304230c0405150105071e0506040c050102100902031b010c02100c1a070c080d0f05070206010f09090c091503080304031707 72
    0x1280302d407152200d10fa415200e04240150446412040a6a0300c03001074403e00000081c00213540a0740e160382d160a07100846c0c0b510045032130039070240e603448200c95858418190044900c40941550f489499444902d0100c0707002401c135480000001c2842040c401a840014640caa800703811101404240c1314030700b16141049254208a00017041005904040791f250071b15000c481541c00402d9865942d640c807014200301042c0da045800781d4080304100407d603410031100c0040180341004000200d40c680c000f0b9515a10710011200c03000713403a01014030310380c026031103080e0658010307008540d00c90303d64000908420760340204583d542ea4038a000d01c000d0ba240d82c1010320608040d11002075058103a1aa031103990404940d250000fa20382d0000914072806002d428016802d540040034503505000300308050f400d01e90410b42e104c0745000740700c2000c14649001002100c1050000203401c45a09820032940c0c001c540001d008648000180000c155200c815004078a010980d81c4090f61120b000850300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 665563875 1250 665562625 665562671
    0x60e061614070f14070b0708041a033303011503030f090e0604090611070308060126150109120804060e06072012160e07020609071202030718090204 65
    0x1211114020200014030804411400a02c51390890712103a030b580954080c2940000310803503244402180030810f900000604010a0f0480350f4401e0552a003071420400c101043c2c3c02030510301014020050700c1c4191201e0300c030400400500240820011001e410004d207003036100440010315090182e03038400e403040050100b601c4492505010503165070b010040a001c5441e0140c55183d607a50b40d00c41d05403004401060801d00c2516002101e1500000240030b102c0062400c0d1603182c01c85051091048c88202c00f540d0143c0d0295a01011002d4800101c40380d50301d40d00100c0c0401452181182405582c00282c011a15143e62302c2d00082841002e11006001e0208020304100309490580c43c5200803c00c0706c82c074903401902c03d0f041c24070b21010140c81c1c010300404c1d1010042e4844024801030f8085400d20741e014201d80010301050418091301603407902a44191460000c444582c00119034003440500c0c000c001e02035400700c1c1a03140c050800010403540e43d04034803403850503a644002e00b00d685c46500b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 665565125 1250 665563875 665563883
    0x1b1215060f041505210603070501030b10031d0f100605010c02091614030a0e10020a0801031b1a0c15090c04020d09020d12020f0f060112060e06161407 66
    0x401d1501d000c01103c00101e10000e04400d210742489448200f00350b0200034800340c0d0801c060516541801000c0c541008240e800039070400d800c110795240c042d01c0d000f00c0a8041c55051900092082042000200c3c041078040c80c0803c0340034102c2103c05d2118001440b500c034001e44101081080da03140015508403880040003900011000006290240e005e81c10b0440719203d400c050002c0d1032030842c6910641d008580f2503c10a40e5552407200f044420480004111a0350104601d01a0389003006450080148001000040c8244a010388140c0c1600203a008040c00501820101840c104090b0540c0190003100c401c3d104000720350140f4404104501d004a549002414403e5600307824000030350b11803180040d410f5220408200140c5503c2060103450f0b01442c00220806800c040003070818601c00300c2e20034980d1015004140844000c0760080c1155a4101c0100e640602d40c0381480c0074000303090400c940703030140e0780070440c0e044079641d0b182c03440c044103503580c088010f060002e1002c07500480c54050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 665566375 1250 665565125 665565127
    0x40506010b09190b03010f0605070503031503120d052211190512030d050624070f060c0e130c02281e020406060c0308040b1b1215060f 59
    0xe0460148010071140d0400f03451284602c031894045011441640d0010710b00032400001000028451228107010700164501289411000e48a0950300c0c0000341c070181400c280c3c001d0030307840c95504008030b103c3c207100224001d49400c07440502d8401040110f42c41c1220320b0402031008003120b12152104030199100d2046501e51030385400303000e0745d05911307005101715104107180411075541d1041d21541c0503040348000d55642a9080725402601c0d40034024500a001040b0000d803154510007619070f5495009400b142c4802c4030f42400c0868001d805001307480140b0b8155513920b2680e104882800c4541c090320301c0120a46d40c1034140040302c0c5404000001030b000340301e105070b4070344e4a02c041010101c0c1e40310680490643c140c07644c0ca0003103402c035501408544195543c000b181000d00909001b40041c0c2410411440c59440c040e150060060000300112140000030b50700c0c0304503030341c01b500c10071056041584032418404c0c1c1a550703007001d43e01034005480f8000d1465051800004807188400300203012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 665567625 1250 665566375 665566379
    0x904022101081f0b1f0905120619090203030a0c02011701170d020c010e0904060e0f0f070f030b0403050c0f06010b121f030f0305091903060506040c2309130903020f0604050601 77
    0x14002c0b41c40510071750f08200c41c500000036203565059400500403501c4001d01a20305101e440c80401c0d84820240303013001420051441c2c0582d50100681d06c0d40099400e01152002d210b02c01201c40247d142d0850403400303880b400100b1005240046001989100002ca501e051450b54003079a4a40361034101a000410747c4407004214240028420b41003482084003041078440d07441040d08040e01815040d40d59405101b641c9000c500c1006200018003804070141e003602d08545070307062a10f2005002030184800082d64400703d010412a006c0e50003898000d460481d619000c00c0d80641d480580c0512031140078070b02107103001c0c2d000149807c8050385d045c121144d080c910b9030740080b416040d500030350611400f1f010035805501e0361100070700240700c94051003569074194a09001220b80c0070342031a0090b403400c4924980c0741d8000c4846080c1c5110600b80164404054842200138071502e5180e0f40c12100313150102c107000c0c5480d000821f0040c03003a003d03a05007182c0004681e54402c0b0440b07029095500c00c2c801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 665568875 1250 665567625 665567659
    0x31a18070e0f0a151203030b0901061e0804030e0d110a060e12030424051e3402011404050a0906030627020405040c030b040c0e010b0903030904022101081f0b 69
    0xa9450800c6c03003411701040103505180019922002640010040b403180341444904181c80d50781c10411006605016280342084c1c2c900511107410110f00b00d006d222010548001e01c010000f5081c2400da005217040e0301d0540343e20b8010030b90200c10a9440c01009824803a0406034008402e07102502d01000310442d0800002c40d40301043e0703001400c5082801020041d080001c840c814100441510f0301300950340d02c82e6410590814220811400c0390407240c10b0760101e2000c400b0300300b0038003031703d03024640200401e043c0b80d080c40c0184200c1d40125031220040c03c1c0014203c42e5600305804603801444100304000b51035140010341c506004210402c4100c000c0080010f02c0c16912a54105008580da00d400940301c2c2d680591000c1d00303580640c0c0c003441781181044103d140c0140e890240404004030b6050a001902103966030144400c03d61040c2d03000314007150b00811180c038a944142c84101e8500c680e594403251261190b034240750040f041d5000c0310b0507402c1081c0c103001d071018840c406003204e0710b40d610220b9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 665570125 1250 665568875 665568899
    0x8010204030312110909040602070b06040204060e0906031e061006050a0c260304060e2505040f0e07030c0f1509170f010e07060315031a18070e0f0a15 66
    0x50001380188140f01912440d1140014030340318512034540160342e1906810243c071500c80c02000c02d4803941c0104024490164850299044410b00f580d4a07401c2e81c07907900c002410a0240c0340e0703854000fa048020301714000c200080c1513000d02e114002c0e042034a07450f540100c8881c4250003403040452030744800080003c110207000074032203030111101e00000e0b6904030f038184a42d100783d606803000c68448213080300120301440084946100340203c080440c1e038a41111101d120750744602072003581c0d16804000c4c00344088d008080c0c120600301c1500d01045d22481c000300652000c1c01002c00da042d480b000482c140c0caa03400d41c1e4419188644a416905103005546002e25140d0002c4240318020300c814030a01010902a80603d40340c05406003140d10306001c1d00604072040345d60072505c8001c020408001060f00340c2c1d11b0365410354802d072401020f076503507012001c1030a000c2e141244041c0700711b04001526001480807070307029881000202d9a1074a8a0040200703460701e11200f055140d0f00f01d1010401d01c201c0c0c0d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 665571375 1250 665570125 665570141
    0x5040c0608071e0914090f1302040b0a0e070f0e0d020f01020102071a06030f06061305061c050a0c050904020a0611011401092013060c140f0f01050108010204030312 72
    0xc584002c0c20707000f102c048040c42041070f141c0c034040b80c0c9a01050040c035007052800d000018003034880f4000d43c50140310042c0c40070000b038104036102904c1450303e025516260000400b80718060a810b050640d248c40c1c428011004480d1200019820100021007610580381e0207014280103100c206102c89070707020000840d941c10b0707156065650801030400082c5001001c8555811803201d458110b2070301a0905040c100c2c08203803008150070003070402415070740e0042c020580014600f00040d01f540c0c1e05000c120803507c1202903039079402903001c0000c03c00900069040426100714011440240d0f14000d019031110207030f034001d40c0038080c441d003480058800d01c21050700f0001a400810750700100380d10751040b220b080e0424000755032110305408002101528a04280551a0b8400d1038826907505001404c12640680c101b0000741c4140d05061180e006001420200a0341c19568500c400c42c028907504c012114440c3e41550030303c400015880810b2082e10210394050715801f48840482000400400c081 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 665572625 1250 665571375 665571377
    0x8030a080f25031e0c0306150815210a0606060905180a110c0c04150303050d09050304170a0c0e090307081635040f12140105151305040c060807 63
    0x104c503000e82c1e003000207411101c040c0300d000c800907450800010080648203550850042d14808000300700c0e00c0c5a00140c0c80d80c0c003049140035034111101c0180050400d107114080121184c0d8400b030000ca200314041000503515101e42c1c030821209548290584884156204042e0700800c10610b8510310b4001e4400c0355440400541d00044189a510301b420541d0007890380681241d01103080c21244d0700b40b5106103043c12000c1241c41c4130b12403456070002c02030f22600c5540d0080f192500700745010494100b081d1000fa00781c0569005124840c2894540d4074078002c1000c3d28203c071840000244441c00000f414000c6060401840c1340c102c1079214100e07035038400d40305203c14921035464000403512100740710000c3c443c0d00c40d03a00d42c00403482003146681c0d034081082d42e51000b82000200030020b907183c031110444a101410303505041040c01d1501104150000b4114194205020041c1380005620900c1090074101c03842c2015070090514401140c20841d401880c1c1c08902d501804114014040180d0040b0a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 665573875 1250 665572625 665572631
    0xc120c02010905070b1c0218060a020a020d080705060601090308030c0705190606180b0a0302040f0f0609020306101704020108090f1002040e011e09150506030108030a080f2503 77
    0x742d40e51619103104c1ea80071102100b808680300c44001000c99842c40c0407403600d2410350a100080c0c00320000380c01c22000e183c0c802d0200049810312140248039108941d9001000c0d071010041c0750401e80b80303503400100103c1d441d004041c0011425805000d810085d240c00100da14190350315181c074104075601c20b0790242c0d0300b84110b41c04001c5101c2c2c2e10406604039031140c00c0100740c1c0340c580001404100148000281170604111901105443d40350038041140d0b0121008100104e41a47c154010044402250080b42c1031110114280d00160000d6000b4201501c03038503410041781c2412100c075082c40700785009400c1498042000740d0300c12000c0d1034205c0b407458180e0b45580c0015442d249020150200d41e8800ca401081c2007101291a08007030380141781301d1004246451f40c41070f00041d103820320300880300c0d0aa900c00c0c40c40600e400001202c00603001c040d1005969585030004155260801170303410340000d0050000800c0c05224484c1035004080044400c41c02003500d040000840800f14103c408140d9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 665575125 1250 665573875 665573891
    0xa021504091a010206090a050a030309030509030d031d071d0603030c030307030b0301051b1b030f210105040e0a0602091309112e0e0d080c0303190c120c0201 69
    0x115110b0041d8010103418003000340298040003a0030a0802401d86200b608129260000f02d6404652015002d41c14a40044c80d03181c0b624095545004008241e601842004482490b517034269002c04d44030744044020000300860401c0c41756070f58519020344241c2c109007036140e02d0700d407100c2f20049820410050980342003800e00d0703002514681085404900194031010031085608080c4210740c0c10150f10394802c0c00340080d003201100c0602c9030011144030301201c00328480b207604080c01a1000d151070b07a42110f07594401e0369840b1551607125607032041c101c00b0101c00022140381034451840c0131900c0038040d01d10410181c8815000b500100b42580d000310409501e00000d181c18807600c04e44074440c84680b40404041000c0c031003d0b0026840889201e5880d6240400701d4028402d00a22401a8034000250b440a2008207000e005010401026400d0229802c40080c4000c0095441510041210070b910302814244134280c40495280401142007180064565003590300103525001440c000820010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 665576375 1250 665575125 665575139
    0x1d0a0818060f0d05070e060714120406030f050606040f1e05060d090302012301090c02030c0703080415020c0f0d020418060b0f0a0509010519172404050a021504 70
    0xa4040710044080340301c001142055290613108464006030740b4940405210801404a2181c1c4525000513040c09a1020078a0000c2c07010480601d001e03448000040c1c55591b1070201030301420400d402051040e092000080c0281040030644044440403140c11038601c1c94804c103115640481145400e0384500004081419202d95006207100c8140260005001c81b407401c009013110058450082c4c14121003000026480b0000131560654051903c0007030036940d007070780583c51071194091125442c0030b02e000000602400c40e001d00221000e140d0381038811b070b9a85000300e840b0103000d061654032600dc4012480d043c00d100022248081c4080c000081c4604224080c0303901e005080d404444103a120362143d48241400e18040c9103020082d200c180c8040e0404001818218050040341e0103007061060034202c0000c3c560010000300602340c2640152444010032035100c01c00d1180c01c0074000154801000320b5404040000d01c2141c102019000200740c95082140c000020b201e802800035050002007640c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 665577625 1250 665576375 665576377
    0x40b040c2619020f1b24060d060b0616050106050103110a05040e060112090c060e010309020f090a09080a0e0f011d0118080d0804110301140f06190b070203011d0a081806 74
    0x1000401e4010010b0b040000324255008040d20004a1b0440000040c041c068403000c014100b52a800a0041740c16105040400d45a020343e40985440c0c00c105440d103418420198050400d8032004e0360203102d041582d0820501c0c51182c00419400100300b00401c001e10500c642c07009030800e03030516000d2058500198a40192040342d48261040d46020740304014150300700341d18204c01842820b051100005580006280e0840c0c111428020844800020b49100060303020030441680011815168410010001d00d0305000101d00c5002c1d00c0b010584603190340c05440c8003000c4032500f664540c020b0b00124011500e0001c100c0c40c0e80411480c40380042016101800f51007560152544c0b80006407a1a08121040c01c06c0c4601160007a4942001c030f402062941d0009681b04400d007170004070546408000c80c80f141076500d10810a0900000045251000b44d03009002040c000c90007403100403c030310940c2414040c02e01400030707079601c943c910800080480024020240c1d101072180402080c1101003011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 665578875 1250 665577625 665577667
    0x204060f06050307080601020d0504090b03071d09010501120c060c11030609010c0207140307120c032027060d030c0804090606020706020109030203090906040b040c2619020f 76
    0xb05030048204403100781e1000042d40d006d84248000c2c101c042d803016018120744614020048002d4807220314592548003000100010035550301c1d000d400800c043c0099000d460b0035160840c255080400015211216506225281d508451030394525032401b40140c81c8082c40641c21108200380e0044607039980c2d030511400d13200d80c3d003641c00030814030f490040090400b5115000456011143d100100d520703100041c240e400d5a0311441c2400103050315003000c465001582d403000748180b9100490505070501c403c00e40b03845c4102507600400180d1701c041010102620400a03240c2e021100e00081e000e8030f40b14000034102800790510803c420b00303640350284560704c16044801c809072140e004212040c0c1c1082100d000308501d20080250400564000b9140e214030120244203035030345400314000f50f840d9845031132041d40007481009030110180b00500392400031541320070315071000306c0c40042c0750b9172030800070303110310f0104403031407086200d1401e4040290011041040500c409004600b190700d05c0c603665400f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 665580125 1250 665578875 665578877
    0x1005070e04020d1d21030405060103031112070614010e0f07050d140f0610230a030e06070f1b032f0a0305121012110102030f28020705010c0f0204060f06 67
    0xf19420210002180c224130b05015017041c96010000c00c40810004075a07241500d50514026400080d0303035659030300e410802c1c41303050341c8010000350102c10015a07921420729241d07800f0010307600baa44c0d43c0c4035924056048400c0c2038243d00180000d01214400d03c001c10300c4114601e000950a902d0740b4030f6a0441c0d104039146210030a006c2c0138000189040661401c8100a07403501d02c8000300d8620030b80090b8044402080015003020034800c4040b0701079005070f01c0e040550412104a4601410000d150200c030381c8041c0d0100e9918007a0200d034a40243c69040c0b2180c05072900d0150194124110804041582c04801c4410091307081100151083c0040e044540c0282c9d500e41d1114090019048140e0000d0a04070410022040c2008101c803280051070b001034005104258010b10300740180c3c15441001103070030a01c080000c40d90071b403210320044030b068448500040c04866107011001c0c3e998414900426000c14180c0d00444001041001d005800c80d101074030105400707660358000d002c1e1141d1500850 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 665581375 1250 665580125 665580133
    0x103090203252103020d11031c2906041806171c0302040e010e13060f0606120905030f07060f0911010f0c0c060f0504081605031005070e04020d1d 64
    0x32428200400c0c1108241e40f6840d0005031030356600a551510031070312a0041c4911f6040b01c00800c4024001d4072410000301c41008062840c3e201c03a80d00915150142c400400b401d043e83d1421400c0110450f91064409080c03a0f240c82e040441518000c1480ca481031005074550002048200400f03400b0512041004010b00136410f4611f4407030707000604401d82c3c508140c0b044c0310800c038041c42d003880181107603140090080c4a4540108000301c1150440d0060a8a0300b00340038107111035141d070f000d84203c5640d503440e1414002075981180a07a841c164025142c0d500500c21140b0080c0711200401802c0c1c40b4041c0003444000080a55003a81c40400054a046020412515043d41c01c20402c1042d4480c130320701a034168480b0303a2500380312407850041008101c030f0b050150318000d00400440c0c010f882e15401700d801030b40c10417179000c40124607402442d0003405500340e509000d00b0580554bc0c054080b94989800c04150001440025040b003071400c4000d0741c4400310308a09902d03a0044100340e82c5004064 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 665582625 1250 665581375 665581379
    0x120a0b0a020c0705040903051201080706090803030907060f0504030501090f0201030f02091003020c01150b090a0f0b031b120f04060612020d1e080313150501050609010309020325 78
    0x50015140050604190500400881d400b4801c049050400e8800440d00054403072528102225240508031f0112000c0240d4000807640110016116007220004d54603203600d162114002600c2c0d000a9030b000d440d9510070002404140c1c05010901c010302d903a0f2503c0c0741815a2501c545003540c0d0328441c19a4031003800042e8000350b591600a180309107000d088207600d000300000c082140900c1140c03104040607070100701c503000100290130030046968020a500419070303c03080e4001c02c550007189000d02c1500c2c8030700001401c2c0d0401e250402154007110001e410340d540e41c001e00381d104803030b070950361103080040012030050310207000c1d480d01503e200c039049206403034685019070171a24282c0051140035024114000181d817207159018440d40c1c040d9451002c3c1f0840c0003c11500ca000410082140d10080700300107400203908405043c01c1c0c0110010b406201201c403a5a003114000c1c0101030300103a04200e85e01455001c0e4101c0d4084901c00f804440c04944000c0340040e203982c44461030700400340b0154017 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 665583875 1250 665582625 665582633
    0xa171204060f09150c030c060f0e0c0f01030b01090b0d0f1a04060e1b0d0608060c12070810030b100911090f060301060e090a02040b0310030302160e070e060405120a 72
    0x20319000b820303c624007503100d4100f204000d0864022008000c0030040000311450070423109421000900034035000501c000300c0400340e280c1d1551900e0200c903026003c500302c04c4d0b083c0d610074012003a14020685807141058140480d6a0b00740e4014070100b000d10303458034660340b240f0f4818419030340755016182050020b01d107850100001d0307980940c807805490034120140123a1003c0d54400040e40900344040c19600e549104402000c2c1c041980500741d030380902001c011411040e4030090900652040c500d0f5219696544c056400810550310403100c40ca83d150140005501140f2494110812904090405a65a410f041038491403260304c1a015004640150303076051400340681102ca013101c0007421581808401031080380445582c17131140002c1400300740e0320325455045078080d1260301c1800d5a6031400848c40c922006051008070010b101d000d2408183c2060784d036100c0260303242030520004585401a084621f11030010400c0d602010420001416981d18400288103c0501c4040c050100301414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 665585125 1250 665583875 665583887
    0xa020913051602070303020d180503060906100e010e011a0c01060b0409062108070c0b0d0212091c051b07090e010c0f14160227090c0a171204060f 64
    0x20802c001c0d948414020310010350046002140140146411038010090850090401740998003c5801d80240014850156808501c0c00d1040e4003104550385c480b542c030f031900d02d2404024451004110100c80c018400102c005071160140c44500d1001400d2a04045c559421500c080c0d00050705244002002c2080c032200d07005110041541503001c0d80886080c0340b000d000700c00d520380f0040207108001900c00401000401c44406001044101030b241c603050107139030000b0351106e4a09081010b450000032202000010240464130310b50281034295045140150364503003007440d608441c070750304004c041e5841c1d10800c241d4000301030641c00420b03900c10352440d01d030031603030300d4800403040000d084006110260801c084642c44d80d0300010990b999a03916528039901c000c1900000e42c00340300e00d80500301405144003036421840350503c448802d610b84901d800e607242001d081c004d400c21103240e810080d01140002e254040e11500013910150704841c1440580c69015800c01c0c800320710012404c454841e4408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 665586375 1250 665585125 665585161
    0x9030d0806041b0c02090601030608030f030417040803220b0d1505030106050603011a12040602120708011d04060608030a0c03140906031915140324040b0a02091305 72
    0x280010f5035200c02540041010301e6484010740920714450105926903ca51b02c20720042c01e0304011780c0d44900700801c2034051640203403019201c0960341e010b00c03112072041c4c03c2141c08880340c5034011850b00d04007400c46102c020882804445151400c0c2d0000f45c1110700c040101064802c140340002c00c0c2200581075001e04420360000d9019a01d0100180721a032103e40440303040d10f064407403c2c1c0d100c01c4c580c243c030700503442540300c5650003a0704035082c0700c10000c450b0003910101100d0b0031f111602d55229001194440000d108000307a01c00342c1c101c111a1020711a450130740117401964040b9a09480b050f140e442c50b4481c00d1004001260803210b801815400403414401c01c00881c07049180c0120400001d80b180006083c4000c2c03800c00440c0d01142802a50007107410b101c1c22581c820505507a07040d0303c81c0e45402c54501750300902a8a80e11220218004102e02203204220488072554480b030325510380c40c08008200b00c840302e40c200201c1c0b01076510148407500c06000300320041601d16003260741201c024200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 665587625 1250 665586375 665586401
    0x20418020901051b071a0306010f11070504020706270c060309020609040209010e150d38030a0b04110111010e071a0d090605180a0b06040f0209030d080604 68
    0x14025807129a03802021a0341380c914420300ca01c02201000442d0707003040c0803507000a9507110003c2901d078145480d003010714030074038090322070b04140079420b070042c0c1d00725000f0104c004480c0c000ea4424000e501d4154040c0c40242e020741d600040e4018403403580584080702c0309202c268074141c2021982000301780740c030803000741090b46020b00100d21785038040340303503030003a014103611868010510901c6644202041d586016009200d1600000e02c101d143d2403541c0702782d926101c4942004454026801e106c0006c00d070030509800c589031041170241410806041c07107060701d41d144c040d180014001c50601007400d40158018120b9420b10303a0b001002620084403c0406091030341445040c1401c0317100403503010200e41c2c5501401c403e0400c03041c40f05189106807061501140e2502d0b103003005000c1c481e40b000f481140303009200c0311003450485506950340c00c02132005041401e0000050300c2400d20780c200500b06440c2c0c0c0070140c00c01c4c0f104400130703040070400046980081d0403041004841e02c0c0c680910507136a1a1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 665588875 1250 665587625 665587627
    0xc0705031e0316060219030c0207051c0f05120d0f0c0801030b13030e1008060a050d0f201c050d081501030506030f0601030c150807080f060d060f02041802 68
    0x1c418541a203c1c0140900d462842e010b4441040900019404580d004101c1b604001c040e164034079005001490f41d0310312500140714443c40801d44e0700f41030645406c4081060308920b5a207a56030f0394000c1d400c064400c111490f009009071b90086d54072440c003030015178000d8040803030f040799501c9114045039550000c2030200640c0030010004111041c0f6140e401416620b202611414a810142d4161440c48406a0400c5d100d6036034005441c2d0040c0000e0040b0707001c0720003c1002d6a50000c11822000105015001d01040440e00380000d050b0b010310f900502240c4404000c001c1002d00091030001d003008941e0f2400c0340307125144100b00741030020040502c1242071651082c201045000b514204404485040c1a540c10105c1d00c00c4c2c2e0100940ca0b8546200300c21500650703140d1901c0e01000040d072160070f902c10400c1511501840c050340d02d00d4454501d40da5125095603c0c2e410503544010302803c00c03a009420400020085001405200301d8061003000140c0e40e98900b1a10b040384120b003105020302d6030700c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 665590125 1250 665588875 665588923
    0x316021203070507031403180601080a031b050705150a0e0109150509060409060906061707020325050a0302010605030c040e03030f07120c090302130b01020d0807050f0c070503 77
    0x40304003980c1c2c2041c5140f070034580b54080c42c5825516100010781134800040040100f211034146011982d6035050f402060b1240b590b40c0760809030f0384081c0248000c02003100002142c444402c00301d04456201d001d44100c4001c680c0e124003107240d00c021180040e115080018044e0b0386150007030140a040f030820704e01f80203198902940e40140780f01022660040100000b40a5469070724034065030042c20030684200501a03441c5400d10040c034041c0301c1c00010444082c042e8155103024050148502010f80255141682e6515486040001a00400c0420200300202d40c085441002918a4244a40c00002c1c42c14106010186060420403400d88100d04022484084110100503250042e4040c00408155150184151100201c5000b0200003525240440c031540d60b026250900320390007900d0492100420264190964100061142c00744e40300500c8034001603c07480606620814900d045400c04503000200c040a40c4a130000307012607805001c0a010703501d0180812100b0180019403410100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 665591375 1250 665590125 665590153
    0x52701050f1f0314011104080706080c04030b0a0c12020705010506120a051213030807030507150501150806011b0507170f0616090e011206052202150403120203031602 73
    0x2c28000142410906030400310308038025000740002d5400c101d5400d496035210803030113680d01040d101c1d65002810b900c000c01c83c0b451140003242c0a598015450501c9070b51441c1903100582620801082080320400d000d400c540050b01c06051840d22410001c036035818100d0411010075010386206103190480011000010f0000038071465600e0034030700c0706032103007043c401202c40c6054a83c80039041e00c03000100c4008165101006010b110300c0341d52044280c405048aa07004c0b00c100340101c41880c942540d41180480c010410325522000500d0110054101809200345601c90300d0300403941e951281106000031a0303204010700400301c020340200b4085010b215110303603800c4090550906074240e40000d00a0038415601203004e02000d04180616581d59083c0b105102c510f044185c40142c034000c0030bd4100c004212105482c0d442d860f03c0e0f04145940c1d0380070011000300b8007800102e01c0e41308000000001d5082400c01441100503005561646801c00d44600d495030307030050071801c64106c100000140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 665592625 1250 665591375 665591431
    0x110601061103180a0b0a0207030c0b031b0c07030c0b040914060d200301060e15010908070612090b07020d080f0106140d0e070b0309010b0105031504052701050f 70
    0xf00114801d0030343e080044041550141c0e44d401002c00c1030301c000303a40441c803a0006030b5231040ba0300c01d00c282d0800c40e545010f500d90718001a140000d80300c41400145400d2101b102c06490004c4085003510581035a036a2803185480d407e9000519444010408000b12a0507224484020700034500e001220316081c8001010030540d000002c3c00740054543c0381441600b00200c8101d0608054000c101241d250114182000012180b054800c0102c1103c010369510842044040b141140c008002860a04109950130b141e800c0401c40c0042c0e94242c14070101d50541c64050203408150050481400750300c1c0d000303080d150000c1008921180b03200040069591111480e0f041c1482d05010540b0b942102c51814041c0c43c503013050218511441c2c6001c20040306070001103014509104c0204000c0c6054401510180021503079100361402103142901c01c0d040036001f2950050b400b80150365142841c1d1442003007540014100780035a0b650300200603170503070410309040d005440f50f080d0388032000c80d000d111005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 665593875 1250 665592625 665592637
    0xe031c091a030a0c0909090b0604060b130b18040617120c1203040f0f0615091103130501021b03180901120212190302030306150910050906040510110601061103 70
    0x3d010783d1203085903403240c440d81c0341e8405008804401d00000d42a030900345002d0b41c081c3c6a0b00e20443c030b8508009104400901251001070548401d2481d184c81c20141d011503401c060701c0366800a85100d10b01d00907503628400c10000e010a00100300184281d060218540000e00c00c801c1c541b1401081458400c00c4006080c0359141c2c0c08203203160baa039a461922115410710b6001c0240210022140b81041007000d800c1400c011049820800e80565a11852000c1d02c1e148264048018010030218440c0700611034100c021034040c00005d4a01080201c081300070840560405626400200320b9502c840780041d80e07040510b404958400055043c01407001c0310f00fa017114001e101d00c1e050744180300e101c60144640031000b031000800c0d00011402e410065184e82c021500c480c840d5507440300787c000c611415410750b500d880c0040c2c0082482030464030183e40341d901414600d41e100b6400d200c0050f060761500f40c000e503203090030740e074a048038040301c20f41070310709072060b0844d03001d1000801604607040c8000007500c403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 665595125 1250 665593875 665593891
    0xb0403080d0203040c031a1824150604030b1b0f030a050709090c02010c0e030a03090b0d110412021c03022e020c010b0909070b090607030e031c091a03 66
    0x60342c0d4440b454080c03c1042c0c5c0c0c3d48000c004000d0000280c03038800e21080c101d44a02c070407050240e100400d0340d801ca91140d0a41031080780744483c6442d8202d042d0001d50340b40340e0200901e01e61000031000f00c1e0004d980d0b0340040d84120350310f035010070402046042070342c06c00d0b1261102c11f180a040803c1558a07400702d0100801d280c005a9a5800149402d4070a114800042050400400c0b50062040000740606801c946220200d03854500c0100c6038140002c040301d80e103030191780e01e110940c2081e60505641d404600d50152071500d03002c8043d0b10b409030030300034002032807211203244c20041144103001612280c0214001600c803845100b2002c0b0750041501c6e45800302045071407010446060140d107428800b008024495407003c01c045150080551002da2070030011103154000b9238512403a02da5a40450089100595041c410b400340f82c10884050200c040c86400e1550031250b03e10046403030304494114458289889540b0020440d402150150241050320300d000380406084288029a100203880d81c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 665596375 1250 665595125 665595127
    0x30c19020f031c0f0c050c01151a0306030f0303240108090c01050d0212010e041b030309030b070e03160609080c150d141905010b070b160207081e01060b0403080d02 72
    0x3c807007981c6580650180c80d51300000b009200c41a80f00107046801c510701c2610039602c3c2c01d40c1003850110140c902800c130f410704048031030000e1590715203102e207420190405802d40f20b03d0046c244040e20500c09184100c40600a00c0814401c1c240115245105041c0f03090600a00005200b00d41c074004c0b504242007030081c00e02c41d941c0e041700300c2c6800003480f616480c4802010900c00105415001440031070080b0300540c1c0c42125032030041106c1712051020700c40100420b840010800c0000d00e20050341d680a851401c0880104d1002c40c0401d00313001d8810311300c80c440c0c1d0021406001d016041000da0000d000020001e01c40200040041880c030354201c02c2c0c5406001c1c000c1803034200071545400011089014400d40e01c40d90400c138080600843c20140d400090b682400d00120384a00341e0015100c3c03040c1c1091280c601500c44904918086980030911800c501a0050114410104001c8054003842802004041c41207405501c0e00b103500a030030541c00c0d4681007008201041e030070b006803004521012401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 665597625 1250 665596375 665596417
    0xc011b050702100e03010e1b1819020702060d0c1103032205010e03040e04060c0203090f0105131a180901050f060c070e01060504060e090c180102010f02030c19020f03 73
    0xc4c2d03480122440d20b580c0c15800d10a50b800c031400007081c0c180d495038a001120031400f0307210041044c804520100e1384002c81260b40020444a0050225004148903a000610f412a59008241070341d112410164405071074182015099620a03012059040380360043d46c1541001481c8454083c0d110000c203c0c0041005003950602c071003036024030800790f080303000c580d511550f8107002c0f8000c0504441c191542850100185240c1e80040111101007030010890981c282a50006441c5608510100e03034850941d20f90200d1511031a2400403005011241080c0e140c40c01c0c0d074503541100000c4c5091a0040d4007401c010072090311810200180c20f0b00c1107581e55101c0082d4000107142500d580c0c050b0880100c244000100700b60803c0092050340d17000d42d00e03101400209014001c6a00c415600d2420000c0c0800134107107038003985041c0201d8444148004284000031090031011b0341c00c19280c00281c1040050192502c1c01f03199500305460b441d0b070020b483d011070000c1c1215142c1c05000e500400080d003160712 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 665598875 1250 665597625 665597627
    0x602270a05130f0e0a030804050d111002181917030c0a0f0812040b071d01090603150e181513060c09051801030b0c1c0209060909010b0c011b05070210 66
    0x40c1380070310000b10841e86845103504000b020410140c40130348050091000105072076102301c00c142c00d62a800c41c0140422980413034144000d40c42858451070320705800782400d8159903100004544210414215842e0a04005800400a05803040505198010066214000c001141a510302c41e00000c003121200f00701e0904024520490760850a85450034003080b080248884440b8002d244654072000a1141001d0400d075030311035041c5031800704005800402007688203402001c010a0f06450409400f40e44013001d240d41c0320161912403100c2d60102c0e05010301c01e020840703c248032000c1508011141040e047c2c450302454120006442d80b6240d62500040d0740c00741c03404100402015241c540c1d184816400c60019280a01040342c0c3c1c2d8000304081520f42c20800d0580d2a002404001d2042488501170144e001f9030205521030b0f002041400551010303950b003400203000300348924006947c0d070314441d40c541c2103456481c0d6140162106040100c00503600209a90303003d903049d60072031a01e07821200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 665600125 1250 665598875 665598881
    0x7030c0b070c1a0a11040e040b09031b0106080d08060109060302070503070f050604121107120c050d08040602070603051005040f0e24010b0403030206040b130602270a05130f 76
    0x4003900075900480b00d442e556042c0030071a81300e0380f4104000c0104007015840e450751482288281c038161100c48000c42c0200300d84610b12a005031000c400c4a00e058030304500c901ca11a80030758920416551114200500d4a050004610071500c03403814005a150010010300206002d01441c000c00d5404035500d02045070070000c8401442d005068241c0140d102c0c6003469645004882c22250316845842c10064180100c8255030236400b0b882c05010102e043c9612142d800c0110f40d8103590000394440e000406440d04005555418059042c007a681e0703040060292412865030f0008041510b040f04000c2d140032040c04072002d031002241c000c200c42081211000250459203031a031610b00881b928048130152401e50b15401c424100e01c41c00150b0303a00c0c00c4915060003070384070107405600144001400924144101580b0200d001c0c40e586184d0500d40b0b441c4100d0700104202d4104800e03403c10590f402c00d10075120a4012002c464180d100b174240f40100c2c9401d01660061000261900402519420150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 665601375 1250 665600125 665600147
    0xe0601090c0207290f1c1103060126040308040314160f0f1505010f08010b0f0910150804060513020f1003060e0a02030708010819120507060c0201050a0c020307030c0b07 74
    0x8004d098541560300707080c401c594000004211b90301c1d04131800340c120351800d00a05100401e2050b10034210350b60f07040191a09150402128919604072452005000c030740302201d8000c60183d9200329161411f483d002e07004501000300c1445c60003085c0001014090f06640c00134000c1d1344006451900c1011345031072200c0d43d008080050229940003618060700101d81e00c0070381260f11010b084440580d460f07000034200c40c400d0980700e4019500840021080c00c0800d6160381000000c4103408215690324405400048100c42c0030b0b00045428003480140500d41c01043d0301306402c0c080e511200312141d4005015a050040c000e80101032443c3c1744400d803806640504000c140e481d90700c0b42e00f80350070882c00b802940100d400501142503c400480c0084002411440c140c0166000b0090420303c1e4907a2119110800c0c4003d0030440c08010301c80c0094980e000e05404050035400203c0d10b400e04109540541d0242d41e2480c085500070b0010740c000c01d90120f050381182d600800c010113903485074001103440584d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 665602625 1250 665601375 665601449
    0xe16120509010e07050a0b0906090604050a06051306031404022b14010509010b060d1e11130b0a02030a0503131a150405010f0b16060501090e0601090c0207 68
    0x5080109000041d00014180f0440d01c0548508070740b0362081000c4600503008150640c1c00030701c019007050405030000c10715050020001810305503210001022103116030440400247c02150b5070b41d16021400c6d002e4040c01c05420144030500300040400161a00184007038810010028210501c0c2840001206520310a140106a0f00302a0801078515500b03058845031301d6180200007421034038188202441b0581c010071551174203450301141c0000d0846100e004611350f00840d00e103990850f041c41030260030000410003584400d47c82c0f00d07481003a102a40503030080f031402c020040145a0100407920543d940341051604c03130300c07010700060941a11074402004071100003481078102c020101240d100b654121007450385145498148030030740700c0a01c2003034100a6019800d0103030380f1000d0041d049512a000f0092620600c0340c680400342d40d000c1c0d22802001d5a00c000820380007030240505405001d0004080c01a0b10a00c803009554081600c29061100b68800c8408440390190201000207102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 665603875 1250 665602625 665602631
    0x31214190b03161d09060402120705030604030306081516031505030f01090b0a110a0e040212040b01050a050103020f1605070b0d0507080601030902010f030c03060801230609010e1612 80
    0x200c101d080c412402ca0303020324107011040c850000546160340310224805c07a00324004d03011540b901d1b403d0101410348031803501114024010b010070561820004988141d000f44d07000304015103012071440c20090034030702e01c1170540c460f641080786000c04d0700701030501e03081356203000512100540b030b803002c141480340c01c90b035410300417032111b1440501c054000f01c004a00032608074086440f50080441200c58184402c00c1d124018001d064226015100d5010f5003040580090316242103a00381980c203260490301210710b1418800140000e0410880c0d00010303003c20301b4118900480e10590614600070200c0860302d1460740741001c82044000e01821000303010340d03c0c140ea2110410340712070b00900303c200d40720400950310b800000c0456100b40210408150103845000240d1104502100035013030880c0400285611070b480010f441d60244255500c52510840c807640301e0202984503508103002400413031049003d1401441701c9180a43c03141e41026000c15480702c040b004110075504141a0407504c401c0ba86 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 665605125 1250 665603875 665603893
    0x114060903071805010510022104170f010e0a080306060a090e090a02190e150f12031e030f0f0703090c03031d0301020f2505060112031214190b03 64
    0x4559200d041d695030f1805820310250380c0f40c030f00b4442d44a1503d52030740010b078050302190032248180142150a1502500e0302c51505448000004184007a41410442c5600a030304007041040284585036540703520074042d00d1622410b4907190440e000140100b40700d441c0c0006d4800d0f910b80a250150700502c0e0104010840b880c03c58060b580712035042d82c0c01d038041d01c03229051814010b4a40d00c20030940394020313611069901c58440090840c4660000d054020b000340c421404240e450442485c1013010305801166120060110f07120f00340709414074000303c03031002d1041c00401c00c80300c009581d2001c168981003d056aa046003103001e0248000040c12400e00800c001c418554440c0001c4803a0000c48030600e02c2c41c0503102803500300c6c0701d03020400f2126401481411110034a02000340710329010003c0c4600d20304402d444aa0814000b030f884000005003050401d0b0406070045090070040e84134400400040401c900c055807580d800812001c2041e02c40e05140c03908042950000000030000f8007129400c0c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 665606375 1250 665605125 665605139
    0x30e03090301062c040308070503070c05120a09080303101208040f03081b0d02071203051b1e1b0112021603201c05031008060a0204061115011406090307 67
    0x1c910300542115044489030041c480c139010036803030184d80e155803109150764814004452541025001004100241c254a0b000c074500b04106075006590b5910140e1301d90032000040d21800a980c4240351a0b00140100040803442040110071500c0e41001d01042541a140200c8240700d141c001e0035600031581c0001c410b004c10140a45007056075401c010f1070a00d940fa080030790b074030b100300c9414006034454401848400c400c0c0c06400c108038800c0c00c1250516035403440c2c05c082081c0700c0c5807112080e88110189481c0d182c03420242c107103510001001e800450b012680359229514840b80340c6040c001c00050903200150594100d5001101001c0d1840f00d1940c40e1400422200302c030241e01c850085403200d452031504001c90348224031003008100004e44241e000c01a100c42d00028200c3c0040000340b0380024415101340001c078801c0400b0725005944500300312000c3c20004941101c40400d5004c4119910741d09114600f071410764150031070644003a40d034100010024800c01c4036a540500070000001010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 665607625 1250 665606375 665606399
    0xf0405160b13060203090d021212030c0d060b03040507142803051204141c1b060f08161d0a0e040204060e07020a11010e100807030e07060c03030e0309030106 69
    0x41c0305107070110100543c0c0e0315000c90b521b000b40317100030b94000102e0703100e28014900250307000f43da101507005480040d42000d4054403142c0044a10015003d80007446181414039442458003400c0844c007039174110300305034484a41e90346207401001c0354150f03812070a07201946c41380d42140c1100c21210604144914017010f03252560403500c8200c803140300c0e4081e9402c0e00402001030f5020384680364034955054102ca02042180800000d40c00000e9010350484030120b004c1e5400c100b07113020700b40c024007001480c5c03002c01848401c03640c20308001c221600c4144001024000810b080042c690310344a01e10100c0841d000c0300051021701e0b42d0307502206045d40050b40c0389000000c2d600c200d008503420803000d5511603a4014041d002c031000c20060b000084040c0029503680f1915007244418035240582c0c4010401284c05d41c001c50301c40300c020031803100812100541c91b008000c61001c5501c080c01905280c814064440c4c00701480040506d5212a001d480000080064900d01c040080003405400d644290320181 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 665608875 1250 665607625 665607637
    0x4060e0f101701022a0d120b04020c030c0c180402040e1204271a21010207080715060602071406070501181403030c12130b0408031014090f0405160b 65
    0x4800505c00d8200c480b42d83c1140715042071002c802420800442140c111380794420340d000b009a8980d1144040310644680c40a441c0c880d80c000000c542d60300300000c5e01c034a02903480365054440c144010701c01c01540071003c005500a98180c90210312003082c6100c00f4207000421004010341c250210340000c10a05910418800110101c08100f941c10303014070b400141c1c2ca5440c00b102400071507000302075690600b2a1f0030200450307005082d102d00f0512303890890985c1c2c0190750550700150080355000a210064408180702c508000c0100811071400308080d40f2080584684a0b07035030180c8000c1c1c0429143e6604490344075510800800400b03414140c5513480140c200401e031010f000e880303420300f1100301c00401c5074041d0101803007190800d01d00800702094948020310041e0211120403144001030800c0d18041c1c0030b98441c0304520388034945070b00700c1841e04105034400052400b8007881280302e0703100d0190441e080742401040c000c1c03903030f150704060f494007581038130320a0009160b1100140c00d642540140034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 665610125 1250 665608875 665608897
    0xb040c0510050306030d050c1216030e0d02090109180c03060c020c0303120f0a0617060105120304060e060702030319230a02030306041e090b1504060e0f10170102 71
    0x582003a074400444490104440d400e8140c2c4c041c81301428818043d07000f50411080a008603950010050192841034101c50000250343d212000c0e400100b5030001c10310090000d095400828944044c5c0018000b0b03135041c4203205c0c41517642c12403074100103a103d40404026070130150101d4580d641e807a01c00b0040011504610050007014660302e072070726000c0125000e4241c0083d11030547c1e101c120041c2c400c3c20002d0701e80c001c20f41c0d4400000490100b071803100c00500b00413401034082c5614160501240082d00551381d0f08540041105000306034020000c00c2e4080c0003580c0319a22002c862010030710303510800c884c80c0d1036158003c0040315950b034000d410a4522003075846c002120444529011a540266201003015800502c00541c4600b0154000048030911030810701c808921010b82000325641224107a030361310190b8080290441c01c00b0502a0303c0103050f1001c201c07603071070201c140301504000b5040c0c0004140120206050f05010b12020020f86101c010704244c0240107400e40d8000c1d031220b13400103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 665611375 1250 665610125 665610139
    0x106170a12050319180b040b0a0605040605010219080705030c06090f15011502070b0313140705180408130b09090a05090712050f06010303210915050a090b040c05 71
    0x8102441001924004c0d0800b0803401c40c5a031407108004c0250600710354000e80d0756845840d00003c541d140c28405e00881c005e1b420402c05051200186040c1e841e40d4100d980217030f007084401c001b540d90010b61050070210464400000700715524000c949071180c1c11001e0410700c004550b100c40c240000c50740c070340104000c1301241d1100c424070f030a10703854050200d0f50510b0b12070b1520040002201c1d17050002c2408a0510560707007003c3c1ca42c5001812030300261002c20010703400e414002d00300041200b08041004404004007045417400c80040c0100051507840c02e4001e04603404501044140d805a442404902c001d1400160319a0a0000a504404840d0780718030300007000315078500700c1489014060322904000d0b0410608100414120300c0076034a003107a0511900840e108404000c0c08041d010354480e68400688041c0012110101c604032003c40c001c8501c0c295900c8006400c0129000c68a01c00309404102642e801e50114010280c0b900090500110607042108118000b8500016109c2c121003003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 665612625 1250 665611375 665611403
    0x9070c02060307030b010c1b06020f161e0f1e0918060e16030c151d22020a12051311040504060902060706060303031d19050106170a 58
    0x444010900010194000c1c0007000031032101d901c2504010150901810030003910348650703072002d42607442000d44100920002c0014050994140310380c0002000d2440100788a020b8806282d1240e0344c1481044c2c031428800e6205507020f0700802c1d11070028042d600d200001d0603914a000144024a000c1c0340c800001d071b60b400425100031a01c44c8210509501c00e0078150101995248001401104441c1ca014410642003204410310090420080c52055428145c0a464403484812400e102c01245041c400700d03801000d030000e034101503561045401c882c420703100350540104819000d1164040060980002159440070340c1020414502104030701c420000d540d41d01440d940b4000c80a00024840400310580985e80e10b02034002d01e030400e00820000402c1d04895001603030030b0303000340400c407101500c44000300145601031140321050340080340b248404680a501054540300b4128074610b0130000c0c1a03007031091043c2544014080c29503028202c010f000382c0b8958a6903503000000031945003103c1009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 665613875 1250 665612625 665612627
    0x5060d14060f0c280302043308010303141e0c06070914030a06050901020d0207030c0501060905040f0b090c120102090f1e06070305090d060e010e061009020d0f060e060907 75
    0x110781d01c90a028100822100b03014468202a907a13840034541007503000d2001041e8090000b000c41d02002d85046490051449a1580f180101144860b0410704ca07078100100003094100f14600f45940040d5180c9640700c0d4a45103c4482003181c00e0104207e100c0851014503240000030b12501070503150321000b1903155904281003401074041809034050b080011082c002807500d401264109011100140c1440d003c110850704030f0300124020b80003e40501184424002c080c42014007502c04400144034500c3c003038598804031300480e200180300610a5000a543c0c0605200d1240004801401c09916081500b041c901070b41050b60700602c520341640c208910b902d09031100089200c41500902d5070743e044802040700941145100b5400c0c01001c10140b01140e0b030b00c2206802e080d204e29800030704401d00e09001401c5035010324030745246900880a200c140342815400b24101d03001007001503910495595046c1c054000f03000b00f0b415980c10520046401c191003081584101410341f4021156594a00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 665615125 1250 665613875 665613877
    0x21c03050415110a050717060402011d03010906140a0f0608060a09020a0b03010e040c080d080a2016060b01021609050c070b090a0510110d05060d14060f0c 68
    0x500100414001c00003002a1142c101c482c802000b603d003400d199554600203050b0034420701c41d40484454000c0c14050114000c100c80c4074403614001e00051025182550010308802405100b091048412510701e41d002d980035004100ca00c0e5120702c083c06500c014405c9004c624000361007c0d1081800c100c4003400c116014414281110410001011541c0325100b5540082c000101c00342d0700240201c50119030341502e0301c0194005e19a458086446190900f4401d02d0392885421122654000d51f05400d4020340c0401c1242e044980301c0c10010b900c16012081140b40c10500100c0a49014040b07942013141d240040e02e0790055014400a000c1c62500800498485901c1610329500c036490301000d00400c8803a5024650010300744e100d6515191483e211210082401c4503050103a03401130801504109041c404900c40c019000800d009004448001c0c1034603000740c000ca250010b944500160315591681510102e042d0400707014040021406402d0340c5450b4121400e02401010744046a00d9000e800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 665616375 1250 665615125 665615179
    0x1002013305060c1617102c07080a03030b1009081c0e040533210304090203041416150815060a030e06060f240c010c080402 54
    0x100c016156a09060400005030803100990000b882030300d03407104181220345004406820b407401ea030000003002c02c42040c0fa151414625041680c01e104000c00607500d242d0103d02070607000c1d000030038a1800101c0f8a4903041c03280e44281464440c03640381e9420302da015408282d00c1c00d8280c403092030200c004201500c01d400680310b00300071544044a0040a14101c00c01f5843e00b001c2c031300d0945110840c480000c0c0684005442400071400c0304050110702e070505d40042200144107050810821910000103986084030641c04044c101040c13130140080743c0700703000f210080d000d1600308645a09280c1050400301e6045c116208040c410780f0020349045103882d41c050110381e08468025005c9914500c2100c085070050003901180148204c115260b50790304024204003640781c2d40016151610300505e61404201a040900405104030181d02b140c5580c04005e02c80c04039012640440c440a070a40f0846100b42d42540c040b0794a4501c491046507801491140128002c8860410210000b402c40b1404680f00e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 665617625 1250 665616375 665616461
    0x1030b03011b080a09020a140111010506060a110a0506010605070507121101030914101a010e0a092309010902040614090714070515073203060f100201 66
    0xb0942030b203402e034494824640d0004400030040f40c1440c041c1c4c04150b5003007054200d171910413681c4200d15900d503031180480400d01d4802001380182e00741040030070141e01c40c81800c45c042040131061000c40c0d01c02000a1041c9991210071900c256039034a400a2503a0442c800c00c8030240180c400026200310751a614079001500040c008004d010741c5070040d4000c0014241c00c580b80c3c44d14002d070280c101c00c140076a00b600d110215011400011703048110103000d00745080c85040c0280c540d8000c0c817548480130b213001520180b20b00040c00c04d000070b803055100003694008980c042003000c01c0008038030307041d000007000030300c241c030140110741d101c40e15226014a417103042c98011f0380003070010301800d2142c010750f5031a0f0800503d084c5802940d840c1d45090200004e1003000807141e080c2402440c0d644031403a02d0005a8034445032982c400d5442181c0141039841d50310a000400c00710108919582d0366503904d6194400601446103064880e4000c0e029145264201c0300d10a200242c03603c948a81c4454800c6101107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 665618875 1250 665617625 665617661
    0x4050606040504061b0305090d02070308220e012309040213151a0415020f120915040e0f0106090821090429031b01031e050a0b01030b0301 61
    0x2510301031200400005109580550f1034464800d41e1100580e0811031224107943d011a940c5001c0700c601d40303011041c107010400c42d401000100080791400f000d480030305404001945005c0f0300701e41c4d495076501c1240c1100c002e5400003000002c010171140f601200212400020000380d2501004100d001303030302214065004541e00c2c055842200c416403111502c0301c90440401025038866803200c00b6540140040c000c500c0000406102d29204d9255120b00c200c040d20080103142d420360a0340741c40d0380008c4035018500300c011900403159a6280d007aa1441c20b450030004c0e40f11b559903550080f0448043d582c0104801c07801e400840d00c1c2e031103480e0510554010000402d82c603040b003e0305502ea085522100e0040c0c01c03060042498540c0d80e030141996a4082d11a6400200440303483c003c026501002558440d41c05a81540c103402d44051004040413400d0070300090700c06454503409074004000c1d400380c000510305010012103001c9503014205141d001e0742c0c2001580341e040141340c2262003001071300b0b01440c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 665620125 1250 665618875 665618881
    0x6050f13110d060501061d0906010203070f111f110a0320010603060207050f0d1b03030c0e030d09090b01050705070302100909050903030f07030203060d0210030e12090406080303040506 81
    0x80e015800141c22140903180d021036210949407101282c0084c1c0000c000200c920031642480c80900c044011000c0f4111074a16041c140b00d0300207952446a07031070041c83c6950b0655180d050040080600348c1d02d01c03014000006024010060200b03840c4044115004202101e030342c1c0346603040004d4960782c402d80c16120036108070303444100504140490307100e0060300c1d0740740d94012000540d2070002e0402030b807080c0010301403064046003250500da000d4000e03104002607129902200d0010340c142034980c0390107080004010424010131102d61011801ca95010310804001401c0503070320910742412100d420008201e40b05450004588500c00d042c0d000c0d00310340c040c44050015190041084094884a01382510300642d2010043c05843e0f040340c0300402904080208005045c8000c2d0340c42c0c0c0002c01c4c0c40c04500e10714201d40004e00e000700f00d0344040d000707100e80d0b88a040424000e80c05440440e5003002140c103104008145464181d001100c500c4c00340e4240350000031440d00000660b405294414064031040c1c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 665621375 1250 665620125 665620133
    0x108010e0a0b1b0d0902010305010e07051c0e030732071809050706050409060509040f030e01021e0106080724050a020a020a090209011107060e0105030603030903160306050f13 77
    0x300050a00003c2889a00e149004180140c008003030b401d503a80400b01e170100c55400003504560050307011142814003a810440710b41e52250469a440d0300c9603036110015055407007514004d042e040c450090038400006c250301408007210314581c480c500b84510580901e9103030541107516900034041281540700d0b030740c184031012844510354007c1c20385101c0000ea0500c0c0b601c03443c0c0761440a40c400340206000040030711006100e40900300160405450f910300506040da100082c5400c2118040d003008507484041c0c05d180c0c0700b031080c0e06042c200000484410b50356030248138000c006074412100c1c103108842000070403403544160350500c0c086c400c8040902120542c0b06071819804000c0d214214080ca51101005075103203000c04001c1c00c8003800060b228039141002429908041c004010254010b5901b0001c03907a0100742e00c550342c2c10070308c1e01540b0fa44808020a1450040203121079041c0a0072a151050940310300065003241d0040794180000d80f1515102c01d45800141c503046c4c1160800d032203807000700d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 665622625 1250 665621375 665621393
    0xf11090a0b030a110d0b0112030809010203070903081c0516020c0405091c0e06190305100e190209030f062e12021909020a121803141603020102120108010e0a 69
    0x213840903140e80b0760300c003495444141c102c009030041c1008042c1c040b508418180d00134101c540c0b0243e4207000714a14106041d0103000880144802065010001650b40202c02e0300290500e00d060b619005120714200000003080e00402100c004c0300601c0303080c280002c549414080e241c01500d4a4000e4203d401c02100210704c024403c042c08010300c00e0a481e00106070f1910001410a20401e02c010800044800f000405031040500400c500070544074003442081c042d011842d03086001500c02900d01d03440101c610011780179148499038540600e132001d40764801c020600e144504440a5240100b090b40c1031000814913000d00c0d48900c001307d64000340441d0328024008041c050000f040380c0310200280c2c99214041607503820181e019500410070402040d00149484081d001d0104103009080162010b83d030b84403064103002e0700704040100c0b016040d40c0004121090540c0603003480c072124886007406400b07035101b03801c90045040d024000260408042c072514540141e4080680070b141b13030360348403000d070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 665623875 1250 665622625 665622653
    0x30405150a090315060e010503150f0709051c0201030b0a0e0601050723011a180c0d1103010b03040201081501210e0115360f06030f11090a0b030a 64
    0x2030040040011010139106007034900083d10342c880104800342840c50921150380f06900180c0203901070f640070101501d400c800305911500c900704801039590381c8a8210744109041d84442d4000e040b0307045500c401c011010b01c00031180c2c002e8030b0600c4200b45850900810142d2845140002c89a55001c1034180d03101c0c00051440f81e0141102c403144400c0d1507031a401040680711104400e80d541c00b040d11400408400813000384504403010120300101001783c903040c143c0200100e00f103c0700061004d040c4169035100d041d119210030300554480d1303115603e0f40b485074402d4405034042150140054501244403100d141e0149040e035403603a9a82d000d0784104158460004040301150b190034070040035103000d20402c2c02c10b11400000c1103890b0324008550b80310401044c255208510f030a080300c1d8000400407a14002c01003000360001e4286120b500540c0103013043c2c0c01c0100125010582442403041036138508401c0320007112a813015468084901040f1030000b0307959a010307004801094003285015427040c1c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 665625125 1250 665623875 665623877
    0x20a0312140c0303040c0503010e0d11070f26030405100e0111031314090609040308070c210318110d08040924060206060a09020c010f0509010b030f030405150a 70
    0x240354540d00404410715002440000c409038804820881070002840f403050040906038002c10a0366043e41d2403a884018030000c40c0148113002440142d004010003520004180301d01d05000d1258507265528106d410303010960320510039510740310540034404001c0b10119400103040e49045c54000d64292010b22020b444181400710090281040700014801000c0002c4440c40944c8440c2c102401982d00c8160302c08001e00600e08941000030540f9188030143d04a905801e040d0503a580310750045034002d4090100500038514104000a400c000c51a95107686101c0d803818407007030b0010340c0590b00c00b101800380038100030b032310340c00b622118149000040d28850040448914003510790071610705554410481240c1c02c0c41c85201c086d142c0100039003850107401c40388090007550400c1c00004070f0030715140c0102044c0d10350004072558504000d62241780c88140e484418069454080c00050003028920041800703400f8900c40040d08070f40100c204c4058610050903800e15102c1e01c075000046400640c4108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 665626375 1250 665625125 665625137
    0xe1e010c03030b01030e150a060e10030f21030c080906040c0e150301020f0915070c091a031c0f020c1f0207032f040c020604022404120c12020a0312 65
    0x103102c00040c80714402c1d6a150407e41c440a0a01c1642c035421982e85512140898004030180b15001c0c4074a0b0744507044070740061261155030b259007440800c0b01d280050070020030031482c080301d0300c058164210341850409511410322981e12844403030749480c0c04540003480c0010790344061049808640c0840c1e04407035a15044c852030007504000c44e00b2031b03001790001d000040020031003480c6450301c0301c00362142c1191106103a0910340580d81d0348611183d54000c484d002911031134ac450344401380800d542c4009000030b049400c03003a0f292490000f015522060700c400102e00340190301e903241c00001d189005100c060701d01d411445800020b00c5440c4d06810f4060114001c1c11800004141c6c0b200c8400d04000000712039840f5501d86151107959690103440b0180500d0a080e503806006801040041c0c0c030540584e541c0511101e2440d081e03246003560044200c2560000c03c2c00b10f02c1c500c0c103034981116a40700b520601c00766603d64180c2d485964003480003c1d8420301a0100b4000503034541012108090709007401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 665627625 1250 665626375 665626391
    0xe0d0c1a071107060e0a0b0a0819090f0f05060705040f060c05150c0a0e0904020d060b030c2101061d0103080c0f0d030902031903080a1107120e1e010c03030b0103 71
    0x2041c00c1030301c3d40c1e004500013064102043d003549800c103400001003013081601c80c5080103849000d42004002801d000485144d0884404032030b8807604907000d219806122582030815038613000703c00801480050301c40c0e1154900103104035024a044900303540714040401c40305482c18504613a21498a60111101c0c0904140140c040c4451140d09000c1c0b00c24000c85522415101c4000301034407812004c0c83c4c07041021a045c003015880318641c1000340c64204c180400c02d281c03100007091401402c02c80c1a6004550b0100141c3c0142c48901c180d095808902c1c000e101140d82d9041410b00100c1140c01042200c80c00d00c010400601341c04000c0940c281c2d40e4041c0c2c2c0007800b42e07103100c50034102d80100704008030348c40c3c1c0400021403034240300c000102403102c0848042400302c2d8800030280c2c2c4000f8101d403802c40e9984180d00d0014140420303100c01c01da00100c2d810100780d0002000f071040303d02e01c107041d02803e0281c941c1e080101d1068001102c4040c10fa690001e000701946003140606800704440b418141e4032078413 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 665628875 1250 665627625 665627657
    0x60a090e030708130303020d050304151a15181e04020c0a0f08070b0a050f150418060b0306010e071d1813050607050a0c08031f090e0d0c1a07 62
    0xa40318030550240700c8018245142001f9081251764011002008800c004210004e1607040d0481203e400700000046c2103032811401d440c5082032000700c15400792040d603d259099a010004103040c03030054060051200c1403000380f001014604592809092010042c0c0102e030600f54044d00c00d010f0007200701e40490000342c8803011007022149040e00e8104000074010b041c0f220403900540c000c200c0920800c141d1a10303220010751400050003194554104110302500c40d0340e203800c812202d052003250103090b0701c600d107455001403070030030042c500a0140d0000041c0da07040b401c09183c4111015110058403031400300900088281d0500201d0703000400c0e0910380c0381c900c2d80170320071031040c4894032040a1004070703402e117140362600080841c4208801048410041584a071026207410340c060060354498403004c04441040407451214910368490042c001036269007908286229100d0742e040e00c0b84c6507d0501d040b69042080500a40049103240240c128601c0441c2029440161450070726070070191408 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 665630125 1250 665628875 665628877
    0x20f0f0d080408011a0f010e010311040e2205031204061b0302090a0f1a0706060e04050304180506013c09030201080906040308041e1a01030b060108060a090e030708 72
    0x1000c0d2890700012800f805031940900c40c50345e801042c100286141148800001c012007480d844c10340c10003038006030710740c1103902030740118900603402952039450384d49075861010410001c941035841801d040c4103684c9601c0c200310440f1070720707500403000c2c51402d06a1288a4200304000e0400c803152a55282080903001800c6203800d82c40c0c0c2269005a60340c00104108000c0120581003120744a600c80002c000341c400524483c075030301c4018000107440307650500b4150b000345480c0e448005800a248200410008040000c20682e19103060080450361141c41c03050440d170080f11a140416600800f82008900340b2000004080f42540f10701d0380c4081000b507864200c1c40034081e0201103010751300244110340c0c00c4481c00398450460b00081400340303015107008204210140024202c986800b0740000135128807d9083d030416040400001c001a003022006100c1c0c0c803d00c019528074040001195943d03210700301030382c0203240081c40c1c04040c6051040c00030040c80e8224030071005200401c0a04001540e80d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 665631375 1250 665630125 665630149
    0xb03070f082a09073f0c0224101a25060606050c0705061801030207031106071d010804020a030602030907031703040507080a0506281407020c1507020f0f 67
    0x2d80ca8240648083e040083c001400c0c5d00b0894440c0940e42101d1141202c64030014000741a400340411040380741c22099042030440c5100801030204140b01040c003407000c2620500490034011540700c0302c0d5889130f0004030b0441ca09004d00c4802003c200030071001d0011203441000740d80720800c1105600300f9527141011210309500c0b0b40302258012607807000c03004003800800700520040c2c0f40c3c076150180008800354074600701a801414158003188030028140702d4410042c45e00c2c032040841c0d80d1030409400242a4011415a0329501c20703240d0700a00c015442180000d000d00d90240c08007011a0035651804003940000300f54900c45d20a0460002c0450400041600c6002c2628841039803070500c1d080c10b40c1441503c0d000002c19a001010b0140017520002d00298081441c074001400c0350002021003012001480760301d400c1904040c803401811204000c400d0040c00b0503001c0b10700c00300c0a0000e00a48150896540c80003d01c02d00007039000d42040ba4509445401c000c00c1300040c80c1030134001401a804607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 665632625 1250 665631375 665631377
    0x1501050304150218130c020604080c011508060a0510030b060112110d02071707210c020d050d02010b0f010c081312030906020d1701120201030b030d030b03070f082a0907 74
    0x10303140310b13040c0d043c10707103220001104901d0184860b54600c03a02035610400548000d26500d00000d04807558802940b00d44900c0b0707400f006001c422661004c1441d83c902c0161000b00142d807414022491900c0e0240629003107070b0f480000034190f170360f40400640b00100200707102d10940741c42d50a44080341081800801c07200f103410f44010f0300c611043c107000030342ca481805555044074040020502040301e405558052040307204c80059602d5401d031003207038500d650140007504034451901c0c42c02004408103e40040302c0c074a600030010382d50000c003007100c8004a100328be07010179640221000855005030043c0414091124003081c2c0503515008614040381000f02500080c04100c0c05000255051007012043d0109203441028100a6144404004810b1203450786080000c00e028085900942086041188c010161800792541a4010340545488200b182c4a40a80c3c1030201d5044000a03902090751001401132191901941d80710b100d80d94480300a01e618a0300c1c0e0042c800641e501c0400354410016 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 665633875 1250 665632625 665632657
    0x3050a0608071215150512010b0301060e09010b01030c1202161205040e010f05061b1009080c010c11150705070c0906091b020d0302030a0b09090a030e01020615010503041502 76
    0x184c3c206200c0d4010040811038030603040462103140c400a10310284169034080328100345000802a480303005004511405406508112000a8503044c110080c1d02c00c80e12030000b840f03e500c0c40c80c011000c440048013000c01040b030452111042c20b06590180000c4c1d50b007100c800c448a0042c1d190390700b0320320341c288100002070301c0000c0600001c02e0198800b0b004196507240f0360461410540000c959000701019031b0b036030203021a0322180e610010840c11031040d800c1d0800700700318a0b141c246841d6591160740d007002036600b0300c40c0094102e440b51f0300b5031414444d02c0e0003030305040b41c0050b07207043d071450040c0969003040b8040c400100401e0515400c20010b1121450008201d858503a0030300a40b1758500500048140042c046114a500400c80c4280e00c0c0f0035141c010380c1d9942c1c1600c40001840d102045581200e0080c080190f54003002400030400c600903211645904090f000480c0d940404480c18250100058551917085d40108060342d00684201d0303103180c400c031078618804100d8001c40710360205995 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 665635125 1250 665633875 665633909
    0x303050906040e0103230a051005220507060905010c020a03080306031222050d03120c020708030a050d06050913080a0215070f110f0309190b03010305160f1503050a060807 75
    0x6a02e1b0748005606480c00a4820950603458194651040c0c48a141c00c460b15040022034a00c018080884403a01000c80320400c1c611500340190368440c203018440c0411038030040400c00d580101402d6050a6005004004c143c6c00c40d611555290000307404503030907104801c416507000094001400c95445481190403d490750f1003c2c8a0f902081c9a0103a409a10402d014800ac641c4c06022000a601681c0e004500445180310491420085620030301050201040c40301c4d082d03074448010018640000414800f1685410402c0004181a6909001010300c4500c04000405000c06016095a640103544408118101c040441c0c030084480c08005911010b40155194202608ca4101c00b64640200000415030f481180d0b40d10446215501c5000d03034481c1c5854a903001103000c000b901000220b1610395943c3d00d02156240300c01e9070820070500c038480c070100c2d80031088802d0004a9007035040d120303001e02040f10f056000300400f03450781c00741da038031110045020b007420482d4800800c034110031550040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 665636375 1250 665635125 665635163
    0x131a09040905070902162603040206090a030203030d1a030625090302180f130804120807080a020303070801080a1a130506010308041401090807061b05150415020909010303050906040e0103 82
    0x266001a03900401d0200300070714047d48071001b50399010350b0603a28950b80b0800140000c80c08070301980025803510000400f0082a26503402112480000c90307000c011a04030001019198081211414100e404001c6070706003409101c1c11001da00d08040c24070b10300c81d9460350003240e042c0c4030950807140043c00e0310301030240711241501d139190302c40604190088200c0c401e94400711548518400d040e5000200043e00080c4130001c000c607400c85900c400303071658408840c1c502a4881d00104d90800101e0b260b41d0002a520b40c001ca251250198007540c00050400b8901d640c0d200c00c0c201034061060720001120031400103904001031130103540074400b07064440e13107418560013900c01000c241d141000f1081d40c1c10481e030720002408105440c4c0c103040c0050042c4000c001c05820000d5004081d1076845400000d42801c0c0001e40c0e10350044e4041d900001318221461402c1c0160301c01e101c0766503089440880100b02180c401c0010b400c1058000b00172503c1c1a64403021450f1144081c0c00a41e910f11009031551100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 665637625 1250 665636375 665636393
    0x90b0907020c0a050f1305040c031a09030a1803060f150501090e01090902030a05070e060907052511030d020c120a15090c09050705131a0904090507090216 68
    0x8141c40103051104528000c5084142d583c4949405400d9840404010741d4400304040c500355402c440404c81850039007420005080248416035203052460401890b20420041d403901c40da0070a03005620b0a4084070040701c4d40020b00c042e500501030710072310201c001a41c0e4001c1d11401c421200c00440c082040e17403510210280d80b0360005042c4000311104000040c41100b0311811540302400004010803280003090030010010401000c070b010b1310030042114155020600d0141e04192010903a558404400b65803a119414040700d64040c50301300003911184014640d40b220748030b01840011014503d0200740340c0010381c0175110258000040c10442414010074101107080003100402c210b284e00d84520703a1280031640324682c0c882e20360302e00c2c10511041800c4c0c1002071821081c2000a49041000202140c003c000e82d40400d9003590710004112901c48401c0321030b2030031f481055107001c1c0c00c44100001803001d16402c4030f80d4010b43e07a00146142c41480a00344803800c0c1c100ba2840b07441d0500d0041c04c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 665638875 1250 665637625 665637631
    0x1605030105060a0e0c0d0603080d05010812160c170304052e1d060a0305090606101d12100e0d050f03010e06030312091c0c0803060603100f090b09 64
    0x241c1c509010090786a0720189040c044a40f03c690101480c1ca489054103240d01c2000c001106242c24078000200b0020305200815101c08000740c00c200d181d0b210b0711850740740c070480042c001c60900c0500c0030000a0148203010b003010b510484140c407401c0e60303504521202d8000c0015029450300301050400450915108031403c2c40c0d1480311040a0390501111800400d0f1450310100c200603114031114074500d4030802c6912601c10003000c05481e8101088010060301080b502d4801e24003c4401081031070400003c070710502502a22410221055100312030a40e140c4040010b501000032040194561014050142a0300289030045840b860a10000d403425045041c0c0c0c000700a020440441a00c03564001e4a05542007003095800039218a00020710754058071860310540d44ca100300380324010780005101030406002e90a055a194000481928661030122001c1c0590000300300003070072841c140b0002c40d84070052003244041075440f0b85a00031a4510754004010486e920580a000b0345442003810354 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 665640125 1250 665638875 665638879
    0x611031602120415110a0c1503050f04080c0c090a091202211812100f0e0606090a180b060a0e190e0118030e04050603030307050f0c07030210021605 65
    0x1071460b0030103510b4180700e0f52088002e000b0000d207500e07000910034441540680c0e000c2c000c6800c1601c0e02e0401e182c58010900c40c81d0f040f8400424040c0c8010f002c0e018051003000c210050480316500d80d140d070051030303100c1c0303030264007900a04c101e0303076580c0d40c400300410301441d0400700000d030b458800e01d0071587d044152a400b200f1755014044880d42c403e0088000c0c0a11014410016203510f049039140c0c01c91108843c01c694443c500078407140d0108070024485030084140c0109001810014039100300312500003042074080c1c2c002c40c000400a0401051164018980b450009100701c40b0181800f00700320300180840f8854800b9050100303600d4560782981c043d05800a486015051080b200d139081000700e03009031003158071403ca40c91441020743c04a030729510a07090360880030003a8070300140812544030805101d1803401022a015040000580e40b003808d00b03840300d600d410b000c0c1d526056960008603041c10300c3c0c81b07059004001602e0300040f034520210540c005010140408503403215000840e00031b06c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 665641375 1250 665640125 665640133
    0x2f19050309090f0606070f08040504020c0d091e0515071b180c090302010f02160801061802031006050d06080106090e010c020a020135130203070605030705070b0a090611031602 77
    0x4040d6140307402c0310003c42e0704c078000701f1021800d0f02e4030804034021070f40070710f0f032051010484142c83c0e240882c0440012640da52000c80060b2955801b5680c610754008550100354850b000748400e040040b00c20b800881c0b006a0503085c0203059a48e100d01e101211102d03221078031054002c004071541200140c0d0801c5059800317002021014000070086031151002a040000070744040603d94000d110300854100344180300500981c95880040c040c00e81031103840c04091101c0118032030b00380c1900c02da90040712000c0500103950310300032080390f90360424041c00302c0040c0e50700700000300910244074240042001207001f25004001074680d9017151080c00142d0f00350341000c070110f40180e9000100e000c10303000d00f414040c1101000c003a0340509040c440c80064808591801303000c0142e51120000e51010f200310201d4140d140c8401e003c4070240003ea4101010030b105000d10340016102c5241d42d41c0c0114260380004400a860301d40d0f00550310274a03484c0340c0f0140300006005010290744070303005c40350f40b20740000c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 665642625 1250 665641375 665641381
    0x4030b01060525140a06060f0b0c06152b03120506130c03060e09030c07060918020a0e0306041b050f090c0d0e1c0905012f19050309090f 60
    0x580c03100c1c640b032800a1401c12440c050780003080200d413080c1c50030f551101e00701c40031078107249004802440607004610100c1401718000606a01c04003c0351a6000b800000c1c1850b900c0740300d00c80c0c082c0021001da050f80b10710003052929514404041030351185071007503503e01849840303090103048030400e803880c4896031381443c00700801c0d40c54102e01c2228400d04001c002500c0442c3c05802c40081107140c00901401c9806420f02c01c024030000040d02500030f2207000d403101e0303d60354802664480024468002011484070804104c6501503020b4184807426082c01050142000002424403004a40c106d507185c20490255112099100c9400702a2505070741d02c1c00dc6100420002d181c078900246140c207544000641c03001d44030301076044003c0c013000480440740090280c3c24100d058541c0301c6001c2000403010710002071190700c59000302c101004140280024800b060103010b401803240325800c1c60714480c2d54001390840700403881070030010f03000d036000d1522120340104122240c5009000080b5900544080c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 665643875 1250 665642625 665642647
    0x40e071704240b010834020109061a2202190c0302151e04060e03030405060f062220041805010503010b06030112051009080405040b09042109180204030b010605 70
    0x5c0f85e41100c6004e05120400115903000352a80400141070245503000c07600d41e003512601504114000c80c462041804000804100341403455103c40707400307900c0070202001c07034904044103880000c98942c80000cd85003024100e0b04988400e01541c0140000b11480c00c5402031590500400e103403690000b1104c0318904107500c011203007504190402a48040c0e10001c40c0800207103510103101a4015420340b80c49162604040f919140c044031101c0145c0c01ca540010540e2038144407a101c10f511b42e0303075080b80401c00b183c074480c018900d40007105903410011101c2c464810075076018100805016288060140c0090015801d0340c2040e40101d02a81c10000b007510b20f680d9400903281502c1720080c01c41e24103071103810468500300c090340328021403502e030064450501030114001e1090380e0003964180481600141031142c420000c0320041c0010481c0d50840e00d00340c80c1c0ea180e20302506020b140120b401512034100c14004546815442c5182d42e0002d03042081180c0c0c060b03514014400e60411500300035050700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 665645125 1250 665643875 665643887
    0x6011a032206090f12020d080a1112070203040501120b090403081302090103260c0604021215014101030b0126010f05060c0d0c0f0818041808040e071704240b01 70
    0x104100180351a80c42e00d13139152b101362040d07910341c1c422310120640c1400c000801035220b521901985000504000013244562164000c1540400b4003400c8a14590f5854804803044400a015044041e41c0d40070524056903030404580d020b1800386504100e14149540b41055103041c400f0819100002805142251600400c003070390300507019503078448203540e07501c100c074100b0f000319038040d209030005400480c4d0524221143c440199280008a0348000980954418800c07883d03102c103034104000e42c1e2400c1c25440398020001c541c9060400c0c841c0100c4004000d01001c00740344c2c0c082d8181026200402240c0c100141c00700043c54241c404900d0580c1c0604a00d132128490400c500c24003608100d0042082001c0324240003013600650029125002580500006c0d0103a01003248a0b82c10001481c0030b120700d2015441d4550380c40503d0614040c80c100042c403200358001d0600041c803461069858211100d4a411480341d80300307220f080d0501c01101e410390824004801441000f5182404059181c1d0f0004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 665646375 1250 665645125 665645131
    0x608100b1e0301060b04060c020310050609041709030f01051608040f0f0503040e1602120f090405090102161202010e0303060901030618020307090c0206011a032206090f12020d08 78
    0x15184868081c1c000c04280035012035031101c8140d050000740010800d62054000c02128400c0301038075414403010072070405407a0309840056100100c80045000641c44803042e01d0381141d01100709091042e1800003c6c1880444002c00060b42d44035410400341444e150b0381d11145440d03c0c242414542000d071211a03d551031000010030050b000e00034102440000c20544004142480a4048034034100d000002c4c00320343c0c61440700141c429182031500e8458814291000c0000d4880131074140383c00e0500700005048044d000315a41d5500704084801d02c48198941c0d03070540e000d148500810b01c6c0d80d4500900316030000c403000100750401e106000b003d40d20650144e0451390000004203110101440f402d00304002d02c800250305120310000042c00c06200c0e040007600d041240c0964140c0e0380c3c0c410442e401221340d2481000f04440410015460001c21034141c0c51a0f919800302a0280942d9a95501110407207032040d16003e070101d085d4401c100485088080c02201840a020001d070589005020b87d0005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 665647482 1107 665646375 665646409
    0x501060c021002010b031b0a030203030a0302040819021503180703291905100b0c100501060c030e1507020306161119200d060608100b 59
    0x117100b032513066076001c0c0143c4800d405080d603c0902c540203150b601e60182041c03d0100c05614200701500100c001038400590744c0e810b11240c11b140042810006100c80d40e00c0e807621005031160891618114107000007180c480d113441e080d00701d804403004e69403c0c15108a003400414450400060782e0280410400e6814498811508140384041242c1403440409280d0200810824503800140e204090000c0c0b4201d558071840d81c101942e02054080c4056448800d4003d0140d9891003628010812400c041541024540d8040c0c0781c003030515030340d44c40340140d040f410401600703240442c1d5400b41d005054030584d01c0d03ca00c0941c0c00301150801d140000b184041d01c449238650000b95a01c800390850010442080d00384c1c0d506210b4489075541c42024504101c5600c0c8039180c2002c841600c038407450000c104981071018183c17505512003a607503000760516902074284e44805040d00003e00d0300c = true := by decide +kernel

theorem cover : BRFrame.Cov 665467625 665647482 := by
  have h0 := BRFrame.cov_init 665467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 665467625 ≤ n) (h2 : n < 665647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
