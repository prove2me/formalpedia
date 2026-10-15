-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5120
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:48:34.042832+00:00
-- url     : https://prove2.me/submissions/5b1b71fc-2681-4912-9002-e60d78e264d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 920683453 ≤ n < 920863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 920684703 1250 920683453 920683487
    0x50d030c0806060702090105060d18210815010516080c0a11032803091e0303140c1e01061a0d0e030703021b0a03021503070905041a120102090a030c06 66
    0x311082000d6640c3e65846c0741129001c8901c0c0d13907214215201c40014205429100c0381202c1252400700038004880c0c0c050850343c4a000125200c00703410001614401c5041d59050101817019900d5401540504c00910062040700010103410036542d96413285644001142006030b0032406840c400c202640e10201180d080c100c0c00790900c8078555a2048074007800451220001d0308e10308045c4c0916006041840103444603180501c2120004641800f0701040e511040b40003802e8104d001c800140c08009881d01101c0b600054801107001040aa904024042c442e100c195a181400a00720503800490490445152842519641d8003681a000c5a5000041a0980e00100100e030002940451140504559050515001956400401d40e421516000203400051041641c882c00580f180614072031549580d9555905459100340010f646900c500860100c2484900b00c849140c80318041c41d484e40c460b8001802e1140c613800140400c1855481030307410743c0c04550248500303944103800104100c054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 920685953 1250 920684703 920684707
    0xb0108061507030e060c06010f031104090c0e0421120b03030f09011404032906031216060b042a0903030e090711060901021317070e060d050d030c080606 67
    0x141c12000c00d00d01c2103000080411012910501d075035a80c5405480400165804560080d0b0f1189507044c640002c0c0d0000761601111007281c0e0100d0319140c02010710480c0e101c84900a000d140c46c01c00024140040d008498026503413000340e1402c09861407100a00b9610355910714400f0f8160b0301101110b9001021078003070742081100c1d52848615070215100300100303280944d03100701c814080d0b405030302454000914001540801c42610858030815070083c0c45592520300c0d49803120010103940d880c65620586000809001005400c603045040d081120b00030b1070049803240074a4000b408440d80c02002c2d50b00c405400e40b0125141c585440e480b030720010103040080e0b509007140c4024101c0700d0b010b00a01d00c1512032b0000106c00b40c1c0720300c004030109043c110440b0074506160000398080c0d0003a10a4042040803a00001175603085100076115980320180500003290624481d0b4440b03a00043c01c40d60444d11105400303000172401c1015030010300d100c2c0d400143c100c081c00c41c010f00e051005803805200b9001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 920687203 1250 920685953 920685979
    0xb0703060521060601140408030307020a030905060a080a0c0302040302180405010615080105130b1c1b03080d020a030b0319120e0f100e041410080d0807081512010b010806 75
    0x40054020740c090030322003050f4144803c40c06c61072080390045e80d103d005c0030043c400700c90b40008018012a11070f8031000c444a07154003d12105001e0309280800180728440420789811701d136030010031070311518640545000d450390042600080460404d144000c060010002401000c0c49840050000300030130302c002c1407000c02c0040001d030b0b06000785440358500600c1101e60400c1640702185440340a020001c0541d103096000da450100308400360744a100c0862200c0d00040f1a01c0c800050741e500842441c1407181c1a402c3d070ac025001a40d4200605503229007000c0036035070800c540f0b58504d91094003043d9100300c5141c40c114001c01d0740e0784107080c42100d2414800c0d603a104042c2c140c0e000802d55030041200b400e02011a07518042c1c6c12500c0c0c20520f00075203184551510b034402442840405115003e4541c0e40c82c5080e03840070394030b80440004541002003140e40e880380c0c032006c1e0090088031220f500c500c0ea107000910300c48000750030210325a5460203604415600304144607030040044880740d940110b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 920688453 1250 920687203 920687269
    0x30d051807140d1202011b140403230f0d02010b01080402010e0d15020f12060a0302060f0304052a0906010c03080109022d07150204080d0e0d0b07030605 67
    0x2601a49003007542c052a4007007a51980da5500202035000b0b020b10400d4014548080d0007080486040d40001c501042030040da640282ca940c0b0700c8010415407503241614644404245060540111880001094800703003000340800c00000d4030032050000d003880d4017120a019084904100360a410301120400b0400582e801149111030340340140c034100c0301400c00c1d01d48110910102114511708034808110002500314807005860700d01c800e07012541c05901d82c03d08001c0ca510b040d100080d4841d504104101c84100c0550281d038010744a0310884000f0360407080c41c04170100740c40a074030300100ca003640104880e113406c0c001550400801c7c202103110049640300108823940c14040c0141c0c2540009500300181c05070802d8040c034410518800740444031100c1586020317440a14181d0325454802c0008078120094800c4400710380100d0010110307100c600b00c069030701c041e00070001940308d2600c040441c08181d200800e81e124885507640003071750b14181000c010150851543d02140050070601c00c01030b441c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 920689703 1250 920688453 920688463
    0x108060f0403080403110a0b09160e340305221104150b1c0606180e0a020f030a0b09011a0904050c07051e0c0f060703120b04020c030d0518 61
    0x2c2d054a40f5803035990319410280c840c040c0c1203a440e402da129031031440043c86038031300b40d00c0e0041c03403084251400c0c0c409038480c80c11140c401e0300481d1440040080070680d11001502c11000d8210b01540c0501000720f501039001c0f46440d40b0b2107440220391a070b401c010000314a1001c5481c5a01f10a00c40300402c092629058000191518440d009580c1d81140c2030489001c070038a40c00a003819048990344d800e19881c5e04490719040c0e034400d00b80f681030080210f48680581102c3c0340741c4d640c00c050110000e10305045070390385c408040c1c81085515400c00c200020307103e012000718070808980f140400d050300310354180094030350140d0186c101c03214240d4206103081c0005044880701801201c02040703e48404040f0031603444ac41100502621990307401c00b0384503c20540759504118200300307455100c12600305100c0784031520144142d11440800400e00000d0041d40b10540942513001e00107004049880454200e0b40300d030304483c0c4550301c0420100807055441c01080d910401c180b21500460000b50341580d529 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 920690953 1250 920689703 920689711
    0x3031b0313020d111e0301050f01080303071d040e010e06010603151a0412050a0c0605030412030203090115140f0a21141606020c01090e15180103030302120108060f 72
    0x2d15071544000b01402642c0c00c0404c645100141045843d80d00c010021011030b000a284a009500300310005124080ca040740e68101e51504d0301442c50f581e10002d04072040e40000c0742c002c0c0031840d0321189034015120780c400c105000d4029000002c025040060107442c1c1072050b4899410142809042c500e400004107540044405049404007402d000d058070200c41c1c05070713402014801005405c1c07003050040000b40c003280cdc2c41c012440705181da038640c00c00b100e49100c120360180c024181d04007581d0380030707200e5801142d00070010400000e101c3c100403604214041694046503a0002c1d040060409244c007202044621400b2103103004950301c3d01d005408030a400406c58a464007000c044581032101071003010703000828020954400000000740c010a00801c0d0150000620130700c0317014406540039006003401c0d1070b1711030140c513005e64990300200a5040244025508a40d0b0f8110346c0030b42c3d0b005600c605000c0d5102e9203015031030b03a800038448400e444050784106036a0b408002484800c4100b180400d0b00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 920692203 1250 920690953 920690959
    0xc0914040501200d02090307050402030a1b03050705072a0b0a0f0221130321030c020607120c05120c0c0c0a061220120a1506080c090102160803031b031302 68
    0x94001b4040004c0c00c080c0150b01003a007143c000010440341c012954016280942c450210b030420002e0100102c0441d501140c4400c0494003c012500c0410041074403004040714040c2600c5c00c80380300c600400c103111000c0e84284464100818400380b010380084d02c1c60b03202034091008049196100c1c01c51020754400241d84190316078009207000721010381103a05000755801c030032100b21451b0341c02c00d50032202c0d07031009035080000c4c9424204100c06201007a254011420307a52034806103000760300190008d0603100c0441040c808200b241540148024117000e04c01d101101c1400e0712003500e000c6482c00c01d40211070071841459000000d01221303803c140351019184000b480000c02c4a80034503610201101c41605114112000c1000714804440020840c450040508107112603e05000d11070410300b40303030003000045581c1074009000c10030400d01510703034400305104589540d00c9080c5039503100c0005400100d00d83c0c02c00410000c2d600b2001d15088008000e08400c10b25618001c1080083e022241d040284 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 920693453 1250 920692203 920692207
    0x105150a03151401081f06180e07170f01060605030c0712300c090f030b0a2a080c0f04150201110307050a08010815070c0c0914040501200d02 62
    0x84801c445a10440054040c10f030321440958580c400c1c2da680d85070b40d400005502d5690130214141c1c80c3c8901542040382c0d0043c24000116041954140c0030380200040c107a580d20982c0800184682c0d1b100040c44201d40a0001d090007180344148903094401c10340007103040c00030400500110450040460300c02c1500007015406580071b01404a032241e07408094842d088946065038104000256081d4400720b080d450f04000ca400320702c3c8150307040c00700d0388a50308500400210130404200720000c4180c0c050f50150300081c40c4141c204005481010b5104520b40e1680c900010380074140e0041d65258200d41e0500e41e0700e0906847c90010070b000d118600940e140b00f080d05034242d007114000d40000c0d02007134a88140d1500c0c1e01c0c01e03050080c81904100c1c169400119860000502c60b6008105404140c1e01442c1040b220750300c100341a10a03141420007121011005280090b04103c1442080780c0107640c6c10008150381001c3c200b190a42c0c0c50305524030324001d103141c0f002003000f02c0345040312048100d8240150f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 920694703 1250 920693453 920693483
    0xc0b0c0a2003031c0513030f1803141c0507080d0c02100c021b060f030705031b04030c050411121815010f03060c0206041a1503031b0105150a03 63
    0x126550003030300c007980c0520000c200142400d00201444007600c8080c80c00300441d550740d20a1b4012240317000307805000700d40c03003001c0780c0003e5208015071074241e200481d4540140348d81e07580d407002400c0e144052513025048001d044200d81050780340340094520b40e140c0641041d0381c42c1c84017a000d2081e010740c00121a80c1e01420a04140244851174898070403038010810252062000b035261142c01c886080c03c0c0801c802403608a1529506490211001415842c00c6a50301c403002c1c0d48590000c0c20f8641604995820040c2860164005102a51050041ca13454038a480103000035200103892800d0080400d000400c1c2c29102a000180c0c00b181001d4418a0425010521030a1520890f8a4201c5c04c500b58004511510510f0a8070101c901c6804100006100c01404a07111082960018101c2c6a84c81000c0d450081c110320441d01700036602400700003420380c10006461070340700b90044d1031600c5805407403800070302080c450075038000c480f05549103410010750000740d0258034900008041a011064032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 920695953 1250 920694703 920694743
    0x11416020c10321803010b011110150305030a050a080f0105101d030a0615151704080d0204031104060b030603120c100513050708152406040f030c0b0c0a 67
    0x2c9100748008203c5070750381d00c9007030a80841c0c1c6041122040d00a609001a58555500c030704109016968041c0c064044141d5556484018082c05400816411003000001c40410810b100074044c40e00540c88050741c074400d200000e00482c800030043e8500009003001003003181c0301c0514081d046849890200740a0308141d100402d00740740d1000c41c903054415850a0b01c20051958803020007400d41d403c1910001e50f44243d100b050320418401080050b1010b098160585441040703a50460700c5039915509252181c0100400ca8205900686007480d100b040d80705c040c1441d109e01d501501c015185285185000c101185c0e81b00e0380440c600300f021000195440c030401c1c0500091103c200b018000b07121a0034810044014030b1b100310002ea806004000e000100f80e40c0004800d01191030100410360303165038800150307004143c3e94254004c181103d050442880e56810003c0c03026059129900094608604012000103916040310ba07209104000300c4080c00c1c00020a07200803940b0140c209003001c3c00c5c00ba0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 920697203 1250 920695953 920696027
    0x801110f0a031d03131203090e090309100e0f03011104060e06131502101803051b10021b0705090103060e1009080702132309011416020c10 61
    0xc1e041050000c00e03c450303003800c02000801851611124969141c0e884900d41c00d9951090300e001008101001400c00c9040c03802d00020f03038880d00303038000c0c1c074200300ba0078000c00c8841610303e0760a4000b80c404c1071013600a1401e0b6003e608084003c0e802000074a42e800007401c0e0030322807030160b0001c0c0011030381030003800d41c2c54a04036054000c002c1404404142c1d141c1d2800c8103051020501400740c02440c982c644c0c200020701c05c2c03200103440c100401c041c4404984080d0382c03e5000490100f41c41d0744514403c0303c540da04101b840da00c0c103103c4000699443c4810100c41156000420308009504051800c001590ba03130000c00c3c2c10340c2e4000c0c41c0003c0141c0329041151400100c0041c5a00c1035042c058100c050140b103c001c0c041c010f000303580c02805000c94075022000c0392088080d010a0b440000451100e848181030301c0c9a210161000014046042201c05e12100303000b2528110492051140f495569038140803001d4064015038075061082c4c1c2039400904212041c1010703404540b905560311445000c0020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 920698453 1250 920697203 920697221
    0xb010b09011202180301090f0204060618091d030a090f062610030f08040504060902040e04060c050c0f031c0203070203041e030803040f02210307080c0a0b07090608010801110f0a03 79
    0x20003000401d06238030b8481d05140301024281c0c450307890b0080c002900e90048000110b0178400540a051103410952118014041c8401248000402d030040100350b240c10130081c50b44101c0c503142c80300420b142001c0703103161100c241c020104100805240c40c0f0340c18080020031a00040c00c07528020f1039510508081c28847d07140c1d00140032805d102149109100d40c180013042a034009450600400b52100c01c030206921491141601c0161943c00007004140203a205036809030240c03800500d405c02ea04040c501c4d01603549500c0d0019080050300b24805032025150000e01c4800040550541c07070072182c0a034490040748aa4452080300211a844828401c90941d002e1540700c0e030000e4490900382000c2d204110031043c104d0080715095402c041c0b00540500740308014128000851901c1e10360b9940c0c44042d0400f20315080c4901c54403d4800000c5d0071000c5061240241d48c4d5984803440c07030f202e03008080b000103030320003149649026010004021000101c80c14000e0b400c08280d13030b034114180c040b001800180 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 920699703 1250 920698453 920698459
    0x2130305031201090b03150c0f0a211e0513060c0e04140f0708091f02030106120506030309220606111507021218040c0302130b03060a152007030b010b0901120218 71
    0x184400a16400812440d040301c03004100112261300d02400310110385004401070705c0b04400000c0c91000d04c0c6503411032035100016018080701c1c11001c0c2cfc1c66406a940c0502400c001c510303800311012290406105020190902403180071440c02c2c0010341074103140c0040d24030003c0000c403000141d0881c20400144819510113080440c00195080c9860020341007805541c00040c03180100318045107680c00303080c0c0a900001e014518040d0000104007120164031040c641d8041140506462020076101e10350082c941c903210507403814810304c0d5481c201240306003c503443e26200c009000c400e070703070014200d90a40b620011540d81e9041c900085445d80d00b0307134070410341d006050456010700f0b141d240c0c0241460400880c0100750a0b40c4522405020380001c4500c25000200a50204108480001d20030026415030511981d440b03c130904400445c105407000d10340701d500c0440104104031200401c2030040000b501c0c0c041c1441d6450000800482c3d1040d04402e455801090082c4264940e1450401020f002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 920700953 1250 920699703 920699707
    0xe030d0c23120a0306050906010807020d121d0105150307060210091406100e010f0b0d020a09050a0603050103020a060503070f08060f101101110903190602130305031201090b03150c0f 80
    0x4003074004e015106501a55003c0d880603030104842c0d5000b60652401a101c90700941350f030441c8034800b121302c201032003c4139040c152590640d9444200c81410007074900da5a100128070380c540140078184000c00310326090f002e03a12100c0108407042e408281d40215644050010502401608001260b01820110b54072180a014107000c2903000c2000c030301c0c08440b11b000c080f0400740c3e82c07006403010018061291103c4a542000b005d0540451540241031120b09030400e079410781d4031000404c560010729007000020a69580c014410b41c5001c480301001844546086407842ca030028004018014074003607842030000342c801240040e174600c0800e100b010f0018240c00007501085000030901a2601103805240d468121241e411701004011100c031080064000e00043e08400d5400003000c01c8020705540e00b550a110315120040240444c100940c0210011922003103400c03586041c818040e031080d22160b1600c04984407640b4081680102d41948500600140c0c0d102e030150035582c03040380e150a00176080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 920702203 1250 920700953 920700967
    0x20a09171b01020303090c0f0301060e1017070b07151d240403090e0c04080a0303090516050a1a0f030a091a0606030408030a15060e030d0c2312 63
    0x20038480c0c1074000a03485041000020069860748000d507820100c54011102001c8181420ba448501c2d03004090000075590b592540031010040054800351100c81c01140704100500000007400720090309071000e011440d140481a00d41c920030b07001c0042076068510800902c510142e4031000308484008428580044c022200c2a1200603441e40300a040e40008841c0c461001d1035001c1c2c62250750b00d600c994103070b60708128080101c4c210040000140c558100808112104240503030030440f442510003051100c15450710385c1c1411032400988508044214041180359120300042048541c440c0042ca81074040444051a9200d4000400b072064800418424150540e90000e02c000d80550281c003042c11007902c00349590b0341e0a941c0360f1b0380000d05001140c0401c401e4001150400c062020001e102213605031b5810301107001380d024002080300046520803030305040c05210b181316941d18001840174102c0d078840c0094902c4441001400700751001684408404100d08040554190201611412 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 920703453 1250 920702203 920702249
    0x1a04090803220506220507030b040b0a05060a05060f04091a0906011e0302090a03050604031e050c1b1503181209180c130b09040b060a08010603020a09 66
    0x12098500d9204002141080c91940411404650b400c0740e21001a00075600c603902c0f04c04401c3d00942044210683e0440c0c2040040c0f001c22403540250b1140c07080890b0b92a150424990341c200061000b0745441c144420849a551042401c1c400c3e10002c4855035221030101c0d000505501840c0c10528141745800c0240720324500c4100115440311045404440c02d94070360004480034241d00386030341e000c0c50036241d090300c00b80e0083d0042d01d503854014000d0b00c00507940ea181c441c6060f40644050300460b804020345180c1d00c0c92903000540d440000e080c002e262240706d11032507a03211046211940039028042d07012641f655003030109914800400d0700d00d0340300c0c10620034841080700e050b01c0b003060f68840c4604542d0300303e40c02070a0300c038003040003002007803003046240a219108000401001d62014204036072200e5004813409840039040e400341954990400806220496885000c120700c511011720024540690001116055607081c2c6409030729034180407010f40b19921550048160180343c480f407090041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 920704703 1250 920703453 920703457
    0x618052e080d0306080f0a021003021c06030f050c010207080709240303050d0605030c09042603180c0a0f031509060c08060102010c090b030610120c110d030204060e041a040908 77
    0x172201000d440701d00d00f02d140950351b101c1c95603d000390403501c49131040c00010b001707a004d0030680494100318940c03c005a40000e04407a0240c2045410300c6050300308600f402420020200c0c500402c0c00200109400d00c101560b4503285481450005500d1340c0340e60020172000c440401480c00c0301c00c0781003483ea4491802070320540058466814542c81c0074000640742c0340000b0722005207140502011115222601c0d009422440c1c845500c800300d5102c0b219509507801c07107009600c500400c0c00380004c101900728000b8184802d032180e013882440501400c0c440c00300100318090449500c000c440a620b03101800712400380202003405070100b880e01c4203400049401520444c490382e0309130700800188003226019a510f44c12801524040181071001558a0810f004004c03038803a2942460350303114815500001c1610070707500b29440002d0002846178210a0200b150020201103401c00f5420181003110061a440250181c24426511401c54814010080c0c0b2400303035032500544188074818032418030b42866 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 920705953 1250 920704703 920704709
    0x3050c0d0207051c060917090a0803071a270d030e010207260d05100821030f040f0204020316080a1118060f0d0618052e080d0306 57
    0x80c0a4840400805031010460038103540e40102000e5014400c0303180700d40d04c002001812140d15940758100300114030540e450b01b40803500d2450b0191f40b000e125041c0200e80e0701503030210031150700c184440d500041d0b038000c3c0b03184c00c0d80030442c104241d40d03a08508031411401010720300e034026103083c84034440400b000c2004aa110b409403030a0040700d00c5442c00780d00f01e00c141c3c1c1014040d0b80a048201c0c0100202e10520842142c0301840b0508000c3c01000400c1110015544280750500000003081085400d00440c1c0011003c0342d4803110038102e02000b0038062000030041d030f503c0c4158030001401c001000c5d8102c4406500a0000c54407441e100c800c202041401102005c0030440b10000202035604a014510b111100f81c2075843c14918007030105c4192501703201d10300b9030000050003000707800681000a49124104e084001ca06245440440c001e441c218506035100c4508000410030250b80e0102c0e40b07100c5c2240d181c0e06408204449001010b84052a0031120180c05000410300846502d07070452400d0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 920707203 1250 920705953 920705977
    0x70b07050c1002012a050304060f021b010608060a090b0a0b15070605070815010f1404030203150a0b0d081b010e060a1e051006050714100c0e030c06030a0b0a0f030305 73
    0x14440020804000c0d014803017207a0000b950802c001070004499400202c000c50fa200c0003d820900b49503c690b03545d00041f040380700242c0d503d11082000840c1080702a401610140c010040706450b40c90300002600b00034841c80245854204200841c0c446c12144440404201c101c0c5440d00b80320b181c5080501070030745804001855640100da1100304810402441100517102c001150103028010766004095500f580c40c061424080013000d0f031414800c1a41621018050300b505145c0007408000f100d480d410140e0266074011118000038951100310394075013103083d020341482111240040d0240a488001c151240980024045030503031582247d05140040d0091011030701d0b0080164003212002c1b6030140812030162410000d00e8001c4004100082c0a2400d022030742400b00301007881c1c074849840713120702c0b280e581d9400a060341c0e00c1b54010710482d070f08030040c00300030082c0e00c005484c0380800307480311140d00c1d0755080e42c0c0059602e003035511004150f1501d80c204040c1c1d503802c000c1c00c60341100442c101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 920708453 1250 920707203 920707241
    0x3010c0512060f100e030c030607030507020f010203150603280e0d0c050c0d051c080106090803090904120507020d0506010501170106090e04030309081204050d03020c070b07050c100201 81
    0x41c40d1205401d030008401603c80c10503000500720844170f811030701e503070740342c1500454944080f1a00c0611002d44920210784003c02c09041c07c81d4001e107450b07a0190040c44592051040c0403a00c100021388610092040b5030f015120346483c000c0b80c04071640041881081010702c2481004103845810882c100c146030b20a848880340911804c1c0c0e240c203400f4030700401039005601880d11a10b801203c401406000783d04440000d10b10241000304041c0c3d804d0034034003040c1c40a00410000f980030442d06d0161480802660408030703500d002c036401c0301c0040e20040c0141a01002d03108002e01c81d006030380c800e41c3c00921030812181e1a01b8195240c00081c090503000581415040f034408148092072412500d40d0f50f200c4d21aa071810001ca140c1d1030303010b40103c00b0035440e444000080754684015060b14103c0c1c084901090800340740c0686000300e154482c0080c580148080e81400c000460148100c40c071441e01681d031000c4604e00705042c000d00c03104080e8010012080034400384c1c0c0c15400301c42181c1428507241 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 920709703 1250 920708453 920708461
    0x30c03051617040309170105100f0b0d0f020903071202090a0e0d08040203010209090a38010e040207080f0706050a18110d0b070c02090a06240e03010c0512 68
    0x1181c510800040360011462400c0502c0301820301e10415603000313000340383c00007440f511005e100341a0540070b601144c80e6915201841000502c0c0c1c1c010900801034450240206490038005184502480c0d610b0b202480d921501c00000e8507454040310f0700300388010160380105403603a40b001c2c0c550003045010307405a4407030000107500d401107100c2c01c8041141e01c0020545174910020483c1d140380010012078155400b440701c0309180e101c2d10745142c050b0015001c04500300f4114000341c0f050140761617800894201d0101000350035601c019003582c8140082c6030174004a0b12401c0498082c0c45a52402001c010000400602503034401010317151992143d4801c1c002c54441c8070a420079142c80a0301c0c6c4d00c41d03c0d05150b903c0e0000d40400d2501c01c1d0000c02174840101c040c5c1c1c80e15021f80c92082161703079001080d880c800c6002145000d00725560700100b5a5004c0102c40d080800d10015a2a44803a0f840300b0f82c1d00c04a0140c50784d00a541c000075203007004009104140b10341c40010648d406c0801d9000c1e1000051001c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 920710953 1250 920709703 920709721
    0x130219090629040506030c1c020904140403090909081605060709060c0206030601030c0c05010603080306030c1905010c1511090a060807080a0b0406090615200703020904150903030c0305 81
    0x4052107400c20b04009082505120401030f0a40c00641540502c0e40700b0403000304c0c03004914a0901007400662401a00d0780742060600c801e5401c030074240300f0788030014410072001a401c05008801c2c2c482d0640c000a03198454034001c1300e64400da1082001400460112804000700058454404d101e140c1e1120610b0303555410550310f40c00c05100007588441e042c400034a4a522a5114481280b641e28041d04095050f0b00c8482c03c660302034005851000f80001001018201000081c1c007124056809072804006841000c103920040e00407181003100d101020024000322080c05c00040340144420810142070499000181d8800090940201c2c0d02c1c42000942d0760082c00c15610403861901c0c2e400803a501e501d5500001d00303200c00c43c0ba0f44107235200008104c00c11148240d80c003420304101e4141900b02c12140113800100e400e05103440c6101441e284845c811004600321003201c1d41613038205007036122480c2203e0045a1100d01c0f1038050301e0421840c0905605421040c103081c840d4400700b185031194a04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 920712203 1250 920710953 920711009
    0x91009060b1e0a09050d05010e0705060c0703080901031118030705101d0a0f0b0310080325110409080a1e0c0807021c030c060b0609091302190906 64
    0x96002c41c142e55411050080b070707140c020400c03c0303254940604810f864000003000c05408030b105031000d030764507062040c02d07410400000c4050b2800301d84450820132004022943d1b0405400018030303644000c10710310380c00c0c1d0190300048081a0009480741c0c036112003036240c004040810080f10303ca072081807030010701d81c02e00001a00c8401269640c946440101c47c00031855004824210390b00400c103000c00155804042080c480500001c810180d40c0381003801c154001c1040a401c030038801d40081028110425072051440b024030107803440103c0e401480e08050900e08806130001c0d40042c140256581008403190061149003810303102c2d000c0d400808a0844101c00b60703107007a10301189001900c400454228005000000d00c01000401c1c10b4072030303112801200c210940c0490210b01181240030400c0214040e48407285801c1c5e44450034142e11030b00140d0802e5025049071900501d1442400c10f5440d51000301240c107003101003125240d6901c20241005090360701c40e2070481c1c4000c803ca0009100400c0c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 920713453 1250 920712203 920712217
    0x30d050c03060f12120307020d030f18020d080f0d0501090f1a01050d0905030f030423032a0a0b1509010b0415050409050a2307120c050702091009060b 66
    0x2003500c0102d408180401180030304e103262020b10401400916500015000714030400165000c2c00000c10360381000b50642e520862552001c0341000d582094a155450ba0750002c503804035654034010156040c0005103200d6404500002d02c00041c10348035007070058114504035641103001300003454118032079004840c41101e94455500454640300319a40c0715034080e0400c0320750b65900041c07003001c6a031441d145034040009003c07400008070401080c07020f8180ca00c041c5040c0210301404402c4a401c7c050745900c141144e2444910070342a0146408503c080210099040a411503070b0b0300080b03050104060100702c44120404c280c1b0072101e0a9404e01584190485541040c03190810f41020350350240e0a90b0f81c1c600d0820010103000010340200745020b514040d41c2c1850300090752801400c11804a42c006840b00302401c1803a07000e1000d025030058480d01c840179966400a170840c0300380d00484035032080c40f001a44c044816000c0c081031501d0902c1039403c847c1c0c4218204452b964656a03c100c50041070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 920714703 1250 920713453 920713459
    0x10c0936020d1d15100807050607080415020a060b0a03020d140a0209010f030c15081503010f0f1e060b0304030309030c080a030212010609050607020409050a0803010305030d050c0306 80
    0x548a8140200540251400354a4042c001c41d0080d40c1006243c100f00c400c0000c8072040d804440c100d10604110184103820218a8070800707034050401101c540c1d42d500600c101c0e030184100180c01028000440300365005001110505120000344980c02941c82000e640c080d034401d071801700d03c600e0034540b040c03a00d01101d41c041e001c0079008a00783c442c1e0114104034201a082c0d40566001c210040e920104591f000c0d0200d41c407210781c0302c0d0031403d1020746040345422841d201910300043c00d04151704111482c3d400050148000155113810300800e0160000450804005050000301140029141c100c400715801e0010006d036665002c0003118162a1544038005012034200081004280f1a41180c01c900c3d0081c1413802c02090113544940080d0301140041c0c0000341e011942080240d1902e000500600b4a0301d803900480f418940000e40601c00c0a90003849a0341d1000c00804005081c403640403041d411102e5117440e07696038105a9160f60100d40f0301c0b810507260a0024a98003c510145d0340550400703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 920715953 1250 920714703 920714789
    0xa06050604050d15021603110f01021602060c070305010c0f2712060e060f06120f0d1d062a01090305090d060b0d030f090501050306030a03030b12010c09 67
    0xaa143d80c010700480103075243c10341d45c0030419064621030003041221454403035668841c2e08044c017444c55044c10f28031421034210740d0040001d0920100c20404550189404440090359001440381d040d141c40e1040d4002020380d424107021a4a40c3d401035038140c51107040d6100c0240785c01d07800c112812038000c49155000720441c0f000f070a2100d00f41d01c441d00e5540b184103d40018003018100c100030300d4500c081b120150345c110b40800b00441414040480001d103024180208024005101c52030303100e028140400c406c0090b1014940d640e00c00042c1003104420010303040c15500d0f1009a002600e51040d06820f451000c140046607204280502c14811401d800d51746041c10110a44104003c2c0258124207031038590700d44080d0321185c7e0710021074224040c0309482e6010001c4503001c000c3d107a90815400b50341070150510410074151004908101410760602d0002000791003074000035900742000041070142d41c0303020083e01426400220300015609440450710741103042d407003400010782032800007242c20101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 920717203 1250 920715953 920715979
    0x60803120403090306061e08160302060a0207051806030114010f0504020a120c08090f0102040b09120f0d0c030206131211030412060f0b120a1b0b0307080a0605060405 73
    0xc0c03500501d41081c8646000c9808035076030f4940c0420341c1d0071608490f024404101c080241e0954113040e9030010b00c2080c0c051f1044090010f92440121080d100c064010200020100000340c400d1281c00040e040040c82c5e401d41003224194902a01c0013205d40602035807800c0c40384450810001c40050484031b12441540201d810042484003035040403c1150030300803e890101008116401070240806156a9460492074594100340c502040b044000c00c1a03441004107000c614100c0e0102c51240d03d0030340c0d00803a40460001c0c622716046030090040c8850244000b1000c44a42c0200303500340b00c0c2d0203503089507025102c0160038211540503010061100083c1e01d50a64640c4c0285843c2e241403811600baa410140d0b01d400201540140d40300840b003442d81c2d603515400c0540305114400e4880c0c02038030002481d03603aa003800f660317441400c2000780411510f5a0041c1d03215007080307403c00140031509401038036400c0c41c5070040e01c0ca03003080c0d480504176420044003242d142000f6003520101c59000b00b01040d0301203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 920718453 1250 920717203 920717227
    0x702150c01150b0c0106090203061005030c0d0c05130f0f3804030218040b040f050109120302091011030a051e070c080d03060b0f09030c03060901051504060803 70
    0x44006840d2815540719540021075490302c020800003410141e0072a07503100d0300d071008a821503c2d5600304403a458030501c280806600c070105a10111241c0e81002580c1e070320b41d8004001c050050240414069051800d0340307885943c4540580245882541c4080f0b03820b40700c03402c440b20203000d4081c011440455540030020102d50915003044000d4000103010a514110380c040c2d2000041017000582c0840018100214200b0325000c83d6581c001144170006410b00c1da50f038807003449018101500207807240d00d080301030250079801400c8059002c01041c1030990715040140c040d401a040840c410410819180f0141e40950b070302c155407440796800b80d4a032121002081c0d8940e0000f138042600c900d03000c00030580d40418100107103980750080c9010b2000c2490100a10303d0951800303407400c100350402804110b580c1c1d030081071700c9600c0b0071191004d0b203c8805401103450400c0e802d01c1994540701352014403108000662002c4d02512468242c095113826542c10700095800d17521400d40c40340d20030400c080d43c0403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 920719703 1250 920718453 920718457
    0x1b070501140a1808030a09060203090904030e011223090619050702071208120c0f040b0702042915070807022b030e03010c030603110103090204020c01060e0411010203070215 76
    0x30b010b040803400345030000302c00303110358405411401180d400020701c04602c82c0c1215405008007602d00c01540f51400d4080452801d0b43c3c05040201030001c003132140d6120703a00604900315009000b01040000428500030030450f000074080c0c0c00e400700e440c400440d500b480c002c140b01d07116a02140040641d0414403003000010701c03000345a10114081c00c4030209500d8205125103e900740110074047d00c4e903940e6280415011000380820a02c0e000401111102c00c40b842d00b51000c07a01c00c800071689a20311400403801502e0103072021030001800008100075400c0c2d512034402503003400d40b0301452604408800f0308c1e20744541040600b0300c000a202c040300510704000810520040c0325000b20740b5420b103000c50b9480d8200c200f401c8000c90b80084400169080c2403203103514050b8645020302805166841d050a00300413030318904c1c10140c60b138212400790740350341c0c0440343c0340e0801d540208062561880154500075041e14122045d100c0d01c003036840c040d81b000003503c10b580d40040c141010a5441147c0140c29 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 920720953 1250 920719703 920719717
    0x715092f1921061404050d031a0604180c090605091c061b030e06062803021009180506060a050c01090206160308070f0f0f050412081b07050114 63
    0x10841031001182e0a040da0603410240d504016a000742005149010000c1c2c2d0158054104510104020400445e00021718141c000119003000103041c000a8056451007045418240c1c008a0000c0c0006941005c20380364410f500c0e6017401000412030390710301144c44003050b119000014400780b00028440c41c02e10317944045000d414840c494552080d58402d0240e130341d20042d4418541c8883c0111108903014000c01c020f46c0c1a080103803205290100001c3e80c11182c850521070139040b0700c8200328104651110000185400412588884411306401002070145000340e00c829038940300c411030400c0d503c2c00f0310340c0104001083c813414074240110071211500000c5500d0515900d0b4942c02c805a2909002401612025032800b46000100d050207802e03603030302030302910411149010304c20905a1204168254041c1d6147c40500c8205414048640d8059500b001d81d4444a01a106041000200c000d20207056000700005050020340c400e561250450300c50b150203d00d540c030408024403c080c008100c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 920722203 1250 920720953 920720989
    0x606011d040f150e011401080705030604200d0b0d020d020f010513081c02150103021c05060901020a08071103070b04150e070e060a0501170702030715092f 68
    0x80c07103480302d02110566140701c594140344460000d00740f003418508000f0602402c0c008581c51958090000000c02c54200109150100000400403814603034030742c0c10441e00c00c605141000c050591890400c4065070250403000141c9180c80f0b4070300814200070354070001150f001460804d03c504c542e000c0c40451100c440c3d48504110081289040c11460110700d4000350007500000c10401442d2410051905005400388040d980300c5c219440ca41d15009105034113599050740c056010700013058100e403c00c903650758018418026842081751919056010704850b4045607200000790315015020b8903012100c0030544800c0d041003000c031000c107030784103140b0b03800504c511002c550040c8480506000c885a520300e40180b5000840c041103400c840c00061608403000719a103000711440c0600203410041c6400e00c0308250f003c0d01c2c00040f0345500900554440940100c19081e190b0035100400c0d0061041c443c089600c4215074007000b080c00030034144080c0b461484d181c01802c4015110820418000c18030368050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 920723453 1250 920722203 920722211
    0xf0206040210140d0f18021c0203030405210606090105030703030f020c06071203050f15010e0f060406110d0320090d14010605010909020903030f0f040509190e0606011d04 75
    0x111032900702008004c800c001c44400198419408020016205040101c2424090102c0d401c405a9240650791a103095502d28104a601451001c01e0850080da0301c0380e980300084000c15a564402c0c0728082c1211706c21071050b40c0d22641e94004003e5115030030301505815500460041c80000e003d0718000b8080142d030b0044801d01c0032048006003203540480000c80d0207518103125659880d8040c0034040e000380d442d041c00300d12071503c003d10321a180350030500b4a040ac251540d60600c0c81c0c6414045540303829019080e9640ea60b160035000d0301440c03100700d0b0480300d442001383d80602180b00c2c0c80340700340403070300c500e109542004c000c400410107401c90340c80254882e042854280025040b00d440380e2f4001c1691001040b05842d1074005008400203a00646090340100f0032000c41d0b98000c0300b00d03911405034007016a141c0c00c03071640840c800e004541025070840c21010600048a032054944800b91900000610903040b410480c0754507002d040e01d10301c0c080303040c0d002041000c1d0a01c40340f0f10080040500002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 920724703 1250 920723453 920723477
    0xa170a0608120d06180c080703063008040b0c0601150207230306070f0906030e030a1803050105090c0f310f02180411030103050c1e0d031e0f0206040210 67
    0x91741d03071151080002c217800d030b5440072211419000041c03540e202d100da0504211041c9051036030502000c45e071b1089144d1100b40607040010621000c440c200c6550000c103020303111038894061001c3c960250324005c0300c0d0311484000254464a12085070803071006030f0b001e04055880c00c9a004400401c1c0c52010490440045040e00162404c00089100d2100d59562a81c2d004030380d080a03000c052150019407c1500300701d0040000d54000045504100881c5016018490b00740360500020f109900000d190f9403c0c1024420307035100c001281540b0701400c0394080c00e002c13011320402c030f0218044480100018003a03c1c0f201901028000c9000301044000300221b0207000714501c12041341c0c00107481c4403c980651b98910034909207403007a00015440d0101d20b42c034650458070758907650704032078154920604840305c40b14001280c0403814103c0b440007801d014201203980c40c000d0000908018280075aa8040740d200d1000740c40b501201c5103500c51a009006192900c0e024802c104001c400d0f50b1041c05036141c204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 920725953 1250 920724703 920724719
    0x9050406110d06050906012607020c0607060903090e060d14120d06030b0903070b160509100201050433150f0602150f0c090607050a02060a170a0608120d06 68
    0x1010010b8074024002403550800e410062172044c0908100d040019807840605088403401a032900060141c640940316a14010100d01d00304140780210780105001c01c180040004540005000034403948601220b40e41314100ca000c4071604071103007a8070072521184040844c54045905c500081410b060f90b010f0100c001e20f0320390b00c0c2d000070380c00c1c80540d959250030002e0011007001d954100f0440f00280d454114903440d14078100344085d1800143c40e80034a40d5200550080d4111848130304041d10000c440300c80110080d0090030115400d42da845a100240c1c42c1110300415030400000c2c1510790042644640381c0b001c4001d2041c0f80d1080c425043d90400450071071310407800360005041541c0200000f942c180303c6e881242d5800380c050b00140c0d0a08081c4a561000c90054170081c00040c1c80f0940c4407646c50801c00c2ca0504031042c083e40202000486c12241c035032200d2550300c02144141d003902d1540b01d2016040031130b41a4495008190403035445000c030750001100900c480c8400d81c4010038807a40361640f0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 920727203 1250 920725953 920725957
    0x50403050406030e0709361112101a01030b03010902150a0e030f0f0d0c020a05090903070b0a0509010e0c030303150303070b0a0f050a0b011e1817060c0703090905040611 74
    0x10014a144c0c40b00001e0380e0011043d1f0303101e451603100b07043c10460751003c1d650003a40d8040000780601c201100c01c20a00c00ca801001004a0400102e5003413124070403c900d84040300040308070580c0021306101c00e0a9450405029000c00c4c03950207022800c079554803204044154020380d200390b0401c004070f608a41c0a940400030020503110100180c500343c218804441d241032104000e050034050740e0030390280980d40d004040300841d5000c1c1d0f41d017039140d664081d00b14110305c100800200781e4150700c024000d51409551003580700d00001c00080142d50b00c1c01040c1580c800705c501680b0340c141c0c0b0420001e0141004940b07d4000ca0b04041c0c12030342061555a902c00046a080794610505075880280744110035082c0207441d085000910100078803030080d40001d0241041114a040805840f0080d0401a10900d4102d01010360001d4a564058840c22110703c0b040022150001c1e611603c2c02240005d400001220b182551584030809070629003840b64002d010b0082c000d4a61176503420004405a0b01000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 920728453 1250 920727203 920727221
    0x10312050304260f0f13171c11190c05030f071707080a0807060513080a08040312141801050702071818150501171f0603020a2304050403050406030e0709 67
    0x140064403a01344c418100310782c2e0011f6024990080180c4140c03007011902089154100c803419040c00d41c541e070014402c3d40c5030180c0700399111a80c0f058009904500c1d50307000d9007800d558403d45000030f01c2980c5004040d5185c82812841000760001c1e60b00308030051450f1803580c4552500320503210b54a64070000c60741490820300c1e080e81d08103400900001044010f1050942c07241c404040c0d01411441511002d10380e01a010300c400c2404880d801040c241741c05151600d0020b00c1c1c000007031124a9401c4030b100001b80c0140d0740a00302000242ea11741c180340303060042610403001a8003c214842c548100f0200c0d001194407403c3c03000d560f566002c2d00c5000034021003182940140a0342511001440b024021038a050f40203040300501c40031030089844010584170451044220010f00e811040702092000380006e60000707620080e1200001100d03512168110042d5044601c00d02e051071001041c0000e0f154100c5004000031020082441a180654080c0000c501c1e000115140b05480d01c6c19442100c0c0e000c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 920729703 1250 920728453 920728477
    0xf16020f06190e010f1e0306050a090e16080d18090204090c171506070812130b0f0705030403050309010b0a170c0103090c090506010203070b0f010312050304260f 71
    0x39008400c0c0c12203020b03080300c4002c1c60007170040390a00400400b501d4110020f289070351020400ca800d201c0c400c0e04280043c0200800048035540e540e1001030041c864222000d030a1300505c01aa503064080c0c07140c6104440c0c041d00038210341014141c003100c0c1c100a50401c441c40c40c802c420085005c01c4184003820142054902c0000d82201601c806814142500072200e192010402000b42c3c0f1581d0000d030000d80841660800d8584072103142601a0b030080060030740b2880284420028290140c501600c12a4020b500c04642600c840450550580c0304a030004082a001c00100380000e205400469108600740c00019017400098000b811000c1d1a0740290450b884202c01d0968440b0b00703114864040000b401d0820405000c0d0b601d183ea6400c07544030b0408604d5030b620000322164001d204407a82c0325071000b00800305250809400c0a0342e038080c04192040780c048054150043d005000300d0713000e6a0400c0c3d0b102c042024070301c01d0514a04000140760100d00c001e000c02c1d101240c000c805841c4034490b203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 920730953 1250 920729703 920729737
    0x507140f0f0702180103110f121f0f050f100e150105070312150e1807090903020307020312030405070e0103020f09040221010203010e09030f0d020304060b130c030f020f16020f06 78
    0x3000302301c00782d040502042d00c00c01c02465082203034440090001d05407060150480a6850038429410040541c4059819100e00304401c20420300c94400a8a2288600061800200c0d45500014034214002c558003d010030698002e0203d42d0b0244015182e8240b1901d410641d4007912010641652903045071548202c1da89002403001080494080343e02608030b14800a07240f03441662650303518074920900e42c000e56a03210a40c00d051081c0f04842c0c41c0307030300501200c8041102003008902940101c406031114060083d000c40c51800b1441c50360304803500244219801a401002c0000410f00039004a0b48502d450003505146100042026988000500011303225850014504100d00004144240e48d800070041140b665141009940d40d658112500503145c3d920340c500300e4000e0010451080d44410704450386030700c2e0b0032113400c1010700710f00c00c0d40c0c240440c038850305440342030380160301d400e406003c070901a4200c01c8a0050944c001c00c0d000801011011070302c80d010071842e41c8244041100d00d00c2c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 920732203 1250 920730953 920730983
    0xa170618030c070e0a141303090f120b06040e0123090127030315140f1e0415180203100b03010501020607050c0a12030507140f0f0702180103 62
    0x19000115244038000d2018515082204044603194101802203520140401c00420002080c9034041d140503982c8916001030b5061600c0e201035007500c0c400d800c03400240405030120b24014231440400c02c070b402d00d4900c864000110755444a58000013070615410590380c0143c00d00c1c541090107003824004005110707442044a80c9030303650a90000600b03402e020381c14001000b15603a00081c0304003006c02030030311042c005946450120003400c1d09078451208a0012200810200403042ca280c0e09124107c07042200c1542a00134800359240c19065252170340203200c01d2180c1e508054005222500242945900c01e50303e23041c08140d8004454060b01440394040204802e0f0408030350141c0160550215290956140c500000c0d41d64200600d00001c01601083d40440d1400c20081c0d00941e41d400f2400c3c000358400000010020981110100000340c080c030810b85030464108101d0700d00040d5042030b28a00a500320341072040760710048003241c002a4480320304030400c0e500a0040d020b1446071a60441a5403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 920733453 1250 920732203 920732221
    0x5010207020a0920030c040902030402192606060f24040b0c0c0a081207020a120b0a050c04261203090d0806060a05070b0619030b09010606090e0c03060a1706 69
    0x1400e01611000313110820034040c6440034203080e0740440304072250140c1d0700d03601d42c808950610048214003070030f01e028510120745a165882d160000112038079800141e200301060407950354a0236507006811011802100b40b190800e200c80f101c40751040403c203000d030041d116403100550f00503402401c0881e000b00e01007045038014000221b200310220742e084140c50400c240191038503c102c6d00d144011a0014821045413100700030800240340740304280c200c2881740d0402000c0e0f05c0e8221030555000d0310f0100014070841c488001d0b01c0595100300004075007281d214020041d405c04910305509944200d4000340d581441c4c4400542c89400c0703800113000e02c202c55142c0a07080a401405541c803032041440f020007019441001d40d00c045800000c00000c0c0d40310203002c500018028810a00014201003010003444000c101e4940108035003c02044641ea03225012551402ea03405142103c441c0c400c0031901e0350982c04050748e00428000c2000c201c40d0380e1b130360514801c144451501400b98200c0b10410501c14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 920734703 1250 920733453 920733491
    0x1514040f090218151e0102160602101116030c0506010b09010507080a090902130e0f01051518040c0f1701240e03061e090708030405040905010207020a09 67
    0x180c1660400d014015590340003580b0142034400a007440b0800b0000158030f08928544482c0b50340018141c101c3c80d0288203114202240300b0001030f40540300e10312010411a01214100080f600c6aa020b04112818542514054518091701caa0880424880d010200d1601104c074100d5034420f03150140620074514220b410500b05902c41030f0028000d00440d5040d9810000300c504403076001c1030055543c1c54800c002d0714000425085031040c1480032607000000044020b01a043d1802a80484266070300c911081d01c3c1a00240036050308244624403094540d030415010f401c4804d0100001601d4179080e0000c1011240c0682d14100040c070000c55801d032650b005006c942d0b8500500030491210b41c1440e8076051214460030410f02c3d400c1101034601c408510a408802540900506542c000d00b4548400c002d0103480f203001500034440380001c58441c40e00000c9820848244902950502d0f103020304010040c1a4060281ca032550204201d00050b55004459400b500794140000343c044d020003500101c407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 920735953 1250 920734703 920734721
    0x3010602100515120a0b04030809011406150928060f030905250317070519050a061e02030403080f011a03010315150e0a18020907080703151404 63
    0x207242c9028024000461a01d02c155043d003921107100341c8181e103450b1443d2000260000d4800d41c07120b820b0108169202c181d403802002220024080000c00c0042858942c3c026208594003031105000c9030180e0f48200058140d80750000e0403151548000034203118580c120142e2400240b1103100c051161940001079080c85c5070340b9150400030300c0c1c182e40d2455a078071112100b00c0b0201c0300b400d0480314444a4140c011004d560311400d4100c08120340d40708503903d17800400049850f0700500311110303034003014003420200d00758012001b031594107103a899200007044410006010301d65840c0030036150010324001140594807aa50300d099500c0c0c181c030b000b00c0380391041c0c00084401e410320b0740b500c4124500c0c00c1500d0540e0b4102009202d020826007005c00206690541139014a840c000700080d491401c042c5a0f21a01c0c8007030040c817000a011303070f10401020364124000c0d80546840c1c041140f0301d208104013071388021507040015040c80004244051021180e00c1509a846021061042c0b41414047d405070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 920737203 1250 920735953 920735983
    0xc1315051008091513240e03040315180b0403020a0212061e070f210c09080d030204030c091d1006031406090601180b0607080403060b03061603020d0f0c0503010602 72
    0x4c1c50503c0540b01c51555804003001d0510804030070032074110320040b400d1800d8051882c2041260031f09403d285c64403a005448291440c42e940d0f1404c0f000442d86018120740300081d0b80c45105010f04654440d02140e50141055046101d0412924016143ca0300800ca5561119005105910b404c040f40140c070b6021240000401104805204941e0b40190001d266000c050600303000c000d940911143c10504080208034080b41044901682550014606400e4507888403e8900039883d80d102501a0311491000819004407400100700124043e804064600c2024000c100c610403002d030b0711407610144815a900d041d42d100410003c014604414104100074900605003902d402001151036030414481d40085e030202e803003085004550f550084543c0c03c001402d860301c44075141020701d8140c120b070200b100c41c2da01e0120760201c1c2d46030000c0e03898441e0b1200b0710030480c0c481c2081000c5010350001010140225118140070240d04a64002d100092003941e03101922503150800003803a10b400c4000c0c02c59 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 920738453 1250 920737203 920737243
    0x3030403150c09150c0201031418060a05010b040909080d0e0c0a0909080901031e020315211b0f031002091503010609150507080a03050103050c030c131505100809 71
    0x8445001340b0040b4099200341040d1110042c140010b80c054405030300740302800010b110400a100d05001303004d5905002010446640d541c400400e0811a80c080c0184c280300c1c24241310400000c03110f03800170b03070509124128040c02d01190081c0301003514003024005085070081e810200e5603042c00440c54004001c2e9110a00000c04291141505885000c400d541090388402c0903001564041d03050070414213428804540d2450f05040100d14205a100320030310500600d1703030340c7c3c120003488031603640340c1401e1f100070b080a0f12500c04800c0014150031746503600419240040c403c656001c0c00301c8030340106801030140e5201c3c0f40d4010002d010700c1a200f035060b044802d00052083d20344c03240402080e10034207490580c1c0304068030f03019210740c0242d2400400d40807000404001181e810b800c5039040b01c2c8600c0440700c00300380c40f00405032a040c000c00a90f03005410302c00d1280c030100301d6070040e68001180c45a00381c2240d40b6100461965020002243c020440c6c3e2018410300560400606a9212800038001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 920739703 1250 920738453 920738459
    0xc040506040204141905150c07270b030c0d030504140103051006051608041409010503010c0f0e04020d2d05060108060402090f0405180105010f0503070314010b03030403150c09 77
    0x550400075800101c2c1c003448a521445d01c012170034101600250400901d002c10305410441c0186e80344c1d0180728003020b5800390103000100c0d2101100c0c0110f5401c0d54264031000c0b510024204c8000f0964004e119615206603412a2004d866000e0441c034040e0103680c60340e40d180d04101c10101d22050f000702c001c1c1010701e4074081020f90001c860300318040e100300745046039a40040c14402c0c0e02d130140f440d002910303c07003001170002919074001500c2d1040010a4070808209e80e603a00401d806ca030602c582240111322140c80c05800540304522910302101e00420060500000d111603d0803140160305510b40c1c4001403860f05a0010046010003a0300e032101024002450000f000800c00c11000d800503011325004180308040303695a00b8858009030010308108164600400e42c1590038a1000085026501e0040003040d45403140030389209540d1f0160040110030b24603038484100d0080c0c444120115540d0300c201e00d03034580c1e0a100a000550041c111003c1c07180d400c06011044071a0300400130240300784a07500b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 920740953 1250 920739703 920739719
    0xf01051b040e040f02090a05040b15030706030b0a030b0a0e370822060e030319050c030d0203010e06130b0a260a050f0613053c0c040506040204 63
    0x650668500c101c120403983c0711480c00070102a90082c000350b2104008040200c0343d4195480103204901a0048014645070300195088414841d0003503501500f12150502200c0e0282c3c00940040b20060002c040207541c80e11030005004c0c054503621a00c0d5200d20305500200020010070074403c3c50400100d150040411440842c10f08000b100d480b2203500720380c1c4005100e01d031029140500c0901c0c004541c0c0411920856090121900481020820020074540b00b400c3c00001e40f007080c0e0075009404050080180700380d8103600803d101e8922880100450008034045001560003800c04161110290030b01d6010407011001c2d02241c01151864104214066610345000c0c2c41125030081c80d90780904c2c1d03101540c598a40710088120054818401420100800003440441e07001209040d03a8440d00c7c0d5034440f001400091001134800e40c802c01d101c450007248081c4c10400c400c2182d448015444400009650390409498421102e0700300b601070040e103041c640204c95108100300c604514050904001c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 920742203 1250 920740953 920740957
    0xa02130f0f0303080a0609020c060f0a02120609040203010e0d020d0e01050c0c0f1219060e121b07030c08060f01060519050f040801060b040918030c0f0501110c0f01051b 74
    0x405410014400c1c0841e414066a0340f02c0da02514450000f95543c0062704409565600140d44000d4150101000074002c4020b40c0b0941d180b80402198415140d221001000b5526034043c03c1a64155070301c80040c04404405c01181007000400d4001d07050419155602824128029039140e0610008001c96526488082000700544104a410311289032000011502103115035910b031016100302c5280040710840c6505c03002006200b41428004403c0c07014a071500c0d10418200d42403440020303c80030b806602e00e01d0a40c94130480703620440d590f255484d19080301020341d80d44070400c603405c101c06010140f1070b80380d20305024102d5810024038020720038000c0080c011003040303940100300c40403030000b980203410411100100844802409281c0d2141c030307c2c8000794014464031000c1c03854003547c6038a211100042501d016019115245c00300302c0c5440c0d099031486d183e8401c441e02d5503101c0d109144840a0405071016440303140c000e0008140d001f0459085900152025440f0442c0b005c818a01d000f601003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 920743453 1250 920742203 920742209
    0xa052107152a082715040605030403140703210501031220011104051201110717070209090d23070821090309011b110f0d0b0a02130f0f 59
    0x40b19607400002591000c81c20401202c010b10814000402814100c01052050401070f0040d0140750720380c503082c00300020400e100039a1203141d00140010400607000b03801861303105010b0700b40781e61500140c640d190b2243d40045800c602140c0321021000d14800002011414000034205c00c101c1c2d0750658070b030703030740341005044a103410429003c0401404250382210340500c3d01680c0020b2004010500440b4141c1c1c10500030706000314498030031005c214805004001080024030407a507d0700c82151210110040149a940b0000404100010058481191007440307040d030b0101030b085206006000418460866502c06200500e4003a01d402c043c69070012610a207a000c01b1090f039580000c07003981c0c088120365a003c042403040604101c0c0c2c2c404080020507509000340c3c5c64030b4643c0c20708590707101045030140d0068a2001c1790840f102171410a042000c0745030384000c10118041701683d4a030a0345a004a0301040d0541d00030030308150142d18032204e0f2002d4014039518007540c42c2049944045a04584 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 920744703 1250 920743453 920743487
    0x7030c081c08150f01020307020319140d051210080d0201150506071a070c020904030507032303150a180b040c080c0d2004060c0c08030a0516020a05210715 68
    0x40b6413020140e008104542c1c0703041d80541500c0010b403000040080700e0380c00e880180c5021000300b00144504a01007181c0900b03c5803038540505001c6480168017259130300401c9140e6507068400702041c8401c1c2000310703030401103080d4004526011104040250801a6070040e80164024400c0000103603141001082161440c4080d612680c0c4224040300c05a142543c040d4006101c0003d01090650200051017510f0007507c81d030900584240201440e4180072041503082001400450609182c070604202c15410003890b8400c0f031902c4a2084044440203c00945800e82c3c0340350300e4050b03081038010360034044e1640c240b5801910f01304940320454425055160201683d600840803249500c40321000640140062540c446469480c054510b40d582d0106444d40540000300040401e8004101c07500103416940343c0781810528514501d40c0d80c000e039070403640070f0000c0c0004181b07a1038851015046050314042452004000c080581c1406d0301500100303540d05144150710b0096400030b6081040355000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 920745953 1250 920744703 920744719
    0xb031504020a120f17190c1b0609090e0706050f0c0703050a03030902040b030f0304090228030603031101090b2206050f09151b0c07030c081c0815 64
    0x28070005040c0c61040d04107220060355160030400f40030315001d0080c0c91038400c0004003a00000c1c0016031200c1d00078100d180500c1581c241c0c040d603130343d4424a0314115403403044034440d0580c4403d0107100100030080e00990001044c0b44c80030481c2c8202c40c02010424000ca20141c1205424420000c0541c82102c00a0380d102000143c0100c0e004410080709009540201c00e54034800300502e0f00801421020b40c2c180e01c581d0510410040510780403c500c450380d08848001c5240500c2d0502e904043c2d04041e1600080030344143c011680245a4032824584c070155580c00a00c050840c5801b9004c20482c11600361940c1c0343c00d0514000420904001b81c015004540c82c06289842c20f056905c203e040b100010011810302040c00300200401950341e028800c0e50b410341302c0d1038990a0741140545402c40715050140d200c1e880d045001003900000b480308044103410b541c9040d40f0b03500d8480d0003558590100f882541b2001a090b0303107000c2e20300444c00b03102c3c09103001d04050030000008890400e00e100d03407a118800c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 920747203 1250 920745953 920745961
    0x30807090f032a0b0412021509010801090b0402250204050c2d09040c0305010503060106030c0c0807020a0f080a111020190503090f030a020d030327060b0a05040b0315 73
    0x6000f030344000030304450004690f07864a0345c901c00120010742c40203c0c0520b80140d162002d244242040d82d400d82d60681d54141a03a180a1100340501003941030913822a50070420300009a40740c0d040c44201c0d0f000c1b1001201015031510600040300c40040c0f0710810600203101d1104108482020702803c601400a17000740d04000d034401000902c0380d1200958010300d00140e80d010540c2681009040301c0c0b044082d18603a80e40c1324010350513a41c4598a80c00020760b10319001001541c1c081c00b034024540054490400d550b101c5404100c0c50341183c101c920140d2160204008004c0541a2400d85403030540c0c00c6006145c5400000e0303c10650f141084880107803050b4010b0721480200003042010301c8411200f24801380703c1c188642c8170391065200314001d20040762100c8a0f8200000c4800c2d400b94060720480118107992402c80080204500980e05054642d5410440040a15101c000300b4080e1000050500e010400c00401e5100350b407040c0d0040c0e045c00120001c43d580414042c0782d410004000d40a5070b51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 920748453 1250 920747203 920747273
    0x7060813060f06092009060a031a031203090705010f05070b1803220504050606091302270415080303012d0f181e1802090103030807090f03 61
    0x20030302c900101e1a0301e480000981d0f40141e030400900f201040860b103441e03041301e403042107040c80385d040003e4004004025a544542c881d82c0886096111482001808545040000e0620070a240e44210019001c418090b050200f40400d41c0200001d080840e8403141c54040035009000c2c1d078002410100d040000601c0c4603e03d0920035100141b200d0540340c0d141001c4a8030340010100f205034000b0407200440114030742c10326201c3c1c3c40c0a404000e004c181060030b028108494007099100d0544101c1d000d0040d51480d1134405c1d488098211444a1181e00c019030206010844141c8501508000c125107401c0000210100441e41543c07902480c44483c1ca0b0a900c2c94050207100c400d003440300305503032400091000500110034003034030081100c40343d1805403000f01070103562000b6481c1d207070012018200c2902410307540c0543e80c140c80340d2080740d00412250700015400982680b0076400b1810480402110302c0e44000b1030f001070a0083c480d00d40c41402e54031602c1000f8140760a14000c842c1035254208001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 920749703 1250 920748453 920748461
    0x807020109060c091d090a080a0c0c180c0507020d06020c01060513141003080a0e0f06180f01050a020a020d0f020901090e010b04020c0c10030219080103050f0706081306 74
    0xb0340101d003c0c00102d10a202c01048242c01d84600c0d1403181e442c5011925070302503040e0b030a000300b11020050070640f2440e1103240c0f495000c00c6041050040c142d41e244c00080300c121180006015134906a010b220842d5584000d80b0054444030f8108001082034100581e030705440c0c40409604004010385a40014841c1c078014121a0045a40407480d59880541041160007013030101d10b150303110310300c42c0d200c1090070000300c035040c0002002c126007802035900c200d2042c1c401d40b1608200521010b010a010300100306607500c0081c0d010403101c104107085039241051300c00303c41c00290a1070130783d19164080c00025100c04000000900c0752001084aa0520010a05158a00780c00610510300f42d40e4803820345004110406c0304080e19400c0c040300c10824a81032095914200c142000740401b405000104a0225440320909003031640c00c1c041c800031507014080000340c503221901c030200d0079411030501700c0c42c1c440800d154000300d03800711006020003030b445040780303400c03c0481602c248450704a14008003d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 920750953 1250 920749703 920749721
    0x11040209030d4509090c0b13050d0602070b010e060f040506030321071b230708011b02100204150521151002071512060e01030c0302151204020108070201 67
    0x200c00280f503030720400071800750041c2d0030003003908107401442c1d07641d9003c006650450310054000302206000304000c1f44034000821076a5a44100c0d00039280d106c3d03000482580c20030a09540c0030354040f4080c01000f080454890242208481c403038080e28086d0300081c10740e94000319050080341ca07480070680c191000c0043d640b00c91441d2104061078400c00201d50000c41c4101c82c2c8100080082045008142c00354041d030040c036070400d02403c150303010050200b44082002c2da03a0748003413080b03070f8000500910a2080c6071202d120004007400c000c0092a0082c50800c100456880c0300d841000200120fa0344c403100360741c2e000603d0070300350344800740001580c0412900c4c0c000306003000842010007500b020100304c281c2003114100e41c00365891040c050120382d40c00c0f0b0b41c0240c10644140e2240d0340d000c00e01900450000c00c030107031000301d080740d2140b80103101c01401713034403c640b02901c1e40018421450029480c2614140155002d410400c0318040f00c56a01030150020b8103005004011401d518803e4010b0300369 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 920752203 1250 920750953 920751017
    0xc05030702101e03060501121a030a0804091410140307090501080304032003070905131b0509010b1606090f020907090314071d06032811040209030d 65
    0x1280d58540e0090881c0980400303d052003100703100302c00d04040c040e2107440c0644106070340318001100380c201d11000400100300040311420242d4810781042c0e6040045c81c000394481c4201c143c94510303200b90031040d510400c1512000b00c81903401c1100c60240384030658111540c044d086014195240082800c0002e04d801200b9003908020010607110400402030080320711034007500d0695414400c100801891500c82ca9505400400c0300300160391a070b03048a5049a401003a041540027540d1b540408071450302d800b08212245903401b04500c0c030b002181c00340101341c1c440800d484c0c0072030041c84920981800e41e0041225503204464003d0100c036184001031301c4d138051700c04d20f09410030f62400752405805110840c0d260105503800010030380702003001d004644210b10309407030406105012070104000141401d406206a48126401008070744406050740b4000f04141050b078501d0401d10220084118214060360040007007581c40e840015941c00d403c07610385082003400c1c0c2c04505400040004404c2048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 920753453 1250 920752203 920752219
    0x120d1407020d0e0105040e04060e10020a03050405060105100f05030a0b040f1b1b080c0a1b080f03040b09190906081509061005090a0603020307030b04030f09080d0c05030702 76
    0x480c0c15000030306000320390310946030141c160460400460300c0c0e1141d4052011042c003080042000544103401a207090800c2d8402e031074a00b1000c00284040760809101d01c0000398030703042030105002d000d000a40c003500c0b09a4070b085a813000e400000d1b2071514482c0c98801001000000a10505155480074100c180d0040c01171004515006002000c0d03c038207001c1c1401c0002c03602107280c8a6009600300145141e0300e03490126105600c1e100c201c15038005540302c841a004a88000300020302c4001c4040d44e070715002160f034840c03a0606091703d15140c0b0586c2240c5076030f40100400d02034540700d441581c0030380780d04464941240d440320005d18010496580a04001c80c03c140010801d540c0110f5090b01d032210b65040c19915070740380b640c1d641e500d040941f506d0641030754604007444207092400d0b46562145090502081090fa00d1b40440c0c82c2003482d40c820380300441398209001c02c1551100c804051910743c0e20340b4901300782c10030450702d484450019203a004c0c80801410340007046824804e40710180d4008001d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 920754703 1250 920753453 920753461
    0xe1f0e15010e0a0c270905040609231c050d09150b0d0b06090c0c0f010506010e030102090f010e0d0813050f01020604080306150712030903180503120d14 67
    0x48040c840c02c0c0580c10380a21010001090194948141c82c013401c0559034020542d4901090301c02584204028400c0d154080701020a24100302d0154501444c403945001400080740e05041d18400a0001e40e8940074840312001c80c170aa1000515440b09480000780c5281840841c42c161014402ca50000c0d00341820450904288030300305002c0440041624000c0c4030744000c070410450881c03103410005200c504640b0102c4d42030308000d040340e40d1041d111035100e4508910b03c03c5803407500d4601d0045920580d1180c08103c0d455904c0001920036600650080d42405085c20026400c88404055281000518000b0240959490b0b0b5000103107030f001002a40c0e109140c12141240304000c0c000c0d14060b035800e0340002c816502c0011840c3c03055810040c502d0554841c4410402c41064820380c000c1d60345014070544000c5003601500e02c003e58010b4400140d030280600d0701a20305004045a2601d0156203101040a6180490050044014100c4e41c0d0764034450010110002c0450f00d5410846000d404200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 920755953 1250 920754703 920754733
    0x5060f030a050105010504060f0302150a02030c0a0f0219081009060b0402040e01050906010908100b040b04181a070203180604090c09030615050a180b090a02040f05040e1f0e 76
    0xc4ca060b00c070705032010f014213901d0f080b04501e2500180302c02034105411200344040750309400050300280405105030782c98032195080703181c50000f040c2c009035403900345001b9040462503c1c40d002a5452440085012041e00d07019400c1c1d103420400b4864052280c90311803800400201e0f03030040d00c040030000c0c8215229a20b032207001e912028240241c40c05400b2190210320030350700584041048074022401882c2e020074000c151030180400310f24584d0401d8580c503c1203507503540c034044d16070140b4004000d041001800d09184038000464506014000c1030241030240d415408422201b2581c01c840e1510312030b0800502080c1c00c2d200340d501c0750816903e080172964059030b000b083d80302101d0188500340058000b0301141200e02009114490f0301c69010f03142000540210b0242011421182e60000385480303030030022a010350030854946800c40d50016040c0f1142d400e21041c903020300302c1600c04101d001840c068407541e8840180200c2c1c103207030540049015800b0341d070700903280e08080c007400e40310340805030004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 920757203 1250 920755953 920755961
    0x6130e07080c0d020d0f0c030803013b01140105040305120702131811030a060501090b04140f130c030c08010c0908210a0215011214071805060f030a0501 67
    0x100003a6010740c2d00045010b140560010980035001400400c02105580d6140c004084240c000c036441340007030800102040324000514000c2c205005c501303100072401c03040d203030305c41c0c0c26450300c1750860310b40740031605c04ca41d1049621410b4403101c1d21020a044180401640c103405607510040035071003400341d00383d65111241c0180490034425600c0c00c0c00840b40c0c07039820f4103446000b40101800c61040c1d0002000c00d44003030080e80c00203409000e81e259805141c45000949209030040414203482c0d0a00c05035a040601ca244015805046a81041d0800a43c4000c2841d8080c040c0d490061407101054140900d055042c03004580c0100030781d80865880c2c684901809007101c0c1d0f00003058601c1e000080b00c15001ca8404620003a02d0403103203850070900c51440c6150043c0044104611481400d60b001c0590801194084c00c042e04201800d10280e15002c00d050717444020b144200d82020700104104841c0181540b010314901c1c00125495031024013190581800d503920781ea01d0f2040f10401003d004041d80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 920758453 1250 920757203 920757209
    0x90f0d03050c070203070f260d0c110907080405251811190e100522050d08090405100501120c02010216060506090f150d1704080d0905040501180506130e07 68
    0x100e00f0f0305a90401d0403d500320748c11102488aa50001aa0784261611904070b01250600c5580740c3c051601c4010301045c5001c0c0304492070300206840e00d05110030300500b0842104413820400702200b5501644c028030003802c00340e216030440c0d9458a0044144580f6507040103185c480e194a0f410780341c3e005001241411044840034070041441c035070030201d19003050075940744500c60742c2d2501e0780b61010b800400d43c0498420100b0342c5e103150b0740000c00700701540d45c100c402d20040d004441e031035118503a2200700811200c001d40140c1c8042c3d013008040101341d800143c80c0040d00d070751120010704d416000b641a0701a120b0b64243e410540c00d20b0064104001080d4803d030301441c0155581ca405946045003c81034041c10303034440340e021a800d440c1800a141c40050b02c04004e100c0d074448446092400994019500182c01024568000118101070140e0080224004000446003480a03526203000d200d00b103007128984840c05070b00c2e45c0000e205c0b61035100c1d0000c200c80c00001d082104140c114582d98403076010340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 920759703 1250 920758453 920758469
    0xf0a090c0215090a02060712120608030406031b0905091f0b1c090503030c0f07080304081c090b07030207050c300c13150e07020312090f0d03050c070203070f 69
    0x14000c5021640001360440d00c13203501400107464000641c413052021003e40c54030000300109002c10045045080c050301d0000d04480380119216410a80c001d0107541050311940401c9003102c9400c1c10301e60303000222008964060fa07001c48036031141e0581c140c625844008a20503640200d030001400c40b01c0c04000c0051400105c1d034108840e1100c03051100b51264410042c2c9150300030307c0862072414090300140074000002c045617113403082030f41d43e07041d042e00122016105804049030504014080560714410408000f03c10001c024261351450072600c0007a0085042503804a200030401c0020405160070800c014590001d841c800b161540e81d83c210400c0c20303e1075003003035032420014490025005450000003859507142e081e011039004020b00114a40c4c1c9200120a5800200c2c0f444c4c0d820380d90300850155000e1036880700b0407100e201844070080c0550070036500c042d001c03c0e1110004500c05d52041c00c640340c00f04580c1c4a03012088998021014007070343c103000308607001644225801c1010201c0f03410ba = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 920760953 1250 920759703 920759743
    0x4020c0a1407031406150906010e1806150406120b040624020f03040b040b0901021203010303050c06060108040b04030f0e0303160c3201090306020316090905060604050f0a090c02 78
    0x100c04c1041c0c5904059035446d1015094104015035407401000440d4020b1041c50706034803003001580001e25021014079001c0b001072426090000e2070418044041020405190042c5040c0c1351900041450000d8200c2d40d0780550f4505480070941c0d1942c00c084000c0042e010794207079140051004141c82c4041303441c908003520804442e803045c40d42c0402520210b44407003003600c0c10580341401c4503500394805202c0b24110b00508100e80d0840c0f03d80000703940698000d96816442e03010a5040c0ea140c480044d11903418064804d041200107803080070400c2c1d0096051600c0c003004a07200d2000c1d240258810700d056454003010030020070099215800450650003540c00e82d09256881003041c080c1c0c2c1543c50480145100c00310141d81c0b018400301c00032034010041c90a50b80c0d070b95594a611040380c00645400050380e110382e0301c086505510502c0500641080d2408200c581007502c000351041c03089218040c05024111103901d0a1b81c0d502141d02c00a10031880c0c10b1003a200c0c40d810003500c0c0d404c180c010800c030b00c0c41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 920762203 1250 920760953 920760983
    0x140a1d09010e0c0a140303130b0a1202030c0a030e010603050f0109030206011401050a260c0a0f08061f03110708130605030405060a05090c150421020f04020c0a140703 73
    0x20b01c00c14440c0020f80100260703402c0c000c0740050085544617958041c071003006040c091000e00702c640001050710101040d1580c07490000142030507046080e0072207c038014404e1000180310401100c00f400c5190600081541e00c00d401540980b0056001802502400d28038410244040d045040060310940c20350301da5a88501c844820111407031031890001c0c0d0144142c0030014060103d0001141c5016202410401c03400603210005400700c4954140d07010100310049855002030006108010324109004a40f070080040703000d11540040d80c0458000200c01c050030701d0701a9200c400c0c081505907040fa684c42711410042842e030f00c8060195641502c581c40003900354441c0c01620300661b44400030b002543c8030039030464003610009c1d12410352402410b0840e030a9a4400c00204036902c9508180ca8440f03240001d07515614080d40c1950f00312001428a0100682c1e8981004001e600210f038011b80321942203801c40d14141d842c940040c20b12030000c0c0c0e01e01441c00005002c40803a403203502450709c1d03404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 920763453 1250 920762203 920762231
    0x7150f06090f05010f03080a1e0c0c090c0c061505030102390606040c0e09090a030207080a03020a06091a0f01050a1401020627070b18010302090901140a1d0901 70
    0x181c2441008915045185c007400082c29a20080c40816a1490029003401a41401c0c0d02008110b5200d43d0200307245242d503904001d2070003a0301000f00148801040b11504c103220151485024800003069240e0b03403201d10315240c800c541e01c08003610000e03000715219411035410222540032245003442d448080d4a07406802007918803e170003050004400f520050b11018180009001080005018402803030308044407038a8042d040d5105a900304000c090398912801e0103400e00c001d80d04000c0032a00201100804a0340000e490f1500c9a40004001840d02e0301c1d062207141c01e8a100c21442c03072803120342c0500641d402c00045080c140c0d4811510300400950305c41c075101005c1500a00c0c54096080f060006030301940c2c01903400c0d401c2071b404030800d65a64a4410140c1000f04035004040c0d61100810005803210701003441e1200024282011498180c10200054600c00144220300710080e44540647c0503490b8000c031480180303c4440c00d519520b00c14044050b0341d01c003c82d21002198644285006912 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 920764703 1250 920763453 920763461
    0x6030105150d1107031e0f05091504080d110105090606090408090d0209070f090b0a170a0e0d080108190803010b0904020f0403050609071e0b07150f06090f 68
    0xa40028019101052800140c403156000300c02c103800100c0ea02c07810040c2c4000102c000307026251280d5605000344808850864400e8072440b006003c004051005505407604001114600c00d4211410b450200a20130b401d0400c2c0b0803500215114094210300c0c44030a038100c0080d40074002203070b0080c0503958400440540c1c5040803128261f1040c060350104001c01c0c41d10b0001d0482e054040c01c002c141e95400d0b0040b03100600b040e01e401c0300192038214000003160f41300141c100a4a041c000051a004036603400a0080c110f05c44402010101000415001c90b8103038410640d20507000300b034480d10003460801501003038092003266114029140340d089800c0a810b00503034541e522002150550342004c1c50440c103504000d02107a00b05a003000083c1c0311110700c20150000b075110360014030062500e45810340c240303410707540851011020241c05040e14085c0c9a02c00040e07904202d1100c1d110140e13400d00c55a808408643c11401d586401c3c910180602c0f01d42181e03082c4e8a80c0c420034042e00d15041c1301c02c4111 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 920765953 1250 920764703 920764709
    0x7050d0f170601080105330d060503010e030d180f12080601110d03150b0d09050106080318040c140a0906080106020c01051909051f020d261906060c11060301 69
    0xa40d001300511440c541008190120b604980503e00390041c400340c1207103004140c607034030140003c0201300c0d081824a180134100c043d081c217500a1081d400c0b002e0909589000740014a90f0441c2c031640300d2000341955040c980c3c04c00d5001904010001414140601d0100040c2c0d0008000f608980000d0810b501801032400e918251000030101105074080c22001015980d40f0020355068144001808826010250008820020000880c03d84038a051402c50301d80b50b0204400790400d004440100440c881140405402560b0100e0382d07a543d080100c0d1031040120b001010b55170003160507600c1e81da00680079001c1c0e070303100d4071504416601c03514243d80d2000e0242c0f0003400181d0401600a4055045d801308012440c00d0900404164480700010f0240d203120310491900820098210714190f810040c402044465050032183c0c034007a030700c15000002e0100b001d07500c000130100c0400d0086c840304000840700026851704101c9580c44001c01044615021000e0b1000e0324107010014551030000704032812 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 920767203 1250 920765953 920765957
    0x1d040b0303040e16031806050c16030909180f0f020f0405070302120919170c0106030b07031104050612070c21080a141602030c3f1602040207050d0f170601 68
    0xf21640031f5076a40e01030030340204505c0020000303200b16102c120140c2c510a404070303c0b94075044261030428643c5c0d411a0040030040a0f58030201c19079801080a2400b15070003950404030100d4400114008507043c0c403106100290040d00d02003c0000e02503044c1c0c0501200f5589210164040d1240030002c2d0342d0344c1101400141c5540c05c018a14001804443c041c001d54aa0425440c10001214403090031100d4550050326040080700420481c01d500d482083d109004030744089007410b003000046005030003014a4900e115415601103801d1031302903110310890baa84604001c40000712041400e5540d00100c0744140850403480100b030303242e4001d00801c1d0034848203a0318100d240d617511441c40194a010709141b02580401c020301d500c2c940050009a0f8005520880440b14002070052401510300030102543d04a92020402c07004600300c0080306c0a01c04901040b82c541503840c00020020310440800030040c3c410000340c810f045402180010380d4420720f441e030f1200e04103190880c0741c4006040f207050340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 920768453 1250 920767203 920767241
    0x8370b06060d0902120a0302070e070c02010c0809040f1b0512040605180a06021206040c0210020919080604031103120606030a0f0c0801150f1d040b0303040e1603 71
    0x10385003400d00107014251400007022950fa8040d4001c44c0786201e17070144001543e0002c4088200b40340d0100850070007400980c520030720524040500812024600c0002410011220011000c0c4107144003901c0034010000c204001e49880e07225114010031600c03060207107494000501640e0a400342068038906a480d1214141695880c0e4941005000040180e41c80e508421414240c01c802042200030030340c071030500180d45084100020003840001000c0314451810424070804195000c6624041c60800c1c480168031000103100040c0d050221040ca100242001030300010900300c0012080c0c0a180262508940178040780d101310340300c1c4036070705455848012002c00b00d01c3c7c0703043c440f00466012070540400611017101050752000d64030021096000610240010302200445011100d001441410314000190300004040d00304414a031003804403100204e220085501d40d500a800307103900080a0740e81e182e440e0040f01c0d0340070074143e915403a04c031802c1e001540c1140c080d100f10300c40025a481f1246c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 920769703 1250 920768453 920768461
    0x318151206040e01111303030825080702190803100902030c03070e011404120c06031b08091e060a0f0c0816111603020306090102040605070201140408370b 68
    0x10001c0d102030205400ca565031005c040100307112080107410f4868103001130040051440c00d0042070020701404041e800700f121000c410308461034944c00b000b62441810440030b11350b154941070742001041100048103200c101503100403c42508001c0d407048080c0040b003103d0946070980d2900300e000449082440407010030100307608074003a20060b204a1414984000070704001c0802203299001580000c6000c44c41048910800050341048801340003107180801c00070340c1000101014400c0b514401d01071202403008504412804d008500000072410750b44004001071000440c1c1d00e1030111102e0702c2132480c1582d0358208201900601d40c48442c950b882e50807a891b8000c1440600180d80803201c180950554041d00d450303000c1c03140a02103c2051045480300d481c6005240c24070900401c40d4119902c100000e12925800c00191041d071902840c00505551007068964220321917508020258482c040c1d941c864181e48003c450911091200c4e0036401c1000c500a903450800381303103002814644404001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 920770953 1250 920769703 920769709
    0x5070c080f210409140105040b01080705090d03050c0102040e0f0a020a0c020906040b031c0201230f0403050c071e05010c1101030203270309030f070303020309061305030318151206 79
    0x550550a055110324074107135a0752103003421207a132840c40030300700780c0a0320042140785428461680c1c500400e00f0101c05614055200808074445c0b5141c0350311a400344901e5100340f5202e801541c01c20b10b40c4400071940c0f181c0f02e8006a002000498010598500400c0000c00585950003556880030003519500c100400075400c2001200707000700b1240e041030769400360946c02d680412280d2582d10300b004080e01c0c0380e006260000e0941701030541862208521490410302d0310340c140490741d401100b024020101da1981d280c122601d100740003040c642e038840d1040101d40140c02c0c0c40e1032010407001301e4842c4a515600c80055a590812800180851000e440c881210754001e8009581c4150903000001941b010301c070100a0940880c591180b03103910210b8200058282000040020055500203200481c45c2d603030025030324801c24110a01448001c1401c01c062104c005241000d00001000c0d80d46441072107a5012880e040e1040d4180310711102000d03200f64203607034821180010a0f07040a440250346070014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 920772203 1250 920770953 920770993
    0x6070c09020a030b0d0c090b120a0f030e1906090905190e0f03040f171203010b091306060e030105070504080c060c0a060903110105011d04060c020f070605070c080f 72
    0x140310149038903207034039420f507698032003038800f405105400c071ba407100b420050b540c003c48100b1072540d40182446402c1410900700000c1850901d58070400c04031010201389000c03070391480c0340d4060540200713141d601e8882c83c1c005066180182d444a60f070366031314280e03070341d01501c25260140e410440c02c02d045c00411144182c6500142c0104d41d01c60f0407101c1d030003800448145580e1255005000f00144040e09014487e03148141c1c2d004072101c8001002e000031859500c41883c4030620074004c0500c0c0c002070036500b585521640c0c12429807480c1042120a0786d4010103042d80e650088040d1081d4a80000920414091001d4905440ca0715000304202442101840303000d85c408203181d0414410184a0710008203103000f20001140f1903074030840da50007160b00301800c0d9401078002c1c1c0b151600c0c24101550f01020311180c00d5000d604040c01241e09900054143c3c2005205986040345008052001c626690031400528106c1d214401203001c10303985150f06902d400103d031500c010b80d00010403175405c0e0044003031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 920773453 1250 920772203 920772217
    0x50901020f09100c0822080312011521141003031b0c1502010204031202121206180103110a0509011503021b03210c130b031005060d02041406070c0902 66
    0x14500b40380e0113a9280c1c492117800991020000494520380d1038009052640600700624010008508089541d540038501c80814003c0f0080c0c0c0c0440c3c1d58031030401303114450316480c55070440001c0b017560400f4084040988bda0006003c00b0320a85000b050140140c0c082150840350103039601d00850792851004a080e1020b442c090701d100b8130382c00010840400085101000f444180c00050740c5514614146024055011071007043d50000c0040c088040c0d1141c1c110740b800c003004540c0104540d43d00380080c2c4448203000c0480201b00600001104002e01440f24002e80f01e01111100314607903440d420002140000d004803142d041301041c0d0000140c0c020b4000c1d140e50340c2d03048044403213500c400c06041e196400251031b82120111004240104442403c10203402168a000048c81c1c240200c0d031068403035085104495400b60000001504415484040006040010207d40d503804401c1507041c080e411070f000e104c03500d8640000d01029440c001040319502c540c84a42c60920703500d441d000c1c00007500501e07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 920774703 1250 920773453 920773457
    0x20c010f050121111215040b10060801091e050406060302090a110f030c0c1b01090b040e070f0207080a030302030f0a06030203150604270606051207091a04050f0406050901020f0910 79
    0x3070502206102400a4258800006c03400c1c0681d2415042203030750000080c0103600305030030210051120590000c80903041d1040100080f07107000880c07440c150041200508000546d2402d001d003c1005000d401040031607000715030901054489040d41d50803100d0406480c0041081000090242c00480c0e000d56802105500254201203848003094100700142805580354821020086010741c1c11103080b20260003500d0240e81003074103060403428007080c041c3c4100306006041e04250001d41c0300300100c0c40038100e244140c44409416140c058003030342081d81c410b188140100001050441ea0703104007411030750000c00030024840c010094401820000d460a40c00c82d48410f19248640c2030507444c18040d007544070969004031740780e08000c0100c07242504143d1040024010003148030724001108030076a40c4444000641200b01d44c4002c003c800e0042da00c0707411600384401c1110116071450f100c2d00c80d5000c1c803030a12507591103881c090708074400c03031006803c00d000602552001c1d04000000300002003140c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 920775953 1250 920774703 920774719
    0x30c0d020a03020d031110021312020307170a030e030c0315150d03210b090c0c07090f02070c06050708040306020a0e090411190b0d02090a09020c010f05012111 70
    0xd03000304e92001c1032410160089104900a0000b01000b0403180c0540c611850003141480b103103000200e4180e1062003003e0110039140c0c624010b555090108078000d0180259134040c01007810141a01d541c0509025000720b5103114942c3c0b0b490a0101b044000c103038009010706228101d10000c81d55100c0d01403c4804503a00301030044030103031106104034a0050003600c5200076a898840c0610100746410350325a401c1d0b06000c1100c4098450380c4185820623110180641c80d0452071b03544500e03000141e03012400583c00d14610a01002c620f6008105050062203442441505c48105540d5403040c0f61004200f00e00803c41000072070510b9014080f601801d01e0030b21024050400000c0050f04c040d502550f0001410440d90481d10700721891403000b804c40c00160441c14035000f80401c85010f10340e105188241c000403c0d00043d507801412602034552810119100d55056001c54028030528200100161a00700081203a020b01c558070041001e0880100048034481c2d951650360090103d080c640014032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 920777203 1250 920775953 920775959
    0x40905070b0f1305030114041104150f060f09060f0f05041d01080d02010b130b01110a0c03110a030203031803070b0c1b01050a0c03110307020a03030e01030b040b030c0d020a 76
    0x7200e801422414642041c0c651140d1000c40b030400c1c407040b00e90003144241c1c50401903409280c040902d06500036046998002400480c00200e00601000c89c050350311440d402c1c1c008030b540650000d0800980d0b065585008181c01c50034004d40308850310b409400c1c0401d10408444450500c11096010003022902c0c10500b400e0f5103404c0701000034201e800c0240e40d200e281e00140880141001031081c494914402402040039880224460009468104101c603807900b05014031640503945102c46010780100300c070f003403142a040c0320700d40c2c40940c0001c4070b009220382d5201465203411a4000d0070f880c0c00801561800c8400881001110305000c1e80c0e0307825008282001a9003031000c0f001d070200ea0040c42c084d02c41380295492040754200c592040e0707814030205020703800590f0343c07003d00c940100c1c1c0c3c50305044503416007200d5030502e140120b401c02988804020300c0802003540c40013a0982c190800c0c0c0f42800720100703050401090b19000511950950b000840843c070b1807074295100b0071a00d0000d811140d010752 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 920778453 1250 920777203 920777219
    0x51806010806011202032803020c0f130509150106080f0702070311010c0501110a0903052a060f04031b080d0206042103090503120f1803030103061a0a0f080d021b04090507 75
    0x80c0d0003422110200b800701a0007031540620410400c1e0000700c1d650600080c9400c0014501fa1003005008933080d0ba45e400a00511000c11210007150036080c410031042d86d444038021725243c4100c903480c810701c050f4404145480e000155150035250322118204140780b8520045424081c00402980c19640307424074000100d40f500c0060083c48031036038a85201e2410740c10300501d0500c0b4a0036030101d040c0c1200501101400880240c8074000040755815610702e4a14000000342c011900b01401c40e20f4000700850309014111001350444144006803402000c1602c410390701c500041305d01030903000450804144c05014900404882d08450400007481840d94664902d03540005d5004d0495000c0c4000380035440c00ac0413801d40d88442c071001c0b060041e14142c00c0d19906c9010600c0010440358892818020a070042209115106c030040c001c0742005554200d4030050100754400c0c50b80034042d010201070320700d1022452449001c0540901411826210180802071203102420b41e01c0d401150004a0420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 920779703 1250 920778453 920778493
    0xa020102160516060203180d05030c120301170a1205032e0e2a03071209050c150909240604080619020a2c0a0905180601080601120203 59
    0x3034010030040161072401c0c82c04940e0f6024682200c8255401845071044081500341800c2c00c00380c0c10f5580402c0d007000c6140403807450045d02c4282d006801000b48202c070300c0980303c001c5c50403901d1440c001c6041812280e0701c6500c0b0f4200d118081d000b00c9078000d0251400d070041c401542c104010040c0b00722810004c503404007244100205000003241020003c1140186080044c0e0b0405101c01c020414210b00381115000080c4c885091075800b1804000115000d024610b6843c6610042d035040c404003110f850040d88a8410004035441050341c540c1d00185c0d814400250b410100c00608a540e2a80b100070100d0300c003900c0c80302d0898aa01407401d40040b162680c8024000515041c002407880f42001884000e5842d0075042c0d20707007030038410b20856100ca540700b91781b0318803030043c140031126640c070702034000c40540c4205288d2500200d6050300003610941c10303805944500d902100c2640c40f0000150f1881c1c58030701c00c1c031940046512000052015036050100c44840d580300804490a230089554020821 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 920780953 1250 920779703 920779747
    0xb1311040b0a02010b031011040611030409020c0a0b072330041e02010f05090f120d02010b06030606040501082d04020f010212161104050405160e010f06050a020102 72
    0x517511001440b03100e060070003841030540300c0d0720414042c40342620180c102c14002e41c1b00b40000c00c000d003110103510080070b208803000781121030760942d514100c00e100d180c2d80d841c03c0342d011106040719000241c401032081120362601303508000b28012101c108506540305400481d4080b19485198801000e140362101400d4450260f400c031040d80c500e07042c01c1c0300505440c030b8141000403c10380024100144c0c2c0c007a01961912426080040c2c0b2a400e250208500c2408601010f4128100c8129a02d21050000e4040703440c24a0354000c0c4441c841c00402d02440d0301007030703c038180c02c00801c1c04240119801094255800a41c0614500d4140e170714400f80e90584450824940b0a04403550600065060680120078030304828002032401c4045411141003e20814180142c00c00b0780303a00400402c807190407461080c083c0100140614180f41c00c0450303c9105811445081b01007010000130b03a404601340c054101c6a881026420180c0790880544050303011018080c110b5508010921001d0402038506140f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 920782203 1250 920780953 920780957
    0x501090b0306090a0809010c050a0b040605010f05031606030b060f2a0c09040222150906150c0609061b0225050a03120c080309100606030b1311040b0a 66
    0x1500c14403105041c2480e201808080302600250007100c0810000f004031b540d82507003860850240b11042c28045d003440d03080d85c070040104003050140000d015180d08814180d85402425100c01c640d1002099510441c802000340a09000030003040300d140030342d00c01907503208050103152508002004504103644001c2d5404030701c0342e04140a2104103040c540e0f410300b840f0103d000708205d001290014441c0007008200900c2940c8a4001203213a880842ca1180b100c4503015050080c51a803100c107900c006218003c00a180749000800a4010648102e08807018101c0e2290704121400c7e403520000380100041c00c0d22081e89400034152008101c4404801120741c6901501c092841010a50a070b9a02d200a100c0841d820700304c00d00056480b003240710110390703100354422a0710720000e100741c0d501c513890310b409410950040200b11950b44041600e12441d44400002c004154460744240c0460b070f80c9500c11a000201c024070b0746288466644440f082c024052411030515549904501043e1302003a20140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 920783453 1250 920782203 920782211
    0x60406090608060609130914030711271605130b03040303050a111c180b0412021b040203060d0c0f030b0108010c0512150a0b070201081b04050103090213050109 70
    0x86141e0b403010754180c00c881c086075414500090940020042d250705840c02030186e40c3c40714a0800c2000d140c0704214803550b210248c175204c410350305082d04584a2494500d004101f444964000d140340086958114034040c0000200350f05c2c0d416040755982950044a030034040200615506d9403404500d08008108000119580b403900e0700d8010240c40300035290769203c500707000300303448d0b50804041a154191041d0044801d44824440c100018000811486c2007000072128100e080c400401201c038400c5029061444070ba1150400c1260385580605044000409140724510707285130640085402c604c0040004055048503140c0c1103003203950303034807600541403e03000400030080700540b024010803221008225140312000301415a2180e086c0c00d1030089154030004007440b00156600d40440b80c050b040c03040c03003070300c030101d000d90f81d030001d20180d002c10641c0c0e001405004031320703c2100849410703400c0c0609003484c0500540203094a404200ea008441c6030b0103410316802c074481c581c001e0480c400701003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 920784703 1250 920783453 920783459
    0x210a0e0a03140c0a0503100b060f0c07170c06090904050a02040608061f08031603050d1e110c0a080c0a061b0323040f06060e090609010b04090c09020703050906040609 73
    0x162401060310700c0d40f4080c03005131a0030091039901182c90740c1d100d5181000070811000860000f0028406c1901c0580e003024041000308901000184030b500347d40c1118030f45070501e6a4a006079690380d01c5d02c0d98595200c24200300040b02c40c1003680f05150402e1040007111036107442913000a040d44d0003500600c0c081c1d4001c904206203004207080b602119161100c7e08403a2504203c0140d0720b9110b0480302000750f180c074521600070184514116072140c50022800c120400700e43c00c00c1600000401d41403020f490522000b4200400d0303102c01c40e102c0d0310054005180702c01c0d01e90307550740c01c41c0c02045100c0500d020741b03c403000c0458228061008070b8050100e04a03000110490041e0403103800e424444900a4842400c0d8400d5500b041246d030042d030840040c401e000140e103402405020359400060a6008503018004001d10004072140510761040092000c06c0d0900b0500007141c0e5808006072442c22448810010300a20b580104030072400780c1b400b245800751003400310b50a580680d11140008090042c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 920785953 1250 920784703 920784743
    0x10e031009030e060c030f0f040f03060915050118050603031c1b090e0a1116060c0e09100306150905090616031a040b01170109020903010e210a0e0a03 66
    0x20040f0b102215514184540f03050303400e50300d0246a41142c0d66500008001c40f040303004005075030040a0600041d8405500c2c1e1070490058012540c0449442c4003202c80707404000103d0080c01c2c141c65075120190b052501100750f420160401601311030309408100701002c8002003a02d400308a4400244003c2103554901d0941450005100c05440c01c00846400600c0749006003001190030032815a0081350302c00221400b40703034500c1080c001810312154040000c040148030b030461150350740c486d00c40198030f070300c000144940248109c0f03400300643c6c0b5121041c400114140e1001d200347d5001c0c00240d100588444020302107c20030303105c03c0070f1584140100120840c03000c400320140040340c40c0c180651039201c95041c02c1c0c000170104252040d0b441d40307040403e0780d208061410300819003080d03400040d65a1810b9400035440203c1d500c1c060350030400e00c00143c40000940908140c11100319203495400000003002d1600200c0c440020003400d2440414542d40c0e41e82090003840c01040300c130000c08140510 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 920787203 1250 920785953 920785967
    0x9090510030c08010203040b0f09120d06231c06060b0c0a0210030b011b3003110408030406030203090f010501140103060510080105011d0409060905010e03040e06040b010e03100903 79
    0x3c0b810003a80100100000903c0322032076190080c61170303c40c100c1c0c280c40d1075150609201d0000da0020a02802080300c0002481b41e401150444004401c0c00289284200c01e00d80e041040c90b040f603070412004502d06440f00918502c4400c59070040a00041048d212284140540d003c02000d1180d070b4481da003220194500602421250f8026050401520700d2400000c0d2808200d501c1c8100c503880c688035071030140503403c5881401000d000c003000300f0501c2c8844609000a400100c0000000d181c0700c0c110703c54210080c125029652100c0c000e5003014075104044010b540014800816801000c0c0040360780c0009014a502038803400c80c0c0c0b0000b200a810004080310380652003503105419480000a15942189045040d40d40078030740521003007445444e084020b148110041d4106103400c030319005114040d407142403d20310600090064002c0c400d07040c1c0c0c3d2030046002d00040d408503200440c0700c9240c00d610554035400d040c100907025240341c4001a0a000d01d81c02c60014580c2c680002c20101540249 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 920788453 1250 920787203 920787209
    0x2070314060615070b06131b0f09080a08040902030402010e030709061d070e19051504090516140a03090f1a18030906070203120406050a12020a0c110109090510030c 72
    0x1490078000c03162200c020300c5174050b085034083c1d031404d1492440100c3e65006034105284440344840c10307540c15000200440b100ca00000e00042c07200c3e10102d91281c0200c0c0f46058141c0140180d82041d00b01400c1000a40c00a40124144100d0000d010a1a01d007480020b000f4001140009082031030801c683e411101840b1080b0142d007000c404001340f01e40c02000c00349181c5400d90719450180b41d488011142140c01c1c3c2c004551001c0314002054080c08007000034002d490310f03175005004c1760702c2c0c03607087e0080185400c1810740824902d072010000b01c81110068042c100d1035141c0403600084580b1000c0e524000b851007641d000102c1c20b0060b491613042d1903140d070010074200f000b0701c5003000c0c0c4100355120700814403014420f6a00041001c2550303000c01042c160002016400c5a42d070390303070306c0c00540b2070741c0202110307808144031480d6420302e041c091003a54200403864440001903c030740d0761004a040400305c01135041c080a1040801c0c009a00e01c035551080d051070790901185820340c02e040036103a843ea4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 920789703 1250 920788453 920788489
    0x9081911210d0e100c2406090b0103140103050d0828060816082503080a0c0c170d03020d1803021f050c0702090c0f07201c1101020703140606 62
    0xc0900703000d40c4140c03640c0d42107820154480300c801401b02c82d0b031a2424103003581d0450314101100402c0d414103907031260080c1c2200342c800f000408480206144121000d02c0007801c140c001c9291808031600401541f5404139451240103036444804804100d060002d400d003088081d41d03118240b00640c810880c010079401a40e000300650345c600b50303580e50744142c031218185080c0c03520390308940e20031614254074000e540e02250301615200e8805008210008030002a15410100304000030320780c01c01d84182041c40e60711800750042c01c0200d075042c0c0295100800b0f000d1155500d0070040d0790502204019004c09100c0c0e4050100420849541c1c2244d0709407030711181243c0d14100600000d8501c0c0c000b00c6145940c16110001c150781e400544c4800b90080449400014200203055800c0120340d91002030010004029280071400c0c3c03109206256481c41c001d40c0c019154401008040360a20380041d40890701481101c1049449a45800e80c29a0070740d80b004141e03004c0814420f581c64290480c0f0f034074210798 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 920790953 1250 920789703 920789719
    0x603030e0607150c030209030f010203101a090609060409051302120706081f030b040c030203120f121015030e0106080319050c031201120309081911210d0e 68
    0xea1103101040110038582d0f04520f0f500c0700c51180703550094040d1110404010182c5004908549246010358422103030341e60b015548100103c1e0500300c070300d030840d9a1101e00d01010300748001441400344a070320803030700a035001005100c0000c4078203242c05a075200340c1016800091080451051090044086030440c0003604106c1d014841540d0050000da03101c0c3c49002c00c0c40501000301511861840140c00251021a07054108400c0c041c0700c140100c00c50388241e044078400d400d92101500d003801142561030703015100300320011070203840a0307d45030008200811160002e5441459410140108030380c000860f403525040c81003c8002c6c41990001e224040165140c11a898202c0b40343c1e030881074000d81072003804034602000c032008000303543c0d1520b4200c040351207650319949690070f00b86500b0310840000340c000b0800b0070040b03004030342070403001410502e001c1c2c4d14a031552068083d05031040d80a8000962030b6104c150a440303c420140c5442d0110b016042d41401440c0051400b4130384400d40303000ea05e403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 920792203 1250 920790953 920790967
    0x10c08130809150f03182410090c02010b13050c070f06020d0513050d0906140d09051606090806061e030a051c030b010306080a12170108010603030e06 66
    0x12501240c031401e81c000080d69440c480c220000715855000c0c4080360100c40c000c5540307285100500700071800340692400584d03000d009036156950300c1b0000210300071040c480e1501c0e10b04148038a451181c03c040b103940c00e8030300c00703441e0300158088805200038440180c0d107031008100e15051403d00391040c036812040034000c5150210003039080d881028002090620402100014400f050381903445020685806001c0d900700180850071010409205492074090201c2c402201d42c091004801100c80c1500e0b110404441d50280400a802450001c10002e484000c003600003a0b060144038009801018070940c1c41e828070f0001410440305401c54500c80d4003520a00100e640c034102c1c80e208104040e26501e0302480c0c001d0102e8204408690010b007588640000041300e189501e03c08107422125540c10880620b82c0001107007581d405119800043d0002c460182c0441d0402d12440310340c40301070602c07020a5041e1041110444c109a11403200c9941d40c0703805004240d0311a8185030301c000d08076036440c10480 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 920793453 1250 920792203 920792221
    0x1050a11030411011407123506212a090112061802090a0617070b040509100b03091c0c03020c0f011b030305010e06030a08040614071211010c08 63
    0x3c000000b0390306218290706104074004162044031030640e07202506144245aa0002a245060002a011112a2004900864083d98030070704282c5071903130344d20130003948036501400311544c000110000018151100050740355802c110083c8181c5c4446101d64048106c40ca4015090070085602c2d80705505210040181c1c3d004c280880078444c0c0c105000155081707105800e0620b00c003c0200003900501c00c1810402090410303409a0304903a40e0907003040c80c850114110985507081c40c000e010041609200070300c260300300304454070751142a50490080203529010103401640003200c8039007071503101030744000c40d0f5aa481e54045034000f03281003035054080543d4010303496050030512540204002d000c284540e078814210a209684c000c0e030850f005200e14100203025100034000c42c00342e5600c05004c6034003410000b690740340075034102000c103080c241014000c6070880d0268480b000c00e00402c0c003001002c03880c4648070400000305612143d001c40304200c0091309481181048000b4008034600f0000005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 920794703 1250 920793453 920793473
    0x10206100303180515190306081504050f0f0a050c0a0509010e19051303030605090705190203070804060309120c11061c05070f14040602030a03050405031b01050a110304 74
    0x107a4541401d4088410f980c3c2401804007070b43d80030755807048180038500c010b0001400282240660803840e1416905482d5040e030039a5043d124800d0b00b1740c444a510311540307661984054000d4440c03003c1d5019581c640c20398070300c0c00b40e0030f8002c0c0c6010b411102201d4100702040050850248042c0c804c440c801e481c000c006850240148603070322440c10b1100005682da4500400c0c003042098205003000035003014103001142000d081c0c0200c02007464100007107400d280211943d441810241c1e0f905181912010400c100e010b08030b500141548414480140000d1a0300301030320140c415981c000801402506014113001c003100318801c00e000308841c81030003054034400000903645041d0348040d45d400191640c0011420701c40303054004c1c07515090a000c010340e80060200c00c0b5040c141d5a50129140b00c08070709020b442356110300c0f00076038401c22220140c07a0007500025401809402075904140d01c2e441c02441880000b280058265550010010f051120f84103104000c00c2041501d800c501c0c1c2a55203e00381 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 920795953 1250 920794703 920794709
    0xf08150106030b1206040318050d02100309020a0b1c050723160f1401050f1e0709030b042f280503070312021002072004020c0102161101020610 63
    0x15483e2046407101d81c49410b02210508031160448261380b50905008240f4907084078000c0d840c9210460004403031405038001081306070010501d4522120241c0241d00074190350070300300c0c0c01c031800000000d80912010003402d02003001d50701c200f4460100700340700c82c11920001c0c070a900740000032241316280e140080590405540d5080140da803944001b16281200d0080900180ba1214140c0301004101c003012280020f0b00409000b8801740d00c0b000b5110139240c034104c80083c00c144411015002003801225083d40024050900303a916607100d4442c402c42c039074203c8c0d094a421124008800020045510100c21a20003403010310050541900181225059094143e14903100300e0b07240c016400032180c0d001c024600181180c00c0540e8910b4040c007840300a0464070094001c1c83c00b80030191000e070089442d542d03448980d035203400d1001d040310401864011b4a00303800a07424010502264000d100500c0c480d10144503103080d46185141044101020881c1c5504542142080c040c0c08100850350b041a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 920797203 1250 920795953 920795957
    0x310020c07090e0a030807030605031b03060f010302130203070e0d050309190f030b1015020f0c06160b090c041d060a020406050301120602070b070f0e0d0b07031104080f070f08150106 80
    0x361f140c024046020740026040564076010704d19200c6e01004120380e50100f50310701a800c0d0307100c1d903680b1a2050425402440040d411488592405036003480960013154003600c14101156202c5200f00071520481100400310341690001402500d0f510703040003a501c0000701002c0c0340c11001e0a21464000c00480703440f0041100441c900441c460b0180c80c3c0180000d45500540c00340b0201d07110000a6030f40303060030855000c60140440560481c201a0100c1e904e41440c1040e01041580b20780c3c0e2188201d01c010b04c02a00c601407119003100560701c80c055000c40d05501c1d0703c2c06030082400c442d8141000005040c008810344100000c005a0b0380207030559046841408105540300d00741c1c10004c0c060700c80c43c240100030140c04030400c90b4240d040802d20000d200c5c1030b900c4445241d03844081c0052503115940103481d045518001400f524480c1c0c2003490180c030070344585420300750340e60b001e0b03454060441c0f002c04003500b161100b8000740d8110000301004012500041115220a01c0151404001801a901 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 920798453 1250 920797203 920797217
    0x80d0b010905030a05070627180f1b02011a0a03030305071403091b01021f05062b020910060c0f03051b0705040b010309240b0310020c07090e0a03 64
    0x11590380502008001440083d0541d910038900e45031441e01d0f40b469010304404200d82041414039080105207100d0b5262820380d0b160b01d03190800b468000021810b002003c80c890301c0780529a83c103943c0b0f005095502c550034040f01a105500300b000381c2980c03803d002080726040c010283c0c4140d9550032080c0300c210394050500185a85030315004441c245170364980700c00c400c0400001d00c0300c1e00c0000500050b8224080320081c182100000c012030712107901418002c0250300742c070b80b8070240c0030031f95001c9500810002c00246115212008060348a040015401088840000c0400070350030002c03010380e401ba504054104a6034108100500001d00b00303000170b40701503521b02d1700388105406542202c034000e440140040e41c020383c6200c40b9544080790b0150f54025804c0c031a250503e0b500034041c001a040c1c0c082c1640441c0c1c1c0c2d901540c4179210081c6050301c04003a850b03a01a010585091100b1000420704000250340d80002c18101807411440e9440306014030710340381410784800301c007150701d0448070780c90301d0050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 920799703 1250 920798453 920798471
    0x3053f0c090d120c0f0b010608221104020912060f06060c0a031d090a150801112502040608060708060a063005090d1106101a130f170703080d 62
    0xb241c4180707944000f01a00c05400c17442c001d0012025250781260b8030b5a40d034061983d901c04c0c119500030071304040b8a000800d0b41191800184003d08201502100a403005041c040c0c2400020040305c440001d01c81503411180510a4003290080d0b1140d20410a480041c078180780c854ac425569105540c0c050100705015050b00840c8036403140001c00707030000810541281c104031110030010320882d03500700e0b000d440075840028845018000d00c0300307e0303040019182c285460003003610500e0881602c20200700c10070100c01801079070b42e803150701d019140000044c04d251526240282071143c014110740d2003900d046408108883e40142e02c0c422f0354000c2e1460b0051000c0110a14850030255032690031094101000c02c102e400c4009500d4200401a03500c1014000303604480c0c944404d0203840c2c120424403620000d2280034842090803d0f46c210220b1018a17040d50000301d00400f10300e5030001c0d40c44070f2540904009484c1040405210070b51401d02a21040c2c0c9159281030ba02d105422400707484980322a605 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 920800953 1250 920799703 920799707
    0x18141507091719020118180203060f0103050705041211090906010f060c050d030b040e010903020c042a0f020a08042c0709051c0f0602030412020f070303053f0c090d12 73
    0x28010004050445400070391f5804140c040e40080307480e42e00a044250500391320390712038060180680650780b112031500b420140c0727410142c00d900e001a2124a40310380c030801c1540798504582c2c0314403000e001030009075041c140c10428000e02035000408202d402d80171440800c80201d07541d0384911070750500003034170300000780468007900c581c0100240075481d207884002032607000f14089d440c003041114104101c0c400d9198100380c40343c0d02c5843d0004d0310b00c100035640159004c0c1501103180c001600480d0315101440c1d80764212540903401a2810f000d0b00030704085e0481c0e100760303005203800140400100341e11b0900070007020703180310f0700c81c051086035200d00f00300100c2501205c40c04507680000b100e40d8490703800d00b0418060b600560b0112595020040702c29102c502c04107a1405811300200905106031543c0c604503080c1c6c004035a000101101c4844080e50540d101b1003180610441604144100341c000444d10203480e4010700c0c00e01800b10400c800000d070b036503030040901816800f540200d010002b103001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 920802203 1250 920800953 920800997
    0x31a070905040903020c030c1e04020f0f04080d090f140d020a0f0b07170309070905040213050403080415150b1605030f0c070603181415070917190201 66
    0x46412503d082c201c281415400301e40401c04003025800c84103005132034000c0c031014540881544c5000a00300700c0f00c0c1c40310300d040c0d002400078003401450142802c0a100300101c40e540b0580c082400c0d58400c8800040d22034008210800800d9460301f5144c40510f080551000e81515001c0c0c1449941c03040c0c200320071540c0b0400b00744003525500018032807032a1209400030041d80948800d40711079880d44d240b91804422141200c0c4596011000382201c0ca10381f0488402502c2d01400483c0d02211414407044050400c1c0b0600384160700036519149241007030b041c0503084460070f10358240c456051099148134004402161412a1a9070409a40d20302141c01c8000700304043d0b2000800310f010020740062801d081401600441c82e42505a803e09030341c1c1d500a07411940031101d20030500002c0c1d640780e0040354141c0c59407062800c52030144c55030402c298214000013030044403950301240c040700041c420160341c0c1d00400c00000c064001004a00140240044141541d03200241081050383c000b18202201241d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 920803453 1250 920802203 920802209
    0xf01060b03090304050d02062a1b06160203100c1119030c030f05070501020307200c091302060c0607021f020304150905030d0c082a04120c0806090a0605070f0e13110304060902040b0604031a0709 85
    0x10100110e0200c00801880364141c0d206000b0180306190360f04118441244943c1107041d890b449070081041183c1e015210804040344e40f8003403213402c0c000580841c5c03080c002036200300310f296100c0c0b005154803505600c03a500b609041450235031142a4000140d01c42c10480341c4c0201940200050606044c8000380d464455240d46644a01684040c02000b5070005000404482c240524055102e40b00020000301d00003101c0c043c002000c040010341d00d65004d64801c049090090080d6031420600c020035a0640c0c40e40d000140000343c0c00c4041004050500309008146058410041803d941022004803d401140031f208030b1040c203094100304212040010000510a00059030b103649004030103691151784050301601d4160034140001c200794071410020718600c00070748480d45e04841c561305200520030941d25440c2080d82d42c492b00603100030844042d62107075102d1400840c1c102c2203881804141c504020300d00f40503a2061100b440041d8400303240706089009840700480541e01c1c51b0084802041031340c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 920804703 1250 920803453 920803483
    0x405090a021224030a110a0b1c0f0615170604091109090c1503090d0516150f0906060513060e0f07021e0f01060b03090304050d02062a1b06160203 64
    0x4040c0108011080c040760701101000c503047e440c92641e40300040041c3c803401e614501001728090311f02509030140c1c2c2c0140e000100e01180041c851351a10b2180030740100c2e980e804804145141101c069809196800b650722000c155000c0c070ac604c41070740c1c45826004d42c80c1111841007480200140852208000c00c1c20344020042540742d10741885110f502d125030080d10b41b0714840c0911004506190f01407030446840305008411003000c00502d032554224000b000203068002501ca140b16a0900514029146082c0c020701d40040c0c11841d03d402c01240747d00c8001e4030a82c88c0e0400c44108045602c0480441d405081d442c8000c000d41d45509040f03040c07000c0704050707112403459107084000454001500d0750020351004c008000e02c40e01c40a011026000444c0c0c0c84605038000c001c1840303141130840c8840c0390b00e84042c02c02810940d400341c49020050300c0c03008140e180d01c10402019401132042001f4000101e11007001ca004051038000300704944030b0301e59191072040701400ba01045450412250341d03040944 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 920805953 1250 920804703 920804713
    0x8091b0a030204050c0c03070c1802070215160606060207080f010506010806090a0b1c03030b1509010f0e060a020a03180302060d09050a060e1c1b0b100306060b0405090a02122403 78
    0xa241c0305858030814082d5000cada240d1030200203c0c40c0b2080c800ca4800d15001400501e05002123032100301c0030340c40300c0c103101881c001c1c1d08bc00364001441d81c002d45000d01150303005802e00760300703003800c280c503000c80020444090381c103000c148500b03640c006a400341c10a03c280c032850480d90310410703441c010348000728140342c0184006164003100b03850258900b005a109a03800d0040032109802c210000740a84e00341405841d040090815640c0140b0005207254041d042502c0d000f90090b0014540b500147c00700e00141e00301c408594100350340b020781c2ca641c0945040d40c202080c3d007103401003180d5014040c650b0745465510890700040c05403c0050301e007505e078002018000e000b610075400c0d03100e16208405000300d0182040f540c900314060040e0501c030310301d448a42c11042d075039616025507103031000d81248a8a0401000800803502a0150341701412401c0605aa81d0303140409203c1d444d0703001007808400600c14002a020100c4600d590bd4022000302401800501c4813545111a4581d0203001c0d5414411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 920807203 1250 920805953 920805967
    0x10e06010f0903150504140102031e1f0807050901210201030b04020c0604240903080619030c09020421021c0303020d09050601050a060f0f0f09050a0608091b0a030204050c0c03 77
    0x1130f5801551046103d60601d0303440c0d6401e00ca1590907800140e41c1010040d50001c06000301540b0a90141d9101d1007104412070000b0054843c908132840319002a041504490720034022414030345002e50045c0b4100d03510030320f00445500c01c400307000f20304100203041580310110a04143c0e00c5406481407100c00d0419102503041030314100710b001c80c80d9050410b151050301010300303c003072907881030359805901511040c00c245d40e120104040091180c801401c1400810030210100c0e44d104d5018011708200c54006a03140e080200742022a021501d9450050004180e144010f03204d03480181000441c0382c90503040a0601c1c501500680140e071501c511061508a01d0414403d0004030b09049a8082c4c0b545822607442d031f141152100400000c41c800303d4520092040228440c2a00041c1d6030311516000780f03420340f101d0024020b4202d59104400090391001400480c100500807205050003442508040d24401c03808545550a01c0c44064071407550b0f8400503000c3c4c0066000c440f070b41801038080d00e5903241 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 920808453 1250 920807203 920807243
    0x1d0a090c06111002040b0d02032508150d02060d09110411090a1505040b071a04030302030103050114010e012d0e010305160308040b160f0308010617010e06010f0903 72
    0x60040c00714140e20650901451043d202c0c8200c4082d100700304802c40c40e214007403000002070361010701401503181d120840b070507100810341c8030302005440075034580400d800d24251002c00103196441c1c8911a128440044006a8401e011101080141070002c90f00700c2c12401c0000000084d10341041c0c07c542071071010060544c5000041860071003c5403880b84290f22a85842c8038859021070100c00305e0010030060004500c0318000e0444903104050b9000d060107601c80b5080000b000390b5049021039000b00061003000400e009490350f000c4c083c581c01401d07624000e8540080d11061048041406052680c46040900102d450000e4540b0902462409a1341e50310445500780920040d581c40c020041c1da034010b6081401c02e641100d420529160a242c2000c080c1c00d103543c0080c900c1d42c00500444c01d494005140e881016451600076203540b2501d6160a50240c0310400c0d801c080440444044018000444540b00c002c0e001fa60a20782501d2850648505941c1d61083d42c10191104207007015107410a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 920809703 1250 920808453 920808467
    0x21b19060210230103063c0b03010507021c1709030d0501051f0810030212060708060301140a200d02130b04060e010c0c120b041703011d0a090c06 64
    0x7038010b0200401541c1d01015109140c5510000040101100c010404a00320741c22802d895050300c420900c0c2d00c6a06c1d80441d4841000360f00040801201c11003125000e041480740a0180106900a0007a49880000203440b07600f00c0c2e0000307071108040050f0f802c0580c8907115506c2c0210b00c070404420f50303042c03a0003040d81d01d4000c082524050790070a00041400d040403007860030203150a60714249a0369040c00180c694401c01031203844040d1a00307200202607956044908044100b0b103012b0310302400c080304018a03441005104e18041c6e81000c510f0303203580007500b5200754401003442001a0758004d28030501100b44020f40b60001072071000c25001d0412000303500425020040c030143d10302a56a607c11841c46010324411040820311102001041c0e50140070070468991003009007000540d00c03118000415444044299105ca00000c100020045a1128241035028900c409420344d807600d910450782120001a041481b5800c1010403140c80864124500700781d4881100b6004c180c691000402c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 920810953 1250 920809703 920809723
    0x12030c030a1109061804062112051309020711030c0114090a05060c06071805090c090a0b13210b0601211404050c0d11010c02061b0312011401021b190602 67
    0xa0362601500040b4001826250342c204071b4000d503041c900000544aa100b40080142600c060ac9020008020108080a580d20140182c0400140c4072400d41c1481024082c2c08900c0c80d0090b8030280c40035985a070060744150510340054001540d840110700803d81302a0305a000342c1c0c001001040701410510042085440b55030700d9940c45112982e00940202140c1143c801d894002401c9004a0a088020001442c10910141140030a03d030350345182840d541c4008a130103d0400b036090240102017500b64101070903203801501c0c14510a2544460700740100113070881d4144010001015410098200e40c2480154058410402c0c50079450084e00c001034101da0450745405402a001e8161a04a0b10034050b180c0101c81c3d805540161001274503501600401680e00890a100c21780f48240c1c1044a00030011440e0b001c1c54a0f07856181d245824140180c2044200e4000d00e00c03407501c180d0303000035075114040c658031080c0c400c080c0c04000725a05071440080350f00d5403107000e400400c24940003d100100303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 920812203 1250 920810953 920810959
    0xb1503250203041802030703091227050303040905042405041101050a0c060509210a1e020c040c030609090b090613020120030c16030512030c030a11090618 68
    0x580c08103103004070380301d203d1809081d0454a1007405242d04e604a907004c3c503070000c480e060004407151682c803505150000310345ea0000040c101c42207800060fa00b00c000016080446084825143c01c0200094607409580201a101c607036580c006401d11480c105501481d80c10002e0002119118202e003401900c8121015909484150a10716a40d4410011920340204981d92400024403640d540f0004d850003510032102413003940c28418a0040303400c480007002c00c26800d002c1d038842d60400c004d000d1b10724690624001800501401200382e401051010044c2000c0714005980446000c0540c0140303580c0d04001d40540c40c002c2d04808002c400e4011a014400407070448913580e0310b110314009114400c0c6402400111007400d401010360302030580e80107480c150307002d9904107502d4200d143d00d0545003580030a13101e03040c40c03c100b040c00024000d420010010301015131a624181400114502c0080c0130094000e5941961500c8551480700f43e586110b401420325075100ca0030100f0b0041d41ca00699940c0c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 920813453 1250 920812203 920812261
    0xf0307020106061d0d021011030c01091a06061903091425082116030c03090504050106080628080703140f0c01050a2601060305090c0a05040b1503 64
    0x2042c04004800c04c2003c010041010720b0300d03001359080c864101410301c010014810200040c40d4210810b0010302400d205803400050507001c07604110140042620384511611000410b0104030b8403180e0840d0070615500c400700035901941c0f2000c0700105860100a045414003000d100360841010942e03035280c07030071400800307401404100031040d01d4405200300b21250344a1060000384020a0391082c001000722002035040c41d1179207104c0c82610b103004400300c0004840f981020304054121040d40c1c00b8003810f40c4c0401240d814079001030402603000c0c01980c4204c14141c000090300941d0310002000c48613003042c0c43c280d20707a0707910515650303421400100c0c0c01c006140400001d560000406141c03a4021000407d000390a940055689911401a08003000289841c00403046c4407542e60100b000711096402c4210b614040c0001d003181d10107070920116030070041c43c0d840c00303596810a420070307168100c80008200480c4000125400321016072120b1315174001c002c00c4034405109210759038032103689000103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 920814703 1250 920813453 920813477
    0xc19030b1b091018030c0509010602010e0307060e100e0708010b060c1209060d060311101803080c0703060501141c0f1e020306041416080303040212030f030702010606 73
    0x100c1a8600034256100d0140900580700b00d840e120840f140310910504101c1401c03d920203070302c5008034098009075204005030804000500703028142c10300401484c030003080b01d2848030304042d840384252035011f45550b03113540038112440d10502c0500816211145c080200f044229121900d0713107464810000d10354684200c854030f50038074404896039189803030007801008409601140c06500315051042d040311082c84030b08c0440c0e009200c1e020155009003515a054507215042105240501d01c160701004289112a20b0004c002054501130304d91040e540c03030701e401380f041020307203401d02c0f41d44007074401030501c0000640f1140f00316a141c0e2100741651440b1880e01c4602c0c3d8800e1034070070b0020003803400b013501e4201e07070120f01403100c80c140101c1c1c4805c00030f00d4041e59400191800109580c2545c1c03403c83d401a0308203014080041d501c050144100c6400018905010a40c07030380802007010340941608008440100b20500840b440d40104c03541e42500e80c100854000e008107241e0043c1c4c400305000c80c0643c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 920815953 1250 920814703 920814721
    0x80306221b0f0f120e0118061e09110f03031603090509160503010b070c050a03150605030607140304020a12080301080601080c060a030917032a12180c19030b 69
    0x4030f10f4a50041e211a14080700100105000300516402d030356282d562111a260f000494850103900c560103080041400d8448140c065902d90540c841c801840b4a040302c4240040e20541038050b00840840d031011213801c804020030300318031604a80100380c1e08940c0704d1004040c0c00c050103000780c51040d03800c21a69a110110f05000485080900b0f010807424030040050300190030080c90401d110301c49482040e662032010035610460b503041165244204518614800c40c2c900c01e4800070203085006118034208100050810072614003061040203000000405545600328003400414032407046515a1900d410210b00c96042802510058014000005905603001642400110008249510b4106458410780003030060b0039040f104055084071000002100c2c502440c880d240341e40407100c1c2c030305118100b07040340b45010107607401200f401d0018000c80118407414661106030354482100080140440625002e0417108076030303104640c81d240c002808804211441201d20501e03180b4420f4941180c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 920817203 1250 920815953 920815967
    0x180913141501090618140414240108060a09081917010e071101021e03190c0306080d112806091a091c080703020f030109021b0a080306221b0f 62
    0x1011b1a141c41100c0428040b070101002a209200c151045400b601c01c209504528103822055280c07850081c4070041050f10b1041c0320031a8400d10342c000800640c4200d558114a900640c1c40d0b151481240c10346c0350190601500c0c4c41d0b01361200d200e0303c2484a607034846141c0030906d005c0345c1541c002280c4511840342c0c00e00500030395140c0040016844c8002c000403100c4142500028101c2e09082451005440c4180d507038401c01200d445c5654010811a08115200345080513002000f004c204001c128102003041c0440e481d0b10b00c50482640d840b05010f04400400c0c90402c031040a07000d145014032031801c01003002d0126035424043e1001a80701d68920f000c1070386072002800d8850301d00d00c00f01c071504400d80c881c2c0c40191f4400d40c14200141802000b40b0000c80d5038000f46c024844640d400a011001108101c4280141d501c6a070010100c580c5c082c2c0d0769568030700000c1c00302c0703001b01c0110201a01224100c0030f204c200071004102040390100c52512000d1240c1c90401400100ea81c42c90402d8140e446214 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 920818453 1250 920817203 920817221
    0x204120503072a03080702012d0e0307030c1206020c19110a0b1902070f0b042405040306020d09020607060902040e030405030c09060d0b0c180913141501090618 70
    0x6056141072a58403455031740d83c01904100d04011036425901d140b8100b0b4509210703d078425103594000900301d45405440d00680400701c4e407088c0d020110400c00078280d1030b0954250b031280050030241e60110b02e4800080c2c05100c81c3c2071014021095903483c0d080304480315261842c0640c030079052070401d00d0248600c010450143e004002002c00403803410b0080c1501c0e101428050744103d41c0340c3c1e6502d00282e03078407164a4021324400000020200503c0c081c40c6c41101820f034990254144060400002501e01e120314480106044e401041c43e000d0078503558001c0d14101d4000e0601c40d610f545503c1e054008001c203401c1280716910f84840c0c1202c0c0903000003560706079200580100016000f40b4100500100010700315035200c10034036004000501c840c0e25080c0903100211031180c40f4100329512005485216074217a004070349a20810080d040c0c901c45a00e8072513084210701c00d0103980708a0450510b0b400d4641c06201c5034455000180000c1181d104208494680c07070365122801c3d05030010000d552a1b0b00d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 920819703 1250 920818453 920818523
    0x2031f0b0109050a050d0c27050f090601031b08010c0e100903050d0e0301020d0207080a0f0807020706031122061101090f1118100320180a020412050307 67
    0x120180311a007011b1400b007000d0360040385c998200c50f40d02c480c404445054682160701414032102e03442c035000030340d0050540103204440304c803865107440c02d51103903582ca0500c000340082e0b0000c0211040211801801005403009600910030090300c07800107808041204001030084407d440002c1c0307080d2040e8288400c1d85c1d48903029091840c025039046030b5031011035071803a038107540c01c00c40100030742894402003807030a1040130045d80750340b1100d4014000400300c01c0e408041c4003403401000103456010030310000b5a0a1414002103100b200180e0345518000e814240d0040a20741d41075445a6451064140444415966050b00c4001031b2006609a40b6501001044d43e04480704800001b07862400000000348040e0000e190080c00b890700d0892010300341c0f07056104445c0d0078018000d200845013150364a03070210403000054501da8001c201196205c141d81880d030707800c1401160303420300305404039401001610403e43e00c820a5052680c0c4a078040c40d0210340f090103200d549a407103000c21030382c440c2d500400c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 920820953 1250 920819703 920819719
    0x31911010e0d03020f0405040e0705090c2b020409050405060f0703020c031c0b090a09020906010e1c0c050307030b0a0c11190c03080309100c0809190c0302031f0b010905 74
    0xd4420f401a4110355030514400d00280800300d500d403514450202c0c0510302400a19200b844c0005100c1801c9000d40303039010039a42040721105102102c03010b1140000c010905402005400c1c0500000380181c0e00884401030a140a00061040009081e400380360440203114071034949810541c2248988010302030507420500050701d0302803da28620b4404039000138046604840c00c2c001490444003125940c0405544141c801c0650411850f200c0c0e00203030a0800840d65048000000c0c2c0e00590080da05129064009101c02002408040a00104405011104025141d04d80801506021120f41c20300501c0c07c011545030320310403103213040d0035146031028024038490000c0004205084080540d2085141c4100000042855008500c14600c540252403406101c0744000103480130840d800040214a4003031000c3c0b040c2c0810040c2074040d0f14443c00d8a45c092903c0c040f96142050b40c4065850700846000d4020740c9807074070181c050b0824042082106600c1d900056907940c0f09400f4040c1c000f694 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 920822203 1250 920820953 920820973
    0xc0f1a0c0a2f06010e04030f09050f060304060912020307021806060702011d030a060221010605030105040c1e080105180403050301061b021306080c0d12030c11031911010e 75
    0x311441102c0d0304150a02000710342e200a00241c64034200ba0b000b95400c00b81c2034200002e01d68484261460f03501c180c500850158908000621080e088541592040500101040c10041254084100e0310b41c4000811044d1092050182d1242c00814090780507116405c0c0012114114044513032180070000c1240d4148134898004440c8003070540c01140c0080400c590103c0d051703a0800c85101e00900c51100566121040741c40721010120650a40320850081001440604d41000980f81519000e43d40010b40c40c2e5290300440361150b081c13160440003142c4007503812007141d0111f1400e043e0744003954032480440145620b404555030482d000b5001660030b10050040324031032800000c640510210001d10304000f900081c0480c4440440c81c60700c241c0e104c0080000b41024071080103001c1c42103230038810807846512031001e8881c4000114040554800c0048034450041c015080746008a07002c99480391020504551100c207039401401c0400e610051104400c2c605000c3d42200c1070000024185000d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 920823453 1250 920822203 920822237
    0x705090a050613090804151701090f060306060f1d040f0b0601110d030e0106080c031c0302040f0305160e0c1206150d141803030f070c0f1a0c0a 63
    0x740107044950711006018856a0800f09070040c0c40185010380300c0e580d40c9a1400140c1c501910b140d01c0c03101c0c20b04c801400d034404441005924141122407041c0c002c41c40c507158694100080c0a5500000c1c000307072070820040b03501181d0a411105440103a00a12200c0d91514011100c40000301c1c0d00030100d600014421300010039804070550000810305151000f00c88805002d41090b41e0b031002740780040e03610b0100700d851110900801001300280c80140680f412147d0210791181c0c5080170101184104030007582d100c1d4840d504850051100000b4050480d1702c1e032900c44d4903500301c050b20010a54001c000429609503000440313004000628041d40b8044984400c61118071000300b920740e006881208035104400d1850040c51041c9800f01c0028418043c40e135440301000c0701a20440035103420399a500b00844002040b60381256999814541d95529144101e40101120340018058001c0e440341c80c0406c0494900b0b0401040880f41c5100d01c0d45c0c8142024605010302044400001c0301c5200036000a8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 920824703 1250 920823453 920823461
    0x50127060b010c05120f0415020312070f0c0611040902070321020a0e1201060305160801060b0909010308130b2704050910020a0c08071110050403030807050307030e07030c060905030705090a 83
    0x5098611b00e41810381d42c455442607564192182001351700f00060900410720041c0300c035540704080e41040e90032040306c074600411406555000501c0c2a5a60705003030700751a00702c0150b500030304642009542d50741042c07030b0040007800034400c0c16280e9a208041d45624000310b0003900c1040701941d594103540d000d06410425425400c1240c0701580d5a01c201c0800810028800e4003196854180d4050b4007900c2c1840721030842c0d02c80c0c1e112150700142481007403100d544031980030341103942081c0801d440760700c42507040c9100c10090344161100c042c0080d050940b03004441364081400c10240e4029511b02e00c1c102030006480044894062903004810110706d4003d4550180414001c1464452158881c0d03640c1c5813020743c0511801c2c0c5003000c1d10110007819180605003044042c0b820314259050034030395a0060400540506020140070f00031001039950740c425401185a01d864008030780d14644d0341e0801d4000c901c22402414001218840c0101e041c0c200001d00310101e900c042c4c61a249a503030141007034010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 920825953 1250 920824703 920824717
    0x20a0209010e2412060c0c070504020f070b06181306060e250201020918041e0c052e03050106180803090d2307150e011704050127060b010c0512 63
    0x4020354101c13000103010100074203481122082c403a9a81c503280c0d06802d5140c01c0380c83c0e2000748103c1c010848019024280c0701580d50265110140707501c603403101d000041c500b00c400501e51f05840301c00070030880750480246110700200e0140700200300a40d12045845071203002168900e203000c910355501681c040c2494424484159148001400d06000c80005070000b07a8070303000d0404414808080c030041c45500100301e500003c9450803040c040c9015903035002041c4a5214262160102d5500c4800030b200314074542000c121061420344d1410017003440907008020078001d0070001007101113018030041220142c0e4003650688001107041100d840204650301c1011181201c0704200c40b200c500220301502c22080d010041c0d50081c02d03140e400d2640f011040910717a5040c03400c0020a528207040c59800002911036400e8490301807006664034108203016010315007282040c11090070f14241031041c117041d12900709100388814405251100011510f010072004094070039000078000c1c07030348c001883c0010b00034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 920827203 1250 920825953 920825959
    0x170403020102270406060207030f080f0d02070605100f05010507140102040510050403030f03050606070f030c02060c150108010509070510020c031c11010c05181c03020a0209010e24 79
    0x39002e804100c3c240c003140704541d400c050700040c0c061801545402c1c0a010b01a007014402806a00d02d9070f21b41c59501d50307440c00041c3c440c180000b1a01805059141160a6441141003e640da4802c5c1e2410700010041119626011203500303002040c181b48031b11103401101c20503074405041508985078082942041409a003566508010000e03842d02c4104c410201940d458031055119480c5041c041d1407040310720fa01d00c0405192808024545e036401d002d40311856042080030041c00060316059807900458400030350310080c0414600409400021000e02c1c440e00407480c0d01d401c0e680d604146098400955100542d034000c000b00380214109810040c041515074030444d0745000b0388801080c140b42d4601d500c590101141a80b44121a4101c00c0c0d000000b0703c0c040080220420402008020b03001c2c0155045246011100003c031341d64802d0001900d8004451010f41c4010007132901a665104102040740100e03050310001841203544280181700e01100000d5080e00140030104a456440800c4807542c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 920828453 1250 920827203 920827207
    0x227071d0d0206180a05092502030a0c1415010e010617130b0c0706020304050309210d0503100302130e060c0712050a030e0607180b09030a11120f0c0f0d03170403020102 74
    0x81b195503045075603000b1511141e01f2102e0288010000302281d0401c07a1000035580204660a170055004100610f02c0303401500d103924141240f03c0f0542010382000854848900d000e00100fa0700351041c2d8480d040b1002038036032151500c0b905407203040945084800380703074401e00400c0c04000300d0500b0320019401682c5030b10051a20b040c5580e0382c400c0340c000f0348007685d16a00125011744a070070501031208002c080c0301e13503106000d0202030030b40740d80d40f61038524202005000300c0420102d8840368004400386600a00145c0c0d202411865000245072076042da82061260741c010a164032140001c4170b82c5280c007c0d0300380d00001c18850080e21030703038444648001059580c4040c031280c140184101c41c014215a680e804205a034494444a640196081b0450200007005011015900003826400042e400003002c0c00d145101c100050320544051084c1086008042c00d031140e141c40451502072811080301d90704180390b00081400828842c188000f00404c1d5400010051501040c0c005603005109200245c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 920829703 1250 920828453 920828459
    0x30a06030b04060e010c050903030d0b24070b0105010e100305090c060d0b18011401031d01050108030307030e010c0f0503040f0606080a03020124030227071d0d0206180a 74
    0x22200e038030116401c3c2e03155a9940c0891480000a0088200d5004203203001c6050404910009072644201e00c1d41d07810032585c419441b25039403110102400c80089004e0b00d4a0503001607001c1d060300d030b40078120407540d4901000c00400c0c035600403140702c0c0c00010013900c8000d4050010742e05500600d03010f004100e03180709440d100c22080e0740300070042070440504203000c84c24008450900c01c94a0711000b40381d075055a0a8014444241d8081c0d070b411020360246070210300400e4240e078100401e1003500b0508095424080082000c41c070000080d03001c2c1c41941e43c03c000c00000380c6045403ca0303c440180780001580c800341c2c11040c2c0d10075006035400078001c110710100b03083c0c00c0c1c2e02c0c0030844426502000c9581c012441c402d0074140c082c4034061442d00045855100e244910f105100c000303006000080c851050100e03006001c040e408148210b048803c2c8245019040400001d446068440c104003007541d201034140880b13040c0070030729100b915405013031141003020500c1c1c0c0c032074a01c152218042d08845854800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 920830953 1250 920829703 920829713
    0x50705070816060603080408010f140a0c090806010b0405130c02060403050a0e0a0e0601030f02091f090b16062306120c13090c0531020903060412020f120708030a0603 73
    0x5004602c07446e01c083d40d862900c4c0710b040c20341d244c0140d0b1145883c03078041074030407042c43c030366002c1e900c100c1074100000c459103003910688607071101d504000c03240e1082c071001051142041c0010815140d00b01c0703018240030302c80c014200a448218070904016049840814006405580900300c005038508044d44850007240101d01035200b258460004150920117000c41035806208680d5240010803080d0315107810b0710003051000c0310f110041203412001e600400d0780c26200e07030311400c041d2100e140050f54801c2e9600c041c40e21002560000d50f0000c0c908001910704160710b41001d034110b0318480350303070341c00d65214001c20010351075400d854600c500403541900e405503210080361940c10164440002c1c2c00025080900481403241c00190144284030f1220000164080000324000c1d84080801c1c50000380c096150f01900441230160f4041c4540030911040000514503a1148203c035404c640b020850009a6a0b540840b201f8030720001c0e904214603004111000000e6504c00e00d20740000c07491940d81d5550f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 920832203 1250 920830953 920830961
    0x30a05180a09090302070311240c0a02132a0e0907030e0d0207031a07050d1e050c120a18020f0406081608070e010608160e060412110405070507081606 66
    0x4210010307044a40180b02300440203580c0701c00c450060320441036600484030094518881c0400300b01c1e1b5100c02080840d003c0c0c0c000c0010300040750740174000f84014289007009901030419a250302d04c4460b51032090015501c46d40b00b1340d90714a00140d81e10b1054109403c203001c90140c0c042c02a0781059200ca0707009645003410040007442c500d031a4001d05686180d400c2c0500245182030b00102103080040038080b0481d40002620100d40e40b4000004e10315044480b20b220700c40550b0f000c401c2071800c00341040b11f9040310001810321124a0008042075641e0740104804440c1c281100d4480a00110f064002509007035901d481d1980010304000746582c1c036000d1080c542002d080d02c02c0103034001201e0501584005002d11401490141828070013541042005491128010003800e6200022034201034098812440c81080301400340c403049d0f4490720f0f809503880b00c20f607a0b507040d42c90b004800201c05c401c1c1081e1058502c00c40395943c815041035a256104980d44c2e01c145184c48042d0f64040a070b40101d01c1b01e00c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 920833453 1250 920832203 920832221
    0x50301090803270601182301030b1503100e010b0f030601060e0402040902030109060f080f031813060306230f04141614040e0a03090302040b010c05030c0606040509030a05180a09 78
    0x4800f80700711300400f40f05171260301c0150002c186225000700b528401e101c08150650703520028402b03550b81c0343c1090700c1880310304e0358501d43d241c0300c1c030032081d00350803032541c0099149201038009104940b104000d01003118a02c42446405500030b0004204070303032143c0100c0700a400e0081025140640d00c110500998200303070002c60302c0c0b9a844408001004855145000421a1101803d070b0401c3c5042400e440c0d0041c3c180100802c0142c0c042c0008680d0ba5101d2465140c42840302007100070f4880c1029002400040303600c58004200c0c1c8a034070352502507c28814030580110f179030410165919503810301e410360700714103000c403038030a01c5414456034159407401c00140032a6468000340f5010b0700c0401055600102a41c2c6081d002811010042a4048401000d6a40654011480c42012401220003120800025050f4003000c94101c41d442e001007a2540520001c807018003603900d6030104d11b920782c4a000d00050100780c042060340751116002c801d1850444008058200151b9210134050a80d44000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 920834703 1250 920833453 920833469
    0x20d080a2f0c1206010504020304030c0b100512031804020706320a06080c01271d0c0f0313031e0201150b1306080a1d1501050301090803270601 63
    0x100e8204004070070040021014000c0354080316101200344442d40310203040c02410700854000001509044c080e4140c03030340155019004105a1400100c041000e03481c0380155440340100a4041300b41c0d18000041d41c004e4242c1e000307460b010382404002c00000398400c15040300c6e0981c6400b044907548580f0f0449070b410807084192044858846002901c1802004000c180e500307180c800c05116002001542c1c0440078030070b0030b21440400441582000201c0d02800c84241c0ca0366601c0042807a244141d125082031003003c208a07070646818484501c14001c00e0446004c514083c0001034040c0c00322801031201c9800303414401000c0000d80788141c5c080d003403078010a02603916500300541c07000042040c3c00c02004443e12180c2440c412084a12902d03200b44943c804026000011401035a40341e400000c56446035030030700810300304003c4807684800658070070420038081c1900004040c1410f0003142119071703100041d145140d41d4282c20340c40e0703425001240700300c501e048200b40c01099004c2101ca806845a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 920835953 1250 920834703 920834777
    0xc02150403065109063f0206162301110702010813060906050c0306091612020c01020c01020705010b0a0e010e060909031603050408160b0d0506060c070e0121020d080a 73
    0xb05403084040344880c05e4107a07050ba94254411b20505001504803070268102c400390340d55000f0b1901084020a2014060704c0071480401c0c0100d41c8009d2800085401d030308070001d000a07287ca4030001214001e1802c040c1c04910044001032035103000d81d840c10811071282000240000660300c410040341c0b021101304801c040c0c008180700983c9440003800e40e101800c2d0001d00f001d801401001000300e108500d000c08401c4c2c0208400000d03140a4040d0350085030114003c544a4040d41001406040f1a41e0001d0090b07a40c0c2002248e103041c1010114103030342482d81c40b19020340f582424002c010000034207500090000b03010340d890200c44640160006070181ea02d003a141d03030402c00b2131030426040c40c1848042e00c0c09404204030b001000d10954003919800c0c03d001519030703103940101d1454882d040103520103005071640820071099078031845050384c0720b0a44e80303d424507030310b03450314004000044040c0d408030b030303000c0d403800000c0c2080d0043c1520509494490030340c2d54001fa040418401c40e82d0000307030b20100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 920837203 1250 920835953 920835989
    0x8060903040e150a1403072403050708010806310b04050106050607030804020f0114071401110901170c09192d060c0215040306510906 59
    0x1080095801c02c00f5100d0301e03d458481c02c80001c015007064407501c0958200101c03d01d0315944d01384007110050030b85485140c80c4000c003104030040d901c0300fa0b8400001c2481c05000ca9212031107980c140b41a2000c01d40145016114111041009400034159403550035100e060400c17030392034a400079038826125604060705810a4644142910340d544c0006004030402c2c000303140402c0c0d00884d40c80e08560113890076013110011500403202003148d6112412100c0000a0450402c83c5420000d901c05010000130800c20070710810002180c0f003110480c900151030038940072100d11120183d1504511408401d034034003034000000c58001500000c242a002d00c0c01c08040010b1005e0300c804c140100030f1140340120a01d403242041621010038020700e401c00001400d48011074a0f11411500c4a003400e000c51a1210350b24a805d4001c1c10382c0340554011403030690603d600300080420141440030900c0b840204080480c0c88041000c0c104140b140740c03082901500017031014461080601405103402082c4c0c010803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 920838453 1250 920837203 920837219
    0x2e06090c02010608030a02070e0901090b0412030c020705011215081209011b0c0b030901020403060510150923040b0d060c18080a02130209030607081e01031511040806090304 76
    0x91951004e8a560410425282c0f0264003152440549010040745031a039180d046025004000944c002480c0d104001c00b0b0000340021000700d00c000407055070b01488132102c800000c81c0c0340c01251207000c0c0070800d4610b048018904513044501c805c0e0800344006910399580324003614005d421240c1868200f00010020401d59100c001010300e0704c00c0110080b414280c55a856100071a0740c49628407009001c0003141a6050039011640110380111050046042400d2042041300142c8070310004210b4040070368000a00032079a01044074030700010f56222095240051408044080c0754950065459403658016603444018609582c041c210002c0e412803040e0000e0b01c2c8941a41450403811003080302000606400101801c42da941924030720305a050801500010313019501d1495414000c5408100d07130160703c82c400521403004500da050182c10000c405444200c420300000c5c04071007a00408204041e0245c00c102600345103111814585541d52940b00c0c1880d6040d03d0700c04403078100040800c1480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 920839703 1250 920838453 920838461
    0xa1b0f0b04141516050c0f01060303050d05060102060f060405090f121b0703050c040209180a140c0705250f080c01081008030901030f0b0301060303020f060f092e06090c0201 76
    0x1030f40302e2020700d20340e0808611142e200c0403600210710800c90001a015182d14080c084070b81d22500b03410003400f080d5224600038040c0d41040d00d0f41c87e155458000001c12545c40000c03400d01071480c48034481542d443d51b0003071001403c2c008201d4441403140c1110b50358140000c11607119141d8614000ea5283c0600d605941c585041c000818036155000450610200358003142c10224418206d60051b0303100c00040100390343d917040b5054151440307401002c0180080340e60b00300606885e160003048410303a0310112001003e02400c030340134107660300881c81010b00740c14000b040510700b161021814051a5101021000411681c000400603000701009113101d5803c21a0030390002403240061401034180301d07809a0328000c40c104070781003603100c59500940c440d10b9840f0103c4a00301900034000d05132207040c00b0751b031822401c42810780d500c01d020004a4580f80c0100c0c082c02404a540a0065221a0300400e4402c0c400446c0062492400f101036245101c6184070302d1000704402100440c011080c084041d00315 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 920840953 1250 920839703 920839723
    0xe030c0f0a05060612060703050a14070c0507061404140d021507061401060c080a20010902090a050903070f03020c0a031202060702070803040b0d06180605150a1b0f0b0414 75
    0xb802c030740d070740170300000c60203e10241c0c4501a454006a00d44d5510801005808025101d80c0000461000d008509500030301513a40300e40a101119803260303884000b00c0d5820307a50321451071044400d01c01840900361003280a001c1c0b105c020100d15030b6190940005104480c40040c10240d40300014950f000c100050140da8608100070b40c262245e503160180142030501c5015009110300800038034016030324040c103001003040d0405d040078801c068081030090b00800003c90268800e072440030014030105060b001e5180714014000c09076003446200d99480c645612500f00c00c80c29405002016040c5840d0480140e0045004140401c4509100a0080c2c2000f9010300903000b150810340040c46610703c0001100d085840a0304075641d606542602400100032036000043c045800d1400d03600d600d10b581e00b1402c00d40e83c00b203640c004440076440098080d0301c05c0c5188070010a80c90280c0900304020302500340c0016001300303400d030b110000c195150b48a0319800c480446200c409070010750301c039031070400c60281d00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 920842203 1250 920840953 920840959
    0x905040b0703020c0d0e0118060201150b0405150a022113060305070c110d0c0305010b03070503070f0909150213320d0305040e0a02030103031202030f06040e030c0f0a050606 76
    0x4d040c0c2200305168035500d0800485050290841d14291664820381c0410528480b0f240f81c60841615884002d018055200309011060b40800000c154000c560003128121840180313507041d41807140e00c0041880d0080103105d010350159481c400c040d103121409207031000b0645013926035110382d040d81c0740d000c20465070040d00405152004106029400002c400e40c2c1035084001c05040d89812000030b042c0040e00c0c100101140c448413400020040b05422110740d1100c11807d494800e506c40d818140c0d180c440e031242c2110031891a00c01c1140d00c5c0030358000540d2500502401000480e5465008141c1e8090820804106c0c01c0c80020052949081810b0910141c1070301c05111459410200c4402880240702452140800040c14001c06028008443c010034040d003000c03400303150482c0d00c90b000f504240f1040c0c02146245c03480185030a407a2080781c1c4520741418501025440e04070a0000400004180040d548020055142c1d28542001104100001c0c400100300300f0805140050902001400041c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 920843453 1250 920842203 920842207
    0x302030a173615180c0a090b03101107020f060c0d051c15061b150f24060e030d08060105030703060e07050405031b0a0b0a0207030203070905040b070302 67
    0x301c1000b14000c1c0c144040524094201e40d036a2200d8080c1182942c1d00d8980194070440705004502001058010300c03070080c040403250140e000d5500b242d21400000f150702d60000840d6024089001c0c00d92008001150146c00c548280d0750058415013254065144a01e185001003041c00442c80c00310310000d004041950303a141400141c05c41650350f80454841c050a1140114490249042529080c02403100e001018411140d0584100400da9181e00031000041c15407210404070301c02055001081039804011041d80c1c84810007208020100c1c41d0110402c10f4603513450302c041b2210307402c00002c2c0d401c0421000c1c0c1c500d450020301a00c168400443c190198200c1c0e03040c10038040d0804180d07075200c802070800c2503030303640e55400c00c400902d851b07080310b110a4403030020710042690043c0540192407043d0220348031a00c0349144400d00520f0701c00301d242c1c08200e950043c400e0340d0504014101e0200b0b9401120509612980082d084c50035a400c5a440319a4600400050029510141d50404002c3c28214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 920844703 1250 920843453 920843461
    0xa050901090819050d2c0109020f090c0904090507060219020d060902060d0207030504091d0601140102030f0309100b100801030308040c0e16020606010906050712031104030302030a17 80
    0x448030f0050041108099021004211005015404407803a00317510460401c1010041000c03070028000e02c3e11940350300c4501180d0316400b03450522401c030190780c00806c0c542d01d414016040081c60300e001001c0070018002805441d40c5922907001e60010f062280740500440c50030164028030b8040d07101200c0c00c0924038801c0074405a100c0341240400e40b1b4204402058081072400450403074032031903081c0c40d5113130710020307a030801d1540c8440508183c4800400178800310b13100701030469008a011002c0b9005421120040140501508110f0281241070064908110349000b803103050b0b0b0403c80c0e0440fa5138024603031034255031100e41f207102c855070021a030b4800c214500c001c0050000307005000003800c0c04a0300c0089001e110b0b20800c8a0b004000d0092030044a2424041d40064032503140e00d244090710411020604a43c0150008015200c2964900f03081a441c0d0b1500c549551080d08400c0a00d5541e4a010b0140c08802c4020000365003e60000e55803000d13048401070281e80c1200321301c0c11650754030b4244 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 920845953 1250 920844703 920844713
    0x10e0c012606040608070e011e03080d0b0310020c073b072c0109050f03030729012403060f0b18040203010609080f1207031b0803010308030a05090109 66
    0x1060081180410300c000e5554600460000e004c40d030407241a5225200d000200040004001e074149e4049618038914511585001c0e50082c48074040280317000c030140070101c0c0e60b1183c0e40c001021004001d003114082601c10f079410742281d01c1004010007a4115400500800c0d21100312900811075040142c1c2e024007492015019108180e80c0765081d14006030080b90b0510301c602010070f089010004c590282400119115110345010000d01340491458000043c3c03a1604138004003016001078040c0d03240c00c04503034825004994002d002c400301c10011900c5200c008003a41c1e000d0103082d01030001000b000c030b40f404050204e0402c1000c0d600305420014244546541034407000e040b2040c003c0c803141c50707003010400302842138240010141c0080c400b0000040c0154030001c41c0341210070800988080489031003400b40c031044207003050241203d0821246c40041c1c82041c0501403001c10b04e514914081d40b5030f5032030490354000ea0040d50121808006d100010280e417141d02e40001040d40200006030140d620 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 920847203 1250 920845953 920845997
    0x60306032509020f03150d051b0111100504031407020f2e02010605042301050105030c04080106060f1d180a140c0414060a0909050a0f0905010e0c01 65
    0x4a0802000e10707800e0208801e507000d008801034060341030709540750028005240d07819001101c4d10801203003405e0002e012400c1000024205d1900180a840c42e10f805550440c1083d803103010a90401c50101081d100448090040140404200c1e4001c185800d1a0170020051100780c030041440440030003030030006960344480d0040d5500156482e010007a0100c004451001d242e030600f2020002c628245546664103622400564008031020000c06e030321890450140e40d00307405000c9400351984010710566018602865004014048031031800d5211002c05082d202140c6c8a5030100f20071500b0005c45680242c42000510b440114640c1c2a108210010f0400c00b1801614200c2441010104041c2031458100c01e0808409a00c1c0070810304080465000c664050f1088000187e00c8111600b1580b40c10002c80d42410344581c4c5800481e814400c9907001040c002d42a908000d1b502c41c0324001d202c40e80e000300ca4111b07004000019062140e08491070130300740741c1d15800d41044400701000d4050031107114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 920848453 1250 920847203 920847223
    0x90c07030e060d09050109031101140c0c0c03030c2808030a0905071d1803030f0a0f090f0812011a0d020904090c080610150516060b0a0b1806030603 65
    0x58a055001085000b0604901c62040340002940c03d0505440c2030000540203100564070941e0750314061074010b80e00b00c0c201e959030320440e0401184200894003240303d040c050804000440141e5811100400010f8596480065144d04607040103030414007188a0050368200c421428240d140c02881da0303035400310940b00040800018a6944100030107100f01045808080e1200d60103038071110800382403088840c80100c5810a000035a00c000181d0480040300307a038014810403640a0846d112104040080d000358110321110782d03034459900d00801d440b1100001742e54000d142c20741d80d50500101c04906004160408851841501e6101090342241c20171100280c010240060303c3d0342c610300010300903241103c40a001803100386404101288045426030084030150cc0b5001c9070b035501c0b2040d2401845940481012175030500c808440d40c80e5641071021604d100b41800690f000c584c4000a03c03884064200685041001ca2210000440c00206a40004003111000c2c04c501d0b0a000080d0f80d161040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 920849703 1250 920848453 920848457
    0x6040902130308030a0207200f13110d061d0603060718081c1701051c14010c050c1b090c09060403140a0c0b07051231050a05090c0703 59
    0x69554201101d0050030001e1a80540c4941d6281400009180607400101040e2407010b400b5803000c10201180c2e28000041a01502d2816a4081c3d00100b01400b2224040c64807078039150550001d80742d070100c0003000020500c11000403541e09018404401c42e44000b440650001064280803107a82d0005000e07901c81114505a900040e1900054550310003943c0300d84d1036803041710304803207162804050700b190001807951b580c00040c1056407803001280081c451260407914600841a40d240c2881c0103945060064003890301450702c02d001d0342e08449140886800142c40803503080181e82c01441041d443e0300c40700307480f07550101071f1200140c03421074082d218800d0604002a844030540ba054191401075802000d4051300c0303200318a01c5901c0b408052011502515800f04c0400d090030b014040e02d6a080c0c0041c020f00210042d681005400e0340880218402144804036030080d83c1b000151003012405d0f4580b0727000207280381c003003441500080307504082d10030348424081119000d015020b0324812038040c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 920850953 1250 920849703 920849707
    0x60613150207030f0f060b0603040807080a110d12290d03030902030a030819090b0604050702120412140a2a21020114031005150904090c15090506040902 67
    0x29109030726002d0359074002001024441c100c0c10034818941880c8030410b016481c00d204a440407000c003c040d10003101c0007030140009000000c08240540090400c40c0c2080c01e100c1ea0004014151900d810709007090000050440d0017503000654150060031030713042d101802c11104076810084c0ea45c40a200d03410281c0600c40420807041414031a4110388a925006001c3e100c61214500f4001c04014040b2008199002610094107070007401d4403441c4070240c0c102c0b98985094888000b0040a00700c0078013201f0442c40b50084c10f402c5107200c80020402410f0b078415207094000341b07280c2064040d02121840ea019000020590302081051002101c03040807000c054424500c0c0da0310001d2598503541240c0710241e28480040c0402020031012070b5594000d0b282c44100500c0820901c80c41d100807665481480a1050100404d0604014801107202103803031880c10184820045421200303800d81c1916200c445803010400300c5400b80c515006600c0e079141c541341c1c007420300e000f152191190b403051039102980 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 920852203 1250 920850953 920850989
    0xc0102300d060602070f0b0406140d060b04080c04061403061801061e060201050a05270307051501060f020a0203060c0307021614010906051e0901170109090b060613 72
    0x850100c03140710105601c1001403030340340c0d040295540032500400d50020410b40010600184e140265802c035a259a60595010302903c0800d003d80c02240340302c1130181e00c6050124082c220040a80007428004008000300e1440f40100010b41d010380c1d100c4111207a00481c902d0680c5c40106243c1d90114003d4000c1040044c0685098010162984104040301c8402c00905000d00308a070781130101c46041e4000e00994807201142030031a01c050300e504682d00400400c05900c2c8207480390128015074080d06490500c00151540d904000030313500340382e07021001c40c801881440e401690301c0310804c0c11840108204452507020039914400070f0100a81042c000c00050040c40c0f007000503140e04055408a0801d06688410000015080401c4580032501c00c10300800e01c603110710b055442c00f5a040480c4c0c808480740716542003040d0300801c00c09040001d0314410701d07200e0364182d010300e00800080d0300010700c0303604074201240890005801c0601c40e03c010460307402104d500302c000205030307525411100c910007c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 920853453 1250 920852203 920852293
    0x171c021c2c030405040507050c0c120718051f0e060607020a1e03060501060f051804020f0408070e01091a010e0109051201021206040b0a0b0307050702210c0102 70
    0x80140c109050890307100203450403584012014200301d40081e10140243e8464a506480310b00810700c1d40c00f01d6038441002c10302c1e03900c1c00014003142980c0b18810740c1d6885456680b8409403104583e059007105803150f0a0020060001c011568140080005801c4840c180860f4032400703403010300f66a00c114004550f4005541e07134650884001e042c00542c01c6000403c1c0207900c2d106580520060301e903207203410000282c540c09120503000740030319a921a03180c14001d545021201200f040d4450300a40d00344505448100c44000410240ca820f20003400b08504d07001240c036003c0c1050f000808203504164001c10024000d5084c2c803c25071007407c0c00c2c5104c10200d80100e03405c0840f0b601c4290b12030000d0400c00c1c1e4070101035009101303107085004040c155036a400240000c2e9050b00c3d4042d0381029817800104010105030700515084030301c61501a281000d40d03000209102040075100c4031001c01400d002004400404c400c980070602800030303240603102048010540074074503048020185504a034286041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 920854703 1250 920853453 920853491
    0x4060b0a0b120717061311160309080f070614030711240603071d15040603060b041a060306012102070b06090a1e0e0a171c021c 56
    0xe0340c00301458403000781c1100b0300c038110300545503000030900102c03446802c1ca026401c1031303204010141201c20785100c64082d400040c4200004080c0380c1d0018403040b0950803060710203c01e1640241d0321416182d0801c80b02c1400c0c01200700402e034850f484003804000c16908058030000355040000159100d550300141580c2c542100c001c24819401031441c80301041d0316140d0341102460a1100c40c046990700c08060581ea440c00340202e016031100301c1a0121402000740400f503015070840c07400300c1000a40782c00300302500c10780e070002c0b2003440e196201e2000d5810140709001760180303903812560b07800c9100d00100d885844003400c40c904210340481d400c0d00485920702425411908448110340d200010b00381000542c0040e5215032180120b113011580039035840c042d000c0741ca1080c80d50758543d000b81d10140da0041c841c0c1c00c440011030058540030804245050800040d075580111802d1b0303126085521000351010a40d00340c5a8144184907180501c0342c08250142c008560550000d46411403c1003070000e5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 920855953 1250 920854703 920854709
    0x6060f0418150e010203220507151d09040f0201030b06071a0103020109170c0418050f010509010605030a0c05040c0306080607030b13090b1f081b03070509010e04060b0a 74
    0x1030140c081c200c1c0421000b241e0454100d81e10403010000e10702202102400c0c3e12080d00d00020290f581184d804000c0030b078400301c042d02c42c0701d6401c4400c0e01e6a16005039060204406031030b8003061031202d040c0c880501c110b500740003401c1c1c212043c2c001d40c9001d5481e0308040350000b20290426580d03000703c2d03281703458134411600160b1300011f40310b019003805070742d20080e0035090008a000032031241001a101c00d000000b000010001c0001d13000b9507900f003003480020030303507070010312014031860042c000801c006010303610208403900000300c2d5034034050742500d09540c41031340114042c4d840850f030440418810500d607020342d0401c4401141801c1d40820403400380090340c01031100303070083c00306006520340c15070300c07403040082d041c1d070016203505030162114101c80b4400c8000c2c080c5801c00e400a5480e00740c2c2c0c9480c449800740c0c07041d102402900c401030f80307150060440310a040038040c5018045145000c0240000409046542d00425814050300302801d0001400050a0320386404600400d983e90745200006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 920857203 1250 920855953 920855981
    0x30f09020f040f2a120e030a0831050c030a0b010e0c090909100b010f02030a1121180427030309050d030e061003032c030303040303050612010c021213030501050c03180d0206060f04 79
    0x251031132b60013103c04c80000401e0f007280d00b482003034401c00307842c280845d1f8142c800d80c10070b8800c030150307113070036140c0e051380e42c00601c0e000200e10300708201542e41c1e8070700d207a1500440d040340007030100d07410300004201192014100c0380d040c006caa088000c201075000007140c001e8021464054000c1100c160f02c13524128a50b000946500f51510002d0306920910000d400b0311181110400003829100c03060004486050907000b05500420b401030510004185c02c020f000d5110b0301e00003a080d082e40d00d550b81400074100075100000e444000045c4950000c01c102900049030310882ca01b1070380f4680d80544645040c6043d04c4400c0e48002c40300c1d0000f00d103072141b14003100005d01641c0e903e24040c075004009000c11110140b040d40c1043d04965032050510030040502c145400610b11034900101151180c0c001c00039142c5900c0c03000f6404030004800307001e51030040d0400c120858a81c10801c0c0e0814680b200c1c3e000b45a059401f015401c445541d0006045030420303002d44514550309030308004a000707808035400b0940 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 920858453 1250 920857203 920857261
    0x6030f121e030702030712030b03070909022106240f040b01170a0b01110c010c060209130f0606020d11070e0c07051903030f09020f040f2a120e030a08 66
    0x10f5110b8011004000c0f0500c102c40c20030703612019080c19012203001584054055008510a00c81e103030703080d401000818001403282c0b180c0c26880307040c03040c1c81d0244a122491508a1814000c0d07200303000006644503060400c1d0618401002d20100b081e84900c99212032150b0b454481290083c2d0040e50100c0c8003403269004048103242400c109405803005400550001b05800ca0030104500045110b01c08004140cad10110040d04585504000e50400c400e0158813210817100c00d000d4030850b214000700966076480102d80c1da07140c8a0301908214048035a4000d020384145098140e920100d5800c054a0303141190712160340b56500c0840c00790199131801005481007d11100c001c0303003002c403451352540c40303680c0900c60003030781c0d20110702a80c3d0f4100009400c0b09170441074031a14a01a00201900043c0d9000080c0050b051144502c6401140702142c071030700030075464010003035880f410064600403000c100740701c14028070902da40c0ea0701c51030860200308000880881e158030b40e40d4280c8200640c0704201c10f5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 920859703 1250 920858453 920858461
    0x25060507020f1212032203020318060f07030c060b0409050304171c02060f092d0f011e0501051005030103030c0c05040608150a050c07020d080c0d030902040506030f121e03 75
    0x2820301c1c5c0c0203450b103141c4002100c180100c60203610141d2990300394507501442c00c00036050300c1e00c5a02d0100f020944da0101080c0019411940c11802500c80030b800b0341d41e600d0714210f8606000702159003909905000301c1c200400070010070b8000044a040b22082e2003142e0b80c6680210309a03043c1840504050b5450304030314001401d40c1d90005209008021000b8024071603120182c1d0607a0310b40d501503c160241d01d500340c1801500041d4100c260b50141200c065803c0c00c45000b5200b401c454100e001041075000d480d9111420311410301c140350161000343c403004850007034a02d0241142c0030501c002800c01c074500c0600c2e410401c010041c41c0044c03501a0050184944a40c0c3c1300b51651800007000390813007040c2c0700184040380c07a4082c0c1c42c000c60032449981c1c03a0030650b400707001c0c00b03d502000654044508000c08100310a080000f0782c0c0795122540c000411312000d00c1084141d480180900b0300c40e90200304064007503040032420b0f03c902c2041180883da18001c40c030784541a241040c80348420308902000700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 920860953 1250 920859703 920859733
    0x510060b03090d0f27030b01080609120f03010e0a0906050406021c0912050901020a080c0a11040b030d0516050307060221220303020d090525060507020f12 68
    0x195000340341001c1902d20502103440211691380009601400051207500c404582c0e500091210441075480f55165a0325a101e849903118894282d1005e04598020002c0000b014024403158401d0120105503528043c240c0840c6135440c0418019580c4007680c5202243d05405030b607001100c0075034000418440d0340303480d0600c0802508603110303060241101c07295a4803400d185110324500158040107450035046040fa003125150007902d00181940310f580c000d00040303540c55019000c2e2040000080001440e2440c1c40c621034003015210500442c2042da500e10b065502142400d1a0110b134600141c484541d107030400441800e1100c06011400700048210610402d500100045194103640080b20006005220085482140c2e5a032051103601c0f41c0c102c3c2c0d5a42a158140034034041d140150410b03020b50030702022100c84590031980c80c0e01c61404003006c6080e50144607a081c91040c0c03101200b40c603011000d8064418100000d100340750118588040d0340e00c48540b814501488411030700201c00310807003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 920862203 1250 920860953 920860957
    0xb0f0703061e060e0a051c080c0f0a030210050115030c020102040f0617150307060c1a0718060f05070f050313030305031b0301180504170c10050603010506060f070510060b 75
    0x40d10f4000350b4902c4c0b031a1510300302070084a084484c0a00a9030f0f600c021003551100000b0b00510032034510808015909881d1000c00417182e95542e8003000d0300004015240181c03a1080d548051009203003800010404c070499001001c0281c0c046040204050000031400c900a105540000003101c0e54100702080c5a42e210880e44000d003081c03202e0380d0302501d5012150300750b142d1081e880d80e810743c0b020005100c91846207003d000564031030481c1000403225a41054042d07113080344c1c1d0a001a42546500b07180c814020071480007085541084d180d000d104150040c0a40308100014080c1c5800420f0a010800c081080b2103032680c41c002041d2241d6203901d07008003d5417083d80c01001018182c000d10440844650071139040f2441221118030445400d09290068000244140c0d109043c1802080318410540c0c000d0000b1021030003e4600440d180880ca4116400034000c640682c2c9880708216060b16807000311494803101c46041030b200c01d954a440e914108400000b649558281240040c0b20444200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 920863309 1106 920862203 920862209
    0xa0b180612060301050604050108210408031911070609172b0908011a040e19060c080109020711040b0604091103040308070207030b0f0703061e 63
    0x1002680d1500100d4291105505041c104141d078a000e1080a0b8400b4040b14100015410026000d07544c190700800c0607108481c0b010030110100300e41003580d004101c0302c02101c0c0d65100440302e6a04000f0f0144604010686a0165030203601010551400359125540ea035250340f883e0070b8240304a6009882e14500c0c0d405a03c02d445c08081641c0020a20105249495000002c406e0401010403d0b26400141070ba407501c0341c68402c1000709003031ba03074154030103c6001c2010104100100d06141d2410110000182d1a0322103030204001d682103201c20100640310b45440d41c0e41c40107071500ba0710030b0b184010301d26061140c9a0b4060710741075001500d0f1080240243d41400d0700e4010000c1211030b20343d0742441d8110040108010507500c00300055120b2014405803800e5841e40d62032035403071400a8804090082660000390f04c407071096104e00001c0444074070090703400d43c106018098600081c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 920683453 920863309 := by
  have h0 := BRFrame.cov_init 920683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 920683453 ≤ n) (h2 : n < 920863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
