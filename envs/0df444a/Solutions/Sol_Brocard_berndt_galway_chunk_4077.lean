-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4077
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:30:08.451476+00:00
-- url     : https://prove2.me/submissions/9b1cf460-1be3-4e9f-b872-571edb125fdc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 733093525 ≤ n < 733273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 733094775 1250 733093525 733093573
    0x10605070309030206030106030920030c01120b1306060e01140d05060a0b070f021807120c1115010503060601023405030312060102011b0212030702160f0305070501080603 75
    0x4546403070b0294036940442c00c0d83c1c00a90201002c01d85038007083d01045210f82c07030161100310700807501116003405000030f9a12040c00e10100d050082d00011010420f42a401c41c40b81020054804211007400750103040042410344941400507104c41c403458019840b8601a1941501f440310150030944240a10300c01401c01600d410350100f102ca10000701c800700440503161075030155134981401e407003900500012042c01a656220381c0621810000e10310340001001c100c1d002408000150303140c50b4007040d03a10918444980b14503210300e04000c0382100d0380c1d05400381070b26415070603980ea40c2c07601401aa651f060348130944402ca6007880350003038883c8501c1e41c2d401c0011001d8610200a980d00c04c0030030305583c00105072182030389500381000225602405080071445801c00203d21505008400039280d0078880d03211504a0f0000011031840381c400c01c20310039482c1d0005440c080807603890700c10114042151004444500a400000400350702410499100320308c080d020700303131440110302c01004541c084 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 733096025 1250 733094775 733094777
    0xa031b150c02150a090c0501141b0309061b12070807030528030b041a030a02060d09080301150e060f091315180b090103050d0f020703051b0118050303030106050703 72
    0x45a48075595483c2e4800f030501440100c038001480c2c050350709126454401541050b41444003800418801005070011035042c1c3d9440f025044200c482400c1f414294414050b555511080104413800240e141045418601c18128111181c0320840c001111540c040c2c4840074001807010300c24100401d00030001050800001100312241c4c0310040030070810740342110384800c0026550f9000090605240c0300c4e010094888400c82090000c05030300090b542d4800b140001c4c01540040380000b5800c0c49904207040d5543c1c84543c560b01c2c0d60312400300e40807180c0300f80c500c030001034802031798103205051100c100c80d2480b5214101c01c3c90420100f06104545203012050040603a454948070088580c280c210070140c00c4031f07440016422607990385502a2403261800a1041d002c1d01c00420004800140c18a50009039091024241c13002d41d40590801009510160042c007803020a040c62404000007001d0341107098955042e841d0f03118540c100b0381255401541c0d01b51f84200300503c03400e4003800240030040d2203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 733097275 1250 733096025 733096033
    0x103021c030908030d230928020406031b120807030f05091509011202040b04051c0b07030516020c0d172503020d0c0b1b16050a031b150c02 61
    0xc3c641c03006265901815017080016a21400011118440c0700103030003103160002103407020309000000f941c8540c1980d8541044941c5032021403205290f1040341d40025400900401c0b0080d40c81c05d00894106540b603001129010204000c90404034144aa6075070b29000384809003018815a81901c200040c04031035018004240124442036942c5080c0f104030000e001c001c55141e40c2c0d04070004d040e4204102d01307030fa42240140400d0100854a42c2030700c2c12110101d5510300b01100a0681c2070142050000103804014044100080c03290107402103802182c200020140d0504501002c0b601c0c2c9106440d13056220780a80480808242541100495100a9203030302e4175214a04505500350307a90704810303c140040c014060418141c0501440104250f18249a0b030f1600443d661503005038401000582c181030f01841c00301c17000040300103445a0b03400c02c0b2a2280100a2070038003580d1280800c0d0110300040c6103489810407100c0b510501c24500d51301c905004c002e50405d14880f8042c041c441c50700c00131440703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 733098525 1250 733097275 733097279
    0x140f0103020d02070c06090f0b0708090a05060a11060f2208190e030c0612010e091e0c041104051302070501180c060201140708131407060302041d0103021c0309 70
    0x46a84010304d80244600b020308501441c0c290042c2c40c81680303030b000f020701d107180320300421066240404841c201c650140c030b443d50b1140c00030002036000d4901e42225401800c04a0a02c014075081a12803001030700c2c010468840d80e850030b4074040c0c0c0e00022140c0d041131003050040c0f4030072004160b0140c0c4a0034805d07000c0a0400441300440412070303950205540c009181f00f50340046900301881000414032058400b2803130001e61104201600f80c040c0301340f0a0a69200e400180700d1001844101010703008030314501190ba0410403203903034440c01d0010662099140c124491482140807040b00c040b110080d20b8501084503c58501000750071950081d5103554070780001ca4a030107015691441124801d140e130195640c20601c0c02400c441c00c7e0050300d0380382c0b5100d90031b2107411a0000ea00c40e50004401481c24591041d0389041e001c0040324140b868881c0c403d5101c04101c0d02c0d05030700508144c03101030a030440c0c907402c0d1001c1d403040702900303200194119001440000070b0003804e11905500d1802030401c034007059 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 733099775 1250 733098525 733098547
    0x11040b0309120d0c1b02030703120c0804091a0a05030c0105090a050603250f08060913150b120109080d0b06074d12010f110a0216140f010302 62
    0x6800015800052542c4d26205501c05401c64415541c204003046510f82002555010139511400c0340400703094205001c1c0d001c0794852080319003030107140d40224840e40791981d90020708090503810401c83c460b104502524140360a000101404442c03008000741001c580f024010740702c1e6400441d10310f802c0074101d031012510b915a48002c6000300e4031a03183c503100b000c0b58515840300540340e41c41c02c420022000013028031317290b005569580110040303c0d051040c0d00c81048040c01e400340408020040341e0004c03240101c0c0700b5a130380f01280c1c9450035038203001d000c1d44001a0608880c1e03400703801090303200c040c41502e140320441d61005440d180040c084501e0707c101501c2e000385902d500c07584944601c0000e00030b990803602803d0306010b40801c80344e0340d00e6204014204604500121001240170b0030400c80404050b2200750403031051303164440800c20454080b03d1200c80140c0c4150f038032030054400c41703804032045c040c104401408c8444058004460711445010407081c2c10f101001c0904054090007428214 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 733101025 1250 733099775 733099777
    0x1d1b19050a2706091208090103320610090f0e0901090f060b01030f06030209060103050601020c04090b0f011508070c051c0c05011a180402031e0601090b0411040b030912 74
    0x2c000884a0160003902e4540010300c0740710309402220f0704c07101042e86440018020000c0d9018240d09003004a210070b81148008180d080803a01c507101c05400a0b001305a440840c140c4078000c3c481551460b080760152801521410f005120345041c00020031001c01925141140e41074000300d00d20300220b983c1d2000e4483d4100b41c058518166031071542c0e071107400215a014458894900c0f1400d0090008501d10b400103002010020441410f06440300b00081850f0702c280460030400100900070400c025083c201307101b001e20b007100c00c52080340815002003410351144940081f2107043c0d0f59201175981d201181202c5850b007d4908075180c0c81180440188512010ba114108034110354440310f800c0c1c01c60a00d00d0035103c3c00000e40704004490316a4040035190102c04000740f08000e510541035440d0381c03020919040519200c07180b10b200781c40e90f144d003294021500300d04850103403e0a10070000900100403c41d40d0300c10680b518942c0c2003204200d4040904042d640c00810780e03050b91a68050b1030286506 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 733102275 1250 733101025 733101077
    0x30c04061107090c0f0f030b0603063d030e010905060115020a061d150907090902030c0310021b010b090406050903120901020c07090b090a151d1b19050a 67
    0x454518403107003145e140d20501000d40c1c40c1041c681030000d503c0f100b000c1000380c8406407405008007105403006002c052192089040d90341a0110300c008200e0140240a0340384110074038500003400e10418980c08001402802c004542100181140d40d00c0d140091149002007007054081d03004540028012401e00d04c2084540d60151030182801e26200c6202d60030080121a030f0440c0120520501840d0100013800500343e072409580003500a0303090002a00e4003a88060fa5541072103810703050400412981c000d0959051483d1018038054801c0c40a5070a84808109650b0001c150100007000302d2015000706400c90413050540340380143c0b09400c58900e180890725800700d6900000c000f841c4083c00c2081c1002421000d00801100c041305002964660019010340483d0b912040130300008102c520b054402440844205111582480c880f001351010448110b210140582c0360701070700604000840d640b1030060f41444081ca80003903001e4490780c1110321b4100400203210501c2060240101501003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 733103525 1250 733102275 733102277
    0x2090d0618030e010c1a0a02070f12080907081203040303020d090b010e0109020a0203041412030d050108100908161b0e0a060602030702010903080915070b040201030f02030c04061107090c 82
    0x40340001c1410301400c80e40038400ca090410450107801000324040003050b441150a514440351180c54031080c03000030f80141900900b8820740c6014880c20002510304c203440281203511030701181d0360f50310038058944070f20b4465107a07175801030084003000d03191890045a00a07c2401d00600704054042d2800841d03014480c00c03140798500c24014007290900c440c2940c01080304490a5151280d070a40081d03c81c0031b0743c0700d00409807000001c9010720381d031607070380b89150307040eaa43c107d0303032600308082c01480645001c1c03040d080540544501e414181016001e0b94586540140165140074041c0704444018440c0740d4040c4c41900d60840e0f0041410350a00b00c1c0c0c80203181da50424100c5c2c2c106007a031602183c8141e0300c034006640c000c0103213400503600251001d040701d421000e82d43e01c41d5482d001103400c8500348454824117010004515080111180620740158000e81c6e08100c41d01113000091700300d00c82a115081802c80c140320030411103110b0208032900e07042260070f45009950b5684000243c0c0c021440f680 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 733104775 1250 733103525 733103561
    0x4080a02010305062428050d0b0d02010c0b09010e030309010b0910030c032319050f06040b06040b032404030809060c0a03111b100c050304120302090d06 67
    0x2000395079140c01a2038022108880501050000301d0001030030805400f02400741044c003044d5104051100c07503440600010141c00d0303450503c88414020200d5010141488519103401304030026814030340100184241d041c0c641c2d10a003481c540342c007810510001c0042d00c896417504d0346103100c510b05202030360140d40f8680c0086000c1c8516001c0080c2a04004c01d810b551a042943c1040401d803200450703000c4940040790301042c510399400c98040c01c10a20b5041916104000e0100382400c3c1501c08071000b00d0080060355602030f80c280c1e185440702415140500aa0380f04004141c0915007580f11424050b401130454441094601e21845d105400c2c60500702c0209950041005058004403655400440d01014105526011070044980c0c018132058004065071441da80100042c0d02c07003192000e0b268078100444007040c0201666581c8074604903000c0325410964a400303118010010740c2d00070303940080034040c6074001200440094010340c100c20741c4a0010501000403803200e20510101584000c409 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 733106025 1250 733104775 733104793
    0x50114060d23010f0e0405030306060f041505031009050f061e0411091f0c030302160803090d180303120e010b13021206060909040f0809060d0f05010f0b0d0209150408 73
    0x40d00c4d8500e0107600440c02d20340a8400c00000403400f0080ba6402901161030325143d0701d0541d40d2613158011604082500034624422050407600040503600c1141c00c5400d201d10141c403204083c013929010b80d8041800c1850310042825850a094035164148142031190030003181c900004068448201002c40280c000040c20025410000d0403540da14080107040011021a2800100340c14036082002d0b0070150301040f1a003041c1050448501d54030f07046000c6a45904103c0f00954951030031002100114104001c602c0c1c1c1a04421084400c0b660941c507140d05001c64142000040e000c500e0010340c4555844e2111070080c1c0d10480c20513038000e200900140c031908003910010b8101e10240030710b807245405004204c56560f0b40040c099006a20600000c95a101460101c44a004107195240c0c0800c010540c5181c41c01c40b0340c03186080400103041070100341d07a15021040c0200c80e60040504401d01000301450425040d00203213050340c0040c10004002c0702d407480140b800d0b0803503082100b442d0480001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 733107275 1250 733106025 733106039
    0xf01050a0e06060d023c0102060c070b0406020706140907090606022d0a030f0e0109140f03010605060a0c061a0303040e07020a0c060305011d060627030307030807080a050114060d2301 80
    0x240d03100f0302c2400c8c0020902c07418041c0d0072490794011000010941d9034000d002900304840e540588003510f5200805000d0b418000094a900d0242102d80109902c02c103100024803140c1405014202e6045402034860110b90400c0c58483c000c000070b031449072031005070041a1440080254240850007641c4014000688a0000384503074000c500060410880c1c400038061000c00390a200905401268202c0b9042c0140c40400c0c05004140e11140d4446004607812a20702d800522101209205400c200800900c3c480d0f800e28200b00d849004da0554428070003408044e89802e6000e40004442c01216003111003551070b1b0440020541080c00000d80798801048207044607407104518000d88143d41c891490040082840342c00f8100170b550380081d4a041d14007550030b00d0216030400000150640b5a920b0543c14054466801581c001001501e200000707150010588610b605a40030100c1c00b41580c280c0208028544c2c1181904101c1e16507251035481e030300141c10b440c2e4510041849072402c1c1c2c640c50844 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 733108525 1250 733107275 733107379
    0x121b151e0a020f03120c0a030e060f0613022109070f030602070c060e011d01050f0f09010f2a29070306050301090c05100903050f0f01050a0e06060d02 66
    0x42001c00d5a0007440f21880c075440c85c501e0300e940000c500d42200c0c0c4030501004100c0c0903104c2d9034a66041c50042d51f09106400c03100090b100d100d030300c041c1c80e030100400c09d98800a04a2150403003801e070382c1800e000c40b101d025030004080c68021120750104d8042c1c648603c9003801105071070f0b00880d0501d0740060f214040081c081d1245000b4101e9042c020b4200000c14006068242e54035103880c0044c00304050a020341e802003003502c6d03503c8050301005803600035201003142290b02c01c003a101e01044e9039a813100c235424410701c00f49020014204603107000381e9050041c0c0300200c100a01c2210120000200100350500c0801c800707241210030b03d9602c01500b4600005070488401d60040c0703001764140081c0c3d6012500203d0391070100c0c5d400f51182e0003100000d55080b210030400e504010304074010103d0403420480000707699018a40d1107002042142c40b1106010115801c1425907185134006900090552070001c101603910b9002614100040b446d0700c07417000400c0310101030f10000303402d680c1600020141c4a1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 733109775 1250 733108525 733108543
    0x1091505011d15040b121003031e0519050405030106080a260d020a0e090c0a271e0f0e040b06010c020d02030313030309080d0219030e03010f0b121b151e0a02 69
    0x41f51060490708689000b400000d16103c031012150030b081d05d04481c244501d04413040c8030300c0c18619030041c18030002d008100368030070b1140c1c40c400d600342440401d1950001c02d0000c4425404000c05101d241446a28013544a941c00900c1d0302d41d005003c41007090300c1c03900042080a2039130b500d81290341e0b9900b00300300701034601802c0381d2010705c014081c031808183c1082c4100e01149a0344807214840400fa0001d480d40989604400384820722040380e5805890188031400950300400c0d51441803035200d404d1100b80343c80844c0e0251401c000c0401040155000c1c0001004682c006003030360700403040c02d03000300345182e01405030a00b4000c1d8100c41002810f82c450903407409030482a000c0e0a10001c2104002d598010400c403441300700441c0f0710b07040105402500c1900e042c10000e40284079603501c0d00c1314000100849007443e40107440600f0100d60f1200e010802811004090381840b440d44a0320b01441221000e6540328909407108000d08003034150001a0076079500f00f900d8116544400a00d002424a6804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 733111025 1250 733109775 733109791
    0x9060b0306180c0f031c020724090302010e040213150f210b03160608150102150c160b040b0a0c052106010309060203090601091505011d15040b12 64
    0x4980d41004200c0c0100f40f03c012448111869a04069100002030070442541210144d809060a00054040c0c005c1000c000709c4030400100c01d102003121072004403080c00c0f42684c4000a201d00802d20040d07026070b0f44101103a0001d0001810007031901041900c141050300580000c0e113403020100751840c0e0102d80840c5291180c5000000c140640c20000c030800308110018601700d450b0204070010f0307101042188008031044030a0888280d407854060104001543e107400c020b4191180320165500001da100c050000301d16140b00b050b42c401e0010312a6401286002c05410b4042505c01c0c04109841e00c000d02560082400c040035003480f42c0340741d0442d00608500005d01505110480743c0560080040801d0740710300101503225030313400c80102e000300100c480081c102440442881004c240c0000c1490580e980e20404118045d02c94400c07818110048c8140790020340701000340d249418441d82c08004002014001402c1041c809007008440c1e040340e0042240c0c5180400c948101442046000c0e40020700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 733112275 1250 733111025 733111051
    0x1b1b0102071215090b041406060a12030f051b0619050408040303030c0e0a140108010905010b0a0c0507080102030c120f071205060102150711071e0314010f09060b0306 73
    0x580312141c81e0b2019041d00c0a000700902c1c01001d07140c01429000710008503484030340d2401d80e250a02d444014500c1022090400e8410540041d0090800d1004001603401c2c4444c40a1404110780e406c0b94144240140d00082060901c14105158080010504140b0b08a400740940303140c1085002e001110410080d10442d08150510005c2824102110181c1e505807401182e4003600100644040600c01c1d040354104048042c0050318040c070112000c5030442c2641ea072616030341c0c0c460030802541c00078090070001ca0b50030040304940c03c3c01030b0130002102e4403035001d5450070356864841a003203030004c89641c107034110000f42c0d000d03001004030345495000e040898801542d04203030900034403141d02d24894043c80c5982e1170104299070f008000901000c90b10305051181450728102c000c004c013100310340f141070500c0340301c00c00328101101c5a0204040c10004d0440d00c44285141c50b248010b81581050750a15543da6400d00082a045c1c0903003001c90307002d0708000c03486003080c0e003d061030598001c0032030f101566 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 733113525 1250 733112275 733112279
    0xc0807090c080c040f0320060d0f050a11042903070207080d030c0816030212010312140313030e190e04020a080a120e041424031b04111b1b010207 64
    0x40300000b45c030070380b504010f1918010089174032030491064004e50b40c0b54402e0700425440300756119900708a00c0e08284000c24015070300c8088805050350401030203c400500d06100c14000c80c404040000b186039503081200e080d9007800c0c690301d03000354015942c07200183c1021b5014407405d43d042000c00d02d40a03451804104004441d0001000150b000d40b2030f80f0071800100314140e485120790141d5549440440100e49503503507038500061440161501c03400403415907075503200444110000e60b441880d10710010140f5421607039048450400c082505070344048041140c1440c0c0e229103151001600c90000d1103031480c2028010805485400d5012424039070121803490005200441c0c0d02c0d404c10010704164540a050340700044c05011500a00c0300400400801c21204140c440340640109034a0b1740096000440c01c401d25449403680343d0924036000c01c061320741d400c5007000d5000202580c00e050311030341041c0310360140c045000d03500405500b003540a1303001d500c40150030440d0300d1420f007002d00003011100c6c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 733114775 1250 733113525 733113539
    0x60301110403080f03060f1903030305010b0c06130320010e1c0e0409061d0a020a15050307080a02042402060a150911190909060f120209040c0807090c080c04 69
    0x2100d204511503104d5030210101e2000d0310790503000502100010a03030a50110524805000340740c0503c019400a0b044c90000501200010111503164407154050300d525a2440040e480a4650140031020000c210041d9030101d000c150136814002045070020400c03440c1007520600d451940511800c40c1d8a074030705400101e41d00b003446104030340e00550700403d0420712820498010f00c0001c2c0c1511800100000d0310b80303207903000f203000010f0724800c48003001e60303a490761500c0e00390601200825000c21000c2010802041c02802815448030112401525154541d00e03130144540d14040c030143e56000c50440802402d03018082658000e078422020051400c0c011040b41c0300078200d214214a103a5958182000f2440c0c4000b141c0f40d071036010880e1304c10b5010f20100107004504c03901c544840289000004600388088200c4281180d440003c105072174410b035020000000000b40c000c036001348401e4400900c070701051003200e002303014042000450307501a02c1e016100300c0000b008111038202c104000e00200d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 733116025 1250 733114775 733114777
    0x604020307050423030102031513020c06310809010e0118060e0409140f100903020607050d020d090b0a1d03070305070311030c0c0f10120507020c041406030111040308 73
    0x21201d40c0b1501c0440401400e1400c030604e040103000d0b4155000000b00580c1080300c80c1c50320388490041c1c40403015290b600c06944100c0c013414420403400c5d0488004501010b01500e000c1d00e180703c0e00c01a026940b0300f65500420401c09220007158400c0b00410710074001e43c0c00c2603504001d00d00a00f0003081107158118240d449190500900c0140144600d02038880e88490b8080d040440d8030030010801250300400c1155100154480440c5a1044082c58031341090140103004519038903030000c01c095215548161000d800ca070502c2030281d0b034240102c2c1101120b9004204055004a07012031103401d06000240c00e8510314074022a072103164014221056600108076031240e078041c601540c85968601c1c0444261000d034000303040611022440c3c201d00900410400b203500c0d01121585c100480030010b000c100303469400840c1c003103042440c44001064513030300415442141031058a07600198640010122406200107000071a4044200a4581400d10801414401ca2085035041c54555520b80e01070b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 733117275 1250 733116025 733116029
    0xe0103020f040525020f0105042102030a08010506090117270109020d0605041e0b060301150506032806031103010b0f130e07121a06041b1b0804170606040203070504 72
    0x100c03401d6100d2034804a4821b10282200b408a40000d01c40c904050502410b25405034420b4646040250500030450380004210707040300c1d8130fa450f08919030386880100807090f001000d24038180458031594100c9000500072562090300440722441d01c0c4103040502d4460400c884182410b541c2c07410700600c001da41c0b8407101d10521a40080041069038480c64031040440d0200440c2d048d00b0f8000041404000705440070b0340c0b044e10203030700070052201c4043c4072000d010301900c502604240300304081279007904038040414032078103540a28800c8180c1c12814500319200355006884003075041c281d040c2c0c2840c0a0048044c0711404480100704001c200c00001d085610103a4403248032a540c01d40c1c144211000d00a580c010030040d52400144440c41c01c000700844685000c80300b14045000c005a110f10b417900c2200401d40c0941005980d4550540c0e0075a90300c801c51a1201a450752926a0b00003d00340c03500400141042c410000020380180100c20311300b15000d8500e9200e14010700030804c0f0f0650042c140d4003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 733118525 1250 733117275 733117321
    0x30e0c031b06120405031b060115180305030c0703050115030b060105072d0302010b04050c09040e01060902040306020421171b01090c0518040c1a130e0103020f0405 72
    0x503007205268005200c07446103115032960300e00110b00300300601901001509100491076140c6190001c400b1005031100004d008454002200c07400c100180c3d0b105030718842e181e9446d40051820b4a0310f03600c800b8074682028012500a601660091040050a0003481402d44050407459415070540d0f4590061010040409041013000700300781080c030040c044440720010f030070742c0034580351307000d000c035001401c12030780c03400e4000d582032042c0c010843c1081d2052603c1ba4903918009401d09140d94100400ba007844075a50801b90b495000c041103483d55071000784000c602c2014010780d80d514011303001d000409400e5904940080e182c1101c00800c02d20b05007503601100300007a0b203554200d500c4044240644040101c7d10541c80d100603c403c000c10441d03007900350741048460b02c000c040c80320440c144113403040710010124882c100040060304008510311040800c4000c186080a40c140000c44914801c2d42c001051080b401c0300420a60420f00d180e1050244165403d00c098601907154815000456541070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 733119775 1250 733118525 733118563
    0x51b040b0910091e03060b060c1f02040503060c0309010507141608190903020405010f060c0b0603121201150804020102030901080c1c0b090609090d0c0305040b0d0507030e0c03 77
    0x20010361140704540c0280c08070401940f04d125413184a00e14038800c030301040701d2003441c141c4801141c2c9410010b07140700c01064401051103485030680e1255642000d4100b0301000e8023400040f4499906200581c441c0c3c4461903002e40741c0c078284542a00f503c1c40908030b2001e0000c0082d940c0b00850788501240d0752048080c0c500c03158611207103065465441034104003042c80200b44917010740c05034081801c01c1121300845040c021070740c0314600c1c00300040c441d02c500310102d107850465000251580d0141ca500110090175200c8465800c961030306164862006040314005600c01030200d840d40c102110101189890091030901d0a0350010b5500d11808000343d050000c003a000480000c0d584c400c480c2400101c10b1100c4254080c040b0240180c105c1c00e01a03403003001e14034002a00e60070319109061052003071100410100c1107541c826242a02d00c44c070160100034003000041443e40501340144244501c00000080600d02107400900f00c40c10517580010680055a84054030303a00090741540c0700008400103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 733121025 1250 733119775 733119799
    0x53f0d211803051e040612062408100b0f0307020714090117011e1d032503030e0303070f0e22150305010e0309100c0f03030903020a06060306051b040b09 67
    0x403c4180b003c0013034543c510800042c021505a504c0681000a0749036484180004c5499115400c0340c100705422841d0035004040b6911015845000b801750042904090003400f262604680802a4014850076244c40d000005105400358100002c0c001000700e0b10014030b08500308030004580f030344107103d0840d04040a1100c0a000701083d0b1020480c0700031040f624403d5041e1181d40710252900b03220818040181c4410102405004030032125061130104152380808000e0f11003642c0381e40800f0040e800c06a07034150307018614000300001c1d406100540ca4942107203d4071070000b031401a80d1f180d09800b078109149900d65800c4440c5070403100d812038404c0410704011040c2588400d01030341c3d201a000f50309041200c01003070804401440300d448152961341290194100c1a00c0c0d49410340d800500346181e1640031000b1910a900c800d150512910669841e61910f0720351170705440710b0740c0068400f669103e050110024081e4103207130020007111142800d2a203040d0364199217020711508513016030089005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 733122275 1250 733121025 733121047
    0xa08061302040b1201140619050d060c0c05010515120102120609090a0f06020a110d0f031802090a06091a0604361401053f0d21180305 59
    0x90841c0c402d0721039008000c0841c0b5510001c86c1c1a0b400d0b1191070003100180c040a0401111400030000e0780c41c003815090284009640b160000d010b540100c000f040a40c07040c041c0011400e000c0c560156001c2149220484074000401a035002c0c0d1784041c0c00303941c1c4100129214003ca000081340d02030011102d403900343e40c0c0e072900c00f8100301092500408401050b94001c7c00c001180c2d014100c40304103171b5107100307548508003866641d41d10b490b50381d078011440f0b140c0190506032084c1c2140c0030000d140c0c40004000e8203e035000c00c079a090306848500e60386450701c000744001c0700c0511955191180040050404585950104150f84654010000c142225030145130040002e44000c00c003d1003403440580010b045e0807900f40042843c030208080c14490400005050b107071003403554403010150070020000c1c07180701103071551840369800e912001c604451100b404015040c0441c08690200e51940b20a004108030049190140e10304903025040c0f501d4001204000d2142c50240c43c1756241c2403660391001c036454 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 733123525 1250 733122275 733122289
    0xa0e0102040f0902030f090a0839030d0509030310030b040206041205071e03020a06030b010903080c0f12160807030e030a0c0e06090c0307030f0908030a0203060a08061302040b 77
    0x10b810040c010307801c001094516540114071800c840c0044400607290b907030605445004144001e04554018400042240324500000302c0f50310300c00c020340041c50344070010501401c915024800c074640000c280490044418098a580061000f001e541b039841c100b01034151086441c0006480c7c6421076001500715150301080394060011075203148500902d0380f90a582e691400d001e111000d60100c1243c40510358003098100c1665402482e80303850904007102100148a08544541042580c0c0303400030100f407809004143d4205800050303c2c43c2c1c200c1840540c9401d841c010100407202c1d0070409116502d40c08a400100554403042559403060305003401c80322620000c40080e4103009090b00c00d030422115103c021700b1690307a01000704850f507481e4200804150116035016880b0410800030700317001d119070300c14142d50203141d0002420a55a4031381a1654004503850090380b03034000709010302c918140000d08000c0441030000d10301454410341c5100901d086c650004c0c0500d0311400310b100d0395a2842 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 733124775 1250 733123525 733123529
    0x60f03020c0a080d091509120c02040b10021c090321090b22061805011116030503180d0503120612060a1b0507020f1009030b07090f05040b03060a0e010204 68
    0x2c244036031900d1080c80c00d400100340441044031005031046d24803914041ea030003121003940d040ba0115564140e04042600c1070310400108aa22560b00c848481d1985e8811001c07102c0383c00e441c0d00070700552020f0142820b1103440050407600303001d542081040050161815491240da601d079100005008001c030aa4902ca15504010900707940890107070079418a0000380388031100c6031030440e0b5100c0c1e514001601d0303410181908840c401011b05040c080355000316001c001102c06001201c3d55581500d41304500c180040e0070482d4240c10004a07107450101d90091011714100850b41650030380c409564003652442100d114002d9844c4034000504030340d030345072110301c17200d0054000c0d40d409180c081000c800409941981400c40951079a102040500c10f2098428841d0302a00d8864806496410803078015120281c060401c80303c18000b00005205000035800b400480e01c0c0c10522034104180d03668880700c6c0b83c04c4180a540b514803180e540b40e400041c0a90000344a020001d4560308450380e550283c8582c2e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 733126025 1250 733124775 733124783
    0x903050f07030c02040c03020403021c0311011505030c010801080604032a080c160b0d110c0109032d09060302070311060106020706031b2106050405070915020106060f03020c0a 77
    0x42070401c14941c0050880041d0741c821030301044252000c4400754124003031808080d41140c2d40b9000c50b2816418200e0b5003090034068203145641c0c92420582d035094828114000c1c004941500301000142410492101d925000b4201041e0341e40c1048ad08039519500208003604000307c10001c200046201005107540c1da03007884e04123116440c1810311070082d50200b80c107940381c2e119000d12040010b510102e104180d605004000703103442c4c034070107051010302008800c00c0403160003040001161039007481b5502c140d620907100c0d00405a088805440da02039914000c001800208010200c1c0c10760204c070b55410f5a850307081c0141c481005090840d42d5180e00608039690788a441c00100e0303580c0d00021054101c5006a4041c88103c6581c000c44c00c0381c0c04120792041c00310714103640e0020807240080c5440249102d42a000030101c0c0e4400018013039450a40f1110040741102e10b0078402050303803044021002e40c140c0028460240303029402803100000947c2c01042590115140006236024841041c9035504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 733127275 1250 733126025 733126027
    0x30d061e0803031f150801060f030c0e01050702061606060e0702060408071403130f080c010c0b0103060915090602040303261503010618020a090f0b03150d0b0a0b041d0304090903050f 80
    0x74444060146c1d0028001c0d400402c01c1c0880054440340b20b030150301c841d001a0b698100c40c0780b0807030005458640080c0d80407a07104000344400d080c803004a080350000e4074042e080125201d8a880c1d55035141100190003c41190046010003010518403011226145d92202502162440c000304881c114051040500b09210443c007000582d40001303540b000a84040702c2c151a01d00c40340c02c0043d198804685802000074041400400104070707540c2c004201180249280407000e10712041e080f046515640003252030300d901140c02d109050740400e000d40038089500800502544894091003400c000820000012250b802584120340b82904518020102c1004402e8044181d0304564081d401917003840c00040c040c03550000360170032004142d800f203901c0d0300002c51858a03840e440c4510791070b000c084503402c1903501d0350590000780100d8040d889010380d18400240402880100402d89410161442008004068640101780b010084070101c400342003000a01d207003a858103031913600511044048044c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 733128525 1250 733127275 733127309
    0x114070f170c07060c030b03010c0c150c0908070b0a17040213090212010c091d040c0e0717011805090f030901051623070b040f0b1b030d061e0803031f 66
    0x50547c02625040383d00300c0083c401c200c03540c60304580030011035001901c11704071030f070b035a580f000030315800810f40c1c251901d001d840c2261216181807800e12030b5800400c451000161041425902010021104240d9180b0300c92509281d00010442c1a00810b0b89204503920b1348508210350b250b0700740f5103181901400a011144d881d04002d00224040c2c030500581040e505d0142c00b8291421034101d100b1a407040c0041c03152414200805490380005125409024150a00d24042204009500d0007020502044171028030103071019000d071800076088505581c0301c130b00c1c0c40b0f2031604040162a090b14003840d04503102c50706145500c1c03182505403c007402c500f00811501c801700c440c54400301420031640089800c000e90b1056210290301c6588036540c0c1c0410308220512a2941050040c111a110f4000303686040000d00c1e101800c5030300502071a15000e83d07034401006400c41c021404450302c0f200c403a203507a5991038a44900d880b071000500390610341c0e07510b0404025200031205020302902150f18405d0700e06e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 733129775 1250 733128525 733128527
    0xe0102031e06190f0810090201090317040801050c0c39010e04050a060e13050d05091f03020901121103072304030506040b010909030909022104050114070f170c07060c 73
    0x3092400365100b46e0291107403119080c01075016a21165a0603517406004524544400740140540701c95081c03950010800050080024024540202030741c4071065660004000031514101d85070864001d0ba841c40303141540380e407800c504200c4402c842d210304030071108030120048903620360340c4240760351252902082c0301440d40c565003d0015941c3d030b0801440e40d525003c41c1c0b0f040004404c94001d10b542e1111a02c0c8944907c00d0340034100700d4101804245e820b40c290780c3c45e80300300071120f208407001942c01315200b081580c2c0319003070002c2100d0880c01045204921151040184402800388082c48006070108050350940701e440f921940300981000d46898803441d0060b02c519003501c0a07948400b00f1800400d0703460252140145103503040d220042c84514040c0241c0c040d420041c0b45810307400d0a0280310000c8040344214610991040380000380051022120a8041d0805490201040004c50b000d00741c55800040c1e0414001001c1511b5400d84d407496800c0c003480c8141100100711a050400f110070701 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 733131025 1250 733129775 733129799
    0x5010207060e01060e0910110d0513170f09060f0405030703050a3c03020c21070b04051c0c051314010902030c071112060c0d0e0102031e0619 62
    0x39042d0003401081d9603001c120700e1400042d200082c0541201401c0340c201007456002020403545001c4140c102040103541d00200d502c00c645d039860344806827828204202104e00c3c420060b4442480a03030500b000c40e18840c44d1406603000340c501aa00001e0b0150050740303100300350342c000d2400608503080c058507441c040d9290300c590b40040740c503503800300c0704010368032082840d4250280340e6008000c0d070300c1c201c0c0e0310703010308901c081c07a0a8003503004000d2510f0b8251141d5071002c5143c40c0c80c0381e002589005c0c00c0002303490994140c0c4062315044090109100c590380e00300c07500c0c207082d0309000001c0c10501d07603040c44035005e5680c0e40314650241c44c20008071240000350b00f20600e08034a100d5500c810380e0f0b9411031b480607480304452402c0d41c42020003110340024a8038a612110201c0548011910a1240d044070304d080c4c8140c0d0f408c1010000070a807207118103404e005405c10100c00d44025800c50410120090030442c410703803000d07a400201000111141c49d8550780c00440052181020b00f9180d41c1c1c0100000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 733132275 1250 733131025 733131041
    0x30b0a050904051c09030809010507151d0c0604081e160f060e010207060e04090c0b04060206091608100203090c0a090c0f020105061509030a0f0302030d05070f020a150204030501020706 81
    0x40c0f8411351201c003070803400313200f4807011250080400d61400e001100110b820341c0c0955070884600901135580e0041c0302151099046005404600290304d26440c40702529200c00500c1b2140301d680c4c10042408000b20114000d5565400b00409810782001c1c2c00101c1c0c2060890341c411800c007615074500054081900b102101240d00948a51002e00d1520004988664503405448049152110714003020706069100000d80c034040c60300d096100381c5400494226a10581c000001640039505210082405014644208412003460700c1d1061070050704603120030020038902c40c40b036408400502c59400a000f41c280160000b0a84144903840701590b07801040303841c00b07140004040340b0010b400c00e4014850700d400788000901141403801e007501c415503141d0104103c01d030140101d2014070000780c2549285c0003828803940185480d41c01c0d2407100b01c03c44030014680400c110346410b10161807900810741c80101d580007440c61203a101c0d0651820040d2080e07500007880d942c400500d61040c00003980c09410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 733133525 1250 733132275 733132303
    0x203150412081806010b1e18040b100206010b1810080702010e0d0c08070809060703080a1416030c03110d051503030a120c020a020d05010b0406060519030b0a05090405 73
    0x118540314440b665003904150a0024041d500002c0184900c00451000d0a02c01850410208040d20380081d03047d940e0300303c145003200b0391026603d4a1000e141034010499242c1c0203030b4101024010030b0707900954554041c442c00825950000740c1e112481141c5045e109074a0000e00040f03203031210f820004150900c200d41c0b06005520f00200214044004191030180321901d0b55980d48118583e240d5035501e91022400720b13508401040340c0c09042e1606c802402006029032149400b40c07a052054000b928126090540e04e03a25101c10080c3c000b081408507044901035140c0014155054581a002488240070340c0d00601c001145550b5038540c142c0025120340500d2a88214180042d001d02d0b50302e01460034000049110801d408203000b00560200103510458811500a88040d4012500c0000e000000f84d415944810358a001404c1a0003000e00800103490564a0200c940410004206103511001b04042d192a141d402507601c054030b11018200c01820607180d8100b506e841c50340c80340b4626082e8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 733134775 1250 733133525 733133537
    0xa020102060f1b030c0c01060b0408010b03120a051c050117071a0f030a0b2e09230d0512031605070c140d0f1203061202100503040203150412 62
    0x142d0321001c040c4428081c1a454640c3c08480c20154000e2519810043c40421100c1051056800408003401190002c0075403240d1180d8880c18440c02c1d5003074554584402d0300960024075200c3c049595982200c10206403441e2042e00c400152070000c081b440d110407079900c220701781000401da0b45004401041000c00010031991519034400904c400d03103c0700e540b03100d1a5041230250403401074095000716404100c41c10002021068071000507409000c0c6100345039580070650681186d803824403030021a2442c5800c000c0c01c0b85142c044052201214880058600d07031049046803010b898001c4003c508540c45003e071000e0f5034454012860b641c2084078201d5004140001c884a15030040c022070b05400d03003201502100d18105022880e140003d05c0301c1c540c21900e49c45e50080480c10850503081d0803440398090040713005035140e00500761441c54025212080c00707442c0e40030050f5106401c00740e4040d00750070031b50388036501c600000341850054150311000c51030322000c000070454039079442c0b4a58511603c0d41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 733136025 1250 733134775 733134781
    0x409060f080d0f0c0506010602101a240702060409050402030601120b0c03060a03080310032f09071403040503030118091a2502070911090a031b05040e0a02010206 71
    0x11005402180c4240d507550303009181e82d124180d110f544550f80c1a01ca50400101044607580c034503140c20300c02d900010041e0001e001d1a0324005150080519044603c00840d00540c410400a80c556003003918501b04082a010911504840e84041d100c02e241c005200589642c5d60b0303603220001d0301d0300b02c5040b13220b03005010000c9040580c0e1240c15201c5038000070f5201131039a811510f0b2410b0303407001d460613501c0300b0400d00000001740031301d005501c10340c03207243c0441825145290401d02c0714401030798100c3c07100c3c683c8100100403142d000030700d0314458122401982501d410301d043d511245100301010315000c000040100340400040110b0484041070700c41e6080916100581d022940c403090000c01209a02c52042c9400d581882c000f42c018060320380003042031045007001d400700351070040340c0c4000d40c205801c10032a080792445000f0794101e0800046140004003000078014540501000b061508400c07241c295103004004500d001e800090300802a251400d804907503a103200320f6089006216400c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 733137275 1250 733136025 733136039
    0x306060f0b0a05090406180b100f050a0503041b0f06021504020a050f0f041e11070c0e070909061202033009040e0102070b010e011e18091205040906 65
    0x90042100d0201c1d040c0d5041101007602143e40b83c0c4100c48441c0d200307850b000049800d81c1d200c02e0000d102c18141c41c0005d8041c0425081c0500784081180038401d00c10f188d03001070025038001c002c4501c0c400252810303960380da031107242610544045885e0450600320802c2d0229124000b01071580070381d080c0d502201c079491060101c14400700d0080324001d402080c504407c0206041001d0760f981005070003020000d8162000003c54100c0d03011040c42c1c1032020305070b40703c8040b5000d0341c07140c03072141203e4a8130b40d40782948a44805421012a1258000c0e8420320b0000501d03c074030a90b00c01c0054803413007000f0303c4a02d0b0b0700c4001d4120cc2c015a08107078440e00840405404c400007400000c0440908103148184074035101e8080b401d00d030001400c0a03000350300c1c0d007240c00000340d080c801000c017244207100300c51140d4101021041451750580290710400d448407103410004400112080403180f032540e138410171a84503051200900803813200140511600e005040780c15420801602c00c2d541c4d0410108401a5103400d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 733138525 1250 733137275 733137299
    0xa0e1915181211010e03012901020c0d080a090e0406020301061202072a0e0405030a09150c021c080c1c020c010c020f060c030a050706050a060510081b0a0801030606 72
    0x100e8008941c1c828902d003000a0444154811003400c141030281e038403524030012a00b0340d180210100c0f840150001104004520041c000c6d0b40703183c080c4028507004101c0b0020415200150b0b40150070810041952060984101d40750390107080341e0741d914245401c0c80d01d006c00203034001307014000c040341d102d80740b80d86404058802d4640c0785401c91030004d1181c000ba8101d07404904521303c0241885081080862803c8070192480d00840c41075006645d680d0075064014020071a5400c000c400c080350040c1c1009041c0d02400601e03130309030102c03505000d94529000440218482d010000c05510740480e058640402c042103014034035114200362954004002800c81c2c540c0360803c68a400305d04400207100150030002c051981149025100500d0441101b03c050301e5a0400211540003401c0020007008002090103807681007200d0540c10b220341802c101c0051800301a8072602e100b04400d110000d0940180301d0240c803031081c1041c6c10b00f40e507802495001040c420702408280c036454200307040000c803001030603 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 733139775 1250 733138525 733138529
    0x60c08130206120705090a080c0307060323060f12010e0d022a06041d040512040e07081b0c0109110d1208090f0d030501210201050a0e191518 62
    0x20b200e64a0a4080402d10b102c00c10090a00c60070400203016482494540350584005090200000c06610500c042014a820400d8000404260a0214202203a03071115144c20700c9560744501c3c0c1c40541c0d10580880c84010201c000b80c2e62064150854250364581940402d48100d00d04095894001080a060b1313944c52204802c10424010f13105c2000b141c1036034100c01c2c0b400d602c1c002d08461400d592040b5070700d030006040189030350562807581030000700082000600d09019100200505061802c00815400c240040c080001d10401e0350020318120080400790801800f0118496241c041c000c10681c02800445812a00b1942d1410803c03400d1420680c0c42c61500d1b80000c021410b1040050110350300398019100900078410b40b07454409040e810b20103101240000c0e60000307659854402c190725000c0e003c2410300003803100d104020300541d91100856011106a040500304090060045000200271460060241c94420804100704030b40300301000250805c0d81d40c044a510058114001d1105a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 733141025 1250 733139775 733139779
    0x170d1407030c022d16060912120c02061c0204083708043f030e04110f0f0415020601080d200105090a1403070209040627060c081302 58
    0x100c2c50200382e1350265800c034600d401e801ca000555000180d1806481d01041060f01c14400c1070040080c00291750182c40d8000a0440c5201b119a0103019200c440c00d111406c2040070801480e84100f40654a4140854181c0c00d000d00c00d04681410410a250007034016014a141c0ea00441c005201c140d400f010904c103110300501d80840c00d20494411894105003d1081101c00c03031414000000d8505a0000c0d02503903086d4441c003e0358081c005400c596052500c003020800c0c0a1500340500c000ca80d00000c0048019400c0c1c030001176035203210b00d0380c00203406500d1880c0c0070340d00006401014030505034040d0085404a0f004c00440480c4000181c0e1264000d000b4000c140d80035510500c038545c0b00340808010040c0c8100c0654558111001c464291141265803540d0b9500c0080503800308440e0f21007464031044080084c1d03007080801e0340064105500074001030020f90702e41c00030940107a100006201019203014400404000e07a04d440001f41c00700000c1700c004281541c001401024220100c0b01c032860b40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 733142275 1250 733141025 733141033
    0x60711072903130212030915040320010315060c0b010e2a090d030305070905091509040501230f130305030708100f08070509250507170d1407030c02 65
    0x9294803101c81504010650b2403c0c440c806000405070b101c007001d400d043e500702c0d0040c6560303805100c00d020002e2003c500204140304104420404030307100c840c1c402140580c50041d03005007800b1100482c080e15040c45400c0e00780d841c08ae13001510a07044540c4401c0c491103181d070501a681d8070020320188640450390411644d5081c49002c5800c280c0805804a90000b0b1801c01c0c103103121140420340d09403090000b1000300380e940c2c0900102c180c01c0441c0c1002080115002461854886a000e03004040a604140034540400104040020a4104004207605542c1c0c0d400c1090009088051641096a0140041901e4400300e90a5071402c05604125074040d2075071441c2d13480e034000071940074000502511494917000808103000c2d06d5608504020000340d4002c1c01200e0425080016001c0302038590001c3d00310044421034200848502031195915500b8001d03150300146c20404c0380304501c0c43d264400220002003400750005c0341d0703201e10380645440c11848031964507060140c04a41e107219004015900c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 733143525 1250 733142275 733142339
    0xc3206101202091b300c0901030b060904020a051306050a0203042d0e0114041803050f0403121d0103150b090d05010e1b0d11010804030e0306071107 65
    0x80c40018250001c203528041040c0c180540284d1502d07030000625407415144111700c002d6240303100701e04913403010110a07208582d0b0522820f000300b18031a0350b1340c00d818140c4984000c94142c0c0c81c102a100500d0010f0015507580b6135800300100fa980c0705140015500c504001d021400d10b116405443c1041c001360011842d041c1084a68000180f0502c2c8658841444001c403014881c11000003000401044041500380d5050041d08050705000c22245405249030200c00e24028603003501c20703480e00d13405042241e51034051480c003035511f101e5074002034000e440c040045004e0320303400100e012010403503c0240300300c1c410103c0110191205441400c50a001c508018400a00c206004010410700200003018191183d9181400d607881c1d2111901142c210300038601c4004121030320105041d80c1140d50020b075011959840c030b401d4099004090411071030500241c2054011908513004200003800c60707540740792040c2c004222400640c44400d55002d03540340041c9000743c610114a2141c010290b40301545 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 733144775 1250 733143525 733143529
    0x30206030a050109050108030f2d0c0d1b0b0105040b010314090610050a2409050307060e090906010f090e01090b1510020d0c14030d05010f03060e060c0a0c3206101202 73
    0x2000d40754010b6487e0540c06032090400b110500422f200c5821901030840c400c008980584501c86030401d80c0d03003202c07082e1480000035402207081419242c007110001000f044400040b0300522031818905029030444007442800f070070001d43e0922a0001e000f252054549a0342803142008142c49a59400043d004101c90300451404060741405e070189012042103a403034000a182c11481d03884034011804c80d189201c213a040c414055580020400000c0009514214400c0d200d0141449840b440581e00c0c0203a443c44d40f02900711110058018001300d01c18100401c5180100800015191081c90856403181040f07001107909844c804194982200c207031403e071158100d400c3d8680c0b081002d030008010036a83c4c0440342c45258064064200000b2000f400c51070000d0880e800381800203561792000d420801c1e2092001d080b98400d404500d020802c103240341c642003500d24901d44030f1103052240d251403e40300912089500600f422a0021500e00c0e440340781c440c021552482c0580d00c0c1007140c40001034094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 733146025 1250 733144775 733144807
    0x30b1f091401150c050d051804060506040b070305190801050108070305061005160b0f040314040f0b0702180702010c020106090506101112040f03020a140904060c09030206030a050109050108030f 85
    0x2003803a00700000241001c0d603807036051840006c60403010840c0822090364400422110602024090300c0c10482c5608003c000784a5000c2c03440741040c0790b24002129402c1500c100d00303840c1010080a44902c46445110028200c41c409004042c001288007000035120b070b11a028260080d80090b1280a00c010460703011a0329900c41c5042140201280005400003404101c0300780c81549032540079000c509244c070f8014441881c105900c82c0e0003009220600c404030b1403020a4003211444a01c180d036414051010840c07110b0320407a40002c40710b040c41003160868040d04034511a0440d5802080455118511902140d400792001604942c0030440d04240b68080c100030841c2c51000002c543c01818092200d9140c2d130300641007407480d040c10140070401c500701400c2c44c2c0040d10358078040c00384a802d4400400c0b0100b00c020405071003180c8884201505a0180030b410001d5500902980c0e0b0740d14007a201c2c04082d101c20f101c0e5021310381c640400042e0007200442a50311031503400e8042440c00b8003000f641403507 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 733147275 1250 733146025 733146059
    0x3050601031b050d1508010c0915080f220506150307060509040f09020a06120f1406010f11010c030515030a02060f0304110a1e080c01020a03050310030b1f091401 71
    0x2280d036490085105050105c800310b4010700101c0004143c07449500801000380c0300b01d070b2024456291078141180b8440d003058200b40d21010348066081250341e100c0e0311140303410031540303c05040b824000c010310030b1000110b585882002e02001d44490007240c80c00b40f5a41d41481e00c50000000c0040c0154055480c0030b40040358100046030001c159117a540e0005602d1186562207000828100980d041d00000640220003844240003000c001083c030091918081100c0101014100b258018614110030f004940c0315000590a0b002003120100b0520041c000307000603504450310350030703c82801d4918500000e1001050380c0c040c107146d060000c0300c01000540c1d00b000e0001c0380d01c4405905440c0c11615980038180092000e4038003920104443c600d96001c08003103800c6a80d9582100248101e1641c00007240007400d981880c010f95240e03203040b0b0552100d0403d4000403c0c82e039081090044264400d00c3c100c1810211400d00d1031065594014541100c1a58003a0075201403400010010301c007204140c00341d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 733148525 1250 733147275 733147297
    0x1050c0f0f030c09030106080604140a0c050f011106100311060a0512090c060304060c17091c020309191d0f13030c0b040c0801140c07080a0210020d0b0103050601031b05 74
    0x10601303959100103801c0d00c0242c3c01c00c4109520803810081480002e034044c0c24510000005008a070b011911411104000c80c0201d80c0158602d2806170856403050031030055003110701003954442c1c1440c24001048203828441550b05000389092036030317203180031402c0301c654640c513071910391400180651625224a0003800c2c20128001c0c004000821b0305d40d1401584644d103d1180001c00302c0384d006c80902907411140100c40343c40c400d00c0400129080002c0c80411881d241c0518400d42070144204a1941c4035556220b60020540ca4198a600c01980340e80c3e000c0d2188800c1542c0c409174000c0401707211600440f501a5007000c034030040b0b0b070001580800e41c0500d40c000d1820320713101940c80d00e6220a00f0800d1740e088901d4403100d40c0401c484a001e100f00c041c4070301515104c18a40c244410b6134481070283c0740c0003804100c40000e441403554001c000c1081c03d90a0008250749405001c081c40000384060100d6502203418407000030401c0d032182c865041c1346a10b404041d03428080c13444040341c42d9009418862 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 733149775 1250 733148525 733148527
    0x6022e150f030305120a090507050108060d05151b0c0601090207020604080a0c050909070b09130e07030f030201060501112a0a03050c040e011506032007110301050c0f0f030c 76
    0x2041000c03035144040701a500a4540e2a642c4061a08003511000010000c640c018980010300740011000b096503804c90303400b4600301256454079800245815014440241036220350202c0064a0f03542031100b03407050301c00007084945500c0421b5081014030849201c0d18440d0004d0005120074520b50f03000e0246c460020b440301d81403903150010380d0300c3c02c0c00544080c0c0e00b0181e098403c00152030007181c1c55074084444006003081c1890700c041007100c0d00410440c207100d40306030000c281c201d4035198010b5654038090011140c1c01507890801c151038030500b440a800650902c24041910f50140e008154092486401003442821843e800c11044107038030701000c00300400c400104c07041d60b80c24001901541c0203c0241410041ca14200000c81d40340a1991000783d042c0000b00c43c4d200c00b030641d80c4003110320604000c18030181105041c0700c141c40344050000c60b0103021480c5024000107100400040d102500200099101c080500310035004900e540070010f6410400b01106072200009141c100c1d800000103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 733151025 1250 733149775 733149779
    0x132352030b0c03040c0605040b070212010f0c080a150e0a020d1e020a080603060609040807080c0a03090501020d1103040b1303061b02100509061302181006022e15 71
    0x9003044080075114081140c070040705000034001e642175440002e04103410641c2c50b051400c0e1785c1039400e018050001c0c1c03040c2004003042d20302400a401a0b480c0300d80e21241088489104003010303100743d605a5046014030300c2c00369895045104d4013042c0041d5a00310401104507981e40b6090b0f00030b503000c04009100540c650120050321a411980813002c3c103910403025803101e01c0140000e1200710028540e51203944081d0900c160303521450301e81a0460b42008260341d8502850500e804540720f0320187c18640d2040c1000e04040c10b600c5071040098070400d0382500d0703590740e00c0c5000300c42e80c40d64a1000861500708000c10003202554134020103040c0c5040c203101c080c00381d0b00d403209421075043c1003040070141414100d94155aa052040c541c21054452081100f810140d42d1550384680c020300c404411980040440309558a070748001e0340801003001501614034010618041d01a00c0d40300c3c0001612400084503180c0c01ea2070070b00c25413140742001c0030744d0100060155502038098002d000d4a105180200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 733152275 1250 733151025 733151033
    0xd2408030307021005061e0a080a060f0501080102070b070f140c0102130816050d2d020a06020102090d110a0806070e01090510020613235203 62
    0x40400600010019540324500900041e0401401600c41259a403909081089944d201c000d100448502100340340154004100850010111074200c60304a00c030790304220041051940160411f40682c3d501070145036039994070a820303400f9030603000f450303890400d001542c0188160203c040b500703500d107484241c0b12003030300c4040c040d07902204aa2410765000103c1ca03184000d03170000b55004000c110020003a03619400c2c1d6041e070194060003803e1041032501c40d803000344050702d040004c2241076a40c031542c03503003202c407440c04040101c110220f0003030001e84030020320103006109560844001420f20800300703a9582c2c805201507181240194000c3c0d1164000c40c2080080001506c03903480c1c1d44940c480e000c8444009400c481c550390010f0710070b042c01c0d13035481c2c07060f80c0c00704a0503002000d112484580d44014a000b52000f00308011440c01c51002c3c44c0c0d104000c2c40002489000d1088080c42044100034010801d00d203200d2100064800c040041d00009442001c03107100c0c0c1c0d07100c600b800c0d0320145c2606c03903075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 733153525 1250 733152275 733152341
    0x8060604050d0f0606050a03211806030207110405010506040909140102030c27060703030c0306052205100308030606030a090b13050d020d0206060618030106080a0c08030901050d 78
    0x509550f51840c078030a52040000522503400913100031584052034900c0c42da140000291105620269450898841c3d40040d00460302101d00da000c0d80d0b0340c0540e05880c0e180040003500000707020b40303540303d5a210343d032101d090501c2054140d1780007904c1c032441c0c40e0810481c0c1007d0945400115503103100e40041c0180280c0078406103005025100303849544030040c2da001844016407440d0711000040403070a20000b45d40740d208a40c0d041c3d51600b004150403001002c203900910f1075502903030304036110240402e413180c0c0782a00a0301540d49034008211986a02404102200041c08000d15000d01000030915500e046006035510180a2002142c100081d5076810f03c2c00000346c0c0d0210004050106400c10010280b01244c800001c900c0141450320390302c0c0c0b000759a41c81c081d007880c1c01000b0000b10412203400090240e4500700f00038009201680d40d51a0042d41ca1000c1c2d0015594101010400f1030303172000c04421103180100507500c2c103003400f1b400740d1f541c0001c140c61285c103c1c0d030100c000d01a42039400310302 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 733154775 1250 733153525 733153549
    0x2010f1121060a0902160c030b0412030b0f0907020c0904060c030e07050d03030e10060e06010e0603130605060315040b070e0a03110103050a060306090506060112020a090b07020303041d071404030201020a030806060405 95
    0x22700030b60900e04144c6803075401100300c600044145414448141c403a41c542003940c3c520380504a4a00302181c0b20140d059040c441520603880e04451701a0401060110300c0c4c0011480c200590b41c10401038904645254455403e401210750040a000c06400843d2098004134820100041560f940c01d51104404045034150340c4112060300710801085940c3da044090a10207130001d031031192852400052112000c22064070062000d9550408281b1544080010340420300c4040b07040301980c24507050608a495040f07550000244000e85400724604000715900300320707a449102c08011010720401980a414020203401c0019517814000000c50014014034100902071009000780c1d081c010001414504143c0f0b104840c01e00400000d20b20075841f084950031100380c8000c458440c019480064214071855000349011100b03610715102c1a070701280154026004c0380c440040d006400d1000203001d01451001a0158000c10a00000309009100c00d503840240102401d180c103465400003070510041c0703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 733156025 1250 733154775 733154783
    0x150603070306090f06061b0501020c030705060f06030705030a03030c030b284103010e0d0905010c15051302040f090b0f0411060a02010f1121060a0902160c03 69
    0x502d4081003050305600c20440c030f014080c0c60070301c6880d05145d00500762555000000001d90f0f03103201000700b488829815901c00322035040540b5994152424000ea5850083d40c1707510101045002081440c500050550112100a40070705040d0b500c43e02c2c141e000b41191001801415154010100c0c20f03981c2e00000c00c41e070840e082d403080f01e21351605184811006550000781c0d4141007080d005000300c180c070784184000b090340111003130f80040030b44e0030039600c070710341d102803501582131009a445501c00881c50314482038035035035640095680c172030044074001a40e800181c0555080c50074400400681d80200303600c640002e8050044d81e2450b80402c0880343c90300303004507042c1e5a82e00700d4000c1028041c0e8480c0c1143d000307034911506050075224086491940000c070b510480000a184080500039000000c03a03821000040214184c0f50246010503400402c8a0b02045c100b0900660501480c244007406210701030308100300d16003400c0d1940000e5110001d0b26540b03203c42d901060000e0091015a0099845 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 733157275 1250 733156025 733156031
    0x1e170408070b09120d200705030a02060705120105010e18010b03060a060914010e0d1401320f06060d050a0c02070803070b04110a030609140706020d171506030703 71
    0x21608008914020140c034024941d042240c4e030000741c24140050720088207424000044140fa00c0011401d0070b01c10508a041421b0003040f1081070080100181241d0416a003d480d0955a800c800700c6003807240c086525031541c020700060005521400e24500c03a68000780008055244901c400c11765210242d2110008601c00001c00086007001d0780b00348001c05076801c2c1414180c0c180801030700d81013040c50456040200c06065001070b41ea545452004598110802605040d004031255010340380d00d2951803114041c90040b07008181c07503c0a00d40741541c8040c0380504e80d840f6217602200c0f6900c06010903a000c84103100845026009224441c000c0c1c0c104080001c44841858001c1e0034204561702c40030444e0014003040340880d0b02c4919599202e0703070210000c5c0c000d80c042070001d0039280c0c80380c1014080525100942040025201d01c0203a0408020300702c80c06190354000c200ea03202508070301c0100245520440110080c44e0400c445d4101c030484401c170034000e20000218070283c03c01c440f40300003e07071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 733158525 1250 733157275 733157287
    0x3020c0109151506120b060403020a08010902010e0f030307020409060e2a060309100c03020f0403120327060b03030705250e130206090d080a1709010204061e170408 72
    0xb81c284210030208418010110b003a514000f401381a034000c0080303503501c82d500d810341d0150070b554050494010b9036005004210075a00e4400140c024108001c00b00d010504240311841c07986020000b840a49a00600a41ca4030940d23034284401362220203000ca401d151116010300044105100c9240c3c2ea9000e800c01c240306408507000350140d003a000101500a120400620031102004034070b6107130003160410041164415104210000d10980320000344464001c80c011040210508005004500c95603040c0545054071400c40c110b4608024000040c2d1401035181303001501a402001007800f0050a40c0c0c2016000c1d118035050103544d20b4035143c00d00660342e030b180190541c240c9d40405000306042c0003209141c02c04058015100800010744146c501044c440755a43c1c440c0a00740e00554480e0000391101049074000c0d00006407040d82c03104400d01d450019140d908140300307680840b40580d0b5449041e8400e02c503c108400e18a5009608101c03900825150650500e010701d4050762007090480c1da960 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 733159775 1250 733158525 733158563
    0xc02030c0405160305150303030f0414060a0203240f0d0609051506090f04020d020f0d062405060708090607080d020301080a060b01020a03270519090c140d09020103020c0109 76
    0x5e00000c103100b18031250140780b03580d2a03c000003525404285080c108c0340c00d840300c0c00c180e072100001c1c020101d4584103000401c00d03080d100b43c000d540180624202c0280480307124070034024181d0f00302e41c00358001111144003800c901c0d0100c203218006000d141d0029903103880c0c1d01c802d802c0c603207524950a030514004e0180009401c01e900c00543c040810a15006907003429400500f81002c070080c040e2051041c90410f500035600d103800706840750380c801c40810a004004003580366903050403210364401d1501e401d0018617410b000701280c50300d0780d12020180c500303401c150030410290841a81514140c50500003002d03a0140c034070040d0b01a06100c8024005203509140510948410344091070440d08207940300700000c1c2c0c02c2800c4840c1c1e050387d01e11a084812001c244c2c16078030b40c42c581c03010703600c603410b003842440c2c03009110940c0c02501c0c09541e0600404c0302803032064031052004092010b038040308002c24501001c1c1540300640c42841403502502d40080d040340642902d500e82c070183e80f40d0070b0004450350382c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 733161025 1250 733159775 733159781
    0x50105040c1d06040903051b060f070c0302030906070609020604080721050c0103050702281520130b030a0b0a0918110301090c060207060216030c060c02030c04051603 73
    0x40c03007503800708071406507414600b038030803100546007034080c6440e503075141c08260264040d03850036a4106800004120705d11525503481c0001d0350400080400f5001107000c2d2032040200501442c0c140e001540f034031030108180082640180720070307a402992241800010307a1004002d1004012140080c03d40e81c0c1040034002c034600c90601c0c4803c03083c40d02c501c21070005401140c0b2043c074103024240055035a6031040b0580c240084407143c0c010502080703005000c3c84000920540a0501443c1c081a444658401604c101c91500d00240384804242280b4001d0740c1c0c1c14002004100c0d032120703401314460398860454005400c143e0302075a0320354884600c5200350030880f40d26001411004004d01a141169500095020020b040607040d007402c0300250300da5441c00d4021515042d80284a42080d50f03581c8402504c1d00c070b15004400060065541100350f43c1d005400f5141030725040450340e0f50240c60124195000d0203007801c00c0360503000e000341d40c014980d102c0c400c0d43c2c458040a04000100f6003032100c000d0031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 733162275 1250 733161025 733161029
    0x504090b0303090f010e010c02100f020606040c09180e0d0c060e06070e060c0f071412010e0c01200105010b040503010c02160b0c19080d11070b07050f0c0a050105040c 73
    0xc0d900503c50440320356144075420380100e00c06e00300407510a228000480340c20480b224080e40101582d12900190380d0300603100240c001d451fa0903a15a51240300c10002070342c1d003141044000907000002880220154044482170040c0580700040341103031140600d00f05401b2084070004503030328000300700900c041c0e405039102904202001d400c403840c0019002d1f20b11150402910300443d000310b96a0385240d8108491440085d030070301101c0a0964030101c50071300d9000d80503040d000c0e100c0c00d41380080d42c402c140a640c0780c50644201070085561414011516100d01d10a0301e501b62058140d440c2040100303104542c06000110b081c107580d2414403040c5820340d8038296904c0d0456000c400e03030018100000300a08291071a110840740d070740494a0009213003481c03070b0354442038071a10300e48440d040082450003820300e03000d845818000031845101c2030302d850091280c0a4050720b001c03000100303e01e104100403c00c5480c102d4a00e42400e072500c7e1011301e01103401c20102d5481c1c3d034030024042802080c0c1d00303401c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 733163525 1250 733162275 733162279
    0x1b1903021e060f070e0312220e0f1914090c010f090e011509030c0e0f060a06120509011e141803040603020f0d02030c07030809060717040503070605070504090b 70
    0x10b4070f040020518101500043c818000c200301c0f882010304541c3c0c2032000000d4a06043c80c060344813800d8081a0440205851410200c058090800600c146001500a03ca04428074914049607201580300c06581000756400c4c0911359034081c1511200300c091800c030301402c60320f0300800b448100c04001400d4614548a00c10a2007062a0300b08040445c41a405054400b0300300e1030f800441c800724054a81e213610f504001c03c034030103840000c1107519100c002c280c445c0c5074204150b965510780c007050011700401400303140001440004050144602900282d41080030743c40002801d050218252404034000341c4002100380d280d21130052200850b6400c01d412130783c032081c035030515010503104079540d20841c0b140109247c1c01140e002140c214900070f40f100c1c40410607055540b85850a05046a948022001c40204100f03001044640b400000c1c4a4480c5006403a0315940b0741d1201c00010b45503100500450342440104400743c0003175101d0013494000c0c03d030b9442e01038403641455040301c2a15500c604080c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 733164775 1250 733163525 733163533
    0x1b08090402041206270305160606270908030705090a0503010e0307030305060f0d0f06140c250c1404090807120f11060103060b01030b10080a061202061b1903021e 71
    0x5c02051612000554455150403d02d565001c1e420640e40b05550028014001e18580400050500e5074030015a082512032034480240c024030922803000c07611625800f40c0034020500000d82c069026400416040c0001414800380e0340c0e0b55000030b07007910920380c0d41800c207804c0808c228007016054003d1a401403000c5440126224180d404580809000003014080b042860910f005111955100502900c600ca11003034242c81c16001100c1e15602c50544480d20280400d81c7c024070342031036804203c0440c3d105c034450380480c0c907019856100488030788556034065074072007480e4001a007440040c20340364400d030307540307103120f08d0941015000000c403507501c0080c070001c06031076000074202040d0301d410340b0f41c0244001980b01001004800501c58400102d4100b07000625203049240c00c4442144111000034044c81101d03140c46407141d40b0300039200000d41000e0280b0688ac6542d06200320700f00e54080a004444031318203007010800a14142d0360041d000f50700080d66907514042d00007002c0200040d208028 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 733166025 1250 733164775 733164821
    0x40b010e030d03290f040c12090f030f0216050f0102030418060504051602060f220f05010605030313030f020102160e1005090402031b03120a020303090f0a031b08090402041206 77
    0x100f004545c0e440340c054800c690716000c1355a41402294005582e80007010104404a10340c0f80041d0610300405040d4041303446a081498400c2c800502c403400c0e4001d01380294480e5181806001002101e01380160541c0020310000c2886d10040d50f1070224880c40c0c1a002c250240b5103410f11040754000752110b10082480a40019110b4000030740079003000c100a240b801c15501c0a0074400d02c404c1d183c03030b21054450748020120a01c00b00f28040d200702400780008004040d03446040503030720311440c0d036229031120b1238480800106400c16800e40e4400c0c018015500c035144100881a01c0010b40d41210a007a40c0a8040c4400c1d1600c402e47c0c0009854281c9407203455080c1600029900c00985406410b12070ba2032240d84030548003071002200b0b8024519920b41c07242c0039080017a4490308122003240880c8107105e8410611100011840c500c150103441c1c0b40050303c0398640c1511a605415410b40300d1041c20045803a2030703215803004100030405002c030380e01d2091051a03e8006d6034004281e0f035409961007008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 733167275 1250 733166025 733166029
    0x130e030405041d06041b0306021809010f06091701060503030708120a11040306050a141303110606180916230109140f0d0605040b04021008010e06040b010e030d0329 72
    0x2c0a504542c06c0b100c0d194400e48a00c0f8241500c40703440d0001405c1c1400070130319640040e65040381c2c84044030f04507107100b020380e06c52a20240b40403d62080c0030000360003103001c10400302402e1a101303008403501e0000c240744c0d85480c0401e00d0360717001e104119621900041c0b02c48800600f03100302500102011000d02110356060a822290700440c0409003950350f46001203284003038941d010f02a0b20484140203422450180d0401076100c54210054010039000c0e920341c002c800000c905607104080060901d0040c0c4500c0000c2c800700c100041c00f5850070712914107014008114010750702c0040240078a5135018101020804098401c1028201d06021140e0000c2c0070f4821f0030f1505003082041610222010324107a4005104226480d40144c1014502000d00080c4110400654030075070007614411023000b48030600b00e540380c5c002d204082044070400007080140c80c00d41c00440700614145820100130764a100040e0134000c40c0740c607100c08241e8070000d211030750405140f103101410102880000890207200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 733168525 1250 733167275 733167283
    0x8100602061503010e0a06050a1512080a0c08190e04020c0c011404050a030f03020105090a08031b070b0a0b01080105040606020309090a06031e051005010320130e030405041d 76
    0x11242c0110282d00c107a601481c1c80035880142200743c064101c9007100f13414103007040141400d50349103203411b003001c0d1500e24110703e4070000740441d00700c003200203007000d203548801109400c211041d20401645a8403800450b0410000d400306118682d1801c044c11100000504a48500a5440d015600611079041c4001d400b054076600b104083c20700c4064100c250403040c800744119008260700180b0340c81c010041c000c0c0d140041083c10301c04c1d0000c204644a0070901559800301680040c90300c1030820010f294040080304440c0103c0048244508200c003a81e989114039104640d00ca0725503a9a444460300340d039000c8501401801c0507641000100c0c00c00e80000c1d00c0344242c02126010780302182c0402d0071244c0982c030401c01076810010303a1104032200711004c0880a61441c080c4c07121f10907801c108030420454400c483c100d81d07015203546c001c08492130006030b08410b90a40385500001a0f607110048103903d000e0a111014510042d5655a040208000c11204e00d50111412084450108410050009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 733169775 1250 733168525 733168531
    0xe120a060905010608011d0709181b0e04060c0e0a080d140d020a0207140603060901030f0311030c011e0c080601080c0d02120402040e010b0312070809150a0810060206 73
    0x240c00890740c4615030809501428070740d40145200e41c03810400780828034000d402c10000c00080702c2602d50583d0780e0040102654000e51201c12079900f40c1c850007000802c4500605001000c0a46c10204c030b6a4a00000c11006030864069502030b49640540941c0c582c08203800c070030100c080341c840e952541410201955a0700e00040c040500003031303a80e207010500046040e0355900020703140540d80e03001d80e82e000039215200c2c4e104a10300c04102ca42d4010540c6040740940384140c1d0040c266000b20380c030390307203420340a03401c49142078043c4081003a101c62044c5040c0000c2c58010219400802c240c01005100344c04000c02c8c4078a8004c0503d0421030b40c019690256070070b40c2181c02440c00a01ca1744640ba0001c02c54400e01e44403010583c40082e02d83e01d6411400f80080c400c90085904105500300c01629038280d6210048080c2d05030030a1503800301c950340035000f41a5850040d44014106a03241001c141d80c0d6444e05200c404c2e040c0049030701110350342d0120304507a005075200c0c40d02425514054000c5e5039101c010f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 733171025 1250 733169775 733169783
    0x15010c0b070c020a0308030903270105070204050a020d09111302090307060804021305041209061d27100503160f0b070f0605191109010c080f040b0f09010e120a 70
    0xb0042c6241035548100302030020310b8000b8505a60303070404941c45545c03a801800c542c0801c0710007010410f246101d20360421800300c1c06071525803070101e90703a08100c024a0000c011100c0294288003a218000192050340000c903c00c24158048080c40c00030012422400502d411246004014032001e40d05c0100368141185e035117040100041d1a644002168221aa001491001c0c071b058104024001400f500c19180502c1d80c5900300c0e2681c442c102250001c4940e14000003602146a4104050030101d8040d0000301d1070b01d034660088145040882c5a007582500d15441296074042c092180b49000c0c00303d504140b0351700460800407481c180b002034045120b803040740c550400210300c0c1c405000401410304402035101c8402c100c280741a007416101c03014120a1192a41e02d40b10086400d511984100e8448142c1610340781c6460909a980c4c41c25a4851446915241014080080c6500b1203c000d401e003103030b1302e00c466034541c101280010040b598046034588180c0d05100400012000400c00c00003250704 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 733172275 1250 733171025 733171037
    0x303110922140c09010912021008091204031104230f04061e15060206010f12141609051b0708160c080703051b01052b0203040b15010c0b07 61
    0x22003009000b86200a00c4881c1c6154100c10480d25001c440014807076000700341c03540d0b8041030700d410791030740a1411840003e4106110110302102c10380280c488640c014038040464038a2400404072a8041d04030b580100c9a2800c03101d409503c2c0e03e008d00940ca00c514980700d0002c80c44031801e4a10300250005011b150f04140c40302c010900307024241c1c01c1001d0020b42c80e45500e0940240444110003003501c000c80442d07210411102080b5507102041c0981221010040070b8151810841030f100800e007441400c4500fa155503001841c202010710410749180c19504d208903846141c190114140c4800504101c01c80c03000400c46451040e2900c01e5421250b009426036841d0403540360200c5800701e004801411090f104940080d09220020b600c806580c420025120b0036240081c0d214401402100d415001c14030500c1710000c6540c464100174090a1034181c1c0000307131950006044126030040e01c1c19999902243c2c100310501d5801751409100c030b102880c00324070038000c54440d0056124003800445c20868 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 733173525 1250 733172275 733172329
    0x60e071706090a05150709030602070b0f07030c020714010203040302150a0206010902040509070f050c0604050303090c01051305100c06021612021507050906070b0a0509010c021b1306120f03031109 86
    0x101c21f200f0300b07000d1356000c0c500310b584031017a040c50990300c00101e61400303030360a121000591462003406500a51301c039940080c2000d40c140f100f00e002c0c40540008003811480309200020240e07a40c0c4401c41d01002181540c40e640718004403000f428000140c1010b50100d00411041201e138603001c0c3c0c2950f10401a140506e50b001d00d050048800c2c5c0f043c40e81d22046403041e1740900003800004001507005000c020101d07420b65460b28019505402800140301744801e4141082020b0302303100c11052000081c0d032a01d410350001983e1004201e0300103003200407101e0307030200c1c4641c10080907074102c0100105500050000c6941c409030f54414103001090740081107400b24041141e03880c0e04064401055100b841e981e1a45880300c00d00c4018001186c421001c2e42c2084220309e0800d0011071020801c0300c84088500700b03101c03400281320743c1c460039242400381c1c142e80e0140028000c440c2c2110800c814450b18041d0047c11150900030141c660407804203102c41c070100140125540d81c0c040000e0401907081c1500c042907 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 733174775 1250 733173525 733173527
    0x31101110a030809061e2a0a181a16141b150a1e1e020609100510120f0507030c0911030c090d060e071706090a051507 52
    0x259100900e001034440e1490500c201070704040320500c61007a190480d001a07503150300706034403102006c12030040401c403480070a0300c1c44510b0600106c840c00c0980400c0202e44060322140c40c1d64810400e1030001110140340c004030302c41d170001c240000c1c4489914203014005d1445ea40c0040c1c85544000c40d003401c121000c039401c000c1071038074883d8031125820035100c4807243c02c910f0b00d407284094030585224403603000d0b00301c904240c1c0500352a0f0707510b095903400c0c20b000d004031000640301800840a0f010b00c03071414a03040c03a200d030791298507681c588154040e00060502d07003105494440400ba510360600c3c2008100301169910683c1d18044403014142c104803281681811120049480406001c40c05982408014843d43e40300e98800c9541c03c20741007055441400302c90449001c180d0b00100000e001300b00c1000c0b04c0c40c4c0031048a24050180c0c01c00102d06100c505100d103401455807120000403d0916000d071629028041694845512002303004225030680e40d0b0b5844074030101d8100400318448022440d21 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 733176025 1250 733174775 733174787
    0x816051803070e360a0b18010c0314070c021f0302120901090c0b090a0e04060f0e1605040e191e1a060103021204020913060f02120105010f0504031101 66
    0x43c40000365094560400709400120000c8820414180c440c52100c3e042824040461036410855010054a180b0b007041c4e603006283c420150640460900352040205074160070710941c20b1040f01a240000d802d50b2050085404080003042c0c20144000000e4210160f10b48415602d9520303200c0042841000072a00203800901803500d06034450307003156041001070481540601c111500820024007503030380d1a043c02d0305500c25030458a4126a4400007005007206005180d6040ba1182602085a66128220400b1544169054511a0310446800040740c1110008001030b00003502c05000c0026001d400ba6902e00070342c18003584250700c00203090309010310005980d603c6c000d04e60066550b5441d03802d10f9030f40741d00d0559607400c118106c54003149145d8060300c200c1c0d8050302e402c0109075050750360f40c0801910306070052208080d074800600c01c80001e207440c802d00d07484c4440f248005031604a118a00d20b0741e000140c0049042c800c12610303121000340c1040587d01129440210804c82126010040b182 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 733177275 1250 733176025 733176029
    0x106030e190b1e091b04020d1407090506070c0b091813151404020d030e221802150306010e150706050c031611070b07050607081605180307 61
    0x103641c884a00601c00c2000418070240105030f56081d11001c1030304031070000e40311801902c0c00700b0300ba0301003842d40024140d80700f810494184010401810030000020a500ba109039151243c0142c0c00941048038030f0350402c241001802090380e80e14180390890b5131340740b00c92046011b1703107111000c080b454940a44c0e454401407018007a81c80348140a003010520b183d10f141e1100d50856503401202c41c014444482403040780b4031881c207a040380f500c0c0d0711a9004d00c070040c5101d0380254108203142c0d0041d80542c41d007022007522642412040b0203036070842d0649100700d40c3c100403064003a031003442060b00541e0b5264000c0b0208403007908083e40e29100c00c00143c80d003072107240e440fa0f003040d58458941c2e68a01047e026083c0140140c800b8006a43c80038ac04a0840c4811643e809482c84900c03280c401070341c0304060700000685502c0855084075100c1c004003100360040d0008031680d90010f81080304069200318031a0308040311080103902105a984050100c1c01084d540340c040401f800c443c2c1206079400c00035040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 733178525 1250 733177275 733177303
    0x3121e1e0a02030c0c06160b100b0a0e01180605040303050d0609050c0705150f130c0909050f0f0105060f060304060f0c0201020307110c130b01090f09050a060501050c060106030e 78
    0x81d035180c128074040c1d220f410010714010700d8000d80b4480350940c28140700302e0300c1d03407036070750681807403204955403504da10720006801200c61201d0450041081101c1d000180703101482c80e01c40c5501d400c03110000400e0b40c0b500390004084114131103000c1041c20f4020741520305880e4581010b9440c0c0920007280d0b4010f01d8180e10070b2650604201c01d02c84c40c600640000c02c1054000d0055582c40c8144022503144a80262001e0146503132000001e440780d6042203c01804a20414405150319950000b0106407450124248c8003a00008240c0003494010007034042c001054400a11144c0340050000d680328600c0c0c440b29005240000020301000503550082d0305040191404104201c08450024001d4008035180c8000c540d066204100112001500e085059401030418181ca1a01503240b07014002d42000d0364148550b605001c1800125160f590b13001d860000350000340345c0307000a0444280c50003948054180102080160a02c2d000441c00d103041d80c08509001c6250349a43c0c1c010303807030300211003401c0c0c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 733179775 1250 733178525 733178527
    0xa1a042d0e06010305130302070b0309150411010f020f0c0f120d030b0f1e0418020a0b0c01050c160f08041806140102030a020304141c060b03121e1e 65
    0x115000d00c41c020100e000d4038003a0f030200100d0307480341c1100403041e85c04000a00503a00450742000407030b90240c015940688800252030700202c3d40345a104582c0b00aa03001c07181410030400500140d43e2143d8000c10b02d45040c4014407900c28912403a5494400d105020fa004124030043d2901c15168950194403ca9403a801c54489003040d0324010005c02542581c907103e41d8440201880382e19012022130b4414110200302d0544040b51000c04c002071a680d2203401c02e8540010001c07000d80d030b070141c4e0312008240800da510b40e600043c890507400c403500200304440786101409016081011248407192050340b000f41d0001c0310074241030181090160341d1002c0038206030008100941181034100004444405040d1940e17120700600680c0c41e4001c1000880069209110820060040d03640b00704407840d019104180a00340f660130500408201e12080d10100e444428000e5141804c104920500c11501d104c40d0529003402c007140842e1305e041e0108160100e01084242c03a190007203101c1001318418000b62 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 733181025 1250 733179775 733179779
    0x9090103080a1718010e0c1819090b041217040b04050f0601080c0906040b01140703050409180b060901033f020705091b161a04050c0a1a042d 62
    0x800030a20700003891a84d25400d0001c0d200303c00c040050300442035000103200150600032480100d10503a001000d074408440ca03080200e40140c05449140901402148408001d00e018201b10300400303003c040034007c00c034110b01c92a19000440300e00b1034105034032084c002050f80f10360402c5460440b1035402074880e4020072b400010b5480000800d40043d100580311109030741d40e01410002100ca9a41c5158040703414254220702480303030318006141e001c0c828100642040c1c2c403000d242c011100102c204510603040206980140300b441900a40e1046007103407810150341c1556203014a403002c034810140707407041c1c400b50b90706405045030340c0342c0380d2010341480f101d003013124a20025540c280da44103044c05041003402003444c1d0310085201d4001703000844001460030603855600c000c101070001c000c2e01e91002941c1155082c07040c061281e07000790f00480041c46400030402c01c0000207452607000c03200c040202c00c4080c041d11524030940d8111010004000980c009170821201042c1c48541c410611111602c80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 733182275 1250 733181025 733181041
    0x8120304020f120c01020d020102030f06061606050a0207150e12090409050a29010807050f0f0d0b100501030e0a0b041403030403050a0933140706050402030f0309090103080a17 77
    0x40c8404d040c10983c200c83c5068001101a401c03448260760b20060061480000ba1a5040c01002441c1110040d4a035034090030142d10f40a04862094421300c60868000601509100c0c40022408101c01f1480d81001012810f010f240d55a80d10300c03030030b42c040520100c2c1042482d80c0d10740c02100d03071070b8024081c0c0e03942e60080e02c2c120180b0030620301c0d1408801d541c00d10400c02102d00ca25a141178400314001007070303007038200f404000c083c0d5403469005600001c00c03440c014142e1142d44821803402d124040200d00ca0800d0240c68440d000d03290001c80c1050714000c1e00000d41c090015a001100350024000d020359102c038100200141d005d0110181309210020078442090362141c000c111084442e174410321020303200d20f540901380061054030740b45145000400700000391441c0c0c040c0f503000414240341044009076100f803010790300454400e40d02c0c990760b1820801582406c0c403000d07407500e244d60051490030621a0000d0440039042c00003403c000000324661064a010304445105440e50300003400307040c904000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 733183525 1250 733182275 733182283
    0xb0d1a060f091212160501110417280807061413060506060301420914092a07020307121109071d0a090c02060106090e0108120304020f12 60
    0x101d150052626540d01103c00750080b4080310380c850404c4a451601c55a04c1e0000c1252480f1309080e00d4956842d1b10030036240d405040108000c0070160070a00200d4064140141401c0240c51404482d041c403030f440c824900009245207034032540c09841a034440043e030605000504285c2524242d0414540034848120511250070100502c142c005100c43d0391360030203200c00740c0001e208418a0b041d50703448840e410281076050460020301701c0100c0082040000003000043d0000e80c02a001c01c40c044000d0111109100c0040f01e480b0007650b40da4128280f8807400320303030601450744005441845591501c2c024102c070701110159600102107850440d21580a1550a02d4070401100c8201c0d0900c142c0441c0d0a11494103480341c09940c03a403618404130302d20800031000244d41d034107a00c0b0380281d0300440c01e1a214810b4007150b241503401400c482d81803400c00f5180c590a901302000400d81c200c010001402c0016010700458030300c99000fa201e0f02c51348040b81c410301c90843c0f0140d12204510714441c0c440300000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 733184775 1250 733183525 733183537
    0x90819140307030203070b04031b08040f050303040b1909030c030503090a091e0c0c06020403120f050f0702041e0e011b03230601050c100504020117010b0d1a060f 71
    0x200340a6211101110351a96030710400000030003680007800164041540113101d030b40d1090082c10074580b001c2038544003000c204c402400032100c013400882c050104041408940001d41410b03001945024100f512811042c010f2687c074851640c240f41260031514454030204004680c002d0110303d9480d00c0340380c095126000040014001c0400b04030000d0784c1d18072801400d40b0341001440c2c03041c4000c2c0c2c03105c055000d40a02a0228140301c01d43e13041600050840c0300400045009202c80e1044580010700117020f80d54441001007086014018074484e50301540485680a504a400060800444204410041d0000b401d00c54030344c68800c0f40c0465400c190441d2250ac001000f41c491204058030098044401a01c0000c401c40300049880c4042c11410310341030740000341410004e00700404042010b00c1d114069500400c1142c40d64140300855821009030181412a50310070850b640c1004802c2e85240545001881d2064480250030709100010400c6112030901400c0107698207040081c5806503804a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 733186025 1250 733184775 733184783
    0xd1109070507030804020f120a0804030203120304050601090e0a02060712020607030e070920071a090a0b070f0917210702010c0213060e01171c0207060f090819 70
    0x41400034041500c998100d40c40c66616803203043c07441e1580d07028080e80b1035020407031540180c3c1c0d51086c500c0c1544100b0450f5120361007400c0265640c0c0c03d603c10b240c20b0441603180742541560074001d200c002207002c185281500e0040c00e000401115501f00103141012502010f508100d0000302c1c8014812400f404110090b099001c130754050715040e101700c0131110f00e02c98405082d040f030700c4213101400244c3c1200300003c1c4050300038603888419070110002c92340709000c101c50b0010a011303200308990020000e19400b44500d00504406a130b580c80e83c0e00c00c800c00070420f00401168131441202280203d1400d005400c0a880c4c003150b0b40a004150ba03a030741240d001e0720031048400303181414064621412200c020340d041c1e42d20025041e1079401e0143d081c000746803880f200703903e070740c00414110760000360f050003010809008050803480c00c040d982003685a07640300c200d00714064912034525400241c1403088070003500d002a11110702040866220056801442041c0294020568846c80c041903000029001d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 733187275 1250 733186025 733186039
    0x19030b0c071211100e010f0216020a0b0a09031e120905040e01020f1e0409141b09030a12170a0606020f0d0905061e0a0201091407180203040309050d11 66
    0x85900543e0a41407070505920b803603108000001410025030015415040d100002144030b0941121920507600450f022552540a41003c0020b500e40004824014518050564500060308400802d81a0b480c003002c0c0040c040c1c0718109050761b002d03105980c041a0481c0100c4007400c071003031000301071100d54440c083c4264113014a56100c0e90061007103ea4020070101380600e0141412080d841031940014041000c07a42404001401f40450082a03000404000581000c0c03405034580c050442218440144010342400300b000c0390740340017480814054014400055244401c00c00b11801450328000c00510f1903003506101c1c018001c1c0e000b000c1900c4440c0c090b102c0604c002d22610307640f04164000d1600145d20003504200e45c3c18007200a226030341080c45c40c220355030036420850041e503010500c0000183e5440a0140a100c0381081c02d100c00141c0d2401741100c40c0c54041e01441d10b501406000f4019035001010034201070240505000406000c1c3c11054508400d003010403038503100601080c01004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 733188525 1250 733187275 733187303
    0xb0309011d0c06030f0a15170706030203040b06040b2107030507120309060c06090209130209010e0105031b030a02042307170c16080318010f020c03030619030b0c07 72
    0x14080340c2c2c2008203102400003811640c0e0031103c00750740140a03018074805559111040303004584849440054004d810145d0302d203084a1941c0307443c1000681c0f05004040c8103205200025180c1c15a55030088800c803400300f03810f4601000140510031404c13015480014041c02d4944812020513003904580c0924142d44106681e943c005100386d250200090004048040502500e405050140c00040c02802d00240c81c129a80c08940030030f400389c0d0300f0b10640314041c000b0344c1140b800107405400f428141803051001d500d88408683d0350100210300451212100c000c0706425241006100c640e250010f100b441214005018220381c5259507540e07807100d41e40303400000c0c420343c050000a80c00c980009441000d640d03440328129250780048000e0f400145400079840017254100c1c01442c01031000c400c03a41c001d4a8a24091401c413005042c005043c035005000b41c682044c030110541c0d62084007900c1248644400b81001040d840d07458200800f4200d9003010b001e00505080c2c09041910310845454004407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 733189775 1250 733188525 733188581
    0x1030b041104271104031b0305010f020909060d1709011b0303020304050d020319080903071515120807020f030316120e030a0f06111b0c030601061b0b07090b030901 72
    0x13107003594194500041000b0400025075800740c008100b94415444001c6e0544030354800d030940c0c03042c0c18098107450b0007152140c020b1510030080c64011b23508598100d1045c101d581d03400c02d102054a4400141080031504110030390054103c200508008040a8400d003e14a03000e4001c0d0070a95040d1010721802c4d00e003100c9035000200729581401d0000c0084948000c461003161030300001071520380140418800c1d4000200204d91582c21090107000100341543d90103880302e03041c0381540c003074226000d140c000000859294000c9458842d0103070b5506030350440a0000c646984100401a000340c070209507000300740304074482441d624050307c2d581c2c039400310480c1c02003590710403002c03c0c003a000040540c05080000d00c0759203c200304c5000411310b80d0400b00d950420306810700200700400303015040701845406a107014084580540180e0130300d208405000b04080003000c003104002090800c44802250480380546585402002080012540c3e450504080b601a0000d401c90080704c040200984001e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 733191025 1250 733189775 733189781
    0x30103030801061b0b130b0f1503012003090a02030d030903031506020d030e0708070e1b130614070c27021824070b090705010c030e01030b04110427 65
    0x9500c250500b13584859450702c0f00000480054124480c8a01d0740451038001408020807500c241151910154545030071005441d41007400c0c15920b110341d251551071200480b01050012080800075a4140c0b6665500c2c52540b07041030040c0c010b58148180c89400821990603000340302018800c0c1d400303120300c0d60081d48101c21082c1d42d00405025822070016114207078030070b5118603d02035a41040780c0a156541c01100d08060a0b90404c2400140b10410455000b841e42c04950000b00f84282c010b180220220b10403890800c01d01a030010404ca489425041440390030542d06c1640d000410380403d299640c0c2d01c3c07144109044510240c44a40300d1011546030124800e4654200d42e4141c0581f41c0c10502c000c005c222404075a00548844d001c05454410146000190011510a10800322682403101120b4580480c40d0301407810403645d50406400079501441d010043e5030282000b00c2c003008000c0004e000342030722481c2136600382c001080014089000e81018040340c0780e0140c40e400445c40b00405402a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 733192275 1250 733191025 733191047
    0x90302060306010806041b230304020d0b040507080303070309021011100f1d060624040506210c0a110106052b051501030b15130e0309041103010303080106 68
    0x480340c01800001c00b00c0d400b070606654081c0c070040c4009619802201d8004011207a200c2510004002980082c0b898035008071035903929051804250640c80c00b0b90000d5049004200010001d1780c041e0f0108040160401180c00589001d0342074a0b00c03444d00381e030014010150b2500992141d030841c0b030360624150080010810904480d4094641400c2c1e200700640600400075110003416a00e900540340321341245803071408110340394080c040c4c4d810944c1c1045505040300502056401c441800300c0400d842c9081100d00700d40081d510207445055403d508101030711070040c001c46030360800040168010900c0001d0071100c4464940659a4004400540c22601180a01a0455080f020750546410301102c80703a5651030b2841c801b00d18204544d100c9040074500c01c1742e00700c1d00d0300e032800503c100142096420361010039400c1e11140d000784900090003403919a5041c1404660300c014102c2c013890248101d5940c01d4004d04144100006903240c1c5900da40309200c00e030b000030001400410410300ca0744010301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 733193525 1250 733192275 733192279
    0x3040b0c0307411c0908160b060310020a1407111305010306050c030c071b260d020d090303050307210b0102480301110d060501090302 59
    0x411035984011840e61540050700e84020b10201d0100d51501c41490070600585005001c0750011020103880403107221118001c095040f00014050300305004048a14140b20030440c80003c5002501401e2035906032140c1401c809512441383c0b1000184036031000441d01811041c2c9c11142c0d00c0c068a08104101c2c0030f44200400007540c14640e5140c002c007204040d02110b130282c1030450000105400048075401ca44104404013900c9170010401e00c0414460f17142e0026040680d580b95150210f03544072944a41d8000800c441c42140b0300c5c0c0300d20300e01291008094070190042408128101c00f0700d00c0a00d9440400d21014401e0502c40c0001610225910b40001031070385500c109281155001c0ea101c0d007000301000c007004140414035840c051850401c00050b1200074001400902c0c0c80002810407403900c40070103014011642aa0001c1420700d903000d100b071390801500304200f000400007410307120201c810395419030814a2000c0301d02011001040000c6c503000041200d103648000542d56110b051001035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 733194775 1250 733193525 733193543
    0x40204021605011d06060f190b0c07091a060a110a02040509011a15041a1c0b1e01080a020a09080f0c030613020d11010c17041511030405041d03072001050304 69
    0x64200e0800398100c0d5240c81423400483c20460700c1d1041c0070007036040100820f82e103074004041040340400520441200c18209401c81113007844803408034010344600c00f8404100254525201d0b24010140b120f040c4560b4020428030844c2841c0744000c1c06018844207807540401d051074460360a1502c0c81e04840e0580c60142c82a06051810070381e8041d020790080c0e01050796170200002c04c012400c030740c80079248011940c00001d6a81001080c85202101918a0b122004264698071442c1c0e03006509a40e00100281c00982e0398036644000300c604180366840642c0c03a206031b684206807504041550b0122a600b0340849485995a84100a8148950740042d400034450981c1720040b8050004400303130b509060405200714101a0382d041c0d801c01002c81440c3c10b050000c42c0a02000e0003040b02c460403074a103803034100380071040c0f0b0403070540301c0c45144200e5114030754a00900d601d411202c07031074402d07460310700040c7d07510746031103080801052403c50107807203050034941014101036014074141d074000c0360052064 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 733196025 1250 733194775 733194799
    0x7110f0f1b0307030215071401091506170604020f040905120d050c03040308061306031208041101020a05070504020304060605061b0d0c050d0f02162607060c0b040204021605011d0606 80
    0x106c2c009a000328000c0d1003100032030700b001c0d03c0c050b024007841c0c40d05485600110440c800540031042100c403242c220103501440300d03a400c260302c0c2c03000036016081601140ca9441a0390f0700f40004004008208009003980603c80b2450408507080014103142d0a003002e040c816981c1d54803401004e8441124010081900000070811901344035102d83e100040d904000200c083d20b0b901c4082c41030034402c1810f0001443c0e4401c00003045240411011201020300081032080d05035500c0b103403508010301415000300c1c2c0c0400000d0a009094204a00410003d00142d0741c070b10608a6941c504014007203008868418030203010b0707001d40300d15102203849410001031720102e84c1010301201d207a26480462401c40c46102100402107a60000840040150340010041d035410042c101031110b500840b0450107400000040001a0b001260b625146501075103c242c3c6944500c0094000c3c0500070710b003115402c0c07445c100400c01c181540614401c3c4503120004241390f8103902415568241281e22581048a14020b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 733197275 1250 733196025 733196059
    0x804032706110d0f09230a03050307051b0f150910050a080c03070509100903060c0f09120812070504030f080403030806040b0f0f03150f070f020106060807110f0f1b03070302 76
    0x90a8210004121b099402c2403a4001107440c0078542080e43d09030030009070301040210070008808800740800c5800ca1000c5000b0008e2140c11320708002d00d02506030340786020b0500300e0040440342e400200800c20050300c44000b07401803150300f0010000c00800d030b048002c160800508001d591080500381d4409203414208010311aa10345c5210310309050007881c540100c0060341d079004041c071843c2c03d6078070488040900000100074544643c441c01d2481c01d10b0f48041c022440035804c0303030b6541c070150322140b4090311008804c40312807080f944050545005000030104020080c0010b00840e4000d81c1d4103802902d42c101003008035140350303000940c000e5616800c00b80604000c09612040308005003590740c915040d0408117401c0300112008440b65001e031042281071504000e6000340904144000c2000b9030030064003601e0321201400002c2885003010f122030070000304000340034001500c0b40039603d4100c0c403603041c0daa4608441811040540c42c403c00e001c41800c0021703040084980040c1804088060203030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 733198525 1250 733197275 733197299
    0x7170f1905032b060f0803090f010c1202100605030303090c0f0a2304061205030a1b060c1e03110415090b1305031506010804032706110d0f09 62
    0x108803003500050141e0f0442c0c03080c3c0440340128401e40000100040c0800704884111946034000031039261030380703030288440a0004295400c003141690f000004966103401a50001300420700101100c240d14600b0130540c0d40480d8584a142040b8010b01481d5260010542c9034001111011840d03400014000b041d41390400d07092002880182050249075203520402c001c4050a074100e2800c80300d90050035044d41000d100c0c80008195450603001e5002c4150b07560b540320721500c00003008001101140900d018940c030b2010b00076551100c02041b803c601c0d200301504031507038180242c140e8592001890241d43c000e000700030b003440400740ca5602d00350611000881c143d105d411104104404d10340040380c00181c100041541b200040400017240d4509010145408280043c000d000707032685003441401c1e40c003e042c05400550505040c00c80158460200c21648010740b0a10051420356400080d10364029504421000c0c8003420365a29603050041178074641003090008000900c031002c10469905091 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 733199775 1250 733198525 733198573
    0x280f08041401120e1f020c01020403031e03090b0118020906031e06120703031808160e01210f050c09011e09020a080c0703050f07060b0f040e0d0f05090d0507170f 71
    0x17030070050070302c0208030b00e06003203070007580049020503e40d000081c0070120310345c42502c10103904c0ca0240031840280c0d81c0d115403d20103110b074843ea540501c5900e40525441d405440c1c2c0c90300d000d09903680700d1400b074a00c0540d0a40c44000200703100302030400300f611801c0c804900072088042000502031700b443c50340c0445070314440c415224188034004d91301149045080c003884000e60500e00d88240001c3c24400414114003041e0306c00c40428011038045041c801e024245c000e40300d034000007003002c440000c0c10f01500b840c400154655201207043c00201c2c4001e907003158001403541d0300303e08042c5191103022450803845046011400f042c412800640700000c1040200485807082c40c05601b012004c8100207072a420041084600310348904400d03481e400d210100d1b002c8508101c0703052010b50082611183c80301603480510040204114615600c0360290003228690309000c0d144880d4002c00e410842d031161818012015940403402801c1018400000c40c0f101c5080c01d030024180e1104004c0803581c94000034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 733201025 1250 733199775 733199833
    0x31a07270503120c060108010b0f01030b130f050106020f060906041101050f0309011e14010e0a0605031f0c170c03040c35280f08041401120e 62
    0x2805001c240d64505002c07004407a040743d2441ca8407880918481410100141c0101003d41e00d483c540f0803840d511074480302d1980c6c0702070030f001800381021404204c9250b084107480c103040e8202411010605101c3d80098100d44440d420b643c004546248045d450701410317100d001c001d5100b2000b2070003081c04102c0e405000841410003d1400c0401344495135103401c103c404940036595400800003040200b0352115030386140c0c1078200100382065005a01e5804117004020480786814001041082e4a51044014010090454a0100000403000c0301c8500c0000000c5811b0300308040401d0702c901482903010860755407c16400c140c0d48481c1c1d41406600002d10a81d000958100001000e5110483d6000020b10100288440e10b07107010304200081d160420030311103640325081c0b035080800c0590ba01000381900c0300b202d840342c28081c24034299103011010b0141c03940c0c00011300050301c88107006042c1544402a2103814501d00801365080c01c447c65a41840e00c1c41d002041071501ca9451400f44241e0b070801 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 733202275 1250 733201025 733201097
    0x100606020d050f18100507030306050f010804140712080d060605040509010b0d1506020f0c060a05040e0a060b220803030f040303090f06150f0b03090307080a0c020d0c031a07 76
    0x52500050032a44050317041c003010907400191042810b0381401000003a250a403460300e1050075800000301507040c02040642803a00240301640d60030010300805004190000c1500003207801410b180d010380d44030070203035645503240c001c0001d42d0031302600954007240c0c801072001407a6840d10f1090300195004a45207003d450362501c040400d400050725000140032164010201083d40c0f40509182141411140f4813901c0107103c621021540720b8100c0341035540b606001e0059480352101f0a02400c420380003620f941d0f030082040800109652551016070a2007140c100f00e1680d02d031085c6440317102c03c2c0c60541c242500800020007103406034110032040b520400504400c10015101d12086440c60355020707020f100c03241c004116102c85c01a601014014500c1c0140c514104105119030303034072512800800000c03000c5541c1300480c1c000c070300300452103801400c10941d204541ca0020a5110b0038081214455001ca5603480f42c041031031840d030700c601060307200d0702a409411103603119124404081020160700e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 733203525 1250 733202275 733202317
    0x90408040b040e010620100b21150a0c020a02040b0609180105132a02120d02040906060234090923060f0402130b0d05100606020d050f 59
    0x8184004000810340f006508042c2d506000000b01540e00c4996859400c581d0044140d1100d10085002d91300610181c2e000141c40c00114041111040c4000c5564460640001c107034140c8040400d14495024008140308090f43d20002e00801312202d5030501401a40705008200040c1050780c410000404001c00ca50306001d2980300181d805c2c11a00142641004100010001418040e01808107070b0300445050081800304d02c0e07002281a140d0700d00604043c8000441081d09000340444080310103042001960740c03004100e070a0103940603104902060745452400214188041000c0c401c0311000e800780201000041940c48074600b51041441c818945094000f5402262b1711401e20f0142c03191860442d14050134410f4240c20034072190351700e01c90300103a0405c5419034086c2c105c02c1e0701540c1151040b07a4040501c8800c2c0c01090303501c4506400121142c005400c0c84000600d40601001c40b02042c040300b5240c50049846840304111500450010b009903500710700000d01902080000d1360b135890b1462 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 733204775 1250 733203525 733203539
    0x9031920100902041107080904090f021e03060117030d09030e031020030f0a090f0c030f140102041a0f070204110415020a11040c0215090d0e090403020a0209040804 72
    0x80d000320003201046603140748030b104504050003a210b0094826100508040107504daa90180c4240200d00c1e10613540c2d100c0d80e40130060102028460150060900d00182d58145404540c3c0c0388444000c521900c1030400006c4c250700c03108031440900b04c40d40081e508205811380580094078150f0b03000c078180301000e4411402910204400704408003054804120740902c11401c140081000d8561800079200708204804111903501281d040724580b80001100e013502c0c02c0242d05403801450007060040126400000c2c008045081c200c414000c2080d1442c5a0410b09503600f00c2c8075030720603a00d10700101d0446190200240c0c001d451501141d088144c030f40311495001a08941b6001e0500c144082d0210f418080103901044a080100143c0002c003003080d002d4503158058038255180350310881c3c0796258503079500e00c00d2003060000240f142590945042110000d40c641603081130000000d4840c2c0d409114030b02d002c0c03030150b000d07076015006480a0000b40d000e02115a0009006545000701000001049 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 733206025 1250 733204775 733204783
    0x6070b190f0204140d0809060a0306030c0303050301030b09011a1909111c060f12141005090d0c1e03050f1c060b07170a111c030509031920 61
    0x1110700c0300d200580c1c0e6414902984015040000118001c0c00c01c10300d0000005c016104440d4510002c0f604151070b01c4600204030050f02c1740f40c2006141c12030706800007003096005800b4506a0b440382c440da1074160349024000f401c84400141035040401b042c2090b43c041d05189c0b10200410100307002c40d511854584400005685a00421a10190b0001050410f84601055003a004150310b0f4003404031034500001b4541c407880e140a5500c400640945000411150030080f40c800300254090b102d00000c1c10140e440141400c99941c1703154011f0586005030300d4070034034040401e903521800340b02c091081055404004031100a0032024090100404035030750901c080900015032014001c41e604041c03880042d415a1065803110000d058184110000100d03001403c0014220303040d03c0c00d44032441c21204442d11740d006881072005010351000c95007404814011300040b040c1d151024050341c0c1b2055030180d544d02c10301c000040130078401040f01c85080c1c440c00c00444d40300580318500d4001400c0f04012130070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 733207275 1250 733206025 733206041
    0xf041203050c070605100503062404230708190e0303010308090a1725060507120315170d050903030d090204110d1b0908070308090a0e0f07030f0b06070b19 68
    0x90260f04d00811842c41c081088542c8452b00405001854200c3c00013955541805000076110701d4a45200c152111060607800500c6da455804412071402d0103000500f01c844269065140303c011f8020007645622640607500da00000d1038003c5145078030350740314039405800441e2035681c45030520340000f4100030a54146407140643c040079040a612103140031501810003400810640a400c0040081a0300403054aa031182c0103418002a07190000c412001040b04005043c02c41020100c040350b002e00d410b011403015021407085503407011400206035168080c03210100d078960700c1001040e0041c0c5030394011070a158170141c4042a60000d00e0a180c4450b0054840329a1460340d4241e038908200491405400701078586c1002d9100a0502290329105c01d07142c00042c0c04c060001a2185960701c60350580d80007003503e8a014981410482e41c4030841f56801c1d2940000241083c4016484840314826110072110081405241c40e00c540e8800e480b5010050031031a00380200403000240707000d20301407062 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 733208525 1250 733207275 733207291
    0xc030501020403210e09071115130203100203060f0d05010905010903030209030d03050103050c280603060f060504050906040b01030e060c04050a0e040803010e0c07050708010906050f041203050c070605 88
    0x8500d40864104c5a8407003c0c80c4851020400c1075402030105031901c0707440e5070700b0501c10316141d0700202d09080424036007900f410707100c124402c5220810141080300303400000014030803000e035100f051504402d0000e1340000d9504c0355014030541201c4245140c081c59041b0010703c501c00105400e8600e45445003100c0c003200064012a400081001d40307450103208150402d401030804214070350540d142d20b03946d010080d00250213014801104001580e01e01003800c054002c17107000030303401510303080c008015003540c1c0309000109040c410080380040c010f1003500c0941e107010300140d101d90703508401c000141a4504000b818141e48503507a04010f40300380310b5284036955050364603a440d0315020034010451204c0c0c3c401039050f4244010f00c400030300c24801316411552a0540d0341c3c1c0d103407642e040d8900244034070f80e00182103120744403000442800c1034000141ca180110300030485030756240710301d840000d412032f0001c00211404000000c000e01a500c091b40010102d00e2850800c289a0380303082c00c95000303680c203207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 733209775 1250 733208525 733208543
    0x130507090219090801050403021005150a080309030d080919060603020910150e01020a06270c061407021f0207180509060901090f060504020619170c0f09010c0c030501020403 76
    0x82e52900105207200410342080200b02d94a45901c009480f10144145240e0030354072040441c461250f115540c02d9011790040c20902c0003940c46086d69900e80c4504600343c0240141005c56034464018013203248107440c1200545190400001500c4203587c8078401203501c107540d0800800540c030307a5100c1d2440b0b504001c003514416800c0502501c4000f03a1002c22100b0400f605501c08080d0b42e01140c12490380e84d00443c0030a0305a4920030145c4a4464800994000200d00180909028075003e4241c112591030300c80c01409800484059194403820f100a5003240190418a6007000c04113607058543e45184151a00b40fa01c841411340d09201c0d0205450100f0703182e005201030800b00b48007035504801504001c000e1580d840d80c0d1036060300e10081000d0200c82c0e44070000b50035903d5100c1181c04083c41c0c100d514140c2000850050300e4981404038041f00c14864200080c001c041c0681114820840503104c00e0509003240011a202c01030641b049030030506050700000003a40c00d0019101640c49202e0b55 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 733211025 1250 733209775 733209817
    0xc05030702010e0712020603090a0b07050d0c1806050c070b19020c04061412030412080714060907170106180b03240703020d0902100e100302121305070902 68
    0x74251083c00f50002e085410100c0104a00024081c0070342200341c1c169022501c039a58207031340d10300f804c1d503800c000351469501e032040003d125880380c01007030307001e942d440c0801c07024903e03442c2101c2051001c010040703001560324051200304d01070030103014020791100403102c030a80c880c1070101441d089003c0420a40c0c860318119441c0c540c0601480e41c4008050b1010403002e40340502c00f0340300e640742d620100e0003514071070032450242c8410320450b00a010202402078103080c0510b041c02c5c85a200c41c40c01c3e68920010b8044200b144408100359004012640042c40481c3c204200c5a00301290b5040c1040c0035940c0d0b9500003414038034601da045c0e1080f0030340703000502420280140340c01c1c150b2500281544000c21310070f951040000420158000c010380c82c0060315000200500d200510388454040d6101c0004024928901da0200b80e0a000503c10388001502d1147c3e000207038264050350640780c8000c80000002064480b900070304401003070080040b1103640c1d5440000c0390481c0c1c4582c1103104c584040c0810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 733212275 1250 733211025 733211027
    0x30c0d0f141305010e0109120305072003060a021602030a0c03050c0d0c090b22150b0f040e1b0d0e0601230130050f06040504020108150a090c050307 65
    0x21007441c07004006440c5203005801803070b0360048201405842d06000d0a64001d9515034841e100c40f401400301c0b81e4220341c0900b03140c20701030070716006494101c8420740000e518004ca045102859000590054002c01864031038020b090003a4100301b003d00d01c9031104021201c00740c1d504104500f0340a01030403d0840150845c01d2060420326003018140c054250354000c00e00013801031b00d50f4400c55507414030001e559541c2e20002152903151801610718130910380041503d0340f00551020600e8040c444c102c60b400b5580b8400e9407514003a05c0c0381105c4001050104101509030903a1140c0d21000f604074220202c0101408c03e4440d07040302003400080c0b55031300049690880300b00821409004516802c0c51024681c03814061014002560b07603042045403906071021807d212040c804411444004d10141182150148000d000c202c600c0ca1507100c40501180545c02e16228180c003d80c1c060b5549500c9968065070802201000c00303001e90050315030900000c810f0342e00d1081c0c880e215807556034503a41c0d040c4204 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 733213525 1250 733212275 733212287
    0x50d05030714030c01140f0709030b0c0307030b09071d010e012a0605040c090605190b130b0c0309040b0603060922020301050f0711010501150c080405120307140a030905090603030c0d0f 81
    0xd070401b40106110b0510215980e542f01d590b001c0c540031603495032560341c9402100038008001809411100746414445019045445210541c1500300810200181070004442c0300008040c80c50100e018401c900e9001030b108091295294102c507401c0b400b03040c0030750710f12045030740c100d0b1b068512283c01c030428024003015003c2c80e0000c01e4101d505c8510000c200e51f140090000f144641080e03900300240c10740141d46045d210100402481120710740300c1e07042d01c44144d1244e000c032030361341d21036843c1c8000c0394451303d4540d0541c0d024860182c00c000713041d41c9202c40b040340411120950b20360000b40c2213103940140e60034081c06221f6141d81c5079000c0941440c01d8050b0820541495000b0075174142401402210100c0d403128111088914021580108500f0521010302c05e40d08000c0d0030508070442e41310711040000c0180f100c0d070f100d031456070f1003a0107806526803141c80528004001031110f000030855480c040002940140c001026a840c0c00c25044009240003c501220800318070112000c0c4241a0002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 733214775 1250 733213525 733213531
    0x10f230702030712030f0f020c0a08010e250e041518060b030f1b15070804060933090b07030206070e0a0501020a02090403050f0a05090307050d05030714030c01140f 72
    0x60072030130540019076806808680700c0d08101c810004450307110004284200802d40c1d1811000d01009509a1111410707806003141e61000d105a100c1c4220341d55401e4810540019104440105003c1c4a410310a401005001c050802d0302c0340d07d40f01d00303510b4458486108a03075030700d2070454801d1405c040cd4505003040e280310250306403080c2c1002c00700310040f020114000c000c2401c440c2503030200740082400105882c000300c0f581c0360b2071680400e6001c00c00040c140107001381c45541c2c6600d552503940f007103443e0190760140403620b01c035404500d80c1014003030150802c141c041d5480c00c3c1540c01603201d4080706266003090b030054006900c0355091051207504000c4d140044030003a1014a0907908100010f591003a81c071100901420007407000a0a1510601c1955460004090b0040d62400150001009900039943d443e2080c011080700040d20314004800ea44080d0340580618100a5983c44101c101540180c52400c00e0004200c42403410340c0c207208448550061602c6842c890400c0940100c61140c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 733216025 1250 733214775 733214789
    0x70e1602060a0c0804111c03030e01050906010f06110a02150901080105060301051804060209030303160909052814010b0703080a0b0102120304060f050403090303030e0d0905010f2307020307 83
    0x1180c501e40000358001949a8002c0d0400d00c0405180114008070302600d281d086001d1f4540c00c00003004007090f41c140c01803e45010344e90004d210750b840b0202119118803081c800c50780740301c140c0744c820480640619018600c03a49040c0640300c802482e50049516800822111017402000081402c6c0d65070300700c8a254090301d02529824115030421002c54281800320b00480e8560f0300c0d00d000982040b415404840500c040078083d2500c0b42001d145d003a106031a240c420718049103507900c01003060300d56440b6003481000240d40f82200000728030307024040019013507058209580c803208800303e5031402007541802015515800341c0c1c0d9600c20705000708126805005911094209440c2112980c0d000498030000da04032075005d0394945441c039044c8004c1114000032402c0f181048100400d1540210f202000c40340240c03400e100d1001c6681505480325041c3c103c08011030280030050040354400c440000941c003083c01d0240440f205072440000f00000d058a40980340300c00140c40045080900a4030f004100d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 733217275 1250 733216025 733216031
    0xe011407050d0e10060b040501090911030105100e0315070f0c110f0d0f050309010f030b150f130f09111207050313061b0305060a030b01090e070e1602060a 68
    0x6a4005100b84550540c10086684408101c040300c201480700c1400000301d9034040004907a100e16001454005c0c2c4207060116402e584e00094481b440e001e034000c04022880a60b01d560700300410402400d05940e40c100402950300805065600d0400040f140020382442c038003420314101000502e130860440020040200050003035001a20b130306864101e01800b115007000e046030800105d60141c408401c05011400d480c06101c01b48003005c0018842c503402a40e91040c01c5160700300540603140460466a0811001c003012502103503004041c040c490b514207001c07440e1184104000e10412450381100d140b00306014410410f222a5115000b00c130325141601710305000c0135040076420740c00000c2150080c40301c000002119000b40300301c0740921603400b85040103002c11440103130b0b649203a4480130f107010a03e00700200b04c441c0351038144071007103c1d0b104c0c0214030141e09000380c800141c001080344403000c1c45441003300c0d01a1740c240140d80725401c94603015480c150007880c000d20f060b00103002c001c00d041c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 733218525 1250 733217275 733217281
    0x13050103050f0a03020a1112070e010806010f031e0204111201080c030114010902031003020d0b0a05060a0f17070e09060709090c08162c1f0804030809070f090e0114 72
    0x85c0201d00c1804254005904001e00d0041402141e418000584800700c540158113021031150101c4c000281600c0c84e40b0211030300c0baa04d42c034040005112030301015200391070030b10035141c14002d03040b4075900a6102600105000b8515544c605480e00714202e0401003211080060050102c2000a0701061608400902400344c50000c030b55440b003018054020305a40010004d2a844050b40d00300000310b0380580110105e4503a810300c4400b5200913240848110306140201e00940b420043d42000e541030140a0070b58036281030005c0c1c500215110030701a0502580100144249a24808911921007500582014900070701c00074018403003500181240c62520b81e14003056603210380c600ba4400c2060780d1100712440001d10940d0304d0410b60307510305111040c0030318495004114801b160342c0d8407425600554000b60101160120624806100001401c054001800300348141001da03041010340c0d06a0b144540c9482030085070600a0b0002c5c0f512540750070086503000c3d8244124504078500514240c841e007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 733219775 1250 733218525 733218527
    0x5040b062a03090916030f060308030105010f0c1202070302100206010e01140d15020d0b0a0e070c17070506060f09070225050a030c08010c0918020f0913050103050f0a03 74
    0x408012210a8466802494000004810401c882c0801001000e4494a1070b00400c0c0c084490520203421700040c5c24010701d0f8081003201d000b80710540b640001214110ba09120044038540e101034420000c00403401400b00c0410f132848116500c0000c00d034054500309041d8010f0260040e0303100c0d124011544241e00400074111061070701d9041d40e09041c118805021030100040910a41c041e016000d06455540408900e02a90041612020312501840303408400403c11040260512500302d4a01646000840e1359120324040c1c103226100320b20940049408801d01821900515811206c9510640602016150800da01c40c0c1021003120355590501e0682c4c2d0003034441d000340c01039030342c40600000c00761442d02040981d81d0103058007404005000d641c1e0706007002c1ba04aa072080254952030000c0683c0d105100f20100390940703c1c0d04140104514a001c00d0100941c00040d0b00d00c401070040c040c14070295100110f40f42c180140100100d40d42d411824250700700880c000050707a030b651002144900207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 733221025 1250 733219775 733219807
    0xb0c070c3c03061112100513020a05090d020105041211130606020c0d14010e15010807050a0b0a0c1205090f010206070f050d0b1f081617040f02060d0605040b06 70
    0x1032035000002113078040d02c0c0500d100700c0780904c442c50049100e00d041004102802e10b2a6401210001c49040142c44409a03070403089200e901c1c2c0003000188100103440c0941411005085468410b16003185080c0c0d4500e404100c107828881c003110400c0da400c0e04400585007581703580b2030720800250108002c514120001c1c5da564004101a40150500d0f4940818054000c0700300807100070f0300000340a01c2c207940d00031036180c030150901c5270380ac00681000454030510014140068a1024220075000d0342441c3c00c1e41c0c8203410003007510003003207005d00302c00001500c196000c42c00c4040644629840e403000d03c04018802c81003c8526046502c00001c20030307019800000c032000c1c034a42c4d04000303540e0b000801942018000150800750801000311207004109807003900d91460342c03402d9940c21071540f900f50b4009000102028040c0c00245962030b45060114a201403d8004d4031412190207210000ea010882075005282c2c20b401c403e0f41c45034100a02d080c11700513400c1500044402174a40341ca41c031030031402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 733222275 1250 733221025 733221029
    0x3050c0f120901031e0c0c21020a080c1c050a020c040920030708010207050a120314040210021006080106080c0603060d0618060216121b0b0c070c3c 65
    0x101030712918505c41e51050700c107024040d070190341003d001d5030b04054000b41c11070b0400101290310b084034032031030000d01d04540c911100042c55a400f030801444241c4543d1807541100c001280f40c0c2c060490808800c410000808620000301c2d151070740c0313031085848041d00700049206050f001c6c1c0d0810b84003000180b59407280f805072800078840c51080401e05d0300841d00d4030403241c00c00809580300103800024000c2c0082d00c99411407240048911981d10460105c00b80e80c180c888028441200c0340102e401032500d500e0480768200c1603c111001c5440002001013a96110351015078281d548210030b2008410602c84443e90704004e903410752840c00c0800200305407580b5070388041c00459950246d018a8440c2c01000124541c0002080d501c500c204020024182d150782000c50700f00089090901105014018400a0081101150030484802c0e1a01c1c03001030f81c010b0034903030030080400000b00000c5c00600c1240107840403451140030f032400384c2c0508465460707450207030020509070010700803102e11940c1c807102 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 733223525 1250 733222275 733222277
    0x901090c080f1302060f030103140a0b06060930210910020705060a03050603060a05010b16020a050d150e0c13020c010225021509010509040e0a0c0303050c0f120901 72
    0xb5056681414040d034280d15204000e610440014901c084034403000055810780f8018168002d0000100c50341c0e9a42d030034a191f00624003c0b149001440c0e900e0040040c0101c0d4102a00000b0398403601031148041076140600803141026001450840803000c100360741c5400001141c890300a481c1d240c0c001c200740a4484d851f88207803e9000150041d43c420700a0b68010a000740200d41c85658211025000e0b240403111075010344210f02c00205235406501445040f222440e44140c42c19000d80380141840010150590f08800900000200c9842d801c0c56088114002c00500410b50060740e59802655000c0880d04135a601006a540f034903510003121400900c9050001a0343d050100007030b602a0040540320034200303420400010754092100101440c4602c00c407540850390395000314a1807507000d1600c0c40c81c0020028017881d81c4c00d08195020404801c620001c85001980c49d94031400b20303108035001103000074000f01d59104030000801c0344844984100d8050300340001c4c40040c6c3d80c000e003d1400414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 733224775 1250 733223525 733223551
    0x30c090c04091d0f010b090103110427200a270903050a02012301260d030c110d1d04091515050103060806070c0311060103050c0901090c08 61
    0x850000c4000c048030000c040070038080c004203420038082d101d44918011103007058020300044140c500d10621506034114002012160a83d00315150104000881104213400c169690b00080004203812406168040000340400d42850705180503058580300200c1202d1440329030301d60380c6160b40c2e1840e0541c01d944400e06070071241340305070020480b8409121100c9542ca403402407854245580300004062400c020340082c000d00e1071a11001c602101d01d4038414001ca560381005105d2103944182480818035001c50061441c0c001d00e980c5418092001405408240e640911006440c0c00c800108080f006820103002d0a43c000700000c1e0000240c0c440501064521400c1c03000c441e0344035030040c800a500403101164114030504c2080040020320040346103050f50003000190b0350f100e0f000d50815641c110000d0a01c03a1103404099a607409021412424481e5800b10352040f05001c0003160b00a40c043c40040c12100d0502040c042c4501041e0070002003d8204160300b955160401e60081d005038003d0000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 733226025 1250 733224775 733224781
    0x403080601021c122405010320040b031e190c0c0807050d020105060604061d010521010e0f090d0807120c09180e10020919080d0806040209030c09 64
    0x103d08112507110240108a1541081c102c0183d02440140c81219071203402c2103007200d00c8080a0038200d84011505241c46107a40501441d48139800100c00c1d05002c00220113036007462194030307241d900280c00c001d001610110401c01c41ca2220522445141c9107260824a603080481d5040c10394000b00c0f460700d00c002c0d03c81c50b181c0f0f03c8501c2b91203440c3310160030441a64440354545440d0f0703250003005003a50010360800002c102d80e440d002d0111421a42c0301d48a102d00c10000e600d0100c88403000d03006840c18400309001244240400080c4a6424040c030a44204150b0608071520032681e0048c1c0400d881e000c00004100b1480c10014040a100140c1d08181d40556210390080f034400d01c450904070a06800c001000341c01c60303008451201603595041c000d480d4089451943c004072050181358444941c07102040d044c40c4249607005203e41c2c00c0181244130410039201f1003481040541d0b0003440c840d0f00620a035402c1d10341c41900c240d0048800c440a500e400d60100000355182ca21507851442030138400d000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 733227275 1250 733226025 733226027
    0x3030313080714030a0201050105011d090a060b0310060906021204180b150c120901170c0405030d09060201050a09020919021605070608010e0108060a230103120e180403080601 77
    0x1650b4126500407002c0600000e280c501070780343e40010714004050740c01c007400412650b00903500c00e8841491001c9001c5024180d00810094040262407030840d145e83d0744000c05c440c0c1036000103600c43e10107818500300081c58818010608040e81d4401001c54004210740004041d1800071141240d000300fa8030100d42c201009078038024483c100c102c0b58401c3c200f0484903180d661020243c0044140728091354051240176000240c1c5200d035a1300a0b0008019003442d0210b84180b80b907070ba41040c4840c503161304143d20703100400d2501001c40360308000301d0803607441042050360901840f503108403190781c10300074140d06074045044003a020346102c20801140d040300c1660381c5a9815902015801c001c40618120113040540c0ca5401c20700419001034500e0001103180200c404101d4100d030710100050800e9070751159520001c005a03040042c510320303600c6602d42c0031044101024003031405030f420a41c0c4213001c3c0300c1c054041b44401d052280601f598080750709008282944283d846509410858550381e00d041c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 733228525 1250 733227275 733227277
    0x3070e0609040f0603062c060f0907170303040b01050418021201090b01030c030b010522050c0903030a110106120309050d03110607020d14030103051f021308031806090303031308 78
    0x4154191186071130800024400c0e617401420329241d00d40d110122160080602c100c21400304900c0e4805031384043c012880c1406620813565000b802003003902c000030744602840b481484c485074161056440402400140042104071900410080b542007100c081c502c109900801d0b00300344041d1040c01d13801c10042c40c0340001c0d04031911030341e40722000704110360b101d140100c1e49070301a000580320b0780f24ac0400401e241c00e04510100300460841d169507191880300c035140c0c002c0c2100030301d42442c0c8c0c00140421840d64034104007400c40440a40c5465084034110080c2c01d086440607404001103031294444500843d421030768040640e103083e180c002c1050b44500781991841c0f000440800700f272140c441000007942c1d000c00d403118010300a0b03440c6602d01650040c2c2a52600003800060440c0c3c0218000b81d06440708401070b01544e1090240c058148254120007408400d01030788246005e8000040220510349560711440001900b1100c0909010607400480d99900005103e414840040d001e52000d00c61540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 733229775 1250 733228525 733228541
    0x61b0f030921120b0603060607060903120207060f0e03270411160c0e160804020d2906030303040314070611040303051206180703110912070e0c03070e060904 69
    0x12010002000024078540c1c243c5422140903190101010151824004aa0141c91f0007800282030040369141c400003082c901d40120180110005c20104141c25800a084014024500010f81152000750a003d68090300710000c0141c1003081201d400503a142c01c00b013600340d104c80c006400800020080b80040180100080c0700003004100a4604007600304542081d6214840c07005003103540e0301c1c1c8030042000c00e440b00d070354080003544c0e80b510340d910034542c080e409400101458140c110726150402d588120384403404d81032804042c140c0039100b101d0a01a00210203800951661509847c002c149282c0c1c3c20039041465000a07002c07061000c0d40d00119000c02160300519500c82e80e130314000d08198800024403007a4048a00000c5140c9030840c00c0e8100318000d200c407444182d0312900d040703008ac0a80d0085081d5100c0c00c0c012206142c8075410048400c0d90994010f10121b400c0c60718110405500402601c0303082020820000920360015041d0448501510a1034072001b0b07040004002c0c0c4106 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 733231025 1250 733229775 733229813
    0x280917160803010902220f0e04060209040905030c0d0806100e1201021c05090c010207151403090106080609060124120c0806040608160302120f0a0807061b0f0309 71
    0xb0002280310b070303101c0c1d008028614258216201502e51705a101c0019040b5100d1303031b0044075258804002d1189004041a407040c4a520b0051130081c1403030005040307444900d13044c4c40302c2d480440c0030a0206070800c02e1103940010390400e10014580701c0000b4000c84004403101081105444001e042c41e00c03520380300c002500600c0c00039521906c4840c0000c805c0c150402d070210603181000c000c0750581d20089036510f51000d0680c050182c0030308005401c41203e45014641080101d044400d21001c14500040c40c001e41ca91030002c00c1d00340c60100d5003032400001503d88940fa070880e40042105d400b580e61081d5a01d4002c013180c1140e090040416074500130080344c189030050031301c80c0c04010543e021f00558802c40c0100c0d010406079031200d200170703550000c070011310125840410051000d40350040d0f0039000a01400200d840d48400090040e00300050498225100071010580000f0842c0700e000c1c080100142d19800110700d07500a400070180700d00e050784001030542d82d14240c402d00246141146001d002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 733232275 1250 733231025 733231027
    0xa030b041101140702090403030e070b070b060a0f15030509011508010e0706030c020c010e060c0712060501140f0603130203060711010509010e07150c0501052809171608 74
    0x24180301c03126010001000e40019505040b000d070310b040e1081a10003854000c0c100120030740e2075603810340c0202540c08103200c0b20700c1521000556202044010810903100d0002100d55081c45020b0160607062038005904402249106004850000c607082d814484030f4503000c02d4035150614400e0040c4112a106e048030f850300c08001c42c42080c15001100d2030a03088048a44456507404103c0c112203a40f04010016008000000a55885180d1004003200001d103d03034030340340c3c0f25002d00303190160382e6200c154480c05055154082c807005100c1c00c0e00526040700300f01150100704002034260100840218841d001c04000300e10386044000001240590140c00c96040703007171070780d0098425541641c20481c650b007010000748007a05c06004909210b00801300070402c0301d091041a4100c00c00781c2c11080c0030406040c0c030b400046582401307400d000f1502d860002c1d901c05050030481213400c034080d401c2d155240c240b41c88080020f141c18a07458262440e8240c06444205060900c8410010b180c805058040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 733233525 1250 733232275 733232281
    0x30402032a06040906080d0e032109100806010816022a030115081b0a15022416180603020d180b09010e06010f0e0403050408010911030f21090a030b 65
    0xd03a00040940c1d02ca1b108450207031004940407152010400050303074161704a01c122940c421a40900d03490f42d031480030002401c11f03545502180c00003040d8a602c0d800940e002e01841a00e503004038000b90045c005c60185200b032004808080e40da00c0010001945607414500f50a000816010311100c1503107000b4000e01003101d040d401c13140c4450041c00b076060980184c084603100d241166040103135001f03001e8404140316280c0540c07810340b0048014004152300807000000244a20040122443c0b004c0302503045441c01c00000358003846480042e04000c1c0044803040500b0b141004a000e0203c480610303015a68640800d0142c010301062480070481302e0794848800f08226846168912413402040200302c10100b404156554180c00e103ea00c80b802d10101c400c2c0302e0702042c1c030b50307407948940207040141c6010390710311109007128502402900c11610150311549039280900030610b41114640084c000c1030030320100b08000c0ba0810b014000142d4002410341c4143d00d55400c1c0710011500004000090700d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 733234775 1250 733233525 733233539
    0x301060818101a040221130203030a03061509141002030d1e0b18130606050d120f09083a050301030c05040c0c0209060a2d0803030402032a0604 63
    0xfa00003280900c0b44050014600e09050500c280d03488209603a004520300304000a480c05450800f0b40400001c108021009000d030b28200b00400c810704040e0f6001031002c2c5407218201402070200c140108200940d1403c05c12400d0030210090319000c11140184806001401a072443c4200303080d02c440070741014480703c10381c0300f000c981c4111408480810300100003100d007000404c9050381c064599030b5034200003050001035500c0e10b802000380302c1d41000035000d4032003000914800715110100d8204c1182d8600702180e9a105199846032030f02810040c1c4208e042a6506450340c0000c181403403c0040542e482400c003400c250b982041850007800205038a110304402011940240429100003981d9440052903040c14410440c01c90826582c550010045908010b100480540015480840c1c40720104845c000d0f01109004100079841e40c924001180703640881045255001e600310750801e104010140e14082140f0344403403480c81001c2c2626101c1801c8031005002c6058554202e00003050101c0d80c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 733236025 1250 733234775 733234781
    0x50c121906090b120f0304030b040c080a080702031b030c0d0f08030a0203010303140703021222090c020c03011512080f031e0f042a1a0901030e12030106081810 70
    0x2c20507650180311048012210340e845e01e141a0300c42d110303401000104041205500100e0f0070501c901c40c00c0c0045942ea000c03051900d0740542c003d135030486000440c1c800b14a003c0008088080d4580601c04400b410140001c0e2241c0300e400a0347d014400d407080768410400c04040c004c0c0819440a100c645a0503c41c1001c00290402d0200718081103600e0105904650104103a07071006503d1340c0100140c0c28a54444104c0d50040510f1000d4000c428540c026001c410005070707405040001c4e0009050340e9079400081c504191040224084e07498400c0c1025101581d21140080c0c3d036402c1d8541c2c080346201d143c41c3c0c2003485000600310802c1800302c180603603013100e0b41c000102842c1011050407a0f40321044022218402075500605621586152828101c0103102ca0300c010300d0800000c0303031403d40d145103c1c00d5400350250660708004001a2554480da01882000c110f0480c1100a007030080040e180318060b0b100600030001403208000c00200b0340310717284a00614204801040d135442c44031280050000e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 733237275 1250 733236025 733236041
    0x103030f0c0b040b041a19180203030a120617030304112d030732062703011802010c0b100b0c01020705010e1b1c06050103050f0c04050c12190609 64
    0x803444440900c40d4400808450f800e0041c0c40ba081c0c07e100504802038154010182c0c022801c810030442c015400c05668140094860349949840c0c28407510704070b0a660088980d250804042000840001c80c100280081502c0e13000341d00c0782480c0d40ca00a500009a007000040c0c1042d803994807000011440754500940381005a01c040e4121030760b03c0d40b0380b841c4800c03104e010003454440c0021043c2405101491600c43c0c45903120162509103010303054003a54440400b03e0000c80f101210410b40c2c0f400c582002d00c40d04400902c402d204048026260b070000300303448054080980885a80f00c0822209000d01c0551002030641c00200341d500c081c506020340c082e401254042d41c641d480d1002c0d070200100d000c9010055040724460f5525900310410812800402d50350b140350380c1c000e0040d19800024210722805020f14080c50090404407a0408460f14000c81007242901481c244414400c0988040b81528440202e43c40c42c08015a502c011554014485c1c1c54100c003011700304080021000d140b5031220b04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 733238525 1250 733237275 733237283
    0x2030109140d020102030f0402011b0c0b180904030903150e010203040605061f0206061905031603020a270903051e0d110702060d0b0102030d0c03050708011205060103030f0c0b040b04 80
    0xb180640780d074007a803c031300049070503540c207417000320000d001507100d0013100100c00403c10140c0e452000d152255940c01300c040c1c201140c4c11000080c1201d102058880600e88200c0c2182c5500f0646460f550003003421520380b0005090f22000e8420340003c010b950028801105050003c646034600f40c20404080c001c2503402ca40211410341c0610b80d60450341c68a15003c030350f281c0003080c6e103480e02003c0c46406845450217205c200e420f00b0021820313a500b442010002828240858907960460040280c0000180d02605030308055009155260402d0703540c0340c8400e00301190018005c0c800381010303a814071a500c1f040c28110003100d001581428000081c0c83c2045403103100700b18641c0540b111451500c03a01101a500040a200b02d08659206030050700d00120103205a90a004519440c8019a91980c4640c80469100c074100130f14254044080350040502421183c51442c4584503907031a024107010203805c104a021040003c14090012003651550000b005038091801f8103250000e40c2e002e40b0116 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 733239775 1250 733238525 733238533
    0x20f070c08060402220e070f2c06060a0c0209100e0603010e03070b13081303150605060a030f061a0405100f020d0f0e0a09020c01240308030a090203010914 68
    0xc55801c40000303500f8401d50b80580107110b0040c0100d118242030a82c43d0441290a80740e4040c5140e0000520084004020102040710202d05100c813100c01e0345609920340440a02d445d20030041d074202160303d20340004050340c02e190390f00071841c81150400301010001e900004000b05001d840c603150207003402202d0f01c01c1c101c1c08054071031304105801d03180e4103494030f06658424050a4003081501094540040850403140351036403142d6034003c40f54111103201d50080d0384401e0200144070388101070020152500e0710821000e030034040014094021480c40320201965082c1c1d5400e0802d07a80e00103c05802480d00c3ea1007001c407250030100d0542e015000b42d0740920100107001c0202c900450421218010a8003d8840b410030110121407001c04c100b182000c02074850345100041d250100001c000d031024010140e5290400d0110b00e09580112611214020b81c062403404111001030321981079075401646207980e6200d25400701d02801007400d010358107510b042580e104010340404d00505175207800085d6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 733241025 1250 733239775 733239779
    0x3020f011104050f2b26040303080414010509010f060806010b040b070501060e0a0e0f120f0a030207050111070b01091803030c120e060105150711120f01020f070c 71
    0x59800d9514640c0300641c480d40500c01400b03180340c441072401d410320f800b901c8403003416188071045140500d00445950258030003044c1809010071002000c0c04c00c03080c107154902c050030a00d00c4034064410b1f4400581001036020124042001101c1d49400f44102a130080c012802d240440c3c0d0300a00d62038102915491429100040020010640e10b04070341040440c141002d18140302d00c080c99200301c1040340d56540e9890301194850601d15040c2c02400501030001e920040a1003082c5011049a00d02059607c034010341035078070740310504490300c80000140c042d80326560380303000750301030b0203210310042c103950034075001c52000400e0001070f008880c003403c46100f05903070b66140c00044a081101c0108000c2800c5601030100780643c1140c442500b140c42c00364912031004130b48108031007040101d00d250760030040040140d4603041021012002402c00b4451418100381e50342100d8118210f051401a14101c0143c001820103000200854107a5802551341c0c0c80d4240300f11045611080040350784806039400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 733242275 1250 733241025 733241053
    0x6010810270212030d020307051e0c1e011d1c0801030f081e120411011d0d0c1703040503010f061203080c1e0d0c0c02010c0f02030304090c0203070302 66
    0x2060750240c00c0800380c00d4807028580034480400c0d6291072800440c8020025440491032900c010b6101c0d1146984241c1c039104c040d14501c1060f8021581030000c0182030000c58081c840102d0010204081003410144103c50700c0324140c00761100d0f1002d4008a074604d290640110300100b030020801001d00104030045036141703815501e0080a00019144103c2204c0c4840021001301c01442d9419100101c80501900780103107101c542e0080b42ca0a40d480380c0c500c144410030010129503404400301b424000200704007090b10944820107200410b106458a14901c1d0a201c0452a4107002e0034005496500c07504000180d43d55952151141601961034000c1c507100400e079500c03410781564002000c08082000d00e480031215810042c0c2070748000b0604025075440303514240441c03a18081030340d03492601d0f404829080411681d400d0a800c041c01002c10030000181cbe404030300140800e90101036140782ca000b50020a1442c0039640141009500d490005104680c0000181c05118465400c0394200905144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 733243525 1250 733242275 733242311
    0x3070810050f13120315090212011406070b0c0405060c031b1f050907090f060305010b0a0e010b180a12020f04060620030d050103030305011811070b1806010810 70
    0x41c03614030500005403c4000100c0c0c00e4200100c0b0a03e52501058540c160b075a1040311040981c0416030080c5d00043d01140f136003c140e28a0300600e40000801131440e176440c0405c1440c46960002003100d40000005000e04905c03505803800f030315010304001d44031641ca080280ea80d42c0402c5a01d0083c1043c000c00055006002a03405041945503805200078414065210080d00016106000301c1c01003800c0070600403018030504082c10010000802d501d842c50610b80d0859001d521998020040c40c4000e1003051400c0020904481d9424201c5907242a0320b8144443e0505012046501100a582c002520300c2030713a405072a02c5008030350b81030781070700c04000b000101c1d840e0703110700740c0425004903003440d1520b00007140c1d403c00c0501d07009a0341b800541088050407114260400c802088d65040140044170000d85804584080e85030204071003130003404002080c0c060114020321781c0c83c20100040e410042c100c5141e4843d030440c800c994007540c40e100580d49801c072000b014112145880c00c60712100720b1401c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 733244775 1250 733243525 733243531
    0x10031410030b01091b05090f100210061403155a220b09210f0d0c0309050d030905190201080f0c1215011704110409020f03070810050f 59
    0x170341808079040c01c0c80341610207402c94400d65502101b8408402499166116000d4052403654058000c50b90203074010070407640c5c0754100c010341ca02801c0110b450743d1000945a02ea83e400158600b020780d561340501c000c0c0034812403400344c1d140d40c05400781510b1301110940429840c421081c44c1c0f100388040140c400381202c0458004410702e00d501c04a442d0070007a070041d001c480003141c0b400d160945075444d21440e4030001d40c8e4800c5242c4c0021401a5020a402c0c009240d14180309401450300306d000ca9010b0180c001e0714100301d0302e5680c0384410440c1754040c1e8010900240d1013411742e4107030400d098000d4001d001c0000c00f07a8184c09132603003000b1060911a6002039965050311804260349030b80c82050b0103901e004100d013040000070005e20307503e440302d220505d2040c4080c0c011048140c0401c0c000601404c038442c415410320f42003c00703100000754100f88181005400351000035070f20006000281c000f0812040954040c01018008078000c100400d503860205003c1d0401d001544520541c80301c054012 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 733246025 1250 733244775 733244801
    0x100807050316030605040c0c060515010203040902031f0305060a06061407080304050a020315220c14040b150915040302091b09150a020609061510031410030b0109 71
    0x800c001500300d04900c0041a50b03000510b400a56a51201c0100f400c4400d104021000b040f07a0080c2c540412030350f805119400f040040e6195580400312001030342c0c900560080c0d08846030044001ba1900360b1010034500114400402d0041069590814a4584e0002c2c0c4200d0b40c0716003048070105043d8056028488103410040603980361113010389810b09250005001103503940120207004002da034040180c203100e9030415003403850034141070300c6000c50410640000c3e0504c00344001004003040400c26003000729800c803aa19640850a4030002e8002c150880717a065001520f5160402036011050251003d650160b650b0200801c4117440d191441c02680b000a601c07078140000240c820810711310f0750f140021440c40c2d041c2003a54540026100181d024080d90400b01c0105100020b6039040129507001424000500401d04149928107060411485603c0c0501031908294203207038402ea114000d03000703070806108101d0401d2100001c42000340e00c8150340c0c2c1d02a070000491544054411b51640d5004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 733247275 1250 733246025 733246027
    0x110a02060d090501060b04090c020d170417071b09060b18060f04080a050c13020307021e070e01090b0f12030904092d050f0705010e04021e040605040510080705 70
    0x100704040d001402030034a0032181075482e10000141e20100c4009440a045038142c00300313900407107000080c905400d4080090411101c200804448130114004a82051708122640001e00c1c035440d20002d28814090001c4c20305609054035030501680d003841509480d910b881c1071004580d2160105158003c403080781600042c0e45c0035002444c580000144a8006600c104a0605540e8040641444101d4900b500c040c0c1000c0c40c118041e140000d40c2540d0038205800441c11414403020007942e801041100034030851754400c6103000014200408030040c242441c00440c10b68403240b11402404007510407500402010010780050710b040c00b051740101400d94011814080c1c00d80c00c100c0075041c07034801a0f496061341da004584400205c0d00ca40c51920020010055907102d07072510a25008003900050400d4000b0641446181e1b8410303500d203140c0004482c0541c450f504ca000c95806424507401c041c0100c0c0002400050581d080400341c822a50100d4150000003c4400f05a4401404444240c00100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 733248525 1250 733247275 733247287
    0x11e0b030c0a0c0f0507050108010b040e13021f1107060527040b0603040f0c0509010b0d02030c041e0303081537060306030c080d050a05030414030d020a110a0206 71
    0x94000c0c1c04079031418901080e02042c02c0c4c0f00c840312220310300000e80c0c40d0317006080140308950700031002038010704c2100c1d0340c00d24081c03910261200b2800e01801081c1c04010103011401990b981c10080d6121030810030381841042180c08010b0810551030011f5040d9004401001900d0350049054420b42c1b407100360b200b40c190000d41e021580c501c40300815154010343d1510440001c1e112075028512462040e00074988500860810105600031640014481d0911500511128010000340e80342d40c4580880562a03498411901046000da604903452885c0f4208114681d11401800981100e009850306515903c032814011020881c003517441d03030010a201d44481d444a1000b20014a00780407050300c1c00e641680da254010b148649520020029882d124184140180d1000c840010000b2100401001440c840b010b0300700e0050503907250038400d011000406028200d2503c0c07400d0703c844020f03250360b0b0242c4c1401ca0004d401540152000900e01c40160340c440c2000030703d800c1003a070024074140c2454 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 733249775 1250 733248525 733248541
    0x1020901260f1305010603030809062404020703050c0d02060f0f010515030603030d1406041d280803160e041509021e19110a0804120305040518011e0b03 67
    0x200c070251068540031460080f10300442c00030701c1680043d40c403a07a1411a40d08103150300e1840c1c824047c1c0000c00302608450384100c8900b44464551b40004243c40242c1c4400d031074101617406000c1d0300303c4440c41d40a0b00c5600035a2a0780400d845101e40907144000c90141c86a080801c03e0707940074000d05030044026255800d00c52034400c0a50380c0440001c1c00c4a103841140550f88013501d80000b240342156030400c080c0400e1303150a004094030740001c100610b40c034101c0b48046030303a2424500c1c13040308100c2501d600032203c4000da8071070008142d00400310581c1ea0400251a40b50480450640c0d4006155050b0b400d5080c9403a000e880e501e60f5480c070030700d95140e0074001231b03900a5018546641003a007902c001d2401800140002c0c1012110391646080d80d0071f02160f014052112420203c0c403150060554400010a5581520b044d0b804900101c44021a180b4007524a4421600038550040f628200607030310864040460b41603980211400b103803035040c5076000901c0100c6008040300341c0c5003480060040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 733251025 1250 733249775 733249801
    0xc12080d051b0706060e0603160b131208031b09030d030b010201182603010510030e0102070c09050a06051c02012d0807020c0f061602030c120102090126 67
    0x9103034a082c150103071000c45485540d5a00600b02210415180c00d001c00c4402088020507600802c25400780c41281c4c1800340701e461a00c214010030314184004201400703181d04a07502c0e98082d24030f90584034a00219824109241d401c200c40034580310858020500e10060030b082a42d0b03b040e00035005254100e040300b416000381000c0078201d4111b6507550100d0705510f8020360b05450f000c0c02130111261254401d64014801c6250364240f13541030300c04000400c016103600c900150301d54128580056811801816103000e80310315040074001100318400450840c040d54000c60041d9003a17402003100554803010b000c80820310519100850844a01d100050b500808800d500f0200c2c03503486001c22030000c06481c041217a15071400340010305a0042186080d0104100c1c81c58900403034204d4100100040091082d10074160340c5100480742d0116102152400c0003104610031008120b440d01c1e010211b0000e000390040000c49000800c0003442c100e109680700030340ea50010f414155194260746022098201c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 733252275 1250 733251025 733251031
    0x801150603050414071202030624091801060b04171507030213330206090303160e030a061505010819050c1b030702100203031009110403020303160c12080d05 69
    0x14114401035298020b14017842040042c5c143e110702c40c0c40c3c444050041c1850020000e000071200040c0b03030342521142d1101c101001c2540b07000c4800c030b04640d1752600b2031107080312424071500f465030800c140800c1944480307029200b03803142002c040c240740c1e400d03010300d41d40c8540400018030f100b0742c040041950303144603400070030210020a242004080c0e8070048c1ca42d140051445071140c040c40d555241c400d60076a154102884546071000700000d003400c100300e039101c2c031002d0400b03802c4217041032030003101e54041d5603040400321004040da51603009908000001e005100e440f000118540c12010440750f0091030702c1c5020301400b926aa07030b0144c0080320780c0000d140141c0f2441440c2000d11800c0503c901c001c4841c002d0752981070246446440314818401005150046941550010720400ca00941c041010b9011140700100100c0e11800c0000049158400d076000a505400001401e04020bc0c2174008480302030f1043c03c00c0e0107025541c02041c000002c080100410050040040021140701c5801c4960 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 733253525 1250 733252275 733252283
    0x70c0b16140921060a0b0a1a03340801150c1e0c090902040b1c2604061709060c040e06010e180402030708030903030904090f060203010308040f08011506030504 70
    0x196203c21507031a04603841d0007268640580c4000c0402c440304603203000744480f101003941d9040055041541c0140034100300034030f0080030300c000b1001414261810745060f03103144a114000c07820750111042c411200f01100da43d43c02050340e01d000001c03e604441e0443c0f0115a065a84441a04403580c501d4100f00f040d0010072002e00150002c100440c038151101002072065120020b0071041520500040c2c80b40c020034588501e03240c11200300040c290300701c82c0c00c020350301c0304c0d00007503102854903e185468080c1885240b26a40850003068081d000904512103a400c400800c81d281d82c0c11031241e42e10402180c110104a400b8030040000e61480000560425014188000095041e0000ca0034011050b06005080da4007441030006604080c0702020203000c04001440c640f00c503a601280e03681c0301e01140e203401296904a0071040c0700304401003560705a030100e02075580f56540e003083c030f00300d42150113a0407000301c040c10f000605041c14440e2820101510302c1001a02e45070107000d40c020b10004000792 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 733254775 1250 733253525 733253539
    0xf0c0203071d180a1505100b0d0f050a05040809010503250507060b0a050f06090102010f090605010302010215190c0c020301091202011404050c2106070c0b161409 71
    0x2092900921405404041030b8504805682c94681c0d00c4802e2589940a504910740010013000040780c05036a0141e1400c94100c2c012a1684407406a00f168203425800000300381404640f000c500b0608d900030782e82c010040348040c80a82c031048054000c840d41644c004042d04010820600070b540500d010b1540040080003040040340290b61030f60054400e82888000130b000000c40004000d558401c50320b1080054440240b0721f4105400718000e54a60083c0a108250201c1c0d4101c2c240e100f5004040d1007001158103010300d41e86480c1c100040c04082c0422070241c0203401103c03030540e502d030381c81c288628851100d0010280c00946010300905a10228004001005c601c420141c5ca09014414106100e0714441d41c107040340380c8000382181d200c00826004064200e060002180d4001410320140000b110301d9100032003600104075100e80120400c1c4003500480042204454020700c00d84140c2d270044000411030381e55074206400c04800d13014588045082c014290f1f000a00e41b802501030240081c1800d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 733256025 1250 733254775 733254779
    0x1050f04110d0b01151e022a0a0b04050a080a050307380a0b0f0d0624090501080120030a0b03030f0c03041502012007060f0f0f0b0306070f0c020307 65
    0x4000b2050f0242c0048907080529011042101e91100b07500100f80b8042000c1c070b201c80405900203480d0459408000d00c0040d40420b80d00640a05280d40c2c042100300801102c1b0103503480d0909206a0802e01c505440784204401c00185004c000c04d41275691507204002e1403a084032031307840500501e51603d0740d551024007005200c060a180b0240040c003a18001c0000c00d0f14a00710101c10305442505d11100c5c0140092040c0302426110765188404c40c41d400a0080b40943c039040480800b0b8202c00000301c0c0032080004005079855065001c05c0c140d4018074003e0000742544105444850f010b8245051511000c10015402000680c000c2024003001000e130791800112042d1000b5136002040407684680001038200071884c0e00001090302e64250b40005e01c41740805d60a5101c0ca145000c5030207110b001d00040460401c00749610000c45c07080340620070400c0054041010008281c0c035140c00700550710740010760210b817400241d00c6104050942e0307409032107090004120740c5900c00c22003c980510941d400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 733257275 1250 733256025 733256033
    0xf05031009110d0f0e0d03020f1e040305070b090a030615150e0a0e0f0c16050102070303020c060f090d11030f0c1c0f020d051602120105061201050f04110d 68
    0x400d00c1114940e002c2d562a540d001c1c02c10401c4070a100d02c20b480d134601d05a041782c52840c021078062001401800d0050b103d8000d80b030781e1040b82c460141d0145540309100c03412000101c00c3c034090710540e40100201c07200c8170f4658410f0265440744103c200d9020354107510820000e02542c02421000304010000e44503295150b266600150002d82070f600031407169009000c072800c00000580081c00c8a410400460408a00c940305180740a80010131100c0d0003d60804c00005803200442d406034031800841d039416460a0080c029081040c01d4a00383c02003c005c03031841000343d50690701a0b070905000e81500e0760000c0050ba03c00f003002e203a271707031071400b0902c40e0100001480001e0502608114042c1010103d1284100b404034a8030b081c0c801402041076a2261950303000441e048030381000d041c130654818840142c40380070034a01000039840b601c0c0e0400101203040642101d4000d4509854403034680032103040c40350980f00122002d69103003008000140c08140304002c2604120006820018a8602512 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 733258525 1250 733257275 733257281
    0x1b03010e070303031a010503011508040309080f06100b0a090501051804050406020406110d09140f0303070507080c0f030c100324060219021c02040204080d020106050a08010501060f05031009 83
    0x40b0680200717540e15980d28941c2c2681e944a2498002480d0841c0b4560500c06940f0390203424001d89030400089000003010035009102d485e01801000c41280d140e010303a80a00e035031f1048101c82c1307081c1c03000304a5000241c4124900c02d039a45030342a9114194001d046c80d0044929400c00c90302c0714041103c411481407a91164459207002d2030164501590340c034100740000d0041c4990b00c1300701d0b0302e960041c80030349042e40c0c0c09604541a115a031044281f810303106800140301189040310b080d818040050b1507401c00c900041d02c0002c4440a805071002d11702c2440800c5000b11022140316019007051a60300414a0a91001c415007615402c0010300141842d01c2d400d10b0510803440801c01d4116003500b0f10480c0d40400c44035161600031565000548410b84c003041c1c0b668440d801e00c107240e02041605a08550300d40e01950041c00c00c0c1412a26002c80700a40280a0100352040602034107481c10040781030310060144906075503281e2102d50f41401c00c1d500441e8035501c010601c0480c098000c50205103029180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 733259775 1250 733258525 733258529
    0x1f0303050717030712090201051209030712051903050c0c0a080d0501090501031a090109020603090d17070206132d030314040302060106120b030d2f1b03010e07 70
    0x80ea84a48942452501e68206a8000d100c1d1030074081c14400c00842907802080045400c0e90b00c40042440c00c0c0c03e1005840a025030b1401c00d0000220360100324210a0000252180d14011010070ba0030450010081c2c54500c24a5801c003003180308a004110000d000360011508602c0c0710505a00e01848032400d01d06001c1c6181c0100d0b29440c000a20751510000f6015107805007218034000c001f19455992a1180307800110706400c5e85044401c0050b800d00f030294008145190085d1076150f5915050400c161104070444d44000440e2007072318209016803203200000d1103504960000e0460b83c803807600800200c0301c0c4003030441e80e009a200c2409580c40080502c030240c85a9013518444d5109145406400e580e29640503025001d030b0704042102090740003070101c0c11180f550900364020710b40164060040c1800b03810b56501407240700c1d44071800c1030380000000405800e2400401c542ea880c1d0f4107000c02c4603160840d0b600c203540401044984a00305286a04c0303c00342c0200000f600c952407100b080e050285035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 733261025 1250 733259775 733259777
    0x2090c2808040302060c1620130e1510120f08210c0a171009050108030c0d0c0507060e040e01050f060a0501030b090a1503080315180708040b1f0303 65
    0x784040c4000c0580400102c0d42000c1e240120301d00707210741031003140314801c115a03000d800c4101c2d810b07070801c02044002c0c0405810304054911800c8442041080700507180c03c12406500d0301c140c0009182ca07050b00d50a4030700032110507465400345494040c03560781d0b13900315120070f542c0501d015802400080c4280000c0c20040000d440d20941d0000c071440703082144100500c0040c08501c10410010402c0c1d2100c62a11000740c020860b21b81034035020900c800030703210703504400141031411001180c1e00e840000a4441210740030100e8000b003c0c0c84100319503156641d40000c100740e10040b41800104d0180d007600300e000c40041c03c0003c02019010380c0d40d0030b585080d0754120318455014140046802d080c1442000b80c05c081c00c061001c991040045208544001c1c542542141e407404640c5440d100b9049003402160807800b1030b0f40364140103400d1910301c2c8200306030600c2030318410100d1a04103011006c1c3c512030b00c41519021401d544d152070301c98200d10002c02c200303202c000e0350031040642d008a0006002950007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 733262275 1250 733261025 733261037
    0x70b070e0628080115081902040803040f061403041202010b0d0303050601141c02030604060f030c060e030a0c0314010f0c05040e0c0405101b05030703111902090c28 72
    0xc0e80b00940300110004080c1802c2180315070060103040014103800701c0542007481c00c92825034982c609001000c07490117210311001c4c000200010303e02d030000041e106441301100c506030510382d900020b54403541c40c009803415041051000502165001d404d40d00c0903d0705000200f610810100000c080f401c402008a01007603403401445840c0d41c2c440410a00d080b010500395242072000d0300c10a03e03a004032b20841700b03900d0300080015020b85558000c2401008045041e00050b0b0720303881c0c03082d40390001d80100c2c400034282950407103840c940025880c2c0416004000110b801d82540c5401c0e2034030841e00303c0102c00c0c0d0f49419541081c45141d1107201903042031a55041c1d01c8604103841125031180140c001c44010005004c20702a95543c1919000c0128090515002c1d20100e0804007842c00c0c10031602a180303000100f4988249a00a906c01d180614001c054a40100060503524201c01e13003904040c1d049418200002d075400321030001401078102030000c141e40203100b01d14070b800e070030000800f040000703072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 733263525 1250 733262275 733262317
    0x10e010e0f0c0313030e090c031902071a04210f03150e0609040309030624120f140708010e0109060c081501031d191b0b070b070e06 58
    0x19220100c2a0001118600345007981450b1010320702902000d0005140b603202c0070091003c0601402e4500d081c403501800003101c5183c8a0710000d510f4200b00da0626000c0d0482e07000100a0340140b00f0ad03140701781d000080c498180321919007060380c0600180220b410804010070101c0c90565417400e80d250300029500c940018a000c0c0d001010b40c1c0c00600110404405c400d000d01140c0c60201629521150a4500f403941d0b0f910360900b01c441c84003580c80a0322451400c41403a0119140000e1310701258402c5880d801a0350360b800c050110355a000102034548425440ca00380018003640c520305c0c034400d5100c110340701140c440d0500b40c2101c0f1074400c40c84c4940c5d03481881c1341c10000c0600440c420340c20f003420070802d039281004018100d0620f800e081410903907100007030660340d540002040d5031822240d0071030352099410840010b806411007402d8810207603000c4e4030815058010020350039140115032075130603c00940e407520010701d03000d4444014011081c1c54588030392908001382c160a18001e49400b0109 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 733264775 1250 733263525 733263539
    0x14070c05040b0d0b011a0913090b0705040602060604092303090405100501090b0c0a060504080304032d140d0510030c08010b011d031e0f0705090103020d170d0203010e01 74
    0x203080c1d902c525006103203400003800880c0c40c1100042c1180c00e44000a4814510b06003c014107100b14400141d01c00d80c003411040c0040200d6110000d0584251050189902e442400f629640140e1282c41e00691000b80040d441d03007881d4100b04140c0b88601030000c40520180d14201c403e1000d01d40004040e440402c00c1011132509000d041d400c0404400d814003414104400200a0a07007400f80d40400a40044d028162103400c12032201d07040e402403001c00c41402c06261100d0a507105980035000507a02c06d092503014800150040c940300103042d0460100e83c8415401e4484090740c50402d910300c10140506d440d080310030300034170344602030005080c034600d82103103804044c001158001d80001c1c5c1c5000c1095072184d0300001c0c800b030301c80084650014500c004500091802c0850383caa0310b0035034843d1034801c00717100001802c3c100c1c07594080d0039242e40a460300140f01c421002440701941c41a9910460004a55115440f5001920101300d19107000004408076060707a100380d010f400c80c103940c00010407100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 733266025 1250 733264775 733264781
    0x60117010b060a0926060406020403050c01090806150604030501020307051e030118110c07061206090b0d0605180321090307321006030201021c02071514070c0504 71
    0x1c0c00c04942280c03c1030084a4010100851030141440c14003102d5009921000ca0321142d24117440d1000440b291450907291076001b80d0440d100848030b5210300915440e40c2d6003d90f42400c25100184014450f41e61500da082c1510701d0280d00160300640c0c20400800800c0082c0003c0d84aa0351940b00c2c0e50b5141d01e40c520090151b14580811041d010041c801441070110341124042000000000455148001280e0079030601c510000c0d154103215400000540b640c0080240000007184441000f20555518661050b291042c0c1d07090780c881c41d485040c40c0010569485590000d450885c4a420320002011061850384909460105180130301c0107003100c0e1082c40c8016520503510f41c095030400400d50396080e6540101403444080b0f01160b03442d9858880e40000207681440b400048480a8440c0c00140001385420301041e40140a071500510058440c40c40c0c10805000e19401800000e2800189104612005030181d04114101c00d14103a000d036100080c10f1254014000012240e00d0201003000f2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 733267275 1250 733266025 733266041
    0xf120405071208030f06040f0c0201050105010908070e0c07050a0f0807020a0b12190e010c1218170a031107140f010e0a0605131a07080f060622030506011701 69
    0x210180b1045402c0060700d410141ca07040441214046550340303410340080d01504030750b100035185a29003100ba10040d581504994102c64083c0c1780c002c903135912081d40c1da440702c0c0c19000e09500c12007440081581200050024044c280c0510195070000ca002c1e51140049480c0640c142d031000408118442585030204400000300300381200545000d1440c0b00c00c3c0381c3e48800415a202007641c8034449160310003540c00c02007181c0643c00003000141e003100800741c01d104040c103c0a104030300e051240210203502c03001c0c0b0010f42d9084200000d540403ca171401d601588822041c20816844e292500210000311015180e001c0c49404c100b0f107a08400b41086141c030040303030410301c141c1e0305100742c0c4000514040303a80c1610ba90040300c04921542c07811562426980e050308010941c8051600c2c0f03112001c41b500c04540140710710760704d4990a4941d1800340028820a0751901d80c048800c024440f006a211540d09669110100301401141d030360780c807010300704a001d0b4041d40242e682048101c0f080d9000f8854450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 733268525 1250 733267275 733267289
    0x140c031608012102010c0605130302010b030d09120f060f091103060403080105210604050a03080f0708061309060c030b04060f0f030320011113051f03020f0f12040507 73
    0x40d150f2605a00c5449515950700310880010b24900c00c0d419640300321151039503d508200d06122a051000100505a810b071106400551070041520b41a14010a42d40280c5500e903031843c899500b01200341c081c519160f002124100300c0840072000040c0c02e40210707564420185000582f03045a410480482d0340c0b0b203002248290060001c00000a0300010168103403a03040d034a40320480003070b200c0c044031214a118103180030b21a004c204402c001c400101b4100b2684a5595088141c8400850400c160010f40da40b074045800c03440003451906019403894054030709483c02150440003912484210740d08600b24900081c0c4840c04202c590815014034001407201120451040d403401003035020704c2515000040c00c0061304010036040410324582d1144120010008024140240036482032a5010500d181000310041000045038682110388031544085803c2184000303546082c01ca0096004608010b5024001d201ca140c050b41007030042c00365a02e8100b0b80e107600e401c041c104103140c0003865000b4a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 733269775 1250 733268525 733268537
    0x1710180308150307030512030417030f060d020d15050609070c15050603010e060c040f1a0a033611041814102c0d020309090604140c0316 60
    0x4002580000c1c40d0340d11038418440801c05001c25800a42000c180d070303102801034480c60240c1c0903c421144000c50256108000b1070740c41c503241d00825002400b04a070610301010810000480c17604204040140e8603100400d8082d4000840e41c0d2024078002c1040d0280e4080d039a8001c108541c01e281b2905a001040350818070a5090503035525001114111318130780700707540c0310404950342e503c4c25041110981c0c0c100313060b501e81e0b01d802902058217030014401c405500c480e0100c002480c00d42c01c0c248105d400c0d000d04440d07280089190b025000750540d00b000d00c15807100c015420328a591518150041400c020064802c50089404e02c0011004007003034184c440c500d40444085d5040a03240c80d20f10160744504000e0100f01c80486c0c1900701102e010000505a06104580029015101d245090807092900107800d411a071030560740d403080c1c60b03104400540d00c01c0000801520704440102d070700076402080410000500c800e401e40c000b0050b204003e440d140441031110205940b0950155001030349424 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 733271025 1250 733269775 733269821
    0x60906080d1206052101091202061927110a0b0c01050108012315040203070806041508031c0e0a0c0602070605070213020c010f060f050f060c0c040c091710 68
    0x605014940400301004a0b4283e90917070b0f0242080d0418001b10340c000c5010a281d2480407030280d150b80c0101d5070200c00c004074481507440a46e982c411038076080e0143c400e03a001c012462000340d070304c05166201900c103500b200c502011b880c0c5c2c403450054050606541c10b1503c8a101c000207a00f5680181c00851440c1d05014101d0090001c000310b0701c2d01109a02c0c4428070544500c1311810401105580700f45d0003174000410090155000b2031a907000d4079056404122441e001c080907001411540a81c4800350010010066110401c03454410b0030380c0048000292884002c440300c0c68100c600400b1501845802030411925805108035030092001d400c0030740c54419280c0c006520380388465605d56540354082071303880800c002588030f048044040c03130007006403d80340c12050400c000340c3d1160500c500500c40621031300b420f2030b0b01620100020b51000341a02e1030484100f0000c0c150f0308080342d04025000200084072941404d80c00ea140369a8406031070300d0288200a4003d41d02003440d80d10640c46d80b4102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 733272275 1250 733271025 733271029
    0xd20090a090e100b060d0f0b510c07060e10050d0203190207050a02090604020a0207120f020d030503010513110a27081e01090b07080a060906080d120605 67
    0x2801d403601000000015005004800041c030324007484c010b40c950301d451b02408211001043c1d01230708820904803210042c058201180034051754075a100b01e00b02c81c8096403484061007404481c800c40b020300307241d1080e07844412010b0883c030350001c3c6058011a40408410800a0742103e0604c0030308006841240e2100f12501003d006840783d0350402905c1540000060f580b4404800001440c5050410565035a070280c203040c2e5641603460005d034810000180481c4941ca0284229800b51078183c000d015001c0c40c2864070308210310b030144280c41450000c5d40c4c1c54010303a19488030303800291103038981a442e94185001d00c000075001405142441d403400c1e035013080210307000c000c2c3c403400ca10f580352a849494188840d072003405000c0b0110300020650600c0801c0c0080f0204611650b10110051850b0307041c0c1c45802e4034265038202c1030240c1004485000300700b00a04c141082588015100340100d8100d40c0c2303030924000c49100b603000c200c080d00460102804980c0c806e543c400507603000d60003030140ca414840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 733273381 1106 733272275 733272283
    0x30405040e011e0203070c061a1f1404121b0306020c0321040803011a091009060206070206091903090e0106030c110a03050406050d20090a090e 63
    0x50543d1014080d10a0303e20445156850901002507074031410b000b4250010074600e0480388540e458495100c001140c10b080c81c0907c0075840b9601885402013a01c04200014098100b04000800102404005980c081d9030403040660088681c84094035060206600c0146964004149042c03125000b0001c1c0143c90703207041802c1e0b242c03600000103220003541110000c0c030124080c0010300000039825a014990101e446a1f603141c45c00c1ca0f80002e00d56002c08226000150301a2000c0c404e02d0b82c14401030f83c1012090004241ca420014002500c81c44102400d031a80039280d0034100c1854802c1000360002c080d49050008256142c02009024004400803007000c5801d103000e500c0e60850002d12000d07160b4065580c1da08040c00e0840443d55944000320907201c1e039444140005201a2802d00c0c411685600c0c01050b642e0f040701003e00013111070b994084141c5074641401d0459105001c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 733093525 733273381 := by
  have h0 := BRFrame.cov_init 733093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 733093525 ≤ n) (h2 : n < 733273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
