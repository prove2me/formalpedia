-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2365
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:29:30.528981+00:00
-- url     : https://prove2.me/submissions/7c331c3d-c01a-475f-8995-742e49c0a928

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 425179856 ≤ n < 425359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 425181106 1250 425179856 425179889
    0xc0312020d09021c02010f0f0e0306070c03090e100b3901060803030c0d0c110f0303012d0504230c0a0e030a0804090b0117040606080c030d0207181103010807 69
    0x1180d801c550341a000c0c3c0801d191f11148000319125407064020300302c080c2090b0065110f620081382c5030400440319900440c4090100740d050541044840d002403446000d22142841c00c034005c689003200500c1034841c600c1000c59000d490800e80744403151844108034000c1d800d41d40082100c06500a4034000000715440c00c1408114540c000c00ac0700c0c41400c0810b00c051800d49410710200040901452170404c010070203e800b4580c20041c084da4058000350401580c0b654101070003101000c04800b8a0046011004400b0b09000ca40360004000c5039000c443c001140100440d001e881c044001180b21004040c000030040c040021202038035076503540741c2e112002d91050006241d96115505409486240248030401004189811070301458506150089210b80080c0c00d1250280094401f00ccd01203440342c0003401491410004588150021001011804045440a92208c0c460701840c10440c0049001e80320028051f0484d408800c000c2c803c8a40d01d41c0d548480380e4803007141d80150092141000707039 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 425182356 1250 425181106 425181139
    0x80d0c110a0c050f12060109150e06010e12010b03030d02130518131a0411040b0a1d09072d0e0f0105060d0902031603020108130309060c0312020d0902 66
    0x48124a03550301201c2d5080c51402e1500700040d40040752005076010148402d02e0940301000d109080c020103994101155110b0b4104446091000319040014021814802c004036a0f03448000e03900000000d641c1c407002078061403200b901410b42800341c40e0f0035200009a4207062180c503401895216421741502c40d0f0709440303104220001010052100403488048081002d0003240c9070750b28003c92051201c1080702000d0400080020f80407641642d07a078482c002616501d0920f4090302214500c1101c40c00e04460802403014441c100145401d100480c24000041e49040204070440143c99601a2542c0c40c16001410421102e4548101d083c8a15400400548032000445880c040c5000c504801075581c20310091140e5030700300c0d0f0506441c0d40d48031341020000d0b0b20705020350000301c130a440703501040600b03500015008050181900c8011003013000b040010a03803002084007510034515102642048500701140d4034485803076120750b82c80c0b000910309a060700716400039a1440c400c0d12481401c090100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 425183606 1250 425182356 425182363
    0xc050a030b030a1b05270106050a031808040302030d080402090a09021809070f0f060e010f0c06090b1e090307110604031506090b06090a1802040b1204030e03060114060a030207080d0c11 81
    0x54a0346c2c0c0300784014005204450054020700b118242e90700c2d000603040e0f0101084401c2c404071100075998264002002d006500b0f050004580400d460b042021f8503040035800304959076402441441d144d5036649441c0700315542c0c09844400c04010101c221302c50b040500c11315880304268070079802c80c0c941d2200b000848000060710001107a0070380c0c84403261000008015103041c480c88104e10100031010442c0e0001440901c900080f40e40601480d88407840d101c030306112500c0003071010a440445400c20424140d5001040b1815150b004210344215a0b498000c205280140d0700000c000c100340c480030fa00041065070107039084500054090081140c030f00c041c0500c5115054509400c0b0300d2500c0c0901844007800e9149003a44c000da0001031425079590015a90364202e6600000d140c1500c400b0300040c1503018030021a84c210407006801c03035500d03007540700610b02d00c005410b0f400b418000c208107100b0b90099042e1803075541c02c034048554580405412034010b00440c40351034041034246c540d4800461000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 425184856 1250 425183606 425183659
    0x1141305400303090c082b02031305040b040e0604050f0c1807030c1803060207020a05060f04120206070c03061e0204080c0108040f1403070c090c050a030b030a1b05 72
    0x1101d03812016925102100507103e500b905950100d00000e001929040c1007000c43c022440341c1c0180a407411030120740424442c45180e030401154000c0c401c1c500c2d0344c095401407030215003084a00084145075900400c01510303e600110742035001e280704100901074042503011520060707100342c41c0121050f80c02c00c0b00c00c10541c1e009482d2034005400080c0201c2c0a5441010300280300d0900440003200c900400d0803515040d08101d440580201d0100214108810b11b500507005c07c48000b41822a24104044103026900c24090145500e4281344259207411080700d90168100d205418000d441e4108000504110080340018101000d140640302050b0303c240e0301900c5500e40039050704040b6400440d900800540300799485603e2501c3c41001031400c070401103000c002e01003c2c5807501c0c09030900c101856981d920080c4445d040010b5902102d6100c022603a030b00c07826090000b1aa41d00001007480d042010400807d02d00581854250708100b50000104442080390940d207410581e061400343c03140c81 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 425186106 1250 425184856 425184961
    0x30c05010219140a0b09010f1a0f0d15021b06060108060f040902010203040803070506060910030c15030b0910090e07080604080306060c031207030f02070b01141305 72
    0x50240c2c000000c0c1c0d9103003c1e1110f0010040407142c1c0c1c00d84076210008418010380d0160560b03956071080b48801581d6004480c61211146160b0000d111200b0110700160650403060344292039209040c0100301076840807250320b008220045403070304004040c03101d42c0c252554400d6054801c0d280081c203d50b100380e0a0354070519000d068030720408083c1e410302029180c040c1e070403415400b06000101d40c3c144100050840c02d80103c00401042c01c182d02881b00004000d01400300d0420300f62002c1c00410848003800b011165006c1e20804d1514440804800500d128903415500400a00c140a12940c0d41d41c400000d4a4048a04005142d8481d034503603503440061103003040b40d80201000402060a20010716031000000d8409842e01303044e42c4800703045600c0b0710300300b1204045540a11948662609c20500d032039034044011880c00c6641c2d01d503240400d105100b94880d0003981d0000410070f441d441d94060400c08100802d0166041401c1d003440d0020408417140301607041c00c00c040c8464800c00e48142c0f500d036007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 425187356 1250 425186106 425186143
    0x70906031a1806220b090105010c08030403120b19080c0a03051b06130815010f0303020312064009020a0306050a061505031602030408070915031209030c050102 70
    0x80b1400e511002100042101e84e12000c00e402c1091051503000700f01c0402c11038a00e0000302c6041c480c04119401d981a0000d5042014520341c0c040014200800c0300d400640600701140c1c4d407150015070780701422051003030581100f505e03c1050030000d02c400381034090380c071004141d0ba01940480700f071010381e416501c405400d5910808405031024400f403a419510000070307000d0f600c1c18080c40c01c07040c05080f080c6d100b284031394450289900e90701ca003410701c40c0c0500070040d00100c2c1d49141d510000d41c1c074081d1110345411102c0754408240d05644090115004150902403142c0040d040700301d086c524401a01034000c2a082400700618120b401d1040091043c0e008002c116480d04588412004100041c2101101555070501141d41c045690b10207504101d90f80d18075a42e03140a403088512146140514025035100307210a02c840600441c4030000d407200d101c400940c03a003500f0600e212003e41035202505a4a40d034100007070407a4007000d01c4096070701810b904032905a50303000480ea280d12004a40001c2d19 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 425188606 1250 425187356 425187379
    0x105090d081213060e01091a060310050a14060303040f0b1b0703080c1005071409030709020c0705030f030a05030105010318060515040f23040c0e070906031a 69
    0xd410380d80c6000090207480075a003845112002c6000c0c0c030200750360f440021000c5682072010001d00340211450398071400d000340f0036550302c0e17075482884140406080d054040c060002450319281001164102214100107000a0504e5a0072500608410303a0030050309150a00080741410000304450484d1881d6040a03803540c035002070203100d504041c0c007000e94040400c43c48003500c02d0810000b4017441c052000f80c0e684683c1405280d1070102e8400759420060f0030881080300041c0c2108004034035800d034081e166911021507000030700780b12040e0044001c5503c04140300d094940001601c200b603400c260b04031041d442030b031590990381c0e005030100400010310410052049500c40e81040d021401010412070050303001e076481000350345045401d111281e40700c0c2480c40086c40c09014207404014454010010100e00901a11001911080c0050850719100c080350030000c0c0f500c0070310020550440501d41c90b0504030f00041540c145407054000103402c02c80a1022040c0300003018455003030003803240485e072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 425189856 1250 425188606 425188609
    0x8010c081924030503030601080723030603010b040e161220040e01020a0c06060b0c0312060f18040c0b030112140106050402070c03120201051603052d090d0e010509 72
    0xa100b1144060318462031204204038942070050028003440c41100039649034a0032000041001d10020400c00030841c402e100c2d2143c4d03403070a0194040300c40c0a215450780d00d640d0034000c45d015125021482d9001071074081c40244408010071119000e00912020700111a510360700d04405c0148072001030940441c6e000c84000f0b0202803211a1000000540045510703959605034908a0708201c080703901281c4051102000c1101900c00d01c0c1c081d140303a5030344a040c000c041b0600d59480c083c100101c0c0042585001155007940c0d00c200c1440d080000400c0c41030440c0d01c0450142c2480010b69084440c890300400c0422041010001d4034144c41c074800c0c407110014a1a1640010040981c0504095558640020070180c40f580024500903024403010111145145001420511b50300d01030350071a4900300c18400e01095048040150401c90310b03020400380c58421040c0f144074a840d02140c40c0301d504001c03000ca001c038211052889524000191313000d0709140c0b1710607915404402e40080c0021010000490a03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 425191106 1250 425189856 425189861
    0x30f0d1209020d08041805060a080d050915030103080414010c0f0308100314010902030c1804030c081c0518060705090d050106050604060e030d0203130e04030c05150108010c0819 78
    0x90b80000d110145601031a00e03241d030306910941226644000158007101c8100701401800d801c0a41514078009142c9050306541e184c0040704444020410006404c05865481c034a650004081e80480385503256075901c0c09a038168842d2107a075483c05540e00501c041980110740c0d08070195040890b119107100d02d82d5080301c030481c0050405484020002c40400843c8241c000c84811318a081c00024400e011030041610f03040142246500c00d0301d5010903803800700d03507165004ea0001da241c100303206a5406494a02003901681c0080002015940c1c110804444030f034001e280074450a50700780c581105076079101030322400c0031200580424410445003c02d0304000a66105290041d0000900c1030344a40001e61254032075400200028001400d8140f11714081c42a4010f981603030006610303044420b004113501c03500c01d104041075410610000fa0605014612400700307154444151400d11800f42913413008403000380201d180661800303950001c0180160401070080c4401a8001d48402c0300d00e000c2000f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 425192356 1250 425191106 425191121
    0x3060102031303240213060e1503070306060e0d0f021e150a111605010e06090d06050a05060a06210e0307050d020d21111c0b030f0d12 59
    0x11403104001c210446241103107044081e5110380421620884d403030100301e45541801110400b200d10400100000c50340c0c01c2d0480040b41c0345418042940307051500000c0b101e400c00915900c14510000c2040b84c42640340e4400d4060f03800d1a100c0b00728402804081c0600c82034080001044050390b0007410001d86000c12500ba040c1040b42c0b02d1400110484000c181d10b4410900c488180c0caa011820284058100102209050294004040040100902009840961103841d0501c800c001101c0e0300c0c1c0c0c981208aa0f0b21802c054501044800340c0c0c079180009003012108182d12034600400716109140c1200d00c40c040322019655801c075064a03510782e0100c5d000107414100c2a0380c0d03075144a1001d100c148050215540540c01400032901400c101904200c2060400c0e0100900071007603080e10340100003407610030300254800258070f140396440b03180e40d44150011301880c0181004640f80070640c40e04074645404003517041c0c0e9044048606c000b9074541911074503102044207000c02130080200740c0e10144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 425193606 1250 425192356 425192359
    0x129250c0f080601090f0b01170c0d0c12060609050312030903090a03080a120603020a0308180402040803040305101401030b150607030503010915050306010b0904090501150810200306 80
    0x100c0540e290080e0700d44818039480b1465642101004000850b0503202d0383c02c00c00251341d4103014140002000801040c004180c580f40100b0381070118200c100c0c05c000755490840700c0c0c44c08001000c206000038000c10b100d000c82d54465406e20402140181c402c0e0611012110058001d00e40c020745807503da0042d41000300a43c030184010701071803403582e07a407403041001140518000d0380d0b2008241c800614001000e401d4141030750902c4000c00050300c811001008581d0071030300b550b844148180c00050104800c5000b154807500118011640c0034021006104586c0310304100c5001d11681c1d240c0c0f8003074a0441104a82d81c082140041011a402c85502ca5001020302d1800e1030a042d0032000454507001402c00b40c00284000c00184040e41040c0f061a0085444000840080780303450002680c83c041409040c03200540442c1400c1c064690b82c011007516036110009024511058202d0b9080c0a03143c418680707075205d00c0c148031a40e1500b074402e125036000350310300c00003c20002c16100b103440da1001d00a42e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 425194856 1250 425193606 425193623
    0x12021506100e0306010603063008160c270b030705100203040e071e02061302040f0603020d050f0c060a0e09060d020415050a060f02061f0b03012925 65
    0x84010380e02801050701074103487d01c000408608068040c00d04080c00303800c44043d42c0420601001500018001011f11030384400c08541e21015480c0f401c648040d04200203080c1501c50502140d820402c1c1c000480c0f14180c1000d107215644031483e42000d840f00241c07502d405800c120018403403805c20f5000b10394040e00d030780102c1e481c1036070700d110030328032107004490200000e005280340c001d603180f100400103c1081c0314801820182486016800c1d034120b81c4800921031507540f85802e41002103071300101d00075600101400c84981650500f00e44407010b00889080344d0050300194a481d2420318252401c0c1d080655416500703001c4035040c02103400d000351005500001220036040180d4481c000d0340e0928802d48038658030b591802090201e4050281c0002090200e15074020603415400102c03a94040e04035010301c14040c80c0d003a900c84500c4040d82003443c0032040040003040c10f00f00741c40554110b210f040e4030501c14202480e00c0c009640102480000d601917500750f21000b020814500001440c00f40303204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 425196106 1250 425194856 425194877
    0xf1c0c1a060316080a02031002090303180a050a170d030c020d080a140103080702040506040b2224140603010312030e010e0d0903060b0f090c18100c1202150610 70
    0x10715041c2c103140d8001c0e101c40e4000421102181424840d898642c08c91540960800342d103440084e80b40d01483e6071030242000101c055030036a95036aa1900c00074039010301a00d040716103e514412011041820145483c0300b40c25011a055210707114400d0340b004a80c0c0030b01100c4c00424030480720001c01920b0354001548660007012100c0051605600851180381c0d090360741d207054414082900c0700201494803540c0f80403a40e83c00c540b20f15540401c00b08403000b514a107640c1131400e071001003240100c460071942c50302190020b842d003a91001400d80350321520509400742c0c400c0400000d44400d0200605101e244130780c48202d54002d8000920f2a1140c500100f100800005c2039850843c6c0e01c00c0c4c080014100c1c8108005021540c429050810429101c2d440290f10041c0410300c92040a07054a00c82c290004081e0b292140064081050348001040b415461020001c0100311112004d8141c0b00c0000e264a4094140d0001403600c00007018010ac40030140d0755203040045030803000318803201380000c1901 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 425197356 1250 425196106 425196133
    0x40f0507080114040303140c030a020708040e0a0b03070b0a02030904270320010203040206070b1906080309090901090302060411180a050117070e011a0702030f1c0c1a0603 75
    0x40e1880450f2044100340743c9140508009094a10840401d101407034844c003440443d030441c900700c961050a50002580c1c0d649289000000c511881d0300a680d514041c000b0b103c0041403d0304040ca16501c103c08480c0c500351901d010345964440c1c50070748800340c2e0003000b500d006414550000481301c0c100c100e11120790140a032030f00e141a210090f0490024480f65200024003030b50140002d50241e40500842c154070381035021840034480d84a0117001e40e0315503000141104000800f1000300c40203a0000d001456941d0400c43d5250031041f1010320030010300d00015030940c0148152000160907034020801503c458840034458100581440e402168000809882080c0d0400342405400d4202c0006241c0d80361501d0984030b40d000b07100c040c507075411943d4101f01070b660300550f040c15640c14103001801c00380340c0510b08a46105074880250903002e403411740d01d1940c001043c601303140d454402901000c1e80209a08441c681054200280011400e1060303000c2524948c602c541c3c4020090100c903031705844501c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 425198606 1250 425197356 425197361
    0xe04200a0305070f030c050714071206060603140c121015021b030705030d080702071d040201121e050402061b0604050d1d09070210020d141e040f05070801 68
    0xa440030100e522007042c85900c9900801e611026115880c080208004416000704103220381c900260100b03607081010240020240161070080640140c1c03603428a200d40b61001c0034007140d20885000c20703e0b000300c0e0741d1403030050f00c402441035600e9011946000c070307801444001c0c160058509551804a0740c808030350513201000c1c05260b0b104c10340080c10420541d545211101d480c5e245010701a170881d61041102e51070018070003e9440c2c0d282080e0b00980c0d51190708a20341a0a0391080701621940007090400300001c2100d240114003e0707031650700c4404c801c60058180c40780c8550302c0f080c1c8411070b03210840f20301c810340c003450700300c0e2000f030183c0d16226a03140c45015460b08003510034800d230000390500c0100a01000910040e50450503d0402100d20030007002e120000015414000c2c00c4400024004ea8400e200c0f00b42c030700021040854440101c80c1490000f4070183e62000c440442c500e010411400c803450034860013940c0e41100c01002c0e511a5030340c811f038a10324501190b0500c00c07038801081e10902070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 425199856 1250 425198606 425198617
    0x611030a0603050105100b0a12110d060312020105060a06030e120d2306090115020309130507110a05030702010f050f2d0c060720120d0e0d0e0420 64
    0xc0310108681e41541010303400c4403409828507080e40d9007000200854030464094403a510a2401d003098000100803003140034007005003210032103090003c2e001c0d007c80120f41c040b905407030140d84103e84600d12a1000d0f0b08880040e00c0b4240c0c4884100c1d0200285880307070b082400c4071034802c820b4a80088075440103030001d400100c004540310361191a44101042d082c4800740005407074070029002e900700a4086401141c042c0220300c0310304880c0300c0c900090350080040b150301c240040c0044082c000e00c0000b1000904013514044000b564518681c99200b800040117209681c11401039440c1940c81d40c010759240d200c0301108814080240505aa1020000003400300341c18604154044090742001d42c41100380340e00e803000615002408032909141c0000f541d55031244460034040720642c001e20810041c054062009c003c103200f9943c60021158884021b448200180007092042c0c0f544007401ca03854480300d8060200281c1240045841032501c0e03045042800a15441c112120500702104255031344207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 425201106 1250 425199856 425199871
    0x809120c1504080a1436030607020604030e030a0b16090305120406030c08090606010c03020c060c0f0607030905031602040617011508031309021305040c08010e010806160309061103 79
    0x200e040c208580d0800c0100c04034205c0d880700285010351020b4800e05135054403809410507081d5040541814001c90801c100791480241115814070304034500039a0780c4801c68080f000507075030f850380841c03d0400142860060b41d001000700c49a6444608580c200c00c0038a600f05e017003184810000011840600030307100c201104030080ca81c0c3d1414807030301a0907107140d03030700240821004908100c5a0364012407540c0c2c11980928149609582504080386416a4041c00551184002070303680000000043c0c5440d1f41c41f074031010b4504e0780c0d50310f0742c00368222003500d10042c266400c100b01e02c40b95034503480316030082140300074400030b4041c3e12500a000203a42c00315100c24181e5440180c07115001038050b0040080c1803500045251661522010080620394820441407980129990b001051103001c0b1501401c2c0140040241e4820084018807804c0c080c800d0b2800ca040d11130010813011400b08030302e40316540d00c500300c40d00e03940c903124100c00400f10031000f600c46550310764440e03682c4e4451000660203a0354 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 425202356 1250 425201106 425201123
    0xa06052203170105240306130609020711060f04060c0f0b0a1410080c010c15020f040515070b011403011d01060f06030e0c0f03070b03250809120c1504 66
    0xb00c40031081d0050060300881d00c61902104040881e00170010042c40c00100e0414813a203070f85030348011580001d401a404c0c0f42440c00c4c6007000c1802031903036000c1c0c0811405900d8801d84200d20301c05001c071501c20340803000741ca16010441405402d0241009001d03580c4554a13803261104ca41c2c40d8442088010794000308010340720780000c00000304a501558101c5500b84d049c180051410040d20342d50340b040c81e1403905020110a46006010101c00c28600100366000255a209031800089441303030300a005092103a14544c03250f01c40d40c0101001d507019541d11883c0365582d40d090107040f590301003110703a003141e040d903c03030003949094010018148a00a414000401d0050415800c0c424100300341d0065000c2605d40084c80018000004100621480c04c0e1a21400e286203000400d04042d11600311440100002080c0a00e101d0600d00300c100501582e8102600349101d050101c410000c10b07500011554004418108981d158500412421403024111031040e05000741d0039803a100c00b1642038403002e4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 425203606 1250 425202356 425202377
    0xb070c050d05032b05010806102306210f0424091401060303081b030f040206090904050604020916050a0e01110a14161a0901050f030406050610080106020a06052203 72
    0xb00c035005d5580544524800b03004c09103488200982610b000c1d11070000481d07401d03600c51503000b100c200704100001d806045650384900743c103c150243d40090311701e01d0b151542c1d20300040e2164446e15500c0d00542d0700442c41c4846510412072038000c0350810b480101ca00b552401130f01c00107002c02d240680c030401da00c000458094a10700303015140c044020411840d0824140111115104c0e020459a00c52060140d2071032030340b01c2d4000b207a401d008000c001500103c0701c1043c0014000d0010f0950310503442120481c680e07035201403495a00c4031604810781d01003403040c00392407000c3d401072843d0709880c0e40601d04543d0b4041d5007000c032450040340c1c810680d54071b1403001600348015001c0c4422240348020071503640c90203180a88841310301ea40400701043c1c2c84000f14011070968403030001c07074541c0841841d815807241003e0820702c006200940f01c4620a010800080c09a18001c40d41c850480c1e2880c1c024009489458444001505005140d0b28408149d00304141c40350341a40c44c0c05440031301036aa00107000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 425204856 1250 425203606 425203687
    0x30b0409050f010c080c04092a050309010c0306050d02010807120614030c030f250e01090b03010c03050610050c0a020d050312090c090a2708130b070c050d0503 70
    0x44d00c02030308441c108440c40082200500300c0108480407524048000900b0400510083e5691600d8081442c0140c0c0c406444046c450351090145004800c144020085001c40c114141d04a945038443d00e60010300c42e620043c0951b00509540d40d001400c0c0c2025035a10702000d801c0350850b45660400f0092101c00790042509040c1009151412502900109100081c0c85c40312030b5600ca214000c40c4002d201113086030700c80015518094001d20011000714040e5842e0942d400c0034100350038540f070080d8030f01040c00074817622a02a03940650030180102070090120bd604a0322030384902c9601200c7c0c402c0c001442d0058842c8070014003903d01500180d41c80e01a11184101c841a01034203119096120054101c0d0696440740f00540102d400d0701c00003000e41d00c1c0f001103000500202108403031240007440e540280500d0500504160100c0b0400403180c946500b00042c6a0241c0720b8054100341649100340078904240e90003a090501900889007401d00310f8040310303400044c10440c00d420552011100000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 425206106 1250 425204856 425204861
    0xb2208011a12070b0c10020c0604171804052a03010302010306080a0308060603060f0409050f0f07180e0a02130f0b0103020a1205060a0b0c070f05030a08070f03030b0409050f01 77
    0x9020200e0b1114009030a840003a40d6031101409030340189080001e00c241c1c2c10f8030800174001e64a00d0030b0010754840400102840d143c0d0b004460940e64001c408841316100b040d0b007811100710100405421441c80a420b0500c00107000090480d0003000c005081d8204400c2803210040c2c0760301d086007070b5030f40d650705504c00102035600c0340d40100c40301c2c3e001e40800000a034014400c00d9000340e095035400e44076074400f000101c10032082003280d900700e45010405c0090003000302d1051140d54103141100c0207041102201e580d504594421034a60748585100802c94410301e800c524440f007810b404442a010a83c0c0018140d124a19050703610140d079042c0701084030350f103400380d00301c1d240003403d08509207844084060403c0c05aa8000035029a41d100010000e0340c4944184d0003808003d100543c0340d5060081080e0390300e0343c42c0100302001c443e41c0000074244c54000741155820394032a032441c1c00d091003507076150750030302085000b1418180c0750540741c0099221882215041800b0b0030051480021800080d409c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 425207356 1250 425206106 425206151
    0x30c1e0917160803090325050603092d0c0d2603090c0303030c0a05030901110d0e012f0d1416260117070915031b03020102070b220801 59
    0x71a0011700800c2c2d8140d4012a55560400c02c0c65280c1c40710602e5140721014122141e0012035120724007000340092007d0005020840e850703042c00c0c07101801154504080e440a8210041c0d2003644030316101a042d090205a0b0002035225100c400c1084030810018a1194581d08600203004004810401004020012118050415005540f85040142c3c400055105a03d000000d02a0000c041a140d42003580500c0e0a40c0306a44c1c0c207900d130a0007079144000707004031000320501796082010313082240440c8050032002103901c40c0c909009154529408000e500b01351004605159644880d1808001404845100d0010b410145080040b0780501078140720410541c00b00d41340c118540031207444004100181900d02c1030799041c1105800c0d540ea28500100c58020b201528108845030104002c0c210030313001924401c80140032072041400607900348098600c0081c0c01030740701480401003004510010a40c03400d141d10701d45480881340c00a41181201640312514607951100b0b0343c41e040c1d02c420009036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 425208606 1250 425207356 425207369
    0x51510090e15040503070f050106050f04021201090c020a351e1602031914030304050a0807020f1915030c171e09060a0606030c1e091716 60
    0x21140c044404250380d100007001c810b0020b221400e010030140402001540c45c0c50390310070703020301e11006c0354a0241d02a1800e03104160185224009514080c0f44c240259643c0070860651a400d50380f90501000c0908542d00000781907001c0c082e04100803e00000042d05100320389102c00070545030045003800c011540c07490150311980107000c034404000050380c0013420f21144000c069155001108445034102c0c001000a605100c0c03240301a52864081d00540840c600030b0036048038050103d181c0c141c0b20701c0101d030000c041b600601955800611060081c218003030000d003203800100e02d0403020401005c100074541c984480701c100100150300200a41030420720592500740289410498040c01d02c190080010700c020b40e11400280c40043e483c1e144c080c41c022005620b81280c10103054883d02d92609680c001d100c28100440825007038002c0c0220351090841d42c1e60304403500700360201003070310760901c9041f0700c10090071003000140c0011031200084404010b00c0034125140310b041e40c10054070307070943c13001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 425209856 1250 425208606 425208611
    0x3090e0a05060910050d02120106151d09010315090f0c0311091f09052512060602060c19020a060c050a02010e06010501140d0f090f05010b180703110705151009 70
    0x18411030301c40c04001c80401f681560250a1428a0780626000d0911a000b134201c801c0b58400c4028803951008000180b039204600c00100e0f40302a00c14448540000d00014020715034012400310242101d0f440242c00500440100c090b04100e0750740c0d00c51075101c4d98000da4641540c0c4400f1b00c0d5514101780000d03000420540300d4107450f03c0c60104c142c41d1042920886506940d20000161050908420b4030b034880407903050b0003244140a02c0141501d13541c07620340c40c4494a020000b1546900000b1100d0003400d640d85640d0426519171000003078609a49a9002180034206030000095103038011003000ba002500c4036a01c60501680007401c41d2007d0840004551041d001040241d0f000f030502c9202e0202d8214080c2d071480314000300c0c40686120214000031602c1d0000f43c030305109445038010f035403a1007100240980692042000200d6610545031030030f140300306004c40c44030f5001394401100030096a42c058146519610340a081c039100400e2021181e40d4501005045500c2c02280001340180b21001c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 425211106 1250 425209856 425209859
    0x209090f060405060f100e0d0212070608160815060d0507091401030b0f0405060d080c0109030e010302071a10030605100f08030309060103230d02011a12060a0903090e0a05060910 78
    0x1a508500e54420300040c0702d04501508082d03200c001320744a40725006030034150042c90108899036036401c1880340300300142042001c600c0c0801d00021500d01d6450990b00c024441d110342030743101c1200f861011542c0e0320010400540225001a01650344218125220080300d00d24102c17904442003128001c8e24101440c2c0202c0c404955a041480300111109990000b5950b6426021900030071500301c0140422070b02040b14a2180d005420405d490ba100f03941e50b140c0d6800401c0158168081c1c850020308600b6080740d80c600030a0300031141580a4a10060010000e60303e8036142c0031034105448008025a4620382400380340c81d407205840050031820002d614500e0050244d58032188103010007001d6510780c0c1c5010a8000b084102c0c0c0e86103023aa9415a03042001d27140c8083e00a2504400542c613403422400c0d018074500d0001220b2868400c1440030701100d60390780f41500c00808100e035080701408960403000c5508801c441321a442100c40c00e5000031a400c11004200001c48020070160340b00289020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 425212356 1250 425211106 425211109
    0x41d0a060e010c050d0e0106030b040b0402180105100f12090302160605070b150604030204020a0203090405070203030c2d0c030a180b070b07270f12170a030209090f060405060f 77
    0x1725900001c0d2030b54001006051200340c103015140f25032020300800410010702050042d8001303680d0086100311003840c3c1000748116031004078078091080580c0508241400a242030158403403a41c069414a8008061440c1440e060112541d1a4007600181c1c4900c103948081420141840301501c014241036007801c0c010788d0b8546080034010504120145800c407070200544511085d10081e5500500c1503480c1c1c121540000c1d580e40161446a2080c1d04000c08030349018008412030380941182c51070303035140c40303c0a80c02c010800f00b49004030b080c2d500140c1340c042c1c0b20709100e00038040d00d1034910055a55401013040040c61402d0000d4440c82c503d0b6511000c100385403504045640c01c0380d0081001800340ea41c0d800644008204030800c3c240015049980e2072501290700301c050699010000302c8400c00d468400c0390040b06181a4000c00c400313041200c000500c20300c14098080e400540c5400b5207096080c5020850480c03081c0c4681c488a00d0701401d11040303142c24014264440d4080c0d49440350030038040e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 425213606 1250 425212356 425212367
    0x4030201270606090e0a080a0903080a080610030618021b06070306031a0105010210180c08030c0708030708071b0812040608070221030c09221401060e0f041d0a060e010c 74
    0x1200100b440e1f1780020300000480c05404120000c40e0000000d130b850b503006900140548100302c8929115165408038144c0890081c42480107461581c070345525405410395001e0000d600030850480c1e04440003144460045040002074480e803010b6a0202d07540e45103203415068008190010034200c010240103001599000610691a90500703c0200342c401c0007147c04099104000c2d009841042d0141c80850810340001c000c080c1c420541d8100c032140ca03130b603121050720790061010003058600f04000300c40218a02207004c2e182e09000c449400e0b266a6201009403601c070304414500e511100210302000202d410102d8940d22100d103001500c04426010a1032030740380d5070824141d000d1f040120200e801c001d0307040c1c26500200009020f43e41d60119403490989000d070981d90511201d411300b000c094944d6181d0200c4c034100c4103c0d403a0120480400410072070030001301c90910341c01c156190130540c0b0703199004403c040f41d44192009001c20740920b04110042d50007d507810304050b81040340c038003207056220 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 425214856 1250 425213606 425213623
    0x1022109061614070c030b0108030412080c010b1206040605070804120f1101060b041401111906090209070e0a0b03160e031e0304090b0907080a020304030201270606090e 74
    0x1d0000d44401e82c031406065402c41e00c0f126034018842c4001c00c0d01000c100301d14041006490140383c0d0410345a983d42e01241d40e9228900507154183d01c4030b02501c0004564001038510600c4140001c10b0000f030400205000115412105415a00c0340c81448107000c000e21845411002c07030b20300b003015131400340c86038410144184101c004201e20100b00940d02442143c0155400d510130000b1301c01d81e5582c524801a0350018080d5030184281602d0018281d070082c0c0c1d0301155040144050144d1140300c10105912142c0c2880580304142c55002820042c0c0d220035840b842010b060f220700400001c0c003000e00440c1d02907038000c411403201c1003040c008100742200c81c0b81590061850401c2011160340c000c2401e001500304104030601d00c5d13144d0742c0c0058002002030b1041c0c2c1c40c450301c1002100c0a07082048940b02095801401051240010900c01c184640055038171030b01034000407400c00500f02905080a0346900e8050b94248401111001c1140e90302811000b071500c00300c2409101420311003140c958102 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 425216106 1250 425214856 425214871
    0x11118100c030c170307050a110a121b0b010312020c040504030503150607060603030503011e12060903030e06040506090115050a060c0201090f090504020f04090f08130302040203090102210906 84
    0x5803c815030130400900c40d85400104500b0030142c80e03017458071014026070881e615180c0400e0344d03416103041c180d5000454000480d0409154803039103458071015900002c0b1040701104401103040d501c00031903012407006008620401d001c3e05413404180b4000e041024030a1010321039410b04041c0004698070500f40c80d00031a1180c034034030102d0002000a642071281040041c07541d41400307800028150014082c50403075100443c0e0040e415203038080c1041e50030150241034841300450098501058195000300091072081c02c00080e03d40d01d600c0f813240360440c22181241c1da544030208008030f01c2c5081c0101040302d008036000c004e046040c400007420010301070041c1010070401940400a584c0b05909443c020000e038500c00158944445a24014000c00c4070184c1c0581040c0d15810f900341402c5c03140c00401500032014110507645541c643c003043c0d2100a006c1d0fa02d074180100400580d640d031000314001d9280c40c000680d200c4000c00b80100c050740c041b41ca440110b00020401501500104500b42c2c080301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 425217356 1250 425216106 425216117
    0x30309091902041d0906130510050709080102130f0902040503030715140a1515080609180f1e06010f060c0302102c01110a140c011118100c03 62
    0xa600724890090050b54804000c4550380444520399400c0690101e000e50041010f0719442d507203022924041032040d403002026544112103211407800b540e44920303007200c0140f51034154143e0b914000350036a0401c2100030f41d0440c80c0c1c0d904100400c40050018010191010709501b060315050010340c49009165010341807501d0303100210941c840707d61005041c4100307079a00c0030076414488001c0b0010714040700700d00c45902085c000481c1c0850004042c0c0940e0001f952207030080e07600c05061050b501006801401c0450b08000002514002482484001c0164200600a8030a4000d284101c0700301c0b101c803503200383c2040f001031107420848414481640d001e41450900d2a9042c40d007240391240818010b00072a281031720302145018500d03c0c07801402e4400450340c8030f00c548004054203d64040100c20b0f1503480400103052103500601140c0c6210159840d241d0600c01218100d9082d260304040044504200080c2101c2d072204811505103080d005451000c100e414404000c0c0000c0c42c0001d0182c140034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 425218606 1250 425217356 425217391
    0x80105130f0f06030b07030b0402070b01050d1b061d1f0c08040302060d05011806060206011e1e181e18050a140d020609071205030c0a0c06080603030909 67
    0x64a070b800024041c48054020032480c1e540b030814561540040d0751410000e0308080e0b000001f40303440e0003640c003440e0300203602074040e904e04000c1009840c0341040440380010b4201041b1f01c00300c01901108018555616060100c449001460000c04689c901c03c80c41200125414440c0c0d54010145000d1a106800e001d400d005007400c2550741ca01655000a60084000501e80c2c6002c1440c0c12403412109054608020609108106400d885141c0181c0c40181c0c8403100401190b41c1001401c00e000d542c030854121403988407052030800d0300780501449010419080c080101c0118181ca44a10007071035403082085003071003030084c0034404801c046640b071039846000d500c3c20542080308000e031980d404400c5441c0c00e01503140c0340d2404842000c10203658000d1194054147e800461142e10a007201400b8003441820400c5d080c02032240800266602d20080c00716030310702c0720b04000000d00720f03004142d280c210601d0040018000040140558000d42003031200318844c1c0c035608080c54028070840c01652011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 425219856 1250 425218606 425218631
    0x151d15040b0a0e07080a03020a06230403030b0f0603011d09030a08160324030213110702040c031d03090307090b0d1101020c04060311090906040822050604080102030a0c08010513 78
    0x108041e040a00c3d41e025003061b501c05c16400082801c3c829104a078207025500351403200910801c41041ca0742405036100300007030b00091182d80044982e4000804219030b00ca2440003080c04d50b0402d030002440007041d0315a00414030300c0c500c4a80c1d804003c030750080d0700d00b0031002c00040c01000c2c0030b09070240306200380d000a01490700a4000e0400302150000d1144920040c0008201c240350620059000d200c0d5540d050b00145001c0c014000794050780e2000034505501c607820303c801030690000010406070740d240c1c0b20148507a51a0210442e00f00d00c0011612640314201309820100b99501c48060a8500207420110f500d03040300741548260000d520040036002400140c0c10110008a13032a8000d14100003c0100a08024030000e00d40e801e465070580307a034442e6940d80e901d00c000d0b64058920321060000100420208840080c09030078600f40041417991030780480c0f071f41d0300540c1110345036940100800440b0301d032900c145160b040c440d2600d030809502d03010114180f80740d00b944590a5a85079680d04002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 425221106 1250 425219856 425219863
    0x50603011a0d030c1509050d030e010e0304140a080a050a031202070b150a0308032d06011b0c0f0b191809090302011e021e1e07151d15040b0a0e 63
    0x1031741d0301060a020003450fa15115441c0c2250f03000036804680307083c2600350024014450390b00103040b548011440c0504040c0c01050403107001a183c0c3e40400000008918907400780042d101c01c5119600903c0c0070005445d000e0040c0401d07a403201d601510501c54070020130500c0078071035042442c0041904074440103401185807152150000741c0182c00001c02c1c003802c411442e8540c0b04d0704d05100c0c5d00d60304100b00701102e2000604d06980107800181d400c0444000c036030510040e070b03050b68130409007070316a165503031000b0516001f02d40c09010301c0003011070325074a48001c0d1080404074444030301d00305a0041c1024004540d10010b13004826003d48c1e12006541014001d500100c0c18441c036024103000d00034006119800780d40320710b0102822a10801140c4060007250382074039940743c1e090135505c0340c2410814405607207407c0301d80700303031811680035003080318111071486403165061202a40c54031501d800392021385032000d000900110812402c0401c00810507598039150050040c00020841800e080501881c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 425222356 1250 425221106 425221133
    0x910110c030d08090c0a2d080a030e0f060c0d0318170a02070f1a070305071a0a0506101b0501110a051314030c12120d050603011a0d030c 60
    0x1014400c41d00082680ca8021000f14810441c0500319524281401c2c01e0042d404858400d0410344005540c1c42c1455091125049803028403440c04ca100c07043e601c08104d03242020038103040d40800c00c00040d9042c60f04149010613824042965654901000c06c1032069a4101103c0701c1002c041e5600c46407840ea81c072070f0820511694228101280042c9c0465000415a1060382c0038005441a4000000c8403903062000702c0468000342e521b183d11301e8600124010b1980040c504504001303003000342c840010b04880000301188995090b0043c20b1602e0318900040b40c001410382482043d1280d0075100c04e86c0e01565401021880704d410082400741e5190483c050b01400490100002001c02c0c145034840c1d01c080580b581c3c1c2d0300c460508200c60b68444400300d9404041007502d4140c3c00c100c86052650030b01c0071000070000000c1c0700710303450000207a46491172074105201c950820703034035070b0b040c020203103001d0044c00911241007214280c82114000010b5a032103011a000f41402034001c132240501c00381c01c04010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 425223606 1250 425222356 425222359
    0x902060a0e0415031a0601030e280b0106031a0f0d0602090303090a0806070f0c08221502030a020705090c03060907030603051902031509071406070c0f0e0a020910110c 73
    0x72070707803641741018540c50200082c03000589141e000948035071003030181c006103150b4640034000302a1101039090032100c5650b07440d21408000c07100300c0000b0380454100707402010555400281442d00300d81d20b100021724082c00d103209409040703150055a4840300782400d12544400300598840b20000800e0440c0a80c004980d402001c098000950003808100e25108000680d590203040141d15010b6820080c1108061300101c000d01030070a54012040c0034034860001c4201005c41141da412211060340407807680310303005801c0814091f11494040203000c007c1c14044032500b126140c08562007055000c0100030303074803800a01010500442c06035020382c01650f0000300395544c9400c144625115010311681c100d00a1042582c1800c02c10000030069014103d8100544041d51624075103e6007041030502c0c007035100404020202c0003800c0034214000810116000c0b40c041072401000c1c0d401118000e02500d0a036004014105e095030b12411620000000780c102031a040c60780d030040d00d05d49003098801e01d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 425224856 1250 425223606 425223641
    0xd030306051201022a070302010806040902030a211b0305070c080303010306140705180f1c0609110105071a0a0f150302030c060c06060405090c06030a060609090902060a0e04 76
    0xc040089040d001884500b5040115402d4108051680040000840005c0391141c01548041c0700540c41403c050790402c20052000c14415826000a403c200c00c0c50030840382d0382c031852100c03040458200806014190320341070204d4400286035504072038185501c4c006003001b5000801f0020801b2209680d006000503108503500c035a141d14241e0000d145c1304104030340d6411064001401c0c0c62141007221036030200400414800d10200307040c0100c10320720f051465400f94030131741c014800310881c0750074440a9000c0d58011885880508202c001403440e0601c190402100b0000000820006841c07191a02c00b0141c0d4105075988400d107030f030000c01d40c7c40c9200311020b0401b4203200040a0703040410041e03c3c000c80582304110310380e40c20042c16108101d980041904400000f9047c2c0c90143e102c1c9900008000946038055000f20025071607500032101c0000e800e580b04414018180c0c4210114007610341584200301c002260f4000a205002e824009001c02c80c220014030190f0f2a180c01401c038981652501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 425226106 1250 425224856 425224879
    0x206070309030b0f06010215070c0b0a0b03030715050a09330c0c0c050901050f1201020c0d0f02070605162015041a120106050708070b01121e030206060d03030605 71
    0x3803035002d210580705d0030b0052040c60241c1d0f102c48054441503004040944031010b003840b0640d80c43d11204401060902450754880a203145600c060006082041c89044181c610928045040e01160703009030500710030500c0c0c40c030030000007200031041301400807901e8110620343e00201c0780080d40110604a10300b485050864581c1c80507004921420494807401c10b091416480781c0034451640402d01c00d4661003409000388044a081078242900340948202c0050301c1c148a02000764a00041c214406000450256044980d0340e410f001a0380034203158034003039140104212400a040203840e0b409400c4116081b0b103044200da41d09504407088001038004c05060030300003840c0c044d0390054840c1c001d40c1d981d0140303001d0386c0382c00900882d4004c1c040c1012480190742095002c460307941103e54102c8610404009000c089491070181d5030082c002a03051520021161a0600030010b42812080c08092001801d000007600854415845030042d65900710200352418110060b01d026409141c001d60001039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 425227356 1250 425226106 425226121
    0x7051908030a0e060c0406050c01020c150f0f070f0f0e1002060a11040f060e031005010801020702040c021b01080c041806050f010c050c01181509080c0d02010207030206070309030b 79
    0x1540c42540115003c10051001800c080d0715083d04803902c10003800100001d00c0340d0b5024401900480c0101d100042c1030114101c4c000d49400608041c0540140d0b6400800101c44041c2038907640c4040d0014200b0b40900382104007a121001103801c02061028061032114403510034680300c1030942000b0704041110301c5400c9d0103074581006a0318190300504018214440c00c123004203c500310381d1000d03085080c1c41d20348042100c07101c80d61031015034903002d6003105400340089802890b0281c0b10303210005035540c8980c0304000458981c944800159000101701c045048442c2c14118a104420300380001d0607520490360300d50920645d00b1442e1241e8055a0039440c4416507400242607035020b90310606441040001940c00101c1c00e50018170b603602910119023654420003034040d20000350558404d140f5226003000700c508480081c40d800003440158100701c551030801c4803050301d08098803d0400d5020300c0d00003e40310f40e032500000c1e0080d2f5001407178000b014419a2840011a04001000b0440c01d0244 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 425228606 1250 425227356 425227373
    0x501021c1d060a0807110a08071203060b0f19030b09060d030504051201020d0e03090603040809010302070f0f0309090b0609120a020301020304030f08060a14040c02010f0f0c03060807050102070b070519 88
    0x200c45c0700c0081c404036000e2080c45000186084003a40104180d802c1208e1940d40c21520301c2c0300b0980d00c0805403207250010700745d00e10501030401d01c040d001c5200d07210380000214466000420301c251040500f4003407400400d0701c2d6050b805400c614162030484094495040a5460380302d81ea11031900054514810846818103501400012500c90b03024071003810103c40d0f61307550b406060f4845030302a50410100300028001001451108010b04015091208544070a41c0b01d001c0f0b1078017540d0441194406004041d40034072600b002d0401d04004024003806040400c049004100d0424082c00300c1e042c0e11441180c04000c4603001a034010002d6581c0d1070700c1d1078020501c05034158010007040c0a03c01040b158901300d0703a21400c0d60008200e07080c0d00400c0100300000b030100c0502130000e555941610700d184410700d0194403600d0101c1c5c10081038540390b05100a003141d450390300c282850340124400307203c140c1c2c0c0840c9a40460315901c00e110340360b20044c106181000c501c09403581c0d104910b010700204110b0b602 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 425229856 1250 425228606 425228611
    0x14010e1203300103030806060c010e070312020607030e03040513110c030c1b01080f040f170307020709060b0f030c0c0a0f17072a0801020310030204060501021c1d060a08 74
    0x2101c589188998040e0b450700d8101c01c0c000240855001e800052443c00d00b200072307184010400700041945002c82d4441401c11200c0d42050301c441c02d40c03030381d0203022680400040f904504c603860204014980d180d42907440b070040e070107490703c0f92031410320108c141308594012a0b100d0001c041d2065a84040c121140e80d644c0c0410308443c02401000090f01d0813444030910b141c0300c50f1b41a100e26645a403a4100301c0708904c0024401c5801c081c7c592201000301d010f101c15044440f100a503d25620705040ca4041d25141c103036404190014184402403041d21449400c2c1c43d89415864010b0351203440d9014440c4950007401d80c0310b00039100b09100c02c01031080004c1c2420980b8040e01041003840304181c0c0300c124600c41c3e01009884150181d00000d941080700807540740c2a98a6480b404000d601c0b40200c4e03003a40e109451072103000d072240d5414030642c50035101c0d41e0000d00090006110300c04a002030004d21443c1030019105000c0003160a442141d4205040c90110000400b0595580c19a10740600f248105 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 425231106 1250 425229856 425229907
    0x20c1605091303170403050f12150303041a030901021e03100906080a02090601110f01140606120c07020301021213060608030a0e04050a0905010e030406020f010614010e1203 76
    0x60086101c4100b2401d03071103240e41d00341c2c0d9241d4402050081113640c0302809001101040020400c10b0b10340c440300c0c2c2c041c005d841040e107041080c0d410103010b81c0a050f03410045140c800e030810001040306080d00c0f0041d0088401050f80c807a00da0341ea04001a0082c0640f2400f860302d030100c5004030408082c220000d51040710201d00032142c032038480981c1412540240100462a4000c00c3d032072000d03141c10202d5641c881c00500d07111108a00e080411070418401d0f070a81e844503911846400f1300320740c407000d00c01d501060543e03043c1c0c10f000c003100f41841400700c0505240082c1e4800603106095450a40485210500c00520240c0e20b0501034201c5001032481582a00c00600e000e0340407038042c00100031034500c00103e50300d04207400c000e141008002c010192100c903005589461742d0f40040c20070300a0315180006a406552240d19040005c0e007403014a0b0081441a450004244024450807012000c488020318102428120b03841c0030034212404148100d005100c0414a995031103015040520340c0d005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 425232356 1250 425231106 425231119
    0x3030c030106031125050c15130b0a0e120c0301022a0a0215090a05100519050c0a1203090b150111010b030c091f140f030a110112020c1605 61
    0x11300480c160074080c842c403904840c21020f4a030420704e5810749002e80101c3c004c07400c1d1000502240c000036100c40342c01c3e1155020301c00c00318141404200060744440142401c0b00042c1c80d0004404008102094002d03030180300d038401c049820007070a001c002024a10030b010b0021503031000b0390342e156103c000d50701000c0d1846900c0c2c4203c0c1002d200000c03440100302c036405094158410001000c0c1e00940d0804550f140e00401040380004066881c0c404000c0104000c0d215076945801241c1401d240c009941c8400301400002c1141c8a0a4403000a000c0708058003d2528032241c0c0030b8850031005098980780c06007015440d4001d000c088000c1d030510400a082c2600d4000e079200c51120400e09070340c920104203905810800b001d01c0541022081d882d40890550900c681804000c49101d8000043d904041d540c0d61040c4031210140c2042c64441001b09400c5000b44290000f558650980300b07800b600950400402c04200c0b01c2e1a540c1d1b405890941d98041d0603030360004030606d031041e00c9101034403545100c2d01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 425233606 1250 425232356 425232371
    0x70519020f0117011502120d022511061605100b0306091204150905060301140a0518150406090614040c0503070f03090305120103030c060c030515010e030c0303030c03010603 76
    0x600540c0d80302228410348000000c03136840c2000f01c03600d51383c010a0f40005e602a4011404450556100034400304030120001a180d10020789415000000c0d1156464421240241500404c40c4425094006c500450384107a84152120548010f2a149000100705c2c0c4910722046403403400d941c01c40b25507a007050f411650556a240142c03a510500842c18070107081c0104401e0040758900d603030890014042d414140f86076540e440100d211035100340d100c50100c442061a0840c01e14080300d85c3d0008040449594403100a194001c661309280a85a18080300300c1c04d0f030441c6180c8a81e008240140184202000000e90b41d1021080700c0c0c455402941c0300c2c41c508081e100103540280c00307807401503840d56a5000080001d140c1603005221002d016014000144840b40f055848404614007a51080e0340c2c031070000b0464a000401d03500480900001d241c182410045c203600d241c0302c02d008a00003440e211804c100c0543c0030900f44011004030039014000042080b00601c50309009504848055404001c01d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 425234856 1250 425233606 425233609
    0xf0f06021c0b1005030705040501110705060c0609010510050a0605030a0b040c09030515010e1612060b0c16030302060a02180d0b092b081e040312060b1617070519020f 73
    0x600c03017140c0d511b0210700d0900c4140103030752103040e61000030008442160792554070b071000649184c0040b58468103644c400d1003040b480d04000c1c000c140c3c0000e040c0d1540d1080904200014001c070700310b8019a000c120b40840041c403801c1298001e071030000b101510400885c071074050000c1c1903501c140819501c0d407059040040d80803048940c40340c100d40030029217407c80d0b11010642da000820341c000881c10014000d8004150301d08a114003c024640c486046540341207a41da1075040500140503508035a1928208002107034004c122a45d2103102c200c0c0050355184d2144072614031820110150b80c0002d900301c1c600d0308220003110014066800d1000325880001d2854560703280c0800c9042c03648400790540c001c0040d05014400c89a0400c500003ca4080d50440c400c54aa00c0c0750111015030000b5014106206419007034400c0d04040c1404058161070141d14139050528405210001040301c20034213502010603040d402521121a44002566030303071000b55401600d0300c50301a001341c3c0300e882010800d0b000c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 425236106 1250 425234856 425234867
    0x40608210405100309080c01020c0a110d0b0c0d15090212100807030b07270611121b0a02030709020405100318201009170105040f0f06021c0b10 63
    0x4580005100310883c40b80d255003140680070080007250105070034031007803900a4003800980704950850005001c000c4035400c3c004502803100ca140c2d4010742c4103805400210313000d80031040d070044080320036503624610000908001c12000200b0200010030750300c0860b620452340c00a100e0035a165900541ca91075a4000120b254443e200341806079018500410001d40001c041c11344c410803d0070030318000342f00d800c829040484003c0c11402c510540729414080b03242c00550440030020a4001801c4920542c02e01d05420720802000610b07031015200c10340c041c8102004440c022907070190940d10480d540b4064140a504140601403054501c90b240b165854420b02c105550004031010400c2509825181c90320440c1800021707030407400980d04141d085444843e03900664a41c1640c603182d0346071914450140300403031121490b103907074105011700c40850940318174003200360b41007a8110b800044d24a000c2d0000c1c45040c624110000038103117aa501105d15500001c0078010533242c210312201c0300b01007101d9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 425237356 1250 425236106 425236109
    0xd020304060903030f0c170309160501020a0b06060d0c0908011113050402090a0503030406020d09090902060306090712050a0e15190f020d09060209030f0307150f0b0406082104 77
    0x40030300c1ca003040132070f2007081c0c5020100d0040c02c100c2c4480c0c42a031114003501080d08020303185402c000052080525003000301d4844900480318050706c141c20480003e442c1d02101c6030160114808201040080c0e45800403501c0c082542c260421101c3c08401c005441041180310380c00c40ca51800c3c200c0451845008101c503680c1c01c92810141104d400c01003040029007240001c15000550b4141c0840c054a041000b0800740409400400101e210950300070101407880e0072007079020b4140410304005032104810341e03402c02c0c070440700070a081d6036080c400c4a002400d078441151341410070090000c000c0ea540d1058002d00c94400036100d102c01100c0d5003c428500548035407070102c5640c04d00141d480210f80c419880e020386100050315290f5100722076019103281c54000d9034501e90014009003d0700d02040500d12010181018608000303458440d4039007010980034000c4076686640012000c0852a0b01548403000020000c1140548907609aa528125110f00304c10392003025661087d4416000c2c203880 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 425238606 1250 425237356 425237369
    0xe01030507081209010528120f0b0310020306060c0a0b0103030f080609190b090a05100e070c080a09050d0303090302010506011409040207020315010b031b090913051006080304080d020304 82
    0x1071a104402c80111042d030310141c58100c0031251f8148100c02000e41041c04051102290340c0c1c1d11010949141140448070007401440e980342c0340801c183ca950310003040030766003805118001030300c07aa502d2002c154103105a00e02050103005ea040e541007044141e0f498141a01e0281e070700e049540108280c140c070346800c107030381e4543e015000300002841c0441d281ea0104541c0f10301030002c514000c1d5440410000502500e0b01840389413120b0410640301809280c842c011300041c406a0760301d081545002c2c100141020003d841034400140301900139000f620b01400130140508100c481031a00e040050082500500c201d006509040c00320300710b58401c8520150310460550490310301104602040029440020101d070503000c0c460b408405441006401c1c0e00030003c07410300b581d59141030f04400500d01034140c4080382e540014080c107400d0b519000d00c05a07000d6840c041001c003114207401c00700d181c07045201c03808100500f008004248600040080d0049407544011204110088801030362030b8041e602805 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 425239856 1250 425238606 425238643
    0x2b0c0f03020703080f0c0c12072108070804050a020a2414090d0516170601050109030804032012242e03080a0c0308062e1103040e0103050708 62
    0x15506580140005800c06422903006e850488008502c0c0c5c00d00400e20000c1c16a846c000c1140418088442280c2030796048200f060481c1034030191001d031922030054100c60800a08100180c00c0203410000c6804058000f80480443c540c0d0702601465502c1c1c04c0c91480030385e1040d240287e420303070082c40300d80c8201e41040748103814014007406100b0b419a903480705079845c0c82aa40160314040c241400107014100110724134040101c1d810641e441c080042e88044d041251341001000400c508100b52805d032a03105520890352810483c052000d80c03015952568003004038620124840c074005180e40044c03207a62400c0742d2808050150348007041040300d080203d80704604030000d5039000c241c414402d55038140e0301d00f0304442d103d40710158941c020440c848081200c0ea443d10080c15001402c042d07111101300c0c0c43e004622041c4040e904100340c20034050710345030940c0d001d00354040c1c000c0405980c525400000c0703a40720b554071104800030000070310050f01c2c14050104042100790313000c95500c04490241154 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 425241106 1250 425239856 425239861
    0xb0f0105041a0405040501030309030c15020309010509012c03150906130c0315020423010f05030c09040e010213120506060f120a061b05120c2b0c0f0302070308 70
    0x10a00c074540303900c5600804100f102054580d40c910030140a075019a07580355130941180f41000440180b40c104404010346886014140b9500104032118000c00b883d0440e1540c041c40016500f6800341c040e518059502d500002d1034003514212006112740c007c404a41694100d8268120b000c0e00a64030525513412070800580301e6403201820992262151f50f6550300940c0d06c0e250101c0340f644003041c2414880e00090b0030080d92030000c081583c0601030003403806025480d03a0020b440015424071040a0040c0031000610240346081681e10060000e4806d00071b0300381d0b40070f50034000e5010000c0c20110122000010034800000d8884840043e401001000329031136038000c028410194610f4954080c00114100034095010302102c4400392007040c001c650882d0040346c8440b9402da002040c0704125080c030900c4011100000d0301c0703811050074a0701c41d9865580311140d1a5520b107980c200b16403000c0c040042e0802a0311940442c1e510b80850b40d9050060001103400c40076072045050180010b4481c102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 425242356 1250 425241106 425241119
    0x19030b041b02100b1503090f1b01120504061b0504030c080303100e09100c0c0203060f0613050a0f02040b07200904080315270f0108061f0305150403030b0f010504 71
    0x4c1460320100c0203010580d0355401950480e500d61007120424043d4118081d02d0302ca94101b0090354400c80402d6541c1d00004000780c00003842000203581c04000300351a680800e09103c0c05500401d00c201a108035240e40140005010749541d11610044400c10b01901001603108404002c0e24001c21041190203507052600900c1403201c000500200420300480600d00403480301849040792429240d10f8404002c00c0500425080c01c50060420002800c6170042015950340c8500401a07484009400250b035250340b041100105030628124013494030004000c100b1004c01000361180074880e01a148014184c441c0450003100103100f0260846212808140085c0c14080070390341c0050500c070a01c01100c00040000c1e0384010312081240000d141e200021621400b00e5a50342e440b0703001d149181055498075403110ba46135001484000030024054200a00015490007503000716040012a6240203c1c502000340014055908401091808481c54a182084a0b0701207500d80141c4a55003418642031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 425243606 1250 425242356 425242361
    0x30c0d0311010207031e09150f03060b040b0c19020303121906090522050c01030b03070f0e0f06010f0905010e0117040f0212070f0302010509010519030b041b0210 71
    0x890803418801d9088101c0e100c0c440034800b824400303001750380300320040404031030f460404d1840d00c031038038200950368409000b50f5280102d20140450b0b10b14048034402c05040044000300380c10b070880c5c80b203400b0020340052000402000341c054240c1e03400a07181201e0301c0303500c100b925804201d4000c1d016001403107042010b44c281d84e0f038140d2198000c002c00341e0701c5204689260440b413058003e0203403542e4413410301c20700d94040b00050400e01e01c2e00c1d07090751219034181c13210f40c1e4540d2403001c414105503c501700b80900ba2000e00840c001405042000a543c6844a1030007204050450701c0e002014105000918658454000000c039114191100911141000011100300b010702c1d9209041c045800715195840541e00c100ca48218014500900c1c0300c4400c6c4108030001c07410240b00c9170958020b0000f4018000201644011030340c1c24200f4650380c00d507610040e903160191345024101350380214400307020f054250700001381c0e01204540402003245402c1d000c03055503554256140041e403213940041004502d40e03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 425244856 1250 425243606 425243629
    0x602090102012d0914010903120b040b01050301140a030209040b07030515101107120f1104060503060f091903021507082e09020408070f080105150f0a170c03070f05030c 74
    0x218071220349880e0032401700342035480c926011400207540f034440c50f50000c540e100d038500c040e20445040c040c000701d5200082580c0018081d0300d60070002140001001c2e17980712015002150301800340c201c02d00e01401e0241845c001191400007107414440011200c0c403007084003100d801002010010303a440c071890308031a2080302e030007665440c0c450000c022412420168044522a21440e04142c4000c42c83c94815040c41241c1d0303078a4020390400d40305020a590118020380d20840803007904d20035503200d505146c501003010441031401d91680081c8028954003250020600c00300c1199007000d52140601240c101408407003214a10070030300c900c10b50b83e48411070301c510f003d4100081c41030940e03180c1c1d1082c2d040ba80b01d5030000c0d281c0d501044042102c0041802100000c0a142e4020445864180f1401010010005600707101d14014004c0766056510720f03010a000d0301c4101205c60078040f85012302d6541d652180d081c1e80c032a220b40000018008402d10302c1009441016014008643c0140c05000070340884 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 425246106 1250 425244856 425244863
    0x806190b01050f160336050303040f030f2901050f010e0a09150e0f060111030c07090504031803030206150901050a030215070b0a0218061207051608070602090102012d09 74
    0x289440340744401503890041108640106e8a40c80c1182e42004250101c200c0d070004c0d000e50010300c0300704244941b04101c441220781140141d8000c0403245405824002c2d8056401070a201808410145840d20300c1300d181a00d0055502c03180b001415401503030300d2150395001c10b40c842c610113024020420981c1143c1c1204042c0d078170400c241074179509103403800c6c03404a500e945d25910703070404c101c02507a00054400742d000034030002d03601d00342e11105010b403619a54054010302c01d84603004102090320802103000a0040380c020034070215141e290094070f0781000e9410301c40890358002c1440e11458140700403812554014026036a8078915828415841140365100f046c0701c2c5e00340140404a61500768051041441900042e55840c071110300b4003841042d40a0940100c4042c80701e000b41c1020100c180b50030259900741b0036202d903c82044901800000702004200d000042940c00c2000829000361004000c01d0b002440040040441151404070220a40c101070a40c2d00d115403280300d03154030000801c0c1c00f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 425247356 1250 425246106 425246117
    0x1d0717041203060503030711180405071e18090c06142d0a02070302090a050906062b05060609010905040c0b0d15080f060c0f180303040806190b01050f1603 68
    0x1c1d10400207085401c00794003648e2032070315036200c609145032590720505018440002d030100c5040c2922220b41e10750309409803120310b055001c045812801640b044e0070090851048410340d400070800d01201401003d04101c0f0360b11380c0c0700404105240a07010050214210190302c5003032405600300c0e09100300c4480c0c180c010441031080c0c01c24009d07038010001c2c900141d40c0d03001458443e20314410700070941c10044c600881030740b50009000c11808085092500f02c607084070a20110503041c542042218803040040440c3d607100040324041000100e81148214800c444c00050b07682e8809414094074400c6400170125464010180412013000c2c02615110071103603400295850588000a0225204e4008400580c89550041d010306da0411080d0f6100d03101c0402207040807000c051080c0a4000e0040c001d40201903030600303a580341c90030815540100300344ca088420504182c2c8885405c0b1100c0c0e407944180509040f08290203501035411106224606040d1514000c00414044000360000d0310403002c114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 425248606 1250 425247356 425247359
    0xc03060615030402210601030c08060c03010e071107090e0f010e06063307110406150f0c060501150909110304020103020f130303030f0b0a0503070614131d071704120306 74
    0x801c000700d2405d07001c201006010950444c10040c0008030940e20a68207a0b001804000342c1004207000e817030448540102e0b000780c0f500c035510142e94081c0d4032220000d09124a240c000780e071180743d8201d141002c4c4c6c1031090380c0b100514015007a00b40c2c1d90580d40c2c40144c1c0e0014002c0f80305800d080360a161040c107172142103410703204225151118040e03015008000034001203444001c0c802c0000065140c2c2004544c100f004034500390380c1c81300d04c0d01c251601e03405011480b0701800700c0c58081c03c2c0401049900260070011580c590251129940c14119400c0005130740d440d02080c41c03038840c460752804042e41c900341811543d4503801140039500042d82900d9a05041c441c5640c41c181c4803400c000954840c0e01d0200300e0710004000c603130846068001c898415040010208003a480101c0d6910590b2442d00c0c01c4d00c0e600740300e0105204584288031a00c2c0d545c100560740040c6140d1100003800c0c5010b54445141810303100c52008854215108a086580803000303004240080c03848041560081001d05000c100e85 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 425249856 1250 425248606 425248639
    0x240c02122d0a0c0201030c0302031e09010f0203160f090b0f090d08070605061507030c0b042621061c050708120d0605060720040b130e0c03060615030402 67
    0x40e0042c0c03068102060001200030210b6070140207158040c2d070946009c41c1989420558001c65505580c200d4100b00101c00101d41020007e41040d400c0c07441c1d15034155502d0034280d414070f0103984c1c20070748003000a03400304004a00b2803060b0480c5080710105da0314a820100c00d0004421107904c9810180d9201c00301c1007416000a049001404216001c5d1400180d0341c60800248114400d000110000c1204104070481c0003d8200c4032145900b60800300c0042c00d230f940c0f4540480e6800c030440001c107106480c250094403107000c0000425000703e0400d50301c0140e800003514a8840281030b94040d038807483c84040c0c0211004d0304407000d03070014064421180f0300b40d6103840107070800b10707050100600d20342c002400502c076403568042d0300000c0000f40d6500c1e1800d90213813651210690030140d12040104d100e055003840c2d0342e03680c2201c0349501e0000c1400d6107810903000010000c100340083d40f410390041c0d4111020918010503107621540001d400a81c1d807002c07640d4140165480104100d90010303401c615403118 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 425251106 1250 425249856 425249947
    0x140a0605010617010f05031209040b040e0607030b06072d08030907051c0201140c030c031206030114060105192003131509090f09240c0212 61
    0x20003040c0c5035441c04030410421a4200c3d20305800481100341c24030010032003500c0018903480741544004003107844494800005016144e4a1080e0340d0050401e1041c1310380f0f0a0201c0c0d8240a80101e44082100d4400c1c001401aa40030b0b8080c013801c605005c00d6056003c1e82c038014190080300081b52036480b18041d55440280613041900c3e5079103590b01100c2c1c24805804c0c030603400e000390516414654038104950380020420324542c1403a045903080400e2948040c0000c01c02d8407158148041070300d072101c14035140c200d000d01c811120f40384030f9824842e903812200b40c0e4001e494050b00041c0c3d074240c90282c001c0c0c6443d0141511880050400000b0700718039820345601c41d02c41d0b03d1882240d02640d5a030800001440208581d50420620030045451b20016190000380003403c1320140100802c17030a0b0901210002448240005060300c4501c9201900c00030301c8100440034408105010460300a144100f241c0d541500c4010220948041004150040c4114650441890030320090350b403200d81007030314074003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 425252356 1250 425251106 425251109
    0xa170c01050724050603160e0105060901050408071404050a0513021210061403120301060918020d15090507030903200115060c03120b030307021201060506130e0a020702030703140a060501 82
    0x154103507242c017400224542070089031000c0d080380a62a501500b0003401e22440007040c49618440d4000040c10b880d0380e401079080c0c43c020102403040e070310380c55654170050b0305401154001d548207038078010000d01160500c3c0324083c000c110104885090080c29400d001e121842100180c10745e1007500c107003040c1c43c109030140c0b901030704004035046058000e00040c94507207036188551440ca0b0006200602819030b00c040d001c800c4030302909041c0d80520450703040200902c03039030541030304446c145410481c86c010328241d810211070050b40304201a03600d2542c101e046400d80c80c4001e00042c60030110582038000c0c0d039081c90340887c2003400090220421600150301c90340581c00300b0041009040c00c80240340d04501c1101c81480d038000c2c14001721114400203502d83c03061407802486104e0813000100050700035445000030b01009050309a460300c640c10b4909a000040c0701d100b10031880400003030020800c034000e44090560140091001c68210f079180c41e100188080c150400e40310340350584002c144c0c0e0780075460 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 425253606 1250 425252356 425252423
    0x4051501240e01051b03180303030f1303140a08190227180115030605010801051507030905060c0106030b0903070819030f02030c19020c010906030b0f06070305090a170c010507 77
    0x5540e811f540ca1108050f075440c1c44d03064800d42040c020000008038800d07810383d000440c4610840820f04074a8151a000010302d40c0314a004404210130b940550080c40840c011a80c1c044640450f503420380c4a10141e1103110303250030383e0109101c600000300300c00048215500b0b00040c10041c03490020096002c404509a0205070007096082c6003408007034140c81900d01810081ca0078030340a6050601060b50350841c42804110004006520000d15209826a1000d000024101540d43ca03c114038140170b0401030009a500d604c200d030201e40c4a0000108803480c10360301590b180e04114034906a04810b07d01500c614091540324001d0705140e191038401584103c9401d40d0940d142d03017a04220504440031070700e090081d5070251181c03509a1f03810203114000c884041c6004580d0b2242640422038200c80025095000302c401f1420904268004000d0600e0150580318941455955a10342150000460044400740c0141510350225407080b4014000c2038041c03400c41c1814040b00b050b46005000131114031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 425254856 1250 425253606 425253613
    0x2010501032a05130f0c12060906080a080c0f1f0c0516082a0a030e03060705090d03091d01180b01081311060304051501240e01051b 58
    0x52007084911480508140400d44000d482c0410000702d03002511801c2c003505109a001010500c1030226541125000c0d00745a1014440081c0c10040038103078036010700c070300800c090400501041c070400038459281210309480042003401c0440e12110201e41c0811f40101c0e580c02004030071080f54404002960790700424000080c030240541e41c2100850b40d22407054010840e04000c84649442c0c00b00d10360408a0300005e00c0303031741c3c0c03400043c500403511048046e250b290120340319055904070ac0410211200c3e070080c1c40c2c00001030110010103440d03d008413408000b00342c0500ae02011030400e910348034821072090030305510682e1282644045030304e0351000209001e2114005010f0031150703500166580e580d0b0002030000500c4100060702d2000020404d150950b00f542111003404200f5080c0780c411b440203043c0c5c2c0e5580c2050705110303442c0c0c3c00e4a82512040d2010f0000055510709028002c0156600c001c50404070588061080700da20328a80742d0141045414021022454015400d00a0417161100103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 425256106 1250 425254856 425254859
    0x1b0f020d05090d031d130207020f030c13090c050d121101150e04021c05031e03060108010b0327010b1e03150a0f060f03020f0a210f020402030702010501 67
    0x28034100e40d442800c020044140544000380d1110310840401a50606065400409130340c400e00182d80e4042405500c0500403000d174503500c5030755000300803140c0213842e16000310400f20107241c0d036001c4501c04260088040701c0350308094030040c2c1c4805001ca10502c0140740ba00d5032400060400d0848240c01c2e210f10103118407107201e254201c0c0455418201a000902007550f9801200000910f28032400680c0c032100c0c0c002904542d1000c880c00c4040c414608142186084c03802c1480d0749411035100883d900b480200b0301c003855082281940c0c810003050f9642d007501d070b00303000c0c2c00b840b40d0704085c0101444207105128013050450030b03c024000090302e000000388900c0c0803002c1013403c4020a078a1411046441d040b0082500c0114030380005800c182d10b166060b03150418650020300342440340c1038100f4541940414000101481003049030700803503894030010200020041c101d01d0f0340c0324a44175511000024100341810140b5407214074050150030001403203680205080e6071080b500400182d550740d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 425257356 1250 425256106 425256137
    0x818030a0b070f030e0c010309021305010603020309120301150f1106191a0307050f06040b030c0414060a090303030c0504080a0c0f060c03050403080d020403050a060509060705070c05090a1b 83
    0x10210f004400e10701486002c0d0503d102e107031184020a16103040503142c00703155081d52200360880c0b0010802810070480380d03075a041c00600a41003a13a608980d4015400f9040d007c00390710050b00d0690b007500d0003080005150800a0743d480c002c40c00e0b0601485002d4039503000f800001d0104038441d0241c0c0c0610405602ea007003907035088071582613203103500901c201c6040384151400111300d000c2d500c0540c1c0c070690401000e000200c05004507440041c4d00c4c1400801c0180d20b52046002c3d104070342119030b11034181c001c01c40c2001118003a0b0302c00700d00080d0b0604801c00110384241c20412102100d41006807030141c45a900c1410402891016a01c29080c040200700c0307030800c2e102c00001840c55241c01d0000c2c081c1ca545c000c02e113204601c00941080008180788407029110b41c1124001e42c0d0107000ca5003023109510304035000c0e100844255030580103d2001842241c011012a00d40039489001030070528141001c10250070400791901525580d5442080319007405414100c840a415440d841c683c1d201060 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 425258606 1250 425257356 425257367
    0xa061d091c0c1403090a0305011e09021e0f0612090f0604030507080c0129030d030612080715140121150c110d09060801050301060b03040818030a0b07 66
    0x1070015014103050320058030007640c00940c1e418032961218035040d092002100852850062800700e56010743c40345000401c0040c1540501d40e0a850601d005141c8490a49110b084a8540002a4203c5060408043c3e5580e012481c050415401803c12501000032004602c41d178120b420007902100c807a00c14090005410481c2120044200008003c9441d165034002c20600902200030300300000414130b40c0d0400020742041200c0340c0d050000e040c60040700c1c0ea6600031131640720000e5000303020b44000403070071034442c0c050030f4140e410310020b450004080d6503900003a544226420307541d00d046589040d0b43c0040c9401441402d4280c0214044039504184c0c0f100d10445005803c4035035039030200c141200003420f03001881e0b2601100480000c004101c0c0409035078000140030845124026040c1300e4142130381002c103c0c4150f410079550b65160380e0b00e80d0189403c8031345600880c0030000c004d1002030f00180e50b0354020a051901000d50b200c403002003a003c603113000f860301c2048410b40722038410444141c0d400f1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 425259856 1250 425258606 425258623
    0x3140a0c11060406021f0e060703020d2405010c03140c010b1f080f070c0507060207081207050606060306060d0c080103061a0f060309160e1f0e0105090a061d09 70
    0x300d95051501d07107030602c003a560310000f00d4100300446c01e0048000815a00e80e1040079100c1c403260640e41036140c14440207009600101c140584686010006801014001e0407040000601504208000d0801c0e00550300103100650440402c1074408500414420b50000f8103007000b403000012070707910f0340070042003000f40040d0b014040c0355802c0b40402100b594003c0d4220f4010103000e050a107141c448110032613440000690140c21481754041c00680315a0004016040354203c0068846d03102400140d10518400c96501500c66840034000ca0364600e4420015500120000c20f05440c000c0c03100c0032030f41130303405d210704032000304090000402c00d0080a014030700d14007108404c8011000405030000f8010220f00425a000e140e0200008a110004001c0040380480001c0d900041c07076510904804091012214041c0c0c03003c1911100100ba260351112030152010b214815102e44e0824003807013070402c002410303200314540342d11000444600500031400d4941d4000b80324900d81c03500c650007600c0c2c40e440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 425261106 1250 425259856 425259859
    0xc090e0303070c120c0b041506140607080c07150207080c0607200609060d0914030f030705180604080a030815011413150c0c08150604020703140a0c11 66
    0x4100304a800383d8040741d80e6004070344c4810f0444e00c41c0c000000888144802a04c02000000c560341484280290b07140400300385c01800c031050000366154a01126141400341d07050b031300407070240070107400513507201c010300b21961440c8c0889501a41d64604410b4547d01e25900601580140340e081c01000c01c1401543c42c0000c1c02c0e2515440c000c200c0c0d071081c1e170848248030307503032440b0540c2d21010a440c3e0382c1004076102110300408251316800c007000440300410880c002254080303030350403144a20b00008810380b103030040344000890441d525030350140c0700e0f98810100e82e03086184082a100b0b05546540c00740000d030801400502217810149000344c032040000e40105614840454000358580e4459448003032044220f182d60b844600d0a103030001e841c85241c000840031042d40c100340034200d90111103440054068064440c0c49551540065140c500d100750701001c9185c8140090840d0426800800c0401d00c40d180c03d40411a00300100c00a94201024501c0010003100081080c400e003a00b004009020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 425262356 1250 425261106 425261113
    0x206071a0c04030c0302132a020c090601020604020907090815240609040f0b03060a0507120203311709010f0503060a052b0b0610020c0a1701020d06030c090e 69
    0xb551501034220402c1c0c17100900c14015280b02c1041c1c00c01d2038121031401c000c070002842d0060420039070300341c058007180300c040d0052007000d00700c204a10300058030078040d0340c040e0003415807030701c2e290240513030548010300000601103650400200000c0030040c00c0e82c0d080005074229010305191001c3c3c20340071612050324245c0c1c83c0c152040141da40e50303142111100001203c001072075909064001e809040d0040c55a6454043d9204210341d92504d9005584210002d5907207074451a4000c41d80000c0f404142e4010000c1c00b076040c0813860314080440400744055001080282c4c14001d90388480e101c0f4542c01031072200f05404110b1009658114031400718011142c20308908600c0c6c5540481c0c6101030503c5501c0c40f1b09030080c00008000303480301203000254501061b9800b091a6414018000071055901c1030041c0b100c1d00031241614800300c1c0d4200c1a481c0100b03c50301061a24911030811112142440495582080200000481d61085000840c031076001c03003903254900900da000700c07481c25140900c6500b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 425263606 1250 425262356 425262359
    0x180506090c0a05220507270e0c0f12040618050a121d04050604091406010608011a070f020a050409030e19080717030403020409080319110a05160206071a0c04 69
    0xc1c690062282d00040c81c180c0014259948041200d21008034007100001441002c04400303002075070400042a280c2016070b40c003d0b921040303c00071240c860300001c4ac41a0358288084480d80e4102c2e400340e50001e0107907001140d1025005008845c000c1d00403000c4450f540308807180d5003004a4011010a5941da40c141040d9040b003c07901c00e58241000080548110354500000e2555510360b800782d101170380c0002660b04503a0804d840701c1d079505400e01901011442460000840000c0d01503151551155110b1460500c040350380c0e10000140c00e21012644004081c00100345916a4410701081034000d0b900d40210015820500136842c1c210420320100a20090302805075400001d6003000b1141c95104a0b80c0b003030b0004210340c1c01e60055400095001e414941118140641140918005e40c0c86c0013101005e0241000307004100c81b10599034400b0151b051010b00c0249025101818290048004818401c1d00b2903000581650090400315042001e001d80144a01c81240f801907100844400083c5000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 425264856 1250 425263606 425263639
    0x30e0102090307060c1707080c1c050f0d0e010e0c040e0d08061c0510021c1514040f14040c081b0402030c090a0308190302031306180506090c0a05 64
    0x100058000c213014081010300b00c02c01c0007501b0000c5510760300e064a4030303034481072140340c1880194410755031440c081c8a40065185c5480c10904d0340c455000d415141d0790324240043d25603411641180f250380e4501c540c2c1d50011414046c00b800b42c4440004808003904440c1031078130070401294101d244c6010345c1ea04c10300700410326a8002c109560000411507441c224401004031284c42000058402491405140203a09030b850450300a02203800f01c2607100c00140c0c1035090030400702c0340f50300300c480c8003441401d200f017107101c1b03200c0401c02c824100034201043d144e60f1074044005a44c0700070005c403040040d400c10002406644c54402c0068002040a03022a654030210103440740050400d041c4140c0e40040460019030500e030071150400360240003010040d40d03034101259540c025881000120405a41071a01d6900c6882164401c1d00490300d40d00c280c403080c6e15800c1c010840d03605078030024242403015201190040094078491105140186402a07a00c4103100704500941d00460140c625040e894264 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 425266106 1250 425264856 425264863
    0x21809010c0503040c06210207110a2c0709030f0813050907020d030f0207050a050f010606050901050d0c02030408070e0105040606030603020315041b03030c0b070206040503070605040f02090f040201030e01020903 93
    0x6c603001031800c1c005010106046c04c1d011500d03000e030380d009144005581002c0000309801500c0250341144c0c0a0f251984d985080c0c43c400c1c500b280c07445200d25580812000b01c0ca54540000e0b0011240e1610020458a0b541d40707110b0b080038104255598940844e4286400401038542c070040d02003941c03640b180f81054070020b580d0f044180c440d403040c142c41d141011000301c640e50540361400d402008465415217a0f0900603142c0e6034140824001d5403c1880120f0018040c40031118103400694410f480c0001104481c1e004008114003902140810000001e01400400c03841c006003000b02c4407210154074120400c01210700c181e016105142c2403004c1000940e070042115507050505401032003040d41d641ca400fa18198910380d031010b400c0c15188010050550201c01101810b00c6030030498155151804160780d100c200700d5005004c1d07402084074200080903500000c1d041071207011051658100c650000da002c0b00708503010003480d0b84030b00400c82551380c1400b45c0130088180d40021403800c0c1e04100840d8a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 425267356 1250 425266106 425266109
    0x60402040617150d0f02040e1b0105070c09020406260103150f0f0c020109050129130e0613060506101d060c0a030905011812140a021809010c0503040c 66
    0x22140b41c0c2c01c000f9540742490a900854448001d04002c10b5402c0e5181008000d04201001c0c1d0045190960300904200f0001c3c04500c045000c403107401210701d1003801140d13540c0c131025044450204a0307000084a03161400500b000c2c14940d146d034407121440703c210808070f03440c1e41c03c01c20341c0c400c1d40c0c1e0040011850004004002000607040810481c05024118014014030040c912042d85405102d4071388a9040d44a602c80b58400d6000f8080c0c1d502c0d000e2643c0420b2002c4d26403600b25a181005080303030340341c0542030007560300c1d202c0d40104202d44144041401d10b40e0456a01c111202c261025804101c228880e09600c2001203070000015501c42a0044c28000b100c102450000d900c0c038027110f01a501c005c00e60301d8040c0100c0c11240806d11614005048070f0007881494081080103200041418550f04200203842c0b00d280303003010491090310766a00c1c01140c45c04289040c020f0a4011740561184044a8014100020402142d0030111145821201c800c0030080822505000b4000040c420510240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 425268606 1250 425267356 425267387
    0x1031202060a09110d03172701020304020901060f2303040611190f03270c050319030c030c080a18141309230f1506030c01030c0e030a05070504050604020406 69
    0x1260200f171403406803141d15070011610031a828242c20010850310507821202e20508248011052070402c0800f20b00340c0c08107480080d4845025801480f02600c614090384102c0d400d8a0044403401061410480c100a00251415070200c00003c100a1010500880400054009100b40b130080703418001924040485880340401090003404090b082c07180c1c02c43c0304c140a10800d001e1145601c03114815816030104011a44003543c42c50000d02840d000c2503881d070302c40e14003446552112080d45c2c101c1c1d4280017050100c0921a04018440200d00c1031400b5000300305268448010940d07410403268680750480c0e1000f1301018160f51842142d484c1c1c44000740000f040f0a0020030a106903240440d6042e24803201c03149110103c0d101142104000152800c4040c1d1007001e40701814001d101c509801380c0102c8640790541c2c45050543c0d03095110754410403c1c4940f81c58008110302200c8002070500d800340a051700c46900100c001d0145141038801c003500000c0446045140500d440c501074207040c0183c0d402d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 425269856 1250 425268606 425268619
    0x3151c0b060102210d0c0801081009020312031501031b020c04020c0102042c01062d0201060b030a060806130b040813031502031e06031f0e010501031202060a0911 71
    0x1d4480e4001c00c000d12984400d0780d04000c194a050305054003541090311075042c60b0b802c105414040c0c50148056030305a5480c0409881c4160074114004041c05040354202d81620940c0070045240c0d01c88809907004011141c1080525500c00000405030b03418101920241036a40580f6410280c00013090400c81e50161005603d5400c400000741c02030146501140300402d846c3c01560b26900403605c400c0c841401d400758504103980300c52080301c0240810004030310f4207075051741c0c51403000c40018410b00745080c2c40c40042641074840448102603001900c01d4181c242c0c484006001c001704c1480700c180d000d00c074540c8041d0004442d481d480503060001e44047d01140c40011b00c580b0403000002c40318051600015400c64198103001b01d0002948110340300f20300c11801c10319600a51082080080c00740e04d000700145007a034042c040c45018990001c1550250542d03920001040940030300500f0300860103101502e199010498006e800c0840041202c0070740e03468010080300169144040011142055501c07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 425271106 1250 425269856 425269861
    0xa17090111030718030c0f050a06090602060a0e010902102a0f0f020102120a0c0c06112505041d010b180417070b0a0e071505040509040809060d0203151c0b 68
    0xc03e40200985c00260001e074249001284981c8a015240201c0c0c0f01070742e1400359130356940c00448001000340a15070058000001103507001c001a004021001d02e910b00000300050658002000c0e0340c9903859100204031640c000c05603020340e64100c200c01001001e0b0b00404a4510b0366000443e40502000401c5101c19600746025644200260590341000407141c540d5009410030140600005100480d02010707210f80c0803c5ca04d224148500801401100400b800305098032106402c40d4102180400c410000d0b03c001450342e614011090400700d1422100c9000c0030b000403031401c0d20f0302d50b00100e01170010303448240d002d00214940c81c1d6201d5000b1241008c600484014407119100f1458080c2c440c2400400740302c0c03409060390200020b00142c0044960140c0e45d1000c4580c100d00301c80689020410030300040003982400140581d0cc64495180b2620b030201c0c0d0f00009034290003004000b05120350210820401d1520116160f0111b0070403500100780040f00314201624085120300204000c03015000b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 425272356 1250 425271106 425271137
    0x303011809140f07092a030219050c160e0a090c030b0f160f050d021b1f0b010e0d060914030a030c0e061305090403020a080a170901110307 61
    0x32860103900810b20346078840d50300d12465852603c012085002d00500b800022041c9041c4100c800603080100603440064040036050b02501050f04640240b40e0200a000b0315081c100b004210000451346400e92034080c03910a207440c3ca200c5121442000301d5150060000b56010340e145a8040050b04010407200c12610b8481948407403a440108026464000d012014a90810740c51080104060a010540c8661030440c1e400c51030408950100c1d04c1084031541210454005104e203803030b08a40101c440c803484006a00d02100c0362540b0060300484803001100d003d40c1d0150407400002443c001c002400c0c00000150f00820322200202140e0341e4040110070080400e00d43c00781c0000c0c00054940740c1000c0e900140260114024840018034070140b02d0340c0380c7c90a07006541000c00707101030070f000d10743c14001807001e83c0501400540562241009070f100086040700113001e0101266100030381000b000c403844040a001800d805860390402c6050b1040c60800b00960303622295903d82034290640061 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 425273606 1250 425272356 425272361
    0x807030210110702090901060b0d0911030a060e0d0809190f061a010906180e060111070303021f09030c0602090402130e0402100c050a02060a030e0f0106091503030203030118 76
    0x64040340c00782c2408409010352007080060a403042c0203580000056a424122078202e8901c2d00800000034000e010041c403100e860343c80f041c50300d48207002003880750841ca00024078044180e00c00319155510b0785540103000b1010f0003c49880540360620341d90768104804155140d04641070035030f0660007680002010300142110344100d1381e4110381d04014021271050044c000c10609100a404106001c0c80094540c1c8550380070b070300700c840b03480554500c107062040314182840041d00a5040002888404420366801c2c8481e90085110750002c0c038805007040d80301d548041c0300b04180781c03009241165500100ea00540d0654005600810040c0c0c2d80e1068cc002a000740640c031141c084542d00504045400e45a94103071a0046000715180303054207000c0c9004856000c1443c0c0000c01c540c03c2244180b005051940c0508685151424049000c40010034030700d151104014000c581c1d80e4451900304041101c0e44a9810031103100081c00d050030341503480c0a9520710040c4200303203012400342c20200f0108001d0707 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 425274856 1250 425273606 425273623
    0xc060507121803020c0a0e010b030406020903030f0d060e060d1103030c0d020109020913020315130210200601080c0906030f0102070305040f0e010608070c140105100305121608070302 80
    0x208012032000d18445912410740c2c844110090310501e01c40c003460740b800100e0141110400514040507038248400140c19070005401202e49076003c3c0b2017400156420300242140703c0502002d00c0d1200040d800030000d9907034540c045811070701b00e80b041c054151296068403240d10b801080380c0b428003100310042403540c13103244810440d50203448403590742d055040d0400c42c40e540c000c48140032503450b42501244545e40d801c800a61680c03042204005403420014120343c0103650503841c115265154020500e041c500e1165200061000c03a80141241701038000b18007101c21550081420750305010a05030354000714599248120300413000245140d608111001100045000a54031260640740251540c0c000e4020280e000c42c202c0c0380860081140040b46040700d00355518944181c98000064440c0703520740d1010f0301d8050710000e44469070b020234041d81d070059a24102e2092064990305002d41004c01003148600525001c008400302c480c08401c0802070980c01080195440001d49010307071520422 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 425276106 1250 425274856 425274887
    0x80324090601050c0a140f010e12090904290601020f0a050303010528150908010b03100f0b0d030807030e07051503130506100f06050309061815090d0f020d0c060507 72
    0x24104201b030b2086001c500110701082c110002e105280300c48075034a4a81d0940541d0448002c424001e0011501c3e103003900907003060042c03026a1101d421070301203032402e40f595000c001c0501640428050300b0759040004030702c10310301740c0c000e403448509a656160b268803040c86480d103d280510086d0008600610b66426507180907491408807a0fa11020460395400115031a07000c41d104d41400201d10308103004211000701d000300034143e89100003900340c1c028984001d002d000b0079a2003070441090f483e44904940a64080d40b140358003807404200003400d441c2801116102500814820010b94480c0b07444140451802511142c03030b655691400117410083e174101900510400040c4582131100c16103100070303a4010340254942d142c44083c1985d0900c0151000301b001e41c0b040c80080d80001e05003903140300c891013013803e0707540c882d110b40d00c01025003105507004c0400d40c11441c0116095608400c50044180485c009804100a0204054242c8409900140c691621240041c20b994850844400600390 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 425277356 1250 425276106 425276123
    0xc020a0e070c381e10030305030c0c010f090606050604030510090203241504060b16080f04080102030a0605030d0207032a0b030f0106031a060c1207080324090601050c0a 74
    0x1050b0158507040340c1c242e411044298940d05066041c0d8004440d00e40f203140b0001074050280d01c3c50b0340c2108c0785c0d0b1005240880002082c030070066905c5080c01031601a031041e202c0810410045d041020881d0007aa2041c1d2003a2000c001c02c00000c0d0780402c10ba403190fa00450001030f0f404246c0017090414100c18894685100120961854a03844810140c028001c40c510045000c103940c05200440700740b80155800b8001c203029103a041c00100311450640c5101d019882d00380380382c251082420360483d0b045060965004002c01102c0201c0344100c40051004400928410400c0800a0b44601d05400f0140c690481e829601c400000c1030070341440f50000e00314032440b10f20b83d2200114099081501e2210901c000f2400002701035200f8011108540801c040303003458002e0702e504215280d40485c0c4448814052030601d14040500800a04545800f880c0000e5903031600e162120016180480b0040d142114031070010410b0300d882d480113038003400031709020303550341810380d080c51901e00200030040c41d4a1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 425278606 1250 425277356 425277443
    0xd0918140c0403140111090f0102070e09010b09060402040b0301030b0411060a0f0e190618030b070f14031b16050d1817120307050f07030c020a0e070c 66
    0x40544002c10072071340500d40c641814900208040d090743e01c4009000002ca03c14000310b4400c1c6041c81e54401c0c200300c1401240ca80ca6520300b02c1038503a600c00c84095121b80d540701144851420007200041c0d200d50111400c6103001d042151060360740c04117000180a038000d00001808110309100c00310500301c1c1c01080383c0e03100c03070300f20341d00900410014030780e00000b42414008100a040104c0714002c030700311000003500c4c00d40c2021004c880c07100c66210480c100003c445000808120154a003a02550b0035507680c2c81d00e5400010080d000321940e0394901c000e400108104501c00e000d000c080302c80010300d2950540c2e110082070010003582003520000c2c003e4000c0d19110b40055400c0b0400b0718641200c04050302d035599452400359443c1c4803040d0040010b410000c5a44c0ca0040310b01c0055900c0301090074080d0400000c11001440c640008808602040031103030b90405618120300850000c2501c00f5035410a8602098010000d050800c0000d00a000310154010030710003074115007421030380c0c5214046006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 425279856 1250 425278606 425278621
    0xe010c174b01030c06030e0706050c0c0d050705011e09053604060501090e0a06090f0c030f0201090e062d0411040914090607050309070e091b030d091814 67
    0x1c0c1081c0710440f42840d01c5040001e50500070301800904001d00740241038a9464248203440540c0b2044803404140180d808401c1c0d16501d00d00415640341c010f0008245c803508003c0050480105540340600421042c610912401c0c0e020040030180c8800765504ca08200090540140340c1140b1429410426200949210001c0390519001d210b140038450610403a6030340c01580048850f202942d0b0f4058000c21409404144180c1000c4c1082d803248008020124854895000d1405941c108607100e00c0c10044100a560b8070600d044094810000a000a03051000008081d400c40d050110000413408154800c82c104903c40103011a2014000707002d00040042080c1e070540c0075000341d0608030302c1d112140110340c42032011790b44100f0011004185544a9100583d5250802042d04d41c071445010300114222900215050040d21071900811a2910605034410716a181d000d01c2d034001d5200320049000242c0c400401012107641800a101800c0062104009400d81950186110511030148030b03e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 425281106 1250 425279856 425280001
    0x19020f0a03080d1113061b0c060503010e061c12020f0f0a060e0a0305031b0d0903080403030509010516050705010f1d06090714040b010507060e010c17 66
    0x104802410801020b08406044e00841c05040803080c4a4842580207012a9011700410095116250001d0b01449000d50314210000c506400c0308000072804001007001c10305104400f41c01010482e40f21005190354103822982025948024094841e10087c0d0700d92180240003141120642c0401d543c94060804407099035406a8081102c110740b03001c0d40c0104842000c41d0140c9002d40c90741d1650b203075460348036420012908211114140400c01c100c4000c081c030041c404c401d103052181e00c4000e150f150030305000c2c0071201e0061904100d641403808100c4503c01d40f140c0d00c00086080e05042d0f40710000b504045004111030040501042d00d445070062281f005480c03e00010141441158655920410015141c1d089842244502542c6400c910306c149050307080201096011700d4aa0b0800c1e403540c441d18140c81000300b40303544c0c0380d641c2d561040400e50b1150b210780c060103c6200205841c10007640c0c074814500032082074103c0c02e01d01c0c40e21a404101054003414400c40e03d00c0307440d100b40781c06c0490044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 425282356 1250 425281106 425281117
    0x503100209060d0e0715030e1b12060108060703051f0e070201060503060f010305071706010501030911090a0b150a080a020304050a0507031202061303021906060b040902031006020f19020f0a0308 85
    0x2200c1ba00361040029032281c018041c0702c2c004880548052650205513560a20041e48200c0d40215401117020014004104003802407200a004101500701040c016003254005841e0500705181c14511000c4441406010340450f1a2000c554603aa41e070208100d004050940115030315000d03010500155424601156060700d0107903099076407480e9100501412828201c0592000343c1001004010b1580260b03c0440282e0048500c44180a11040000c0100c141202e212000550302d0b1440035081c1041c40011b0b01000032580102e01d810000d02002d004484000e081610080c1c00200240800c8800e00c54040c08503403000807180416100c0c80c0280756424210079410062084400140400e450000d1490303a0a405401034141c103800c2616218082010364030a0f604941c490200280700c0f500080248014400c40d41d0050b102d0402510b450100c220513806203003154425046503042c04400301d6844504124a00c129041e2002440421880e40071420310780d03071211051400005110401c0300400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 425283606 1250 425282356 425282369
    0x8060f04060909141006051011010f0c0201051f050604032009180d03140708150916030f090809060a030b060d0902100801061e0c17040513060503100209060d0e07 71
    0x43c2d031702d00c003512803c0c01c4601c1803040c1340c1c0c400301b0010001c03441800340d03800c10a1403600000109903801c82c1c2c1c106078107841d00200a5030041c0e550b0000c100008982d042c074602d10750b1140c10380091311403600780001c2e01790160780800380200c0b14665113001150b1548003a0003100c503000c2d01c240e040703140400e070b40da00304074444d510070b030003030180d000480c3c0741c03e20a101e100b0b00d1408004200029840e40c0030111041c1070000c00b04101d8100c0030003140781c66901c510f4030510904030380440c0600342070304a20003025107117660180321116003065110400200ca4406842c1c040000b1b842c460784420051500310090f211801c25590040d000082c040700f00d807007e80150340414000e0300c11030403502d8405802c03141903100344030740e000281c007019148041020408090104100070b00d82250141c4040e1140024042520040d4018240000c1c081006060403421800401c20b0844108401460400440c0c0c07100b8114058003140c41d80000c01d011300e9903400040d61518544028100807004251020380d507030700ca880c018003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 425284856 1250 425283606 425283613
    0x2070914100f030804151209050c15030907120f0605010f03060e030306010f1b0510240f06031e0504111212040e1314061902090108060f0406090914 65
    0x8141c203141519040102e0f9131003114185014906035a40a140000c11450300400c800c620003000b000d1146c1c064450024060005041000303440340070000716510400d5119215142407041102d58080810a0411034880100c40c0500301c03000e141560440c203a0360801084c0e83d14000022414074280c2401c0700c00c0d40c0c1b28040400c0b03c07501c0014050398a0100301c500c94001000030710720030071445c803501c62105000140a4044055146595060f003861840c007040364070b440c1d0741d00c900302d648000c44500303800b44032100108461150404007512600c0081d405440140340d2524022004c4841c0c0321045805100e182100b000903007018680f031146074403500c1f44644035800802c12584009130105907045001e450340341e0b46140c01c1c5820050900a03000400b4066042a5045510040340c40d403c02c1d50740e4208a903000d0b1000e0f19185d5400e881e03100c50801081f24181c41440355003400c0c1d8200191700d810075001c60301c03078580b8400030001601512154104176200c5040c48a600200242032180c28a0203500d041035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 425286106 1250 425284856 425284859
    0x11e03080c0d0e090f13020a0b0f190908030a03021804050a0207050c090c0412020303070f050a0303050f0f01260706020c01020c0612040f0302010b09040c0e090604080301060f0207091410 82
    0x20089110000d42e456011707000c015011403c04040c071807140c915180b0180c48005410340d200981806608800a404080440080c1c002e882002d0300524400e020b40c0741c100b00584a041c012120350728003901921354149a40040c5c1041d240b40203001d00291044000c200740035078544144041c1c0a900002800c481d0b51207030396034020385480d05080c8148501150090941000c3c500442103849c0b01401c1400e981501080101c0c0c40410354030500d50382168001c2e0000d01000c49680381c01003c540004007410003e10300c0350203010043c50721a104a04403a018501313020a128190300314468800c40080200e03442c4207808000030308603004541403000f54002d80a81d58144080310510034503210703000d031907240440032000043c0090751400d500e1007500e0080c400043c250100e500407071541c41040d1001d03110800c50407410419201507103601136000c0c003510301030a507500b01a5240e400c0360006024103024444007500c6500c1140c420440c0c2c40c01001420401c0c0070400800c41100c2910300181d68404001441040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 425287356 1250 425286106 425286109
    0x31b03111e1c0308090c06030c0d021e030118053303060726060f1207030803040c09050a090c03140a06020304080c060603241305011407110106030308011e03080c0d0e 73
    0x307140c1003801c80600854a159a00c0d011100356510102d2b4039005203900b401040100d42510228810f0309001c505808c0d0760354106003403240100401c00030180b146050408020351500c8a4026100c0f44c441c890300c83c001c1c3c1400e100c82550b030144609416406118131401c00c807840307034484140c42d0b141165204807035002190882d601c405c1e4000b100e60741d8002e5500601b80c0200c0c00d18170031040c2c02194400640e0f110075225910706946503c1601c0584000500210034030511030329228094116019001c1017290848aa0310b01c7c2205880384005042c82d100111409400c1005106644442c2d038403c90842d52031409180081c030360380209150340018800d60000443c54140007402e00d00c480260b0514181c0c2210700388925541800080590080700c82a50a100000340240645201852582c404251341c0c0ba0015000b480c2c0c084007401c1038140d03818000c1c10004a6002090325064078403c054412400b41100030300b5a5100c91544000c010000c0012803681a650105004581e4292070f0f0390080d62001c0c010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 425288606 1250 425287356 425287363
    0xf27060d0c0e030f0a0206070305040b03010f03061a180705041a0d0506010f021b01030b120109020306101202010e0402070c08070e060901030305041202180709031b03111e1c030809 79
    0x200f900301d1035000050312000340c0b410741f0203804400e201b171411510307103030301c0d81c008501d43c1d00300382e11520701c0d01d82c42d503801d004010480c01440e90301074080c40d881e244166070b240010050703440e1000c40c64000c541d080101e09102c2c480d00842e00900750b58192418032509600c0501d40303e0b41f0025214010b01c4c07070100400c065600c1040c5601206605500404820300e01c150180e07030341080792664034141513a400590050361103070f500181008039000000180f55240d030061505000d40103107641c0d17034a03c0070071041c441c1c168400300c1600c04030340a02c0c00880340103611001c07030001c0c8214100500360a602410000721100e001504000303640c2007180105607a1509014811462002e0000801181040c802480180d519642e20750f0708500081504c20400d4002005081030081135507260f002400402c41441403010720f003528002511640b4240c2c00a81c99034441f245201082000c3ca4400c0048841c80d014010000c01401034544004049040e4240e0411620421880704202100071604600c00201840b4010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 425289856 1250 425288606 425288623
    0xd1d0301050f0601050d06081608060703050106020d0f180b0a1205042607021011010c020304080706082a0d11091e0a0801020301080102090103060503030f27060d0c0e03 74
    0x71842e240e0151510401901c1c1c64105250315500541ea60350001005602005258980c1041d2142881e100d030820910a0601d07000412040034541060f00402c40f550740000d100c404c0031083e03d0300840030100030340b0440728841c1e50364050009814450020440710251802099102d01c540c42c0c81d4048401e4005803030903a43d00312400741c5000440b00603903000301c07442c00700c0c41c024a2106000034645a000e600282400d4219150100006c03440820000040000d03c0384802e6007c80d400154141441c18500c41d0b581c1006005a604000e030400c003140d001258030f0386d0446004040c0c0c0210b903c1d90b043c040030b503066400c40c8005a924078140100700305c0b000307112000c5070003140e809030801d14101000c110500800c40800550b13034110b075030b1243c0041e0010003840954046c082200000d41c0e140401400103080e41d000c1e0300428400e40040201300c4460141c90110341c04224042c01ca00c0c0c0b1444d82403900c030700c0c40d40c03524100c641083c0300040544240d2540e51114414001030380307841030b5500b4240103040d9141c910 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 425291106 1250 425289856 425289871
    0x1170105061801050d0f02040c02070521031e07080403050d09060305090a0209070e120604231b041107030f1404050102031c0e010e1c050906030a020711030d1d030105 73
    0xb49401071001e400e000c40d10303022040c080d480001742441ca40c1c1c0481c040740d5130f1444800041c0c002c500d0901c078510f4403c00070905413000412420104d075032652035079101d10510041e000d0f030040d0994085018140141038070201c5400c035006a072619568140562038107640c0c2050030000b208820086100c5000c4d00c075040c000c016607001008550702c3e9a007407001c03111015007180c05204081c40e044100c4c0d9105800c01040481300e0000c0d213000d0800b80f600b4106070780401140e80e548129058800285000019801281440e6001c082440c00706d1001242c000c02d250880ca00707000701c0004814060540000d08099606400c2d41d90045540c04800660128007907400ba103070051f0402c004644061111404185500f00d2034180001c008961030038503030031505003110301c20554120117032030b5220380c02503050327038080300260b041c60f519107184e110008080780710081000305410f0340402c40500740038201d20382002540001d412101184403a0b031026240d200c02c50310bc86d44c1c03000b00300000c02d02d07400c0601030280140d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 425292356 1250 425291106 425291149
    0xf0618060c03030f0b09011e050607082205031203090f0a15150b03010603060509090604170c1f0b030c030106050603180f030f0d140708010e07050408060117010506 72
    0x1d055030b08502070403c4511902e500d40c3c8032610107440740e4690504c0c50013030500c109850b101c21690040700b07203061003540c0501d10900c010f001d5900030900d031031300301c600c0708140814007846283c4001c910816074200f070700815058402d4182110ba146014070041d8081c0b1900011140c46890388090035a031080400002400c141d800e100c00c2c20000b4160b008247d104041d544c44002d180d859072190400754000342e00c880c000941720340040025041c06800f1503002200c0340040c014503d040d8850050070211180384d1081c0070070002c4c0f4034282207014080c002000101040762017160022142610190000341e10062103402407011038580352805200d50003c4500280515080d41d03a985c10368808040000010000d40c00707610806540414140020003281010b08030322520344010590607022940c140308522840c204000900a00580040b5068110f480d13140c2c8250b655584c07010100d4160041ea440005203200300d0001003001010344208072110003110008000c0c95580703004010281410701d41003440701700c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 425293606 1250 425292356 425292377
    0x2715060a050d05150c040b0c0303070f1d0607060908070308060102120406020c0d06140c120a0203060904060e2805060907060c03030c0203120c0913020c03091306050303040f061806 79
    0xc0c986042c00e42c0018128041743c00c140e6140028222036000c540e8510321038100004001d0040e41014024500440624000d04112030b103030044054050390301001d40c820301001c5030b040c0030410750750410700443d6484000d103a110840751801030502141036540030301602880c6024001c0045c0841075400300d543e1a4028416600030909203c1005a0958192103080d103030046802c0d80b0030f1154089024842014905e0f03503030340c00840302c8426000007a0a054280d401002408450b0f076521440399006900710000240105034200020300e095a42d54400c071881c08524044d2841c4003010400d400924050700035101c06554074042151904698005d85000c200d1442058010030703ca5480f2480780980c60046074038104003804040038001302215040c40350b80c00001c103031203641485a013005d20307040e03201d1043d8103061445801d241c6900621614500031110b003004c01d14000c806400280007040098140c3e60780e40d488250700680020240913081c045880790300740381c400103000102d4a00716600c5075506034806 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 425294856 1250 425293606 425293633
    0xa1106091b06090405010f062c1c0606060201020c010509070f060f02010e1603050c090106090909050a0c0816140a030201080c1e0a0f0e06032715060a050d05 69
    0x403070818240354000748240030b212001e80b00ea1180078082c1201070801102c1a2810100800d106245104442c0d041800c0015a5220042c0a2200071040046580303c1004800d655100c2e4000e00c2000d02038291800c00c5c1002580a40660040000d40b5414009001039a00c03860700c03641d01c207224810040140c0fa400d404110305846200c80026130b498610000c903d01d03408034400740c0703003006c5114051b0718400050010000c0160400801c100507800b44d442244540c074100340603001402500c240e212081d10380054504100f001c0c01201c14884d03100a080d0516a207500e0b64955501d1411844a18052101d001050b40350308044089410300340109108080350850b401100c10720b5015100d880b4255007032007045c664007400c0f048011a400802102d80d1111041c0000505040d55034003400700340f110b00d003081030030b580b01c480499030f0090200040000030a1041c0d40400d08150034521613a9a0148010740c24001603003450083c0602003c40303070404015150000c0081141001384d00400d19408500190b403c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 425296106 1250 425294856 425294893
    0x307030203040f141c02011b180e1509060d0f020634060c0e0303040306110910031a09090c04090302011503030228081204050a15020a110609 62
    0x3242c880c04450784034615540c0d40d080202d0b9069a00e104540044081c240c100c502d0310305e001280c003604e20003400320300c2c250250b281028290b2501242001a00e040310590000610402801019040c1d02d0311420300c1c1c03202204032041013011056100e1205d0a01103825860014181d072400754000c081d0780c8900000303a08002265010040380010410102c0c1c200c08403094501380040c9007403c1d88942c7c22680b800d0300d000750451715144a40d00c02e0040c6010810001d45000090701d003501d50001000441d080b420f11914402c0c0140c0b400715902980c08990803080f0340d8190000078211070580141c607001144c50042184c55501119250025841000207050924040d00300094540c002c0c00001581000d08172250303010780d01d613001940568021454200f00c030130310420184050a4044103148589480d550300704230f0b0320450f52603945610100700480c0601c40c0070310020091540c4075403550071b089445280b82010b034000389041e40100d0054501c60503000c1c030200f0704a200c5e40350340c07016103042030315604c04110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 425297356 1250 425296106 425296111
    0x9090309011e140c100b190b1b070b0a110601031a042102030a20030f180301090f0b07180909030509040f2f040303320d061202060307030203 62
    0x8100140118940072104040200040c1300940e0140c00e014942904038810340341100142802050880d8003d20824420780e10002640c00b102c00d82503a91706a00036404004882c5844004a4007a01d60000780280d60300740105400d1840d500c460f00400e5040041c10b07220030302403202401c03440440c250460860203034411180d00c58400c0e00c0301d055504210b159200c4125541c0c03038210159000081c8011010307000150108209200640c08604180001c0c1e09502d84c003032071383c201c000c960000c03601d0300c40203203e400610154400a002045581d085003840c01000d82c10760401c3c0d407003800007004100c80d64030481410100705e00409845480703c0c6080401401040d0342281501000340074071400302d05541da40544e00c0710f440029800f0408101101c030342500c08505405a483c2000d00001400c811034460b03007580d0071260981800380da410041440d070003082c0014048040441420448400122290f2014002c440380700302c010058540c9030b004001c00ca420843c000b030b501c00340602c0082e9040f803113a00110b5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 425298606 1250 425297356 425297417
    0xa0813020402211503030403050d030c020712211b080c01060e0c04150f12150b0705010501150201060f03020913021206010305060a0b01080a0510080a08090909030901 73
    0x5180407000450b00803d00e0711510b41041c04540d0b0401e00681403142c801d46203251504401441c9403d02e590354096480922810034800e0586540030342280e0303802030000d80b008000c01416020741800360300e003a508000f07081c11190030f402891040d0203c001d00c21b801a58140c82c600c1c011201180140d152003d05400810400303146640b03030400800e8803000c000c003c40c040c480d10b0003016155400e00c001c03c40940300488040e0104805008092946944920111036140d4108000908441d00d94044101a9480d401c00400c5000020b5000e04206055208504070780c82d2603c0c1c4106075010308012800e80d4402d119078404c0503541c890078070252a0118040e0b812102190800070020020342c042180240c603007a40c200a50090b80042050050074803000354080409a000c21030748983c8070000e402c0920142c0701d031803040d5681001400b080d5030180e801000d009258202c80340e080c403c2c42e201c03440782d110b2101c19001b400c501000c034031001d000100741c4135262016100c15200711910441c3c1e0007106040c80110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 425299856 1250 425298606 425298611
    0x7020312070b10060e12010608030c010203101a120a0f0507110706110a2901030507031202010c0801090207050c150a020c0d170a020c041b030506120d030b2e080c0a08130204 76
    0xa27281d1000c00c028840f01070b803103002580340d107080803180d131466101c0c3c0e2041144662010741d01041c054228111003100d110b40c401d0f141c9684030703c004c002c0200101c000d460511072600c2c0a2010007500489000e00c4d00c940c00044600302a00c926003101d040f0454601141d65502c8002c41c1c1000507400150190300d41303464281101e03010b01c02c83c848100f1102c00e92043c0c1d100d0700406ca05100303121551f1250403210307400c2c2c0002d1114101c0e286c401000390300144a6100d03011b07404124241040740c203009146408100400e605580c1c1d402d440d000d04d482e031101030042d001d8400d000a404090400040030455140c000800d42601c060708018071216078042da58120440c040e081c80c0c40260fa076507204d840c08520341c01c070490280c0041d03400041c0440d6000340c250f41c0700e10440407911441480019404420301c10b6481d012402c0d00c200c1021031000302644030030850403200d154492040100d0092a01070080740e99685a94a0303d81080c412054880c8401d048002600383d4001601c950103604241481032020307100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 425301106 1250 425299856 425299859
    0xa240302071a0906070905010206040f0510060605090f18043503071d130c090b070f032c0d020a12060b0109060906051e07020312070b10060e120106 65
    0x2aa10082d005900b44404404500180702c20044104807030750b403081032400c04100031428100040d55601000700018034490b240031398801000f9040c4000d51861043c003405000c5c070354032441e002e443e07500b00100641c01000c4c6040c00701c0451800d11040104855002c254140720b407259100c0c1c0070748006144d062280c900e03603200c540c3d83d110301100c0c00601034018018440d032a801d010700300418240042002e200461400e03940c182072940e403115008400048180c001842007910310301910b00c0256035019582140d0302044136000e1100b01d1018000d42c0c8e10070f6031442002201d1207084039960400e614102c4440c11585016103d40c280b0001c100d010302c0c0020a44092180d42d07803400c240d62016090101c40041c3c844841da422945c100c59007074054032441c140080c0d180c0c10074400130054084c0c0581c4c0c020b42c1a0010034080c410031400210313080150064140c07250a0b00a132690051036020005c22181d8044180000e00c0f00034295217668259841561400e4581c00c1840400c0a0744028040185040d56190300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 425302356 1250 425301106 425301113
    0xf03010305060901050604050105011b11030307030c0606050303040e010905130b0a0b010e100212090d080c03121e040210020127020306061917030408070608060f0a24030207 76
    0x14600861141c001880c151521800d0b0324259140038203454012800e120060003240e80003d000c5240c4440c902500b503031b1490904092011004448869030540030005428061651000b41405c6050040030103218481e9220b080c03550328442c07441802c282030a10b90050041c4284c0350086600901c80c414403203050070b090b868450304a002a10840d0896907541050742640d40c0000b4005100c07001150300602c040d9194502944550807140150095a000140a003503580c40c100202d008179000360780e417522001d0003006a42ea035803007280c503401d80407011030000b6079440e40c0040010703c4510803003900060f0384940c0d0a220204101c840030205654a8082c00c00c0c1c1c0149000484040c00541c888030108202180180360518201410503406a400b0b90480000c0a100048190443d4412800108146041c3c140c007800d6014940015105000340307500000d0f03041d405012540100c034119031600310003500c0000c00c03c0303858407485080c2690066084540c5010b00d54070701842c01100606001d0314010040d40c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 425303606 1250 425302356 425302387
    0xa1e05030d0204170a0308131e0501200c0c0d05011d1b0105030f2a0d0605040c020a020d06020a0e0405310c03020607031106090f010b0604050a090e0102 67
    0x16071403565010504100b8848144141100784511030040c1154090300e4400a20003103000388500c08601300e000f1043d0400101840802511026001e025510100c03854114041d0490030740301441e02c07540c07101003000c02c4041d00449088082c42c50041820140d42010710a5456101d41e0550f425503031807008210540b4038200520b060308a80c2c3c040c011041c520965058135100c6207201c14100315040c400c0041d482813880034140c00402137201307a5011f00c59140d98007070102d020402c12610b410080340804c0d0b001110f8201c82c040c2c07001224144070a010448081780d48606030440a940711140c484160046400b035401001c14071241e00d0b20208040181e004241035400a4030703206449025018200c0841084240c80030786d4500c8502c0700d200c00100d54885140381c1c06a408042c5c41f810740011184101030040e0074280c08110400c09803002850701074a0141c40c1c10044811140350350030515041c98a10f0080100c3e429107100800e040d900c07905041000c0c000340f101100044c00b6650812007a0040441c16 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 425304856 1250 425303606 425303617
    0xd1109030f010b0406120f230d0305060103201206120d0809100612060c120501080d0f03060602030412050f01090f060e060408190c020406080c091006020a1e0503 71
    0x1000045003d080c08010701044910940c07005402c0c103001d80b00040000c01e51400b9070080d6401034114240b00d4441c0440e90082c113141e00140d00d10744990306440070308036015040a8071602c3c2c00d0324100000c60b4010342a42d408010050b14080d4203204020240e40341d5056007140c2c0d00311001410340034a00d000351240e03d10f80021107240c14045124441080050041000f020b00c811403012418852a45820100f40001000b50320003403545440c0c41000d15141c0c4141c00c071014911801d10300b030140d541e45162441d01d0384020341c2064009030038010b0307600c820fa0003406800c0841380c056000758034180ca004c80d0030b81a1800d0270000c07601401746080421440d074090056510150013142c82040320344082c580f190407940120030340b10080e0090340800008c2003044080c2c0e006914101c125500300038241104440210701140000c0d40a80340070704c089101140000d001e01e06140c191607010290300c2d509141805012184503c10050b4400402280040c01030f035031461060b188100c0f2074041034130301e0755544d0075030b00070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 425306106 1250 425304856 425304883
    0x1c14010902121014061602060301030b0a0e1b10140a0512070c030f0c14070303050315041a061303061a13020a02061b04090212041103120d110903 64
    0x80380782002c82030090b800300e0b00a1000399003105118074001960081d00054075040d48150f2010520a0901000d243c10801141d030080210360740303607101d240c80c006240b02030314041c1000d4944000ea03d04880e0001e20f040c10b04242e5900c85003681c40f038200300080f0203541c100301420003c1460b100e0341900c801001900c01303020583c41e01519485070454004150000610000800180a0507030010030780000649a03000d295140000e03203481e00f8141000710002950340f28a9512a01d580042455480405980100c110300c1c1401d8900c03d50200304000d942c90707200440e129200c201294483c620f840c80041240c48900f0444540c11170356900d400d41110901d52005048040c0c42201440b40e14080100e03001110200104504183da035040080d92102c0040ca50b04031400010b4024101491f4141520024200c1e00303030955550003010307030401c1c3c1c1e050161000c582c40801c0c20100c5c1694a000316040c030800d080c0711315a9080640a0600340090411040c11208005003005040f0541c0c0f014802034166000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 425307356 1250 425306106 425306111
    0x3070218060d0519020f03030430020619020d030227010c080a090503100e1902060d060b04031104020415081e010e04021318060b0301021201030b012301051c140109 72
    0x4490040c1b2030ba02078060700b424800d41082006003c07402c0c216001e400031050070748000d4082500203c40340d040c1200300c20f01a5000a001c1030300080d0500c0c2442c034014002d0254256201c2c84078195007a001c0c0d00501326502403001001004030b120309a400345158000005241c0b0158001d4140c40740d003880d41c03116011070300050501c2e009010386c0c2030402ca1440100c0380107004002080c440a0816220b4002556808466002c0c05540e025540da140540c0c80d2411b0816040003c00c3d60340719180030310b601c01e00c022500c983e00098100000c4c035052090350100c0302c1420014441a0011004444441e0300600c85103d00381c149449280208032049000d00ae81840c8103ca10181020300401000f000039000201505040c8640b500341408401c10038010b10b41d000d0004542407aaa20001c0d0281c041c040b46102a4072a03071000005018503c0700381c0c0d040714104c0300e0010040d218141100d0100c800c00d80c103240070990401014001103c00a4004010850743c0d000040402540c02202d0701c02d903003030348160301154 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 425308606 1250 425307356 425307403
    0xe04050307030237030c02031f05010b070206091903050109080a1101060f060c02010201140f04030f020705060301051309020901090506030706020a2a090e100b0303070218060d05 78
    0x41d010050380c82120b040d108104240421044a040c851600d80c40304213003503411080e140c1c1010b0040351048a02907004054612801910122003110340001c40c600040030706180002504072461ba007225610303900640318034509900702c01400790040c2c100403886c1c0c1e4400c41c00000400300d4020310500c1c003920b11494900356505d03481d410050054060f90200c01d410b915015080080003540444142203807100e0510786602c202500041c1d0060140700076850944520808110140c003400a80c2882140f1a803261000c002130a030049968131994090383d0740001c01000140b06614040184410110702d850000c514036041e81d0109000030000c2c0d001250068a40e000c0c40b1052400380548000340c042840244002c82e0182c903001042201071480300c41061001080071003070b43e0178055400c0542020b060a229007c000c4e1042c139580c020104100e0300c4907160529912a40c03401004440c00c40e44c000b005003034040c0200100040c84100900b116601040040c00c400010303400348941c03004000c81004078004030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 425309856 1250 425308606 425308613
    0x2130b0f03100b0c1506010201240501090b0301080606010e0411070302070311100804170c0d090614120615220302130203010303020607032f0a030608070f0605130e04050307 76
    0x110650840801881c0c01d0040c100644c0c0b0014103201e0004080240102c2a101d80c00141d0040c460b80ca040e100c041d15100c5001e4420b01d00c2c021039400c4aa00303a0703803002c00680d1040055000c1c0800e000301c4800f41c000c1008200c1540c456104480b90f044001d00005545034002800002544807800440158000240030010701c4101400316040a0043d6028200e03402d190400614554008000620071072214085680002c035400c151040022010100d4090202c00c00d00500402c81c0c6100d0600020140b18a41c030001503d10140c0300c4810550389100780359240c03101040825212002d001401740c0b024000b0015242058084105804890b00c0d4801c00c00d003980140706e90305540010f14400700c1d004000410010342c0c005003e0b42c2c4840c40c0d1800141142000d034042c82600c0c9462a240c800c8203c181001e005c04014030b000b0b02ca941c42d59102081500e40d1840c40b5515009203214100d02d0201c01002001810300400c003d0158000320310342805103503190111006641c00c141e0f4284c07003e80c000300300c0c0d1040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 425311106 1250 425309856 425309881
    0x4020702010f0311120f240d02090c12100e1303140d090605010611010e03190c060e060420041506050f1303051c080c030103170c06041217040503070602130b0f03 71
    0x1581c5ea40000e60442e040846e011a01c00d02c04008d00900030311300040080c0c0450419400d44644004800300f80080c0d0400d08082c0c03c00125a01400d126064a10040340d40c0600500840d003007283d15031603e110380c0e0000c4400c480c03160001100100840d480380c08181c005051f40c41007034041c1a1a45a11510700721246034070782107409802c1d51401591080185114580d850403504220031050300d0041c81441c910b241c400083c06074407070b1001c070381d120b807409010411224010541c070007101c8007184540d03d1001d208000c10b80c0c509a65407000489040014891603200304001d04080c0308500c01e0701d1800d106100d25400d00c2c12164810381d810340080c1a007804000c205a0004000825807803e54107900300000c880f0050b10042c070000b00205421071141d080002c08000751864105d0325000e0b00c0c442e28040c14030380d102403510034520000401d8104884080704000c59920302032604040114101065076441100a5101a8200c2101107584100007041030341d10000f06106419038080c0d0340c032401c084405810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 425312356 1250 425311106 425311141
    0x20f0d0f0b0106082703040b0f0c0a05010617010b09070e190b03040203070617060402090a080303100e0c0c06040206070c0b0d021801080601020a060504080d0e071404020702010f0311120f 82
    0x30f540f4011903a017040c1d44000b081d20191181124415035404840700101c9240c800c1100d6101c5078000c0705a00400c0c44019402034040364407420036510225004404070f400ca0707080d182c107140d00c1071401010400481c03040100001d180c80160180c04400b01c1c221071140480d0301e592190038036a20000410085060038403402e00240300a051901049200128030b401c111381c004c0c10140a6035000c20380c2e600700e0744c803000c1040c0180200c1090725602c4c01c4c246109200129103024090940240750701003900d2450311811140c060b003865002d0480758869908004080e800620195180d005c950b1010641c111502d0042c01031207140000140d80e040000300f00c50403449450101410700001da0200195640c0104006210a9014400094513941c42c03901141a018041c030207040c1920b030110030003400600060701d00590f01e201c6500a80c0180450411040c1e00c61520001d00045500f105282810b000343c11151914210500213402d0048003054040601c2c42101d14000004400060028081e80d8424034607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 425313606 1250 425312356 425312401
    0x5010906180b18032502010207170a1104150b0c0d170c0a140f0406020c030111190c080d050601231b1e0705031009020f0d0f0b010608 59
    0xc144100d80350101d0340b402c010614060180c00000812007050148101c1e191600c00b4000ca01144a6416040f0502441508100d025115480000c18140000f80000e038412040740c00403d4070704019a80c02da1446005042c1c030760002c2e01d42216622103d1840418400350816110203500c8140c02035805262001d034203110720502c00e0011001c11980d166402e4191720003c28031200d50b0340e0842c00030446109024607410728807814040b030b03803010340f02200000700210b5131194215000019030b0002c0500701e43c00500801c54100d030810170301c9400f088603440000044201d042c030b0704401c41e03551200d00c0326500800003004455520305c20022250f81250791841d8001c5d40c2842002e0110040e400352800317115040190164040c3c0501ca803030141d030100400462a00410813215200095840150b519002405014803d005800d607003171441c0401e110712800c264004040b01841c1080e0800c0c081040ca01035405c0e900500301150b0395001c1500920786500804083d580c00909160a54082826005030740340030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 425314856 1250 425313606 425313641
    0x40509011e0c0210020a12090c17010509031905070503070c0905010b03072c1c03020c030d020718230a05010501050c031b0327130e100903091205010906 67
    0x1d4a002e6070000380050200100000140d450f141c3e844241d55050100c030541480908000e0480100300d00008503208907a2030448607000c0140c4018214281c4c0c000301e501026683c0184200300c0b503541a0a54995015158182603160a119072101821588181d0341910001d00c400400c21000106208403401001429140b03429420001c1004008040050f0081074683d901c818080c110a0381c0d4490600301c0c0d00080c03c1c075076078041b000403075041c0c40300d810030135030240c00b0f80c0f01c03514560b040224884000d000c0c1540602000f50900701104190384d05950220380c003598403a104841030000c8854064242d6042550b040710740b51030b50901060710341c160804c90400206208400b4254400030903202d2400409503050440f141032079096246024174504e0585512174611f1205c952140c0d01c80301c0034880340a541c9483d0840034414041c055071611131090240e540030a600409030761056112000452191402c01411039450980e0541b10010300410350303699544841c0401049414401c0f0317100901c101480 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 425316106 1250 425314856 425314871
    0x15140a05030604050a061d0f07030b330d0b030d260408161424010306051f06020106060306090506090103020d061104060c0b07021204050d0c0302040509011e 69
    0x30600d01001e803030240210b4444000c22059280c5030056009002c584285020458001c44148402e043c01d449164400f103102d0f001c1490240701e07005804903041c1c040d201d00084048101070522009034100102590107501d004404c60404074030082c08549110000800d000301e2680030581800e00050b00c01d014414030300f0a010201344034000c03006800c6002050710110b42e880c0e003841c0d42d29204904040100c000341c106103070700b08600700b40096451808a02160000c0c00004c040303140c0000c50303886d00d504210342c2c10010400107201d42c1203694415030800c034140c2d00902401702d9140d40c0c55260098005070b511142c090005a1f450f1059a00a00502ca41803110b41002c9012981c40c020600003c1c0c0511840c600c00301c03d200c0c06400c0141d1201c02104c041c2d60b41c69883e0802001e03104240d00880c0d09005080105490364400212a401075507510050362401d441d080030005a041200342c01c44030780021510001c050380e91403144601c03c10f410f23400411380c81c196400802c0307c8003e01002d11510381c54a1034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 425317356 1250 425316106 425316127
    0xe0c19030b09150604151e03090b040209061c030f1b08070b091203010e060406080609060a0e0f06010e01170a0b0417090d060c03111809041a011514 65
    0x2001d83c0c0001e500c10541c07000c3d1541d03a02280b528030a6411001d410340e0b001c507070819900e50003502c0346801c03250108001c440c034102620032415a0000b010150401042c0000324025140c49032421b0b4120a00401c005201c11003c03248800c81d8102020503001308000c02c54140b01960004451b201c01290792809004202040e51154100d0141c40d4000e0f0182c004d40002600ca100c040010700301004158807520384a60b900c90b80c0f4030250208847c0b00740510b041000010b041300303001410f54010368104000e04204c0d5034035010000140007811b20101184610f810003181307441c3c18003406018002010a200d179660400201c1a84502480c040004a90001843c0c1012500c1401440d812661041e100d02890fa1a0962014603010700c84003a80c0c00341500380c2080410640c0d6010b00200c104a403001d01013903240d43c017200b80ea40100d070982006110b502c0645052450816884d0390710a04c5405503903038418103003c004140c180d00760080340b045014407503c0d01005070050100150484030181d620b00d442807100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 425318606 1250 425317356 425317369
    0x30b040e0706170711030c03070c05010f200102041e0923040b060a090e0a110105030c18030109060204060f23090f0a0315020702040b0a0302100f020102040e0c19030b 73
    0x24040f8211551400200700e029224050703d54500c00640c00f202e480e0f216001030a5100e0f4055002103403060449400001d455014034a25000e100c050303241c0c250340c0850b100485a004204104441e610355080001042204450644071544060b207010401e82a0802011030201c900800450b200722090040d2040b840d00d205803000c0c1e1242e400103010f512510b9000c041041e68029421030314026081c0b0320000c0044400260340040d81d070142d0703400c031b0014080309e0066899200c01e44041600142c1003001c8402c9080d0390f003104900404c0a0700001d2404a1511441c04980040d00144001072002c442e400c80a0381c030250101c0352180d01c1d070881c2460201d200b440101c030700c00d0200076401042c26010881082d9152008003004641050034010074403002e40400d4000e40c0412412413099181c005000c4440c10014903240580b90302a05511111a01d04c00a40304107804c8035403042159000c000201c0d429030306048880c0181545800c0c0c03a180c40707015100034140c1514038080740405241c0011505580d4400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 425319856 1250 425318606 425318627
    0x120c1107090501121e02090a09050c04060b0d150b0403050a0213020a0e0f18010303180f0312031515030204030209060111060c031314030415110604080d060302040c030b040e0706 78
    0x8981817109019030100d409000742d0038005e5070101a040c100322403000e440e00131b031809034840c00030743d00414022420001115a2401506122502031000150f03e40c6070b94402d034140b4101c45203000001d41c1d184042c4039541e000741c000321265046030b2860021410b00300c1c0687c10840c40c0350340039403d00b400003000a00491220380400d11941711030015241ca07407101040e420409084100d03030143c80d86c40c0d050241408004610424240b0000400090030880f8515501c064aa2101a0388144c255000c0c0c128060820071043c00308031354403083c00041c604000c124041d00074200d52800750300c13145580104105180014012810700448503442483c40304041403403640401402c0185171030b5100c282c0c003031401101400000306800e107824006800072a00201a104641c060300c86905140144c483c00c548090300255041d1039680a034001c100081c0030580a0311082e20b450200194035607032600010207071446150a40c0210356100c0d4540130a040a020304510044c4040044c080146030210007400311109 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 425321106 1250 425319856 425319863
    0xb030109140f2e090227010512031801050c0a0c0603060509060916020f010c0806030f160b0a120f0504020a14010f03050a0e0a0b07020615100c03120c110709050112 72
    0xc0403d02d1005101d52100001c2c9801070b01441e8560a0002d0302c02d907241703108030b48a010700d0700342c800002c030f44c9020600c0d02c00c280c11000c06141031000c0440710b04040070003d601c19052190901c00ca5004202c01c026600e612401101c4e0f01d03412515040e005411107400b41c200750301844603402041065200c0c5540c3c0e0b034201102e020058a00c80d0b0518080381001c0d41a81d00c2000c95003824014249e1a0780441034500500b402c4040e20249e4107a02c100301e544520300110040d501304d00074010085d60101c04003902c1d0b042c4040c1000d013001c2901c103403407030212a0072008a15003566641c00b48815820089040c502070940e11107682e620170f8521001812036036071000c4140c100743e2103200240c010900d0740c2041c001c3c010010700b20b81c00510145488034801034201c0f03480703005120b203000140e490b80350fa5810004504000c0d004502580f004c0d081151252000341007038060007a42806480f18200a20600c2c007640c0f02591115241c400e20722070f0a0034246079a11451040c5d043c04010300401c40e07840b0120403420350 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 425322356 1250 425321106 425321173
    0x60f030b0a0b040e0c13020903060103120509130501080115050303040506070606031407051f0e090402031509030301050f040e060c0c0703080406020d12050907180b030109140f 77
    0x200c840920700540b002050140e0064101400d5a014620008284e038942404440c1b28000118403c0c12508900500511070ba0580c4140010000314140c011201c1c7c3e070503481c0c90310514007034040011076000f100001c04c07000f55640c1c1d0801003103410f000307100380074140f11088400d100071484d0400195890046004042c4584400581c0d101046440d80c0141c0003164083c21088404c2d85c21903880761034150610507180940c5070206031841ca1650100988400100c90b120310201c4206913052120402d03009001701c0e014464000645903180010601ca803150b9030000003560380758101424000115420300c20350f4011401e07c00e84400c0200702190080e4001404800302d41c43c0c0e81c004115070300c2e14250794806020800d000402050165000c62141c510840e0b644804140151001021046900403604c4020b00c1c1c01071001808004842c4086150044040c0380c04900020807200080c2180d40c04201102c2103420b000462a10210621848030740140d210003910000004424030511040000c404ca0103885 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 425323606 1250 425322356 425322361
    0x303030e010605030a0f0b0609090d08042d110607080d020c12040306020a08240405071101060b1306020606030d030b220e060a061511010902030f03030f0a060f030b 72
    0x403002d5008500a00004044400e0203819003085885211480c105481034404d05001400500f0101402c0340a009442d00400e5235100407070741103840c04000342c8101d401060790007404048480350210080b02c024104540340c0c1d1107c030391502c03813410110500c006000c1e010074000395020030398107400d407440c3c1d007204080581d50b09005008c4504029005440004107035000c5404801e00001c0c0d80a001c550942d40ca4074960707034407105800c1c2a103e48064488582d82d010030000071050816422140d00f28115060020001001c40122401c4d07a000e43c010140c0d070640814503403803201051000000a00d11400900300c1814400c01003034480c015400b401050544484040807980c460314134074810b0145040380c02840b840be80309005c0203011250400d80ca0361184102080c04880c03d4459a821928451004000d0214088090f03688070b0b95800320340032655035480c00e600940c42c103008118010b4034801c007459403450020313044043c50101501d039425480ca8101c06003c0740b2a198400360030399410106c3d508640c0e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 425324856 1250 425323606 425323631
    0x507110f042f070c050f120304061106160f2003040f03030f0e090a23010b0702120c01020c01050c0102272805060a0516080702150a09030303 62
    0x281034040c038103400500d80076525a100380c04104441800040c0b0004150180140e10642c0b42405405009030011481c030300304000c6803400e03031400700c1114400b8010001200f213000400c0d0440e005507020001040d401822480c04200c184503860707104800d060f5105042c0d0441400808602848080c0d005000c034a41c450b40003001c0304889000d039002c400301265980e0792205007030304041a1a2000f04c011a10064030020454003a0300c0800340407801509111380c9a480d100080003801107480942d0107007981445590002505641450207000c0c00c0070885e90f281614414030110750000b0080c1c0000780c000900301c9102d13a0740401d407816240424a0502d88882e032001a0b1402840794012030310703107a03080b01400000d00d09180380c10420f12500302c80d00c8101004203144661907415254449480c4201c2c000140110701c1e224003d4112060285407181c1083d180302410f1040780d0300940709552103180881c05204520700f1051b03000d0851004080282811242c0e00d0280070403c09020003030a040e19500c000d82c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 425326106 1250 425324856 425324869
    0x3040302150a150806150603072c010e1215060117040f0302160e1609080615100903050606040924021e07020d080c011515020601050907050711 63
    0x1880758401441203600305040024020001200451040031108000152400000c11082c0c400c25003a00c21007803044001041012a41c0000d0482040c0020006500846c0034801e4030b40710f0b03070100409407070441c1c44146d00140102c0055110340b441540c1d100c00740344008502099050582b54981c00079103c9488000040c1c58401c080c82c51030b8400e651040800042c04400500700008601035000c1d01c00b001d1100300c01e140c5500807400f40d0300704044400d000c50142c080c030341142a1070140515203980140d884081c00d5040c00310550f60b003070301103603a402900a18580b001e0008801034031030405840c00c600d0355a44c0350b190f030002002c081c41140e80d002d0060038050520b40c0348800c3e803d803c001010300c45421800100039000043c14840b0781c5100c550590403c0040c0c41250342140c1c009080090b040c4d1140e940846a80c40080d04805954942c40740104076140d0005401c0a09007510f030f0724400210700000249000c20590220f80700c0d0000b6400c1c8540716401400315241c03190842e04102030381c0d20a4010880 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 425327356 1250 425326106 425326123
    0x90a1e03060f1419110a0903151b020604030201060f0e010302060919080a150e0a0b25030e0d021515120d0206011509031502030703090203010e010f18050a030503040302 74
    0x10b1005001085915003076804141d408913070701c0c5410400c00704e0006050245004099204020600407036040c400301e03040b02c03e800ba070000c400b0001720f22000d644010111020f1300ca03810401688c0a2410300040540a00860000d00f0715a06810104d600e000000d012156062001034001d000000307456543e5180c0d4801450000150007541c0d14280c0d880d40903507550115240c0507164000c101d24281841c601c1c90144000b550b50541c0204420400d64840c803c48000141c100c2c11b460440100007818401d40c4581c100020216440000305a20710715022814940100c0c0700c10115000030002810b03441c1c4e0f5500c0d10313801c0b0102c0e20b60038160a14441c0414101083c103090078015104403108000955800241031b030507503000501c482450030700f0b50026141c0b40c2c02c60200510118607018040f00300720b2264042d6610a441e03250100383d0f8a90380c2c01007401c645c2208e480f0901a516406000720322074480c002e41c0400e21030511450140030040d11150346800c00752100404202001001c5014148200607144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 425328606 1250 425327356 425327381
    0x7080601050c0c0405090303071b08370504030201080c0913020d0209040f0905010606090605180a05090a1b0e1c0c0e0f04120813030804080409060605090a1e03060f 72
    0x2501701b004031540c4d00d41048581d140000c940401161044120060301040d80781d018507818100042281140e00da850070102c2015050482e01e4440e4909400c90704108842070a41c4545545605500005001e0348005052141c4020308021402c0662030b2032007040c0400c408000f005845081d1808480080d11900c3d050700e5201d403c0c01e1503203200c10529071048580502c5003000300300450b910b401c2030f900034045104000108005000390a50054a030f80300d1101d1200080c04000d00c0c076212000225480741c141d942d445055910818211401801000c1c00c02c1c00c1c50760305011501281d4200041c0300255800c0b58044200c04004030082003040b04082c00d0060590044ca00d5034034641000e0b101c3c800082102c0580d071981e116548120403070302801402e03000e452401e4207021400c5640e01e0903200028054411030320968100720000f02d64000d80309540181500b962101e41c0c44550200704a55461640c120303d100408041000941c114000243c1041341d84c00600803441c1c000305407010008100d03012441 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 425329856 1250 425328606 425328611
    0x60f030c0d170d0b040c0906120e01060b03091f05010b0405061b010204120605010b040608150a05060c100e032a01020c0109141608061b07061b0801090507080601050c0c04 75
    0xc0c0c0006000b50001c0c0138800060301c1c00c111034681c44404465002151041e000410403440f40d03600c40c00066008681c502d00031000108903996110210130059004883c3d0078010380181ca038050014008200b691846e0000403814401941462380c2d1003907034030a510601d842080e0018590300442d503003000e1a5502d102c040300842d02c4580d04e8403814125841d4440803151a880c150001c0340176000030003550103039403481e074582d41c00b03540b580c03101f003c00d4600600316540411300c240000340c60364941c4000c116908040e0302504401114207500c2090310a9200060103680080c0040303031880158040c00d01200203910240711a614201039030030300910a289584006500f400303100e40a0100700031400c02100d07a0001103d0702c20401c03104201c04000140107a0354260010400310781c0c125201c0c04004111440301003c42d10707200310356a410040310280710b07400320351a5a90a00102042d04415580d0041a20300e005001a1619280c020300c4110000c01040c1403080202d0b40d10f007090b90400681c901a800175204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 425331106 1250 425329856 425329867
    0x30314010b091306150c0b0c0c0703030c0201020a020a0f05040b090615160c03080a0801063213090b040b013902061c0e0307030509151c0c08060f030c0d17 68
    0x20710308400d02c0c000755050301f0404003158100100c002200c4016200b030303000e41092400c5075012102da0100d41e0043c1c0c1140b0900d0b0030a8096a130750a002402001180c84290394a4980b009020039250b01316102c501c15400343d0100a01e03500c40d40c0c16000c0922482410669580300e0140c494442061244040d1945400800210400076042c0c000c2c04080c5c2291212041c503a628003088139030101c2e1040c00c101034800d281219801079140401c040090a5404032282400d2080340301c11f0500055502904166842e10318441c0ca50400b403041280b04803082c41d01c1c00304a03007059034150480500c20301c1e07503000140c07281181140152210483d4021540203000700c0d500c100a0000c1d07100c2620a010b81c0d9012450011280246600042160600b2f649a296581003200d528100709051002821042c5a04002c21101c00400100d0058880f44100924000b43d110020a8001c101c0d54000703202c0c1e80500040841164143d60002e03c19a0030300e0116480301e80c4110b586403441c150302c8010107100810b00c3c040342c13 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 425332356 1250 425331106 425331149
    0x909060f0a030c0e1f060507030c051e01140705040509160306180203070306080601050a171e1605190b03090f0624030102030f0105121612030314010b091306 69
    0x100501440d5114101010000e1750b0010700000803e520864000c29020031004000900500f04414540d000d8416141440c1c400c502b01840504141c1c035240460750b540d6845034028801c41c10b815041001d928041d03080c0380c01e210100320110005000b03403507020024208140b019210390400409010032a1400007020905402031000e504140c0d100030102381031040105140b580040c1d0305040300d42c014080c00702c140c0741c1180c0114450314140c00710490b0161080d115481500300c01580c070122520b00c010203102c111f40070161784c2e9401d90307040b035881100c0318000041940d140400035401c1d81c0b1007040c0b42d40e50b078441e00015031900d15404a0708080d4085c420412010401d82c21003000000302c11070030010713000000c1082500302e120490340a000b13600e61500602040c00c0c00c2e040c54464000c40750448461005030000c110f10300f2001d60000b81c0c4008040c61342c4c800c0541c940a03108980100c05101c02507941030052130174460003051821030140f0503081c2010400b8200b030700300000812264800b01e00b15a00c0c0d50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 425333606 1250 425332356 425332379
    0xa1505040302060d06084c0207020102120f040e0711070e0a020d0908030603010c020109120804020a080111091c05071a0f0f031f03052e1407030b060909060f0a030c 72
    0xa0001001c0380d0342083e0101c0300508988030007d85d8280303000403444001c1e802e0000000350402a4144e0440c890f450200c2c100c201d000740103100a002404640d40c403145003104100908000801c65010008122011a00208005680304c151160120410400d41d03405068030001e0140a100c20340d018144000b00090040583c003c0d40105001c0e4028000c0c41c40b041000c0c0d083c0e8052400c02410303c0843e00040140070707c50251243c02c00e100401c03410403207036070302034460a581188074801c03142c8200081c00720f07151600300312002c100720600100000102494032401e440700c03451b200300c820f00c2d810410142d4082080324210f501c0c1452a1240d55295100113400e0416030300100c8440c04128414416210100030a84c100b00441e50300070000c106400f2140951146600f0440c0d0351006021034030319040d40c11509024500d00142428021a000d1409510040a40e000c1c081c4407801900c041007070328075540b03030520030076406102910320a032001e8009012481440c403551001c0c05a40900c400400c00c4d12004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 425334856 1250 425333606 425333653
    0x24030a09050606042009031e101d150711010903020705040501050604050a15021c110d030203011d060f03060403050a14030c0405280b090a1505040302060d0608 70
    0x5a045802c03903a40e1406020450b2001d801c001817420f04581448051580003004015550029003034403820000c0044c60220301e1060b0345105c266403c840c81192100000d4465a4208150315408a80d16081a030300d103521041150b50811a500c0c0000000d003e15000708a01c600b02c450040081144d4042c41c01c00075182c61040c0030340c034426400c01000090503e006401c1d102070b5080242000b40d1507203000f0318400b180b0b514035000015405501c1c030801d0210302c81d40040301802c0e4291989904012902965801c08030f40c41800d805044c030510040c00f4284d2810b000c10071085121450940c20b0f203410001400400201e00714a6141c880c00d42000101944900a00281e81c16510307941c207058280443c0100078002100d00f840c0302e6130244420400e0345000c0b00c01e002c0b40c040c507003150030700076041c0322144095100d503401c004000b0800140888590a1005001c00201030440c5e41d9a12048802030003003076072107070b4440644660808141c09416a9055000d04c004200c80000c94007000c416140341d1403440686c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 425336106 1250 425334856 425334863
    0x220201050f130f320619171e070201271407060f020d0c02060307030b0d061d0d0c0515180628140403030e01020f0412020406080a050303040224030a09 66
    0xc41c4c80141018441c00c400c0b001c00b18010403a60034146d070710f99103d01c0880150983c01c00c20200b07560000c0e01c0544000c070b040c05044840407c54100307018603001c2c44000006855203085a2611a02140c840180710107004080180e080f11000d9045900301060700701c0741d403074a03c81c0e00d0040d030800040e1140c000a018026074280c0d003e80d4030002040c1016039642440b040041d422910402c00240c42d680319a1100096090081c04444002d14a071540e00880350144212003070300d204c2416074a800c2c0000c1003103102d48040362800c890105416070f84ca54407040c407184400700c0baa07409070104010b40140d5a01d00b80175414901100e03e2441c004401110b403004401000460220f0980c086c403449400e0701903240361a624140c0b045150300e40c2d40d42100200b010405c0d098065500313100401e024240c9000a000403c46000c0581a0a860740100000c880e11507020010b194080b941440c006a1b01001b501d91042d0125500d5040d0f07054045100c00380a2a60f0218880f11000810042e12140c07523401f10307070003500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 425337356 1250 425336106 425336159
    0x130306020f12130323040b03130501020d05070e040e0a060504021503570f0c060f010e061e0406050d03050d0c020606030703061a0402030708220201050f130f 69
    0x60485d05d0205240300a9992160020400c8144202588440115040702d21081e5141c00b820480d00c5940c00ca81109080c0380e60507480300140800366070702160300c2c5a00a821501080078440010b83c0326910180035000410a6440e90001419035403104443c9003c03583c0c0780d210036503900d0000580e0b02503100413510f0b055429081c024000d200201440f680390001021000244031303040031000041da6942c2b10803811a004400c001c0780c1c0510b000c100c080c01c074030100d41c002004117040280120b4400c1005030450360701e0391100001c105540e50382c0307085407114540c500704404644100b1030100c3c000c2c242d40e4015542000910000c0020503510078020f00900c90030f59000c014003030304040201d840c0c0000382c1d4403981c160701c140e4003440402e00d264040c003500000340715011340c0c12584402150689e0070869090000c2a10740003000b00341c00c00000d00e071102800314218212562002d0f8000707001ca002e0109020120400807420050b800241581c2c400a01101c101c0011000d0b50303001140440c03010582c50b00d602d84c9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 425338606 1250 425337356 425337377
    0x5210a020909060723030f18010c0e0f120705130b0405040309090507020a050c0111030d0c261003080c0316110102010f110403030804051504050106030201030c05130306020f121303 79
    0x900500b00c445d003420307441c1c16851031031315014956503046002030050742814101d10113000d54400c09203c1e0306145001926104840b044000c2000350701c121031001d0324010003800303250030004003021850800340c80007298000d418400d011071800041441c5041641c0003803030402031000385a00201403000303d40c0c5c2e11400340030590760311000300d0301d0740100f420041c09a0301580607030a1542c0501c40755a000049801203a041050001d12602600c0c95140000003284aa4182d040c049030165000c401e11020300b8034461050814000210000c2018400070307182d1a0040341c4800c1c82c1100340f049840e90b140f42e07440488c040c1000c4c10162a42040383c401c0074003561900c0030410034043e013401906020030048000e242040d1a541301903484260040c001c854500035a0400341d4803540314080749001d04d0040c0c00028070182940300150450b40300015107020700c403040c4000ca030310f9440304107618180e0341c1c030800160302c0314030340385958440d801420801a540380c0040208030741c10302405903038a40580250303504041807 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 425339856 1250 425338606 425338637
    0xb070c060c0b161103040e04021005040e0a02090f060304050c12010b010207170f0d0801062303040611160803041506080a030c0f0b090313090605210a0209090607 71
    0x3008005401400d550b1050002850440000403000e80c41050b4144a1506000328220740d0850b0703c590444130b40081c404040c0001e506059002001411490800c0c501c0d20382003840071481110010103524485070001942d101e03d89a21075044883c1001138422501d904207442e24075150344010b442c8074094144150f4000c0751a205008507030f05040c06030040c15107141891001030f640a2038041c60841c034440d43c001254041410084045000e005940d107990315414000c000f418501e004900000d20030748500e440c130f4100c110078103c170b0700103602000c000303140c00000d01221401e000d00c01401401c8110080320900b800085402944241c1c41010401aa51030303610840c012501c40d4010310300160300400c06840041c0c0604040c420035809140517003030303000190341c80a1030030008803070b100101d420124210005602c07101810024040d40301040c09901c0c2424045031201100f0303180350400d040982c03014041e9050038042c000b801c540141036031105182900501f030341c40200b81c030300ca80006e4100c0c0014454 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 425341106 1250 425339856 425339867
    0x31a010e010c02010305040609021504060e0a030b0f190615091a0f0c0f060a320a0f150f080d0905010c0f050f0a060e0c01090e1b130b070c06 62
    0x24000142c540000d11049600114000e0000800c101d90440d559207003c0d015940b46051444c0c440e45d4108100d949a052040040281c18a12502801030314000d1080c000100e81d0b500c4184d1080c1c07001d119a0700c65a0b0048007041d201c4c0458207503041e89141c40008600310180b84401090009a0b85546001079612000000ba803425005802101c8205004821204116100078052608801e00303d40040c8005d4401d0760070f14806941c0c14032181c0d900c810605d030700c413044e01032002e001c401640d110240364400402c88101001c010000700700b0540c0c600c0c100100f58691b6000c00180d6140311a0b042c9016202c0908644e03101c0940541410391059a6900b50610f01c1154613405540040e0740308103440e0000d56802c850100d281604445c039014015920301d150400300a8503c910f8000d503804541c840d0401503c0e030516080c15101d604104400c84144640410714104540002552400d0a09140c01100114050003200111441c413401890001080c4580030094901640a184004078031595040291003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 425342356 1250 425341106 425341127
    0x7050f03060c220e010603050103060b03060708010621110a030516020714010905040911040c11060c0c0a0203060c0705070b28051317060a0e0a110105041203031a01 72
    0x108500c1008a152406255000c0c12452403c0d00d1032a2881e0344c44040802c0501c0c426041000000c1d0b1301c1c2c0c0104140082402032600c0700b507042e0054200b6050403c001031429005008503410b003c50340d2807120000100300342010720940e0401d404c1000190400380b80c0242e81c0180c0402e40041e040c0b0780812201402e0391200c01e0081c42d0313600105401403a104c0e456003210212400d82d03040c440d03100710018054440d40522030141744600022a141c102e981e04103c01c0f5018a80303d18104030721440301c21000c4500055482d002000e5114aa41f80d24015800500c0c0c6161850000d406004400c14030202c22201000b4207c540d115409032400c030b58540304401024013502e060b851180244180c0034490300159005400380305030a1611070701d0441402020300c0c0040c01503101020312101c6c1c00b04041c5c200d400b40000f41c1c0040c0041c2d001d00c02c0201300e40d0070725500c015200d40035100804d48421040c0d9070b0301039822280141041c1d56011100c00580c01c01500406118a40d4501001c0703c1644d03007519849881030b4034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 425343606 1250 425342356 425342371
    0x105060102070e040f060218040c0201020405011b081e0703030f18060c14040b07020f030102070c05060d020d050f0108011404080a12020f0c0307020a0603090507120602070b0907050f0306 82
    0x1d0645000341d503c00402024006031031070300580501d54042107840c0020410348000600380c080030001081440226a036444012085910500c01444036a034030004520102151900c901686403060400380024494986130441d44000305800f90b0010328907801520395140251010080c0c2d0798600150030544901e4400d94000c0260b451100c800113607642d0002c00075410a16060f501803000680701091640150400c0c0e601c0c03480441e59070110f1074444020004000140e0095080983c50355809072858168001c0b140310310008036100c034295103298190b64800644000500c0a820110000e07408581c00380140701055003002c965440c07429002100c03900179503008041910300380c01c805d8121030f1a060f44c088400c020303800f00940c82d001c1740884003030081040244081e541d41d90f0b09204020390700000780e0010040c0360410f0880d0002c00c02c04120340040b5042da01030100000c40600d0f01000034070a005d00141940503440501c0009040003030340c501075403000c1d82c5040c800c1d0040800c060b42c03840c0454200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 425344856 1250 425343606 425343613
    0xb0a0e100f08060406020705031909050411040e06041e0207060518010212060105130b030a020406090f030f1b0308030a06080c0402070b011a0702093301050a080712060303020f0f0105060102 83
    0x1900155180e8007c0c5441c502500036030741807a07003c185440320a004030890500082540c5070921142c13a00384103107022014005005840c0c0ba142c440c2d05410001c005103224841c41d628452580d5943d102c01d440300039100d56039811551005189800001441c003918221921203c0c5041d100c4080360520031907122008040729040c1996501004440c01da00002805103c8902c44000249800c8a603001d0350044454400158603503007070010051800c1c100350300980c00ca1200410400c0070802508540c4803858100c001040303062089403010b9000c44603680004e050407800000c024a215071275008006458001050344c0d0410908000c21003a400382e000d0152001421030010089112440c02031444400003440366401c1c00103603000210b060a007107601c10319020300a121502413803c14000b201d03103206078400007034103000c07400002051802005801401e010070f410120341c20f14000c1048104503100f042c801d010103a2a4039000b511003c07400002c0045104600d50f004c20b40c8018000c25100d0075041e8003d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 425346106 1250 425344856 425344861
    0xa031a06090906040e070b071a060a1508332d061605010c1d1906030b03340b031510050706090b0631020703030b0a0e100f0806 56
    0x8020045c003500780c2c0641e07548540100010940e54100c00ba00125018040720061503070001408000028000d011504c80c1ca003110092002c18203022a07005000b446203000d000302d40e03801d21424140c41c51140101e01440b07205032001034101d1110507492614000b6a44036030410010140d0041078107030710b0030401256081c410743c1d00c09030822501920b42107152202a210100307490312100e085034155060304000481050115640e60400b40b96801941c40c190742d5040ca88200e1100100340c08806d004040c100354a0b05c105440c0c4c2e5504010540d242c10790314401c007118201548524508001c1c8028074494a082071a0000c0c0c5c0043c03450a0300c1c0b00700190b043c030200c2d4400d00c00400184142c56482d11081c49814028500404c07090f100b180c404c5441580f503903009003050030410002c06c0c440c0d40d4a401501d42d0f815100c050b036002041446071a000c0305405a103a0040346000e0700a05002c00405410050308078000495a40c02c0e40f12601a2a000701c0c048070703003601c1d616103415110706802510443d0b44140007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 425347356 1250 425346106 425346109
    0x5010206060f030c0d08070c0806010518071e2c06040501140d1b120b030a0311071d0a06150203030105010e1201020a0207090506010302070c030b060a03080a031a06090906 75
    0x2401414020144d900c003818110009250400b920003d88042d50041052000c000c180c0010b60003904282009044961501e0009681908040e801c8541c0b091404041030311035005410f1844020414551104d51401c40c0720010800805040081100e40303030480c2c0c0040b020354072941c00b540110081c009514103170621006642c1030030424000c4102500070800840810140d03c240c03c080d924175581040b0024600200404101642c00304094803440c2414100b01c60750300150b41c0b01f015615062400c5140400b41000f82040c2c03c660100030300c00001881090400c4200c940784e40b20305c00550042000756242c030700c804010904407404030b0240e4401c000600c49580943c1561840a40c018220700c01443e03103a4242e03003a0703000014464090b80c041c40c0144034a180900845510a80c02c0c03034214100010340e210920100400d200c090820128417021400c1c6484404c03042c00a581c100c40e420340c0d9480d0203000200100690404c1c12606e40424204811743d29042c401c46241c0440244402e240340c49800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 425348606 1250 425347356 425347369
    0x4051f0b150c030903030d0603060c050f0909071b080309060f06030d110a06020403060e0106060e13020f070b01150806041505040f060f0b040f1418090f07031202160501020606 77
    0x40d0b281e02c1601c000d0000340e1060f68200003d02480d00340c800302082040c594074020b03042c0e584603c2480d00313010052002c681e0310410036060f2640c4090446050215803a0905c069030718141001c0308032842241c03004042c0c24081d1460003140521255000c486150303584c0b071800104a201a1411a419000940c0e10400301d0300ca1003400310004d50301d00c01c0d9040d9000030f0799480101d0b4403d03401124004d03200c004005190f0b00030700c00c04004041a00b800c0c00c100420b80d00044013996803030b410300421070340803981c000303540000810344080e998041401e01b40d558480001000906090740080c00280640c000583d041c1481d000f00328454018100710b602542c01d21b004c10001d80041070a4084a42c2d8914000030381500324100e43c4020085114440d40e00d6086c1500f03d02c0010954100c0092109500001c29850300e55210040d4640d03c0c03808500c03d03a454410780c0904108040b00d81c12203500ca011008070600241c0d901c180e41c0b8954076000c81d114074403040003800b21031010f441502d000da003006d0700180240c2440c9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 425349856 1250 425348606 425348617
    0x51b0c010522050d0b1509060a060c0c03020616050d0e030a060b01110d08010603060614040302040c050d06090605011b0203070b0906040e0f0106030e070e040809150304051f0b15 78
    0x40c0100307002d003a200c02c08526000900d03001510700c5102c400034400602c1d020444404805419100c208841c901180402d41b00030041c4501800c00041c0c3e10107900b441800c8582d0f01c050341d07008000c08d83d201d01c1d0101e101020108620140c8150140d6900040d400d80504091902c1e258080e000d0310a1050742d489003001410800a03843c140000e0403040c0202481c02d200802c0c3d00c0a0320f40b100811541400b038001e040b182c15030844024401604c45800032003144406540c126075040301c002c5500d01d0400400c40e640d008144041442c5810242c010884c035402383c0020741640d03801c2e6159a4000300e901040c0c540440050710103074054010f04403d001c0040b2020091809040141c411440c1c1030380c4020001c0703101021100848000400030061120607894040d1140d06035a04d4000d181590400a101400b020058070003400541c0010b492070280e2108217600c4502c0074503116440e282d1800382001c94030b641a441e080007401c0203411044410030994032a58080c075002400c140e00100c002c26509006a101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 425351106 1250 425349856 425349907
    0xa0c080a110a0c210f0b0a0618050402010e1804022b030e031002070305030c030a0b0607030507020a05090c09010305090106030f0c170c0609040c030905030a051b0c0105 74
    0x294a10080401e00412607141d94900c0741c03140b0b190480c585a55115908880c07141071810518202407400403640c01650301c80e066411600301030503a19a406540c00514140e8840040c013070303a00f0220036440503e5071101d40701e24000c1c1c944400d11900303a02003040f240c0558047c0018a401507001c1009800c01c2d01c2e03501040c1c0d40e00007076000001103032843c0000c04425080214009207400c00c0b00c810904080c0800488403440c12005c0d07040030798540d80a082400001d101c640d08540100001d844c1d20b1180d042802900005010107543c1d941506000b1300507400311105034010315411100092906203000d8240c894481c00c51440c2c100104000110080e01010304144c2d8199281c03c40880807075400d20000000c1807061580030003062602c1c901003086640070500032483e401c055402c010035160002240c0e8038031012240082ca0490b220825170082a0481004d821b902c000716601c68810b8202004115580354130b40fa00c0e9820400305102a62070645800c0540020700500101c0380a0f501d10175030803c061075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 425352356 1250 425351106 425351117
    0x30b04110909030a031404120f0e06040906080c010f020309010323150102060a0501050a2c0718080a020a090e0a050a06140601020604050c010f11030f0702150a0c080a 73
    0x10030a0020360399040c141d400984680001030798502107509482a8540e00341615050005072409480302d5503910108900c8078240314280020640c024402c1040d2800b003a4010052522103840c1e400c60f4004020714040c201c46849602083c080301e6005280d1b25080c00e04590086203010700620044000e40b88032140c00310711240030b001140b480031022003524807401c6601c611107400c002c0940024982003003c4e140700401450600184a0303500d54601080984900300301340307800811814004100701200d030001079002c0b549002803000c0554030140c109030184e00c00740f88458881e110209552100c9115030000d50150781c5440070090711f0a1900600c101042d0743c010f071409134041d600d40c542440752042084807803a948040061188440580441c0c0148080c4001c000718035003a0354a83e51809010070b03107410303c00d0000046c841c2c20721038022040d00e680310406403600d801c400d11480c0d00603040703441c08074404ca850100d5100c0d850b4260003a03c00030502c61b91082c4241100e40c40b81c0e013140d8000501c0008000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 425353606 1250 425352356 425352383
    0x6010902160203010f200304080313081204140d1103120406110a020c090c160b09160f05030706050c0327040504080d0f02030705091207050a03230d09030b04 69
    0x243c003031245601c64100740001080d918800d02218038200c00c1ca400d41c986800c0140240004240c1e0312045e69400701008040d14400603003424510824041c1d000f0603c801c00120b01000708002c04413040945c0f9444645c00c55014103001d11081d281480d141d188030016a0090103402c002d02c03240301101d9000fa021b00300008145014960b0202d841d0300503c04440564080e5800010b1030410240d10356028080320348072824a21101d903024600c8a201c50041c0040e03e0300008101805400d01c8840c1501070050741c40b05005030f0303c860294030005a4402e1910900500f2030020f0031900480407560495281c00c091850800ca40e9142d81800c4038041d1130100c0c02e0000c0241e941c0303d03102c0e407140500070f41c0500705440c0c5030400364a4035015034040f2008240f038a030050042c02409038100041d0b44145600311503440e02d100e41c980c5041d05d0480190b20440c0e120900d4400001800750885000107044030405040c0d000d004040f083c1d5a40b040c8014080e00062030b450410804903180b448940c0d045441030f000c01c0340c41c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 425354856 1250 425353606 425353609
    0x6030a0204150e070512060a0e0c072a0501140304030f05030405011407080a0c03200913050a0e0d020705130207110a03140706080105093c04031709060109021602 71
    0x2030b401101c4c07000c0402c0d40002e403100803000b0306030a59880700d02165004d030200d041207071400910102409400f100310300032420310200041c06440e41612110307500c0003004080c5416080718807074102c2c810503001c102e60122115014610340304580c4180c0c0c0545510051099402d0119080e500c010000c0d070329550390791900259403500000e214080c020b84e0342c0b40360711414184000310466051301110001e05103040c0040c0e004144034650550641028940c1750384518520303020403a0654646103d21802d8508002c000125000d9402980c0c0c0c43c1080e000c4a05401d26103a0a90781d0303045a000ea030703920000c52049070b02040129001001c0d410310030045043c0b00385003040454182207064208a0b0942540e000c0e501c1d10010030000f101c0140014501003207154541000308040d031001070054410103901c90101d40910302003259010f410b000e14000c40d41c2103454020428008103041d00d0880009028240710500e41914140060081449a02900f110703460f1041b228020b40c001c0b44031515410f002c81c00071015 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 425356106 1250 425354856 425354879
    0x90f01021204030e010c03020c120c043603050702040b0a080d0e01081b0304140f1002091005041508040203120d0f0b060a0903080d20070308060102010506030a020415 73
    0x8079601c0940101890405103400340c00d688102c660310f030403c001080c55402007a40010458804882a03500c209035418811400341480e8445040c60341241c2030541060b4122100c4484c0701c140740300c2ca450f207000450800c44094030007400d00e0f0090000b40080c800840946059800410a5013008148400075503139807010031f043c00c6084ec5c2c0712001c01d44500c4054803950f003100041c0e51002d001110400324844103001d8107400e00000c2d101500300e5042031543d07000920704110f004581d1280c0740071100085c8a10303e50704080d41c00742c41d601c0c0c01580c0c94640c00c040c01e4080c0042d28203440502d02c046010183c120400c85403028001c0c8207030b915214803000000184d94010042c8620140d116000c652940744200e12001c0e50541d40703a460140f0002c0100c45940e80e4051000c0b81981d500003181c3d640c400c0c1d0b422522020f840108000315000554204104140c1d46020042155521070303181c0082d02d940300c000580c22a0380032103c0640540046000d080180b074140e1251903414207444044040ca610784008804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 425357356 1250 425356106 425356117
    0x2101030b070e0a1223070f210b04020103050a06091b11150c0304030e090106170a1413020301020f07030201090b090a2402160309060f03020301030203030909090f0102 73
    0x2005030300e10301030040e002d61044000e40540c406607801e40c541c1e4076013000460700d1581c41c540034121038410810a42c102c0c0c041500716100e00b000e002203842040d100c1c054940c0403039a030b1180d1840a002803006035490788040d00000038143e0001c0010040390b40d240c0043d80075080041030004120b5460300007051480d4030344030b0b4800030042d036905078580c2100390318003402c0142c0c40c2c01030f000d19500c0940484865910750000540c09091201080d8507030b00c4500c0e0586826031001d80940d03001f44220004241258040c918010303036800d4404006541d1215a81e0901321400091501c03403081080d4000341007190b85214240d00c051001d40010716000c0182e400e0003c5400002c0103e00603515008a00c1c18840359050f642c1e0400034038805003e5201ca0341d03581c0d405001c000080c0750780c825462018400541c0b115810340d8840701c0003000a400500c418500101045018042d00000c00c00e52101b03c2c0002d8400e02c2924140c0342d02a0040d464410b801c804c01c00081c6009000440912407107904602d10361080c000b404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 425358606 1250 425357356 425357363
    0x32e060509011701081b03100c02150f1006030b0604030206030f1f2312060703050a06060908030d0906110f04030210030e0c0d03021e06060a0605120705210103 70
    0x16181c0e00ca100c00100b07444081040e104202e0300c0c910040c012181d01281c2c1e80703280c02e50f188030040c4003402c01c4086410100068401c40c600c1d481c0c03512a10215801203021a62801c03509400401c550361425800040034056441c40e8100b5101d01050200e02d00070341c000c03000010010101ea040c160b07030385e000441d164811921b2031082c65000050004c2d4681c0c004456200101410446c0742c1c5505280d9140b03ca18081c1e6815003000d11140e041c03c040341c40d43d62400c1c5103880141c0545480c3d28150b00c2c040c002e0315098429000c1189001000214540321310b074100107886502c9c02961a03d0b0020702010003800e101d070001e450469a54110403c1030b9040b00007001208001e04106455501d540104081c1c11201d040b18010b250401c40c4c01d100050307000c2140c1c08030b00c0c022261600c40300c100b420308a2030407080e00c001840400108081060140d4000303a21442800121051000c0a4a40d2021034036400b1744071220003440809404119090b0152000d400c410306440486500c00c6601e401032070111000780d0055 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 425359712 1106 425358606 425358617
    0xc07081920040903020309030706020c030c060c250303080c0f031602011d0102070209060a151421010302090f010b18060d0203070305101a032e06 64
    0x1148100900704000400f594540a507032548540390300e034032031712814000151180c400140b01c80340305000713009810800210810f1003250b421088904019015850001c2122010304100f40000400d6804200ba854039500b400b904030403000d4924041c20008003e0068141144001c0f07a030010225410060801e140b0340080b40180640c461441c0009080800c00c001d0250540107030103020300880f4482072540b103440410440d40709501c140d1841d00e030300005c192481401a40c004030691164807425150400d02c00f001c0b086510690303020b00746900d0840045c402c0d03080107094194041091f85070241c19505014128019028170458000d40f49145900c0302c0494035080143c51411982400a64a034204948044c0190104a41d140420380e2031410010b9000c800442c40800880303483c88261564455110790000920620360b0030201e19004620903c19900c0b140d841c20040025036100d = true := by decide +kernel

theorem cover : BRFrame.Cov 425179856 425359712 := by
  have h0 := BRFrame.cov_init 425179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 425179856 ≤ n) (h2 : n < 425359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
