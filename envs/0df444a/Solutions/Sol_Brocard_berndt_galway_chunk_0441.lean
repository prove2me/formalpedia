-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0441
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:49:58.54027+00:00
-- url     : https://prove2.me/submissions/61149b09-223b-4973-8708-7d3aa8f4a819

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 79136692 ≤ n < 79316548 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 79137942 1250 79136692 79136713
    0x4090506030703051609140402010804060b03030702040603060606030506010c0c030f060b060a08040203160e0c03072015060a05012304080109050a0b0c04060503130503160b180c03100b03 82
    0x5150103000d48117041d0303c500322141085840c03c00c0c0b1a101c1220102d42e14110b81385003036000030381032076401480508a580c030b800c40401a42e03409d1045607021980180304003c10390303c2e81040c00c020486070003408040780c234010208459600420040c290560710013202100d0a00b140d5416410812801c0201c40d40c549900d80084150f80d00405040030250590ba0080286030900401d498003650003400c0c940401c08100521040c403184080d0355101e140009142c0e92500c4542c001c840c8580441404c042070301c20141c0100d400800480c052200c1b00d229042c48102b900c7d003408001156100e40700f400d0115481c03111101030450302101080302c19220014060030300d951129040e0035075142d4a0115416004820502d00308034546020a030009211280c5d141010f06002c40a8018400900b41509034180410f4550800c00f08008031810b10740d1080e0035081e11090762510392280142504c2c00001924440c01c84100c41200084001890740018024184d0340c1008110b03100501d660b14030250540201640301c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 79139192 1250 79137942 79137953
    0xf020a050d0807060f112d030c0307120b0612040c030c0902040501270506070501060305010c050c0c0414190603080708031602060c040302060c10060b041805060604090506030703 78
    0x542101e801000410740d115103514100040303510803408000d0082c81c1c5010640402c854405442d004422403000b90486106d030355961f102d0240d00426010b51803030000170050944c14110245000710515210020785070400e07c400401d58207502100c5410030024045c151440c4004140c01d40c1240c054645408181d8a035100d005825170150803500c10140c000a0800035942d01c51140201e010750044441c040b0610050001c24a4805106480c885c060210350384040c81000c1d4441d030700656001008108a01250801501540100411804074007a04950b628182080d00585510070030b070740300f50b29140d41c4801d20f5002c00714800d00d40f03101c42d5564440c0400000c40c0400240911030050024548134030b42000800e500542003210304085401103028044103030060010740b02941d6045034119110401c56000c50302d401c0b0f0502c10300038940c1c105140000d0000100000740241ca020192020024030541501c00945000341d9200d0b80000041004002c1c403001584055041100101a41d1507182da903201c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 79140442 1250 79139192 79139209
    0x1110109030905130203060307051216060c110d0302060601081012050102040524030a020703030209031509010507090509010b0a05040815060306160c0f05070b0c03071b120f020a05 79
    0x1180415210502031005240951481160324204c1d08150f00c2e500c4e008003c00d0702d030300c02d42c4103543c01122210f083c188100c506100c078162420700d40c50880b103820f658003001014161071150954009080500316891401d1008801c2c03485601500100003a445030401103420440041560580151103040030420142104036203d074180940000350721a81070004100203070543e14a040c201d1807032086007a0100d01c1d920103980d03000d10550401611021113050030f41c007a02c030310342c040c0b0340c50b0040804821032100102501401645180002c0005076130b4001c0a0302c500985016160f4001d10220042203146a000c00500d140401ea00c0c0c11420f00d030343c841c089071600d02c0b5042600429000c50040100604040120301e5114445c4404040e0300b030042c242c05000700751100c4e0b02800b45110510301500780041004828010211600b4041d40d5400220b4000d442c0e82206034111a011445038100710820145903440098910b4000364125105c9a0769400c400800f00340d404a81080344410000385030b40e550400d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 79141692 1250 79140442 79140461
    0xf02010e060d0e010e06060102030a0801090b010504050907111005070e1215190b04020f0406030209031606050a020606091b0a120218010201050a051b13050316150503010303021b011101 81
    0xc2000415440c03111b00f00074009004504542c8248040c41100c1d500c0f110090450f840c034040000c40701e01e4040125494800c0d42c01ca10b4103d14164180701582d41d0011030401c42c401c040c8250b410050340f60510341c050380c1060300c0c0a8001401844016454075000c00c0b40c190b07107071005040742c440c441e02c0c10409450040844002d40c69000b800c0942d212018203001e40310174070b00215003c502d000b00007888110180110f018013001c0582c00328081945440c100300a4070b5280d0f00f007200f41c030f01a517107080060090340581c680c00d00601501010641034205440702a001c0c4d140f08502d0403086906000f05141d81e080302224108020292031520744445040c4002c2040c0e2006048081303a4044490001e425070b400a00440c17180c1d03140100304150541c082c01c948040b0b440742080c0555811082124800001c0d8a070010395242c01070105040e508210340c0e405108492030240d5558209000034000e5440f4082440042c02581104400180f05000010a440300304414100070101140d040002c5003100e0550a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 79142942 1250 79141692 79141721
    0x110f010c1a06130c0206010e04080c06101a0708030c070c090509060601080f070f0f0203130f05090603120a0c0221011d0102070206070605070c02090f0703180f02010e060d 75
    0x180300c0c10b810005080541c2070f0114205201074007000c84000d64614051290b0355080032080701250070015600112000060084129001420702c009028250f00e80c0e4481ca0301c0000360031207003034001003070642560072040e002801d00d0305582d04d09900d500d03660301401c400c6450a02126000c41c1424a80c4034103170040c0403c5009080c0e601d00710001500c01c050141112503034590582c1004a90b41c0e004880100c241c7c150f146c5000c0704845d07528240d02e14000d42c2000c001440c1d00a4000c96070415240003030046a0003210742c19003580b1480285500c07030036005485040e0700b03410018000d81500070521401500e1010b09082d4210f111403a84203034500000c40880041d94454a61030f415241e14020140b0744490716008519210303003640081e800780300b040d0000b00a50b4a901c0015036050041c44031050302030b00a03111808a00e004006114401012940d000110303141010042c00007880088620a01e03500090710741c0c4202c0380790019110b145640c0034503644101b040140c9d01141d0310074003904000c91000c6c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 79144192 1250 79142942 79142993
    0xa080405010f03050f1f090c03090203010c050f0f0705030d0504050a020102010501050a06120e010f06080d02062d0411060a18050904020303030c0c010b030d09050913110f010c 77
    0xc0010401d46000300140101800c04080c400080d10003410181c000d50b04080210a0700010031591b04808019845404003601d03043c1a440d500750160004560300740700302c008101202580340251042d00401e248890084800d01007417108100800040c100c0300d000b03804981c100809400480140c4200312400c464a8001d29014411560240078141c090302c0200d40204460b800e14600608000b1403003220800b45880303000140e983c1d9801e61111600c90b424000a0011a1f10764400aa5903401c000d82e90740144598000210b031450004202012020701081d01940340b865400014241e0320081c0050f00c0d041450b0980d07009583c0c0e810000c060801d01510307100311440848410340101003059020a008001050400005039030200072a030b0f0004280090a48842000c60b4040c0145014544c05401d84512188005890780004a007001c98408407040c0c0740c0d0b40d5904201c0c1c11a164000c034014a42504c1400000c6240350118503400980c40c10f240c01c079116446034845856080490540c034040c01a01e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 79145442 1250 79144192 79144199
    0x5030a030c17011815050d030906090b0405010504151e080a0e0303090307060e0f1005150f031c12020f040302010314131707020303070308060109120b01260a0804 71
    0x8102160301408002c0751009039585041030030650141d44440000c0619582e6080304000c1031051005409000d0250456200007158036010b0100051070103110302103401340310300103400e141c1003049030309031541a540d480c100f51800402141c1c07043c110b2807080030f00815121044095071441c036614010301066450211600380308180308119440075006000c942c2042080103000b003000003c5881d00eaa00820010300c0f80d50445071242400801a61800c81d40603210005105031015000fa9004070884000b9100b940082410485041100c048040c0c2541100100010346d4510b2000400c1c03502c52414401c04846000203600126070010840140404011400340306659049c4954481c205140e05e0308141810001001014041c200a004000345030304448000020400d07010b603075030b9030380c05411a6180d1009183c06006c0800c11203019000901281000885603182c1c04090403554118131104601e9003400d150f41681400c000c06080c840c0070181104840748010054062041e016030b45483e1200e04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 79146692 1250 79145442 79145447
    0x30c030908032d04030507031401090b0c0316080f0f071b0507090b01020303010e0f04050715081f1805090102070804030507030605060a1a0a020c03010c0f0e0315130302030705030a030c 81
    0x40d44103601c04950f09100500003d40000f44210540e42c04c8036120461880410a0074098034181c10020700c545291414049012581e070b001e18045c0144480907492440b0101003118004011a00c0740e1403c1060404500d021000c1c2083c42d801000300e00e01405100d81503c041c203030018090b1000ca601d40d01c205020040000544245026800244055031865161003070b86504948003901280640e180100401e0400070204061401000b039049004807040210741d000d0f20300081224503980300c6c890b60440d60100f0b07440b49448800d40c0c0d0081c001d0700c0450350301c0c00e10744000d00000740380880d039650801040740840c500700c02400040d4841d03401481c1a5081d841d2801c20b90784050a03460150701e00c000240720700707603402000e00115240302e4051a21410b20400813841c000c0ca240000d40c1551800b80b00c4048030b43d100c00c18950000d8140c44841034400d104060544c2d50f02405003544400031085e0100305002c101d02503010b58039019104507401c08810791140d500350740c031204041c0046991071240500198 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 79147942 1250 79146692 79146757
    0x1718010510050d021c02040f062619050a150219030506100e030c090c0405100c020307030204050903070c0b0901090503010c0e04050601110a050a061b0903030c03090803 74
    0x78000900c1d8103201c0c0361401150050160710b00082c4500080142c0c10030701301e261241d032191140c00620038444620940c0154005045c42d014501d04072040c40203809204280c580e02420165500c0003c3c88600011010f00e4211805140100c03814011031050201054298400401451440750011380e00e82c8041c821040b900c0081000c40d083c03500b45000c1001642d2a614124443c10250a002044604c002c00080c01e01c20300014580d032280b402402e1100050140d0b001c0d01c290b031070642d44502d000704056001eaa030004170781030007945076026441c103100505094002942050175001100e0a14446c1d944104c44c580603034000001030b0001007250346040d07034805145e10080206800801203c07010a0000700800c1074102000d010f1510394020503a1640b20b04e40303022895860380c090b614041c0d0a840d016486075411442542c1c1c0c1410700020a0003006c910705030100baa41941c489100451659030240d0303411004c810107505100c4c41480c00182c1c608180700420104011720407043d0109000d064914294 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 79149192 1250 79147942 79147951
    0x6190806090411040504060f0c0903020306151e010e10050a0206011d04110111030409090506011403030301140f09011e0e010f1701020c0102070302060f0609040f0f020117180105 78
    0xc1d0101c1c014000854039812910720404001d440101e015503850070200041c01e000c4030313036030201803818044c204400c0d40002650140c81c800c0302a6031040d01c50041036110390902c21140c1d60b0041c0d1019409a1030b00c106070000c1000c1c81c1c11b050103150344411400282c8000401c0d01c1e10804940c001503405c5030f05c3d07818040540900f0b544800c0a000f4029049059440d2a0007800103081e82d81c1948500002e070f025446040f0554481c204584d5126102d60030368002c0d101036481160580b0640b00049100002078101e00034000c0050021030a5a1810701c2d448205540e400308580c000b608030700040c0441e03e030801c5542c043c01441c0d80001030310001c0075200c11003400e00da00c000c817241a40030050100702c0710810480300300d80c0c0404c003100020540d01c040900902c00c9007a120465807000030b21104160700804d10728855401c10322402e402c2d40d01d000a0050541003103800410b00b860700c02040e00022540340c201000c00d801032601c141c00d1000c070380148030307903060948440400d002ca1151032010325109000e0381e94031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 79150442 1250 79149192 79149199
    0x4150f0c060504020a03020604090c02070b03070e0108100506030a02121602030405150d0501031416080d080a0b1503090c0a05030a0f0203030f130603060b090a03020103021806190806 80
    0x1144401400a04910301440000c1c205915070010030155910085400c01942d0002c010599655480440343c0003030606004100250096031070000e03002e2001010340f4400c05107174841e85a03050b062001110852402890303141103001900001c81d6607181c0320041d40c42040004401aa2005c240c01880c0324004010195444262040b010503682d50b0701109842c02c9030001c2e10303555166100f02d60807041500640203000045e51810340000240009141c01c201d002034048195441c100e21a20b080c09850303540e000348642940a45038000b4464440d407050396000d00d400400051200b440800910320321074040d00307030b00d1948001c014050381410600c26400c85ca60100d888030345003031a10011a898400300304001d8052040042160150744007071041b5402d000e15410380603550680d01c1100d074100c40a60140704000791030040003055000c0c4c2ea02c115004d0000050482040d10318690045029500107114400315040110740701e0600d4075070348081c0c1000300400400c4a2841c5000400804000f8010141c3c0d10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 79151692 1250 79150442 79150457
    0x6161e0909020f090d050102070605100b0403080a050c010f0507080612070b0c15010602010912051c050604020f07080304210c17040317030403020f01110a0302090d020a0b0415 77
    0x50103800500310001ca515420000d03071190760301d280800c0a4044c08071480c1d00a1510780c65030b010482c0641c002c3ca01c1038455101008a900d8404e81608500028040c1c102d003181c0400091000c00c480c48044d0603804d00c2450280d2400c0c8031120401d09442119255400083d200c4003403040841d001503100794014002d0b80d40b07200701310582142aa43e14028804d02c0c50646002441024002d002c0c00124480300c8040402c404170359695a00038001e001c0004c055495030703404404413908620501c00c0301c1e10158250040640074880541c444024031002c2e1666500c5542001030f400c014800a0103000100e0144120549a151a041200d0f64041000c1c031051104c0401d00d00b81c0c442c581011165101030381100c0204510a00301c4040601d5102ea6007000d45814075200c0181e094200c000002c6100350720036402e60309100e0030040c202d4240c036000328040b4800d210600030721941a00c03950140c1110000100980d403111a01d8003c1601040300381c00004c403015002400740010b0030701d4102a90a20000e140401c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 79152942 1250 79151692 79151747
    0x301050603190c0f170708010b0d23100c09140306040803070509040603240624031e0e0d0509031f090605011806060801080a021504080616 61
    0x2510b80009500540d0308028424440c41440010181031024000380000030074690b41307400d080f00c0500c2061103010558400c511020920401c103002e2104c20300c02c003400800294400c1e946080c100d103022000016091245d4550a8014004114189000d030301b0840008685844810040000340d180c3c05c03290fa40c1035a0443d0001544000800c10b83c420f0300080125282e031203d490072a030b503202e071120156026083c10004001d110200007500e110740001d245a0300d00f020000f900c074080c0d4000d8401d0000c451a03009044003040076030505203207900110b181c00a680d41c8034001140c0061071a409041e0441e5980446a000000c01c01142190818a0500c42d0038201c09400003652120890026245c1c0c602c0042516010040ca8000307021103a440f0700140002e41e10350580d40b00109034400803500107810043c2c0000c440d03000d0341c03805042e540450b0242107080351039000d2041750780c5036060704000c000c42004000345519042c0051401805581008824881e8816004040030324255884811310724400046 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 79154192 1250 79152942 79152949
    0x33c061b110a230102070503030604060e09100c02010b060304052107111309120807140a050301090207030e030d02070503010f0507020618011808040e070509100503040215041d0603010506 82
    0xc4507882c1d4808030f0710f15801c0001d045040105000c08003500a0360001c070b42d8900700300d00800036510401040c1d40030000e49948440107a40c0c15415100c541003500420f69064072194030350000d42c1503040354000803a4510002011490b580d00440e001d03200e94200d80c07048a400000c00245c0803600c2968601d181c1420480e80719050300899021019100e00042c5a103003405400c1c640001c251941c0000070900c482e81d2003034004c1c01d00741c000c440b02c0e4006a0503103d0000e0408442c0c0c1900c12000d01551881e065a00313041d0464001d51003245c090f0140048102c12004690b420400c080c0c05604903409000128074002c00d060a64404910304400a0306180c100000c0a50024109070301c404400300c04c00401c1820880c503401450303000440c1103018030400d4a001070120b204018012515004003624050396030a00c04c5410340100c0c034003258440081140225550300c00c0c1d01541d0014001090010016044000040241c0c0181d101000a21b0b48540007995200343e0040c013948840158001d0103a440c245000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 79155442 1250 79154192 79154203
    0x6030c0a210501030302060f0105060c1011090901030c0810051501080a0e030c0a020f030a110904141e0d09030203030a12060509090703020306070306033c061b11 71
    0xc80c040010011800c880c0808000781c00518103080d060402c10742d61607080081d240c080441d03814000d1010f24000150303904141c0d04442103815000c000e09141c00c491000807020308100e090f0701c40780800a0100400d40e54800152a000b1440b441c08004908c2c6840c52a82c03c0100000e0091005842c0400b084844030107250307501c0f0040002d103810042d41d03403188981c8004080013405040c1510010030346541449000480d99041402120840c000c542c8201c101661041c4c02c20300100440024036500c2001e081501503250001d10502c1402404040000c01070300e00395403868155107103940030040707540100c8180200440c0301000e01d014600710741103801003503480c072510074402c00300b210a030888545101150f0200c0c0141c803000b004240c450410101030341e82c0d0489408164400d006444c04101c505000380703c0d800803250701c000490903140038216001240b81c4c040542c03105c0403454203403c03904444503176140d000b0b030361242500007140c0540700041460001e824100005110f0480040e10404400049 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 79156692 1250 79155442 79155457
    0xa0207090e0c0d03020a1a0711010207150902031e06100506070308013804050126040201050702060702031f0501060e0102121b0303010305070e0c0a051608300606030c 73
    0x21000c0c0b1100f041d1070201d15000c42031001030080324400804104008881485500030852581d5842c403040c2c0d031100403400c0748102d8100a100a80310010554000450b421640c0c8080c0000c003603c290264a14030040080141c5940700c030290003880800400c556804102405040f00342c400900308081c6a9024080d08418014404030100c404844118455440c1400800812098100c16443c8000d0040c26550f00103001d46808192404000100007541c034010060441212a40901a40b0f4a40041d1840d41c40300c8006d0360000c0080140c1d00241c2c034100030751903050103544048501c010501051004a4406070881002c0103960b0f4006039541e03900141071001c441131940041d40d0b48406442020380c00c843c5003000e030540e00001c0000010b20002140d8031086a0024180c0d1a0b107544400f0038403810712461050901040060090840783e640555400c9030303540c41407118514200c0c009120b5081a411200e20801e0060100800740a0005403150503410100580f00c00c0c2c2507091014550002d40241c41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 79157942 1250 79156692 79156699
    0x30909070507023007120b07020a030f0f090b031f06140d0e0c031507020115060c08030709080f013624020a0c032012130f06050a0207090e0c 62
    0x118050104035504c8080500b0031021000c07a41302c1c0e551000b2094000704120415a0740064060000701ea032400492050310440c0d0650b00d03504c4180b4080001d84692108004c00030411500ba4000300341001180c000b1030107400307039802c61041035030038075103640300b10507540c0043c0204002146110000d040d04000c1d0745a01200d401c02041c595455003086d440c01104441e6180e00d03101d05c0741c110034000707403001101d400750300c00b64003d10240d480040030210303a42c41d9104030400240120b00f860003281668002e140c00641c0c0c1c0c0350099450340e480d5101850429254000b444c070765500c0584558243c0c1104400501242803010014015038a10f1114043d030500c4001900070000107880b921030703030007008800e1410000a0b4046469698166000b4181000f0f1801200420215114280c0070101c1603d04200c01c00480d0041c82003500c1051044450f0300515804204610380400100d42c10400c81c000001926465580644854541070000d2401c2820b1f4082040645802c12098120202041000b450a03061303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 79159192 1250 79157942 79157989
    0x604110307031d0d09030311030403030f0c08091008061219030507170d0605040e01021c0b150d0f0c1d01050a0504031a06030c060c060609040c12030203090907050702 73
    0x180000c0b0000e001c400c1c400b801e00d0244e203403c3c100e1360b60030100085c180c83c02565030f40e180f81504040c2c141d6921460101030003050341c00c0301460781c00f0b211340300040c03410380304d100c066003800303441004142940d850f60b1104012694650410046003008180d4009020b5120b008160414599860340f18840107000f019007007100c0090b55000740000912004a2000d0003110a84c0e40c550390340c0140000c2036140921407003142020400034115205000b916010b2894203200201c600c103d6144900400e1484c00351504004030b1203841e405002c1399400390901140444001c1088611300c0d842004585413410f8032010b20840400c1000c1b02021307851b404034144003c1c20200c0c0e941041d00300540cac0c0b50066170300c0241058400304003a1410222005804d0080f001901107421501e40d04041100ea8001d41040070b9040c0c0c40100010341c680b5092000940003402aa801d61000e40c942d1482c1050407009441500541e00c006410101c6040003104151b01c00c03001d01d862400c050042d400075602c01c810165002807030218 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 79160442 1250 79159192 79159211
    0x210809030d0801090b01020c011e02030f0a0f030f0501030302060a1d030f03160f0519030213090905060a0c0507110a090e0303041101090f060305190c020c1e0901030807141504020306060411030703 86
    0x70412500c800d0f0928dc10507407500c401d11001007002000c1482034001a0901c5c0c410762350a440d501a0034180d0b6413540242c215a038880d000c90f00145118210502108071414807000c82a2040c0010400840b506800c3c5d07589184c03a20348481072110503200d40c010040100d0505101c6540074043d145424850031000d80d60110818048000c0d00031144000001e81c240321000071040c21741d5010b061028803130025039643c0d0b5140c0708000d040f200810032504c045a420440c48001880100b842c14811800611040034140c480040000b200c203c0c2125401e1b0364000814081440303034034039078064a0301091030103030402400e040081002117250b100da041419141c0010600e454468030312101040c0806404002074108402c00954640140c00b115014001c8030046242e0500c3d0403e0001030100041c0035550700b80d186030b83d6034106a1210b0f105a40401d02e0030003007420060148000250205100041459030030640101800d0141c0640703102e225519001b805001c0070100402d0b0b0781d100034182030006817070741d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 79161692 1250 79160442 79160447
    0x810030605070c0506070e2202040e040303091a150402090d050a08180402041d06010c0605090c1003020a09030b0711071706010f210809030d0801090b01020c011e 71
    0x16400080095081104106020b50b00480e4024810300600c200c400740d458010042d40c10000290b0810740110143e1410404141c0342d0701c1c10384010b5604540145040d80e12050300d0300c00002a00d00301c0000b80c4a10110741805401d4000c46001d040c400c1c1c06001c1030500a00460481e118603d90324040e68002c5a9480d01d65a0a022030340800d0f0001c0644440400070324019074164016502d10000e00500d08091007242014801e80c0c090311034801a0800101c103585481065410051440381041001001440082c80b41d004640c09040305d04028414184203030300700651400c0c1c5400c4d000030507206001c000c07881c070780c40b488507070132070f41c2003045c1c0c41860b1141d4400f103481009460020300c5601c41d80c0e10014103142c03084044c0c0407a95807a4141c4416907294514101e08025510500c0c1420140c02c40040c665003500d0000c075500c61013101054079149400b00842e0415084906400108401000401280041e0700032030003240402d201600d003802120b80064411039441c1604903c000412f11113174511750 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 79162942 1250 79161692 79161721
    0x603070207060827012a0c020607050106050307091b0305060607020d0501270501060e0103030210020d0f06080604020a051504170322151d09060a23041103010b07020108 74
    0x100e110030399440c202980021078040c19440c1d101000003540000e80d240246159102420031540c0c991b0b0340e51001f101030b000c0140b903070880f60065400c1c1d507903500c000a503980c041107440002e02c07203000e010607000b42c410104c1c405030b0107041c03945060504110411480750b45440c1201c29259049801a21204240c00c0150042111146110819103005503160007951f20b4480358a40d10b20800080c13050a4980f080650310032828800100903034440040503c000038103030090070789140c02d220300103803900d8010200400c0e500542c0c841c1c080c0e50017510030f00c8298108102d1003000780005a80e1642a80130303081e0b402c0b100740704900c101c0100d18500070301122007000c02d008407400741380c04c3c1c0700c8418406810280340962007485e00c5281540d982d110704000c0d22902401b2018110b456006440100d00b4061061000048004143d2399104848140102d0f01110711040c0d4070703104190541e80e050300301c0d00314144812990068030303690340702c0d03020f00042124058000448204075420b1a0108698940c0007501000700e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 79164192 1250 79162942 79162981
    0x302040c030b04020319060504020903060c1b06010303052205100c0302030d05010f050907031b0309030509040c0302030a06050103020f071707060203090a030806060c0a02010e030a0503030a0204090b06030702070608 94
    0x10f00005c141310703e000c004c44181c88091403c02080244a64681c00c00c8100d00c144080d00e5096006000003070700c100941e101a043d500312080c54103401001a0551508021003608118045100071603c2e41107501c3c3e5440d811810343e29441e101c04000d0814002416400214003050100a07511485801300746c030920640d50441c1034030034140103c0d610745105110003102805518041e004007000617034007601c240a21910071030004200291008071080c114060311030b00109406002d8104000d4080d0b407298410044104850703507006032a0b06140c0443c03010766040754070907070401d8018040c903849003288004035030b061a400103030000071142d41c0310411450b000b0748001900044c0301104110040c000805c8500c0000c1c400c5c0c0e1040c0407a43d8090400c0020302a41300e5030300c0286d101d1801c290065024101500484000030111184640142d592900e182d00485801c4c076195000f140400002031a0300903d80f80c00c0040b90032038250b16140b0700c000d54421b820712030901008080004076811994800f07044403203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 79165442 1250 79164192 79164199
    0x150c050408070f05010e03030406050319090b071d0a0e0f0702070305030708031608150907030b030109030e100c05061506070c031b0b0306031e15070c0303060905010f0302040c030b 79
    0x42e56035514400300c155a580c46180d0200c2c0070555400414a008401c4409076501a110a400c544452002170188202142e04500050ba680c00050100c2e507a0011148114540e0b6103914501101d41c8507260100100d0390500d01920005409002ca1800c5d80c1c20103a00c610084400400e03039603202070491404890360300c007425500000031614144a0080020f42c8503583c044a49410814110307402c032410003044684000030309072140c2003851440e00c0c038961a00300c80e90f407030042205c10380c92000908581100808501041c030b000c16403145410200e0740300c40380c00420300f8800110708560310340c3c80d1a4000209080d40851040b6440c0600390785c0d010584541c5a04002c40300300c038549034175040c0c10828052840703e1322100d2034400016070440402c11640b0440c0c0142c046d00c0a1290600e0481000d001011008514050310240f00354000c01c40010030301c00c00c1c0d00c0d07071030360b82c11f03030503810007034100c0324103400071400c0d0750615006001d418000711101007101da06541c0060f04d0039104004130010400040d040d50f2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 79166692 1250 79165442 79165453
    0xc0c06040f09050714120405070b0c0706020106080c01170709090c03020405091f050f01030b0301090b061002160302150c0708010b0103110304150902030307080c03070b090a150c050408 81
    0x85006119205009039000c0a000f0001c41d03e40c410140d95a00d500642080c4c0c1600c204007154050072031501c190703003141c4148115580c0c15101c1d40104603940040507404015404100d003000400c0d424064400206120005403110081d0480020844400403c00500c404101c20100b200c451180745900010600c3d01e00400c01c0001016004019610500c5250700c154280300102d010303026910740e4034106c20605c1d02d01780891442c081c140a800d054181d0703510305050769695901c0803505c00b805a50521031003480300a40074a408010051080000d9100100f10350050306072060149069201d00306070798048507440728170b0001d0b801c090041c1c0702e00084800399005049000900b03ea0540002a945400b41c90903c03031030032540144507403070200f02d03005088420208562851000b03243c0c4290340040c009400e580c0b40c0001625802266800303c05040d00c50751000aa010030b00075841e60443d00818040041c100401c040d446502d4402d2a01c40f03080000c0360f03111000031080d070080d4219001000c50005560 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 79167942 1250 79166692 79166699
    0x6061e07030c02015c01020d0606170109020d0e0a030206060a061412060109030c120213060b0a0e031608030c100506101101140a0203040204150b0d020c0c0604 70
    0x10300540345110100d000c610300051404045849030504484c02c45840e0381c1d080d80307060680c1885140000c4c3d481300c4920740d14007200148058040e260462140500c172001607941d4817030820200460305560301c503e04003d003180000c842c203804814082d04555201e0b40150b1107519485884005051036207a00c0454404c0743c8a80003015000f1036001d1085d18111005040103a490200340c851840344201031403210810040e000d402010007482c2c0350444010b241000c502500d80d0303103142e4100c15a80000c0a2034500d000714408500c1c1140d20004644824171061010b0f80c50705445101034090420441c040c4401c9482c0c0d803000e81c5040004030184091a40c09030b29440d600d4400c180c80303600c120444002d9009a6000521030505405958010781d805442d000742000c0e840400c584141046190003840d548410001c800000742d00c072440c0c01503540032401a581d08203441000f0444464400750310b5041d220020800400641c8400c1c2c41c02259145030169890301741d5101942440200b101c481d502c4000400c0c040b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 79169192 1250 79167942 79167947
    0x61c06170604030201050703020a0e040e07080a03050c010b0a0621110f0405040b0303040e06090c07050706031b0e03030a05090d02040203070c0b151f02011d010c0306120b06061e0703 80
    0x70381c05140681c000300074035115a4011000d0f44900350f1a2004140007040301900d504207503000b1405010804240d441c420b403100901c0b0b0600c0e050807003d40001c0c0c800b003140d95045c00c082c86003180071002207036a2526a80b030580301424580500c020010790080c0e05d050703960b900300d0396000b0201400c1c2e4082e5080d9105007500700c0106a40181c014280034034580300e0b0101503403c0000455055811925854035290750721020403108050040441c410900103100d0400024030411210014000c40c0c2c030041000d14130101140d218040403503081003003091a10249089850220443c0d503882031900d889030751002c0003804039041040304040290010702c008108055540e000d601560558400d064408150721046003588102083c1020642e000741141074212441c5007030102102404404c1c000461482921032000380103844249490210740d440b1940012510381c14400d807805484080150503d8081030303180c0c0da02042009141c240175079800030715103e03600b6074121701502c541e22903228259907a5062900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 79170442 1250 79169192 79169203
    0x301091502040603140402060313030507080a030c0e030d08180a080403110f0d120f030b19060305070f0203070f03110706050d180f020907140406020f0705030606061c0617 75
    0x60400107407405d4122420010b5581c0d09a02650f0001d16450a64403881031400e411070000108905201d004c10075100001c1402000d0a40d490003500c002441c6402204061b005280c44c100ea14800c1d00420700c03901255400400c5580c00c009980324000d0002070b540b030460301c0c0c41e0580c2005400c54002007400010045c45443c0d07001d1090050301e0140c0c0c0b488100c41448003143e00c1080040440c1145a082240c041c4501100200a441c2d480c3c0495148600004a085034103980c41211401e0382c81d000500529405005980d045040d51034400c9814035407000c025180c0c05404c00050101184480300c105151003109000c0c44ca1405c60140d80002d640c5190241183c0c0c401480842d1860401503040c144a564004600860750488400c110007002ca50030010040f1000704080180310b0082c00f4409594a401d010340042c2c81150000c01030f64070144440e40ca41601a44061b01ca68040c07000c0010790744036042611099404151100241140180444060865a009180c1c4000341c58000c01c070304000040d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 79171692 1250 79170442 79170449
    0x19050705030f0312070e040b040504030201051609050a0522020313030e030a08040918140309030106080109030219050102092d010804020108160e10020f0f0703021806030109150204 79
    0x1140c1811440e0b00c05180c030b0340900d0790768901840305000045c850501400325100c03451401000016403148110010b070450b0300c01e54094005039076a404002a202c103440359039014200908090301d82500c4c1200140007012503010f034a010308084114181400c1c0d00341c6c1e13811030a1403813101c1551a8548001d480760b600d842c4040540c0000c09004100c00c050502040c603688080d00480e0442c60241440002c9000e814140444040e0041e00d03000d0707070082405030041c040044d1a03003014650700c41c401030800d400e4410381d800c20000359240c090200c001a80000b915401a11080d1a84500c04207906002e8028040c80911513001302055403181c10241f00e1030284040c420b009003c0c0c00d0b201502e03100444813003108490007400320300d4207404602d0701c1c1c40403203000500000c98078185500801041c00b1810b0001d8a090040150303005941d0700000c001c0901500c4440c607241001400050b1554001490654545021100741c0c40b0000115405131820f4008040083c0c0009040380e540c00c00300034440083d0300505c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 79172942 1250 79171692 79171699
    0x1180b010e040c0509180d091e0e0103030309020a090603031e03020909010603200f0c0105010b0f03041118040302070f06030c0c0605060a03020a0806010e130201081302010219050705 80
    0x80022641c1101450080d008070b40164005902c02d06040601000c0d00e005050880000d060072050021040d042110809001c0c031035581c81c55140c0f41a4a2454920502d0180d081041b5001414099a040ca03042241103d4140c503010500356100d0010902c44003003a007140c01c03410b0421002005268020303540b942003103916084c2400800723100108a040b802501c4940b80d1042072140104501480303600006a24400781e00c1c1c441e58040b007204410401e41c0100c00c1c6a1230341740701085d00620307843c003841018014002e80c25403a00d40a401d9220100070302c0b000344003e207200c0d00718210002a4503407400c40e88032403840c243c000710642030038100a941c0e03060b503214000b412411010040341803480303402645110982903c400e000d0100e40e650700303070240400400182d04104142d8000025960f0251010014036981c0040c0608ad41003100c02c45a100700240500c2d0105011107020340182d9104455a1384404000d04056600c2e1191004030f040010724900041400a821141c81c1400000b040900840b072044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 79174192 1250 79172942 79172963
    0x20a270e070302030114102006040218090a0311010207020604081e160e0a020c07120b01060206130204020306040b03100204051207060903140f03180f01080613020a110118 75
    0x6072422400da1009000f6520b41c00341042c03201d880c60910000700030340c1c10403909220b038003004100c0b5840d0450825040c811203591019041c4070550a003411a000c1c402c200d07911015083c5003c046082d03840d00070510040410070a101c180000c044294107031081241e00400301565107541f041507554400f10402044020406200300318248400010041103200d0b4010707032545100e141040e815940c110050011070741e65002c10074055100c3c1c0c01d0110f540a0300000c0204010842c080c10600000101600101c0030345d4016814030401004047c1c00050150341140d004d40d9a586030750114010300790451056030144206098146a00d9440c0c0141c025100c0035680030990300078100501c0e50700c105a209100118004200070f20200c0d040ea01c10852440307085c0125541120009105803450b03200803001071011541030088900e6262085544080007401d1030500a242020400215090100ca00d860103c3d580007400b43d555a01401426505020f0702c1d001b00903240a1041c41c1080300c07288042114400c0c0704 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 79175442 1250 79174192 79174201
    0x31203141501210b04060b120702010c05090616050d120b01090b0304110d080a0801031104050709050603150904051005010509090c040513080309010c0801090e03030406020a270e 78
    0x210400340040c0c401656a076000100e10303038428510712050814141e0300f40d10303100c10f041c0b07548039802207000402d01e450f2400c0e600c1c00c5004442c2c40350301e405403400c01103904203503060007141c1e400015500d1000301165407580c1d0b2480003240118071030100c800186607018903010303001c80e03541040b03400b40641801071080c0101d15403200110f910380c101c0c2c056032284100500c041008901c0d080d040561000300030380060400540d0352038401c0300c4d402c2a144a00002c00d2400144104040841c8000c1460815203051101e424028006403211045010b03d9025580102c0059407100034980c903140b1581b00034003a10980e0a15007402c5459288980301d8801c100c0c1440000115810f100ea90f2504c04c52804024000c0704d41800c08010241c04c004d402028213511080b1034802007a03140c1c00071802120404000500e003d40f056000e00000f40590156515a1500705586a204408411290312076401540160744845521003510000983e4110700c0302d0400c0c060a1180316100d20a10034280c4038620055003c40e86d5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 79176692 1250 79175442 79175461
    0x131d06040b030c01021e010902060301090e07090501120b09070b04080a020a080303070903080a0504051002060405010b100f080a060b0408030a120b0d060b180a0c110706022503120314 80
    0xa0300050f075005130b00c0010402d0504000015401031101824004100c0302400d800241c01500700b80c102d1000d09550f40400d440d24a800c1200702c000f060039900500503985408007a88266400d02800780c040c0301c1070400104d000c2c43c2030084801800310203003102e4660b42c94400c0075664181050040b4002e25200c41d0203e880c1c4000400c0c0c0e4440c01c81943c032109400c2c1155142803158100ca44484103100c0280000308041e91030f00d024010580c80d644c018001c516050504030300350303040c0301e01d07007802500d441901c1004160300c0055006142c2039418000c1c415120052038800034100d503804091004008200030481c540e011009180d024023a5403015401142c7c0f46043c0f040b03903d1000110b512860310002480014810303003144001100081c141f280300344090280038803120080740c0b0352000d6580c4100c2d407284070f50404104003c050500c0001d2540504100c00a50755030304a180342441e0203a45007510f0104003068801c0b0300070315406400c0031600c0040400140140480b102400c3c3d244400f14001025980d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 79177942 1250 79176692 79176703
    0x4030b0906011a0a110316062a0309141501030b0c030c0a030b180108010c090b03060901090e070816140f18070c0b040804090c05130b131d06040b03 65
    0x3c0800d40c80c160780c004038081c00c4840354403e03801d40f0284121141000301e808001d20280c0b00f04610000341c07524000f41807400b00100d0b101007203810b10540500800f01068035011038400056585410300160b041ea06040c42415011200c0c0302c10b18510070246401440001404035604981c4204402c40280d02e82d031a54150b079001c1142c0440b09100c0c1070200c420b49902c690494420030001600d51445009203034401c104c410801d0b0010681c980d12600e02c0e2903866402102d120061615280140c00c5042001c000b03400c0318010f01c82e50029903180d84071040a51018400130000300074074405c807441c20088030f00384e40c00c0404038810300342e09010600c080e04075410309030108a4000c000821046141c04003642400140710f01408000400c54000c2801d00020f05000c80140900e004407501034440c1c0c9130903684006d07150146040c03001c001c803d201d140b440d807038258079800544420400c059140c48174607940051544499101486483c074a07420200070908004070107018410942d4240035a4035030310b09043d03840d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 79179192 1250 79177942 79177949
    0x8192007021f0c0201050706020d020304062004050603011206020c1507080112050a1407050315040204050a02160b060118061e140f030a06030c08070f0801060b09010e0406081204030b090601 83
    0x641c140c45003c0066204030010100b40f40700340d40c010300f084e2007109404203e030802ca5046035900e03501c08560044a6000c845246004c0d0300c0a0428502030402006c00c0b01400180f041c0c1240b0900b2007404010046c0d45e030151480c4551120855101101880f006840e441c020f50308140406d14500000c2000e502c0b048070010300940080040a0140480d03a506101c1784a5034102d0729203000c2c1032400b20716598240080090405952590748103030425004102c22224040c101102403413041000100510b01040401661360300612415100e035079440c01a50281d007208042c26640c0702c0b4010220b02e440d040712001c2c00c0711083c05039082d110300309a1025180710b121903003100075141e8103010304400b4500500065500c03000c20007010840c15034079a21400050042d41080c5400d4000342d03001d0110610507102400100441002400140d20b00420450b440c0720340240203041001c00c100d03a042c6500c8603085140203003070300302c2140c0d040019690070001603013080c001120f0881e0001e0100d950b0b2100080d2240c180c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 79180442 1250 79179192 79179197
    0x1605150a1b050a0c030e0901090204030b06190303050a030b0402031305061f050415031712070203070b0109020313020d06060614040812070507030605070f0906030c08192007021f 78
    0x10059201d80c00c4d100c4080c4075404404005a100b6012440c2d11903400060082840240140e16642117150030407507c0c0c002006140074109080c14007154400b80750301282140c0e0503040c150f5a07402c801d08100d002d01209812260802d00000501034051200200406403e00030419901c65403900c1c500390351f01d05156100e28000310108001804a40b4150348062204180d921810b02d50b070799266203611038000080103031800304801244181c4040c0d0240c3c06039610140510146140040036a54640e441406010310402c1c10342c04400625101d05001c51203414030740081503207250b007a1a1030720750702401240c001d9800045c4415000c040890001003620141d07644403011b000d12502c64100003499421444041d1118416100d001010400c54400c15021320603665903000303807500717808010348401c51503440281018907044080c1015507010340c0070750300718142010040f0307214400c0c0c00c0c00c8098008543c0910052a00c0c42c03081014074100402003e00b00c0c4244c40c240629400c49c101000c0f014420202e0001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 79181692 1250 79180442 79180447
    0xf023c0109150b0a1a0d05010509010b07080d020705030d05070f030204050f040c21060e06120d0c031e0c0c090c120f0912021011090a0501051605150a1b05 68
    0x140b100e5540000c201c03044041e000c6080e072981c600c40681c07a00d0701403001c0e140c100000034007610601c0700c80c0a80d41c0988020b8410681a52420b01c01280500c50040c000d09088008101d46004101503011244066008030880391180600445000204403d84040c1d0210300724038582d000740e5020340292000c03100d00074407a126080c030b6241480090914455210304010030149400000810310311000035500c0031240000f441e50070441884880d0401900143c42400c44101e44000b1001c000b80d800700d204801d2a240071400d81600e410360707484d480c40b0a030004003500407500c03030341080e88800c8000c8624024032400f182c2c241c0e00c0c24000101c4615003003c6d4002120380401110003030300e54021030b07050041503d000515845a8640d094684012240d03140140c10560112141c04110300426614003400d140c564a0300b04000d0000c1c01c2c00240e80f0801c2d0502c50081082c1480112200c0c00040139a040800d41c0d002054030a00f41207081070883e070001a0619080c040402e44040e0001c0c0c9800c1c9941d620340e40e1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 79182942 1250 79181692 79181723
    0x180f03030901140f03040f1101080c1603020a1203020d060b09060304020603150a0f0608100501020d0e0a0e07020604030909060e1b0c010e010b1309020307060f023c0109 74
    0x1698101c240e000707500c07040f03401c01c0440c00c91341501d00114401d1380a00c100b41501450b507d809440c420041d22030341d041040d0101884490300e0860221a060f500702e0648180d0101d051400f0703820801d455034058281088085a0b008054040e0010603210300e9120b000c10016132110300480003405079076110303504107009100080050400c0e0005641003207000300501c07101600e82d07001441c9284d1980042c407038074000103005c10046810514682e0499171000b42001c10750309180000303580d401b4090050f0204841d00803600c0b003985a41035008042c000c0c0d01118040c0d490705080c0a940e0301c0085e42c08400181400030001140d03500b500c01d48081d03606c2803808103115100c007660351601c40204600d65070402d10411030b054240c542440707000440780d07254001240100c43c11341044032000c41c141d4110640b50509100c1001690086461416540715061501150800c42804c030f00e04102c07449240e055001d801c03003261030b58040c4903500702840710380324100594840e01036501d0700b6902c400000400440100d44d280 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 79184192 1250 79182942 79182947
    0x10512030f03040602090109210209010501050306030c100e040203270303010f05040b130f050703050603010902090a050703060515030604060f0b0304061e06030308060910050310050615070305180f03030901 90
    0x10001030382c052502048031a107501a0160b5401c4c002c00c20150710501180109c07c40c1000600940109803d01f045400d514026020984a00e4091106881240000c094201c0c65004074000700d04d0540c06442151607152080c1c11020150140c0252655030080c40e010381c90041c0f001040724147c40500e60290740e1249860240005451861600380e801102d0060180c4117260318410700c1c41c1140060300210729800c0c55100902258400b0302030078002d0341820302c20310141e00c030451429000391180d5400500c99a0307000c411001040c281d04082e6000b501c4184641c20414444041c50042c0c0c3c0848080100036650054800c2540c002e10030710000400038000a80400c1480e0b10903004854543c40b041d1020681c0944101101c003950011004142c5540501105051080c032aa600200408075100c00504040009030358042602440380f40540705c60002d40192503080c040c62030081442d81458a481007840d014080e9080344241da00800e1103049002141d14010401e4001910f026018619001a01004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 79185442 1250 79184192 79184197
    0x130b03070504060804080f070503090f15220302031219031b0507020103110f0c101109120304030f03050a03050901050103020a0b07050106050303161a010b16210305010512030f03040602 81
    0x603500d000e024059907144460343c1c0004c08e01c03240b09802441e5190382000402c02c2210141c0c0c0c00500800e54868178181c00c010394404c41d0090010442c6c0072200194050349100c0801031030300029054091062101d01c21061000a044610762200c201c00000c2003511048080302d5480c03100104960904450400c2c0b640110000d01c011401850b001c1049285040000c1440c0e00c08a516480e401d000034210f0045032043c410f002c075500b8042c409000390400c018031141c00c1c4c0201000184115602d4084040c5201c0c00c0040750010765000ca0b00750680d40c0c0c0e509015050307800100b03416000ca07080200261800006100b028140e0340d0051509075a2400c0106108050300a5a0212415984d4a00c0422180c7d01040a401c140702910b14880d82e10540780b80496180f8080100181421240307001400030594500a44180d043d4100e600c07055040c442c141001500700d0400300581c441e0180c0307071541c980d076130580100381694819500403032070064850000d0382c3d030312070401c401c5d134081002d0000c5000181746800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 79186692 1250 79185442 79185451
    0x3030405040f0b0a06020c03070501020307050706030e0703060609091a0402090a0c020c09090a0204060e0f0103030c08090d0c08011d030f09010306080d0201090b07480503130b030705040608 83
    0x1000640d240303484021036a061300a8001c0c001603444220342c041245420030418010344001e20285080a100355a940c0d40c890b00c03400b0704401d00d074541c00c0d03011880380700300300010045400c5a800e004240e034450b00d4a0003840e121b08143c032040c182465040903501c0010030680202d070301500b4018666151107400c1c008084010140302140101138865016580c1c00c801d05008040c0403002d0018001c29104200c22551268002c461000c080010400290104003c040c116501824038806045080ca8401c0c0c880c441e14416039808050300d0034201c00c0c813003000202821707982244001c00c240001d000741c02002c86442c03035000907954800c1245400080f44c02d030180210300d01c10306005c1405900d6031440c0e4184203960903203e0041c0c3d5030340da16030203108018840540100c883c0c18014400c48854018820f1159004140411a145210740c00c1225002001540c1100c0107603642074a440002d280158990b80f254000c8030350b020001c10041190341100d4101c80c09609a074a441e840c007442d000b41030304d18420007003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 79187942 1250 79186692 79186721
    0xf060315060f1317010920010210050c0705010e0f0d05071a01060804050c091026030406050702090906060f15251b03121b020406060306050108150303040504 69
    0x1141294402950019056070980d41030344140c42400d2581304c1d001c441a1280600060703051250140c0400c004046245240740017940c014003005103080141d01c3e020000520010192800c82004820000f00d00903211440c401c1c0024000d520391125204c0c0d0b500c00a071803401c825040300459003e464001e2009000d440c2c07040e444801c80f08402d10401d04000400d078084408101068200800c2000911480c0c030307020001c0320f06004900f0b100000030081c4072680213072841c1740f00000492454500d07150020422060a03000c0f80d90780c42d1240001001c94000050490080703038040c0201d0592100400c2c5c8500c1004042c4c0000c80c00180781c410441c5141e241407540d90100ea0412069402d003070701c0843c95100303d42e0050100816401440e1003100d07511180c1c50366066011b500c2c0c003400002c3d15076421065501c0325260119103c0d1500d1041c1c80100c0756000025440307403410a0015005425401820484409880e540304c15aa05019402c040c005041b2240e81a0400c11061181745020f510241e041841034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 79189192 1250 79187942 79187947
    0x409020714060f07230306090901090b010303110f07050f2224080a0b0402011d091014060c07060c0305091815060c0703021212030106030e010b0f06031506 68
    0x240c450508012094800d8550b02c0d541908011345103800c12080890903210000303942062118814403000d90001804440c4078004202c003150f001ca42c250030001000750400d41d00c00c0156581c1c070f0054a800c1520160700d400340a00c07681140000c00206403542140c3c009482c001040088030f04111000c00070103480d0900002605441084200d50b20800d101d030004038112510b02e440c0d04103041c1d074600003503200d889140d02c10051280024400c0c1c015640259082c02c0c0414a6031068503000b4240b480504076940206c1004100401e0111620b000320440e040c102543c5034158503003040c13090a10a4840761601680b01a0302007103ca4403c028001529009141c0703030b41030200c540009805130a05000138055240810f040c4010301c0308003004050b0b030000440d03d880c03420700b01e00f1032140c0320132075440007134411160400000710300320040c40322044a18003d03030069542d6868010103070042c50000042c51056180c1800c0e00c0243c101a00c500700d00c00b1000b0310081c219aa000e0600c121801071414480c1c001030709 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 79190442 1250 79189192 79189223
    0x1270e0402061309020306040b0a030f0609020f1201020304110a0303020a1217010602011e0606120b0319030801090c0912060b0d050106060302040911090907050a020c0306010312020f011104090207 86
    0x742c3c0803001030b0240403400340c0d0f242010001c10054810817200c040c030510baa102c00308001140d22010585181c0d00c8070f8041050130701400001c0c60000d080c885950016101d034041d2130751130419401144201d05c03552030b41c2050301020083c440580c0381400000e0140c6e00c0280000d0100e0111038012948046a24140d01820340d080c910503503900c0b0a900100150b91256040c2441d4408894081d100f07041c1c0504c1080b2007031800500034544000d402d80c0c07444c81556103075544200d0314107020f8017007142e400740003c10034030400707107401409081c00744641601d01d45003065484141e88184400e000301c4070400d07402600c17070609440301c0c402000c168100e281e00c00714003164140010400e010302e0000303242680f801a02c49103170400b80801d840381c0200048441200b000320810f0340e0748584806800110b98030745562038a4081c0c0341030340b400d505920010b03030600c9018000410041c488020343e032022241d43c2900c1a40031100103880c2a240c15061008505000344814081401c1c02d034084c0940354041c80c07003002512035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 79191692 1250 79190442 79190467
    0x9100807030c0611010b130908160317090111030f060102010b030a0804081207051905030f0301030c03060c0c020d03140702060708040e100308030a021b15040201270e040206 76
    0x80d6403044a040544075410084244c011028204000c2c4140090055034040b40019048241c6801c0660038941d80d04a402d00348500310007650507400c1d0150070085a80c246003806003104452926450258505100142c40ca02d018002d4519441c01c05031008d04544a0700f00600030a000103150604640d614500c55507195010014110b419008a040a6a85007400003060428030302000c00d242d2400c0800400002910000b0b0a00d0442295000e80c4408607007032800368250302c101181380c002c00038040000303c184074039113081004480c46803030100502d5a41140944260480c1540a50f1140040c140000401e0084090700e10b030020714105140b504100d9800588180c00c13824090340c0000001c03905204030202c01c0d0805801c045008240300302d547ca5a0346502a5201c01070000b5450b54002c20f0317480f2600403400e001c0c103071a042c1c0c10a595030285250110f40e072100c0b0450301a80061041c800741c00400c01c40748105200800c4202a280c131503420103401e030603117101c0940700b01d820650800c050592101c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 79192942 1250 79191692 79191703
    0x80a09050303070807120b09010504050a020408030c0304050a06030506130f060506130305010509030c0d030c020304170303072d0c080f1902120307050307030c03060503030d0903080a05010e06091008 87
    0x802d0344c442010b01e09103504002e003180100501c01003510b2806001024640d9614051030464100301c90200c0c1c1070342c82c2c0700008041d025079800080c440c4800b04501464050210182c41030f10803c0e0b521000155840340d007102501c4080d41c00c0798004580c143d15020304813140c1c008400c08a82840c1c00f00383c040e510b10101e0942d5120001020100d0710012007401042803c1c0111074000814500075420900d4014082d9140c0e00302903000c400745551020b40014840c003c3c0140c800400e09020300300c0c0041e0112002988a510031a04000007070080c0b00601c09d0700311070107c0242e1381490440710440001c01c43d1030503107048031008416510888288251501040c81800070f280035a0300500344500700404c007030040d141803501d00c0014960744042c0308111001c1d80c0041500d0780b2003038a00d40400e040600103010340003402c0c0e68002c0358050100007070402c0784031419001080450311030703a9044003942d146d000e220100c41382801521001544200030650611780444850b0b0000c4404010300c000036903803aa414940b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 79194192 1250 79192942 79192951
    0x8040b0403050105010801051608150d06060305060f01080304090221090f10020a12181208090f0a020a030609080f041215150302131e0209100c1101080a09050303 71
    0x24000a014000c005003030254900501d1144001c3c48103040c100360400c4803800e84030800d030400171214009410f451101c6ea0307200003c0c0001d8406035000f486030404030040c0495010554052140d9404030b07520b000d1500081c1c2c1280c4a01c4003940c203041c04c01a030032006e035020b08010800d1a0155804d01c051080100300f803409150108001c0c1444045643c2c0c00d0300b000f00c103145180b8540e10501404c08981d030880c0c01c0c1d408503240c0d843c00203000061003585050341e0000c14000340848010b09861214180c100300700900801703205045074030440340c0c00b450550350080c241c1d000f900000400e0f002c00008c0d00700d800c01900248180442802c0c0401918030521640086d400301d030581300c2070005c000608c505a0b100904204008105102c20230101d444000041902e04c4002d001b40040c10302a403039580c1941c407228002c62441928000b148140c0d88610183d000903d0503803050714040041a201405040207d40040d4000c850041c00203100c001503400ca44010300310b050481e00c07080502c00040c1d090004501c0b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 79195442 1250 79194192 79194209
    0x7110c04050a140702060c0306040c1e0c02031e030f0c0f03070f06050106050c0307110102100204060801030c1707170c10030c08010b04080a02060708070204110a02061e0a0902010201090804 83
    0xa035101104080c0c40f041c2d01410010541d003080041c020100240021a607000c14103903008580d816009c1c10450395640b8803007101b0159000b40c2c0e11009103980c41851540b59600031011074a00c1703440a15110980918500c802145501c00c012000c0c100c080100a0b02013001001d0982d40c98184146010742158003a003002c4600400e4206401c0030061944501c81c007600d880c2ca00305d41040503c01c0c1c07003541c911854101038004203580d21030400f1a0320800904207200c1d03200b041552036565445001c4c00d1000207020031920301c1210341d40403800c0064040e180c9002030b40000240f003030a142001d40075804035000c051040900811020030b245840b4507001401001141d900041c43e010704510090804c0c0043e008404400d904001c20820a40d0004010301c40e15012200035a0b50321039072516060341c0c407640307100941103030500d40060b501600540c06880d0a10140c0c0940708540c1c0c50507015050701c441e60300f02801055604d0041010740705d80c0e501c0106600e1060000161409641d101c1100f140c0017944005403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 79196692 1250 79195442 79195451
    0x1091b080d020601030f081c021c110f0426070e070219020307090c030b0901030302070314030c0a08031e0109021309020309030403170706061806080c0907110c04050a 73
    0xe094010081d407403508000c0d101802c1030b9411940d411120440180e00039040c0a00480c461800318200c00c2c05424811b000c0c0c400f19a01c1029480e25a0b0300c411340100004060b00d001c401303860380300348842200c03880010500402d10b00784c149034410031f8200030f0524102c05d0846080047c1001941046031102420485001d80082c1c41c7c40c2c03c0c0240b0304032094090b410068840e995480050f2000182c010640d0b596134000302d50141850000c9001380220304186910441540000081c15000718601050700c8c06481103a600c1150214030960320b104404962003190302180902002c00c4600b006542c2000340040001e00e004888030a090107614203820042074141c5c006007014440c095154a03030b0080804407015401c40c64007a05240e01c1e4000d038400070340781114a00482c0045c258141c100c0300703003551080e01003042c10f80391515606203192040211081a1616001240c254030005540d500060020102800c0341c0d03940710b00315401801c03041d00c2412071160307000c02c0c0b000e0356031400707a54440c0d51030080015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 79197942 1250 79196692 79196699
    0x70b0103080a1106092107030c060b1201140f060105040f0e0402010c0b0405151b090409020a051309021e060d0e1009030509030607030c050f07020a03240b01030b0f04090501091b 78
    0x488a00d804100040401c030030098180080e070845000c0783c006030030480006510341558033007000c8c2d2034a00c7c6111055440e010181a0711b030b409600c01801a0f443c81303d5418640e5070000103540a01c200e0141c5041d120b01c1d55410403005140b001c0490f800b03403061400d1514074016641d020080c860994003140c19401101a0061800f01c2c2c448450380b241302090147d04e203041c40c0b00103801900c1803209840c003031030711441c0e658150748548012600410b0040c11010107844403080e10400bd114040040384503403d0740404c07111500700d0001c80c1415000c01011945844404165000282000c000091050040f00380d80c4c0040034061141c0d03a4014007948905c0d035207018650403d800c00d42c1c01801d4100349440e00d98102030290303001d002e46103030700c0350407050036521640c5000280c502d131410790004181d40c40110744821450a950460400245005028441c10700d100b40103500f51054100c0780303600004140b5403581c0c1c3d45410b0300b00c115060300a0b80000b40c0006180c50b00e02d401c0e81d503032154405404c2d4a03041007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 79199192 1250 79197942 79197973
    0x9190f11180f07020c010c062714070b07110d02010c0602040602010603060509010228020a0b070e03010b030a120513030c151701120b041b090f0c05070b0103080a110609 74
    0x790f50104007031020b000316146520002c0c1c4907040d0241c0c081e180741e84c0d40c282130002040305281034084030b0650701010406c81103032820703e110b0205c80140c1043c50240403400038031030b402101a601c00c10f9102e07105003024810795040c0000c00c210042c042c0d041111a1300900c011459901c01440603045603400400d0050035820190280c480180c5009120b070700c10046d01000490404001c039040d00c1c007404582074804034883c01ca01e00078a0044c00703824003143d0024400156000081d0f421600410303002402181003038010140c894582200250120011004008005101c0c0e0020401c515410342091010780d280d0300c400e0020304139600412a02003410340c06203a1181c100d802280c441101078000c6050358181a1008101c4000590042c0142c0441b40032801300801e40582c006005032a06040e0140d03a43d640120b00607101184452094500d0304440c02c0040d88a20b04a401068100c4d5881a003646990345d80461507101c0c000501c00c0185107420035940b400e050141501501c0d045001340100e0340d170202c69 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 79200442 1250 79199192 79199221
    0x60f05100b0403150902180f010e0a05040b0c13091a0103050603060408040509060a030b090a0c0b042103030b030304030b0a0b040615080a06080f0105040b09190f1118 73
    0x74145070010710040000488501000c07104c00f0b000c00010a00407903501c00b00307115003040f001008613206400f0401c80400d480f02d0089048451400b0301d08801d480e0160808110b03801964054a0740c2c070702c10000380581e0b000c840200001085914200c0b082c6944140d18021103100034404421280c500b0400d040c0c0d03603854000d25070041402c0300608032604260b5a45409131140e40310381800b8818110010300d45548011154008540080f0000c00d1450400c02c1c40f80c44109184040f501031080c00b201081030f802500603a0203950359543c555900c000c104007154101901e61004904150701e6070b0b143c66080d181800900011445031000b030000741002555401541d044da603c00340101e1501c14104680c1c0c5141c20410302d0205a030800c4c0207140c0324822404040c02064020807003600c2204c8104108900540c0858807403809000384544503142d00309590303110f0007070305000905400c041c42101c0104440f518005e01c058481c85542d10140d0150001c6154070381d20360400310010629108110315035041102c1d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 79201692 1250 79200442 79200449
    0x9030206011e06080406090204021b06180309010f0503090304150203031b0307050304020d0f05240f040302061803040e0c1b010b150c0a06020c0102042301020d0516060f0510 76
    0x40c2c1c0d024003420114001e004210040000e0440c0d0b44651444041d5102c80d030403602d10301c030084608615040c103242410769640301a5481980600002483c00d081000030051704d040340d90594032107000c8144204111440c4d04003030910719480c0400c0200041040344502c4503007580c1441d4000e581c80303213004010f8900b0802e02c0c40c070786960100c00304200302038aa485402c0b642d100342d0490348a00801c4540c10302003000200c1181c02807240c0301318608a580383e400d07104500382d0b03400c0ad0154941555141c41c441c029004050324004e005d40c0c81000407908068203404c81c441308041c003104603810301e40d680f054441803000a44d560824420005080000504064860500081048d00a020745a51100496038807070300605903022206e400f00d41c0d4664101e041c03003004a440c0c3c004005540b03a28104c01d00d18003d5101d4411424400301803400c070b00b60003c00400030b40760410160040e044960f62032105607819440304600704154101a038010000030250b114014400c0f840050000300da141205107800c541c4c61a80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 79202942 1250 79201692 79201739
    0x30f010b01110a0804120302100501060201060f05150415020a1704180203090c060c0a0209150f0102120a0804060b0607120207080109050703080a031517150412030b0f040903020601 79
    0x50000c0f0109120b03404036411510383d5020401c5c43c4a65090490801c1e18142d02c180b5954240000064800d50541100003551f404015040c0c4440c0c5c4e440811408622400402c0030303854080c40100100c407041c0303060320741d4142c0d130740151088144c0c5503a640d040b03400441075408941e80041018050715660442c10409078801e44e504519508214090303e5580703500800e03191061400043e00040700105100d03160741554058145030703880c2040e4170001001b418800c80c45000703140b450204c19a56100040100030b15603c0303841d80d85080d1002a0455208000400c1030f141e20b52a5214003101c2d843e0340c0014840301c0d000b0701580c60203640c1c1ca03000a040041a0f8040320742c0340e0418411901003200402c0078011030342e10200303090f507c1101d40016006032034070851070b0303003104680e0300d0025180d0440b03410010b0403606802510000040700020400e031200c140d50182800041c0704020403828029401000d00200c0105489000303140c1310002030964003214005c800581000004000c48103100108007008221003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 79204192 1250 79202942 79202953
    0xa02030703021501061d010207080f0a0501140c030c0d0212041b06021204121109010b070309050d0308010504050a060911090111030304080a141e031f03150b030c030f010b0111 77
    0x40062801b076624550045000034400078501c00ea00130032012005103041425103a0545d0720020b103d450707600c4e070b4501390798a501b80001d0442440c4c1c02e450003841071080c50720b01c900310b480f80a4a905c0d84e800c4044590a0a0ba081201d00d5007080f0358040d50b44a6486070000c4032142c90045072550601300507500a00c15503021201c09603008403801d086e2801e9424003100d1403140043e80c00c145019080e001d005a411241e11000841c403445158010003480d0701036110550045c1c7d580e41400114441c11f40003400103081800144100c0c5410b80109822900b4103101203501a100d00864045a105000040d681c940004580c066035801215441010072100301842c20b524203903d82188038415025104100101007500030007061005003994140040c01207099034104d0050003428a650041d515114111a20088400c3c48850400c0e45030540764810040b240f442d01800510014110b20809254140910030032429030791410441442900b5500001060070740c05500054071800c4001c0c6208540d8004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 79205442 1250 79204192 79204199
    0x90504150e0a080f0d0213031211060702060402220510080709020403020f010f11070308040303090512070506131208030f0f070206010303080c0d021c0b0103090b010e06150a02030703021501 83
    0x140382030301c203a40084c2160a035900ca42c000c80f02e00034454281e1a01095030740c0e08012081c001440b00c40700c050700d01900c40803d52101440c00c4c564070b50b82100d0580069116400240040c10310054101440c907520010601c11120810030300203460b8200c0710082800d4140b00200007042040000c10000d11850703074218a46800c0d500440e1040c001c01641d541409010703100140100e120720100d0220b5001841a520855168906a046980144000d40c005403601102144914024004c50701a0b10341200a00c1c00602d03201c02d210395500f0801d40b10304040b030b50075000181c00d0f0b0754046400c8920321030355019a40c0e01d8020000010040007500391007880ca50002040209500024418152074041c01c00d202984e030341500e00c6480d84181360324190318a0000c500078131140644c103440c45108082d00c006001e00e40d101c0b0011000c6031800e540141540c40080010003c42301058001034007d03501030000c2c800808101040e01165210001038030059200084480505078180005002c85901d41030382c410b654507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 79206692 1250 79205442 79205453
    0xa1514251101140706021602030703050d0305070e0907030c0908010f090b0106030603021e0f1302030a0e0303100308090312040f030b010b0412080a0c02030607020106030b060d05120a020304090504150e0a 89
    0x1c4d0500040665900280ea041d0201c450208985e03d5036000b4100c6a81c030340c8900d40113807036592044122001c80e0629001c40c903042d018078440d60901c40c0140030070440b6940c11134220b0150030714031312240501510b1540031903418800e0165564032500c0f242e0101e140314003440c2c50403400c00305030300440805203820805c0c001030f520140c071000204c45050048041c0300343d103c0000c050741101c01c4559444091071035492a03941c056001b5520031105034400b001b00c44a01c400e0a6101e10044501c1c1c0c0000e60030080c20b00008614902920107444040c0403502e0050003101814603a51240c0c12100b04894040010007c000d20400441d000d4000e0b40d003280e081c24909101c0d0801105410401444d00701c01091589451b4440e01c0990400381d002011107a550616040c064000c00300c80c00191603196051000855074100485000b4034154010001c1000d804c0d0103402c03690780e402001c0a0340440c0410800066910050b001d0070380500d0088080e05400111403101000300c2c0c0d4000b01035080ea40094072984017049 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 79207942 1250 79206692 79206697
    0x9031c0c0207030213020d0207061416020d0c050a0c0b0415030e0d0e0f0d0b07090e0606120402010207080a050114010501020f06190204030606090c0e0a151425110114 73
    0xd5061780c0c007914001e03908004002900410001900c041c3c4042040c5041c4a000d40001080312203189501c10b03542c58030841c0e0303c0b0000408a059001d684078018031402d00d0300c105469501c0394003603425180211001c5d0381e08003000d003d80d8821410200c001c1000e011101e80b65102e82000c51550904022450b110501c0a07100d0256461903414049003290303801c950f0311801840c94111600500e244040d1080d8500480e00d0784081e201c103c0018940000410b03001c00068805001c1c000040c0451f0505089041040e0a8074000340100d045016429000580a00400a5140c0300307110720004111740d070740540e403080314410503030003130381113502610b036440c0d041101058940d000011440202d4600b060889000040e21450340024011403518800041d00380d6241c0c00b819540c1503c0e80c80d100031031030301741c1000150589030290f500c01e280c0d90442254002d000300000520124035101541c10849041c0d420012404482428840c100a801c0164100141c8020141800509080aa01000300c42e48039107443d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 79209192 1250 79207942 79207949
    0xf0f020d0302071502190207060306120f050f030c030a08072f120d0501380c010f020d05150102010203010b0412020d020306091b060304120e0406050909031c0c0207 72
    0x10790000720542449000d8150480d4030f940c04905558036000c1c1000174030403002246d1114018080c030100807540d14464003a8004480200041c0c0054846d680c03900d035240c42d041ea508407018442c1d441804905881440075115040500e40075503240c3e511103001031b010318001040c0400704801031446180c5603911066590a41300b6180d17206031000d0b08102d005141c2103004082c60007514012881904c0c82c42c19401040c145c8011100c0c281380040c080880c902a240c0705d24000200090405140000788607013030150211000c42d2001181940301c49441200702e0b40203070504140c0795200c3c420042c2141300e40040d000c0c2141e0070300c000c600d9507140c5804054940214041c0115031b442146e03400c4207640e6030055602d20aa00182510694100b11140507602c2d0351070160b80e06204d0604000c0001864100d094030702c500e070040c1a1490020405004803041e10f0040f0b41c01e0f03401030341c03440c0200700c540f21400300340d10488081c002161707144181c8901341c030728100102e2480019410800f01c51038140d400f00300381c0100c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 79210442 1250 79209192 79209197
    0x7080a0f020f03040b04140a2402010612060504020f031203180c06030109140c040605040311041b0305091015030b0603120325050909040b0903040506030906070f0f020d 74
    0x103144008404030b060118a1103148140c0c4000f04012994103c081c00030300031143e5251840702000010b00600c0300c5d01d0003611400d001d2400040c0c41084000c03a642e01c4100085c420701c00055180d4444100442c1e12000c2501560081d42d240200411410303c195138100c1a5422001002c1c8070600f6101d4180912000300492070282d51142c031500d502c1000c0200d08156800105110345941c1c40304a004010700f00c5050245210084501290664106900b02e9050303810b959076240c6010b085d5203944039645828071a558100c7d50310300d00410718000120501c0c051036182c0e5400709150034241002ca1801c241c2c00081720240f49000c86180c40c00b40000403000440390b0011404110741e44602c0001d00b083c0d0800a205120800001041120180c1ca008104001c2180002004841040204540b41c0c011200000c0c1c114810202040c08101881961680040c200c0d086034030b811b840700081802c580040d00c2c170100702d0740110184082a50803545403401d001d01c52420040480640e40020759801c50340706c0d0b8205 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 79211692 1250 79210442 79210457
    0x120109021516021e030705010c031718100903090501170a0b04020702100c020a0608090d120209040c0210061e0312020109020a0602060a0e010c1218020a030b01030606050607080a 78
    0x82c0d5910400c50485150001c000e10200e0b8101100e44404070b04403410a48030b4041d15074040341560280c42811070746a059910300c3e000c01c00c86851200d00d0762016000d894995007020300c00066000410a40340d000001e1007011840e48000d26024100e81000d42115050200d102e100d02e884103260084560700c000b140b400806c00c08130352008117001340700b4040080e40211804500003440c03038101d0901840705100355069a400703036462030308851421301900c0240b1650003c043c202c0000e88603040c0c0291351031600100502e0034074400001012101100d81c003801607048500c590f0603001891281e0402010321980059500c05551004151100746000017030000d00c84244035200c462003544495000c0d80c0c00313048602c149844a2010359200c100701d820501c00b0303003000118107030b46c0410b014803000c3c129642c451004015189505102030708406152801d409514204074001d40d4401d041c4034021401103494520b954110300f00385007a5080c070303001079000d85d508100b031100054a000441c0d2200240e03141550 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 79212942 1250 79211692 79211707
    0x7031206170a0506150616051006140306060307030f0314040905010b0c1605011b0f06050109050103140a02090c090301022106010207050103050903090607031116051201090215 77
    0x405054011000c06520398140700c1001d20005448030840d4043e90032a4156500c5504918a80b001d01c410950403c02c2404009080c0a4020303503464014410380c2640c8550003038000d40300448090703902800140c0090b9000c41d40604051064980104041c1c02901129041d070300c40d0002880708079001800c22112511804090038680143c0d40a030160700000c0c08596518441f401854002001048260055038840451102c1000707603c1c0880750103845903000000d17034203042040110040300507a0304400741c04440000a185200391800ba040f00900000c640d4114201101d5480050002800640c8090303121009651940001940040482d001303da849a2660109001e0300500200e40500440910940250303000b494009104010a030b08544c2c0713182d0388400440a40380c052381c44c48003c0d0810010440b540c140346000709a158043e0500140d5031100301c0c6814030300105042000c817181105401407100c0d1a190f0740403082008081e0080c001882a5000103140c0d0b099002c3d001020340c1c001420782d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 79214192 1250 79212942 79212977
    0xb1c172d030a0605041505130e01020304050f060903212205011a03010902060702040e150f0108070b0a0f0e12010c03060f06081b0306010e10051c110703 67
    0x20206a000141120080e6051000040c540d0401d550000c5103d080800119490400c0d11401c034582c462212100720312071500e8248860000490300d1042c0258403003003d000980e000340002c42c02244108000e1071810307044040c840c1011000307410b0181c107420030003c40c841064182d0b8441e00d05412424001c81a80300d0304802d4101d800c856200764190944880c401c02800b0043d4001001c1d044910081905607580008150885054050003548044107200c00009410164403840b0030707170700c05021150b5031601c5c06d140010006003146c01d1041e1a010300014032640c0000d0042d103005107020150282030001824028102d2440c40c1404002c01164a070350860702d0381d407443c40b00c409a100500801000c3c905041c010082c069030700950b054000c0c0c8610000354544076010b120700c510f094002c102e08800c000b001040c81d962020b0041410004079140c005042da40d076030280d41589406484240c1e49911010f000140040364444141c4854544913080c8001004501124112907040c50514210b44c100c3c40701 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 79215442 1250 79214192 79214227
    0x2100b060d0c0503071d010912020607060213031b12030503060a17010207030e0307060203042303061e10060807030e010e03030723030606040b0304051f0b1c17 70
    0x40c0080582044214000c150b0001c00642c081d00c00c03955032004441046d07050440e841e51600445000132001c01081003000070014680016034801030216107015903589450046e40c01030f0b901051000c0d40100c04104101e11107011034038030641c0d103214080c01d034602080d03054001c0c6500e0380a414484000000bc1c40e66661142e000b02a2040c08a0550002d428000c868001d4010600840c0458042c0035418400d14000540c10125441507004504d80740c184001c52a444000c405802641110a030a0413aa0395044c0b02c2d1a1190341540f8011040e490120900c207244c110103401075100080303000301809450345c804641e59201e405410040707a80b506611440b401402c1c2400e040c0a030b8000031090001c07882c0c1c03000d400240850901c5410006940c12001c0030641c0c0b01c191015580701004102c1008800c416034003840c1c2c0b050240040c0c410303024420b070030301458404407135401140c81c0e6550b2240c042450a600c201d407241c110000800110b80b51a6140c0c02c0c108001c050507400240d010591003040c4001c44003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 79216692 1250 79215442 79215457
    0x207030201020c0703050d0909050f0c1303050a0303050403081e0403030c2706020105180307030e0103020c01020a0810230405041b0b0307021c0c0308060105041d041403070302100b06 80
    0x201c4454170b54909241d40c4503402d10482c040000c80000000036442020300503503015034215256036466403100074030700c1800e51248103078880c002000c3c0c0703002010400c04d0110f4003455000351804501d928140c640201000c2c801010702c10361410190040c150002e0b510045a0701507850b0400092100d0240400d94034046011100c9007800013400000007041c9890001400f00c5625400a01c0581c44184030302d2080d140b200c1029220b03503c01d0003460b021a1145804003000401810f00601d0800c03180d8402c0e0076070740000e19000102c1c84000501c82540c034007400304801004100d82c03814540e6101c91202101c5143d600000e0f00ca1a25a001304007488000c00041c600e2500101d21200b0f500e50f00c0ea180d0145406c00ca41520142c06687d120007003040741050080c055800b103503252807401c60195825200103001409241c1046414400841c0408200e8407021780d092040d00071050914007450b00440c1690490345c0c03030000350001d124140001f07800007000c01c81070040d074102141e180c10358008607034980100c11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 79217942 1250 79216692 79216717
    0x9100521010b010302040317030c040b04060c02030c1012020304060608060f0f011508130c090509030702040b0303180d14030d0504050606092403070305030f030906010e0108060a020703020102 84
    0x148441140e15440000c03603080c6003000300034429100c80e1001542240030310f00c4090300e003842c40d44074a420fa104075030003581d1002200090905043d00c6003c100100c2d04250040700109188080600a40c5001c00c40300b400108110350102c3c84c400a42c500a20340300310311806042d8244c000c40070404020054100e50b0180400e10308844881c030b003d94401175219420750300d007038200064a00100b01d5829a003ca48010401e80d255082d40381c490120806100711655025501d80315180808030320318903180519401040f442008603241d0b401401040100c40b00c481c0d61502c0f0754030030040c1018203070703046e02c0c0f10b0310089040f5a54488111141010515403c00007c145424080024490003a0900d0b0f408180514011801c81c0e030503a844030b00707001c203440060b5403034550a0080145468031031400c0d00d0b0309094440141c280c40800d03503203540c1c142c40c50b0400340c580c00c8560008805c00c0301907103040102c40c0c010040e090000c4407552604c00713050f44895024000c0b0f141c0c1034001503840c081c14000d40464403074400c0103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 79219192 1250 79217942 79217959
    0x3120c0306050a0b07080405060c0f0a03051b030309060a0e030706020304031205070e030a0b09160801060602060601091409070521010302090604090b130f0b0103030203030702010f0c0c02091005 85
    0x800a00a0103180690b41c031805a0800100d4507003842c03019104400c2d4041110380c5020304080030000c00740c1020425200f10301c151008185081d5091080008451080e142c0e2a2213040036240703c50100d00c019108501c1d0b62091041100d4480c0024001c1d821017150b0000042001d10880020b0941c42400c101400c1680000180320070107500442c19844001c20340c104002c0d94030307094011903031907944551031603050740f1803041880840c991803d0943c200100300d0440b60804955208400703035008662200c00f859660740c03005c101c0a5010710403594060024602000343c02e00782180503140d2549640050300038072040740028009402441110012000602100f0140510007841398106400b400224003664102c40821020708107401400d80456201015901e00d5030b500e81c881e00000001c10341610441d12560400000c00c540b175030018043c1d4000d0f4003440d40d900c2c08050181c02e481c01c0402c94175000d4642004101016803241c00402e00d154121500520350f1280a00e605040305c0b103070009540002070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 79220442 1250 79219192 79219211
    0x1207200604151116020109050f060a08150a0320190312140301030609020a0806060105040b0d0f02210c090a0902032703040929150c06070e010216060e0d0312 69
    0x1c2d04a640d520310b100340d031f4031102c10791110140324902c0010b44003143c00c030718188103034100c55000b0f400003a0302c070440010312007914040c2d03030002d500310006070300a503666104298a00b0401c10840840d88015030182c40d604110750590701172120070b011130b1001800300642180130841d200c2c400c4c480c024000070800c03607081c0ca950b10790401030700400180e24228840c06c50310100107131329000452801d1084905031151410715107000c0001c0500c0e0b04c900c011804031583c51700300c02103144241c4043e11603421480e14140d2200894003400090150203004000d00d072782e0901500b00256682c10a15091b611000070160b200e450f02c200e0411500c4000003030030461602c850080c600094004060401c43d00110014041c8000000966040a0064040400075906222810902d040400c00403c0b0301d42186503951a2070400c007005420f00005549110000707407000213280301507a0400c080703907081505225a2403038034604100900b14210780180d00c1e0042c8036204400c0240350188040d100c1d820000b00301440003804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 79221692 1250 79220442 79220467
    0x50a060f1b0c061d0102071401180306090b0108060c2505070603020a02010b040b03031909030f05070504050117061503030d020309060604150f1a0d0212072006041511 73
    0x4980510400141002c0300500c101401a0004901c4207046e000f401c009400d0001e0341805140200303082d81840700f161144191500e0010744000158000c01c40029826600d1900d251201c406078002e2070303a548400c0c18000c440c07809500f04d810307201440c4108441ea24203a01c05505030074000c1c8000e827580c014a4000100180c064006240c1003240d64020800303890003204000407600000c031031a8241d031007030041c0c14500f040da0f410000c02881f070b82002200c1301d980785d075280c1201c003074110200d4458121804c20803103401c0c140910b6003d020070003440e0710680851400190f903034100414030301c030150030181d1b50403094409104403518030303c103030006660b030b880c05410716680d4402c25510319008500d0300d05940300110304007e50b0000d0b90030360250040094908460031310210303444441d45443c00d004010b9000d4080c0f940c0b006009100d07400c1355004c00f520b04000041d02e0f0801000308801040d564200b00e69040802040559001c0c2e400b410241c2c0c0744a4819283c4001d203511404440c4560300000e51004201 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 79222942 1250 79221692 79221713
    0x903030b03010b03070e0a090305130b0702040c030207080d05071e08150303121810060611160b2b02040f080d0f0503070e040b04060f0302130501050a060f1b 69
    0x300540003440050711034401d1541e100014801c0d03101c4400c8010100e0004130858000b45062402850520304042c1075110708000e0070307900d5210411103a0005160300c2141441d00030b5500802c00c40c2004c60905055845082c03087c420804c0040034a596000003501442c090030400c00d403c11a8401800391030718140000e00300c290242d564201d02030700c0324410007441c43c001003200c40902905200b011292503200e00040340070600d075500c2006000d036400364441216a4807844004100b9a07555a14072000000c290381404800e0030900c00c04540888240b107003101c03040480c0c0344d42002c030000c0e520071004420b002c14607030340c003060b0499000e000080000b140700110140b002600c1e0604207903404030030362038015941814085044004501c0a10020300818000c502500b03120501510225908100764000b40458400342c01101c03071460040c0042c420343c241044c0941607084410810040ea5050400147d806070551180c0c50411071603403c0301900f2403003800180d00a00019801c6030400c0d215103807011151 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 79224192 1250 79222942 79222961
    0x60306030b06040c020c010f0207050310020a032405010c110d08090324070e1809060a0b030318040519181718010e03150f0106020705063a090303 64
    0x10607904000c9401c5107414854070115040c280c0040c02004040340040d40c003070030a000f4a4055005080c00024141c0b4148111881c81c11007150050307a900690101a0844594505e1040c1d500a00400c01d0410415001c241c0305550013401c0a103001031651611329041c6009150154014148034122410070100d80082c180c1c1501c22002c3d11001660441444181c940b0000540e0030450260007180032680600c1c404215000e02038100b030343c40c2041d820030b101444002d072240c1c1043c0c0e0009081050545982c40f46004400f4104d01031482e01c9918080e10040c11981540e281c4100e40ea8000705002c0710740240e03030505c540c01c0031f50309100007083d81a032100d83c1d80400809030303902a00b207c01c0c269103a424600b12240c0d5901c03003c4006072070075010700465076004050111030b01840760105039042001c81007072042c49901c0b1821202480d604000009051103c10703400380d4005d8400303000502140030b41e251001000c00c0640b00441e0f000d0203510703d40e80381101c0380d0134150019181c0001c40703040c55419004850322 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 79225442 1250 79224192 79224203
    0x3060e06010b03040b010302060306010507080a020c040c02032a010b100e01180503060a0b1215060f030d05040e07030609020a020d0816020c04021606150f08010605090c07051606030603 81
    0xd40e0341c0e04402d000610040740c0042000c9030050041c40185040d0001c0c5400c8075040c580681849d80560350303a00079900160380701015034800030b04038101d1f00c0c26000380f1842c0940340c80550b0030300c0c00003120814150700c0c00901200340f1400d6a03404032540001d51000c80c0c5204000c040052805200d200500b403141540c503a1400500480c0094001a0003503c914040700ca000c2c00821017561074070461030090203024241c56100310889ea544060301c0e0100000698064801000c03981400c003007040018040e00850700501942100701c81c40da01c1e03500681076070100c0d20084070402c2240d803036000440091071a81c2105400600c045901d80c4030783d500050f10483d0f01150b8540d000f07103481c0c40c00c004000040014a8200507400410002c50a007003070780140601b184c04501d1614811201e60f1a2820365100c00b440c480f100440c01000c004411450000c0c07802080641c000300012805c0801040b62100b0007441c81e0320241c40061044200700d420804002841d2807180481c24494030781c0c0e40200a0080351006071107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 79226692 1250 79225442 79225453
    0x12270603070f031107120804062a030b04050609041209080d17060a1a070f0f05060714030103050a031103070c0902130b0405030a0209060612070c210207030b0a110403060e 75
    0x500b039449012903105a40080b11000c6c410082001124540c4e8001c03c21102c05407202031800c0d84054440301e0b014049152120f03c058054065001000c40d10040a020b20550418003802a561908807641d50004d401030307903081c5040550b540030364401031140d000100354032440101222250f4041400365107403c1c10310f4611100e0304d41400300709030036140c0c3c002c08110070f40300021100303aa141d2070010b10319148100c0f0485040d002d5a1038881c41492161026505c0784c000c0320410042503071001240c011a5090314090341994119140e86a8982c2e04c040c1c000c3c14401c0d450b4511000400401c2980d2080e58460b1000450360740714115040070b07402981e45180a404041d50221340200d9500543cdc2c140c8901a0050050502903000c10403d4075001c0c2c01150007510070011003c0310740300200841d1150b8000d4480124141c0d061030182d4400c2c000101103400380d1500d51414000a60200751102220741018841034640c80d95020b0000805141043c0500410002400820000207401c030001e00ca100380103440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 79227942 1250 79226692 79226711
    0x90303061503040b0a02090d06060806040605011a03070c02041d010b09060301020f03060d020103060807150806040c080a09060e070e042102060103080c0a0213020903010e12270603070f03 82
    0x1c030280810b81e0010805590000010f2240318564042c00e10228000d00745440c0d40c405480303500480f40035030801041600080100b0041c060180903142c010f0400004c0b401854451150204860101401d50810081b141018100f55651500704441e042d003200c0341c5070425500208030314024000e80c2c800d0707406021010300041d007926040c42135810741c02c00d00e110a891641c0b800108817880300907074000c074107041e6070307210209007400704100b50005842601c1668001100d40d04000d8040700d070042816124a040c0891195030a81c080001504180754200100d000c0310640f61a42c003800c0180c8800e0b5051064800c005031200e20076074100c0c0124025a0640c4160380c0041002c6080719905040201607440b400041000580410003091402112002d449250200d540042d0841c206109008105500420303542220304d0203129074906068117070020507045031201c407400c0e4107014803840300c0d040c200103034503404c5000c00164400031080d030000c16039981c926207014007604541e4814810301c0006d2500c600324 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 79229192 1250 79227942 79227979
    0x5011e06021f0b180405031e0405010c0305130305030f09041b0215070903050304170d0201060503280203010c110d030501061407050309030a0503040501030e0106030b1f0e09030306 79
    0x10424880340440d800304181c0411160806071000480c180e422410403805021803868100c013180c05917201c0e50155941d1070000c1d10010340907800c8000c016502100700401c10090381c100b645410307174a9041c00e1a41d25107081880c0500f084109910140c241c0c0030011300d00701d11007981c00041540b10340844041002c0551101003007c000d072440c5604016034844103500c040000c02c007003515440701592030f2641030581c8907920725085400943c0a01d509120a00507008540310500c0180440d00c4e40f480204039039481e0000180e038640588500d802c03442c54140000c40c1d425214074204125076005002402014075540f002032034184114840074aa018855032080c030b6038424000c45040719107c0e501d42c4491024401c041100c0d50100c0d004450703d10080001401d03070344051140c0d68072580544003640d100c5103080e001400b62a505204980d01c1d91404e0020300014401b401c5180c1c0007407003140540e8071000d0000040c0041441c9130030036010301a03d10100003084900000071441000143c035140e00088148410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 79230442 1250 79229192 79229203
    0x90503100e07090902150c06040c05100806040209040f0608070303110604081206010509030a030806030717030706020f0408060112020f01030c08180705060d05040b0705041a030c0d05011e0602 84
    0x5011440e08001c0702000081c1c50f9800c0f840f4100c0c00200450425451003590340050b030300c241480c00d055001070081006100c0000300345001400e0a0310021502e95146000420964004003e2489264081a5982c640d11650b2003c3c061491452081144544a5003015a50b90072031004400140c010740c010f000f41040420010b002d9a070046985083c5411a0b20500c1c94050081c1010b0410009100f055013503603041044040c01030094842450a04254040c107043c10805d4100380804c48032214070554040002080f00c28640e0005001a02c1c0c000000881711544916488401135104031000407175440108075040e50030600c00c9030498513250803680150180d42e0f80707041c000081500d50380018840352144880b40c0340d890b955803e664915843e1000107a058106e03140e0740560380c0d61748040004020301010855005031032401c260381820700c0e150144501c1800285615059038011010806406054083d98103011070301806229030360311401101c00908040c0d8401000c5061382000080280c00800d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 79231692 1250 79230442 79230461
    0x60a08070510051c0203010e0708070e0a0b070501060312050c1b0603070c05100c02010c02060a0501120311030d052404060b16031b06060e01060f0807110a0c0609050310 74
    0xb0040111009000682d0250000700c800f039005110030855020464040c80114003030058106001c0050078141001001c0b82d20003800f000070700c50041b0b0420329a65482811004031450079000303079a102440e140c0345000d01103c0d40000c041c0004951208003d981140182040120100c101c1d0754080d8030100c60030300b041c403010fa0540c1041c010408240441d114001c3e28440a004004803104503031103124410466a000c0c44810040c1d648160b07810030240d0600100b600003040000502503941040700f401e1000503c007000406000d5448055294800140140d502e14003850101300311070705e40407490a11421805880ba42c017008240900d000914051103424107030b860314081d0750b080c8030902c200e68560404000082d01404010b4540e130543c400d0041c44004038a02c11000402d445d0b01c0c10000d015140c0040e04040b040c0000e4440454036103500510460740706107107180a010888100f8512400d0141d0403201030603030070400f07801081e0190000c00c0007044800540880b1861400382245c3d0049404000703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 79232942 1250 79231692 79231699
    0x606080a020307170106091707080733090f060302030907031101030902090a14010602030304031d0d050f0a11030304050a0306020f13080c03070e040b0f07091508060a080705 76
    0x200030030646045940070716401211401c04440260b13070000c0941c03500f1000d034080780001d0840103050010700101801c4402544444008204180c1040700c0316803200c085000d404001d03100c2009411034030480c442c03000d0540b442d0070141418240c0090008050440318000c05207075010030000020070364824800c4910441848016000c42c60070366807811803110000c0660f60401d03450b80d001e01d0259940f8450325014100c00000012442e070740300e40d03c1521031016446001503400c2402000046500044450f240c0403803d56515041960200029038440d41013001074150710407403000c20480e840019410900714041c1d48050180c00c0d03040d0401d680d9210714003602c3e0300304449400401c0019000e802804070f1801c8010810f0400041e1036403000c03402c0c12a48004c140d580100110241d070b0a040c4041005000a2080303a1f041e460241c0722001044d07405004074138405c84440c00281300034403c59007000a0b0101d09203a940c6c010b12960024010031040c0c800510810380c141000650000018001044a5014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 79234192 1250 79232942 79232957
    0x3030c0c110d05100c03050414060403090b03060a0e04060902120d0c03050c100203100e060405041e03020a02061c240e1f03030504032303030a020715020705060108100606 75
    0x10018804480c200b05001c660f41e11034000c148002e0210f42c003070300c600c004080d075001455280c5030810103028030411181d10354941010f403d0001199024001c40159000050816641e440f00c601160804c0b4155010030f115820b160140010040b1503040002024001c0710310403400030015040c26110f44c09013024901141040b40c280c00083d0140e4040c2a000720684151818010309841101c00d81e481100c0945454010036800e0008412328071080f0f41004040d0303000c00c114503082c0e03103101c110900b114049111074810f03180c0707504040c808c004084146030702424907a05d4074185662045c150080558039179020307003018090302c101c00c109601001071407070b03030200c113500146810006004640040c00740d80070300d1074242407446080e144030a40001144607503074042e59146541846131360304460316a01ca8516120003803000d84000c00005076900004844001641c9480c5490000c507100c5c0b4038001812441c0c0041003410a200001c5038060484800c82c00b030720120145a45003d04841160003a1408606071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 79235442 1250 79234192 79234223
    0xe0105010f0c0501090305070309080105071d041e02031504090209040206090d050601150905090702070905070201020702040f0207140a0521070212010608070b04180b1f080403030c0c 80
    0x2500003072404400702d040c200c055440a071202400c4d12140001503011400004500d0308140d4000c1c8000010804c0200802c40c41c00c01c048014014008a071480040b1141e8000d02102c1e69116402911110000d2500e40c1886240c2c4200001a4000311341ca203c1740d40540307600c1c100c14102400750107100c650040400710320f9079681c1e00700065500650034090300084070164100005804114a43c041c246030a0341e11401c21a18000408102158110328000c901d14800e0080c51600082d0f41d20650b0071032100880c040c0d41b0710400300d009000e12040a98040d0400a0092480741e075540241400790044030107401701c2c142c1410740c95130780301a09001442da902c0700e41d040000c601c00383c001c01080010001c01c189404015000581c400e04984c41c1c0c201e80b44d6507403034100b041c40d000300000c600415007611480e040500e0301d21103c0c0030301e4006100402c215181c055006540d502d051003034016851058102c0d903882d04004d0000d10417802110200c005c6494007a410322172038003801080a28941c0114810450201d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 79236692 1250 79235442 79235447
    0x61003050c04110409050903071a0a27060c03180f02030d08010e0a0507021f02030f0f0603030417010209030d02101413080901030b090109150b070506011208040801061413060e010501 80
    0x82c01080c455040c0424009e400008140d000310365108000717109101a42d00705101c180c4125804000e507416242c031009c80146500100800c50803040d0741280001418551280054000c2d0503c0030100c8c01d9034800c1780d100b40400c07a00c1d098400c0b541c0d0094040714161612150150358203031080c00340e034400410074030000f4040c1c9115044654840b1141c4192030319540305c407550345802d4079210650380d40d8075000700402c040142907141d81a4403401c0750b20000003078100040400d44030300c214011100421058250220011025011182c01080107000c03225a059441802074548001e60090320381c4a0a04000f0b0404203500400d8a0046001c141803950b1480305a94883c41c40d4070460f80b807410715840d80c0f0f035640c4030740e26007a62900810041c0400720b41340881d030145640910040d045440780307000c00e010800109000054080c15117040040004034000c0d0303814041c00900450340584103543c240310001c80c00c6540f652206804035016600e50001c21205d08281c01552420700400980e4000000100b24662 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 79237942 1250 79236692 79236701
    0x10605030c0a09081504140109031e09052e03060f0501211506020106050904150507020f0d0201060501030b1f05031902070503071b030b010b0714061003050c04110409 73
    0x16901d00740402d5840c2d130307000301900300074448400d00c4145100408000500c1112556000c800280a00800904002e07540c09400421200c0c03a0031408441b2800c0c00e145240914801809010003d040e4041d0032000d84806106003a020810040200a403ea400070349000303010309802d491b12215402010f5003448011184c040d403d0140c9084d40c1c03004940c0c5042c0c030a8510848004009040a1007030103810300001a0a40c7c039076500c110b000b1140350040001094003481900c01d10010600c0101d8651102c4000700c4c03038400c03c00d0244100380940030307403411003580542c424400c4440a803014012900500200403c010082c19000e161041a4494001d074074461001158003034400013031300880009851035501240c201035000c82c2c09034800600c000502c00c2030011607115903004145940300ba41140e4401035074080600ca0442000c1c2d01042d04c00c2001843c01c500b403101400042120f5591030101400d442c46000d40c070054030300d070044219108241c14907004040807aa0286045841c0a103425280401032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 79239192 1250 79237942 79237957
    0x80402060a0905060a09140a0b041211030d020307020406150f03050a0f0e0304030c1403120d0b09160f08010807051c05010203070f09091b03020c0705100224010605030c 74
    0x3072480d00490315a5418024081c10350080d960ba41820303090284010400447c4029148a10408001005000318160072a4240d078030020108008412600e005048180030b848a188e0600072100120707050369001004c5c26a050089405004003665044503d003401c0c12040c0c3c11000806030380d890f694842c001d8001c541c1000b2854030018500c0001940c00c02140c24031481c004a64100040030003e200d00e20341148042d04101804541803840c400019544000161a82d90784007804500712110030107e5100034456800640510035a1804142c19814020a00b458002050350148180c030b40c00d118607102c60507684410001c0c00300500f40020003001042088174081d4521132001d4400003d1030a0002d10b01480461b21054031100fa51440074049003440c0d045241c44500d00030903260084881e0b014a031507844a410010ba4940e0859892400d01003175402c6940c0184604001c01c144a0b80000c000c5000b020440140504080000403400d00d030384203208500c00641c0c01d2012400112a940080408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 79240442 1250 79239192 79239197
    0xc03040c050a0b0417030301080d110304050d06060602100903092d08010e06070309020603060607210e13090f020108060121020a0318030f080a060801050a05040c060906080402060a 79
    0x40381e455000800042c21500045481c000200d810000a00101c41e00380710248480b000c0c601b5903040241c082d40d41d910001c1100100604554640d00154082c001c4034080c1801501040c0d200c0700505214000e0040c0e0700c6100014440c151640b889001d5620400440301d6040d030360380f16036078039004070b410038519085409104031025100034600c909803401c0100061a0070300000c5040c907042d40c206400e24000400180501d400c0c1034003400107a4031320044940c80042150a03e0b160021404c08901002618007801003120202d10142e5440c0d4010b0a00c1440724801c8520303940c986140b0709040155120054020a103060b4000040010360040500c2544140c0600d0150001180440c0804250100e00c088a00c495400103524604a506008600c2285000b68410302452043c0d50010314820a000c085030801480b140403034007c06454002000800c90640248414100070b2800401080261005c5420000c1a00c1c00a11603001e5002001200c056803902446652140c003400036131342c05604074608 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 79241692 1250 79240442 79240463
    0x4140306041725050703060e03040617180d020601030b011403030409020a0201020c0d0807121a0f0f040e070f120b0a0b010c060e0609011a0a0b130503150a0b010302030403080c0304 79
    0x10820403d140c6100090241c001800d005280d410031000302e80050010311800e4108000500c5481c8c1c101070f60345000404c09450304419540c0a42100b500400c0340c620704202d015810452801030382c00507003139050704c0c09099804d605907a84c801010030902c03050031858241d0000d01007041280c020341e0151242104600000d0b2400c0005000b207800e0140044d945404a5030f8201408035031644045515152140703000100080542e2030340e0b519104501024040c40b0306c1541c19030040c261100d0200300350b000c0000c0d200b03006040200078056210b803c03134020b5251524142074001600e941e1002c9018246420045501341c42e1a45c05401c406404003150b0346040c0b24041d104d910015800d4410404c003810350201501d600e041803000c4c0d60a4030f200001030303c4402c5006003484055a1071401e03000840f4210300c00c1c151707544020540510406000d030307c4180d150043e08400c2e0106071081080b54410b42d2503500402000c003060005404a001c2503c02500154000000031041d2429600468000d805280c0c92072 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 79242942 1250 79241692 79241737
    0xf060304050a060618060501020a1a060d0210031d070605090d1e030806010e01020c030c010c030c060e0d0f080c0d110d050108030c0f0a0f020108100b03090102041403060417 76
    0x202030714107651225040350005c43c0355100c1c0e003540788a5103000e854240701520022840d900c484583c945e0201100002a10f0300020a1050b921082c1003913010ba40034050610404500030098010b25003081c0c0300c06101c850510004482d4804249030090700c407103444403401c16504006011182d0130340c040c00c58900380a9215044941ca50a805048051180d66001e08520700340b400182100400b034142410b55001182c4e14002d50f6010803011031042d003c2ca0040085c1c1543e0504468003290080050251403a0448217001d14030041910387c59403480b03440301d4443d8a0038a0b4202e0b2900f1007151302d035088120078081c0d004084544c0c0c01c010700d803203130301281e181c1030000700108441103840070b9004082d03c0d80001141c040404062094480311910303540540039040141d2034102e09020503180090400204000140010707004015010140c20940c400944a00e04401064004d41c0180901d005c9040c000d08190441c2c03500080302889503038440b860303109042480c00c03c2000d540190341500c840f402c2d95042e21 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 79244192 1250 79242942 79242953
    0xb0102120c0105060f06030f06040c1218030f08071704060209120c150c060103080a030617030304020a090605131a041a0a05040501030308070521070f020f010204050f060304050a 78
    0x8250701e40c9518000142400e1580801c83e0014000e00018000c0c10184100401d0040c1c2482c040e502c0340d001d903000301b002039035a5822220301416000e41da2101c1c0c42c0001a94101e0040b24402e40000c1c400c1c0c6039014400101041510860012104a40040c0c019610320030304020b5070742aa504640f1442002d410442000005008900396681c4400b040d48142810324540c90000d1580001c4598001c0c501c0c603010700c025140780c8404050002600122002a4805d0340620991151004211254034882a043d04024068403940280c606034401c000049012030610058072501003101c00041140b40c0c1d04001903412009400c00d620745a205440311040085261501c0c01307204071036401096000602030301c01003044500c6000f81c024601441c03401e0300500010746c2214825402403040d00b041a2682c0ca480c82c5841d14107131015403e1a60a21074042c0282550003d0080301480a5a000c0d94020100608014200e028910a0951001c0e107024840c6081c2070000c019034100d801b905c10390b4001891922103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 79245442 1250 79244192 79244197
    0x70902030f0714040503210f070336061b05030c0a05011406150f1303080702010305060103090837090609080705010903020405070c06090b0618060607060b010212 71
    0x229074424035a01c00c1100065100c080711000030f40c1c401c1298103150a0070b0200c1e80d50301c0440b510120003000d5811076504190f2400555140c051024041c0741d5400d00c52030001c7c5500c014100b014144920000b4a51443e0040c20a034601080048850b081543c030346803086604201ea030039131001d65508003e406020036000e00040010342480d030f00030903014415180c01821109494141b200404484060000310f6842e14134030900011202681d0382c540c10a801940024481e000341803500c07103541d40d0000104440702c005401000d000740c03000c0000b030742c0381380055041d5180280d00421415003040000240120800000d0301110041d428a200c0805002140c0e000c021441105010480d0200208880c550004900f00501540f1f03001e403042618200021b00075045d82e00000303108075100c80000b10001e11600e10f0804280d00400d080c4490026400d100701811402d0381c03c28041d20351006800c0d030000050780d5440c01341c0009044245000306c1916000c0c000c10300c01d05a0360460049128040001003907101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 79246692 1250 79245442 79245451
    0x4090507030308010501090e010e0c0705190506061305090c091003050118021215070c0305070803040b010312020109051b04140907090606080403020d2f0604050c0603040203060a0b0307090203 84
    0x2540f00c201c0d41071a0006d010884154011482c44032180014083c090103440003a0f003180500003001d40b2001145800c900b400c82d0140400c0c203100700340b01c041007440400102c16004403401e41c0e15100070074410000005403101161003e05960001440b45040d00301034509991004035400c00442d82502c03a5104c1c1d0a446034040505a003098020f903231020361078581840010f40c0108030041c040e41031074540010402d280102580c040c40005464403013494080c5086450041d803282040b40d581c5490f00d000c02d5481c800b80815903441c1361103240704880034014403945881503001402802000030380e011160030710a0310002550419290791035603038412860b40c0790a00030800da0000e00b040600300200c0754100d6801d58065800c10a10b44140400303e500404daa0044282c40c0ca0003141c0c24481e80d8242c040c01c1d841d02c500c04007000a003940c98404071004504980554810015101000d03c003508010090009542c0a94507801070b401007a40800184c0c452040f0000240640b900e45075280795501c100d820844 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 79247942 1250 79246692 79246697
    0x60708030105090906070f0e0d0c0923100905040c05090c12090a020604050d0c0509150306010503031206130e010c0903030216081b040609020a030603050d110a0b06040905070303 78
    0x30061082d854201002d540c0054888003c00c91407a1559009200c508003801e074205100c5101c40300100d80e1903500161600c6500680500d00ca0344d80c8104103401402402001000811071001d0500c1095000d0001c5000b8100015600420f5007898034500013032402810440f8a2204445c000031036455480803c0d205002c200b821540b12000720071003041200c4000c11445058000c0000343c00180e07203030415603040d06c0c019a61a02805424505086c42c2c0009401c410b03804482e003401c0008013031040f201074548050942c02d5500c2640d903101415542d0081c44840c0c1c08907809500010740ca420022050304640308100750100e00622020140703070071120500c04601c00100c400d0340610505804010004030b800030f08101000305490b200c00e0b00e8960b04003c0c0a00420803c20b40b08080715036075a00a80d02070610000c045540d6081584040c0040401e84400c440c14003813141003524084c060030340b40201d41118009800b04030010382c0d801c0703101d69004052585c03059440e135051011500c1046079101a5100b074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 79249192 1250 79247942 79247947
    0x815040c1a0313050c0301050f06030d050913090812010b090406060f0804060f11040e070806060310030305031b030a0e0609010c051204020f10030606030b0d021c02010509060708 78
    0x5040180c0006201e030031007680c1c40e50008120000d01c000104503584546401142e600c204020b141890070103686030419641982400b040c803102e04004480320303015a034101c00300c48140c04144c4044d41c06001e0744440c90340c0207451a922110710714041c2c001d10b80341072042804a24280f2010040c0c003c0310300070380041c2420b22020070f40b41d07800e0405201e1500038201505142006041d035100041007080001d1000f000c0c40c0e02c41840301c52511a60304061a03000c405014280c50b01e854110618050000f103c000b40020880d001217130203410140c00320790040003002503a03044a410b603101614161700150440b8040090415080305a100040103113005034180100411800c0c00c16607070740c0c0750540103060b26819925241c40c1c40d0b130203034101013154110030b030082040542e84e0303a030700024694503c6c0c42c0c0d40907081641c0e0944040c14a0b41a4411015107101d80c0301080766080318000d111501654070402900800c002c1403803818041c0001d24068090b205161140c540301740440410015040310340100ca061402 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 79250442 1250 79249192 79249201
    0x806090a06060e0606032a0f030a0606030902030d050a1407060c030e0111040515070209100f0f0b04060809011b021b180606030403020f0105011d0610050a050d060815 73
    0x501442c8000c142083c68a03025052410020b80380784006403070f000319185408451081c414404112042d1002000c1000340c40711400c00c030110b5240c0c4122440040c2d103240501c0498854001d06c505602190003400401c0303141b81282c019901507100058180502200d140003410007411000140078083c404d443c042108101d225018040d541c0d560f124540a904084151030b13290b26060540301140c40c1120302811510000d00c04c0380d281e02c10b03603401940149210041028055605940404640300c0c066042c03d03083c0e480a02c0c59048615018241d040141000100401c2c2e205003003090300000200300016100c0355518980321602c0b5840f100f00050303008030580c2c40340b00000040ca003415030403c1c0c0d550091142d040912014a500052405204041c080082401c2c135208000700f5a0f4111940020491940c4440200c100d09d842e0300040403446c1102c0c000030700203003000e40d0310910003e40f94030b4181c00e01000c2101925503801c91407094003000e9846100051201c4100580f020300c06101040c45001c0c140b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 79251692 1250 79250442 79250453
    0x19050c010e070510050d151e0f03030e090612070305100c0201060b09040507051b06040212191716080901021603080729090c100c0201020a0b0403090806090a 69
    0x104991031070003074004a008103d5a210241a410110524034001740e440740140b244000500001c0100c40380382c120154040b80c1c150344844a01907511054294840050f0f07640c0c140da4401c0c14134000100051400c2d040c0b821241003120407103070882e10080541d85550301d0703c00b0885c0b415645910030f0f01c1c0c42e4004131007108810b03000d2107180c142d501307284000e0108604000091142c0d21480c201103001e00c1d9204000b070441d911600075a0444104200f0022503102d1300c2e1741c003070750b100800d842c284c0c0724000030401c81c0640c2c5000100c0890f540380f01c1d0541940004180c642d01c4c28910b542c003500d450710a01708040c69546c1c0071809509200f911401680c0c0c0c40308841e070002450712074521402840e903103000900380089242030301a80c007102d90049115036000300680b101c0002c996000c055a074224801010300c00540300105201240c8001642c25030184085040215603138110030f14040d0250b000f070540800815084603045034041d02a08024010380e58408400d07150030303400c40e45040d103508040000c808010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 79252942 1250 79251692 79251701
    0xf05040c05010e21030c030f04090612031b03090b07051605030304030b01031e0f030309050c0121110918040506090a0b07030b03010605040f0f0b030a03020304180219050c01 76
    0xc2883c110f11000311000c0072403007107046041c2c010b0940da4800c98846000c0f004004803504000d00005684d02c9845201d40000f09400074020700c6072840c10100301044010301c4520321014950940e0701e0803c44c00384e880c12101c81d088048419410400c5000d004110b500904000300090351041000780303420040d00b008012a42c0300e9810091003070304108000c00110b80b15610700ca054035000070440903605002406d0a440019110004103008040d4000700d0a140d0958480c0090314010410745044943d0f801c0111003010603030000d035103801044080c49048502ca64090000b544501a02900c0c1c040340c0c100090201c98001020f080c084842001c01c420480148582c0e40c01080040061072003024030b94408060640052903001059505e550a49907580c1c2508aa80280006481006a42c84070781c240c8001d480c00f10b00154640381400c1555005040000d046108682c0640c007460510f810051080360f00b5814031100f0384030315000c1c81902c220f1507000c1080352510405d900c449540f803521403145400d44 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 79254192 1250 79252942 79252949
    0x5130b1015020a033c0909230a0606020c0127032009091b0d020a080c0a060e0102070501110a060e010506010e06090619050d0e0604060b060705070e19020f0a021e150a0605040f05040c 80
    0x2c50030070ae4101720350fa800040318800400d0909042008103007055013001d103003820030820600050b21140000c140203000144040004c0790075007080e94602c0c940240060081c00b602c07139296550001c4086010b980c03190350417035141200100000b80d030724402e40000b01602807980000845800041d1040760501e03014800000511190a043e038944000e540040d407225480e02c2114140410091030048030790050203207003005944990204083d0040704c070076034000c000c02c950301808204014038000071440c0460954007680d4008101c2c03890003004510781501e03611441c4500082c4042800182c610f60000d000b001d5418082000802071490541081002d0781e03120b05d1a030340038600800051020542c00304040c02030b500f09104803222a114202c68224010032001c880d41464030101d950b0b80e20000b00c00c0242413140503603003265030720708612442100c01001c1c00d508451940c40503c00d9180c0c1a00c02d044a40d0011914100160207941e580103c0e054850341d200404d42155a00308000c100314038403500c140503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 79255442 1250 79254192 79254211
    0x120b0406170105090a110409080c1e010507020703170a020c0604030506060901050427080c0703140c010305010f09090503160b041505130b1015020a033c090923 70
    0x306241501c1b41c0703103122140181e80c0c0c022074407a6242c2041c01018000ca41e9401c10080480d02500c0841001d80401c649902401d60154200004a0805440040c5040569400072035010020107000d200e90800d50001d40c20308154064060a43c2050381c41c403002d40f00443c0580042c0c026071400340b08202880d0030580046100d032780703813550070540c1044401c3ba0b5911404860340407080c04109040a1030107003d00582d00216218003000801004548205c005c903c890303220440e8040000f810054013619024001c2108070f24804204000100154000a50050080041ea8501507040100704540c6035001410796480000300244810000340b200340d1381c030640d03813050204603078100300d01484e2034108158800b5100d100c071440440e2032020028081c00050012b4804d00080c61400c48001c1c1d290360108a080d0040b549a00003011069030341e00259100c40c2e240c0070409031404101c40000048111030b013104003086a4610701081c1002503100704107206454040c070b40308251048a941001c1e00b0b004203201c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 79256692 1250 79255442 79255453
    0x1d07030c02071409040f02040f020a081602190c0305060709080d0c0b07030b1305130516050d171306090503010b03150c280305060103050124120b040617010509 70
    0x24a03c090300310506020032a2a40000d031198241a0310000060030701079482440d244205400d42c00c3c40e4000c01071080c0c25218050550380d580c04810b9110034409100b400342e000a10b4414200d00003c0407461024031600750b00400c0760722034554a1078101c08a82b00804941d440e9400d00050b103042205c03030700c0001c0900d0102c10b01c580c1c965030880d440e54040c2400040c151a40c20b03581c2c003680e865a0100c2c20019504041100c0d00c1d001012100c008400d0380c0645160054031450001660380c0da0b040c800762074010b4482d0003825440d0356646000240c81d01418ad6000c1d040c400181d0061011403040010400d0303640780d4082c0d50411080608603003194a2580c440d900c42950702d40c0543c1d560078001e0f80000c40b800700030380351000801225800e40000ba0204260078164101c0020141c060388000c0c0a00d60a81c7d040180f6030300c0704c0c840d02000d42114125a0014000c400307401280340701700104802c000011001203010f40701c01c000704094a85c95000045c452030003440400c014030b001d210301984980607100401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 79257942 1250 79256692 79256699
    0x171e190912031d0a0305030705010204030b060109030f03050a0c02040906050f060a08070e070507050a081e0403080318010f06081c02010b0105043f020a06080c0a030509071d07030c0207 81
    0x3c1c030b2450211081c061240040844a500c1d551320100c0900450b0400162580e610340303454094000e501a00088640c5100314001c141c0070b500c9010b03040b003540c0c1d2021401710000903d0301c0680e01170308603041ca8801c014071b440000c0016292401961225840b828001c101414007135403d04a03001e0091005008440485040208074400100340c030888195911030074141c0c41e40e0750121001c0c440c84401422078802d00d840c500800224100908034051040031007401c5810222483c1c01074811841b000e40310050500c081404100c00c000d170003c01190b0440001420b4100e60600c0c016070f10f40d0b601c540d07240d0b08440075074070021480050f401d441e00450b2008004010b21100041c2050046002d0100707406001c4800c88103481002a01c2d00324002074840003103103248034105544080b0811b150487c0103020442c000504580150a15402035204003221820610b50369400c50080500502340c0b006482060302c000b454415640401c8031400e01d8800c85104d07494131100240a64024040660441d4013840d03040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 79259192 1250 79257942 79257947
    0x510030c1503051b0702010804020a0302090c1e090a0311130c030b0f0607031b0303020f12040303180b060111070312050304030206100f1a090a0f090e060103171e19091203 75
    0x8407a17103542400c0c6182251624004110840c41a40009401c520290140452414018041c00c40f040800c0c41c2110040d100214083c803070f0060300340991308030000c0b0205000082c8040c060401c1c409001c0c4c50311640d116041c1140082d20400d21042000c02d80e00c00c0a810381d400c1010170540059000d4800625201059800501c0c0c00109200f411b8902800ca03080c100b0503110790125101600100c07506915661031031100c001a41080e28124042840c1c203c0044903441a103285081d0365030001409030f4555601801510600640e020400d030070702509001000145494031420b420784100d944060700c170301d480d1030003038503103000680b9240b02c850413020204024415076240506580c1c1455402d04002400301031066030b0702501c60744aa1081030f5034004140782ea090a049400c982506c0c0e03007480351240d00449582c0703e200070b0101030601449107441038090a8160000c2401c00d0490000800c0402c1a602002068200c01c0920b492852a0303170741610701941c80191600500f0f001e0342500c0d81c62880c0e076800f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 79260442 1250 79259192 79259197
    0xc010306030c1214071d010e2401020a02090a060e0108031801050d0b090f040b070f1b020a0e0a0b0405070509030604021002010608120705011b020d030510030c1503051b 74
    0x70b00200300d030543c908508010b09158944481529030b41194200d948441c0000189840c5003040c65120800c003000107030003040d030000d480c0120488040503460311030203401080c036800c0c2c45a0040c15840303039444220050b100c400400748038074203604000401c1c5080070b40408100304103030304c800410750003400318108031b050f40d020310756000c0401d081450340d030b545084425001e00700782840e01ea84503290b48104288404a40c03403444c42a4415030729808140e4603080e0aa81c1501c000d0801000500381c0078071441105410301960410500080c01054560382d03c0506a82c1080200c0c2c1c840c203074603100c0142c140141418000d00340c01c0701c03903402d0440c100715000002c42e603102c40c02040644141521400070858a000f0352009010301441d40079900c1c280a046500140d5500c081c400300e956600e001500070060000181580c9022055405010101c1c0f180d0701c00c03405401d020708034804a009019000001030155100308000f004440701040760340851110207811a54024015500b002280d4400030b1040d154904 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 79261692 1250 79260442 79260449
    0x5150c0d0513030b0112020f01020313030b060a08070618081209010815040c020a05070e0c070209070207050d14150708060d06060909080c06090723010315030c080c010306030c 77
    0x3807180e103803400c40e502c2ca5950036290340041e210007a1900085000460b40e03440401440c0203031480c1504562450049903244103415441c1c400003020042070001407800c1d00c1554101000a000c20442d5448518046c10920142c2c00f09001c6089810341403820b450111141c00142224009040345015100c500102c601c10349031014100207884c000201d450342108800340702103a02610802c40383d8680d007000ba40d55003440c1020345492042020001d03202a02e40d521502c2200b04a101c0350070069540d0034800741c550082c1840c001c1d4000c030103000c523050700c4402600c44080c4c0900c0d02d900c401d41c4004d850505141c240e000381024084010700300f010701c90b042800d00707800001c15924510942164107102c00140400d0704174502150074202d03240c1c1800700700d5000c0c2200403014402d50318903888031091103540d0011403041d050200b40c203102488074034416985280c2c4401e0f0604000c140c01208031410301000e00b00303803c01c40d44800d44150070300c0307042000c05c0710102c064402c0c03c2c00c100140c00e507210080c032182c0310310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 79262942 1250 79261692 79261697
    0x90702010c080a050a090c0603060609090209030c01031806050f07090b0306031e150a05090114011202010507061e0903020c04090201050d020304060b0a03060506040506100509010c020307050a0e0105150c0d 90
    0x81182d501c0c41d03a06c80d94850b5003000118040a40307460303004000d080709118600000300103c07008101072420b40b0894030174a000038000d1255500050066000e88060883c0c500c0c00300c1d5a403442000320381e00780a002d00c161140703a07540341e42d8a4200e4000d00207001c960407040d0806820300c100701080e01c0c00509400d0724104110803080d0054240f003c1840d100403031500c201c02c40b030044184454400150821130080a14000a210858104040b544405000d00c02d003032105c2400c42c404000340d40a01c2c01440c1580c010403010502c442e0201800a505e1210b040100d0710b103588901d02c0382419818400700c246807004890611580f0100d40000702240104625086d0f0f0700e80c0000032030b0400036941d100782c0141300d001d80b6140f100c036540c0c00c1400c014941154a0740c052420a40040d0781843d00c01603200d082e42c4148c8803d400c0000f0600111041d402465040b81c25106000700810b40343d42e080500c0c00200054800e40e00c441d030500c4280280100181ca100c210700ca401e10000113a0080820719010405803031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 79264192 1250 79262942 79262951
    0x40b0c0a0c23010e010902040b04050f0109020c01021b030a020606011103090105180306010b0d05010807060c06150801020c0f0705030304030803011505042c06011e051c02041202090702010c080a 85
    0x4400d2214000c1254102e403030395071901141010b2440d042d00800016030089038200445d40150f000d010640e041140c2c003c2941f02183c005001c4070006501501c00005810f00040c200407560414500890802c01042103940c008101c81d502030f86c1c100300d003a81c00031007840c20001030b03d21091030717650300e0140f070110505015000c00d0504619404002c05155004028100c5180b0750f50383e0f0030710502d58010382842140310704010000c940d00c4000601d1078200d030784d2551580b0300c8160a460303c030006e140031140103c0d1031100c1c0c10001182c43c000d0010349501d40c581c80140045032084c000082c905000350740582d0080d00306200800110f42d105013624111420550060311001d00317803000f101c043c41282c04c04402c2106458815044401011000c50b801070b01e45410b00b0741d40c43c0c0c5401510000300054002c1182c0d684140302c51131305481500070b400080c2005842d00e5100301c50007014410307a00f1130f4100342c3c10200414080019890b00651240d0804202d0008009000404000920640c801060098660703200c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 79265442 1250 79264192 79264223
    0x12030e030d0c1e09050d0f020f0d0b01141f0e0d050a05010203010303080114031e120301030506220c030215091f0906020106051c0609020d0605040b0c0a0c 68
    0x620484400c441581c8041010b007060720b00103090040c0c41c6040c0000002c07030103c841d11580c050f501e900c080d607034001e00f0208142c0f081c0d40d40040705d05055104a8001543d15034a03102c68844624540c480e520503403403081e0315810b1128810804030040381c200e00c60000090100c1c2c0035201c0e180100c2ea1400507242c1801001c0322040031421325140820700404c030340301c1d800c1e80d042806030650103103050fa80b291703a40010316641c0d046040403948944079080d034190091041300c0015501c1000c80c2d08510501d009450329842c1d40c2000000300d03002648207071403e401410410419419030306508160303020101040010000944948254400b1404000d002c3c581000c101c58031601d0302402d90700021401002a0080034000490303c64003407003c55130304c0101e81a0640030900d680180140e500761a805000725031031001445483c2800313801000250307541507681100e00c0150300c6081c0001c0c6443c2c01100c010030141418600306245000003011204041c4050000060041d440190794040c0c6404c2100030b520f6082 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 79266692 1250 79265442 79265471
    0xc060f09121507020a02040b152d0703120b01170c0c0a0b0a0b040510050102030f0f04090608030c060c07120e01031b030e0f0105101a0403081309050604091203 70
    0x203600070380542c1c03084030070850500d50020700e00803898402d480c00d120142c07103003083c40242001c000302110550000d200c242400f000c42d00881c1c48094902c0c500b1152045442142e58207a07000305000e500150b0600305041c40c07113500d402200c07080d5000786060b2000d013080c41c074001c0b22054094400622020001080003420703500304010030515403c407040454a0800c0b0015800400c40c10540c4c0d03024604210001d00348005406d02c2d07404850041e0061441c1001c50354140c0215440007102c01d00b01d040510021401c4101403190310f010301029002183e03208e18a4000d01d01c0e0003001040038008150400032480050111100c20b0301003401d90405c5201170710007a0040e005050f4030070b10304000c1ea00207100c0d41550b603419000203850441580c1075441107094101c0d46401d079030040b00c1020490140d66010041c080e464000c04280719050a0304a0509440b0343d030705030044e0b0041801c840405007040d810b122001413849810381018088030108510300181e5a600021004a5008001d1694a000a120481 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 79267942 1250 79266692 79266703
    0x90303050703170106120e06060319030c050303040804030c0b0703020d0f02010b090c090a050402090306070f050705060f06011101090f02061309051819050a1e05010c0f020c060f0912 80
    0xc180400f42c5660b1151401006941c0650b9040038550900c81001030720304011620318086c80e00600a481c90614101090134a507002100840403c03504203c1a00800ca051018500551090031519510341c598202a03e95a00c140c120080050b400c0155034002a00082c003003600c8265400d04480303410160509a00404c85c890748950403000d1542042151046a001403082000072200b0100e600c1e200d034140f00482c02a011502d4042c2e01c14000300d00c03d41e00840312042c5940c6546850f41c6881102e03941c080c100081540c500b81c02c4203c600c14000c1540e08003840d180e005030128001c11403034030700d5103442c601c96a81c083d0180c050800040c000581d43c4070b2101640c00b40001030002e0105042031001c00049100b051102c5125010700001c0d040c180d400100d1540000d900407000741a10b051a4503049001400486510406540074242600241c2c0a015002018100d03440303950000c103004001038284001400654864035040100510f088030030303c10784c1c0b0808001c0d0f64180b4841d442a10403464170 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 79269192 1250 79267942 79267967
    0x150e100509030a12121404020d0c03050a03090303020111030903030f0c0d06030311121201031203090f05250f0603051009020f130905060d030807090306051602160501090303050703 79
    0x14010f00b0400790a02c000b840c00c00152043c1c581e5000003594032803a10400700d4201d5094514582805401b203000761a0014040b00340314001c800800c052a036950316546052000340080380440c54410003001855028490340751b1803140640c010340345142411280340c4070b01c030080c41c00040300100c1c1c010400880c907000640d10b1740080d180c000c02c942c2d600c80c1001b910304087c48031403000b40d20071090100d80f044000c5090703550a140e11072240c106a4203542d00c841c1d5031001440d48400b00755403140800041801407001c000200d0041004e4103107038a03000c0d20f90f0810362a4000f041e0160210040070004d10000c41000401c03540c0178070300003a44d900c90320042e208496141e230081858074004030700500b11803240d81c0104401008000c400c01460780d2000904140c0e00d0480da02c0f5800070b00c401c070381f4000c02c0c0117407a1a94861904d2505840780c0e5126504c2c1c03407c54200f954000c10a16444501117069501080070340d00b1f892801410f500042e16040000f4141c462502000301003103408106541003501503054000523 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 79270442 1250 79269192 79269199
    0xb06100c14010603050f01020910050a050906030c0a0e0f01080a09110a08010b030715020d051b0d050d0b030f07050105090105120f0a0b100c170c15070207150e100509 73
    0x1003080d507500c000d0282665000542c0d49000345d10b0303402405141403085808000d800f510500c81c03124103000944454008d01c200600384101040702d2011540e070707200258410f0000c841c0c1c2c152600e03410200113010300010040c00f4052154040d0344da0b103982c0c10101d010340c0403031003442c04508180c691401ca00c1e02d01c00411141e40100352510003181081c1d064000d10503000c002d03802c0783d0b501a0707110300c803941540c0d0715000c090258010344050544288600001d00c03640c52040f8540d82c120404000040c070b010100e065540c00907101250034494014039004008058004070000c103130140f18001c4440e00d40c5068820300d814043d0000310002d03640d00030415505030080300034a041c00d03403810140c3d00c412020300700c9030704c100186000003900f8149803004a1000b400ca83ea50340000c4e05010350750f42c4c01c103a541c0c00407143c0d15410a02030303015660700400c07007295944d91416007215203013001540640341c4a40c982012051070008141c01401035849102c4400d05c94089035402c0845940703034030554a610074242c18640 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 79271692 1250 79270442 79270463
    0xa05040f14040c05041404030914040b120a060b010e030316021f02160504020a051c180f0b01090c050d02070606090908070201170c090d02040f022110030b06100c 71
    0x2d10070451060300444c0c0066034140b110320000034000c001080210f60050128a0603502404503d2441e10a42060100a0000200c034600000050300a0742008074402c0320b94840ea000c1401c11405020781444141c00b030038007000d08482030000940fa4010112010401d60310440d815044d552280c1d00d512928400c1350300c109803886041c01c02510745031002101491000c41c82000100b5041c60f10803112848016500c0303d04052030f40c0413034480d40404228001005031100d60000c0428082020b4504251040e0007a04190400b803601c564442c00580c8140c0202d03242202410199070404103c4642c000251001a9140c0307540c03402000034a403503040310301c9240c9404446410001240f0090240758000d803110700850041101039000280c00311001c5c6030540c0140401c5007982405060900000c0c80188003003021410308044d03034101c0e04540c00c151002c0c640c0c3d03641c120800341d00310310320390b009920140c604c0c0d80c40d41192244c14464030040c001034000e50003502e00c0c034410b6110384030a000007a1301410122 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 79272942 1250 79271692 79271701
    0x20306130e072d05010305090f120c12040303021504031b03050409050f06010906050717030c070201090801180803090307050604060b030f010e070b0a050f03010602100507030203060a05040f14 84
    0x55550034240120008108000c03c000c20600c0120050780d00800781103881c1182c0d80c00d150044029140c090400010b5108103419524071250620041001c00c01044503a600c0b0204d4502c1d46140903103140a100300842c0030007091010a5000c11040702451084040e0801601c491070111020b100b507240e161030340c01c0b08110328170030513a00c00010021107010301c105102d6a200c941041c0640981603403107a021410000d4200911409080500030b828000e40425442c3c00c00c0c25150100760388215800c5403100c10000e54a002c41d070300018850041d10b400c4008115007071540744a041c1c040d0095030b016042c554048009020075004200304c44500350b2201c15190242490b00c3c10310040c0001900d401d21078000c0c00e81d80c20154805106050358a0041002031007000d103888164240b40d400a880d560400000304400c1495001c4500114002d20103079005103200c0c0f440c03940d010104d0720040d02100c10035004005201c0355a03125400310f829140225400210110390500001c0200320040007000464803100800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 79274192 1250 79272942 79272971
    0x2706030501030c06030b030c010806010e0d0b040201090803040e01062307050705090615041703070218190b0d12110706030f050615070303090c0e04080d0c0206150402030613 76
    0xc1c12a48151007044010b5243e520590644110519990300f56001003c040040d600c00c2080381d4001c4418180611a10031070004203018100900b41510849100d400f8001103581c400c51900003400301c0340186003000d040c01070070baa02c00c406104610402c00300410168070003035040c035030041c0d404041045a50711190b518100c1e444284900c18240301e41c40400004940307050a2000e181609607004e12245000d003043d2850f6240b1000c00003910152005020800041c0c03100310f80841141042124401545407100014044280e4400c2c410240c07420803007004600c0e01c2d6203072030300b215644c0700c6441010303508001c0048850340d01c0e0308100d454600c01c1290000e24940c040c2e01c021040c04041d0402d104540d00c003001d000c600001141c206904a00030085000402d02c00d41c000c030069403045500041403a07445145900358101594240c44503100007421048201241c82a1030407055507001030b00c00e074076151451403040e00d903000100d0300892b000400105142c2d00e0a41e01c10b60035040034410812000d00041c030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 79275442 1250 79274192 79274201
    0x50c0402040e10060509240d0c0203120a0c092c071d0402030403081906030b190b030604020901120809032410050609060705150f060a0f05030607270603 67
    0xf540d5080c3d260081c00701d10305110f44201d444c8041d014011580c10b0421a00380107a40c0d205c4806d030b035903489003805540120700007400b0b4074101d642554001d5454180b1840d8140e138204c806014244c3d41454105080390454211000c00d089902d20301c80308009007034500400d81c401c11501c00c1c40f42014141c0b404c000a8540202070800c20314040d0940c000720b00717148801e00c002c900c802d60740a03020803010f8000549081c00b4062003000c1c01441c04002c26040e41d2907841d00030905007640e8009403030710022010700c140f019030b00c5281d1050208a0083c852410f1507000303d803071030f04103006203401c4402a074100000d20403031204480c2c500d003000d821502ca001c140241c0300028017895090104000381c4101281140d000280044161400180051728108950080020f04c2e03010000440321400354141c0c40d0114611038000f18401d504c160f0004000c0d02d04001003068411090700310722400200464184001e88001441c0c3d07501c004641840c001e550126109845490004260604c1d560351103480829aa64141c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 79276692 1250 79275442 79275451
    0x403170921102a020a11100c0c0305010506120307022107080a1109010806010e070518031603140a03020a0f05070f03081213020609010822060204080709110412050c0402040e 76
    0x144030100c0306151000300d844810880780070380301b01e84641c0c54034464a000c50102a40c0801ca007071032004003006944071034407031441b5401540c09940d1001007080310b007005c1c2d4081c07a41c14900340c00f07103251059650010340c005102d2201000000106c081d008a03011040203000c02603d503a204892540004c0c1c03a0030b81e1181440001140100c215800020f451100000c0d00d45c16500044690100f660300c2c2d031011a4107800034840c60702000001032103c0305035107042c050445040d000344401d0000c2400c5051600407103584983e03a00590340164041c90120340d01141c20034000740d2000c08500d814040b810028a07201c16500300d00101520140000200078100c401000140c1e081070418289568025040c01d056802c660040d4101d86e04000320145584240100d941c01a042040c40b0245446031080c41d03105030918400300c0d03607140d000400b8410100c040120320010603441d20301b480342d0300c00960005081d0080748180c05009001101c82000c0000c2803100d0340e50030328080d00c1152181d984001c41d05140350300740c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 79277942 1250 79276692 79276751
    0x70807020f06030403021b0301020d0612050114060a060e0604030506130b1b030105040509010e060907030b090304060c0b07090308070606090c0e1e0d17040317092110 73
    0x80741c00400e03007403240550f4401c681540241100000d80d8020b100d4000d107000e030b070700e505550030811001c00150034070905001c0c0c01c2c004480500481c091621600311200b0b5456114100c60003001c1280035580da016800560700345140c015613140b400404102c06029035000100640103920802016468069000440d68000e0881e00420381340e564060b140014500e845c0c00704610b00700011310450030250131040c0c01140b400b000107016020380074250f003400340070342d2100e4054003c458204244111680c080e908003003090302941c9007610300307903024103910b1140d1402002620f0080020b00d0300b07802195030200554100b04030a170ba42c1e80c2c43c40d18600800c1113001d018022480e007000a4074051241d0300d94001101c015010102c40c0300d1810342484600c00c10041c1035401440e4210303460000c0c031000844051134049000e00740d2100d003546402c0b000b41101050f0710f029500c0500c004402542c170340944941d5800014040080018076001080c02e004c42518a10b182d18181504108400e5045617258100c0c1030030f4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 79279192 1250 79277942 79277959
    0x303170f04020a030209060d05060906091204120201031d10061a03090c09151c060b100207030b130f150b0102030f040e3402190803070c080405040207080702 69
    0x40800d548000c0c0c180c50103500800201401e000500381265016000f40004109901c140020395400e440d014007100c0c01581c5030442c030b0038130210103020402d4010449202d02d280b42040e040101c800e44c44c4030030b0742000e410903450b100d600707080008612410303854625150980d05285441041c18010b8080361040c1201070041584000c95400300030280c034001c1210f24003609081c88050304111100d5001f6020707a40403261218461029a00c50700d0101802e44420782501d80c4408600345041107945480f0018010084481c00c4103105a000c0b4800003600e03440404400c41e515810506500701450810052203451040001000e00201e44a03c030240c242109041c48070f01c00e06801240c4070300850849074080c450511044c0101007010b0151a44a4101b98079a0313101002032104030a4080d00821541e0514920011103915580c1880f4103145410803110414806586680320449403200416000402030048a494204a00c1c201100d00520000f08151349905050404280d5a407103800100d01c14401d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 79280442 1250 79279192 79279201
    0x6060408100515101d0a08010207110901240503040510061d1f03082d030a0606020619020a0c0210030f0513020918030f04030c0501110111030c090a03050601030317 72
    0x204400b00304042ca80d5544d0745034604580400354000c1001000340d400704c1c0b0081b01280c4000240f0242008900030010201001c4d824400d2000541043c0c00c00102581002c1811304010041076400c07200d100c4520304a59a80e0303c505000b82001e6598911034205030402000040d1a80c02c1c4a0001d107808000104118030749a8462400500b81e01802038134002d0040780040001c610b4840162081c0000b4101c406c50385442d2807650075480c02240036141c4041c0d0b010007480503018035480303135038054402e500042c006401c1140201d21012000c0c1d03041240759800281c5c480c41284500b81303450a8660203440f80303003041404000134024010a0201084540c681030004201401c1110300542d0103401800408041c0c9480350100d0911800c0d0560707a4007840100140c51405040c800280020f502130140c401c001403d04000416140380361140040580c1040c843e4407072143d503001125045015440a00d40e115a04004288005001c0c1e00c06070031805040000014140c03c00d001701d00b0000007103030315010ba594 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 79281692 1250 79280442 79280449
    0x30c06060e0402100815040f02040503010513170403050a1118010603020d20070f030203071e02130b0907030b010e19060305100803030c03040804030b0907080f010b010e0906060408100515 82
    0x24103c584401003190981e426010b42015402302c00070300e82140c00036180a45541c00300b825110117496501c80c040d06a0326080600200141c007074618070307001d0f516a01d00351854507130a541e03200710b2402900c040d80c04a024583c595402040c2c8000c0d0051990755001c560707486901900070340104442d0351045003400782888032180d801144508144542c682c01d410800c20340c903168030f9188050701c202d05500c070410411000c43d402a802c5d0480740c41522080038000814810f0200c020001d01080718501d0505c140707005642c2d614015182e010380503280002d400000100101e4003014220b9605820041b8180c1e8070b4281c40040c900113007030303a000d92000d200c10780320060240c4003da100d1043d001142c0040c004204c41001d0b400040d600580a05512414280c8a803a914800d11054400c06411b900c04c0300708104200080c400401c80c450404020000807001000103020500c9404845200f010403000040441e80c41605980141c1501411608481902200c1c0401468142c9842d40840300135142410b1515 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 79282942 1250 79281692 79281707
    0x50a0503100f020f03010f080705010912020d0303020f0f04050406060f120f06051201020901030507050903071701230f060d201f05070201031b0503060904030c06060e040210 76
    0x9501500410503100e000e00381000601c1c80302044140541c00f08014900340b00f8002c05140a840c24030340541d001c40c1340408880c5401c0140c1e0205040c00780302e0004118110900d26030700309042e01030700ca589a142c400c0c60202c00900c540e400d241c1e60054003041950440000001400c207441040d42c041040d19110b40040c4c90489065050100145441c0b10214801c50f40b50010b400340801400d001c42c83c07685031800242c0050745075456080070381d4041110822903905008040d0040b40d00e0030254981030001001c039444519030f00a0482d00e409220714035041c540258048010303541305800b200c500013115807540c071000e0b1042c1d07550b0f07500340d00c81000300d400c03440c0c04842d001c919a4450341d03440b0004500c007403000e1003980912100e5403054507000d03041084140d01a22911211042d0388955440c0d030548005005c4400340d100c540304200481c1882c80203140c12404581c3c01420884100c14203075510304c0d04075a10006800000d1006050600001701c5491540e80745000d035100f241c2c1c036601d49040940498030746 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 79284192 1250 79282942 79282949
    0x909060e0a02090705160203070312030f050402010518030312010902040609080c010207030303090228081b060405010804080705010207061407110d0f090905090309010215011a030c07020d050d09050a 87
    0x1d918032000c213140d0342c00b410080840007426a505c08078044242c0000b0704290099105030b41c1103101c0b00d00000c0980c1c0c184a1611403482c0c0f0b0208008a05042d0002031150082d000b2030101c2800607002000b00355402c1060b180030180e80c0c10140069a1184440c001a411510801c0040352030094040b0708c02d0008504514542c8044c0c0c010121540786481c00c80c041c000c400c8003aa0403034000301c00d0b01c032100110f8034980e081c2c1c0100d44c8600308480c42d10307114038509202d45140504c1c3d0100d824481099a450000b1681214801d1801c0940c5031102e040c5100180b240b954001e00a42c4009141410004150440b40c001071b40e4014810441c0c2d10004203841d0f6401d0202e01d004103412441c0d1154403140229000c10071302c8c0c26460882070541c1c80302e0000d002c840302594460f1440d03001203400790856030304000000030660380044600300f551608401508800d45070b05083d4143c00040300094243c403e18060755401c640003000c0908000981c182140c9032540c8002c0e4030001503642c203011503282131000710346045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 79285442 1250 79284192 79284199
    0x1406040308030c03070924110f03070b0615040305011a0604080a0210020f01020a0c0b0c0403030207062604030804020a0905060f15070c15030e0d12021e03010909060e0a02 75
    0x459503a0080210544e00c0201140d0074041600400710380c002c041011417500381c024040d4090102c644c408084c040d603040d15840c24095202c420380d8070455002005603030b01d0b00d83c402c8152506413202c3e00020302c9080c07903a0424014040214000083c8001500a540e00d03203038043d11102d101905406005070b138801c5d03001d084810383c40f8170400d50041c14085101e100e003200b1441514140f44141002c0750990341302c14401d00c0091001040002885620441c00c4e4100402800d0b4520301499594069110200ca20982041c420240c40c008a44000907000c10021505d04091103400d24140c50081e01c0c41006850a9008803610040414000618030940e070082d28010182c592001d22001000808207001e4040b11051506014100000302d01c411200040c0c00d2003076a40740c0081c80c03082d0080480e1000c4a00242e0340d0321403a04c41350100e4100c5581c0381c001d0410003000d40d031260000403012040c20038250780c0340c080724004000110083c4507440ba900d1036108032800c0c054480760009899070380604200c065403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 79286692 1250 79285442 79285447
    0xb0a030804140310020c01021312050c1002070b0a1106130c0b09010306030b09010608150f070f031b090f0602061618170303061003090c0b0a14040306061406040308 72
    0x308500c01110b0104400c1e00070100c441c100b0540d45014140c1e0818281003a46a4002c074407509018041304000024000e0040300251200c42c1d52103090342e07209590080c0d4012058441c110071140d10921800024100b4180100d40c4d070f1003001c80041c50704220f0b02d1901c59601075070b4080b0340503144146840107001d82000b003d085c0c807401d0030b01494580e48813900307d6040c036580e4800000091940d04c051b40c0700c0c0703243d40000590b4925205100303003000b003541c1081c4054602501000180c014869805420034901c1c81c0082ca00c048244003500140b44107031602c1249107840001e84102540178514a0948020305568070003260b85102c02c1e030351440c01b0b407206405105c140c0e11203070250b44541c113070b012080d03119100e40b20080d0703a034010380012a201d0a80c85040d50000003c029050406000b4896202c2807071604218407200c03500c62001c01c500c54081c440c8540000601c007040d9034860031955280e1120500003e645590381c0c503042004252500c15015a1000303001d43c46d185180c688203640450b03801078811403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 79287942 1250 79286692 79286699
    0x60f01080103060f0e160801110c030a0c14060a09050d0504060504120206120a0609060f050f0f04020c0f060912040501050706020906040308040303030e0f0613031d09190b0a030804 79
    0x40d102601c0c03200101980c44003508185c001c00c0100b02010482c0c5a03110103130b541802c80190a6401014140321091000c200303c20401c3c0e40002210f02c10b01c4a49000e0003001084d00d071481e0741241d014230300d0b46148603120034020100070650100c039080d07118000301c1d0255030b4104000e41d0540954414603000c90001c2c8801c125040c020400e031049148020b04c080e250421005130f900226005640600700306540c2c0703070107000b541c0452007076001400442080c5204a454000052426903040b0302481c00ba55040d00101c42c15291a015a071070390f641102a5a100044070f003019aa40c04116103005103841100d148881c1d00b44114112420b0707d406a5079103240c586c160701c512010b5800f0708100c91b003003201007000102152941010300027452003613034042083c00c6003c3d0300c2c51900c055402c00c03c0f5950003c41c00c2c056844604503241110710340c1030400050405100c000200d13001545520150032001720402c01510713040045a142d0000700016080006100d032a05010001c4094000200820400c12050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 79289192 1250 79287942 79287953
    0xc0705030f0c15040b03010608101406030601180e1302030c0901140603040c0803040b031906050a09090203070f06170906101211030a140d0e09010e04051504080a08060f01080103 78
    0x80e103c0809102410b498155668030980061b403003684200001072000b42806184540303260420000c0c48801d09084203001c810b00060101d10020f014541407025088500c01424480700302d10004100004040010749064103180840720487c8404901c01e020f5100c403508185481400281a100c4131441800400198814000b01340c4c00036000340c9140301422000101c0b80d50401c010005080203c02c81a26400c02c0130100c8000348442c800c0901c0d0700d00f041c1c4140900d48681600c1021070301a00408500310f6898004681044080d40180f113441c010070b40040790854000c0b0443c441d00c0040000b5100c0780d41c4080b800c580b10401502d0405509032084020800c001c140d00d40301030f140b8090013580c0d540c4001000000e1500400040440d0f85c40c40090b846001c91070b051200d41c1140c805804e0030b44d0000c1c00c40d0006003845030140521409602c0300740101e418803900300a1244140040b80d4803501504142c10450180c5d00060f49400006000000240040c2000382c280da140c91010f13115808280d003141c0c0d54 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 79290442 1250 79289192 79289209
    0xc10050405130501030c031712090c090603010905061b1b010c0e100806010f05160f151503080f0408030f03060306060604080c01030e330a02040815060103090c0b0c0705030f0c 77
    0x141d0807040c06010426527402183e003801c0c051000f03070300104502500304040c041c95000c018451442640340c40aa50b01003600855499030296003032352024038840000c0b40750109800746501c5034001821f400e0b48140301c014150311003000a011901d0701e20810115208101c2c0040400702240002203410002c06c116500905100e04041341c3d604185041c2018450400d0704895481025a110340d07400003400d042c815680c00e40c8515800142003804060840708440d12219003504c80100b50341c2e00007a01c107820083c1030007a103001d00800400d4981d506c4640d01114840d410554a162207800380201040c09403034858112070803980001d0141060380b007840c0055008003010214121a40a90301421420300c1c240c042e40042d802644c0c241d000625000014400300d9403000345071410f0144100400e0006070400030303c00d03441d03620f0341031034482a94031540101e02401000d0340050100312150004919000040054983e00842c2c0c1c017124505079881d4101690307070003100030f007036165002010105c05d2820140f21 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 79291692 1250 79290442 79290473
    0x3070c021020010c020703110a08191e0308010b0912070b07201c06060902040b04150206011a090312070602040611060c0301060305090c10050405130501030c03 70
    0x8019110424a80105181c050304401441c001101e2014500003802c80b4100e4003601540c801c000c204403000030b03001039520000d6010140c05002c403400c0d007030110340da0800100054114001030707541500394031029905194840b2000c50382c800c01503c0d921503003003500304100100380d0141e6440740341c1e034a8a685031a0650207001607a801003141008d60052013403c00c601001020103168244d91a101410040170441620785c03e0440e40500140c092001d0ba2082c5603100c0b09440703020b045c0c40143c0f4500d00382004042503032101d4640c0b80081030000b132203070300c14001d07104803092a802000000d50041e81240c4031482401078101140060b54601c0024424030040d089a000283c00c0300d00c00c0c000542000510340080100b22110703900083c0c14030170036a204403003c84085407400144000c0c240226000150b00050007030208165407a000629503034000c21900280303020282180c40d20b0080e00000421981c0700703008540c09001494112400c285c202d00c200ca041343d0b004528012010f095a6540c0244c000b5440e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 79292942 1250 79291692 79291697
    0x1506050a020f06150f0609030a060209061207020307060f0b090a0e011518060512060c090a1815050607170a020703080313031709061303020304080a05010b0306090c13020307 76
    0x28051402c1e50000c002e52400385400c50255140c80c0300b900101709070075100c4000c0b540112000c0c000401c06807000603800c08096403102d40942c81c0c0702c2d500041145805511070b40c404425140040c8080107401000902d41c00740540b00600c40d40f00810b01600a4501141049400000410004043d5107a50b8806510580c2c0d03900003142e90032030a0000e40d201400c64101c1c0080e140c0103800610040c1c3c092050000500c02540c0c0010904ec111a86540302c00008000c001c1d65900024150015036038000c40c1c90140c080700303281315080c000c81448a002800d02c480200c540702000100400c091030040b055442560b4804c05144c0030421980014040da008021010294410200d0100008a920000e9032041d0303a0f403a03443c001400760303041c000c000b001c50303441540b40300580200f40036800b0750204e07809500081540c24166903500e5450308a180d40f04940c041c40c2540540ca104d142044010b4102c8004a50210125030180d2520024240c442d002e40000640c070a0051240d0b0948820f60f801440c1e00a2160 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 79294192 1250 79292942 79292953
    0xb041404151b030b0f0108040f0f0f0204090302010509060601030e19050106090c0203180f01050d020c0a061a091806040b070207050d0803041e050c0103020715061707091506050a02 79
    0x10b01450086401c1058802183c0c540d9828241801d000c48242c0070000c007442c111182e81030a0b100c24125202940c0054140c590401412052141800d0300343c006a42c007900401c0b064405081c024024101614901042d018800c0401c185d58070030b0041c0000509407101070f0501c03007543c0e0424241c0818281c011580e5540382c2000041c2e01d20103109641710340c0080d4002c5c50f940e008980141114801c0c0681007031281441311090b003226640101500d00030340980c1401a60703545085401490241c204c14020a41420440007901903401828211311840056030040030a1310b4000800d109802c03100c01e030902d0380e40228001800301e100e214585800119900540c0e00315920390010a40e82d001c0c8903019174039050300209110070051160084d0300c100ea40c000102502d110325554190700d480301c000f0014109a00802d9182c20300915400c20315000702c14401c100602ca40d1010540c0340840c1e80c0900b02014002c2040c00a0800341d140a50700d48446000310384010741c1d04240701521580c1000c1003000861082 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 79295442 1250 79294192 79294211
    0x30a0f060812070302121801030207080d05010b130b090d03030c170406051e060a0605090406050a1706072105180f060f0106020309030a0213021c06090b04140415 71
    0x280082e040d12800d07844141d54500d01d40c14068641140034011280443c000c100c6461a201c00702814100ba08007460090395503c1c003801d0002e42c2e80650840403001900d400c000186400b4580d00506807000442240600c9550301c904400b6a40100c081050708042c1d01404280068401c0e486603e0018050074661058500f03294506a516400c441c2201c0f450340d80e90602803507501e03106980062100d00d418005062900d0000304070040c80500c14001030040c08102c04034503a5480c3c00010240c41c002d40004003182c1e80d40000102001c02c182081a0ba010343c002060050b8032a800050524088045001d100282c0040c01130060000402012400700150503c001c0007405000c02900510301300020100350401500a1440f124180c0c030007415540200304002441d1030204410081d1901101c0b140c10100381105c0b020060f00ca80007a9810020102c10301e0078081c0d919a0141d0113032120741400f0052403945505100480d5107040780360b04120794840016001801c1c078566000300c42140640802c14248 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 79296692 1250 79295442 79295459
    0x6060f0304120837060801320f0f06040204030807080d0605010206270c06070503040303080f01030f080702032811061207140705060a050f100b030a0f06 67
    0x100351002c07221180d0039890760801a40c40311246030400c0700d0500216145049900e400244c1c2108840402c8038419216054909a100d502c4a8028411600244101e10a01300744001d0729084001e03120483d02c214401256113007a10f50000e03c5140084c1d040005d645070601e100510110041044e80e01a400f00f00200c000b400c13880117085410310904100f52500000400803080e0b5080e03400031411988400c082006030b0744d840108088911401e4034a040c000003503809141001c00e8030364141d410000014441041080c0000100304032030181d0b98556641d207441303c244221110a20003e050500098203020129025000416800c0e20040c1228503603260461030704000520081030414100941201743d00380f0613011580107443c1c20407154145080044a19041c01c00f0001c0d11480030045602410100d200002c0202e850068102d0700b01c2d02e1a140c002c2802000d01822104501c19101c040045100e01d01d0340c54038181955403c0103d1421a0f440c121020003e05001a8001c200c40c0c940c0400605180d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 79297942 1250 79296692 79296697
    0xc1509030c05010b18070f03062c01060c0f0b06010c0b010e0603102903210310150c0308220b044206150801030c150e0906060f 56
    0x34401d46650300010030714200746003110050000c0d14061940c0c1299801c103024007060071070340400710741001090b0700d021400031001001d20360032200640d20700206003840d018098207483c81c2e41c06082640307401c9a80303500b4104c500808081c001001c51070700c0c40302030b0300082041030302980c40755061500340d41601704c0383c4135820060003e030710102151400030140003450070144600d62204c406c06109000c28060f041440c6810b015002d4042c02a0302040c030461156501800780c034020308541025814030b0602c135040c540c920390055a80800111180c000010410901030030f4182140d85505c03001600d0031107440985804a00070b041404403c100100b420051501710b10076192103000c2e00220352207182c680b070000401c05c00d2a031018040c680001d15030b000ca00c081030b0344031400030701d5046440404c110048820058000c40d08407000c1422507403480403066600050b080d0403240203800c907030000c80e9140b070484501c0000fa004480020080c80c01048241400c03401203401c008060301e01407500c4109014044144c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 79299192 1250 79297942 79297961
    0x10c050613240e0132070509030f010c180305030d05090102090301090609060c030b0901140105160f020f06030c1204050a0b0705070308060405060f100306080106080c1207080d0c15 79
    0x1c9a071030002c1c0c071051100741701c0d03070065028042490608010841d07000e481c0340038a09100c00c5007051400014241c138070070400e41d25451000350841d07403004410396616028190301090304000500c0324211080218990b501d0b501100d4020025501e803900e000ca4401c06407900a02d101620740d001c128903003150710240b0541c08500d003d01800291000b0610b01a0b040d12200c00e5440d0401d4146032282043c2d5880d6802541100c5507103180e51012641400140d03680e004060103c0311683c004103082c0180024031026840d075510840f800c036414400b8800b000f000c2e001c00d4480c903502581c18400014041c902040301600107006004445020b8041e5544510081c42110044002080801c4a00802d0b40004196801600403030302404a45454800306102403050300446100302c02c10303003002120501a41c040701c09041c06070000d100301030300d0310001a80c0b044802d140c2400b4800c80301e40c80121520104400007a108048080d080c0580036044c21680d0843c120000d80f011400f583c1c410511108902c12034610 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 79300442 1250 79299192 79299263
    0x4030c08042310020c190308030411041404050613020102070506030711160e0c07020f090a1e02070b01060c03120501150f02010b01080406021b06010902070c05010c050613 75
    0x2a02080c401d80c4040b010360041e1a0044007144109181d1640214010304031940680300c0340000300c6104660300c07030b1030855070014108150000600007400000084003105410135038060144041411815428107021500074013250030a0020480c0c02d178840031400c04030303801441126880c80c3c98a0024010340d2046d145900890100070031107004001c14010b441207041c0c4106c10006452909c0301ea02c01480d001007468142c000d0016907501156101d9907208260f08020308040c1340f610b00070305001d009103416510b080e01e4000e4a0058500c18a0a00132a160b0b590b1007544841c0591170682d06489288251508506002d1811016590f4100a1294900a203203c1556251020050074040c1000e55071002c00750440e4142043e0b030100b40d802c03100e030981090303110b800181d80b081d050013101059084060401d0f1140034000001904200a03009003095a0081b0500c1c000300d562403006552403560380d00e00400507001840042d802040550034010002e0080101e08001c0e81c2c0d441602501122070f030422500b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 79301692 1250 79300442 79300469
    0x30601030e010e0f1509100b0103020d0906141308070204020304050a1b0311010801080c01080405030408010e03071b0f170a02120a05010c0908030f0d0e03120f090606060706020304030c0804 83
    0x1400000c0110a8a48a001000c1122400c200c511141c4030410b030580d041f000c41c0c0b40c411000b216486941240c01d130b80c00c50041001004494035003240038294403051804020b810341e01103190b069070044c42d00100c5a1014256207070110a03428030019400c01441603500d80107210381a4042141001031030401000f41d0790b9101c0781070a51030b0004105110002c0181040f001f88018440c90074002040035402c2000d0038002095504c51818514500c9990040d0b072007035080520000d800f8000201500d4064801d81c401a01c4000440740801c0105181c07007004035007401d00d0030401003403d0801c400c000d081c50000503034200171805d801240b8048002c0c4108011603000301000410701001384941101641c243c600600c41915000380143e59000e4405402c00081d8005142610075a0652109404110b110300b5292601c4c0c142481120700700040341c694000c2603803480095062180810040c0c0f0032480106001d040012540b12607009400c001c00803028030030300c039102001185000d4003400060125691405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 79302942 1250 79301692 79301713
    0xb070803070f02010506010903020415050a06021005011202030706120b1c02040b010207080c010f0201020c060702010c0906030b1309020d020a08010e1b0315070210150302010e0d0c0506030601030e010e 88
    0x80110742e214050804592400f0203001d41ca81c2c3c850141021030303404880c017081503580742e1101050001d1903805542d22480b100800034003240c0208008a20340c0c0b45000411142c0e13680c206201c0c00e41c0e01c0090007903140e007280006000039030084d01203d0b9030144000f00000d0121354040891403007054545200241c0b102120340208510301401341040000e4207201a12007a0310304201150b8461462807100d0500441420b100201d5200358103503496219290b0440d0624248101c0280c003d202e00c002e55800503415a02c0841c44902900440a125a0160a0403542840c1d003441d20000d02c00355200300e92018000c0f8200d03000d0395444007200050a40d410000840a0820981d540380100a02d038007084910302070344160f1039503000301b0900102c1c40c00c090007800e10307034903030030100d042011007820140900d141868184415103003d02c03540c10b4a2003a241d19030118600b80401140142c4040010f000000c402c1c0140003034101500a103400001c10304000c6840903046400c0ca0075141450085100c903480300c640e11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 79304192 1250 79302942 79302947
    0x3030801030c05041b03180602030a05100519060f05090603070e01030f0e070b180d0b040201030501060302090919020d090b1611100e070e070804050c01051602010c0c0b07080307 78
    0x40062104590400c82104085819030084100031029800c0c5a51f03034000100000050281020241d44003200319581c0ca0b02d0241a002001e003a1080c0c4c244003200a0003150f58100704103103825400b8440d0441b00c1007454140c00710b80c10040c69841d001006024443c05100da125200514000d50b40d03902c50100c24107114000600321003010032480c01c885e0030a491080c05650101e044029960400707030389581e803040f0300b9800444c2560b081000e500100c002101c1d005004081640c5401917200341d90500a030303680c83c41d04030306901407072203200d600c200c80c81d01003103860080d100752800200203000054102031800c206076084900b911010345102c00303401e003001180d4102903a1b0002c5050213003414007900201d0840f0a40d2084103160806119a842c02c0340d0354510030170045240280106803031b452691a10001c0144900c2043d5000c41d464407805000c5401980104203898001da0301411442e1003a0068004540b8440b0030302e01030f200c0c030022210100f000f844a20046c030183c0d0048640701e9880c01c5c0344900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 79305442 1250 79304192 79304213
    0x18090f0304060914040608070e010e0f1e040203150703020c100203010e071d030a030f20030906070c091802030f0c090c09040f1a0307140d03031808040303080103 71
    0x1924480d0000c0106100103500216a007058075012400145a1100ca40c0800c0040c0311a0300b140d0b090b44101100065600c0d07000b00340c68142c3c0c1080c0f0b0b95034000d80f55a011803a6816003554020311604007069240e41e10541d41e96030552080c0000d0850710a01c41801208003c050280e90740302c002a00000c2c000b810b1001088403161070321800700c00314a07641c07401d009061441400390604041100d98500c440355a540f0140e840d0b6144c0c0c0c01026284450043e29025010040e00b41c0300350007150502d00f44102444201104401e403401c11405035181149400400038664800b04089562148402000c150325220740b064102c01d25000c071025441401c6401054644aa90b0704a100c543d80508251103045c0c8807076800540005041942c1911038805100083c00f400200201044042c82c14000b010003120f1039a5900101030141e0513114402e4440064000b000304580300f00b5007009030448074800282c480d034804460080000c0b00c1c18191a1203030341d041d0060b44982d00aa001803c001c0060092141004d030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 79306692 1250 79305442 79305463
    0x2180a080d020c03061504050612100207060609020306010207170703050f06040606080609030712030615031b02070311060313020a1d0606030123040209062208010207080403060c0207051809 83
    0x4110600d010364405210b010210030040c00785440d90301017481038403150304245041280105942c0c0101c65481b454000f0740037090281ea51074103280d03000840e030345940301301c90040006902600c4a9410034109611200010381c541d80340d03110b1040d00101040301404000f0b2144412405003a4500305420404240c506940201140e0340210052000c5604000304076100c032540000e0104080380620303030540080c0a5540142c240e00d508040c51414070303901d0340c00740d040c910b001d85101e5200611560102c2c0c1d070723403801d0000500c0c04030103004900341454114007039540b011160a00e211460340700d50203d2044251079001c5219250b03a9001502803458002060340c2c409419a4100d06661501c145254818850f011001024034110211034040d211074040f0303038001001402c019666035003034440c1070064800b00c1125041400085000c04d607400c0c1030086400540e04100e1181c10581180c17030305001854821070341007c0d44505200001d00d600e4480d2800c01303003071801642014502d1304201690508801e500c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 79307942 1250 79306692 79306699
    0x3030801031106191206090509061023060f090d0305070c210206030907090510060912020619020c0d080a020d020607090b18040e010203060102100504120302180a080d020c 75
    0x2c00404000313113491250b42d025105203064001d01c00b0300c44220700244019000081b140703081c40c040200c04080010140c1c0107103412954445101d554030407420107044e01030800188410b80c1412a0340704d14040c070182c10421002643e8600d06106c040015505402400d021804590042000c005000d0248070000050085640c0505615080a040c0082030351b940f200911030034002c00840e082900800c80c9601400c10003200300000e0520019180b00e8000620070785001a940d0240441c0019214900a41d00e642c003601c81828656488030400041841010325000c40c851844019199a20311044c0f00705240503040700c0342d5400741e0f04e4000381464500341e080c5007503500c95802d000c1c0c80c2d944207006000700c0c4d0b500c5105a4032400c1e01c2c00381d1454202d081040710f0f4001d050081407140d80c0e2040d402540540d1090f021154059000b00040c0300307030341d4100c030094120700f0304407180e43c402400303034001b085095511440c41001a030307020000380900300c0c40c0c1c1041100b9405850100c0c511030b010040710f2007014048 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 79309192 1250 79307942 79307947
    0x306041a0c070206040e041a010e1f05030a020409051c2d0804060b030a140601090e0d05090f061c06171615090e04060c030506041b080411060403030801031106 70
    0x3e80201c2c40d94031551080030804200000080e05101030340d09080c03601c0d14240b00490283d40d540e565451400c0050b5403001d04034030045880030390840d007440c01000300d841c050060500c031661902084010030340f40c141034900e4003980300c40281428062580510760019512030108401c0c46081c4280010807a1010024141c2015000e4114941140380c05a029910070000f040701a0708902083c108000107000905001c0340b102003001102010031510b0603200e00000c10004174090072040f542d618500d1510f40c0209004000840903400e2075038481400410142003c2d00d850004191444118010003c540c1466a50002800301c01c21030008038ad42e1103071540c0140f241c00c003114181031000815128604c829040300e01499429070050700b1200c000d000100700c1811074641828694040d2440c25034090005e4a0080096114079062058002c202e1011041c000440c940c420207035641c1202400c00c0d50804c00b40c0405a810341d070380d8002040514072a68440d17071076500d90320b03211349501450840740344030301f50a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 79310442 1250 79309192 79309207
    0x3060e010305100e030f07050303060910030209040b1021020103050a0605011d0411120708010b040b0703110703051b0301050a061a030a0905030403060e160b180a050306041a0c 77
    0x851180d095020f00e000103c81010300e280f10320310700c1071169201c4081c1011076810103200c000b20183d031142c13805a691404941e02c401b0744a4481d261400002d50141d002008100403980c10624654000303004041003400680704e85100c2c0d800700c1e1350261114040c2c80b100b0040c0440d6810b008035508420342a03002d00402d8100400a4036218505140d001003100d8008000c013107070703210b0308503c007803200c2000b10554501d403041c2d140001c94021194880892461400080c881381c1c0c040441d806c40b206200c6070b6044c4000d030fa4088400165104010480344524040400450814400d02d000000c4c5d8078814001c03601584103150035950010b0400003018505074080015958802c944440e140d20007100503034030f6071514103c0008007504680a00140320109011007080714a501c10418050074100302d039000980307182c042000310076500600448410a01084a44207101306050410302002403200e8400d0351140c000c0303803078000c0c00caa05440c46c8003c0c0d00c0b400b03041d2081c00310807500b2801c91403007286032200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 79311692 1250 79310442 79310453
    0xf0b030705060d090605070512010602120307050d200a0e0d05030f0f0d11180409020a031b0314010204170318060711030102070f0302060a0603050a0f080f0a0f03060e0103 75
    0x1030610503940100303400100d0050024181e8802000a40c1c00481080a4103001a00511507000380c08402703003150030764001051441c00002d012541c42c400308803040c42c1d50307500001141c064003c2489003044545503010aa1102c0d208800d0020f101c115010700360b00d4903c00c8034000c082c96110203515004510740013440c00400d2000c011038415513034804840ea83c1d5040140b00c01c00c1481015607010b1180c1ca4001d442501004080050541a844800564081c89a102004121400d00d20300030b500c80c034456010000101c000c0400c505800602980030300d02982d03601c801102c8640c052106001380d40c0042d050149a416080d040f500040d0080114108400e58510809800e1141c3d58a07200e0100800c249040000000501442c408080e00940d22981d40c3c0c50020b011414502c07003200076001d80e40c00141030300058812502100c0c2c0040090400c02440d8942c6088e0805222060300d103032008104200d20000b00308001c12980c64103541d403031107028480d000202100c0c0b160700403a03014400e10004101154 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 79312942 1250 79311692 79311703
    0x706090f030b0403020f061603110906030406050a0204090c08010e010b0c120903070b18040606051303020f04020903011514040908030c0a090503010606030c09050a030506070c150912030f0b03 84
    0xd50042c1e1201041d00e0350305080e4644100071000c0781261080c07404000604110103040c00010f6120f88041c0904a0205100800c40c0640444a0340000e0140300080204550f9001560050307104140146019280c240400a5400010203000464100c1e4010000c0e08110f500d03490040c031604041c0741c100b1401145a540b0303140c1c0700071780418508006c5044c48a03580c02f844114020310050a03010340c3c45c0b1889220458810076010720500ca58030f4802c00050b1140a46d048980c0c80c100c010000d10721f141190708007c02c441c40c00e24550b401990a00c0301240b036450900c03070810418040c002d100710703483ca0401ca41c01c00c107014505260180e401c1c000c11000091048007540d41102404500648a000300001110a45400d42c0095170540c2415400101960582d20894094081e551140b40e040e4840c4240007404500f4800100294010800103c01600c40c200c1c03510100d11801c425809203a60000040076251522410340e41c3d0f1038080c9075071305556054455400c40c01040e4000780101c0780000006034841 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 79314192 1250 79312942 79312949
    0x801090f0b040c050303041203170910090507030b0f040c080102070803040b07050c010504080d0f0218010f050f041805090105090d14040305120c0705010507080906071a090f0706090f 80
    0x740c485002090411020081c102d01078103010707003283d855a907a44101d451501c0d60900070f1b00420006030009607094100b000c0c903032080c407510b001800c2500e01d48940800501c241c0c40159070780d000e40d250101c0010be004c4491401040d035a54690018101811301409110303c0764482001c2c6c0e03104000e08400911401c09596000350070005030b0510395204079054690340b0507880c481ca000c0d440d2030200070400440c3e20140c04c141d5400c00040080ca1242034a040481c0f051114a101e8401804c1000300c00350710544807024200c2c80d0f45070640c14400606c2d60404c180e003003a001007409a98040e00b83c60090160310885a00002e100e000307004600f00680d0840d1142c0c0703070100ba0010810840d0201e2402958602110021603102c01101c400340800c80c007408031500012604980ca006029002807a9846801079500441d0031035030140c0350580c0d00041004591282030122030b440750b208010400c51f0740c9418140e00c281c0b61a006009140c0308054268200300d0550002e0041c002d2a81040c4070f000240315043c1d055 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 79315442 1250 79314192 79314203
    0x3050d09060c06151d2e0b16150903020c010c0f03030506011404030501140105010f05040605090f060d02120604150509090102190504061e0c02011b0b0a0b09010801090f 74
    0x111145241003204441c2e81703801c030168142e20a104011581404003c040c481d0910344001d081d41e0800c12400910010078038090004280d0003c0148035204440c001446020704824a00101d2000d5a540ca8146480010620801607841081340c041c980c040c0400c02e1190000d18100e486e88049684180b06041c4034074001d02007607a0351000036800d0340210712200110f104111200c1c1c07202e40e24034000b80607100c000d1a01c00601c03180000040e055005480c10381d600201621140d081505001c4201d44540110f4001a0320401c00762000c10300303858041c014807489a5804025130f40f110b010075080704950000d051140110318114800010840030b002a5054403003c50300e40c9811f8640009860181c0141d003120080050508002401e060300000104116651502c503a2628000a4031a0300400300b00c2a46101146518007240010740c82121070b150340201201014440c080c040c0c4942c0000d50044491404807075407590028890b2404017001c0d030040001c0d10081c040100d25945041d0500f01c0310030002c28 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 79316548 1106 79315442 79315451
    0x6020c160819200607120e030a0302060109090303020d020d200412030804020102100f0203060411040302100509120109080901110606010e090a0f060801020403050d09060c06 76
    0x303600621802c0079802281c0c032031800c038500005000b0441e20300c02c0710100103541c07410003500000d401100c00e07480e170425039840a0214901d401c5618485d5004400800000b64002081410342e042110007095040c603d240a80c042d00411120803101400442c401c480d480065200035800b08410f00030b811120403042e003640651207540507041444100664540c0403a001d4000581c0180c41841140c8240c58440b01e00c9048a000f4a000210345400000780011807510340603031050100c682402c1450107141d540000d5260300311824400c14040d010500c1440f81d90303026440350a01c6500c6000380030300141c80c07420362503580c8118070050200d000113803c100380c0d450000e01d051080d40d042e115109843c00040400c0021381000701214941130301d404443c005180170303020302c600421040d0300142c1c80c1e50443c42c00605000555000c10304201d03081c1e80802405a020a2940d62260030500014 = true := by decide +kernel

theorem cover : BRFrame.Cov 79136692 79316548 := by
  have h0 := BRFrame.cov_init 79136692
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79136692 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 79136692 ≤ n) (h2 : n < 79316548) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
