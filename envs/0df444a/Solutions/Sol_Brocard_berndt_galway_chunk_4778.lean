-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4778
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:42:08.790003+00:00
-- url     : https://prove2.me/submissions/e6dafc1f-21de-48c4-bfd1-59049f87c864

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 859172661 ≤ n < 859352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 859173911 1250 859172661 859172669
    0x120c101b0e060306190305010b040c0804200d0609150509070509150d0506010e060315041e05030c120c07060201110307050f121321120906022503090501020313120c 72
    0x3805c00000020060103402c417102070141150104448004940c0548010034101ca000300a000c0d03a0000c0104d41501c00d940381c4c04141d01409491420390280e03035010444031590407e032070443c05004004070721180ea01403240d104040801401c4c00a162001140302c100c00a4044c03908500c0e1020128413544503410710303038245a0040c040344e90550303540424102c0500151102802806132070305403140d084440783e81500859002405020207204c3c41050b882862141600701e07110b00041000003002c0d1410014400045820054030360b0312101d1841d03051034028190700040a690400880d19448017904060f01c0c6e0042040c24000d40d81c5d14510030303001341071041005105c480720025080c0314440a0700c25650060612858400000d02a0702290402c1c884000c040d68000400c1498082d006441d04e401000186105441c00340c2400c00c1818820510b5800104481e10480320580c8101815803018080c001400280080c615040c03c1c3c400c02042090140501100002c2c0c41464600700004400004014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 859175161 1250 859173911 859173949
    0x90b0f07050109030914060910050904090615060e0405010803040e150411040e09060103171617090307060f080115110a03030615080f0402010c05120c101b0e060306 72
    0x92080f071130042c2404139107008100e45041e10404400407030810400f243c6081500030510054020354542c100d036140d2140c0c0005410a84035000b2600141c1c86000344842d691400b61201001401c03d60018010341404441c0381c49030f410300c00108901100030080700c041d0f03144c0e4403450b5500d17070b141d405c041003040400710b60b140c0051270440b00c0e248100f00c14001d00191142e00e4001d004d1501c46003001d644d501020301009c0d190314030031010000d181c0c940c040201808100103c0310080454151a900d41d43d4413482c02c19100e11400062141c5145801d00c9088041c007d18100042c81c9522084020009241405411003080b10070003509202da000b411010b8400c10920200c07040004a071030b005000c0c260034840c1d440c00d2010420948442130064036001d10540c031310451100c040d03940d80c00441e00c16082c820f00b1342d400c0c0103805042404d0040440289074100001000b01003100507a10450b08540c0c00c8039038407040c101d0004d682c0b17142503446131890307104000403540396440761140f10010714407058040c2e5500c44 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 859176411 1250 859175161 859175171
    0x4110f220f0f17030705070501031802060304080403060b0117060913050d020106032102101d25050f09190b100c05011a061e041503050402090105030d090b0f070501 72
    0x48032450320000d5059482d00840d2148031001e480f096907a81c0511480281a074110b950300f0300165200342e002d00980300d050300b1118800c0d07442d50045800743d4001d41c2c05890901e800a0140f0a0001c0341c0510f9449520a1900c90304581c03440114008501340641400e01c1a00300c2c2c8049128422188100600160040103a5500d503640b130201034004c21062204448a111000c010078440103010440b0050241a4001d0041c0007003034500c0b100100b108003400140088c9010301403607070450070042c1c803151200c181c2884080c1c0303481c404100001252517102a100c1c0500a80820650700d0300560541c003e4403c4410400c140c031001c0400c0b01618070601215000a540d0b0b2a07041003130390100707500003101e0003070b00200a44d000482144500c0e101802c0031036040300c2c08000070405580814a03013807034a030400002074103003070b2521402010500d040205800080d101d0050206501e0008210303801480c0071402040140381159011342401c1d910711074401c20b20404151030303115204420407034083e6a402002085 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 859177661 1250 859176411 859176419
    0x170403050f0904142707060c08040b041e0801110f0c0f1c03051b04030f03050903120304061d0d031a0a030f0b07030902010e060a02010f1a04110f220f 66
    0x400301000c56031740140b040b4030121800e580c464010012403e0051744003074105941000360903a1140b003800c404882c0b4150410000407101100006000601814a031140720300d64140001e00e01020207400c003c2603645014001c4019107000c508a4404204034800d20b9121203003219140d04180072441d0700b1890303025501030062428032003401949101c07400e8a0800450320f504800c000600c54080f15804400d000300800e0002c2804030a26120076072181c0361092070b01040b880800c0c18281d2052102c80426000300500c801c00030180656a4030040402100e500c031240202c1d5944d071810341c600c0d08018541d5500a100001854459040011802030301030180956640b6081c0040c003e90319041c1c80c05111000403502091080c050100a1501655964440b407000c404005180c0d000e400c06005565942c0140303010b02c0103501a51100340c00d40c44600c50081100b00601042d2006d8070315540344640b040241c14140b000c10420380b09118040310402909948015024102101a422140031440c405500107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 859178911 1250 859177661 859177691
    0x30d09090c11070e040206130e04140a020d11130204030503212e15111009020d0b04082701090621050601021c030e070501170403050f0904 61
    0x8100d45000e1400c210600c40c000080302c84048007410500250412a401c02100450180854210b4001042e1b10700d40030f8075125900e0145400e51140d02400c110b00d08020900070340840024a044040d005003a890300680d0002e1401c0381c41c000d0040c8242a82c862903034240e11240d03042c7c0d0060845e0700c82103696603100d0400310380d04c0d000000501d141104841d00300c0210b80d80580c0c041c0c080c3d48203d0101c1d981a08110f040304901041404800c2001c6081c0400076010403024004942e0030040d803503800301050200c1c8800d0500c1e40050000701440d0170b18000b240143c54403074000c403c954021101340880d8880d80f50600c120b11030141c05c140145801c02110240c21141602c40703c08074426201c2c2c088156440d8015108001c05041d9503001030030f07101c3c880304e0410b519080550b02450510640e00300724850aa965415001c0418050010741e81c1c004c0942c0700c0d00100212409400309090201401081c00c208100709000200001c041010208280d000300401c03c041e01e000c030300c00402c00e000c0418801480c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 859180161 1250 859178911 859178927
    0x611070812010902040305030403030f1e081006090b0403021306051929091003110a180e0c0a0f0215011202090a0524060c03031e09010b011e0e030d 65
    0x70702203055000002980070303042d208a4040383d03402000340d800c6c00c0c07842e02d060750a0354a01d117002c07091101112007100f444002c83c91008201000d5262030a85050a988d1a01d02c0e5040c0d80007201484180300c0c0c24001c12505500ba1401c417981210240e042d40d40390741440d00500386644c0034035003005058020340d0801822102c64019550380170f80b603104d0441c0c001c0405d04400ea1400803850820401c02000d40d090400b5407041c2c04010242c100803032484150303d2170881550004045200055200d01d13440c60007101d044019000b000d5034042680320341000413212102e4458802a00c4c2401845401583c80c1402404031031024500c020303807400c59681d04c2c1054482501510012441400c01c81e00261400c603091042c140280d180d034904020000ca0701c501c1480380c42c00364a003194008020700a4500d0103408000640c401c0180c105504c1c54150070011901070100080d1103003580f41d052a0303103c982660704c4801c0a107140c42040700e9189800904400b6600c080602a20540502880800b241c4030b035000094 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 859181411 1250 859180161 859180177
    0x2030403050304091d15040807050f1e010b01030510090914101b02010c081501090806270a0525030f05060405101419020c0712020a3006110708 63
    0x36100e00c609982400d162122550107107040039005001c0414007040025000e270032914031400c1100e00981030090b1031450030300341c0741c2c00507a401042e51661020600030b0080e02200e500070709040c08182005100c0508006260040c0003281c0e691301e1740c2c04140304103003840c0450010302d84142c814901c40a1f110401419005001c0903044212880281d08184144200c0c40300c201d5650f0b4074082519181000d1402010003030209040066000c8042a03140052201c28000c0302070403119500c0c01c62401d211036907100e0306031a040740c0f83c1001654a0200c0c1f408915120f00b404010045121002c0b0040441c100b9202900040c1400031080031307103000c02a002909500407800b40d003c07600000400088102600d2420114284030701002d03021901c42e582410f8280c0012425080240c2028401c00829143c0803543e0301540c440c07141d96100c1c030701b0341c01c10704500b2004d4810a90304150410982e94441c5040f600c008501c008000b140310b600c8103000e0b555200300341107400c000c21541da44040341450345650300310b02c1d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 859182661 1250 859181411 859181441
    0xb22080406020d08150d03050d020f0306040c0e030a0b04061808120a060609050f2e08072c0a090f0f1812081b160302060603010c1d010203040305030409 67
    0x360740c100e038134015100d0718450841564204594080d51007400b00181403100110140082845284840000360028060b040c00310401140c4a20b840c0040005880500d655041407196800b0303d0062520041f901220303c641001240c3d000b030b110783c42c0040c0100ac1c03031603602c00110b0b00002103400f08500b000061250b18140c0078a02919203400300800101c074954440c15000c9581e5204c10041810b0024080d101d0103402007880c60805d0004c403407058402e1041400c82c2d0b10424003c42241a141c01400311a0018900c0c030700b075814940745081ca03a16070344403000c044509a200c1402c90502c0d41c0c850102d00c1c003402c51900103022188482c18000040d0110b00300d05095141081542c1c180755070402505500b084d0002c400d003a94040824003038131b1068000e4034020602c000034034101c142034180d900500c810181c02d4030701c0814503454100203080c4030700502003034400d9041c034140105050f4800454800c012400810a00b08a590b00060b0f00c0c510441c0e100600c24000405c00085902403035100000b40e0705028 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 859183911 1250 859182661 859182673
    0x5010303080a0b011d15090a030503041d1b31090c080c0304030e0a0909030c170c0c1005070c090e120307050f03060109120b01090b0609010203070b2208040602 70
    0x1510350b0145c0c40180e014103140d0070703400d41d421700e000c0c2d00c5140107206020003103290110300408101419541d0704150380e01d40c000a0100100c2d403110010104a8941160304403050800c1a4600c034913408401c080c062081000c00c4000c007906040d8510b0b1000c0b2814502d84410315401c001d5004202518424010b881c1c0ca04241e0b04407590060351154072402518510780c1c42c580d15942c090704d200d04100c84443d040001c4800100f41d40f055403150502240c002c1c2c995141400d042c1c540351074507024640781407420700b070203000d040749258000500001d4640100d589400200007407004849602030f500b006850709281c50800104480320303078001e0b012a81d4502c143c408070700880d81303a510540f20a0307404000040080002981c00c0502c0c00241d81c00960505d0301d12a155034504a001e12040c00300f000340c0302c52031035000420240c5ca642c07003102494a8251042420849101b00207900d9000e08040900000c1c954800990317000e01c0c04021142d5298801d01e08400f501b03050030100381e0b9411901690025101341 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 859185161 1250 859183911 859183931
    0x510030501030c09020a050f0a11060a2a0f030b06160f020a1703030a090812070203130f050105040b090d06020c0607080f100324110c15011409091005010303080a 71
    0x40c2c001c85040d81c5141d261103180c88c0340721143c1c1c0c81ca0751041040b401000700d05080d54880c0b10041c4a007a005001e000404503403401120016404080403011407001041c02e20321001705250480000c440000c5181000525101020b0224120780304000000b803460f041240d14800b0015410342210001e03000742c4001104036111050b1010501d0216010240b40d4414030000315120003540040d04214890305a0f03e06003883c260300e040d080c01d01595200e02580001c25094075540d40582150010310080e0b010030200c034074000001c1c20610550052140c01c200006420b1160303252500c0304036240d50302c14801c40d40c0300c001c1600b85442e4582610f008000a45440100d481380102c40344d9240150300e004c80c040c6002d0301d140d4650484000c42c4d90860304a807052500f0422507a40c034031462038111040820140e0ba02403c0d005141002c0445060304d0401e08041c00500c8180c0420345240c5140c68180d0b00340340991140c8c10402d24001c1401808088582020700100070164010b002600030115110709000030114 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 859186411 1250 859185161 859185179
    0x20c0303030f0c0a020705090a09020102011802060409110f040806091e060604020306041d0606181608070c0821010506070b0c13050a1d0f0c031306060510030501030c 73
    0x40e11481c00040b524030210320b161070041c00501d6081c2507401100d40d200c0e520000310349454070407900c01e0700465036000f0110070355030280101c0c0b0801c0441c040003102845154001480c500940c020b07020590f40d43c80d9014005007010045400585001d2112510f85035070b4000c407651031034122030f4900340d80a4814941c45c5605841c1003010103240d048082e1482d640e07401705210080d0001031080746d0103500c0302403404554020540d1554220b040350050310325403810500384017805990400819803650180304024514610725880c4680443c1c030f14040d1400c0d1106d10089030004071440e006800c00b0400540d01d88007075000749403070005a5501c1c80000090381e8410410032075001c0d40c03402410700310f101c10010b80c108d1060300040c03004c40c0b030301c19612160740c4c2c5840c04240304900da50407079a1142450940b04940c02403040301030385c1c071000c0074003400c6052420280786417003804098510303806024034204c90410132056801c002c5c05405c010301040040c91246000801411083c40182c0320f00d1658200800c1550b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 859187661 1250 859186411 859186417
    0xc09040510020d02040914091b0112090c05090f060901240c0314040f0e100f060f050f0c0a060c02010b100806030c061b06060307050a060309050f070f0303020c0303 72
    0x40c000020784502180d078072410020790b001d02141242c0355420400411442c2c04c82c420f000f10f501350440000b07440c1c64043c1e80781c1d18001c40c0d0740356108242d0429646070700f580e91040300b100480701000c0303001c50410303424030b030078040c680c015001150300204a0302000100038040026501c0345001b11882c60f450b903a5083c5903103d59a2504103901003403c0195607880060240d1141120b641c42403510920f8801c0015446909400070b400c0040942c62000040150380104011541c1081c1c6195804008d10318104020844141510400c4144043c0310141d0f88400d0043c003d80700a00f2001c2c224980d00c1035070354811500c0380300b01d480460741c0c189059065500e25205120740d1030300410180c4184072003004500c0039640b000004003100c1d414403c40720700c011207440300f00140114480482071007990455080159040035001403800303009a2003180100701942d00c10711100110b64150a001070321407040d007030540c1051006a100e110038460b514002926010326880001160b000b5401e8480e10b001c00d60070161a48 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 859188911 1250 859187661 859187663
    0x1503020109350a030801170d11151303020609120f130503030409141b04061103120910060807140f030f010f1b0302280c0f0605090c0904 60
    0x100d5041c0c00784600071191045021a02d08031503002c0000181e503203100e0b00860004030381c1e0800e41241d01060201500910418050901034880720813122280d19100c5da510001c030000c3c1308020b440e5041200040b0107100a0315080501d1b14485424906070901c040d45a001810450043c800c039800900c0030240440c6030034641440c82100380c1307031011400070400c8a41000641510703000716101c1c0001e10795002c00041000304800c9001003004190084402d036a0f030401041c100c011b0303c0d24004504040000c0040b50150303080d83c10b0018090048299084c030710700500c80d6500d01c8401403414451482c6000a00d11520300b0562001d01c401500c402c03085071102400e104505120004900d11307086440e1546100c0d0001001600b113565500010304007600f51a060700b101c3c410203541c1e444840784044905013100300612030b42810f51400f20f1116980200e01c80910780c5203000c02c04070070700229003440303100d5009100760807409500000b0502d04201d001000d0030f07500c40095200d1901c07200700c14284894040c0c821 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 859190161 1250 859188911 859188917
    0xc0a02150307090e0912180102061f1a0f0d1e0b03070308030c0c070605040911030402241c050f0109110412030306090c0507020306010902031909080c06040b04050115030201 76
    0xa41350084001100394090b2480210380a840103401c8090240c401078030803081c0203009212250880d10001e07052410203031803d9000c101d462442c039054540070054104542e003a508404102000400d08111405005244407030303400009008580700f43d5030740089480075417140c0c0c1e900c006810f5610740011242180416901504006000c20110b1400c0300510f0780240c1c001c41d258502031208501900303282c8141c000c0c402042000c103003805020420700c2517003d804c00c000000c5245041c541c0010b000c0d0b240c05c4030380ca40d04410344445482c0d4814580241c60401c005080c020603100209595039018010403a0240101da80da8000042c3ca41114000c25052011035104540b0345402c00f03003a41ca0319020003109405241e02d070180055180c88038807818a5608aa9454a403a820244109828294180d029501c254014024070200007406800b0800d1035507690400526401d02d0f01d0140458040c00308070524a025090030801807055050055100e40d12a0000308104980001d0f0b031001707000380780006400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 859191411 1250 859190161 859190177
    0x50609220b060d08030112030e06030403090b0a020c10020705120304050f010815030a0f060c2c010306050312040f170613020319030519020304230a0306020c0a02150307 74
    0x81441e03241503507000a40501200543c4076143c8500e41ca0b0f61085e8061010000c1c02090300c802d050780900345c6178240f40100e82291540c00c160b20000c0481080f80101c100c20103001035224003241c000c100c0c900e03d040c0c010740707942c81d404080480a51203110500c101805211404210f040b4402d01004603000c1c1c80c030090881c81c840000500464628a0003050224185503540b02488140d900f000f4401c181407103400300e13090381c140d240f03010410303070310f081c04135009003c40c40103900c88080c0d0309800780080d030345610340352034124941c04d0040300540b16950242e030b0540150600c045122100d2001401561000c003034980da043d0b070350310400a080d00c100480701074641004020610310f0950141c3c0144017030009080b520810200e065003a0344e0507800318101c010420015144403030720344003d24100c2044440c005141443d1416402c1f9541038119501c901380c850181c60407449030750796200484051500280115103c000103101a80d41d6144924280d208000c03140302070a2020400301100e20603101ea070380c0d40320303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 859192661 1250 859191411 859191413
    0xf050c030a0e0616200d0b1816090207032a030302091201020307030b01020d020705010e04240b04050f0406060e090a0b0d050c150f0f031f080105060922 67
    0xd140315000055550220341000003050003614a0340c1c0b81d1040340500a0a0080741440340c41c10103030305c800c0c0d41030780c000c05610440d407001c280600b4000c6d900038894503003a10010155141daa00b0800d100e62443c4100c00c20400100300401e4960150984034802c0c0c4a0b20b08004001c1071029442261501e03040446421101980009101e900580318a220242c411600c509070a1196400c0e60800c40340d180020360b8401c0c0304503580d0303410440c00c0018880350001d040b40908041c0001d1406803507405582c000c98075020604120411242c4020010000c20001c440e0745440b5100301d025548503101d864410341244807004074a1402d4418070003100c00700c0d102c07124044080401d01c000356600801e83c501302c40d034605035010340b41c413000c801c4000c4510440181c4130789042103041204001400c1034030b80c1104e80500105480729113540c1124141203000c800c490300ca80d01c480100f945c040385129110482c2e9031183e00011481415003065021342070448914103c0e640310803003060f0004024105407151441200408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 859193911 1250 859192661 859192667
    0x106110613030e0a060315090c122316031113121406130501060f05220615170609100b0a030b0d0b0603120313021507020d0605070f050c030a 62
    0x1009091083c01c02200c1c24081e40c0002e540303015a580108080380e16080e0313100040e141c242200016100100e010402c610f15a64020002100d42d06d104440c01c1e59003140d9075030a4001c0d40c0080c3c1c680c2304c07031061000314585004043d50386c07a0304000741004079060111204000f40b0120176190170316101f114800319a85032a04c034528031070b0801002d40341000e1210f40c1c480320400901c10580701d101102000354450205280c000d0071074215038486443c8a0701150107001c16611190202003514070401401030b06000703d0002c2005007101d600c03400e409042c660a40700616000f00400c000d02000d1040005150b6840086c8104202e0444101074102c0c80301c9030600c8940300060242607540711a18000440510b198080752a41c0c881200554007041e0400070004645810401510004100741005007981801c0b01400c41a003c8090000d100c0c2c140e40310b01c40800e60122013614030f103d0700100040350490b980d080000050400b56004400510180c031220a224010800c0f641140b10717050055140039250380c411 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 859195161 1250 859193911 859193941
    0x70f08030624031012110f061b1b030c090601030f02040905011d091920030102070c05040b010f0818071e06030f0626120c070e01061106 60
    0x1280d00244400d1402030746184810361400c600c48210106a40b1300389074281c9070050031580d001e0203198003803d1900d000a102d100f000d1003a0b4805403050303400c0d0a80756002890a00465640014108040611040d014000139008480c3d41c00e0100c1c0191682034238040c142c0320300d04c030720320315070450140c101103015540f09a1000b01030b403102c007200605154445009009030b4038280e0020b840c1050705080d84440e400f80d6502142c02824110060840c101984960320007201c03000340240c00514042142d44202c0182511281941d10040c0210344e01c803002c1c9070002c640780d06405803078011890102c0341c28003035002d4481440340020548825540d41d4400001070120480d000070700c5110b0040003c0014041d000c20900f1102c40000812016524100440142190081c0c1c034070821030f41c1444030810400030b50700c0c00074020802c041a4201d41d58055011707203103000406502800d02c07003400207040703140160200d03811068600201d040b150390390b41ea10741285c0c1600b808002c101c880d0080030105090220300001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 859196411 1250 859195161 859195171
    0x9060702010e030f0d0915020d0207030f15091505070e030a0b090a0c0b071e0f03230309030403051504081911070b03160306031e02011e090e0c070f0803 67
    0xc96441c2c8450b100030798101207407000b07405c02141e040c0d8018010260300003004144106244000c0061002c00103000b50b95001600c0301904910140910000713024082d111014103409102e000d0000c4249441c100c40d001103108052110359143c0710103e50514032070b0320b0b0038042010040080083e660b054075001e01241010b4041c0740e081c0f16402c04a030000340340204020050070821603040d194040c07820030301244c2d1801900d40d200c1002d00661b20000a200340030b020207261301490b0245c00c0c2a42c80440200c011301a035080200400c02000300170072190000700820540c0d00c90760540b001c3c580082c1e40c0c0c000b049800d0707030010209441070000c042011a01448100c29030300c10728100c0000780240360481d09042440e00003500c403600c00030802c03000f1101c29401c80c2c40180140f5003001124551740714100150101002000c2640982e00c50200350781c894078149000040c8800724100f01c855082001e49151510b2040340800b030f00e00e0300000c00148240c011359400b2a045800001c4042d000d03500d40840e40e0000340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 859197661 1250 859196411 859196413
    0x20601050f0d0b180601060804170703110106090e120f0403080918070c060e0f07060e012a0b070503040804060507061e0b0f300a050d03140c09060702010e03 69
    0x10b0404003094142c001d240c018196103021100c0e643d034401805042440c140c000600784000201444006125451202341605824186984645862800312122030300501c00b50b02d913600380b580200e0498002d62001d10300c61b0fa01422034400c01032a1400b042d503406224890408290144400c0000c82c103104000c000a0f48010000040000d41c2c8480403080c40041d1040300010b1299540c0c607007041120712031603202e00e800c01d008140700c1350782c2018540c2d5080319004076403c02c580c60458491070390154140e000d0343d000c003015142d009008100c03070400f545009070b8141c81c0c078400e40010031a418090000c0b40d003e150404281460300707003025000e80321903129400807140741da07540844441c1601009808032102d070301084080ba11501c40d1003046205041d800480f4440d45156181100c0049290300e600000c01c0007040312000100c4041a4504001c3e09450281060184000c00e00d02135625a11600e5a90741103c80300c500307034540410f51030003401503c09a075000603040204201543c0030f00790044451800034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 859198911 1250 859197661 859197679
    0x6160f0c141204140301150e04030f020106050d06020c12040f0b09061308030304060c0806011b05070503030c0d090b040b0306040518070f180506011e110d050c011803020601050f 78
    0x200d2402e8107038415481402020a00e510060f4141350a025514401d01842401c0c1001400c1000303201c0b62080181005061152015030782080328004c1d08200000d0000904c14120f5000908007403000c0d600802c0600401e0003440001c1c10120841426602541c0d42c81c41c0d8441241e040242e51540340d4000761b80e20303070701c01e400b4850000010001c8040c00013070551f040c0a15140c1c10b203841c0c00400d0310390202440e802d0211388800c02101d66400851900300c0040c0700c6428240b0003040c140981000320b1500030b141c16001c00074115103112000a10b004003030300aa44e464254958a2038000020300544c0100702000e01d0400120315240303016044903400c0b01407800c00071400340225031454a0f2004c5039011503410741546204004040048080131808500b03900b040c81246400c5000038482140318234a04800518030900c2c00402d132041c009020301c020706800303c0d401641c401c0c03005043c82d000300001107415802c00c591910810078080b01349507410761503002001d003079092404202004d6814a0090380040f050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 859200161 1250 859198911 859198933
    0xd0b010e0a0821120c07021c1e0201120e06100e0c04170f07030c080c040204030b01061125211a0a02070f0605040b09060903040303050d0b1206160f0c14 67
    0x4c014940c0038842e40121241d03510150310501001d03510403100c8a4008100720001e0380071a00b81c90081c1200b14582c000034070700211510059840542101121b550280380c8084801e201d50300180d4503003c3c01618008801f202c2d51110140b5003442c0482e00070905e40800d00081122001d0541101e8003142d412054503016400c0400a81c5040b580d42c0c400c1d00c41290700001000401811f00c01d0012206e8251000e514250464581440c0319006100d110108403e0b2038141c1c180384030034070008030000c0c03214601d258003a40051140380410041c1c05101c00c015044903805004042c0828200314460b4480446400074100b440d4941103070340020704040c0c0c1d00e5001c02503500040d994007900300d01c00e0700c02c680014041c201402c00149419000f01103a030644c1c80313082030003c00300d80001a10200c95051400305d6840d4000e0490001800700d03500100d40102d090b00800c010b000c0701146a6215003460070310012400000c00302154564a4880e4050100700009240804220104104083c02c228202154030320300e18 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 859201411 1250 859200161 859200187
    0x3040b0706021b06100f090606051818040605010302010201050703140a0b12010204270b130506010306170607021b1c0c1d1005010804230c060d0b010e0a0821 69
    0x2041712140d40180002409106a40121340000d0241200e40810840b203800c0120141080c0329011110b906102200203c0c0300964558000002c40c410795001d1a0381410301d0301c1c0001c0a08002c5c0001c0f405035007011700203403105129110710210b0200440380c49081d91200c4205174000e04200c54910b41200c0d1500703420300702c2e2400340000c000402c2d404099000d0170311031281c060701105140c060105154200707140f400440d44d80c108079960003c1c0500b400945510345100503001440281c0c0441d5000c0204400003299180204038184109080e409988100d00000030041d00001c2c940540d03944501941504c0c003142c4015080404068810480c2d400c0e4140c0b0744059403240f4114150040240c08620100200880340c1c90120000b0802824807452a0a0030f5481c8100c680b0703541803003007500b0300d441002e980c68901000f15011407440501815664805400c03544003031b0403a000200e02085c050180341000f810640d501c4800c684100300a07106400f05414581518458032100748074070f407400d02412000580c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 859202661 1250 859201411 859201423
    0x4150309060e030409060e0915100330230901030b060c0c0315040309180216050705011b320115050108070e01120b0103020706230903040b0706021b 65
    0x50b0401140c40f185054603250070340300c02c1d401500d900c1209006104001c0700c0020140c4030307210460000c81c40340da6242004403010180e07030700103044500c001c1d81710406200806180410040c903051a01e40056048405130b40300c00184a83d80d0560403140038480d0000c000c007015282d041c005150104a00c20b44c000060303a40d800c0102101042e42007246a43c4007441c0802a0700d140608040300c40c000d510786920080c00d00800c61156000c0b6200c01441d09280c0803e544c1103e10700b4007003484995014086007841070780c0d140f007806060302040001c42e810421120305254244803681c05166000b0340746002c80d0781e4064056000903070b200d0361030071196070300412000e00038140c04044059100210919001c001402c0801c003402410034441034103000b50190340e0214030b080109804036404965030002d82d004030000e01c00c0c004050500e6281545501112001809150144200e00e07001c01e82030300e562800341e0312032183c1e12940f140c00f0800c010702c100107000d68028007020499205000b058000e0403140d541420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 859203911 1250 859202661 859202681
    0x23c0102060741210403020712030e090405070905010b04030b13030302190201020903010f09051b03100e0106150306061d0604030624080f03090405180102210f0601050415030906 78
    0x20010034404015070301113145140701c0d85002c00d00501418552406501d483d842d00880f0404505003c81e2428140110007855140c40060a503100503e050708059880307013403d00400c00c0c03242c2480000035156402c0b01c161802d4a0b0810b402c1192504e0790001012540350360103045081c9a000c1c040c1410300f010092039008920019000540c0c1c86840108050860301044c810341100392800f084100442ca0003c2c2580c0c032902c0d040c00340580c070003281d00084d00d40050741c149540e2203410903030700c50080354040d001101100c00209421341d2100b84920306074140e4078103020300000103081c504a04e8042c1a40d40c604480c0701d10103000c02e07241980380c2d1185001d84080503002c220940541307a065031441e003090410401440780300c015000c1e01c00703845407068a03885180a81071040d0380f1000460150382111422a510482081c003c5540781170790321b01e10b98075907140603152030104800000a01480818a040c034487c0313205a4a0525241c203190441040c0c0c03441aa0a0042543d18107815001a90510030b80001c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 859205161 1250 859203911 859204037
    0x61b0c07050307030b040c0b120406020711041d060901090519060f050f0105011227060e2d011515110601170c18070c023c01020607 58
    0x1850181486241c1f00c142c2e0780001c5011101300700e540d0403158070320040ea41080d807044006d0383d141c03558146420090140340c04250b1052610440c0c1002e46a52943c0c45100c003148400d4480c42e0b582d0340c1c6818200c1d420804041c001c5d030042ca40d100c61030f03c5070204001c0040c0c82010005184034108030114103d81e001c8407590180703082030005105e10360b0006c1d15041c1c60083c5280620a0ba444009590f440e044462088090940a4400c00e02000140d42003e2090364041e411a0300c1456982c0c2da1202d0907000e0425034180a110403841c00d441c1034107020b100c10b10715118060300a203a26000641220400d0018036504000d00c580e0030b41102142804114000c022419400c80d01c5511410354601302a0004010b074841c11072540401c0d256081c00254035440702030f0742850352541c0a00e001290745120500075000e09180c0406001e59010300c0a0352450724491076440f9170100422040041e40c0d6000140c4078040403614083d810f05075012410b401c5c018002540d000029054046d02d030400300414400e2000d005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 859206411 1250 859205161 859205183
    0x90f0e0f07050108061c03080105012c01050d060801020c011a0904170a030e030a0801060311090a030809032b021e10050c0c010207030c020f01030b15030702072411061b0c0705030703 80
    0x2580d02015035041044c00000940c150894201000053300202003520305101c404520740c40600650380c444001011008001e6544181c0a80f009008008409031140e401c3c1020050900c2030612035103151040e43c0c011404607100d1a805c41c18042a000021410105519000c80e504800000e01c041d018254294490351495410030707001400361400c040200a4100050000840036a40c7d0146030044039000300d03916580d00c0c1803501203414005000a0b1282e0b680b98200c07503c4001e015403607142d083c9046030303090f00c0c81d81d84011041c5c0e0384016001600c1e41250711141111044a840354403080d00b000340c0760300341c40c60022401140c6007642c001c10010307008038900c2c003210f0040d401c01b0204001c01400074a400c000750001c21000440c88145465a903130303440004000518503d0081040c500070700000b4400311401d0480180350310722035042e02c03034080000d00010704010580b9130020f2960b00410503103800d401c42100102001640b5000400ca60159200d02d00e400601c81d2400d2169034013a5020b4904c10301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 859207661 1250 859206411 859206419
    0x5190f0f1b2702030a0209060a081e01050d02091e010b04090f050c0301030f06060f0308030103020310050108030d180c0e0405061303020d030b19090f0e0f07050108061c030801 77
    0x5821071165002075006041208449105004200078400d0214281801a00c80e02c0785100c042c000c0c060214840e40001c2c0c0064034203034844d00044064842c17080f184410500322502600c036140200c003072207400d4020701c100c220140140307007524030150301c810220300e1200350303070000b100d89008d0352000e0b804030500702d0000a00348078002d09805003000c901d051031000d024a04240413600d91a100512002e464980307480c48820420007103402a0f0001c180b80440301e01116242d0a06400c0c56102384000c81c841d01c5003030744001b81c03a0214000da40c121003081c1d000d142071088000f0040b018001c00c0704411100710002c41100001240004444013400c1008191440f03482d2500d4044d00d003c1010b0201114003118400f25000130358001b07900b400c40d002929010540c030742c507031000c188241d0b20410140c036940c0b11a0000f10340291036130710402504c07441039420304c00800f001c061145c070355014100024640c1c01c0380c08140701550003100c85682048018007030303c009404c0d03114100301201262604a00150840e00100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 859208911 1250 859207661 859207703
    0x7030e060426030103050d0e15031906080a0302060712200703030c08040c05150c19020a090209091803040b031005090f010b03040b1b0a02061006030905190f0f 70
    0x1102c070101c0555140c1c91541542c03983c0390f85601c5868a02c040100301003511107035403510030700400c070520703c01c0b42d09440781800b55010012404414030045003a1404000055811000900524440d0140c0203080651180c0340c013151064441400d103040c883c1c5800d0340091140d490009400c200504100160b1038100f2850002c0c00e59024900c0c0c601044600e41c14800801d400d20414000c4850803240c1c88104010400303000c3c500d000f4451001418082d48100b01e540700000c60b40c00004d5442283c4c101010b94440c407001c8100d01509415980000c4041e00040450304d000341404641107198049a0030541c0e01c0c0c4055503a030380103c4e56008045401881085a0f0404d01d041c140c001d10031070300d0240b040d8100b0a1083c0c1e035010041014262414141c00300d100d00100c00c400789450460041450790710100581d0281d0f56003000e4854159540c0c81c039500081040c428810301069a600c0405030003000d000641250411180c071100f514404015517511000901d080c0c110307a0080c1c0302d22803881840991032200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 859210161 1250 859208911 859208963
    0x1f030902150705060f0109020906040902030618070203072102030d0b06040306230f01030f0312140703020a090e040201020a12211a03010b010e0d11031203010f0b0c0601090507030e0604 81
    0x404007c0d8014005035003c2d55502c01070303c1c00c0c1c030303446000161a60340d103500107542000148501c0451142d10801d0010199002c0024405940244010201500d00301305800c0c130110f80661600043e0406d0000c2c0303000003c550420542401c00a1000b82069200d40354002143c0060941a2003210b4130482a8003c000c4810150340c0210420101782c031561444c1c6480344030b40000c600040400441117480801001e156001c80c030201300102e1000c10724500000701500940c00100c2e0708010a0710011300003640225186074038403940c1e041e4054500b41c0c4966603131030604101c0f04401414070021804c9801d07000c00c1e40074980300c00f800b0300350003140c124440401444120010380e120750099042c407145d002d40e80d800052031001d0040035202080903501d942800e010204030021800d5060144582030064001001e000d10b06941d5000d440d240403980d40c84e80b60748603102e2100c0c40c208030342200c1d004001e0032550b81d0103175070712000600700820020104c4010900304401150308445089040d42c1c81e0b03000c03000700485 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 859211411 1250 859210161 859210169
    0x3090708150606090f04021201060f020705030f030a0804050f0a03030b04050121110f0d0c060e0303040e15223611030c030d09141f030902150705060f01 67
    0x404040c50070908045290f500c1030303421003806403070603541c04812034036207504031215555000c901d03204a50310f45070001e1600c02ca800320f0b08018402c00801103030915003c036180117507040540041d485c1c80c1d5a8542502c0c3c041c001001501d841c02030303ca0451005500341300e154109403103075400185184403c8104421268180c01c183c41092251074038203040c2260040c005004c9802c081007040034541c070700004810f84110054641c01c01a01c903058801c03c00b8441c480410740b946030303c681010b0340741c500902d0b0381c1e070060f4410094202d00d01004500d201e100200100c00f030718009000580100300014564800c811104029202181d40c0c440ca85020042188852100c8048102c0e103008407060440700303c41c1044440300984203000300e0040400541c0c04101230000781d00c0c042d05491400410580141a0606500c26007858100030520302703105291015640002d085076108944044502c080c3c106d004013003105003283c110a1560f03414007084c041e10040c0c2255403084004011030325152207065045001030380 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 859212661 1250 859211411 859211443
    0x40b010620030912030405030d0c060e0a02130e2b08010602060106021b0d0b130506010503010209010807031a0405100f08011401030b1005061c0c08100b0f0f03090708 73
    0xc452000c1c80d4012080b240003400403038a8140e89030654555a01310303c40c50703201c075616105644043c000e15400944100503180207000400c0315058011050b80c60b5148804000e43c0083d1450b00c07881c190b400c503031244079143c1500081711410107111300e07807a00e6020081355494030304c0c00100340a83c00d254019075141c050102d030b101130900c41d450035002a64450200c4801d00c081c4000341c12500d816202d0300e4040400d1a04154254039905080600040312000340380d007510355014280000c03c4030305050003200c004c158183d480324896624100100c00815400111040006500e0440c0f001c0e543c45000d2140035000d041e6003c41010719000007422140001e034448980c1d81d042608800d6841031940745103044076082803006520340e075807224800b803007001ca1b00202e6024001141d440c80034071070301a0b42c0c0d940a64845003000038a240c040c00355203900c0308803401a6001c0d00c1c42d00034012014000702612150301030f07503e12402d150782007000e548950000c0311303c41030640c010041080065000c02446650b201007203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 859213911 1250 859212661 859212707
    0x506040c050f2206030c1d0a09022511030f0a0210110f0d0806092202100201020d0203090606010801300309031a0f151c0602070b040b0106 61
    0xe8000792640c090912080c0d100c4802080390401c10078210842e8400b0503e107818004200c0d25203c000d0000c0212098620000d01072007404450701e841c0411040c0c0380d4000500a120282ca4240124040d6000c81220a40f540c0c5050b1158841c0c0d0510000e01710741c40c421552202d108120900f8580741c000040f0a500041c2d002c29500000341c2c41d410801810f289543c904410343d1080e5521391458442c00b4910760540d4800c0c00301080715268012001e034090541268055050345804c25030264481c1d90344000300032070102e16010740043c6010084821034000500025041c0141d0110802c1247c10441d0914266000b10081000780c5d0307408455107000d40007180070664486001c00311010440e0092a900100303c280485c110103040c00b5600c0340e00259882012031220711095007581d22441030030780c0d0003007103d4140000704001010340c10560868140180c0320140c24601c0100410001e44400019507801c0e5003008902c0104007000c40c6e052003035001b07440b42c8015502d00704006086a00302005030106020403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 859215161 1250 859213911 859213931
    0xd11040e1806060a0b03040f02010306030c0603090501110a050a0e03100f05060405060409050703030f050f0c0f070f12060207060f020307091701061d0403091502010b01090b04030807030c0c091e050604 88
    0xc0d17010303241c1140e0044c0300030381801007900c016001070202d50000341512070700c1c1d0400034146515402038003115210300000d01130240016180074550040300d102c9400308030144010082c2511035000c1203102140181116050f07203182c619442203584104907821150303120300801405040a0240940240040d10f081040c01c40715200c40703440320054040102008049286d2600f46d500c120195060340100d46981c80d40e98076030810017a600c002c5050f040d1402c3c061240001003990000132410122440811005200c1405a4400000b5800b00500b00c1300181d0301c070600354500400d817024510441c843d031104a035190410049104400f80f8503041343c05130f810500c062202190301242d103202904500351081d070a49552a041e1960b60f05a000300c103130a420755008014081d81504030780d40b10942a00c80b400101d880b21084403141c0301d2808003401000d070030080400028805e800e83e006a502400c0c0e050100d42d1142008410341b961b0118002e054106a003514800220611840350014011142003108441d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 859216411 1250 859215161 859215179
    0x103030905060f09060d05071d0a18060b07030207082a040c0509040536060c0a0c050609060403030506040b030703020918060907290d11040e1806060a 66
    0x40c00340c075024660106000f62210401401c0d5601000c004102d25124203000040c2c02c01000c044559000141400c2e0700700c100c0348986420006e180c04081c10b010901da0030f00e146100c48031740c070f0f52000300c00560b2282c000804415410280460318425409403409628240c1814600710308418042d11558903407661072545148081c207600a0031096802040c400300b80e00080c0d416018554010380c205003080d042160703c510144120180500c808218100c2c2c0384007410840403402040c40c1d9042560040b0041901390b20800c0243c03030325007402e01c1e2200711070580e96540c81c185402915103500030340c45001400f04041e05401050b078080710a6030100320552100e000241d40c0d001c0352002901400010000c18074900c1c0080d000a103080003d000c844050a2540b4503c0c0d0f40e20403031007280c01c09a82c46110304480403e40140380c40300c00d103401c0d2986c1012003a4544500424400400c01000134003084005002042ca558062103048198a01052280c128016908104008006c00e203d4518200c0038003510403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 859217661 1250 859216411 859216427
    0x51003140d09052706011b0b0405060a11070b06191403010506060f0a030b2106041118190f061e0e010f0909230d0201060906050a0501050a021c0210050906010303 71
    0x101108081301640c940c00700684810700700e5000199549410640f00080c040c5510441c0d014622910880703400380e50340c0960000b119000c045500d85840100b0030400843c000ca9002600030600405090074400401411000c2d0070195001c21007c001003007013404c00340b400f0f00c0750f07540c800000c0d50358626100c51446d0800c1c07140310710312040050654a1784103100d1600c0f0111444c0c0700100d0443c001282403001442035540f0790040300c088444106881c100d49980c01d00010101d0084a07409850500b5100c0046034200900281030303c0940300c1c3e640e0665030304400365010340700081014103d0b0558940403a608001648800d40003441c1c3c56007040010030a030b80103003034036100315010f041001a0590301381c601a200301d01d1111100d40142c07504a0a05035038507001c00c005111564a400800180c1e0f40c42100c030007034841e507210741e540c000d141c864101f2455000c0d4000705030007200e610650741c102c180307082494019000451100016800310440041014940c071070542c015100308020000d561540da0000d15800d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 859218911 1250 859217661 859217719
    0x40b1b03010b070b0709090606090503010f1401060f0e0604150806010c03050315030a05070902031008010b010f0503090f0a031107140a0314030c07030b04200f04051003140d0905 78
    0x30081320000e01c0051103005024094400d070a814802a50b5588000b0f142402074050141310f07520708401011340f12502d200d82d02c50305043c24800c900c26881c182054528801c40440f06080c05040c0d00780100da070b070b2800018030241502000d020801c020340031000b0002000148102d0511040101650101c1e81041c250799200502c002110303010000900401e0601a42d46c1d40103200d4426940d02107448211500914855402540107401c616035842e50a820703101461007140c0401d1020021580e040c1c400e40065a01c500300008440d445031341210140e10382008040b0950026101b0148443e4034841401610010104281c00d0403d1008180000d400030520344402002481f030400409070002041c0240c0e924510704100f0390f41c06030707a607042c510003182d800c031011501c044c13031080d41c00209104190003245000001e00b100107207842c10302c00d1000405c0058002c030340218241c0c0e000000200b40100109400e030002c809411f4034507851802070841ca00c5504441d2048904071100d4204000e5084041086 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 859220161 1250 859218911 859218923
    0x60c170609042021010507050a1b02040915050403030c0905010806090417131401050708031f08010216120201050103020102100932100203010f0e041406040b1b03010b07 74
    0x18250300414120f5071100111258004000344d41e00c03c0c034805110480b003160072001000b440305030b86085044039580f04845000c00418500804400c0844035160a1000184040d20024a003622510f42100c10103140c0d00e000440350701c400420040540c10b02807241400b14a04001c407005041c00c001801c049001081d41e80103a1034075001405200002c0b2001c4c0c1c40c1145184182c0d515007148e015010207500c14011010280030141c01407000b94440c000300c0f04201d400c6018203003036458070b06046550301040002504514100000441e08607801c0c802442d0350450a00c0b140780208540c90700c0c0101c078014120038019a450b003001040580d802207410344052500400010383c3c400f9600c1c0044451910a84030380708048854010800030300449856440703445580216405000d82c6042030083e1f203c2401828034000d0b80100030444940502c4600303400a1044144100080342001480d1401c03008440654401295006122840710701c101c4090b011506880354034519810030188040511035214001c00c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 859221411 1250 859220161 859220183
    0xa0e0a1a07020d0606060c031404182f2106030718150f091a030c040b01020f19120906050a081314061b04051005090d0602030103060c17060904 63
    0x11980c0f1581e004840c2c1da071003801007184588505005041310003051084002c1042c29100c1240b40c0c1480040d5400c030b910f150510041c0d08182103580c1c0203811844246d140d01c0541100c0600302d404000c0e0f10340541e00c0c0804102c0d0b16081c0c000b90010341c082c1d001150302d8031315111400384280e5440100e040d0055602c130b07004c010b415000c0780c03100390000e20031002d0503001c0190034100401c0d0300a8a009010403035041c1034081c800b03804c0380c01e20303001e41380e4103105101d0381540039241c02030181c02c290304244189001401594000a0394195050408000301d40141003881c00c088a20208038140007070b41d200510501d0500c03805800c00201403d140708440759a424080301a0014442200041311140c0e183e600c000580141c00303690040300d03621042510a0041481640c14400903016120141c44c1101c00040545440c200c10440a551507480b4941380f940201d403105034080820000d00055009502c1400c000074601c140c0b90780284944405030302e840540340c00300184502942c0f000c072640e0f04150801e0203140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 859222661 1250 859221411 859221413
    0x1a0619050d0207030504060e030303090a11191503060b0a0804080d0603050a030e0f010e01020c0d0c0e0106110c01081302040507090503010c0207050a0b03130303051902040b0a0e0a1a07 81
    0x40c00e402080d040c1501d0a0000644804140d403180140c4115103041e2110080c6001c84020962240000c594084140d4000860600072445c0c032290382120080142803c4030302e00c5100c0d84030000d4000c640141c1812201008582c030b0b01585480703040b006050f00d50980c0c4c10110401d40c001c00320100504080e00401004c01c1e01070032813115501a40c001c652000c121102442a8980076140c02c2050240da4402c0b4400c041548055000c1e021900100700f0590141c40c0c010510401c000c02603d00203c00e5403a2058510041a43d03030248051501030315194580b07054034006803203402d19040703c082c04507042187d40c84c2845060203805a125030312035812640841c0a07610042e046540e4040303179011030f916600380070f0751511203a000300d0780c0c500f07441c4250390b41b004070b030744420f11141c41e440255030030815003011440b01c4d40424401c2c5d103d55044440007071100a030984901010060340c000340c00c2650503010003d6807449454000d400c031213100714151910380340949414503200303030385100105480c041900050703184 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 859223911 1250 859222661 859222667
    0x316111225150c03020c2206170d0507050c0a1212050405061c0b091302030705030a0b060d050703020d1203050a2c1f14090111072a080f011a0619 64
    0x24010410190880c7c0b40d4081c03010301420301e0202040203020345860031a0200b414000c25000c050b07070751a02070041c40002400402111240d124050683d0a4066002c5422a41d5102441c0314010a05881c0c2461500c880382881200080e01281c000706011040004001c0c0d911528241e4445100064040707800600c402c0684000d40740035000581c0c0110b510082040c55042c802e00805481d001303030100d8400f1910340d801d0540e118841030300074006192802c0040c6541c940451390341503051083c816610490783c1d1340d0110308503804101048175141403408004040f50b6140c40f4107980240c0d03007001800500385101041c80d01502411480c20b01c540416424002480f08104503103288551030000e100c0710403c5035070704004101c140403140d16002c2d0a008603110140c14019040c1000e03c01009900d00402e596400180e20707030744801c49015444119603042c4041011040c100185409800351115400000c5280e0031a00e0b8500501c5010b034000000c840f503a261581074811180c4088800ba41c1880622826 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 859225161 1250 859223911 859223923
    0x33061b0102120c0c0a0312021c021c02030408121f0e0412030c080417040e040602091c0c12020f13140603150a0b0a080a0f1109090316111225150c0302 66
    0x1000741c27150f420f40d844555980180030340c4205994241a0054007601c1805a120a40e8054881d034010700500c094a40508070468000458a920070007050085c07264108441140d40001050200741e000c11041c02a074000030440c2d202c80c3d1408100540c0074410140000314050300140c0001c2842451005007031000b811680030345007580e10300c100c2c0e2826281280286d40300101349406008021075401c00080c0c903074041c20072a42c3c810605061a410004803000000202c001030fa4448250f581088140d15901583d004070740030743c4404103040c000303c100840a0480982405d000360302170141e41251804069030035800052450740032803e002d20000080400d60250010314483c060441c4000802c05210880601c0a10440e02c1c00000803c0101304403c000044403c00d40c240c00400040e01501600115126007a00c00c040c81002107001c400443d40308000d00003010059030198140300410088007009800c0d035002d070021000c8003800c001424080850343e401d68014003250301034510826000703001b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 859226411 1250 859225161 859225177
    0x3050f06060a0c052805070e090a030c0309030609030e040507050c03071b0e070f0906030b060f0706060f2c090d0f0c02130506040533061b0102120c0c0a031202 70
    0x174000700d4612409003121400c00310104907118880c01d000000c0a83d48490300380c0c481c40d03e040c06803048211584060f5005950504110308100001c0408030000340a40b00d910441c5000c1c1e80c859610841d00d40030320045442c0a089041444414440110312000020445006660155038001080f00c19909420044007070380040b10800100300420460f02da02c04000061001c0d19a50090040e035030340d9082d41242c04600c00103801000800c012640540e200c801894280d10a80002034155962103031405008243e410503455030f9225042003130403c101c801c400300030032402100e00ca2070b810700d110034555480c501c1c41c540040c455050090701800b40160494a0801c0d0040c20559880c8001e2000e10020981181c6191150b840c24020403003d10360b8140140ca030022121129010460200182000d100310800ba0b5074445002c004805480c0151040101148124000980c50300b401c120820740c2604010702120500006120302ca144a0002a10040e0319802d0b05103203250545080d640703800380c820419 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 859227661 1250 859226411 859226443
    0x105042d15091a0408070b33010315050904023109031e0c080904060914090d050304210c050a030207170a050c060a0203070507120303050f06060a0c05 66
    0x101c444030510440c0c004034440ea1240c03201249400f400000c44486520565001c1e003000001c0c0417400004a00e054041d0b00846d00e0203010700304128203a02e40d901c5c056074221103080f9000c80c0b014003501d96098050885403402c094004c1d04118100f50100c1d061400007080a4801e01101c442d084000071003920300c480c5200410300301040d18524009650281c1100c6030214001140d603400b96505003c10300c0d008404210654030403208003402d48640301507401c41c00c80d070382d445991460f00060001641c415075000324a035202440c1a45001d0030f15070b0034610300344150401e1042c20420000000c041705502100341c044424415030440c402c107003c0300c00c0000c5280c010711a00c21000e00c0000e040c2c00081800c2204c0c42c3d01c6240e00c2c0c468078a100c140d101c42840c40c004225511400380d52100d403130070801801701d601d45807040301d080058a846170b91401200e64032041c1e4010a603d00031083c1a07043c01400d5008000d101148c2080c10424003080302d5100341d1001e981041131030304500c030403c5001d201280703601c80c1101e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 859228911 1250 859227661 859227683
    0xb060f03010f15080f06120c060c06040519080d0207050a1709090603030a0c0b15030d1d01020c0f09040213060902040512070609061b1b0302120105042d 67
    0x214410010360264041d10b80780300141e503103810806101c1c4d240c1c03510502c0c4800c1403840645404052082584825411031030038001e40c1c18144187d26202c02500213000d0403002021b25090505003541008540d02c0064100c1410700100c07030108a80904a506201c02000e0040c2e480815040c11810705032803007001404504a490f03503100013070400c000f80c4410241110710000307580360b0000b01982c3e40702d0b112512010500306507140011500d09010182d00400c110300c0e9403100e00505000034180071954030000d0125504214240c21084c40328111501ca4000780014441c5003115800901d80c0400e0801c0d6501c182c8c0c00314001011500c3e1001050540e05203c6824014a0f480d8240c00003e50040c2c01400c1c0203407046c1d4a10140c010000030a41c1c1184d2450700d841103580d0600600321020503282e06080983c0c031051110100040d40080020740d06218444000c0d0a42e087d441040040c92007010021802c2e0b0500e4207000c0400c44045031041440d00501d007014180004041058850f40380510140480d9a84 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 859230161 1250 859228911 859228919
    0xa0206070314190e010c0c0b0702030a0618121403010311041b0504090c03051303030506030f0d031a0402030f0708060a0e090a17070b011a0d0c110615010c060b060f0301 74
    0x115441100d030140a8a0f201c2c602e00055004454030386e115580a801138106041c200081403180c002405090700113001d8402000382511581e09907001e03802d41024696800300b011017817008100c0d07012204107440c50003070a140343d0004844803500040c04080d02c0948600400701d6142d90b241d008592200b441c1200168008817040c0c040c055030814403507905400d0508526402562203031007582d00c02d81d00018442030800380383d00c003140140350040c6400d8152080c2d861007400c42c881045500c80c003046558000c41d00c1d00c4050610b080481c0204003260243c0d0042c41032002e042c21096080380d02c10385a01d40b080c107507500c140016413000010752102c540b41c4600418000b007640040707160b03508240510307848140c0840b0b2165441d100e219500b0040c10b0a142180144281c45009401410720700061030f103a41010440d070b9510044070f01198159010445646001000100c280034483c3e200c480d41c1c0c1c440c403860070a040080d00d44000680010030b25030b47e4018078242a9594000e543d01c80c158103050303589030340e11 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 859231411 1250 859230161 859230187
    0x1706010609060207050d0b0a060e09030c1207031707090f0602010506041a01020d0516080a030b010f08070c240606050c010b060406050a0302030406060506161a07020a0206070314 78
    0x10038059080080e14840c004540070703000003800c8040740d0011300b201c030140e6115156503442e41c002a200e080060b80782e0030300081c0e0320111480b0b5400350745401c0195543d404000c0405203011b59404072001c03644000d22014010075003280404a42110f015011405940c5010045071408900e401684040e4020140410800e03415440b080c07003040255001c000900100302c1144421701049045401a0300010000707440a110340050320320032400740c16080b001c41d11a0b40b0001650000307410400060b0790340003440176942c0e000781d180402d00c1c11414059036608043d0341c001c08527044c0368006401d1030008a0707032615501683e801403100b0302d11124108229034841000604036400001811450360030710319004070910f844000c66080310034984030245003ca500e88194040e420050058800c2030ba41c01002074039440d9080105464019080d9030844800c651034900104603040401c564440804006c0000954001a1004440e601198070603102d001e240b6049403541c08000a50300a01c1c03003c2945104621 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 859232661 1250 859231411 859231423
    0xe030d0b03010b030309060a111906050403021911060a02030702030304060c05071d0a1e1109190807030609050f120301050918120c0a020607081806070f02041517 71
    0x1c5009200400d1010201980c900030b032404103038005d101700109032400380684183c1c0ca601045c1c3c0f003621506072850400704c044943c51101510b07210344070380c00c00041660500c0315030b110110b0f030b181c01041040765807a800c2184082c502140d00071003001232001840d0b8000c10030b80d400f1950040860b5a255120040103001c1030444508561500c2400341c0031840207003e401000700d5481c3c40448514540d40c110059014081100130303494603040208001c036416a160042118225001c0c2800f03036500902414040c0c003428104500c1111070342c9000c144949100441c3c4001120780112002c6000d20003410040e0a05c51031031010000c0e841a141840a400c1c1000f01460494604841040703865807000450071400c03c0d0304a0400702900003210f4407221031000405070024078107034422142036400c15400f0400d5680092002d54001ca13000c0340195020b2900000800008802e54444d4102183c56640c803030103205805d07009102d19100c6d210305206a5451141d54000d01005580303401145c1c074900b081c4d484070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 859233911 1250 859232661 859232681
    0x516030501080a0b04021509030f010b0a06020a0b061009050a09050405060c030f340908120c0717010b060d020c010606020f07181d0708100c0c02040b0102010e030d 72
    0x40e00304000058000b2001c103640c840c0507040f0042103407580d59542002402550b01812003c402000d104515480c1c50800c035000104176100000138440c5880750802c02072101b0755225401b107500c40280700c0c0005d005074030425004401501e440710302400084080d5204a20f03a00600c1c1c0101c7d0300c040006004080c1d82249026034001c20607101180c458851016580c40225012082600554041001d07900c07119030086206049220780126108080007400000606101c00310014000003428880d00350140b041080018000c4151858501410042e90301d6510602c903c00d00740c45c00000c1c0341320b036404c29080500d00d001c008165680d20f004000340341c0002e40140c0c034a43c009610f0100007040c142d00001d08007400d444010018000a40750203100b00506003a182203503015a00d4550254400c2d0701003154000d02c20450f000390007100c5c00c0c601400d1901e56000740c0c3c004030f54141003841c1d20043e00003200102041d01610089401c0800b540183d014110607403a412940c40001400041004a1785c0080d60b00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 859235161 1250 859233911 859233917
    0xd0b0106080703060e06010503070311180a08061509180d080f100509060f011124070f1b11090103030305061509060906030723040333020309100516 65
    0x1e9201d40408030f00319a1103015490740001c0e41404903900d51300400243d43d005289140101e540c04241205540300c0c1c10400d03180c3c10f00d003100a40e0440c01c0c07501c07481580c0600b801e90000c10551400788030031134040c9a400590750082d070204004c42c40401304003050141ca120200201c03403042c524500020101e1800715550004000c0c140c01041e100c805901148084500050024010392202010084482d5a0310701150521544400200b2007010501c40342408806583c0302d008502e603140e01d01410203000070401420171134030380e0401300001d8200c0540c110182d10581c0c12180e000b041d180240307503407020300400c5a211034044000803c040e410340003c0d11408050f90070b40005000380b205823280d400b9443c04103074481000c0c440d200c440d047c0000a583d00c147c440c03403e01b4032700341c0c00007842d50318403082039603c00d80ba01c0004050003800009400d03e07189480380c80c1680ca15074441130000060043d80059039080e03503000004a007008408122000e100d0340220b40030003107070404891030161015508100004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 859236411 1250 859235161 859235177
    0xb0f0f281d1012030f14041206020c190f0305030402040f0e0a03031506020c090a0b0603010305101a2805030d050405030d020105010b12130b0a020a02061501020a03031503020d0b0106 80
    0xf5205198011008554151602001c004040707400b616404618030303000e055840c09210000380c081118428400e401e004500c0140c0d2014070484c07050400e840d0b440c401c1b1424549100070303070004080320624241d07140c1500d8403645980712440044d014041c0b5110782d40c0340c2402d1108440400002240074001e40307109131020071841c0345e41d200301004200309100d01703009600681c0c804d05c85401c1c04980d242c0e10904100001030100ea4440008156410130b0308152203c2c1c0c0f085807000511017003803003126440941e00c20306510161355840024409100b0f180c1581c45484950021300035030701407140308800341070000c080e14600d003005003000302150880d1250603c01e226000030190f08500611510b03060717440d82c0d20346a2800c00da100141205440c040c010101c103600c20701440300442d980c0c1d403009010b81c88a680c0507964001c140303c020706d42032025050380d481c949402010183d684e00064481380d603030740c5418041400d072100076140b015100c040e03002a401c490b444c0d183c80100032200b81c44134180c8820361a0000c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 859237661 1250 859236411 859236419
    0xb030408030415020a1815200a0c0e0711061b0711030708031c0c02190503040905070c20220e030d05011e050d060209041d010b0f0f281d10 61
    0x3031411294008008544181045800c8035000c0c86002000820320b021a16124440d40d50103940107a50792008030381281803000d011508dd80100f003086518004401000c2604203000c002880154840e043d099000c40041c0c1e100c01c0044be0740541c2e20000c0000d050b1803e4690703540f4096101d1744002c0d0440180000002c40c040303142042d00c524440404942e00030400030004603003941d030050580506440300c0c80180000541c0f01d46500540d4031840460742c98502480c00c030f00c4c2200000c207018000400e10404641031601c0c64680200f00d03c0d901030780e00032150302a98450951030044c040007400320a18000015608100145504010b040301c2d0050203540c004011103080c283d06607800d0040941c0140d07000d003c0301c04100d146c0c000c0c00a941c0000c10024100c8525682070008030b0b51701c4c01040d0265100c0314a4403c44c03a0040003c02c1e104000d441d010b848a25003400503240c00d0b41700600030040c641c403290310030402d50b500b22448043d20a00840071143c5804801801810104a465003550304509402203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 859238911 1250 859237661 859237679
    0x1052a03040503010e01050108070501211514010201141513020706020327030a080408042105010c0f0905041a060f0d060f05030619110a0c060f060b030408030415020a18 74
    0x40c100c0e10400080c0800d14140b43c0115950504100901c1c26080000100c580d007000302c4c8a4015501303500340700c198503d0b280a282d491420700351013f09040d6407410a00c3c00e0904c88400d240f50b4410406022141215500c00c0040c0004038255061100c1038404280c80c010000e081c3e0040d8041c0c03050201ea82d55400302c0c524450078120028071214480d802c203008500003580640312090300f00e031080d10900c0c14103440f480d6501c3e075039039010b107281c00343c04001400b034090080a02c01e004c507500040ca441c1d854203080c048060004166845917502495559940e2910340070342c14445440d414008243c207580e581c0000344050160042d4a25640440c90220002071a920500c0900203c0744060702900c60340e0703a091082c01d0600016102313502544d8a13203105011100b481e000500450031540c5502c07620760880d0802d5000c603195180c0d05070015150a60901130012101d0589170302c16442103030140d517a6190325048230340c0a0040301c1c0010311800440c0e00305600da040000030841c04040410040b505076202c2d0340c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 859240161 1250 859238911 859238921
    0x50a1a010f0b09041d0a020103050c090a0302150906031e010609060f030f061a0706060e01080705060d0b060d051e2203050f0408010c1101091101052a03040503010e01 73
    0x31000c00716030200200000503402c8041c06440100800016110081e0825105105442d54103003991350084843c0e1030031580c052165603041018101014245400d007804600b6000301800080c0c03191044130b800d48541ca40b2982141d4066602500c40740e101e0070898254100341030343c0d503125040e291000c0700104d5258400e0480304102c03892613071080c0f866820010240e00504068010810b02d50701d0744d0000c24040c0515038044a1040c0501403e030343c56010b803c084044825a402100c240c0c0c0d5104010080c20000041caa019280102c0d80c00e6600c46c8450300400003403a040654a0f0060750201d401003541d100396000c14441c0c00031000d0201014240b94240642400c01c580c204850040c0e5042d41812955001010700140d1007401c00c01c0c58981c041070084080d130030940c40000700383c0d141c4102c0030720540d2200210b4031400c3c0040c02801010850303510303005200007540500303041020100c0c0c985810b400c5407483d150004192040c0d120382c2d5180c00d2210303480354418000c9500940c00d00052101c403420500c6a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 859241411 1250 859240161 859240169
    0x30a031b080919110909030a12142805100e0c09013009050303060a0e090d1209080d090c0b040e010509070e03240c0f09131107050a1a01 60
    0x380c460200b25800f52011030615a50a81e9000528554107184e600d0310b004040c02481200011034403540e03030707000050114030645a0b940d01542080100c03078014801e00e146039005004040910042028403a46ea00c0182d500c0c2c15400d101030038101031103101d0348556010310980700c03802210080c503079810b5807000c03040c840c08031014006030700070890001c61450002685030080a000e000366002c2c2100410b80e081e00e019100035900e5800000900c80d00f445e2000480e0001c0046002000d400c0c83c0628004c0c0d0ac45500b40300351014000d07104910300341e041440d88004140f91384034a000b601c0b5044540400020402010210342c110000f0b4004540303802000309840c1200d41d00c1c41c0011260382032806000a980703014080005100e1401c2c45007240307030740a100941200048149001d8000606440c1c001c0501000e0100a455602042101c00c05003010003101c404003810386500d0340800f01c030703135010000340320001d010321094030f0103da034004114022911814071170044203051074000100c440020b41d251b080c81 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 859242661 1250 859241411 859241413
    0x112020406050a110705040c170f09100b03070b07030206100f05030a1b0e090d080609060604031e12171f18020702030307210806090c0912030a031b0809 67
    0x201190f1503604c508480c02d825007890003620202c0b552000404c0517260070103c83c03c04203201d10b0030118046d8031032140e19031154600f40d5205079400c1c2400c88903203980c5a900c0c9480041d0719021900714a8604124000007407105500b03a642d14041414005c1d01c48005450501e070400f0410800100070300d26074180419030700020068480881203998a000015950080d410f01120203400092103c103400503840c82041d1120140140c1070381400000c140030700080a4500c0b0303e95410500c21151142015075080d82c1d80700c506041c0798200a5021545000000d40043c0654100c6900c00e8195034010b045805480c0c440d6100d8201d0340700c4419508014001c252510100e2480803420001f520001c4030907074200b43c0d042001880e00b5100c1d0080382c151340c419541a0b40c804245800d02c03100400c50350170020322440c186444081b50801000041c441d4038094120717900140045002803059450751918272a4102036000c8961f42c10340400701401411001c40780090221100c0b9080e008540181034103803044a0280c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 859243911 1250 859242661 859242667
    0x7080103080316020c0607060b01090626251206050102031611060f0a030204142e20010b030d020604120804060905030304030206040b0a110405130b03150402011202040605 75
    0x103c0024a0b4040010164110301ca020740c00714441d201c0d00014680c47d4000c0d8000b18064140711300140040d50158407510400a959081c0c1a030b005280500110000d404d0b6807940450301c401c046820900b0205d941c65602d00045c650240325143c20401e059084c0000000900a05585500590312800741d03c01d20041a8035aa00010002e9045401003480c1e140081c003031420458124400c210b5a00403019200100340d00250a00c0f55528030b41d9070749425a82100c40c008500c005188034450a20802c64140900a00703c9003a49820b015031010056a034062a524030104184aa0140680411543d0500a028016040044520120703c561007581c0080c03408141d0b25440301c00f02c803003110003841a180d0f99030322040766000403028001140a54003d0b4000c00340703410300c1c2c10644000c0c000038101480b060710b8021602400c0b000f240544040f41e104036254040b017112081080c02928100042940c14002c0301c0c20518901d1003180050b00640c000e90755600395620041c4414100d2059005200c0810814 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 859245161 1250 859243911 859243921
    0x1091a090c0d1107121e02252d060f0206010e040c030609050c03070902091804060204081c08070c03081602070305070803180a0e040b0c1c14070801030803 68
    0x7107009111244106000042c0300104a404100725081142c00b01c40d866042031603e07a40ca07a00113480b41c1281c3c02c1345803074410204e0301e5501942d03c4c4c80c603403d150203502d004011004c1c500c050b884101c0081c07402c18090110003170700b010354000441041d12050700c01c410400d00411401d100704503002d011071076600140242d90030182070091420004104841112001002100081e450b000301b0712114861002041e20b01800020075082c0400343d0800950584144800700003513680001320b81705914519204081a100e07030a00d4170181c4515000424a0321a003c0120b0741c4540c00300942c12201035541d5504810f4403600340455210044c50380c00340000f17810303074007103004007007a0180140e007100c0500480d1000c40ea255286400c2c48a1940401c0150700302251031030100d1030b0018081c012440c03ca840032221400c04511a4101e40301800240100c078502d0001203403076481e00d08541c1c000390803680304030201061000ca04d01034400c03800700c201c4070f42d03000c0701240c650f0380220611ba05807548200414215610 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 859246411 1250 859245161 859245181
    0xc022b08100b1605030f070b0105031507080c160215091c0f0803330111070f0b09011b0516080a0203070b0f0904050112020414160509130f0501091a09 66
    0xe103c034140c0d2140802c0000f03801c1d19101070000c14036144030380607100f141d43c03401082600f401c22100726400c1d480c00c51000c002c49203034003d03040e9074000d01d41d802c1136859803102c4035900c0f41da50850308029041840c5011f50303294202e0301300203441c1041c002c813448031a90410113082c405082c5c03070000080c600411010060001548207020719404141c0c0104510901c0c0703a040103d1800200c0c03240081c900c0c040d45822803141d680482801000c0382d41d04000c0c01d60360f16000d5280340c440480e208100000c04003050ba031031075a1040c455200c2d0000403a0040e56217100350309041d602c03100420314001d440100e1080018024001103040800b56400a015010b1a41b0388041d1456039480b1502d05102108100700d101d440d55101c0c4a00c41c00f0740f201000d00300803000c00384140411202030854030003540858404000d0b40349420340318407040c01c0c0c06207000e40e19450040c001c191141258120301d058a400d05004c090390301416802070703049603c1d00405120f803003014043c52680b243c1c640c0c88140c2002c61180005d02c0501c3d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 859247661 1250 859246411 859246447
    0x12010b04060c0b071b0b010501091a040510110303010b0c161d06060417011b0327050115090902100f0507020103021b0a0f03020d080106080a0c022b08100b 68
    0xb8240c03c00c0034904013002e00d110701c0d4039000c0170216842c55003640184825680a00080040d00131207003940c01c001119801e600207800b5601c10746105581c2e5a0700346080d140704d0071542c0420960340089036100d584403034603003200d900800c030704010302d02c10035a000c45031104102d01d01007120b444408012800013802010780499000070251600310703100304070000340c00c29522200c1e24289401400054401e5010004408811041030300b481018286000340c2c080030700901c010b929906e020000800042c8051400701d0241000e040c0c035424020300b45600080c1406c05412010701c941c821584000340d030b0307a404402e881846803202c00768001241070110301c0055010f80d0042000301c00d0340d0000c0010074241d56945240c40d540940490f107004040b4994010103404118450704648541803c110035030410700c004040d4080200126001c4c0d449040a05805000f032041c0b21074280031407418600100d24484005003021444881c0300082d20040002d9807652000e0003c4040e80d61005605183c0100907002500400b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 859248911 1250 859247661 859247671
    0x3050406031802030d05091509061207030b03010f1b020f06060607060207140c13050f0c07060213060504060f1b02040b03030c030d1a0103051312140c0312010b04060c0b 74
    0x2401e460b0800340980d904200c10520210343e603503055915040801400022500e104a0301040d1a050007241c1e41c55071000c0139220582448035140714036039544a422030140c110a012a40c1552030510300d1150540c007600300e40300c1c012920b60f801c0742d2490400000c80e507410340203200b81c00da500400089106440c0c010010030180e40648400750424581d07844030b03071031103050354210f2883d5030040d038160b00c403800c1250314030410900810741040a03140100300185420030040154115070400550001041050707415280d0920340011041d1003d82c549401a00c650b00c9030051801207401685c201d00954898445181c0e0203418801080740030480d83c1c28000500a0b20851951600061001c142c0c6503204201074051100d1111b40801c0d24800c08580f2101c840840501c00c1c1003505010404c044103844c07910b120001030f8411180c4e5001121208111062142c0120f4504030b0702d000075205682020001c06402404921002031040e42d036103000181c1540b285208480209a002078008003241a81030215404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 859250161 1250 859248911 859248941
    0x1501020c0d11031002030a02030901150b07060207031b2d05070b0702061e03011e051008040507180b03010b0103150611100c1106010807180b120a05060a0b0d0305040603 74
    0x504c014140300c0c140d0b0422a000444d0680c08810001d41090074020000004041840c0ca43e6031400c254070840c1c148981d40010701282c1d00010f4030310425100c2d4400810300e510381c0001e40810403142c1303406400000e40c210054510070203100300c80200405407160084c00d0b80d2080003801020b19111044540e03803c011010b0385e0082062003412034002c0030520811440003500b003815500e60502404101e00300800030040d50020901c4024807250f15000000201100c41c1e0038003000645da107181c07041c50030310950000c40040422102007080098079400c4103032221411002800303842d40e4500110103d0700240c202d04116005414200100c81c02a031101388444035140c103641e1120b107410a220140c6402265010001380490844803040805100490141c04810090000d040c5884c00d010000e020080001c8915595900d01d80349039603408410012449402054540c20225030802603110407044030380f620041d040c034042c0740c0d40303150040021380c1040d40b5884050915082036070071001024038419030a10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 859251411 1250 859250161 859250173
    0x20100e01021306090f08010c08130203010f24080a0c03031101140106090e0a0509030a0e0307030b0709031205030609071b050717010e06100e0618040602031501020c0d1103 75
    0xc402002c498000203407030141c807520011813810164002c182ca050703000124607403401560400c4640d02803801ca0704007005003e51020315056000080c01003440c1c03041e5071450751420040c0f890705c0800c01c2c2050b4402c9008680c100c485e554581071152550102d02004042d0814201c0a2000a010351a944014084803000280c01040001c4801410f50203030448008502240c504000d025000078640c0d51111819009100504100c175210f43e5078019400301c5c03002d004192640d000503490402c00e40303000315040306610465090000340584040ba0a01040d24072101c0c010741400c0140c05542268020f5001822602c1183d07180401210120000d05081d0200b078201c0d0400404982e003000020043c1c044244500e0f01140301e181c81b182100c160000b00400c98100301c040198000d406540d0108441c03141c02000c0742684e403500021821103801d050341520130005028041408480d80c0918800c854152140007124008401641c0e0341000751416584107034803004013000904c0d617080700d0304504405411940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 859252661 1250 859251411 859251427
    0x7052104050102040302041a0a050f0d0506010b030915040308040b060f03030307020606030613261905070c0603020304020f0d15090302102a1d0d0602030720100e0102 73
    0x1805550694080e9116900401d0502c00d42c40c0c03d11511400c41c504800000403004018042020382c03009110b642d1040c030219420f803070309468a581c2c1ca82c80726842801c1d0388096842d202c810310950801e403442c2150307200c0c4640c551601140510101d0140f84c05843d202a10381c1d62b0b50f26030903c5000242400e812000c02c2c2d90211890f20304001a5000341d82c1900a4516403806109152929100a00c081200d500a10b101400710311224015914141140d1100c2d00408007a10700240380e200d4007040380b03040c00c0d1400700c01001c5030740400607180152103103000307980e41c81e40c40d0301c21000da01041c0c5001e5480285c0c2c1c41c0f0f07141d040c50520000900c0a2180d42140042e0b0132a4401100301c60f000700058001d43c0010448403042c05a5210b801003448050030010f100070344c4008400305010307068543c5014400852021200c0c1005010708054a520040c415101c50801c1c2c03030040081e40054a100380802c071450300706000b19828402482b103d00b4528028070050f43c6a4090740007420300c2d0003901d91255800c01c1620 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 859253911 1250 859252661 859252717
    0x2100c1806020303180c0d0204020903010b0d0c08060f010f050f010309021c0c0906030305030c0304050a0203070f0915051c06111207021209030a2a08061603140705 72
    0x10010901c0340c014644130325001c00701d02c0702c02c19a0220074040d6048062507203003540c0c403240c4078544290140d50041c3c8034210301700032074010540c52001580c00200000708204000c10b001c08d42040e0b03041c2070300341c4849032034074215462000020300480e07244080210703040c041420000074196160740145000f244840c0c050700440e02c40541c1c4410003d0200010300080140200742c2c8540005001100041000c1e618540340140300d404054252104c0b54000400702d400d011042103402909038008082d12041c40d90380079149180c0e5510f1042c080010b01700700e96412240040c6035800704560b409014080d10002c1400510b80c492043c07a422110640e9600400301e03d0942c101c0640402d054424156055013071502c0044c0c901b03040d0868294080000f0041d815142c3c41c0400e00501003a0b125410394095207003072a803c5861040c002c816100218081d4000969001c00515980107080c144100080e103004100218180c84503c5900c03034000d916440400c0303005100d280104040444000041760020b0960300740 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 859255161 1250 859253911 859253957
    0x306030a1401050703110705030a0c020607151505010804020f12010212090703030806090c1603030204080f2a030a120c0210080a060501170420060d05010317030702100c 74
    0x5281603030f64034010040c9075a010710481b8000018080e04a04203501e070340e5880d95921400100c0e00400c403400351500704648074035050350400d50384a601d00c0d844c210f80c0300481000f081088288108521403100c00100e40d4000c140180c025600a0000b42c000600107040c0440c0e00c01d0200c880c0300070365003008912510700d0b907400058022008400a01041451802e0050014001408540c80381c041d500c01d20038204003180484110200b0084055010003603070500390000d0050354045084d0b4003030f202410804c0c06001c911200c0b8000d003c8056007110f007100f100c600c80c243d0300080064040d030000410201080d03e81180c1e82c6092100d1034260705006542c0e0201e480704d0f0321a2101d0000c40e0003c41801000142030241c5d00160800386400c0000c040e0752901d025807000064800790080150480f2420104071104200c2c00101000d89282d603100202e800e180003c2c0403d02c02030b0749042c1c0e0300301040b4075206e15030b040301d0180086038001c14078800329076078481c01080250344c00814061100c0c10303804000c1c82c034106 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 859256411 1250 859255161 859255193
    0xb10051f09082e0c0f0c05031603051c200306030a02030a1406011406180310020f09130c0504300804060f230717030c03040210030605150306030a 64
    0x1102c90820310f02007103002c031507503180500c3c01c1c03a030030825a409200c4e402aa075070007440d0b840c501001405c04504225066100b40c614955000490080304d90074550000010104042c0b40c4021b0a01d040058610b0000c4404034416000c1c5070840c0e0000c402140d500070051504050020180c4481c9945603000038500f075200e280c01c42e0007080c40d20803001b500d84288000c9004000d05030300404403510070741c00152503100f0114100d40d46142c422120740107403010007441110145c00300c0115901c200540861005801a0f8800381c4540d0807403a1a0443d404280170740101c908a1744c480314101f606040b6104448200003a04400c9c0c07234413940f495143c1d078040c0f508020140c2d010355000c581d00e60500f200149038215002100f4240107640311010b82d403c3d014a01765044402c0800c845032586143e01d0505002d000f98695086010408004d0050550b203a500440c001ca100b1103280300e0001c82d4403c01d42c1a11000e1107001e90259880740a20920005a0003d50340003800900361386420321180d58407803041c0c50b4411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 859257661 1250 859256411 859256443
    0x20d1a030601080705240d060b1803151303020307080a050912150411030c1e010905010c050c09060105070212210f1b01091401090b10051f0908 63
    0x158002400d041c80028050519540600540d608140204040c1e00007050510110704080122448203500340d0291603079035944034000c1c020076594019800c0903070441d00701645403400e05040031902c0c1c41c000440c85141004001c511000f0f40d01c904030642151000d21007582540800c001504c00280314400034443c0311302c40c0c2c44180d22110a01d05110381d0070348076461002c2d26031001c1340759400080c25a0800364070641c403481415401100c040403d082070369042132503400204603103098100d00401c28884212003020780e10074030003550f9400111440202c0f5100a400c1c0c0d0046001c2c4c1c8040d007003101640b64800c4041c1401403400415030302081c01c0d0345005003c0e043c0d61f0001394200114512490300c24103a103407486410f904054060343e46504602c9179802c050070411042c2c01c034580b000001c0d0060485c03030f034000400880c2c5a4101d14228060620150101e854011082c00140e040016054150030b5500141080b88450044502c01e481c030303c000c100c0e90f4140030001600103500e0500300002c1603c04c001031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 859258911 1250 859257661 859257701
    0xa0309030c06050313060f06081005040b0622020c0a0206030108030706060503030a0f030504170a12270b130209070c050c0604060804031202130e06031507120f020d 72
    0x2080c05107150038150003100412500300180000f0501007405200e40030f4200c80c00084840507009070b240101880d40c002c00d16401201030840d4000755a030f1043c0e100d83d00030340c00c031305456841d10100601c00c9030503148043c11103c00716900b60454a04da004c0c04988100c0c0e800c868450200e0b03000510140c0090344032a6250b440015030504106950003621f009103c25001927080ca0621140609039141000b2844101607842001400740415610b044410340d0081d50155aa0500c0b0071004100716152003c2030b00c0d003401c01c241c02100c602c07102c3c2802161030f260700e40c440c2d2490069995103245030000d468000c10240d4005080c0150b0764030440c85008043c40c1d02c40901c4e81c0e21518009040c4410000d002b0b03c666024401040600c0e003000b4290344c050781c941f42011030000004250002801010000c1d1800c20305c600010840940d00070312980108011001c403100052102d030503032480740c0200c907440c0c00102101e0404020090701e0b0407040c196940e5142c05401d108a810f09071049620800d10501d01d400d00d6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 859260161 1250 859258911 859258913
    0x328150c2c06030a24060905040b0301020f0d02090925030b06070507081b0a0305030d0c180306050118051005010f02100519142203200d0f0306060912030309050a030903 74
    0x40050400f0700a110702d001988540b0741b10000d020705c1500c2c03003110700480e02c403035011000303a500b941107800b001c0b40c0020503620740b418079269000035004141ca080c0100a0b48010031f62403030308500b4000e90801a04401d000d807204946084010b800307501c1c1c000e50009402c2c80607500040e03050048001038400080244150510b104002c00d40f0320007411518010400940103201081c1c001c0b046442c10601c202d40070845410504049030225104100000380c00a415000300c20021560040340c1280d0094003002c0005000c0d1009104590302a1100300c24482e24040401c401c0d40901a4000300e800300e801030700c4031400030603224026210203c3c1c02c52038800001d04885103078009417003041e0202e408004a40c82628040c1c95044210000c5d9541d800d1200320400c090040520035010740c20118a907141596880c0f221094850340c40007007510302000f080010205511161191145030102e80d542e40c0d131a101203240c102d1101f00440c10b460140d04064680c0c81e03134000704808005070081107111365141008940f41d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 859261411 1250 859260161 859260191
    0xe030d1701090e0703060203100e130b0a020313022803051606020c01080a050c0f0a0f02101a0d0602040306020f070309080d0e0405060328150c2c06030a 67
    0x8160000078000b0310f0030400b001032281c0042c490303081c1c030f600c1100140e6a4407105d00c0b08541030040e034010040a9503150070004101c800c0041030800b5481071135141610344603022841c059010445d6050b031840309601c440c1001d0301c3c2039020150045102044000c00c0980f002800e03441c007145400c20744080d8410304101c49216240c818613001014540301400022007a000000c1900310b0140c00214510b0703c40000c122000080c0703040300c0300000340c50348442c0e640c8050900681000010240b501c094046d03107020130300d00c80d160300820041c03060100c6005511180d4200300070743c01c401c0c00340a6618650078000400014031310310003081e903a4003a0b821103442e0800c51900521410300c41c0c21148850708501c42030782d00140c001703a003000c4260085a010a2980e95480400e1a0801800c14080307000d0b40d0b0f080c42403005510142601600d4081d06442121241102d2034000b03985180d405140000c410b85a16142000b5201c0c032400300121016205180d6040040050001d030026200e9030600f81e0344689160388890303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 859262661 1250 859261411 859261457
    0xf10120e071a0406210e0312040302210307110a1b0510140904021c050f15040501030c090b0d0b0c03070f1106060609060702040204031a07110d030209010e030d 70
    0x122002d4602402c0c00f00083c055a5510b90001980b03116403000b0300c001d602500450081883c03441201d4070740000803040c5142c0c0105a4094015000381c04410410004988410f5040c0341031620f06451515a0007045482e070075601018611805006643c20010350b078032015aa40d0140c6032424002281403d0400c244009030480c00014407001e83c54000101c21024250740c01c1420031100140c541c88200c208600c9000050900da515500c1c140030800d10030000003e0364000c119091110300c031040d9000500040710070038040074014201300c0c0401c115480198205218420002d0302014100e541c2c0c0c0c1c2c42c00d519850036104100060000700812854550141c2c4500b0440c2c0d0a142a22200750311040154031070002074112805110001181c034000d840b4001191103056000d00115665560b0341030002c02034031000b0000070140303040000300fa507003403203003555000410804014145804a6910643c000d6000304103e505000e1428060100e694052101d8081c00807941c480c00d07000d880182070508044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 859263911 1250 859262661 859262699
    0x6120c0c01230f061f12050a06050a090203131217060103060e0402102109020301060e39040602010e01060f06050406080a110301080a060501090204050f10120e07 71
    0x94444050200804103800c100ba00708692030f0a00c0f00e180c403036001195003900070070005418a140040d0400d951a40518003031501031100504100546400c0314040c1602c000c1e00c0384940c4942c0d151014059000c180d402503401900162115002d500c0950710b0003506d00d550b09000001c52000c80440e851a102040c80540c401024682008000d0401c03054000011019002034010110110119100d0b03001e10611509483c1d041107200d214203c01881802030424204200e0081d4205400010851140f1400500901d100c9944181c10803103180d0450503030718003000707001d54400052042600c03903400d04010005003065600118101181c161450300399552940810b28000c2d010600304043e6601109840540307403985424a5241ca928a1510140c440420320007070902c0004000a28584005044010b071b620626060ac101d82e0380c0c0d00c02c2d808034003844c400ca43e007022a07145c203003445207400103448020240e81d0070803000366400588600100c41002510451941c4015414842d401c180482c2c05603036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 859265161 1250 859263911 859263941
    0x1a1b19030801140a09020c0c0a0f080708010c050a180306022a0609031911060c03040c060f0207060e120106090b030c060405130c021f27031d06120c0c01 67
    0x20388450004903108604170f124a0078816400305100441040612025502c05802001641565100c0d145031240340854850f901d264880c41000041200e41801541903009083c4c403124140070b0181001c2e1413460b900c51407000c040c207000d10080000307003ca1000c0c10b0740e40f99840c000c41e6400520041440710045440e180c0d50f055101004204100704000111001842801c00107a1030294003c4292282100442c1180680c010744080011035000c0201561040f40507514415209a5412068414803503e01e42100181c000e400207000c0b550140f14a00e030b0340301005e0007210702014038070032090031190035421044c0c0705da0303c605488085107420070500940b400300303c0d1220b140600d000d00203000c042c040c00054a003d80c075850180780d110300074003405603140008542241887e01c01c0ba0407400401a1320440c0310541100108182e9a045c1c800920503c203625881c1c01c1100d5400c50000d404180040c0b1105034003002c10011500480c10409481d40035800b800059900c1d4481000840c2c00d54040c00d5a580720303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 859266411 1250 859265161 859265189
    0x522020d21141c0f020f1c0c050a022d030a0f18081506030102040308070b0a1407020613060e0708150903250203070e041214041a1b19030801 62
    0x3e1107046a02c541c0d81c40b400002181c80040c26808081c1c02642c4404040034400710302c845c4540c9966482c425044102d0504210202c014003065401d8040d200d0f1000040e40080341c045489403010704c2200a00002d11642e58a400c00d41110910b141e01c0b105400b40002c903c500482d003050381280501c46c1400300c0c5c0703072001401e03420b0030400c80e503405a140d50f4080b012002404101152003c0d41201d02468100144660740c140a080c020540c0c40140c40c100c030000d0de0061050400f202460b603881c060545603000e00521f0b2180f50303580018071030341c40c0d054403080e179150619031030102c04018240c02408100050480786125442c5400c50650050100c00c03160410030800309898242c451902d021110a0048000c030002070001c40c4c03030305480f60810701d80e100c1040148003d00c0012440e0042c0e500c038564806801d00640c007841d60080c01a4414201d0580e035220000c41000900d0b000b810b09004100250117554002c14016031600001c8031041041120024030354042c5940a24441c0c05400590b0024407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 859267661 1250 859266411 859266427
    0x90f0209091209091e0c040e0f01120f020f09090c01081501081b0f0403080711010306080d0f170127020702011d06090a080708010f0522020d2114 64
    0x31030f1003211105449030081000040e918200c654110048a04104201090345403100040520754813500a0710943c0d5100400240401c83c0c51311424162012030400d81038001d060707551480407588805049900503c116100040c903294015005d200b55900c0004001c2c941c3c10b03400140c848040605170b00482d4009503051a00da0340c20140c0c0c55002003039483ca8038600561042c0080d00b500407841000c07205a000140001403184100240003164020880007654040300c074015001c0303806601c02c1130201d8202415200d03029005603900313040d440090030b15000815140c45075455071b00c000d0700510103070042018103040c0581e164080c2e00b80c007111032034218035228407600045c140e90f1002d5140241201c88528155443e02c404054840700e1501805a0860a8440c002c041d1034070418024603489610740345080f41c064525015090243c14211110420b000c2d140510040a0180090503030f008446003400364001240201c0c038284e4000040d4214440c021010001055440c00a5125501c1002407000301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 859268911 1250 859267661 859267693
    0x50406050a0e0309100c0f0803190f0209100e03070503150405010e0a08121806310201140702011e08160c03023004080a0c0902120115020a0204090f020909 68
    0x1110580950411503240d06e104c1c5031110b05a0a07881d0b008200700360210a1240988000307444076000000300409010044075841c0c50003c900412401031f6010124041ea00a940d0151001403004900075096500242c1c85002091a005441e0052921490098104014842e0a12811458000d05800341400301c000340c4030782c04540201070301e10700f440d0000008550140440130031480f003002c15409650a9182032900301d8641c0d4940d1034680b5070741c074182c00503207003001c0a28030003800290305844002030b01600762062240d6170070a10040b41403001c010120100d13503880300c1421144984603521302e0b000345084042886440700c000c1c240d0051158920760b210002707801080074040e40e2900209a0017145041e00d0001a1100048070812600700000d004a040e40c40400c0001d4664066404452516a20341c0302904030300c61228030665128a2000500c582100825034001040071441125040c12041d00050304072007220780d0860303040301d8a0945004500b00001e040d5484086507000d0042698544012 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 859270161 1250 859268911 859268929
    0x20f03070813060905030304060c0e0a1404090506010320030a1e21020318030615010807020c0414010303110d0801090c090b13180b1e01030f050406050a0e0309 70
    0x5441400030700c8000528504070030100840703441c1c0042c801d1000c05024202a0b4480e80300350380942d840c5040200201803075000f003010a82030400540318540b6144bc045880d50040c200c010903980c0162550380c601c010420401465000e103000320a081000c0750b400102050340d0a40703000d454040c0d000404404007050700c0c0c1524200c003041d000022040c034140b902d04094408001c0b0884110b88111403c0f0005596002014290b05010b0820b0154000600001c047d50703610101c0340440c18081d406e128050300d510440f195500030100780101c0d030325050030300d0008090324020750410110200000c010003d0507448850b00f000180c000024010584002c1c50007012460140507a0035031640700d1000f016003d124000550082074100602c07a1910506070544410350380604c100030800d582d00085041d420740c18030420a105000400c800030b01c444440118220180c005035242c1072558540d040c2140800d2030150030310882c031581c40001c0394a8580140c1d400c8440b100d01a03101c0390300a216100c89a00c0340ba5503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 859271411 1250 859270161 859270171
    0x1909081b060309011e0c02010c140a03020a091203031b08150906210106150203160b070306080f0a0b2802070203010b061b2103270a05031c020f03 64
    0x210035035036035a503c0c91901408840c100d0743c0381040710003410103094070341e039010030f800c02d040f680244023590000760100c8034641d03d51008052044200000d29105019500800c0700030200e0400c0341050b9a608402016000450b030142c022a856100b400d0241041c0c0d0071880014856050004050802e00c0100d803454444299007400707560000301017108d9540e02001030a4201080418200201500708070700e01908451080f03004031142e042c80b01c50800d0000c01139a051240c40500d00d44229099103c4601c01d40740070380203c051595825000c14070034414410005420034900061021301c07040d280003410000001c02c4425146103181140d0340e0b251440c0c50000d00e0798004000513031222071500001c2c0c0140307069080d5660041c0000f840001c510305400e16103200602200a850503c902c80c0c070044000070140d41d481c3c21604040000400e096030700e801c0300c280c51240d845155940b141104590b0324019481c0e40665180e8404103220192900302d8258241d0102403010550400c800065031451501010306 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 859272661 1250 859271411 859271419
    0x51303030e0f01020f0c0606010c02060a0503150a17120a05070303050c040b03040b0906070212091e030d031a030304050d0210030e0604030804110d0b01060f0507081909081b 76
    0x800c000d8040802c0203803601e19480e010085551340c540c261240035030b44c42100080d0030340c02001c0008110350b0050f848072404540181c03413103290104404bc101e4865000920714080382da42c40b09152510303204c2404140150162107205405000900340e000e1802c060411441040c000c00c0044101035540b00b01035841665050401080b0f5840e0011070401c14001d68001d90032230300c40881004148030121a2141c017a07020340c01965481e07100e04004a850785c0c060034280040c2c030030030810b042840c18003030b0b6850454070211401454005043c2e00180c142010301c800c200c0020344551072088010f00e0b00070098110201100114035091409000c608103940100c00039101d18014015848001d00a402c030741c452080c40e00a49405140c940b40241810381c050700c054405102c182c50a5034641413801211800d5504a03c00500682c6000c004450740d00d1450880c1c0c041001c14040000058000c501501407400e0b13100801210504a4500070440452070303001c201998055507400c51214066107445814010641d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 859273911 1250 859272661 859272671
    0x6060e010c0c0902070503120901050c040e04030e03011d151003081e041e090509120c0a0506090a1a04030509060703030e0f1e031e0901110d080702070905130303 71
    0x810b003019000525030101d000c181c000543d01d010010040000d01c164004800c00454903103034000c542d0b00f01c0f03900b242c07e25250a0200001e0100c1c1c400c044403e58010300c00c1c60076040550b81c4501180c2500c44100c0a00b181c0c803603450760b02410034024406410b812818219400d154940607003090b0071264540301c007403d000c1c0002003035240301904100800803044d2541955507240da0741c98450707074000080c491490413050030007400304a54429014050103803030000001c10070407407104040c0e106a07100d02c2c0c050701c40d03100d5210f142001039800d0004911803103006002d090a0140c90900480044050301070702e04070540f2400300b200081d0440151a0080b8055603020303140e2001d440d05500820901c01110628420a40f05204aa500080113840035440e04848205900c1000301c1e50354070300415000e1030460700303519840c02c44803c454025050b41c1205142c844400700841c1c43d01410a9504422500000c440b60f04100c10b05030100f11450003406010020002d1f440d020a8801c0d1601568200404060b01d403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 859275161 1250 859273911 859273913
    0x6040b0417040303111204030f02130b0a18050606070f030e0a030c081b01020f070e0417030403020f0d3603060204060f0215010e0c070501061508040b0a06060e010c 72
    0x8601c070405070300300101419651502da0401602c44601480c04102d02d11961b030021203501c0c1400203840031240e00c000700c0c0d8000300e21079080240943c2103410040703681d07036280700315501555100850700091103881612415400503411101c25514010062401a503003041544002071800b22020030154141c42e000c10341c1c0d0402000a224055264000740a52404000c00f00344c1c0900800d401d560030556400b83c242c290f9100307006984410000c4541c40c1d05800c00002004440d072a043e0041d072041c81140250401c1501d1005042c07150020b0340c0c140c0059100102c1a000351208004580e0402001c1c00e00d4801d4041110f44548401340841e401c40011094100d2a1544241d03071856030091a4405000d640f41c42c0c65400c0207100110b040d1441d00188214111803000401e201949816201c10002002c215507403842040041d6004141c1100d25668442e80002d4035080399440f41c2450040765a8003299003040e040900040d000640411901450060104100740d0402105a041002800d180c0340440031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 859276411 1250 859275161 859275173
    0x609150201020d2a020c091807081504021503010b03072a030f0e04060b0d0b0312070b0609090d0c061a0306160f081506280305040b06100206040b04 65
    0x8598604044a04144c502180d0b0b10002c001840312440038001c00c40d080c07006400032a80c0c1d03440e8040c00c0360085074030004980030f41c0f9034640c1c6060501012044504496482c07e400d880d00348602482003a0914440c107000842c5015400408400d008a0741c80b4251750410448a05512000c0e011409100c901c403041c0c0b00b00031800c83c421500007090211088808030070f0401070030115251a01c0c1000842186141515190500c11002500d40189003217080038903ca0402d0300070104804880d602d8410307403220401c1280303440002c0034910b114181007069820701a09021700c811025021309500d4001e414080c81c0315600c089054003060300450041060842010840c000c44504c04416030540140d004000e01c20000c40b01034000042c00340d44035802140c07281012600450142c580040d4585117000d00f0403103251440183c921240507100520b03249401c000382154000d84c100818001c40d071604108014070044075800e5030b200c0801c0d0b50401c209510700318002e40b6040010070040a4660500c041401d1080b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 859277661 1250 859276411 859276417
    0x70f0b090d020d1a0f01121109092104050307090209030303070804021906030209120303040b0415060906060807090e0601021207111809010c1d010f020c03100606090f060915020102 79
    0x60000001106500c4030600c0200c0144119175858550400c50000980d209081852500350b60701320b00340c1a03448488404100ba01c24020748601514411040a601404c00d0515010400c0c1091078801e035640d8506400d141c00c0080a40c040d8504a01c14400d45d07204d61008000c03a0b0340110f580c6003890440e6203d10000780340c1c44c007012400310407844842001c80c00f15010740c01480d150000700c994500c1181c030b00b000c5070390b40c1c0310450700106694003020200b00080d001c03590448664800b2200800c059441c1c034001d800319400340d0300420002c1c51039810b00c000c0039004043c1d000545401c41c000c6c611864103100203941d4019440714050b9900700050041c5c280040b00240d1004400c0050000082c034288030440303158000300b0307122010654a401015101d07507010304180c01114071542d19191842440e44011b40d030b050720300304000082d80228801c020041c3e6041c030410094040d07900c2c00048150411000502c410380c4c80d0400303090503280342401e219181e0050850360459100703030b84541d611140020101d001e80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 859278911 1250 859277661 859277663
    0x908030d0605030c060405030d1409031c1b0c1707080706050a1103040f030204110909070203041502010e0a06022d03330103050901060e040c08070f0b090d020d 70
    0x4040400d04000c040c10365007180c81261400c03000c480c100d19034041049080c1c031aa10a0a50540c08840250b19043c0200c1c000e50384040640c400c241801c000b40c001c00d0400c00d0941e050240000c1002540340e0035500700f401404049203503e149400000240e030348241506650040c841d40c0b003d612003114200e00104404005003450301c0076207600503669a0080c050303403c48003200c004510710341d0780d0311010800003050710200c0b01c05160f00280ca0b0700c2c540900005020003543d0b80301150040240701c00f1501c881764854019034042d401180d440c2e2404000d906107818480c8010700716410304500030300009000071034007140c1e0b4021000580d22914170607071700400000025440c4040d144405108444540540914030034070051980300c44600440c2a4a00750001e001901c80c01c4002c2c1c50b15010039540b080d80320766480f800b00340001500a8452100100140c4c040720101d9941921b0001401001006e0242d0001000d244025507405030826022035824002c1141441c001c0b900300d0990b505540c0c9d800d1210200ca = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 859280161 1250 859278911 859278913
    0x180418080d05011401021204090902210d020d020705010905090601210f06060e0d0f110a2c060d0602031005060313020306062403060301061d070f081b09010908 70
    0x1440d204142600904001d00c04c08001d000551400314070355002045041041c10f119068610301410603481c0002130043c3d0f03500740e82015140e400540e40c000c5840b44c0640c4d0300082c00c010712035101c070820300903d0150400c50030303011908075080801031a40c024030030708217440d01244c00681079030b90600104ca00703811002480c1e08401d200c850300000903956030311900100c005c0003c14000305031110b1066443c101d084881e1600700060484c0e08001c0341c0d01003c10003a1a102d00844817140416100080788144950070001c4c0c07010b4081e030203ca480d00f400c1520000501c442641090903d4090005041803080c94005001d05400000140b4266080c011540140a000717290507141c0c01c04000502c00c03084a820700728002d104040c0821000e00d444500c00c5a03081402c00794142100d009001d008003500050311440e055902e800d404a007255480800c403c030010502c50000312490300650040c4041074080a59041c0b0150005000604070020292105400302043c05651083c1241c0100d5854044c0c2d404111070b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 859281411 1250 859280161 859280167
    0xa0b0a0207060c090807151d0d0b0a021c1515020309030607050d200412020f0301020a0816090501020a06020307230c0c0f1804080409062918041808 65
    0x15030044c041500b550500c07411501c0317164840811b1848940103000040204401500c0c1000c2c208000c5264240024040c0020088150a0b5a03682d000d560540e1444d00182d008290a00c2199100c904424201c0c403c00c818400d441d2810003401a09103d070040e0100380381c01e40c42d00b0b405140208101da43e13044c000347c102c403001d152450b0020020b4001d000c00800c10390501c18031003c074003d0208185140a04100328030701d8540b0300000c2c00490b08501000b2a00711182c1114800c15607028406080801d1450f01d8000162401e00c010440c003000c2c16000e04180a04035805200590b400108804102e5104400507625100d2880c01e890b110031449802d00010780004200c600c554514000c0c107010f8080b00100d9003e003090304108541d042c0303250310064100608460032480e480034000842d42003401040c1036880d05032699180340594a40780c00034080554a08610f100114505207201032140f03800d054036040178600c4443c03a00302e151405402d0311607a01c80100504100350540055841c039801070070346503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 859282661 1250 859281411 859281431
    0x6010c0b0f06010f02060702120a300e0708060114060d09060e0c040b010c020904060e0d0302070203060a05130f140a0309090506030601030f08030c1c02031005040e0a0b0a020706 78
    0x207103403004551a034005203000741c1d113091142c000101c16004d4903440d005004000081c5040b02980e070017083d55101042200701a0302503003100300c0c50880340005400300201503c1c4400000342c055540240148400340d2003001700308981100800d00c0340c156040755171000b00810034131000842500640d51008101403810b000c200400400ba030000880c50941e00c1902d420b11031460411007142d2086903036034041141080402c00501e440c50130386902c01c5c810440040c40d05031144140340341c80c80215a10740801d500041074410351404102e856400035142c18144418540030514030040c80001100405162444c540e503c00c1012030401c0040000c810000c540c0b0031004c1e1b007401410394405104841000303103003d001c0380042c180072940d28107aa82010341c601e0144013543d11540c050741700030300c032031724044e014801c01c00c052000c81820380090055240c09612420055441502c80b0820b901441c40349160550b800c840c0c0001160100c140380c0c2003040e54079641c2e20b103410031002e48184003004000524144901c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 859283911 1250 859282661 859282681
    0x4050703021224010501050901110f120304061a0a030f0311120d0608070302030616111006060e0405040210180509100608010812042309090715140a030506010c0b 71
    0x42000d0000010030f10710014803025041c010078010940081d070b04001d91401c0b54028139041d02a1299a0115070b110520410201c0c18001c0450300d00e8a0040e00200f80400e00ca8140a5950b00c00180c02031011040803600c0001c0e900717141071000500301c0070480c030501c042c90f000e60404e513010b660340e00030b4880302412441c070300f0031540c0a01001103a440c40c103540859002c400182075019a64050002c203016250003202900d0804c0040300c070340803c0815840c43e0320307581c0305018907a0804a50840440c006080020103021829440c0340c00b40190b1501c03040001503134035042d9200e10b403103d07420070001908c180301c00c1c4c03c0c200721a82c002c40d412035410028003942c000745551680031151113949407030703060362504038042e100d27800c0700300790542c03810180030502c20013484c038040300007504102000c1c0300c44494000101d03007601c00498030780704250403803034003003100000440f45000c0c00b82c11854482031200d030540e582e40d550300984030070008042d55540001d410b07034050301185000e6078001201409a19003c0c1d03d071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 859285161 1250 859283911 859283923
    0x3330c0322080301090222060f080708040f02100e12070806010f240c0f05010c0306060207030203060c0307020c0a030b1e130210050d020d05010f0e0f01060305040507030212 76
    0x103500d403111401c000741044a881180080c1550b803210486203164601102c1d000a90040c1c152907581406500c0c0c0e401d1481452003400740280603035200d000d0401614034010705501c3d002099903090120740c404000c0020381c00c400d151029541111880700f10282c05808941840d1079544a58105c1141326103040c48003c006411021240c1c1d44007100d1003680c80c0d0130982c9003a4414810038180300b42540b081c11060340790581082c1112660f15045170500c190b0b4942c1140d1044601c82917829175901c1c3d0995410396031500446000d00b0041c0000c01020b881c59000c030359501c0004080361001100800840e100e1b9100303000f031000034a40100300403075842d240c1c00c20700b40c40b8405481101040602142ea1103010782d580ca8540d10400000303074601003100e10f68090190814184002108000d0100007194101d182440581007886118200269640c1041d0090102c60350940212104181036002c0105642c68441d419042d00c145140108590b19245040c5281241b5030700003c1d0b0003c40c44130540b002140c00190703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 859286411 1250 859285161 859285171
    0x90305010501060509030703141204090203040212010b300616030513150209040f0216020f191205120f0a1206080d200d030606020d050903330c03 64
    0x204890b907690b203c20750301d41c412825203a405403c20306081011510202804054881c46000da41030307d058400c0903001640117810501c0100c0e4040103010a50508480448a600b1440020003006000c400020344121140103a2412113504503189404440b0b02d151604401340510121100c40c10107440c0303100000c58601f41100041c0c680400500c2c0d100c5100b05440102c4d4100c020f5145412200302094082c2d880300480380c3e0055200d8146045945161008141d08086140c841c00300704240c0c8100b148020696844911807403209038041741a0120340e201c00100d643e0408180c000358040d140a50a040c40e4400003c840f113008103c40009600301c00080c0b003000d0f0385039140b00780324095595000c11550280944006580300111406286020310003a4884120881c1c981c8000c41c280d204c5d45140000001104000940350001044035940400c03015080015a051903070501590301c000ca55103001100503000ca040d5003e030481d082144055072841da210625890144504d03100c180103d00d0b5100340c403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 859287661 1250 859286411 859286413
    0x3020601180b04020c060412020d140f1b0c1002120910021e0309090f1b0a14130e0c0408060601080604111204050d09080c0907050c0303010f050118080a060903050c0a03090305 77
    0x40140403c0e803010551405400ac5511031221a0381072081c1081c081c0c11045006014480c104451509190800c05001d240360a5100030f144103150031003401001d0030150f910105661009040c4640c2079059419900c45c54000d49804154801d03003401245443c0c522a501020301400c03559a0181200110042064400a8401c0d81c02911484c0c071900c01306808803800f0310018411141141c20280c030303000416100d021450300344441600e101410486510035402259241400c034020000c401c1c0d060030340b650010840a00608151038101002d840780e400030006030421840d8400100d00340e8580d400500c0041c040c104071901e0326030150240000708015241075910703106910000700390601c5038007060140c600b90b1028088003001c810600503104806000041445028000c4000413030080004c0e600a1440c0001d0b18001460000007400d038040710459080c60f81c21010040c04410000100c0300d80069119600103444842c40c141281c0c2801000c103000c40e1070081d00c075131074107040d8170580c142c003a640144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 859288911 1250 859287661 859287683
    0x30303061a0313032d2001090203070b0a0c06060305011d0f07120809090c1801030917090120010c140c06010314010603150e0d030903020601180b04020c0604 69
    0x81c1400845000c200d41c82c1526040044050002a100d440301d1403034540004145071180029003110f941500c1541034550019039059644420780c041540111a41001070008201008458003c01d4a44415014080c003040000807010a1076101d503242c080c998ce0040000c028031703503c92800c00e01038040f001400401300750302c000544bc07040d0702084882c0c05c1d01e049401020402d14060001009030981c080c16103010340f040c806400320b922480034041c0308880030704030715607601400195568060102c80b00315040505e040f80440024201e10310184084208003140782d16480940300480720510a684503900068030140c403100040d105402911000d222070b120186e60140f0040c44a07494002c0200300c002c1540041c0040002c9400000f40022103500742c00045065034480c2c81d1220610346901c0002209035032522303c80740c064800c1c00f0390000918185800d01069106440007562036106000d1003501102814040081441030340c001d070782e8004042c000b99199044010010346480e1f080301c7c00c0d26001100703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 859290161 1250 859288911 859288949
    0x15020412061401051c05010912031506050f030406050c071a0603070909081204080f0c0c0a080a030206010b090f031b0f0303030f070503070e04180203011b0504090905031303030306 79
    0x1160b0418142c50010b400181e52040d04460b46806180c2034100759442d56036480100b000c00c0310100e001c441c9250584010420141035056245108090350000c07042100c2440304000c8411035204072600325420a40c08111619200d161722618030400000624401d61035a1320244481d03184103052050302c00f182070318042681d0340560401c1e0f030060b001c000e003001401c002200346540c0240c01e0b150014050926541010242c04010003264442c58200c8001d5100c1407007a4043d14100d5a01406081031401078159043c00b540c01031354442c0c060254003480300c030105070308249440d1032112000e0000e0003000c80f5800c0c903207100321010501c0c0d01c0d024075004400c3d43c0c3c1650b41c10f00f4004201d03030140814000e0b03021190703104030040307519070406001c40c0104100e0303618803e059030300c5000e6071031841115240000c2141a47c4105800c5420706c03500c00e280140803280d0000b409401505803021200b41050128403003400b85401ca00318400c0d0b045087c2c20300034070400031040c980d040d030040050329204003205200040c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 859291411 1250 859290161 859290191
    0x70905060408070909080708040f030606060c03020607031e090c0512010912050f04050402030124080115111005012306070804092a050d05062b1502041206 68
    0x1d500445038503074022001082640115842141c129003d107040e0340c20124aa81d0300e40350790344103034801c2280313480107013080c0700303204182c818a0000e000b942404011150320340d502035187c2c2c1004101105040d038501340e510300a80400398035050a0070901081203c1c009601d04006821558090640600c55082002020480510814413102d810000301c0e51203424440d002c45039544405005504903100b07020004043c0c840d4000b0307601801c503080b451481c1c00d01425003222007141045149040003050700041042c40d1120214455000c0145030403020a0904c14000d860030301d600780266040c0d894280001000f0fa0b007075403201034800301c40e910030180c5030b4107900300b103458001d101c4081c1c68618100410090952a0b900a80b00320300442c610020710101511441e9403060040303282d2000c50300014802c90200154402c00e50b000e10f0480e0b960541090101e054800b980c2c42c05840941503241101c580e050010080021444403c4618259641e0340c8881d1a95078600b695a0100c3d04141032403c0690301b110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 859292661 1250 859291411 859291417
    0x9031202010212131a090c040f092603010902070206071208040308010b0a0806040506041503050d12060f060e030307060c0e0a090b09060103240e012408070818030d0507090506 77
    0xa08054444200e074a030201041c1d44400c0540250454468580341a07c19100c070f01540c2d058030612440040d04124a007040d100807581c012900320540003203003003911903246030800da0b815111201401601c483d0300e071000ca00e25204100c000380c4144900c40030080915402586644198030a5403403070b1240c0d903154030582031f038060403a01d0320202e10280d0002c0d02a05050740001c3e408900100086114640325500464082c02508207540681250840c0000c0540154401004001d10102001403920f00052210b620345c01d400349000700301410046502d151340400595060b15002070040000c0d40313120601031302402c40941e03d00c1c040c2811440c00039490040d4484c0e12140c030b80260000a10b99034a6004500904090103d0404c02140b8807905180c502010410009003e074030103c2c90031075042c0081404480750340c03030f000003c01c602c10f400d251f8156401901690003c125051980305602d035442d00c1b245040c404101a880e5104c080780c0742c5c031445d040341c0189001704910b4031181009901e5005101041c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 859293911 1250 859292661 859292663
    0xf2a08070212130609060810030605041713050109051c08090604030c0e0109050c07031b06060f060503010f1403030a0309230d4e0606050a0206060418080306010903120201021213 78
    0x2040e165230410100c1c400741c10480c0c2c007520854400e40c110b4060b140c41c2e640c82e04800c148084440c104042071102e03507000411034001d82000c8802d0001254200410441040001c00017000d484010410403a161100380a48000d9075100e0403405400c0c1d114044d80c1c1c441c600900c191222541800045491b08622800f200c2c100d40d0180d48804013043d01d036404207007003407483c1c074225169503a8501c0042c14010b198034231805006596501c95032549440480d0210030102e4009640107002c01400203061b41d000030441d10010400e003070118240c5841d0400c4d41e1700102c0350040c00025111140d4203102803c001c2480d031488850340d01c0e984d0420352000c07218a5a40c12144039007c0441502482021881050140d024030790312141041300b0400306103c0c0030065a15580c0001d001c5035020404000043e01400910380c442d10680b801c2010750344038083c40c2d2124484810141c458200000491100d034810a00c482c0516040001d0101032801410001e000351b10905003001c9903000c0b4030100e03252140044802c0025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 859295161 1250 859293911 859293931
    0x923070c0f080307171513050903041a09031504140a020609060c0c190e16080606070f05011401091a09270d02010f2a080702121306090608 61
    0x4652142d40c0c05106520103044034042c0090740701e0703540705440161519482070060a800c0880d911144040c0581d0724106808244000c2c1004200848441e0000a0f0b40442d6000c0c5400109842004006006071203088605034042c0500d40c00005941225200203000b107105408a4005180700341c4841e031580851031000754404810003402d501c51500b10f002c1c042d000c040300295040b4140500004510070034007103c908200c07035656000c100b0101d1f800780d500c1c0d00400b5141c04000e400d500040051150a004102d28803c181c085121414450f11003650340300e065019000f00500a400307018241c48010074803502100034203001c07402441b000700c0100403e40d9100070b08054900d484039264440086442c1114511058400c1c3e100040d0300300800c0722200c0c68041d0b400020702543c01c070980c81c1c16a07104481c00402821080341b420b0f51a9a10345220414500310b1034204060344950804030304080305206440c40c511400b155403080c0701d0b645803801088070601d886921100740d86090a880e481e0b021545200c80e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 859296411 1250 859295161 859295183
    0x6130902011202091201090b04030806010f080105010f210b1e2b0c120c0f0803030703050a020c010c0216060305010b07080c1c08150f0a0b0c070923070c 67
    0x4000640213007111003402400c40076108004441c080c05c50301c0b681300036a00c05000c00240010b06d60002e81e0305820140c00e2038a03100480303500d00082d0001c941031081d14100701c800900405803c3c0701c4c0d0001d010701201ca00c200b02d2986114a0303290f01901201d83c20512a2440c005500c0c0d034004003101d075500d03414011b8100310b005503041048000c0310b0300f51030130740d04078404004950000482c0d828802000e8400454014076805c00786c102030001c211550000d218014481000340044d010010035203510248500d004116503030b5a031301600c0a03018008000c0b005608041c0d405041c55004284160b800407030800e01300d070782507444070100c050364002c0c854000e222030304000c0407012032000b030700501034010f0741412950100e59003910000302c08071a003d0380001801140600c10089a101404401410102d0b5200745508011002030368450f81c920071b11030b40721000911111421003c0c800e444c010b04d14428100032a50303038154202c4086154940d16601c0c428580001402c40d40500080c0307031030351380151035148 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 859297661 1250 859296411 859296437
    0x91f020a0b091f1d010c02060f010b130b031021050f0312011a0c06011202030105090a0308060d0204150b13090203130b040218090f1911041d060109050613090201 71
    0x10000714503480010f441403110120618402d000707104102485031f004010501d4075010302c0880e0203041c2c00442c00b45504000304070780c0001009108090b40c040003c0e045d56611041c403181c0040502364402c000b6008003500d0b204c01604d80c04050b42605000d035050303510124240b8a626224413038110300c00c108030010001408041c22290000092030440303140d1600d40800c60450344d160010980c482010208005203410860800780140c41d00300e4880c40041400210381d941c060319015005281ca03005401940302c034003e55690341c000c010703120510303203104c031141e5210111028a030780a25120760216081840c00100c881072403080740d2083d2000c08411005405039516034454260140041e070340103c0d0000c0241c4203004646184e400340b2544c0004107060b81092030103a05080300b40c0d004802e8030204401840102c1c004000101130650125030000329289000d03000084492202c0c0303180824806c0b01c2c004103054205074840c1d40600d00803150008102d203032010090554001450080c0020540d045400d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 859298911 1250 859297661 859297723
    0x190e1501020f01020301181407020a080306031204090b10080403050403080304033b010212042606130204200d1d1207020a0f0515091f020a0b09 63
    0x210510105205990108600a00302c030b0036a042a04001c4100d40b0b41101d2a400b60307980d2103504012884018485110700c1c0503800031f9203400c42e810f4082d08403000000020a5980c0501040a005181000a40e20b41e40c8905400000b403419105d0075024015294030071045e20300612001340b0856055642500d094116694104686c002070011424001c00c001440645034030844480814442c400c80300c03100380c01442c8500005e00718141e0040c19034200b104070503202c2450340700f00c500395103219130400c0408001110004010140c00c4611045000700d00c01c3c0030354220411094911503000312014080c29040702e00290905500c203504c116500410050171100c2662600070040304212071f10540d03450307004048942d040810300c00381d958103100c00141c001c1c00c5103082d0748910f001c1c090482400c0c01c801e04200c042a00c00020f04140006408049800380c0340707a0b650004806009030190780101c00c1e41c0000000fa56600307005000b181c1200441c00012080540000d558007458880004580c00044a039a18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 859300161 1250 859298911 859298941
    0xc0215031027050711060c040b091504030f29012102010c14250609031515030b0708060d020310110408122208121804060e06190e 57
    0x5070854142c41d1070030001c10301c0e0902c2094402c1d8110f807100c40c4040a4400443c0c00c1c200010f00001101005001c1030100a4070203040c0e40b070b044403d0342c2ca80c203064080254110280200ea00c010f1010f090540c4207020446809101c901040f8071561544580105400b01c910170f150901855280c900031809000d680155a407081c82c80300c1c01810201484102500d6284851018000c45142c9500050f9410b00c9031003ca03081c51140c0d110403100c20081c0e07092401c010040082480054240c440c002c4c100c0b00c940c1001e42c400071001103841040890701e5038034903140c0300074001190900041030100c2d00260f01070070079002d60408070b40e000340030741408000c400c02e1600410307190300c203103040340010702c804500d440c010064541500c41d211502c0784c5a0480c4400e40c10140300342c4d410402c841c0c180c03000400c90114001801034a101c0950f0801c0e444000380040d4020014500e04110ba0207130a203040069024548007842d0300410b0203840c8842140210030310a4117810711480341007004000040020601a609400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 859301411 1250 859300161 859300199
    0x51c1101060e070e2403100501090b030a2304030e0a0b1303080d0605091e0105011e050915071208070c0203070506071a0411130e0d1805030a030c02150310 68
    0x1d94031544c5d002d11100444c40c9001d040d48884003c00818010007080d0040303d07200801091a05800503400c25003058080c1c000900b103811142d0712401d44a04011400e001c00000701925048100030703281a00b0020309a1040100e8540560340024003c1483d242100407103000070342201c481c004032840c642c0c411525900011480f5042c40d84c405e00483d07595241030302c55009030140f244400304859a02d82e50644901b040c0e0146050000d200321800c05551288810500c41e00c00c1d040c80703625244d07040085aa0f803a10011810840c1c0800504241040444844616406d40079910a50503640d0790710160f45607400d068001c1c2d0b050340041c0e001c200a24200c0c00500301e45100e2007140403070302c000c1049895110010765040301c0c2c500318034404503ca82801601e002c881c040180090111007401014541c50b50418070405040011400e1072010810a0b414264001e000c04cd0454140c41c0140c100101101d000758412845140030001600305080742c0400c1e640105003203007110544600d8011159454079031004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 859302661 1250 859301411 859301419
    0x30c2315090307030b0105100f020a080705070f061806020303070c0b09010908030c0c15060f1908160618140607170310060206090f0c0d020409051c1101060e070e 71
    0xa44007035803001d10810008511a00400c1029410f040170068101c00101c2040c0070030003000000b0b52040d80c002048980250011111680d8082d9414081e0030054141c120350104001d0748030008106501010b504c0031850340c4469402d4064803408226120f21007a03400720002010303a903407040403130000300050303800056140000401e002e040d529a141d5801c1268008880c403c0441d2015804009102d4251054a0031145c5007051512100044006400c40e0070b09000b2043d01142c4e031036511a020300070014064900c102e8006000d9a00c0c0740c0040c210300d008140014819501c000445059076808505490321703026024a154000c4040c0880313600b0008040e2000d034a00d80300c0e45910700d4060001c50180f002042c0e41148181000000b0307107490703800340c00c5214542c0207100d40800d001000c2004294060126920300b0711248600029010b0903603503a01601d0f6019520f07800c082c2503000c08050f02007402a403128003480b14042981c900301d49042c0f0a0040c4032000350001107080744180c00501040c04014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 859303911 1250 859302661 859302667
    0x3040501110705280b070f1112160501030e0c06030a05101d04031403040c06260a0902030d0206010305060c0d0f150608060607030c080904061707030c2315 68
    0x20002e0000051030704800342c00740100113880701440c907403d02c0304040d08180b0690303440c0191558901407801c11548025214200000d00720301103943d200350480c0380740c03540b04c201d8400103210202d4840c410031a00c1080c0c00320703180000c110000f29000c641d401580c0401072026082d03955249526014010007000c0505c500701055001ca01b03500c41c071061941881c7e00c8800005a442c151074042d115034007000c00c01411301024020000090301e1850b0030710642c2d003503207428120101520241c0d8084895050b181040c103440404020b80000541d101e0074416008808a505c42c850488090381c4840081c000039103641c100c100000c0391840000c0003003102c00286540054005004003611080365600700165120001d070b003030100700c1194003459140c0c2210084956600d4454a9078019002c849404c000402c980e80206110303403507a80d168020402048005900350130401d00641c495180c40e000e0104462004d070540001c43c580c0e000038020511803c0504242c11030301101c5080162000d80201e420038221010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 859305161 1250 859303911 859303919
    0x501020a060c18080604031b0203030a2304080312130f17041802120702010e033103050a061109010801170109050706030b0f0402071a041106030708060f030f030405011107 75
    0x10120f10041c5140809014181460b20740145180340c046000600b802c140f41c0f19801596000c01102c480008a0034031074076126803000c0c00003810140d1503076880761010101d400902507002000070700d0340e102e07400c114a140d5500d210340391b9003000720014050425040010000300240001074003260a01c51b040c901404c107a41d079070001000d080c032004444e5a1a4003c2001e03903038015848141904002c05000a00c48022406140c030350b6405005086400d00c650b010180d402c000100c00c20300d502143c18401418540d4590600076540c0d0010300003154903518040240d0f40d844070741e5003617130b0103028160346a4040364600a159030390104d0808000d400e5541e920855030004008001c6a0018025a00c0118240048030200410405504011800b59004201403000502d2482240790035100120a116160711581000c085c200e5600c0c014503040000041400801c640043e4001d1241108640c01d540d60303003541041c591507600d58218405d8943c014481441550b001d00c00c11403d001c038600494a03401d5403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 859306411 1250 859305161 859305197
    0x3040b0c0412140c0a030201050a031d1608070b030c0901030902030c04090506091905030405011107030501020304030c1e0c18020d1103100b04080d180509100f050a0501020a060c 78
    0x1e5242c04907080801c9600001051a0501003000d180e082160440c10311407a58001815601c10444404d0070145c0e0380000c0042001821000d9030071429150480c0c44010b402413a4600a006e640100c0109219942c0300160805010088034400c116009440b8140300f000001500039000c5584100d85c1070007544a04031003503c55100b648001070150009010f54200001c029050a840304c0038691000480365030b02c07012540c000100c41c21614280b0340b41440440c00000d0500b85515508010029400002031209060344451480c10345805046920002c07041c0c0784c4c41000300354680500806d00c0c202e4040401c0390258089a44844840100c400340c45e01c09140750701c0045400202556448a10100610642c03440c2d060901c4081c00341d40361090b10f8a0b040c5400e89540e4680055031008001d082001c000070840410301100007440058000141030900412841c0114214001c88074215921203002601e458500c0c10001103c0040c0c0207020809590345032040903108010500003400301e090000800040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 859307661 1250 859306411 859306439
    0xf010e040f06031101020d0203121b04030503090306060a05030a0f11040f1409010606080f0a020f0d1d01050c07140c1507150b010927230a1103040b0c04 67
    0x140048005405403c61415544501c41344008030304552180c80c1c0b1a403010740002c129020030691b030405102941d103407080384100014000c428601480301080000410a00001402c40404c04170241c40380e40d600d180501800207003a10540e581a48024586030210300516006e041181c02042440c105441e8500800c099a644250200c10f40c1c1c0e42da0021142c14221010440d0080b000c00700910465140010042c0441e501900c890416608000403410100c0c0d40c2e412580803402444426884d0401b0780f41800003801d0a5940c8510f040110340c8030080008184200d5102e800e81c8813115003813005580740c07120161121182824036116028201e0b0850f0f0700d4016014000203150503581e41e07640d039454400c40b103d2503400310f0041641000040b21180e0782007a090001c1d14101341c2c00215500365101309000030060120f114075018071708a015111019100140c4003100b0210041944540380c0d001c0d150f00310f660b040344400d001074080c4007250015000c0b4005a42001d0741c030250300c1c10130b601c480e660001c2070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 859308911 1250 859307661 859307681
    0x6120f060b0c011d1c0e09010e060111060c0a0c05070314160f0609060f020c041418060c161407092a0c0303021e0c0708010506100507020f010e04 64
    0x44041140a2502d809004110040304801d8841e034044100c01c054690b250541150b00b050801e030040781406032403044e01d8110144900421900003569103001c48044d10400340c41c10307030015051012040c410000051a070303024071a8034106524044429804840c080041401103940740607089000002c50900c1d07a070740003104200000303002c2c0354941031030207441c05038035600049014002c480c041019a810103868022102142004da0400200702412400c0c03080c20701c08a94030525081e52052161010704a00384108000c080940e0005d4248034020b50f42c04045481a0040320700f080060008004a4280100306200d120180e81c4415801c20b00b50800c441a004005820f03580c02001c1002000c83d98541c40c41c03a16503880e00c411030302c01100100f010851100207014150005803041d642490120007401c031000400450340c44d040c02c075480c191210310314854440b1a45c00c03d804610b140c034080b180c44801c900785840c2c03a07180080f1a42441747e04180f0805040c184820703140e107491a51140d000e035985036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 859310161 1250 859308911 859308929
    0x34060501090204150f050406030216120305150a050a0302130621020a06050405010813210206191b12110703030f0606020c01121107020d120201061a0406120f06 70
    0x40b82015060301342009541049804c10903002855050f03e601b00003200d0079141c9a180144c1d0b205c501c694010304000e400c40005011000d804419815142d0590101d4000c0070b40e0402c0c90071041d415810040000c0c4175003e40741e80092901c1c0100010318107902040c8121018880c08601a9950008609155903c41004c5d01003001107162030110700e098103000b0098420360034024142420710000a084e180018100e080051140d042c0d0b4040c496a10340860010030b100f81d0303451000c0c20141009483d514103035000c0c09030b1040392200c98142c1c02940541035019907070101000035284940012219800b2048484c915107954035102e02500d0a040001e2040d540252408502490722441c0d501c12107009038004000c6400560010180f60790000d004d103590080c101000c02d01c00d101e2600181140b181c2c1304029440407240340c80e1010485512429028100310360000c0044a40e00c0601030405000080c17000d0001000f048203106081c02824094001252030b200012807410890f43c030700487c0d00136000401c2e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 859311411 1250 859310161 859310167
    0x19120206010503011b030e1618060807080d120212010e0105190e0106140d0606110f0307080909180727020f0904021c0f061a340605010902 61
    0x15901000024018581a00200071500f02240c0e07450349041d00b40c464a00301600c40c260703603c9024041285a5650030803904040c4c500340e481c100c41e60036120283c000341c4d02c54208000000c1400d0081400c40c2211581c01c0a40388241341d101081300c0306001840200317242503003803252009040c00307981607034040c1c8018141c039100c0754144810485016915809030001607420b1070306100c69221111094110b5101e8180142400d071141c02c5103200303016500e400c03010940392078000103a80da4000320394550b80340c602c0152214814440b50181d00e81c484c1d282d0107407441c50304101031001c81c10480d00041d402800f001e1282d0f440c0d40c601c50f2150808000d98004001c490114030f0104407062001d000011001c03040d6421071070852005a8450913010351001948940ea01007050035160711580484d000750b90a03060200000da50711440f05000f001107008044145804011020a03404034000f00c6061412050b040002540201c2a4a419400482c40840c5a50805c2c041c0303400030714a4043c0034041c00e803070303130016032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 859312661 1250 859311411 859311443
    0x510080d021f02130605030703020f030f0402190e2205100b040c090303090b07081e0a090605161b05030318090f010f0e1b2106040e10050919 62
    0x100e102d011410a030698810800c0005030903128064004440741414800e44a54550702e041d030090090a0310240310340780000070405a0410041e02e9840b8a00c210740000040e0308192580511400b0381c0110b00c01001c107040444d40018220b00e040507814550003240d841e0951640d201810a9000d00000da00c4a032100800c05581c6460f00030107105101500d8800e22a902c0d58400130319081c05403040c2c0300391403000a001d0003030250013412a14402506012005e001031041d26460700c0c7e41c448040000002d10b0583d0201e101d510800807100c4140022070f5a004080c540d840301c480e100203002040e5940b500b01c1200181a8801b40050505100c41955420140e40c00000f8000820b10013030140700d2408440300140542000706003213405813510540c507420320340c0d40d1850381c076160103907080605510040418100583c10540000d111209100c4903c1002600d507401840140e5980c41a41e1203a07403c0380300c402d9038030f0050b030740000e5200c5600002c4450400c0b05034008980c003001c051066502c009036102583c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 859313911 1250 859312661 859312693
    0x504110702040506040c14070206160507060207060f12020a0908010c0e031e151e0f09010f110a030b0a0e0f100b07110f0f03060c0901030b010c0b0103060510080d02 72
    0x42d13101c01c09550502c14010030ba44020f009460300058941c0202e40820040295107030301d8195440d07074800724030640b00d050b10740c2032082d035400c2075210705401441021000b0814a00c0f03515034040d180301c1610b0714100304000ca60760001a401848a071402c0064032500012082c0090091000d51441500d9000851510310141030900c0c60f40c80310052401c1c0d1034a041c602c07e040000300070448812112003c076141d212908516026802d444c404e14032204d14070188500d11004540603030041c41040c000300898080e040505050b6102e03c580c000011900f0711010603d940290031035138042c00010b11601d0807644074440b0100c0443c003601c41d2081402044200038181a400e0104405040702c1ca0007903003001c200b51740700e455002d02103100c64001c220003802c400485d21030740880c166100d801400d0b240c0700c0c50038850400b100c0d0400069140000d041070009540e650091000c200c4494001121000680c02c5032101e001034280500034440030114520000ba241000b882090300c0000300b9030182400d406501140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 859315161 1250 859313911 859313921
    0x603023c01110610050a05010314130c030b16032a08100b04030606050a0e190b18070c020114040501080a0e0a0f0c061d060d0b01140c0f0708011e0e07050411070204 72
    0x400c0c10f051420ac002034210a10f04080d41d408810124600807690301c45c0303402041a10715502c004c1c802c00104062100f140c075154079407040100c035039500701f1084900020341001c151a41902403c4a0800c08141421394410a60345d13500160040e008500603941e2050410306901642c410794005666140502071440d1500c0b01c80c0003071107106240b1806040c810503211b210340ba00e00d5071a050030399522240e0300c00d4a0300350341c1c140c070702641421158140c0780207000070700700c0c455960040740013500b45003485020030442030555090302c0c0c0c180d445420583c0c03407850080041200c0c00c0200c0c4984201c01401000528030610b82041d01d1040b80860101c5203400070191100c8915075540e503440c148001002041c2e150f20043c1c80310000301c1a408514103c01c0d0005071030705d40c1403c0c0000c280307044c0055108080c03000010040c004003400c80460340001c1d030b41c1400b5422198544021000384008042d1500100c14a82240020071030110035252090761351750018040b900709038040000303140c000c0f4010303081d4a454816 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 859316411 1250 859315161 859315169
    0x7030b090115180c0c021c0203070602061513060b19080c09180a110d060e060f1f021c0f0e010e130c05090907030603023c01110610050a 60
    0x240081801c14803030010980c022200d010101381c4d04c41145442ca88141c801081e200c3c0c02030140d511907204150440d0b40209910803e07030291017000000500c0364400141d0707070310403102000c44030381440000c0100403519032500108008603882e04c0010804600c400000c02001c1c056a107041c6894803012000303080c2e40c200504115a01030148810115525415013601405a822000d0603c50b684c20207804014050b19841406506010030b9108030144198001802c7e501e05110408040d50740c1030410003108543ea403a180c1010032812410240e580303001100c40d130040d4500686580a11074580c5000c100c520309082000110320310524003800da042034940e001d0728003e00e030240c0c0340e603d00d50100301850a00700c0c2102c07003203644011900b00c161160082e0ba040c01c1e801040004a03061042d030081c00f401882c0000d91040302c201800c04085010556040c28201020b24520601e441207502105a5002181c450b410b0100360341e0002034442d028480d04c3c1c4107940302844280310358200700c184122500c090304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 859317661 1250 859316411 859316441
    0x9150d2324010806010302040c1817011103060d080915070305130501051306080601090902070501020406081003050d0309031103070f050613080906130317040e10060c02010c0606050307030b0901 85
    0x140b0041c0004100203046d0782c2c060300d020074840c2011000b200c0898082d402d58100024078200400c1c030070210182d96081d44100c000a01c81580511402c0031b081c4010f6551a034407002c07264450000600c61405411000710041c42242030410180b820080c551014030200c0004e00001504600941c80300c1c41c95000e401c00f803800509080307010b004080c0401c042e021340e500344845180003c05c03a80c8170381d803224090100305005544615451410501035000b500880c2c000c0388480c00004c008009410306603040f00e411100a2107019030400040c0c00410301c04100303508000f00e414501082d080c0400007029500c0c030a034102c0d2071400310350820a0078620082c01c2c503d402c0600c141d140303000c41c1c0c8420035682040400c80344155106500203801840b40c2c106c0c0d000400b030041140742d200c0305000c044060400c9541d50a0305101c145c0da0181200242420781c029100442c0c585076011015500c604041c4809038496940040c8042d21680081d01e03000c680d50003110746c0000b907401c01c44d0b1681d00f030007610041155a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 859318911 1250 859317661 859317733
    0x1050a0501030506041515031b060329011b0b190c091e080601290f0d02030411040f090201110c0a170a061401090b09150d23 55
    0x798400340c8031200904054043c0c9011070a03204000e41543c0030308a9030350000021607c003540d0786062031582070010301941147c030701120002011406070007010480c01c0c00b0181101001401074005060702070a040c142e0400860784000385002190f81b500e441c065004c0c44002000d4175224058008501030891020f04072400c1c00036400c61160408030b41800e550240c410f03030050903031640807118101c0840d440f1130b90350300c500000024490b03410000c4442b0240a00b09050640c0662007859240384507040350840503003c1040f000c5484511036028680240c800c80390358140e100076500060070380d07074003900c01080b45035507190b40002c540c5c1040030300005460b440c01811003400d0b00c2001960240451241c920400030344054200103440c10f215001d070302d6a01c11000c203d028054081085120002d00921416074030f007507070128240c945206803c1c8900d5107000a11003194190003400380304100b540c02211091031608244194450483e88120603c8012000707203c582004054600c0013901030342d0140300c4910b50307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 859320161 1250 859318911 859318913
    0x1101120f0f0b09090703350f0c060f09070e130f080a0324060305090a06020310050a08060412050a050403020306010311040b180103061505220e121602010221040801050a050103 77
    0x8001d9a15040040d0004030441403800c9041111000001014030803082002841e500d55098200103400301f13021107402ca400ae6524906034511062040e1a440b04580c80400300300403006803501c2056000b203004074070407140c00315031b0740d042030000350458100d4540f0b4021034002106617261180100444490160300401c0c62040900540a0320f14001d91302003640f00c0000901c402c004208003a50285c1c012411035591511f20917100402c0880d001e12807140325120000500884000b030786031301542d00701d0310140e403010a950f029500b0b43d01c9000024203010f0140070010142e64217202c241d00940c0100070170101080760f24200011620a05103141c4601428044481c034041010400f85c1900e9000400180e03100b851b2204c00e91400003540100e83c041c1c40070180c80740000d01a001c00743c103804210018420000c1e1614420380317402840c007818a01004c2400382140900f00a2078071100180180142c68031690300044001c801c480410203029410300c00203040200d26800d01c02c00d60b02c00003100d004c20141d411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 859321411 1250 859320161 859320173
    0x3031d011a100207050a030f0507270e1006030b0109111603030f0b1f030e010b010c0b1008120403030f0305040305030402090406060f170601121101120f0f0b09090703 73
    0x4640040790091a0259000540328002c110b224003a000c000c00900e4016600e14107408400070704ca004891900034010001a41c4481003da4101c680d0100454440306582e46408402441c3c002c2c11044188950400d144819110b4032680d4081c2d40210884a06903040074007103015030b091070001105600c010043d601e42008210740724a13099616103408521003001055000182c0a1910b5180d40030b15003840c0000d007205000750072040c1040701d440602c615103411148500301d0b02442e00c154045922041803000003441d0090041e48021710110307980c4165150b940c003518120b21000e400c451850b002030288103064000d07040d401c0c015810b20701441036103400d40d8001e0050101070802400b981c13001c40490100319054100e1000341400318143c1071242c1d9580b440c01d42624007840804c02c07070b0180e10004100c406007200100071041c2c01c0740050201ea40c0000044558500c3c03008500d04895940c0d5118402c21154040c0c0c1003141414031020481000300e000f003000f800c40c0a400762890f544906001c20014803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 859322661 1250 859321411 859321451
    0xe0708150903090303161214161a070306061106010617250e0111010e0604031b050a0803071d130c02030c060f01080f030315060a0c0203030703031d01 66
    0x1600000c000a0352900c0000c207245000b207021890b8580400310b802041d00601141e503010b414014007082d4404040d12105136102d9060860000d900d5004100b2102d00d05d150558500312a40b240c4841d00c2e50a800f40d940500700f0a0580309180000e4945400700b0006512900081c0301ca02c000780031308115413618102a1803014200e41182412000800240580700508559141d0300b6140c40e46a01004031240010810302c41c0c092802d022907030414113050003050520407035021207040c0300146643e4480e82c4041e51421940c1210a070a842025807600014406001d07005029101e04407003a12030924040107040284103881c4e01c680c511034031a4244040d910980c800900c2060440d00090400c000e05041381584a4417074004000e00c42c2c071051010b6685520790042c12180c0702d6040c0c1c1c2011080d5812382e0780b60b00c03080da9154101070441a5a07100307403420400500b00203a181c1403452580d08d05034042410b68000c02c41c1540800d5649072404c0110021340c811140e64100d8a0017048001d00c05e0005407071140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 859323911 1250 859322661 859322683
    0xc10020a020d0812070905040c020304080316061b080411120c10030e0d120c03090b0c03090304090c0806040b0f0315100509040f030314240103060e13060e0708 70
    0x3000d51800c40b0070700c854501210b134180040070000c2d060303107031815001c4c0c4100410722410340030328902032000c02c01e41c0c80481501c0a4512000185140105480b0441d40c01507070044c0682e500340da105d1041b540b41c408151440858003c2e03407a144102e140c503041c00d031514100b5042490048410300c144400401c40070400d1708000000300c5003009401c00085048004000070107800c2d8262040410042c41b2582004421084a43c1240305000c00303005403500710161907288400821514030f05020810110b0103001031075125002c0f00031a420300f036840d0481001c1e40c4860b00c661b0081103a15090100c0d60030725010340d042c0824256030701100c0742c080744003003580d55150302c84c0503150328010000700e001807099240780e0000740002044030450b81080e09150b075000300301c40c80c201c000c40e180260482212092000f01407103482a14400c1d120014021200014010703001002410140c3d2410302044036080c1c00c180d40e02070b000030790302039014100c81d140c414111011700e40e0081159100c030fa13082140481c00a0501031030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 859325161 1250 859323911 859323919
    0x60e010518150307080a0c090603030f050a050c0d030606030b190b070c0f030506190b06041211130e0106050d0503092b0506070e01030c0e010f0c02060d05090c10020a02 74
    0x766480a201000d010346040c00355a00d03000b25400002e10010020b121072a20b8000c0882d22200c41ea1001e42c0800c032021440001c0200301d40081107901240690b0141c0000c1c0c805003006454242c0006095041c11040180c031004641e4860007403120301e41c1841480215281520400740c140c0c07081c41603810104661160b0500c00d00c0004021040060880b8a000100b40104401458a8072460b02a89500b0202d030100344895001c44400340c00218ac1c02000c04105000d00040d2801e818004540a12201003209540040c40c1e407101e04007686541100010300c8107007000c0042c640c0350381c03c241401d4450302d9001c68420f400344400003001ca0700200c102c642401045407000311000f4418100301c1c5607100d988d00318006640304a04a81408400300702d607031081c400f6a650002030714000e4019000ca51020000c034000a0b0743c424508001d5000346a824440034031414202040c460550001d92194010358000d0f003407903150024061808801c00030100000c13011520180c29012a903402992811030070000781c45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 859326411 1250 859325161 859325209
    0x140118090f0e030d0509010c0801150e06040b16020406060509030303060f0a0302060a020c0310110d05040606120c14010507031d0f04110315030601180e010e0114010801060e0105 78
    0x20361045a00c005482c0281070140c039200c040705400786005160440d1048480d5084c00300c1140280c0c42540a641a03c1d0026540e540703040280c00219407030804c140e441c541201c003c00021401c03040c801d0103400c003900030b001c01c601c144a03d841480b09a07000741d0f000d807044c49403d000300c242e944e5010007526440142520708200d071552001c0005c0322a8480c0d44040d4001800242e0490455030104550864a00a40840d21651580103413581221707030b041c1d25078941a20511848080e03001c90341005400c01d0003000003264064132050344136407204001c00126261042c01d581081440d940101c2d08410301c5090a000341003d80ca41c8001d8140c80d001c501074494071944000c3c520700c82c1d40d00c402034103000794017070b000b0881c0c5110ba0074840c0050748180ca001000c1c9209400c900c245180014410341038840d800d411258500c0d552821602414641039420070b507540707a0075400e184200901c99502c0441c2440d0100030300e549007100150845005401031444100c0f0080180301c00e44a045240001081d000101c0d10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 859327661 1250 859326411 859326431
    0x31627050903090f0f0901030b01031b06090504150503250e13080a021c050d05090109350f1e0304080f03040305130b0d0c1b021009030c090614011809 66
    0xb07400598400d0290701c41b082d10000300a2100312000c583c1620300c02d4050714454003a114610050140c6842100c0018880f411f05121038245500840311608419050280350380d01c880c0000d08114040f6180380c564036101030780307811405d554500600100f500138100703130746800e05404c024070030404501c02400c281c400240c0252814030810404111035550b801c480c1c106002d44000a01c554040400348544908180100c0c00c5000184034444969074450320300b01c0b00c0c22000802e48040c0303400280341180001c08045113000078003400010010f005480039060358072840c9020b003036a40c5003a9040c034641c1910900800c000191204121801c0c8240030016940742d0392545411129031203080c03110350002107041ca0004d0000c000e00c01502e49401000800d01c111650702c8000c6031940e01c0b0002918042003080445070140c00c188107101c410200da454011043c5841c0d8a81300941240c035441280600e68031305080040b01e02c00d000801c0300d0030092034514840d6000340615003035280300d4010309040035981c40f03020f5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 859328911 1250 859327661 859327669
    0x120201110d09060905010806090105011d0a150305090601031101201e0d0c08030604020f090904080a1d130e01020d140108120c0304090b031627050903090f 68
    0x548100d1503030111408181c14140041100740c0611030750000c1001c1d64404140356000340c0c00188036480107011031303005a28000c01110003140205210100f103c0909580791603031a202c04a074003610060100709202070352080014120f460007007452440b41c100c40c1c014000185a80d480048903402440c080c0f0704840d020900000360610360003050700500c5080140744582e03110310a00c00c440300344202522014400294103403019050b1850040070802c040001402500d01580030386811000d1402645c00c0c1190300012500340781c02502c0580d031040c00030646200d00d581c00614000f0390080c002e25424590324040101e03030821380d40d20400040c940c4414038980081402d5040c0c9408003100a001e10151601d04517a0300011404e002d210881e000c2d421120740c1c460020300407205a511a00025840d1500d4500c04600030040703800c016515008029084404d100100d0071400600f10781041c0c10009041010310240c01ca8100060f503010714201020024084400b00555030410790a540351411021014001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 859330161 1250 859328911 859328927
    0x6020a080f0405041a01030606030b010917121b010609060513050a09170d060f080c220906020903060a0c08180f0601061701081c0f0c2f06070c120201 66
    0x720740c04c0b901d0441c0c800b000515150400040c180207880c20450903807039100840680710345c0b05900d4042034080004118506002d01c000c12880420410740b0305024a0011045541d44540c1d440d400d01090b2024941c0031940c2807095100078564020300700516860900800d000000d203881c40402c1950b075100003946c41d07c80381c105210565001c14a0440c401c0302001c0494560060584e125006250903c00b15038507030038010020a40e1000d20080401800f21020010f00d0600b1300ba4104c47d42074401615907002c0e0590040a285c184600303400f58541e04090b050600c0c00c080104008401414511540015074204140c0c54000c1014540b0200c00c548031665585480405032101c081ea01c61000001080d581c00702c144001c0c2d008030880c603000707a40e82e1850655502060a1810361001d02408120303840c5001e08000114401907060401c1085e0180d1600901d40c42d48080d01c42c060780c8040700e90240010b2400048203817107011242603060a01c242c413080341001c068004d07612820202000075041da07000d200c0c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 859331411 1250 859330161 859330169
    0xc1c030f110f0f0d020c03010b0a0e040302160b0409050610080402090a06030b0f010806070915081009020c06190207200418121205190504060612030507170406020a080f04 75
    0x440f0030041c0c0a040f116039510082c5012401030190b040728590625041c01f1720303401e40c08001d104200349810528818410b03500a40200d0a51103a4800114418074240d5030100500344a5501902c0781c2c60000c11030140c030350051a062007081703230080349060a070f00065100d4100b03805441e87e04044c3c1d9003030703003000051401d0340005d0180600c06041100031440d41207503a0582d00950281c5400d500c0d5480c003610f00c00e00b40d02400208461025a500081d4401c12030307190f000308940500b032101599680501e0880e44901c4064999806c102c0400048800c00b8800780f244404c8028114607181041d2291102e9040e00c0714210603181c0d00700c0002a00740d0700ca80000600c0c40000b203d9644120007843c100d001d051008005201041402008044081c050701c98184600c240210f102e02080728154800300508000b04103c810b103550303140105a80d0680309000011510980340c1d182d841080d41803665500102c81601c000b0340904000a00c01140d0118401c15005c0e848025541c8070070141c0104c000c14050b03504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 859332661 1250 859331411 859331413
    0xe030319020d150312021f0b04060e0c071218061d0a180b03120a031d0106090213120f0206132102090717011205030d05090c1c030f110f 60
    0x83c0302c84881e0076190003400c40e031145000c1403020143c02030607a10f07a40201025580d0242c030307807010000f0200c2a00400680a402040065440d441720306840010b00256054105070a01007841e000300a1100c000149601441c240380c00340d44220a4020524801c2c2d0081340d040040072a00c0c1d002c031802d204211411080014100c1c00d903035841d849450200c00380c803118040000d0900006410034280410b1194006101c51051894104440416006060b41940d0021003540701071001a4483d0300380f0900018002c8800c0141e0340300064400020181080d400034150b000680c547c2900045c846940940345580c140d071495155500c1e007142c2a0f0a0200764410039280344020305841110001d083d030031004c0d40c422503101c0034a0302d8816080780d9000f641d80c0f0090b81c22103407034014082c1a200c0464074040520440c1107a15103501c458880094800690302840d095000718618080303464203110f81c40485000002c28041c9042075140102135181811031403050101581c01c060904400744110032040728114 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 859333911 1250 859332661 859332671
    0x20f030304031806050a050702040c0516050d18230d0503120a051806150303071505010e0c0325050d020a0f201b1c03020a020102100e030319020d 64
    0x424054007510041c2c9045001c0500301c10040342650040050750f410305d900740c1e07c3d40c0c1080c44a43c240001448070341400810301105011801c038158440e44403e8031107100c2c00c042e042030301c0391100250002180038041110049130282c140204a05500c60505190700d940742c49000c062500040f400d452078444c805440d03400006030800704001d0f410411402070203000d0302040a41d481268011400c5641c4c83ea10703d8540150000c20041d111401c080c1c03035441c00082c180c900c1c1010030794503110f01c0100784208441151311000100000400c500701d0960007003859000341e182d4500b01d10750345110403940c405043c2c040d09428030ba04103a40300d401a2030017140d58040465076022090805000c0f03800e400500c0c0006500d82c00c00c3c000c0d9606550801d000d109120000b0322843c1000c0910850b6030980071082900706050501d5000035001807494400900e020b50040c000c071800d140002414140044030814600e414210380c14180200081140d5008603041038403141e102c041c0c20004041d109020315040c03482c2c244 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 859335161 1250 859333911 859333913
    0x15090d0c12030e0a0b0711150412050d020f03030f071803062009060f09040b1908060f040201140d060e0106030c0e030606090f1e0a0b2d060a020f030304 67
    0x810800300e551030190f103a02d4000d40309034080100615550060800f4040140420070000f084008410b040e440f006000e0030500035142c962200c07642007a444801004125400b14080c44810b002c5902a00d8980c400b030135030303076005080543c2d0b030348009800f003080321080500291081f4801c0d40740300c0303540d181d0041120000784d407403c00c0030240c184481030f0540d03402800e03070079450f114008080b05c61401000d40b0b06400d10200398008441c0741c109103081340d00f060310742040c4442c030355070800d03640940483c207210152041e041c40c10b140c0c5490b60081c580131003010040300380030260382c1040440e843c01007184036951792048444c180d0000b41006510084200b0044000072030050b406802c10960710b00c00d0342e101000c0030403210405a6445060303402a41003c5503e02203460074100c0701c1140d0380000091903c0070448410340402101d80030860750f1400302ca50340c2c0c100503240e1400c00e440001c1c5040744449000034540c064040c0501c3c54003425554400c41c00012811a0030380240622608101c2290903241c41c0e03d0a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 859336411 1250 859335161 859335179
    0x3050f0601082a190e120d0f0c0218071701030f020603071707030506030c061e07170a02150c090a0e07030f1803080711071a0405030a0f050f03070215090d0c 69
    0x150780003803030101e030404022175814204071028045a0100344c00504e0540081082625800b01e2480140c041003251070200b001341e152410401151000c00000500c24030f40860010100c0040e40080100c0369549030040001c90111001c180180b901110555502e0311400c900b664141000071705044545082c2081003038603605079002c184606015000e0760b0034504c8a00030440349101c0c01100030840e0410400800400c980303180540340c2c1500c030740c040b841c0301c41d04441e6101342500038029200041e40b003c00142e040c44016071a50f5049020100103d040c54089400180c44c00789a00030550092810300000c4c0b0440c0c406d4001d07001c2a04880d8080009042458502c00740e8107507400290081995400030517205441407041c02104402c4a000d040344500f40117601910342e000700410641c0c000c0c14131010400b0f50f810b0140703118142c40f41007010700080d0145062410098950012080ca400034030808026854808400c18043d945c1d588617690f030160a00055140710542c603016019010740300b800700703481c40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 859337661 1250 859336411 859336447
    0x90b042403120f080f0912040e061507030f23040b0414011716020319021e0601050d0f21202803030609020c010204050103050f0601082a 60
    0x405050040d6641140c82c0e41a640355040095000020300ea030b10000b0901d0030450803281e00300394810f0a030740d9504101442044541c11940220900768140e0b0240070803031070400c00e505044056a03410506140140d1406403001400c50307814814010350070050946209000708120180b20822a910388458480350741144581050181c070300c0e44440300c11300348580d6000c2d078008008188680c15461b882d5803461240c10a0b42031007100c1d101075210038002e0308500c0d40c5900f10702184040590003803600021440c1c03000f034211002042d44002e074001800501c059280d0024140145030400d114090702d107034601c0c000501c04a10303920080c0030711801b01c000803026448010084c4651901e040100c400180c0b0700225107072250400d42c0f00000f098078080340c444282c4522010074840c080e040000d4000c0c1d6401c10f413030903a40155644109654006001d000340d6816220b03540e0021507240c5d440f00e4514202001820005024012006540010320791010080781c0e41480c0c004803c400e0700791030700c580302050095060302d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 859338911 1250 859337661 859337663
    0x1908030a080a090803060111011506030b101d061c0203010312120b010801150314010308040906060512041e050a030801090609020307080f06030106030803040b07090b0a0207090b042403 81
    0x24204408642c0700d04041c05000c0120b80c0003604a8a0340d2507100055a801c224103c80e104195213401043d402d02035038542e5040107105540300458510300c65020041550204d403020001c0c004c07900035910002d00c2004500702d1143c810340b44c5950340c83e10b1001403030b510030100040101c1d0303d0000002208005000d90984810646500c4032205041c02100341e00c1600d04160404d8002041d0f10010840007284030382000c051025410000380c00e02c44001c04100d0407002340c0080c1c6820400040030031540380c4500c10321000b081c007460003a051405400102c8265a13000c4c1000c6c0141703078400c90b4a0303503c21704225240000c0780c0c880c080710003204076840c010b0031205c0300348501c8080b549080400500981c1500071a80f04260503510780b03059980311000144102c2028107000e0b055903035604040001011034000358041c0d4000d140b00042440d080b6001026100385230065040b07510244a0380310200d400158071015281e07a01340c0481d0044c4000b01140041a654661078400b08403090fa002452481ca041c0d80181e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 859340161 1250 859338911 859338917
    0x5040509151b0a05030408160303061401050c07140301063803010302010e120f030c0c0a05011e1413060f03050a050118050c0d150e060d1703061908030a 67
    0x2580d501c030b01c0340307506640b0690394000ca92802c01440d00c86030b225070f00456010307200d0880e82c0e0800f07034040148400d00c20f50500c1200441d5a03039101740001540c0700c00c0c1c004020800d1030078520b0a050902c086858140c1e03031080540c08801c0072051440c961b0207402107030103066144503044c001c42010030400303038a240b030411070004040c6803070507894210000c0007180d047e0b98060312211550030145080c420403a0080c100080716009294264807035000a10003000b49143c403000070450345400004100b4084c9060303005906004c600101c003010f401d040c205040305170046040284200c0b05a00140900380320b101c0c1d144107224500135021030810f4200545c8012111956410070003a50780a0024045070800c0c00390803002d04a000000c034403807019401c013642c404a1080da490900348007200000a0350b006001d12004185842c500740030310180c174100f080c0d020340c0455040c80b41c40305d5034072044802421010310030501c500001c0021410703101e103200c03282195243d82c0c1060303880307030b40b14000c6860341c0017000c00f0300c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 859341411 1250 859340161 859340203
    0xe0103050a3b03121501090e060910030c0f0f080d0212070807050115170607121a190e090d1407030e03330603071205121602040b04140a0b0a05040509 66
    0x517540704002547c1550f070082401e08540d21080304004102200521007800e0b02e030401000f2001820140c0240014407400461030381031030070040d100e80492002d0300402d80b168005020140c181c0c2c2c1c0000c188200110462840c0c1e990341c480d0800c200e251013403680c080c3c003541c208030000d04051240d000900840f070507007000300244c032909504d098444c1c405848060001e50702e00c00c00204102c8541c4908001d04c40e64040004640b040c0300071a101014001180311500b680240c104002220180d00580c80408400030382820042c0c414041c0024911204c401000c44011401c2c408043c041d400910007020700504845050300d21400c014003070251442e02c40040c420b070364005201d0280c66217036540100300c0100501b58640c2440120700001c0c0d503141060b0380d00e202d54002881c81504400051030110615078103c5120b0450307006120684c0c000c60f040500440c540b52128600c0820311980f20341055008201141c40c1d500e60000440e001480d80080f58800e00e02018402da1540000d200300300b8030b00715110521 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 859342661 1250 859341411 859341451
    0x70f0c141914240301300b0c1c0b040b150a0507060b060d0e1c020703080d1b0e0a1a1b0106080f011a09040f140304090c0e0103050a3b0312 61
    0x9001025808040d0b5401b0410807207800203010603441c3c0f41e2081100c00c0d40c1d8100540d030030844948250b40305400f1000359440c01c860030141480d0044a09501e415102c00b02c0000342c0c0410328640e48650340d010000c210000c9804001c200c030b15081940305443c0100340301d880f003918050200080510400303107940343c440ca0700003130340420341089802c0724201c460b00681011442e5485400c08c50b4018515006070a0b0344200c9115041103044c42c0c1c4c0b148110603513803840f05110250038040b02142540007004074641410508045682d100300300c3d203840c030038030710400240200c1c0c03800d40d800750181d5009110f00740603c55502828141c150300101d01c1266202100101da1000418021400720a40d4003420001e24000340e40042203588421406141c044070880c0e144ca0703503a00c0803d04a91050044100195010003c02055a894041c090b0081900c540801444000c500404003203860400c494440b20503802243c41d80ba01d01c1c44100f001c0010040559641d100e00604082d0004000c0310b07200000d1203035200180c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 859343911 1250 859342661 859342709
    0xa05030c030706080a0204030606080a060e010203010b0d09051204090906050c1207111c0c060506040e1b0102030904050a271a0606070f0c141914240301 67
    0x101901030098050503481d0300f0281d0490b12108010881d0422940070400000090307414400ca8004007464006004c0f01c408078944201074448040740b98080e68010300040c00004440e44c1140c10b0440f211400250702c90340d51800c0b504212150300388010003980420002a8a0030f55000b6000486c030809081180382e0360341030034100a0103103000303c00c2200e0b0080e0002c0c1416001321440b07004902c907c41203420030741000c2424800361080c20070340b00000380f00548010400c48103000d41d58010b02e0841d000e00050044640040d45c078490460080207024444c0808a2141d009104442041102034030030b00c000c0c90700303a0100c0c2c094203000300b1084240414118206510f9140304501d12034641c40b40003400440d1005407450080780002d41815071102c000c020010014811400400201d4810400150401d14211121048003010380409010300030010390000b0700020162410159000d04d4840f400044901010a2543d001c0c0c48465010010203003100d007c0500c4070020b03604031050403030081e8800d21292070300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 859345161 1250 859343911 859343923
    0x20f101416030e1629121305060103030309030306080c0904120509060304060b1c08120403032301050108070e1503070e0d15060f030206030610020c030706110d26070201060518060a0503 81
    0x301031102e10500012011646e000d59040d00500040006099401143c803143d00703104083e40101c001c0b980d902d0500d01059094040d950040281c1009030600103140b801007400d07010014002458008403110258019000e035040d11440040501032580340c2c9002c1c90b100c0c004004600700c00e407190368481c6100d02c0340c01e00d412030060b6417640300c10441d0900c400c80100c699203160140c400c4090684506002c0088490040503d0442c00342c0c14810f42d00d1f514110003d01600320282c08107082064003881c884003902c90341145040d45030310207503486c1c0d6692503200880d1400351000392550f000088000403030a02030700205c0310340354064004040104a64600011030198442d110094200b0018400102c40349400e01144100d8402401616200c1d58400002401c01c10300c1e8000c00c021820b44001c120090b4010003580c1d01000c0f080c00c05400490640c05112002858800a00f0301c00602e000007541c024400e403c410010880a040c01c0e509520345201c40e08400030482d1603030b00400e560300002415160000d01c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 859346411 1250 859345161 859345229
    0x240e060414071d040f090807120f0e0904140a2303180103020d090b0a060f092313051e1b060d020f0c0d020f101416030e16 54
    0x9912000c11182d490580c10550f9801250b50040c0e4507005250018000d0141903041445080b0b030329a91641450300840d0302da514080300f01089010583c2e81d030b444c3d42090b10000c00030001c030b078080115a02c40c40e000a2403500003a01b003d690040c17010b410100191a0284080940042000202000219011a624010500245080707252102c2000c56075000758020700d06401140400704620300c440e02c81d003403404020f40350040b421f80d45400411101040c5e49003003015040464082c898508203070000b00b00c1031960301407112102050030100340440940b60b105041c081d442002e4034541003003100307540c100141a14154569000300034010500b4070340918442442c8000800c0c1ea414141740c40900b40080d0003104030301c041070074104444c40380103808020006200c2415401020f1180785442280e0403c4050101410b40307074200799071740301c0900d03101d518130394131000141d94910740311102c0008401901c200a010708450191410320400128211003c50035501001941d0701607091241c02c41d00d00c0e07100451 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 859347661 1250 859346411 859346417
    0x1b0f01021b0d020a2003010c05090109050a0302091602031e12070203120a0c1808060105031515040207020103090813080610030305091302040803130e01120f06240e06041407 76
    0x5011000506911407041428122082c17415004240741c02290071101c0894840c008190086410791030740d0b80c06001d200140c041600c0d0b51070603902e151b0118404850140c1101e403600240400d010044e4800c00580300444031900740034002d103000100b10707017080d03200c00309806100310304500044c0024000030840f0280b003610764034458196281c0305010010710100c00c1c004100403204c0d91810107020f415841c18042e0030510041c280551504e0101850041c100544140e071035288420480e02898044040b030540001307950160707503070380b080c801200145101c6d84024604400030520411038007141007502c042c0c03418a0111015a1280c0c1255104c12803103100c0240080c0d010001d15056003400f04600000881950015080c10344403000941560401e8403011200c1410040030040c803503018040c0d60042c85004500705c0004125151200e61015140d00a0049626112034004c640e0341d000c400f800c44440f000d001c00c0140c0c0c54111049029106480680c429070420103100041030b07401411600074281a2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 859348911 1250 859347661 859347673
    0xb1c020f1b011b120507020c220f0f0504030207061b0f171209070501030204050a150c12020c030c040627020d141909080a051b0f01021b0d02 62
    0x1240e01c0c111116845408800b5500d40c052400d01d5121058075040c882200d460341303480442144880000c54074001d04500855001694968940d2914000007082a961100b4402c8001c1599090700150440c80031200d811850300318107010801d292703880f850250b1310a07425581020340d5010102c400906460825400c420749081000000303030680116200c6a215001c000240d0789601424203c40d0000b103800010070000004100920302c050002e0b00c040c201c01d0808504042c103003404106400700030b000e40616910b02a04898005028040c2e00904543c012049030900f400c6410017500c60124843d014024402c05202c50f4041c0382c00e018500960700202801c8015010307201c020342000d100d40c024003d007a6401c01084070245880c0c02410038600c01c41041700340508024010448510618061442d624a0804540001460300040f2283d481c2140751440d00c03000c0769040a60041062491400c0038840c2201c001800b034019009408600003841c240e00d14052010190b07611440f0b0150b031440160009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 859350161 1250 859348911 859348927
    0xf051915090201032703020f032a0f0f0319030614010c15050112023c0415080d032301030308100e070806100905030304091a0a0b1c020f 60
    0x103074801440700340145004926100d0840c40100804141d41c5203c9600d81c2034440e4906141e0100122002120500001c0d45802900710208000320000011004945820154070b1403185040000c0c880c020703000829224401030701001943d0701c1d07002410000c800741c0c1120600d4543c41c0a4810002203a02000702001005100b80044444240340e4004840c08a9580040c65105c0d51034443d1502a00e19445241c03079030380607801004081c0f221040181c401c0e00700c0c44801000b40c80749141c4244034040c07460011940d10a400d00050141400c00059559a20120800582450000789000340e060690300c04104580325622000442c040f01c0407080c3d12000c0303040041002902c00d80041d6071002e003400404020903262105d5004941c4162581c000084050007400101d2030201000c4031400d0807410141451841c0c0320100362a4007541c4102c510789552a40480301403000301820300800900200014166619a0300081603500458841d51070300c00860510448000d280c4202e0701c100d4000c84050b4204460 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 859351411 1250 859350161 859350203
    0x504020702010c080a140c060a060e04230f1005060406050a050d0308060409060501122109061103041d1e04080912151512010c17040512070f0519 64
    0x417100c00a410422003442c403074032006a44001d0207000e0301e43d8010703181038188040e600054480c15045101d10b0f04044060000064040b13102030b80c100c1c5010a80319000d8480113009007480e8050301340303448500401c220800b150100398000c500c607083c115000c122464841d024841c030314030a402901c0d0404490300c024008240034500f0781d0b5100c103006001013140240c07039642d0000d451080e80640324545107080100f0820a038205103216561481e110b0120440411034000c11400b1036100300c1061240305a24000085030520456024101c5421854513661101a100a05140403100e1101070440002110b6400130f012a21074090340e0015580e608014401702044142010456885038910030b40c5c0c214081e04413140c642ca4801c1c018190002c20382d031009007d004082c01401c0f1480c401c1c1c0d144c0f0000105080d049045a08a0107201c00000b040703607210b140c41850b03c50b104000e0607aa48010413102d0420240f2080c100000d80b24000342c0f08030b880c000c10091b001c40511071004281514062401072006c4c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 859352517 1106 859351411 859351417
    0x6041d0f040c06050705030c030403051c030207050d0e19081e2a2706010906050306030d1d0910050a0b04030809040f0e031c05010504020702010c08 65
    0x1e4a540c45001e00b0700140264410701c030000c07903041d0a0180800c25100401036160480f641d03542c0f28107003540d443d4211050521400c0b052052111703410f21030300954983c5a840001001d04c2c03400d00005803140011540c0303554111180b0700000c0520191980c111004002c0d840c060300100b001e1000207481d01d1484920003845034000441d4040040046d00841c2c0d9200a481e203040f05c4d0308084000a4410142030340c04011041105046040c035505101d00c02d01811007605c5890b600e940d10078054070180411505c8079810b410031102c00301c803e4010341c080c00d04980e0001d84031000b040c01310009a405401aa8489081c41441106015504164041e030002d045182516400c0924545d5215598030406114501441d00d80ca1140c00781030181d002a9000c6a104081d0790329510200a017181c0309020741c80401200c2c2c00c00d4000034484c00c240c402c840d00b8940680d1104058075141d19010b01c035074 = true := by decide +kernel

theorem cover : BRFrame.Cov 859172661 859352517 := by
  have h0 := BRFrame.cov_init 859172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 859172661 ≤ n) (h2 : n < 859352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
