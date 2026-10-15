-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4572
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:03:02.217023+00:00
-- url     : https://prove2.me/submissions/a3d8aea5-dbd2-47a8-9cc0-001ab73f9d27

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 822122302 ≤ n < 822302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 822123552 1250 822122302 822122339
    0x60207050604170906032a030f011404051501080a0b18042303030c2802030c010e0624040b031e060702030702011d03151602070b1905030903090a 64
    0xd541020b40001e807602100c02e95030580780190001e1b04542e5609010302c0402c9843c071010604008a000204009441d07900451150845443c0c5040d2035142082a20b1101c2800468510850a00d42003200b100006841039140342c0092a20251a480d4007001030000d220040c0b0342900400d00042d0b03520004113809441e40114403d6201000602c070282e40d40900d000d0b2107004c02c081e5001000852410f60908000d40039203400b0701c500b544014514060000704507020518079000d40c0021401c0c0107207000a01c1156100c0c2d0888001d170850386003100540c8544450114810b644440660904c004d45d103a5034400100f0800c00b80c00c5070080341500b5103d001242007031000c0c0c241c51180400151000d4408801d40d01c40703503810f071a40c40045210004104001e44409503454040c403c1c000942d4141c0010100d00e07002c0c02d913480f03400080310702c0c64030000e04040164105213000c0c2410007450001e400110a80004515545091a2203448544086003140700308044a42d2003000c1c188045000c100808094108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 822124802 1250 822123552 822123563
    0x6120106082506051e0f03010603050906100e1b0f0310150c080a0804020409151a01090b0405090c1308030d0e060631020304050d02010e3007060207050604 68
    0x2d44046103840d01c00700c00c0b80502c1000490600c100da0f42c1c0c545442c2d0700046040c01400060421a5518051030143c209078080c1000907220401e009000340180b000980141a560b0340941c15410103803480c0c00828090200d1014074021806007044c05405025180160105d51620b656810311543c004251500b03802540190082c94a0030344406000c0d00300800c5481d03010304c2c43e03401c08003114030540c1c0340c00000b8010780c0c220380c640901400081c1e40c05245180f8600d80900091004060200084c080001072001418040b580c03409003c01c202d402d00f905e003141c00c01c6032041e42075074414440f001140510b41600304d45c80c5030207a01046400020002d4000d0004010b81003007080c60f5100200c2c0d462400f0746030542c021425401c0756854481c800310f2309090103881140320307800c40032071701201080360300c111019100340e0044c2c01c000c880d5a9081c002d055451346128014100030301d1000c4c2d01d00d0200c0540600960094000c482030f581c8034451810388101c6500404115120034407810f0a0b42c0740c540c1100d0817103d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 822126052 1250 822124802 822124843
    0xd0f0902120f07151103030906070315120209040201020a051209010210020a0806040b040221160507030503071b0c030819032706021312060e0d0c0b0612010608 70
    0x320704000303510b20a4040460040600600d00040c041014201003034507030401003074a01804c2051700c2080154090340241c00140720601c1c114200030704031001e88131f406180c00c00b030100411840018010500c441d513011a00310115854510040c0e00e050b0b2603c1d4010440d02907103607860502d0f65204060502510300780c003036844182e0400c1c1c14104074419030700c0c10008540008007140b00c5086c82d81c096251040054001490440402e00038044c0c544030594902c0160102020030820b0ba81450659800110703d040181c14603250742e42c044c103613020042c103400c10042002c10764800c2101040303417010000d0700202e04001304c0361282001030703199000c04070010200d4820356402511038401e100707560141e8240050900700314180110390503002140c0c1e20695a45809100055402481507803400c01040b00c201c440c55064901d180c4141641c812070303e6404039070000490001c9280e0006030804072603a108900345042e580c0c07600041c01007403904400c21103c1d881e2400100c0d1106c00050801c03200d6013110142c41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 822127302 1250 822126052 822126079
    0x80f010b150c0a0b1609090506150d06152d45170303040b04080307050706110c1b0a1403030705160e0a0b03060c0a050d0f0902 56
    0x1400d03a05a228440d8001d100d5111041da40381d40007000c0c00b0200c14040948401c440603803036134581c01005079030010b03070403107416044900c05030050944c40007040f1202084c030081c9442000512101c50104414540000000321883e07802c10a0b07202c0d80243c64504030038520a0400c4134000d01a17000003040c407040080e07440031407011100c8480c9050141d28565030b01d100703420404802c0e81e064090b540d1001061000054080c0030307101501c654080403140ea021001c0d515141a41c5154107a60180004e08160400c0091101180002c81400d03406904455420f40d0380e100c4200c2211603214460018004529007401e550080203503034010702142d80c2c0503080324030724102c581c5800312883d00784a040f07a100000d240d04001c40484101b50105050008054a00705421500c58904080e1000d40405d01301584200510800c803804414035007003d6064410000344d140100480c0e900c11000e405107070909c00c00300703500f91203600c12002c80c0e8414640c240c05110011110304001c2c0a4038400d03200f00d02c501990424107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 822128552 1250 822127302 822127333
    0x80601030b010b0c0a03051c0e0a021809060c1e0a080603070f1d04030c08040308041d07051c06050418060b03030309060a05070509061c0b06041404020d0906051008 72
    0x83c0d40b9559008060554100701d65020b0340c4c503611034181d00020807100369410b180e840e211701c1801027049102c0c000d400f48001d02d00c10031048584009569a2001040c0240b24024000084540d4401041841d841d610a040030b003c110f14061f15440b4400640c0c00103501c0b012030340c0515150300885040e4102c13044142c964218400f441046c1c003556032154805c195041000340404a19508140a4180b10301911240e441c1c6030100e41c032035042910030002c0040c04103e152036000b01c505055050140d01071035400c10150003001407041160000c81d00e43c1800a40c00b1446140e0b0200004000003002000740c00d0b08000d80c003446240741c00302503950a02d890260146424080202d03403044020801a00c000c0c1e485a160600802c4094080301c00c000080c04124020b46a500007003003038401111444c0751008180000c881650010100240101020310040142146072898800100d01c00c583c0561500140c1140f0b1000304040c60025000c0ca00346410700403800d405184000c01d8070004003d8441040c2c40c005e01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 822129802 1250 822128552 822128557
    0x2010f0f0e0d03180206211f05040e010f18030912170a110105040804140d08030714090301020703030902100302070506010302120313230a030b06061e04080601030b010b 74
    0x64219a0080c0000000c454403a90044513805022050072074000c82030780105801d500080500700041060003442d81c066614081f4682d400380040c0680d0100b280c00800400c3e0a10440c81160f015945403c5004c0441c0300039000b407005021300060801c402c1004002514010700048002d82c081040c030800800c1c04460410700340460398000e00d80e5205600030030145011a48000005010451300040780304a040342030003000c1c025400303034411984982c18000300c580182c02c3c1c914802c0c4903814003034400001840b104180c941c045413030304000080c03100c14455207505120300c13581207a00d544009560020160950b0080c0c02942c0250f65409030780c00e0782170003a0100d00c00c1e004050201d40c800c8004100624280341c02c101010721b4802500d00f030200311707102c0c0f50060066410403c041c0201c20790758070481d2004550030350440c1c000c8a9045400e851510350940440c00540010300131080010103010091120b502c2621074501e01c3c803599a030303a58172403000361612000c0c0000c840c0e0414484c000210420b10005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 822131052 1250 822129802 822129821
    0x10930081e0910050a022119050c0a080d0603021215011509050d020a0519030308070c0c091517010f063c051e10050a09030f0206040b030702010f0f 65
    0x40c068441a800040c0c2e030942024000c5030440c4603007901f451102241c41b0551141c900348038000b507251200c0002d0791020b00c01541e01c034420458103000c1360160000000715141096040110140e94200fa8115140034202940000e90405244000000b24031800141c0e15020032400501c09016622038441d151111020000d6600285e03460100f40440d183c08041e19840c0c500c010700c8141416603d00c04a00c00f445c030981c01407070740080c813007040081c107400c030782c250350f10240d180b078003800425075642c40803142c11075401010081613a4a128480200f071178980000030700003c1c28160000074001346114040c14104034110303015400c2075000603001d1541c00068900c464034013601e0074880d10a00708451200c8800d6800b034009040d035a800145070b151444221002e0315444456039030f002a5006000700380c580901942c0421108002c107076461540303c109035007642d5009031041244109800018900c2c080c540260b44415000001c1c040385c16015817114402c40085142803208029000103030f412030b0150712 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 822132302 1250 822131052 822131059
    0xf10050610020a0b1005040504110333090f010e0307110109031208071808010e0c0a0506031602151806130b010510090f0323060105010930081e09 64
    0x4030030300d001811000d02c00d03600c0f42040c282040a51b0341ca00006054a10070349055401c4000e400800c040703400c091183c20700300c404046454403001049070180b840c8000700c00710281b04c41c0788807000c1003c840303091040401710103a61000b44120307105000b900d5240e500c26001101c1c0c001902c26a4102940030f841c41c001101e0304488070020340a2040d4059800d454000c0808007005401014a0710714a0b20703902c0380b8003500b00c4c02d000180c0071070303020311845c0b6108501f0410f612462131f4060070001580c0e40d600700e0750b0210340d8070300d860004850b049060349840310b9070fa905210101c2c11820450111201a002c061840c0900100d9180f0780311018003040b150b5011401500c10070380b000050225040581c00c00d035100100d031401402e40c60f5120003628801c1c0040d081241d450141722a003082d0b01e038010300c59004e0050f8080140140e13526200010744020094402c501c0030b00c24040a034ad15180703100c001610321824030820314491542d2490706100981c00130b14184152507003541203400c4001c20b00155000303420040e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 822133552 1250 822132302 822132313
    0x111030d020f1902010e15040f020d030f09051e060901090e1509070c0210030b0a0807141219060504060f0f0c030f0212010530030a142d0c0f1005061002 67
    0x87c5041c1c0c0010100910541d040181c02d050b01c00181c4032014003001e42d5001c0d5980e01e2507080c40baa801003400d40300e40e21603442074407090b454103051408100d030380610031012a8129aaa0b0010300180e0710340a130380d442740714000c0d480300801c03550035181c90211100c01c408407004040c0d03542e10a416a0309070510080690043c02510560407c2d81c0603034802401100c005100c100a2582e481410b45801c145030052844034840ca51103030a00e081050800408070071a0000d05110422442d4510b525400610041c044584a001203414001154072040355103042000a01218000710030b00d2000d0f1824030791000009181002c101101d01c2c41c4c0c42528080b2406031074040f4607902c1c00080041c5d8a5400300109080034444206080300031000c0d0101c40d00d03508030001755469401000014103a05124006842d030914108030307095004540207082a07100e8110034000300886100243c60a190044009c079007294454240e4020542d100040c1600811160000c144001e9482105104039040c0032140e00c000740c1d024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 822134802 1250 822133552 822133573
    0x20706140d0b150705011b0e0325150810062a1506030c1a0708041806080607030f0e03090a21050111070506100b03060111030d020f1902010e 62
    0x85400c000c030380c0c22004091440f2201408400d601075848260111196950380501e10003028091a040a2628071810174499642c070000c0402e407107035450030b104140001c00c0140c40c0d05244a03003d101000d041c01c80700600350109110350241c400141520101030062034404005600c81c42081c8450010121001c000c0381c401e11820121542000204201c031502c0d241000302c4002d201b14459040114003910480b41424a008070b86a089101d200d0048003071041007042c0e00200d28808111401c03150206800c3e042050005440b41c014041508100320328007071407040c0070903a5890342004500c583e28103005c1007802c0c42c0740070256407441740301b2002d41c10190740c010400c81c5028402c10840c0301200511700140e1403580b82c0d6040d003103500b40c84040501071008039203c0b0501c40100683d42d031040d80840c0e86120b450521041c826603000c0104203904003d08810118203415041c410750300142e000d0b0800b95201c54141006002e81d41101001002d00d210b00c24082000d10b00c140911101464001c0180c28511107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 822136052 1250 822134802 822134827
    0xd051f0608100504051221040609021f021b1c0b01060f03020702280801050915060108040b3903010503120406080c030a0612030201050a0606030b01050429040308090102070614 77
    0x2103030b04c9607100d6041d2501506c7e81040fa41040c4038034810714000030b40802c02e1041010803642010303205152400b02901442c3c1540000c0c4c0800c44000e0ba42605108000c9040050310840d00701c080382c0020300c00440200e007000201d111490580d000c940b41c05010b45440d1344120100d00030340300302179070002114001c0c2c1100c1c4e40d048001031405050300c0380c45c500c3ca0f4540c0543c909590068502c812654011410b0f080a8804140c4407a085842480c2c0b402d8a81041c1c4c0f00d05010100241040c0f202c483d54803418140c1c11b80354000c41da0101284021140c0b40c24100c0450382442d0800d22400c2c1c001c0c01201d117001d0315007404900719820384501d9141c4000545510311200701ea82c2004110000003540e807000841d041008280d400a407901c01d41c00810b06103850b10024040d100280e003c0001e05003050f1140141340c2e045400e503030907150f0707001000c503230482c1010030703001911500c5d00600c580090024012050140080050280d482d00780c00301d42c181c40d80c030401120240400e21460450351000d206151800c0e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 822137302 1250 822136052 822136057
    0x2d0c020d230309031303030c020306150d03030e0f16080613260906190e09060105070b150d05060708070503010e01060c02040e0316020a230d051f06081005040512 71
    0x81c4001101d0508000d0200c1c00c038007039000c0d00706901188e5403143d4441113207010410a5030000c82285c1c228003102624000c14080002c4040c02414180c48000081c007044041040d107008004501c121001d8046100b0200c2e0460407501458030719015020016a002110000f640120340d40542e03134a82071994600490005441c902c030300480d24108101400d00c07503950f02d019180c0d0507400c0925000000044001400f18403143c00507a0240440c1c0d403c002c00c0381e07040404d07106c00e2500404460300e2581c40d0b607015204103419294265000d517a01c43c2d800700740180040e502e4440c02d038a0f02e816005440e28103041d0b62602003446041c80000d8910b0050100c240704281480f0303864800703400444e102e00400c1c00780382035800007004e00202030b0003443c54100394608202c41400901803c800000541000032000081c05501b4547d940a40282c0444104200b070070131070f01102414000c1d8081c02d00d1804d81e0204060b10062192480300d114028030612901c03090b1146c40c1c041d0380c2c4a0010144030030410040400e54 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 822138552 1250 822137302 822137311
    0x5190507050603041202010f09080414010909090309061103131203021c0e0a060c050303070302160b0a020702010807020c130e1e01090b010b070305030a2d0c020d2303 73
    0x3801050000501601c07aa00614001c610444a6403104a0b071682c000707003101c400b03140b180d680c00d080c0114403010443c030728200c509032501104102a107110b00d0006941c800850b40c081e0803541e01e0011a4401c0c076500c45003039070580340d950707403510200c50780c19034913582c3c1e0300078107c1d40312505154000c20030103402202c00d40c4401c0c0380300f0b0050350800d20a11640046e0a1242007100020508000a1920501d0b002071060b014000900700401005140d07240c80355a0b000c010b200d142816400641c05039050140c0c0c905642c400da010050300c1c03080c07404117a8080030790040403040780810b0784580442c0215002050b4560740f0400074008440c0400b071968002c018184018000890707004600e0450b0415614000c0194502000d03400815020302a02e02096071007016809030038000700501510000070b900a08176a0004121000421608030413600018124844031400c28211551070703c00f090b803c500e0704880340700e140a40079546041c40c0410145e412038a0b04540500803100c1000245034900c429007c0c5811 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 822139802 1250 822138552 822138563
    0xf031201050429061b100608060c041a09060903121e041401080604020d091b171015180911040b100c0c031a0906070318020402070201030b33070519 65
    0x58003411104c103802c140d0780703007010382080751541f400f40400e507810003295411585005600b0301d003914041d0035031140c02c0c606820900c07200380007400d4809581c0b044e0aa0b100150004c1c281c50841880200d241d100b548400a0841000f95403404020441d031745100b950203c40c440500082c049004000460f51948010710304c51b4807560034040360810b200d01d8480c034030483c6d100303c0f440f208100c4104000c44003504a44d105030498000c00c01c000301034580c04181a500e8540301203000c540340c5907403c24424900c3e62600203419400c43d14201603009212600300d64000790040d03027403094004c6000d06100641c3d0210040c2500001150020311a042c03040d803804002038003400d03c83c003129840381e480b074581450f1380c1041c0b601c1c07035013a1060254154003844400d420820754201041201481d601c0c440c500f038074540c40648101d43c0800e0120941e400b80c0c00500d00402c005254006602ea0070888884010440603078080e40010040840e403008440021201c450340c005005041107560000600d44001d828542201c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 822141052 1250 822139802 822139837
    0x110a030605070c0203191a0c07170403060f0501211e230109021003021b1c0f0e060702040c0228030323010b0c0f03120105042906 57
    0x1180e50362107114000e464566403043c1109040c0101454214480866008010222266000520f0740c0c151501c44248001d156103007a070b0f5244280003070380600e03440a440390142916480c0603080020052054910403a01041112640318210342151070900461543c810002001144031400f0711807080321a00c917850f4106012a0505541c0f01400080d100322090841048101a8079002e9142d0303260249455000300501c0700b42d600059000e10450845805040d8001004003000c6011580790021000950881d4211710303102600b82c40c44022218042c000440780d65400481500c80c80000e0f01d0a00d000308180e00305081074013000300401308100c58100394850049000b541e0107514216010700c0d0400c002c00725450416040c0034013540c5212041c581122440070405040712039083c00c0a05403015100704540390300175481e0f4240352412002022a6a03c00851243e20250768812564141d80c42510140142c124260581d44002030310105a102d5003a4219041c1c400e0608074007030a001003041c5003441 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 822142302 1250 822141052 822141059
    0x2060106050c0705030f060105150a14090f03060702060403031b090506160b010b0415050301030201051c11070b040507060924030f060b09040507080c0a0c050c030706080f010902090d110a 82
    0x6c2c0380c1203201c1040c0c81030b0b0f08104010071051a0020444030035003841ca41c0c03640341440001008000b840c1c1c0e0076049488032000705000780161141c162904400c1400340881703125041c04500a5640c50084408400090500c0143d840e001d003005100001c03c901911140c00c0701d0b05003020040c2c40c0e000080c110b9061400c4191210204820400c0f05000b8009400700b00d540d6824010038241c6c80750480180c5d000c3c8041080100f0050340e100702202c0c04145a001640f6030120045401c0c40035141e0190310102d00324000c02c2c04001d010120002c94010340c0f00e51b08644010355503640a40791003801c0d224051074504c19240d0035a400280c100701d280d068037140ba00058443c0c108801c1000c81d1019080701003c44400f081001c010300381442401c2c1c028005041010841ca041d0320900e0b21071280c0c1004004008107110400c0c200213081142c8030549000030701b651801903c1d00f000800e01c40085540082c541ea480d000040c200c68a403003140c01d5181c0140c0800140d90b000d46071420124507500c0004d40021042c80000f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 822143552 1250 822142302 822142309
    0x50108130803010609031a040b0408030402030a06060801150f120813120c0518150d06060e07050a021b0d08221e320d060c03060302130c02060106050c0705 68
    0x2035010b09001d4031411000c42c214100547c440c0d05038829103155410000920002c116488211a80144e00182003603503561580301081c18507800202c020252030500310086030340c16040d000980c07509003441c4462409a9640011b81e1114000e100f000603e810380c80055002c28149002000c1009521402101c082d035280d00c9801503a12240040c1c0d501c030b0f8149414000351502c0c2c280e00240c08408040e50500d4144504a41c0324007010301122885070304880044000c00c005500880001d01480b28956124070f0710318400ba1290b88a8007425006004000440d401030f4400842c140503207401400640c800c2880384d54000341ea40c00000b0b205230300e0450340b00d4852604920030550000d4141e00034000e03580d2036004001c1805c18031325001006100d2600365101c0382003d10325200c2010004c0b003001212006409408a041e0300c90075800a032450303042c0b50400030400c1d0960040b00440c0e1080d42c802c610000260301e40000c661215a030500117030044801004940d124a002d4a22006880181d51001341c0c3c51002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 822144802 1250 822143552 822143557
    0x318021e01022407261609030830090d050901091715060102011808030406022502130203040f110a0504060e0603120405010210020325200304050a0501081308 69
    0x4403800f03400400704004040c0e6100140740e4551001e80106034100e064071a03884a400b1004003000140345400b42c035540b1440c800e40d000002940c0240405a4810a0003d01c0d0302c01c80646110880c0180303005140940c4401002c03900c1d2085006001030030215865000031146d036070000d6810303410415001d201060030303d00ca4121106c04040e40c4002c2c28400d071242800340308014010003950540e450043c030310281c82c600c0120018815445418cc40e42c03030741d42d0329007039009000300c4504611035609109818050308140c901014058000c941c541480d03d050180e031003da220803503004264440150f04100010300240e10080b062000500e9090081d0700c60010604941e001d0741b00740d14030f80b01402486618101030145200300c0740c42641052600b4204000030703540c1c0c45412444501c40c0d44c00800190340c0c286420304440e030341d49001502c0442c2d40c046000288130b0076046900c2102c203d2004503003000c0140c004215412500054104000c280c5440019169090700070050500410300310f007200c0005505000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 822146052 1250 822144802 822144853
    0x41a09040e03030906182d01020f040f090501050d0803070c08160201030b0a0e011a070f03080403030b01031e11090d0b07080903120a1a030a05010b010318021e0102 72
    0x550f03d900d004104c040c0703041c4c0c0140000d03403290601c0401010200001c200b925070450701c01d180c1781c40c000d40c0d042c8200d001103e00f0054030455102040c510841c0360301600610446182d00d2407013001a40303c7d982c1c002110801c0c8901a881141e415402c80021180400b645d40440c00c1d0074000554a800d44403024564010003140a128505120407000c540c6c00d8861440403100a0f40c445400906044020340240340600588410454203a400718064101c8400c840040b075000c440c1c1da8a2244a00d409082120207403400c4000c030382030100c8a011035100b8400e140d03414040a4081d00a01034411042c00248400595070100c8101003140700c4c4030780c440890f040412881280c0003034091401c1e40c1e00a0540c14003a0440e507440e0020409040504150b00080e600b01880b032000090110b040f420b11008680c148100d01d03014011900b61714203010040d444010407117000c3c5c07024024010490745481840350b990744000e52080c0f1480750b40900700802d0844102c1c0c0041801120741c1c0c0300c100303091000c0c0c1032819072 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 822147302 1250 822146052 822146081
    0x30e010c050d0e071409091e01050415051005010f020a140708010e03160b10090f061e0501080f0606091905011e020615150409091103060903041a0904 66
    0x155480700d808107100e14411100140007404003541413406105c008110359005a118801e60008900d0005090001088841c1c051038540c081054542007140642000c07102556002404e2403412406080e90203802c5c401c680450000074480d041030015038440d10711600e02d0b070440c4200c040581c0018400400d0f80815103160300244000381c42c1503010307801c0d2618104640790300d40091140300d0300039001c9040801080c0c2d2001d1011040d40d1114081c403004c2006510203400d42d400d0000c4002016001e6102d80b040d50403019406800708400704100403c5811072007a00e0000780c80070000340307400460f00070040c1c0141000703008d5031504444a0008080341ca038425014044150304408108568101c1d000e01041080b0b1071070301414090420029441c0c0c20014445185c81c0301c3d2085001c4659561024045030b080c86103140f6407155226040d0000914440e40c003210840450380b9035804910300091400d00caa01c41d40011890917003040240c1c580140781201e03c905c8040c050006401ca556180940d00c40080c07000e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 822148552 1250 822147302 822147307
    0x9011d0c09030a0c030c0801060f09110d0c030e0d08160e031c0f090509010e01060c0f121d12071503020708040e0a0b040b01020304090c020a0b040f0506010f1202010f030e010c05 78
    0x10b06001b43e0341d0110303074484403d5a14107601004140e02403c6000c0c02c54911207000600e2058071000c0303000c14031641420500c0d00d403811144082c50794240d40010303011460742c02289c87e2000000350a643d018030680c1d44130f00c1443e4046814903594455440300741103002c00b40c182c98142899500620f9107060541c0407001140c030507201c918003030f6400080708008100840d5449181c0d45003138504502200103014450810082d41c1a0500740101d00030150520742d44801d5903a1030080c1503100810381c0c01342c00780302c0c84800d0a81c989001c0a15042c0e840510701d115090180074103903d400201d0f40c9012055806205140e001e0000001169005029000a05a0020202d078900d4042c02c0c0754112000c183c0740d41d129520b000b01d202100c5c0d9001059505881400d88001a9080c2c02d001c1680b90118449008041064000030801000341c86030340625034a120350200c034026600e0b07038181c0b4408240f902800e0658501c1d2514440558410000c5050390380b1182030004004491614541c25a00c00c0c020000104800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 822149802 1250 822148552 822148559
    0x905030f0715110d020a05120411040c0509060d0b0a0305060a0209091e1f0b04081b01020d0c110a08010c020706020c0d0503030109090614042009011d0c09030a0c 71
    0x2e4140b80c100b0140c800c000308640c1819a2a9168601958841d2592940d02140d84820140101c00300c60300e10022488501840c5042c0c6000b8004000c41000e003800346040500c0d003030006025100342c684900e0020035841c02c010720300544400a000c2000007a910a00399400000468810700180e4002da10700305006da03071a4220424425043d074040d291500581c461088004003109941d0300642202c00708110031101440d8590020390207525400090380d008001030001341040d000139115011141648180122544040059132101940d54010002c07400001c4918001081030004100e0128010056089152141d801901716010f268a04000d03038481d140a02590340c041020a00f40b5000b11501950f0481603514251640418410414075070344481c98001040030b2a04041c105c480b5143c0c40e0340ca1460541007012800c3c40071003214500e4072807400076052505041c1d051505a0388241d10305110207041c2c10641100902c020a400d01c2003070180b00c00129550f0a200000140380501d45c2c3c410540c1c00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 822151052 1250 822149802 822149813
    0x602090d02191e06050a0e03030c16090b0108010302033007050634050904020415050406030501120c06110a0c260303220510060905160f05090f040905030f07 69
    0x83c04214982004400c4410080b86a1100480d42401901d1401d11480402d81c0040f81c03850051000880841c0a45a038444011141c203841030101e0340e140c1c01c148000c09051005583c0380d0002e0002a4040c2c004600c00e0035654019040113224604042c1209001c21059044902a03000320b441210282c206030180700e011410f90207104500c0042c4036000700b100c141544402410103121004506106022410240030ba495605444c01003444902c56002d01e01000300040030b0f81e0040c01854003080c1360400109040c8105034100c52566440003c5200741400e000d402e9075604040086d01400d40300315a0f00100145812030ba5000600c00c0c110345128039155401844104030280c0e240351560f50092080281240303010040c030a0080130fa0228603070340c1c80380c0e0030603d0900b0401010340d00140d0802da0300003040f039101d902c81032240d419280994034520502608945000c945035038030000810500c400310b11864175091410710150300800c00035542645682e040c3c20f43e0070285042d0700558000c103e003c141300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 822152302 1250 822151052 822151079
    0x1a031203090a3206271501080718060b0405010e19060504081203041109090a0602130303030f090507090b040204030b0406090b0f0c0412140307050a05070504020f03040602090d0219 79
    0xe02070000d444e051070302c0510300802d42e40a201040032000700b2900d903d100102842a20302103500b00c030b0141c0056840f0076480f99240c000d0712601203d42d05600c0350b60300d40c030400d100e92816034100c0b680300c91810749800d00445240b06407514079580114000c49200c44d00c1c0896800d034008100c1a1030b6191600d01d03100090782002585060010f03c10010020400020508800740c1250401120400156202d00c80307268035040c2c50304401844948006070070400b0030b151007041c2c02168800e80c0c0510840c503c0140400a6900034030004200e5030085005200000154000a10460000e080141030a9403a1941140f019080c0c0b026150035685e854254180b0a4220040d644045047c10b0340c0220b04100051041d01c0c4a5846110944549001c0110400c0b41103000d040d203c1d000e0b04100c0c2d407100c20b00d080586d11400150001c031918461070f07400090b903007454000d40e006a14008040c9086642d20f8071408043e600103101254015001c0c0d91520050307441d12180307202d01c001011480049803e0a03864106107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 822153552 1250 822152302 822152393
    0xe01090b130c0203160302010b0307090903051c114b0702030118050c280303111603030c0c08070506160303110c101a031203090a 57
    0x6042032042612910780400851100c5400c0c1d00c005252401000200d0031070140c2040c01d10700301d0407544404181a415008910300110850031303280050303603c80714030080329403481000700880e41c00e010540b54811744048081c1c4016105001103549210440003c0b25a030040701740b03203140e03d1034000d80e6945400050100754669004188941589541450000c2040b59800e400185940010300181151000c0d0083d01c81c50400505034190204c0500d81542c980341ca640040740111410400208410240101c903000c071003102920046603425520100c4804402990031101841801e80306141018928000d0b0000c0d07004e03948105803901316141c21400400545d00c0002e0651007070f00140310591310802250ba46003000300807081d07a030102d0b01e4140c0c00760904540000300b41c400800c081e180e032207010032030180350074400300100300c1c12965440301030050b0b042c9a40c0d16055482800100a0b907050600103640001018040b503007000042d54501813091407046090380000d4807807030900042001800c044550 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 822154802 1250 822153552 822153569
    0xf0504020a02060606031f0b04050301050a0902100f02030c030409020702211e150903030601090503070e01261b040501060309200d0f0b0103030216030b190f020d060e01 74
    0x141101044002e607110405000d0305c0c0b003014000003044080c084400c1c0d5010010b00382c05401a007654a801d891001d41103441040d000b035080500083c92460340d0b102e041e180c142c1c01480005940030360b8808a030f00d009040460350641c402082103c08044040001d40010441c840700940e80d016a0b2050100384060581088035a459441007202051004150340c0707281e031640a8000d50000d880d01d201c901e003e08043c00c0b9401085a00144105080c011004500c1801b007a00c84807445650341040c0b554542d0030b48100301c1c914403004014170410040040000350b98414070500e85080404000c0541044020040885040340301406080d00341401c1c024640108203038181040381c68001d0321034181e42c50f9800c03081265141c01d00e18040556580c01c0707002e0481c54016240000e049800e19010400e4a002e010650151140c6014504410b00501415059a03030021400600d1384a202c1c1424cca5424001036681c05610b91a203c80d203608140b01422003888510301c003107002890021032600f1440306800100c00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 822156052 1250 822154802 822154807
    0xf040507150f0c1a07080105091501050702060c03043b0603030d0906060906060804050111030c0a1209080a0f030e0c060a0c32060109151202150a090f050402 69
    0x41d00c40e004030740d264074038240d81030403811812186451203c0520180703d190940c94807a00380034403145c0c00301c00203060b40d6003514689001e443d14400c40c80202041c0c0d444a00140d020003180e070040c14084040c0482c01040c40c01c403828252901c0c010b160304008541009400c2403103c8850f40e000000d034075014201e401160020302642005d50100380c4a2280d035420401c140d45030340c03c041c100402130340f0280c0105400d0034104450707602c0e050018901d201c20384040c0c40641c20040c000c2c25100e004401c4a004a4161102f00e00d000c0b04000144d50b0110a45603488100e80e0380c9044002041d00000207192080081c0c1d120300341010080409002c984507445051080c4c0c0c0710303a040804e2a15008215010702c071003800d040d400040c0c4c030b2a01c000b081d446230001c03c0b010300a00120241c00d220424400c40090032520541c2c01c940e8a038210700b0225154401c0c60318202183c8035040098200f03410a044500f8005000190100c2c44000c440c0700550107080e403500000da2498040000202072100040913240c201e90551 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 822157302 1250 822156052 822156089
    0x12020702010903110d060e01021b0d02070315060305010c050c1006050604170f010603050a0b0703090308010317211008070f0e100f0801050610081315020f030f040507 73
    0x20103001043c000181900000c540583d240d503035507181118000c0d800709040c001d40f5171884145000c0d4004021412641070981103000816002180050807049542c0c010042c035440d64a40d10040f1107080c50003054a980e413040400442d000f80a85440b0241c1d6403100f541d22078450130b600d4030b04040080413861070381c43c1aa0600840d590103040350101c1d10600c19403074024100e0a212824403080c094081c1032503203401800000c000c404148840d04034081c8a070600503548498096091b074130bc4030300c0180000e0f0140010300c0043c83d0300084120b0341c03000142072030401c1d118088829a00020a070851000400c4004000c10000120441c03405040f00401070020b10346040340f40d8100c9080f5020f4031062058000000b04420401c101c2e080052156503240541c460356100c505000b0034055074141d024100e40d0081d00ba8640c000c010301c0b4000d0f05402d070140d40c01c1126482d40341121481c68603810507250200540104603218201560140780001000c1e11203007418600039262101c1c6500060b0f20b00300110b0f025 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 822158552 1250 822157302 822157307
    0xa0e1002150a0e06010f0303080108060f0a0c2a0c12150b011710140108400501060e0108160e04150603080307090b04080c04021c05010e04031202070201 67
    0x103104048950300200c0c10760301c40510441c050190500744503100d1141e0000002c4240c804d01100044138060b031500c0c80700381d07254074803962544c2c030032146858008600341c045410203605501c0b0200020040c60445408a0030700c0c800a43c03090390a1140b007600448031800e80c144003880c1640c0e002010540307010031030b018007560307050264414101900c0b00c00307903140c0c28000130f640545c0340e60500d061a816020441d1821050b0040c01484c00d0180350f040c4c1d50568205082c9500a80d0114014005900f111040ca082c0d50015a074549511440d9810301800c10141102c40241701340200b507040c4240700104082d8180f0b401c40c125080141c0c0502d40715400303520f00c0f480c0e0640d40c1030400d083c0c5e001480441c46c0ca0780c482c200318926040d044640301c80c1030310380840082401080005540100526620903940c1c1d0313a01c3c4100d0255000321700902c540754111800d503150318a06640204000080e1024a28004000e10108030480e1426400020301d0030745a420802056031100b400b410803030b00f00da011400e080264000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 822159802 1250 822158552 822158563
    0xa050d0f0210180c080a03030e07050f060c010608010204061205060303030705070f050708031603110c06030c0904060305120406080f09030d051806101502012304080d110a0e1002 78
    0x80c822036546102403440d0381d4103003004990050b0070805001d00551795182c0c0950b1100090b10903000245020251144810013045050880b8801007a042000c41c03540c0c1004181e600158034900159690440019220002e0002e00000c292a884115104040c507420f9011366400900c8503200b03400410406c10b115421030166a1104e40200c5001043c80551500c0c42c900320aa4000251034440441c8464810485000356000d083c426901c1c0450300340d050008558690f201c42040754402020301c001102c50614030301a0038145401800841c030380355a903c405051003e6a40c560b01207290000f000d109280e08603e4058002c1c42100c0b2134401803800d80101074032801410601c494041d01d0f0000b168220b001c001480c040b40800c68140d920600304003d030030045862501c078400d0300410200c18074042900610030025030072060f103050b022400e21503030307440200e4000400032241d06078140304200184965210b001c880c07004e180d658581ea00703c2028041c207410720f25503409206003809400390803e154007051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 822161052 1250 822159802 822159823
    0x11012a0609020a0e04060b18060904021c082206050a05040b0d092f0f03340e010e060d03020a0609060b15043308040204090803090a050d0f02 62
    0x20300180c001518400141c00c4402c590200d12040304e80e00c01e00080c840180c1c4100040300c81110540800a4005440f85c075101c82101e0740d60717118010000044c098203003000307000c00c2c9020501c1c5000034140c581e5180c0071190070801d501a0551000b5050302c10741890000c1190113400681025800d10300c807014020074600c46c070b0240914082022454181c0310315550081c0343c826611100b21b9204140e80c0e007101000f420742d094200d11a030000b46100401d4107140503814205000a000380103100e03c0b4107441b601c551841260f0000d80703552074007003c0515004040d000b0240400c20840f0f042035141c0096595282c0300589110311584490150b0400260000b8501d142d41d07030301c500041580402c2d8148040208035043d40550050b04c03034080383c1d4010395906d00a0003074034000440c210340d086a05c00d401500300e446203854004032514220348101e2900130441305600600c010030104400e0000ea58240103600300b940e0313003891940311414203005c01c8801d01404c0d510700507510b00108001030041d4004e603245c44821 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 822162302 1250 822161052 822161063
    0x80403080c030417010c080a110711030c09070807030b01053603010f06030204180c0302120111181f02100e030c01090525030f02060f0903070311012a 66
    0xa80c1c1c20201d00c1c00d1041d9801450000c0340c0882440484000a000e080b036440510000f4868100180d10b6251a00c120707034400b00410040350600102d59510308400e03c60003a01ca03414800c05008031050760b642081540f0400d42c0e41d940844230b0a000102605503458100c0c41c5051003014030100c1c1c0059280311081c00c10700d0342d0f020780c0340203d050441032000744000301d1a134035055400d1042c00310021220b9007145044903c01d4904004e803980315401410301a42007040100044441d2000700050301d48005001c510044030000010006203c00400c0030903400640c00030b240703c240304180c128515041c05040d02031154060303032012030905850000d440b04130280983d040250b845080400ca00d0081080d140b102507800c0003005550250300340700b07544410070084c1c01ca03941a983d0021300724540d24020041140e5004080450606480d42040441d4100300ca141c4844141802400800c2c1e4003040084001c0d030113503618070641c128110005000c14194214010034840c08041c1b11030040070780903800d9401e9000b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 822163552 1250 822162302 822162307
    0x10030e0c0d020d02090705130e0421170a06141017100302030a3e060702060c0a0f120203120402061e0c03030a060e0f0f040c0b070f020306060d08040308 67
    0xb44001103458407000406500701111104105500d07810000078013040000354524410141d03203040181611390100d0780100640c03e070721119201070440d1b41000c24080d41d941008200800450422106000200c4000d0041c6407240d8040009800c1c0101c101ca040005030b501c0071110318840c0002d808500120040d0301c2c840410400525501c2d44095158043c1d03600800350f4a540d5981e04110340c800300043e4010382c44d00c40081e840340c040082403d80c0c0c1c0c01c1c1310070f413003100c0100c512a0301004010303002044240c0c1c0101040080504010381400405043c03486200742c840c500410b420b14500c0c4a0303001a003003080d9401000826000060204403039070141e8104d402d560b450400d41c0010844070050f40110101280101d103600301d04030080091031150310074601c1000311542c4d80071120500441614208011740044c00400d0216007290302d000d50090040003030124a580c1e403c3e80c68410391014101360b42000b0030403000011481d051244079041101100c12110f40b6583d0380b40d64189200f10301c4001c0c50f00c0c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 822164802 1250 822163552 822163579
    0x30b060a050915150c010603060b03070305060106030c0c0c080d0206070e03100b042319110a030e1204060504050f0907050f0d090b100816080c040c02070f06030b10030e0c 75
    0x5400341400a55900700282d17440c4d100c018140e6010303203c580800c8a045017020907085241c240080c2c1401260740150050400d40d20301402a80100701c020030343c00030012a5401d020204508482030b4004090150080a10440d5514001d007805009010340040040ca09680e0702e4581e000a038010214410703280000e50102076000160050000700d0703203130a650103501a2178904504412203d40700d0a1000e82404586110340d4480c0b044904040c18003444d24400c2c05942c401602c00c0d132042da9543c0551086820406d81108204074641080c0e0003100054070024050085043c15280b00010150544628940d4108600e0141950107441405c540010001c108a1420407150300b0661031315400100c4890036040c40d8250800900c81d80c051780a840c404c095100394113665140c0e101d012141c5400107405509120780400002d014492413090841c810310390b01007a030894901c0702500078046610b0001d00b081501007446084030002140e20180751a01c2e48081c4c0d4440702180c041180002200c0b82c0ca0300111 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 822166052 1250 822164802 822164809
    0x301180902010509130b1314070309020907031802030709060906090b06070305070c03140c0108060f0a05090603340515072303030430020a0f050102090607030207030b060a050915 78
    0x8921b981e080e806101b130900103004042c15401a49541d1000c00722280d01c0c0d46560095080e52003107030300203412075074890024009174800e52100340d0110071540d07035004d011085e8000034503161040e0000c00080e0707503421080000b03680520400c00100054078042c0110345460340000d8480c05017050240a000c030000307640c8108030b4000e0300000550f61003181e580c0202c5030b8041541d075451400350000d020900d810041110307860035005212580100500c2074615a090405101c101d4101070100c0783c041c814900c000201c1c41d1140c00c5040305041e008a422a044c200c0300324000003070011f9103ca8020107258040f02452603042084480c615000072107140700e0308101d0701c01035001c2558000000540400720505c02004441040c0c00c401500c50340c81e441c0e001010f00748a40300313000d82820b030341c0c0541e2000803842c0024044101c2036038042e000e0344c0014104200d80007c2111070307015040460042c1c00482e024010440410300480c0c0100040c1c40c035842543c1803501245190340042c2c43c241080b050026886550394 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 822167302 1250 822166052 822166061
    0xe0622061508070801020903010f050903033103031e050c0f1e0c0a020a0b040f090e0703020a060203040608070813030516060f090642050a0b030118090201050913 71
    0x1203002c84124554540c0d84c24000e40107080114469400c0151190000c4d401c2e000d864065448000514a95103500c02220581c0c2c18005030341040d44003000c00442c1d80840801408801c1e8000c0c1c0b8082038101c0400031681d03542c00d202c144003030464507107414401641c1240d0306543c5410b032303002c5500b80d40b554040c0c24049202c01c1001e400801110000e620031501501040500c0031610a903490420302c1d8507041040a580240c1c01080c005002c0b60301e040280c071001c0d4000041d0f80f0704003c01e0300d4038291240c0104081e0b00050700400b000d6440001e0400046d94048826544070b043e5140c1400142084131002c0700344040749001030100000419075082c2c00b030701803450b40c100607448030041040d0b50010442c00050070302d03500c0a450b01c505d007282d0b0010018501c100d00900724640041d44010b074104110b41d00d032100243e511141c0007541c082e0017241a0b200c60280c03030098031031045000d480b580340a500700c0200b80c14100e06e40030350307061032001d60050341c109090303a890b0607003201c4009030030f0342903102c40c030081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 822168552 1250 822167302 822167309
    0x609040c062714030c0f1003020a2309010f0903050c0f031f050702010c0206090330071e0309232b0f1403010b070f060f0e06220615 58
    0xb12480c4a0010700b000c07151424103001e140075010740d08000c250b20100504c40d064400a240c01490040250360710511a500400004903a41410100d106038a401d6203c40600124201c0010b88000f400e803805681121203100b12410515185c00d40504554409883c1c10220840c0c601406080103580750564042c0440d0340070140d1815041502040008130101400c01aa04840036500e4240c81c030769140d00c0801d04d548070f2900c52000303503d0b005001601160000403c013a10340226128182c10700403034120704035280210030a903145036941822810078428440b00c603002c0700c149840c1002030342c00942c2d21209040407040c204042c40301d021940507150705002c02d42c030a49441703a20039600078040c0c540f01800070284016680d00c0c1c03c414801c1034410b4075260b00100d050019400144010889d101402000303000c20340c0700e03041000101c0c0b1141e40752401e80c1c1100b00842c3e07410345c0340c07400076020640070803e2661100d8070700340342c00f802c4a0421b001c4214040d08080941840e4644c0c004100b031181c0f008000005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 822169802 1250 822168552 822168617
    0x5090105063a180b01080106211109040b0403030b0a150810080706050c0f21090102030f0a08041502030606090607050a050d18080604030f08090c04020d06030b0609040c06 75
    0x1e001000c412060344503d8603504680070003041d000461009070500c40c840c00d88001c1c000c504080000d0030001150280700c05400c0380c1d14808051504d4403912080b9046008911070000e0446508091802400781c54080940900440488108001c4400003100500310119142042d500325220302c403c0b140013002c40e030003411051080d0600040c03055400001408078031881001c0e9100404140c000c680c480c840744800282e5420154410301d460f18221008200c40e182c14011249040d180d0144441c058010140c02804200c01408000c10f1010042c8001d0b40c0342c020060851039440d113040012032601400032041d00901c00070400c1010050104417801000d44c201c011100c41000714a40108603c01e0603040005400301610000b1f5102d80c0012100c1c01035a050b140c14041010500c0300700d030302d02c80050100c20345116690a542c2d10b51254030003041c0320300c415140400c45508504215804080203020180078944103020030010070800c0c50f11a0588110785003141081d10711802d401004000380011455 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 822171052 1250 822169802 822169811
    0xd1a04050c090f09040c211b090f111c06050402040321080601080406050717040804090c05040f0b1b0f15060d0201080403051b0708030405090105063a 66
    0x790410381030080c1030401800c681120083c0410001c3c42440c003426a0000c207401c0c0d58040078041c0f0b248100d0601c0c81c0381c0300070b12401444450754440341203150411036401c4c450030030900107100c6650280204500c0c800c001100348860b61031035500300900d03c116000f09403054142c4051160000d0380d82c1144005250041046d500d031500c03410a5450714035135181504100c800c07030245c464002d00070400e00d84140d505855800c0107a8641d01c032440940401072031042008584100c40300c0d1102300440c428040c500460a070307034941e410640258112401000c41e68180708050000300120840080da0000341d4502088554480b0000c160210501c40d18030310b0800c02e8041c20010340030107440042c40f2040c8542c10315120f0b04030b48803a8144203500c2c03083c1038081d00154980c400507000c00d000d00000c00c4c2d0100c0310b40e02c007600005141001820140c0c160010080d43e00300060800c00f81c6080d84410b4007402040b5141c3d0326110031001c042c5031120014065a0b00301400c01401080f02c20000380d103103907941c1190340501 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 822172302 1250 822171052 822171061
    0x1090506031501090e0f04060506062b0e01060e0606090f100503061003060303020a061d100e010c050f040e060a053309010e190f03050319020c060d1a0405 68
    0x400300140d142a02c3c00100082000502004042c0d146402541c4100300c455a41d2070f1511854040c100050126401c00b0301000031820003041100f40b120325504865010701c20088001a04003500c481c0b90b554062a8103104042c841c4611003896980c00c8201210035590f40c1c001c03100803810b403035040250254000510080d502c0c0c00340c1c1200003513110303440840b852407548001040540c2180d00034000640180d001283d05c0b000601740754030031b05504000310508280c150900600d945440440b6051000107502d80201c5011848240a801d0811280e41041402e002030710603031a0090107188148090107940f000454002d45903460250090701e0050a03003110303a02103120819500741140641500c403654103800241189950b0103903404440165a46042007819004000708000d201403000d401c524490340c005041a803a90341d03400258441c0c4050341e21b405010303031035109509060600c502590407509d843e02c500d50702c000c01ca80c8426003440c7c0014004002c0c01c00d40d0f41d80c100b8138800a401924020902 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 822173552 1250 822172302 822172321
    0x601142202120a2a031e0c05180301060501050702010c031112040e07300b030102030a060503120c030307030c02010905150a1805030301090e0a0506100612020309100203060109050603 80
    0x314401e0302c0e0000188130201d60100301c07803403607000f9210a900b210210122000120300c2034000812440d40c94401410318178402c1034440407209444510808240b0004003901000541200b09190500850082112920300300000e880d5202d0000001c1c1002040381807a005c25014a2822440b101c64000b10f4100318404050020583c0c040c0c0aa4080500c01034000303040c081c850f110440c400d181100070200b0040c3c0f4162000380f04079800007a10099920340744880c60b20b4a003480a18843c104030080030805614080a15082a00300140858502c8003044502d00390300c000011280c10032403614000400607550780049004054030f400041c028010500b0a4400000002215005034050902080601c81070b21000400c0a510a0001e010350024401000550f40c50f074450b600d00c40700b060503640039101ea56103803410400103ea407960303180e4001005200c569400302407981c0300442248210f181d41000c1031140e80d01d01038036040b4240c05400000188260b403148549100a01000c0c1c5031507128103122042c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 822174802 1250 822173552 822173587
    0x12030806130b0a0b0c21031b0415080a0612030f0801061b110f0904050a1104051306200703030219020a0308220f0b04020108090601142202 61
    0x801d110360700004118202120301d11541421540c014083d05825180ca0b000081e142c00548911740c09020f0b0f4808902c000440c0e0981100c01e00c0101d0005580b03140844107113610044d480342c0d00e03001807028007050000c1500e00d0205040d41249043c000450fa45014883d0044c4c1516000030010107400516101019044004180f2070059500d40c80c00036a2105804ca8080c1116030851168145510001c1c02250460a48a01c2010003600f1020482100c801164048030151000c440a900c038001e424240044407075a130900300401c031020f020390304000c0d003001c0070031a0040020b02402d6461100704048c0c039000c01c66000820130100c8081d112030b04e038180030f4006d41200588903d01d00107820392074511403010402c148515032503100d040141c0c5682e94100c03190203081d070240310051401d5180f00041000d00d1a2401c80030b1054281c14410300e41032000406c011409088540035074441310050000f4075082c142495000e10940700311008401c080a030080103034424504030b042d6440021118005030341e8924 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 822176052 1250 822174802 822174811
    0x80c0c190303021c050c040506030a1b110d05070f110103270506091c0f0c020d0b0114091902070201020316060e151e1510020127080403020613120308 66
    0x2014140c4e541d140c04550035a44100c0e494800600204410301c0240703013910256400c210913440c00100740b0f00c2001400c810241c14034060700414051003902e0403074401040301c011754000c286021800c2c40d4040c0e4a112008050020003080d004403a1502000d50b4405d5002450030540140c0c102d0044690483c030b00c5442440b0744050b40c60b4043d020001b400740100241081280b0b640c8500402d900e000748004854091040e5025420040c062540c44c0240c1d5414510f610402d000d1345480e2013030b500d02030754889112010859103010b004614100501c05200c01c0b519040181941c80142e510074031440101e0941c4035014200703060740000501d010600803194001034070030398900100c40c1d109000c426410a1180c0881d18110344062803d94004400c0c041001940c0100c0b514480d1160301800f540043c00d450400d182840060f036503150144000289203600d611302c0c0c42000e03020041c0404e11f40700d407a250300c901d0101a00400c00000c407095101c070022040e000900c0c5012080000d081c0350714005181e041b0649 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 822177302 1250 822176052 822176077
    0x7050312180111120402010309030912060515030613020111011d0709061205030307030c1b03020606150f03040b040c03051b040c0801081b0402040816030507080d080c0c19030302 78
    0x14030300c0342c200e8003030088900e91350540c0b00f80501070752140c0c011400f07490b00100071001c0040c0d81d00006035140d40f41d40c0012402d0311501020030b0b5403400d1107546440000107801d140c4039600140500c951040e2625041480307607021b02e014030b411000328000c1805414010b2880c0704012580c5da5a02c024a400305041c42901c0c0802c1090003c26a00c0c0510a42c100701490045c0c1150010001301c0c402500a60105e070003000c20341041c5811403c080d44400345065080000d4025821400801030f09241c4800004401d520900e40c581c24082c0c0076510f200a400020001404240c05101160901c015299070000943d801030441d071030001250002c0d10007052003041c41d406a03003031110704818140509a21416a18108020700c01d2100e541e800d130886810806803035170002e50820010451140c02e00170750800603003c0d0310b90880c49203146800c0d840e0000591204550350040f40c100c8800f01e80c001010382e00300c81680003c2d40c850342485004e03410b00807590400b0343e04401d00300b001010181c041e005001d0780501c60 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 822178552 1250 822177302 822177311
    0xd0c0e06010203070209190609111315020307031d03010603052a060a0f17100f0e07080f0a060f0e0a23010915030203060f011e0614070503121801 64
    0x240d005a03664003500308000e46c048414000200040c034190001400c2ca0403c0c000403032440c1d43c6420b280c040700d080d20f6201228002c0000c03030b41000c10000c000d1100038a40d07c0115060b120b444603000b522405141d034020100540703940810420401c0400000420702d00400030001c040d902d00d805a540c0290750500d01070350089c90711003221186900c4000f03a07600d4000d8020b82c9071031b5840000301c50310000501000103110000705a801c43c90a40c1d000d403485619500702501c0c409003000c0c070750b400038443c95000c1c02c4040f98a80400113401d91040c001a00620100b811900a80782c03600000301810094100e80c95101c588100011400700304681c40c1d018102020741000032001070b01c0d03002d030142c80d03981c5aa29089450f0004101060b41580324004400291130300c1000d0a85031350000c1d00740340782540c1400c84440a880140a150b00300e00301020f46070007100c0d0402c2e00b9407030000040c0c8408803040702d200d084000458a101803102c02c0c02287c00040400207c500d0b6442c0506680340c241180c00e110721071540c81d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 822179802 1250 822178552 822178561
    0x60f010e090a030e010512010f1701020309070603051905090106240905060a1110020d14070c0f14010f0504030f09081203040c030c060e030d030506011b110d0c0e 71
    0xd0000d01030003541c01c4005000103a01540301620412811401c45041000420840d80030140a0403294040d00400260480e284e2400a401400041894980700c040c0d104100b4060744810000e00c1078211140d60901003042d6075102144100140700042c071070368040c18070080210100065100c6005d46650281031020b0072403804180499403568900380300804c15110701840a4907002c009885030182c0351802c0303041d0722800c1c00294201b0003007902610020340c004c19130111100c000c0c014001d00405240548819191555000384040b81c05000500740d0200160400c05100c101c03a8000c5001004900038800f1200300d24050700107000444040e0000781e2000300442c641c034484d02100703044501c008000d141000700701241240b00c1d40040c004550708903400c0381c0040000c40310040701001308a02c0c0c480c141e045152500b810f0170b0103070f070b0190070080610f82000c2000d16a04001040c0c88014110032460000300d081c47c0040038140d480c06a5648010074101031000c000300c244200040d03400700762600d68103445 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 822181052 1250 822179802 822179819
    0x120112081204140d080103390b0c0c010503060d0f080f0426010204270209030f1501090219030b0d0618150506060306060f130b0702040506032e090c08060f01 69
    0x1000e00004100d81c401c1030641900440341c9450b030007081540b50b8070511000e81c0010840015249600440e09c4aa0114000c4100300080c02030206081e1f00b070a100e07246144c03680000c2c4110b05d103050000e100750000e92212041c06180401e45141c120007041c0700f42d031251210f0100030a048000d1001c05000143d01e07603040f8541041c000e0f5412244030b07012850312a4580700045410004500c03c801700954248100b6805550411214000a0b100c0000d4142ca10f0f4200c1c4030360711800c0c1608481901e43c01080003000c1c02e103810038944042200380c5030001c1c1c20a48140003c51400108a01804c202e0030a40d00d800d0407804030740c148202d503114004043d1201c01180d1400140e8104403a000e60000042c0002120383c03e0501c000c04501c0f06985c1107900d4591082605c41c174280c00d68002146001004c05d841086007454400d01707410171411001010022410007000c012011403a02d08102c24002030308100000741c4a4000b9000ca546c0050760290454035948115601d19045414441c1140c00c000001801d05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 822182302 1250 822181052 822181067
    0x1d04060f090e0c0913110603010b12090106080a110402220501110a02030604080a1403010816120f03120f11121003080405060a09150309030f05120112081204140d 71
    0x15000c1e160244a542c0c1c2101100b9504141c4400e44000040600a1000c0d40c0d071a802180a08100d682d5a031300e64100bd5240d2079100c600515061485e8504141800400000103901c0030482d404192140d54603201c0d004980a801210786400c09030082880301000216581520303416641c080e60340107400310081c01c42d50307540c0030701b108003a416820642c0428042900c05005189954040c107044260f10b615003060f054030b80c000d07031020070780c1c1c0c11414101c0012065a4003120007081e8207090381c0450b100c0d41d12000510070702e000004050000805441c0c01000c0039401258034040c3c802400c100c8a404121415030f6980950680750400290000041001200080d150180c9400605a078103140c2090140506640700c00100f400f4009d203244002480750300003c010080079204c0e50701080c6095246005003512804481410a00c0810b00c40b400c510b141d03081d50035045459000f84071410240741d003051541441002c101a50460025007008244010244180d0032891a00300301c500d20880c14801f1500c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 822183552 1250 822182302 822182323
    0x12080601052503020f070806041e03020c0108070e100302030a0f0618090302100c05090102163b01061116051804240e010501051c031d04060f090e 64
    0x20b118014100940864402500114400d0048801d8290701c054840e01c0c02040da4000344a03036107c0d408100412804003401c00300b8051202001044101e01c0c5d8029455003d9120000d04205010340002c142520078401401400790203045981c83c2d9140703a000502a510448091a030b050900a07203182d44a034500c10700c0100c80d00c10200c070300c00c1d450f40c00c04600907011480040e0b046110f024800c890060a41c840e0b0f20503201140c50b040ea40e0020341c000a8140b60f46c100040c009016144010800600721955058200c0070040b240140c03800002c401c8205500c81c401c1840e441c04440c4004200d090f0840c4001000303441801c00c8841409201c403100d0001c44450040541050314800c0480003100482000d6411a200d08008092100da660143e00b010104000348071040703448840d40042c0c4802889458090801075070342c045914102600b055000038506030003001c01a0000c245075541c00c002203c0008131900400903c48299210150795408001c0e001c0e105a5926104102034500000103806401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 822184802 1250 822183552 822183577
    0x12070c063e2401120813090b040e0c010e0111120a050702011419201203071206120210050d02040807030b06030a2102011d011a01020a210e0d1208060105 67
    0x641e0030034468601010f0100130071682d82a040c4a0110518515080340000d408800000542c1141440c108002ea66483c0c1c840c1401e50028510140300d41d82c0000403104004081c2003402c604100708104924051100514210701e40003c5061156994400001e0281034000d98551149420031b10104c403291041c030001107110b100301c01d00314840500a4003401c00344201450b02035610309002e50840d00b407609100e10203000240000c100407c1d150015018196240b0f400d01c1001a5030a001404403d203180308400303031242402540c8d8000e064452012100e01c08011081951a60703134941c22750303540e01800d0008880403099200040c200d801c0000b10400394503042001c4151480c9000d4206071621a4a010382d0115501d50340c5c5100c0e21800c10403070400c2980d105000181c00034200d903004410440404800d03045402a01c4068007003056a2414685100e01e00e005030b286c001007072016240350b0000c0580d1342e0012034110b51202407250341282115055040d44a050969644c100112098854904107584 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 822186052 1250 822184802 822184873
    0x2601030c05030d1e1b0506071d0108060418020a060801080d1d0f0307080106030b100f080331030515060411040b0904061205070812070c063e 62
    0x130702c0403003041e007503807061a942800690542c9000f03a141c0d510750b0004003551258401000d0040c050381c445032501800010080c00b4042004002c0000e2040c10003410962180b0f0320340042a000c403411908000b42a5801040c2c40841303a45c40b140a065103c00740b00b83d00d0f1900400300301c3c6410030b000b090240c083c0800c1070808603001601400700304210440112490709403080b0309010449810901c03803400034502a821280030b902e081c140b40010702010717400c180c3c00107034055410040c40c032001050b01c1420b43d003d03c0401c003c078150880c4241070341811070b0013422075402800000070700c01d0101d04031108200b10030301c68008c1c2d92003405003c1522805210b014503603608000401a411048010f40444600244003290a23607407001a92503001c0d0340c500035180c581100d20200720251b800c00080003400e004100306030400701075884900d0406c5c1240300d480140078246040503000307403407400144103195882c0203441001c0103d0356003050b21110080e60000a00c210b900e8201844a51062241c01c1c0071000c164a5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 822187302 1250 822186052 822186077
    0x30f1f1d070201090b0a0603170405090c160b0a0c1b0203060a0f1404080901080106090302010e090603030c1029090411150403030e1503060915012601030c05030d 71
    0x3440c0600414403021035682e00035040c0003855803a41203026a90b403020120f115421801c00503044065141140744101041004001d40e44400ca400c0c0d42c8824204202a29110000706998401c0d400c1c0c00c0003050005104200b011400c5580c0c0319054a442c00c0c1d0b2014035545405d88072910349044403002035456880300c0001244c0941c10b41100380354100b081c9000c82d80f4541c24840c9440304405441c2110580e01c08160040c507943e0001c1003600619142c41d1007070f2141d05d550006000320500070080c5000383c85141c00100661410001c6416030f40461046071540c00e20585400000c1c603881c03140ca120b1500302c1c0540c012030b06040c0380c0501c1000004240c10242c1e15a03a6407201e001d07007407116180d0041207500400d01082d0804016000450090315408101c44c60b007020000d000424200c29101c00005005115140e2203c5c0700d00d592090601c81301402c0a10f0410043c1c454030f048051040580720100045816800c1c89010941241d118000d03a150040c7c0381e00406071501c0501c00c0201c0041c00104004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 822188552 1250 822187302 822187349
    0x5030f010b0a0c1e051203072703060c0c121812051c03090b07020d18230604050d08071109060d030320030f09120a0e0f0a0902030f1f 59
    0x2584c40800c0751600301651403469503040d05003031300900c0003041048040108000c45400c440d00303078840038412110420f10900d80c41c7c1c01500b2011800050009984c1c5c580700345196003da9164040650010911000c40101034001814002d800c1c0880c80c811160a00c00a041848044103082c883e50140203080300f101400c0c0070001c406070184421003019205c40c0b2410214000350f00e02382c0650040c1d4090442100103901c0500301d16017000b08503d801d46a15001c02c04404203901100c8410541c590030110752042000286903030186810540c1d110040c81d480c032081101e50401480d8103841113002c40075550740c120410040c980d044903841c0d048031044200390f000903c20740c0642808501072030701c08a00011100512465002110700c504425101c00c240b22101030200148030380030500d50a0a880c0441e25100104001d10f1080d104e030090900d401d80240726a01c0400e64005001a101e0854aa1500c50142450242c054a001700030704151038080780a1200341150805684009414202c80001d03d07218 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 822189802 1250 822188552 822188573
    0x3070c0228060f0f080f0a02181306050108100b160519080d051528080d0302040312090302060f03130605010602241e0c120705030f010b0a0c 62
    0x1c070308039034101610207500381a1045915024080640d1408903010300860701401142621480d10284402041005441d0301940d09065010150000150f01c4101c0e400070720f0848540310842640c090041c0e43c00f802a2999039000302e044400076aa8400d20f9140c8500f80000c2100c940078044144608000e00940301e2079942212803a1071040048840c92400c00c4803130308210070f01c02c2003203030a90b5000440f4441034049019041d0011820a500c440c003240580014404118a18240c101c4400c00517001494072001e819060040404100341d82e07000c035200000500a40c041d001c12a24103002c085034500c0c1c2841741c1100d9064036405041d82d1b140206e2179005901d20341004150700c51030600f01c80030000044581c002c0354000d2003030360014100c880c0c05041003248444c40d140c0d03030492280040104001a801040324014124502820102e55200d8038080c80003442400000c5002013864000e00c106183d001c0000c40c0300d9201003030308140030390701d41d40044d94502c2100e040e080061000c44036000480c41c03048a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 822191052 1250 822189802 822189829
    0x1d0901060f0915090e060103020313030e0312160c1e09020306060919050306070e0a210b1e0a0b13050c09040c030e01050f0105031906141303030e0303070c02 69
    0x42114681e0765503540f00601009a01e1800002030204104101898500c81900d070411030909096045142001c0305019207051a5009410480c0081030310380552004d0001805001c03442c03c0c015070b80e010b10360301901a1207030040308403129030b074041c0b00003019855955640e032300d0403629644100c050310b0560641c001e0740000e010300303030f00c031004010050440c0d5407510710410716501010182202440e2204046c14030100415240511280b00354103119640c41c01c80900a44584401000381588075951503411000d140324018a410000740c01d01050941801d201c103510840c04030503040c20b40c7d809a001c4250f401c030f124041d801405011035016a85980c0c4c00c216805800000740a04000c0c0850010303040c3e600020b0001d0202e41e5803a02081024001c0c01200d5101c1150b48403691503514020120b42e440390103594052040ea0b4039500341041080f20b0300140c1d100c281c0c22040c2c40c861304110602c25041d504c141030890201e403600000021005000c4140c81c843c22258403a6480300c982c0d5000d00425408241 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 822192302 1250 822191052 822191057
    0x5031f1e1e050426190f020708010b010507020d17030403050d051f03080a030b0a090e100516050c010b03012c0105071b02010306030206040b1b0a0b060d0f0c0b03071d0901060f 77
    0x30980c542110b0000600c400d02600340c6d0b511000030300480c13000e401d00c540b030342040c1c4999040420043d0540d0300031302228034055050301e18884500076070401189940e02c050303a400000d60008180002d0542c0320000c0d00e000030100d442005641c440d00c40366058822070004440019034011010800b003880c240c0580708003001c0c1c0c100460b6141480340007071100c5505400c00410503a884041c2c80c0011400c00040d00c200d00101d20811903410300d501624900410300c09100100a00040c50b9070007410290051502108040c009000c034501d80d0410202c8a0b404003800000c100e10048008031052050142c24060007094a4190101442e078044c0c8082002016059043c0340d194400040140c841c4001440180008500c0c50341b207503241051800c1c21030682e88241055404841d0303801c081103200503000c1c3c00c4401286c28080c004240e15288103c07503230002016180014500c80002c411442c1d200842c0f05070362540c0d504500500480ca00714903000405410f0740c01c601040014801d4500407404e0014405003030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 822193552 1250 822192302 822192307
    0x30702060f060f09040615090207170a0504120b041104090c140a0e011403160308030127050412021c0804140312070f0f0905031f1e1e050426 62
    0x300b0120790101303c241e40881e0705580d9029007000340300092075814040c0c210310300152b24182d00c84c5c03a004159900100100341c030080c0080d030562000c0c002e40440b0021b080d209a80540d15815041ca400400350031a400e1701c10064840c42d803503080c03409106005d8403e82c4084500002810056210484c1560b8940307541c00141c249808500b01c0300b011001d50082c0020300101800071401070a140c184045410440c24103480c0700c4d014400075a444080d40e0544072080145c40d169096101040085040c11907051300503442e00003880144030a116640d42050599002c0f00d60444000018040d10804440220000340000f000b080005001d0541d5440030f0f180d0504032030410035400680300142c03005444003c0881c8560040b00317031560b0042040310b41d820300c0d4180500014600000300703031120520003c01d455181c054251680c0483c0c194840034201d80c3c0d9010002c5841d5140b540c0310000c000d444070072040c8004550711031040e0720550140f180326543c402000c20349220702d00c035000c10b1110007030b02c40d00103041c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 822194802 1250 822193552 822193579
    0x21f03020d110721021b03010605100201020a0906050408191502130e01060305100e07023c01110a05072126061c080903060f0906070203030702060f06 66
    0x2501426030740780b0801c440d09a4410052078040801c90300b01e40c1300340c44e0810f502d840301c01594012602c01000c103400303041101590358040009004020355000141e006103189098010035905502a105111941d11012540c940365002952517000c6ca2240100f660311800e200031440d121071281400c240e108800c827990411503111000c0903a0448440f400e254080d40d0f40400201d00080c0186d40105028201006242800d500c108440500760040c8450110b002c0003160754a4800c1044c0382c5151055903018010042030311440114850343c1600d030119506048a2141d2624103102d58025800e45002c0c02c1c0c0b40000507082a14240c01948050301c90070840303001c00040481062000010640e01c0e81c50800400706d410f1a80100d14152009a030140360000c108030140c1c54540d003002000002200b0100940102e02c0c00205520038008900c0d014065001802075400201c0b20f410f010340c1484003540c1090341c0f030001c01c80c1d80740021a54200160b0107403020078014001c2d1715400d0b80120000d03003403210344884e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 822196052 1250 822194802 822194827
    0x510030c0e1e0a06050a05070b070203091905240403031b06050f162606120f030c0c0102060403020d1805030a14010b0111030f0a232104021f0302 64
    0x11402080da5482c110701c04034016a260181940c8050411030804a003030903010380c0020014028158014104041400802d0487c0e0080055840088000384407221744d02082110660019007881140d00401071442d44d500e8071011901024001c920b02c5140508082c45c54030304442542e540c4040381c00302d0300c6a14900c804600c15003c0e42c0c1c81260000703404142e42c1003504408840b5102140b5940030010104a2040064401110960b0341e01086410104584034900000da500381843c510303440c5445251001c00c001c0101101805895503c1c2d420b6034090b003071a00041e616040c0803100100181c00c100308114100340988003100c400d64941560700140f5844501103403038288840d9096a222003003100c07044c00010300340601c003156402841c000c084540001c508071b0b40c07401100000c441658001c17400c900e1140c030543d41c103003003500c80340b80010042400713443e40404e0741c0c4804264230583d4040e107000320204500c0c0307040078056a40030b800c5004080d1000da069090b1001d00c811441015000c0050000150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 822197302 1250 822196052 822196069
    0x602070810151205010e061315240e010302130c0807030e16120605061f0c080c01090b040326070c060b10090f2103181a030f060306010510030c0e 64
    0x44c0b00381c0c00050707480e02090055280c0140203041544500350384801d02c0c0014510380c24449160501c40d00841c01c1500d02d1442c1e0343e10300300050030420402e600c40001600b42d03900d06802d0f040364000d8840e183c540e00c0402180e026600c07100440000718a40300c002c158000d01c2940801020007400055601c1c144101c014514140c49551101c82c0004110032140180700340e621455410650448001501da20301d000482d0300d01d10390129010a00948130307120800d10001c00101e4450035240c0000b000031040515201016100a90f4141c0004412003640e442d0f0400088408050842e6030305084007540d43c5400854054414107000c94050b42c948056203d603442e440c441c150400c640740c5030f2510640c100081c105070600643e00c01701c17040296400c40308060400d0900b0541e03140d010315112104205aa0082d9218801c950042906051070100c040c03008202d54080c5002e0307002095004603545440003010307680c907428080c59038030070f12103100d81c01064065886100081410300345010307034010040003c0c1040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 822198552 1250 822197302 822197339
    0x101b110d052d0d0b010e03010c020606010e010507060203010e0f1005010c0f14010c081506030105090114061204061b03152c090c0103200f0904090b100906060207081015 74
    0x551140030100117580c206501645141c1c066000b00b0070752610800080d5282d40207420103043c00b07802c0226049992040c2d04607002c0c02d070000003d66880d40d464008032540c070011100c00540072100e80c0425035070000c07009410100c43c0165105412030103142c071401c07124281668102c07800354000101ca00d5203c404c0c0a20801c05246803502c070041e2400314101010814044c221a20510f0100014010781d5104100c0c2419035801e112803080459401000c20311611800ca050424500d140c0f042004210141e002560320b44050341c407030645150300038419020349080003851542c6060800c0c2c1070203100c4c0d46454210b400c0d2646c0d100c60201c0c51b8100b00500e402c10081d034011181c1d800130030b004400f03942c02d4011074100e41506820a0850100740b0000c5085024401900c1100ad00001e00c40e401341d2f407150811300740150401410012801c101020030203201141c0f040c0884a81090400200c0700d00100b0b0107021511140081c00320a5a034000501c018550440c01c1c022404000201141490080d2400d0f43d14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 822199802 1250 822198552 822198577
    0xc0105040c050a060906140d090b040605150d02060307080415091a010602070509011202030a0803190606030e1f140705131203051902101b110d052d 65
    0x14982450140709150311160402405e000300e891041028540c00001400300c2001030b5000d640301c5912850600280a00810140c94202c0e00010710042c08215884135005100d504054003814040d10309000242018040c003039480380d002e000082e03c045c01400c426601c00e104441c0051103811021100c004c031020f407103094442081c40002106110a4040100e016295500040c4a81c03454480042c2c030800c01406600c0503640b1051510b811520104102001d566219000ca501e03403034915550454549070070050111103003003d8000a500e4042c0c80b4207064145054040c0c80030070028022821440d81d41c04154482558034469190003d00404000c0e010790f240303650382c42e5106803001c850000c240e8036400ca50b00c0c20a4448500740001e030031504544110104100400c6003802d1900c0030303410002164400034070b0301c1c00c000158560038000300810344000e401d80c42d40c6144003a820400c07659020342d0800c100c0850001c0103250340c0000c01e0305141d4000d1140d4130119000340940040d01c0b04a40000c05908407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 822201052 1250 822199802 822199823
    0x1020310081605030c150d0203191d0d030b0f120a031707050307030905031b010b0a0f12020d02060d0c080601030e0604050d0318020a0b07170f1e0c010504 68
    0x30814041c040c10a07140c030b502c036010380d00a080ca0300003521340080540e0b103481503030303219000d0350603100000076602420880c210454072413422820807100000d2004100c4402c500d01a904942410941d68040c14400e00e00002c01a000351000c0650003492403c0c0007640c0309c0750321350100c035240e51400701c0025982001000f52144081703070700e005400d0403031079140800000034010422180984c06402e40c1d42c00303640d51030045a4074615023481401c510a040c0e02d20b01d0092244070038201e100c0150820324846009480c2c1d80300066075402402000400c074011f418001da804070a110240c504464414102c50000304000d00c0d0860514085084952205480010800c01d1040001668061007070007009404100503118926050b640c0c952111860459501030540e60901400e20000ba002a01e0500340d02508402100d0f8882c0c3d616003040c0c12220f021101000303480c002850403060710701a81c0c904003510380b10b28104066070031521103603541e100c000d1031140f2090021036501c01003405605e00440c080c5c2c00444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 822202302 1250 822201052 822201059
    0x10e160302010e0603070516020607020904110a090b0102060109090602040e0a090c09140f2a0d0e0102040506070f0302010b090c07020906041116110d05060f01060e0d02061303020301020310 83
    0x1843d280d00c4800440c8500d0b028001c200d8601e1f00101140e8401c02950742071815040c0c1440000c1c454020020082e4100c05858100000c002400c1c80000d10386104440000d002d9640d8284c0da400d40f0803c44082707005810030313801004a020b494100a010354401c0c00d01605140d103d03600d1403c074200850750070704000e40391361071081480921108980500302c1c0304000d00039003003006940d48905401612902e540744201d000034101901d0013010f24582502c2152a03040c402d08080c0b04445500541d906288083c0340401141c0c10318014800c139421220060080c9042024a459002e900404e070340059096541700c50241c031165680c020100e02c00c0d00b0030501c081d240c180700d00500034910300040c8140c2c0503d10380800e000030b006404003910643c281000314054070a41da0719142c0c00303421020080c0703900810140380035001c214000c10742510984403000905a540c0e03840070102c0d03264400303c5000703030001c0c0c15040c060f001d410064003c10800e0000601c50350159540e9011a0032a4001c84074071104540300314090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 822203552 1250 822202302 822202307
    0xc041803230a20070303050f0c010608034018060b04030f060b0118050607140114161e110a0507141504030b15130e0105100509090717010e16030201 65
    0x5090b60f100340014003000d0304595003d02217218400040010550114440c00314441c2500300b20040d03d42e81094070b80701c0952820340744030924460019510780ea01d103c5624180c440f045211101c1c2011007100d0840301d403502d01e40c007540c82c1d0440300504010f5210cd80200b0a545640014001180310300d400d000902d68500f04001126624030744103040003c0c004006103409000d54440007640c03c122941c960310807003864210503120b0041c10501e825428881164055040052030324400c500780a002c0070074282c0d402c401c440c0f003000c0c4549104030744042e07510410030f6032003044e940000085079011079070904141c1d1599441c002856021900d104109240c404550400305004c1c851540b0b0904220704090440d51a460003000060409a048a03510a0003e02e91b40c2c11404441510705030000700002a940d1199901801701125500c03515040c2000020f0b15081c0030b4003c910030808003001d80380b91420300011b03a04071802c0501060f0075648818600e40d04140030b01107440d8045000d580b00380c400e459403001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 822204802 1250 822203552 822203597
    0x90813080a06050132060c07030b010314060c07031d03030324010203040513020a03090b010b0702090610051206060910050d05070207080d050901120c02010e0c041803230a 75
    0x85040030618180ca021000070117491110b040c1c283c1007190102101d102c0032840a004890724054a4494540000203004c00c2c09084e5050301d00400807506c6c0600545401d80c0c0c3e611058504641c102c001708040000310340700745a03954510070700c0380c8200f451086100000707123190402d0741d655016503103600c012194074880c4c04c0500b1075414203002560409183c4070000300c008910a4103c1c1c1c00e035030001681c450103807180c1d0140b84110b51020020305156140e40d4050041d07080f207603040740180c1000001c241280b40a60040c4420600ca58a251920950210b450100000942410340101040c40b41349519680d10040108424040c0e455035258003400000c01c003a103001405050a5400c00c1005004940010806540740040c60400540c1e174401c0200498040c038001e045030784d0346031418010101c805c1e410b4011007464101d0300110b94003030308480d081004460203000303628800c169001c0322800084c0110520301c0d00015000112a058503601ca8040c901e41c0070286500014904400050185079000b04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 822206052 1250 822204802 822204809
    0x308030c03102702130b04080d0201060e06061911032d03071e120612030e0a0e061203070605090c100203030121060b030109033f090813080a060501 65
    0x2501c0540f8604070004090740c010b0700e0b03241c0786182c001412022401d0469034403c0100382540000b03a8955940f81c5030740c0c43e12080c80d800e030015400d00d0000900949a6020307640911030041c07001d407520380242041c0040d601045144d405100c0b030030fa03102c0030001050020306240919410300020420044803440180d000c1c0c1d903a040c00802c418410310110310350000640e40c102e03d668025840b40424800309495070210192994012030501c80c1c00710741d0340800029501d16601c6601d690303c68030144c008200c2c4070848ad02a84045210a03c000b60b0a03103000384031034070340811020550f490412240c0341d00c6c09449040301c60400560203415056000d0628203141003040000c0d1001d142554144250720407003246450300c0010b1100702540301002e0121a51100c3c05401d8001c0003007010041c0c40c076000e446071442052420640720283c00c00000c086001ca015400c0030551038070300454080c20b2000c2070007484170080c00c1d42c4003c424071820651602c0c2001c0345020302100002085201d46c6403038194241c0c1c0c0c0580 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 822207302 1250 822206052 822206069
    0x1090e030313020405041e050304060e101202031902030a051519140109080d1805040b18040f15020d1a010804150e0106090902040b0d0201020601120c0308030c0310 72
    0x41000008800381001c0c1602c10382c1100d003c905034540741088120404445009014919900c080302c041080020050080b03412903144c1454032294101049828140c0c940140041584509505103201c941c1d80110350100d04c804440b1140b50070b01d5003850403070700102c80321850f250307884e400d220300a0304030000880d00000865012036260240f203c040e12220300751190010743c555110491100f82e0041c04030702c0240c080c03c402c85900980917100103001001503110845102c83d84000030410341018040d030540329002606400822901c0c108480304040d00520035941640807a0045001400d4000c100c20603203821040580c41e603044901d403030100d450400d1440701003140381010345400d98205d5800c90780150800750620400131140b245601400d600a000301300b075440c10b0404110f00405900541c48a03000b51010014451084244007848002c100c010b405039102400400448101d1000d4800d903500c142d43c150030140e81c87d51600c180360410354050010800102c10480e0694a00e1100130081c482417 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 822208552 1250 822207302 822207307
    0x9081c02130801061d130b09100e030c0d0e030a0203071e090516030902012a0b0c2803110f030f090a20010207171f061404090212011401090e03 63
    0x1105101880b4031134020341c01c07032141707040010500100d1105041d1744980003000d40045143c4400302c0d54844a44c080c90118441c075080103148508000410341d80c00b4440c00d0001d0180090340201070f00c0000407048002e525205014941005840c10301c00d280081c041c0ea2544044000000c01d802c3c010030345034008008540c0741200300311407002d081420b0b0842e240726082c0055030590302e0004031341006c9800a001c507004040e100c80800c0007502c1d01044062400341141014541f03e044094001d4806d00c1a80007440303040d03445a0050303031060140006e1380400c40c140000d8514503860605400e80049a0601036403001204104103840048005940001020003914200c4610707600e92045039517001c008480350039031400300450750f4001c00c070810207000d000102c403074000c1021104a0b5664400c01c04901001624580c282d1003d015001d06010b80309a480464045901482444010051400c0030703070340b00c4150401c00440500a1084a42000c1a5580a807039036061140220075585503110200305603108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 822209802 1250 822208552 822208559
    0xd1209080a080f030a150f050103060e0f0604110412150605030c1819050a020d1b0912060609050a150501090f03140106030227151309081c0213080106 66
    0x34808540c1600c0004154503225182c120102005110321a200034280340e41906c08146114090300160803220241c0e01480407588448101140b079505840e8540c40d0781f18000842c0c61490550000000780c0c111503422401c1c03030b0b92400c0e00d40b295501c41605460308051a1070038000390f07525015150107003205a00809140400802042005901c00c0603150200c030b031017001c03926850503006405031511002100344141e00b003a0b02014000c1d8441a12504010325003840402e030408542401410b41ca4151903440c00d19180c10315820900003440e0f01100c10b2940c8040100384640d1500c41d150080c0898007000850340c400380b444c07920b03200564021134148044204200083c40d014404182600c0d800803007042c0c1d1146640c1c1c60703400340525800080d4020302c082100761160440304640144020845005005071f100d90b000044c1800741c0b0f80c20160170001c20b110710301045006411103000c40e40300c8c15294ac90800782071000d0642c040c0e01070302140d010f5000544050405070801c0103c000d0f11400300200180392a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 822211052 1250 822209802 822209813
    0x90c050c0604240903080a050a09050303040602030423060612120924041d0f040b160210050c1e0a0903030c140d0509180912180d1209080a 61
    0x80100002e12201110b40ea0f501c000305031245a624015011105011080003440c0c00780000804941c220040740c501800244a5440d9010703d00243d41c006000d180340d600d5079111440a58401007040d1000018089014211000301c69104400c665000203031215041c00c2081218249041c0d0201605910040c120072806d030310a000c0f686c4080c0111101c445c1c1594440c1e03841143e10104070f200f20001004100041d10300d0031103d121030030001c002c03500c003469600d80403134411914003035a0150452407a800040ca01e01864200c0b4854200d1900444204c0a031214003a020b42d402242c140d198414040b4a000e404400b0010503500000710260160900340700c001c1c008d00b00b000c1ca20002e0104200c00c0d600609101c2262841140145400259147e0703211103c1c018003a130b44184892805005014031180c400c0d01e280100394015180000580400d80d001804548141c0040c90340c0021861070a44494450b5200905580c07050310810030042122001e08025016144070f0340458040d4002c2c4160300000781 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 822212302 1250 822211052 822211063
    0x1e12021216020a0302060a032a17060402070f030e03192001110610150c05120918040609030e19360e0105060303040b0d0f0905030f04090c050c 63
    0x501c0c2a000104460000442107480350344040e411040002c1c02402655058014441089444608010381920200c44907010707010340803040300180248403041020f1413502203654100710024005402c00303c0648590040d8003451104030089001007c000000e401c051200080c40d604001c400c00e0b82a009031108490380420409095030f07049050790300f0b41c0ca03a01036908a43e11440e0101198803a1504c840900210b41c1d65009031034149980b2070080080e14810b005104016074048080c2846901e0280540d081e50806403207180e000b140602c1030112003503182d035028482d0f030081e500807a191010303040140c00040d0600c103c50050303074605141d907003982c81070b1890740407500b4000352000c0540b2948100604c15448130051641034044089c01d0000f045543c000f8038400a440008124a80713802d020182e40b849180f107013000c00c0109000c0003202c02810741c0505465542150045481e0035142d80305411070348092140b140d00c180120301440500030310b209040f200d5030541806482d1600c2010038503902c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 822213552 1250 822212302 822212317
    0x30111160803040212070801050712091109070e040c08061906201c050c0d020d1d040b090c190309020f1003090507060c0b09071203080a02071e120212 66
    0x1070000c085411502d982501c070140c0079004c000d8030680303922034644a020700400d0380d14000107040106a403400d074000c1c2c0729201000c0d5211502025090000d001e03c030054000400d0f090500502141e031f50010340307490152010020b120b0b0364103412071030b120081064107840b018a2640081c21001c050090310307005813901c190a806404a201c044020401962070b01a425101541c50322464405005407600400904068030b420341c2560f00303500ba14070049945620340300e55900000c0384500746076980c00c1c05507960000040040d0010130074414503404110aa20242c9079140440000504500060800c9858a080321500c3c60b0601070740c4610f030001035003001c0000c4114850b0303e08010448007036001b9402241b9a55009c819189201d94520000e8264801c803181501c0c0100e504000641440c40450b04605450138098600011411070701c080705c0c2c4030002444a03003071a90170090310010408101e080d00c940300c08141c0703c0c04c0d0700301c017440c000740202004d90410303003590f000d1034800300e142c00c0700c2081d180c0c0c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 822214802 1250 822213552 822213563
    0x6080c03191d010f0e0c0f03070f0f061403010e0714070605010905090c0111060106110709020c0102071a041709010311030a0603020406120c1a0d1a03011116 69
    0x2a5112803288881c41030100940807001c1d80b405007080ba8618054645030481051800200000306900080742c1c04d0b624a620301c4075040e0081417994015140c4003550100355900030307048580e1507455203ca40051030b050b80111100c10030701602080031030350145520907206e201404460442d45031001c20191540b000c1d11003800e10080c25045070551a6060030ba601054200500780046d5071760300325103002410b043d203842c2500e002e00740c05986994010072880c001015640001c1441d686041c0040b00e4406070400c1600031b5020301003001980000c40e0025002501c1d5030000141c0c1c60002d4a002c200c03003e5440360001c8191107a00c00c00000c122140700c6c03c203503285040c4085a88202d800c004034000c01c0d464480d0210440040103105c0c1e4a0390300d40c06201a40c0c0700b0f41d4104134994039500c44468511407000028102681c114003030103da13301244440c0b880c07010300122401c0c003804a045c403090301d03e100605d0380d014070030814000b00ca2509001c0c4030380002e5502c1d0440e20300602c0d0300b84041d0030324000f40003401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 822216052 1250 822214802 822214807
    0xd0608061014040c030212040b01170a0c0312051314132c03040f090605030d052701030b0d0f0b06010f0507020d050c0405040506073005150603070504080106090606080c 74
    0x15401703501260071000d08125103501034607044c50700b20b028540038040c1c41d070141ea4a00700c1010303121000641050031904190301840d0145590f84500c0320101d04421f2004210b010320140c001c80d451140410301800b02ca140901d80c1110131002d004008509800310030410f41071041e922409054641d1b49615809151210b044000001108070324511507680b0182049104460000386030241e0b40c000016280c04500350741d2540804081191705000e104100111144008100304054444c03205019011106040100c2c0312541c440c009070104c4045d50041d42d4007423641150700c04000f10350042c40c2d032000c001d00707200c3ca1030012000000c14a00800c00c0c001d0142c02c030034128000303110b010840c0500303d2a0062040c8002d01c0e2614159031150784c02d0b6010008503080d8100c400008203080c44034040c4011035003403104d800140c1041d013005014003503c0280c800c62200c54040d5a51541001184902c10079158296940e28003c822800c6840c03560080e160646030200078080c49034421030382a0002511081c164 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 822217302 1250 822216052 822216071
    0x405090f010b0f09072609031b010501050901050d0c0b030f0612210d020405040c02070609060f05031303050d0c09140603040213051b0c0a061a0a17010902060d060806101404 76
    0x43c40108480e41b0581700381c0c05000c008154000000418901c1c80c006607151044800304460303400d840007030240661100b80800107004908044032075410160180e00da0800803030b9184107c41c020f84c01036a0180018a1201c108005800d0070301006145034500c4008000000300388026001c10100490303032400008000030504000a81901a140a8040103004000c0c041030041c0c01b039550361b00b034442d03103002c03030481140014054080d013580916040140c80e0145155515842d400c0d1140501c10201c0521800380304e0850b02c07001d90311585080084d19250410218200312070307150a294641c56092040c0d104008110058540760740d94101d44040040100d00da484442640c070303202072180030741026050007180d0507160700e900080c075548131800f440c01001140440b80c9000d00c001c4c050403a01d034014000aa0803ca0700c0b8119000b1451050040c0000a4446644d0700040150344007121390001a91610700c20310840500f84481c03500f000c283d16001410518001840351840494050584a0f81d601c00608 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 822218552 1250 822217302 822217337
    0xf0f0d060c0509030f030d141302060f04080a06060315020f0f07030c0516060e09091f060b0c1c05070506040b0705040906090507020d030e0a110f0405090f010b0f0907 73
    0x43e030540c03070014140c4082c410400303c880d64070f401040d0552041c0b0300340720100080200c029000ca0240e00000301011101d001c40e0280700403540004400134000c2c40410000810603402e00c44680031500c200c1021a500707155090030058004854416142d080c4100300340300d40314604c03100310b40e4140021440740f901c50316141416500d080c00c0d094058003e00800840c540409440840242030b646a81c994907a40c0c910f0205102c1f0104045801c0d4141e0b0348840c10340d40600106428080d070290380b4070350100b5040d0320388203440c80301c1d0070200181c07401e0b601051012405042ca12007425140301c1c0c3d031400741c2c2400f041c0d484103540c1d80340c040c101624452040000c00c034654462000c0b00c000c0d11080ca024000955141040d4004103030440340d180041c011645075101e1700c1d11078081c41d64241d444d800100080c1400340c49a10b04000b002000b550301038500e0b5a40d1000d500c0e6402154882c1d0041c9010b030031000e4a644400c0e00b5100590b580900ca04440305910060781d030f07a0041c80c0d8000d502803400702c00c0c25401c90b106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 822219802 1250 822218552 822218557
    0x1011211621020f07050601080a020f09100519031406040f1b41030303150607050f071814070c0f020910140d11091e0403020a020f0f0d060c05 62
    0x4007038196000182d2502c00241c58001004118850011290160b0fa5041c000341c5031202044000d40c000c080c0246020740f4980150286c0e0400300f1102d01d010000e0b62100040c001c14418486400700280001c0c08006108074090341501c42c0c05441c02624052509954038410815182c10043c90100110520013104240702c5404002e0f1540c4030b5000c0207800c10b20040c040101680c09182072140300281003c5c41c56950160b4081c00c424050011425070304e818485039054205101c0e00c0e60030001c18010640414801c10047c10442d0a00300646040c905100031000d80391002a07000240300c0c10401c030b000e070380840c0e000c020781e03c03614a10702100340d41500e182503642005c070101b002c0c0d4801510000d1100e00c0000000c0ca9040314002812041c80740310364030034000704582d907260140072500c03c143c243c0c03018100001d40b290b21038420450301a5032080b0703883c01c1240c05001e440030b82c016407082c009001142010544201c100108840d1410301000301c0001406814800350700500564891159040c2c0c075004200303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 822221052 1250 822219802 822219857
    0x3040803030403090f12030804030521010308041d01061e1403090c010f020d021c210c0318080a030c180e150103090f03080910112116 59
    0xd40e0754a0809060003400300c2c0350b602071346440c2d0f040c00c1400206817078408152035003580d05403101041c981c0c1d15202070781e130741c0c200003a00300581803403110142d280800011118061485a40382c1620746083c00c501070586034000b9035101009003294010b1001c42c0e000100b058001c070b103000703d101e88100d07160001c1300c0b003102c14114106800008001c2c020020004aa200f114000aaa4005010500000c200d03600c1d03d05001c0c1f040581c2000f40c50307440d8645920a40c82d1801c4160400d0100f641508100d0300201d070b01804e256100300c3e510428034440d507034540521220070498011062070708440342c4800d00680314001c0f1480c1410380d1040e50b50040ca0054000c8030a007100b80c000068019903949203074201050444481e000c52260392583d411702c0d8001d02ca4105820b800141808151105a4050b9079a40018200e4802440380e0103400d50341240321301583c4410409070380950f84a441c503c400b01408204400002412200c040030400c911000d003a455400d01950710b0010a00454003d022201000020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 822222302 1250 822221052 822221069
    0x618030b041e0f02030c03060709090203340216030c09020a1808030a12110403031b0b0403090e13050d0e0607020a0807050a090209010203030a0b0103020d0c020606010216180e0304 79
    0x9010307414044a0a2a0f03030300c03075000b030b41a031b59016079110425888410403503d2101050f01e0010500038902c10ba40919030001c00002c804000c4021020010503404051000c40d000c03030032581010441c03940c180aa038003d050441000a095030555888840b00c00c420700680c01c400d580450b1820344079200e62807050000c3c190a0041030105e45400c44541c0302e81c0102440408202e80b500c1e9010800440d210340b030b40941101224908060844d0340440b2440d00c00e4042c54010250640d0400102e0701802c5418092403181d1035041500745048000385d0390850051003d180e1a911100403000302c0c40101310000d104025262030303141986508002011809000800b80d000003c03080040b45120000540c0401d6410840e0419041a038480300841640700c1c0c0d604141c01600305001241d041010794114841c1010705040c05814400095500811a50218041001070340660140034080d601803008070000e42d80c0c480c511400c203040810003107050800309104500280ea8121086840303071b0900c241e5001d045980d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 822223552 1250 822222302 822222353
    0x30f050307020c121b1f031107080c0313050f01170907120803060f030f1c031d1b061e070f12091401110c0904060e010c1205010618030b04 61
    0x70841951008009151714100265030400c0ca56841c14080d6001182c0311540311020701c0040031022030142c591401200b032194814010343c000a102c15018000010003078004503203c0320781500d858034944080d40f003907025a0341c403550810640d0307201c0c4286165400c104030b02c0640ba00d810390103d10308a0329512540b08002a8018903040009620040d400b41d40100c031000030907201e000405403a0355001820351029400740f040400310004036980d0405030540c9080008903204a8a0484003203a0328004018054005044601ca0364408012140b04040c05448540c14166a100c02d0300c601c003004902040c1203400401c000003000041b642c100007a661050101095207005000640807480e54011001e00c070024018040045d4410243e803001d15034100d000340710b00402c0c8020300000080241c019100e80e9100c10f00301c0307401c140174092080c0d4000640e403000c404003002b008040c1240c0c41030b003091381000090400c08000c280f5809042d01a030350480c0102000c1e40325494822151640440240944c1505 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 822224802 1250 822223552 822223579
    0x1005010818100903090f14010207091806060902131a1c1517060109020f0a05090d0c08100b0a060203121003060921020f070b0a270807080703030f050307020c 69
    0x408402180e4080f1b41d926441601d4404000c03016540c010f6060069000000400881ca41504810741042000b001c80152104036240c40c401d031000354002c514202e1f000a82c25151074003400051000300b810380c01c8400e0123004901080240d200316041207010044400001c0b0000b144c9901070bc90865242050001c500d0350780c80c8a4600c0d902d00b680c407604d28007803800006002010b5000321404000c8084440340b1340060094161803c6c1c120000890308007131005d03001c2000500314012078020700403003002403005090464800003a503040c5451680620350050040244640000030350707003d020010034070b825681d610b06004898440f40d60029200c0d41c06c0491100038850281284902c0103080b1000f405074204040050380d54444c84140c201c142d6100800400038613012201074400c0000c146400051245e4119050204100c950b13580c0c008404c000d1420002807100b04201e50081a5050261200501c0c54074082d0640700b22034034040234810000b0006099500c24080326214100007404107041064 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 822226052 1250 822224802 822224807
    0x303040b070f0b01090207020109260d02012702090f07050c0111030a180f1b0801020f0301051002150109090c120f12090f050d05331005010818100903 66
    0x10702c40050380d4501a2800108250b20280202c882d001e406840720500d061419100b03001001d02110071160002841080d0002c01c40c00703100035040000507500101d4204d001c81c201c0440c164048180d000c554804100a50060b10390f403d0b85d5a1100c4400103184c80c1c1d41e03c03014240d4040c41040030020300d551800703407026410f000740c01c05180565401c031010882100000c0c41c114136030031413800c0500400c91807101d070341c0065104111a5103500502108181c8981d80b00104d909980049104241806000c40107000c181015102d44110301d44600c010520f0205010b80a80803580c18016101090745501080302400609005c80c402810f00101e048520144d0303003065442500c11080440302e00718400c15945a80e4400e4604601b41c440760f0508030801440e01c42002000c1c9801c0104032068020807a0f10b000000c1d075107284051140c001c0f4200300e690350354010200c042d02401011202101d0301940c052005903804070f0103503807290804100c500f515008081c0c0524016945104d641d1603410300450004055 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 822227302 1250 822226052 822226073
    0x1a090d032c1c030210060e011401050a081302030705060c01150b030709060305090f0105071101050708010b0d24140901050f18040f0b0a0e0d020a17090303040b07 71
    0x38000c044028400c001c106801c07040c000c000c09a42c0d10180303524a114501d402c1510581c1018803d00444035900031182191040d542260301845034461b07003a00420505042c2d0642c058480c80034038095207072140188000d00b0422018100c0058583c1a030540002c6440402804c00078280080c4a503486512403401c0d240606207038842601c540c003180c41f0000b00414224203803401640d16441c3e080c0c0240c140780c800c40c01050028900b01c10741c070490800b040c1ea00000c1c441d0b54000c5450355100402c801044503e1401d44101030070480400203070800400c2400c1c2500181c4580d450000004036540040030f000488001a207002d1119008107080e001507080c2d07042506500e040b405403010201d503a40c0c0c1040001000349040c16680100700f4a018408007060b404c0361a90152144e0900f03807941340a07450f000320300c803800c4030404015551105042e000160030012640000041c0c0300511030f01c10140e54040358120095924842e098003c80c0079965a035040c0b0a0f10084c001040d802d588845007410400c4040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 822228552 1250 822227302 822227327
    0x3070c291005010f0201060b04181508030a020d1b030c14070f0f0909020d02010503061f0f1707020c01050c0f060c090405010b0f0906030c070203011526071a090d03 72
    0x981203c250106036006002e40c10848d5032007026141024605141c214450704501c03074228034240d407003900c0700c407000c44185c100c0301605e806801141c44060300007010f49400310350301c2c1800500100e40f2002e5078005894280148940c1e042c034005a0000d80c82c5820301c0c001121400e0b04005e8054000c0c003088000303411411900301c0c0c403c1c1d221240c80342c0d50b421102080b1500e80300b000e504400101c83c80000755000e0001190041e2000d801d02d8040403624041082400c1e00300d4001d00052001c11100320440e81c841d80d4120104600c01c03403100603003805180a540ca802075001141406008203200440d194203004802251050005407510761402e20101c0b25164402119507114510f042c1c0042900c0e030761308050700c2c01c90240c14100c40c5418500420400c1c40c0e04000c0001d40c0e04001000080c0050300c0c00e020f980440110420503500b041d050030b134500f004004480415800324000c00883d00c0b014030003c1d441c0221a801400d40e050200030100b80e40b258403d68080c07a8001031b01d01c03140010558051440302d42d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 822229802 1250 822228552 822228557
    0x140405060601080a0221060a030804030f0308010f15080c090d05030d24120213090f060608030a05070807140d0f02060a0203040807020906031f09020f030303070c29100501 75
    0x4a42c3c0b80720510040780540072034015501005c3c5251500346d114955a190050300050150521a950307a480180036441504212100391400484400b003542000805014249038591036000c50300303020386890700b028000a00410801c0040100d180306501d80100c54054001402105403074403a8207000b988c0350701c1031074043c080520b400784005000c10041c0b5041c8003a03c4171030b0700780819460a2102085250340c100243e0340304a0040300c2d0110078a0b01d1061a1119200e101d5402618005042503030444a141e4070000301c0c2e0f00204010500b9640c407100301c400c0340d50710592140d260341150034002e405910000003081d092246980c04420b0300d1b0070040442030506603074200c3e00596240000e580aa02041d50010802c080034048000145000c0500c00c0e48907174044e080b141c140e840c041d0050982e213170021500c041da65981c2504001d40c01d00640003580b0810640c0110300e1070030b2202c40100702c41045070002d03180901000145011010032041b00442d894071102d01d8010f0b0500c524800c07844001c1c0d1080602 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 822231052 1250 822229802 822229817
    0x70308130f15090311030316050c100c0e01021b01050a03090c0812070b1302060712050c010f0e0708010501180e0a06051e09160605090109080f070f1d0403050d140405060601 76
    0x6007114008200d2340315110070035140b4400d02c910314096607140c00c0404100114050241010b80b03401c0039214101403403031280e86214507404248000790820b40c92000007515060a03982c1c900e01641c10070111085580390f031500282c0e45c1800d05148150076000d030001200c81c000c085860f4000310b010300280140310300541100303031a40c55007001030031203500ca034500940003201482803030041104080100c616031140e08159142a40c140c260508403004500408803c9a0390f00d0b00b49050a0100700300710107826070000802c81ba50600030300703084429851001d440c555440d18441380040c20180301e440e03c03081c1d0010040c0054105110254442580c00000b040310800d034038000b03034025000055003d40950b00d1165010200c1c2068001c903030580c45100031905001046078006a8000100310103403076101c403000641102d42c03c144600d862200e150780903104032100003a00c0c08800c550754100c40c0e002039043c103225903203468140700030b000f1303201145480b0b041e400214100300030f0050118910344190700998900c0f1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 822232302 1250 822231052 822231077
    0x10e0a0f0302010e0607061d0d031406060a03060b070b061009060806090a0b060a020303011e08151b030a050f07021902010e0a05090717010b070308130f150903 70
    0x51a08148192900001441810805540908500c2070b60400203400300e0314001043c0c9401040d20106038407903044040014440d04c0c118030a101c2005d0b0101d40c2e180620034483d2348691040c89002c0607160611907040014042c015038042e0f40114000d020b8020f90301c1d15841141001401843c08036040703401662000d00e1300c25424444c0c003016003076505a4540c2c0686856490a00c00040c100a00000741d003542d40c00b1854041ea524009007070f400599034000d65a80d81810102d601b10041a03c42c800141c5140d0024040c1003000301e807404e0f5070210191030710203d9580b200c46515504110300403a4500c540042845031202c4180c100d20b10440e55003590b50580e403241c500407a41c074542c03042103c10070299440c0ca07400641c440d4240c54001c2c1402031492440d252607030002400310905880e1134001c0b0f548001503401c0420029400c03070041c111034220505164140c2c9002c0d056001c000c3c000e51815284214003020040e83c20190130440341c0200e954542ea5802a400d10f0003406d0180341900030420141d0103a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 822233552 1250 822232302 822232309
    0x50f01050705030c0c010920010e0d021c0309050a0b0a02011404110402070203011e020a0206010e01030b070e040f0e070603110415030507121a010801061d0108070c20010e 75
    0x180c0209460b80c1c882d46541d4852007010443d8010455450555407a20f00c0d400103d000e0240b070321200b215207842003000151a4001412620011003050b00460b031f08402040075036031f40300c1401190242030011225041c803610382190b0020181e0081e07640b00c1c003840030209a080762040076110300f007115002080b016900280007001c092040314018080c42d8102ca86c3d0706c0031f05094000e852114809030000c074000c1c07082540c5c00c114070781155260740c4481d400f14541084581c1000224010b101d05c24003052107505584400d00c0a100040040b81404100a6162035613201da510855a2250388882040b0055540600540324100c038490a000241000c06501108a0b014121011101252592114655680d1047d0040c110090034401803000c103080c203c000101e6801048100c211000d91240301ba1f074000009051000181c01c124204034901c4c03d1250081c034110002c503841d4209092003105681d4004003200c0b20401214018852a150f0610b03000301401c0b20182c1042113800d8135000420b82e10340c801d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 822234802 1250 822233552 822233561
    0x71e1707030203190c05040911090301060e07080606071103030a0815121009030c0215030a0f0b0102061b09100201021e0c032d0703020a020906040213350703050f01 72
    0x28814541c1d2030750341c150700804c00c503030003041040c9103070a1072400c0580d681070503400c54118003070300c070925000010900624a0207109040180c20110a112101e09201c40020f0281c4002400030b40a180001022028841004583c2e408a50b0050031240d0700c0c15803510062a200d01030340c0314000888001102d420b14a800b111350b0400140041c0181410381d03000c43c001002e031031300c1101a0184400142d095002d600c9129002c0d035102e071441c416a55034105000320800f101c002e514900b45403490b00c950074860b07aa01080c0146c10404004030200d5401c0c2c840114100717886039644042d03000e8610440900d003130f40c0640103440c0200340c2012481e40400c0b422000451441602c040001c15001003082d0040d4910000404103501041c0a80c10b1940104145c240c1842e0710203642900503034030074101c0c8403c518014405c154005011b0f03506608100b40028038420100103400f40c4042c20403a040d05280c9039111003041482d04241d10548000c03d43c16002042d11040a80002e582c01d0103108040c00808105018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 822236052 1250 822234802 822234811
    0x301140702030d15050a03031d090c0714100c12060b09030307080a050705100504050610050f0d02010509030706171303090e1503060a060609090b03030a08071e1707030203 75
    0x1641c500f030020825100100101010b1080d034510400c0c0205060700c611400354041d610a031529918103141500c00318403000d8054025220700a00d030308201c0c13642141c00545a800344d01441c80303100211030603102d60500442141015901d881c10b10300d4503400394068000208081420000c10689446c1c46005003240304c1d2581c084e030143d000b088110700050158005120b0340c07956260003030404001d43e50b06401c00b0420b811841802d0f40b9082400140a000d00c101500a802d07402d211a030245040d0100768188126054030307118110190180c400d59004104446800c1c0c03004042d600340d25118a0081c05000c040c003012000d8080007000a6842d22100c82c00710300c03850b00354a82030982440c0c54280319050b2002060401d01b0502001c404000e600d0803c45d41d030007168800300128510b4148480101810f4090f48a600c00c1c40c1400c84014554501004540d5990254039081ea641d42d92020160b61108070040c00090f010507850003e0041c0d64411100c014031030442048180c0d035202c03a80d048003a4002500c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 822237302 1250 822236052 822236057
    0xb040e030c0606060a022803030b03010b1f020a020d05070f0e100905041a101703070213090318080a1a06090708090f1509070803160b06060706020c030903011407 71
    0x210f151440c02c407015003444600b620458442d0708040c07800b0001054003a03800914842408251020160140140a046082600204400701191000405102c0b40c1e0940c40320320807a24000c543e40c01d00c00d112841340320f60041e00701c0e848190b42d450700c103964403280c0c42034009141c841035000c60249500b04285000368510903080b44084d080031402d10007024094411962050801802c05000780400c40180c440c0c8215003004005510703100d0100107108030503402e0758036a04100011001070795011040d0317520030360103007001034103080038a030a070b400c0b00c0c4c2d1007042c4908154aa10016042c440002c00c4040e503840b407512001d075850501110b10361800f0541d0003903800380307100340002c5804d0b114140d001d42c488a41400c8070070f4031012070512420301140d42c59140032003045a04000c0915800c008810080138440d004603c0c0515081c541999080001070081001680402080450b0381e0300c0251002e0641141046544860304051140ea0ba8807089415001c0d508000e120500480705120441c03082d2801d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 822238552 1250 822237302 822237313
    0x80a021e0a12050d0801080d12050a020919030c06090b040b0a12051e09030703140c0c03011a13090c05060702181303140a020309130216060b040e030c 66
    0xc04410180c0d2800c0109190000c826040c000340c0304851071903203040d0303c2c0100c000d40811340000c3c1d0024140c140507003026615500800c0104042c5500400c500b0030075000c0d100010b1305445041c03000c400782c4504855164004200c0c1048007861042007420340849205002002c42e8540e0b50324251482450380c854491186000d00082040000010050960320150310304010701390703d54183c1d170007200c0c8250b400d04403103c2c440d03c905840c441200080b54200c4218030045d8100714890750001d00d003128480040300e40303080100703030010440d00c100401005060002c0080c00035099064100c1624104c080120780314000101c2c0d80f8031090b04500c00c0180b801c0d00721100c2c0400f64208014024a50322584049800030f41401075214031400c100c020368010086450b03540d000e151541002040700364000c1c44400550781c108040f07840e05d50000708640701c0c40341c00da03801c1c4c90718240102c0c075074006e006a0785108801944022820708000301540200c00c1c4210890303041064140d107101e0540ea0b4010511864100d5116 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 822239802 1250 822238552 822238579
    0x21005040e101d060303130e01050f04110a030e07091e0b04021602061608030115030b0a14010e04020409020307020d1d0108040b15031b030607030c02060601032f1201080a02 76
    0x120242641314001808407441c101d852112a05180203c1d4490f50300440384d58010301081c900100802c80b2084103c3e010701c00c2d003070341111042c0300340324000c0c81c1c500389139960303100c2140100103006010051000746c41c1013185a440707098081c841410a2032400c0041d02d0a1081c421904d02442510031800001d01d4a840102c000c1d4244041c0380d01110f500942d49880d000e0b40c0b40014209001035001e88030407440c800700140344040160541c1c941100c0c15104084a00e81800744000d00070300c0b203504440910308182c0c00d200c64408030b0700900c103e402048007140004108240180c0010b12056103ea890351421550119603000c80720004901da4114009200f4001080200d0424001c0580210403c6a02d810091a41000a1030030580031020410a5030000b40c0e1500e078a030a0141c0c0f036100c0940d050902c03501c00102c000039110380c0020005410f2690380c90040300000d007202080d0100c80360100b0ba8420001056880ca0b0461700100c01002001c0040000454040008290a805030307a0103020a2042c0c0ca0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 822241052 1250 822239802 822239849
    0xe0a06080a0b01050919030512030c0d050a0906020d090c0f08070905060f03030c150c0306010e01050d1b05040f29180303030a06090c0e1c0609021005040e10 69
    0x480740c10b203030400000740017510030340e07a41048240710032801c0c5114090703c5145182c07003414426941c40e000d071448018070401104680010856841c0141020300050136540c1c82c03c600010104a03030084d220310300c0883d8901c2614015481441a0f6000d0070707404040c03d5951030804c2c1640540d0080301a00d0b0001002009040840e07041903030002c0c8000c260450602c02c0720080303861038100180302032160303000d0b8441c10300c1aa002c04016030009000c0703000d00d02d10f2401c00000b801e54190310f2003050412100003507080c0b400100e68000a0f804602074012014a102020002c1036500103009542041c1014400050b441522096400004151400b03205882d64040103d0304a904640c0e203018540314120801210740c0d5051001b03501c10313903400100207280e0f410310704042d081301c45d80d01c001d100380107482300c400030350b42c0c1d41089030f035030041c019001c2001c0c0040070319206001d488c0c5040000c2d000a00c44800251241d0820090800c1ea10441c80b40703965039031010b0f1b0a80303c5c14101d00c10300c107002d907464842840220 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 822242302 1250 822241052 822241061
    0x211e04141f0f0203040b0304030801051e0d0308040f0b0106030f0e0609190206040b0d09170c06011e0305030c03030619060516080c061905010f051c1406160e0a06080a 73
    0x14a0f0b005890400c0e5031075250080940c8110750840014100400501451611241410040b85a0041c0072144549a00030540a81a0b00c5001c0c051190740400101003100e007002c490030032a400b5000f401c895a64000150182650400c2204201c0c20007900520140300024260b00c40d5000100170103106c614042e0001e602500394400f6a00f2060030080480e40c0d281010080194149414002030780c0d0b80e0a003060090f503840a07010190b00e00007004694840080000c0c454150348100b44400c01c0113186070b150010040d03c0d9400188540400b040a46021030b01002541c4600000c2c0c0d4051700d10706030304180c9500003119009004c0440c809002ca00108140202480d09252150000924282c40b0085292030008115200281d00001d48860b05601559026060042500012160426040c0000240b58180015203050b03003420000e800c0040c4441080104650701071300d0144c48040c10400c83c00482d2215100d031030b41c04103000e039000c40302500302072004800b00d5500c0d90f90500329460b8007034000c0281 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 822243552 1250 822242302 822242327
    0xf0b190b0c01021204050c0916230c10020301091404030c1205120c0703030c020c0a440c0f010503040b0a0e1e06130302211e04141f 58
    0x70340d428400c2601103c03130060320034001c5000320010a00c104c94401002696540202411070f92221365180c0302903150420368200781d00124039180020f8802c01c80c1e55003658041e40c0c0207800c85220710b0900a0254600d41e0007941030b1034040c1010b100c0103035074050811f500002694010300050503000f403000412b980d4070101c0e41c907440e203113001c1d1f24242044000c0c00c50f490082d180303809048000100304003010b8061007200c10406080c000f900081c05001c0000f8500c82c0355202d00d941c415020b05004102c0d03140240510042450020403c2e2a048030ba211414085e00c207004440962061104010585c40c00b003c041ca070b900b84c141e60341440c60740e5660700c0240180c0c0c0034203506030144e1160042541740d1001d100d001d03124151183c801c1d1080d015188030307500c1c12401030304406403401101140c01c013199001c640f40f10561400e035802c490a03541414042d0b454443e050400a034061100c5145880440300c80061086440c9112183c4a0185020400910080e81c1d81e40c4441c80030ba032042450b0040c000e20100c43c0e00e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 822244802 1250 822243552 822243577
    0x1211150702040c030e010c031b20120301170102120109020c0f06152b0b0915070905040b040c0c021002030f220611070b030a0b10030f0b190b 62
    0x203211441e80800c040d256510300501c00301e5240c00050152643c00d20410310560340b949418004106006100070f560850303d080402003100b040884840e48410014a4000d08585004c070381d8504480ca8062041f60000c2c0a8501418072485a404103003205000380c9141c5e04180305030070100d1b442d05160500941c0407404406090180039000b88a2445c1840038034862074208030b28140703001502040003050010401c0f440c135074604003140520245030303000b04690403541c46015941e150b01c035110013518220200d49144200001d05040080300b43e8044004003c03144282c030207005040c1d400041000780c510280d01c540c00912074001c01805490304c0c25240c240c450850040e40d15007010042ca802455109941076441c03c1c000e699681c418816401501004004601d00110200e034070701c940c15125855482141c1140d0000701c081281c202d625400710b50018001048000b021039922806000380c00340074005a440d91a00c5082d401504100001c401c0c07000c090100000400d0801101c40f109070029060030a6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 822246052 1250 822244802 822244807
    0x7090b030c16120e090a02070503090d05010e06011e0b03060108131704030809030d031404080304020f1f020c0103021c02030a201b010b010527150a0801121115 70
    0x1043c40c2d80965600956559030b01240045880188910305401420a18000d44100040c00c0850390100035540310410840b0a44132811035404d206024001c6000701c2d80d001d0080d4400021040c00d00e038221031000507402408583e45580d60480c9115010450302d560119900c900080c0c4400d1001c044018a50710130705100203078010b510301c4407889400a40084418040004d460307001854100302000f95080a4a018001302e0985500c80c000c070240604000c0c4a440040b02040071540c0307804440c004c08401601c500301483c0094940480084402120030142c000d124417412154483d0080710b030a400824540c0e004110769035502c5009600081c2041541a540c1082c0140b084101440700d035401c201c18222a1650707640d00300302034840c01c22666608160b01d41828271450766000400e41c3c1300f544a990b0024240b6079545002e00304407014028181e40300300048550501c060b5901d0207072182c080c055030395400980e2555810f80e4071102c0c0050280c542c1c1075140c0700d5089407800111314842410701070030027070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 822247302 1250 822246052 822246097
    0xb06040608010203010b0d1103090a02120312040b0601030b2e020717010c090608360a05070819230328030506041406011412040b070807090b030c 64
    0x82c22a003080c0c0000e12003040001c0c1d4000e0100a0303000d101201525242c00b2459401c0201c54540d44400304400240901d00d070a07129500e08030180107881050b80300c6991004585050300e042600302e2001c66002c0e02092070300d46400020301b00b400a02c18160030b600070084011030400310031078501001e481200118485c9007000700c0c42a9080c9042c0c03818041280c004a1900301e181000340141410340c1100c410040740508000703800c0c0004203494070703a44c00300801c1101c404040003442d5105849100b54641c0744034030071680041110018081c5c0488005009031500d1071007a405941020b0860034026101902c420094a01c1281c101d013021421100a802c403031034180d0119480c03229070350623040c2d00c00022944000080c2a80c040c002c0c03560100d012a41004809030b170140d14408200081c0c9460b0401102e003c2d9900440c01c161b040307a8404141c1021000c1c149000d140c000314040040b41e10f000000c1d40036010422160250945c0010340d0740c118221803c41d500d804150400e0b402074034410301284880b00302c0340c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 822248552 1250 822247302 822247319
    0x4050c0715110d061401080106020609030d09030504031a0a0b030a0807020f01020708160801060608011d04050124080f0133030b04031d1207140604050301050f04060b0406120b060406 80
    0x82c0000e12002174903000f00c0b50490b0015107080016400502507411540810500b0a0040121544d050345030758009807485d8541401c4a140c005e540008001212001611201546842509200b0001c410003800700c8008002890340324241008000d20211080c88410010301d01110f41e041ca00d00c2c10310460300010782e6034006500e01805802c006201d2040f18030103001100c028090f000c00303050b00e82406121949861303040020034440b101004282c04400011400b0405c0c207400c000a501c0044058609507900345117600c43c40c0304107125000d2944111900101c4031601070203a8504c460202105040d50848424600d40d404030000d0f5044000700c00141c08000154000b4010780242e0003a51004102c100117068400c0e4010184440ca00c41c011070018a030b40c176580010345001380d43d6031100c850810241880843d5040c0596003016030f00d5420401000305221a00440b603102d680607200c1406250321000a000032107c841c094444000d291800700004103c0d049111a009040070300000f40f0150341e0000c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 822249802 1250 822248552 822248561
    0x7091a2103070b0907081b04022208010b033a092c09070e07110120211012110301090507080f0f150c0415090504050c0715110d 56
    0x122040c03d80102032040d2041d040041001500050b0b000f40b240700039411000c007445029000c901e100701e40005e8000c0340d104010b00d0341080b081056503040c0d030b0310fa100c04100e8007801e14294807602900c20140c0000301c0480c05008488255401050418505219100c0c1154408500d0b0b004052007001003000641d1442084060a500b9a0307c00c410310b40900502c66101300000685441d58aa10a40c8240803d082201340d0780d41000c03c41c00c0c50003903030398640802400740594881740b440720080880c07801c4800e0003c200500e010385200281e420304448035250a40b001d1015a8601c24000c074031601440515103030012241c2c007900030200040c102462500003400e40c6c140c4101118a034115240c20841c102c6c040080c00321241c001c00c050b00c40459103c8a10b640c90340b000000f20011030191001c281c0c034014200c1101e029118580186540300b60703d03540a040c1c144a0710401e070165140400042c0ca2003100015101c0013940700548002d030803c81c4e180c07a000f8200f41940322900702c90401c0903d0121081f40305 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 822251052 1250 822249802 822249817
    0xa05060f13120c09050615090f03100204030605010f03150b0d06020304051501120213180503120105150429190804060f06060f082a0c07091a2103 64
    0x90750011502c10f8540103841d5007407688030000700e500304014042180d5401380e030794090100760b010150301c2d10104000140d110100c941066054081e40811040c2410303580c0013081524009c940c1441581d0381c03451111017404143c400603210ba9001c3c3c00301000343c0000c3c1c01000b80090028200301041e081ca80b1400203c0e802607138221400e500c8000c04920341010000d405005200c9140091500941d075000308030703007403940003100d0b0100795142c401561761403410000f05891500b2400b00c0e5152401009181d001b61028000c0034801d81170090b490b540702000408641c00d46401ca420014030500d41c50311400760800803591203a045105015800c1114808495030294030302c941d4549840342840d0500300d04691504180c0c1130010306101c000d10445800c130034500c2e00840740c0c0c5044021131750b407a5000220070911040350078004090108801d03074500150702504421903504103460301c0b107549001c2d01c01280e40b84048840200720f903e2501890340741100804414400c1800880d4500c6e41c0c141d84076003103512881 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 822252302 1250 822251052 822251069
    0xe0703110c100506062506020c01020309163204110a1d151902030c0a060b10180501030f06090c09260a150b09040302060a0c08060a05060f13 62
    0xb003500a40c4003860041642240f805d035080c520b4400d0003549405a108009480d4030440d02440b108802c01c88194112555200442c1c021900c80c1032660425481d480c5211184400482e444808100c840d0402c2c1520401d8412007007004401030916011a0914500c030360040d4840c2c1d8519910040e440020014001c0c4102590740d2000320310044000804803100a01140c040c03c100e80c02c00e0081c44050741110389030b001c00301540800741f580807002c034910300c207910144500740100468a070421006810500b4003041c11580e0080458000e03408545000c03a0702d04480390000b03610000c11665000b07900dc48000d00c4102400301d10f11f80c8502c1084243d809850448002504407401000011401030400009116010386407101000d40440c0d6681d076040410042d040484180001d000004c05500c05504000042d241401e0b5243c47d041c06501c41200b142c0c4101003d0900d10240c901e85e101e165417510600c001000c1c0060329091005100703a03030700044100f44078120200125860319414100c884000e14820 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 822253552 1250 822252302 822252313
    0x60616020d020a1725030204022505030301050f04090308010e06030a202b061104080a0507171515040621060b09130b041b03030c0c060e01020303010e0703110c 70
    0x3800c55614282a4214030108060543c5d8503516000c4051015402c9030b80446001d6150345011412034603410700c00b40c28140c2038030990040c0003044401700285040b10780440346180280e40383c20500003903408041c0000c001030691801803141170340268805070043d01c05070440303c844496903598000c481c0348900e840c00840c4280700d00c00c0300380391110b08515139000e00f04013070510340082030500043c0304446800800302c81c1c032000864942c00c000d805441c01006204100c600c0d03035010381031040e2100c00c1070080d490030490000003c020a44005258818a4200300340d200031640c440c006200d666459481ca941c1c03041e142c0c0400110400002d1241d0001d040c28603004c1e18a0041d490300004031105641014081c12900081001d0300d1110381707001041980199060890b99218a880d0600f085100d40707403030848840b05404420b1603400301c0e608610910910b079445425840f60800c7e80c51810342c50f6400c1c010b9208100504c100c5101040e01600f00b02d9504000c036115100810160301c0d0b412102d2002c0903a40300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 822254802 1250 822253552 822253589
    0x60b0333030a1b1d040303050a0f020a050306030105060111100203150d0b070e0904031202071106130e0a09080f1606110705010f05090d0c0c080d030209120303060616020d020a 77
    0x2150150b00910b415924504960303c20350030544c0000c4028070280038182d03a0340000c2c100300071076003001c0d80300761100400b150385070304950f0080c000740c0099800c64025864200010400c1d4091000090200da072400145042135072010042c0c065440100740322101500d1454058150b21014102200f142c41003030304443c1031900302001045090f5805003a485800c0c450305100200340c202c003040244206404016030342d019035041a41150407207070707420382c0c00410014203c2c81501c6202c0340031050382d03002514503000d901c0d00c46901c0d0564070003030340c003030410107040068101b05410b480040c0000c4d00c61480410750f441c100e4460004980d0f01d00da00b640401030010302c1c0010044e0a1045068110301a01c00700110b00380144103031b640f0034808a41c1d50500414006003400d01111407105c3c00104180d00494080d036030000002806900b007415807500401e940440a21300d140007100f541d103c2e580192901d0700701092120650004604040300361380100e01111010b0258480d0400d0390b0151440e21548001c100c00f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 822256052 1250 822254802 822254843
    0x80c270a0f06170609061c140606010e0a031e0c0812091002010c0212090114040f0602010c0801080c0f041803030c020f070b1c2c01060b0333030a 64
    0x20784069042052018000c014885e40c51800300c07034004000b510710941c8541e00382121209160007040c0030f4040195004000c555240c00950a0300c03e506c00e0703030351045070041202030003d00703015400004c06c044800ea0900c0320701e00c190112002c1e150300a5510000c0e41e990b03070b0480e07400c0c50900b41c0f08943e640c00006002101e801e00c07640d034201072000741c0300030040002201c80c003d44483d614418905c0c610300c005001540c1d80e1091007c25034111020504d0707591187d503040301c9002003513640b10342400755007000c0055880d14002c40e035680c12a0070981c054940c880140c0200001e58a0800480d94001d40e81c15011800c0c607100500310300140d12940f07001072182c0503000c01900d0041c80c01c202d1481a4800c00f0701b80b01201422003a5440d03800d120014404a0441c0302030700014000f00c0c1d0080c0310107030041040f590180400d1140307801c0340d040320008005035502c0301004001448112150643d0150001c401041c0244403280e505c40447c1d50300c52a91210351000000341090070100094400140000702c207160700c42d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 822257302 1250 822256052 822256067
    0x91203120705120f060303131202131e02030a020d061413060f05040f020c0a0c2d060c02010e03010203010902040e1501020a080a18120b07080c270a0f06 67
    0x856a081c218240025801e03c481140c01c001c1c9108502c580c07401c08180d03039480c01c10588115011840c14010b205480d5145040c11084000c0c090348102081c0c401c107104001c942c0305111000c03650035140b011406107154404065030002d01240103295003003000188443c0300c1d01c0340c1409800301c0d8900710300c4130118404221001607095400d480041c5000740030804005c40003003030030494409503008a0000304140d0351070000c1c001c081c6020034600540001604100004000c2002c0d506680d00c680310b4074003060128105510701221050144440710414091a03019042e16808144145420546035031004046402e81c0c1003139024960194000c20f0520541d880350740b030b0356404255120944017201524000079502c0104070300140050f880090071041c900e00c542c68040c0c903102d4080e00c0b0250107545291404e50340c0b211507000e07180007030080c3c00300700514800c206060180d400c03105400c0c145a403580c079001c0320510302440100c1040307401c40005100d4448074840710082045180b06000c82d8609071000e0a0341 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 822258552 1250 822257302 822257311
    0x3240e070507050d1e0f0914040204080a0c0510020a03080712150e1602030708040e180106060c0b1509041527020901080d090b0f092806050a05040b0307020309120312 73
    0x20007030020840760743e2007013400003108c0180c2c14030008400d40c6800304c0c0091180e45c106401a0051800c0142804030803030300502203840c1a130b1080da01070081002280ca40b03c144400038006201d100120303403100d110701c0412000300c60400c0c0000314400d0b04884440300c21b03d00d41c00710840e080318108205d80d01c2042c1d0000c841191960015502c1c01005e036449144038800c2e8001c0e44000b40301680412500554001e101000d20200f0300204122078880002a121059100085501040303100c002441c111600324000303000400a13003500c0c244d845960b203889481c0d83c240b620400040d034402400d03221008480700e84800380a11080d0301c408180c46d00612a841a05030001da80c030b98020303034804148550202005017128429600300c0c0c2c86035404842001c0a11030f08504036840089141000c600303c0b0503049901075044078030a01260035070703240c1e02500c035406000302d05004a4810f0201b00300b4064102c0007560f008010703205a030b00e88020040050740300e0b010102165a2a80042204d2420400401c51181c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 822259802 1250 822258552 822258557
    0x1c05070305030c0d0e0a0602130f0506271905090a050106020604200405010b030a0b01090b09040b0409120809070b03060a030f030c02090a0207020103240e070507050d1e 74
    0x51a159460241030340c400606582c6200500184000196110740d004200f03100d00c04056407103151a504201010750042180b8064003640324400045500141c401541201c00107441d0505084041c40c1324182540040304103501101714030204080780d40c0340001000200c5412180b0443c2a00f800140708010760000c01d1404154a000c2c018850503400041480e80180c4c0a80c01c1c01000203082d415100d110868200c3e26049800d100010645924100285102d000780c01c00c2006295603c03401150410718500c107540300000300b0403880300c0c18101500001c0c10010060804102c0f020b50f59584041c8142d1150050005a040c00604c443d006c414001079004007500500e507400c0d03040980004950500c60702c001031007910707104000c504050003010142c001c10b400506184452510350800b030003075130280d181240000e2400c00490041c1408603855075120824030b141050301410000080b0038044060841000c1c081c09000b080e000031410449150200c0a540e100034601c8406694001d020110b9a021002d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 822261052 1250 822259802 822259807
    0x20d0c060c031407330510081b0604140303071415161205090f1b181b210405070302040606080609150a0b04080c0a0f120209041109091c05 61
    0x1265045c0000c6040c1254407004561507040c88031442c0c5a624885c0c00700408a090004020b14a5140300c20641100c40e08407c0d200980c07415200d004a8481c2d0600e003950100050200307002851f9440490200d980c0c0140480745402c4007900c811404050115030b07042d41d54040300d2003068292100f401c2030740010b1100c840d0408031051160290140d0001f071104c480c525aa800000d00c248010020030b0300c3c44000100b0341d4100f048841c0d249035424a0b007000d403800303050a1213095020000f441c0d1982d200e1805001342e003800200d40010000d042d4002200c61110701c0584060b41c00d079104071030305a40a548110002c001451440c030501050302c040e035000005000070031041144a40741c80300302c1070340301002d54a14a100101400041d40c80b11454101174000440484c0c08203050030001014106400200c400000d003941e222007170340c1050003034054000c1c0c411804045c01d0042c18005051a046446410180c51402c03142d0b002c6812408200c0e140182c40d41300902c1080c01c00c009030b4500c034526416141c001d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 822262302 1250 822261052 822261067
    0x9240703021608090406120f0204020a2a0b340905030d0305011d0f15120307150608030a02030703080703060e090606010305090c0a030b090a020603010312110312070804020d0c060c0314 81
    0x35400d107523000040e0103a0380000d58100218031444411080c2c142001c00e6200e40380508a65001004c6946d8044070600c2038000031440300741008541282c1e0091411a4520b641c0710702c4041410300f05900503480510903202e4011610b590240004180014a40d0b0f0003d0550314122601100161a0818001070710340f11080c05410fa54003618158061802d546581076141c101020407170302c6003600b20b8061280004141d2b102040741c004d42900103070760300e900207018860321000b80300d03140e100e0b001017140580d0081041000090150810f1503021401c2e050000d6a01c0e502c2000b491321805c1182c003440141c0181040150035030305882404e40199200c0c0003001e40c00031040200714144085c1c040508400c10101c0003d42c48841040100b20455014048c6500d95944c0d281c4081c80c025501c2000000c520f100c0e5410641d09000000d656603000c10302898003058950ba201607601030406041680c002000c20019030100d026450a07600034146035031899900107540c100181070024100d009031440d502046076a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 822263552 1250 822262302 822262313
    0x180c13120c05011803150c0e0406060804120905030d03022106061c060302030f0d0212091819140709060302040e0a0209360924070302160809040612 65
    0x81090b81c40c01e0030300321140d07510800c0350349100c03000340e000800c407600c1e000d0140441d05c5650014048200315844048043d1850800c200c20b452041c0142e80005000100207404034034124200b16103052a410251601c90712003012a040540a0801c030380405d40001d0900b075800c2004040720310500c601c41101c041401c00d480000c0092141c2c4196038104d8854000c40604110350764007941c01940c0c000c0440b07206600d01004c0036181c49429804074054055207008101c0029040112100403030700a00e4406840e00d465801d00700202c006d0007a0b083d80181c0d401c41e5030070354482d100d06840c20401402003089454400b600a00c80707040da07007140b0201401440100036951001145035000f0840003400350f100c0c1c0e800004100d8066101001c5004692041070602a81c02240104004250041050500c0d03654039000a9a610050340000745401502c142e00ca1083d0b030340038040c90300300d010b919000d450142580c0408941c00d052080c140c03084407001810960528262180c200140035540300100c881c03010780c880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 822264802 1250 822263552 822263573
    0x90901021e0c030409231308070609031106070909050601051c0e0c0901030b04050601090209030318150c15060f0904060209060d06030609060c1b080702180c1312 71
    0x8264000740814005100b4605005990203031031003002c10400d04d0450107400103e4109115590a505d03ea030000c503640c1c01c0c011501c05901908070902526042e01c947d165801410f55000036000c000d2400c0c107610100c0e8080c4034450060100b9502c0310099030400d02410100d54001c0e111074107200b01003150f00c05070a64002c00d85003007629450005001d0322444a8a8117210315401540e52194032840007004000c50100348602a90180d03040324520fa0300c40503044220b215040361554154402c4c005103104d0030185a07010702c40100509002e999071544880e0512981203181d000342c1a070882ea00030b0001d1034a101c005544400102c0300420307003c1440011810401002e04054600ca8002403e05e20584402d411204061310102e410001d103079030380c10841c0007400c003200c0840b510390810603ea601030340b04000174020320001032020107915034255030b851010b52086108a81020f1085940101c0b44081b1440e5446070000d04003072075030b035061800382c503004400c6a0014404c038030203c5d50003008203030740001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 822266052 1250 822264802 822264847
    0x4180b1c03110c1c0312060e0105040e10050a02090102010b060f0a142703060708100510170a050603190503120601031e020904060803090f01080712050c04030209090102 74
    0x104904059440c688031414480403c0c0c025801010190448003041814000d140d981d170b000340e4070701c0c10390008800b0042c01d07500b403442885100042200140001d18103a888403000e105000d046907559211407440b5420355104540000302146d02148820040d6020301904080b400115080340c5448c0121486036824002c10783c060040001c0d1000b484002d0403240c0440d50100400c0d41c81000c149121040c2e604110885204540a402040042804540212481805403240c0c00701c0c001c6890902090003564010340104804200700c140186480c443c824400c10b01680d01020b01289510b48882490301d400d40c84000c540c241c00214101501154010003a1221442c401402c5032241c3c44035401280a8004c043d40544411002603030389901841e154002c020f80501510184006075a50360207a860780140c00440f50400e10100d070f2102035600c9401544d80c0410503040400f41070520aa0ba101142c1089624640e85000014140103518001400b6540413030050000e5142180c0000c5180010642c1038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 822267302 1250 822266052 822266057
    0x501091a0d0b1305070e01030819020a0c0e13020402070b0426030f060d06050a0e07090b09010b070f0b0c0408010f0218151b07180209010f12060b04180b1c03 69
    0x1034008013080414030206000b071500071404e00c42540c490074150041e40c0f20400c4c4000102d22605060340440c004194480840c0d08020026504da01e062100411180003e08158850800c1001c81005a4680c40604032143c01740e02e5008140c9014500a45007040300150700c03c180342d00d0202d100b4440820b40480c0d901c8034850400c081030342c0344d40001c210b03541100140288132030b041c401000f03180442540508038080d0040c00310743c0e1060392001c505c0708546500d2582508501c401d801800100c14640040212a02c92414004098481d440d540d40310707881915041c02111000504101c08a001d0183c560800b00105085182490203500480c03003e41071079469000b080b100b100340009003e000d094030031044145251060308507030484815241e408500401000401007000c6040b1445d940c425030340b0b20b00e410b0716068081c4200d01410b0f00c07600701c2d6128030411107480c0c0d0004500300200101400c010084841035507100c0180d204a442600d80c10140b0b140a1a008142c984011400800c10035000d40c050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 822268552 1250 822267302 822267331
    0x503060915031c0f090e060a0e130c03120f050f0a2d03090302150115080405010209040626010e120903010e0613150507020d0f11010501091a0d0b 64
    0x40d0301082c2040d940e5000e22803100512882100c2050b0004100004041340d0b50f643d1100716254100041d644c441035400075005201c80c01c044c00368078683d000c02604109000300342000d0303080c0e668a2008000d034940040700c0b0300c441c2c440d408440340d4110b002c0700622215401c0c4030741002804600f00920307004148041081060614101d2143c3d94901c4424068841da40c411814800224501801904421004800500c9a04050903ca48400c001a410307209603003002c001c0d1b01c0c100f03a8111440c100c00b400c2900d481d5403c001c1c0c200355a80354403e800081c2030480400d90800007505500c007001c648072002e85032590410708a0003503c480421440c28a900703613805141c90b840c004000c2401054500039501d800d12405045c40b80c075001c101e101c410907503c13070610000d4000410a980c0e00b0740b2020b44d140009a8800c03807003221818003842180c242c0c0e90491070174030b1240c1d043d030441c6425a01c0030b0f0f000545a50707a41c1c1e40340c050501c4520002025810a0707a85000b2030320241d45450109070000c1c00c0c000d0303020a0703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 822269802 1250 822268552 822268591
    0x1506080d0f050d1d15060a09090311010e2a090601050a090f03080c0c0a083a030510060e01080103150b03030304030807022b0c05010b060c150705030609 67
    0xb6030503120041158002000f982030794030f400e0a10f0b4160141d024445100d080840c080400003101d01610525025207845207040c58002c00d00094105100110244090f084007240b4600d001d224400302c0203c01001401410100c1c2124640256200e002d01c40c17040c41248600051340310042d00e140c0000c42031810a50b41c0022400848130803400760031056018540900010600c03281c0e10140c8440392201c1d041c2c52543c60303c4030410000703040510401c05160132040d4003203058491000a00c0b03d618840000707120001c03002d49000c100007801c00c40140400d66038030500162600e014a072101030411401c01c001d03a05d029900103080c00b481407000400400c0a003402088143c82c81e00500d91444000c1e0031242c490600346409032202404660b54001803281c4c140c080d800e9400004c00c0c10b040003c241c0304036404a80c04000701c07030407440c1c0c4100391125901e440c0b200302c054440400401c80305820034040d084210a40c8503400500c100070b84480c04004040c001d001d403e9441e0504150001400c0b1400250004d6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 822271052 1250 822269802 822269807
    0x40b0705040b13091406031009020114070317010603111b01090c0b030f0a06140f0d02031e011b0801050d0519110907020a0b220b0907031506080d0f 65
    0x1d1904500d18540700403809924050a441848055031441030040c840c81c103107104da404c0300d0304040710084d51550040d00803403100003507580b207540c0080c01890503102a92803210300d4007071640100d070110001240040014460350360b00e03084d83e016140501d0180000001c1c80c0d0002c210340141200c0300b00c0c0c1050f036000300030312003003d40c0904000e540c422407420301c03280e50b5801c00e0150f410841e03854420300c20010008014066032304c21070082d10450a4601841782564042c451103500cac100a0740d4210f0107510112015079010840200b000c0c0d44440c070f41d105030218400300c501392034407000301c20101424900740005c1144c102100340d06484050300c1c2481101c441341043e629200c0c14140c0d011700c40c107900a80c1e85c14003200703000700d03001c100c002c1e1001030007a140c81801301e80d1650320800c0640a00340a0000c80c51540701c1c6400802020351003c8003242c2038601352501c2c2c040500648006000e54094542041084500b02c24070292a801103410001d0505d8075040d00e40b1605285001d004000083d0142e00d480ca0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 822272302 1250 822271052 822271057
    0xc04052412031e040f060809060709150c060e120901170f060d0309180f060b1e03060f12010f1b050406030510090216050609031c020c01090f03080f1e040b0705 70
    0x2040c45c40d046400f569869000e030001c10152141000ca001d103400040845010b10307070140440d102c003504104100d01c1c4610440e020102c0003003c450aa45484603a6404070041103605125030440c540c2c0382d078400500001401844407003402e440d030780c401c040c100b00c805101c2c2d051055000c1ca05480c044280249481d0481c2c183d10b0f01c2c1c00c6550610720112803503c40340a69480152101000401000940d0b00c68030628014081d44440c2580c9407003240f003074903000c080c0b030b000f8581111015008400100c0c0b628005440e2011818800d00169503030013807a403840b006c1e4010f822041d54111012a18034000460041142c480c82c05820103154072407021403501300701a40144014600030800719161145081c41002841a01e0f0f415200c1e03124000100b400207602000f12040e14910301c40e030103449100381d54207070301035089002e42d00c509540e50011000855500e1149000c600d1090f640c04105d4540041502c0c00483c0180200300202e108008809a46164981258009400401c4002c41d995480c008980380e2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 822273552 1250 822272302 822272309
    0x1b190819140408010b01090603060b0d0c090812070b010506130909030c140a0c0e190b040b0a03081c0b1003050907080316050709180f03020c04052412031e04 69
    0x104400100043c0581065102c110f00c000d0036601c000c4481e6403907034200c00707440d6a4001c00002100070409960041c1840d84101d0501343d0904000e0741042d5aa1000381c100007000300c0312000c40c440003403907404000b400c0100c076002d000304454982c2810b01e01c0c00078450700c1c1c105000c2c885003c2d41c1c1c4c0d070104062601406007241c2c026800018a1440c0f020000c041d0f4640000c2c1c07a0840324290072500110385a6841120f5510034900249001006042d1101860141c2490380a10f0b070001d0b0340305554005525400034180c00f960040c0c0d0303503070394942026007107040705042ca9601e0050740c0e1910800312081d640702c116441d80c58a1a1801290300d46610481074108180c69005965600c00095030710700245000b6900c0d0b00d46401142920011961040c008054076050250640385800c030441590005c1c8441029100f0203020348100c560825562001c17130110b400c1516240e4021240740300341d4560f95844000c041100000340d0f500c426041e080c0551550780d00071880e00014a8086070105a100d407000001d58005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 822274802 1250 822273552 822273587
    0x9140c130905151804030e010f17010f0312050a020a1721060a060905090424020a0c020a06260c09060d050103020f0603070f050f0d021b190819 63
    0x5810300282c420b440340800324185010300103010181c0729140c00d00612170b04c1141c05446284c841d40e001c07001111001c0001d98840c041c8108403803601e0404a0040480d400307418081219140386041d801e01401440424195008204040110200c180c1d80401c8456905030300942120600b1898080f62036507010301400f80e09128041c10b8101c40ca43c90210580d405841c045e0f5a209901d07484100031103c44000e40541c2d500b214038400450000307800b0a114202a4408102c2c3c80e00c1800d0b002c1e40d99041e68400f140c0c1e42c0000b889564071405624015410030300408207411b22542c03c0d000ca0402c2014000f091030705501d035900c030400040118010204403520355100914843d922003403c20355600802d002e0100317034020045040040e500f030034058100c078050a06038995072036220040104454680c000702d0295103a15042c0301c821410299400a05200e1002442c03603902002040d5140d031411800f198400d08040d84c00c4c002501141c0604112800c0d1055800801c255400b48181a10b00302c42d5111800c0030f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 822276052 1250 822274802 822274811
    0x1807060309030309061e0501050d02031207030315030b0610170612010b06040f1701020a0c110118081b01050a0e04020906070b09060109110901170415150f09140c1309 73
    0x21030348044014901d0443c03518901f005543d8860041c000410a6010001e4140d0701c4201082c60507008000500702072480f0b0314020461a03460b4031580b031000e18690046415828039801d01441d0319008008401c154000d242c010071909540078141840d820140540340540e40c140c940e600c0803082074129805a20300035001d1551160340eaa00030300d00e24110710803290303450100f019022400d1410b0080302c100382160345d136288450f41c5903180c4620a607807590346281032140000411280441c1030b91300500410641c1e02904031428040c414911201c1c11502c0342d410040100030013034000341c00c0302c4841d00003c810b44005849030b8207030000c01c0403889513070000307414010a1020068038080c0013a54a06944402030140868a58030049800c64043d10a9003804603060701c84407002e10b01714500f8254440d0180300e6011804000704240021500f40701c0415498603000c031018400c1400c0420104010040301d0020411850009500c42c1c208070041d004a1250400113010030b0f440240340c042c0d0002c1c002c3c1d04800c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 822277302 1250 822276052 822276071
    0x14010203090c030f03040501050901110c0306040809040f0501030210031a0a26060411090606090d05010b011d06073009140108060310020309010e0321180706030903030906 75
    0xe64442c00c0c1601d040c480c0c425141d22004400d03011082e601101e9041e1991404c1001c10001903646040144166000b44500c00740d402e4995010041d2601030781c05481848e80c0d5800940c240410f603404030821001c540d041070010001a101d800c0081400c4116243c0080c00d044600c40a1641203031505101e075125141e0400449d144100c06162901039000d80d0300300650751002400c181d1900811140035040000c071240954442c1061144d466000400070940c1d40380000c44400141040065201a90035039540d0b83d141d1348550b0880c01d841c0317604004965442200c0c2841002401d0b41c40740c41030051803295903d036845201e4410030209051030580d01030138841d1129815000b4040d800f64482e000111143d444414810350191280314050b13071001d40902450b400310300c4884065880a000704402d590b17a41001c1c40001c1d002e1002d0029005000c5201c000c26180485034a07500c04007405501e083c140c1d040e035034101c2c8400040d92500303d81a074100480d40980f24201078000307081ca010054022800d08a642 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 822278552 1250 822277302 822277321
    0xc0e1f020c04050c13560f0703080907050d0b04020d140703031805010c0f030e01020717011508011b11070f08010203090601091107230307030c060e010203061c14010203 74
    0x1000c882c02e40079084c407444d2503c900d040e584000c0071a46c2010151100540e184550b03010706042c1c280400760841c0b1304100b80000070400d0340180f07800d500103074030b04081c0014035805122680c000c000445081c0407908880d01d46904104000e04000c2c405c01445000714200009180d248045c1c0b846501519900c41c0d4a003000b81942040242904003a0040744001c80d89601494210311500d0b0003951501160006650030760781d04007504a641d055100d95400000c010702480380c513800708443e5400104000d4014203c01262410076003000c54980d05000300c00c2020f4a2854594012440301e16201d42142164800641016a25041072581410603a0045841401500154095440790086400e40c0e07a07500e80714000c682503803100c0c003075282c5c080281402003a030404601070b899500394111261104100400c5d851640200b40c11400300e4050b680c0c15050202c9480742e41c2000c2c0d1507074025032071480d1039000200c0920544a400c1480c007050700c1200b0038032035141980c80840d05410021075607402c00c003609 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 822279802 1250 822278552 822278579
    0x111041205010b090f0c18090a06030b241512040c03030f0e09190e0f240126010209030f070f0611070501080603100c0e1f020c04050c13 60
    0x1550250300707143c0c0707001c01404d011071441d108541c0d0b010400308544400c4091203196120040c2042803102c0107014025aa96031907030a40a0010100d000440d18958907010030000002499941c403c02003c1c0d07400d01e000e24142c80c58074110411154490000800b001041c540c1c015215680e003024900c00070031040010b0354680b8000e9174000d40710145c1106000b0404c540301613500c00704603000b408003004109041c07130110402e030054100d503c0100740100040011417034404042c1c501c1103146c0c8248080824440282039071804040000340d0700000b50304000d000800c05a2682e40e484050002810980019400b941541c1001000500f91901400d40c424800d54881031401022201a0314940000d00c1d40c0c01102002d8503082c8040182200d5481c00005403000b02004043d50f1b0140a04042c060440300107202e00c17115848140c5441c1c1110480e0000e10104462880d580100079066030201c8001c103400058003640d04004480110300e682d2801400c042501542d40c294544c6030340c00001088030b1040144 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 822281052 1250 822279802 822279839
    0x201090e0403051308011b03021602060f030f010b03010b0703050304021305090c0f060c07171e010f0501090c0804061d0f060114010c0b0c0c0109150b12071505030603011104 76
    0x50440c40661500009404c07201d40300388107c4850008030540e20298000c1c0c000d46116502c2c50240a5a00e5040d000305841e40c0c440441c0820305a4004200811680b801601e40c0c0988814403640f4203540c10712018208500c9124005818000c020000804564030940301d101007881080041c0301a0400080701a5030b289070040942c85041030000c42d500700d041c20700540702042c605600510000d40b9111000c00b68018140e5455154041c40102900d9014030580e50b1950407110f4000065001c03d00b80a0343c200c07201a040320b440300303081c00e040c1000c0740c1d8404801500950051000280d2244e80c800c000343c0510120303c0b40b041400b400c0e0004440d1080410303201d040326105040311982c1410b40004541a00c0c0c0714134000c06000500022a41c01d41030b1a000c0c06d00b00c040d8000000d403058441c2c842c60303030440708400481d240c1c0d1f1300d81604041500304003404c0380131040c42130028100503003040599140b008140c401c1030f00300031011000406581c3c09400460219640c041c0da60b6403151207607294034141140c000e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 822282302 1250 822281052 822281077
    0x606020708061f12061e1509090f2306151e030a05011b0e0d0f03050d0213030b160c030503070509010e1008220f12030e060c09120309030601050d0201090e040305 71
    0x4030200c6c1501034001c06015841c0261008165030509881d5002840d40307200a5509501010b81500061111850084512882c4165401002a140c02c180c42c00f81c004281444400400c4141c910f1a1169140007c0b12060501d89030892404440441d00e0030382803810181c455030900c100301b248681240301454116032940c0d9054490343c58a010301801c0a10045d000300000c0e80c440000c004288900050a60f0240c06980903161200060010320b18008903001030395084441820b12560042c02640740c4400441c9003084083e500303050f180131b002030100414120078814000340040343d50303124890608414100800b402450080040020400c610443d21812820038a00310151040494140d2044e07841c0d1182d09200381c9041c0741e544119881440c0200000d240d00c42c5180318811000340400ca21032014000c0054890141c0f03070410061010742e251030380441d0400c120007080ca440c040b03202410f64005646407a0784ca4242d2004940e141c00d9540b0009011007600d0602040540c41001480c0c0c090b03106 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 822283552 1250 822282302 822282341
    0x20a05062a040810181b050405090606090117161d06010c0f1b050907020606030d09051c0212030a020105011d160e0a150509040606020708061f1206 65
    0x5901c21035148158040c00c05580d00c05603181c0d15041680e00422030000035200162080842c0790744603624801d981500242c041c41070f400074441c90601c0c9c400c0e664410525401030020b0304128012455880c018090f03c036900343c0d0500f20511641081042c0e40c8024002e0b4034020420b40d650006c1c3d85d1100240c1c0c1c0440044402d000400d038550701c100e45501100780c2001c403101184000313541d9100d440200d80300700c1c5401000c01c1000242952100181132280320541c001d01228985a0100b5040c100c1d1901258180038035100240305545803854040c00c441020142e00c000c9130348900000303811011094800c0d00070703c00001c00141266041d004581202d6003c00211a0900c4c1903d81c10b45a000444045500003440c42d8040c002c02e00c42c6145115018026190301002600c4a800814a404d81c031044804140009004002800c0c01d208070002064248080c03c23206081c240c0c1d080d181c0102600b030300c1c10384c40100e1590069100d074441030700060400e0021081c0441e002e281200241c0b0480810211030f40d282c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 822284802 1250 822283552 822283621
    0xc1b030303010b030c090a171c140a080c0f0310060f021c0c060603080d1e0e03031b0c070e0a0e01060b09010f0504030215040510030216080703020a0506 67
    0x400c1c0c905841c011448607003140d40d06a410354403500314500705548242404c9002900c030148440002071102c0c16000b5241000b804248012105001400d078001c1226914007001d91020344e0095900b0503c96141425007034450b410701c0070084c000d00c0c0085400c240b0002c1884440c84d00c5e210312104449003501e071407090380041d500983e01c030100c01c69403200c4c0d03c10b005000d144c3c0074440d00c07820002a118003000503406849440782580c541040e0044182640d4601d54101e414610b0446510b443c3d613904418042d460301d40780304540303038000500800c4060501c0041242c0c01c89924096801c00505a0100c46c41c81350359105203003052005a43c81d01643d40b811440708a094410f004003c02c1d1800c200c9114a4181e0200044034508100701c510810070a06100c040700594641a042d04110b034046c8401340c0703c501705410080088200c0301c07405d050610421485a00615401546210b1604980b42d180c50300c086d800c00703a0074040640380050140c003c0c8000c000380204a0355817030002003000761400520500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 822286052 1250 822284802 822284809
    0xb03070902030c0304030305090312090304050f06041a091c060c1b030c021005120a06030311060907030b0c1b01050901050a110409020c070806090d030510030807140c03030c1b 77
    0x300343c401c0c40c1c800604000080c0803d000350040740d00542c00314122880c194002c00c4003c0540e000366240380a42d000002d08000c0f5240041140340a588100c1d0f0051501d881d24400400c0000038117a45d17034191001083c1c07041d00341d981c86140c1d046254880d15104101140d4a400300040a040c1d81c180d0200c0d6048608103c0c000841c0700000b40594940c4514010300c001c0e408125083e4a00c0d6485420004200041440c000030850030340c0c0a00c1950b000416183d055260103024500c00240012695005204005a501c0000350030b00031aa000844099907844511640085214000d80c40440302d11080c403902c800c080560049200e40c10050003004682c4804443c842074a14240708404c0d0000148400d20050b50706034018a6004460011104441e54a40c40c4508100d001c070b503501c050342c000300c1103184420f81500a06600140c0001101140c80c00c3d652103c40c58010124090b081440108510342c06810070450104501801011262180303505840540e44911a03601b015400810204c001c15504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 822287302 1250 822286052 822286057
    0xa051203091902060d15080c030d094209091104091d1e060106030506100c170f07050c120a080c0109120f0e0a15031a130b03070902 58
    0x55401c05490b200c400841d40d004090402841664041001c1207050300d0312104d80b06000903085084821580140342254160801d209140c1071360103604040009030f0300f140c3c803200c20b4007581c0c0385110301030240b084480101c03103e0fa2607500d1064030403928086150602220469004410299039404460301c1d01c5207040300a8400b02c0090340079500341480244021960b030342108200494003011800c000b00085011032401c2a5134000b0b41d46004d1414840010407400d129040c00340207103090500ca10b0a01d1408907140c20161090359040181c541150420403c03280c641140030300c1900c100a03150f490300c82c6403428650000d10b04640030f20901c0102c54060804038101248214030300f001c0c4c44588115150b4182940c80b00c3e8030540d05550790088040010038417800c41700c083c2030503900c41000da21202c9010706001503401c1214402c4075001401c101c07400000c0707555840344800c2d15001c601c800c0c040d804480d0240035140d6255200c070140c2502044081160b11540c00c10504030122031a49545c0e00700681280b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 822288552 1250 822287302 822287311
    0x80a030e121501050d1a04060b10030b093402060a0f0506090a090f0b0708040c0e060906040c020115030f0308060604140f0a0e0703060e1501050d051008030c0a051203 73
    0x54680b5004101c2841c06008003440c0718060321000343c40c0d0150326242c1c3c1e84600111401c41d0201e5413500d61002d9400e101c4464903046403181000c1003081c00c1c07100000c3c14510000d04202c2da2001607945110114550704581a2074055400c48010a800460000e504c880d022640b0004180c54101c0326201030080d4007800c0d00a500c0940500f032152164500f14001e8030300b500d010f4030300c01d924003918800140e203017a0311403142d80d0a41d14101c2c2070500b46020069186207034030106040d042c1a01380078180d525241030a0700048111800600004c508034140d000d0240c003e076072840b0448000c400400e008800c8100d4074030500c00c5c0e50f540c940e070366100304000c0c01e4003803801601c1c09255440d001030120300f000701da10f800c0080000c024000d0580c2e18070080100304d0080b580718001a490340803c2004200030501d445d000b0408401141c0d0b030300c4001c40000e28a0251a051641254455000c03c1d902c4000310305004c0a8107400d4241c0b42c1d5030361000718113642c440401204039a02e1145d0380d4600d8410b103142c000d482c0078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 822289802 1250 822288552 822288583
    0x50714130302121501050d021c080333210f060108010f06120305090402040b0d02090306060a181503051c120c0e06030a060f0f0e01090b0102060609040c080a030e12 72
    0x2217900300000d2010700350450b10100d800c00c4c1001c10001c1c01c84a5013441d90013140c440c0b01c100f50380b45449d92034210b4400a1032000c0e4440d104d085211401042c02040102c003507902610300a95140301d0b0001c0c4500c01c866a01500c0150041003040c0402400126115060701d03250305c02407050a00103640c0d48221000c03445105201c10707030b101481002034801c0000740704c4210010005030405468406d164070031341c025101e45400740d90006040141d03080c18085958016011200142c4040c0f810302100181605407409164090760b030704c0444c10751620070121038051a00002180c41c60075182c540c44a02460b409440f501040c10310078029402500d5004070410390000ea03075031611494a620902a442e000640f0b101e280d10746070074000c9900510743c0c1464000300311501c012401c65203006682c3d2510001031f0441c0d140302c1d0a051510300d841e40c0000385242c020800352007000481e9140d0402c0c181e2034209410107185030045080101c2416840b1404620700c0f0f40c1150300c48052403902910b80e51310188004100c84 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 822291052 1250 822289802 822289843
    0x30614030c0109060c06020408030d020a1106012d12030309020a0e070504030f0812040c0614090a1214030a03020306010e090702120c01020d0f0203041e051005071413030212 76
    0x900c03a144000c171542c403c8401605054a0b11880d42c2940c000740000f404d02980490400740996025a000003001400d5014001c1941042c40c1610841009500c5107643c1c40d02070a045490845807100200030001c0740c4590580e0002407400070050502c0381400c1e4401c040109011840d003c01001c518054125922090300c0c0a21303503528541c8944032041c0aa13040348040c00b000c540906200c19151240f8459013075500c01900303000d8007525000c2c080c5c0300c21600c0e01080c003082c00c8076125001f07000f007500c2c407240c00c0c440805031030315020b02009604003810720940070202e40d1850142d05a000b030742c0240c0303098880200004044080c40102e11040b2040c800581c80f414034070314004c140100500317908c204400003600d8503080c02d03442816503d201c10300c1522650700104000501c000000c0808102c1c0400d0381100701381c0c0158841c16a60f8500d030844503880747d990004100b00c1c50085046a9001c03242c4492981c8520040070b0394048201d241c4800d030300480c10001e50400c42c001c04100e1819400e5210327801d16 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 822292302 1250 822291052 822291059
    0xf040f0222060219290f091b0f041e0504060b0f0102031c0b100504080f0604080a050c0c0414041709031b18090d03110406090311130507030614030c0109 67
    0x281280d420341d00b0382e03e0171080340103c140078842000122615102000c01c854504040ca400c4c600b2001c010620301e4990000c411044c4102122500300c06400c608076000c80c2824003070000078000b8a820250500d2082c51503a0203240304000d03801c070500c144e014907010070851442c64140000410303150029801600100b180400c414441101035503030001446000408501c4080440d180a14412510b000705101040c204450001001054019510500580b045082c50380c0d0303110850103211045028080041840d22003107404100000d10690002d2052008000d03a49411940000540b0700303072551010074034004c6100d0914800c0700c450304405001050850b00008a00003405c1082501680c001142c00c2e4092280c107114400074055800304020f0301560041c4103001c0c0c02c503040850000b100300c0d82480200b0907070b80c0002012049035008185041d01a2903400000c00980703d401600100a1030001481801ca9042e030001c0143c91302c0b03151080079812074030105071352204d00300342450000300118400d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 822293552 1250 822292302 822292333
    0xc03131401083601060b0706051e01170c0a14091003030905040b0102031215100e13020f130902130504110901050c030d0f0c0813050d08060f040f02220602 68
    0x302c1d0461055049101100300f007800ca68291405075000f0030040b1000b25000040c820b041c801d0580080b0944a03091034004400c0c2580441c40d414840c0d0311004405d54030b0314504400502041410300b000402c3c1900c29070310b9120b096002002b90b42214021000c02c0c0010f0141c00345141450156034041d1540e41449241104010246c100d8000c91130441c00140a00b20b0a207d8003012070b03004960b090b11001044c440740060144804a001e1000c0412000f80840c040540b244440c0102c407484203400569541d50501e4803000381e06c0b0f04604c40c4040c100040c80000c00c42d44641c00f8000c02508403444040907542c400801003580c001c40348548101e5000c1143c1c900a6014100a041559220007038905114202000000f203c214000015009031107816803000c40d5448004158000c0c812015030b1400301c0036448081d600d01442e03a0a40c144209103001ca5038503910176031821a000001002400f901c5846080707003000c2c0d044000400007140340200211212400314840390301b990302760b42c001c01c0d1080035514007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 822294802 1250 822293552 822293611
    0x130807090f0234020411070b0c07120305040614070c030206150a05060a03060302190e0711210c0a0c21050d05030c0d020d0c080603011b050c01020c0313140108 70
    0x114510300450f00d03040380c01a2128010312408000c40c80c0c455441d1091030510b018203400090083d00c0b000ca04014000c005010000c8851450306d00e4a4001080c4d9542d1820348000c00c1d1130000101d140024074100b000160384400e070f03105034500c603500b03540302c0d0346481c025190b00e44d44480e20644e10004442c0107010b6410503602400d200365039842d002c511944e4a40120320740300c1580d00c01210050100c1014400300c09440f0440750420560314019080e2000315040607150034064040701115001143c105442c502c0180580d40c440070b0707a1f0107580440035581380508002e0064441c3d54028020308810103000002c03904c00010460304940a40b05020700030008558645c001084c0c818a100d05121240d103240300c51010f0b0045603081d0382c0016003c01d1000000c0c201c94002448903200e6070500314644c00c02d000e201c0691403181c415003060394581d0384100d4090301900864220400c80d10000c60401040700c402c2080008851100d2003d0304028000001101c603000308890040c5030000e07069412124404c044103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 822296052 1250 822294802 822294877
    0x71119050103020c1c120612022b1209170a030206010b0319061715011404020a0c02031506010f0804030203040e0703021204030225030209060103090503130807090f02 73
    0x107940310f01780c8030744803600e0030190139003c18000b0712122144c004801c00761150b01c0203000c0b060106140541d244c0d000840c201d4034107403903c00900d03000307415064498030080580c40c0d05a000c5001e003900d03e05603100070f181700054031801c1c0342024000141c0280c02c4011640900d49038045d405000c4c5682460b050400310350019155140023042456041113005691040708098035280442e4103640c1481c4020610b00400c100c00c81c12520390001c010050b8103c14420007400d16001d45016071901d0110b002520100d0107a0310194150244010882d0180d81502a152003140241c903442d010101983c0100c540a4048a0044c00360348100801d0016511000d01c407580840945800361038902d009008500200c410b850032809a804039680c2d910003494803442d0315400c0e400302c800000141c9950000b4500040c0513200c58103141c0c2c1c0c0e03580c440c1072080601c112510a6115500f030070115537203040c40781c5e4480f5640f0910354031501e410101440c1820340e0084540360070300081a405440d03628500f20000418025 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 822297302 1250 822296052 822296077
    0x4030e04060f0b2a030d06233111030405071d0609040f0503120907080a0c0506070807020901030f020411031513021b010203061005070b0f090a1707111905010302 71
    0x14511210504d0400082c000c1b41c210150200b842460040040007000c90344e00c0b814500c40400d84a0801611f803001048085400c0092142284e1340b0610081c0391004200d0381007c04904140600c400441003000850295215408603400256030300c03611503003040c0200c5116802d40c42640400e100d880c01c850011b402a0041c2c26003402000f043d902e03645554484500754070041e129100700b0008840a000150050031100301070201d10a0076620680202d10602031180b00e9030b40401d401050000c2c4500b0b440d0416405410380c14696181d08008111000d0148100c0c800d030b00b0002015003400f100d10507070b40105901700701d13280d00b10426400c000701a0200d2580501107039080c0b001d0703022800070605030300090520000060703072401d1117002d1000b02403601c0b0300c031340505c0002c00a21001905150f400343e030150080c020f050a503155101460304222044002070700c1503030414890f541e181001c80c000c049080c4295480040f41c403400003440b03114001c172840d80880c0d960907601006254000d03001480f01d02e9048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 822298552 1250 822297302 822297367
    0x5040e0a1104090201270b27030607020a08130b1b01060617010e190507090501230a140c010603080405040509010b0306011a190c1403090d12031404030e04060f0b 71
    0x200003031002ca40140706140c64078600e15142c0381b210000d019044d00d88c100140c01521041c506000702a680d45e01140e030003071401400040c0c031200b1194242100010345400481c040d80ca4410f0580c50501002c40c0d030030148103502e00000001d4560140460b02068510703c0c101c4031440e86840c2c1038000c80c80c001014040404c8010441c01d080d51914410903104180e603450b100b21440c20311000601d00c101c00071101e0980300181c3d83e81200c40d0f24a00c15640d0450851406070310b0b031041c90000c1d103847c0c040c0140018256007445800310410485d64041c10641e6002d0b2410801e82d0390b40c2048a0a99000c0c1c805203405802982c010302c1103860600b55080e1001c50704170305515280c58402c004140d5641911102c0c00500c4040c2504c0400003904442d214070642031000b1814407850100090f030005045800401da146104801d100745d60003a0050318281c001000348100c0381c030713150401900c0a1a61546644100d250150200c0e0103400d01036800240c4100700c102606103440c40c42000d4142c21400c16284405518 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 822299802 1250 822298552 822298559
    0xf09060e060901120504080c0c0d1e05030d020c031e1c0506010507020a0f08160609181d01050405011b020606060d0209060f0a26060103050a0605040e0a110409020127 73
    0x1d17009090141f840b9074070881d80c070300f00c0c06141803d206002807221310440c4000048000700740095141d001070f07020f81032005081c500da032a05510350310440c1101c08a590000c2001c14200d100800502410040c1e0315500b40c0904084480b110b0f80d204010540c000307a00745407a500d09490305030740101d0f4441d5041c103040d450100700f078000429242c83c1d0381c09451030900c41e030801c0c00034020500080e5602d142e002030340001e41d82000405020548107009541c03049404811000d0031119070380108164074000c60b445601b03040c100900038003a0800b100c003a01d06600b400c00e007980e5100f5408140101c80040c2e8043c1281e6181c0740100035081d4404241400741316001d100c6020a0381c0c914004140303480c1c44410f155a10800b032030025115006c0d0550000c0c540780c0c0d42400a100c010800d00540d4485024038000450b5501c0e400741d4002002280c100d41c0c4c000e46014135005c3c1050780000c030b800010b4014600303000000e05200401095800c002030090001e2071000014103182003400701c0142c0d044107080700410305d544 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 822301052 1250 822299802 822299837
    0xa0e03090312180109050a14150307080609250309140610030c080307020105070303090318060e0901080d0e101e050315040917070227070f09060e060901 67
    0x1802240504190300003d100da80341e03201e03070500e001000002e08100e10054a000c00155100c15076201d00005890440f43c4807a01c2d135600c0c1036641100408018054482c01c3c068001040c1c1c44044a50700e0041e091000407900781d00c00030882c0c03c1e014410541e010b07050241010210003070000c1800482d032840c082129158400003d0107603071721481c50400690500f620354181107c401c0754546c41020702c1c0e041040074a000d030740c2c000120b60031a80c060030b000c01c903818103140889100702054895100c1c0e5104880120340542e010031406c040e0304c001c440106459072181501910303469000a0340c0081694070581c0a00f60030f1442c060b0029008078240342100c08d14110441071307070030031800980700026000000c1280522903400c00320f200c0d480998041001c491a170340c46040c003150092105142c40b00c0843c0100c11507641d26041c1904030034011042d00604505a807214640805032501004656060180d028803071007400c0c03000403100c0ca582ca01011041141c2407001c2544001c0e08641041603440000c3e800d00c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 822302158 1106 822301052 822301063
    0x19080a02150c07030b1f080601031b030c0b0d18020d1704170606010f080f0402011d09040309051302041d06031e010902010207050114030a0e030903 65
    0x190001c07040300040c010342c411200d151003420404810481200b42c0e0b180280042d1a948103030080303807101c841a01c0100c1c06141c1d40307580b240340100081a00e4690000201010003c0198207649a46440b110190907070841190080c001440310b40e00d0308588145d5a0108441c070052200318035940c0064540e014000010300b0208010305c0f10285025840e00300c6005080c0d102000c0b0643da207040d0f201e522681c00322400313030200301e09c41d00c00e100d01070181e00701c0c80c407903008044091a240e4640c2c0c01901c003400d640c2103d5030b20020080071082141c13140580a07015902075250000d502d841d11040001c8101c20b00171805400f40107100401c0702c0384480c2110001c11040543e8100c16070744d10400f1a251103541103903101542104202060b1200301035209001090003a403c0d03d010075118401954141600c036010320480c1e0003040001c0b14402c00c1c0d48041960700e00700c006d40b49416003410000c0d1425 = true := by decide +kernel

theorem cover : BRFrame.Cov 822122302 822302158 := by
  have h0 := BRFrame.cov_init 822122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 822122302 ≤ n) (h2 : n < 822302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
