-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0573
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:30:54.231538+00:00
-- url     : https://prove2.me/submissions/2b5a3b5a-72ba-4bd4-9471-a0717fe00349

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 102877697 ≤ n < 103057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 102878947 1250 102877697 102877699
    0x30e010608191509020603070c0b09030322031103030a020c1203060604170c06030a05070201050a15090906020f030c04060206100605090d050c0d06051b032511011109040b0906 77
    0x14040c000215407803e000c0001100c140001140140103035001c5059980700b01c1d000030008410010b450104602800840c0c2c000c0c007220000d50a509140240360401c90045091000070141c1c4043c11303040500400089502140c010250303912498411982030182d84054162245400707010496240c059030801660f0180002a1078681424141150210584201e400a0701541301d5501c060205030f5440c0025489031545940c0030035103040040029007501c03005010821140c2c00c01585d0703c1c0300c0d0424605030044038940d200c045201401c03814100003d125001618401020000c00c0000350b01c20034006200b2540590b080b150245d85031804203044401501039040001c504009041d000d02d048461206428020f42c20b580700ca5103150000307005081559022141c840d161301c00c20815650b1181c00c1c02d041c68142c5562483d600c0d00701c0030940d02d8480110b820942040c21710700f9088031440351501480d4018982c0c020010070b60080d510700c0c03003508002c3c0084d1051b41403a960141a040c02c0007840d0082e00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 102880197 1250 102878947 102878983
    0x51f03050d0302030c0d0608030901080c1e030604150e040b10180908090d0f050f0d051603020a08030103051606030204120303050702010b180411060c0304030303110405090106030e010608 82
    0x16000d0350441c06540003405c1050412070038041a403c614440c0304220081a4500c0111b40c0c03491840700140c0643e10042460700b0302c804c24000004200300c0034104607088909581e010366290703150f100040040111003030040f50881d001e200403490440c1e0035402030190340941d05040c40b0365a00c07c420300c107070042800b030040858910100c80c50102c40b25081542950720696041e0b00f4490032130040f0f01010302c504c3c0c0035500c02d4080d02100c0c05000c0184284070152a80d01c02405442c2140d0388007401a00c141c590024041c01084001004c0c0752083c047c2400e140e07030004220307a90356584e091260352118034080c0006001020400020518082d2080754101e911070050208407180c00d49003500146401440380c001c1d075481d4100c0d40a0f0303540e010724088504803440d1451416003040d00b801c10b200c40002007018050442000070111810f80002a10f003141d03890310b8040b40b00d05104403084018004c0da4001e58008a01c0c00000c01d659130143c002c1c42c040180c234170003000030fa640c4c2c43c1400d43e641c4141c0140f6040b00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 102881447 1250 102880197 102880213
    0x60901031a070507080c010209150910110f0109120314100e070e150c010506090103170705010b04020711040b1008010b2505030301030227060f040b0a0801051f0305 72
    0x154070880003aa01c54000e00307046081c4051a154140103a12080c695a0142d500040804882c5411b07a8107070f02e10041c0c502228145500036010914080d52180c16174244119550103401c20348080104144682c10807009004030920351802c00d020100c07814100c1c000c282004002c255400f4a003800c140b0448222040021282ca0611051941e52020300700b98100038050900c3c1d01262500605400f1024080402e1039442600140c81e0782110405403a1900c52441100100041450440c0620b4040090595180d946e0b50a281803401001803191040d00300340041889018001d80ea00180007a40d804d407014030081e8928000c108001c40e0042c201c3d0040348502c0014806031520350042c12203469559524100c08107030a4081d0340e1a41c0590048440f50b00000050086081c409020400c0558410340b501020080c2d01150507107680040c80180582c4224600341d00964464001415114000d46544285d545520415020b808101c3d249806041076600030146c0d00c141b800d131001182d8000c03001d0f00344a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 102882697 1250 102881447 102881483
    0x3090302060a02160f1503051512030408240601110d05090d0203030c01061a040b0a030506010302070206030a050a0c020d08160903020303030a0f0c03020403150908040f030b01050906090103 83
    0x42e0419003041045106803000c0c019503254400d2800c0260200520482a540c60b160180e200e072052052180101400c080a00c814005034064203a40303d001101c40740c81c1c1b109640e61f818031f18016540304001501c01c041e00801200307142c815a0f0140f00b0806016141070355500c00541d150694032494091951110002d0382003140b18101400b44038074010604001241c2c1134000900d140c01200d60091181d43d154003c1040c40002d00350342021098402c502c90800b0f141c81140c0e0042d000c3c0b80000000e0607201c0c0e002030441c1e8820340c11a41580e070b0007000c540d101d0801586007001000b04403040c603001850070384940c204500005484e014035400d41c0d1a00b6903661a0310822007440c00900b60b840a200f10450301100503a010302c0a18802e404c14100020750b00182201c501c20350b010458242c05041c81004140041400b540c201440f203060100c0c0841c0e022010310b00080107100e0741e48062040c0c0f00265000c000c10000451441c12508111158140c0c0d8450070104150300c0381c00e104c0101143c0d49000031840d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 102883947 1250 102882697 102882709
    0xc02040917040929030a082508090306070813150e0f24010b19180801020a140301140d05010b100f1211030601050c010603060e010606170403090302 65
    0x5041c1c428102080601c90655400740381d60003640080351455101c07031482e21030700c0c4602c41d031200048030700c4900144901040c0c0030a4841c012003030040c002520000301100d00d00c1d0344942480300808801010061880f950030019a207801c034240c483d10a010740b4004c0380c0054400c5038841d00440000700c007890095801e94440d01044d00c1100f6520f403054456034000c07601502405112140c4030300c040900700e144000760844c0c41400c0e04540042c10445503000500c01503401d201609d54180c042610618917070580c440a0312445511405032824081114000c10440c0c41034000e850307015081d0329010080c02201d031069040c0d000901a46418181490b0036a10030315002c18002c1c6064020000020b04040d40b03000311f10359000c440c40140226400d108c04c005155840104062519840c117410441e110000c051460903120242c1380604001010980c85a140000c0d84120001c66210b6420065104052a5240681034074401d1002150580203000c0d0046540c00c9000d214030350595452500b07604682c00c10103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 102885197 1250 102883947 102883961
    0x111b0a05040b0418060501050306160f0c0515090714030109110607030909020403060203060a0503150604151214010c090605090913080d05010305010b040903021e03121311100c0204 79
    0x2d40281c44503442001d40314007060711862240117813000300e52981445c090510b03042029100b800e15112001c80d90751744a611101c540c458070b4035840c0c80c410045441c2880e81c54019100e40013010401581e050001d54074000540c0d0303086442c8007120300358024034482094200c071210358015140d45802d2501d00d646240290003015468801d040401c2402c1e1909894030403a002a0022521558004280034203458044150001401e0450049c408800254001e5001c00c6018081e81d004640305c0340ea00c00080c0c0f00e64004070240007541c1c1400c5581c002410480c109580581c184689940380403103810030300344135079880025034146880c1c040c40d0203195000d2007a8000020518441c45030178104401c00504690b00400c1c041c8010b80c0e011402c0e50460820a08480004c03010701d10030391400f00001c0c0041e401240760340d00703121000303100da034074502d00c1c0c820f141140f08035086a000c8444c1c03c0c0410484503e05500030030954040c1a141003844840010310400003030545c0c1c103001040c1140b031402c0c0180b07040d40100b2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 102886447 1250 102885197 102885199
    0x270a060f02220501080c040b07170c01020a03090614040206070b061309030509030106050609030c010e2e09090c081303110f2103060a210210111b0a05040b 68
    0x14601000b80c05241100414020580610000102e08220940c2d204283c0e41e081001420424602490184000c01e144103003e4028205895203c4541d625203085065a07200941c21009540e42c1c1e40c4418014001c00c0e415500b00c031649c1c0740c840d1040d0300420f10364040d4801d40e4060080c91a2204ae5112005121402001c8070f501072094418420400003c0c0500038229219446103901d5040ba50101400d403100303504190f020790424058552140e40001e4840210003080c2032601d6000001c0d00420000300c1c503407080107030340700303d840800200703030004005000c02402550320744945c2d0303850712000801c0e1950510178500080600001c02e150261601420550038800c0c03c006d90345103002c84401d810140010040052a0003000505484a019408407006001030320a842d2170340c030708000001c41030201c1b030107103158890754a10600c60741e08016078070000098004200c034420b0340310020000c1c500c1c3c0c80c0703080030711450041d00c0c444c200204000e10344011503500200407412582c1004284001000d400c0206 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 102887697 1250 102886447 102886451
    0x30303061908030a030e0607020c0604060c0503070b04050604230c091806010b0406020706020a0c2706260604050606060a09030602040e060102070605190c0606030812270a060f 77
    0x60030190800040c0701070102c9440104001c8521070a450170520000c1010723055400c4120030304001c0d40d0380e804907000d0303038858100041002d6142c20300e58614025190014005190403050000b403004c000344580c840e510801d200020b041e14640c04c3e038901004440d03075044542c000c0003180158a844089103030b100b07221176503210300440d40c01026440e29200b07a00c41a03841d8000902803100301d90600900b40900403a0005058090382940d40e0810f403c1944104403207810341c8405c221011300c10611445081d03440081c2403001c0c1d5115001c4205001d95003d1a003200081581e05004040010514510698105000e4440ca40e01d00c0244402c1d9882204003500304042c0020100020f040c03031000c0e0002d004011040c628510741000064607010940d00702c4402d0200c00d1044645802e000c480c0401d0102032450080d440d1030291038035038043d01458100030020b0001040d10099005446981c0b4070446915001c0100c4231a0441e6812214215000000068022518900c00f2414581080403510152000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 102888947 1250 102887697 102887699
    0x314071104050a090308062409060c07030302060601080f090c01030504081306081b04030b1b0906040801090c150509010e0a050306010602060a0e010506130915020a05071704050303030619 82
    0x6070448408440c0144420b50b0303884038100380741d4001d003036540c0f0003c103403811001036400403154583c0110350031200000c241c00040024890301d82d201074a80e1010ba4034107e030002034682c5800703910f0712400c07902c0d180028803c40c00030748d40150180505000350754203400b806070409800011030290038010400d6411502c2040004519030b02d941d0720700000c10b440c1d40c1d044e8540c144504040c000707c44448440d0844c2c00b05000034404142031061094000306d15016144014844007003840a40c011944078039031001c8040380000b41354030103410411026104910104106444036054081c40c220100309400081040c03140601c0c03940192440014000024002d03407400d6640c00000703242002c240c00c10001a0800c03400e0000c20407480c0200790304070032004000e01051400c3c401092010380c1100103041145d0300c850682c5c0038800e8526111840038020201907540350355000e4058101d134402e010840700080e004464181812200e020350702900c0004024525580301d01e02001014205040703200d2008847c0300c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 102890197 1250 102888947 102888949
    0xa0f050c0703320c0102250b07230f0c100905040e0d1707020a02090a0f0c0206060a0609030b04111c0303151502060103060e01110d0f05011203140711 66
    0x40c0c650220310010f078060a903491001e09a440881003003903c18810380c4207464011590383c0110f0540c8a4518140203904015072001181503400702c15845664400c80c001901c00600041c500e10701056009031400403554100d080c0070f2562195a48003003a441d811070b0304080714900c3c15612282c5104d10034580804c201d6200c20000b07040780c15400041c425603107c0c241014103550809040c3e0340d100102e000744103143c54012800380d200c004440000384203801100014400c20410343c05030056500506c0700304040c544400c1c000e5554481030b281940b185a49020024a00f03220701480b200384c84c3d004100442940307865558000d01300004580c03a070700103a840f144002c6150010200c08206020b550045058031082c18075580a04103030b04100f403992850010b003405940c0000c0c45034112944a030000403107003103201c0d5050060482442105d103203d00005d03000c1c1e01800c560000d42d094002c01000300003d9a0707822004a041550060080205465904085240050101070b00d98140585002c1301c1d0b05150350 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 102891447 1250 102890197 102890213
    0x9040f110f120616050712030c03020c0d08040339060204031502030402090a05010b032404090503090310180f030c0204050c0d060801020c0a020603060a0b0301170f030a0f050c0703 79
    0x2600c65026032001d0708111100c5405030070109212903904100d03143c820300f070b101c5d91480c10000314800e0505803274159003030000e8404d50407034292080c80e8098a901c243d81e058001c00d940002e41c6d003900000c80080704c0c4030300300c1c440d99400089103c107e0700d50300c031081c03080d901d846240070381000917034032250309100c0000841e480840c1713500349003602e840050392450544100300410300081c00010650b8601801481316184136811030350007a07040b004030088818110b140d10040c1c2c010352411900241031007a61410880004042d044480c0c08030191a400340001c000c03081165203051001d540705000042e40c401150004007095800e5000c0d240c03441c88c0308030907000706050f80d00a407003a4200c0c010000d00c05123480407030700c1500064074125009610b420a4451400d54507260303400041e106d240b000000c10300c03d558510445005041c0da1680a4032503a403a00004c0c1a0440071803680b0742d82c001c1c00c030782c4140d003a00401140c0c529509500c4203034203142042d108a0f01508101e481754000e100c0c01707a020003c90103207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 102892697 1250 102891447 102891469
    0x60f16080f2101120f020f12120403051209030a03080901020f04350709020c01020d0504030305040209010807030b0115050904150602070503010203010e0a1e050405010209010e09040f110f 82
    0x2001c1c0034040c002c551500d0b00745844164010840382c403400d07a40c2d0300000c80300a103030301090340c040700e21a00b1440b040c0000b0f100c4001c80b05e11001c041c8215406400340c500b006003e4011240110301796142c6258444810300306110b030316078031a07141e0044038030500040c0c020502660404a50800141000d442c040c00e1112680140c020b2808190074410030910307122a00100010250040401d8440e080321a016943d10800780c01802c00712a008224044101800d5043d0340c40300544a00c14000307400d042c140134000b02000d41d0180d00417000b800000c20145800a8018100c03940010f05607202d80c13030240c145510300c4402ca050403c1000030000c1410755a40c038040c02a01e560400f4001032464a00f80d0003074030304000d99005902990040c001000220501c0001c10b511074603403400852619101103201311124100041000c3c0d992a0400344400c1c02415806088454001c0c0c8501139441b400c4400c010180d03a007218010301c1303401c91703401d100000380c0c51041c0c101c1141c00141c842c0280066820001d5031040b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 102893947 1250 102892697 102892717
    0xc1b0604051605031606110a050111031e07050a03050402041d060601030e070803030c0903010b030d0305100f1203030b0a08030a080f01090b061605070e04080702010e060f16080f 78
    0x1915025218a00d1404420b0080004070014411104503c2c200c40c800400e0384104014400b20a0001550003030a0040e00c868643c040020032400300071031800034031500700340c9520750711f040da00201d5404062811400c60040803c0c5d11500e06040c3c0140d41203000c4c150080040383c21030f4490307900c4103445491758000405150128003074016031401c1000141100d504585030003140e4090785080002c2503001c01280d8000201c00b452560b18101c0c03402103400750066589039901480b42190101d10309916a100d9806401d891581502c015074407503042c00020303803501a01070400501c105003000a030090340010550700b40940f14030001c503038503d2404e003541c02000789040410b54100c1000003200121005501400100404102c0f5a400e800412540d0080c0442d0491a001c4104460705101c01007220000501c44500b40900c2c620700340c80c154690b504124012404181c0c09071001031a46070403c16909001c2000200c14141f0701c14181c002200071036401d06032408075042002209040ba03201c010648070030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 102895197 1250 102893947 102893953
    0x905130c03150c08160804021503090d030608010b01050d0e150a0903110613080d020405060307090305010533010e0301020a030c0f14070b1504090510060b03040b0c1b060405 76
    0x103001c2c600c6080da8244280303c42080510800c10003088010403002c81428514a070003486030740c4a1020134404040c40894600340328004c401c00510800024010313000c1342003540c05122140e681d80c200350036a00802030182c08a4018040031403603840507401030260300c0c265411030380c0404c0320140d0404280c1d000e83c0d03140c01c9241c075461114103054001c100520b8159811008101d2442c0000d00040c600c810354100074071070580003a408075040b0b00344c0c0565001e4070004150680c0c90500e00000f4040b09203a100841d2203508120000f500702030500401c004c140c0395004a0110980e00c42c40d05800112803c0f81030707050010364440281a903c091000d00614000c0d500c002600714041c000c00b80603019040714807c10080f0300303180014001c080303100341d458140c0d01040c50040d94807010b9400c00001d111208003a007251504800300c0034002c000501001d40c480c040003c10149445440c80700c07403440308690140c5917411550101e4002c1d20301100802c6011b42c0000c844049001d1740d00060b00b030640c250350a0f43c00343c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 102896447 1250 102895197 102895223
    0x180605040804091410060e0d05190204060b0c10020a050c0601030602090301050108070b12073e072102210703030806180f040201110709050f01120302070905130c03 72
    0x40c0d41c2e846000441660340c1d00d9004030340381c00c005000e284042d5015a80800c0b2101f08841415210884100d620315404410340314144030b5030110810b80c03446480282d10807030501c040040d0481c03d00044a80d15020791014001780c007840d020340006580302d40410000c0120030090509500b506001c0140610300c00c04016030740d000e004003010300790760301a00850030f5034020000c10800010b01c0001c444141102d4143c8009640e1054010b8941e51001c16906807040d150100902c540f2040a15607601030700302c0349001c800c58100300901c40d5600068005c1d1000392100000650f5105008070403052607034802030203032040c550303022110230407041d41d400f26060070b51101c0c1c1d060040542000c903040d032001054075000000e0b102e1061910685401070541c4003040500342c00714065921440b0162071042e03800c400c50b81010b03682c1062200505048514100600c0d0840020800c0c02d500000e00740703483d03010b50080600900b8444150000c100161440a1455040030300c400043e803209009070065000300d140068503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 102897697 1250 102896447 102896459
    0xf011b030c0c1b03080f1315051605030415020d020106080c0915040906110405040506030a050304150c1b330f020f010905010506100201020f040603180605040804 71
    0x8155010101410305010140d8080c0b58000c40e6403551580100c0e0019501d40039010305030010401e900060f202207000188540061941c41c02010010401a40400b03800e0395607405407004050031401c6000500d041102c2e14414101480001c14140110203691906507a2050030441e01c9030051020050307000650598803403502845450300030070b001c0c005040ca03500c4080c00aaa00c40d8000d00d60b111000005403000d040b500c0c1c90780005505070340b0801c20803002c6500309140d111070300103111b898419414200054880d05002c5004120503030f11100650070141031000300c41c2d0842c003480c0d2420070040c040d001c00002c10440b813804440300760301c802e82551090414000c01081240c0c01c5c8107a111000f03414910301d0b07101c03158002400d01d00c0181360800c41c142c11208200d007030202c0c405014200f9828045040c00b44401035020500410040f52104142d81c034800041c2d00b40e010365940036031034101c203002c00c0242c0350098000d01d6a6107481d250075110300c20703a5550700049860a0300d0030349980002150610070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 102898947 1250 102897697 102897731
    0x91401030309060807050a1b02150301080c010219080c12040906090b03010b030705040e03070b040507080c01020a0b0f040c03140f1e03030105040207020103060302120303190216030e01020f0f01 85
    0x54440c526002025203005e00010304039200303120207141004050800c0741d0181c00360110081c0126030040c00310403822a281d40c110299003003805808594001c074041d030321044d0b00000f12001980325a40790000d840c85a500e81400c5604445840b4811340948801c8406030350340440100060000000b000906504050a5400315802c4154142c0039a240c1080d4041a40c4c5c0055100201d074021500891500d1006880c0c41c00c60189880080c04c401246044c00100040441c89609448042080f600c00c0e0781c68400481c1d43c0c4800c4000540700400510128180028040015a2050060041658841d0790340d940142865614001e60320303640208a8003d0340da0001e000c1c010f40041e2540010184181580000d40c980c40188030740c504c500d078005294011a40243c00c62401540c0003010028440c47c0c03080314980f65403080f100060b0a250b0183c40240c982040e1080c1c0c0c550440c2034074030140500c11950141c0301c01e1010050141984550346001c00710440400014044d4034041c400801c2c850540450380322 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 102900197 1250 102898947 102898949
    0x615070b0a0b01090b0306090a1503051f0501050901090f06051008060109080d050409021303061104030507062a030e0a060306030b0603241513020306011209080d15091401030309 78
    0x10400070403044c104102d080520603250032030340440b81c0008503200d1000403002032240203000300001c03004000000900c2004111034010070458070004161502d151042d004952090041960250400f8018031190106a1000c0c0c2c880340c0392031000448580350307400100710f8400c0608010014058004000300ca582c4005c203040180300060040c030582046800141c0980120300914529550200340e415040b01c03000c031a58011500b003481004441761609030000140e000c0d0100b958079205507440000c8072841081c480c1e121002901401d01000c0086880d00e018222094007a400c1003040302c0701e1a0b90359160a0000c000301020b4400280252440c40c000420790303c01001d0500c40d42241c900170555040d024180341006840e442c50f032000e42d42e41c00340382403040c428080054000311042101220181d09900a43c012903090702c80281081d4520b841805030b400c5401c0c020048001030001c0707e00c130f03019034011158000441400b0030710300340c030742c6c96100484011482541c400c0310244010020f064208403104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 102901447 1250 102900197 102900199
    0xb01051207031707260c06010b040617042402090103061202090703150905010605040e0603030702030d03020d0b0d050a020f0904031407030c121e050702030705090615070b0a0b 77
    0x11210902c0c1d03444081c80090000035200c1c0b8900001000d4080002c1d0318880c1001c201900d21100400940807000c0c40190002e940c0118240b0602c0004a44d911501042d9400c413221546da20052074082c0c1107130b904130000a08115401031038200d40c5141d45c0c3d640030710301c01d09661005006880f00324000004051b1130f400e5019503c9615010402c0c40941c54080d035081d0301010030300300421880120309040800404907444080d2141c80c10001145056002004000f203414410350407544d40c94007020140c4a10420400941c59070200b510305c03850034045e0700945103524544200140002c10103003c44c104015020302241d45400c02021074045190114241c1001c000540d11400301d440c0a030740250243c048462161000388000c2201d204261042c00c0390716229900010201c6506046080075090004c0c1cbc503440c1d0302103010b0004103d64540700d08150b4880d90340050092412601d4034080c48400740001d086543c0040d2020445e11002d4140d000414000307124060406980c41c0100081c07040301c24000c255 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 102902697 1250 102901447 102901453
    0xf031e0e090a061a0705030c0d02030306042a0f02030409060905010503150907141c0303090b062d030703060615110601050a06050c0703060c0c060f110a0c050f0a0b010512 75
    0x10700c90720150b10489440449404e200554031240d9007007492540c015034066001c14030030700780300c58181540032002e503002d140192400d10046860003042c84444010084480c445401d2042900b5080c0c4a0103808480d5650b60050380d02d4103482d40010800e03280c2a4008401a036156801040b85080400c440420030f0201c3c50380b00f85504080c20040e440303040610075081001c00220b543d40040c1d03039540c2c4c002050b00c01080b60340b40100140c0b4020303014042d07074101507800b1124000042c140c2d04180c15a80d40c8105500440c13400f10a0041d0010751892035030000c13079090b20036190007000282842c0306000140c107a500548180e03c0c042c02c4004e000c207551035919034031900040b00400c059183c2c11241000d840a0b42415521040c03913000480c07800400c0c0e84054030b00750600c007038100c20503045170400c01c0362030103800e05120001c0b900004c08182c4990060030620724038104078000c6654898001d0340b0b41a8419400e4803030090304c06051a01d442d41c0d5060030340d400e10300c4400410480c0346c03204200654100712405 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 102903947 1250 102902697 102902699
    0x40c0f06020106060e040f1413110d030918060e0f06010806030109120309050a05010c0519021513061401060e0f01081003080f040308180a060206040f0818031203040c080601120f031e0e090a06 84
    0x4008075581d01c1910403000950320801079001c000d400a60140032091070250c11171030701c0100700c40388500c240c9146002c1882c95012a906003418003031a034103a500030b40403103801240120b00304c0c0201952002542c503400f0303012010000034001e000d14000e090850ba80c41da00c40910070700d101441002d1740d11001c1950b01081c036600c480c584455038a0340c420305004400e80400c2c0b00c0c1c1402406407501d030286c07403d074807641c400101d1241d030041800c2001c104280c3e50070000d400c62000540b001c05060f0707065400c0ca40c12006c1080000c400c800284451042108924240f50381ca94500559801c54010b448140d551150710a150b030408003a0742d8024030091006140318282a20b940071b6450080101500350040003602c1d02038846008030302948140081e08440d2030200942c01090307613400a50303041b20b0490358204001900d501c0090702905a912541340071450844d2543caa10800074281021005e100d2002240401d00c114042d40492000d00c2c0d8840c0c079540c40c080e4040002d082001070084511501d0000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 102905197 1250 102903947 102903953
    0x12050c150a0801030b2512050c09030601030b06190602010b031507080a0c2001020301030212121917070203070606060f05070204020c0312040c0f06020106060e040f1413110d 76
    0x2d1800d0440703401c40103a41d41c40d2a000b82c0380c05840721021610420044001440d01001d50000740314a00560610040206403548080404580b240d00c40050381644500c0041c0040303807034940e000f80c104100621258181c0b1044c4225403c980e010360014000d0b1355601038088030703030400b48110602940c0c3e4a820251030b2038001000b4140c03510150044141641e622402c2d1102c0e4040c10700c0c111071123008010025920a41c07420305020394800d01040b401070a00402c003100c0c04000103401c1c03428128140000e030818407800481c0c030045240c88034920402451112a41c02414a0402c00c1c0c010a807541c05155510294101036040e40c006500010800c01d9240c4520a40342e402001c1d1f50700a03a0440e00541c2d02c1c040c1c0011030b4618020500c204032086284800c0c001003200c0c0001c4082100c42c0074036405405a500c860a03400ca030740600c150400b2604654108483d0b29056120500e4a0081800040c0c8440058104c4558407012140a6404500d00005600b030003214241000e402e0021030743d00603c2c941aa07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 102906447 1250 102905197 102905207
    0x6040b06010206160e0f061803010f091205030411060d02040303020c0901030c1509150e0123030402040902031009060b19120204020c030f030903130603090b0402130612050c150a 78
    0x40310304d00070040b0083e10a40d00341e90344505440130020086c983c9031650228140d0164118a0301030b80e5200303604e00074038482003e00d82d01811440e540c00c80101a07401d00c02100c00d480c41d0303000500c22190142d40380454071941c1c1d6000090120712891800042c1c46509514000c3d02e0310b00440d0400d4400c0904900400000c1e110315145c0055035450004a00a00003d4809407101462a0001040c0b2082800802c00071907106400040c0100260f070b520b8842c941c6092140131141160300301d07500c00742c020400039001d03091542102011354400350885190f0400d80d102c42044910b0750000b100c0051300c4030505a82031074207040c410400b280c40b0360980011860b01c50100000089483c000703008a8011499001502c41442034a00c190140d44003541d03030303152a614241d12a0300072107003905400c2d0115070100e0301a120f03110700b29150360301642d0f260081c0c442d502008400121804048032141c1c480c040491180547e10749888140c3c403580090049445981c00c00034030311045215801aa0001d0001003074540e481 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 102907697 1250 102906447 102906481
    0x2030f0a1415040b0603090a0c0b0406020c15071505010e0c0408100c0c02150702031b0306150a0b040906080607031e020a0201061d090610080d080903091206040b06010206 75
    0x44410800c0d0620baa00840d000d0031842a00c2d40d80100d02004201c1c0718030000c991440340358444c3d90130003807040e02d404540283d03000358010781005030710803250030480c0d0411003c851160010f07035606c1c80c20010256100e013408103141b82c06000c072540b9800100285007002c81000c1c0c2141d00c920445003801c1c1001034859581c11000d980105aa80351040b554181d40a40307012481950003624100600c000001c40e0300d00c1d40d0103000120302030321804001004248844014440c1910001c020f4403c41d01d410a0890361500300300740481e88041580400203440340a1001080202201c910209600b440c0012090400724010500c0082c1420024005141ca80046808052131115040180c89190f146401c03401040c1981000528115100d000b03a000cbd44c0050725140724602a01c1110956540c0034829070901e1418824004c66901030720164001c05d010310540c5500c030940c1002c0303e003440d40600003d01080c1480d0910841c03500048240024080381c0c0c45000e80c481000e000034202c80c146940020911100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 102908947 1250 102907697 102907711
    0x6030612030e060f0703020f060a150b07021201020a120e01140403230301120212070308030621011506020d030b0a09020a050c0609030a1106040218070203070c030602030f0a14 77
    0x30300309222466a0f20241521410141000e02544480161401a54540a0000c240802e1040b08002056034446020f00701d0640c1c7c010f0b402c00742c404d01e80540002c03030f07401c038207800c9071f003e0310488881040c48400d00c0a000c0e00040b81d9070360346840366440b401d14112000a00c440a060341801540d68800e00c0f211f95441d0030a60514148050707140d090b6510200c00c480b01b01054480c0400000007541495102410120500850b03c0c4001a802a03004681d40d4405d413100a048120600002e40103242c161012070442c01c55145400030031a07540030403402c4561b403022803441044070103018010b4517410410f503040c070f107400e080400180f0440800613030955018481c1410040e00001c001c4259481903050380d2846104c1b20441c0d490303062030b140c00c6449030800075500000a1201c10703042440d00c0001070040c00342da00a4a903a035004040c0b0f5582c2c102c46002840c01055100801c41d40300002c1e81130515100440c0100c030016100d0030010313290b5485400207000c1400071818583d451103200c084666a07500140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 102910197 1250 102908947 102908957
    0x1a19111204150203070315120201020703030f050702150c010608031602101101020d0b0310180b041407030b24031b0a0504021c060b190305071e030c02070603061203 72
    0x10703480c5890b100d07229440441c012140d0010041c4807081d034054101404283c8000440c0c01217503283c00900040b900139080c00b90040e444038000b0400301c1c3c050404e012508640e40703001031a100c000d1700030440348600b90030410714600c0d0014481d0050030302071241a005d4504400594980711500380300c076103d1186090060320031010700c600c000c0d1041c0509440018001c01034000e40d1119000154680100403841545019003d101110750084031248a48030101c00c41503014082c030140d60303ca545107180010300495680e08003a9100504041c20410a0021882111640700b103180030030605280080200f01e0340c2c2c0740c688464843d11290742c0400d000001d00c1c2c03000f1000000e0030f03011001a1072001070307500254105200003001104031602e100b101034000c00078a014455140d41d05240358061090744007080e940035030141d4503900184640c0006412a040c0d14141101e5140340c0f1800040501610400000c02e54415000f280241c05015020080074107082c10811149041207904c180081002c00608201d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 102911447 1250 102910197 102910201
    0x607080603011d010203040201090515040902070c0815180601050603010303032319060503060408160302030418020702090f0c030117011806151a040b161a191112 71
    0x41ca0035482002c1049001100c641075440000c03030b030b900079841130703e00740e0006103031607004116810b2a1840c4d81904041c040540c1c60b040c60600542d00039044020b0032541903800c00c0d0001030300c0300b0400c4a0344944050740b04120003810a8540125006d004000030562074006100402c42c03940c51a055038112038044c20081066506600040b8103908510341c04411910360b0b000f4052038402120107025582e88582c7c00300000c64a90007019640c11086078001d0286100f044240d44000c5d640780940c960038824012207042540340c400b4640e03202d00450f81c4142e996408500c1c00107520b403e843e082d8000465030710608450030b1118074090f061005000740302c05401595508890100300354024007012480e1a050103002c901840c002014140c0d00708250a4104e07509804190240d4144154803000e500884652506162051207046500145a14240703000c0401d100c1010038540703811101544c000c58442c828510302202c030070781480c00754036a10f18000e207041182c4074400d5a10048078003c00541001008503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 102912697 1250 102911447 102911449
    0x90b0307030602091906020d09060e0a0605090105040305030301032f09060405090717010c0305010f14220f0903020f030f090906150c01050105010f031b080a0605040c020a050606030303010806070806 87
    0x201142d0072030001881784040001039035a8085146000c8002940d550180965540f5013110850102c46546600100d0380030100041070081008000f2000306061190826599803202403d40d0000d900c2a036002c09544d01080542c81031014121388001c5e00c55040e141803030b01c3d00103d140c01d003009000500032a5100d020030500e5400704007079401411780890465070380c003496907454007802000c040880400d082000225003016108400d6084ea8641050032580178440303405c002c81c0d40c516180d051501e00c030400000d4404c0d45140140000b00003c2e03034001c201a5100d281c000d03e0b009001032540099002072050001d0040410103c80403420100e032907204c641c85040c002400f4a0251034400c50484c00025031001290040d002079040750760980f05d9404400c83d4070016407c0d12415610f50300c40c5542000045c002034050705113143c00031001d8600142417501c5001090441d80100c4014002d03a00c1001064100a41085555402101038000e582554941030400d5034408000e01250107010b5610300091007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 102913947 1250 102912697 102912709
    0x80a02040504020a050705070603061815050603090c011403010f0909050f0109030f110c060f1602041e0501120f0f14010516120e06130206040902070302060709090b030703060209 78
    0x40c01c0024021580d90049480291066121702d4040311540655200050114083c0c402c0c041100ca000030350301e40c14001c070349030711000b0720340151701003400303511050b001c41c480c0c071041c0142d403150001000903c00401203400241c4006500068501031000070401405240d0041091004a90020302e001c24400d202d407900e2420840d042503244119071a0883c0f9105065000301350900018aa441b107400c961940e004158031010042c1065070490400c004103c00002c4803401410600d903c00510701c9642c5040e030009094414030020f1007081132060161070100243c901c1003500400b010030011605003c6030b61407100d0000028805080490b4290200301402002480301a80810170b8000300528079111107100d038503418a00d400c0001410707004100845000b184a183d030513034440700c000d240b103554000800d6605200c44104a0300f2010030f11001038000e01034005040d205201e5000b070100352500c00750061101c0c40d10342c82180c4440c00c1c01c01c00101510041110820b983c3c1005000d640e1b01d40301000700710 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 102915197 1250 102913947 102913949
    0x11404090501180f1a04020d080309010b0a090c030b010c0f0210141306110604050c12070801151e030f0b0c040e18060610140a020a0510060815070e01080a0204 70
    0x3038030140342d0403a0b00400032120021942c040c030541005c41421904442d4400e0100125070094002d07040288000214008201031544149043d002044010b60680800c10085c5190300c0b09562648400f041c1040c1601400340854041742880c028048010300e0310303003a10303d00c02d46001a002d256000c80104520b44158100c660007032400900c0c551f50f900514091039201d0384d51245000044110882d103209401c04034905010b242c01800070010f0358280b07400c00074000c0c241100c0c00d84521400c1000150001e0a02941500800d4000203103103261812458044100c56074030003500203041041306200240d400c4014250480e0004000c060310381d82c9032907110492080e50000010100318504015421040e0080e4440c15030042041e59900d4541c0400d0220074070020f00c0c0f08000c540745e031013010220a43e50010b400c8100441c4111180f4425649403207090080c44011100c9503500d4401c01c0c40121000c21403d1188008440290000d280210009148191001c402c0b410003800e480411000f07103417601660 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 102916447 1250 102915197 102915221
    0x4180216050a05010c030903170606041d0103110a08061f09060803090301060906050d021e04020c1c090b0909060d140d09090b0603190212070c02040e0105011404090501 74
    0xc419540e500306155203020741d00d401c640c0c641c208280419a5440f90044940241d07160720b882007171145081c07403400b18120091401d5042031080c400002c40c41940c004d08040c580c0c543d00419103a50450030301742e0003e1509508540603601030f0408100c103100014810764400c903c02c8400e02c520180f10700d00c034031039410b580c400720985003482c1c00450903100100c0203082d081000c41c0200102650b5451040a441d018428594010540c2c11a080942002c0c940c0fa45010744203240e00704000f1070540064201d030414002d502060740846841103a0481f0920642e103015540d042501c5124a00802d03000705101e03015100d4040d14560303001c24150344a00f04003100321980305160700c2001100c5400f10360354111190700003000401d01c00c2e000540750854032503d110403001502807441c60b6500b00c800c414020f0208800c40340c0a0342040403c2c1304000c03000e020783c040c2103a6a03946024003502c3c01044113480481d0303000c000c01d0745408010000a000d000c032200c8810b000356400700d00c4040c0c80c1401801485a9a03c207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 102917697 1250 102916447 102916477
    0x1060b030a0f1803090501050706060918140604150903021903080702010b011106040611130b0d0b2d0d1b030302010e060108030f0715091202100b0105041802 69
    0x200a907040660440410000088020404110340b50080c10205091100190100d07040f242c091190354408c0d0f000b816401e005020106038559195004001c50302181e050b00200f00301d95500c4420000182c2d203510b0304d14180c0d8010110342c20140c48032600c030003441034101c220550341c4043d00304050003403004a21115480024008036503c50401074103260040310740c000154a0070401504560050504808040d40c10000301851ba03281e969442c024088101002130015081c407a0310051035460001802034a165005192204818105c1d2019a1a81c190750b5200701e514640809034a05000100015120045440d4161001850106140b6030103060b001c3c00f4407030220540344440740c0c0e000c07100382128400c1c1c1c0204030320500031449031380365042070144d02d050750020070117115940948005032080e64040c0400360700300b44140313000d41d04441e0b004000700c40c202d00401c540c512417601405600c038800350390031041c03080384201c0000074100c1c412802410107111050201055406107a070603035030b40d08144064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 102918947 1250 102917697 102917701
    0x60501170c03071710140a06050d02031506040b070501140103050307031409120109140102030106052209020406030f290910030f0311240c0a030b090c1b0d0c03050a0201060b03 77
    0x19450031740c00900a18850724001c00c40764515003003002071901240e41c580e558174140134003180c101c40a5803000d024448902c100f001c3d04201d81d552280200010312000e020a03a40d901c041c034115083d1090140001c640b00d00a41c01000400e002004560040d585071500b201c0022480340310001398062140200c1c0c000a030080700b4000e160341580503220f424060700c2c034060010b00d0b0034956401e03440240a001c00013a003e20104000141804000d440003c0580aa80c4240d8030780d07c6002c2281c105902210010752200c00000c803510062060480d0f006400700017002e01c00b07481907100c00b5a20f45841c080e02500d00c5074005070445480c6141500650360002208158040c1c0c0e0070014261400000c0100190040400c1c00c106000703244500e208418a006002d00c00b9520814031092580102c0b8060051549419036a5896070f01c070000c49118201400445071030b0284072000c20424500c000104400d03510030034480e10501d4200c22030030b08060b0b040c0381166a0b0122068100e02610565000e030300b0803103002c02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 102920197 1250 102918947 102918961
    0xd0b011413090c06080c0702040c05030a05090109080301060e0105160614090601030309030b0619080708070b03060315040212010608031213030f110705060c01020d060501170c030717 80
    0x31580e059a4044544180380d4400c401e49008542e00303210700401c0300000035801c1169a02038010150303c1a46500560300b05541034010409443d900303030354000000e20000030000c0c4028548506074202100300003c00c10003d459840e6601e074030040c0918400d00034442c0310b40d82143e03c5101100c0440020841008118007a40b40c031002820a0a010800b0b001080c800030b1030381c0364009110341c1200d81560381d00b94030b140f0315140c103000302c10040e1006130080c0707220f4441200046025101c41c01843d00700000d010052804201d41c3c1008070f95004408008010003d2003403980e03000901600720b03400040304800380d861780d10000d101400940b03081035440d42000c20005100002002400742e6140e0400c0d40d030015a101d12341828041e0004500502180b007450801c0f20300d0344960110110720031481c0403a0245900e074000500c0d00c0d08207034005a40d680d0009440c1c0440c1c6418028580105020700f41800003030505501e031811804010031b2042c0c000d4000c40003a0b00c4520480d85a01c3d4401c0706684643d0300e080040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 102921447 1250 102920197 102920219
    0x70611070306061706010e0c03010e2502070501020c060c0c04151d06130b030a060903110f0303040512030105091303021c0509030f03030613020318070602030a0f02120a0e0d0b01 78
    0x582c0e03039138031406070f2000061444001e510340303445400d010318a1072940c0c1c20031070604107482c0081d081c0e0b05000360782c0f20000d240b050030b15900315403040c5039001800e0749403070306000920f0608480526809a50709100010500b00000b60850118408940100d13007503048103600a0301c4420f40d07001617181c0c45c5c0c140800c241d6141e8503a0715406918154bc60f12181d6a03031030201d9040e2007440315044d415a11804240300800c06036802610718505c68a00b958010b40410b80041c60051109140038003504000180010004c04000003071110380313808440b074115813606000807038604000b0226462100f0080664042503c20b11607113107000100454015000c03002400240b0302e4000030301c030070700a11030351800420031000041900c2c425500104040d2034420000d005001941000e40390460401c42100701d011000720034001c0b40c01800145d40115240e01802000411607401101032030195003040440160b010703450401c031100c9006a003040c11074084041c0120303101d00c0d450303c00130300030580c03c02c00469640818 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 102922697 1250 102921447 102921479
    0xc010b130e37150e0703030c0f0201090306050c04050f0a27020d0612050c090105060a140d090b16080712020f190201020a1d090402100c0506070c0204180507061107030606 75
    0x160f50b00304031034030f42d51100c04d5882d22180409004903046012081c0054040d00e40c00d1001e51041c585076500c199203941d40f50982e4025504070fa0783c400301050034001401c0c0a00b0000c03a400303080758036002d00d61030001c2542e800c1015604010003505c2d03400c510a180403150f0115950410360b445c1c104811542d6510b08100303443d5a1500310303000c0c05044002c144500d06a86000d0585400408141c82c11302d0841040d2803541641c9902c0f83c021600340803a682c0d0a0991164480c2503004000715401450303c0b100c0c0d00c440344207150381c0b00180480700c0203000300d01354080d90045400082400040e9200c035566000c1c28203028501186072094a00301000d10840d40c1900a000e0042daa0b4035012400702074208420702c08e00114820302e411114210020340946448101c1c62111426070821541e40c8806865441c14a1412641035001c1082d91aa100440c105403003410a191240038401604454954a00381c85a0491081d80100050688000107140c0140290402140d1000040102668545440d041c0501e1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 102923947 1250 102922697 102922733
    0x71103072010020115060305100503060901091a09070603020310050d030e01080a0212060f010c0b01090203010e010e090303060909010e0a051605190306090510020c010b130e37 77
    0x9000104520b03e00500503000d001d2843c07a00b5440c100d007804005c9008200090580907001c610150018544d1400d104690096030a0310011844288600f400508080010000301c6010611030811582036400b04844082c3d80d85c0d4a000769894491078624200c4140f6070f00056170001ca800210f80426030854015400244203803180101135413100ba91200324051080600301070300d5aa0b00140b9640b61442c1d400044140c14100384003145499111250301c244240c01c08441b1550000060000300092803000d80100340c001c0f8010081d25041c02c0141d05c0340030282000740116000004208140c82c01e40110074103980407400c84941c10464103189940d00c1c090401d140c03914003143c20106140c1084c0561039032009458200e501d4040c07556030b0b101c0c02010a8032065070b20780281e400301446139200e400181481000980049210740140d01041907140c235060b0180001440d00d00714050182011544406420f84564989510500e02140901062a0381064244112440c65040c01c0041c103e85058803440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 102925197 1250 102923947 102923959
    0x200102060906281b0908011b120203060a0302060307020a06061a1909120303020405090a0c140a030f110a090f0e150102100906020c21030711030720 65
    0x1600100703940c6540003038038242e00400c0f01c840c800d1074406540b401124100040c040000b11031800108140e805440148950300003100401c0802106d00c0074050180c2c1e140d0361121002906003081c0b800340210440040b03401d4065000b000007070b0790b40e40c1c21154100468002d090203170740b85040d1400a446a100b0002180c080b440c2c1000401d11002a0340d005034140991000070b49801a40c2c0403510600303400c2c403d103200b00030f1804030115103290003c0080100360300c00d440258071030b4101020012080e40c01850150340f030b450840c6407140c595000890310203544458201d540e0710070101c0c4041b4081c0500000311040c5a040983c4603000320440001804092140c0c2c1c0d81902c895181d8034a807500c0b82070f5105072010290305c4800b00342c103000310140608103060140112016406061558400c0e40c40c0901c046c2e401075404a10b1003404c040911203404104246641100790f50000c0d030303032043c080c000544800c0c2007011448812104150800c00c07107071076540080241c07030451001d00b405243c10003462200d40c002d607 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 102926447 1250 102925197 102925201
    0xd21080a11030105060a27061e0203092206031b031407151d1c030e0a0b070609020f0603090303040303060509060102030d0b03121b010c0f080412090320010206 70
    0x10072600107803410788a0041c15180b03000844c003812190f82414080218560049107003a00c003851000007584004e03c61511903194100c0c00c44040c0900c00f5600c19800c0030754004000140041da901048044140c00c0c00c011102408498820400200882d8100500c200703d1201294490103140420108503482002d1000c450301907100c00540307400d11031040d541f07400360032400603030618000d0303590200d000180041e1300070058040c0001075002030400030100c0d014000f00b10100c01c1c0340e0701050001240b10181c40c00300c19140341c886040c0040c800c500c03014009075038035541d2034110b5696020b9092842802010380c1e840e400c1c00d90b80700b030f1240d10554003140171a00d001c1e000260303814401903991140304142c005e10f080220714113419018140d4106840e40c50701a0020412401c5c09100141105082d0b0070f0460046003207540049003100c03540070404c814000c280c404e00601c141e02c0200030758002e0b4014013420185011007400e0340e5000c1d980c0c00091200081d611210081c19440e4168858294243e08441c0c81ea = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 102927697 1250 102926447 102926471
    0x110708010911030111030705030402060d020403080a02060601110304030201110f06011512050705040b0705151807080a0203060711030c010c0c020102061305100b030a0206040f080d0f0e0d21080a 85
    0x300c5c018a00032584c40404d000060300700e4040d03405150300a001038296072900e4600544142264819041102c0c41d01d004030300c0c401c80540c1001a907a0150702030800400c0103091102465890041d840024104504c4209260001d0000c1c0580c00c606030558048400c656192500c400403000d1010004000403552500e450b5050258041c3d54041c5000b80c44440c46e040c1010040666580036033fa095600384203003202801d0302d200c0480e13450300c05c40c1011028003040c5105004541402407a5000c0801e41d80f0450038030001da5070101c0ca0347d80002d501c0c1050440242503402c51411405000d05051955207854000f40700e1940056190328064803d03800d03206a652034811103a008510300c1ca010341b83d54459220125000b4481d40400c1d450300b40102107a00400656001851542c80764110b01d441c2c28020404003c4407400300450044c400117410302010391808c40c400241344880b80b0524a204240010072136051114029480e603102e4046203100404009448000c7c10a00c0c00340c508240b0586044980c03c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 102928947 1250 102927697 102927701
    0x40312030b0913050312041b09020309030d0207021207080d1e09180603022713030203031f0902070c050a0503070501090b0f091c061506080708071107080109110301 72
    0x60031400509822040c0c499150000444100c0e40c000c413610320003044980c0c414499203141d00c6c442c912446051013030314040740c0d8800f02184180e00c1800c0c0d0307900520038842003090200075546290103001e00181c07980410300019448100b1074030304500901a170030010034401740c0400d0500c5444517507103451201c82d02485041d002200041035200c00140c80e4031007400300d441e000b11440412050550082491500d90b0001082c8503c44c40820001d020320036004a504000462016408007011040711038a200c55200a91039110042088440d0740124800000912070801e82e403014060480c021925140645402d5142ea012405014400c241440c0001900d181c0040d0010507250180d40d60003d0390300c3c0c11803104607a000405200c4403500d0a002015454543c810416032001c0600c010707021103481401c21100b1155000c6500e41c8501003100c003445000d40103124980c02205501d800c01495031112811100c1115001a070020b0307000d120000074191005410025a1500401528169440000415007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 102930197 1250 102928947 102928961
    0x708090c0d1a0405120f1306050301060c0809031f0504170a0512060a0803220e100510021203010f05120303040b061009030f06050f0906010f050d03050c06010b04031203 74
    0x20201048042018075100d041c0710b15508640701c4c0044890030001c116440d4901d800009110308600e0000c02d4800c1e00550005001004060740d06141e459075041003030040c4a071502c00009822800000ba4120303070780d00c08100c105900149441c18800341c01a61a071203015100640e07040d25140407d0255400f103400d00c0044038005802c9031200c9140003076004202c00e20120080005600800039100012658002d0005101800c00070003030201040d03006802100d590000e400050800e42d024003001000310424904000b0307208111010a90014079140072840c3c10514220b49a143c4400300000a04030500121036050700e80032a0507100001214224981d00c2c041160042c001303401110101d0704504000c42015040b1400303151508131f268a0380c503010304590007901e04450683d5035008000c3c0700b0300ca00524940228102e409008154541841100030325541d006880c4900140c1ca58042018050002c5815943ea003000b581c103190707968481e074011504140f005513111142650300b03001162103441190 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 102931447 1250 102930197 102930203
    0x2041202040b0306190b010e090406060314010b2202090d05070612020316030902132c0c2b060501030606080c010203041212030905010f05010807060e0f041a06030708090c0d 76
    0x4681030000c0c5c002000d4400d01d480641440402040c2c048070342c80e0308035501c3c400c500565002c1580f500d0352a01c0f1030311fa10740382000e041a9250400010265031400020241d05518448480e201165a8140c2c0d009101e101c82866200194181000400802140c000c0840d00141c42ea8030343c0012001c896402d92008960b41000c0395111082c140c100c1d40650701a45070360313001800071641c03a82007044030422601492400e41c40c454040d260716000c8a00ea00100c14500c0c4c1c0100581140f12010001c560320810310f120080000c112110000e006090b4001d44010b1550004400e11040d6501e0400a004040d68098007140f03010302022051694000001c4408540c406c4c0c00b4151038080549880542c4d49000d4022410507403142c1c44500400d50034000c141c200d1040c034000151551400001c0c62602c0043c0d803004060200d04191541140c2d980300c07100e942d40c1810344000c02c5a41001c0b152850b0150780c0c0601d036510660200910601c558050301072445100100c04840220128100f0002aa035001c0401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 102932697 1250 102931447 102931471
    0x2e03020d020d260414101d0103180305030901110408070b03040807140f060124050310030203070e0f0a020f0a2001110a120c020712050705030102041202040b0306 71
    0x41401400c1034688180070b2401060f0000c50240c07204520140142080e89000010501290500c15040300309481440c01070100c40e03241c140b040c4814060200b601d5110814203d02c0380d400741d0020744e402a042a90345000180422541020503e8007401d180c1040d141c1c52030943c13800000c0d145c1c45410341c084a09449628004203402440d150003403009500080046403190814410700001a540d06e01c4a04030251804c0940161005498079030f1030300f581640001d0381c01201c0c8034840052844030b05102207040e1a86482c1c0c0d581d541c0c11061080d0b240f0241c1c0002d40501c21b1800000c0c64444004003540101c41070f4003030b00117603158910090160700406200b420001c008100081019000d610b4201907840540640324401311040c10490071101d01804070301410b000024038082c1c080d84000c209010b55100d0307404000c6c0100c6010000d5403030446005900001403584811001d00c041004030710001c150040c000d55807a43c0b0341d200491a4040d04404901a0b403d000040c00280360119003a03100354502c40725 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 102933947 1250 102932697 102932719
    0x60c0c16031e03090b070606050f010e01050a0f0c0b0408030108100603020306010608041505070509010201181a040807240e01021903111303080c0f0a080a180801052e0302 75
    0x6402c0812142c0402c40078400074400001c0d0010340d50340a441500e00401000030b0340340c900014420040700c1745508504100e41d0282a01c041c1e80c01c00c0948440700f005141002921450705001d4415040700e22004d0034107280b0300708120030080060020341c1a0f0f0711130301c29200d881143e241c03a5015a0405e0100035810b8000030018018123100d280c03a80c2d8428041d8003030104410498800c503040f078200f60b0b01700300010390018918140e5602409490701c01c400b007005441240c051070310340107240c42ca22212901c070210882c01003414803907440207482c1803a0300b00f80500d100011540c113560002d081c1d400440505420a140064602c5061007541c3d280d2502c070100c014102d0520104900800031040414141401809504c00250085e410340c0059481560700340d175a4460010380310b00d070002025a0302c2c036540c0701014000004401d90300f81d420405050a0003001c04214100510001c51581c108445640c60a020800398481d91040310608111440f42140f1b001d849800c00e090790409400080d41003118805 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 102935197 1250 102933947 102933983
    0x30a03050a1d010506090c0721030e03040609030c1203050910021014040204050109020301080a0305090105120411090a020a05040b09040204090204030b09010e010209010806091305060c0c1603 84
    0xd194441d01245001401c1c2032606001c0b41c0030300c0b2800d07078000c0301c1c3e6403401040140d00701008002e8000203030b060803e0414a03180c0d25145015041c181600e4080d224055000425009410140c0420b62000a0345d489135100c55000302160102c0c03000f03039144d10a6001c001402e40402400a2520f501551502e29121031718080c401e04184615036101148940d00c541c072100c1c0350600c1030541680c0c0b0350454181c581454010802a60b4040c3c02c00940b0358070400040114820000e441c540580c0d05003442034075010b4250050364940a16160b0721210707035803502001b08010324030908640091003242c03030804940b5151008403c0b8055551500301003a010042070103102c141c80050141114002e00140c81d054844a90005a80055008031550001c0005100302004280251110307505d6980003141806c034402c0c002015141e001c1d00a80c0209400e0000c10410844c0791074a503403054110701264402d040207603e402e841d1f48680860b00c5175008500703050046107020491401101e402022081801021034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 102936447 1250 102935197 102935201
    0x604050606121005040218150a09150504241e022d010c050702010f030b0d0201110307050a0305090f030105090a081b1902040501050609010804110607080d02130b0a02030a03 76
    0x1909003c00c0c0d102441000400795103a0006050020508a490104240031400d0185449112010100c011400e2111845a60344800841c003140e104402000050413007010541c0c4600c80d40e0001214550340310a200018130b4a00c4044c2c4c960111603030340c8402d4540c40b00850441c401904000300046c1c05c4040003615048050304075940b44045d00c603030101510b140c41242400c440c0d00f28100800301c1d030701288007401d5680003045944107081c5824203020094081d000a4142e01262a00078184515460f4103101343c0b00401c203851382c41da403200840e54080c0a40c02c01074166044cc2910f1441003400c902c0701c01003424103000b01402014881c0c020070904040e540c5d810340326042140c3c612502e004c040d0300d10030780c2d01c000c0011b080f041458025010007039086005000940e90143c2050b40521010040e8540b41d0740d03c01d0240b0b40c080d8200401441c20600400040c10f5481540e0004d070007a100400d101d26504003650003000c040c00030a820700d000603610b400c0303801d41d40a00654580560014411002d24a00075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 102937697 1250 102936447 102936451
    0x6030e07141c05060108061602122809030b0c0702010207050d0f0507031b060f08150f030307140705010e01080f060a0b070b0703060503030414040f180f0b060405060612 74
    0x303000540410380040704031084884000c040d1080e5000030010046e618080c0425900050034010701000000c081c3d00c06544c84000d1f0313107454803807403002072030000308500d06603c08020200c000d440b03841c0d59660600148282c2c240d01041d2210050b800108500980200c2141d1201b541070300030b06800c61600f420412000d0004106070341e800d5204c7e0300080010800d010310405984130b4036801c105011076411400b41d184048d04414140103641643d6000380c1d4100004580c8400d400c03648209820f64000400c1c14800701e000d64540600c40403030404208180b501010348101d100030200e0346820f41d188011210f10043c1b407107003804901a0030201d2002d041c03407452a40c0c0048050b00029646941d460f80b40466840010140c9405d00302c2c0d01403204980d45402484c0042504500442c1441e0038038540c140044584c0110034401c9584040c0c2d07504000c0d094006900c02c48684042c0e0090f40e4482c2842c0d82c4003452010200d8404103a1400503030310380b60511810b4013404c4060189030804810f1803035080039402c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 102938947 1250 102937697 102937699
    0x102010e1005040f020a0e1e0615030405251a031003030c050f030304060509010b040603080d1512050c030609150411120607020106150203030405060a151203030207030906030e0714 79
    0x1980e071043c000758a46c5903101c1d0080400740340200062a00074040040031a01c1e90a1035000036042d01031280c1990745400c4104074010303000c0303460f90b80c2d2500c0c82c291b45030108102001040c1d503902c825240289400012880444445d030300342071101d0400c052509060321040300c482d2501c031480c402c1440400c3c031a0b01e030400468072980864024017101c40d2464510b03007089904481d05901d603020092030320004c0c01503140809003602d05100482c1599551072850048902e07900c840d6035550074013425646043c2080005008410b4002c500b0589030414030344404003035051500900c100c4001c109a24400600314a0f81401c80c101450310391161390f107230400825158116179100d442402400203410060040700d0049500d41c000040c52450b20b13500207400c46c05400c018003590401e00c204804141e0104445500c030910301000500801c4a07840d039007001e02c46400042c25401d416425000301034040c1d00400c507250180c0c403078642aa90300c1e901101a0b481c0041c6181e000e802c0141308007e101c607664985044400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 102940197 1250 102938947 102938963
    0x20310090917030906010302011103090f0105030606270406060512010501050a050702090703090c0803040e060409170a0201021c0e0a11030c06070602091e030a0b0c040509090d08060102010e100504 86
    0x162951500b42d08262545601a046640104119a004041c149045241101460415500300c001800c0c0c4803003000301d14140b040010000d4440d0b0368200c111608800b0300008415420300ca040110020f684030902c81e4007452400c94003141550051007940c0e50403d03060701d000d00301d80c02c203001111a0b80040540d601070000901503503005030b1318041c0d120b1040e041580c00007019042414140e51080581c1c0c005119070b0000c10080c071140f0048900c155020340300b6100450098002d01e050304070521056401c440e004004940a0030003603040d0004d1641301e20400a65030340301c0200049504448580c00b2440c020381c0401c0320000001c22419500d144030704004c0a580000c40d03000003040e01540560005c558041d4002582c0c8014540345007464180010305503080300c00e403c20008240d40b0080c202c005010b0a001400082505c4840811140500740c0541650454142044111383e42c01d48550310002003500200000d070359510510402e0081d2300303028000d1005c0c072036800d00c00c00204401381c800d5840007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 102941447 1250 102940197 102940223
    0x10311030102130618060306080705060309070f0e0f01080615010804051c030b0301060b03100b03130203011e0e0a17091512100b0717031305150115030203100909 71
    0x702c0781140f40301c002d00e010b4880c0d60010070880c045d07031020320340ba030000800d25103400000c0c891600e000500506440c01614050b689403580c46880d490041603920020141030058000b1680b046c4508825000d8042a80c292420340d0f01c40703003d5521060115405000c240c00075071038944c298400e01c1b046400600038020fa602c0e810000301c5619042150700e4220340840d444102e8072059003006d04c41d0714000d180fa0b044044c29410300c0703404692101d441d0701c00d401c0086400300204030303c0d9070650309a00746240e00030020440b0b56005060800d480740c41140480d1034900c0c1070a016402c007004200b5542d040d41c401d083c40550510b141c05c0c001035400094445070400301000e00000e042403054001c00c80b40d6400044101d035031400c1c9442c0042c4840c5508100f903a444140319000010b07686070321b801119004d92841383c0c1c0340c1c1d8400000011b42172a0540c00307840c40c8142841d0b694640c80c10341d4401e040c2d81c801b401c03c05103c00e44a4003070f0182d10050351030200b40c10705a801000a401c05a0044015074881d40b5009125 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 102942697 1250 102941447 102941467
    0x2150c071a0108060f060d0b0114011202030906070e0102070924050105031611010608030c060405010e0d0c020105070204020d02070f0b010515030f1008070b09040c031a040b12010903020312060d0209010311030102 93
    0x80c02090308200a41d416655102b589507800c0064030414040d01c80b4290b1561811910040c2c48080281102060046581c0c100406c0d07070090000001500b81d14034204002c002e0410a600960003024614440100701040450254401c00441e88a01400c0d80440c140d0300719500c0403501c0c41000101940e41c1c0d580d800d004615000c043c8014000000c001d00101402e09142c149642102d01400120300c07244d0200806403501900320034148140758090800341e850b0121070000c64064452100c07420521440000d14004001046001d00e090700c1c0141e010300e000741e8036402030141717840c0c483d1a108440041480041c0312010b10450f410391241c060140b403904281e82d520b09034600000e03500094560100412034104a091510440b0307804c14240c41c0500504500d40842c1100300f014030407035070003070381c84140040f07079919a03c0b003904421444a00801c0380740c1c85414020341380c0e00f10850410350310782030001080c081c1c9070480d100185250001d00d622032a9195503200745200201c96007a03074141d50284403070303001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 102943947 1250 102942697 102942713
    0x9190606020c0310091713090203040807050c151b0a02120a0b070503060901031101181503180c05010c051203070c050c01030e030a0f02150c071a0108060f060d 70
    0x340059001011210342c024101404c180240420184040ca891481d402007800080e41d4402d0015054003147c1e81c210884012940c4d8486801c100002800003090104000f074280050100c18001c4d0b0644103d1000c45e0b00b0030850078545514200342400a01c04081e52010400301680140003440844140c5001c1e1350224131451003d400200c1c0b01d4101b4101031090107509120150b0100362454050300c1d40c03800c0e0001481c10030060001510714940711180310b15590040004403120038450098500780c5079039070071202070700e1601080680001c0c1031000e450024071010351341d400020341c02500ca8011a0410300116841900640207075920302c5850301a000d01b40ba88801940070762a160b40d1681d22102c6030800741d1420004031005810580b4000149000c0400401941c11640075071a01c04204102481e040b860301001d03014140800014409020700b100ba80002043c1e00c078420302a20b195402d501110340d4030380000340300b000900d401c1100040e60001a0024866100348010032800c004803c61304d41c481 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 102945197 1250 102943947 102943949
    0x71b0323010614040b030f1b130204060206040305091909051006020a08070821010909020a080607020d0f12020d0506040c110d0c02040e0d0801052d0904060e031206041b0509091906 79
    0x206140140c2400c0c1c400d42448406042c2040c0030700c0727040d454a403429000030743d86d07003009001800b08080401c202903595100414039800501c605024901c0607207680040008150503280408042d076a81e40000f4042c1c00410020346507508600428103081c160b4484141c01d5106003689540440c0a208a61070404e061542a000e44210b40001582600510501c01c21840a800483c070f00d60002080008040d800a90300c81140c129150014402c01e41e8541540d160001036445a01c45001144581e91000c032030b48882e1003007108590503ca1940901d01c140c0c3e14000808800e0315640010074035051903070044400180c601e201400008081c844110340a007407004e5100c140c40003070b400d040104090b240440541c072005000851046c03c0c044100811010f032500e0280807405211000001000d10101e90300074442000801300b030783c1ea1880040071140701c090307044405038440c82c90642c0c00c4c45824011140005c8021480e140e43d072410b04c800d0b0400200044c024206d40c55072914048842200c1610f0040314 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 102946447 1250 102945197 102945223
    0xc18030d0201020415050906190207080a0605150607020303220b22060801050a060e03010b450705070609020418030e0405040b010308071b0323010614040b030f 70
    0x161500d0620000c072026085c03045032142008003d1041d44001d035030342812901004280e224441003200200030623406c20216600c0880c5a02074015a8410311819800c50351240007440d440e80d1010810038104152070290b0040030750540d00900500750031880074403549000c030101141400b4000d0303072400244004e622440300d40c0d0050030a00700000034044069054009401c003814488183e605240115041c210144180300401010070048103240e01c00390711030103d24902030720882000074044140d101c1000c3d0a407030440350b402c480c801c0034100c0310404059100d03054003d40c1103040d41c035050340841d616040751900382c031100c0e82c0c0d00411006a440740b00f000c40c5406940003500846a10b030a019180d1b1443d48660b07030099003800704000002d4070724010740c0d0540758030018075501c84226017002038110602c5c0008441d045500c41c0f001c000d110b180400003032010300c214803151407198003551260a03103004c1c4c4100c0d0000b18030729594070800d1030141c0142401100140032030f00c002000c01f0000785440801c00b000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 102947697 1250 102946447 102946451
    0xc0a0215240915040f090209010305070f17151533040b07031b05100b0f04150b0c030d050109090302010e060708040605152808150c18030d0201 63
    0x803241611000350180ca40012145000a49003d140d00090381c80c40c090420312a564543c02c403211020580d10000c902500601254501d41c0c40c1d02d013403031366120396000c0c0a00740d40c0d80d03920008607072045038852440d413400d0801070a452000750b19808000e840240818a80400351100a84c41da101c403598422005200340c224280b60a024402c4103550500c0595085030100800050010803880c8003210861507061900d03880c00400700703502c82800c0f503c075800109940546214468540c100b0380062455100c110b40490300051094100b000702c88a0661003c00044d09460821041450901501c1c101e03100d4010b41c1d1506d004c0340300200454109800070720080365181c24910505034244203458901800000508450800c6007001d0700340503000b080203050782d448000150200004e21500c41892202400007a41c800d1081c80c0000302c0340041c011260030800281001900400001e911008481d141800341d40c261289400c16000f940006c8404140d0522718640d002c0e0341d1010070048401c04203d80c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 102948947 1250 102947697 102947731
    0x1050408100c18060206041103031e070203010f020306030613111009150c20040603060f29100302091c0804080d0905010e041802030d030b12070605030c0a0215 70
    0xa84070000c1001d03040583d0f890b4820a110654000031a56000754014034984010800d1900113451842408000307402151305601b92a80100480c010300345070f034403c1b002440010303100c00450f4100e000403650954540d00103400715032058000c3ca026a550390080022001440751400841c00741036003107940600140350b6480070003000020682051540620f031a2242007012140c9480210350050b0007400c3c00700c1c122601146440d03441d640704078010743e880941446910782c0920003400030a0f01800c040c034220191020b80d50440c101c51844d500000004129409060b60401c3c00c400a41150319007030341008114202d07640b1061018000e80007188140800b80e6118100201c0310b0a00910150203c144220f404061140d83c0e007148241d141440203540010312403801941d6200c4030118210301a4260241140f016460343e41a0450240004190741da5101d1a001c0303041d49550b141144154030015501f8008125405404d100501c0c404110b48101c90360021480f00900c00000103407494540c200706165 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 102950197 1250 102948947 102948971
    0x709050604020c0607200d1d0f09071d0307030b061008070804020d21050301090b0105040f060507022403060109050d0201080103060507120905070602060f0714090105040810 76
    0x68254412025035055080400701c1c2509566081c0141210040c03010f2880781e641c00c500000040c2c4041c001010482da41d2409024001e8441c020000d24200f0108024448106a083ca00ca405188603c00380400c80607940d02c0001311001c044050070f0040c80841205a44600d680030444200514000c5104101d03504040c0700700603c1200140c0780d6800c0c01a44d00c200495160080b01282e070040d01900c0342c00b4102d81c10710b006400c2d008454101d014041d007080583d1400742e4800c0140d4160f45048070100f0084141d80d00644060080b441003c21107058100240030080c07140c00a04061480608039104000e154403d00c20303d000c448d82c0c200001000482004002d6902003c0600100020381d4146080c51503500000c01d9003005000240405440d0808211024401c1c10282c1c142240844100071404c180c1c42e0054480c1c00c244500c10052007400c000c02c00c21089601158090241d0b2b071115441d144a5907126401070b00014150b0f4103202c0144400601d03d01c05000a000d0040140ea0010360075054032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 102951447 1250 102950197 102950201
    0x20306060d1b0f14121506071b0906030c0b0703050702090a0b0a12080313151d0106090c0c030c1b0b1b030301060c080d0b120708060702011e0c020a02120709 69
    0x8244641044132080c04030b200ba00c10001140d0041017080e02800f616036a800895054205400c05140c00a1001035580144800c83d1014000070400c40040200380c0e5076181c01e1003e0f100c030380c00081c111100ca0304041020464080052000c14030904000c0c3c01c10040b60000382d2401c0080b0ba4040701c4645030345c0740040c58507150501c1c0002c0d050104c5000c050307583c2511000498000142003181c3d5007030b0b0325610802e108081011030380c18060b034001844000c400042e000c4038004904541d5825600744000445d602d040c5d40140300020449035a0f45d41c45405540381180c010480c100c013645d01400120040c070000b110101c40b0005050000f4007590b03200344c02c44082e008288400d0005010340c00500041c8125a405039691482a4004c05d80c1500e0714040c80d0350391b00500003840b0095004d4070307110b002e0b1b9100f02c4c08500078048401d40c5040e034999a466800070b07030036030303420140c8090240040000054a400aa23001e086243c2c40b41c41151820902036000c2151043c00c07948648503584100d0701003116003018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 102952697 1250 102951447 102951467
    0x90303071101020a0504060e0406080d0201060e09010216020616063201140d060209120c0909151603021308010b030d02070302060712050c0d08011d1306020306060d1b 73
    0x41c800071850b06442c0d1600801030302a0b80104c80c1000707100700302c00d809543c1e00e4000130081c0900406403030181200150180c020603442c814690340a80150000708d5007041803090b12216a181060443c5c0810503508125980e40440718a015600354141c000e00880c01912032451070400c41200c129180604061445440f18035040080b103001401e4014008510003924a100000007030307405500207a4546083d9010b8019003c6040d040305440d1030840b000302000030811101074040c1c0311045640c4403103800580b40c450840100240d4005000811030018511660b8602c0104500c0d005040c41c40c0c00010b21001c1490ba40881103d82d150740d000c4406103024042190540c07070500040003421700d96408140783d4002d250001d84142c01868a11104500903c00c9582d420b502e070301a01d00e00d408820014011035803c0c0510008000110402d504440080c401207025140b00802510007083e25500c4c48080c2d40000c080e1070304803506012a400c500d510740100c07509031210403000394242540c00b10060007a029 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 102953947 1250 102952697 102952727
    0x100e010510121110030f0905070302190b030105060306010c02090712060b0408061b0c16180207030c0b040611071a06060301030201090b07030e0d061d0d02070620030309030307 77
    0x1d070102d00001424042c031094261825110b00c451189166801c3d03008011350102c002c10241845006420020041580e5090324421100d42100844a50002d40c07a481c29000720340001ea400c00044c801d81c50160055a40a001458407081e51000c560105100c603805850303090100d60603030301d141e000300028001c41d4040c00c9005076003410a86804000740d40c8690142480c96030010920055032200f6036041126242c04040c000c44511180744084015450000e1007040000c0602d2152521540c07843c2c000c0342c01c0990955142e100480403911054206030001e081103ca86503541e294844a8109802500b48680210400c01000d00128011071203650002c040f240f2030b440130401800103030703080185241620304403003c6907107030316852500b03445505100d8402c030750001c011085141041007d4200803031118058100790b8440702c80c2d03001075943d2441e1170b11404c050b0b00f0032002440018807894800704840680f91540d54400341040c0704504590040d0359840e40c0ba000002000211030b0490303078101002003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 102955197 1250 102953947 102953969
    0x4210503041502180616050d020708070b0708030414150108010207030305010e07170408120c07020f0a06200106120506060a0e0c1b0c03011406040c030b0609010f02100e010510 77
    0x1d00fa42c5074628001814291034400c5002044c032402040c0246846486c0c030340c0c0079007200e1813102d10f2480a55948454890b509081c40789503030202c1d50158080c248c400b0310341d000254a00b1034450343d403807415940d603882905207a48903c1040c0b90044441b465084e000345440701c00141ea4100341d003001826150146c00c0803844a201d10300307102c8070650005100034002c5400c0705013a056151403401560b280701d800d10482d840301c00c800500c1f40035000c01005201d114800c840d40b0120400d0300062210032541e074803600c008038002d0115101401302c044419401a041c590000684580300c1d0010078a031a281c1c842038031103901041c00c0002d0703818030340e032104054040c101d8401541e25014130010002c0c4280884c030090004207010214445a0030446800f40c240000c0c0248181d0345a001324a0540300100d80b203512070f504009400c0001030007442440141d880140015150aa103c001902c140384002594011032241841682c0c061070b071442030444200a01c03001054a09089900e048000e00a40121030410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 102956447 1250 102955197 102955207
    0x90301090305030106030e0f0d03020304021815090f15130f020d0212010611251502010504050d050906090f03210432091008010c1809060806070804210503041502 71
    0x100c00140000b2809c48601d009a907a507500e1021483e010700c989060740c65104000b05000c402030354100a84510f030410750700801280c2ea0400c00d04203050741a00c038060911040d807503e201508004050340c50300c0801150110342030021101d00c00481e400300440c1c80040d940400c502c0c0c2d8485c4039001c6140185902c2c501000041c2200c642107450710140c01e420303034144e0380d601101c042c102d02843d00d0380d0042c444c0c1000d20102c0207030b05501a0103001c3c100c4007207a82e030242504a1103118043c90a0f1100e54070042c155a060208190600410300008040c8903454807a80c02003400340e41f90304050848080c4078008198403645080900200c280304015003403445910b11102164405d0501070082e96401d0849222440e5101d42040404081e41608407034155424418140e82c0e168010000c1030001e0310f0044501c00c12542c501640e802c076401409540b40907040394011456544c816209580c1107030245408180d03c01160710440c05d403d503840d0307006022800200402062000d005080e50741844c030190254501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 102957697 1250 102956447 102956473
    0x90a0603060819020a09021b0c01090b0a12020c030307021f0b090619081b0306090304120803100f090506031b06030c0c0f0106030c030b18070501030b010302090301090305030106030e 80
    0x50b0019a0b00607040501c0c0071080e030f06540d9100d90000041040407004c55880001d0201072a1015014080e50031074030480b543d42440e9482003600c0300444102c89a66410480b0320744084a181e01034040c0c0c1c9503041d07001c0c4141c001d0b040c001d0004500510007030300100072000746061142803101e8091384603d6140c0c42d0105040e03403519412255548600304840200d105410800010681840741d08402c0d0305200d80c01c0b00e80256480760100c4020281c0c01c4046070f81ca41d03148a4202c0c1d5070b22550082d5204904121040000100c0b514055504800c09121101256841e50314012002c000b503400402060340714014854a800e040c0b2444201404264030350501c1f41600020540c28880948981c0c5500303030005030501c1c160710900c00e00c0081ca24420080c800c1903903d050001d403407196130105031284c1d005600410003195078101d92082d615522805050814540001500188000e61010303050603001c0166a0740e507507081c403410b120340d44207803622030702c075410f024005040f5424000c5100301a40301d280b1445d50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 102958947 1250 102957697 102957703
    0x9050303031501120501062604021309210201050a060608160503090a02150711010c0f0b0606040503010c0809010b01030204030803010e071404060504030b1311011808030c03090a06030608 82
    0x84441c2c007011402c5800c00d08401210b1030032440031a4821145450300100310180e004189850040700400700d99900902402140c2c1c0000007500d00a50024810a4440552465803c2040e80c64080c04500c3c0fa0040c0003500b401d0140a2044854010303595541048014510b81c401c000140066140010051910700b0301600c806d00c4020625007840b0b0003100260344800c040290450a42d8040c04031124124025401100340d0804101212401c4541d2550601d80d445000e916003140d402503055031841c0c40319100d4424901000e006079070410b104100c0031031345072402d0203001200d840c82c0e502c030089454140136150840c1d600700645810540100002c00c04203c06806517415901c090340c802c182c984445005454038140802100c6102c44046000a081b40c0c00c000a0f10499010b01ca0020321960b424011466204000c807000308462141211440f0310351081a29541450300391038a0b0305c40c2d0307440721640c1703203907400c0150700f0203150f400010284458100300c030600004048506041c00f0b524201280292 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 102960197 1250 102958947 102958951
    0x40302010c0e01020c01141303060e01060506130b0c011409060a05010f0501050f09030703050703030207080c0103090c0e06030a0b0a2a05031b0d020a05040501110a080316180807150905030303 84
    0x41000b100c20f02047c0c0c0c18a42004540c0c00c00345482c1c1c0e241405030b0b03a14020f0054906041c5800e8654a801c00004840c02c18400312003030404800c0c0201811402c04203288155041300c0989405590394100100003400f01c3c90820f40244541002001790740b400d07050b00d0003a604140c001401e030080c440400c000300d980000645204041d01c209a0362600d1030080420718040c01c82d88042e2251023981400400d05030003250340420380344604160751103103010030015000c1d80d1030107500510901203210100074200c0011800360300184003c042d80d81c0b0307076150b846040000e0400c0d5503e10711603942e485040d030542c0c000740c2c200c104070860580f00b5019074940440036069000080034050360003038004007036140c19031260455520861700103045440b403400c0000144150818002c3d05e01140340c1030600041800005000156558407a031150314680e683d140140e641c0c01140c42d00400c0c80010808002d000145e141d0b45405004180300500303229141c402c1300400101810240e400340420075400b40500c1c1ca001c81266 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 102961447 1250 102960197 102960199
    0x105071106280b010201140c1209030901020c060903010f0f05100602011802040510031208070f020c03071505070203120a1404061d150c0106090c0e060d0504170403030305040302010c0e01020c 84
    0x60344200343c2d0051b0b0141461404103807040e0f10742e40401c82d07190940d00c0640504034030400c1c2200c2699480220303541e00d1207424401400345c2c0c003066118611349003000007001c4d44076000c1e001080060040040006495481c412141d106485108000c410b0a0504050740207184c90f100034403001114900a40ca140804e900107800345132550002001d980340e21408000565210180c00409064140c00a00414069030f0f80390005183c800346c841d40314400500b061140c0701c01009460f2941c50003c2c5040c209594114260520006002060140c1d80a001c00d40300c03041540a0b143d50f810b1400402002c0058076180201d00e0403007880b050200d1680718401c0400004d44810100d51441c02c9000150428541c440b81030f1a007500042e107408088040d00400103c0e40780810601c01c188a598003600c0000c0c19080702c030382105040c062450b03489000d07003000d50040c0c088c111800d502c1078050b600c64901c0d800354106501003515402400200344c0c0c244907448410205152085100d20b51600007500c880340d01242e2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 102962697 1250 102961447 102961451
    0x2010e0d05070b060604030f03050408190302150603011506170a051603020c01090b070f020d02030a020309010507061103131a0c030606090a0918050744010507110628 73
    0x22180c5e154242140c0c05183c00040c202d051248600d4004d09070340c001e008810075230107524483d250310b02c503248140000030303031580242002c841488600c2c034204500800040d81907403a040131007408035040845d07001504070ba540e0510700d40c1d2007a0074280f50140160000d5140ea00c2c10041255905242199071298815860007681e40c2e801c508541340074009142c00540542ea8410900c4600c9030001a40402e0551540956044000090b01661a401001c240c880503801c10828140d03290310810003001024800d44c4005105101c002c0c01d01c00703d4000710b84074951951500da864080c00000103201c0b0380c003041489140c0ca6440c1804e6000414000908464000d240100d020911640c54910010150010403401c124044521084c13035500e00c910101a0750038002d02c01c0102e076100300c00740040030b1a0407a00c07090300605039100f25040040882c001c070003a800701280403403a800c00f00b0300405000350216030b03c0340c01c101103620440303040c000090200000c108070b0010501c4461120a44882e400c1007034240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 102963947 1250 102962697 102962701
    0x121205030c04030606090203160807050406140d0203150306090a12030b04020d0504030306170105060a060818010f06091107030206040204111605030d0b0307081002070c210302010e0d05070b 83
    0xc815024002c0d40c200800050500e80b001c90b80d0440382d800b940c03041c81a074503083d9030120903803030507602e07500309807442c400003807041109024260244260000c0714400c42c4150346060b0000c46544120380080e01c940800280507031058201d4034041040603041840030000d41001c44003030369418202d02400e4209000d0645803440408969165130544102d90700d0080248018901454020020705880c011410704140601a400d941c80e0144545031041d030300601401c80150a041c2d00303076050b40008001144a0701040a0030451000c280540c07010300104e400042402c81c240b0404406031a041c9180e200140f0042c00700b2070200340e00189241d0815015100011910480340e0014003e1040c00c05040f032042c41e05e88404100040000201840142d4032030400080201e1020941c07940410b114840856200002411400c00c940d0300501005204000846c58140d40e0308131040003125540c140c031a1070414880360400d164082c003d0f5000e209a0b08090240c0b540741d810017402070b0042a002415038406080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 102965197 1250 102963947 102963961
    0xe0a02040314160b090d02060904020708070f0201080604020a05031f05041e050907030507031202032a12030c04061d0904140d030b060f03040c032a12120503 69
    0x812100035603002600010b50031282c01080c0c2d607035030085418490781c841c05000040ca1101800079a004a400100001503461198003003008580000c510103030701680c20415034000486450040007024071800b942c2d140c294240c00094440480105440d0050340108507074101c0d160f2000c00ca0390311140042144449096506010703074102c66641001e9001403511009180050203180420131108807500e003400142d07201c649407a01c032039091000605a6104031418000510100320f444c0000310a841161f04080d0f034000143d050040c10016008201900740c8610400d020901465071081c200c00c0c009440e604000310b001601d4407640c454001004489090b2400140c1c0d4068009116400140340c000b00c3e04050030001144200800306983c1072252130f900c00a514003e0181d503500c10002000c041c18228081b181c00c1e0381d9800184101c610030301c4404007100003450102c9142001410546c0c41920000d4954003001e031840c5900305140240e0000c0d8000e00140e010782c0102e911305800c1c40c6c01c603200d1721600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 102966447 1250 102965197 102965201
    0x2070b06010c1515090509120405090a091a06270106050705011e0203160f080f0a09021002010b100306141002150c07030e06070c050427080c0111030106090e0a 70
    0xb0a2254203d814040115220401c1400940035211510b40800c0942c4806480c1651100c00c400c40c0c490800c0c040c0070800c50b0b450141400756118040c81c9001c100c1c128242d4854010f2803030740c5055201460f841092215906017501d110f9004104139591860321207403880f40d0f000300c01c030521440c01001400a40c03c5d04110082d00301c421030301c0600c1c00703072030180c804200707420043e40049410089580c2944c1002a06520640d0b0f034024651640c1c841e050300d5140d902c403520f40c0c15002041848030586440c030703d00040c0c44050f5440e00b03412055000169100c0018100810303150008500c4041506090090212079944007244400c400300315102c1018031140c000c245d0400404008100400d5110300c00c0002c00c109000041100078401c3e5900e031010f003244010004e050103117800c040c00a11604400f4449400c20768083d00403d0801c01442d00c110102460300140d021301010100e40700320380410f100c41a035009000f2200d2002c00c00c83c03100d0840d810b08a00400020307082c0f01c0e4510110394000071038001c451903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 102967697 1250 102966447 102966473
    0xb0102010b090f0103020f010815090604020c0307030903060f0207052a0901060c02011715040917040f0e060d0b0a0b041d030711090c12040206090406150f0302070b06010c 75
    0x2408070542c81c5000380c2c007403690310350074841a8040d1941c400090301035072155080902c00c0034200f4505104411103400c1c0944d260b001010310360005e5081224038550181000134240f041d00c070356201c0402904618000007643c5e640c0c2210741113107006124520002e000810307070540310051848000300356000c000711540305a101000e040d40215442c0c0012481c150b00401c1c480c0364a0003a20b8040d181045204414018101160403005519590312551440e29081c3c01201e501030065560846040c1d48880c01c0e200350384181e000c03007801c2c84c91100822011175100a03613a8800021200d0111804158445950424004000d10507850b640c0c0400c5c070700e81e5155400302108150609400d04440d40290340c20b40c1d00d500c050015102c0407400141c000091601401c2180301c0c00000e01098149951240306802001000d401264803071030038010b401c4552268402d40004103504801c0c00080086100003034a80d840c1103040741e00301401000f40c080401d46e050002ca400070303400e1800740400d250608082a82074a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 102968947 1250 102967697 102967699
    0x32509020307080412050304020a1502120a02030c0c030f0c12030c0703060506010e0301050702100213080d050415020106050105031303030207050f102d0c1209030c06060b03190b0102010b 82
    0x30200911070440e074003026a51240d4414402d05000071800f4100303803441d0004070b030000d50002810344184180c0c1c80040080c54801c40b81d004840c0308807194821005640c0007044003d00503400030505010900040091005941003a406407080c071800041c02c1c0c2d00c0d44044080c443c01070581a822041c152820804c4601501d00802903d03501d58803803074601c014280c2511224000b40054119003c24038041c031420380140c600750028040d03010040c03100c8010790400b6940e1861500615000a08082c0c20f00c108010800c03d55034480d501c03404c10700200c050169442e1010304680c5000e8003803141d41d82140445c0d810841258505450284070301e011001f030310a9000040607805940d1500103424400984d58a4240084109002d58100e948c0103401829481c411407400390a11b0418100d40c110580c00543c40214518048951982c50880c00c0c0a41c2c041c0841100007401c0c020340d580602c11a40306910191240f1040540b85082a07111074503001c0caa02c145c411000c5d510200042030760f00075071009441c0e0300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 102970197 1250 102968947 102968951
    0x1a030916030302010501060e040513020126250f0e040b13020a0e0a05040b010c080a0c02060f07050106050901080c1504121103120a0203040e060a090207060506010e060405032509 78
    0x7449250080c00b809080c4144000f08500700f600030031501c0c20b401030611441904010350790001c4950011110054060420300c4109900d10203100c2804010401c580f25190102c600c191a03800d1480310080440c0070300807481001210344040002540c005c602e140f0300d2100302e0b800316510810800203a4003a41600c0c18121549c4002000c900d03254100d4517501317201104441d2481900d0355081440107a0b500300e82d41c0c6000a2a003900d0a000400e4600504122000c0c1d142502c01b1100d550f007c10b4142d4045403c400810602052900800109000d031001504040e50500b4440d454040704c00e550300d80b0030400b144650284604040c0302c170724510540e40100720b80090080480d6407814000d081104504a1034024014040c2c126800d5482408540c100207043d030003586000c0c0f07800c64218103078001912155008008150000d0880d01c2030001c1c001c4603000d01d000003681c0c1031180024200d8100b0407441801140180400c0100f0b80d00807880d241c281611108810800d407842d900710107484442d400c1207815074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 102971447 1250 102970197 102970199
    0x61518140619030905010b0102010b011b1a07080f060418030c2402221a130b0307080601031505031b060d090302010605010909050121060f090321061a030916 69
    0xd5161300070ba030307085005900800c03034000d040004a00382d802209255000c1040b44007d000002044000f421103140510b00c0c0c038020a00d507192003001510700340d60107000550b00200b4000c40c2c1c29405d46142e0010401ca50801400401c2d25000a4913020442c01609200c06900300c4d1050003580600007400d2141780030ba0a420001030402d80c002074000b950700145047c03007200a0602a0401d41c441c45c150394078070001610b164180d00d512041c070b44c0150510b083c10503000700006140015003000d5070285000b41c070b581c0c5091810400050481e4245581420301c0c4c403048100300a01c0d2008640034004032410311204801c820ba403004550140300c4c0c0c0c000b92000c0752418480b0800d141c0c2c10351004054030800d90351000003035900c0c00d401050712021f0280b60307564a80c410301032069000000c880c120b00b510648001c81e02002d6903401a045940301c4c14180d0104a120518a034005c02c0500100c00d41001110208501400d1400ca00c00c1c08600c2500b010800c01c001010800b03602e820031004003440e070243c8000ca409 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 102972697 1250 102971447 102971497
    0x80403021912020f03090901151205070c060c0f0806040f0b0a1e0b270406030209040c030b060102030c03090f01020f10020c06060121050406021902010615181406 71
    0x145440b0303184001406111005005003201200311030322200020514020f5908100011429414285c0e01500b402540c581482c400326040c081c03944940d142c4d031501240b0032006d04200301500c54281da50070403c810481d440064503042140e00360095403e840001c1c5210304400250028401e680c500c40d804814114009170440300150151180f001e84601003081c1e6954082c1441b00b400b92688007800c0030000d0520015100a6150b10b410641c00204003080720f5959802099945200781c400b5a800c018106d1b091082c090060519074120707000703100451610310140c140507200d008030aa03141c41100201190b024580c400c214410b483c03840102aa04034214071a41071009611101060b0740d1030040e6800618150f0289541003503c480304410300c907010940c00e04450003484010310444117594284940c08036100180000401020310f0307000040c905080021402c1070000c240310705010083c003003000000300c0100d00c0001048810080c0305107401800c5d940042c407035004245900308903018164494003c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 102973947 1250 102972697 102972713
    0x180a0b07080309010c0207030f0f0302030d052a0406170405070905070c03020d05091813060c02030405031b03150c090324060406031e03030605180615040f03030804030219 75
    0x1010450000c002451145c08107980320b10003031101800c080b42e030107a214082920a000740c1107030340c482c0c41940c0c58081c071210345030110761003a2071595501c050301203420314100c80c6842c802c9070980d05080050900d07251400040506e6a0240740700c5200e41c60902060030040201f0130701e03000d400540c10600040c5000c00d0b0040100c4084070080d0b0062007108698414640074004803582a00041d20350f4400240c07202c0350000f010b4016124081418900e81e4050108540e845130501c02c1e40d05030301440d82c50b0714003010140380c101e1070141c08410030080400218541c0d03000807540d0444019000e90a00c69880e05210601030107001030b456003600a0361440b1079408140803156018080400f200c1d001501c0d01c1c0c050000b11030441c04001d1030084170104a0308c19040304000700014910901d0045038558580c00405e071400d800d40c80c840030584804081c0002880c0c0701d511210703e90549101c0b1814540b0309440310044000b10310002c0c1c10b00c49201e01082c00c0c0741c4280512884001444815400354046141c4944 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 102975197 1250 102973947 102973951
    0x60705030708090a0e06090c160f060c1805060d0908070c0801060f06030c0c0308100302150306010f021b1e060703020705120a0309170a050601080106081002030408180a0b070803 78
    0x1101c0d031404d40c0b001c41c00480d2400802d010b8080508407012990303c0d1092504682d2100544c074020740c2c0c00401c0381000500034908043c3c180c2c072680f00481c100c01c01c3e910190600b007940c9040340e01c40c2d262407828402916404290b0360000042d6602248111503070408554038450400e01900c2018070b80000b181141d0150010801c4882c0b504c101844180d0300c1c0d10440482e1402009079000a030565944004240b04d1200541c0104121b0a030300d40300c2d179a85d030010303035444440003004070412320110800c0195a0099103528002d000c50000d0003001e0404030560103420600c06101d4410384a6140c22414075280c010040d0440001a002590300c06007810040d44e2410f903440740c02e20986110078544102c1e04040b03184451150702d43c484441c128240304981d80340200800c45a54244180003030440440c004210041c0240004800052403078203000d40b032820308034004920240c0900400034000004c1c82c05041750300b9140d9845404a50125110000f25261403d42c00ba0521890118414040c03041810081d8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 102976447 1250 102975197 102975199
    0x30209130b180708150f0409030206060915060f0d271205040b091e0907110d14030705160501061d0f090c060f09031606030f0605090604090206070503070809 69
    0x18580c0c0b50011a528a0701d002102d030100014011804a40c1303603500e050705a40510030081c00b9261488811000c02c048842e840c000342c0c01603005100f88142c505207841c200d40c0110302e0301d845184200400c03011400601c41c43d56500080304001075101100301c416480312440c10184010740c41c049504c4d89442070081c25540d02a940580d00b42039152000740a8801c0324106c0d007259000e94102120441013000e1788000e440c11302003400120603005469501e148407076201d100e041d16007450412160500c0d40c6462070021503141070002d000d141040d001015403c2e2903200c0c0d610b2500396541c4401e007a4184800c0d0503044000c10f035608121012405004000e071079040d490301550f180d640c564900b0081e80841805862058090300450419001810a0f500514030400a0a1241d180001020201e46030511100303400d503603803159a80038071070680d240c0282402080d500360103001a81c148000621040406000144540d40e03505035801152100d41c00c1d07900041d0403909513600c40900c0d0070b000307001d51b004809403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 102977697 1250 102976447 102976459
    0x11b050714061b090418050d02060109050c09041e0608070501020c0301060e0c13030c08010204060e0d051b03100614010f09061b020604030b280c02030706020a030209130b 75
    0x30740c0810002501441090881d8608004240300c0146101030b80c0803011482e042501e1341c02030b0781c0e11142c26a508104504c40c00040140010709a03000b4241007041c1c0282484a05000520141030241002d44102e00c0b011500010303040090f90442840946024007840c1d040d04240000030210800b0481c2d40032110282c007600c0300e00c0090020582203400030702900d03180c0881c1c140820050001003002d400c880c000001820400390b2203440300340c0a024198000034485c0e400280a0044640c010251410700381c0a0303d0a04003602c9503030710070b902e68504e4840c09414a41100c0040a02d680c1001548408650100d04105182c2c558000754890028000700a01080031401c080200314401c170f074001c04540302680d8813140d42000303107000b07004540f00080503a8032200c14000070000c0740c02100344030f005541119403140b01c0c1c500c1c03040001c2c0020320620740c004502c3c902440e40c40a560003000316803680ba40404016907844030990264007e018800c2075540210003400d0740180c1411943c04030000306821218 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 102978947 1250 102977697 102977723
    0x6030510060e09070b120601021e03131410030509100c0201091704080613081306031a0303180118030b010e0f0f061018050301050705070b060a1a070302011b0507 71
    0x200f140d40c1d03081c40c400c29100010400811144002c01100d054000f001441900c55450300c03181501580000050f07090150f03000041e502013040111000d94000302111195000503030f2046001440e0300140c1c060034402d160301d80002641900c428880400c1c41013882c2407c005405401d54028020700c0800d00896210360b041256060808245e02501c040b5400d00c2e004269654039105821500c2040707043c112108041404500e1500c43c0100241c0041e087c2c903500018841514201c0c48c503140c2e00f4002040c000c2d00100107081c10704041e8882c200d203581c002e090416403000240000c00000d600e0b0350000d400c025044002103a1518200015405840c08280640c03150715070858050b0181c0c029108158840c06246030207190794021001194034a268070085404140d80b04080703030a407402104c1c12000254005288001c0002320030010343c10001c16207000c2450360501032040c000008003a510300aa0102142c1842058402d401c03c00d80c40d07001c101c00541c1812040360140030354008a100301c030344d1018650 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 102980197 1250 102978947 102978961
    0x711092a03040203031e0403020303030f1f03030207050105091f0e130c1b0f0501060605041d04050606010503091018060e010902090601080705130b04030c152106030510060e 76
    0x1080d60b00a40c0c00070050f501e80798141070044510017191499080e4070b10f05104c0000580d8083c00070310b2040c0c80e40d40c090069894405041c04150b540705101202c0d400d1300d48018804a503000134a07000383c1d0420708040c0d41e0b45040c1c00c0090684582c0440c03032410808102c00300042250301800100c1c044000ba01c201c888580240080c0c1c054800c4003c003070300001d9014145240b02258a5420820a03014410b07504559902c4e450f02400e544542c0c21038000314030001420007107082c040c10003056100c44403000c1c41c2d590429544080e01c0d040042c02a0703042150201c04688800d4007403012071a4840e18140030004403c10542c3c83d080c004641c807003601c090345400341200e000344040c090117400650017400305110780e5500d4015104010081c1c2a0810480c050104110f6080d0f41c03148103010307041c842ca16030f45843c550301e085800760b20035400030107641c200344a0002295030010001141e40c5201441c0350208000f00060900030441d952001d0510711404814a656507104e901c882c00b6034030416285222603039400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 102981447 1250 102980197 102980281
    0x180c020d0503040b04020904140105090c0a09020a09051504050d050606130603030e040903090f0b0904050901060f060302070f02060d090c081b06130e010305030a11060408040b071109 80
    0x10740207022280754100140051807c09142c0743d1040c440c802456440310216921401c4850494015aa5038400d5079584158505040d061004002007881586032048802006003400003503c41c01c2e020f924203c0d940b00700c00f8a20b0003601c010740006031801c542d140b81130400344d60710030f81035800600441e129021134810f2002c500078402500d4141d192890245640c000f40801400401015410000d800002042d450071301c0142900510316030500ea80c0303d603c0c0c1800c0004a901c007602585440e0b140060410000306200da914045410900f40140c42c0c1055003000c11414a1840d8001d46c011000141c2035a2905d944d4841451203001d0351190716580e4a42400075a2000c40c3d0340c05826100f0011542074052404600038021501c06c2d500323103d106903a80380e812400c03000c00e8004948540002c28194101603201c400d0b15903a0002100070aa1402c060700c51961034450341c05030000441000496800703014a8000f868005d6001509110f00d51820a441b1502e000c25000c980241c100000700481c507001400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 102982697 1250 102981447 102981451
    0x30a0e15071805060a110105131a0a0f0c050d15080c041107050601080c100906080c0a020309030703140106050d0c0918051c0f18061107180c020d0503 66
    0xa0361510360700d03500d4080c2c980c00101c40554040422144001c2825201c0304043c0414403056240d40d00c0322401c4000d03070350940310014440c6c04002c841041c50b40124203040041001881d1b2001c1c08001a1283c181c0c0801030200d0000d4440c0c07083c01c208004c00300a50180083c04040c8228408100070704a20003104c0c100301d014400c1400c0390b80032641076009031400d03038031002c0311500d50f80210385051b44956503141021002d03440703150541c10040100e80350b0b0401040300d00a0070342ca4644282c003541000342c040e01c80c1d14050194140c0e40001308215030064002c0045800142005003240d040503a42d18100c1c8150500044000942d403c04c00001000c3c201a44605a00c9501031010307901039051a034a44020068024104095803042d144c0c000400c03400d01c90420300c2010100b0f400360035482044041e1500a40c0043c607000c0011001c0b40c101c607030600d03044e40001e54072076142100341c600140c25110300d452219013020b07484140d14903c032070350903a266001c2103019260b502521540103940070245d03064002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 102983947 1250 102982697 102982723
    0xb0105100801060806010507020301140609010510081603090501090c0501021002040e130c030c120501050121060518030406020604060b04050403051b07030b04080a0212090d06052a030a0e 82
    0x1e603400500c07035640110a040c0c1d020f50107140c002d007005115000030382501c0340080200001d000741014843c040c10b1950780b241c058901030f0784200c01001c0292008200c1c0781c008102104040b50b82c40d1101c165403007034100c8030403150000001c0c040901039007800349081c0003034490b050261007560141403c0b071155000307032402c8540200d400e60780c507952082095486010320b4021110740d5018200400000e140200b45005011408050301c0d071282c0030701d0700c00e08440040c0c104803005801e510b09118050f04401041681d150701c00408992510b401c201c59820315044403203595140000f080100381507600041c501d00c500c0c0141c10503c078a108140a100858005441c0a00016401c1000c00c1c6035403c0c0d20320400701da0201070100d4560380d82e640c40e080c0c071419091b40d0480d00e21030000307011000d403581000550340c0b00d03200d19861450800d00000040d401c00904c01e0081005403210000b4407010800c806000d40b84054000a0164541c1409801c200780c0c1f00306c4074940864079040845902110009000005440c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 102985197 1250 102983947 102983957
    0xb1b0d020d021f0204080114010819020f01051804050109020703021b01050403080a1101110c061f1a040512030306120f070905061f1e140d0e0a050313030b010510 71
    0x20502e14001c0b0704000c040c3c2d84040325400f00320020300d4840034130403d000d408403010302d03509550501048604207000c00e8002207581512107034001c09695240070a240200090030459900c1150340c4071112141c0442c0f20391903005103048000210240181c0080400314032950039214200f020b04808c0090300784030090300d40000e82c1403109000107000200244050b00f02c0f810000221610201c0450941d820112002002e10000c030310f20179581c074108151038000d98800d4407a40c02104920003451004520b2144040800306410001d907050825021078000c2c0030080d001200c08400c0040b80ca60f00d03442500d0650045000300f0824114817008110039000b00c0c070110180120702c2c41e040310000600f00142c54182c2c402148220180100360410b200000401d00f078645004480341413440400c03000340d103061207040c0220181c084812540c400100e81c0350004007000015003140c0700e0f0200e881d1100e070380e20040142c840042d507030040e11110084041124810100021260303215018401007181c1500301c1d001080d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 102986447 1250 102985197 102985213
    0x905010e0f0709030f0c0e09010209030a03031107020316080606010f0e0103200c0601061407020d0b040c0509040507080c01030b0d030f020f030706150501050c030a030f060b1b0d020d02 81
    0x10307a4a0340070641140c0103107000b01d0724a0302c940311a803003c0e400c40c40440700070f50780e58410010080300034012648289114001c50070500708401081e00e45589540040402d0703075860100c4003a0840005032402a40c010302202c581c84d84518a1091a080c10700596100c1d1040800040c80c0c1d601ca2180300e14004001d80d6422247c00440c00194054403100d540c0340918000641c810100b40410005400003d09c08002400c641d4900000904400003c80309000304a100b000160050384500318001002e503803090340070040c1d650f64202a5090030716600a035030b1015920342404184100000c25005403000c490588081c03060310f1005404a865480440790400050004000401d0240b9001c5001e20072038019a055581c1c6504440d00315440ba0000b10381c010740d0384111940d081520500303400030305000e00701180303018030103480256640a0007603140101511020100402d928940140005092100d015a00e5045007811207081d140000d1040c50725105a540e0b07000e001c2c4c80019042e112a00c0364002d08611 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 102987697 1250 102986447 102986461
    0x20f16050a0b0f07080a08060901060e030a230118050705040b0a05040c0e031c18080703080a03062c0a050606030604020706020903150402011704030e01080406090b0405060604060905010e 82
    0x30303400903d1184401d0000707001c0c180104081c0342c010116448280d88160b25450600100304007050103811036020030030b40d014003272810780340003810f0410960400c1d00402030003060b10808180b0110100b84a4065007003a4005200300708090350480c080d413051040d60324050300c580900048404a01c0d80f15480b4071215400c20031410729901003c41c62440d4a0980c61403000e000100303140140d080d0022130408207100389004000c0d2301500c01d03040c4a500d40c0c2001410751801180680e215554040a00340304400151031740e0b0640a41e018130700070109030808120403140c40c58212042c4d104d1492164103a05098005070400f0410f1003000e105020040c0070a0540c3c0b01c0405200003034211242c22181d040c2d00b0044d1b0b04103507a080200f04180d0345d80303804004581c0f0b00b80c80010f002c40c00e10102041004002018080020b4100c408407070169801c1c80d0240c0903940d10f08040014245006014100382d04031014003017840340100300b1314400c1c2425503080c040141d480c8406400c8030024420301d1700c9210004c3c045024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 102988947 1250 102987697 102987719
    0x806010e01120908030118060b0a030b0a0806131a060120031201090e0f0a08040302240706060e09030a050904022109010b0102010b04090b06010c051606020f16050a 72
    0x450406141440449146510b000100d8290030015a007104000c40100422440d00740b11004080300c1600c03c1c80042c0c50309071880100d0140320034007000d25440d00107003501e07512600080c00c000d0120100700d0710581002040c24088044c0c2d640d080d9030301f046c0d8220401c0420520a007290190406035100842030482010b03000002c0890030f102080b60004005122651481c4034046028010390080081c000c00396600451130138070708028204580d08104240408a0b4204099400f2690140c800048501628a100035a941710311440d4900744804038810043c804564012019660351032032101392a00c85080e21650380c051094120001101040b0051143c20f0079000760030005914482640042800c0d0b03c003241d402c10031200f699907607550b610500c00c55079090041140000342038404100c03d1a00b41c51751a1111401814039042c040803640c00010042c00708029035806001e140303e207010030749559009451350016481400a4800d50003110f8940610184100445000810740c0c075190303103401c203d10390b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 102990197 1250 102988947 102988967
    0x151002010608030c1f051e04050a06050c0307030c18060e12070830072004050a06050102120f0a08040f051b180c0417010605190503060a0c080601 64
    0x411552268400600707a182000982101c868890240400f0300c022a8090450340a03002207003640341c1403809100c90b2180444604550340c040c40d0418100391703903c2c00c2461400e14506801420589090200100f403000000a503000311040c1c2e40c24010709200c3d202c111002d600b041121045d0b40f0b26600c08010460041011140200780503001c0d00c180340b1040031240c10312400e5840110b40c6c1c1c101c1d540c1507030b8100204210100300030040720f4820302c0c001100301480d154090002c0003062019a003610394900c0a1602c0d01c1e46101000502c244128a00581010060050781c49218090b1207004003402c4001d00800a480310348030010180c5003418403a1104581c1d40744094000ea8502c81742020b4040032030820300c07820829400070b020a0201107220b400340f000b82c4600d84000440e5030034030703000e007d0600f54110031034045a01340c00741e84642081030b0300140d0040c40141d10260344070741c07072590400d41520007072403460485804606a981a42e504044501030303582d24014440000c09540010b4215070141400308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 102991447 1250 102990197 102990229
    0x50d030b0603071b1203090b070f0914180103081c0908091009080f06060a170a060507030e0105090106080f190828021f0212220506010308030a0c0815 66
    0x141130945652140e200c070400389014080060703241d2421000380040484242d0708026680b4016446e8403440c00028206103aa004081040c9d10102d46006180d8603080b07101500d4200200040c0309503941e1400c10700c0350340300c00081c104003481880300d071100f00094820401340ca030700705d2802c03441c1407015401c0000814002d100041801000305000c101041c0400c407681401c002600181140d003006000c0005070800c9a101d00b070526401c103040d00d060000840e09010190b030105000c41d29494000040d030140bd50b80c000138805610700000c00044400c15088503048900c02815180d565100125040d201d008080704214103154181c082d00009500c50000d0109003404000003407655082800031510075a00e010000043c1e0001c032003800901c45208420010080444d011898a02d144001d05420341e40103288281c01c60042c01c0510b03080e5400c1007043c801d16072100555410b984c42b4034107807030180c0040c0c910851044c0380845645045000e1400380d8041d4184800010750300101c20200852100b40d04145 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 102992697 1250 102991447 102991487
    0x1030b1003080a0207080c090601120c0201060513020d060b07023f0c01021203090712050c0409080304031806140309010b0a3c05010513120807050d030b060307 70
    0x81030b07541c0301070859800780b40d014104007403070440700c2c0d880d0611544865205002c0302e424803810b42c1c0c000b480005468584440490f801040d00e10a900621840e4020f582201c900c5103490340315000350380202560722140c6402c101c43c40e10350b0007844140c0900e100080d0010304c0d03000d40754602d0b40011801c50600c000c0000042480e007150300c40d0400c1c3d140030401d22140d6440b41c43c0d802015038040c46260580c803455107082e401d615205444a41d1508644540b40c18406100c01d0502072080511520005002c094000c4c00b40f20b6040c40e0540036903008032000c1d000189141064081110300441120443c1ca00d6541c00d440ca8010000030582c030350000d0001070740c640d658400d00c6c900d40c0f01c0d00c00a100601c001d6082c040b41c0320317032103072003080450303840e101ca107e40807d40750860010358424286005803070007880d140351200c00300d8180401c00c084035040000b1120b0105104c1c01040030b00001800101e11407429503c104592031020b038280d40701000b40702c1d400581400000c145a101d0305911100d0744030803400c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 102993947 1250 102992697 102992699
    0x30412260d0204080c030d02030904110c0105010b0a090b0c0a080d1e02030a11130308090a0b0c030403060c0302030709181d0c030f0a0b010513020405062a030406050301030b10 77
    0x254a140d00160030100722940104080013070800c1032001040841096015210a5105003070082d00d174800d07140e445210b203aa075501580645901802d64100f020b020f00200159610ba000945ca580c00c002d000600050380646e0100306940300700c080e20a03c0803500024850315406565800b0b058011025125103d80ea41000418030140201c0107101d41c2e40c50100140d5906210807440240c031480300580c000c25108016102c0c000305c20f440d602d01180c5e0012141501c036039202c4001400307401c082d40f000184140c0428100d140103408401081120b115100070016030610480540c1640001c40304203010a82c142000c008221001240d8040000380000014002e182d1034014226054141d120303900a501022032164a41410022805400060001041c002e19941e9624080b01014001c2c3c9014120080350031409a2060301500e016190040c1140d460b0711300741c040c0814400303111078269080302d81ea001800034071a000c0300303c80a85407070340d070795a107540e00f10348401c04130190141010380580a903040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 102995197 1250 102993947 102994013
    0x11090603121215042306040e060112060209060d0c09170c15040906060c0b0105030a0506070e0102010f09080706060f0f050d0c0308040b0d15060c030f11030307021e030412 75
    0x8120303805403c0d40c0403241e05045c002403c080c1c8042000340064002d6280041c0d01c1944080058081d04407064401c07260801d29061038407002a01501500b141c01503008103540c20004419000b0403d4003c165544400d2680e4800d0303044e103241e50101e0f50b60142e40106074016420305104061044102c0386511181c9410f54a14103203040301d000782d004074009076502e01007400b004001a04c06006100807401040e603001141c45080e1a030074050494001c1c07002c207224074541e99000b908038107103160600360100282103090074000c0c0b469101010803219a441c02d00301040300c018000401064449154000350114200710a1082080b200700381a0341108046200100090300c2c10000c0c40070300403005046440c0d0701d80c25400c205941031042154000000300c0403d00c13619521071412154240c06103004904002c180c0c00c05d80318000b01000d1340e401400004100036001e6000a6070030b40344600031000310b482103090b03021181c03680200d024086880e01d4001140012031201e044403c16840e0b04420740808412900e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 102996447 1250 102995197 102995201
    0x50c090f1503090f010b0f0102120304060605100917010504050c0607030201091509030f09031203051509071805030c090105010302072307051f0801051302040504091109060312121504 80
    0x101c82c00144d03882241036080c10038007030161300c0c40d40a058414801d81914000040d45407035103103000706138858001c0005011700c0215013005000301409410a5000300000304014401c0170103009a20302000100d030448070014051291510541e08200a4034986401004101300341d44203401c1982107641b104241c1011540c080da503614850000d50f0000784401d603e00d009400722400200c142c041c84007030b030b6040012400d10096981420500c2c41c0020360347d500c02c2050120440e843c60b0240c2c1108200c07040007055038008404042008401001100b51076882d410565100c514000303d6401c443e9410042009502940192121901c60742800c8090b20070a02101440b50707242ca00c46409500040d4204520705104a18018010303a450740c0030044920a40c0180c40c41e0410321403540102044031496282021035070644015000c01082440300048170304000c031000d13000c5100f95124138007a40c046041d914000920440b0303800056001420202d1b60984162402c07070040c607a04849840380700b92000e6903154 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 102997697 1250 102996447 102996451
    0x2031009030207050108010b300405011a0a03020f040c0203250210030501050915062b05010608040f03180b04060503040302010b04111206030703061404110301050c090f1503 76
    0x60480000c00d00041e050092070008940d202a06024404005002c0340041504440458002080d411a072a06c00e81684000400406110310140401800d200c05c0000641000700b50a81c0705843e211110160341c100000c89a481c40021351110003024192110b041980154080d10f5450040e00c4c10309130250841800448901405680848100c07007000841c98030900100083d2507034070f410049981030601042503e1030183c0503c5441c181400d8501c4940d0b5404200c45080e41d10324180070304854102003480c8940d0041041c9101e50741080c00100d113080c0301d141c41c98130036030700080f070210071060984050300d10b0580c02c610300c400345a10042c00304500b085900284000c0100760345495881c985410000d084408004107680f0450508040c03004543e00c14098070003800540d08007503102c1d101c1d0070000c2d02c2d000c4281d000074100b80c200300c0461004402c00d80658405d070b000c1d002119010964008142c03c0300e10484502c4081c41c2d05000c040e216003440070111004e000c01408800428480d0348003110301c0d42003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 102998947 1250 102997697 102997723
    0xa031e05120409050903070f0f020a080d020106090f050702060601050f13060c0201030e15010b0f041203090305060109090309140402070204052409010810050601180b030708070e030a08160203 84
    0x20002e410000c942c020300c503a80d800180c80e8007960801c0348545d1180d10303c1441d002c0180181d14090006015551416082401080c01200b00ca111071b0b03c103400039000c0c0001e446003901076458140040c010f0005070041d80d11402140d809040c040e9550030064409403c51500ca1141c0e11040c001c402c030044884440402504d1903442e00d07001e1309031510004054428215583c4450341040c1f0714884814003a04240741507403d1440b41d181c0300c13204900a04854002c9074130a400c0a079201a81005050300004c212059a0058054450a80e03c400701001a109889001000260514010007108100312004000d0800082c00549000882d8000401740d40c42520303881344001d0f0500071800342c18190a010815001e060b10554042d40c584917295854000012034190400d4440c000a44140e210b000c40d50440c07a03030b9804605c5806d40b2040700381d055800813155800480c0c400800303d50510f01030290805003500c01001031030611a03660310303d82d00c5e800c1010a09540d01441c2c1da01030041e0707418022040a641 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 103000197 1250 102998947 102998983
    0xc110303040305030a230601030b0607021e010908030a050d0b010c0f03030f0c02010b0d060906090c03060504030801090204080d031a0a0305010f1a0d060b010e091e06030c0a031e05 79
    0x3c08581711000ca5200307a56403515200700c450035004981d400000d90b0340c0f0400c2400c1c0011885100804a095440b03000c0c4000d5010401e0903010050501c19004101406000ea8441400c1c9403290030a82e6130344205100100032540622149503106082e80111503903420602d4006403c3e034072542d481c0c01610b0005000c602194582c2ca05c403c0d940c1c0180724041250a46100900010249902180d0407000041024100940f1241ea4809010164109404c0d2a40c08414141d1056507400c12900415003510101c00060b24000000f540b804140240c909490000c00602036807408a48240d0042c0059083c1100141d95040036030000c1e81c68200303020065004800209180c0010180003045940d92602c80c540340d541800005142d03269203090450742c55022600140700005080160395500000f40c2c02984040c0f01070400c81c43c0302c01e4001c14000002c0180e01d01842d4bc42c0c40c2e0406131622a0402240d4220b400301c01c0820128075500415070003182c1f066117070519041141c13995804c00d8a0350a07624001a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 103001447 1250 103000197 103000201
    0x3090609010f020a1d150304030f02060a140109020307110327030a0b060909010e0105040f050c1f0e010507021504031a040203031b15010e18010e07090c11030304030503 74
    0x368081c00b980505030b042071011894644500809404003820003091100034943e184107018984580c900c0204e014a4101000d44034a81450014440c0c418961070200600442c008140362840d10f000c4c0b40200c8480d6013080c03086a0a00390204000d410051a85d01040104081c0808030b00c4107000400110840c1d4910300880f0099035001180740801900060207903029400c0e14011441100945410080450f600d81003070b19155405e03800b4001d42c441c0b22210703502e0181404104a280300700c036a2210302c28029100541018401c00c4054042c1d00001c0b0011170385240c2c50000148a84040040d06e81e05050560400e01d0580200c0d101608241d078540800c0c10008080c000d00c4203510304c029a0320b0302ca02d20329586241c154003094481c0200c845140c801b900701c80742c0341e180e01e0040c00449921901070340012415a903401500716429000d950307824100c9100c400c0c5160f1410180030300303081c100d50080141901c034646502c190051903d482074400700a800006039020650a10056009038000c1c0e90382ca480e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 103002697 1250 103001447 103001461
    0x3190206071812030c0c031b05090702060411010827010204030b0c0304030c11180f011406090a050f1207060513061d04051021050c01090602120a090b030906 69
    0x2c0302c910307007218041c68024800704500d60240c00210700456243c5804040c4200c1450100116619500001d100341000307500c094806c001d8050359012608110351004103a00c070302100b6600c0b010f0035100506206240204041c844d4064801a5040f40d508494103450b840141c0003606203c502c5140d26641d6500010704105104c0e06800d03c9400104031618503180d41001d5402034802ca4804000074244002c5c118010074982d101900b850300034640c04480303405468201d0070001202e109004501c02c001215a01110508116040d5218034030301410543c0301608000401c072400ca8100452a8494882e80300c03031280b20824032902d8010b1985d9240d554039007100f04c019004091075900884200110090100c0351040f214080500100042d0790000e41170702e8440e02c8090b42e807c10b80140104201c000d140e25501282300043c01d20003401102941c6901c42107000444064100b4400c220040e07003e0456031007007150107002800c8548060400c281c0e585e54641c40031500703800480f00140c09030810000c00c014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 103003947 1250 103002697 103002707
    0x203030d1107120212031602010617030a08070302042102060702040e0a05060f0601080a0e0703050715021902060a080702010f090605160201110f1b06091e0705100e030319020607 78
    0x6030240f540043c0c00d032503645025150490000034024245000c541d04e0f01c2c0c2d8031500031342c030000c090116500d54410268000000c01d80e60f902c0752800c04006561140080d000364442c0c400d48041c1d52240c06020051204561f8440c411b25001900785e900036010420ba50050703855104078824161002c0150807916010b003010b0b41000c10040002102200d04000c1203851380c2d00020241e4081643c201c0040d204e004c1c1e2300042d01d029450b4000a003e031185900c0442c000a84445280c0020346075822101100482e15010f24071001c0c0c444000c0d0081410f0200c0341c00140a940d5080d808445171000140c1c281101c6410702c16150042000d8032040e55840502080c00016982040034036a44d0000b0b01c0420040609c00e0304034400c440341c50022640125035030303000c2905220140c520844120807a24a4100b11181717030b4a03900d01c04640d0043c0000382000300c1071803001049000803900d000b48100c2244010318070566503600c0301802c01d94507020801900341086c02c4191010990325440d4020300c400d14004070042c00e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 103005197 1250 103003947 103003973
    0xe0d090302130501080c0d030309050a150e010b030703030809150a05060f04051e070c051002030709120c0605180613090c02030909040807020103270204060b03160c0203030d1107 78
    0x220b05042c44018082407000207403182d02c42d40152050405203446040843c0100b40f420300080990282070f402d8001d10450704101c10842d40c429404100c031a00601c560f5080700c0111b82120340540254400b000030038010103000e980944181c080d16404000911419444002126030302c1e00b45640d44248299030500c0040219201804d45040180d810200c00481d00c0702162080c0c05246c3d9446000a00b889104e00030351141d0320391090171590700c0204288400081e41080390540000b0b41560300001e50100d0300c111043c00c06801000c9411050b0030300d501241c1c1603200c0880102045021a1620701a48640740180034503030000c040a0b038150700b40301c0c0d404141e441d80e03540d40c0f0466000b400000101c1e655a41440c0d04154071079407a6545440903c016005800858441c62556540141d035a4140ba240b50070000340b5403089a0410509850384410403450100342c4190750840000d650802c0303d24040d0a10000140c00103003220f09200e02c40e402001654072115200d1455400414101c041000f0042c48103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 103006447 1250 103005197 103005229
    0x303060603110a0813060209040c1d0a050d0b0601030b130506040c031104090e0c030115080c0114030a05101505130506090609100c0b0c0403020117010f12020102010e0d090302 77
    0x1843e021549000030134083d000b42c000b0a48000841c1a64208034459044600d209405001030016041902002c2e050250403441d1040c0d18041481e071040300d10b0401030030000d07128020140d1586c100c0944034910708910003001d80d03050640d100360b084040d41ea20b1160030a0b10644040224051408100f8001a2001c52860009240c10401f0760b038030f8401c5100654040e140300c41c0300051103803020b44c062884d0600203110281c05510381861000381e1a502d250b002c0c141d40905040741c0d0391203444001100d484040c108001c010081c01c0c000310389034a2080c3c00054000781018a001f403200d4503100354221141c0390b9688607002c0365001480c1d60400381080705540040500700c904a04110aa002280711449200c1c0348920a0301c80f4034211188502500091020b56089000010603250840201c000340d03205000580c04180e0303803007500100480d030302006416111401c4c09981c403a840c00d4031200d14449108002c82c10742d5210008800ba200b401c11a14160b060a03079079250300c0d40e01d1030041c040d10720404c4a071300c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 103007697 1250 103006447 103006481
    0x2030a200904110103090201180807061e02100e0f0d030605030106050a05030606010e06070807030e040b060a02070e18031603090501140f161203090302010c09031713120303060603 79
    0x407000c0390061520f02c400385001e08001c244100740d807004071030310384492580100d02c004903000440c0203200040c6507400d03500c080d01c40481c0d80c0b1000004490800b0081c4c40320006910139903105160401307075040301144103c0041243c0007040340d02401c41c10700c005050070100080da100c4007040146024000c5000402d001d0b50303401c0b9610b05000c08680c581d040208401d040c4500da40f4206d0480e2201d8003250152904030524a4a88070310f454000c2c50210015840c1c0c0c4614206500d0700110f10f0303c1c40c11100305030982c0d00141281840c2c41740c10944820020070510720707804150203c0e200100103100a09409207141d142e646c3c512140e10703000d800c02103960041410020034031180002040184111102c282c0e5451100351100d10200b00710042c014401802880f8a4030306d0480700d081074260308042c001c24401c0e002480885540c50f01120f204c10517200107801543c0320301c6482d01460301c10004280c0022018841680f0b40d442d4941c01c29503409030344003200001d5580104100c1180d01d03215481c0d8404035041c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 103008947 1250 103007697 103007701
    0x5150a030f060203060d080a0c0b0f0f040f0201020c040f06050306090604030906111e060a0f0507050405090c040f0b0304051203010501090512160f140604050612040303060302030a2009 81
    0x15001a448103200010901c2d50b001001c25103d0392820207200203140e00c80036456441c0c2c0708c00e5000b8060100d40004a4241038954041070300810ba0440140c40b40180c134807912015074031500d03058081403001c1d20071303410b601070b965840d20b02e601c07540291315680040c40c1011a00515140506141000042000c4200e400c403805010009501c80d40850448006107007016617460354120043c28080461810b02c41001044040100440040344503842000072807030401004400c4450703a825580100e51260005100300024040c41c982520305a41184103401c05508042d10f40546c01c80001854000030240303180841003000700704040064040c031039400c010260555241c0300010b084960070f80a024850300d00b0161041d403031002004074600c03604200b070b1000c00700c603a20700717540580c05a1401741e4074545065800a04950400504840880e00050107562410a21680254181c100640704800701500c402d400805a0381c1000803081e2180640e40002446507540000e040c040e501801d5240078081c0c03002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 103010197 1250 103008947 103008953
    0xf020f1305040b0a17070f03150c0c030906050a0c0f0b0906161b021909020d0b01021b090402120a08121609062102070809090903120c0f0d020d05150a03 67
    0x10242100c0d0300c00f03007550480203056502d40c1840c440747c12a10103040e10807000801c0c0041d6008000b1031110b0b00d030041002c0d2004520886800500140180c0400c80030b60081107541d10400042c41c00045500d01050705000f90307640e1540035240c5100070f40d101100d9030244100040144416604403070000000d01c41a0100313000902150290700003140c1046010030f4180a41d19040b071000801801504201040c84e103400740c0c803000b500300354602c01e0510700d4144000400c1d400003500f150b4802007880818418000807003003000d060001041260040104031103e21081c2e4100080d0007440d00c44d11095840f0000d00079001b080c1c0c40c00621103142803148043c00c0019580015a8401391605440c00082209a240140104025003110107a80b244000740d128240001070340541621802140c80d146030b80c4480780c82d16075038080e10207170403080300c040004581400e410000070080c10301109911400c00e03e81c82c0c4c0d2041240c000e903600820280d1100104018125452242c1000000440300c0c0040142992 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 103011447 1250 103010197 103010209
    0x212070f02010e0f030f010903080a0c050409090201020a05030a080411060304020907141e0403020306071403070c05010b0a0612060503120a05090414041506050103051b0a030f020f1305040b 83
    0x1000c0a4140715010500007210385454611800d074400240444040b41c6600c0790040c0241100c1d00c040c2c0004400074041007025046010b00d44c941c0040356501401d0606210192000381079000c000c906602c290751a6400181c4280060161410700c1c0c0c07112101e600d0241000803860103500c03100c5104580400130031005a0b1040d44241d0040940e183c801655003541203007002a200702a042c44481e09c1e80103498031000c201100400990f4402e4041e16180d880b410000d844020450017480400d034003d1000810880c82503010340039590143c4004148040000045810040c0740e4002c5400540c0f010081110182c0d40c0c0900801041c4c240c0082a001d42011303080c490343e004610301a0b0802100081483d140e5440d42c00c6996444424001c4032010308051a200c1641c04158250000a03030800300700080c198080d2242031720441b04c0790002c2c0100c1020114881d1154003503001401455581e818030020039000d44090494040c000040c99920311044185083c00c000c40e07400f41c0d10075810302d4040007040d2914 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 103012697 1250 103011447 103011473
    0x6050f0703031e06090603050f0a020901030311010f1d011a012715020c030d030c020307080a170117010f0b0604092304030806040b06090a1a0c1b01021207 68
    0x1d40360020b00e154490090102c1c2000c1c1d800e125410604115000c40c64050035400001264841d00c11216000213800c4e00d1522041f0581e40079500c00468401000445d00901081040c082c018000207000c820341018901118583c131a512515441d921044202d40c609214941801c40d1041c2d1542c203482c80c0300300082020000305401c0f8007080007002808504403100a0780c03000303040f84038601c3c0817919401030001c0d0382d001c100c20094030034032802160070741d294024400d1028490499001d140381012688410b05654000007a0b0010410700018072881e0103200107106000e40300201c569007000f001c3d20400303800d442e1f5a00c06c6406a510708604446243c0c0d44400312000c50b2480780cc04104c00c03080451b0000700f01c3c480384500c4845000d40041104040d84002c0f80380c8500d5003101d041241002e040300b40815401400a4a0303000101d03010140503400b0005020702d49241c80f40d42c01032800c00514545414101c03c0441a690820160000d24003580c0601042207840035040010341080b1803603c070b0000801700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 103013947 1250 103012697 103012703
    0xc120102030907090e01060807121b06090308071a07020d1107050307090c0e030604030809011a010e010c140a0c031106070f080c1014060907020c0d140a0b0403081006050f07 76
    0x900c44170464070f40000c1d00321600600703500e0155509650303103a0412114050407801111010a401a1981110b205c501d4401c16103480356201d403c1c4d03d04655820b60141d00040e000c3d24680d0748105c0c448070240850040c0e41c425521035000d0143c0403004800501005019401c00c082c641100300306102d00e0f10002081000c8641003040030074050044c0d48203403490403941c0c00c1d039601401800108820f06421810580c0125060030007000102e1501295407200c0d500c075000036000911142613140298880d5446085071400780680c4c9051800300640705141201c141800c9801c0300441204009104040c4a6809124070a6641d203140111554640307052100948006202140104007808108004c1042c501060001c500030800e40d09002c02d5601c9151084421a12503a014800541c2c243c1c80400e008034402809410141069940c1e0365054942d900340184441c6441250000000f1811411410f4002d41c02600c82d80481c0c204802520005102038001c2003e00900700420704400c0c60f200100c0b482290 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 103015197 1250 103013947 103013951
    0x10903020f0102190c15020c060426070818030f0a0b0a141f092310140f010311030406020c0f07080d05090102030d0f060f05010e060d0e0313080c12010203090709 71
    0x210030301c0c046e5a803e110401041c0c18910118901c801c0c2c41000070a1406540501c200d03181e903050300c0c41080407030000e4074502101080240320210000b03030b4107805802c802c400c8480001c4960481c1c80413a00e01300011111194641c0300110f0807081c0a10b61179450342000322040140800344c080382410780c2007200541103010000d0b48100308802418848000320260a5926090115040310302561013010900585004e0500d402404280700d040c86045250440b142800c85152400700c890401c034000c101d1100582c18582c50b40300c425826803940c0000d61159200706001038503100c005440c40c0c0303400606100451340f64000c1c0b03400d000da000006400301091003640b074203d640d0310780c1c000100d00718000d10440c8001141005211382090180da0000001c0d80c0da05459032810359698001120f10304510a00190400401c01c5549000e00c8030750031400c8029108412a4a03166403000812907920950788070840703c1d00b1003005000c0c0c030718026003109182c0001c00c0095042d41041d401d440d4a449a40c418601055 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 103016447 1250 103015197 103015217
    0x6040b04090b06151207080a050a0c08010302010e12011103090d020f060402210604061e0606121802091602072309060a05060406050319151e03060e010903020f010219 73
    0x9503444100c44080d021603441c5c1c1094202080c01a060100541f44078145900745000100703c1e10741d03442207071880c00c125540da071050703480c5400550f005a100500150030800071225200e510800f40245180c001c0355865803030340c0c2d1400c0000203003000d402c45040c8045400c290032840400000003030789500250100d9031251300380c60083d440111182070840c104298001d03042000180507081c1d102000c031960300021401c50041d000c1400f001c590180c000d06000c141e102c10615140d80e1a0703031295940b2445c544544114545a40000307442000c00c56000400342040c3d074040d1110366061000b0b80040085080e98480b101c600d01c083d200071883d416980e40140090f00018010b0f80c0c51025000007408007404a5035119180c600003821a80201c1b840e800d45584810b43c2a012400b40c80340b0954000b04040312258282030100000103001c803a20203218141c00100d0120104402c0d205215004125100020b5100f8180c50040d081c99460128420303582d1040c000094a840714007040c00704c0703400904d40a42e00b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 103017697 1250 103016447 103016479
    0xd05030c04120302010504030f0305100308070507120c030501061e0306020c07170a02010801050603010f03140f010606030c03050a0b090601200d032003090d03020a0c020306040b06040b04090b06 85
    0x2a005950246540d01c00b102011024150191300c140d005a00903601c020002c002c4900940540310700782d0fa00b14184886441c1040820741440c05421480d1003141564481a66000d40c04103c00071203c041d55038411010041040180c01d01c207907001840d00c0c24007003005285040b10b00103e118280f2000d0700c8690002020796458009204c1c03203000d00454010200c8022242d159590784190544007280418401400442c8034074150b01a60304886510283d00903680c2591358030460a440c0542c4410f0034800d0010440d440754080c01508082d00081d40c001441010032400141600c030090321260900e8940000034082e92142c03000381798024030070b08040104038202688102c20001000200c41c160203001ca29101c2d03e42d0540080400416404a1201c0d0307089a110b2000c441c4801c2d0b94a522030751180c04840100c86c029000b40082c1c000321305041c580c0e4445600400e0402c40d084900f02c071030030769040421016162900c10721042c4d02090380c08200310348659880c10240f0801604040c8a113044015004d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 103018947 1250 103017697 103017721
    0x6060607121806030b0301110301050603060103020a0c0506010e071205090c0103020a05070c241e0e060f0a08090106060f0e1e030313080c060711090403030204080106080304080d0e030d0503 83
    0xc49011450050400d0f6662440107000740711180d40b0500c654241113021200001c1c18080d24181c43c40209030301d00d10f0310f940005400a501a8407a001400b4513485060b000c1142440450300030b269880103519545406000100b01b0150313071160080b110300d04000c0c00510100090044100c00007030800680d22000700d00d05603401c0c01a0b100c0180540700d551004074108412009414030050706c20040b0707544003494001036803990302c8158041c410903c0948111149807003000208020080585424a80002c0e03d40501e000c0d0301944480001c114070500740810f5072003d224100c0101280e01d07001c02c00440641c001850260303c2e061013403042848046052030714505958440000800408903940d4200301401001110300314450b440d01802101031425085c00c00508503026141d00c010201034086040082101c4131401030310940800d54240404100f144007440786501400307404004503101d500e4035040c54644003100240104010402c0001e03611604d002800d2185100c040c03e140d0b4580d40e84003d0941 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 103020197 1250 103018947 103018967
    0xa0507061106162304150504030206030406090602041a09030d050a12050604020c0706081009050408040306020d090203030a09080601091103060d06090b07030b040e0d021c030b0d1a090606060712 85
    0x18482145030304d01c0745080d100c0300034402ca035004550743d110a0001d070016100d9000b90700c806900100f00304002000110700c1c1e407040745a24411940141802d88601c298080d4180049546036032202c00911802140340030040e0040080a51600901c4c0801c42c1c40d008002010542c403e1047c69140c5c004594140d8843c0c05031501800b0000031240c22582c3c0300b50017807031108141d441e00481840c603d000300e00e010090141e5131145810101562810303145540d05402503028900580300641d070f9000240040e40c05000410801d103c554864189608181e07116041c688180d115001c440c1c6010700c40300c0a06000320030b03aa40008105e0f4174680483d014204000a02044140141407003000410460095055408981071b442d081c0c404000d14441030703034166580e074071114469016a200c040901d1281500030502662450280381c04a9205c50100109040c1e000a06c0304640c08a2610000d00001e00101c0c0155404007035100200030300e05000010034414420000e0141a110120070151107903401490245 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 103021447 1250 103020197 103020227
    0x121801021e030403120f020706080901150e010f061d0d140a0602130501020c0a090b1914040c08040c03032609060a0b0303120a0207050f0d020a050706110616 69
    0x540d4010991070220746030351203800100c45a9410030318140c00c0078400d450307807041150190000c0a80c503041c55801c0da100007005140501d43c0d0f489080e5591442e81c0c0d40d00480081820003000e08080d410041030805140d2190055010070a05103443c3d4002c91070074000e4201d1580a0310703404003a0398a82001e032072409507080b052130148030f5940030b0030030030806600800040c1c1000c0101c04c181c40d00c44004903100c2c2da840100341c0e4421321841c404d009000c0706130b019850303e14000b000800700c00006007025a0100080d8415030300c1402c041c0c421941c0d03003054000e0b04685401032800884030b00d8950345030205c514082c0000341c100100707600511030b040c074180344000394501d0302030a040c0d0b00d03c1d016146035501e4108a81880e1854102030088216007400020f0f00c4ca00b0f8803058503402c856540180704c1009421012081d5090f204080b06031510410601880c850050258068031001c119420b04510b0700816038080c0c410490015604040000c021a20300c1e04007159400841807900504012150440032038500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 103022697 1250 103021447 103021483
    0xa170705030d050903010605101e030605040c090f090e0304120f0c0e041407060e0603060a0308070f0b0906040209040609020f0307080703031806020304170102251412180102 76
    0x500e0b4002e0f016000c1040100c00a1015035114414040d5801c000034175000460b101200180030300d4014241d80309401014a000a81d095440000a040da40c104034828007080216a0a1111b4014140c090002d4204035409000c0c01c3d900383c6200c0d56070f11807031140c00d000a2104240000b00500035140007000ca03005604040301540300e031803100c85c494058904407500403074480e8101000501180341c0302258480c3d15298241510a01840b2503640010410359200114210110010380340d0340203050100d001c0c840710b10400080f49080e03519190040c01401e8154001c204002c0166540380c1682d41c00b55206002040300049440801c4402602c504480da250103032590200d400341c00000d011003141c1c06944c0d404000301c042400d110380d0700c001d4054000145c10800007800012800031207002c1c1920403070001854850040003110740782d000c412820f154400946000004d100f2505547c140041002c0c018055108a154440000d0f2140c1c100b0f162a60303c050f02000007980c000c0c0080300c3d0080c00e4680c5c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 103023947 1250 103022697 103022713
    0x507030804090506010224011a1c05072a081606060312200a03080603070b04121a0610080a1d0c1903030504050105070c120c050102010501080a020a17070503 69
    0x4150041c0c002114054010701c00d0003042400d20b1000c02c40035a0030590050070111590814070301021043c018181c0100440d0104480032b0b006402e413440344001c040c00e08000502d8200840010f168500b02e80c0c0c0321502c500f20310b02142d5017801c00d00080f040c0d0750b403011403140c1e1440e030184404501005075002620051078150700000703024000052940710142940c640344603280095030781f07103400c2d19808030b0601c55001d91807810009001d241c00d1904884000c08813801540d407580303000c4c2c142d4480c0d0010a00d181c1d41084c4001041031140c09861078160152a025080c80c1410100715142c0b910790b22b800400c51341c0c20101c1c10f2140c544d400003160701c8240742c0780005581045a101c1e5180a095602400780040d5800c440d1a1044480d00905403540b59541e90700c0c0c54035200c01103c0070340100e041034800500305000000c0702c840301100800140e206441c1c0251041c902000642144c605901034200c9030410f011090040c4d5920001500340d0321981c0040b64507288480c0c02c1440c0103415005076416201d8841c2d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 103025197 1250 103023947 103023959
    0x207030206070207090e030304020d050111040f150305010e0a091707061e020307020a06051e0103030e0301110c03091509030a08030f06010f0e040506010c17070308090a020d08070507030804 83
    0xc0d400b4814166602100c00059581c8a500c003280d4294202031071a82003030000c0b0b001441c0c52182c01c10014014030003c1170b8003e41c140440306540c000c3c2c6c00b00c035101c1c800010411030a03422045ca40342c05c021074103080009624040ca07040b020380c001048101007541d00d01d4882c0030007100b6035102100340820a101030700c2c0c04007490590010519840613064804080360110700ba070416008603485002164007034807000540d0380d0b032000904405441884482d44145002000c01e16403401c00b402540295070b21050100540141400c444000040440392441081008001c1d0b2002044920032481030364040600143d031906200d407406240d18665150080702800c100340303d0441c000c0d41c01480180c10a80841c0c0340d8800540b21000001030000114108a08081c05880c1c194031003607105030181040d01940c4841d42e181c42200d10481041d44402001196020a043d030041c0442e03401f0700741000800a0b180182c0004104402d500b03c0102005400180902040740c28441e81c402151320242c5070b511292512 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 103026447 1250 103025197 103025203
    0x2072304050a0e0703031d130212070e0f0f060c060f0103030f11070504020d02091810080601030b1f08010f0c0e01030c0e1003060302120a170c1c090902070302 70
    0x500214400c5080c5030118196041c984103007030320800301c0002002501d01d15074060b544c60181c072001010034480809081a40d80741c00d0340100103101310080c0180c0e91103070722640900c40d00d40948018104110031020341250384410344564503251049505110707680c01000001c00c1c510495540303580c14003641c0e0034004070035400c5049034162072084d104c0328000c034002c09084030041900e54090f440c55004500422207401c01d1b1380103007814420b0700700141c90300c01d01001085c01c03e0b0b040119400c01c0010031041020082e1020070b50805030555401030005545140c4442010300700142c085e5918080507801411030410403ca000020042c0800a100504000c0100c03001800b0803d11640411284050107925620030700c00c040011000d621015000310100090010039800400042e050595880002c00561f172515080300e01d20b84000c000b08104c8a4601c1c0c12404840341c0382034407003143c1040c040d40c528020007003940e0030b45941501114050520715202100d511016070b000680941c400220501030543c08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 103027697 1250 103026447 103026509
    0x12060906032b0207120b060d060605060c0a03090b071112070e0411041d1b13020f04050a0902040503030a12060312030e0618030d021606150918080306040b010207 71
    0x180d001d03101315982e207030441c00d0407010442004110180840010ba494034101d82c0c0200610b0040c81c0c006500ca80341c10108807543d02c40d50720b00d40710343c2c04004071200f0036500035001c1010744070a03142642850040e959900403602500078080c0f0480d02900341c012070b40b10400c081c00041c290108400c445041c10700780051020301c2e40300918022030030100596038891440a410900d01c0f000001841e0442a514501c1c01c1000b00084450340040242d140c0e4000c02c9260004e002049111110b00356290301c0c0c42c082040d042030a900a40645005000c108404d55010058507050485030428607614150000c004008100d250802000c0c00044100c8400e11507040c0e10025403948170108449523038803049ca0309001424a440a510240d00c1003081501c152a290041d0000036104075085900c03140c1c96868a00b0740d400c200c00d049a8070003040081103103d001b406954050b1725180c40a041c1c21402da11004114400144584d0156441c1d00c0c443d503e90348200b00c00402484003150410340002c4c03000c1404125402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 103028947 1250 103027697 103027783
    0x9150406110303150d0c09020d0e010e01050103020a03030c0807060204060f180b1603030b0d05010e070603020f071106090904030302130b040b0a030509100e030a090b1206090603 78
    0x81e03001940004600001103d0041181860391990400f421080100c655401d200440d035480c071045d40000c0c0d0380d0541c0060002e0ba00d400300080703a4442d00710a50b80c2110310180c0c0c00c1c18507a0401c0d004201680b240c0d00f445041c0c3c1d8251520101c1030410741401480e9210320000141a40c0c800100007541541c403000104885169585510030366010701c040b001a80071b1400b40142c03042c020400490300c80b024194044406201e0b040100f110340c40d12002503080854044140d404c0c0c3d441c1c01c10b461040b00c00380800e0000e030056080850502c3c4000a000c03640e40140341c001840c40192001d0895103039150020755041c1d100080007505c061400c1c3c900103000c0d400c114503c0000310a455000b0074802410000e41d02a10701c0c0c0e400701c6081002c1d964003180039003000361059080c0d000f4807452081229950150711024400310000b903940d50721030b500c001d0044450ba07128101c0b02605118064021403410010380d085081103030314240948030200007130709001104c2541003842034255444488543c0e2400300202c00c0309 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 103030197 1250 103028947 103028957
    0x30902040b060c0c06030601031404051516020a030f0306030206030a0920011205040c050a0305010c02070501080121030e180105040c03140403111525020706020c04020f09150406 78
    0x80750140140d41c0030700e405582294100340e2800025041c10005182c0c40481403402140f140000d10203a040d4103029101910341350019404110b000320100c0303865400080d1a02c0000207a4080d80c00252200610709000b0100100341c030003100304030b21076001305c000703507400030106552030800c1f540400003000c0d03000b402c03103107c8040140030310307002c000710071940c0c4820041c0c603010481da0140b06c10300d000780300081013142d1001c0008008241ca1701ca00104002440c40360000080c0c038401170b0070181c5003807070a51001d410010420700501601d19941411240d542c501251a855505145811781c0d0908080082e03940003ca1840f03010729101340781e00d115040303c40648081002d06c0380440101e007907851546080c5501c81c1c580300460f0001e4442e40d403464030f030180b240c140c401c04440900003680901c07090b5004141070804e81032141d4803500e0b2480705107001805000401c030711031804030069100d803074101103035201d0781d400301e008100040c90303400721140580b008003240841e40c501031001c0c1c5181c00c18003955001030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 103031447 1250 103030197 103030211
    0x1b09050916080c0d060506030111220504150303121d01020a080a02160b040c120602030402010e0a03170906070204020d050403090f08030306090703090c140f09010e06010507020303040e0703090204 86
    0xb0089840c124144004d8498201d100540d140c80c0b01070070001e44603d425650755007540021200540140c8811402400c200c500d41d01c41480e42c136132561031030300401d109510b40365102942000440d07450742142d034541050f5107845030500c00d00000700030800b02c1b03648184034082e00d074150b0001980113003807000c010f488405480d16124000c10403400b0302c1d0050118904070520b008040f9094190b855481480342d26041a0551596443c041c44c00d2141411210142c012050100b1507802400030b001d81d107400c1c1d801c2c084203440c40d01c90f00110503816405980c0702c280001c0c1c41d840b640340d01c011102e1244d005081550359411130115030005042c122815400564417180114440408409020440700540c1c01181036403910801c220182002900700014550364040140c009240d100742c0c80010036034641040742044400007849801494200324502c80c00c0f816005009107a4840e0455421038000e10f442d0307031100d001d440400c1c6188200e13080301045480120070492502c1e41900950b00c804d20a940c284481 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 103032697 1250 103031447 103031459
    0x90f0203160509061912060801050f0412172a07080901050307051614010c020f0601232d100206070e06090d0605090c0a121b09050916 59
    0x20301065416401c2440851001078800748644060300c00050004c3c2401d1818a010b02d400014103211590705c03020800303911111481403606e210b01030003000030300d0091289250007030288103000c0005100410b054a048071440e405403085561a5280c900c00d05030300b2a5003041d42d403101256801406000082d810084a00130341c8020100391804030fa03015903424200000e100042d1415000207000c0c1007004000d20801602400c58014168002d000d1844000c900d801d010781c017420b60303000d45507000656100c10540c0c07899081c005000c43c11031390015246100780007080d0301025040051101c560340208a0342403410840c007030a0b00141074085c1002180000c04207007060190065030040c04401603082200002c2d8080d00440200781d40150003000b8a2802c0482000102000d5050034103a0b41560b9039020001254000c001c81d41c50403004031210f20350f1070b18201c07078000392464001000301300c4541c10840602031185d000c00030001d041d240700b0501c00b600d4170082c82c41c0c3d03507900500c00184200300c0100001c0c1c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 103033947 1250 103032697 103032701
    0x207050607170d0c031a240c010209041506031a01050301060513090c020f010b09010302150a050c011416080708011e050402040803030708010b04050d0605060f0301050c04090f 77
    0x4446000d00114200080c03030725108009200480d015402003000c1001d9403900103203114083c50607049440c00122100380440c0f03c0560283c00109601401038000312282044a2480c101d8107101407180443e518003610000350b02a001d000081901b00d81407000d194a046031200c0a4420b40701c055601700310220700341610a0304400030440c8103010078001c000502205106000820420b01074100c02146c4943d2901050304541d4000f04040058108420142c1104021300031500c0c44803049035240c0303855040d6000039807044018000c08054450001e03204050710301a500340e81204001000801c49030042d20142e5215003011a0300310b0f0406100341180c1401400b1342c00c035600803215980c410045a00b0040702c004610400e428064070f104111714005034555076030000388068100d0314040c584a0a2285c406080e03441d043e00501c1c0c540d1800e02091006480d540c0d15a03040c1d50304468041090b449060100301448940e4201c3c40c4c01d035082100700712501c029503000344100e80d0b420713401700000001d420341003007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 103035197 1250 103033947 103033949
    0xf030403020f092d01140d02030c010c230604060e0303040b0402040e0a02120d1e02030a08061c0f14160e1b1602030c010c12080910020c0a020906010207 67
    0x50b22003404281da00349814030302001640819820481c10034401458a4410f418408070021030860f0380501c01440b4840d42d640b8000d0072804c00341c5900c50356094544c00241c55041c0c0d00c080e2410045c48401000a10a030180d40043d00340142c44118401a00b6003802d5454110403501520000c0c14482202e082e003000008591045400901e82070b0355440369404c00010f00f90000c500135181c440da69442025a403480600505000c1c85402004140340e800b001a000400c040001c070301000c10007110280458000c0126030003046d0b203280c03030845a03413502c1c00141400094503032032040c81d40105900c0e04000e100003444400d0ba000b4400e031410005030a0b00d25a0b0b5040000c075100070703e40310b01000c01c409469039003002d810004081a02042c094083d0540384136422004060340c00d007a640350400154202032000311841c010a20302000320900d151102c03242c8858400b1503c00304100d02c400241501f030184201011400c11200641d500d5590b07000a65691240f0242a44150412000f02d080c44d070000407060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 103036447 1250 103035197 103035199
    0x7020a0f050d060c020f031809010602210d020403080412060f02160b090a02060c0601180908120a090203060112020a1d0c0705150103030903140c010e060d090501020706020702030f03040302 83
    0x14010030025503800015080d88484031301076100301075006d6a0341406001810364001c0390304804008014080821100c5081030f030004081d900a0744288c103100d200324114503000742440040c2903590241c000c0d402c0081c485c0c2d0303001a080c5400400c01140c4891405c04892115000701c2d014061401290141000c910603940c064190801c80040c94000901c21240d442d8011407440540b44030585035008035900b540140d041801e40d03042440180001307e680009005a40200c200c1089089940d94912800b441540f20340c204061210700011100500c1d904407803005030b8050207540c241d50b03546144c01e4421080010483c4155000800420700103546005904848031040600790b4079266a414020340d58003604050301d042c020001c0a010441e42d075051903000b584a80d03220b6101c10b1450501410b00100c1c02552105600030000302e540b140c1e400f61000b2482001102c00503514a0b805101200a00120b034000301554000310b80c22061010550203003540c14000c1e402e079040105001409901c0c0d1040d40002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 103037697 1250 103036447 103036459
    0x519080d02070609090f0204091104031202010b010c060902031014060a050d2a09020c031c050f04080c010e07140a05010f08010308090402070221010b030f03030a1a0a080307020a0f05 80
    0x8000b04400380c6c0086280d60382201005192588420840013600ca84215082c3c07100b000180400410800c0381c1039200303608852008001c24405040001c00d1012242d0014103c03076100c46d649000d65500b402684e4030540d4081c2c04010000d00000d02c00e00d140300c2154a1840307080c071081c000a1030b060158101030b0140d4403200628884220402c040c408a81000c5c512803455014000841c0310740d1740e88010106017400000641c1c0710100307000d5000080d20803441d0030f100182400184070142080b040041d0304a584003010540f207192104600f4014491000580e0301c0340310b41d00c1d002941c0500451110b800000a40e80540c4064852005487c1800d505d00b04c9800581c5517001040410200800351034982001030016141c40e0103074000038640340c1100318400326607040511100101c0400d200b82c081c2c003039050b805411540c200066080d203d0000504c030303590150711005e200840003000c1185003100c040042c10700406980750100f01c2d40c4d82d0040c603412401403580c2203011031b10040c001a61000c9450092807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 103038947 1250 103037697 103037699
    0x10803090112050702010e03040b12060411070f0501111605060709180203090c040e03090108060a0f0608092d07060503010b0f0a0e1c06050c0301050603040f0c0519080d02070609 78
    0x2e0100501009000c481155694105550141c2040c0010300080006118607178032810700f080000302c04100580101d200e980380840e246135005884054440c4140c018205041d09200c40c20518050721034072200c4050840300084c2203000d01c1d120002c800d41240240200e03111f0366941c0f8020791314034600340900030084400d01c5c044010303103082e50011607008030428140c2d00c1c0b00da00500810305070f070005010311006400209080b040e40d41e004010f1544076030101c8078a50404c2c40c5c460082c1032100140a1101003020900004440c03010401030100090f08101c88445500e0007601c0c06810740c4810000d0810764007403a0400503c480c480c405581c16904101d40f0349280454134548480c1035808001c21200b80b141c0b6000c054800d5454442080300d030000681e032a0b1000c1c2070352410504030340c001408100026000e20040c005602d80c94140da92050f03014441c0340800002c2e007081d1030044a02d600c0642c1c421454240c420044220581e050300707e0320040c04480000c6102c2805a890b0360490007900c0014902c404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 103040197 1250 103038947 103038977
    0x80c03061605091f030c030603110d0f08031003170405090c070213111306020111030403110f0319080109050405100518010213050f011404090b040e06040302010b04050108030901 78
    0x2007110030320401c9003400c925000522003c0303001c0c4480c0c0c0749000c2040d15030400f82081260140500c40800010b80340811410342156030303002903030840d000618054041c0701690780030016130b655a280c050707400030103030ad03281d05d0b10094070a1180b04500084aa10342c0129060070008841400d403004d1310801010131007d40c0c0c0d070700c401c0b0070240c2080005aa0081010001a000c002c0501c194240f9022200115a031290940307603805505205071300010031a898203200d80d840d03401d620203030707600103a2524002e17144100c601c0946240c41100381c807005d420f000c000340450444040c40d1880f0a05406c5440c0d500f000c0ea1780d140720703400715582114007034504d800201d0300079540301c09540083d5000140601034810014845903440c02c80e0000e0314058004003000100f44114680415003550103d4246455950883d00d84166252801544100300320980c41c2c4500300901e41d102d801450303000c100402140d455181506000340681540d450003802a4030741b00010510710001700450b01e0410040c1c4490b21121f10100f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 103041447 1250 103040197 103040221
    0x320060403030b0d0204230117060115090b030916170316080c011d06010e070c17040e040b0f010605040501050703200703081b07030c0513200a0306080c0306 69
    0x30003400c4e4007042032042c240040c4c3c0d0f24810240d0480284480449030b80c0415045c4c2950103040e080401c90003010109441c12040006080e4152200c1201e912014020b00c9020790310b481040c1c2125603115400b1003000b8070114000f454500440c80f0101e21440240c2da02c2500408100710692a841500100141d100003024181c2003114248260a01490001c0c04260039007183d12400203007038500c0003e0300840000104000c2c50b80507200031584107265003040d5101400c44581c03100300600300542d00104e81c8842c48a40c007550014242c41800e20040d00c0c00b4a0604145042101c502071900103c20010071400d01c544241d809070b80060312003924082c0c1d030751015030303600e802d502540041c09119000041c01c03002c24403484000714480d40070a070319203480201c400f054160090b0105100d038010103041012980800030001100c03419240900e00075500300034507010340400b80c03491246d22000514034441d50107120040440b44400c0e61704010054440001540358101001a158541c0c000004581c41c8010301c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 103042697 1250 103041447 103041461
    0x30d0b01051207032406020a021305250c0606060801080d030603170c1c030207050d0e0d06050702030d050403090602010f050613020c032503170405070b0c031c0504032006040303 78
    0x940310356862260030780800c240c0c030401341d0046c0d0016000340112008506103240d24aa1000c00c040c2c00303100a1514502e000b10040c5048200b0414001d880c001408441c000c100c02c495440e0441c0341407043c50740300c450141000b00c1c213101e1141c0034842c8414990b822486842050b05aa078458088241e0720113101b628a020b40110501a07400d00900300c19a42010503010a003685242c103490160b141d81d41340c20701500b003070729901000051044d04c00c8007a802c1c2d901c42c040b81d88600d034031a10016107503c501104a10754001c04400070051890b110601041c1500003c448040320503e50080c01070614041641c0c05640041c0e61b1a0741040c902c5450601528240c0c01404680c4916000c0300d04000380d034405480c075183c804050f405121440e00801e828564040031500b1094900620000c0034102075a840750b07510745a2151200210002c40c04214090003481210111608089a1105002100035940003840c058508401284016094480d40c0c1e0344440103194800c00c68020380a15620b50b1010b802402c0c807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 103043947 1250 103042697 103042721
    0xc0b07051203070e190f050607050d031109041e060602011e180507120c060806030d120605120304180e0307030804230d030605010201021303030c050a0203030309030d0b0105120703 79
    0x40340455000c60f03290000e91850800070b40398174042071440c6c84024696018140c1290b40107600802408012a00004095901400701d103800550701000e40f1580d9054002c407060b59a0050410034200402203000139440c6204048d02e5040001550381e00043e400c0701d017000c00d8407a9010384002998680d1090340d0010200e205440300f079191160050b0380f00c40c14804142c200601c0c01c00504425828812000808030140038a800c017a40c45040450000b903643d1248600b00042011080e100002e5110542020b070050501618001140c0d1002000c0c5440360082e00496004401c0c4140340d140044440c05078020700b0b0b603501d020350710f03051050320b0803101e000307000f40140c0b0001c030304550000c0f403d6802403080f40c07000c64850192a8000b450880242621003d910035811a80107000d4900c0030103c0411030340450f0384c5400d24071320040e014a010703801d1603102e940180d4180008010007141041c080000d2805106807041001340c400305800541d9140950b0580078581e6001c4000200f40d58000d50001c162102c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 103045197 1250 103043947 103043957
    0x140a02090c0a0c1407092906040605220302150d0e01090c031203061e080f0601030201080123060708090a0b03010b030114120f03040602070e04021008060d0c030303090c0b0705120307 80
    0x45ca46c0d510f0b0064409401c440414507603110000c10480000164204103034100302d454500e0203141010043c00b0340900031101d0160301100c0c245030710319140c080d24800219406000c0d0001c20801014402c4541c0100d0240c025490a01c020b01c60003039018401c01e0746156000252800380ea0030b503240c03032120703640814881c800d240e0b8480b4003240642812404070030001d243c0c040c04007480c0c202002d082c14036040c001d104006071310103c010700040c1c0e04a560541501c072500440a8540c4850000090511390890b50f030307030443c00c0069250f042c40403601c02400c41000036181050721643d502550243e03440240725074445540e0900040c8607488503110200b2025030010040c690ba8150302c100300381001e00e111400c420ba5807001070700304052074040c088000180005840443c49161a80120f44180c040012038000c0ac40703c0c00000d1035036070700c001a03070030b51a030001a0080c250f030322407902030700800e10b4140035210349915000c00500c690039582198581540003000d401110080010305d0381e0f541014140c001409 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 103046447 1250 103045197 103045199
    0x907090e0a0218071409010311070b060414040302100b040905061003051b010e040506041e060305061501021b03030c1f0f0605011d010c140a02090c0a0c1407 69
    0x1014050450403800a402401c0c2140e82803041140c02c82d20308803441c108942c3c0404000110360440d401460407402001810798035100072004a00400031003c0016081d540465002e05100c424001548200300030b9404021380000240203403000d241c1202c0090040e4411220303800c414186400100141d48054000300d0318503c95034603642008012642c130b806580c0301c44010802d0010800c01c5d04030b0b01c0130340c1e141d48580940400000305000340565809002d02d85800105000341c847d6030081e03000008201c202a01180040d080c2e10280105100076a40c41c403d070404224120750303810301340c0c040040c1600107020f21003201c048003451000d2003648a40c5408203011070204918103018a9211070004008801761143c1002c2d520120b42c194055211a0303840c001081c0101d90300101c451465004014010883c0d16034140102d52405001200911505008459083d40c0b900002d0440700e071442210b003149299103040405820f801040030502c002030b0f20142c1200498480c9240004466011064800341 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 103047697 1250 103046447 103046459
    0x7050c09040305030403090609060903061a19140312091c02030f0c03070e0903030414030702061314010809060109020a0311030711070b0c070510020a06110301060909060315050907 79
    0x40040750700740c011400c0042003004040d48692a41b01a008a041c4130104030305003840140024002c6c003000700513542d0785002c0d0004c66140106507040810081c160500c1c1c0100c070000c004101c00ca0310400c0da03906d91039101c030710b0300703140115141c03000551400d4007908040f01d850030000c8000c00d81d082c01441320480d040c1c46026031130a11800480705800402803004038135080602d49015000d40c00008008510801d0204210b8048110f03a0803a070403620209161031580c0000e411845800002036100b40002283c1c209030a506840b54200e17a8504c1d6007081d440814001501c5240044806078036030b400180060149a0166025011040f25894005020118800000066401920341002281c80103420142d819020006030010b820403944590505c600441c3c4541d90301410300503a4072504d040d42c1c0004a0500c00c010250130aa040b45c010301003443c1c6000840c066034002e014860000745121408a203051550151104481e40701d90402152060540c2200090070042c01d00d03030300390050072400101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 103048947 1250 103047697 103047709
    0x160c060f0515011e0507031106070807030b01050a0f110a0b0f01090e0d08011a0f03040b0f1b0f0304020103020f04030309080d03090201020a0b060a0b040902090a060c0506010b07050c 80
    0xc40301038508002020b05020340c0d00d07850403420410850421507084050001624118a20708101c3c24a090490716001d00c1e20b030a84003500b4440c4152034621034441000000703503210041d140070b400e070f9840c05c1000c580c024004548a11840c5c842c0c001103440641809003541c400c103002d80310b052107202a510315004650710b0180307d000588203084080ca1180040c0080710280c4240181d00207840010701d6241000c0d140502081c005204d0203541050050110603c84031210485802041500110b6500d1526240070100b480c000d5480c0b80c20104040e0000700d800c0c650040401031181c080c13031100c1c205141d40c412000355600013027040781056020301c14600e142c1e0503100075201540c42034031043c100c075081101540c600f003141c50204c4100350400c3e03804400350341c001c1803120121b070300440303103101e15035822001c50361402440c0c2c449603140000150000303a8013015030140110800845560a030303551346070003c503920b00d1800c0300a8020f0300719800411921208400500c3c4440c4202c094400041c0b4071000102 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 103050197 1250 103048947 103048961
    0xa0302010207110316090c0504030f12030c05030132100c03020c0105030408040302040903020a12030c0207080609031b070b0a0302040e0f0f010b070302010e06010f0303120212160c06 80
    0x1503034002c02c00000300121050f030080001ca0503001000341c01501c00009603112190b1085220042e656801c52018034031501c202c401840e005000f0344504032940c9001c1d100b00140b030611030002480c1c40503500b002c0d07100b20210703412581c91511801c09400014031000407480341d036040468540b4210703440744c02a22882040c881640c100d40304c2e0042d0340f0070313814041d041c03a255900f80ca04020007001088000340c0300c0025030341035035015180007a043c00c442c079050703240400c10700f40030f0314083d60302000410555064100429410381d5900b40c4600035070341c107641c1e640c0304d00666541c030260700240030403041d01c80d107044039002141c0c110040360840e603038491044001b0390000c0060381c0020f030001014807618541100d0503070081101c141c03980c0c5520300503058460842c07040c06038040d44200001e0308070615100b50040703c001d8410006548203035a5403070380c4070f0380180075200840c045401440c4181c00c540c880c0c402d96040424070710041e06607580b0800180f042c48a141980b0062203001c01850300410b03128480d080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 103051447 1250 103050197 103050203
    0x10912050601080f010902061c0906050a0b1008091c050d0603200105071505070905030f0c010201050609091506060c01020d06030615050f04090807122f1903030e0a 72
    0x7100d541010800c0d824813a01003050b100581c14840300d07400603100e550842c9d0005c0e500d0309a000351001c9002001e401b4220340000504030b0390400c0d040c400c006a041e440348461200c00c5030340c211303200344030082640c0c0e400048805001c1504041c5d0b0041ca4206100800e02c2c0f40c45081c60081c1c90b1041c3c04c0340c3d040485942d0f810646004081003000040300b1169403c1e004460300908085040018542d501c0d10301c022400b000c1c2c052151100f021510f440d0007880004081c28005059642506501e800350781d42d0518221200d00540c00c04020030b0f850f0400e4160305010b400c41d40040c00e03c40200080401b61a0005001c0350b4010000b00603202c030001082c409066007441c1d1007000303d0498518101401a907101c508140c54405050f001009030740e599132400e041c10301054501040c441502d003040d014600810030301401700c02080c0c400d04c00c82c40d4844001c0790b1b01c2d239000140045294038bc104032502c4420a100c0c0c04100e5210b4610320f5034113140b40d00c10328401c03442480e000c144a00003003083c41c10401340032411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 103052697 1250 103051447 103051453
    0x1e03031403310512090d030e0307120302010b041401080d052203031709030c100b060d0203010b03040308010f03020609040e1e0c09090c101d1806031b010f030b01091205 74
    0x4800700001800700c0701d2070040303a4a2550805c4100c078001002a101c00c0401410701101c00000d040c6600c051000200030510402c0c1452034809500300039020b0a04058120f1040d858816140c5500f6908800903042c1c03a20320f00108020010132000350b42d00c0c1e10181d80000f906000102500c0b0000482805501a41c0b0a56425600c4051209001802a806406804203030001c0c0a0483e001c80b0019400008216058002c10851600000b28007a0320407100101d04c0a8000000490601c450400540c0a50710995030440c03141e9a8890050054480e400000c1d40448100035072151850560402d4103080340c26810390795041c6010060100c24021911100c40a0b040452075144034542011100d5003c0880c8020b0725200f0618030005400348000700d25002800b0725260194800c0b0380410081100101c0608022410b00f003002c105402c40b5000c844443c400d116012407810001c00b241c0600400ba24180c40303c0038401e1000c0d1013900075201e03520443d81080340c5d003d0002100c0700c10088001c0c880d4021009 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 103053947 1250 103052697 103052791
    0x613050604090603150e0d0c02060405030a050d08100509070509060d0c02070602150f16020a120306090b0f010906030e0a080403110f010c030c2301020705071e03031403 74
    0x5c4800309506400c0e40c052014500034040144420200d04c1d00300aa50398645001e00a2083c4001011800380b500103d40500c20341590300100140001d4412420041d5110441507548078a070707000c0603901c82c0c01126001071030680800d10b040d001d0400742c40a164024101c82c140403280c0c16644c01c030303140180901c0c01603000300380c108800d6405001d14074109804a20840c6145002030310f81951500240c01c4030021040d00002c454454400e00456002a50080140e01840340d260b1006024054600079100028640000a48240303070482c000c1c5562101070b1916141d6a00c0c2c030000b81c00600310202c0390708090007101c210f0400a4007000040025500c030300300710102d107015403052200058007a410305041c01024400d000c0841c2e00440610540307070344001c500351300900101040d0711f8100524400405507001041200821001294034015103500750a030005028546800444002c4148005004207030748102044890941400650340040030741c405820070301c80c1640008610000411401c11004040c5c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 103055197 1250 103053947 103053953
    0xd0207051609060509060d030e0d0b07090617070807020c0a06080411060903190317010e06030d03060515070c0e040305040f06052a07030209190b030102040303020a020613050604090603 81
    0x100ca01c01a040c440c504010107400d00012a491340405401e5500c03c2e8443c000ba601018803074030340920669000f400100802006150802c8820740981d07080b0003007030b06a076001ca809403107000640701c090044c0420700c8441c1c548038015a91128080c0c142c40460240142100b207030703100d61a84000424190303403405064039081c184007841e0f09541c4d2000740305a20400074005107680000d00001d04503400c0d404800500d1241c5000d41d480986c04000c01128600140006614951034007042d01c1800d054041ea03000c0e0124200841c01c49095000d0386a00400400c01d12040030301d0740c005071000a20981710648541d485025059801c80100da0440001d1030000d004e104034070821504000800481c01d050b808c0400000111010200034a424040c2aa896180c5200c1c95010043c610055030082c142c0c10325428032854180700c0d030340307008100052242001e101940701d080c14404c450850b074040d4041e1004007043e03401c2003110390203400c0c2d02e004c0300e115510200780c2c1d40e00d1b4030041c40208855040010f405181d45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 103056447 1250 103055197 103055233
    0x50408061e0601050a11070b0301030302061e070c06060b0c330103060e100e0f0c1215100e15040b030c0109030b070c1a040b0105030601080703170d020705 68
    0x2007040700760688100d03011030901c0c0141c22140e042002403c0c000d4403000800d03000c489225420103054081d104aa00025046071480d0056042c4e0f40a03500b40c0c1d84954600c00c085080440c510500b4103045854400136140c144183c2548500c18868540803070b0066890f840550a500042da80ca81c00341c1140d03407001d03014150406151081d2916620741030118588002c1e10300c41540c14440500429111030320341c0099842030200b0298200c48000800215503060301165540191602d1040a0b2050803607100301c524002061000e013002010040000c41c580b205181d401d40c401a00b0686143c05a0401180c80e001040600c0d00c039120020640040c0c25101c3c00f040161040440000d0003600001c9801081d6603220700c054003542d8211030200215200c3c0c0d04216176105a00002402d5101d5404954040174100d5a00e02e020b240507041c407000c1642c80d003003050b88603c028420f6102030b0f4000203003000040c50504501b04651010701c401c07428480443d0400381644d2001c04101c850390002d46d000900c5c0301c0c202d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 103057553 1106 103056447 103056451
    0x70915030602130f090e070306090204090f050309031614011808010c0c0605010b040b03040b040f0c06030f0f02130509040213060f030501060501020604230c1005040806 74
    0x201070b0b50103010b0f99009500e0001c56900002072558518010703c841607624002502d00300d0300e1555070100408181008030380080c6c0310845a404110044402e0503002d00640185035901210303c1098200700c0c03454281d100540d0144014001c040c0e04005101041c1001e007424002c043c0d0342841144400940c0c0d0045400e503081007039064005612500608200740701d00030030b01690f41c844002c04294000c0c0c3c068958030180910004000c14980403641da046030080d00300083c203012580302d40702c41c00036580010f00402d03122121420380ca4614441d803140b248280b40d0442c1481580d08101a0b0301d85148546441003281c00301207025035031990080c0c02807180203002044941d55030309080115556a1005550952030844002959400071600c10300c6258450107000f41c414491050018a0308005030211041c8143c00415115884600400200c24003d4032a01c0e159450210250715250700 = true := by decide +kernel

theorem cover : BRFrame.Cov 102877697 103057553 := by
  have h0 := BRFrame.cov_init 102877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 102877697 ≤ n) (h2 : n < 103057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
