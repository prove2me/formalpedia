-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0546
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:22:25.099988+00:00
-- url     : https://prove2.me/submissions/44fac9f2-2ac8-4597-9b4a-0bb7ab182d41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 98021582 ≤ n < 98201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 98022832 1250 98021582 98021591
    0x6070606050612180c150c03070605100303120203070c0204050402030c1f09060207031101053103060b04020307140c10020309030a090f030302150c16031e03060b030415 74
    0x4000107040c541082003c00c00307807480320040105080d40d400154040020200c050128a04103002141340c400d9243c85240d01c3c0000040e1141000c04100200c810003038104c6010000c40c01c01d009010401d600d00d210903000600d00245413200306055208a90088000e5207900c44818143d40c20301c005400f000303009a80c1401003800c85116920307a1800820020314000d0a0340d012407502c040504100000e8020703904640c00144203000241001c0c21610303200100b4280035803115402c45881d0060f101e00103001001a0310040d0303042010020b000350500f41d0740700760401e101a51000041c0300480c00101d80ac80d001604003a403600b44a1407a500400e50811008140ca103c2d014402c0c1c000e0690740b080d03914031000e9100041e00f000d40b0f603001c909200a0098413406484891868900964801c0310fa035004158800d85d0b070100f01c071110084116200c4501c1d0100d814420a85418007070404000c105052682e00340c080304402c0f20510034440d64050301d100f0490346041d0380711a116806481000e48604000a0740c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 98024082 1250 98022832 98022839
    0x30f030f07030f0e070f08030c060406020903010902060c030a2d0807051b1c0201110a0f0e0d1b0905060607030804080c060108060108100c080a090c03060f0f0b090c070206070606 78
    0x38000e138000542c4150040c06030302e1508600a03c2c1d10007a078000e07815a0001c0c800c104c2c85030f0303010a034141c100f80c00100150301d0351034000019004200940c40254000000101c01d00c2024011001e88040c90168444100254482801d40c0f80001c084881158030201200f034103600d1809a950b0603046040c070b01d0500c1c03e2041030340b0b40611016a2a0100b070441e8048428240c07580c480c1c4034010805803041c4000c0c007004071041c140e04070b50702400400b00d007402404000c0c250811302c60703248008040c03c0104542510051400c2081c103803540742940d075222045a600116003081d880c05824001c0d6000740816141078413644003110054006003040716407103420007054078084410440300b400791030000003514081d45054070480c500860810b44030740e03240c2008820701440b50014a01d550003e0000e101281c41d40c040d02e8000a8005140c0000300450b1429a0b005041075203a48203c3d00c240b10707420704009444010041003030104017140d003170400403400c010b10300050a0542c0600200c51203158007184540e10b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 98025332 1250 98024082 98024111
    0x3020d0f02160b0d1509060e01080c06120705090a090501180e060c0a1e05030105030d02010c1b0f0606170f070305070902090d0501020d0f180203060106050310050a1202040b0102030f030f0703 84
    0xa00343d00c06d6403000c3e00d806080c04088200d050301c5004060000007818208410030100e122070103080fa44130f130813200e00f100044004d80134108507100f04070300070048202c9540750300744a00103110a000e6102d040009014103200d0200380e00c02c100003420200010141561548080b40d802c2d404060000200b2402c2e1020700f034460310440c40c1d54a400416100e83c1c0e101c0d81003009142c90023000c0d4804a086a0412a501403125000318010305603004882e9181ea40f12903030b0904442001d480240107103d503140290018130f40034056000e4250800c0c450980311012149800c641ea21400ca00000d407003500080340070004812140c0c0106035013038015052110045160311503a0072600406411184140c442049055804003885240700180d444038200d400344505030046542c5910500901041c04400000f03e4400c0031000c4100d0010302c0c000784000a09038070303141081c07219919100704900841c141400b4601c10340c004029a1b183c9440c8864490a550f80c00251a20070711004e86003805243d81d8405220038030b007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 98026582 1250 98025332 98025371
    0x40c0b0a11100b010e060304080a0806040209060d090308010b0a080105040e010b0306070201020301060905062511040e0a0213050106050f0a181403120a02120c07050d03020d0f02160b0d 81
    0x60900d82c0000d08580c0b004005032145c54070780c074001c1c0700301d02c00c0003000006400b00080e220f03400d0305c0e0325110707039a0b540f0720022900038887c0004c12603010030045603000c1100c1440d0454984c0070302c6590341c5c000f60703680c46859500c107015842c5840085428103005000d18100703603000032040250040003054103d04100881c0c04c00f5000c2d10400c0050f50000014020356801c29800d1005010946015140800d00d991004144a10074100e01c1660402c00030a001d111804c0382d4820540e074003c0c402c11042c0800500075070744108142e01203001d580c175001382043c2c00b0218410306040300c0a40e00c1f501d01d4100c2c0078900540540c80b02d500c2c007061117409201080d84064250000d1b0180455210f035124500b540c10801d8505241f1801000321107904100c03070344070742e075000c0340400c142c080c0a45c8641e12030840007042da04000d895001075800c0701007450301009059000a4011810200d500d0b010b049034041a030890300c6003029400a00c500710205000c003e880d440100500200c428160001240c400c42103100c4c17801e6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 98027832 1250 98026582 98026603
    0x121805010c0813080f0705010c0807021c060204080a060e010504050703150e030a03021b06060604050d0f080a0503061009030f021e040e0c010f05160f03050c030a17060603040c0b0a11 80
    0x20f030300c005d42c086444082080301c10f02a207000d0030080d0b041c09041da00c1d04150b2142807402402a41c2040280c1c8080a00d40e84904079981c0c003074000d40d240c5444840e01076031203011144c160740b21030034076040148042c818070403140160f400c44c02904c0c016065484104400c2079040c142130141d42e940d02910001c0b4814005000d40207525a809661645040d05120700a5064032080200d50011402d0140340d64920f01100c00301c44c1c080d2000c110064260600302d020510050018041c0040010140e40c65588280210b10544040f40c0000b08000c85160459004005010040200020340b41074400b42c0f07010220160360f070070316a0080040001e9040407800340c031035054102c802641305007a240500d60b04109101e6820f0769620b040c500b808418500a0b800c407041c094054140003a0607504001d140c426001c03a440342a0003001c82e5070ba000da500006101340c440340c040480441003107001c00c00b02c7c900a4120385c041e0303400c4068405000c0c02e00203684401c0d804080f1403c203000d9885004000070303200b8464078814 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 98029082 1250 98027832 98027849
    0xa0b010303020601060e10090501030e120d0605012d03020d0603050a0b090d0e030a0609020102011404080415030207050c1009050d0305030f06010201200313020d0f121805010c0813 79
    0x4c0d458000090620b52402c0c90140c41380d103520a10404081e8440c44080481e01d0900c1c011030003440000d8136608200a49208440c400400944100c0143c4d40d5004003003101d800f0380c0c40340c00c0160105100008806240e20700401488400c0c425a6030038400c1e00549601403080f40d001034000d0b074903501c00d45420002031088030fa041c1e100b81009030b64101407014140d1581c075424805032905034500003e44944015000510456440d008003044da4402d41c0700300c100b80c1148400b45401c1c142400c01a03129040b52180c0400c03809151000c18902d03101c0e00941d1012940308000b41482c2c07911000700241c14291400d038408000a8180004581c5e035941e06e0920014041d4903000d540e400c0c4215400a4140024000e0303040d07a0400c259156007409022a0441540c403001c042500c03601c408040082101c2c0a060295018a8000740c2c034060080c1020001852482007040700b10380b41d80c4400544902c000440c0d913691900700c8240811455002e85c2d4100340d558441c80a00e40340201030004014001c0c2607421440c030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 98030332 1250 98029082 98029093
    0xb070b040605090c0d08130905010f0810061203080a0b0402030c2101060e010c14030a05040602060604050c04050f04020403020607210203040320030a060903050904140f01090e0a0b01030302 83
    0xd0007a5803040680102681c409821044403070004100340100e0301c10f004058480c002000c0340d08210325000003002e061004014003095a46004091002070903004581d0b003030140000e59518185035120b01c0d4121101984010713090380726520103444c4424010108080103440304040407480d52584001c51203003d500590540341c803c0c0f80840c0c03c8401c014004002e0711406100144142604015042c00c05042460328403d07000ca1445d104800d1001260b2543e81840301052809030507402c5000380c0280c4103550300f105e1166446030108016036206444c0c0c01e0983c0e108100600c024209030504034160f46000e0405490540d50743d021030748583c0b055030261000a0000340303108004291a5a0302c10a840c1803004500b01400c54546114408000c00b408100200c5010302c030b034041e01c080c0541c404a81d00114101310100140c10301a02542c01121054401e61a00204070401e5900010060060740750071080c0c1d032a40e0030241c09000a00880c3d41c44d80b802c4c8034032500d440000b201e4008142c040c42c440d902405 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 98031582 1250 98030332 98030341
    0x4020621100e090613030528030e011416022109040608150a020a0915030905010b040608031b15130b010b070f0201030b121b031b03060408070305040b070b 68
    0x4081c07980d40d0000448000d2034401e001400000242e00d079009844200380288500c1140b030151290b20914020102031182d210b40d240000503258100800c442c10b41e01d09004040040070705908981d820b19480f0415903444020074000280300319040c0000085004070f40c107450a03000d0000502015846105036080001080841801c06006143c0100b0342c010060082014030114102d0038040240307103180c81540803408480039803050507104020700c20b01c21070b030b401608030000080c0541983e4800742c0780d82d030070541c500344142802c1c800c4404840010010f035013417611701c02d40504040c041c80043c10304c0344203da2854031503040b8a101c2e40e000340d12030301c505042d074603040c9840214410143e22002c40c00030140b1505000ca0000d40802c0b08259091030000f60000e043c0e0000350072881c102155506911408254016504020000600c181403c03412681704200d00384280213134140407540b040c0c05810603804200000c09660140ca0100e03c6420f106080940702c40001801360407610080e5500c040010038803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 98032832 1250 98031582 98031601
    0x90819050d020d020303011e0306020a02010902010305100f0603020309010e01180308070c02010905040b04091709090f06150a090306020d02031e0f01061d271003050c0904020621 78
    0x206a28241d80050000100700740b00c081e4507400140305240c402c039070000c82c80b10034440750f502000c05180d21207011034071903462003030090080402400c12070210745064040341d8054020490309007100d041e414002ca50500309034044020307400207071220301c2c01e649a00d07840c420380301e0078011403181c551400345107400c6a02d50702300141542000342c031007414030001c0103a00c80581d9220b070492050760130a903408174880005c4000704004006038a006080102140d0302071000c5161040100902d032001c40d5121903a48135a0100c0061240a0b00c54941c04285068600010600c0f0005010813002c142006d131101c0342d4988440060380c0c0040182c21307445500004100c5035029190280d80c4081d02e40140603854a81010011520750044c0120801e010400d00b414080b5080d404130002038100142c0411003408112010903400042c540b61090424003d2000540d0285141007140480c0e40100081107440d00d104c0034400525070191043c0d07001402007090f85120300d20402411011a55590300b02168902050328 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 98034082 1250 98032832 98032843
    0xa050a0309170304170c030d03150902120403030b01020a1e0c0602010203070e04050a02090a0b09010318030c060504020d1a07080a110f160507080601140d120f09081905 74
    0x80e0741040034020155082000000903502520f0039009030105c0c00d9810307241d062074000039000c440c2e45449815809681d1a5164101040c20f00e08030b030020000f0381d02d070031060069000380303500d07841010808000200802c0c03003500a10f0382450180103444145d401512011000c00c00c03410030060428094440c1c40802801880d980c00820f5244002c60031814201002060041c4a50440d8495a06c600204854140c65811203814520060110240d1a51001d0349105900800307081c90210b850a1030700d50302c01140c0d05000340c020b80c1c15074400b43e00c1c02282c1d540034000c10000d4400d0760081c0d00c0728107540c0061921318910b0081024864142d03c980781c4a0002000504000c2c24203a1180c108140b00342948101010340d240500301b9049182c403020b24092185000014500c013030440d10581a00003030510011480e01d041c0d40100c0020280c0c40d0a074406c0c0a8030306601280205407044549900c03040034070402510b5111151031401d0030090b56151070903403800d801f0b24030441060b0402e840c4c51003040405c004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 98035332 1250 98034082 98034089
    0x10603050915040303060b04060e030708150c0c031b0616021c1101181a0f100b16060f1a1806090c04030b0f01141503070507050c030a050a0309 63
    0x4003800145030500006403922a40c2c000302074410038507030204007054000d0304014054422903d4a40d1200c0c1c2d5040300600441d03d20442e03070b0103401501004200b01c50003240c00202d010094102c103005840c1c1040740c505517409000c20706a01e010520108042c84101c3d170800369032048240007001c00d802d01310031009485484600c0350066501c118152042e507031007000d503005000d00c0c0303091150110035002c14050152550085100c10710b0148100328080013400000341c0d108200d4030750802c0c010342d141c444500c03854400b070b43c80d24000508074004000b00640c078401400c0c2071001508410207203800b0f65440c0c0944a030300c4c0411311480d8443c50341c1509208074901508401100f00e6101b40c060402e201c13032504020000d0301c058010220300c0000b0780c50402c18403c4600130b40e030150000314039103410301b000f0000701030070301601110400c00101c050b04c503e004108810340e566416410f03441c0d600d50074815274842d400418211500d0003022444041c07660b00b030002d4914107025601800307540400d85002013030242c041c0c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 98036582 1250 98035332 98035337
    0x60a14071e050d08091015030b1806070518040e030d060b180103151e08030301060306140d020310020d09060216060b090f2a03151302040b03060d170408150106 70
    0x8001720b0a8000502c0c00c918100da40e0300040400d9040340800781c112144d0405080b48640704180048440340c4a10300c501c5013018826902e05459001080340e5502c00c022450042040180c10f000315443c01b03502201e110546c40c02124a41501c0991200c00e80720540d00980c600075000ca040020044003801c11030b400c1a0034682000503900c4000f0266946581d4000d40e071001c1000c42000035011480c2214102810b10702c07007200e03169030391404018050295801096580701102c1e207804024202140e2004500c1d80c010050903948009080d010000d4104400320722016444d1140c0401041c5588002c0551032580700c1041ca801080e41030903401c0e00c2e1170300c001c4d07130107040c0d41c40130460306500ba5000960080e0007021041d202c5a0140c840714000c442d02e00040510590000c00e01501c5035901c3e44102074004140c074114504450307020380c90301301e0183e0f204441c440e54041000820321700c2d000c015510780030b09c1010002c0d1068503e52000a41c2e0700950061080c0350b22000000c803000020880e21401030403d407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 98037832 1250 98036582 98036597
    0x30207140d02130507090305031306140918060f0a062303040506011202030a060204060c0309081c110f0114010e10140d032d030f0b060a14071e050d 65
    0xb0b40c04200d03c1c4030030301c4a242030075030f03564042284640704130301d000e00854004049a48a00715003045540100c114424407000c610707c41040a2040072210a032002014020945400c1040c5120002c0712034500911072684801c038401074602c1b0b940e444c0d01150213003020703941d008940d060710301070690b40d21052200955400c0083c400c10000850025926064031020364503400e0000c520720110f0314018041d0001000e1900105010030440ea01001d0103103200d002e5178442010a0b5110801d60b281c01c2c2c500140c440480103c0070700002c6c10300131050300c2c0074510362008442442c0f8003400302e2401c5a002030408200355846400400c080c0c1162891f05801180d9107140b55030719450451000000280815503c4c01403038042c040350103143c055044207144148541e4100c20b40d02801c0c40701c1d581d22401c006000003081c0760121b101803d41c070521501050100190042e460840182410354556034003e0141c0301d500301c104102000102d01c00003500d61300944007011040c417000e5192050400781040c81080402c000e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 98039082 1250 98037832 98037859
    0x8030a090807050319060f0f0b0f0904050c0f1203040b03090f0c0604090f1803020f010e030702030607051303051204060e0607050a06020f0c03030f0403030b0315190e060403020714 79
    0x10034600500045c10701008010f548030b14281010f00065584130140a10701900d1070b02400d21904800c0e0a440102c99040b046080da204028070401c0956024209a104103600c00141c18044800c4000741d00040942e8000c0d9200c1c1c145902e035603c160803d000c4c50310080203008110b242001140f42c0d042059001d0981d50005201080890240c4d1003408041900c50004040c00d00b0b49512001e0202c0304003503c01c042c45124100030790346000d4680c05075400d600e440c4020007070b03480c084107507031080c0da004018242d182c41c0d8032030407609a001035a00d14410302c5030880001c001001008402900040e14078016241d0b850100098044801011028010321040001100164003c100540100c2d44800010385914200d44048100d0081804075411444000207200441402105a61140e4480d64040c030000600c04281500c0d9500700541441c000101c0c0e0100e600f4010b40e00300486595508040050300c020111100d500c0c150701603c0c01d5016070402e00703052210043c108c900380301711030081d1880800c180c035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 98040332 1250 98039082 98039089
    0x80403050c06121504020705010f050603070f1206090809190e0622050901021608070b0109060b1209100606050703080703060f061404030515010f0e01031e02040b030708030a09080705 80
    0x2c004044c00d080c2d04504481c0800303503540f50305568681ea0044000c2000320180400000145400c0d603841303203c0c0c4035190002074071564243d13401c8107669503130102e01d030108220742e1010054445280200c0b444081444602e103140c480100034600c8680408450b240d10745001141c81e038941c406000076025070950303400441060032070410310590908003e4001003603074514010f2402400303200b80449440140360680403d2142103000303803400707c4c002e42c0c040340b042c1d9840c0104021501a4403908000322014046c00039000c4901d0743c480e0b482002070055400e00e07050010031100f204c03002d41007407012810200307070f10091590040285a10441900b410410346081420b90100004584a42420000d0302510364081d07050303400545004503402011111340004040c1040b0f4082000d01400d640f014846500184081002c0c5090f0b04981d08641034900070106121807441c10b00003401c042c0d1308292604480c03055a1001c0240400070401c1001964481d1070914004000c0401079015200da81c2c024001400741d541c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 98041582 1250 98040332 98040367
    0x8040311030c040c0e09010b180108071806050711190b0c0f06090106180504030801030f061514130e07050613210605070521060f0409080403050c06 65
    0x9820200e00328950500c030300081e1070046940c01842c0c01034107200322102a2500031000710030070f000460f0450016a212008000240144903028104030713150700c041c41040d4001d48130140c014466140c03a407031200d210b0105a40d015450f074000700020b03500051400070300c08102c4c8075214036001150341003040401c1c04001d45520f26107003d0007105401c009018800d80000300100400240c2c140d007661220703c0c02e4501507009103941d00c55002c007001300c0300c50107400404078401c181c03190b940360b04c414503540d0940e03c604000d00300083c412036500c1d503501e0b001483c07403100d030840b0b100510704e140326002c10044d0001806810b150144510011500b020303010913601202103202400d4800507180591103010f0aa4100001c1600d50f200307200b9080000300c014241c086c040303004e00c0703524015a02448280c42e451821246c0c0d1040c0380003071190300748822440c1c2020b074580a2564011400814041c805603000c3c00040407180c100c00c040b10040c400086c2002003000c140084652030b8001c45203542840d907807001d00014030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 98042832 1250 98041582 98041589
    0xc09061c0809010509030708071e061e0e2d0301020715020f070f0302030a140f03070309141e10060b0f090406030b130b0f010503030702010e0a0e0c0d050c03040804 72
    0x30003055407000e60b44501c017610329000c0d00508803003005954414580d02c2c0c81c43c5005013184003140144000c1116101c000040880d40c081e55a4841e036414040c00382c100384481406501044500700f84c0c03503450780e030f806207400391030600c80066100c6110020280c1c1d000750f00001041e02a90050050901040c9065991155108a007401581e1249003006841091088540062844001c03040c08000d140c0c0c00005050f40c41c010b515600488040321441c80c1e02409514088005078600b00000340d0f0b074070300c2904900c0a2034841c01c0200051890184c1030b908001a024a0341c12842c80000304214041c1c0030070007605160140002040100e08018801c00148030b10181003117055800a1103403210f0325203074002c100541c0c00c503200030728034201b002c070207030340d143c01c0c80000d03642000c9010204007501c081458490403900010b004620707000c0541d005440c4d1141c641100ba41c445181c80e00007038a019201c1455108101041d903c0d980c42d55107070380701411a8009028022150414400c00000a0903141110180e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 98044082 1250 98042832 98042843
    0x4150806040b03160b0702040209040207030207080609010506090705090301062403060b04060801061103120406090b070e030705010c1a13020a060e091b36010c1a071806020c09061c 79
    0x40700180d0020801910a249038ae5402074070001e200f40505a000c039030701e800d4551007000c0d036010b500c8940700d00e400e030b8000b43c40c0306030b000c902c4902051045000348028000f040c000780011840580c0c4502103e08904408042d02182040c08803190007280c0c54824580030305802d0019505141c10a0400ac1c107640d014081e44041c044a901c0e51231500c0002c00c00e4034540c208201003001146400d1078200081c00c0100720482d5601c1e601c5000c02d02450084c3c20300c022910380603004141e002d02e8080110b480310b1700020705491740c004165000003503111100340d08d44900030300783e003008010001e40b05004007455158030400412081000c0030302c0a80d100c170062034100d1542c645100600c0109414001244114810603040840d18100c0306403100621059600910742c12040750109040030005456041c1e81250043c0000c0c1103050a0f004525240e403141e40100b824906403113552010101c40b00d4008150300108056030040b140000c4500e012440198804030648514104c5104e0b015080c20622194000500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 98045332 1250 98044082 98044087
    0x160f05010c0506060f191d0f0412031505150306030f150105010f0e04051e010b120a020304110d0606080715020a0609050102210a0c02030c0312060604150806040b03160b 74
    0x546d03605510030004108041301484850b940e401c3d5080518a0809800d184104d8a0005800303020824440ca110302d401c4020311805100f1000102e0081c003050300b0711042c48000203400f103615100e4107071220713810030b42c200001c1c2d0340d041200400d0325001d4660607030b0010f0343c40500b66440c440060008075044400c2801c3c40c03192101c950609407240845001d021380c10915100810115160384841c1c50740c44d90300085450020390300c80049070458401d81d6076080d85400032001080c91309846034000d650250088100322106220360300090328019400200303456650f02d550044c401408144200c2d402031501c10002e868080f130b0b002029440341c02894026058580d0f1354002000e1180a40440c1d4442b24540118125040b81481c1c0481e012001d41e91190410701d04100318040c1800001141d4070003190100960074100314a4080140309002003002c1d0300400244000110307981c05410604100304242c83e181c1142c41c0c240203110460b807070380c40380764800c2d480b82010106c99482410720078140c5506d0081c0e1503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 98046582 1250 98045332 98045359
    0xb010f05030601050d0e0606040f050717040c050405010e0a0e0604020a03030804061104060c030207080d0503010519050303130503010c0e060f0c16080d0f030b06090409060905160f05010c050606 85
    0xf04e09000c1d5000c0003d0003070801c05075101c08880070850500c5854200c50400040a00320000c0c41160011108030780400c4049100c801d801c0b52100d00301707034024420401e466002d40c40300c000c50150761082c0c0c81019030b018800140b1101c030700e041c00f80007103820305480140f205290079000142c803075400e032001801b400302c040086400c0c02a10340084d03d54001d0038150a030340d80d54411005000b1800170006a005021301e0710041900034020516400c3d034811545e44908507400c09c4204141c51948294408072018590300c00076140e102400941085178550040f8608071f0301e041c0905080d6942c48541030704000c03e4404083e0150390b030b00c0c00e0300c0d26551501c07100368403840c81d122141d190110442503c0107040842000003600070300040c4401010aa50384e6803803607160782c04c000fa401d076500b01d001e0592151040c4482d1820b810240d0028114078040e20b004502610552a040e0505030042c2c852528850f9990b000d1020900038000c080051030b003840c080244500319240e8a44400018102c2d03031060a410302400c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 98047832 1250 98046582 98046587
    0x1091202030c150a092117070501090b0402090c0702210705031204062a06111213020111150f0c070c0806060301060605181908030a02150a0b010f05030601 68
    0x1160041405820307402e03090000c0c0c98031070b8540c00c141894400034034043d4020981b00040c810b510170359a00003010085040f0b4a0786e8115108a404206198521051100310007158090182507641402804000f040e41041c0c0180a040400100440c00e0050200003010058072600f101d003102003014940e0700000c0112078000d43c03c203c1c40e40e002c2681407240391408104908580020000c41e980380e2107002c0d900011035580034030110301c03102c8507819103000716801c00403804c203801c000b03036000a0b40d0200b482c150030180040100d031000e680114a000740e1603154403c65030000318540c5001d101400500e50403001d0500300c01383e171600604920007240640c001c5545002100c0a031260140c2c0320307030002d0341c40d502e50300203582c4c0b00411200140f0a40c02e01c1c2c4001201e6002e84215007800c6045610003e040801c20f0034000c00480900310000203100c2c0403000508014203001a140e151007990103010403115001015010000241a40c0301c0285080104101c2c0e030380200520004c1c854608005c0d8880d41e402005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 98049082 1250 98047832 98047843
    0x3050a110c0a03050606040e0c1c06140a020a020127060b06070614070201050f0408030121060612150605031c020c030d0c05100c050d1107060f02030f0f060109120203 73
    0x4440d044481250048100100845e83e42d11918040c0c904202c12008045031903551881c6003680c0c0d8003d9688080d116090319901d04814181e4003460380072421000d00e07104a040b05078201c4024900c15400705121600d01c0c2d0a01405070078900d07543c0342108201d02d906c042ea540080300d10004100c690354205200c2c03e6100c020a9404c0c107034000200b0000300d031400e0040310b07041034119441c0c8015460303c00041c10007075445054600880d00142014210fa003050364103084070701d0a0302245110030304c12480d9000204180106405000d800340c6e443c61080a40c40c10300300c541a07440c502c050550078442d0520490702c001440c41103104501190228a0503240c40a90901d4042c5100c1034050040360307420310500ba081025511110700c034204407201d0701c59094004c0c1c200c64100e90f540c17000960401c64104100f100d6080800e030072480e440e029243c002250346500803610400052018a0b4020042243d0701d52400006035008604007150801807600307100082401d855409030054403c03c00410100b9034804004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 98050332 1250 98049082 98049103
    0x30106180306090b04050616050d02030711070603020408010f020306030d0305060a09020d1506030203040c0501110f0f0c01030e030a090b0d0209120601080f03040f120515010b0306041803050a11 85
    0x20032600043d03007068012400100c8043d074003441100081540c2884901c100314241000d59111401d0030007000c07058002e03500190810f000c1002a4015000015003448183e00410503601e005a86924100801e13095410b5001200400e031710500801805072004215140c0c0418986000925550b90400042100520303400c0401590b00c04502c0e404803110310b500421181002c1c1c600704e1441070303940b03c044050f44000c480c010600030380300b5002c001c0c0b03500030b1418101070091507040e00c0c0880e0040090b245851800c01d80c11109900210802a09503003603c150058203040301d02440c980032400c04003030180300184c030994480c02da001407444103c0c54542d040e1010450024400249003d903c4900ca54a120a0081c00320705c1c0188081d02c0f6100000004903000c64510307051085000c0d1404110319101c2c0031144003a074003402007558100c0030b0380b4103991450280030301020040e101e081960a00c030480750520044849401d0710007c41010030b400006451405046241c100584100c07401440c2c105044981f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 98051582 1250 98050332 98050343
    0x10302040c230d060e0c09040c0923150301080601170309120a0605010f18090501020d0c08010609080706050306060c0c0405090318062109010204030c06320301061803 73
    0x1d0502e01400c065400a01215101c60b1043c0002502c2e007086250450301030f80d80380c00050040010010605294020a03c6100e090800801060342c07502000b000c812019143d0b201c05982004426062038101c0f585007a084420108a003150b0504800315170b03611060140301c0444000c0034810392842400c204807000c1501c098070a0040617800141280e032103c1c507000c1195094201000424400e0417503010500308c1d403184008540c080c4040b40b0440c000c2481e0041602c06540030011147d42c20600c0c01401c80c0c400d4285d5075405250b1600600818410703180c1c100c0347c03150b0041c007020450260700c003040d42e030401c004071007550b6640307000c4108038a000740840070260000d04100402003240f602001505d07142690325584022800c00100300007162040c481c100e48a01008410f940a040c1d010911540c002d40c481c0c00145040c0e220745030700c01c10003000c2d4820400036034024a80b1544126841402070080000d0442c0842d41c204400101002d001c1400351500b0022442c10418003021421603140003141c010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 98052832 1250 98051582 98051627
    0x905150d0c150503090c040b0609011b0206042c090604030e1908070602010c020304050303030f060a080616120212010e06030a08040909050d09060c060b0406080f10050a090803010302040c 82
    0x9802c05803054004480b195010302410f9000e44039401c11b0300644074001c0c0000d22480c94800d2100c010358460050f20082c0301c00803200f02d0b10308d00680f141c0c3d004102405d20010a0080e07002128a11414800aa4024001c02c2c1d000c4083c400070703880014180c0d0b0001d038182004511310400201085100b0003161030161410461200020b0614012481000361019a8000d220018030320400340e980c0d106038400c1030b400d40e00030070000b00c0c5107403818807958024400425541800343e0310606140303130820540700e0603d040344c204050440d554004406254030381c1030401c198205140714481c4c20030001c05204517481030f407590000500c955400d012034051554444081c648035911040c1500c020103c514044541d40301d260400c0c0c250724010b500300b00441c0c81d60350303a000e0050401d54951001d0a443e1b410150804e48514010964a80901400300028100802042000f50b41c0034641c05944000c0c0000210300d10305030038074000c1038080f021241500d07010340300420b4a0a07000400c84042905202c11210b2a014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 98054082 1250 98052832 98052869
    0x5061308070602030408090d0b07091a07111f03060510080105030c0904060f0204060e09010b0705030d02070c380c07120203070806010605030405070608060d1b0305060c0903070905150d0c 82
    0x2c100b80e50780941400c1d510a1150341c0c5802c0c0c1d00c003344440800e0b00d0045402485464002820000510640c0801601d00005406410094014002006050070100b03469240500050900c402c05102e4200146002503c651404010984030384c200d0007124017400160002505025041d0840d500c6400300c1881190780d81c1d0745030381c0141000d07070f110b050601c00e4003c0c0d00009280400d1034240d41046400901030762030480801c04490095006080c00c13590504000c80001e8102411500601c66a0b031104015601d41f070070480520301465a072a032540003500610034150860400a821030950381c0080c0b41800d41e41e82400081d20b031030426400002c0c548100300011035070340c1d40180610700070b80c4500b0032960030f0341c0c44035000d50b40c4500460700b445e00521040b44034804204070700181c40440d410080c95148440d142d48500d41040c40840300100580c2001988401c00d003801c020013002840d411a0400036400c055480400807101c80201e907108a400c0040c100501c1443d01201008110041d80d00b4005082c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 98055332 1250 98054082 98054093
    0xb060c010b040608060906010509090a0203030307120f1b0309060f060303050a02060c03011202060a0c050106171b0604090b1203070f060f05090a06050c040e100305061308070602030408090d 83
    0x60005075900460800200013900a000101a401400c564000d40070326801d00083c425001801001008503104025908000da20184010740c05541d503030351000385000803032a000040d1400482486030312403402d04010030f0301c2c0f1813000d48080c200f00d914001c6030704c000d2030500101a24030b038114501c54919100d0004109504039004290748400742e0252201d90b5190b11501035140400d1050490b0300c1820308020b001845d10a00401030018070341015a03216045468081c01c5403516005818103039000c2c4a25220160200b09d00700700f8800c2e106403282c0c01041900410828016841202c61054655828030526079510a030702840da02e044044989801c0141082400c41041480070346009151080c3c51842d5001c60042d14410982807006208e040029901c6100900c002003107032080304414440031580d4401c410f01280207482603d07425a007141542000b904144000d880d030755981e114180740d030740010081c2082d40e07074240c0c2110340142c40350f890381402c4106100f038070150343d4480c02ca41c0f4000c04001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 98056582 1250 98055332 98055341
    0x40e0303040210090b040501120f0203041101020601080109150c0c051c03050a05010510450602060f01090b0d0204022208070506070209090a020a030c0303030b1c06090302010b060c01 80
    0x180222824810026010004d45520503d80a05000f0600801c8180324550046203c851008110900040c0071507038112584c0490304286d904442031030b041c540300049907a0401c01c00c0d026100c141c008002140665031880b450028000060f1619911108075000e86409204010000794100703055401402400301e1100b141410440c0100c0400e2920010802014140c441e05041e20405008116a200700000c15280d079459080300b03181880504c42c0100302c0f1014062401c0110000507000b516910180b94100100c0d540e07500700000315482070080003020007c07504164119920041c002520f035a001001c111a8903020b030020f9041070002400070148102003420140c18050003401d843e019841c0d680a503264005072051581c420b1052226034094603000d074900da0031070b4804c011a205803113107601141d00386801c0c0c1e20594108042003010400c3c590540100103072404202da074010504940d41003040c56202800e00500705960760048102014001d500c08100c44100900c400e48510880c04000c1c085c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 98057832 1250 98056582 98056591
    0x301060201050a06050d0201080604060308040f0305011805060f100f0f050f030c030d030f090218040209011208030f180708031e040e0c0a02100507030207030f0206100311010e040e0303 81
    0x561a1400007118200c45100e13000c00d07100001d0801928070099001114503440c05808594016510702e00040020700301d00003003004000351001c401c0e80720300e9070030128219201d05260001420b209105c5000207070300880c005500801c0c40700801101e80301e43c1f03240c01e1501d581b90000d186600007040c0101e8429490601c1c0c104a42d001c03541040048a06020300d0f4581070120300088d003540c4400c41080c00d103406a005030103203403414140040c0c50311107900041c0782d001c50345c512040d00002400900c030a6003450343c4401c4c09000141e00d0700c035011209a88000c510701c402012424007028020201c3e05002801d0392202e40740100000329600c0d581c580b0300207038590b0710041c0026584544c243d0740c3c46422401d041582c046034003135290500c05698441e07924003d03500c00d44444003180203440c0640949001c603c1580c2c0920507a90740140c40300100c0c90701400c0b01e1070784200c00042d54000d00030420002070743d0205030103996001c10f800c2c42403408170740103980c910072a00505a11508184582140303120000146208 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 98059082 1250 98057832 98057837
    0x1003020603130b071d010f140904091a071103030405030421050a03170a0c02100c02010b060711030c010e09131b09091a0103170901020316060e1002030c04170c030f03030106 76
    0x2034178800c00c010344201388040300c001d020451044980c0c000d110f0980c0500030041000d00301103110741c9903a4031081d0f103003e100c0011501040b11014400724a80c00390b400811201c0c3e00000310300c0c0d030030b00f91140742c0d49020743c1c40346c0d13100300420400b400c0740703940b80480c0c201605a022044656949607840d010382400568000c2102c00384481e0005095502d65024041402c40d02e500a448008030781e000d000080d060b082d00d420700703540d00d601502040382c50300c0d0020401e09009a1044440c204100101401c000010000f90b040000e801c2e003144440d500d007940c0c0390700504408600342001029103881c0d155501e081101c020000407069000801ca001c1c0d03000300c12654490500041000d14890f840c0d803400390207003c043c0003ca403014074020440300083c0188040c41e01401182c2c00c15464400007459000d41d80b5007181c0b000d444d8020143c05400421441c0d0ba11485410709508600d40700799140c440f80558407410f41c0154403560508114202030000d8141644041c0c20303203248404170030450b40c1c0e85c4c3c02071080000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 98060332 1250 98059082 98059127
    0x12180905040b0a0b010905130207050f1b0f010509060d0902030708030703080a0603030e31020405040e010603150b060d0c09030b011202060a0311090315060406050105031003020603130b07 82
    0x1041c2c0c10f988524415510140c541c4c1341007074101030901080f020007a10318a0a50b90030001000070a80030404c1154060040000b482c4403040c400c0d48101c01c41081550b83d02800c50f0240158045c2c2e0001c050310420345050743d040e43c440b025001d440014007030301c11006e50103024145002c40d10302d8021000f05030140c06900c13504401d80b1003035000002c40784544800307800260000c40c000d00740d1a180065603413992045400c2c2c0ca1464182910740260381c00f45691305003d41c0d00140401540c03c0500804414015480003081a285180c8078800d0002c0e0035210103640079a503000c1030890355640c4003551540c50260700104074001510030041c102940350300098034200c0030b24000048550410b000110442da01500b641d05210f1900c90690103080a00d104034001e03041403100c941c564404000359a0161410780c4003408904095091100300d03050744e04003e0401c80704200700920389030034400c1641100d5050300d20b641c0c4d1b5a51100c845c15a4055130310000c01500c80e02c800d00100d41d030f0099002802e4850441d4240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 98061582 1250 98060332 98060341
    0x1308100b03060c040e090723010f05090108010902130905012607032a08030a021b0a03030912030e0d060b0405060d0302210d020705031c020a050712180905040b 70
    0x10340d5400c0440f009800d061041206000c999480071079160007210000031118019202c0f10804030681c0607110424081680011007421503034450910040b8090303604001d4038140491000030500f0704140610500036800088a000405a212101c401800261005c02c100e5842c0d1300c00300300c406032050025106da0045403d40004280110301041203a07800281520100e0898410b500030076813100c0f98075000a0f298400086540090000301401c500d168060305944d134418510b803030304821010210f8000d544140f0140002608034509201740c9411103030000c1140381c2c502c2c0407902004503141c1160000f2041641c4c004101e0642c005d040500c9040343d080c0803a540381390920502c01d502c03040150045c0d029281d46031440303903400100002b10500f8140e05142031a421041000e0303a00444003250a98800600321942c044071501140d04c0c00c104c440294034009403218024610b000f4813a0240800b1040b000d400000f41c0505101055070140ea42c442c2211903942640000420b801c5900f0746401c0384140028 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 98062832 1250 98061582 98061589
    0x22060201021312020406031205071214042303030703020d0e040b0603010312110102031f050a061e02030d1103150f100c0609021305060315070503070f03021308100b 72
    0x40d03051003404042c81041c0391410f00c2410903050a0801a42c00961b00c030000300100700c90002001d512034080e00c9056650606c0d1030502a03c0720010403c004008800d510b414401a014046a00700e4203141c2003048030101c00d49008000d1401c00f0501949840001100010140c0105200c2206201c80d2654180c1290010501090781d01e0464a03c2e44000100011f000003882c071169030801a03401e18107541c3c2c501c01c0304400350880e88103580041900031000405000300400c441d07414050041a100d01079003602d031003006401460340d4040d041d40c8490554a02d04090300c01c005840804c3c803141c00610003c81d0b125400d0a05030b1044d110811155041d00b980e890302e007000b00c1071802c401400340c602035100440140807686103640e03440031500035444020000169880d007210b41c881c0e034018000001c03607003010420035241c14600c1c50402e060309103200c01c001090341c0040c01e03680e0244403030800981006803558100c0081c414201001350030722003490041008540028401c410810a41042180c0e146207401c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 98064082 1250 98062832 98062837
    0x6020105060904031d040504031d04090807350a030605030a020f090910020301031a010e04050312040305090306041b0506070c090906090c060f17040f0f03050d022206020102 76
    0xd10b411580c00c40120b0700080c420074032080000f107010030303000c00c4640030301c000340079950103403015000038202d2120801010700b091840311982904807000c008804040c3d0301d0310690b0041034000b81130134038104401240718420280c3c1486054400d00480034500030b011984440350071841c4440d000030300d01000400c09040005411541c1d50b0014264004900c0c604200107048000504040340ad001c0e1510858990205001442c080d6108500c0420450405281c2c8882500140c2c422680100080b00340710101310080200c80300100303e02031140182d900c0307042c141c2d1030313200f42d200d81505446014100014081e00b803100e05c0c1856141100315602d10750742d1040000d00d0142c50b201070000c0e03101c0342c41041800e000da401071b21707054171910b4003282895041d00c40102492040d80a41b02085480301d000e600f095022420710200340300e10b414030ba050700702502c6441c0d040e94840401440da4000c03044d0402418004c806664880010400556845503214103402e11007400fa0440ca1250b0518940441c0541c018000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 98065332 1250 98064082 98064091
    0x10f030201120504030e060a0c06110a05030103080a0c12030e0c060301080d120f02040f0317070809040b130501141c0803130f020301020301300201090b090402120103051606020105 79
    0x1200b201030404040102c004000c0a0400c03018084000070030b001d07949401d0081c00740030300f090315804401e00d010304025003a0f404130030f00000010300801c03020600540100640e810740380c009020035101e9400260548000a042c0c40c090f144460852000100560540040c03101c60411400c1d503011221180074000075010a0040000031f420080b0003c9040d4030880c01c1c2d0348815080780010800c58400500c0404a91054002c0310100c0401c0c0e178180700780031010440941c080301201d08689414115158031482d0302070740031960b1245407200d60b0510241d450f0020201902ca0300001007100796911000c41444540c2d00a001c0c1c012042c07081c0c001c3d00c421000a11114098100d240c0d50324540e210504100703080040c401c100c4020b41520f2031040961003d102550180030408a100f40b10841c08010704043c00c01c03081130080e070788201e102000040c1d074440c0010b411036102c02001030300c814240b40010301074010340200416184030303040000140800003410f055200c007242c1c00c20b00d2079a100d40040b821f0300c4c81101c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 98066582 1250 98065332 98065337
    0x1103250512010f08150603101802090f010617010f060e030a0c080f0c15040303030510030b040308070e030c030a0b100b0d0b010807091d0612010e0c1507020904020402090f27010f030201 81
    0x10403908d1401d036402402018103000c29401b40c603640c07070f07000840d1840309850700c40c002e00ca2600103100c3ca0380c0128001d03c1000c88803200024661505101003000e001a018032070800c030000b0a0144607071403c00a1841d2a50300c0b5801c007003e962a03c117007075a60f034100b4441d6074491145617414100e6050251f0818690300d0214030003440c10f42145c8090f000b510000e04800020410b848001020a80840030507010b00d2003545c40c00e10a080000d401060848035424541c803d03002540070480c0b907940000c0c0840c410760b001e04915150b44c0c4503140b41041103103660000100d41e1000a00c0d814146003a070140c001001e00b602e030104103403a81001102c50a2041c0944d41301d1040141000e005000300c1c0030300035032011005009502428411500310309407200442808101d602403100e0051516000b4058003050710350141060402c507240d000901e44010150019004139400559100541c5503841600010a000707403036000c0d1a004501c3c2c0d40780c0f00e21307a044030340604882080007060300c2d10030000200840f50141d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 98067832 1250 98066582 98066593
    0x3020f040b0306030c270f0c0304150b12060a050f130f110d0501051006110304211b0306060e04020f06160615030201031103250512010f08150603 64
    0x1200c4000542c0060040c941c90f108940d803500d501e6458a030080f6002850944c10005800201019040317584050010840140b09001308440d00c40c0000070340340d105401003c462803011081120000034110002d546400504003607010395003000c0000c0060054034002c000304550366035502f040304a031806580d020300104000d0345c0c6001150394410005091030003000407520681344c07000050709041c06044102d0781c50b5111820801da40c0503001030440148030a090801c0381241c1c000180c2c0d02c82c0700f507024a40f034a149284850340920014209090419484034480c2a4403c4501c80c03a130a00d503c4d4841110020304014000c901b801c2d401503082d00440d0b011301120f8581000c80d0410159411882e0020340c407030300a04414020813510302503074510103036840e441644182103000046c203685d003100041010010402c14003000c2400c00218041c103070b0400a410306030319240d00040384e80341b00d80004481071809c032000101c0c0c0c0c40240d00103c0b040700c0542089410181c1000c19000340300000700e0f0015410b8000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 98069082 1250 98067832 98067839
    0x90309210b040302030f160327230307090204150212070609080909010303030605011409030607080c0714010209040606030b0109060806040608010908070c1a040302010c0602250209010603020f04 85
    0x3001c14290841d01c6030060ba03081c00007000f40040d5940110220103841460740442400703040d0400d821910850102c0c6144545000360003044403140b02074410303c242c024008800003c040340071400c20851078801415618040c0d0744600480c00b0b5013082c00f038201c445054180c5c41c12a42c0c00001d80f0508081c08419807810050941c464600411a500e000c1d1444001003040c141e00d961b40300344290185119803400100c140c10000010140e00302031014a901e40b8040001540640d400140c0b5940302c441380c900030500755102c6445500038010032200230564015411813510400e0103401610102e442600c040000c65a501011415590003822a5011804000c5c003031143e1889060031650101d07010704041a600d80e929540c034212502000b06403082380c4041000010001d114203540010700c441d48186d841c40550101c02c24981c41036100090600688440031001c0061680617640c210582c107102052452542034030450340954504100c0c8160031240010450703d0027482603507000485022841e090070b09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 98070332 1250 98069082 98069093
    0x8010303050d021c0e060705040503060105151c050405160e1501031118090105060405031002070204140412030c0f0903020409060b0604170f030316121104060309030921 74
    0x8075602c04070a0b0b401300b040c00000650003414000c440d0842d040040e000b0f1001c0744441c20f00d100070702050b040200822007003006035030001d046030548004031144103110181d040405914031480140c124180c0300508140d40079809030340410b01c00c42c041c1061f41c238101005030a410120101f40641100107480c540459003940081f26085014441810001801070296400e003140784c12000044003010400c101500050601080729401080d068881a003800e06140009864aa4a4203554480e40e03000c240c0105558841d00481000404110170a0250402d824003c0100d40060030103400f2a04000e0011708171071145818500652036a603407901c40500f075508010250081520903507c55484101c54205695004024401024441540c03940c04003501600c41c03c1800719294503882da00f09004110001580c4408818111443d01d000054182e0400300c0000400c0d822010000c06140402c1c04900c1d281c0640c00f90f60564000c0d21a8000140c0c2c4a07000c2d0701d201d0603113000c450740d0020760080038000750 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 98071582 1250 98070332 98070337
    0xd09090914011a040b0a0501090302060d02070c0b03060316050a181e020a0210090f15020d0e03030a0e010e0309011107210204050109090f12050909130b070f0801030305 74
    0xd1290401924981003201c1190a403007070320210004484420305414028601445421411038054a103030ba001c40c80c0000280c6a1001840080e00403403001a00142c2200036604a45007150b0000003910129240d8444540313640080b943e042c041c0c030071034008061442004d0701d01003c6800c0101024101802d1490030700244100104d000402a1201006802c040041c05c071b80d9981004403000586541402000a00e071901600140062500d000b174000c011901c0f901d9488180b5402002406071640c018465400a1042c0928500c40b64508140c00400c00340203c0103502445000d0018464416540d10103801c85041c0c81998015900400c4185101c0d400394001100c2100458140c0d80300d1070b5503c00800c03091610b0309440d500300041d01056000c5241074070516001d080c0040041201e12800c1c1c0d5804115039813020081e110222103c0d0220807a4402c1c000c0703540d80d200150030509681010340294084504a0408962a030641000680028491100b0040c900096aa0328103940d19688090f50642d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 98072832 1250 98071582 98071601
    0x1e030a02060a02190605040b280902010509120703061a0609090a181113110d1a0a06051e0715050604091208190e0709020306180103050307030906020d0909 68
    0x14029241d0a9000c9013000d05030180003806001c2c0402c0b50700e02403806d00d20041c0000c0208815480400309a203d0264035414188040441c075000180d2001c14001a200c600904100c03603405011510481030003400441c0c10001c89124031424031450090180342514900e00d05811a0010b0092180014501e404001c0c542c000042480024403500c031400324000203c006170058400740c3d50b10100c9880ea00f8011040c4540092003002040081c2d001603405140b0f1140140c1143c6081d12107090030400035003412074118000c1c00a001410a40d640c000161050300709032245801c0d00003000000003071041000880c4c80c1184d0021209142a801000010040401800d141e411a81c1c401070f03000010544024500c2c040e44940b6a5501803504c1c0c00030b9400d04240d14428580d55007805a141d801e10400038401c825210480c5015032240d85181c0031a5120f54086814011030010000001c184107010004100550107a80d0352617482e5240c0000307982c0c0c0c0c903012006000045040b481007184034003552103000007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 98074082 1250 98072832 98072837
    0x6090402130905240102010c0e060d0609020a110c090906060d0503041203120c0c0b010b0705030f07061410060c0809040912030605010e01020a020a0e0c0403050a111e030a02060a 78
    0x35450346a600201c42048620400c1341605440401004038601d10794190f1010910090068030482d0800806807080d000055008590201c2c0c40048210f285c0c110b0400303400700072011074584102c05002400540400005d145a0003800d052031440e0500e162580d00c9004040d009190303584600303060140c450030407042134525010500011640400b00c051441c0800d002c0c1d9a0303400d8146c010b004140441e03609180000c140300d51903044030009403104000c7c9044540e0856155200d0b0300d1820402c0c03c41c803414030210026a4000f0320b410400005510030614074200040700c1d040344ea034002c00079000e000c090094901080c0e1225003800042c001c2c800510758004043e00110303050f55140d8485011101003280070004c40d0301e4500620065900103120902c0080901c000d0083d8081034003c111075080301d0080e080f45d0170507100020104010001142c0045034000c0480d4000c80803800d0207854070b80c0002d4006c0c070503920b0800f0100781c100a070340030504060008000d410400389607400c020307055100280d94001d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 98075332 1250 98074082 98074117
    0xc040b030702070302120604020f060a020c0406080f0d0f1b03030b09100e09070b1206011106040602130b0a02033901270510200703110c01050906090402 67
    0x4000002001840c020070301c03500105201400c61041040c801092032410105900c0002081b015990f0050b070410f410000f0b68030309944030b0407502d041741003aa009502d030350043d01b410000900140d000511725070003203000060300d00c03402c1500030840304403015185010005440c0e011236450600e182c802028803620900b0001514080c42011903900107080718030140c1c540341000100320048214000941c482c80c10000344c4441c4e4100300c1c0f81d0595001c0e082c0c002e4210350240000559903401019004456400704003101c0007031410380f5115001e0b6000311060f41400c03902d45c000123419203805064441039422074002c0d50074a1402c813010024207070500e020309068580d59070043d0084040c079200080400c20071001103000d02098180f201041c4081041c2e8803c942c0c11b542440210301c001c00c0600d0f440070105000320710001200c1148a2224002800603110700300003d01c4000c06400c40e90910840d040b460540c0c0c8100550b60043d200390003191901e0ba0480c2c03041244e101c15141c103600170680b000441103200b8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 98076582 1250 98075332 98075339
    0x612150612010e04051005160309050102040503060c0703090f0501080a0e0115140306060906180403090b1611090106020d051b010c050a022e051e0405060613140f0c04 73
    0x84141070a0f0f026031491034003e424801032010922002000b02c00c113100034003140c14800380c8108080380106481c07041686c0c506c03148007000400e404a0f002040300070116035160510501c644aa980308a8044010076010f401c0040d590400100c0341003110016100d20206039110f100d160701424a01069240315540c6081c0c081441980d9540c0c10b024210519500c010020190280f610780180502050f00c60381d08a01086500e6985141a098840c250316110809490b51f16050700c09025a80000244860104030010440e410322202030506002e60050180300003824280030100d413083c010000160819000001c00500400c014141010980c00c000038503111150207500b103800080021000823030014803030443c0c0b03070304103c52949811011481c041070707000c04c54560300400071079034841456511751000607400c280d00d030000c140240301804400c0a03842e041c80d1494440c0c0c401c8503128880c1c100400600c42404440c802d0701710740105201200c810351501000c01c0d0701a500141010000d0f00200000f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 98077832 1250 98076582 98076607
    0x50307030b1005041503110f13030507180b0609010c02060a090f0b19091202010c0305040e040606080118050a060b0a03080409020c060c09060a0c020f060406120b06121506 75
    0x403107461820f68440351680c2c100491500380c010140428401c050520403850052054841195040d2022107002070b074600700070495401c07941082c0e001801500900da170010b51b58072180e00c40025001011020407100500d10200040e50040d0381c2c249001032941c9a00304010706103400100307101030040c03c1883e215a03807401c1c01d42151300b8075001075a500001160511034129000d00c001044a0700e800d0070303440c0303901300788410003042c1c03000001030704211030100300c401814000c0040300d001c0d1444d400120140c3c03810b8100301c005400c4a10912500350310f0a090311148a2840d030000003c0340e070050260512240a440e208040d00d00c0c0700c06030b50302090900c80040042c1c80713a0700406c01041180009610759200182050074148020119280001d041201e14010307561007044800c500a5800c00d02c43c3c1c8080c50011030a000d200c0a003880c1c020b80300090100e03210b03800503070031f41100e102c1d64800d010b000e07907031002e0180360b000302840380080f481c8600215007068101c2c00300c0f0760740c0070010b455903081000c80d9402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 98079082 1250 98077832 98077849
    0xa0b0a0614040218040504020f1e03010b010f02100f0609020a05181504030b1b070f06050f04020a06111006080f010f0603020901030f1e21090308030112060207050304091517060106050307030b 84
    0x1c0012b501d6039002e140c0d0181401c0c004c00c9442002403c009242c4805a00c4c0651250440c2d05040d014039585c00145202131082d0b4003050140498620442d200c070716814010b04158400100e4942048a850004585140180441540d916036104c03a130f007480e180d583c1c0d200300b49501501100415044072203a020040c1c03010040d1844a01488803900b08404504010303048a001030052584043c14600700070240c2c17552444403084a001d480e00014606c80c1d100001d0600041e4941901b01d1410007030000303680c01d40041c56070722021190f4000c10125517031400f00740855110380310094020070305000410101e004464002030142c007844184901080b010100024660005c034112a1401e03d2100166a060320b90201d440c0c0e103030541801c02e43c1d5800d40e16041c0c1207000c14490f80c00e0850402c14090200b240755010b407444a54040200d98480c2e4a41c1c245074050486498901a02c043c2c14500046810401002d1540b4440041c0074060b280d00b001022a210b52009110030b0074145c540411081540700c150b40e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 98080332 1250 98079082 98079109
    0x40b030406050105150a0807110f0601030303150b070c0b0702060f07061b0203070203060a051308030405010b04200405040506010302190206040618030206010e0403020a0b0a0614040218040504020f 86
    0x10001000e6040004118506044c030340340b0840440e062241040c026000701c0500d40112231800c2a0388501003490310b9528001074407442604a0140c030000004054154001d15071505440c5500303ca01c03a16031000c24003c4c01484005003104451403010420b010010004010260004d40420324040101000c41d0301030307000401c111441079a035602080240f0801c40c8080b00c0023030902c0958613204140d00040e90b18180509641c00c801e0755600401c030f010b015501c0c54440301e0361008a60b6120300d094244107000703251103000b682c0594200794509240f40d040c2c00b0118448150322020f030f0b041ca41018284402030500404503414150700700010100740b4400d42d10107840a103141e0003400c261825281c0b603070548107082c4043e10160050301441c400607401280850644103950340215056855040c1249007503290540500046d041f00240040c0c44e195402c11410b4624580302421020003042c20b0104074420342c0400781c1e104001e400e0900007498650000303600103000078a145683d0703c009000844000c54243c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 98081582 1250 98080332 98080343
    0x406060e0103080903070504050717070509040e0c03060709060c0602030606070c0b070201090e190e330105150307030f0605040c0207050108090c030d1803050a03170a0c090b0f040b0304 81
    0x4c0c1d08400f520741000311001401c0d080c0c400348500d080044000c1d0103042102003444540341160005000c50f03100c0d0080d22040c400c02002801155104500d19813100b44416141e4000d00614000a82d2607000b921190b0403506203544400354100d0703a44400e40250000342c0b8a5511150400c094804511f2610301e190152029841ca41d6481e443e91001608060302503100d05848500001000072000716000f00902094089602007000403001001500b003001c1d89040403c0e8200d592619043c410030b1a140400d4145c0140c3c0000c10350340c80d88208964209503800d0500202403c00025401c0c43c4250401800c01c180000301042c0c4070346500c0081c06484401840c000140d00085c4204040c0d030b0301c44d02c41504181c94802400c070b00c03020000843e0302d03000304c0c00c00507051010341c00088850406003510b00005503000000d54404000900d0002c0094980200d2211000301100124599032903512500360110340c503899030071b101c0d480c01ca0030880c0c40c0c00490b4454440c010a0000007180b09855000354031851084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 98082832 1250 98081582 98081587
    0xd0303020a182d030b0108010516022b110109050f160f030807141906050c0a08071b0606150201060602060c030c1b0a05010b03010501050d0503030402090406060e010308 74
    0xc1c1030003010b454a41a0414149082c100104964800520a50811800c214414142103042480408034861941c00103008840c008000188100306520090252000c030030001240d4480c00f40890b41c91700000113141c000c0341c5c442c540c51442c04514980f18291480390420135030029003034980c1403c481c440901560542c0044400d40c0d01107609101c81e40b201c1b407107480c07425003d07400d01e10f40d8520413885000040113541d000a0080070b000b128a42c0c40c00d0703d50240111184003420131540860032030114000c0702c219003064049000d103d80c2a0a40b688501640d0746c544141d56032680c1141c02c60498800d4080c901007024065021403058050070002d4102d070048500e00e240c001000070f085621523801201190440d034180090565000c003160303001220a03844544520700042d00464140000308003686134401c882c0a02c08010040d044002c0b660012002000309a0361102840b804411400c0020041c0d04100005401441c181c110180c0040c0203a0001507001d8036021443c56989082c0c10684110402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 98084082 1250 98082832 98082847
    0x20d02030d030b01020601060f050f22120b0106050306030d0c080c0a031805010804120c110d0b0a050c1c0905160303050d0e01110301050105160203030406050c1509190309050d030302 80
    0x100b108500401292408050009e01c13810000c102d40524055142401c0b800103c2005a0110240d000d0fa03c0d920402c5038032a00e640c4220701c2d602e01e2500102150500c070b4140000850502410a0301e10840d00640586480c03103a0b0b1500300c9014180d1f120840b403200d4140302c10482c18400300800c0080f24400c1e240e100c02c503040b0200101103031901b94000f604100b8008100300000c0e0140c115001c2441c0d0342d0400d2449a0f407d441d10f00d85000e02c01015a4001e00310103445c03401d0108141105005034407101d030420850b2240d0110224511548612001f0070030781c07120144425072103502c050340c824000c6050340c17202241e040a06110745500d520540000c0d6003c039035051007200f00d100c0d581441b52128000c0124090401d81500740703020501ca554184040030801185450000d00e0b034400c04c80e4000e007902d598175252100a0440c0c3c0104003201114400e80a005440051000d44540038802074002000a00b590070b44541707903031521000803010031900d4400000c06071980684001d03035174400d480141e2126003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 98085332 1250 98084082 98084087
    0x909060b090301060509090703020d03052811010c2307080a08180708191b0e01170610031e05010c120e01050f0106030f06080f0106060e06040f050409020d02030d030b01 74
    0x200361700054402c2c040e010903c60b8400e07000401c0004c41e54140da01803696a00c506017540d542c0108641c04030301c40b15640c00041d80e500e00d03500760a5074201603203420907400115140a0308881030036042c440401c1c08100c46a441d00f84902d140c0500001c00c000031854a000c2c0d035241640d9400481c1244042908141400b440e402081d002000c0701102100400c00c1a02d84283c00c0e940c0c0700710150a082c10f00c12070701000f00b40706c510704010507045c030b00310522a0101d030740703441400002409103c0d1101c41d00a8a251100c43c000100312180030b490192240081203066445200002150500282102c4242c2c1c8074800020703420f0007002155611915103007036100310950514241d400c4014011038607450601001510100f041c10541900c003185030004500d001000d224000380f203a03820501c2a4444c4880d480b1070140150030181c244c0c0d40d00d640c0c4101080d13044050007628000c5000300c02c5c1c003090b40c0384148220b007011752101c80030038002402026120324503000719040c98140029140000c0e21030104400c0c558 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 98086582 1250 98085332 98085341
    0xa1505060a0b030903040e06010c0f0f1104020408100e01060f06020d091406181c23010605030a030c0f0b070809011d030a0503060411030910050115050711010909060b090301 76
    0x5000b40e100c2c0d295180c44482079440703200da801b034420585070403404a2041c7e440b603204c0064a40e03029a010f440788490b0b04003020b4103010b089084504c10b03070b10780c0400e5880c1828002c0e1411250f04200601511480744003d2029122184904443d9944c0d0500002d0903e48152900c0081c040e9070013500c01c00700114401041c3c1c42164200065404181e03080e04020786400c42221b40c104a44030601000f01e1490f0300080101d4002281e100000d400c04005500388072440c03144810031003080380c20040d8a00408011400d0312444c4c0700c0e1a5147c0c021411040100e40262004400319104085115082c0d0180e40c0d440c0c1440c1c400d0341c070307140041d40703881c2003000d008024403448409071584407864100d803501c0600c070f5649110391808102001400b00c045142034440d81c000280f20718886100079120310b0040c3c4403a54540341c2107011000c241c205000003450304900002105080c2503503455615210007520740c40c0d055001e1615450401c07030354500000d80c2041d548503600140c00c0c820b201d0307a03031040200c04040c00d55 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 98087832 1250 98086582 98086589
    0x20f1503150307050f04050a0f0f0b03010e0607090e090a0c0e01031406040206030703020d0908160302100603051911030616093201140a08010611060403200a1505060a 73
    0x80d4081070f81400150b41e03410024034007540844011405540e20100754000c1d045001e401100f49040070f000c20b156018642000d8180705007a0020860380034100b24443d5102d0b010b58074035011564640044c8220300305001c00c40c1d4400420011a0065081d580d69075545003485da00014028605000510400001c3c1e444c0c0d0700c000d002e040042c441400d0507000126288000b4214005150b80060a00d00303035403407500300b602000e0b041940e030703501e908405d681000c5488a5074400c400601607680001c40311003452080200f9641c1150082c1020044103804a600803230703c0000752601c40150303995607003640d8104580703407040c80e81b020443c00500c460013000d008148150881302802103100782d40a01c60484049580b49000c1c2c02d05020030301c00c800b000698003c103039940c0c110308001e0700244511416800c1003c940c100d80313450351645404240c4d00c036190307140c2c0c0064030700a000862a091411a21009001026000c040721060745c403814003907503900c50741c103095540c812041a2207108000316403400c03c1006005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 98089082 1250 98087832 98087839
    0x5090117041113020a14090f0406080a060e070308030103020d03121a0307060f1b06060305070e010e0f01050f04050402010e030f010614040c12020703020102091201020d0e0309100c020f150315 84
    0x10446103120140c0101d002010300c41c03046d10041000c80c41943c940440e09030000d070143c030030440540c0300c0c0c83d107d858080481d0b007603e015040c90b541c40c008844c0040d40204581d04015501e0071a402c5500b000a4200c0000043d800c10900084080d0490782c0b40c4a805603c00122200300c0c2c2c40d030044418181401201d501410502803460071074492250020101c60814102c03003003412001d845894448000d00c016003010b0a6403042400120390a01c14091160503606210071a043c2d617501e04101c5038814609000d0079400601100c03d030038040c2000c0d00600c1e0403510504000701c3d00b021120200345031000840910741c4580d1103107000c0102d1185985d80d5030707020f079082e202480461a0040081d105001d00004091000e500140c04130505100390306444011100030044030f5076181182030780c1d020750030819074501c0c154a0014101d03529a40003085401400020340703030100c07a4003030b99815245050051000c1c0d80050440a0b10009076488030050101070300c200030501d4890804d580200510020031101502 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 98090332 1250 98089082 98089087
    0x140604060f0615082508010f0b04032a03060e0109020f03010e03040b1e0f1909030c05060a090803070302030309070e0606030a1a0301090305030114010c0c0302010509011704111302 79
    0x40f03114124030248040c030113082001064803081c8804140414502c1020510320003d16918000356000205a0403240c030059401f1388a40c94641c0754556100701e21005040a00304d4142e500b000b0186141000030314800803088082c03560f2515880181c0380c840700b1000c466551031140008602c1c10f001c030356a9124094000b0403164041c1c440c660707078a1240380201e050701140030400d10210500044002c01301d0707900e405403586601050340c180855810245a149004c00c0108042a00b14415221107040302c0c0c01c45003100307801d4901024009150311080290080080c1040c0102c0c610004100a006240c4a540156904c0c60400c0c102820081107400c07000170105c01d1001c0c02103913980e401c25650890014103002980d401500c0d50300607219020340c09150154201010b0382d040c140c0010145048842c0058401c0d41c4c840c6000045030a40e40c043c00080c000c49440606001551181c00582060101030408442030205029040c4402000312011201c4180041c680e10650034000684120540c20313480c19030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 98091582 1250 98090332 98090339
    0x2031213080f07170f150403120b09160203070209041a0702030408060a051015080106091a0706050a02070c1401030c08040515071818060501020a0c0b0a0507140604060f06 75
    0x15120f03041c5109004051140095019841105000c544010a09001200c00215410070050740959040b41d042c0c0220349800c034038041c03003080380c01207200d0070780002c00c1e618a50b55513140c00420000748000c50b20440c0b0052140000503103e00c410a800380d0b020f241c3c04801185a40386921814000601c1c15086400501c410000d0707030400542c10360807000c000d101080079075402d00d42c0320004030258000700e4801000080d91110315008289513059450503500c0521701034a0341c00004500c0703600b043c1c42400d410700b04030020205d1980d903c40d54010b008110051714185070307500e0710741e11121240c20044840e2011500c0d1100307980c040c0715420302401c42d82800c000614080d103980e81c840b001840140090210b2000060015108220035038446420035003485c00980c0784d00d0003240502d14010010060782c039040c80890356600000b104c00d0800c2e4072264240e04a400c000e030003140f80c0c00062840040c001d0602007940013030044240340e0742c010140030050105283c107040c280107949594151003c00c9150140c2030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 98092832 1250 98091582 98091613
    0x6070209040f020301020906030106030e01050708060d031d1f1d0109030605040303060308031305011808031b0904090b07080708010e0612030d0906050609180d0c08070203121308 78
    0x7503100e904030840c0c545150150000c039005e44100800541e1042d0004008101140c06078840c420025642008001d6a0b40b00350701950440003d0714525440710010204500080c071410310441a80c1d0900310a04c038061130b907004540c00a11b030b07002c0d06103454492540b50f0701480c1e1260034000005081410101d4030390711040081c201802da40000340030241c68038002170915000790016001940d001c2c81c0306603240780005c0400306460a00204403055400d020125060204109001e600c61b50881d040030f20b1512103401007814005030a1b4451401c00b030a10203848030f59a580301e0302e031206004040b680164504082d008100c008014540c01c28040140c0041c4003d80b000503d26a01210585d140a600b4031807020f45841d502880c13400c1a040c4c1c0c2405441070800c2050b8104601810050358039071019201c02d000540d038500428110312042c0c1c04650a8801188510700d034605160040800720714240141e00440c0c00c0858078403080c0000300e00010300c124405e06590f0500000c02e6808050501c1c0901e20100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 98094082 1250 98092832 98092849
    0x30c0a0b1b15041e0c0902090a05030c15070c0b0c07181802040c170c070506090609100902130213080c01030e060a0203060406150c030215090d0c0309150e0f060702 72
    0x90540c802c400ba9521300c2c070b09541e012680064000740100301c003580e60044d00c40654840100b141c010800507034001882d041c00140a401120700800b00c86080e051880e00d40d0311504840300943d041c08042d1400a18003800500411140f10a4805403d80b1828201d401951340c05510502181e6031829420102510081d10054501e44d41124003088501d13641c88100c0d058141c0e4100c0103805041318040c4480e20b01c4140003805654131580c240c40c080c1d030350b400c84103455247c111100c1c14a80c22049040c074400c81103500038042280300401c8480c1c1d00000d4800c40c000ca810103a0380d030007509805401402185803c004c42d08141000340b0742802090305e9103402685501c0d000d0804922160080041561070b40c1d035411000241900c05142040a00494001416203181300400d0340540101e0300300060b80100300c44103510403540c4200500c00c00b007505008a540146c0039400f0b404000314104e006ca4041442501c50150391515a2660b41207030801c1d007004082c15001007014400e5104100040042e100c0f94071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 98095332 1250 98094082 98094091
    0x130f030b0610140d1401050f090a11040b12071107260c060a02070303090504060e070807031d070513200f04050d0b0a0f0b011409030c0a0b1b15 63
    0x3510160401d46880c00c3e215521103200103c0c01040104440140360f65580c4038031007010146060b9000f503641d40d400d03c14030f0860002e120790401210400100d00d2843c80e0001114000c1c050320003440c20f0395848405249406c00d40d00384403802c1c103500510819903400000b110500074024040d0000d00e24080d01c00003088802c2c003145944103c81070100140c2d8030140041c522480029142c0c543e00e10551000035100c100b5800218041040b0160100d0036042500c2607100380c51038038529403819294003100307840802c001001d01003095110007400344949040b0321043c210301032000007040a54284010807158a40c0340c56801142441c01c000c43c0324134081c13902040c0801b443c503d1a980d413823030300306421801803140e07400c03c0d0b0b080240c0c03e040f4000c110380b61250358840c104454003001380e44d0035080e44c40c066440654880340024010042186211800e1005000004004081311560391407400800c05d83e5201e50700c0003440e00700203e04200300441d030701c1c2045100000384000e042544030350443d10084500250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 98096582 1250 98095332 98095339
    0x41d1501081f05100c150b01050703030216060e060106111b01080702160b0d0608010b0a1a04030609112e08040f06050907060e04020901020c1315080102130f030b06 72
    0x22000040c24050070b20500504406407103020110204800646400e07861501113a03243c00b440402c41d890400380c4169440040c0503554545403401646044019400550b00e1304100d4510081c2c02c40003036080e200b40ca259094000240c0240e6140c00d001401090700140b1303400e02030700815034400c00f035068100510000402424041c1054881107402c034a040003007410700e414240c02440128030281440050000c00c02107200034004545ca400300c140c281c0b00300e0a00c4580050b61864203002c4440e43c02041d0040d200010407240c02d059894450100740c62010400742ca40280d80c1c16400110306022415a011003101a0a82203070003005c2084420030150300100020030071381c0d0303000c01e0030003030201040c01405401240900003814182540d030307180c2e0001d100301000f040c11500102c965003040c0c001d84018501c142c0260080e1003448040c80030640d81410090201684d40801d803000103201140340d0060054800016207440c66200c490809880741c4d0001d203400900b800040002801d400411a030000058 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 98097832 1250 98096582 98096611
    0x10060f0e280503030706090204060f060c1403190c0501140118051306020a0f0e030105071b050a0f030818030405150c1006080a02150a05070311070b041d150108 70
    0x10324070341c200480e06401c00d603410f000008180341408071a070441d00380e00d4000c90781085119070395503000d064494284115004a400702104502007483c0761000150b8070080c07815a440c10381001e0303180610160700800d14000c5007800303002000b0700800340300d00300c828a1005090380d29541485030804054101e00e800360601a12903000450b6020141220344d0f000d42c0c840810764441d000c050001d08188120900c07100084c3e864202d1015900d0140246030040901c0d8a601c4d000140148442801034681c0320203481600c00c44c20f945001800c0d040300003030214042ea868030f201d81000d40540049608030200203031654800d00c000c1c0400d94035001c25070030307042c40343e541d465075400581c441500700805403003940002850200d000a164001081460342d5030710842e440380a03401c910391001c8450261070159800101c062005000003406410307644040d051200484000c0c5640d0413130341243e50306c42d800043c1c0d80f088800120003081713203080303207140c00a220b80031000811724010002401400c0007002e104104559 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 98099082 1250 98097832 98097889
    0xa0207020321071506060e031216021807090e0705040b0a0c060905121b030c1c1101020d0603060b010f170c070b04060c08060d080a080a0609020310060f0e 68
    0x39104464506038007a0001309041038014001008004511030744000c100b850207542c486203004201900f049840340711039402c0c4404884901414114031030100d0b008a0041008604c2a44995200d4032440740342da40ca004081c1000d2071070341800405440f04043c04410302061003456481002d84040210170701e8000c8480709039043c94809042d2500d8003400c517016000b2605650440c5400602d40000ca001c01e240a0740a5401071998a2080c00100e5005401211450504070b28a135071410104000303180c8845041c13428200542241e0040c03955008555030b804041082040900030711125030380900382400101d861900251181c0c00c00c1c0c0301d01d465156040e0000e5030821040c010344e01c020350401c01d141c070985024a420f0006041003094807000c00c03030800004003549000300c045080141c1c09039005042000300741043ea50a040a00f450030840c1d201e00003c11100a141b01562003070307101c45070711070352107162990207050594403c0b0703003100300031f941030801d000d9458140741883d030300400c0202c40090218 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 98100332 1250 98099082 98099143
    0x5040b040e060d060216050d11061617090a0209250e0102120a0201060e0901020712051303142d03041802070506010315110415052109030a02060a02070203 68
    0x2100004c1800344085440c2c121616402c824161003446a01141c541c0341c0680401d59116415541e05040c85e0b1000d40052130204080c0701c1c002501b5500e01704403401e4220480306001031030044412035030380d5011604660035403030a007200d6500249803800200ca00d900c1e00c20032140240e00c81544500b403140000807000c50382d00c2005000034030b110984545884000e9041c0080c0a0902031144040b006c1552022521030342c418802c0701c081c158001000a4280425101619580c0004030181c2484c00c4100c4000041070344140e40030706c401c4da0000074207844c0300408641095106e811001c6911180e00c60540300c125000002180c040e0b55282262850114041405001900c03035150010314501900c400013080261241010450700701000c4280590107001d000c120481c0202c2c442c00b000d00d0a44891801e51314060001030411051a52400b4404072b040c48409001d61720550320704000c2d038000500074003080d50512915401c4000c2c2c1006500e800c0d40c607000a40e482e0820144810303000c0e030354001041c0561 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 98101582 1250 98100332 98100349
    0x30b0a0801110a08152805030a03050a02010510030209190207080406050c2107030c0503070501090b0702210910050d09060906050a0b01080f061c06060305070605040b040e06 76
    0x1121800030310000758a80a401e01c80d07040083c50300c0202c1d401d0004507991084242c2c0e8000c0703004001c1e01c1207250300a103044c880329610741141440f0540440a074081000d0310309004500c0700d980207407a0b00c3d950380c44444009007180c100600e41001c60034218802c0c00141d4036400106c0d00309800700118180c160507901100000d2050010050806200060005582e504031002c3d02d4420300d400c0075220f0008400e40f040100c68194114500074000c100011700000303006204030719000d07004404490419a0560759a800c43d8140901514500443d03c208030340e45074100000e00d02581402100507107101c01c06521240c034010318400b41c0c480c50b0500314280e0050310400503100010251a401d100f162020b0900d0030081421140c203540140c2040001140b03031010340501d03103142030183d480303c00aaa600c0100f0107402c8000e0a85a8448000c0301c1801801c07103420071070a0140e0051500160303062030f5241661501945030301810901c041400100043d84480341900c2c100d803c240803480300f03942c1e641d002070400b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 98102832 1250 98101582 98101589
    0x91a0a110c0703030e01080403020309011b050604051f02040302060d0b04140106090801051b0904090201030219030204091a10030e0106120f06060b2a010b060313050106050105030c030106030b0a 85
    0x845000c65464501c4400007011002c80b402030700c03040801c0000344011205d84c5411140070b40564010000e40001e035104022880000d1002400f00d02200e0039580c9079810404280e13000d484543c03082c2c518214241071740540d07002580a12004502d850314540c00b003070a0f8040c00f00d139090f020f6600c45120185841e2078200c001d442c5064108459550307140c08000e005005503000b40103031503107490005030030400c45019a42d107954100010a0030304081c2c004000181440400c101d0415800780464401941e0588190b1040440d40d100540c4035401c01113000c04552404aa40c0410062a0b000100544602141c94603803001850041407100140b0485400342034103030b100e54806076140303081800b4003112404940c0b0041c0301d444140310003030f900c014818103400303440d40d640700c075008240404076400004440c0345031801125001041c00c02020b00011442d410480d40b00f0310baa003005c3c3ca07520811000f84509400f81c6801d0070400c1c1142083e122014050005000b0031040c160381d0a680c080c00c1d41c03100c0090004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 98104082 1250 98102832 98102861
    0x20d1a07050c1f0204050d0308150a05010903080d09080f0c0f0d0507030c050312010303030b0f100203032802030103110109060203040b0306060703200d03060815040b19060902040315091a0a 83
    0xc1986071400912400084500d01c0348ad012100c1a81c2d214903103181140c04032401655888403682c01c5031a0451650304c0780302d80000c420341d1440c10f04009004000907080c0741901d0307604142c885000c24869410300a034808050900d4200c000e40390242da81020585600542503c1c2550200c0c05074a42145103200702c403042286800031200000c109503144d085030750030042c150307400e04040c1400300600100e00d664036651b1015030014400543d1180c5c602c2c0c030450881141150448031200c140c1c1a5600b207070b2003a001624215060306d1050700c2540c004011100801da54401145042d15110350310180340800ba10151050301d0008400c0140351084141100a00401c1070301070581c814107200310380d00e05202d0920404a414107000080e807200c049040300e0b918524000a0a10741d03581c2c0d4504481d08801800c08033b10042c40340f00310309010061300c02c000203400684801a6901e0444c14040708030140800100c09460804c02301d14001924503d40c000d151044108040450301c1e4a440c0101404180403200c25 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 98105332 1250 98104082 98104099
    0x70e070903150f27030305060103150e010509010b030c0d1109040f0509161802070303110309060405100b061215040905060a05130f11010903020d1a07050c1f020405 72
    0x100d400e803d40c010072011041e4070040042e14000361814210401c000d400e4250f910080b0408808070740244c00443e80076005240c00036814a01000f40d8908503202e402c9a8061100c0390010305c41c03814020b02d000c2c05000500d003030a0552500038100b4030144111803903900c815840b140c40c000560010f00c20b0324040800180140603010030020038400600084078090990300c5034042154040b040141500180d588415a901c030403040c2200c054040e50010f1021001c0607036030701c0c0026105102d9030241d8010007508001d0b00b440c1c00e180c180030745030a0ba0f9146040056280020340080ca0342c810f07007201c19070380c851100580d86a0700c03440e6100e049540200c8031600300341406070390410803002058852240c04040c40c10007440d2030f18904411411184c150082c120300032070f4103940c04100c03070030104c6640d42e205141450490791240d012612040800b4011107249807651132031450074000f4a400c0703a101c40341307161585c2490784100760f05a417154061800e08800b400034a00311060f1000740c0486000d040041c0181c3c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 98106582 1250 98105332 98105363
    0x1503080d140906090c01080106020d030e030409061d0f01140103050907080105010f0303080c18120f030f0403050c03060f0a150902130302100305060603010314031210140301050108070e070903 84
    0x1070701c408089071612080d00505e0320b161141c1d0b010303074800340c1070b5001e950051460403e07180041e00100300b1492070300e540d44024840080c1e000818060385000c0d01c2d041e902c52440c15140c1c01e4120103c800542031510644c190001800184500400d5170040c00c02460049082d031212590f503822b06106400482c41c1d542804004030f16948042c400304200d0b44030341d80380c04450f42e441e00215520302841e1001552060b030f4900031001460215100425140d44000741c48014140034049842d552110a01e010211000f150800500800b400310032003003101074028084034503080e4105940403800a2811603c69980c80410f07032526103810701400500b80903201155904401c5802a1180b1483c0c8401c0344101500c001050342e082c0f01e400703003034040e06003e0301c1541164290781d164640305000140c0c060140c4018092440340c07440445943d40510880c01d003140c81103081504000c1d4404a14410b107002e0f80c108001003000b810700190410403070796000321550150b154010100c682004550000d0850000c4c1c15044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 98107832 1250 98106582 98106601
    0x105071b030c050316050603040303110d061206110c060403030e0a0503030103060218011d060d090b0a0e06010504090819020705060f030601120c08060f0a05040f0902090a1503080d14 80
    0x30b015075000314121001080d00209944034242c070b41c01140d80000341400860700003800f0350042401e250607511560700b880c03902e90442045407640c0d8010008010410910400c0c054240300f1801140c44e2040b00528103221454903039078900300504000c040560743c8a00f200840341c01e100092140b603018060320b589580da41407410180d00540c03e40041400103110805503580200c102c0054601607041c1e460714044200c0401265410040300810080d4940c0c1d0322200040c017003081c40d882946607050000e03140040c0409649020016007207107015a1412015201080840d0709603007145440040001c08001851400c81c00d00000340d000d1500450086148110082c042d009148101d50a90f80c216041100a10510a8500c140704050204d10110f02155a41c103280c0b03d021400007024220704505992000070400711450048e442100e80e81e94003020003107103041c0032101d030800b00782c4000340f01c5000c1d0101070b0005201c1a110041100100166131071103004c840d0400c1801c0c008000c211300f076616000282 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 98109082 1250 98107832 98107853
    0x20c01020a05071a1605070503390610050409020303041e031103030f04060810150c1a090705060304060b03010213240f0c030c02030109121403150105071b03 69
    0x111840705911143c0e550280e244d00c5002d1103094041c51140c4102c400039001c1e00c0941c001882900c0ca8042080001c10700403115080d0004100103901d40410b14000b00c6500c5000e000100524000741c00c03c07400d00150010883c070a00075540d04580001e001105c1e88006032440c0b049070b0004402e0780c129241d10b052007090142c3c1e5000c90340151481ca0009d030343c402c10540ca03841406004038a8070700c14001030180318172a05402e075200c206c80580c80800c90711013248203141500ba0032641c000811180f8580200701c1c510550600307280c440881c0200508159192030b844a8540c060f42d4000c083c08400a014040503400c41a40500060002c40d995601c0c1c0c42c0b501d8401c000ca00035441211900c8190098800714106401d00d4802c050742c6031010100505030445010a100e0030540c10040c40d20880009680c0a120318a6114400d00e208108100010340103003540b00417505a0415603001d108000854518058010324001d091030320303d5540c6201d20304039555001c12103c0c002170f041854404010440402003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 98110332 1250 98109082 98109097
    0x1206050415020f250c08060a06050d11060c03040308040e34080709050306090c0a0b13050f120105270703020f090a020708191d031f020c01020a05 64
    0x81140c0c80c54240c1510164402d801c3c0010001c1410808001d80451501010f4599214080b00715a11040d6407218804540300d500008160342100d814444001d80301d200ba40003c19007a1500e540164441d02c414001c00440030b9080c1c000c050014200b01404c005108440c0a1035000c0c803c00d403619210048c000c200070742100c50180305c1d41f048000c20025645607101c40100900400c600041d010040070454401101401034400d0010510000c11159418800340e449080c8410041000f10100810800c41000d168000108100b04006180400034003001110a440782074070300781505038036080400c14110540701c80c400e82d5443d0005000c00d00000740c011907035824554540e04015402401c05c16210400c5100c0203500201351940c0e00403d04090380340c03540c0103a030004018140540342e242c4400d268071028440320030920000c084002540c014500c900c6031000645540e40300642003011a80c1c0b00c8100c54030f828125000c410000d505082a0100c507640291940259128070307900a003e00140c20505 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 98111582 1250 98110332 98110343
    0x2070302010906050f19020c040c030b040b0604080d0813020a03050615041104090509030705030310060f0c1505060a0b0c03070c050409030c02101101090b090d020606030706050c0712060504 83
    0x8100042c2640701e042620000a11500317902c0c40d040c0784075a1007841d143e03d00307900c0c03055018181038000ca80d0b80324071800c034000986490215402503804204011914104812031003428240414070150707200080011002c01141400c42c8a81c03100200351401c1c01c1d201400a61101803014080100300d400f155450180c1c3c01c1c00e94001e0512a072604100c142ca500720b51150959070184070400400c0f0098000b10b401c00c1c40001a20328000035038a0386411540b00321a144012200507a08101640e407043d00b0001d212268030781074503028100d1380d5228806041c00540302c00305483c1e8001c900c5507502c041841d4018844e01b1000d03036031081c8807044191240c00203030094602000e0800d001465041a010310000f8951680c1d4081c5c0b56159070b4200307c07041500b82e400307800b00150a00b00c0b80044e6400d06c9010748a9000b04144019441d05d061107a103031598000414085400a400707125490728001440c1d030a44140b420055291500036094618161a031742c40082e9801004610000340141c9901140c00b40c1c6c0110f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 98112832 1250 98111582 98111597
    0x1080307030540080f0106080c010309020a05040905010c020706080708130201051b070503011107020603060d15020706060e090a0302071a0d0515030d05390d020c0a090c051e190207030201 82
    0x807641e908840c0340c1e108e0600300340c01600080300c0940c07003a8026041d65200800345a40d06480d24045011a4030320b08007103401c0c1e95555603504003540c0400c1040c000f000f42d8940f01e8000d10b0300a41c000c0c10385401030300040c08100b038440da803811a0700440544a18038950441000002c20040c0c40c184d480300b1500c56039019520f040e0840004100c031360126004641c01403d0302c0d1840c6c40b081c1c213000390106c0144058400b6a41013408078801c01c101c0c0000c244a80c0111004514a8204000c07144041c01c081d001e200700d5880020400002500420243c1c1101c86048982c5181702c5001c00c0c4901751301c540c2256051031850700d420016004111723000340454201c01d80031102090030b042c1c000d032594400e1301151900c3c01d0006501c40c4000500b00d0034806c240c08070450b602030f40d00d18050b40300c1c90654165a12005038102d140e140c495803d00910311002000000300030300c42d00159240c0904581304030440e6160384c964455086d1100d54000c01265900c0d006101c01c461a426007e00081d200c81e5075020890000300c20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 98114082 1250 98112832 98112853
    0xc07150b0310050a063201020f070b0306010f030b13091410061e0308030109050a0f02310b0912010603170307080c09090112050a061508060108030703054008 69
    0x350568080004803071b06283d22900c003090049402010005042c0c1103200c0c80c1e2604444082c240819401001428200d03502d90030600d001501c810301c0c0011240c1090326009a19110390788d400501c2c100d191100a0015000259040000b61b0a001000c091118814100038080010380790b405442101c07038103545030070f84603d244e0324000d80131040d10018201d00410300c0140101c0b81194000390f00159140c000103038180b0307990460f0040e41c2003107080944c03154484066289140b1159004102da05515042d210118200307032420842c0c2c0a8005840d014849520403044002000d41c402c1d40515002005800410000d01d8209869071084600302d001885141c007141d10409000141d40c100c200040c066442c603800e0480b440c10001c0d54000035030702c6101d1019000040740d900d20a01c080c8142c003111100f002410030f01010f20303200040e4003071030990f4010402c44003c80d80c00320940d0001d550503040d941013000c80c007030030940035405514625002c102c1c5202050700d40320712090070000c80b011b11080d1015000c1d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 98115332 1250 98114082 98114099
    0x70c0504090f21030e0c060a081302030a080309010e01150902090a170a020310050103020f060c2104050a06051611060c0d03020304110f0a0501080c0d0524090c07150b0310050a06 78
    0x246c1c41400c6400c01001e00c48000101d02800855900800c42c0d2000d17040c05103942c001a02c0c1400c40c20041d2080c00c2c0010512107800b0081c0141810364094030000e0220801400c0780041858191045490503079010946070042c2da66404003400034803510a4032a086090110b2083c0c541201e00350491203403254032004400b03140c090103114101d03500240340d81108450032042c018564021101007096000f0043c0c030464109070740013480310301600d410300d00c5d4681d82444148090041550440018000700b48000990380e2100741c140040668401d17000d899201c0718001051140c0141050fa080d117010382c00c50780c5034030340d45070f4040c0d440740b4040c01c03115400005c41014801c1d0203d2154486c0e030422100d840c03c1c4200d5008840d070325007147c4864010b41c03800b588178402c1c2e0103d80040c1c0f580380810141c0881020f4104945030104102d807000c0790794260f68140035107036110b28401c3c6800107003c0e01010800f0308041d00c01e980f1030a03020754058203a404140c460901a0001d000886c2c01481043c0b400c0c801040820 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 98116582 1250 98115332 98115343
    0x10606080906071407060510031403040b0915040807030f020405010506091e0307080d17071e1b0b130203070e090d0503101e030b0903070c0504090f21030e 68
    0x10404006820280c0f10000121401c5800349540c01c180d030403c0082c1000244e440c410b0510030407109150501c0507045150604400e044c1901c04441688140f00034400780c100001150400c8200300d5088040b89000b00f0f0342c0c00540135980c0300f04068046c10038000140101130603003c03149442160100f0083e070b2181d04000e407901400c2444c5402440e061080c041c05601980440601030008044038849640c4000041c94030421100303680000341d6000c01c5c10250320003101829041f500f50f0410045d118003088603810075005c845041c60030400441b001000e02c801003032090540c1a00100d0324001c1e4580184084503442d45c2c141300b24080d1080000004400c0c8412a00d01d010310a0340002e001080642101160183c00c060040640402c01040c001041468440152900e4070041e841494083c0b442c1070201c0a1300004054610301e800c2000480001492010403000340e800c200c80004000505003040b00040380e540800411042590518005000b000c03130300f41c95211080c1c0d40070f0200820540700ca54884 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 98117832 1250 98116582 98116591
    0x3030118060f03020f0103090212010605180105090c0a17010b07031205010501050306190b0408060601120b01090e0903191e05070b0a0203071214070e06030402030706110309030102120901060608 85
    0x2114400b100f40010f14000000ca94000e805146c081503011b241d0700000e200483c1a412123486070340d590742c1000181008520a022403030440e040c40d94039803521011411170800144443d901e1040028443e01e070b00c1c010040d0b404c40404c013140300c00180d0b8441d01446040da002c81001d9020a020204604012281e80100c5060329810307520f45085443d03203028007080f106c45009503444e01c180d8034030101d848905007001c0c10003400203400901d800e050010000d484904904040c40c492820565080c1ea2640c00c80410011101c440c10901040c0d51803030741d82800c40c01820400e404110b01c2d000030120003035002255115810140d4144121440451003e070380d2031043e0341d001005944d40c8000078003160300360341c003031540440142044009a8001d1504004645400f0010410381d00b000301070181c07096003c2001090a1020356015285003015000241d9501039403007a4020071175900c43d1240f070a10300f4001d035003060328081c000750344812848141c1840e50b0000c4070745c04000e41c608440010010b10420005004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 98119082 1250 98117832 98117849
    0x30f080c0304110108060111030c0304090e07240e120705040509030a0c140f070e01080c0901080318041b0305010918030530011205060f27150106020303011806 70
    0x3c8040490040d50405030042c070490601448040031500310405200810b060a0a00095603813241000c6c440400c4600f16490000c0b264000a81031000d090400662282141c82c52151090304910603000c403402c1040c500c50b581c02002e03a680101400c0d030005407400645204940600c059901c0d860690ba0300d00405242d000007654040e8401c011070f0030081014800d501e0101a81c0c49640010295803604a150384203014000c0a40010400c0400500000483e14000c5499000325450440705c3c1e560b078020044120809004140030707030300c5542d070b41e0700095140d032284596000240c0301c90302c040d0040c80700748101401c0505080d00c106c4100c0908020a45403903054a469003484500c916050010030a66250135155000955840e5410700c40e1251500030222135546d948080c2981c81d2580c10650080d140d80e244813261703c1030101044807210b006a4401c6900010320380c940c9a111a1450b000d80c840c03040343c00b9000d290002c02c2103580400194143d460b1364400070094006007030424110340040c4240c944 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 98120332 1250 98119082 98119103
    0x40302041407080c03071d03070e0f04030315030b010608062d0108011202090408070317161107060503010b0c010b10020a0212060712050a02091003051501050403050c0d05031204030f080c0304 84
    0xc14820551f1074070400b00014040b00c921b140c4400140c801c0c800180d40251a04615604100415516014030b46004011020f0b680400349980c0e540d0f83d11040600850b4244141c000c0010095100c1c00d10502d15040c440300101c610b104d0211f50407101c4c10010702150b0000300b02d03400209003446c00c003461849007613010b00402c982d0307a40d17a200c100e165005181c08404000054000f001e8032001ca1101038000c442c1032107038484031204160f01500008000380c0e8105250402e4108000c83c641003829a4111001c0d026455a911240c1d90b0b0035004217114280d81c1da00005606900c180ba9600180500d641c0c6d100361813025091308041c0d15280d40d11021a00c2d0320001c1c2c0741e40d01402e000310242d0030090300f0208403840541003152620011f00c8840c14031484000080da40e100b0061009104203682213100c0c000c1c20914546800c1d91206030702d450950306070078000c2c0540c14450381049000c1044400c4442046030418980c281403900030020344000ca1004002082040860b0001e1000b03012203020740d074804090309 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 98121582 1250 98120332 98120357
    0x203030904021605070e060a060815040b01030b040f0b03011116030c030c020303070f060f2a05040b0304050d1e050a030911060703021c020a0201080c0f040302041407080c0307 77
    0x1002e9800350801c01900141c41030034900207602040b4041c00b030300c1d0034010300201c0e01d032031001e0007070800659020008000520040c8080780355035040000e09410242c07408100008541e0058015000d03441c00c454004d86000802001c002450b440710080e940120024094500a00c503440c440c0d00030a00504039010707819250380002406000d000c001c0394440d040c0b4999402840d000070b07003140c010010648503801805551410001644640e0a0444002e141046009011fa40d170550640051054407103003400c03203040b22400f502920035500200710280d0660780d249801d00d8800c1d101c9510300e103d04081b600e540d96000d49004440300100c440b04041da5001d040040242d0110080e107644d0005031405601031600b2011a11070400402c04903009800500d00031004600b205461200c0100030400c5400c61900900141c0c0d2000b00140c000d40c1050410f600e030b1340607072b02c0c80c0814402c950009520a203800611580b03581c0340f40102d0700c50341d12519205030f590344007022400b075071004940e40c43c0007414107003500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 98122832 1250 98121582 98121589
    0x504020a1415071707060b100801060f140d150320060913060816050906060a20070815070e01111911060706060f15020606010806011205070e180402030309 68
    0x10322901e80510380b829600c048134030303840250780d0114500b0740300c0d0360b00c3e9448451541400981d101c4030220320300d04640d1540c07404400070700f8030306540910010030100c80340ca81e01e0044081c00780d426104050700101715040b45600d5021b1400c03070745d10084802c1420340c4541c2002845480380d680c4240c2000d001e95251059810802c0044042c44041240250f0b88107802f00d1800410484002461240070f40c018902c1e08103000c204195500402c03062141c035040041c0b84140380d1180302d04082c404c80c9805008042001080c6a00f820f03001c3e005110180301c0c04000e65405100c00101c40d004282c20344400440300046001103541e000400707400c20f44c41e80882035038204020640106101c25008120356a40000c403000015007070b41c00800e06880c05131f01c6601c20700c03820034010b03000002000344039052034000c3c640d02006500c0360f2000704011b0501031180d000540d1a4000c04100e50741000302030040000f85003900c00540950344900c12140104c1d1640741c44500303040c01d60f00013402030303400500a5080801c840100b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 98124082 1250 98122832 98122837
    0x307050a0302120c03100e0415020a0c140d0f0509030703111c0606030215031003030c030c0f0501061406120c030403030204080a1203050a02070b1605040b0d0504020a1415 75
    0x1400c20941c0c2000003102c481c001041160180e0003a00680f9600c0c14407010f80070700040d07140c004054001c140340034480001d034a02010342480039504e00c00743e22842c1c078071010750f120140441e004c2c000d0311540520659910300480e541c100b21005440d85401c13940405011500c03805214000c44e015449900140041490344d40c01c002c01d845d0003850300c41d0f207040100c00016985a10300044030720341d0700d4840500440c40c0402240d40f040414020341811460280c00a004940c050302c40a0144007010103901e051610030398282004680203450340d038003c49903140250091010307114407050680e40e118075030a43d1070008211590740c43c502c840b4070202d444480300034000d6880a401202410350801c8005100e1100344540c2e5066401812084802d4400301c0300941501c00080002400301d20402058000580c6041220b8011003030004d00e51000550003030030340e10b9110f43d42001a2400c40443c51500d030101941005104901c00d84080c000ca65445083c1401d8206690066522030300c580b40c82a401d0030031001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 98125332 1250 98124082 98124097
    0x1b05090a05090316030203090a0504090b04060903050f1815030106020a240603050f06010e01031707020f0a080a0309080a0506220b01030303020304060e0615010c05030d0e06010e0703020f030705 85
    0x196071920f1080d18070404c0168510f1011000345c0c00c0481c020b440d0349800b900c0f100041900340c4003401030071034503558a86540c80007800100400c0d954044802454440c0068480c502001e101490740d4490076100083ca00b815984001d205c3c5414404d040d14021000d01601c0c100c3d0019001000c880c01c01c1c0c0d841d220480035060000e02c56000310074110088840c903018090042d03000b4805480741d8540c00d40d415003000300c140c1094809040e84001040001e0000c110741c01454030000e180d0b03441d044c0901c0060712950301220126400103111002152140000c10340884e802c2c8251510103000ea41c030b01c0d40a0b1035510b02000501300d0f42015001404807401080d07880d4680c3c682c0040c0080030040d60344d81a803c54000e03003081e0002603000c001c1108014451040c4d44400f107404000b440c06292884040c00200707103200711130b8100f00b00c200d80e400c06c0200410548d4a1141501014401d00c26a034030b40c035513101802d100e040c000c184142c0106400c207003e4401c031004544560403070391940d40c60201c1556943d01020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 98126582 1250 98125332 98125351
    0x100e0d0204140106030501240504230d0501050618060306010302011b06050c03070801120b0c090f0301060312020c100e0928061a040803070209060402070b010b071b05090a05 76
    0x70880800c2c10610705220f03020341200c1c1c4001a0a50508a01d0038541c0701e040c2c90104c10640080420420301c0c0c121099800b240c84111030307045001940400f54004550b40300c59640c2041d003040c0740500304501074000c0c501c0b40d00242e514030140221884004007020041d1141030705034004100610165104901c5416001c1181c20041c400031215a500001c0314400c07606100f1049010061041e4503500c15005401000c649201c3d0500130216180d071000200302821a6150360f000007103642a80d1504040801420001402000f240e656030510300000340c0403174410401801918410300c0b25140c910001801c510301684c0d5540d0340b0b0300d60f005010340c0340320207406d61064910305800300601505481d01111100b10030500420058079000030b01000c1070006980900c036480a001c02e1043c0980041501c84807501102c000d0313450b495820200c1c000780308020002e06520060301c004622200d0210013403000d64415070030030409841d900380000002509005641d4880400008100455655003103603400c1112103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 98127832 1250 98126582 98126591
    0x40c050405060c03041d0103031b03120b0307080304030f1106030f011a09060412030e01020105010605161a1003140a08090609040e0d020a0c0e060306040f05070302060403030c0203010b100e0d0204 86
    0x294101402203242a15120381b51041000500c10183c1c080920248002c64190907031038403090b0354001d0311040b68010b4801043d40e4849a14005540c1000031070002c0c071480c025280c0d155281d0808442d131101960082c2d0302c03000d8903028507501d803d02d002124419403158050ba01c5603401d14403842180120f52050075141c0200344040c19a9949182c000c2004000c00c01511074880c80d0352802a120500e120055419645001e004010f0503403c042207484060070303501c1d080d901d96424a001c5505034411f0001d010158528420001941360202c200750a9a004e50035032040c944c190b0382042c0d40d4082001001746000800e100783d00540c02c004024003501200100f010514110440c0c03c3c0d49426603150109006900c00300c0c00c201032191103103120010f04045c0c030004049242c1213001c03954500026000400003051985290b0911205020100245500030019039449680f805d00400c0e1840007001a440b95203400ca0906851030404038441c3d0607411621800c082c103581d0010000b00500c68101a600705455 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 98129082 1250 98127832 98127839
    0x302040e0f04120c08040306141515190903060e010507080a090305040522090303270c2c0c0901030608032a0c031c0801050a0602030d0228021b040c050405060c0304 72
    0xa43c01214244500c82e19022450b00e841c0100e82c64010310900500d01480c03001c1c4428a0b59101c2f80d0880c0c450b4101030890340b8628000100032540c00c503040d44084d081e01d1a00180c42c04804c01034000c0360240318169120302c40b5441d003d030301e20212030004c880140454803c01080182e41010503103400646240066801d00d0500c109410003607078088501140020361303a680c8546500000d2081c1d0243d20b50b80343d110701c01079001742d544817101503403405482403590300d04800b0f07110020032010003840d4010480d2a002d490070305114035141c680052483c1400719040c1180401c135240004280c56001c00840a01a920a0310294104000c82c0011188540d40075481e0b980c10315031402c11841011504681d40d9a9021141d100000c00940c410380016214001c01101002096400070a46801c0d01300424010b0ba980d410001505001440402101e000200801320120b030030740114175406a40c2c040f0f003030054a060742d80100022640c021141d5404a03009200500440c2001e4018003e090402c6082f40c1ca060746 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 98130332 1250 98129082 98129093
    0x1030603120905131401050d02030f10050108120a05120406020c070305102301060f0e04140a05010902090d170c16030c0b07030c0809010c02100302040e0f04120c080403 74
    0x70942086011a01418003042941400000e40380018210b8000300280c4006041170701084506102c1d40f88180c421308607107402c0d59014407102030040c403007030b080b10b401107810110704000c1c0034244030304807640c004c1030b442201c0030032007900704d03800401c0c00d1782d070240f900d040d02e0880016804c02520541d45141d0078407003a022908100b01c2074010b5070142008160030ba80b41c0c0d441d501500d00041b17603030005040d040303081a02144484a030343d043d01d55a00b442d14019120460841c0c2c40c12120500340c1e071007420310b516443c0c88070b000340c80c0c5405241c110009004036030b00d174111441030784541c00c640ba412a00a2960401060b207103103a070349200140c249500c0c50082c00211082c6000100400149410075032002002000a9000007100a1488584690405000c0c0d100502550190720000d400010000350300ca41c140e01c281513003100b0b540c0c01883e0522240d08100020b00075001801a820fa000e1681c010901d84480690500d114a6214040c0c1c43c05480121003254410301400e030807960500140800b00c0040c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 98131582 1250 98130332 98130353
    0xa0824040f0e120a1b06020705061302100206062412010f150216050f03010e0708010213050a03050a0311030f070609030314040b0c0a0908030c0a0203010c02030a170601030603 77
    0x74520103020608042001c0142d003003400500c4420342100040125200ca903400c03511015a002e44c1028420b119085801c0a41c040e105242c4000e10751300415081040071200184078014407402030b12240000c103002641070713035030300030a4a9551303004059401d062200c0020500b0865040502c040803800c1542030b0700300c0e00f5440740a070001c04407440709540500524030201030110b0440e1403807004120b411003d007a412071458260140740d00820303031860001e4946d1400d401c0300b01583c8c040c4040b122500da403a200039000f5000010320380c3c83c4e491200d5001415250803001c0006507600311000d04848009560709440010002d4588a2240401c0c05420144207000c4068185d82c2d01506001c030b41000a032400134200c0713079000004680f21000708188030101d5041a9000d900c2124604519039500c41e940060781c5e056156405200c1601c40051020814480412841c001510031740c002e0001074407481d000d91316401503005032400501c00e14149001e011b588412550410010b043c0042c84640320b0311000c3c00b68 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 98132832 1250 98131582 98131601
    0xb090c0a120b060603010605041a25150c39030e0306010e131103010605031605150403080f03220812090106050604030209060a2c0c0a082404 62
    0x41d009007050a0500240426080d40b10004032460740c50b641c14010041c0c200d0181d070143c041400b00400c001000d240a1004490010140645007000380842c011040c1103540b001100b11803850120b0000c001011503400b880011750ba981d214100c40d0f0000101d850208020302130021410b0482a000f9420000b0000c4500101c9019541d030f440301481c1c1c3c409051401c0b0069100b14805280c15040111100c03a800c110b039030340b41c0d001e400c08111042400c0040d0142080f5040303a83d05002c0e4804e0f040019080c0328140b0b084030810345000c0d55500b21400c16050601491002803c1e1510400c0a040d156080b48021030f4004078a05107410340300074058070100c4007404040103e803405d80000740044102c03036040c200da42c0711207117400a00c030349400c02e40415031038015840024060744403c00401c58658400212101400c41c414848078a0440a030306400d030b0207607048640440b64000c00c0440e2520b025281140d48001072500c4500c019116000d10701d4001c00a1682040c0244200040c004a659640a00c0742403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 98134082 1250 98132832 98132849
    0x90406030309140901050d03080714030a0e010b03150c07050f010c030902031506010f0302070302030f16030807022e0905150603010e07050a031416030305040e010618030b090c0a 78
    0xc0d07905040d0110182c01c01c43c00c42a104046110040000d5501c0d40003205805034585091016a05c8410b4203483c16030840c844902112004400c024040e0401d5100383c1c10740392003c00030b110500482080c1600e4551a1807680ca004841300c00080960300c02800030041d861203038046030389c44c01d450b0300c226084842600c510301c002602d5041ca9401c0d8030b000c100d0000c801000d2403140105062500028041c4124a0500b400345900850100c061500074001c1e240706070544400996141d01c504500c4038000c1c14040200d000c14842c0010620052000540115050f0b0320100c0c1000d03152942111034994a440c118a44801e44030382c07144c0002041400001d03001010400104036a05240e0109825a071802d0928462507102c50000c000c03680d90481c01d03c01b180e400c0844010210310040b41c0c14100b660441c941e8180f440302000000c1010f42c400c00074001c40308080c040340e0441c0d1b250750b01200c03440003100510f1403d400d0711405001250704049440e800000402c1151606650200418000e41342a0302200c0c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 98135332 1250 98134082 98134097
    0x306010305010e07090509133002030301080606010309060b10200f060606160b04081e040b07141e030c010f0c120507020a0209180d0203040f030303110904060303 71
    0x145940c00d8000c890250012586500c0d1514012400809018040c0301c0d084c4101440008141d10071aa10025034a6541080d00703845801d00d0720311181c1801c2514025604c420b01204c440c80c41042c4040705581c1a02c501c00007810047c0c80d100b004502519000000b43c640075a0750b01d805901c1d076124198504500300f00c4e01c9480754105500b0102c00640c001c100c51101d150021000c101031000d003c02c82541c000c82c201c4080e84c1300e00400100c2c00301701d0070300c0000600c141e0004003840107000030280540120b00c003803c8440381c046108820b04007240200d118180018609002c0c107000a00948003015203045150111406800303100c4074100b140103892035003c804d80001442d035201a200303005a44000300388007818004d030070070035100504524114000e0005035580d0000304422314030920542010744d800411086030f80c2400c0700007014105800c00009003910901606040311030003c4152030440349580b038402c2c0001d2079a1000e40207440007240c00300e0400020006c140782603480c0d2080d18042d40c0240c1d80c512 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 98136582 1250 98135332 98135341
    0x60f080d0306050102030a0c0602030c0903121c090b0a1a09100509090106050a17010f090614060904032102090a0b09030d030603020a030602070f02030a12021e28120503 74
    0x1402c40321542c1042e41190020006044411b400c81080000300d5400080140c2e030340c0c2c50300c4140f20300c1e00030540c4c83e9a15003e9104540601c0c00c2141c0038001801541c0c00c01041c1c400701c01101c40071a90395210007071000d42410001030f006035140c0d0080000c04900503100810610b060001024110b088401c48200444c000c014007040c2441d0748015408100707400200422820b00c000540c0c0c100e0988940700e400b00b0034211402d403c0d2001e4210b400c00d40786500302404141c045290140103031a8080686c000011b0340c20002d4414940500c6c003c1c0102d815484d0b80d510306803206004001810311903a400d88140d001c02c5840c407292141240d4800800654000135101c2c0c0c1000101804c142500040f2010142000e00c00d00141c0e80c1d0f00b00c110121780c3e1000d0016039071895071400300b48440205501079130500403074040605108106120300c501c91019401d03540c484221003030322050554002c0100d03546074402d1508158003030111310140840c0b200d0034095480300c40140d03181e00c8101c2500c294140064408010300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 98137832 1250 98136582 98136587
    0x1202030c010e0f03090402090d050303070905040f0212040308180708060106090806070e100e19060206070201090309050f0609030307080423030615060c0d0507110604120f06060f080d 80
    0x100c011600c0014040c00c25008403e141d5170b00404c0794151155500040081d56540d41851421410758044142c903101c1c0350040014125100c0c500c5214001c0d801d2810740301e035100b0705208581100080140b0b04180d0348803614210b61400340107201c6c9101c5110050000c0c0d4041c0108042c50041003607000500c1c40c1c2d8180a4020613414155011010b035030700503803c0c055200c1d00306940300326070302050301c24401000c0350410440703210841c141d465400807100d40c0ca0700d800400700c40c800c1e01035030040d4007240c030f40380c444400c200d080b20208000900011002d0005203d68584040075048010b001014a4180b102000002e4116408030300116111240001c04120b02c050211609600386500ea40d003449051106000c00e8580740018040d040c4400c90746020b00e016502c0e40240c61000359403400712891040ba4000240c49540802740c15105114520207900310342c83c058080710305071240c00c00d9040c100c00d207994521130f45d041d0b6168100d5203152200ca021642000801001008000c42c400031700006c00c816501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 98139082 1250 98137832 98137841
    0x60f020903031c0e0627121b010e06150d080405091003060c050a050319060801021602030705040207051507050909130b0a110301060509030304030215041a120403080a091202030c01 79
    0x1300080c3c102104020845100180c080180c40800294900c909200641942024001e4915086061002c6252a908400e00d5042510f5000e113000130880c0a203c121001d80d228802c84400300a103500b04ca461540d03003009807246640354803c0c4407282c00e040c0c239000000c03042c140c101d440d2a035003c03107001c04006000550141320100881410b150340ba0814044000b44984001004203c0444103c42d515640000c030b903000400820b09880215281c2e408941205071503030310801c044e80700348180c0c10045030030b2419100301d41c2c0c4640d100e8024a410b208840040d2141c20006148105005060001801d00d854640680b0300c07a0500c00c07185400d5000c0703490100041c482c003178240c1c0803071840d0010b1901c501602c41d040364155801424115125400000041d02e14400c6400003074100c84400c418618501d0104080d000782d4006440b01c5013016000348a003616400b0f1410841c2c451269100820702003030041807125008006c01802003001c2c40c1c4c5494110009514012880c01a80001540162036200313118 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 98140332 1250 98139082 98139101
    0x14120405061b0d02160203120307111c0804020105070b01090902151c0509031c0606020708030c06010501030213030b27010902030c10180602010605040b0906060304060f020903031c 79
    0xc88203001c07010035001a16000b000d070f414000b690b0020303102d90284596000514250740c010304039060340300b000c1304d002d8503a0415601c43d40401d180f03000c950340b04040030411141c1c030b10120b030500c24803400080e001c0b5202d440246c801d9040c41401c10100001c10207515106000c0c0c19009001b2910750304d0317031060014028803000301c14407280b002e104004011601041e0000d8281d51000f012500c0c2d120344402a040d84210100150003580d44150500130980503001041221805c0e002e4524141d035440d00d880c1c5038803400300282d10316041800140800d601030f901401901e0348640c80114450388030783c0d0703c2e9200c08d030542d82101802120224043e42e5070b6844000445500290001c0c00826010343c003107075503542c269091030310841905501100b00b900c01c60380c000c0c1802c01921803008540c0c0d034900190003440c860040c00d004d5070400892094605018880502401000c1d001516541c2c07241c903600d0080c5103048940d0441902003218917502d9a00f08054460071942c003070b00d01d0810071151010801c0307569554 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 98141582 1250 98140332 98140351
    0xa060302061204020310021c0b090105060304080a0e120309030106061107090e010908030103031806020610230a18050f04080403150b03060f06091e0a020702011412040506 75
    0x440500068a8000070744000e41030030203402d00941c4540c800641804175800c00050118400b241d900384014000044801200105004229208454050104a0100340601c54008030104042400030304c20314001c0c20301000c146003018401e01500001107450940c0685619181d001003000046807a0a110b910014421800d029000e500020500c0b61110054411010040e43c0d0303803a1115090001c1d04405036407940220071a64a603100c1c0b034003a20603500120f10121001c1040004030f034441c0009092409081c0c0c01c501510340324034140351444101c00000505601c140420104030807030b2a1818604043c1610020b1030301c0083c03543c600ca608841004060b0f1009642400c103110214881604403410b4036000400c60f240b40711014050006441881030b2990184115400c005400c45e080454600640c021507504801d9101d144030411030705014225502071901d80d0001c650900040d60040c08210300c18184072298140301d4100e0103098010700c40c012041c0c217208040000700032003408000c1e440520701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 98142832 1250 98141582 98141591
    0x41d07031b03020c0712060606140f07200409150f1e02090a0305030a020a0210030b01080117011103090a030207080307050a110a0504091b0f0e2a0c0a05060a 69
    0x260950038046414140340c81410f500160310003420405000c110043c140c500688400300e001450000000c0445224034000a070f015000101c6402d9800e0480e42c0c0e91000d04111800c006040d21104441c4181280b801e085a10302050701200340c031103005400b145405860b205c0c002c07500003121201514018103d0145e01d034a410740f068200006e040350040c16044801005071502c80725404103074003e030751781c0001d80580320200d0038256040d400203018460920035a015003407013944c02c1042c5c05495441c020580404c540200502001e0000c680d182c4c80b04801d04000310342c86003903c021072600c0d40140c4072070f001900b011045000b8590108040002030080c0402540390000c10f03100d80752a0a85c0355002400000e041c900359419660f00e402c044060700c4001e10400000c12a40341c144002025110707040d0094007940c07400500c0e6504080d400c0212000d031200c1e02143c1d980c00d0314424410031042504581201040400841030582c84050402600054010081128142001c5161034002801f5010742c81c1003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 98144082 1250 98142832 98142851
    0x60e07060206010e060f030709051b0906120405030912010504050c0105030702030a11030403020a090b120105060f0904021306030b0703050a1a04150b130e1008060c0307090b041d0703 80
    0x41d40504440b40c0070b5107951301e5140c80d000a980c0f404480809507041c0f03c0c0744e2011800302c100b644030a00035140c0c0d5404080d5002030001160f49030003200b1030254010002d00c180c2c45400510085c1c0c55010f4460030076030740f404141c500042d800b40c08402c0106407984d551001c10041000070050040c2022090900701d0a61501c40300007036507840741c0c8454174200141e1008003503103940200701b83e0b0083c550060540d80c03469121914074000700154a4810b128070b07104100c0524000c3c0605c50315010702c5001d081000c80c815903000340304408901400c22a0003000c221280d4140000c14868080a10b02c58007a056450601c14001800d40d40040d0100119524041d100b00202c2ea85280203034034610f044e0380124400e2031003600c92007030303074601e82c045011044009004546240300c0305520f003d071404980203900c83d4a9000074000d514806000320a0a5401140860422411100078503409030091803c0d01289480e2045d2140a40055201c604104008403800081c0664500e0050703001c203103458100070302c606 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 98145332 1250 98144082 98144087
    0xc131a0403140a2103050601030b09010614040902030c040303020d020102090901121a0a020c1011040605070203120a0e09060108060919020d05010f090507180b030a02160f060e0706 79
    0x80c03884010102d0303000d596010111403041c05400c2c82d298108030b900842c01300400960307202082d40c00c1350f04c0c0002d1800d40040e290350300910464420300c07406403129085a08000040d5120b0100c000c1c407010300c1c80140400222500c039400150302c240d0189184544980c51494041c2c07034514111210700941e401844030500356100c8041007411118001c0c4011080c4400b0300703003015103031020b4035907416895000040101d8084c2680040a420386510201c81440740e0001d0840116141c990260f40303204c408110801620344901d000d4904580010f0988443c00c406080700300340d40e4420640800400d41c11719030580f8615004071101d50001d02802e01c42396915064002540600c0700911181c124950030508120442260b070603615a185005010042540c403030201203103030341040c03150301c0c0014145800070f074545100d002000720000c00c0e13910468480341008850300880e04010641110b0a900340f2100050040110030740d015540110290a0082010304096098504924100e03a4580c0284420800c166 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 98146582 1250 98145332 98145337
    0xe0d0f030503060103090f030c11010f020c150f030405070e0f0405030a0f02160308030906010602030405010203250b0c21090c040e0106050306070906020115060f08041a0c131a 77
    0x26418682982d980da40d542c0160020005000c4c0070303041e8004610a0400c043e0449480c1d0036160240c001c90006200c040e00440304080c82d0b05140740140c200404140c1c00b4200300300640c00e038251081507141045220400d0300140d4008840076100c5038443c007410801d5a20b0038804903088a144c000180951400c8c0d00d5250340e9100b175900741c01c1005000042c0c0c40205100740034101e41100d5a190240c0341030750b28102000d40741c00580e001c1d00300740518000010918000011582181c406801942c1850b4940c1c01c44003071843c6803641e80c1c00c7c1c29807105005c40011000ca070346910036082048166114149078100c100d00380c503100800300b0004045010300c500c0080004000803490000c0760f01060802c515059980501180e0344940c2d00740c401c00b0288008550044064019201c3d180c0c001c01000a094140d101e44910324452a8045088045040c034141d01c108840343d4054091011000007040700302400b0000c040468451094031008a002e088000400f41d0000040c03500d6054911061880100c2a0462 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 98147832 1250 98146582 98146613
    0xa02010e09040327080f0d02070605030a0f06061d090105010e040e0a2112090308040b041433010506030f090a150203040c05180406020a090f0f03030e0d 67
    0xc00300c9000140c100340c8200c00c01001520104141c404d10b051041244c56011501e0140a074036009000100b500550005940c8031842850340c0101201c41c0350000c10744090f8001381c0f00b15175160312010b010450f18a14000c0c0c6c00180100c0da034016804002000c190b40c0c002d0351400007481812340f4030040041da03a00000c0d00c42e03101d00484002840c201c41314551460300788e00c91001000000041c401002c3e0001d12440030040c02019290400e03a6a00c409808049030b8682c6402330118083d40c0119010459020240d03900038400d0100402034032070f18207900d2600c11103041180c17100c518601d140d0903000350100034807800a2104a010219414a40060509c0c007000341042000d2000c070340042c5071210b082002007041c41d080081d40d24a030084019030030180d4001c440c160f82c0002183c60000d16070501c5000c000902c514100155038076120781e680c9002a600902220782013120620010600d80310210384c400080c40e1381514001c4540c6586400303001000c100700352500c1401c10a4080022039152074050981 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 98149082 1250 98147832 98147839
    0x1306091d070e060c0f01090b0708010e01080703030c020a1e03140312161403040c05030105011208090f01030605130e0f011e0b010c081c060911180d05010c0f0e01020a02010e 76
    0x168a1000c404a141201c8031002d17007029802c0200040500141000c0e8170301512140c3d44410950707880d024a803405980030f04c02c01c81c03254804242000800d1148216201c0a480200184805590f903a047c164a81c100032040b4124001408204100411460186600b0080e01c0145081141c92034100d0700201000344407288662921412044541c8180241e0003503130340d040c2c17941b5180d0802c2c1c2080300000c415800344a00035031070000003080040d52003400840d100e6006000c1464569040240035404554414845c1490303120300000c14540c0c0c40150024540313003034080024580d00400d030b00b145031081006035070515916290902c442c01824034040480d061243d00c1c0412808001c0c00120fa0803580d1403800b50984402141c144064042d4200e46203000c10200340030b0100580700c81002044880c4280c114002c0c0000308030520310071499404031410850020719a20310031850b6203419081da5609015500040c22221104900c0c1d60881803001d010a020300c001e111413070295001800412070104111b10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 98150332 1250 98149082 98149087
    0x905010c150e0d0818010614040f0f0f0f18020d02150d0203070905040c0311041202010e0301020a0810060903150203180111031b070503040e07051306091d070e06 71
    0x10211240e0400902e400b0b00204558000c91094001419510241c80000b2021401c03c6101c80510050080f00141c41c0031350080441c0b0000c410401008220840341c00003140d840300100440c500340d03841800204401c0c40804102c1d803800008070811038640352003001d22007030842030368805600c0782244d1340203059042d03a590035220820700c040005070240884070202140000108040355900101720300441d0000d803001d1240c03000190080d4180d5800d907d403580f0b400000e00041050842500301010164018103221900c0e9852001090a9170f000c142c1003030100d204502805149003d1840c440010001d41c42c154200c1da080d6a50000c2c03104600f0040202103402001260140d4078000030014010805402003007240350b00200c4a056802c04c80d0118204035134031410f001d240390a201100d440a902c40b010b18030341030500c0390f1840000809010002001414441c4c1c02d00041d461451401900d1070351901e5042070b04c1c121080c0c1c0b46888590f002d442c504e0030b40090001003500100c4102c81d000c001c890705038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 98151582 1250 98150332 98150363
    0x41b4a06070501060b2710260a0624020a03050711030f0a0507090204050a09020307020307081204020901050d050d270608090c1f0c020d0606030302060f06010905010c 73
    0x10610300402101802ca07510b440d01c001061030000008003c4609042c6500c40701c10080d40300b0301c0038501008003090b000614008400d242030310074034099040001400c0700d141d241d080e1403400c0781c0705c072021600e1241a966910050251914400c0c2c021044d030304881a0403580b12400d54001d44800b400c54008003804008110401080300310201007414420207800c4991408078200001d503500c006980540300c5029002011400013014001ca038251b44015285040d0139203000000c40096100801c03032011800144400d2000501c824000c01c07003003107046070f1000d5a081ca401000400780060b0300851041010f1500302c0000340001c55505d100310b006003081050302e28040764000c2001d2902005403c04d035034100703001c1005a0091400381c010003c1104036141d04d036108040c02051402240740030710f00085180382c08941032244020003100c0344080e0070808620b2440c2c0e46d050507141150030481c056045041048068046816841d620443c246840007046140070000f030b01212030603001500041e849100d90 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 98152832 1250 98151582 98151589
    0x180306060a0603022d070b0906070203070f050102040b0403050a030f021516030b040516021203010f1502070305030708030601022e09060e06270607120209041b4a 71
    0x24804404d1000d00340c0c5007800041e100c1780301c2c2d0b2001000700c03400e480803000b00e843c0b000c0000310503104941e80d40045142806c181c40d030a031000c0c44031100f140c1940d000c1001040d407c1ca214042c1c0004c0d4442c10003030240175203070719003e02080d03201c10000d0115480382d8802015a882804074540189142507131014645a640c0b044000d4404070050303541060400702444101c2e6410350f2003c00b06111035003583c1640800d0403c21286200a1080310b1000d84454800e10440044540102009030700340100e909880d580c0d03441d64110340002034245d4200f0008003c1200d1540c040c084600030a41520083e000302d6503014007050b80800d40c1608a9160355140241010010316034420924400f98104590642c07410320343d581040c0010070351400c400c0c180320400d4a500c5100007100b5000d402507403143c2002200c5e9820800081d0405090b4a130301648424801000d002410100d890550300c0780d0390440ca24030783d10002540407500b921001101010300d040b281c142b098a052088207408080007486ca0700c4a100b001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 98154082 1250 98152832 98152867
    0x30613021303080c070609150f1106010602160512070608060a03020411030a0c0816030b211006080c1c0609120e010e0108040b0f040204110f180306060a060302 70
    0x182011942429002c824820480c0150440c001842c04441c000c40d2103207000c8400c950a407207655045030386008071411035405003450f5807005125203000c50b410b0690500191801001ba032003140503803c002806a0b4440c8201c229002402c0c0c140c1d44403402c51800b0040b5559070f51244603032410019004003203803003551003030180d00c001e6170020001e06c441c40034030301504030f5a441a02d40902080c0340614a21410340941a501e11489605485800c4d880d50080e041c1c000e0030341844c150b0340c0b0005034040144a100c1100c0e040200d241c0c03178070003040b0503456815a2011240c1581000a05500805c842741c459950741c010742c82000101c02540000d500c85103801c10281100c43d1004050030060781030440c02c0760f4030290200b00920240d07a000c80e144000f03030040d60019026039001c2c019040603800101806030b103008180d0020310283c0b001500150710282c2c0451900302121108c0c402c0780010f41c40fa180802461400141c8100700e02501d040c0c03c0c100000340c0210b22501c6854241a004501614081d811082 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 98155332 1250 98154082 98154097
    0xa03030914031809010603050709030b0921030402030d110d031a0301020f070b010e0103170705150112050c300c06040906050405090a050c040b030c0406060221090603061302 76
    0x40380d881e1035100e405a04a54210803e031030240c01244c1c00081d640c1d01c40d00034107000b40d0041c0c0b03030304000320b04544804d040c12000800d070a2051051540c9410030149600e0802c42c0c460f07560000381d45a082601c1054203294024030070508106100304900000c100c0400c02400040244c01d00043d141d0090304010084d2003280c0303032654154800b2803400780302410b01380108a80d600ca00c0b50980c081e17032228610040500300b0700019020044180340420504640401044058011404c803100000072035021800300b80260002c1045c0680070584c80d00b080b0040104034104c2604480c8084140c2c0c2401c0c48102000c83e006402203a25881000c1c8030101d80140041022101f02405088e5203a8581682e00050030062061602682c584000100d039010045510342800380c1c448060702c0455154400c22019040c01020a0b41c54010b80340d0385602a1368500c140c800400d110380140c290048600c1c03110000d095281214681c1407070800203450180d850074200d80c1d00902c1220100d400a002c0e9a03030100038001c810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 98156582 1250 98155332 98155373
    0x50108120a030e0f07060f180b0304030c0f080d0f02030906220624140f01050a0509030118030813120804080409050f1501030209090103080313150207021306080a030309 74
    0x320513040e480440c0e0102036910300d455414800a0b00c1d4800ca54018501007a13038400220b22409102c2d401c6520300550700540a841d0202054907141c6070701030f00b144000d40c01c54164500180c810300e000483d0007000200c0030745081c11070840c61304d076803070a8503060000d007104e96244904080d6040810070013069217445800010400000c0d00201d5412655100c0b0040d144611005490000d0005181c00c110081e1450140202c9121b8050300e00545458010000301014000c0c1400480120748017481001c200d40c2c009180c6819a21160030b002d09510b2000d0403100a03101c0810805020500c291038a8a1500662a210722147e5076401c01107202d00468000d120b82c00d0401d030034800641540400079000d45403401d40c04103d851070100540807407090082c45501310010000410104240c9006944d000a0500ca440515842640c0310107406080024910610f64003084d44425400c00021034000d00208420070000e19003012030745907441030802c0300202055180c40341d90f02046691003810020b4003155 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 98157832 1250 98156582 98156593
    0x4050304170a0201021e0318041b0302040306061403150a110a200105090c06030a02090301020c15060a05011b110a0f0509090c10050c1203040305070b0a050108120a030e 74
    0x14030039241c42d2985a14103a00601c90450704800d080c406006410000c0310100007549820180c02500b190b05110744100e940c02650341078060441d15003158850851415940c6c0141e4580c01d500e0180304507922500020700800419007644e83c661000564880710248003000e0712241d0366412140c170040e003113404000c0340c01a0082031000c100340d0040da01c240d151907810319030b8031200400507a441c220354040fa1080f40c15881058880c0c00340c00d158008542060070004003510700480c074008242a0790156100481c59400003402e048028418443c00d9084401100c0b000703041d901d030000080241c2131007021071404545d404100810441d0303200c100710046501400d980300d000d0b5035104541d602419032049a004001440c0050149035000c0780103c2e0501004080c800302d0218450200c50700e80100442a8403482009041040e011105c0d02a49c40b5074070940d0359656490040c40c101080801c050003a4a8641c18030006001145011400b400c0071115034040c00e071140c2c00c48a01301e004c0c02403828640d4060082 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 98159082 1250 98157832 98157869
    0x1020405130c0e010e0604060f020a0515100911030705252406030c031101200a02040b031c080603101a011e0e0d080f0c07030605010503070b07060504050304 69
    0x726044507103407050075151150041181c00055802e4858140c00d0790707000303504000c14419a0f00605490140361130038412156144e002d55511490800b055101c852130322103140030045a8128440c41002030200c002080c40103881c103450f100001d000c0544218103200d070114840d02c0070200301c0d542018090718248400c50003041801c100b007104441d075240b50070708400000303c144004228054101103c3c1d000c400d0510140c95500c80000e070080c0072202c00d040066240f840289000203d212944003a088405041d01c00c80510411040b5046400d100740a030b0401c10400604454280c0201a6198541044500d07030b55503030002410540300a5500d1280c41c505010440326140001000411000a803912108011007505103418182c41903450000282c8480041d00c50b8103100514504851042180d2030818243e8400c00e4001d0700103603854a11580301000030401c0c41085d015890040006a018040d070500b880f2212a40e407145104c0500400c0c1c4070300118080080c2081190000c0c40d12040c0401d49018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 98160332 1250 98159082 98159119
    0x8010e250c03030c030b09010905070c0f0b01080c040911100521060a0905010b0304030c0c050901080d120b011b050a05010c110705010e06070f050a0b0a090c121101050c01020405 78
    0x5140c0c400350002803130a01ca403507005010780704e8001d02c43c6004021031040c1c1e1a1840312000b400c80100000e0800514010500000e5400d0504042c51403003045a15210341c1400d901514241584c02070a104034244403021010560780d1006000303917101507800110b80c0c10700b1a800d0315a4460201007202040b401c18821032807006850541d80a44000c86558541d40d940341d95000aa9070207002d041a50340b802c00100300041e02039a0011110b41c80341d09801921a40c40000848281c0300764411207a40d045808507901c541c5d07001c0c078501440140c0784001c000500c00307100024a070103a896584181d07613410100c0102486003c20125500c0c1d1b078071030000c0c4074400405100038920b4014000b1040d440c400c509000c0784641c001c51b4000000708015000e1810500162106941c0b40509401a075043c000d03602900042090b001816114800d0380340040b400b0001e43c54429808003007688000c40700381c00240340e600080d00d1304450182c031601c00d182403a01c5a18001c000c9009100d90b5001c03e42c0a034664542c06035134103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 98161582 1250 98160332 98160347
    0xd020d20010207090c02030f03040c0807031a0709061d15040807060f05040302100e0d0507060e031509060708042406031118011a040506030a0203090607020a0308010e25 74
    0x18020303401e494a042d0307100e01160179110709456440151b0428488a018170458802443d4460b004a0001e000165a4910a0b0030812103070402e848010f81d10041908501041044030341044d4145001c401c0103291510081080303803a4071340d6100f03022070803031049201d6440c0108010300700301c4042029540c0359180d41807584c0e201c040c458100402c0090340f41103103942c0268244c0301102e8001c2c080a400c00c50f0300c0c03011540c141000141c00c0d40440f0f52144103010440c00c01510001c0c1405481d80c0e43c002070408101490308850000c000c0760100c0c82000c1100c480004229260840141e0034842d00075212403070703c056241c02c2c41441c000551070785d01c04008074803540d403c400112802600360884801102081c4605d4842103481c5200d89181c0f80010000310000500d1040c103149001c1c2d100d0b081548510005011781d00a56500b07164540200510020304000d1151582004050009012051050380d01402c09a4148503e4250900c40700020350310080e80d200722400d6646042174904d001d00c081340d0107840c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 98162832 1250 98161582 98161643
    0x1e0102030928060914060a0302040b030915010f0602030f07050f150406050a02190e0604053a050d0302030403090f1508061e120a020a080a03110312060d020d 69
    0x11403800c400025002c0c0078010300d40580f00f40846030101182c10b5006d1003840d40c000819403082507400c000000e6143d4440700a54003580382ea078040d080c005038603080e101200d00107070070007100788184401c01c11505400000722030f02461402705154664609080c10340c00d00c00141c1215a590042e0450403440705100030f68a4403491043c2010001e60f125005074804170b000b006100a45011543c9540034007070b00a403200d101602c0001c00e101d141c00d4540c1e0118420202c0aa01c40c94048001400400b81c8600d100000c0c60440c0940c409040b454080c0d226940d0351000700c445e03942415800000f04040c184241c900c5400340200100e5400b00c0c039a51412403181c0380c4c141901d43e000400d580045001440c001c0305100c040349400704d884140300b03401000c1000d20300c60380e5881c030310504c56501400d005894ad401c1140c028010003024015042c07540c103025080120700d45c04421140c00c00c0214503412250800348640102003500e400d10b245e40d25201007181c0c103240080160000081403181025080241140b0406 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 98164082 1250 98162832 98162899
    0x20f04031a0a0c0906080907030c080309150f070b040f0602180f01080f0a2304110a060504060c060b04020c06040b01050f060c06070320040803040303090b07021e01020309 75
    0x1d41d1410184402c840742c04024000055020348100310f4107203e0385406d9003048a440554101c59565920203110084540c05900c150300041250a1145842040c0000780c4550b08800c52410001c030500200d14400c004004040f104010085030074230900c18803412107240c1c44401103584410b015950659800b000007083d104c0c1030104040011944504581e03030290391103007844000c68031041a10b01c0a4038414070710b122007545a9071840c03580c40c2c0041803940503902944e04010585040d000b80104c0b408150044000d100c2c04102c2001426400300c04e007103002e60044c20020b00d014060000802a00c03910241c2e400d01d01c01c0000340000c1c1b00403074140f281201d004555801c4144415403d000300c5001d4001960000e0300080002818540240c00c1031000403510342020255a85822801c0030b80e8100740c00016940e0300109061003019000b40415010384040e165142c00c1108550005002d50407840d4541001c400302c0c10a030205074001c2090300d41318030001b0315452a5411020041c0c0c06100091140d03040d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 98165332 1250 98164082 98164133
    0x40b0109060816150c021801050103060806090706031104180b03011503150b0f0a080105090c04023c040305010b090a052211060d020903011a060d0906020f0403 70
    0x5440c0c000185140d00321440000040000c0d1404011004c481c84440c140710600422042400c01a07856054603004419007240604c0294145000101100d07025040000c065210f038041c400b8440c40003400108031091131501041e428404400e1484d180265400a03040c03549048680e2140c0c00c260304050407561042d0001c0050804d187d228007084111031002814004d80d9183d601c1c0b44455541259080c10300140120f42d444072800c01040c0c84030f002c2c0e88544503c1e5928018031040443c2842020140380040310103609000c200c58815102c5140d0203010201c468100c1110b04c03242c502c65408500c11811042803586a540d2800c1c400d020b06684095244111441000990110124480d10340100705014010070b00744808811070290340007011007aa40b9141140c09800300713554060041900c0d6451400141c1c03101910401e05094400c40410004c2c0c120402000c8101d607103504013900d904485e0814040740080c09803c00f003000f0f22070f40505540d4554000b80100901514146a1503050040c158201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 98166582 1250 98165332 98165339
    0x9020d020705010b0301051003030806030a0b04030c1a0408040501030f0f05090706320a03020903060406060e06092401050f0f0306011404080d031a04050703060f120510020307020a060203040b010906 87
    0x41c200c4404440c0288d141d64500310500100380b040c0501036021102034202d8101c031800d51510302e00366608403821000104220002800c002000d0400c0344403071a00510304000742050740da100c0700c9006034044e29042594030305609002d21140d400a0100030a007480401c428280350308101d49030b04583c055900803417034070900703d139190140c0032000441c80da50000c2c030520700e142441003103a550310031a01034040640900504440340d505011090003a84502d100055151801c104c0c4405101c004200d1449000d40404000d1a010841051070200c0c8202c1044010000004010303a0140a203c8005441c02800300300c42c6501d01c89000118019002625103441f41644070410000d507118600a8880f181c00050712080742c40e020360042c3d00c00c451810001096511020b01050444804840c11000640c48007001c10411425034028400340400c50201c0700c03004e4180d100c842e541d1405122116034180e00100140c1d03000c2c800e100000798281c0c009002d6549061504181150a6080c018a00c181c1d04e06038001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 98167832 1250 98166582 98166589
    0x30e121c140901030b1305010b191b02130e10020a03060803030903250f05010b010e040207020604050d0515040809010801121e03120609020316020607021b0102030409020d020705010b 80
    0x4205640d10354800c0c2c0c5858201d10045001e40b100c0c0c443c0d641c11281c20110807540c2d4845c2d0013018042d0241c07003c0c0716120044e00000b0000300c000c0e2340480080c44003250109202000c0b41c038028000c0c44c2c0590f420b2944801e10b0501c140201521000d184860281401c401500e882c0c9800400303020303000d80d44c14020145c90710055a10ba00c4281d074542e00642c001c206c44101c0c402c00b104c806000c1c00b48196001c110004640b40c1030750004013a8001c82d02a5990b0402d035243c1d60308041403c007886403e640860800d156580031030098072550080c00d02c00c41c0361190302e804001040050484c1961a112075011906040ca05507042d500010085804200c0300000481e92b15001c00300140c405800080c400d4000c0d0300304000c41c03400001d028080e0f04101002131000c00221050103880018980100016941d1500a0b0f071104402c0301d0702500b9045412100c14880c806a00080030000000e604800703080d5580100c005034a580b05a5109081c43d130300204a28685101c42d90181c14200e0080b030090080b18a0401007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 98169082 1250 98167832 98167847
    0x31b09060f090103120e04090f020102010e210702240a020606180c0c0c03070f080c04090b04020126011205100615050c0f0a080a09090b010f0c030e121c 67
    0x554100c42c1c1c071001040480d08108480702c00218030305154482030b0250000c641510a0304400381c0c2e441103d01d00c2d02e01196424403500780075108850240c00d1400d038400c0120364100c00508110540d29002c9200e5065546d001c44030f0000c01a001d240c0007a1840d1981c2e01d41f034139000a06c05070003500403100080c3c00c1d801d0032280d003080d0001d03a02a020072951144a080080d03044140c1aa505220b2002c0d0403d141d00c0820100000d046403122070010300b441c0600703140c50804d04c02e101c140910300302911500000c4003a5100d90300300380d09003481450440000704004e40303081010f00651740244c0103000080c0e40c0400c2004685407a00400664850322903008002d000d503001b070300c220080b0380c2c20101101040b07445000070744060316403d419240003440d2005094034041d40d851041c0d54542000540084480e0080d40c0940204409607041c0205d80160002901185038200751030188443e100814007014131a54030708420b0325000f41080d03003500305c2c2c401c916550310450b4511001000048106000d0078082c000303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 98170332 1250 98169082 98169109
    0x220f030b01140d06240e01080d05190e061e0706051f03060506030c0301050c13081501031209030b0906040623150a030c0b03070311040b09090405030405031b0906 71
    0xf0f14681070741c50b5110310040a126940b020a8200340410904c03c2809058510080c400c41c80c030025103504054080e0b0901840350301c01400d0100c200654942180c040c0540d02c8018180c1c1031941d40b000c1201d001c030f111071007a001003422401c40300c08002005601c1030060000c2d11b00449040203a030381d440c00d1820810024006502c881c1c1a060010000550a500025442640582507622480034100401e003591000d0b01c210640c010f0214254805c5603000c05010001c0107044000c0c041301d0600282e51030480410301003d018401040c240c03103a418007824664000f50760083c0354031140c0c54000805600c45a003520101c40c04c500b013200c61400c0360222003080b0084050802030341d00640b02c042c0c4640c80340044000450b04a00780078000008144060403460040c003072410159584d00d80600003c086908584a102411a0a04c0140480c0c102617050351204e4000b03a0781c00107176440e181070151550207550301503035140c0f2500b5615214092a10303103150401e0002d0356610707201c3c1c451808110780441202c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 98171582 1250 98170332 98170339
    0xf0b030604050c0c01020c100b0d0807110f10020d03060902130e0a0b030304080604050f0105010b03010b0702010c0c06030209130b06090d0c0306051501020d020d0203090105220f030b0114 82
    0x854550300d0701c0d074402500034400550307941c900051500401d081e6004181612003640100002c0b64507205103000351080e0810481d03400450405d5695075141e40d000b0b0740c00103840302080c1510b5030120345070fa1054030011000144202030444400c48001d6580180b050007d000034140700c0002403064546c025240b0404d02030a03240440c42c10301a1000c002d644c004c01d00e100207900c0f29030882c000d480610041c00901161030240c0341c01e24050400c14070f041081061090680c0c07404c030041003101001d005880c192143e1501440e0781c0c20b001c1c0012101c10290400c00307030629040040004080e41c02d64002c045110381541e0100d050707070a9510460444d82000c5410360402e00401400c1d4062400351400c8031003521034001c101107a6100d443d800c0468204032000401c41100340c002e00c1040d0303010414201c106804d440241081c14980350b0007906ca0003258109414440d0205455448000405d403018541c082c055180386420360f215100c0403a80c60910040d071f0466802d5001180503541c00030303a1940c041002c1c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 98172832 1250 98171582 98171587
    0x25030507090b090a0e100302180906060111030903060109061403030f03040b0c0d0908041a0703090b0906040905090303041403040303080c03102301090501020a020d12051c020a090f0b 80
    0x2031008802e940318908066101c42c4410b00407400b000000900c1d40120842048448114154410b00400c0105240c5568402e4800b0041144d01400000c805030704c0602880c1ca04111131034880a0b62960003810b540c250315006400000c101d0031241c0d481b880c01c5403d040d14800d01c0c09440010b1580b0b0784503549800c80e0085c01040014040788541c2800303504050194280c9286c1400000c00c48110303800c5102c226500c00340000c040003440b8071080c41060034140014902e2030100d41c0e542c0980701c0724a9210380c4100c11408a40ca086680e110801d550013000100d4060003a8540313049450b842c0c1c0e208590884151030040031000241c5000010b44044e6a4941c07510000c1c0d0701c540da04400c95410040c21200c200703159190101d0403400c0c2d2500754082000003000201d40c01c4402c400580123107040d401090456200300c01070f80241c0e4500031207800705904030300302180c0a010b140003154540b0446442c1640303001081180c001e410140da000707190f1340f200c0ea52039102040d115030b240e10f1124443e2041400d01c0f00b0a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 98174082 1250 98172832 98172839
    0x50903060a0b0a03022d01050f0d0c0302090a0905010f060206070909050406110a08070801090b03030a030e0307060e0715020d080414011e0b030f060403080c0a02152503050709 77
    0xa40d010b403218400040403040035a03a40c0d800a141203020306800b02550b442c0b607602030280842142d520f12540424244541045421030089070030f4040c8100280455440c0c0161070581d5000c0d90460b0100480500300c1d010072503d59a0301e2019180a200381d84a059100c0c4001607400e201180f44c5004503159650040801c6c0780000500c003800b400341041e41e245603202c596010050710741c4000c02c2d01035941e403503050140c504640d014003840e0301603001030344e15402d020404685036000310444034807507100d05000840c55035400031180f96001d504401041b05280803201c1e04a03440014842041f84c11b02c01c089800095000e404989034000710420002045041300030500098080d94100600384040000080b0754200c207080e2404500f56000d00343c401541d40d0038000440c241840784115500b6000c00514031410203a6004100000041600103180c4001c42c01d200964403d01c650302210426010055031420944404042e4400d24040030051ba201070b5510f40700303640a0300130980301e42850380703030541da040c503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 98175332 1250 98174082 98174101
    0x9010b030304060f020312040b060108090a17070309050901030506010e0a060f060503040f0c0b03060a060e09040308040c030c15030b101e03020c01091104060e04240603020405070f0e0105090306 85
    0x244d01294025400140803d244110303d854106204034015802802d4500342400003500701140034148506030382080c8600008206c1d0500342030014199003500607520011820101c90811054125590088482c0f000005215000440c7d50607110940940c1c3e206031107c400040844045200385502c0c07003c7c981c002c014040c0103001840c1e21601424000d20303c107041e40d690104084080d013190820030404004d00066082c000000000307400030381095020071001c01e00280c5107030401071000702000401d200041c204020810320400641d80491507004094444101000c02130351703002600002490581003550b186001c0d131308003541107800c0d201c2c2d0350991421401d01041e94020a03611050580822849105400134807502264501038042808082000420003041e10440c3c0e0100c5140d450060030700c000f14424220b0030170203480307145110714506c1160594401404076640040d500500d4001004500c0360010b0240014501030b90b60611204d20b802c0044d2200d000c4c250011380c255020b04000b41c150b03070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 98176582 1250 98175332 98175347
    0x91c0605010b12150f1008010e09030f090609040e030a0206041704060e090702010b0a0806040506092109010e0a060507021f050a030b030a02190608060405010b0702040b0a0308040f050909010b03030406 88
    0xc0f80901170700340849420010a542c0b07141ea210031000114503c00401c0004041c111642d040280364000d0341c54814000000b010f0ba0080400c0c80d48628400104004255a80d07444120820441d03004e680d01d5280c8080040c2d00d4000072a0140c1d04c49024131654403400031500c044400340e40c1c5907101d80303400d14002010301c155030000606042c2550750300c08521010390340c1d1803012001001d51300000d040510341480e1a0341846c00140141d60301d64400315000346a100e0750744800d480381006001403600e4088200040300d43e528103000d00ea03001100348801140a0b03038410000c2c01d003980251588110560641d103048401c06084d00d16100280c421700c01403050901c030390403440d0b81940c000c0c2281e0014201d0380000d018500000402030b5518030b030a20803ca481e801030f9074a0703803002c0c2c1290704202da0340c0340c0402030070a4400d07a030000380316030390303c0c510400304d95246c054600c055608807651585035900c800383d0500130710090044611603a401c0d0001500000140200280c00303034050059410030f0300d03190040d50341d02e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 98177832 1250 98176582 98176621
    0x1306030f0b2d0604080c06161b03060b0a0f050d0c09060b0705100b0a15053604061a1605010f090b0c1207080606091c0605010b12 57
    0x1641c95110703500141e5107420049150303207400d0100040701030500542a001d07006100c20b580c0941d10500003000301d03c00100e040e0f1250f003015201c0f00e41d6000d2090780802d41c6400e045005020b181036692610008030500c40304001e170b900c44c000c2040804c1c00301c81081000100c0384558895022121030501047c1441c000300001c41d44901078020300c45443d20944410b4030300704d0300076104094004c55508240402048003487c8100710304d01c00c100281c00781010030203909035409442e001c2400840d0040340c50b80710f10103d0b10303e004070b0100035298668580002145d15000c4482d488049100e1060000c0c1d85070906c0b582c41120354100c034407030038000c02d1a440c000b1354000800c554203403032000c550300021a50070700561510748001c0800140598052400201c0d15401030116404c51101380b11080d141c921854070150000d42c141058410765503400001040c0c0d10648134000c1d0000c2c00901444004091480840300541c03044038103000c0b80c2e80700c1c2c2404140c1d000300c03944045103854501c081400d14042408401d01c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 98179082 1250 98177832 98177861
    0x615071502131220060c0304060e0604031218300204021c020c0709050403020c0d02040b030a0302070806010b0901050a12090204020c0c120c01121d0a080408010b0105130603 76
    0x111035440c82070008603100c3d4403096480546a20030302c420341581001900d5848012240c450911820b804c01d1552401a070040c07405000240e1003402071540c4030001d5a004660000e01c03003002e182d00c80001072046020030191b20043e007011102065010344100c031841103400e40030701c1d003008c200128045c078214820580b0590b08113600300040d00c03a18001005141e2414030400c8090794580320a45018500302c0139034003008009190a09110000741d01003403500b40f240c0b080380d464604404500018008060640c201c0b54148500112035080540114850b07040f41c20788003d03200d480c1c1c0d903400002030314030402c51460b00081041000c40f031118015500070b040c4241055002605a0311680881c1c120b80c4100896030035940500008a40e614241030365104c810002d2028002c03040038540040c004130900041410115200c0500c0c90b080341002e036620741080803450445052101504180905900c1070280d20001c0d401d000d09000c840d4040c0e000c440360040c030714204042140c6020001c800400310301e6820890b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 98180332 1250 98179082 98179117
    0x14090604080d0c050706031109090a140a0903020f0c0f13140c0705010509070e0a09020414040308040c0b07020a031e020a090b0103061a040306090213050403080615071502 75
    0x103480008002d40700c1e0070600743c2c0310401150101d040040c500b10071640302ca001c150804013190004247c000544100007000e461400d610b0311407480d0b6101800e91038a403004040a010204200e450300d68111404d80360180d02030fa034940702c4521807940c944030380c05140381d00061462810305c80c0d410001400341d480b401480e40000e98058111120707400042c2030301c1d070389803002001c10114140903082c40380340d400c0341e90722004001031403a180b1003481600c0700401e05540b45035613200c81002d54603079800841c05240b005084203003d240915000d45004001c1d43c0640b0080c06004000c100100034808031403640d500180030821301131070341d5221103410419a00d50070741c18406007003030801a264a04401c02070501c2e0781c00400c4203550840010b0846200c0c0e840f0702e0813110203410242062960720225000e40e600484041161207940c00803a5400c0d09007000400003a141200300000d0503030041c101c50080c03508845a40d61b54021b200f1540260103880c80141c1907155140341c65040d80260f81c014490300544802c0d840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 98181582 1250 98180332 98180339
    0xa080105150927030702040c0807021c03020403050303041a060d051b1519120603030c060905030405151218060703150801020f041809240f060b09030606010203090114090604 76
    0xb9414031040c3c5504941d201040a42c21031801d40654003012280d072070240c1082c6098035000359210a2403403140895842510b0040800340300f0740450b005503400100705e0f6603d082c180f070803c0d04596902c80706c14030f62803080d021801381c2c64443d400c5580e01d50410001d01d8403011039184110710f243c1c1a0803080c0d003d2240c032585806040c3d1207010341080d10803800c0c0810b4400c0801c6001c0c00703c0980240803049145000d90510002c1d40042052038201c2d04a04006041d000502e060303891440b403608031a03071002194000c1c040d01c0b03030740c04020909015500044141b5485075000402e48a607004400c1d1844d0300110005003c891095004110507000715417950907007542c6880f182d0072644801c01004219034001814420100c100d07c107402c00b03800b100303820002484292201c3d03402d4a0142041c501c140591071800c03041440c0381d084005600392048080116583e2000b000c111a81712a150034024003170440001e0607580044295405018183c4580160b22042415460750344d0095a8a070740c842014040071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 98182832 1250 98181582 98181631
    0x90c03060515120f060601030605030a030305150603040c03050709060321020717070509060901060915030603060c090504050a110d020c01020f121e0405030f09030a05100b0a0801051509 81
    0x44140c4070403409031080c030201d44d44490a15074001e04841c145418540d080190341c07800526022030700d826250001d40c135220011140e00c4000c0c03d10f0f070203500c1003020041c401440440c1002c1c030102ea100d9000c9814a5642e01d81c0402500c88601c40900038040d00002c030710710080e00c5800044009003600c1540c9140b6102d942028443c0300007918247c840c1d10404c0144503a0410540c040e0b002041100d001d00550f150000041c04c820450088005610400580c1c180743d9000e90400805943d0045080c0040c00d581000241a10303c503106d49449581424007048150010307225280c990b4413613055040c030f4007080909000180d400031030403400940d800c01c064080240c0303101c060001d140452001e01c119050400c2d4100c808942c2003814001051100148000900000111024403080525003034039044117000190074500480c0f0050f16600039108143c06021440e80143c080c183d00300d440910715503c030780e40142202d9040b20804180c83c04000d841c02c0520b442c80c01c203680004009407a184813a62040790 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 98184082 1250 98182832 98182849
    0x40809010e0415082e020721020a031205041a1302060409060611190f1505070201060f080a0507260703150b0f0f100315120501060603090c03060515 65
    0x40818155000f803003800a803505209210700700c040183c4100005203e4861421700d0020f215542e2602da40c000b800b0b60401820705a0b0f604403801b240b07880c1a001c0014031020b921102d06aa003100081c5000030702070102002c0c0c0c0710704c07401240c01403d50101645400d0080d245481d0103010483ca51825001d1a0016500c0c0703c0244042e10b1422004900c40f884d2103405000c119011140342039640043c69442100700301484070030101500704942c60012295410000004c0700c02c40b134010f4149080c43c0070820303159015000300c01160ba284103c0310880d541c40552540b6240141c000400030b03086010304014000d03040140344081c65020300449031508080440624284083e4001c4070301210200e500069000103200d01031803a0000e170745442c5051000e40025065400d5402d50900c00c2c0c50b8014014805403180e845445d8480c00c0401340000036031034851044600c0901901124150b080c042d004c11801d209000348141c56130712695148505095a4450020308001004003000c609850498107280d03231035010303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 98185332 1250 98184082 98184101
    0xc120708030f0d060803070201051603050906070605180f0d11010e03130e070306050d080c0f0f010b0f040204032f0405010b03040b0a11030a090204020714060603071d040809010e04 79
    0x30780ea83d9a50114044400c0e00d240b90320250721908240b040302c1c0980d030030a04481c40e0341160b0010082800c82403606407101e01a0348051a00450003240c50400c010030769000714003810b01c8031701142000c0303c4440c11540e900140c820841c2e0941012032071001d80c6009541c1c80b00e1024002001007881c0d080040d41d030b031464000008081c1d176504254410040b0750485000780f03070842000c6c41c0130310100e418017000c100b480d85000b8009103540c0e40000c4030210084244072070480b8500ca40141c51204413140c4007a8040c00b5120344052017011a00e11a4822b4541403080340c080b00e5101800394604060022a4240c00346250480520840c0845581e0700b5507444d031043e28060702c84842c0d040c0d242d04107800c4c00341008030b0092a116405141c2030000010b00100301c241c070382c010184200890701110901c0850041c0c0103c00008120290440600140c85c001007521803085c0d80507822158a01d40d503c00524030164010031140d82d000303003079020034041340840d401420540c4060401e45541804e180105084550254 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 98186582 1250 98185332 98185357
    0xb07061b031107020105030402130e031903020306030a1103030d0501080105010e07030c0c08130905010806040318060e0d0201090b0318010f0e0c1e0303070303020c1e0c12070803 78
    0x155a56450008212110a212490704000c8003541e42d0b02c8806920440001030f05210004c0f0001c0c00310368803040d03007510b249142907050011070740c0403840742d136243c03c002030007a0090602203940403028440e100742e81c0f041400400401809c003054079004080d09012000f960540010000800094058080d96008103202c20000070385600d40311040c0f240c10320103003000c0e0405090240d0b91102d10340c400d0440c803000b90000501ca60ba100d02c054003c0701d450007030780200030450810000042d140404035109200f44c2c026110031b2903080504c5c0c030010110409005000100f90301111105250800d510010030580c4181848200345071a4401c01056070811502000b4070000501c01c82007541080c014041442c0040fa018012000007400d16a1908a07102e1450700a6103025000b07410340000c2088071207a91006010742e42c0d10305031401c00401070f40c071450250702103200740320380840c80c119003204500c5140402005491700f82500380c01c2100584d03130028500311510036070401084403030b414001041642c1c000c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 98187832 1250 98186582 98186591
    0x4050403030b03190201090e1e06030708010606170a140c030606160501090c170309011214010e0a050c070f08070302010608061003052b051b010501090f0510051f090b0706 75
    0x505c0018850b455941101160080b0001031024404403c3e00040d1000014135484100780d84c1d02000ca0f2420b01d072940080003d43c00c081000031156084008443d01240c59160b449103a0760342a040c3c070a5402e102881d8000350750480002e4001445803010399003010340100420301d44000703100c1980150306c11510a03a11030b552100c2032030070001c5048910009040540b90101d00b000a00100c40c0c403401001061810700c8001025050001010360204546d0216014485610b503151034607035008450480e5600500792510000caa6000e41840c1511019a4004504d5001840d10f989070046d54000010407819503480d0100450040d80a00c0580d10600d6101c1d688900c1c1440d5051040c54507526071581c100008c901110386201c24a441c41002400310316040640e621070519000d001c14170703004468551070754078190022039134803101d0b0007450b00d0f0f0600703000501c115260aa0403003503260a074070469034445804040c1100c2455902201e28254071281480f0000e00e603960014a900e5000c0c0c030b8102c581c950381d03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 98189082 1250 98187832 98187883
    0x1006090203160c021f0207080106150f020102040806041101050706060303111501030b28020a05030106030f0507080406150302030105010803090414070203070f1112011b02150604050403030b03 84
    0x600c10000b1510580c0303000c0422119a402244143d40301c0760341195000d050700076104490f8000c204100003008900020445140c4e2000100310008150005100054a424201d2082c601c14001c2e1819545100060039082c0c03990707a510300c4d000c2c2030812031505101081c040403002c51030358403841300254040e03181c00c040110800e40981c14242d49080020901d034807a130060003c1000b83e070009521460141c5000c006403100003034520201c14603450b05034000d0000660b03480c0c82e94020090750480d24544c800340145806580348100b964821240e5100107032032480000c0100f64150408d120312400c00101d402c0c00c41d125004203080d180309810000c030981c00090303c2c44244c00c25100e694100552204610b20328200751400949a2241c00f1001e08000303070400d200020f2210001240d0741001008002941c0300c1a0034441e00c6c060300000011480d100c0191020004d20b0b80081401101451140400384159440f981040001c1801520036010140e98007481100d584040003090344940c088030a0030042c184 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 98190332 1250 98189082 98189101
    0x30903020906040908040b03070302130303090501170408030f040804090f0617030903060106180f080a261b0712031106060a051008070c1e05010b060c031207021006090203 75
    0x1000d006640220304d808035407008203280fa81901c0c01d8841643c01c1550340e49407994100c001e40564035801482040b4050000b0416401c0811301d01160401c1c1c82e140c10000c8205075680943c0c9049030080d00c4080b080000400d00c4040881d201c1e8000d02c0f443c04281459140c049440442e50003154100503e0f5445500788204e42c00300c00d103074212000c400011482c101042000c03c1c0c031848180300d40001d001100030001500031000c0c804074082c1c1417014442e595642d84003140b17555078509000588a208543c04e0003901c0c40c016240c12402001c0c9031041901d021211455021820044010384081c0d000e01c80020402c0c4100b80d030034a0185029a0325100302c2da540440250400300040e02080c80740080442c100880c1c0c03504003c5040c412a90b0416a159a40e010026502e46d08507080080c500c031080341c2d408140c2d054069010444030b000c1d00081005905180503c803407031242004a54480c0d105001c0c00091540c407050b0154031100314410356480540e40240c48041d00c8542e003124235940c2e00441004100341 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 98191582 1250 98190332 98190349
    0x2120c070602060c070f0221060a020a0e0d020306060d0204020c0f0304050a0803130b0706140118180b01090905030f0313060506010c0201140a02012a03060b130e070c050a03090302 79
    0x20340130840616050b89581d400e40081000303000240100c24410684c0c0b218807861007030300e00e0310565800f5140c0b03e03e06940014001d40c0700d0782c00c14000c100c2901503403030f850a00389400c0c80e00340da0103802040542c9070702040202680c20b11070102d80c01602001134500e00d0100307100000101c0c0111000b1a00d55080808015503805160050981c942c07050184081201640d8000c0d0304540600d02a56030b2000745050060181c5807248003182e0500e0b0030000020003001c210300080940c4a411401c110302118130b0740c0560350840b51358010f003240e0900c42c010b02004031144d03c05104184200304492801c0c204003d81c480b5604111810090001d0018800040c40b60314080c10303500c49801d10303004080b03a026500113800782a44840700010000c000ca01c8280301030003544080c14410100c0e5000003520310801403030300d80d005d048090000103801d0001c0054000b40800a503400c0c10620030b03100343c0361420801415081d000040441e01040440c04904012407810321100e221603001e0f40c3d8000300ba6046005000c07010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 98192832 1250 98191582 98191591
    0x15040506070f12020a11010c170a0209010c080a021c02030d060e070c060902010908010f020910020a0b0f09011d100524010302070501140c0a1706010806010f02120c07060206 76
    0x49540040088802d43c4401e16190202d0420300050701d90040c038008841d8007242c0c070142d07110780d071070705402c030783c04541007200a03c41c1c00e4000d1800c1b00b15a9491034210507401086280c60210b4410303000035000030241e1000d4680702065204940001c1310301030744020401001c221400260700006039400041840707000d8a00540103004c81d2510b01d05203070740010510342e8969000380009540741c41d81011a84140c180ca401003000700024042000c203488000029889803154601c203c46070807145e44298004103a01102c035030040b2814100d95902c9100030580100240854559580e5209402019600d0303080c40462421183c01404011004002c04080f500040c0000c1100580c0f001380708901000000c1d40103c003a020302c0c0c0580c480303034249016405001400e2111308551f109208000b50310126030080e11503020142c0e201c0f4a6a803400f138540031440c0d02510000d000504c00c01c0001c0c420b5014985c00c110021140c1f0449184151800c40680ba90700310010810080d0031104081020903030401105400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 98194082 1250 98192832 98192837
    0x10203070f030e2409250f08060c03010b07082107030c081b0a120f0b1503040206090609031005070203090a0b0405090a1806020703170109050f01060e060c1504050607 73
    0x2180020105060703256070344001d00c04040b06240001d0646901800704214982c8030101e45007503da910b2401003844005402812a450340005d800500c08200092540c042e0384402b2405103140d017040d40c1021941d2001605440c20041040700c028000b040302f201146d004604030359990281401000241a03406491413601000a40003d00416954545100094207000c1c488140d5500c0024020f40700c08003030b08136140741585460388004011890b90081105410101e65084407040c6080c840041804241e40181d003005080c01380d2510b41c14560003c0c20810002070442d0030040703100740e0120544604640460058102150f400d5180c20a140700d10302402e0141c60b610304240c209004600342c440003c1140c0c800980710704055101030041c1c01c9045619400ca03100f550364020381d080207001c002241070760061480c0329000010b08030b41903200b0940510315203202c1c01c3c0c0326480d000044401680d2980c6c89039000b20104845e00508104214030040d00c0c48c0000400d0182c54a420800d0400744000c1c110400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 98195332 1250 98194082 98194093
    0x10207020102060106120b030105010806270304030201180302062b0603020303072307062607020312041b030f0c0603020c0303071107050603070503090c01110a020120010203070f030e 80
    0x142c2c0c0104049040d219549000030010001d1030482c405054408203041d0594079110001c5020240815440d00c141480e4101030391060b21a0040c9241c8840c410031b80c20305403c00d00c010b00c0198810303100c84211025280a103141a502c0f9000175800d9030082d1a1020003810381c0c80020400400c00301c11400325441e00321700700512461a0003194a070310a0000c0144203100004c541c2c1040c0750500041a82d9a281a00700d0714583e03100c3d0b50140020910b00f42c40320009070703050400401c000f400c01d5214418120307030f0302450401501548402d5802400790048072004640d0116103840000d0365010300065008104004440c8214100303106810b0321500400c04240c010002704480000001c2280d400c01c20a1818410890004034040d080100717540080344d1018000040c09805a0b00070302544c0100042d409550b01202000300545040d500c06048501070b8000c03d003480e01641c0205011100007009401d041a0416401d00b02030883c0e00c100e44070390126140818081a0a50602c1110002600d4400428 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 98196582 1250 98195332 98195347
    0xa090509060604050d060e030c0303040507120201051204030306081618060b040315060308030a0e19200f0a030b16051e030a180c0512011a040207050f0f03040302010305090102 77
    0x30303950f10650007000e001d01d580745d9829040081c980e0089001c803080409481d25824015a036a480340e1003030b02c040c1c0b4940f19107840411031000f10202c81c50350f44e134140c444031304c1c15042c143d03030150301e8000038401c0c8d0078541c0c4c49000099810091000d20000b100b00090400b9079410034410305031444600c01c600245625108060161900200440d020f03039401c1a02220900c41c3c006510700074100e00c1d000180340400c04400d1150207115500314182c944000b0054542030502c0140c0c08282007000030001e00302c2250b80e00f44140c1488a42024102c055002d0942d9400c0c0c02d0340c0d40414101b0701d1903841100d0b5100004100100702000c00000b040710000c925001d4680403c0d24414249100b00c41c51b0002160400008034001e41400d900c10607140c200c40e041c08041b00043d09100203103010074400c41c2c0c01200150400304c60410180f1030410002d121014800701d01c803c2c42e080c80000d40ac4a10f088800b44500040c00015800422080b44881c10000c01181d4507801e5100040903a4000b804005840e801800104d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 98197832 1250 98196582 98196589
    0x1905010f081b03190c09090606140906090408030604140c0d05060603040c0303030b04090f0b090d1704110a1a09010f05070b13061e06050f030c01020d0e061c020a09050906 75
    0x4d8043d000d60800c00d58506198117000074001a540c0c0070784c0c00b65140403208420404250807207011200c0410385244015000d00520050950849185074080d1000d40040d0000d44007801558000750701600010711503030340b01201040c00c2819603100d40342c0702c4081101042201a4080c00e80d1001056488a0840c04c2c00e83d11300d03280e40104e000050601d03407103a4045010752102d034014100103810850072a08a04242401034004000352802c480c1c0c0e000706840b485610340504259007001013078103051085079032236031540059000d400241650200c10028002608001400700b840c1c40c3d140346104990b01e890200c000740c0310390b150002086c14044140701010219045c164000d910128203600200444910715240c0e000301164028162418440c4e44207440000d100d0b0300c5001958003e50ba10710204ca0f0b850700b0107607a41c0c1034005050059010040e45d810075403191642c84500d40000e401e16007411912808552142c11040021035110340c00b061555010f907004010000520042e03a0102550400c100030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 98199082 1250 98197832 98197843
    0x501050a05010c06050c121303080708010506070818030114090106060903030c0b0a090827090f01060c05010b040203041410050126070b030405010501030215090102070306051905010f081b03 83
    0x1800d441d940380d00041070f1b482024200c4280d100444807581d0103240002481d117a03404039060550016003484000790043e40a092003d0580b01c008000a040c030410756117400f125482150554503441485c02c2040c2640c4090048100c0c8616246605009203441c60345e807405c40324940d21081c10069420001c0010a400c90302040045401030221a4265144011a0060003002d8001080918000b030180c2080c10036282c00390440303c494500380ccc401c2402c4410020084802d90312450b0000203d40100109070044852003d010311030400890000306020001d003c907003048400362041c4602a080004c00b9005002c1c015134402091403c009030350400e4101365000091030039403101200813882c0000644c1c4c00f003221308014660300f00c03000e9492402d450818042c00084c0300403400341c0f601c007120802d40d05040c003c0e1100d0301c1060f4001e010709803a40c0c03941c401a00f0050814105101c40710381034024032915004880c06004164641a005480d05c08035900c0c03d0381c1e06040b0745070b802e021040c0090b05d82d0007150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 98200332 1250 98199082 98199107
    0x4090c03020405120c0f2e0201020a18050303040504090f15020d05011d0a05090c0d060b1005040e061003090b070f110a050613170412020f01090621111c0501050a0501 73
    0x12042c102c1842c211f03010b0340d00366a03074002407411445036100079110303a030540040c01c03c0c000e9030750340c1c1900c00018200f80800e04042d02450340d050708184024821801e06034002035403607014040c2200c1d03171070140e114120840111420040159000110b0121a8009000b40c0e0f00400e42203440da0249203042c41c2e456804540581901280d86d1a0310100f0400c0d01c040103501c80f44070004221071040340c400d290501c002c1800610403170080728041000314129014000f0b4404a5a90308105800c55449808002c10102842400c4c0245a170760001c042c0461148004940b041d0003d803215544c1e00074072000903020210b5128035055951045034503800140303000c01c1d01900a10002034580080b0b1b101d2030441c0c0c13040c610001040c0c0d00f15020600154000040800b0100140266602d045103180e04004643d45c12803030060b800819003070107200c42d403403600800b64010500f00c45000618989450508141a80039507050074100d410007160000401051207440e00400c405c50f041c2d480e0b6440c100c00682961050b09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 98201438 1106 98200332 98200339
    0x60e070e01020d030506010909020f0a0206011710020304110303071a0a02040e0601080601090b0f0a0e0a030c120302070806040f0b1005090a1104090c03020405120c0f 73
    0x4402403030302041e0302505111100050560280c240609401d042080c02034002031445114030282c68444038458095586211248009180c4001a00202c5813000011501da9181ea00003450078009801460301503181c0d41c903414403045010740502005d4150000103030200c00c200081e0342000d10107204a01030800d980396601d118080b800344c0e000d8000340c140d168000c00c160390b015040440d03000a0500d03207800a142c455005100703a40081210350729480000c0713030707640015400c81c4074079a030301d102030711801d9445c1d1441d02d41ca80d072000d00b840342d209154001510a001d0501c24840d074005040c1c440100c034003508081c0b42410000300340c18021b4555403070000224092031071850b1300100f280c0e0028101130f0380761508000000103201404410629510070070001480d1100c5002d0701b8401c0d5015200161242e02d41014408203940100c5190001e411001001c400c0f40c0e1400c02a00c07002c1400c0c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 98021582 98201438 := by
  have h0 := BRFrame.cov_init 98021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 98021582 ≤ n) (h2 : n < 98201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
