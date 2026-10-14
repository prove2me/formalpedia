-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2977
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:18:16.456119+00:00
-- url     : https://prove2.me/submissions/aeef3eff-9c87-4bd3-8518-f669b658a052

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 535251798 ≤ n < 535431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 535253048 1250 535251798 535251833
    0x180b03030f030a0606080415090311010606111006030b04022b0b01030b100303090b0c010e15100b07110103090f05010f1d030f091c0501020a020c090108060603060406180f 75
    0x4e10000781c07500821110380c502204c000d41003501003c000000e5148039801203103030034044c0c03405100030f0b4801031840d821341d12a9403110000805140f921301802900340961034050307154610034040c042c55612000c42245002d00003030300c035841c1d42003000341d500e10881c1d0328113001810708400005401d140c140042038a209220980c1c0391814503002800107054001d1082c1030f01e50588940e852241895441c12a03500a402222280e40d038550350349686240030001940c01c0450b04c40004000c1c51b1851000d4400b00b0523610008911005218010004a0b95180003194000038a000a061b00f401c2c00c00fa40c52802051019160b0352070096004016019500712614805400d92100103194158901c5a600d11406a031050615418407504180745071604c8446003401265a02c1c03d91500541c032035608a034001800d18000da4080b440e21451803c240c00210b0040c580c44021b001c0303510380800800e45071440200001c01e0320f80d032107100015198100101206483e044141e418900c40f4500e0030810110844180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 535254298 1250 535253048 535253051
    0xd05010f09141308030a06050d12021e1b010c1407030309061412090a02060c030d06090b01020c040903050f0d050609090601210302210a0e0402040f180b03030f030a 72
    0x1030104101a010042d4010140c8a0244101210544501d0342c190400b40140b07070020349407030001410380c0c3c640c1150703281c80b40107041c00b2400f05902040607142c2940c699550080c0403a0320f190714064140440c40f815504a02c1108200101c00000101d64114440c01c0c010002d14101030440d0394801c1c0040c082050307074440e0315040c0c1c48036201d01c010345440d21700f03020f100e0b2844001c2117a440610130b80030300260401d019508950282c511940010103981003400161019400820a40420403090040e42b005244441041061200680000392140010090580101d8441d2400010584954115240c19200705003154541c0b60340c421306c2c005440c1c10384030242304100a2021441440d00452075904a640721009081542d076989410451401d1508041c0c0541c01041c81e030129415414103084136640400ca0403507075070780110402421121400502d94000e03403051106000d8800000381010036100d43e901c0e80c000c1440a042e0000240c404000110b03014007000c600c5000d000702d480040d50103413030640750 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 535255548 1250 535254298 535254311
    0xc030501080309150f0705031c05070c1709010905130605091b0a110c06070b04021f09091d070e2409070c06021905030702150c0a0e060d05010f09 64
    0x807202d68034041d400703600d5400340c001c1c545410340a0b5000c00802e0072619066500381444801e4954505580003070740d08110003000c4003264400d048040c440c403a403041c000e050030074048103281c50b200800c860307001c00c144000b500061091141da004180e402e000300340042041070740070040302010740940400e101d5580260604808540d0305050302da08603000c4003540c8022410410040f5003110b114038000240401405224800002031301c0f06030041601c0350007501d032a8009c0c18944180300c150356205c0940c0310303400350310117004611651150022040301c480c1c2d18003040075940e1800c8008180208403c02080344542c6200140a50040354060710a20304291007007034142d143c481c02c08a0441018456a000e5581030001d043d81d40501c05400d00c1d00e0041c400103050501c0030340f010246e015010f80103804100003100b0030192981c10440300030400746805000c41c8504000307031034540310b026100c40ea80034030800b202e40c151640c80b100e040d0b841d42404a003040c0200e50352284046814103180c0039440601e420318a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 535256798 1250 535255548 535255559
    0x41518150311061e0403050105160509030601170f010509060f090712020103020a11060a1a01050c0718140a020a021c02210d09060209090109090c1505040f03060c030501 74
    0xc000c04112070700029462440b040301c0d01042030300d030700084038040c0c0e004030380c0c500e20071411482c8040c101451180d0300004803400d0201038007039030640403440841001010004c02403244c80104182e0f044800000d40720345545182035a10342407400e540f007038417034961900e002c00c00480c00001e050b5000d52444c40001030540c4030303c3c0e01c5946481c410f00a001c0f08180382155070005500c0b9500400b0040307214039005000d01c5c8d840300c0080c10038170152890725919032541d85004100c2100420340744031842c02d0030480e00d0280003007101c0b6106e95003031260f50000c003480c541031100404281c100d1048444c0000c51040b16240101030030000b500a00b4210005120350410b10004c004241001080000b858004040355641125480d43e80402501000c41254041c481406195064041c42100a105d1079002da01c803480c10040c0031044905901040e049420200c031080817a07910002801a50349004e210311103000260340c162801e01ca03d61001c1e0241900c00340020500407207070300400c1c1a0000790750500c03445e40c0c1c99 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 535258048 1250 535256798 535256831
    0xd060f06020a11130903020c1513030f0f0c0e07020c04090c0905060109030501020d090308090a020612090a0506010303080105040f0605030d031509090615090c050304020d02041518 79
    0x40c0220805a0300201d114004105802051a4074a100806150300207022000740e1003580d844100440260740640707000c188900e0310301d05200048811018050a240b000311501070712801a210107000b4110f420402024443c442d00340c20481038200810410595480413403c240d0502112504010b004580d80ca004502e40b902820300019008200d5144060800407070200812000d0325660510840c48000400181c00780050040703d00081000140204aca040140c0450001040c280380c68001c3c0c40e00b034005039940810303201440c1100041c84165a18903070100c0c40c107400744c040501280b1403803000004140d8440c0032541070b00c0c02924140501c1c10342040303070710591703010303001d00b6030306800c03409142c40040c0c82503005080740010300040310940744d503a4052004613a9900c40c103881e0503444070902003558000707022100040a0310b2100700300c04500104002c00b94040540020722070049081944195600c0d0303000300c4080e0400c0305003845019503a40118052005004201007854203090b8003000c0b00050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 535259298 1250 535258048 535258079
    0x308010608041a0919110a0603141f0b18040c0e030a120c060204170c12030702060d27030f1b170c0607050d110324240d06 54
    0x1000c4000001e040100f485883c020380100030341007134495000008484000c8584d2030902074015018140c0003d20313642400343c14003240d0840303010326080030501005489140300d080c1d80801c0700c0000500e0062602c4c0f1031054840645d004400880d030100d040108000da002950981584c21241001114180801901c201c501400d010340c0c140c0052544802140c84044e0880c03401900c0e1070300c51002c101503919201260402c0e0000d50725011075110b0000c10b040d00300122500c078a800c0b1510000b5071540340344c907030340c078031030007000078082c00011642440b417001c160845412080040040410300a500034118840c102d10f40040d40002c814034220107200d40500c210300c040303144035091f4100c03809650311100e05e60124032008102e1028200406c444040c0d06008041c09004140d886641e103510002c1e090082d502100c0b42c1403d411010030510140001d990084640d2011401cac02c0c0001c900f002c40000c81045005482c9045100401c01d0714080c400c844e0020005241900300c1048138a4440501c400403016 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 535260548 1250 535259298 535259303
    0x6040306051023010c150c1706010927112209020a050a031112041a07031a1002010e030d06030605180322151d0409020307090e0c12030304030801060804 67
    0x2203070418100e0f194030a034010f000190180f0307440d80c209681da045100482d5403200c4940e00080c02010720b481c0309882e8100c001e8014000b40f810040c16800c218400c0c102444401c0003900c0890079030310342c0401c01d04982050010030503001c0d0041d141c280445607500b0b514024445420403101c0303504007143c58006032007640d01c0e040329540c680c1e0a026a00701c00350000c14020960142c035490034460090980e072a202c0c4284124450120058100107009444122a10140c9502e05240c20440189011144150074498035401281c4aa5000c0701c2502d05a005001c401381d00085800000b40e680107440040c0c01180880f84108030070800b581e03805241074005122103010050729002006403840c203603504606a084555040c041e6000780703079500d0440000c58031000c80c140c0403942a056040b022078020b040f94a650b0000e440a00560341c5036030000e520303050b050045070411a41c64900421240c02000561003080c4040c00c1e050041451403401992500121011000101c24800100c0d011744521301140c002d51307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 535261798 1250 535260548 535260599
    0x5120a170a031803090501020d020105010e06060f120708150604150c0c0f15260c0a02011404051c02120306061e0a0e0a060f050d050603010902060403060510 69
    0x11100080182540201c0700c030010180c6950030100c4491140520401551094545110040c035190000e401d00280005203820342e403400c0e004028404100101503403000040b42d540e580c0382e041821315003140c0100440ba494001301c01d406c0220380c581281181c1e0150f02701400c840003d01ca08010802c441c07107180114401c0003000d10018151328050305074140300d10f1090085440b40b948400c000c2c14800002d50042081c0aa260741e22a034aa41000090082d100308400b88030a405405003021800310000c0c044440560300022580c0503a8400c3d8041d240b0561034010b083c0950516050103503554500c03000c550b80c0344030708480108200b400040e400310007800040203070b0300f15a214001c01900340c0188010490800034441408800c40400c0000c2c04100d038191208402d070312001c000e01c02000411307007044052024406c00c4505894202050f21003841402c40c000c6484e50364080403d000d4482044025048400411f02004010031504030034810301550f1002a42603039906030203480039140c500d2030410384 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 535263048 1250 535261798 535261823
    0x1061d0403020a02062b020405061b03190c0204140603250f060c0b0912180d0209040f03020120160c0b030a020c0c060c07060c050f070e0105120a 64
    0x40420188040d4014000c0c01500c00c030041c0c540106040782d10a44c00c540801e1100803c00d400400c503101c0d021390090102004500341410840854101c0c840ca2080c14084000d103159806010410401c036040c0030001c0c9038000c6044514040a4820240210224401c50505241c0c020000795151031602c10607000f8001c000d05607482d40c00070380781401007081c00704008a541004c6000f40000c014080100360b540d45008030000d032401c000c040c008004e0034109643c3c100c4046400311100d503600b0b07515000c0119055440803000e110004400010020009401070310103001c01c4140b099805102d03000da4043e40003440f103040420f0140403001016042c5081c075032018884c5002040001c41c0f9010101d02c00c1c41000b080d80d07111b18080c01d49420443e54026134070380004e1019104441030141c0140104240c0d8050708000e0310160607912007001e806920100402c0c9890041403140400c80d000304c105144058601807916400f140a0388442409010f0144da00f5004907100c1ea5000284440c0c65038111172000a407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 535264298 1250 535263048 535263089
    0xc0c060a0c02090406021908190e070501050c0c0307120b1f03060903030b03060c04050103060b09061207090320040b030f0d0305060105130b0406030b010809030d1e02030f07110106 79
    0x71202e014000b510721540c244644403462130741d4014081f01c028552980d6405181403030000f105412000450301303c890500702603a82e181800581e04c02560340900340381d41c0b14800c001d101032401c440903902c1581031080c040d0000b148a8400904032a050061001e8100d075502c1d034820ae12005004100010a0710400b0001c0000c04c4482c0d0202400600c01d16002c0b038045031605c00249401401d071081e180c14040054200420360305403050400500101c08403a04010790000018183e005c1e0001c0580386a00c1c5200040c0201d00c20180100507643c00090750203485521142420003200b13582d1282d01861403e005451107141c006058201409000001c0981c40413178402100900000380c02103052140c2800b035560221f198003c1a809070a08000351619071f480c2400040031b0361106003003281403103d0341007803000c050b40200413035070ba084e0412004a445141c1a0045801c91b08007240c4040d02c07840481842070000c200e000507402152690342d03c4c070750302c0f5901c4805403c99106105401c642058048201c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 535265548 1250 535264298 535264309
    0x50a120b040204090f0308070909062603040f120203070e04050a0219050a0b07060c030902100c0c090212040209070315030b060a080102070503030124050a0e0a09060b0c0c060a0c02 79
    0x1070280c0301610101d0701011590b2403120355034064604601003040d56007000841c1d03900c54060310003014008814800305282c6441c0562607a28000312901030324110402c1306040108104440060803016440d8403400d94403076500700002a6490101d11900a500001500d10070045061707002c2c1c1d82207000740050180c181d0030898000100c0d94900355103a0074840028030b55035444c0c0354800070f2880c807011541d640460300d00308007111003005410040c94940044480561204422090110041d08060407e9209400d00c250b911030703654060210980002291034603c24030b120102d00480c82a28888603944400f1015001e49001c0c0c1c94040035411b00da00c04001003a0419021500208060030400c40301e500c4102c41c2e4203aa02411042e0380700d5000000400064031074040b40e800045a52898024076040d260004000c1d1003a002c001c002c0002d5040c140303107186d54441a01005040c1c03060704000d000ea03581c440207042d41204114582c0c0303005030864407600e401c0030f00884c0c0a0340340a540f0700b14221000d908011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 535266798 1250 535265548 535265551
    0xb04031a01060504360921050306010c080f03101e0e0a0b04110c030403020114034506071205060a0b0a020f160e090a03020c04020c0115030b0a06050a120b 68
    0x4070460030fa001820100a9443c030006000f031441c40c030228481466043c0a503034042007d20442c00d54400c1301403d0003850340801560380000e401d203040880a0000e05282005028100002c104480000b003171100104020014800f107030b043c1c5099180d84148071090850b0340c8441d1190101d01d41484001810481031503000e012954401400001c0d41c07040d410b07408030290481400c0045030b0703200040030320a42da008442c001814001400c81c516614004401b8a50107421404113140c451440400c80b0480c042804c0b1440c02c15014000f44001c42035108945a842009485000100b140782c1c4a1350043c454a01895206400141c541c500d17903440c0040300a41e660255400104600602e83d104059103002c0c0001d2446c070490f8181050301034208511003a6080c006003400340131744d000c20030800000e40c01207034000c0c1a0b58110380043c1c640c60040f46a502404100100d10250503054202004002e503500c031060103403551752003c2008070740b507a0134082d2001240c01982012055001d20303500141902c2101e6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 535268048 1250 535266798 535266839
    0x1c0f1e020714030f0307060b040605060a1b0303091208012d03121b05010b0f2e0918151215020706060f03031d01030614090c070c0b04031a01060504 65
    0x9035040f0504d6007403581141c0009000b211196142c40e0201d280e8034190050a015201c22200c882c5880c140c41409807482030002080303801507218245a0080c076009522001e4001c0d08654407480d1410b59100040803181e00340a01c0304035251801130f900c100520f54100da858510111660780c0700c507042d40c40b1720001d8201c000300c02041000024a00c03480304480d103140b4410521410000c00d2a029910030031489a640713160082c0140203100000f9140690441241c0a1104210841d44080186c2c9811250320141e9002003501022540103050058840d0380802e0000c10103e80d0078040b180c540040741e01c410303641100580f40c0e0000c010203802490b0580e0080c003443c1d104030f13000540c0c0b555070b46803901003046603030080d0089020859140f059040b10182102c1a450901c0d04002190070415014603080c0c0b86092940601082c0c0c0000d4040b412903c200c0300c81c01d0704900e4142c2480d603501c0c07030741900d44d01c40d0204645400011402d900301081e0a110141a20556101d860a090920610741c00190801991 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 535269298 1250 535268048 535268053
    0x5060a05031803070807060b03191101020f0f0a0c150903080f0d0c08011d0408030a02070f0212011d030f04060e0f09041115090904080a021c0f1e02071403 68
    0x10b400180c404000501400b44643c080c0c40c0c0b03424050030454100c0d86c1c8103005600035000110903810303111080c9110068286e00001310504815180c0040b032501001d601030381c5452180030385114411400084840815100d0840d01c942a91691308141c404d1200c000540c0c0030605040302400000d0598001d01501e1421003c110f003003a1102210f04182ca620302c00002c007290105006201010b03854240d1909900c20305014000c40c1460341e903607083c0340b1000307219150031239000c5241000c0007030318800c004500360010005426800f0f1181e45c180246203159040382d41c0c074007410306060500310100a48a2a00c7c1040c06541060329002051702d440203590030071644800240b80301103550351288c0ca0a40200d020342090000400c00b002844125000e110103d400c0503010b1100f92066070f03034070700c0480c0d10a511440d41350b103c00302d100b4140d140182003801061403040e90340c0580c2026034480310f08030061026030b560201e140c008044005a580c1c402c1a000b006030880b0b00140507200c403009c1c07120041c04001d000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 535270548 1250 535269298 535269331
    0x40b0a08070c0f0605011a030709090b010c0219060906180302090402150c0c0109060302070c030f0c081912050301060c23030408060603010b030606030d03050901060b040b0c0105090705060a0503 85
    0x781c20103907502d2400f04845065652006103d421040c080d01d404080c00401c685140d401c01e954003404880c0ca5215460403180c4421846405074460003460b043d055001d040da1001003030030003000c80b996045020314000603414003400185107101d011090304c11142075281081141c115001c1c0701025000400680c4c00820444401882d911080c00401c540200074010f0b100300b0040030700042c484079542d44400205030040c403080010400e40c010780c10440c0e500c084510100d40403490f041001558a60120616000d01c2c40c0795203030346c1c61542307103150818400c14107075444484000040c0e8203070200703009540006a00c0405100041e0900800300141c0300f000142c00c6c03400d07604240d032350f1540c3e0050b001558079410a130305100c1e0a0400f4050703168818411005407410b8505100401c2d40e0715601e04030001055290303c082542d0036001e5110b00044c003400703d80107a40c0c03a2510030144040d40114807080c001d40c17070714000407440e660110b106015110010846450a10051421600d9030400f80841040500158 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 535271798 1250 535270548 535270553
    0x1e071215021c0c0908160603200a090e010605030f04030503091002040f08100e12071106041d060d052e0c180608060a150e0307140312040b0a08070c 65
    0xd003500e4600340b1000c518202e441400420703a03d001d512882c51640b140240c0030304152908910400e8511529002940807030400302070303081c064404403400c50710800080c01202294004003107019110222640707141030742d85190840d400e00c001c49081c1008032040d0041000030b44244015900003030200100d074603500001c4500d00c101d900940c440c10040302040400c01c40b005050190102c142402c200c00c200003d07039004c0098075036a02c45e41810652a000480200b048448a0111011030740504440e07151521518145c01420803140f1440c0c8440c40d900005001d031a00d210002c5985a106003c0d0840424082c5080710050300c40310341310180042132414204040c400c0c41000c203070b41c2c030542d910481c0301920300100300d508805811039030810400400300300003601d903104004222071400d002c00f0b981c1c0034511000c5665514008400d640742c010094000f07081340e00c003c407070051107200310140e80503410082c44444091155200720024035000703001112115000701d503c245c2c0594507080a40d21411581d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 535273048 1250 535271798 535271827
    0x1171009110405010b04060210050c2a01020307020c09011712090105070614040b0c070c15030f0c0c0204060914130503070b07021b09130209150d051e07121502 70
    0x360000b0b8805c003030100d01003144903810020000c020381000c9003041642010000304031b00c4d00c40c1204815403150345230503061015501d100300a0036483c40700000c44d01c908200e1300094a80702c4441c074440c80b80700340da000031030344009030700030030041c008a1402001090a6003403c04c01641240d0b03022414000180304107800324005000d0480011118024980c16140a141c02e0b2002440980109240c0105002034000510741d8400c1c0800d860800d040d102103840305000071005005d10000e5195118184179140d982550800400305d442c0d03100f26401d00c201500c5000c0041110b00c04600700245505550108010401c54143d2403d054040c4068a01e04105501d40d8480404103551501c0180d00035400d0000c05a804282c0106940b4101ca6841c4141484040320b0902a02981c02038860108600031030000c14480c00843e4050724068440441c6ca00203040c400c1d103a0740710380700b100c0b0b405031502d040001444c000302e022400c3d00c1e01c0500c1026035080c3c40d1282c607a0a007408020081d499400c1000e8040d07141c0b403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 535274298 1250 535273048 535273051
    0x5130e0106091404020307060e060a030506030a020409062a05040b0f040b030c03010e011d0103200411040602100b2101090606260609030a0f09030c120b01171009110405 74
    0x3c500e142203a050500c18903281c4001540040108075201610b24400d603903420442e50010324503d4042000c4e00c03540c00083c00c04004000c000d50042c9050a8081000081c0d04002103040003100d0501d901111502c8078540012941c8410300040c4040006010601a9601030078030482540c03501c50409480740c0e0b10f13191550003503404080c1f40f40f010004010303610384445c449015005070032040030410709821803c1c044240c10701008007101922802480300c001d05414001a40d03400070001c1c000b00c050401000310b554428010b080040c000c030718078049490601c0c05070608070440039100086107181c59818901a1070a22031450095403146030600102d0020301882000d00a8110f8000500351030144c041007031601482d890041d90050380800040c81000300690342c0440c003904100c014036106503001ca030200e840c0e400c0284041d650307172030100798507043d04120a0310354403541840600d80d0729458464410034003586030707240300c0e84038014498000c071054010440403482030007450340365000900081d007500c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 535275548 1250 535274298 535274321
    0x30e070315140c09090601030f020c01050a1a0109080d0c0c0902040e1504140402090603070504050a0b10021207080d0b03010f1a040c0806100c08070807051605130e010609 75
    0xc484540c0949482c2c2e01c814a9040668035880c02d182850240c081030b99803900429641c10715984101c43c0c1c09031900741d01200d1100c040c001c004c0200789000396100d001010191184454064403981c2413100354001c0460000350388003140105034040002c00105c1c1c0300a0040000c54241401c00000640a841c900146c4080c0c500300480c2810381c507220511084462140c0c1c0668891801c1820b400050752900d00000c2e0042d8050701c2481c0140e03101000709291659a0348a0707030b00945040b0802074101d04035808545501011200c0580340801d0103004c9039a9a140004058210020000c1e80c00246842004050310354000d6004188d070100310002908460100c840854441c1d1140c01c00c950501320300c500f81194600440381001180b1072009c0050030754200811090240e078913284800c0516018611030b031680343e0700c451030301d0351120b091400480d15002000101c4281c03080700102c410554841018005075800904030300c0210180030720000150498120040003950307a11000301d207407041405051350f1150b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 535276798 1250 535275548 535275551
    0x210108011b0503070e040507020c031506120106060f0e040617210327030d02270301020403020f01030f0b1518030a1a2e0303030e1c030e070315 63
    0x45a103141c0341c44a107901180101048410000c0040e515007200d02c4814021080d80c000070155103050007680742c03d10a008181c0d251043e40c3d0b1034100100e0081c004d0348110030030358044200406130980c8500340e403030500858022807503c05405207a20f21684150100301d40040001c1502c0350395620020003103d408641c01010b800c07100c4021102c4105552041d900c1d203419559500c4c1d450b1943c110b4500203150a4854025032180025501036507042060b203001c46415401155070324454403440c50780442c50031007190010900507440c40c00e0710b418802d403003c0701d40180501c0c00780348061004400418032030510080260344d0720751000b229110fa071685410010f4150304107649102c1c82d15a0b0500c180e4403541640310b62300c80305ca4800012020a05401081c1c1400d01c3c0007210340303820800b903415208607025154040d21140f210034201d00025070107802c49001c1c2d10f04000521020104c140c440b5081c842088580d00808114440d040c0320350f100d513903017001480176100d17200d4a96480b02c1c80c0c08d640700520460507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 535278048 1250 535276798 535276811
    0x3130b0c041e03030f0c0804031403041a120f190912110a0c031b09050c040905010824060f1203130806040507090b04060503030d0c090b091521010801 66
    0x2040c00610305a50700d10006002110903255640041141c10111545c03030070040c10030a01c81c03c20206601b80c60141d42d100400d40e4444407810206683c0ea0024031514a80083c000859010007000104641c0051644000d000b05030f541c6074104490060044c20300111012440f012942414180c03256600c00e51041b860100090381000c001000002594440d034402c1d04400c190b1000102400c2c400812aa0b1040341c03008180e420b83c00007903006210394098480227080c10100511090000c0080050701d1510808008998030b40704403d550385401c0030f141d00c50340501300d2040b081c0425030800a911400091994100150200204610341d01c541c80030100c50f4008200458200071092114010f091644010130203460140c07601030703407088d240c8a0029825a200019030032a20303140c000001500d0302400700c0e66039270f04c4008458000c1000400300000242c84280101d42902d28404841e40d02c1c0000b404003136100d0072060301c10020390000e01040704c60481c60b812404640d00c2e8000880c0200440e00000911 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 535279298 1250 535278048 535278059
    0x2a060c0b0c183c01020307110301020412080d1104080c120f01090b04110d030210020c0123040b0f06180a06030209010e0f0c0f030f1f0801021c0c05070803130b0c04 72
    0x3141c100c03c243c030301c3c80205242e010a1a6400415209015041144070340558030351404a8024419604a001e0700604500400d0501c80070304000c0c02c9c2c144204030100034000e10044a003010303000e10b0080c590f0325005240066401e01e00007051380e82c0900c54006403827000805105003030071510103076011101070842a04000a105042450b24014401a501e81a40d84959680203440345c113010002001240e0100d505141d260302544416094045080700d94904d1990f00c200d843c3c1408200c41c2102d410340d1140c0000c1c034118494510078003501c4060000d080c1300046a00005903a1401440c8801d80d6669072400000750351200e0101e4020001082c00c00c0c21400c018080750f030000720040c0050f80980d010828840360b00000c80450364003113040d5000e94075a4564a82c0344c02d4180f44100c0c512903040c0320181c00700d200b072819030040c82e02c0c0262005d115640800ba0750310f2030aa03801207100e2004164188440710200b03a145005580c03000040074501020a029524034100303040a4410074404800401c05208 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 535280548 1250 535279298 535279369
    0x190210060e1303200d11030f0a050f070210030b0f15030601260a02091002030414210a050f010c08100905090a150902090a1b050a0c2a060c0b0c18 64
    0x30746ca0301c0140a54a0b001040c600c0c1600e500c05c8403000410030800050b4401d08650000540321074950013000e45c004170031844c4008028006030401148640070a48a150a0b490400420008107410151031400e50b81ca410041d95098002109091443c03041c1c1c0c3c60443c3d0b4008030308043c1c4035207111140141c45045040074007980d0103000c0395400955104000510101180c1d10b0706154016048618085000d00c031420010700d540104d03806026841440305010422101250203640c020100000300040e1503502d03004c90314200162040c5010700180c80080c0a21a840c0c1c0281c0d900215081c12076404002e259181003440560202042040e503584800404620b04070419070303000710f0f4040003401240c46002e410708501840d22900e000f031060021b81d0706040ca00408007910041d801c14000c96169583c1000311000a002d102240c040e00210071011810318020a010803440d034100c48048a1991035900e10241c680c000030404247c441c80e0740340c0f143c10b0740e0707031010001d0032120746084201d122050810250 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 535281798 1250 535280548 535280567
    0x24061e0e070206010b1606090320070e18010905120403060b01080717040201090f0801140108060702061308040506190905040209030a1b050303190210060e1303200d 72
    0x85844003501800042640080ca02d415141c0494081c0e0391481c0103802030020385c2401200415043c1441445420f164004681c0c180c054900a4005c0c0c440070030700002900c4035441e000b6900035285075008210200d482c081048030038800e0100011310040310f61030345480e000b550341e0b01ca5980a0002002d10400a42e8095203500c08002c1c00c0241003800d2078080540041802d0b402820125411800230301507a201e9405a001419400302d4000b0090302c2c0d960315400b0300745100001c4141ea24480000840d01d600042c514801c00c41030703000e003000b9294105054122401d021060b01c2c01c0d00f0922000c5241e0340c1d6a4005e000b840c59018640100001d007080143c0008115401184110304c1403200c0c044a48011410344412503002a13400466100d6850321070400c007440c1c00c181d8141c4008107094004540d059100203a00d400c6d6000c03103500c1c800840c410015110341d030051045200c407a031701140d070581d028a641c655451090419540300e005d0800c0360701c3c1d4041c103514642c00646c044442c42d400c0c66007103100c3c0e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 535283048 1250 535281798 535281809
    0x7020c090c0a08071808010605030105060307060512091c17061002120c030403080d0203100e04020303040b0a020c032b03021e0304030909050703051909030c24061e 72
    0x104180c600003001102501030140d040083c81490400192800c3c401c60070010000f044c070284801c00c0b600c0700740c140e00a12030390154600030b619003004200c403403800003405400c4812540d1a90b15060302a103944050500140c4182002c1c030503060010090030740c2c00c040010380721907503550500741e0404204041e40f00d80c01400c401d00031385603050035908059011507041821111000070396581c0c1100c400700b51843c8513960024003040340218010b008181190015406004960800b40059446803907001c5104400d07079009505500030441004990200c0303000e000869024019640030804002c0800d0616140c154121000003c6203c03031114901400c200503000960703460114200700014061300e0000c030300b601c1103e210030008000641010b100e0b41040b4041d01c010750301800941407081024010740400d503403103030b0350145400c40701e103204040c0c0c465600426099982d500c18104a03469900040c0c041d0038000103003000c666160030414903039018803001400c8261480c240c0b10140c040b50207900881c1d4014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 535284298 1250 535283048 535283059
    0x906050c0909150d020604031202070509070c0b0a0b0d06060503060c070317150607120e0402160303110c120702030f060f0c09031f020315040506010f030203040c0308070b07020c 78
    0x507514545900c0e486a038030954400c0c0d104808001c076000101300350007210009501000000e008000c00103412104c0800c04030035000c07101c04a464104102c2d8050080303914400007209031411101149140051907004a140d21000800c181c000c804100580c41180096803c02d480d24000c01103170a081000c40e901498041f141400d00c2c0d030994009101c0c0b02c030747d00b001d5a561000b10109a1700c0c4180d070040d2410b0040289250303030f9568180b078080440d41105240c000480e221000340f2800b03003418001c4071070392542c50740348180900651758240e0080200d10070074407403840e080c03089a80c001406c00400c0362384400300307810945900d030500c1098a0311100d00110700107500108180010260458104c031b4204e062090358903260014480440c1c600f280c200e200100e080546407e62070000c4a50713008601582d1440002c4000d04040c000740415200140e034400c0c000340556001c03860151003039001c3e540003485205003000896594a9000c042d420510080d40c098034007005111440e90100b01160504400381c50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 535285548 1250 535284298 535284307
    0xd0b0111010606090e04050c06120a0e061306053607050a08070b0721090501021509030f070606050603091f1b0302070f1a0115110613051504060906050c 67
    0x50a44d0720728804c0441e5082c40780c0106040200034805c81d40c4820024280d2502e0340c58a40740c1040245003519070003506460052910070742080881c001d8883c00d805e000600e06c0041640d6102e0003800000c03c10044503044480c03c030311200404840e00c410580d43c50504401030640d40c038550a11599500c100d104912080c020071822801003103947c00c4444980200741c90740c8480c1407410003249040c8425041005c0306a01101e00e07900601040300b6034000303a003141e01c0c0381d681200014242005444050003540709102c1a00641d8405008007151743c0b14200101e10f8603902c801040003604107441c0c4040c01d401410004140204000700e41241d00701e020418001a42c2d40f2089030300d407610441a090405400007260f600340b109414a40c4029580b150440115200c1d503031f2010f0740e0f1102800b400d01c100704880740403040c0f24468031182c026000c9a601501060300c614080040110400104070b400e4000e0301140c040402c5410f90051240e4010300c0042190040fa2501c00112180103001e243c0e83c0c1c03414031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 535286798 1250 535285548 535285559
    0xc01061e090203090a1e2306040605100302090405030301090c0216060309020d20010e0609090c0309071503090c05010f0203090d0606091128020a1709060d0b01110106 73
    0x45903041110056000143d80761100d040700d0f4240344035454041c18014034030305608907020b480c9000d00320b0240140f504200760219880a8454144d4001003010558414408500401e42503030000390800020200380d51015920f85c0428609101200e042d1110340020004110181c4940510f450000180c806010b603200c0310f10040702c503103a45018010816580e05c1200302152108280c1013041e0341c1009507014440b03080d1848031001c4900d0701d0000c1c001805201c192545040c49029945d00c204010129400759540c40c0100b80b094100401c121218481e60314005080f004202c0701c000001616603020800d9072031801e100e00310f0b815541c003072410440038059105e0466070200c181e54140e04200d42492140505091100c09018182c00c003146052404109031070f00d0412000400c044500240210320492001d24900d400240c2d81d90508003582240c250000007601480d02d91010f4072031600c1c2c2c0c5040c41141d1000c28030700c2d08000381c10030009903a08038900140d030300008008600c140d100000c0c0002410075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 535288048 1250 535286798 535286849
    0x2205030604061505040935040e04060f090302070e1e01151e020c12030c0307080c100606080402030f0708030a11011803030914030721020c1201020c0106 67
    0x1e102a00842c3d55a500903c05822940d4900081400500620014181d4100154820003200b44080b4041c01458903180b00a0180c41244000c1c250784001d90910307142503840d0440841c024802c0b104581e80720010b81d90001c40b40f0641580e03d009034014030a0785d0402c031040c00c2a00340a040001c026164420b1106010b0346410000d0549078a00305802c00420314032000d45120700c0d042c0d0001007450046200701040780d070000d0218444601210000e02004070b07110a540c4034800d20356405036a0f0001c12881c4042110140200f046940d100100c465803506400c01e00c00300c0701c8a4110400143c105800d01041d0300d000c105107410710990384080e1603068034000703400ea5a072252840d0b038000d00000f4a01156604002c5d403000c03018a40d40340050804400c42d24008008010580c1c0458000425190001c61481c00005603042190704c01c81048410356640c2505001c4401d0411000840c42210342100280c2c8408591510904010700050b8030790101812650035030b5a16084040c1042642c4074071441069103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 535289298 1250 535288048 535288051
    0x90703090b01120f02040c030c092421060806040311061311120312060a0803040807051507060e06070306050f03031608091f090608010303231b0322050306 68
    0x1803c1c071480d00740010328040c0000d1480c1540a07602a2512582800300368058000c1d180701403807580c40b505003544800030117402414171020140c0f18131007075980408041c041c401000101002513441c510800f1201c0c0301d0820340b0225005000e0396085202400105034000c3c000c030f401d801c4080c0c064071840c5001000352503000d0310b030600503065440703c0e1030346210354444000440d5081079400076070740d8440c4803003004a6904420344203a80035400f4101c001525050110175502512047c101524066203403000300249405040c4c2c3c080c0c210a004c200060000c2c80300d00c21418a1440c0001400c80c80c1b408020103003c40328640c1c046801895540c0c0010016078010003200d8002c1451800c415800040b420f08000c2401102c01850f0442c0c40040c0a080061107586601540d00382a501d03000d080ba01c500088a1248084c40000c0104044026140b14403103505102041c000203400140d003060f078150300d421a01c01190290009540000402511608000005124200308801d004a0961404001c01d940d00d40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 535290548 1250 535289298 535289309
    0x9050f040f030f180906031a0c0a03020a02030d0903020607090807120204020c0a060c02060a0c0905011b05250e100b07021c0503310515070521030402090703090b01 72
    0x704002c0340d003000303405142c060300407010809402680d107884170000f400820300e80c00181c4024047c07803140d21a0300c1d4110265071042001080150802c2d9a440040d000b9400c408112000c1d070000380400c01e0b1004940c4140424a80a0f9005101c00d080400020300410740a400c19030f0150410368040c410784490000b800e0040f0f5041d00e00603542c0c04044040c41c00c004441800400c21420051592100740d800030b00d0a0040d91b941d1804c009120010209440030500361040700c0c0400c0001d4a00f01e4040c60490141c500359000c2c0003030f190006940003070503058000200030a186d24120320b07003e1190040702400a58400c03540303c00726001606000000c0c01b0790042c884000d03c624890780c03201d6100c86403680d0044c1152391003c00c40352079000c4c10021008005189127044c07000c40484503510f103100d50a071a00740842d0300284c182d19441609020421181d80446410760b0603100f01e5891300d60341c01480940c0300c40b4944c11010140c903402d09104204e07086d10054658810942400e01a0000c07518a040ca241142c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 535291798 1250 535290548 535290557
    0x31805060304061a030a2d020405010806041e0b0f0c2b0b0103050c1e0d2c0d141e030108070609150504050d0201030e0d0305010306060b1314040b0a0f09050f040f03 72
    0xb1f00000b81c1014039404800001c1d002410500005001d0800096160082d4854003156403403d0044010800c107401c58100903000c00131410100d8a04040b59a10a40020740d00c0740d901c0c9007405401da801c1003800340c4500000d48580340c580c11aa001d246119020048000b468188018208249074104a02484006220300c3c00b290303484041e2030310103030125400d0b040c0002c014041e543c14519020010720741c1c4440403035204102d40c040012072201003040e00040c901a120307041c0050008541c001d42d6082000d03080031112a02502e04a1031035484083c60003030010000030b03e20a23003410001407940a055000c0740f04c02400d0b90f0030f060300a41000541d801d550081c3c80e0901900d03000d0004074083c050090303c1450a000d949001e404043c0d15402950603240144820b01490355207003490300c10340c03059404103a10801484028040c0284868250000410046c004602102c00314006510280558071000b01c207000d406003004094041c0c0502544000c100440c0007081c606a100e45040014421000b401c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 535293048 1250 535291798 535291853
    0x10618020a021c0302120a050c03160306080708101a0603011707180506090903180f0d052b0c080904020c01062102120102090d031805060304061a030a 66
    0x1442000040c0c08076030031802050154443c124064000d6100700d0010181011950004d514243e40e801050302450b5420710b1540307540d42e0901080d900301707405101d080416440d0030000a06d61410044c2401801c805006000342e070445e58a140200d4aa848440c55441c076883d00009036070b541e02c1c05580c11500c8110515040244464070a420280a6002070400740000f0112014485079940094800d280548aa00d969211111025074074000d90462080344050541d01500900f0180510002400040c00d02d100417100340d61034504059a484c0d03c0c0c500f1408045006000580d003544403500815981019050b07540680c9514105210307211b0028010741e000200f00e206408250f2105004000491002c0038000bc4211070503c1d02c000e80f0f4050b403054002040c010200380043c422a46002c0d4000d160103030b1160b0030741e000c0c2d41610007285010402d1481c6140000c042d290703003004622861081c040004c54801c035040b0b4815014004038030700e02a41c4804030f65400a01c015001d0070041c0820031161001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 535294298 1250 535293048 535293067
    0x705010e090c0c07090515030c030d0e040b04050703020c2107030c2310141e060102031c0b150702100e03071806140d0b1b1b06040309050301061802 65
    0x880c8520002a5924030513001c00244529482c3e0004d801034034500c901c1c8070100b00a8003016a0b0b28102d040155150b000300f100864010b014070b821401c00c50000c1c1010480c590102c0000c0d04440702220180d0102e07400091a08902c40e0502000700d41080c0345c0b18615901c1a010898403090240340001070500c051804c40100303129840c1054600c0c003245900a03c070b102d0024209d991510b00306400c02c0009070402824804564400107903c0c403070240c080494014010b02c1c01c200c0000100604584c0c15404108400300d041c901072004000702c031603442404541c01c01c0f15000e00049143c0d040030040c031003009010040040e5500c8071811151003040c60302840400004001a060038601d50180c94007001210008103100d40e079410103800c0f280100300c0b6800031003400c01448403407428104010184d07600b0340001188001d196500041203800c0302642820809001c480c2d1700a41050401c000341a440346007004101503125010340040e000a40017070080b50b143c850031010300079103521003484668021072100c52 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 535295548 1250 535294298 535294321
    0x513030203030406050a180507050901080309031b010e100305040c0609120b090c060a110c0114160302010204030c090905010c050f0d051f170d0e09011202010c0605010f0e090705010e09 81
    0x40010344a01e1f024030010b518080d80d64502c1d03446603034003603c1a10000103100d207022050340d260840250180c400440255042c203070420422043c01d05005200700c94910540b9602e40052905446481c00030b0700381858123100003121001e03803140c010840c1d0654184a07811a16440844032640240d03500303415126030304001c1c18003501c0d500c9190001000724050001c20740c0a28840307440043c65080d035500f030b200f140044074800e03921941020f42d01000c21810300761251002607400e43c98040e10005080645030b80d681900c013107083d0310110354103440f1001c3d5000c2c00001c1c840c0013050041030410515000c581c5e41c10504038044c210078a406a42c0c2c1e8000285c1140e59001000c00c400f086405100e0340c144c846510344440401508071118a1107406070f140031940c0200d05039003216000030891042c9a00c0d02140400244a130a0201e04001c0c60046001c0050380070b000f044d000c2c21983e072810384801e0400420505a080081c5101c080c0d60000a00f00000c0e608084072441401c01510030441d2690751965004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 535296798 1250 535295548 535295561
    0xa0f080924070318080718020f04030c1e0321090e0703052401050f03130203010c0e1e06070b060607050d031a04090b01050111190c090513030203030406050a 69
    0x6070020000c0d9640c00034001114014102140b09440392030040160f807108020104990040480036808080244007000b4400c09039081d00d05054800751070080185074805050300b0070751088820482c154801d0001041041c3c0940c2110150182c03201001d10b10b07207842103810303841d03140f9180c0b00e0415504100c07030707920034608440034103414a99900d0760f00700090024010308044071000c10712040b00401418507041072203c40a000816543d032411b10701c1d80903440c03c080c0e20142c00400b0300320011100d000141c800b0b0040d1090380c40076032190b500e0f10301c011051010382280c1070362034003100b00d5880c20004a0f5540500b6502d5841d00800b04081555031000855441d22542c60f01400ca44100c1041905080d40f503000040d560401c101d840c0c0003c1c4440013800150b4800110081c0401c0179040184002e500c1070155100301030320001104d62041165038014034000c0b801c402074495130004e0070244035055080c050a82c00c86180301c000d030404111a107009440b0700000c1c2006140c0c644500125190381600d41081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 535298048 1250 535296798 535296829
    0x41d010f063609020f03061504141306120507080712030c0609051e03040f090b0d03030b06270f01050a022a0a0e040605090303130f060f0507020303180a0f0809 70
    0x319a0341800b020305151715002110054441c9200d400030036160b482a4058400b2180c4060f000007540c60341d94104400e82c04804c1c1107400c00c3d0381e1450000f40c009040942d032942d09029201414000d41441c43e268103050141d04081101c00f00702d0102c0002070f0340306080c1205560040c1d400030300000245000c60900c18691001c007201c21903804503021008006c00240100e43d506007180408a071340ea60070703005486048200c21350002000a084010a020740c20042c46184010241482c01c4203048205032038441201c40300e848800d41154100050030031241c1400d6000090034490306216240c80c0095459480c0082039903200700340c00b8600b6200091490001a80d000109242d030303039035101c0745c3c180d00d03c07001250250741c81d50070300011556020022089901a070105c0b4122002c401070b40d1108460590081c0b4101d442603910310740c01e00200550f102e540e018141d140d0103156a03041001c40d210b0050b0741b8410711101508420300400014803034102140b00d25a0014800d83c031800d000002515504540586 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 535299298 1250 535298048 535298051
    0x10506060a08041a090d030b030601380c030901090503120f0a11100911010c0818010e0d05070302100504241b0804060908030c0303010b0f041d010f063609 68
    0x81c40742d48440800c211b1224041990100030000c046020150341e002d00317105501e008544540701f08000d00c012495003800440003c4501203440781003840603680d40c003a1003a1901c40d00003007010091503078009488001818110020598034160a052011340c1c0714840c1c42c40c44120380010b2080785180280004001c4480da1b4081d21515405065480301403c2c01d0039007101e25850310381e481c400720f41c01080418011500481d2880c02e00500001d0f0500c400c0704c0d130784428140f0003681d040b207000b0b075140032100c00324600c12005080384e24034510610000c40c40700a4a401484000d1000703000f40d0001e42d00102d80034802c1c9032090840a9200000d4440344600143d000d030000b1585180d40600c604000200101c5006554002e00b159580052580380c0c01016414055500200010415060010068040d08658070320082c9819910000c00c01c2c0c1c1e00820010104003e00980100510329a2003039000c010942801c2544402c140c001c072076064808509280110f0301e0400310580034620070050309501078001440b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 535300548 1250 535299298 535299301
    0x915020f03162409030801060309030e10021f02130e071d01110f07050306060604030f06021e0309010b041802090403080703111c06080a03050d02071a0a0504050f010506060a08041a 79
    0x3035501c00713815282003d03008502104000100703148603209100440d50103940b0039664216140800001c500040d0300362045214842e40c5040780c003400854002011907003840140c2d1458000f10b543c044483c568000303994003c0b80c1041140d81c0342c120900d044050701482c42c00c25148003840060f13a13005400d0210f00c0c00ca1044082c0854041780c0083d00f4402d5500031400c07218103584540c2005058804c500000705403400070a00070300080c00301e0b000b8060810040c40b282113286100d0f036840300f090b0412182154180e450f03911095417401e01c0d05c100c0040848100701c0c3e080d0f0244a030046403c1c01c001501c01420000d0400014110324447d52020f035405522602a994130058440300b81d410380078041c40c01400924200002428900c0050360811503941901c400d07041c400d50f42034840c000e40180200396140c0c000120200c0e000d02000041500c101e100350800581070416082a1349040014070b5004101d81c500001d21010341c0d100c2e019114410306520b44100c690361036181c054034103010071003505499250b400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 535301798 1250 535300548 535300613
    0x30d05041a0f040e1e010b0918090c030109121d0f06032e03020906030f1504050a1205070b062d06160c051f090605070218070915020f0316 61
    0x6001c500f03117503111030145d442c0703980f01c258200303c0d40f196420090f0300c0100c03916900700044c20100400c0d4031614110039220607000d50800719094400d251000c03601d105882c0c8080400d6600b00c01242d08003500c052101143c400c45078089090811492101d610468000c00041c8503c403c0e0b601a4600388640420107015400219141c1045103032804200c1c4180c4040c00021114200000d0300c089102c415402405400101c42c41000000c0001c2d00c181c41c5c81c002c0800c848045564200e03030f208810303000d65440c1d039544402d04151460003000f83c0120310600007040c0c00c540e406100c0041e01400390300b00c030005500c09284400601c6910a0490190b8413203aa15201401d11a43d00001c4040307541c00d032040548941448407660481040d00800408580e04d110180a0140300303102621405101a154002c0c92000b08c81078000340104564a0740010150082400812002080004603031001d000410345928000d0b0800d45a0051140800d05500d8030501601404618a0b180c84e6804450213082032450029 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 535303048 1250 535301798 535301821
    0x40305090f22150b2508070c060915320d05040609060b12070312121d0d020c0f04090501090f08130f0b0a080406060504020c0c030d05041a0f040e 64
    0x45028007000e80b00d01400180304400003003145d100032480f084606002406458104442c2d56250058511032020301c0b807080000d05a24440d00500060340310002124034210100000d100895540f00400415003034901c0002d003100c030700146c1145014448520354551668412290044812044d070003400c02041c002884070342d501045915010f01030038010340413048244120107104050000090344010030030404100803500030410040c142c03420301d41d410740c000104c10568040501942c1b034a0042e055190900008100e410250801d50016041d0a040d150026048101c0c410f40703e402241c58062500400c2420744c40000750b654050754005100e680745c00d0514050701714a040c000082543c20740410340308110011030b0f0031100b1391142c091504005030021104000081c10466202d9101c400224040d661030015103c0c65510303d00070007240c00711400b05440d180c04e6160003001d1103410002171000c83d0031411420701c0c40382d0514900e48d44030b2610500107031a2051342d0006945803268800d000c14034200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 535304298 1250 535303048 535303061
    0xc1e0302071a1608040203010207020901150f0f050a1202040906060c140106050906041802090106121401210503070f080c0d08063303070c0b010608040305090f22 71
    0x155021070b00d0346198025040b1042c1c0141e4107190b0740d25150702c14074407a13807040d01d0960b4064070150016051844607804645902001c5c0c2011180008a01d024920070b58462070a40c21140d580c0b0301071424207083c1c58080e219118a40110b030800403e80150100c109041d012203005100301e07802005a08d540c0e00e401880d060540c0d9007112444092645212811014046c88055906c010f06142c001d0300c0d144c00700401451074040b080240c480c840c0813100560340d19011580203000726122803050400c1c5140140440e1140c00e5950071180907d00140468a00c0c0c1102c10b12050315024103c10200b03060030264910f008541c80205417a02c0300304103404000390f01b405404689500c0302140c00c2051070b56406da5440360f04850050b08604100030305003030107040c031610142403540c19014030420080c100040b03019510440e03080c008100d91080b844100300032008094010006880d000c5118105560700405502c40c00c1c08441c49807071020020300c80d9036104446116075440445444506544c03900740310014002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 535305548 1250 535304298 535304303
    0x209131b060e1509031c0c0f06050105010e030105250203040801050705180f1005180d050303040506011d010603020d020c01090c03150908070f03110a0b010801060f03150c1e030207 79
    0x10340302d110b103c4818003482076404888004028001c100c06100003440808080074600742000703146541c00010810302401015818015040441c0660410001600d505402d804c0180240e2402c0100301c0c11102800210324032106600c0f0015202c0300c996012451401940c2040001b540f1b400e0a1101d01a00722004014031009204c800302e26241550401500d4030322000c100d500850b05140003c1c00621a00c018070f06094004000e10000358003202060000b102c0c803c040f9802e501c00400d00081c4801008000e00608864114a406c004890aa00315000f41271203003500b1700d1f8000c10a0455840c154056900300524000200102071984c20842c1141d442c2d0302c02500e6085055003a45500d030000d00034801f04c2504072003501d14100240d0303600302030095900d4042d000c120341446030213000141480714104c03c0740540800780302e9504007140c090854070340d603100100300800c0c000308000080e4040e103403000030144070720b000402000c2c0c2c06083e0b44000300303010414082914072a0444200e50181d014010450 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 535306798 1250 535305548 535305559
    0x310051b0705031207140d0f2a0305070e04090308040c14010c080d27110609090c0702040b03060a14060402090105160302151303020c030a0209131b060e 67
    0x400805034002485a0a00905103400800000d01500416900e45400c07926500c0c144d6056002502608415000403200007003c076150440c0c8020031031701f030090400da1161400840074000ca28502581710140d0a10b417001070603100c0300060301d0309006480751140740502400900904400749001003100c10201c03400c0780c200050a0022958100c280b41148002c1c4040e100d4048510041d21207580540140f218694281d458100d80001c1600e4000602070450f9000d0f80b40400054502c1c045411016040c01180030307917014403444a4954680c072034142c1046034585000c0d5542480d0020074090030102c105e140d0144a4102032011000d6075912040041b54200f428501a84030f98040009a110b4240524002202400a00c0b81c01450a2030110b2a034404d00483d50003001c9903e208031a064112501d1001c0d1501c15205028503030103001d505103d0300110302401c2c80c0d10107940011180d10014154580c00c40c807110300e99080041c071544a2840481c04540f4240d81541e802c4c00074294821500c80c0d81c00740 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 535308048 1250 535306798 535306831
    0x204030209131e020a03150903300f2a090501030612020603071107030303060e01050121020a020f011508070f0b1206010516060e011112060d020f031005 67
    0x206842e80c41010035440aa101c41c0b07403000402052040c0d510b404180c0e400740312100d0000005040c4007513594084250280815480414100540640c05140d880d02ca0241001e4a0403410083d401114904805000d000240d0540c0d14403058018800c1c0c00c1d850301800680780030341420b451081d41400700300c000ca40e140011546c99000440580d8000d00c6907640320304404802e00c0041c46c2c42c0c406907074082c030b00e407034000501d0300c4411007946490340d968010340100381c1e51642408015820441240500b5003820107820880740e06000720511070303a030342c5400411540450344400c840e100380840d00700c0203481030091212406031709809a00c08803500c40c403d4a80301da030800241e01d008400c01e00c41103448500d6950b0038518140b070400079260b0000d1400381000000c100c022061050441400015406000c00150148a100301e890840795051a549600342040c8095581000c20a00a5600450035580042d81601034400318105844d030344006a07150007100281c0c0482c10a503400f05100341682c81c007110b101d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 535309298 1250 535308048 535308061
    0xd14010524030103080c032506050a0209011b053a0f0503070302090423090f0106080a02130f110a09120b0f060118090b04060819020d0f0f060204030209 67
    0xc40c0310640740003501c800240010000700e001d60001e40048074080082c0c80c0b030031880d070180002d0380c030f490602d43d8100210710300c504080c4001482059481001c0030320441c9000c0c4401e0020b4100c0360094600411a0a240103980c1046400d205402c800c211419110007041d1150541203880e0b50000c400c400c02e0301c10143c0118217030384110800b20084490f501c400c0d180d6100c0c0e0804401030f50103400001c0d0441e450b80754204004201c0500002004158900030103603080c4080c201d41404104144a40168141042405280b07404100454150342c102c4203101007100002d0002c0c05041d80301a40d03000d0700c0c6802d07404808000540000c12281ca5599506103290303403200d50039115800804409898100f00702c0004100c0340d2400c03411500070005040c9000d150280840120300b0394480c0c1c004221168455400c2e59250a003070141d44058400036007e4045480d940d50008101220f0081c041e01c908141da000c841030000c0e42d4030741e00b4039035041581c07114100901d0801e40042e50180c44101c0c00f51a404002550 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 535310548 1250 535309298 535309339
    0x1707090b1b1c08010e1305030703030e010506010e01020c0d110306090c01020f03030c09090a0902030a2a080d03020a1404030b0402090106031401090e030d1b080106081510050d140105 80
    0x540d240b46840e00354450f401c1c05120003410000900d604051041c0d40c0c031800100750100068844903110395404210302d00d03150f60203402d40c0c20180201c1d0610480030044400c0c1c1e83c011407000c91b41c10050b84c0a00c4502210f003030652103142070300c2c003a079098041d50050201c401008034864462020a8003100e07200407107003040c0c0e990784c40110fa115008110621011003145499041c0c541c00043c418404592145960006400c004d0800c80848140960008500c0d401209841d51030b462082c81e8100101c540c5003e0740192100c41d210019020980d000404444080c09140314900b50042090226182d03500c0e03140c0480c0d0120140c6080e449062000300009840344a4007030082914800186480164a00108500035110448420140340024044404a10f8880c07040b02c920784110842c00b41070321704440d0047c052140680114013042201003c000350b0303282042c0064140030040d100d250b540350322900221894000da0102c00155030500c10030801d11440c03401a141a00c004946001520541881c1101d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 535311798 1250 535310548 535310593
    0x2010903390f1d1b0f181002010606140304030912060509060a0501032a17010504060b120d08060a1205010209030f0d1407060b030106080a0b06060a1707090b1b 70
    0xc0c2c2100700381c0f000800c0c4ca901c8220360a043d0039100c020504013150f0320081c0007580c0000032803070419030001c3d41c0b130340003454510519005a02180000c01803e030030100c0040204501c02030380b4041c04d0000003c1010540f117021540001d086a61508490403010314150000d0503055541d00d20321302c40d02c40441d000c40300a01c1f4040c103c0b680b10300000729403226000601c100091524910041c04e0242c0f0000651255034aa44141131004500000721440d1620b000c3e0210340d000705072070703008a002c8403000120000008450f001000103044c03a0f030031559004001160344c42d4581002e0300a8a0b440200c2e400c0240540191407000d004400340d0303210141507040310b5503501c40d1500303850025541c074980f01c000400d00b07401416801d00401000c40c0d92200304021900b5101d80744c2c802c41d2a54000351586050122500c0c2c055009141105d90740e19040e9006401442c800010001100c005001e00c0820328490003003c000b4001c1c02d810040329203451510b8543c11041030394031169891409424010300f180202062602d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 535313048 1250 535311798 535311839
    0x906061801090c12020a030e011802060301030231020403021212030a0b0301090515010e1506040612020d1406030c04110409020702030313030804170a02010903390f 72
    0x2000240e10b0031a03254060059107085405000300910002004100340c001840d2640c0309840109610100c004403a0855602030314128110188041c0d590060382d4075400c8a04481c1c04807075084c0d0313110300c0445106400b00b00d40d50081101c1d900303848000c4c5400d00c0340c0190040303078001c48681c50300702c0c19110b0087e11401a24401a0319640800c00215000c141c0d81c000700102c0005800040d203045980d60b010b141c103241e541c014580190f0b0b00e00400c0b095581c081c0c1d07c4c0c0d0090f501c083c0812030003460b00107d105800345000e01c4003400a000c0122a00b1072030713603050b11904840120180900d80e114000b05500780c405640701d074000c5c025200d520b8034030f041500940982c0b0f00340c06400c510301450140b400000390018a402ca074140010040810041a520f0031040907500032490f5940d9185042440400e142040040c01401c0d0842648075000d81c0c2c0181c13528007220f40040807502a94040c041200741c1403070001210039180344030030000b070f80c0001c50403c14040d115014800150144c44184e0701d0100740d40d10480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 535314298 1250 535313048 535313089
    0x120c03020d030e01060308070521040f0510030902180708070e0303091512010308091c02130903140a2106030215070303090b0c0306011706030d0c05100212090606 71
    0xc200740e11076807100103154034250002074136640300c0d070310404c46502c2001c050f9195032080c034000004190f641d85520402984400080c585441e2070102020300c0c03050300c1414420442c4014868005000790400003c40c1d90091130200f9080c2d4041310311440c28010344004000030480c4000645a47c0500c0701c4035403902c0014011414283e5203000c028184410009641c91600306010b000030041082d92194080c40c41401e1490300c17040083c0c10b202c40c03400103a24003c108130480000d8005a02d51704142e0401703001c1040302160500103801d082d141c00101c11015111031a001809008055020000398014040c078011820f082c02200c1c041d034165000d5000c003070340c001e050722828141c074103000d03004100c41e0348203060102e9044042e0312604d0300311100316807407e404040002003010941e808164a2490303003401201030160b00b800710100f542d910301c070b501c07200601910703400c00d0301400404c12038103903458422001555500ca40c003030401e0004500b40c9207030245106d008082203091503c3c0032503400c0f4220242c0c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 535315548 1250 535314298 535314313
    0x3010501140304050a050a120314060607140c03030a0e190e06060703020c04050f0906070f0206070e04020909070c14031602090705130303020717120703050f040b03070309120c0302 79
    0x407101ca500280045601c0c3c418a840c220006909000001007071307004021901d01088061000f03410b0f1042105003440110450041200560714402a1a02980c000060580305d030600c20106107411618015164140700100d1400f2a0551010514080310b00581d001c56040192945e403403070015080c041c0300910304200c400141141800c4003c0c1c10184d009204031813801e4610808070341140c1041e039a000380c50fa800703020803200341410031130203030007003050f180bd103500f00c028a00007520342d900a00710000300900615000c4050380c851301950301c108070052026105082803070019101c101c0c00030007107440c3c0c50070b032425076418007020081d9400300c51400c11090540005501f088100c103001480305d000c1c400c00384494110007141544980195100380c0003400c1c10307030402c0b0000249c00d4035011501c000b40e101c0074089041c1690132044e1465698541842d07078503440b501101c00c03160300642d0000940030740d010041014144c0e0540007030416602900c0340161040c002001102d000c01d10400c0600582e12400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 535316798 1250 535315548 535315577
    0x9150302010e0d080f070c1e0311030a06020d05010e060307140f210c01122f1b06071205061804020616081305100c06090813080d0906020303010501 65
    0x101e501e00c0442d8020404105140381d9941c152140d0804800c2c4901c0c40301c0415000c2c00c1003c502580c2000d05403418070403802607544d0300010351144c0d10b400014640d05a100c82d59400392020000e4454030b0b64403c07025512200ca451000c8010f02c024401c904064400c0008262036007408243c440995400408100e14408050b00780000140d0307a460840c1c000040050a603c0121411070392520384c8040000fa002d260380c480001005400c503010024142454001554207283d60454000030895800707070011301d80d204560464500340940c41105010003c0c00b00d1450301501c0c0440c0c054865034a0f6140c584040070b640080c80d0464808890454004041040c81c3c0000c04403180c07229032140c4028001441c0c5003441e603004149044a580c111100d240c007003645c00794400c0e2541d0600140030700b9100d101d5004027030800189580e03e1503101802040d0380d10f01240511541000f25030380d0310641000840020751390820300380c0d0b4072600320081000521140c008a4400e1020040fa81203441c165100191075041d0b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 535318048 1250 535316798 535316807
    0x140c12030a230a030e070b03010f05090a0906020301080d120510120c0512010c080a051b0d0219091502010b0306011e080106060503270607030b03150a05010f0915030201 74
    0x412600c00c0c80302d81c200c00000b15698107004242a450a0764003048040c0300b190310520308185504503510a00003840107206a21081d90403a00f20348048400c41e602e81c0382c080b200c0000780341d0501c0251075030f40000004a003080d000283d000c0e041c2c00941d0b9800032140c000035418100c0d40c00b944d019080001c4000c081000300100300c3e0240c156030080035140559581c90000a580b071503110140340141e511075004521f2140c00c0314606030f000c102441d0921035071a00c3d11042c640480b0a1500018191001c259120385852a0f030541e00b401d08da08101e100401d6034610301078400b002c28803496010068550405a06a1040c0924400500050020076030340c0d0824590001c0c24084021070003032038204c00d07000540e42030b0074050140200250303140c0381d80e24100602035006040d140400700a0800c40f0340303080c01942c0c0d400240d06520401e03600c3c0020b00040f492000030b0810600c1d840a0600f12003003c1440340016060b4081030413510045050746c4216a81c034200c0c010349001e403803a41c030110704640d010005275008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 535319298 1250 535318048 535318067
    0xb0121030e0f0a180b01020a0f030302030c071401020702040e030a0e01050d02070c0b09150a020a020405060604052d0109050f1905190608010f030b160318140c12030a 73
    0x1000060002c1014012540c940da0942c014101c1c10060707a0104480c030120320809038a91020304c040c1c204030300030740c41e070808403030904000408069000000400c0c0110302025034081d1980f1040701c5543c11724044489000c2d4108402c140d10407480d0130380e05412004004215080800141c40c0d0001c40c103072800040d191500018000b001481e001c0020100141e07a611580d0058003210100d15100c444c01c0342840f50181c0044041071b800d0074100110640319070002814480035504813008101c0342d4607000800d030140220341c02260401c3d20b9090002d805400c0702d10018204d45a049245250101b103c01160800d15a125840d044010340400f00b00d54140600320f035916429034103001120f0707581c5801240700001303025448400071204000c02c1c00310381c1e48480441d0050552035804162a801d41d161000b102102620344004d1521f00307824280c1041c000c0d0442c680a02e9503500c04004c0502c10300342004507000141c0c0d006920300400e411001d03203180154940c45091001002541403a09021007034600001c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 535320548 1250 535319298 535319327
    0x1b020f01030507110102130f05060a080a1a120a0b060312040303030b0402120906040b0c030f0114150d06050f0603161b05100f051302102304030803040b012103 70
    0x540d08441d04c0145000d000504e9281044541030300000e180c51844026501550000c9114440403c01117100c1a4409080da411944803840040e11019040071401200b40143c0d02540080255a02c5038440c00d02041c000c81050240040a81981d038410801d510f4400707082000404000520051000c28800d0340a068282805440146400c4040c00c0744000c0e03c50031201101164403c2080104010000b40d0260304607044980c440d0035810042d4051039513920500624003590501e41a4104030740c0d8030303070503488420b00c81080c884d918400e10007a400680240d0148502074100c0c1404c1901e40c0c20050201c0c0d11481e40a15400d42d200a0400201c1e10201c43c140000c0480084400103804a0410300060180c0000501c1c00a4a101001d50f20010b03208020803459444c240e1503c00030241c1c4a52101180700a001c0c03800181e001d2040c0e40400d40d25400d0b00165031502c50200d00401002080c4000318051806108244070790383e0b94072100c1801c0300e089035801350200140600800081e015100020748040d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 535321798 1250 535320548 535320557
    0x503010605090616111e0906122104050a0e09060c07050a0b01090b010908060603070e071106011706011e03080d060503010e10180503040e0a06030212030a1b020f01030507 75
    0xa40d020548111594a03d419035500c0c5d0070f412040100d24026403c004142207800340d00c84000715001c00281120b10003032049028008045529446007002c2c0800c1c080056844506a83e24074000c010851541040c00342e079000364000301c400725001071020422031080e40c0c0d41000b80f403da0746020711480325070401c0b801111644141400c00d00000c40c01d0031403a010304030041e000101c12a040c4001400c0c091154070100941d0854404e10541d82c401240c40c50a0b01c0344840d0201c5281c403100713011034500544241e444601d000b8400045480c2d0100b03294800f07039500385c1041b2405a40c035110000c2c85000d9416003802c0719004440100001022038014201c0307010b54041c006419aa100c01003030035101c250030701a00c0ca400030143ca4086205d180b00e000b80798112081002c110880c241e88041d900e203d43e0140c252103445039070024010f81e01c00d0708071034003556010302181300d0301040072042a0349801000c0c4c0c0c840070603001001c48445100102491607019001020701000d10040340043d0001c0001400d030b0070410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 535323048 1250 535321798 535321807
    0x20a050c0d0b060f010306050a060f090b0301030809120f1603210915050f070f15051b070203010e0d020714060304030504050103050402190f05030f010b030606122505130b0105030106050906 83
    0x90381d803c2c04400080082f51144807280f00b01c950010420340180d00b040c48004010700c01400410b58800580c2c541c1c0c0016130390403d8211001c80a01e10b06050550514a24850000641c9040c010f040c1d40500701d91090000c0d4030b00a9500030305001310300c2000c0d21040007500000040100000c0c000c3e0414168480b41005860840d4041e074485c001c2d40141c00995105803a1030100c0c01b080212002540a4400d03900b0400a6092100b40780911014114007030407000004569a425540c017940b112140700c0c1003400700c07000d000344494065158842c0b0b204200305050815044851400d0030380407244201d92542d13a0914240c00c0c80019002010050000ea81003c18012004201d001c0107100d5800307002ca0b21054800b1600c0c04040510f40700030000100e003036904140c0141d500d07071000107160340c100b9822200040d00d2501c200d02185098089807080810914080026500f201c240921320140d400c04e48442c000c1c40d80038039085041c1e5050701c000300c1c0094000c00041055610034000313080c3d0700c0e000801e0305141 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 535324298 1250 535323048 535323059
    0xf060c1203250f17151201020408030328050903040501260a0e070503031215030a0b040305040311030604021f0c051e01060614070303050406020712020a050c0d0b060f010306 76
    0x8800020b51a00220b04440c1e07860440301c0d002001200307403582da42c1036852213103001202910112045d250312030040000c180b01c030005050030f4040c0c5024207522402c690701c0e0b1902a26480c0a0b04510404102040100c10040607040d50360040728800c1412200840c07800d49020011545940341000410801b51300300f95403900b196124000d079002d4003c60601050b11042d40c0203ca0400c111507010622a5004010508540c13064000055009072850b4031800d110001c68040b9007030003039040000f00346400140030171080540100103002a24028003058280c0c0c0030460500d550390780141c17006540144c0c0142c50140a0b806c61a44a1030f01c00c003850400c1e0403c01075501c052030603e0300e010300300d00c868031203580107015030007407080700c009003a24070b0240586007000020448a1058002c041c0c1059124000201841f409804132100d1541c4038450b9501c102140200a403a4503a200c6c2c200c038140603000e50b0b06024505140038885d01c6401c95100740c8661100c1040003002840c3c031000f01e051544400c4000340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 535325548 1250 535324298 535324351
    0xc0d09120f02070816141206010603050124052d04060302030f0c0702010c0f02041103010810060e07050a1d0405040305120106020a0309030206030a110d02090f060c1203 74
    0x202210341c480490800200034064104503c41d00200798aa1009681c8410404180c10300000c5440344258104d2801d800008185500d002054030001ca00c15a400000d120340c0c5580030383d04071019800c00c401d03a182c125426560384402c144403000080d109220031401c08480900c0d54406a007184808140d003006000c0c003240c9a04240c0c4402c0110740e021041110181c1002109071b803054021b002c0e035140200b15800039100b140c0c0604040d00b181c501a00306421911240e001c03810f410305d28002c0644a603580d02e5210356507210800f8500000e8107016002942e80c0c501304081e07000d014552621380c281681c040c02102e0315515400c00840140c0c40c04180091501c0f24407a25005902a42c0c0ba155600b007503030040c00d00e0140c1a442030b01150301288202c0d0220768003815505c1600d504a508030340d261251202140a44100402c2201d45400000c1a0078030349c2d803940c020041c45e402a5500011180c0c00d074100310940c05012110902c0da0403d401d00c4403042c10450040d5400101c1003486c11503030442c0042c244 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 535326798 1250 535325548 535325573
    0x5071e0b011806080105041a0a0f1b110d120e07090f0903020615090406020a120f0b030111090a0b09131404020f04091106090604030f200303070b0c0d09 67
    0x2006541c08202030049040c41d0084034050700e132881c02803016041035628500304412203002e13400101c0110000c42d003442090b4112a602122016092201d400c1412416440c8108400984081028420300d003041d0a07001c01c600c000a4142d888400420480704d007440040c012503c042c2c80b20740196040421003000f9842040a40701e000000020f030840685800703481c001014100204000d1521010b00c502da86140c00c051b40594415005a02e80c03810b050f09544c03400c0f41da02c1c000040c505140c4114620703466640030f4031809204400074040c171242c050102c00140b282c3c0c08181d0308007602110602074550002c000301000000900003001c40c86100213a0b5080b66206419050f111003c0000e03c81586001958500c032684110b5042041e241c056444810380900310051501411020445a00d1641d0b94010350f0000e68001e492401c4002041c58507000e00004680c0c1e102002c58684504640c90030000203950805900250742207254035030b0841007400350440c100150343c1070345503c0320200142581c602d64 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 535328048 1250 535326798 535326809
    0x1a060a03090206030c0315030604080f18060c0a0506010611191a0c04090f0b0303031305030910020304080d031e1a040e0a050606010305060d031202040e01230303030705071e0b01 78
    0x2920303814151f4401442551462480b8402e610003018131010903410401c80d20300e442c4220b44156607102d00a161362000500703900341c41d4010070115502454820104000c10014421020366a6581e241e140c141c1d95000784202c8001103502001c0100c69001202d000d1800c0070f4095041048a64207418000c00040d00803154410407440100c0d04100782d00c5507000ea0300a01e07803203e03024040d0280a40210340e4900009004068075040c40b108003003448020b000302d40c401c0a0140007010340780d05400001c3d60301d0340140303c0c001c8213104a1030360326002e0b4800d00c61100b0f440031111341001c1e0842d10f50b1610010b020440c00703000c10b1009422000b203043e5550b11030390b02060410710151010b03103100d00780141000380c0100150306040c200b104103c0b0740d548114007040038580c0b42c10300003980d4150310401d80003402190000101012000c0002ca1102d11144000040e4900c6000c6107a54503614010f040e2a40000e4070b01c080812010301c81c5c80300240410229144100341c200c1c10508030f06e215122248a0f6070203a110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 535329298 1250 535328048 535328071
    0x20a021210062324031003020603090a030216060903080a0513031208070305040506010b0f270907180b0307050904060b0d11040f12020a030b0405030a030501091a060a0309020603 78
    0x5a0310f071540d4442041c0c2c2500801c4668400c0d4803103404014402c0201c40c0c03c1c814150a0000c002000070a03280c90344409150090000c1d0744030305d84050b81603540c09204505030090310172a03046200c04819035040e8015034030156106500a80380d07650740400c0d40c0000c1184000d101c0240709242c81d4001c1802c3c400c008500030001e002807030b80010310141c2940c13409010340e020141004c04000100e03600041d00d6044500320948142c3d06c801b41c407400700290064000403001f030040e04884000701011941150b1402c4800c541d00f40e83ca44410000f6100040c000b032559421600b803610401210200601841d804000c1e424060303d45007046000800b165926085103110f5800400c40d01100003051256100180c4298090342c80c080c2801c0448107003c181d44507484078404400d9108003107444101e0998000d50340311440f246142050b1070416101d070440885030000074942400001c03070300c4041c0200464506110701600710698031605200c041c1d03104200c09014503440304182401a140d0000461080c580c040787c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 535330548 1250 535329298 535329329
    0x31003030809030c0a11010513030510110a0801050906010c0219060212040b070f03031d0f0d0804030f2d0903021e0918010b0402040303020f010b01020607020a02121006 74
    0x10054600c003000390110b40c480d07005014002d0340450000381421415080400100000d80810040381c0a00c2140b031b1403605e4003c1e40740000100103001504001d01c4019100c1840706460608114942c1c2c01742c2e00d40308002030700440041203c1c0c208022a95080081894107510488690300032980342907807141a59040890290304200c1c241d814401c04546c1c009803401e86260600d809240795079402140805810028941121010180268030842540c42e41d0f40e0118070b00d00400d00c8a41e1501681290407c2074000d0b468960542d42c4204500743c8110303030603250204060b1b01c00e07a00704c1b070342e08001c6481c144400300040c0705150090f44890003000340d00c2594641012030306610500c000106030130384082d54048426682d80443d0384401e1410707404104400d41c0c1c54a02e203c9aa881e000d0b004035020940c2141c80001c0206c181079010070603400000c0d201c4000d11541142030012a13444208540e00801600040303206d0005103811031402034084400011180004c48030001070301250010b03440b54888625684 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 535331798 1250 535330548 535330553
    0x150411071103030306030a15090f05030a0e1519030e0313031e083a0203010e10210501020d1b0908030310030f0f05061f0504020414061e031003 63
    0x40c244420004141c0c05141541406004250359004203500142303004080c461041056030f40303134085c1e04c0c2581c00081100c0034003900c2c00c045031207034001c40c5d481e00000c0c000f030722018a03801c00b04c88200d01c14500c414141e180844d00d4910b6464090701d00e100408042d2203200c020003415080025000c00740c0c1d000030240744c20b4614038003080c210080200c1c036940703000d00c6804400860140381c141c400640c60140c0301c55003001c0c44500014401c1780a04203a03400c607044480c0003001c41c2160f000e54103885281e10340c16441e1701c51000021403000103108264055441907040355416006c2102920030521410001d4104070b800800340043c2d42d0f0741104c00d4600d0b503250b00c2114205900c00b007020700400303d4402962a41c01c00c0c401d40e400080a070700024044c0740e90041484200406407074210312072074000c0b041d55030340e082c040079084548030381c01440b06480f4405c49001c11b80d07103024421502182e014070540d200b8504070b082400720503045015220f507020200340f0529569070345000114441c546070100c1040550451 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 535333048 1250 535331798 535331813
    0x209011823040e0c0f01021c0915050c06151c0503030609070c0b040308070c051902010e010e010905040e03070b0108030c10092f030109050c090703050f0103080315041107 75
    0x1451980b0841c2070400e0a07095041c0400d184003240400d807400040d4240040042c0e02d08408200714088480c20f40002c09601d40d4005086810381d20507609080c101c201001c001c44190080120011403600a04041002c454800d0916610810081d01495000503482c80e60381d8482001e000aa0b9550000401c016051030f06250443d407001240c10800c03c450115107907281003001c028001018070401c1c1002c540c009008090001b05158800308840071000c3c0382d281c007080510a02006c80c0441c4901c042c841c41c5600407900119a0340040c1d440c02c0b240c6251404110180418180800b80c500040200e900801c0020307106074013a0402400031513030341020a13503142c07031300e0b048a041007100c03842e1000c00300004440e0b00a4007401e1075410300c00b0850111200031104031341000354000d6855803902040a0030420042200c055600c0c04584050007903480f0700c01030301950003c448e4502c604040d4401800050480c40280d40c00003000780c43c0c078694602860200b4216180708401c2c0d0300141c00440d032203003000b41c0c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 535334298 1250 535333048 535333109
    0x3060506090112030e0616050a020114041a0d0b060a02070f0e06011e0314011701110322260910020c03120a031b08100902090105070602090118 63
    0x156541c461a6142480c000325404240500401700440d80700104050b54071403050302c0000460071041110f0803034501c3c1050f911015258100d01107001e151030070301004100026034003201c0c104400d4105c407090759028210b281e440306039a8540310341d45581c9180c030b5490f0310000d05680f4a141e00204501790810041420920349640504494803144003009501e980c406820194944051403807580422117010a60140c2041044e40900007000000003485009105060907442141c100800407003045540c08146880100d4400d24080807901d4a05120503aa2080d03600c80b900480d80350700d04000c045640392607160341c040380581c060008103500b0401e24046001030891352907400200703645022a40465103810b0240842c0a44820100e801010f45000b900702c80c4568040103a4012941084d2502802c003107800d88903058031000d03000022943d400135200301c0d8204035050b10b070f403801c101040d52001c000c2c1d030020396040d042018410080c03103104801207a05d00a0a0050062203d00c006881203480c0c0070320303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 535335548 1250 535334298 535334311
    0xa0c1404030206070f03030b09090318010c050606090408040905010e04030906020a02010f110a020406180e0f03030f040312020d2f041802071a0f07080405150907080d030204030605 79
    0x8000070801640e0716001c840503290302150380b08000045c0c0c10140e0050041722206134111041d01c08000000f10040018002070803100144040d000165004642d01c440120008041c0d921600c08a40149410401036074094824282280b41940364140344d000d45400780d000c0c0c0c501000d040700380820183c05c054610082e28580c4002d10500403a0340000346295002c101c51028040c045042d024284000c0c001d0258194010748180070031940c40001060404150b4003c4140c1840c2004800e071809000c100544d100030200002c5040d911381e440300d101c0125010700100c1c14489a8514005950202d0000d4aa405e0400000151084200d43d061742e00809004101074041c52101c811070000e28030070151002e550780110002c0d6002481e0281d02c00a125485015101d414841f11480b085400c952040f4810356448582059646911105548140c000d5070000c04940103603060707800b51514500a240d000c0c850740c0c02c0318001d0341d60f01207813400c2507000500310000a800103814004d0040d5801019003020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 535336798 1250 535335548 535335587
    0xa0c03020102100c0e09071112040513060b0a051c09080d0f1b0311122a070803060f0a030b09070f0f0609031e02130b0310050c1b150a0c 60
    0x7101010000c080301e00b40c5c088503102d41181000305904500c0707901d4600200d14808212280520103241407400c6400171b03ca542e00c140c2070300801c0c109005007400341e0001c40f01c0480c2c1d481d00303210b8154010f61f010340007401024800d00001d081000400454018041a00e0044072520390f1180c00000d0181a1245c0d01c9030314a0044c104402d00d1407641c400c020303640e0354000c43c1c6000206071a1041080c1c58907c81d465145203e842440c00f400380c0303900c800c0d003c1c03001e455082132040894106503005010703d0043c0074000c0c14000060001910398100400381e030b0f504000081c004c2e10015120b980346640c442040d41c1042c4583e02c0140c0c284440c4555001c190040d0141045400d40f9a1820900a010a003c0d00008014105510103104410001102c201c55030303500901d8020344800018402000b000d0290002d8402d100b60785400c0602c400c00d104580c05400700004c110302d000700b4400d1038203100ca0110082a040d2140c0142c100c1a0341044071140c0c01400001c80100300c0601e613040c003c000d800048508552003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 535338048 1250 535336798 535336811
    0x12110306090615030a12020c01170c03010302060730110c06040b0c070f060e0901091802040213030203010f06090b1002031e090402070f170408061504020c0a0c0302010210 75
    0x100780c005620380c0e02c4041000500481c5032840302090600a1088000340540041092a45030a4004c64070340c1c40c3d5a8207903a4818903000c0c400704154503040542d25401021010070050001d8100080103000b014003070228421100c00400940503001d108040102740002c0b007015020859500400151020390441c000300340480d6020005134651080f403051120004000500c0144e8000034800d010003017840042d050a83c0e5501c0c0c502a0680c80c4500c192842908020008201d034481d0380b081c6003a4540c09802002510304981c02e12009501403041e40303040400480000006a40900603807104400355000071441900c0c1c510315500307580204506030320404450540340c900684c0041581c052480040004e50301a880d541c20a10791701c81d0b441066040b07400040c1400500108070042d207402403107400d05640482c400341c005015809140034801441c0c03c0f50f0040380b044101e041c000c01100c80c0042c40141303440d0a46000b01d2508102c004115201f10040318208103560b01442a0f1160207070071002440003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 535339298 1250 535338048 535338061
    0x6270b010512330c0c0105100e04031812141c050f03041b060809070b091008091204030b0114010f0f08070909061d10030c0b07060b040612110306 64
    0x8a040480552600041850201c0503800e0b600035412040503010f0b5182c20b8a0910010032a4250700c250303d40b00556003820080341c0f02069010449084078100420405252600e42d004c95140348640b20b680c9130991418008140100c03002180c2c1d020600c0b503000c0742fa4950a00c40d1060804118200703040c5c1207202020340491503500082190121005040c1d0b0756503d40d01c910342142180340c4098950388150701c85a0100d44650001281402901290111074070742e0f5917018254214491001c240e500540c4426180c0c1c0d0f41409810242d801c440d1080079543c919410111620f0250491b602c26139002c1183d030010001e0b078943e00080c84403c0002c1c600700c103a181599078003a00449580a4140c20440c401e40003928082c440c03200c01000d403c40da90280002030383e42604c011200c088144511165901c240824011101c2c1c0d0320000499a015a5050300d0038039010f803005035500503d90586405485441c070180b541d50340c1c0324600141140d4200c03800e28101e181040b4039044a10790001b0301070340c80355080c03080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 535340548 1250 535339298 535339303
    0x312020f06221a0c22080d0813051203090c0d08091009050d03030c09081614030c09070f0e090405060c16060e0a0b1e04110301140915090601030c1206270b010512 71
    0xa1f104040d0520489503254251812070400c1450f00190040c0074906c1c0483c00c80e0607000c0154080c086ca0340441e03000380340307a10401c84410380040004041e280200809005410425540d540740b09050500044050340d030b50201d0b841c2800060b00700c00180d0340e08500b6811a030010241000b91030b074040140108408402100170001da18012403901200a0013032000543c3c00708a0041e02c0304018051454500300300d070019002d9030403a0a02030116034200540410703030501e4151580306507000f80040c285a10b40184241040d8410500e04080541d40f1000c070003c5452030180c0c0145625000c010085000c0c01d00708040d1064014001a039003e80c0303455400d0b604422a040e4541194001d84445c140200c0080083c2c01810310345003100c10010743e542000b01d041c4c80890306160320015040c2c3c030405a51000011303501c4043c00d0000403d807482e0303e4000d020070501c0014400303e85100c0c00c0009605000d14580c581820100700a030035503031640c0f0310303200c0401800c1562180105070642e8803960900c3c0c03003c4203d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 535341798 1250 535340548 535340563
    0x141005190f0911040305010212011a0c0307060506032d010b0616030810090603060f05070509100813020a270c0e06070206040e010312020f06221a0c2208 67
    0x1400b2a1581140003442c8000400c440045902c03500031980c1c0d03103050f096496000400d1062000d040004040740058864031811103910a81e0b02015620b85400c60381d4000c001d1501526190305441818200c0c1001401c040c6201001c1110f40c05403015100c090303e1b01c80c02e680c030803164240162414402c00980300001c00e1140125035250400c501b29549414416110481d960300010045d4200007001040c00015441416132050729401404907903900c480c2900e19100741180190030401040d28015030912508589400140903022203d034102c0c20780002e003502005802030000d0401119044d00a0400300401d40100c000718541400400e00340100500000284100d0a0003020005103413411951034a044038040d005044000d510355031a424022610707000c01020202503c19640d444c40d076150000f0f21030340300c0c101d11140e503c02c1d000070300d401304002413040c83d04462806181280d00045d01d80f52201d14490314405a980b0b440300e603100c00740d511850f03903004205000c140c51031050150403004241030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 535343048 1250 535341798 535341809
    0x201030509012c07050a1208070305190509091003030f0f0e031507020d05030114040906450c0510020a060e0718020a020a0b070201141005190f 63
    0x55507940c0c0c261268050464010400d4864100e00c1030009006140b03a031040c000b0489804540b041510b8a080c06504100780c003d130942c1d41c0481c1c032120001102e400050000c2c0d44686482d034201f0115881181801e0340318000900400c07030224038101d181c1009140660302c210814100e00b4030924545016188a50742c000c03040070845000394408819000e61030f01851071078080d0480b500c0b0f03980020b0b10001100182c40d0380e401801350358a5000c2048c461000d80b8165418214520480f549000c10040107144040040344d01c99100c1c0600403c0402031064214100600c1000341c180c403004400247c040d46954808200070505c41814030701003000014844151882075030003810b00080c43c8070030392400700070403002008a4146248120250008215441115408400034030400508454103069005101d110001640540c0031500440e20701c1501c41c2c1c205c000c9000009600c0c0c0c100300f4408a06000b120300c0004101038100c10405414289403503002c040055980c0c82e582401c0021a40e40c281e000c0c40358 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 535344298 1250 535343048 535343051
    0x10911010302090109080a060c03051f0902030628080f030f030103140f030409060e010f0b07031409030a0f02092508041b061101060b0c1005132a05010c0f020103 71
    0x7004140d00844503a4040d0500c0800c46440341f05a2814078040e0103507004030381c00079041070081568824a1900e12000c01352021503400d20b00c4c00e00040c00000c0d0401080103600070b1699460030180c918081c1e9132015200810041c0752000d0403c4440d52a0280600301a002c0c1d6004210060b0340c20425001d40f410b60340e005040034010020423200c1440c0054401d00319841d80000200007030000c0065214000b25184a81038400b1070f0307640d0752404544940c80c40b0300e0302020020041072000038131490040c030080c5680b0250303900305000300011038a04407910300121248500108404298a00300350a280d215411007054503c075001c45003212014003072000c0546c1403200007004070b41005901c1c0c443d61305502c4000000452a982d903c0020b28066103d60944400d528255011a4107c8070108440901389010300404611154a0500300200001031041542d2080b900c661800240b0485044054072032a00c01010030140c403500030305801c00d040e40b21030306000c01c1181c0440007614014071444080e0302400c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 535345548 1250 535344298 535344307
    0x1101031b0c0b100b1c050f040c06030c0908100c0e0a2402031204030306030b092a0402190201020403030801080105071704030c0b010f08121806090316030609060e010911010302 77
    0xb40725940c0070458200c0c80308544d002c18030100050066480048180c000c0400380301c25101c41e0351034203694000380c9014020411080c0d051000a0181d048060440118905070050550b01e520041c184103c5081d03c006c45521241201030841d1b0000700070703a499008031143c2d15441c0c907004404104106d08024810071955a0407542134450082c07040d1401100b0000e40301c14246001c0c0780007130040009000890308108039002040007050001501d10041c3c1000101f07049064549019641c0102d803111b03402d1784150208100f640c003101000720310011340416000580c5075821450082d282550580100c00641c0c5070a08200486030311081c00b001104a8145000b0070761120b04040b80c0310306428601400505c5040d000141e40083c200c1107104840b0343d201aa4001d003c001c914412610560104030000f44514109031183d19003000205403824000b011030300c4940b00702101c403441d43d8203070b4001e0312419a1005c08206001040c0602801000440c000704080145650b80c074003948040003549041650216 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 535346798 1250 535345548 535345561
    0x1060225140a170303012d06030509120d0506041b02071509030f0302100c050403030c02133804020405060d050402040b060c01050a0b010806060301060311161101031b0c0b 75
    0x40b09a4054901c8012200c80480035840b8150340340e1080c40740608008403200d000d880c0e8030f400d540d0103039a50840b903200c2d01050b107080001c5020f400007401d8003995001d0007400321945400d95004000c010084c1c00007117500e2800508000c00c4400b48507228004080c0343d40c2e4801c0c20b40c0c1c08030b440d90548000800240c0d22420018044543d0440c03a000100f44507600c021070b9051640005070302e041c3ea80211002d015146003601e04581e64015440010b022607441400b034801884d03e43e140e074142d201d03036038000500c00f02915242e0705c071401c200038500c2c1c44171a442079520b0260700e4501d0002201c3c805680c1503244c01c0c6000e0100300d071881031000b1440c40c030ba0b82d8400f140440d0f803260009403514000074501070f101c03524a02445d000700710070707100c000c02e840c47d00d000d4111b154029032029206481c02000941035a1901405902821100c1d0040f00c035240d00700200400080d0021403100018060000700f880280d50300009000c4440e6080c003685200104003420b50b242d6031054038902041d030321a801071250786940d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 535348048 1250 535346798 535346809
    0xf08030a0603020402040e040506060f2d0622060f080708040611030109020d0615080c070507121110170a020702010c02090f040b0a09030e120a0b09060106022514 71
    0x82d08029800790002500040300d00e40500324034019070083c1c00b035a14503100c14082000d184209014140c014080c110b0b07201d002880515005201024107031138000d007015640c00600c03954004481840c41c0c0300c803500d41d00200000100820054240786c2441c50118007483c07800340416000610f0142040703100c00000f41049416049044800c0458100c00d440e0b50711032900030042d40024019019031340c41c00f080007986400141c0e224a0000c4c080c0c64901207900c4501d40e018095001e0304c81640c84d031146a0300025043c030101840301d81e00e401038109a0a80c1c0c0b001d0200312101f86080c890000700011484003214649058580c15006890032100503915901d1b48016555944021806503021000d6003c014214070269415489688200f001010664600b16440121007240202400140780c1c0e00241585046c815130a02080d050301d012100901c040d5502c20a0250040320307268001d0304071034010049142c042003891a00420607500036500c60072100304040031325440c031442c01c5c1c080c000c2c843e00510f5140c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 535349298 1250 535348048 535348061
    0x9030e0306010b0c010c03020f0304031404030b040503070201120b030d1215090204060905060f04091d060720010b03101d100207030e18180f0d020f0105010b070f08030a 74
    0x16064601c0381d07940714040c0310039400c80f80e1030064a500b041041c400301d521070700c03c841c51f0300c3d08242002c0c250b464070b0710119121075010b017500e401c0550800c808804611054030300352240f44200300550352a00d09100050001c031840b110103800e60300b840c400401d0f6a1380454a00f00b400d00900e40490b0094030854440007034044001c040071000d0640d00e002c52161025002402070704c5481d100d5401069803242031101521680844c036000fa001800180703c1d42c001030308001074000340c840c0141c82500300d8500480c01c0c0b44041c2c4084000c2101000c95660b0000b1b400700d444414048040208581c6070f00c00301180d1100024400c2680c8180e0350360580440040c2500e05001030300e840c03021a0008c40508250780e0083d44030950650210710b1200c2128910315044219519108a00d04051101d861703020144210304000201d2841c0c601500800c0080b6400800c8010380c058916401054205d48500e002d41c00c444068221040c000010445540890422010306140c0c4d0382c8450a550f50340e41301841100213140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 535350548 1250 535349298 535349327
    0x60d062007050a2a18020d060909030e1002070b03040f060c0908070b0301120201030f0e0d170c0306060a260c0304060b03070f1806090e010510060507150903 69
    0x280494000c0c240080081e083c040280304844003241c40b00801c0341d052083d031400462040e0081ca80c2820f200305469044144030300500c686000d41044071074101c40707064810541008580c1a40c07240140709042d40083d0341c2d280d030801944c41a9150f40c06041c002e4854815015180d03030b107035000022604010b40c3c0d01d40b1400a58028900300700e10307060384e18000c00308861849502c3c6a48104030020a03040b840000300d90403a0601081101c0001c8140d005502404000c0503907041d8a684a0304800a454144160202c03100165154035030310101121003e840c84010f40070f554032903001d000300805500e5103401c85a42d5025418249440d19000d51060340e250300c185e144800c03c0500c84140000c0261a00285000c0d5200300710038001000100103060307031020305100740d29544401d10004c1165082480d00b00c2c210000f481400700d11151a59201c600f600c018185103180760703554004100c0c402405011400142c2441e1a107a8a0140d00d43c80d041c06060200803c90280c9940d00d501c3d008041c02040e200d1125417 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 535351798 1250 535350548 535350611
    0x1030c0503010b1e0c0c031c020a020f0d05120a0f140406111204060c0303061205070b1c0e070509091f0f180c0303030507020312010311060403050f0a021503060d06 72
    0x451945c01c1c0d075110403102c2c201c103009115610350702c640300e03040c140701c01f100340144e900400c801400c9408114035016442c0250781c00c200083e05040c0070400c10700c805080d00c004078400c1c2d42d49901c040c2c2c0040400303250406400811400b5a081c003040d83c950030840e8111201e520b0b211b0b4000c40752070303c00c41c185404241c04420381c1d11700080002d0100c2d08144040500d034041d40341002080d41e034180140541c50075076402880360304902400d1003400000b50203090200c4000c0c081c40095007050880e0002c48050f003084140303541c08003904100c1403070032030440c50f8000720100281c000240d41150000c00a19031450f10840c42d612008450ba4400840d0301024082ea031210f0311316a91015402c1030f0b031300360007140006c0c2e0000f402c00d40020105030002044615580302044400a00d03881e41d01c0e2400000d0b5141c1d1f515511840409c000404079408024001140202401038000181c01e4410030200c2203101c110341c0152007090003041410b070748034280a0743c8540c01803004a4024960307014103401481d00c0d0801007000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 535353048 1250 535351798 535351807
    0x3070803030c0f0408061303030b09010503100e010b03011107050607020316080702010320030618010b090105070c0b0c070f05010c031209060605090901020903011a09060d050c0904140c01030c0503010b1e 89
    0x1d043e8000500d640c7c40c080e4900308402c220380030070f02a41d00030901480360540c0c01950902c0031803016034400035000c94660000119104401c000038290f5591056a00c08000085100344c01d000301806920740105160004614044030204e9030389074560507100c082d00c2800080365020a59000b0b030003950744000541410201300803a016001a51703042500d017107000380e803a2280d9924001c0000040d90594046010380c81c01e10a051004507429800101e08980c0c0340c65041c0006640210b074000f600f016000e40010b090b101c1d04001900d1380d8840039030301150402001e00e0010f00400e41000800051140c15000458000701505140d0090112a03000e0394201d0154000c00030018419400342c500403d00318000e215501c10701c0074244154400514556200e0000070205216240c00c41c1c10f000d181e8451410340d07141103003d200180644408035019181c182ca07140c590404c1d24400d015000c1d01e8642400d0410813401c102900500a00050040040c40398000a143c140e007141d105000c0d00f046400c3c1ea596564 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 535354298 1250 535353048 535353061
    0xc0d0c0306080c0102061b1617091306050607030f1b0501061d010315020c071203020a02100c0f0b060a0b040f092f0901120c03140603070803030c0f040806 68
    0x3072200d071040c840603016402240c0925840880d845024152000080052180c034a5003846164480c8604110441c90800104000343e0b807051207062010b038180007039840d00500018010b01d1003044200c2c42010380b81c100d0034040c0d40d07505000e81e81d031540c240ca4a421706c904071010917584050304001c080004e2200d41004010828150000010b035800c0c041c00d80c403150414015540c0b012030a0200501200003181e40b02812070480c1e0141034900130b00c80442d02c4880d40da031200361442a034110160010303006041c1c400b095081220040c440f103a004d02e804d8940c4103050301c8020b82e40b222404000e201110240100c0c1099031503094140c06444102c40300c9540b40e5507500714585076105442860300c000d003060701000c5101042c4501003103042031440c0d40c101200c20340740c1102c003e501000509041c48400d0400c036150380154441c14407034070880d032800940b42ca0202880b540d00f8600804883c441c2e07110760800c0c0320030140401629048800004442e441e8040003204520501998001501c0c2d071213a8000c012a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 535355548 1250 535354298 535354301
    0x170307030e0d140c040c0f0c062301030c050a06050304050619062c010f061e051b030307080603061611030904091524051003060302040e0106140402030403080106080c0d0c03 76
    0x114000d017201c00300040071000700d068400445025000b1301007540410b4420220350640c001c10003c3c180b1400740c0800c0d0400411128001d9001c2c0c20036942c0d20003194082c060360400702010300141000c6d080050452500fa038507507a40344002010030800c5401c50007000c6281c0301c160405005450514010305a0084410800b58084115021088048005400040c00e4070104026406842c6140e0784ca82007640200a41740701108282c900d4401c22404200300511040b98082101401c0380b2540559a00d04061500400121024107040d1190700084203201c1c41c0301c40d00b500500c0c40c0101d810b103001e030f455420100c9400e60103004800341c0c22030300f045081404c2103144a100440892050410411580d081e01040c810029544005003e2985084184090304e881113601c44080c40c00c1ca80419203540f40d0340803505541a02c2d80081180e91607480504c8105008582d0351911301081c0c80c11800d51a042d1402040123170107105002c2881540000b144004c42c0d2202110070400104c1800e01124406020080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 535356798 1250 535355548 535355563
    0x304090b01020601090b060f030c04080304120318060806040911030102071a090c010f051b070b0901030f05040b0106050a020a2924010e0d06091b170307030e0d14 71
    0x107005001e01c000219160041e441450380044000d041d45082c0f51414000f4017040e44041c0c001c0da01e41205110015440c81304100034000380c4805002e00140084920700038040f1020380304041040080d1020a0100651111205500c01022500850510110b080003d40030303203090201601540006006000c2c00140e00341620174002080403d0305503554a041385440e4101074044a001600c1c0611102d000ca00ca000035022540707d0003100c0301c049030b030103200518140041c2e001141c09140418004203960701031041d62111184a141845180b0717040d41c810003006014001c0130305020f404101d010156200304010802243d016070080d0242c0b02885120100392a08404411207440d802c0020300300070040d640d903104011404043d0141c8040072401502d204110b4901507030041007058018001c175440e809004040340c0212200161800c5880300a0f04607030f000c1c0c000840010a80d036010080620000c00c4910071600344c9041c21a411098001480400503004003410241c19245c1100c8103003004280350 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 535358048 1250 535356798 535356821
    0x6090203040c050102060702060a230f0103050c0402090d020d06061d04050d0e0f093d0609030209280c0503061801060c03050927010f120c0512010e030409 68
    0x180b00107541d0001240e803080300710342c4200181c105030301090041559422100120110000b100782a02c80e21160702d01c221011581480240f03d0440100144542405110b246850654003586401410001f1404202070700500902075140b0340150410f100c4075a00810186c444170b46103009880c07181600b42d400c4d400984003a915030240101c900c0709907016178032044031550b001e060320703c110208000300482204010300840760b0704a52a0000b0b28109400c07a1445124054040000201401c42c40400600080d070441000d010000505001503a40d00030003030381c4041d20000ba00100c0070b400464114072042d483c3e450f80842c0c00d1221840e000c07600a8061440341034141c4403d034040c40412050f4056000a216840c04030b8120051100420300c40c600603c08801c001d000c000032180b003501410a01c0c0f1701c031460210060303a403100600c074074061030741c3e1440203150a944101b221212074032042c0c160380c4d0342c0c0309030707031150031590304103981c0d444207400044c1000e210406690300e0795070700d6002d8070150210bd42d05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 535359298 1250 535358048 535358063
    0x6040309060801290703140a020a06060e06180a02040b04090501050102010b150a050702031f05090706030504030f08091608250e01030f0206070506070f1403190209060903010609020304 81
    0x228138030b9910840449aa007160b40c8283c9598241c048101e00d9610007442030f0100704218070701e01a00c00e408002130007000e075194000c0400c520f1909080c002c494480c0c01c00303104c2c0b02e003040c20303c6030650b030310ba462a00582105c9080405600c4a004500082c880d5038023200504070080f500040003001644124101d400130b80092001036001d1003000795030001d84200401e0880d050140c50505440b03040a0440244040c013103d03096a24520a080d44074802940710380040d89400c00c200c114034051004030010007190809100a050507a0050150b044600020041101e448001058002e040040d00b00301940c4083c1d0403852030326070356a00e40340c04040032024290002045440f0038440306500d180e0840300c00001201d4280d095556031000001840c0d030503a8808003d100c004003090040c4240d60190400307440b84880912402c0c13000d031207091108041101141c0034410420554500b00790100000410742b0016078484040c0000f0b1f400740254002582c1540c600240859140700e50f900442c01640135441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 535360548 1250 535359298 535359301
    0x6043207090c0503041a061c0f02040e0a1115070209092107020a0b0d09050d050403030f111915020c030711030a0c06260f0a05100602071e08060403090608 68
    0x548441c413058900421225000318541060021126442d070045030081a1004030941c265102e103803031030500010303101c14900c43c40d0802146090f1164404030804440980a11302c282e8403100e1120383d40c0c00316030340920750341c02040320349040850484091075070080444042c1e0400c4480181e460220300b00802c0c90704041950214031a20410139a5402030b401440c90178070500301306100c0c6941c2c000401c0450b050392150360050006006110303012651249a8034203489a28500740100140d101d00400c100b48030030444400900c40c00032480c2e045048800e40003901035042443d10311481000030001c2d5646510202d1260080c52010006000180c0605000315200003d0010140c8442c14407000a060703654465040014070b003e1400c0041c5400d201c148460a034542c501068000041202c0b008a070749490001c2010301c408034440d054009044c441c030540b0b0709090003000b0b507031040c0340d0003030b40008200c2802502c1c1200c1c050b0a054060f00b00c5c4000d0b0340e658100380c5005003d41d1030900070b100c080380c100e03070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 535361798 1250 535360548 535360571
    0x11805030c010b091b09060c0304060f0207060c0b16020c04060f060e040c0f0804060204031b0302090a090b150d050a030503060117090307060c0314010609050f0603090604320709 78
    0x342030b9002c3d10454171035944e204046100c80c61039601c0150210741140092000110401061000e08010300b046d03201d881c80c03c00e1144009042081d260048018095100304000115989641503940107890505081707090307100f40c20603842c0181d001841c0398030a081c00ca01150344151008004101c3d039440c0c407241c05445511341000244c0c0e1804000b0400205074143c084012031050070001d0f002806030702e00503d0503440b529840f0590002e00b101e060040344a080c10000c42c20b0100d001c540c0700942c0c0340d040140328034654480440c1400175003020960740446d0400c8115580d000341120146038000e08807a012081450054883d030400c0b5a19804684480b00c2a9080c440b401c03041807254081d40040c5140003403540d5804001c1480001c20420175035a5070882100320690041e041c00703000192503e4040c503142c102004100d441e03803000240142400e00070b00c0405100024540d40041d400f01d422811094517a0041e440d40c107040e25440e5404402c40031034074190502007002c01c19a10351160500904640c1c0c2c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 535363048 1250 535361798 535361809
    0x9190f091101030b06040e0c04050112021e0306060f0403060f050702061620060a0e0d020f060112020f0307120605060909190606081204050a0821030405011805030c010b 74
    0xc0c0685440300d051502403696219a02c04007035071100610030b505042d102c0c50b07000e801c14021174406945140026013031295607040740c020180328854034810352510f5400c0011100348200814001900c01001c80400c2c0c41d03503260b10903100c10403101d0051580b41d40e81c2e801d0110150001200d62604585880086806e09202080391446410f201c03003041994802860100c855101c40000d44032004400c840441d0200e40c00d00c0710500682119402045100c0308070301081c01e1012032020a815581b0400d82c8030b9130341c0c401203400343c111008c0d1044203803400c085002081d0041c1c1448251985400b540402003404006452003000b564010002007120341e0b200c40a10042042c2952240350907840792950b90b422150301840141136601c240000300d03007a5941c0403000e00d0304106140031080203801080600507828500691002001a5402070402c03030494051048100c0181c3d10041c222440000042e091000075046510301c20440c0798100030300d2034030b0300306580c0300c1e0014000c20b4050750030441c00500307a1400707 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 535364298 1250 535363048 535363061
    0x105060c0d080c0d0c020609070902190509040e010c0c0c080c0f27090a05160605041a120c2208100e0c06030109090309060305040f02060c030909190f 66
    0x1040010003040004000940b201d000003030508011500403c1310380500e121074000d551420116400a2005040044599040c001160804034a440c41803054000c1d003803074a0400c044c200c01a01301550744e1040500442d026100b4070ba920b0741250300f0542c0c0c001074030b42d01c07440ca444c8441c01070000b880e6860316000c4440e144e83c2c2451a083c0d0150002d10646401c0c03400b01d51240c00c0d0514822495207142c040a50001c0c41c6c1c4048a4040403a04003c0210040c82003e20001c05100050242020241d00b0b168000e8018061030040610b03a501d9410604140401c503411900c0390950052808001d1808460701000c6a001c035004891040012100e001001455008201038920749800b400c011560412035200400114035102140d2117100d8041b141a2600e10080d40a0b10000c940405c22410500700078100d101030364890010145000100b00104044600c83d440b0190b0441c0c8040d9a0140ba81c1d10620314012181c040d5846a00081030083c1d2048481302c0400c1e2050302d1038140030b442d2090410a088491 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 535365548 1250 535364298 535364317
    0xd0c021e0d02212101051201061a13091103071202030f0f1017010c021603050309040207150c0909180201050702040f020c03180118080334050a0b010506 67
    0x10300442600342c004020f2804800c8144542c0c50905411900c086007030300c07402480340c2802c001c040c014400c03400d01c8201440400f00c03202c002d000c003e00d000c900742a43e02140b552801c1a80700407860002c1805400700d03900090a08001c2400f620407102800c442c1588160b420202013442042c030200c080d006030094905c10414000d0000a07691028224000d40c08010007003c0300090001c030200703118040400792010201108000514551801c001928011808804050b240940c4404000155000040b55040309081d140540c03603e04501c1c0c4144402c1202810100081c24505e0018459a101c1d0544044036030050080c400710084545c611150a001c02c0041d001460810000c1c000d4200741d004803100407090b420043c604111040d849007140c000302c240c1c00060b10007050304507156038050700c10340c880a10070081a41892a000e920f0390340303201c3e804078050540010340d00406240724990b100011400a544003140071481480c110380c50313000902080383c2d00c0f105640040761038100481915102c42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 535366798 1250 535365548 535365553
    0x110109060c120f030f0216060b0301020412030e0102030706090f0327050d080910200606100c031806120e120406080a0605271503030414060d0c021e0d02 67
    0x112042e030704488001c42c0c46083e0003499220621802d502e1103c0c4000c11540b41d462074003a5003850a0720341841620011400940b01c0d130300600062240e0b688101110002c1c0713030306091852001d11340744010b13825030241c0030000d41500c2c50809582d0600100246500300300b03110b43da449007043c9840e20042a10031401440403404038200406100900b05002d90400742d50050b50034038104120031000403404000d0304c5150380001c81440b041c0d030790b4482d03000940c84a03580b183d01a121500e0050086410100003501d00307401c011440240800745401110003d58420302004003200c0c543d11014040d1200000d004034207000780c83c0c04d88484c2ca42c60041580318082c505050000e15003894a003007101e0740310019044541171540c03810300146030f5903000010b02c80c1d4135030140c502000d00100001c0158400e001442d440100080c0a0024125580441101c060390400c04c901c500b0504c1c12008103200e4000c071001c8000892404810114440d0005440500c010a010740308103011000d80c182d0303440b41c1d000148040580d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 535368048 1250 535366798 535366823
    0x60a0209011e2f01020a03230c0f0306041b020d021e07030f140a110108061c0b15030a0605151f030515041a0a050a21030516110109060c 60
    0x3454190b518030704074000f03010101200c45000800f03c0c02c82e401203c00d4000320f6654030900da4040700540900c103c800013008a641c2c10f01e418800620f0500c2907c0100881d0100040012400d6840e68483c03d0820901031469100982c18803003c1d560300c01911180c00540700d2252903000c100c0c0509040c2d031581a1200240145130326681da400402c8100c510200e5540c0e002c20411030090b80108240d140341030040d5421119107104500141c40b502018041351b018110800183e010050781080c1e201c90f01e540800c0d00b808a035609000d02c0301c01028010304581c1802046500700a000c42508070313074010304141900d456420001020440d0380342400341010380301885000900e10b03050195100d81c0d8030005100d90281d032846540300140c111024000c12403500c91034110303031035502d0401c407261501400003904c1401540342481c0b644071145241400300b294010384c08000008140c814400c2d40e41200c942220202c40485030f107059001100742032415800200c1c402c000180c00f500c07500c41c250f040b580207075861079030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 535369298 1250 535368048 535368077
    0x604020a0c020d020109050d080a0f05091c050f0a0b0f01050409030c26040314010501150e040504020604170d031109060405280b12100e0c0d0608060a0209011e 70
    0x3c400c41c1060741442205c1c075002030280ca4403964614000e01c1520510303500c00000401404800300c003103048042010034451202c1e0354807200c681085401d0024040b6103801e00600c3e2480c0b52600c03c8400d44520300501c8080020080708558080c00361060b8800d0171800c2c2c0c0c0320001d1004580a9000c041c0002d11205000004a580c040360b2290301c00c4120300c612600083d0030322800c8994429030040f20818802d18810701f60900a118550240c40e0481e00c0f07003441c0d050900c00070f011034029045d03240b0442c0e40e03002003011036451008031001000c0d07401c81d03e540c1c02414900c0c80d40355141030740e040300807038208044c4c0980c840f4400100c1d10a00b400600300790070507007008c01340300c48120080c1c5a04100300043c18494103003490588508000d01a40d0319159640e140c0c000d840c1ca40c0300000e03004001010b120601402088501005117521840038440d854035854001d40060280405500c8404640264002c0c03002400c01d079002441c004c9420b88443c1580e40450a520307659103004443e0342c0c000f8a940b85107001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 535370548 1250 535369298 535369309
    0x40f030809010b0307030b04060b01030605060301050118051207060912020d12110f010b0301150e01030305031b27010534080c070806060d0302030306150f0d0b090604020a0c02 77
    0x7007150103200006004410407000c207103403040980080d1030701e2440364104400c00415004412515100780790a016491612022801a01040c092a8140407546000c41104001d018074034004190080c03500480c8810b41c2d015a8441d08070380100c13400905081d801003400c500715014001c0d0a84c0c05006044004001d4465001240240907034004005180d80b6001c3e21090401c4240b6000354132070000078480468008140c21941074400c03128a40003854002c0187c1281c100b0110704580e0141031403941c0e940c0c0d61602c801a08021001c130055074102103080754404144980015600e2400b46243c0d00164241006443e40d01814010160062101041710301101c4ac0100b084410001e03120542c2500d05c1c15900c000c403a802204105106501c141c004029000c1c1c20000c00d41c2090040d5a000b401602c25140252240310041c4401c2c01490304a40d402c050002d0304003196052949062195203603114410b40b400642905207041c0d200303540c8400444c80e18a131901c00c80e500b40030300e0348070705030790014507070a020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 535371798 1250 535370548 535370551
    0x70f06050406120204080a0c0e060102011404120e030607030911041a0d0302070f1403242202040204240207060507060b040212010b21010303081306150b1c0203040f0308 74
    0x3c1c829409010000b0701c10420070641c0d150724454400e0000240c2081ea012011900c001c00301030440e8108a001e0302040b401c140b28941241d00848415010740701a10250391400c04c1e20f044d25054070541d0104410282e05507c12203500d40700342c217441d80060218007000251100034000e5155080c207110009020714007013450305e0b10541700303005031042c080d5207529180710b0941ea84d200e00f0f2010010f00164207035150500c411500b40303022404a80300040860301c282040800200340103100d000b503843e0407042c046480d40c0105800e900420941d502c40c1c4520892540f0041c8940345009280742608240c01e041c004a8030009880043e5640750501c07100c0c0d140c0402402c561141e01e07421030b80c02c0040072504d565070b9001a029242e031104090b51030650610260000c0f21141003001c50344051001400044e40c44a8041d802a85000d0005081c001ea820311600a0807800256980f8568804001a801142c400606804035400c0007014040e03040400780c2d030036488200d90082102c2d500303080e860006801801c03280d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 535373048 1250 535371798 535371827
    0x1080f041110120605040507091a0d05070525021509150d0501030c0b0f03070e0f13060f3003020a06050a02030a050603032d2505070f06050406 63
    0x89003160351101c080b41c10b080340d11440b6000903040302c41104101d08180100c1004140c2520100114a45100010004c000c9030040da01c500040b00c1818200340490001c0d620301c2011124100031a00701310340c01600640c0b00d144240045001c015002025071881c00001065a40151034501240c10b440c8440d042d0790300680e01d80303501000001d614860112404054403411700c880d20000743c0d550460400d42c4c0c210045a2000d0400341c010454400090840d40a59400c0742c0705040072010190301c0d034001111419808041600801140950070001441c0d4000104450926095144d0b69440f0815490040d81c240034090f441d1141d410313840c8621120800803c4c526000748140c0700c03441140da584d0700584070f098a010080e90340102c00c0c490084c96910610b07030040b400b24011882c0c20404d801c0c09400305202c0740089251603155a10380d407445001000c86100701000004c0c402c3c26280140d10008080c196801a513141c851040d001c11a0400c0d510410165462a03c0c0d241c10589084003c50745840565042c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 535374298 1250 535373048 535373063
    0xc0d11010608150405010506030604080d0c0e06120a2004440105010902120a0c05250b0a0603050a080a051b0102091302030106120510080303040f0b0a0b01080f04 71
    0x10700c0b220034070440180e00c1d0920f4a0a00c9410306080460035560040d0609103c1e400ca04144000250000d0464075615003140000c2015808a10240d4034801c006000d1380e000070001801c4103500700031200040c401c20402c2c1c803c002c0f0104006280c540c03812014150081d1001c06c000c140f04058a0b0051030b40410038603041c3c0300d1110034540c116200000b0401841c01c6540e02812000e800400078002c2502616010724111700700110900315192090700030f03143c1c3e10032560b5a1491001c07a4858001c03201e044c0c6200400080f0112842095040882040340503600b1902d6500401d074402c044e0b0040004594100005100c0c40e0760540b00e00c40c4a521498000003401800c100e045010a840d10780f4901c512984d40005845448540c00d01550004010425520510402c010701500f60451002809281c805d0300000d41c581c1c0b2201c050030501c150f60040356107480080b04010800114502c8074a580b44982000650358640003d442e050b0b1310160f2280b03011030b101380c00150540b50340001e6036521a014112 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 535375548 1250 535374298 535374311
    0xd1d09090307141606020a030c060f0e0d0504030c0f0807030210050d060608015901030c1e0e060108191103060a06110c040b0d08040f0302040b0301020c0d1101 70
    0x210103d80d0390201101c1207568102c1000614041c4145078901c1c028440c90010301840744590742c006080c1100381c8402085180c0d5580404a51541e81d032208401d290301604840c44010f20410140890704948011102d8409982d80450f801404a1850040320701000040c1812800c5078200090140c070801c1c0c44080004c140a280949102c40c051100100000e4403695100d50411190006002105503a4010010252042c2114074046004524040a4003e0340300c0304030708074071003089907511880402e0304c20101c081c00030042c440004005411a40440c1400c0801c0d85030f0114181c0c10b20701441803038001240c0380009811540929851076222002c520340d448600081145801181d0400381380c141803083c003008011141c2400c145903030180c02e00741000e002115480d0242d5940708080c103c84e5000c3c40d290300301d100d0140c441405402c0003507404900c031a200d5072501d0049050305c0803848207901c6a401c0815400c0e0904040c401c4828407a0707401d02521500d089024140c80c40242c4540d02c00b1150360340d42 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 535376798 1250 535375548 535375553
    0x506040303050703051c0902090f040c031b050402040b030f07020f032208060a0b010e12120c0f070602010203060102010f05070807080402060c0a080711010f05070f050c090702030c0d1d09090307 85
    0x7584440c0c0350503541da00081110307c50051141084005103490100e10350b000170f200224040041c2c150407298007903515410800c2c00b40300e004000d8500d81c07145401c680041030105d004111035024503c903084500a801840d07482010490740c0b11080700b0b099516401c01c026080001c6150340888030101c5002c031220303501990364000c0600c0c01c2030480b01907908039a119508460b80d030f4081c4803c403484100b1610740e01e501007407804003912040d01204145141c034000502d024070700343c10b101540e404600c010540321080c0e80d07818081d0103984111400740c0194030f01504074030000100c0c0300342800340c82c3c2507844078034030380d50000280c8001d84080c00a0b40e00c0f203400e1026800b071410400422010305e21030114281c40e4041450021b4100c1400ca40540c184070060602948240d80003003580d50180d0070040c88076400311a810070b05d0400e182c28107895002703055581040205038000001f8610001c10a0807124101e46029003100e21b203004001d4001005241c4040d07404a01d80248c0e429080343d4001d09503850501c265 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 535378048 1250 535376798 535376827
    0x3040b220b0405070530010905011b020c01030212060616051c030e0d0e1c06110a02060906070807030b010306050d03030b130504050a03081509012d050604030305070305 74
    0x520481c0c031464280e00708410050240081001040182e440b4139800e942d00c00301d03c600501700c00c42d070103a441d04511101c1c503040e025040a1250341d0442c00801c0703140b2001180814052000516001500c034001114005510a10842d61f0a0385c1c000b00d14403182d1180400c101a0341e22a40c0c40d12214954031000f100820700c180700100402c2e102003c04005900c4088020b4182c411101c2c0401494000c40c90600400b80c100500225050f01264407a040000f080d620381e07101800104003600452908502a5040700000d004202c1c03402c59400300c0c3c0741076451040d07155982030200d869000250680c40441d10460181d0000009400141404100d07643c65401240103480e4610040d000252180000301a60070310b40303d140300001c05064103000314a411f03200d260f80c03110210030007070800c00c8038000140d1f8040452441010054014000040c5507511240e088bd4000241c124504503009101c1a005c90f440f8243d00204a40c0d002d410582420300d5600c00b035551344c104030401c2d801e0010400c000091181c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 535379298 1250 535378048 535378111
    0x313050d14060108011a06040e0403052206050307031802010e061317030a09061b08090d05010f05040606050a060905060315220c03090b19061208180a03020603040b 72
    0x8030000a916043d900365034a41021b01124540588800c200c24000e5140081c11142d00c10342504200780d40d00b07500b09605d101002ca5010403500380c45580c5004c01c005621000660040c681e9950502461180e05d40ea23007198900c07103c0c0240801e418070184551411f20300050304540c242041c032313445607030b136200002c1c412010b142c2483c0b4a0f51b0400103059040681152451007d0440c600d840c910300b80300c59260f8181080640e10140c088017000c6443c481d03a580710756000c000b840d881002808030004c02000d480140400f0356040720b401d400d0200104541c10001c03245021100300b6500c06032828030f0081403242e580d10107802074a48121042412116441b01d10212818a012146002d864090030800c2d40440d032440b000303082050300b0140170328040b800a000040e0042821594000094040d0402c0002807030035a12680c2c010031400780601c18442d1800141409100c400040b004c98000c08017044500140c50000a51042080c030118002c500c0e4400c11561060301e00010310350344490a14982d034003201d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 535380548 1250 535379298 535379309
    0xf0a15060c020306092130060a0b0918040602040504180c080105010b0708090f030613050601050306042d0c121515060f0201021b01090c080313050d140601 68
    0x10101c814400c509081000650098900000d0854000c00a001445c0e001c44c04842c1c1a10307484c041a010010020b101e001d9100d5514017910488502e03410b8515103000c08200c0b86144280201c027800108480001c0441e2010100180900b01e00047d04080a1140300050000e54200c1d46c20b0001180700d4a5030310a800c0b0b26540881545055941c0c1c2c6000301c80d18a10750051015a41040010070070800000305983e500c07503120850a07140c0e0070202c0441c0b101c2c0c40200c03035294144a080c00b03002d0211401c880307903202c413409013003900c12580c0c840301419a500d4050b034004081d0fa4070004a04002d129003802000a010004a02d035451001034403101d9690540740c01250211440180060801245401c6a20100c500c00d4080c00400d100e400c5941130420b03136100340c1c1e051151800c2800c810230310070350417285000c1c20f8081c4080e429114080c2d090003003aa00b03500700c40c003407820400420145800000d650a00c03030f44aa40030880c03400c1ca014000501e48030003041b10742142000c00f031180c460701804910302902 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 535381798 1250 535380548 535380557
    0xf0e060307110d0905090627070504090f05192a1206050f010c02150906071b08060f2d0a090c0f030804031202031908040204050c0c060f0a1506 63
    0x2545070b00781440a81c0d05a1414000c00e54070070000f40d02d50807100d40e4011000c0b62050204006490344217040f40c0046c1140004058410810a00380c0e0072101901c103460301518200700f2010320003035210442c0d1042d9904400c000c00d00d8100c114072001ca811140c02410340c0322414003080890050800f000d2039280500300400c1d260038001844410500c81e0340018031007141e2b01e038a80c445500001c0c01071190355602038080c210203045582c200c01c126086403807801000d402255200c482c0e090054103026400711420280703a81e440c0c00280600001341160082941c0440d1900300c1d00d6206003105502c500003021203540000407054418041810440d07486140c0748400854003401d10b1030720b2403096640d40c00c8a9603e800030785052000c598142d0640303007901d600c00f9152075102c400010070b07450360140e40b4880840400281d2103c2ba45a40030003854061842038a0600903a1a52581c10a881c09404a10f0034654081c030001031513410070280c21034003c1101e05001a4140c0140084001c442950f081000881e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 535383048 1250 535381798 535381817
    0xf060207050414012303190c090c1806110a021503151509040e010e0f0a0506090d0c06020a140c0a1e02010906080702070909031e0e0901060f0e060307 66
    0x604090007040300320340061a908869604003540d000d0031802441229800e0030328200f46085d561001c02050780b005440c90151170000641e403401404083e424042c2d41205810025403c00007130080c0400c5614596499050341c05c1810220125040031008084060510806c01d01a0141c0c460619100340f03450369080940d541d00d0000111032456022a50182c0200040f814507514020f951007521200a41201c01058507038a125440f4007500110751850114054034038099031a01c0c0c001011040070740314a050314015510301c02100d444040e01404080800d20070712001001859550003400140441e0401c813171a00051024442c4a421100401081c0c0e400079540b401070000342110848818488440003034801d4407580024182c591501c1207406102e40c2201145083c2e00a001c00c001600120030b041018920340c0c10001c203004c0010148c0d4200b900304550b00c0d40414407461a00700d00c410003074500c08241c0d1a04030112002100209440104040101d4010240c0d841c02d00540c0036403c240d0310310307900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 535384298 1250 535383048 535383059
    0x20a0201150819020402070b1f09140109050c16030e0f03010207080d0216080703050a5007050703030311130506070303020702090a051902070c0e07090f060207 70
    0xc40d00841c48110780055240000c11401c08001803030805103c40b804018590070052000c03a020f030044803c0141580f04450070040030310040c480000c801420a81820140c0d07558204c2a82150203110300c60001520807801032002c0c1c8081c0d088030fa00000101e050b1842d00048036010f00740c04210b0300003100066541220ba6001d8a0100c40844001304100d008524081269640442a22503140560703a003a80104411140640c007207002040613420007038860303071004903140c014010380c404403811000c920500b00754800c03001520300030f4600302c0301d070003c2e4082141034040707030b680302010104103081e40282c10b080188000088030250105c1b178070480080c0517040c04c500d030250070303507101c0b009407002d86405111040240c0c0101b42c8990444006540e210703907401080c10110041d12880340c010303410a003c5000e110004040381d01c194440c0f95144200094082542442d009a00c507540c0d02403d09001c8400910180324501d55007a0002c901d42454509251748201c402e030340441076032040000d41c1200104011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 535385548 1250 535384298 535384301
    0x80a02012114011a04240c0f0303020c120301060c0f020f1518010e060f030709050402030f07021005071d0f040905060f070309120f09030222150509160203120a020a0201 74
    0x4c9600781d94501801c00f810804401c00c5005000c1c4844441c0c400e5039800c0301c099000c1c540528115800c140d001d07628500030b0401078040e60052400140a10540c151450524088025603040c1d4007241e036605034803d4203403141000242510000e80c0d0101e04860208507944e281d406a0b01d00e14441810340352201320301e182c001d81c2402c507604018103003e2220710004842d0313601d2040b81d890106909a441e20f130344900710211110f51181d004550000d100100b449030707007441250910f200f41c989508884080d214041820140c1e90705592010124001c102250030010340d00701c400c16901c802401c0c0c0300c0000c1c251b900040c10356407101c10030f07511134101170180807003154041145a4407841c641414024407500e9550302e145410302c00e048004008042c51078210003841405040d0065400410700c0c0e20801c03100a581c642b5403460501d003003042d464101485500160420003800b1180001c0860516070b03502c4001102e45120519110f0840c041003001c401c602e2a6640c0c0207020b05680c031030040c0c81e80c5905001a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 535386798 1250 535385548 535385579
    0xb10020c1903030c0206031902040b0403050607020a210215130512030f0a0b0301020d0914010b0a261203090a03091d0a0c0309080319110301080a0201211401 69
    0x406070480d410b00120b500b02c0d5010540340d905903a450f03540e40c2d1b1000c095400c904c02c0c1840c150304034000500008c01740b4420010b0001d99026400340d1303400d030300d8100702030b655200040001000c13080100c86c1c0c41000c041d01010300c03407034030341c0c0d4016a140d1403858a505040d00004560304200180c2c15000c0306c00f40320041060100c440e4444039868654105a5200500e120005044684149c0c8605110540391070a4044d1005114408014810300255141c040004034520000810540c0303442e0889040d4a8844c0500c42102c00402ca51042c0541d0000106402e94408400344218440d05195050070b01840004601ca01c007441c000e484246030514008021581c96405805100c009207029005820b4038101103800c02a12a000a00341d54410000d8000d81409040503100040c0807040140035060b450700f441240d103642801308440640d031a000c3d2000c2c0000e0290001d10b1780054025001075020311008040150103804c0e44410840d88200380050300c0c40b18072840310203092072004120788000d822460 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 535388048 1250 535386798 535386829
    0x1030605090f100b0f09090411120d080703020708071e020a0909050709020c061501200c21060f0a0b060d0b0909061501050d020c15010819120c060b10020c 68
    0x1030b10b03085d0442603568083c040c0401080c454005100400c040143c000b0b08a000d4800140c204024507a505009503103c88142d421040803650003000100c03010301c42d200b11010250300072110380c00c107081a104d800c41c0304959503055920307260f05880d48000d0f07030f1414190002072606290214050209141c218200340d90ba900c0b00d00c551780103006000301d152001c1640e40d4011444030160b1f801c0304007403004a13030000105819a5100c0b95040d240c54444001003a10404444140c03903c41c2c070034129201e00c0302c02443e0080340b48616000000821400b05030f1f00d5500e40c201000f01c101045552500700092410350080d01c03441c458507983d0000300c0440c00c01410a9034000c0700d20300a09031920f004000e07900c10650b0680c070241084400a0803261f078504039819a08040001400c440d040325034501c084125080138056132043d4843c0450040c1003040020800049590207040207000c001070402c00e1f1460314103284c080702d00c50348074217041d4003a440303401c80350f400d0070aa0b40c01000190000b1007444000c4c40040f151 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 535389298 1250 535388048 535388069
    0x5070536040f0f06060e070e010207080607090b1308031611120303010b37020709051005010302030c0d0905030405041103040b070e01171006080c120a0b01030605090f10 74
    0x1040042001d9505580100e0f0700b104500d0300c10410ba10304072008000c20f8002c89104003801c2c0c18810340640c080d4456081010a80844030ba09071210031a6540324030480340f950001346039107000e1010880d440054060118a04211621261162002c0e42540c000d4010f10000b1842d0700091014800c005030a9a2a108107498400340080400703442134813413105009041da0180f0002e1341e07004244010900010141c0030110103429181c0092141c0031070009041d40c040188618900420140c64a00c2554002c0e403404401c2406e280c544401900070790002003002c6840341081c0b0200f00a82002d0240c140014412000795540341c0c00d0808000403a80c142010300a503810500c2041b001807064800750b90088a907082000c90107220500480300100c5100c654030203480140c1c10310854018180442c0701ba40d00d6500c0e03040242e81d8002680c1c6480c02040130300030301b4500d00b1020a60a4120b94010030b07120702c043c9400718907980c454000c43c2c2c01600c10ba95441814100004001444800c03404e58405017854101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 535390548 1250 535389298 535389301
    0x14072901060305042d0201050a020c1906030b030d5a050a14090a031202010e010b0f280911040504060906030308040b06130501080309030705030610030f05070536 71
    0x100c100032182c5c000c000b41444000102c8514081c001c10900c82004e074000c1c80711143d20140781c0d101d12035100612503000402d080840c2d0480740d140200b40258074200c2a6144540a00942502180e80514920414901c60445030950f4075620780ca2110301d504285148481d40c007109003c5030b8901c400c03c200c8020800106010401c0c0c00303580400f0302e501803503d8503501a01c036140c99000a0045449510050008016070704204401c0d4064114000a21102008202c4680081c042c40350419075020101d0344890b455000740314540c1d103021140000c1c00b0064010080607102c080010444100703850246040002150030052481d050180d44003038185440c050143d43d01d103a80103030040d03102400040200005100050140d03c54810b1071000140a64051200d03503917480102c4e0301c1c0c1d8410042e06001c0d00402d5008a0f86080000702107000748428882e040d00300c0c0c03541e00e6807109080300d80c42c12541405031820020309540c07440035a50216402d450f82e41401802100c01043c520040d13440d00322034128400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 535391798 1250 535390548 535390613
    0xb090706020331060c0c0f05100305071101020309011d0f03030c0f12010308092419020705180601021c1407020d1506151407290106030504 61
    0x8299240c45000b03000b4860740944000070302101c2003c2100d00140c005445030700141050703104002c8201c260060744211041ca4845800503c48501405819009080d840441c58518400e511140d8400d1140c0303404200540c030280a01d00b60381c010b407502c5030140e441e0850402c013501500d0000528002140c0286022501c0540d19a1a40001041c0c02003078040400d900541d0002001240c0c1c02401449040c0380c151385915004880c0c0c0c0022451034011a2050028800e0b940403e0703180810500c00c0845505022144a0251007003003d1071010003103000c3d242c8000b5a6032662240c00032040c540d9100e0b5500f40c0340c00800245000181d1070341000300304d501c815907680181c000c1000d9000205e00310200c1c0d61008540045200540c401030020410020094204103000069129100361003a464503407030340e4070b0404411940d0f0626140c003204a040d0422091000a41c80e07002003482c584a1000b0301c00390f4102d80300000a84009901c1000441d40340c2c000c01042100f005400350341800d6159034000f4455120 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 535393048 1250 535391798 535391803
    0x309030308070c0f21020127050708030a08010f05040b0906040b120f0d1e0c02130920010f0507050303010b070606030206040306020c010f0603050303070c050726010c0507030516020f120a0b09070602 87
    0xb0750410b04400c0d1a1035005020003400142b014085107001c03655280c020440c001d0228109124513405c14a4845000c1580d2034540155811820001c018000f5500c8080400006220010f401c41e030156502102006182042c02201c40306122200038120203070f40e0340405024800801d071550200c55034481110241c607000300021401036010b46102c400078a0384024a0b00038515160040c00750241e03080b0b6060a2460a02c1540c82c42a007030740c440100712440d10b0151014041c0108c01001c41e0018801400005104070150540f00c0c0250300204449540c5e03008103500b030b40541c0054446a8001034031084080090144d55081005800200031462a503151540c50b800301034506410002035808140911004100340c0000e0030191040034061100107090311114000503010036199400c203c4150580790059044d01c050b950540c903410301e040003078115007000b40a81001280c1c00440c0744001e001a0302d80e5002940002040c80c000d00d03038403d09081901074204020101c14040d48640070a10140c3d602 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 535394298 1250 535393048 535393091
    0xd110301050703022d0d0926030709050906150a0207030611090d0303050603010e0f0a061b020307020d0f230f010501050618030118060507090b070309030308070c0f210201 75
    0x2011840595241d0301050b803045846400c400e0246c80b8140b0785080240403080c1c41c000e0b520150019014020685101c072010039003c102c8082003c03550310708080105082440341e09500c02001082d1104005110003000400d40000b4460401030344076610502c20400d007841a5214000d0740c00c0d1560908400c000040d25905800100408140e226004500f50381c07400d4020b024640351f030302c090710500003486a101d5580c0b5403508060310308500f4040a0f203610303104003000c81c03c0030109501035407030b24040c0e0702401070070210094112071300110303024150003284541c0c000c007400c403030f403040901c0100880c400b20615001c402e41d030814540c1d01d0800104080c0da11001251000d0303504040090000c00c5950019005055030310f1020300001032041083c003081025800207114510585810440603101c20352101c590003080307001008903022010030300c017281c0120783d070650042451812140c601100d40e9480e44201040c0c030203c561140e908904141c10482000c8034280e100b592008010018421043c4000c0c80d11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 535395548 1250 535394298 535394347
    0x6102304020d05042609030c060f12100f23090901090b0f060406080f1f020f0a0f0237020301060806070810060c020d14010b0d11030105070302 63
    0x50018449a9219901035a01500c6200020000ea00d4203003020041e0700c4441620304132081d50280800c907003400040580300c00b00c00c068010285503003448203210142d840081c0c1c1469150051004407440c50309580080d1040c0c103000358206625142031595541600780b6002400c0311175412004501026402d140710340d00c0c483c00c40e0b203c0d9180c1c440c0d4510a0041c01404800f90815003010100301800d05c05c40059401400156010000c041d030b00c0640545842403100a10f26541001c21061f00d10081e0100c0d8642c6142d11038801441c204c0109000324540c0e01200d2003101240c22000f011110302d8040c403828844228041108417000840405500016061284101da06030a001d0540942d282540f028015081c02c00c02c461840c100410003500c0c100b4101e41c5080c41021815010800038030034028500039940c0503048443c20304190780d0785040c20b07440c00b40c030301802c0d90b0b1010889100d507110f8003c4041e940c06074002281c02c480320b406050940c0e40090240c0309040c0100155500075010044070f90b074860 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 535396798 1250 535395548 535395599
    0x180c15021e032209020f04050a0e06030a080706150608100e0105240705150a050703020a210e0709090501061a1e040506270f1c0f060203010b0c0610 65
    0x1190303020024007500300350300700055607880032401d051000606c10051065a0741203400d1100660398010141e8003800844005415030014822040001d1000001d001e54600c00c04001c01c41000e41d00f1010b000e101e8540c08440003403521002e01140d1410b10004030050b010398004540958100ba0206203160014040c080c032041001c0c9142498840b81c405a81900307500c0415645842c5601c0e41280d4801e07401d035407540b2098a0440030a81c490b01910890743e000b0220349603000d40508520303401500d0101c0c420b6540d4080e4540401c6d8403c0c6006000c07460191020f5100029105150300b030041c2160165000040035918050b20090303401c10910940d4001c01403000498000c0210108801103801103070700c0309410000104920300c8000050391b0b03000202c401556500312084483c1c00300180c040c0744441064104003007508034030074242c0e9580c40d086114058044040d0550703440d503442d8100c0e80264070801c4440700125080f540c0c6601404180d410544103040340e011542401d803200300b1415003042e9013081c071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 535398048 1250 535396798 535396837
    0x70302011e0204050325061119031215050a09050c0c2406040903410a1815081005190302010f1103030109180c15021e03 53
    0x5100350454641d10740e0812084071410a4046000065002401414420301410003440c400c640e605251a1084008203040a85075142280a0322241c44444054000340079420407403481016030404600780a11070b65a01c4d031511a0504101e0440300700341c00507800d0901c10f0724108001c1c0d6a04001d201610311404002801d51260951544148503450b80e05a070340c00345074410f01c48800c500824a60164030131112418940d41c140c10401250641c3c0c1c03000b40450002d05402808007001140340c0b4100380360040c0d96841c001c00b000c100600c100800304101d00c2607400500d0202565100c140c1c018840f28411803041d4160800c2c0c2503100c00502c01d4104401c03c2101c100061091f00745903051001800060244040b41000b40307800d4080801c20f010507030120b80d03410040b90f88188501000520590800003860540c1d08110707140010700501b10306008068144200d030804500403802007001440c01860b945808290440b010b8240103c04c15010440050754007020b500c0c640200443d15449240d018043c0403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 535399298 1250 535398048 535398053
    0x303040b061201021305060a0203040e01081f0e061f050406090618061a0c0115080d08070504120b04020307030b24031902090702070f090e0c150703080403090506030a0f0c08060f0607 80
    0x8600803648403533207601c681400054810404119a0700c4401100b60310452200c04241404c15a401122070b50400c0e4003280c0062403041030205502812521041c44607401a503590004055034003036080fa8010641d600700802005500761485140c200c040641886000d00d000b1304030741d950007042c00752224850b0011755210f40a0b02903002501e000c0f0f40105805420ba01ca41c000c5a41d10714904040010076500c1022601c0d06010f00150380868402c07941190428455582d601103405002d0812a018450a0004800200ca5805e1644600c0d0055030b00c0c01d0301e05280741a40b081784008082140241c01181c010354095040070514004581c054038450303c2a110082d00b02e1400c810b640c00741d2100550003101162001d0290030514040380384d001215092140f80c01085206400c41e030a00d120f00700100000c1002030300502c159076000d8028203083c0991640e41c0d0204d4040d074400c4550005c602c0e40d84014500da0340c40780c4213004011200e441d0000303061401d03a01042504210240c4188103080106000c0308 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 535400548 1250 535399298 535399303
    0x3071802070f0f12020a020f0114131413060509010b180d050105091b13110c01140601080a050610210f0b03120c03040e0403110303040b061201021305060a02 69
    0x440360700802c0200340500504000c29035802201c000c030741103070143c20242ca500740b0000318013189540040103100500d11400041d10040d19802c05801028006d2143c48155080f06003175000908550110800c2d100d400030800c19143c00807001c10150b6481e268003405691507015103d8103660000718419603606187d00034802084214410ba075011034250001020040190403441c0030b4000315084840c09214100d01030360000d8548800340d001040c1039040c07003c40085405c8103141c01d000140350380c0341030011070103030382910b40e5039090070b070391003146403d000c10703564013a6040d035102d04c0c0b0a0003000fa60404c07000007280c0480ea080c4c50810041640f19607000b12101b5056030b000d0720300280c02040200400c103810702c003908120314010b21902640040e144419031400c100c604a014820140d4503050900306100c9644001900c00c1d01000f03902d086500b01c0d0384042008500660245120260700e01c0c0c04810000c0c201c6c00e5240b113180301d90040c403c0120040c41351074140203854003280c0f415210518440300300d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 535401798 1250 535400548 535400557
    0xa1202100216090b0a0e0403090e01090b0105070605060d050a0804030516030519060f0221060d02010903030c031403010e06190b0409110702060a05070303050c041401051b0105010b0c100b03071802 86
    0x4015032010024442015005503142d0304844002100c0c030ad40e40e176181390060889a400c6e1000d40426820040d41c1c0010710283d2042d58402c0c801820a8030500c0c1c079888851074910110011900d200300044c0a205101c810041c010b0188044105c0e0700d4400e0640c2d0b1142c3e1a082440b01c465003110320100c808041040355080803501e220041030440d1a030902d2141c01d00340401c0c0085500d607102040c408076042c2c0c20314070141003800d42c040e101d965210b40380d039408072100c0032070760420340c100411380380703018042090f04000798000e00c164800003c0340d0405a040060b81d04591000307544400740c0c0c180030001003081806a07002c0750a40c2070000b40f441d0568554030500e1103200740007988580c001414550403900308001d083c0c0715000f81e50030403a40c3d44811820341c0a02c0360340907440c80c00c40c101c00d80362110f611070402045174681d02c410a01c45c0d4909801d14509480b030a8003c44144c0c8008105040360a0041041201e9441c10342006d0121803400400f02ea2500b0030380c0a0f8188110303401004100c81042601210b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 535403048 1250 535401798 535401809
    0xb0711100905011b0209060d0c03080a0903030e030a0b16261603051302040b03010207120305090d1403070c21030203070305010522021303020a1202100216090b0a 71
    0x1080030315100e00d401001000d0030b01516001c20046184800348107100b8008004840e405810981c0a440e560200091410028812a2081c01c1c0c0900032000424844c081c064501068462804480c11031801030b18000a042041d4001d900085000022445143c1420340160240c42100761060003001d0898074400c801c403031090410b141c00c008910540c460362078180700d081c0455070f845111070300ca0011010f0300c0c03040d5503146805030b0250040000d46450b9001305d01002d4000c000600d800e0385992403038244c1d10381c5074031400481e0381d40f000c00030b000f8010320141c00d0b051030501e807810b800510f8400f1440c003804090890000c106c41302c440042007104106000111807000840401c0061002d540100654822106440000e05110000641d0306049002d0b0080e00180c1030044a01c0303044481500082d0082140105c0d01381c501000000580c03107076030b14a0302402d038049412450f50040d0040c4030183c0701c001520411540215072000d2001030b080103540c1546d9174004040340500c0000002804401075400030b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 535404298 1250 535403048 535403059
    0x306010c0b010b07030206060a031502031512010b030601090b01090e07050417010522020306040f0c0b040303091a030708010e04030c080a050d0608010b030a030809070b0c030726040b0711 82
    0xb10f400c51004024100544c802e0313007207072480d43d00c00c000d2010070709151100070600c0d4417920141d10b006c84a84c0241d03610004034142220414010000500884c0d00b6501c1041c2c165502e14110b41a0b00b014000c203405004040414400708002000085c48501c1c03904c201c82c0e1440c4c68902054007a4858011180100b640c07075040c1d402c21407030800042c000c0509490710300009804031103140c4922b82c400814521103070000c0c064903059507681c0b00c0da202020101011540c0354640c06011400030001c001a00286000382e641841c0d1030708010719040c441c81d9482228902c8882030080200e016480003060303040d144814044102c603125440c081d100003080c20300080400c1008641c007031425030700030042c0450040542060000a540707000351400c0390001090160140c00021100020030b001e4904d0a410190780400c03106125903c00e0012200d0b00f25180d45c3c0c4041e080082d614082c442c40a03c03155208040e880c100345180c038104186a000d1085203d1810300d541d0104101c000c2c800c10402d401c40e4a00d001e001d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 535405548 1250 535404298 535404301
    0x8070602031e060315160e030717150f010302010c060b06040909050d080108031812070602030403021810030201032406120e03090d080702060f0a0c020a0b0a0f03020306010c0b 77
    0x160050710b11611001d00104034440400240c207850001602c901098641c1a1003401780c60300b903c03c0c6a00580d410a101c00d000c3c00c1026101951410000c1400078000c6551310290044a99046414281d210001220100d14802403200d00015014900d04580d42402d00102c400103d04c2c01034050200f14590507071051002c113000808000b5a007140450cd440f82041d113400003607000060340d0108080c082c601c0d4960060140c0c0220b921182c001648000d030040242c1008507600c6040740c54200fa0390040c000603000800c040085042400b40402542e403140703624602c03032400207090000c0301c105102c0a0304040d02c03194001081003081000c2c4580903407010290440344d44840c0d0141040034020000400a071a200d68044903120200594880c00d40042c010b1211030000d40795801c0b40e82048509076401a800c0040101c04045080100745088690f00c846482c0b019500400c4000384059000c52001c0c4410040b509010382d2040307007603940707007024103005031a5124840100c0b64140b05240081010891a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 535406798 1250 535405548 535405561
    0x51204031209120b1f03150b10110c0405150904030207051026070201020c030c0a06060b0f0a110f030408010f06050406062c130902040f0204210807060203 68
    0x6a100000d01035032900342d281030340c2d08101040c80802a4000c2c0034401c011010982840405a8030b40000502a0000161365202e441d0b001401c03141d9000300b0314865590300c1c2000303603007031450903003c049030541000e04034420039015003501d6140e1901c040e4400e698601c0003c020403900c04666142d0394025201c40124549403030007958429883c000d25120781c500b6041407131010310a00011b410380d481c21090502141c4540c086890306480078051034159502488107120380c40082001c2d0169100c0c00c0001c104461a0342010300c21521540c20107004003004204036480101090102d583c801c5032440e060030790010b4190720900706a1140990303051800009000140510150444411108481000c00c41d1903625010001116814482c0300042082c88011038100380d051900c020900480750007a0561041c030b140000e0040400c952640710655840e0b80410030f500786440351081081415104610341418695040b061030341c06030306502000d40d954105010840f210040d2800d4070f601075000d54503400d0a2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 535408048 1250 535406798 535406813
    0x30402031606090b22030b15150d0504140f0a0308060306010b1c0b0a090204050108061f200a0c0608070206092104050a06081b0405131a030601061e0804081605120403 73
    0x8d95401c180480e2020302c3c1100c501d05180b0740c0c80d054028000e0240b409960b02c440d980903020092003550810064480d00c5645002030064803620000200906043c17074040c50007a000e01c5001d06818003d505c41c50042c070500700d0520407246e9842c410711404142001c004010700c00f42c040070305400d0300408034420020b0b1449540d0040c1c001d03220300742c0300d820b050350301e50303081c06400c45200517000100342d08a441d1584460042c034003841107855892101e85860b000192452030304405000456030a89a15800c100c0c0e56404043c89030405840c0c405043c40303090885d81e00b60344039541d288000e4045801e40c2e400d000140750600b21401803401500c2e0300101b40c0d4801003c3c24000c01240d80d0341140310302031030366a0308501280840d015100018140c822407101650048000e140e0411100000001912890b100303550400c5001c2c02440e0941c0c804204015002c00c601c0c41140040442c818041408140000034805009035500c5030445221764035560a1424560300e0304000c44101e4172035110004022050140c0c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 535409298 1250 535408048 535408051
    0x602030109061e0e0709080d0e090a020c0a031107030c0e041106030903030712020d0f0c0306050118030204020a030b0607030210060b180409030e04020c0102030402031606090b22030b 80
    0x608040000e01e90310303020b1074940f840300f820072a40c100d410310040c001c4115500f681c41d0071484600d0602015a241e0748018508160000d44201081d41d070307410351065241688103964884810751040d418400401e4a40b0b55070741c0f07401401070504c81031519844594031700f08030003001580c200c080e405000f590b501104600250036035047d6010700c0d085113168058109001100d0040d101c80d00290314540d40c0c3c9100701c58025500d094008441e800b0406040708074075038060840c071604081000542c7d1210365a000d01120030b10b500007414405200c1c80804040082c652460803607405860241e030301c0300c2060044008220540001c1e0b4400d0002c42d0400038554004ad000741008004e07081044200d84604d031322016805400d003803079001d5000c41c420350a1400c0541229680520a007001410310801c500001c2c181e0300450500901350307502008001c1907260030010018250b04011400c1100b07410500e00800041c2c09000b0340c1083d01c0002241d40c00081c0c2c0007028101c4000318007080d003405449140c0f14112400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 535410548 1250 535409298 535409309
    0x180c031006080f01110f09012025060e093105160b040b07060f1d1203070e0616021503010608060a081e0106170d02060a0902030c0409020f030a06020301 67
    0x34850101c1e1220f00500c03a4104003280e4403e100d040c518900180e81182d0300c02e0b80440d042000a200454181072a0024810180c680c407010f0300314036101122507c0c251803110b10080c0c8541840000300b1185030000d4001032216819940f5003100d82d40e040c03e0074003201d9000000c0881c040d64049460b00d05500c4010007440070320032416185075082203030003002c0d4034180d402507412651003008104039058900c00100306c00741c404e2401180840060220104551404070074143c40c0362a02c0707105562640901140315428a5901c6042c21801d02c0d80008042a5880880500882c00041c1c51001103180c140e502200b650f000741038501091010521075200e82080c85902c0200e07540101003406481c0c80e03420002596043e000034144641007440c038511119003104241d01555880c1e20110b018100c180030320081d00d4080e40185030240f40d0741c6c0c00a20346040105060b17492440d0007003c0780142d0300414028014501200d010800704910300000700c80040301c214196051240280c03803070400c0050740156040300c0c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 535411798 1250 535410548 535410553
    0x31608061005102007061e1e0311070507032d020f01031109091303020d09030b06090a020c011401030c14130203090a0c1404061d180c03100608 63
    0x8407502562040700120307006403580075507a0324041d00d600d4898002d0a00d50700e8559508941008280b4090b81000c03000e0b0803590005480030707911000d0700102d241103880b03400c2c140b03810400c291300030360647c9507003590880700d1041580720342c18121540d03030b43c0003070368061500481560215a92403410a040000f0605160a102c141c0d02e0074400409244075090750b55a0040c201441500e10b0b8070046005012059810000c05d400f440652401d44030580c07583c1c86a141e070080d030b40d038040071b50402901d0f146070000c142c0c04000c4c0c48001480040c0d00280300740c0d048034080e0f414443c25141c001405010f0b0040c5c132940300c260341ca011b03682c506082001c00140e040300d019070800d102e859103070100741f09980c01501000d81c00810021a10b07500c000164006d40d804094182507030041080361740c424100058560140350100c0c90090740c00240d141a1094070b000f4035040e002154861170701200208100c60042800d0034800e0964040c100080703051150103003600c1c5c001e00b60355a00700004c250074010461070242e0311851 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 535413048 1250 535411798 535411801
    0x60f120b0c0307050d0507050408120c12031603090c0509130b01170a0f02040b06070b0702060109020a0c030e13051023011e0207090906050a0b0a0317070204020903160806 75
    0x450307200704903030046000760344051a041c81d0b204084040c1001405c1c8208014041000080c03c07002480364407040c15003241080e5440a0100c1c2007031500f41400d0788844040340802c2031200e203803034040c800c002c4c020700b504020070915014208140410702d164481c41d044200f900030400604541040c0501091150101f1655a41c960325807180340c621030100c800d00e5520580e8030b000442d00300754903960760310300c020804070b00e007a142c07000714a071500710600c111614102d141c1400f4080380c05210307030b07070140c0b96840c1d045041807820900200080f4240340c1c050103020304c105a0091640742c0f0f445400310740b5080c0d2014801c41c100b0b48401e070000d500d030b8800e80403081791001d284c0101c00a45411006040710580d640100002280d40c20070031b0418044041c2d0661080c881c0c0020282024050710001900079600043c4501d441c40042d4181c4180c00c0c0308510522500d46c080c0005400b81480e408000035150f20340b80c9a00d107070b201180007031241044166040c880c240040240c3c10f48500240b060310481c00c191601da = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 535414298 1250 535413048 535413061
    0x60e04060f0605010206010909140d031413050304030b071206151403010b0d05130f0302071a1c270804050a0509040f08030615130509010b1309020904060f120b 70
    0x215841d0f40102401030304190010040700806801544445d03000311842007c1d0081030013580d21342241d0f086030f040403a884a000170030700c0c00e081484a0307108440a5500564000542d0341c2d50b22407185020041c0307000741d090701180203a442220001d8401d20b400302c08004a941300c030071000110794440e01d00b0300026004290b0a180c040b900044d203040341d550204080c20407600190344800b508006001807542400000d040d40841c04011a840703031503000342c02400400c0c1c1841008d0102c1d1541c0540740a040000b00110a007803a44407014420140c48560001521040d1141940031620078000e10241d50309501c1000d02400350b120b006001b00d60084076005e805581d10418040b00b03400444000c1c0c04648421000008580d240004541c40b244c02400c089070b00342d4400c01c0c5031b030740d4000320143e01031009103100a1006080c951030050240000158190404445100c8001342c0704030f0740543c41c20180c000c98420555181d40d0800700242c0b900384400c803610f81d104c0b8081e602818a080c003d0300c806800070046101c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 535415548 1250 535414298 535414301
    0x203150409111f020705240d0207111e0d21030f0506030115031212060902090f01020105090a021e1815101707090e07051803191b030501060e04060f 65
    0x42030f190b58015004540c64a4200400250b0365207665a00404407031050080718846002049804603802006845908a003030040800341c1c90f4414a000e0f940004118107018a890701d44e0807160401c50302c1e00b0b10440c1034640b100c11100e10f00580c070345910f8540c1514032095015000886610010745080080340d451504150a8030b886814400c0090300c3c041090012417215880c0a624105070308207402030781c41c4184003000710340855200d8151a5404200c4040e1890202000c0032007220920080c449810500e021549421520000038814910040807144008032071030303200c85020009080160751907909021176140c00c0304903841c0100d030340044071040062804150710040d00c0007683d115110b94a49980400c814880540301e0380912014101c0002c030120600a283c0c455002c1d035680c2d42e10359410b00301001c020805000c080f8420b0b0044106c0e100301c1740e41040c0d0220b1154000401d046110401800201d18003900e82010300075508100780404e4064403410a5401244500000c000e40e25841e0040070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 535416798 1250 535415548 535415599
    0x1804140c0f07030905060d062c061c0501050a02070b0c030f040605090a0c0b180f03030a0804140a0b060f010518060a03061d040b06060418020315040911 67
    0x540c0d1a00c01e0040d80160051040034092840c442c0c10b011861a40300c0300004c566800000e0b640b40c030070752104010302a200f1218084810602d15111750a10305d0a458176414190b80001c01d00c0f4090380002806001184205101c81000740c1c1040082116003800b40480000c0c0d0b101c001c00355030402103a13010890048504c1c040728850588100600060384842e0380300c0b006460090000300030b92040b43c03260b8010549180c02080240064032015a44002c6140300c501c1719030701d0303c0403544640748441a580c56511301108641c1080014a403901c45035a0710700e000d400b000314502c5462482c0c41202c005104000ba50403031a80503407000c030745007810700c45000011181446000c0c0020300004c05a1040140e90800d40094160005181000719416441d0502a4520314050903000c0015201400b0b1005020300c4d0300d000c9400c00026140c10b85084d00f0801142d0344070890300900b050480e800000903601214108030802c0040d0300910a01000d007150410f0300a0301c2900c1d210b28420006075840c4020558022440c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 535418048 1250 535416798 535416811
    0x106080903070803130203060a1a1c110a17031c0c17040c17150901020403021e060f0a1d010906171b04270902011d0a050402180414 58
    0x114a0b08030b1540d51001281c1002d040000010b40ca100801c0050f6021702486114402d00340001810002e441c5080d9088410100740b18000c6080c0d03c55480040e001655040981380c1055032038810300544401b1038920b80c29079210100c08007444508881d00c0a0100050622060700341c4220001c0101031000b4085822400030310002c80c1480000c0c0c040f00000224590340070b4010032496091540d00c0c426814040d4962024420903040080240c4500c403580701c0c82a0816414402181054116404668103404402610011040c80d40280c903484d503e0508550f0000c203100d190320b07200c90350950007074400c104d81c440c090307200c0c000d6181c0703005d084d440303500135108444e410f42e00d070540c2002911264011400c09000900403001002c0048190498903006000504240890008001c0707000c15152000307149140049288e030030030b02c180001d40e03408100c0074246124002e2480c403e01c40d1100040f9000d20030b91129402900104001c00780600240124192160a442c144682101d02a25a003a1102203801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 535419298 1250 535418048 535418053
    0x30c0a03020915130605030111030610050315030d030603031229042c100912110a120e15030105100e0a0905040b01180b0901140103090c030c0e01060809 67
    0xc00c05441c0c00000b858001a940c421241050320070340c003140c042ea907003010308044d568540b00e0410041c02d0910074020141c00340d014035410342c1801c4000031400046d69082d041089000320104500070b40b17085002c0f4841900500b1070703005242059014010f0500c512080d8046803003203414042540c000d01848404241c01a4140712001c0700c000080b5001b01280e61141d0003d90329032401301c0d42e0380d900d102120b00e9a1080e2400d515008002d150900e84903405c801606410b050003090320004940000c143e84000c12420034400503282c0e428203510b8004840000b4003151050101801c41c00d03003000b1160b002c07000a8540d44621000020407a01354130003845241e401025402e005a5040c1c402c40b0720030001c00005208a02065686500d00705550302960300740c0d00405003100401507000403a00d10750301004d02d00c1e02400640700c90000144800e005100b2202552104407050310b0aa10070303401411840c1d4400300310141282c0340d05107150106c0c5180280101d60b0a628004505c0900640f0722a2280011400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 535420548 1250 535419298 535419319
    0xb0418050108010b010221091504090e0a0c1a0c060f0702010f060b09040507050403150b040c031404020f03100c0224061c0c030f050d030b0f0105070201031a1009090506030c 76
    0x5000b805c0d0310b6442c3c7c0080c441500b4442804d041c1c0e180c49120300d0b8515021001074a80e401e002008044662204c800100d43d0300001d4007900007001c2171885411119285002d00101c001411615850300c44e000b481200c60140c8820444205481c60110703004c0c0344075a0080140120203038142e02140c6644c0143c03035010f9030501c60300c10b07d468641c100300d0780070509140050a0075a2070303403424078a80300c410b694442c40e41c4401c6500c1135800d042c0f003441d0807066a40b4060109569401a140e110107010784040c2c000c09900016003150346040254100b101c5400301e00f013149080c0402e00948032a5440b10790103003400d5400c5412003610f1000301e142d005400051412040f10060f00107103e000d107445900b2074000c09051400004071b000c1c0c08981d0b190b54040c401074001003104600c01021580d00c400c050b803081074514480c0100340d80c040705603500150b0a00340003e1900703c441e13168285400d49400d40d60305c200021035403d0780a50018054040310700072203080c080364450134200744d240d444481038103400510512 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 535421798 1250 535420548 535420573
    0x70b09040e0d110c091b0313050d2d1403040302010b0d061e0504050d0e0409060903051b1f18051501050f06121305070b0418050108010b0102 62
    0x1401049205801000003608180d41c44079181400e0202c060b501c041001d412000c244200140140040f8000444000c1c00c02e107003d14080ea594030742425810300007407020001804210212404c200a1a0024103c034a640c3e41c8036001400c1d082d52508105140c0200403258540c00780b441d800c496800308a807605010a141081038440e5600001d10607003c542d220100007800b80c5a4008a01000d0302604d004294010407041009131806080ba41000f201e01d050100000300e100419a07640011036440e01d10240041e201c00078000d440303d920040d208502d400082001c150300702d0010f080081440904258208014200c591100103399880511020411000900e04080d0307014110740940c2d0411a00c00c855540c0760b541c6001c0c0481603082c1c0d51255000140640c0c5405000c52100301c42c2150042e1812081c842e07629007000b000351010701c031011100b92620411105201003001780c41411075103602c1d03603a5603005107203030140001c940789442d00d00170004c2460031741030003074441d0400103070000c06101e400c40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 535423048 1250 535421798 535421819
    0x2100930020705180103031115150108091902091b030f04050d05030103030207120f080c010902120714060904110a0e10090605030f04080405040618050c070c1802070f03030903091707 80
    0xc0b04c050089d0041c3c4203551000d40c800c0381d29902980392010b0440c1070041000c0003405000780500740610b1680103020104007101c101c0c881c003d903185c0c1078070040003a4980c8a140340071040002c48080034200d000c8108440c0110004940384540e008030100d6401d041c4980054903103100038000134005802c180c01c14808604411001d01500b88140400c41c484400b540310307442c207a0400b031003800d07083e511865180309510f00313100d21540c9001040c000d84400c0b0310700029101c0b54580903280c02e000e00b50105a0301c00c0d541d01c0354042e5403000d486071a090744d51421500020500408105c0c4140300d4090707a50345440781c81c4a0341151059820580342c46117581c440c449940300c2940d00410417140000700f00004125600d80e07014110041c040088000c92840480c5143c0d4103031100188812540d40c0f040c00028041004860f1040840300d0f002c807500310140740712250034017900c2601c1c0c010300302e1341c000104802055816440140c5050103034ac0c3c2c1d000e469072260204440000001601c0b0302a07440020140b00340d000f0b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 535424298 1250 535423048 535423067
    0x607110a0804030b0f07050a050d0e070306060b0d06080703020907210c05040e090105070806120c060f07061a0f040b030118050a0c080304060210093002070518010303 73
    0x2000225001010260380307107a8682e000d40c104640c0e00d2074010512a20300d0342c5140d00d80d04003009060480c20b149548000030450301400c0441010661030740b413403000300141408200040d541012080c400d45490342c003030b80d00a500221507000132a190a0001030107000c0480c0d2030082c3c0364020485d102d981c07210201100c00c0c00c689000003030140b03900040444603581701d105910001040d80c550301d4a036484c212640c2d502d42e100812138165641440204080c295201030f81992154084842c2c0548010401c05241ba1001e0101d5907504540005540030380c00c41e040020789800d42c0300b1502807003d07a410178040074240e0b4402e8007464001d07100c548083c1007498150010010504003400014040c241401d8100c03801c1680354069685401641256081c09070295914016004d1000158500761070b1810095a4615001113440e102d40e80d0a000c00800054045400011403600c105000c001d050400c01c00388a10f054101002600c1001800903280c02c1c03140c0900380700c8022a05903480360703181d5201914013004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 535425548 1250 535424298 535424327
    0x2b030c1706211b03010e0a0b100906080c0f0f010e0103051806011d0f0f070302180603160216050a050d021c080a1d06071112010f02030a1d0607 63
    0x441c041000c1d580030020448400b9602c100d401088585035581c100c0307064034904a03c0728041c0e410301039051041107000402d02003142e4080000e000035031307540c6101c2024080319006250680d0401c88002082c00c80040e1000341c00b4821100391000c0408181045040d4440f100894041440012202c0003580240e1000d035110780c15400702c50000d441d000429082c503200360418251a9440300502c3c02040d260094194082c041e00c0b144000e0b030909426815524030700a0200040680024440100c4192034071160285003000c5d140e1501d90404203012440d0003111b200781001031161114901084008110f04421550040c003e030b2a91410081440311203584000180e0f000601c00144289080942d40d200c1e0196005216164480e0540342008100310201c20b48912107100f03600ca651903030380d103480450b5121035003c800c80b840806c0e08004254140720300c000d8117449528006a26003841c6454008511400d08008100000a0300c075403a0300301024004044022588000c0000e02602c0c06545030020100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 535426798 1250 535425548 535425559
    0x1050130061710270b040840050a0302120304050a030308040b100302090a0b150a1214070e0108040f0f120e0103050c09010c142b030c1706 61
    0x380c841c1d00d2802e80420003500d0160681c4102c0d480e402d0040c15200d800464201840d2440f6240d010000000c0b648580300030140812000d84046405c100d00341c0c086920312020358001460803040d00290f0f00d2402c1003a5444030064140118103410300440da0200070075948000d02140605045400380101481040203002d080c2c8001c09c0041895912101c0e040d004601c05c1e595242a03240030301d800008a040900922030f0110104001d000607982d000c9040e074012030703041002038190036040009a846c004081e03c0740d42108c0006070b240703007140d01c4050603004a240300414000210300f080d0260395100704450050001d203d503016598298800c01420360854000d40c019125020140c6803043c0c01c640b201c0044401c8107504510122094100585884084003403c3c00c21882c6082800046d40303100d20382c4c001e0704122400180b5401c1041000c8003411007001242140d00e4654050700300840c0d20325001820201ca01c1d02c1c03505400b40d921038040c3c425624202d540300d142d828040200c0d511122005021183e00c034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 535428048 1250 535426798 535426811
    0x12020111010f0903020f240c0d05041b050108060f010c05070902030a06030c0b0306090412030e191a040309180902060a1701050f2101021201060e0901050130 69
    0x354800d015007064050002c5001400300820b10b40070385842d03c09400801603411030140b0140340e103c034000b8205860b401080c0c617a925511403402032a1031041342001c1030340501c1c103401e11042c0300300f0500c04003030048a03050410780e00d41c03908010340b502c6100325446a070248031188100c1141d44640204e1010f00d200d4400c0701c1409885104c0d030010398004686060040d5921710081050160701030303400d001070480d81005459410328a001c5005080000d001078058406a034161a00c60704c60741c80310070704c3c00d01700041d207154039451101c904480340036072000d850213083c030300084940c01540039445000f903038076481d1510030702c0c070f8604100c04408420210f0051240c1e96030388040507840300401045250950758540e82d1681045000d500388001c1a0810340c001d031581c980c0381300c2c1d0341c03950000401e036405c0721010382c0d00f11140c0d100001d01912032a1803250706130071038400001d00f00d60407039100388515070100c8001000c0da07220001141c1900c04034030100d00703d4807026506800001c0c0044500000c4015034000f0410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 535429298 1250 535428048 535428077
    0x305011221090f0303111204060e040902150a08090106060915030b0d1203020c060a0e190204021b0307120c110d150507050d180203030405091504090b0f07030c09120201 74
    0x900f2541d0041d40417030ba0200e126007154009110303441e00d000d185c0030344504040c00c0c510020b180182c034126007409581e50311142c07002d550f02da40101900c8010081c0c142c0e0f4510072144001c00800080c1d42141041d07080c61008282240101d42c0b29054440f140c80200c56482200011405001d40040703481e04520079000040105001d102442c45480c015240560360b21038400d18289040e00041450843c1c2c0d1a0030301e80751b030860703002c98064a0360681d8100b1a481000c07030b0000400030b100302c00454100e020054403980c1c42c4600440500802030181e13100b1108505901410b130303010101034000030f0581b0034100060209180c118140100a8020700c0001c80c0c280301c144618044820651b980c6021030800b1840101903106030150421819005c00500d8542500c0e5000c00d0b5603001f80d0040a100c2c00c840400111066426484045031940c000e0041c0110350700e41c00c24a850b50b40135200e4505134228000024069402401420800440c0d540d580380a2460101102c081c0c40540008904000510240006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 535430548 1250 535429298 535429319
    0xf04050405010b190201200d1410170309130c020c10110c1519120c032003130206090409050109050f2a010807120903090303030501122109 61
    0x20b03183e111007040d034a018880142c2e0b20403803545606400c6a041000c030400007094200c042007000101010681c503840780503c000c2c0603001150100c601006010100007690b0305c4600800c084944140e041c450f130100190075951a44520048650800c50850072400a0076042c3e11200040c9a0782c41592a01d600b64400900b42c181400589c00018180301c1d191035841d0800d01c0100d4040c0011a01d02c1c5070752001406e01c20141c01145012048400781d203616001070f030f02038030583e00100c0f24941d04010039400c100d0302a00803c800c0603d60020310041c0300345250b09207076504503409019004440030030b150040c0c2c208038041d40000300d413980003611100c1c1c0b039000035400d000303101a5074030503405420401e00414189203004501d224644052070190708000b15480607030042c1a800000303280146c19540c890201303440d000c50400003440054038100041c4141a0310003c210140c92003036900f40400d0340d03918420203042c0101c44000e80768030200100e840c5040d145030709032070302c805103420114807260350f0354686034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 535431654 1106 535430548 535430551
    0xa27060e0418140102071101030221091e060118140f092109010306050f060405010309020d02100f02010c020706080f070903140d12020c030f0f04050405 67
    0x102845803440c14020382d420554010000f0781ca03140041c000d50101d101030301c0366181951890311a6109000701c40350410700c41407000e054008900610520340000d056400c15208040d0b14045c0c1c075100c0a4424a04050200079100541c540058401d04201e01c6415405951901c1e004480c500181c1d54990781043d080201a81180d44110310f00f46041106040e00d00050308011125580084403001840182c131300f07a80038405e66907150103205071000100319040e44490140130520641d4072276401090002c0c0001d00c100d40a8455402140c00103809000f2500043c60544140380c0c0140c09001c0d00300003450b01d20003030175143d250120040c1164070183c0b607001e404030514049000b10780300d0003100001d0340c0c202030141c10020020000c240e0302c0000603240004146803109844c00800184203031031a860240014514010303030501000c0c1c990f0302150800d4a20442440089100e807114400c1d507 = true := by decide +kernel

theorem cover : BRFrame.Cov 535251798 535431654 := by
  have h0 := BRFrame.cov_init 535251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 535251798 ≤ n) (h2 : n < 535431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
