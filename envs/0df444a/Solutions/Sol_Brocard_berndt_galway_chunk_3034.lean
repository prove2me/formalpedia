-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3034
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:28:08.724932+00:00
-- url     : https://prove2.me/submissions/e674268a-7101-4ec9-8151-de005142df46

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 545503597 ≤ n < 545683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 545504847 1250 545503597 545503631
    0x70303021c050708040303030906060302040203010902070201120b18091c0c030e01080105031b15030702030a020601360b03101506050726040306090b2d01061b06 71
    0x140600845540401078030305a40d2140054508031500400303190301d46490340e40d00303134028641c198040b1aa01d0712054000056550b603c0514000c2088038005691000184001000c103e2405140c0110501d00041000c064407000045440f01717241400b00e44903600c031081142d142411888010304114a590400b0030300651000c8d81001c8a032194841e00044404000150380c0c0d86424040c091b0554001341440c995084014840c600c00b40c0d014003410904a5400c10040f100c1c2e100712003d8000d644001618a071036681000902c1c01002030031440320030350340e0007100f40281c50144405981e00c02d08800211800070110b81c041c040300e101c0103088601086e541d07001d12014040980e07642e018600c0b41800015007601540c202d07034059510221044103441c00241c0040301205040b4007025410b020b105c00310000d6402d00c1419041401004103003e54a000d01c008000ca4180010342080c000c9a084c4191040c080c00c21418103550300750400743e299841d01d15101e9840040d8907405840241001c1a00490302c01c46 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 545506097 1250 545504847 545504863
    0x31e0f0d0b010f020a12050d02120108240408031302040b040513020a150e12010b06130315020c0c2103070605010f05061c0507120e0123060112180507030302 69
    0x283c840080303034000e00000741e84400352044064114483c110450007550310400c01017134204058074006042400703008503401d003420700742c021045030b23800101d08100400341410740c0d14a92130710003110071003403a050303640d10140d000143c40c2c500d0a110b9034419104568540c2c109070301c1c0e4003001c4e10800c40c5180011050f000780c02c41d184141d0080108070300201e030500c0c8480041010300d40a407140000850300300d051212091494901c060300d0755950035910b0856440344000c00d5041610140d500074a811b40c1031a045035100700e1083c20441c1c0c130401007040c40d14004074603a4003414007242c3c0351645a01030001c031a161600031000601500002031000c0800c02140d1005060310b40445400340e9180d00e03441440090302c0713541c3e529a505418201036000b60003140e04600c2c1d111710a80ba0101d0710300c0e580300440c81030760100c086050499448212001c01c1ca1440d146140e0926605120000241407850010307002610424040c1c24142d21040044401c424245485486544c0881124450f6030b80b400d00035210082 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 545507347 1250 545506097 545506099
    0x3080d09330b1c08030c04030c1203020d020c0f01210e0f060105102001020915180d030519030b0d080c1b01090605090d12031a090405031e0f0d0b 64
    0x1402c2107641c15800c20740c096020054449040600c15441600c0307100458100070b080704801c150822003c0000b40b030f10f500700b0380142030507a45030031401c42600d00a42400081100b110031540288004d2a0907594010f0240b40b4560078245101c10b03185188426041812404000708081d080441800c203010300040e140781134001035001c0c3c8046907221000c01508488120200c00080d645001c04c41342513881140c3d0780c5a58030b08000062030a4841c0d03003c105604448131011111400100d6154a04403080801200c01482141e00010f8180c0966000d4054042c100c0c209610140d03562038990302078040e034041046100001c0000110242c0707454070020940c010210440180038203020a100c19556420001100c0016140c0c2c902003810011708844035080550403d070300c00c4100100301d000c10318290b600002604180d5001c20300c001e40400d240d190304e03000c00542d0b0041c540c110811004c1a0044165140081c035200c0c250302004088404843d240529800384c520500006908070f4540e00e0f5500100c42c0c000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 545508597 1250 545507347 545507351
    0x60108130b010315061403030406030e0f0604030c0606060f0f030e070b1206121906090303390509011d060708030f0603010605040915090312021b06010f03080d0933 72
    0x62502400251b0b064071024068250340103000500905000e900010803800c210340032100c41030210f01c066440c140003680c080d00810b4800700301c2c0b41440703642d0107440080c0045052400c0c01c4002a01c1c000c01240c940741d0400c082640d180b016040429040c81840018070394100c40a4031006840001a8242d10640b83c1070f11824044e4450945c50740c020911aa60810304280c640750701519407940070203062040d00840405991f1100d10070079646060403020680000301d40d101c83c030400e4003086110b00a43c1001c0c401400414480600580c3e80a105040b084e000b19884040c0c403004617012900c14026800700400012000c0f081011740305903014000d10414003280280320182d43c8200307010889012941c050140000c02c4102c3c4400c0602d504005402803282c40c00c0c94068000001c1c00d0106d800694500c61040c1000040030b00910f0100456800b4202401c03500640d1440c541d1501740500c00d05100c0d201c1161121030002c10710000ca141c000c036002d02251014405640700443c4164410050b070f01100c068 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 545509847 1250 545508597 545508599
    0x10080a1803020a141608421b0f09180c09040917041d01050105030f1f09111e040602030a1d19061206150c02060702041d24060108130b01031506 63
    0x650303105980700c8619051f00c2800d2103000000d001e401040701c001e020fa60320b04101c00c9101008418131004000c0c0800050b0481c0e03c8120000400090306485035804070001e00550070b20a100c8000c1c0200c07004810b0803900020510b01c0c520782005403540b0550021034103071000c14001280102c0d4039042008003442002c9a0385c030781c0c90381c2c0151560700050fa4403010700800003001480c0c1c0c4c048089051700b8103002c0c00c0f6a007202d650707a0b0307066001e54545507924401410040f4400d4a004c03100c114641e0755588100740c240c142030510300c009560b80903203181c1c5010404031403030700300b0042c81064110b40ca0b06c90103444105100550342c14602950b80510410b00080c64a15000d0002071141c81208281c40e00d034900c0b858080c9044408a522800300003041e03034006c05c100b12140040c0d80340d100ba800c4441000c0000341d241e11240285070b0070800d0906085d24190b0464031644000d4001040c0c0a84c80002400c0605860b100d090808400094030b050042c01d49000c8070012007441820034090385141c804900c24002e40e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 545511097 1250 545509847 545509903
    0x20706021e0304031106091e0f010201021918030f050a12030b1f090f150806090c0307140403151e020a0801050d02040b10080a1803020a141608 63
    0x11a4070031150038a800600c0b06000042c1c410105002c2c0582c010401e60400001e800029a1084038203070030040d0034007c0202600c18107040c0042045540c090008500b401c2c94076100c0da6101d03001c1501d02e410003524001c6214803d0203c0e0b40800610341061500c103004c01c4c149041681c410300a40c0c2070340e402800c02c10705814980b00c1d0180c5101030101030507032000c180800424081c0b0200040c01c5000b44581e0b224040760484030300c07004d04018a49a0690014492010405400c8180180c00ca40c06031031102c0402c10703c001e2407001c80f5004401f91400008a0384181c2c60300d071f418080c5030402412079484030203003046191190040c94400c4056a00040000110144902248190702d20003002c5a55400100120b18004002211050000d0000718169000b40006805000070010b0310380071900703010a011008940d4415040c08106014440c50a2620307914069502e03814128010b284008100d018681d118040c059108207440d02042100c3d000e032181000783c1c036244002c003030840098003a4a0b070841 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 545512347 1250 545511097 545511133
    0x280606050405090307030f090b070503070c09061a0703300c080907060810030501061e0f0302060d0207032717031201060c1109040305030f0f0402060409270302070602 73
    0x80c3c035410700851806605543c1038580d694404041e000780020340d04c00051541140300140701e80c0d84600017175941ca4006140841c1048220340090000929040c42882020089030b4250300c10345480c112140c8982503882c086a900500220380121040d18008104180f80500011006410100c10501690000403001c4071000011154070b0380584c030aa0080241034045d26100e60060490403c02c0000c40d140d440f22030a50303025901901511032642540c5402c101c400070440094610281c805400b10710350f0b00026814003840305140c080b035600042c03010401d0700401c002105035154250503001034016030048084020075119071a584400b4910305840f241e07000c0211500013a0b1020b0304611642021000c586000408004a40c5c8401c0000c40d20181d075140d041c00c502c10f51190f40c9140d540c1ca810b0301c0e5000284c0f005003965041c14001d07070a201c01652a44251019507444900015028107040045803940b0f800794403005010094602040505070b000c0b8071803064418039003c88031b55244122091035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 545513597 1250 545512347 545512351
    0xc0f180402040b091023070218040305070c0807080a0215070f0b161103221d07140c120a09030f20010f080103110a09050702010504141207060b03280606050405 70
    0x41e0446d060300300b00b00088441d80141130080e0002e411100c0d403100080e00d201e40110207a130254045240810402d00700100c41d01190003400003103015100b0f440c80d0440503996046141c0e00240300390342c9491070144050395242034800701a0040d00040e0455500e00300480030b000107803034401040046000b0915268020003241d111860035000035407404043c0e001b4154960307048420005a001600310009294006807c1e20494001c414080f1040c0e041103400074010780c91400e013042c10350301c09000c01d0313001960115051840661805203203541e01a03100041f1601a11500000c2004250058403402e001c44903140f088450a4401041605c070380420054440c0d000d90b16020001030380f0100140002820081c6800c0c00c900082c000c0e001551321001200140c660459549005070740d07440801052100f5044a00000503407800500804c24414481000c0e0340302d5203001400480c7c03204121009601c0800540f0303d445d40c4480004890110040c14503842403400c1419140740d4100f9001142d40e28051203418 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 545514847 1250 545513597 545513627
    0xc030302060c0a050d090f02120f01060e040b0a050702032517030c0d02090f0406121104021c231014031c080a0b1504050a09050c0f180402040b0910 65
    0x2e420705c42805500f001038198000c00f1504850b912000d400141c981d80d0110750704c1c4d541a00540345010b90552034908603440f962040c254101b80c4000e203c0410300f80c00400c2d411042e40c05002c07625656100041c2d185100e45001d0404113002c3c600310700c0c5131150381c211403003582d4820402c98407404940e08204c0e00c8d500007580c1c040e40104081116144044080d8020701196501400140c4800d1600e0002002c941e8580c0c85880b0b0109212a02c8041080e00000942203100c1205d0450400700c40000b246146600300c02d8010f1541d42d00c140e070040150002c2281c501050b440c201c00c429500c1c002c50040305070380140c801c0400d01410740c3c0c44414030345404120b01008165180030266000601481194000d00c0039181c129810f640e07160420a81c0c5610030b20215005441c00c2c031680da00d19000a001d00703100c045d8402045985000b050250303c0014404803203070f41c0810381c103898a958150b1105c0c821040701c40410750388544000b40000b02150444d010700b4140008848206030421800801d41c3d405290703661030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 545516097 1250 545514847 545514857
    0x6081f1103071b260414120c01030e0c190f27020f070f050714030c0901140307080d08040606090b100513050603010b090a060f090905070e09040c030302060c0a 70
    0x210903d00120288201c80380a1340d1420940390050345210038216500300c0c401d4140d000000c0c240000c0e0a4200000c0f072105040e1461503034008480451070f210100d00b000d0504151316007001240d0050100030204074628005c10201038030001900d00c0291000c2031181204410341400c000275001c0100140201d14992045200501c482000c03031400203600c001c0840d80114030900c0305c080440c14680c00d20845070704c07620090001c01d003401250f481c40d2941c003080501ca60b00038802c40c001a114408074504584c800c00d90981d44075035150000c0e0070207100380c00034102d501c1200c5404030a254860300f039074013642c0034440c10861941c071030407000b050310800800c1c5a0410302c05184225098403950007062141c004100701c10845407610002141d940c420381c071409500c5e0000c40e4241840c9440d20500c001000c082c00c000c1d41407010b88001520b42c5131984201a1415910070018003080d014005800ba40b03680100b6540480c0303014903280e041b2140900003500140701d444001260b9160302021605500000c1d00c40b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 545517347 1250 545516097 545516117
    0x5040e010b090103110c07050a09060b0910110a03020615060a1d0105160f110f0a0b0703020c0d030549140c041a0405060d020d06081f110307 62
    0x11101e100d51041c608a41090b40d1500b0041e205480030010b0005036844c8009440c0c83e505d00401c001c802d0b000f03a04502045440c0c03100401848040c00e0450748142d17010f80c1c5000742d1822585040d2400c0c0c00300700c440300d494003906007450308056020484500c10032007801100d43c1c5d0743c0c081003440b025010311007580300895910308046035007d0f40520840203542c0140341941c030340005040719041644400101701d50b0800d0103011182005401001310340c2506007551191044140080041c004e28243d1042c01003074100003401070145031013802510300307241d00507090140315000351400800c941c0c0310301d41541202c0040d814102c81d4404c8816090005c081c480c03012004400501e007031461140324400c0d062092560f60032040c01c03a4264a500512450340008090788481c689001011a444200305030513951200300001d115940d94541921001c8030303031000050f1188030144005004001a8000f040e6902c119032030400c9034400582e10314104401a6014414149220b0500910340015a05440030414200c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 545518597 1250 545517347 545517359
    0x60c0518010c1506060f0e04140105090406060f030809090609310c081c020102031b030a0b12030c070501030911040e1612020901050f0f10050d110702040501050105040e01 75
    0x820b560615009924070302400c0041c1100c18112841603004001143c0010b80404065421103070040c01000192018060304600c2c0d511a00c2c3c040c0140500d61144001c0c0b00400c040c4405540040007030b0050701d0380101d205403a8203201205410810182e40300b041150001001400d28501d11801030b40341024280c04000c510116a030008121500030141c00c142c101d00001080264206000500e40c2c1005803850301d0b12016031400403c80100e401c0156070041041c4094034080f86101408507080d4030b01d05450ba100d1140d0a0040e00411028507840b002211003c806040d0110081011450b010100d0340010b81e5a80150140d0b00e0449000d4451060b0810352546400c180d0040d440c4e1010803002e403004030304081141006100243c21034500b170b828030300911045080c035015050140104480d0075462500d44400103030101400d0220318014051450713286006409401a035405801050042c4188040220945030380e402a0600340d11032802c04c400041c15500039411501030760103c07504140d203682058 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 545519847 1250 545518597 545518607
    0x14040201030b030c06031008060907030507060c140d02150114060d0902010e030f030a02060c0903030a30051009140a020c120d020307020709020a091a0d0509030304060c051801 77
    0x2c1509403d0b000e2030030b44d000303030f41d0700c940c02148111410f0f41c142600d54185a940d07443e006009040d038038140d204010034808240000b0b4201d080b43c0041c50503400f0500903207040b0882c06028280080d01d445803001509103141c003c14182502c0881d00880305c050f80c0c3c2c42c8e008500c49a1041c00c10342c1c002d5420401d24001851765080b9070101c500605044441036025070220f840d2041c01c2184100c15000406d0b450343c3c495052006540203004c40c1417035428000e24100003920391095000c81d00030b2006e2000340c9050820103001d200307512010710b15030b61901403400c80e090002c1d0504507420000f41055500210303026409100e8960401900528080e040d9904909030303000394000001842e05106109510001110000c02408800340d280e4003da1a401c126002924007403c81d004400e20f1740c014858100c040b42c1c400c002c0741c05c07680980302d0b403c3d101002c1b08088a00f44144600c15003810f003882d08214488030004000d60249214480401c800e580141048840d401680541da5010f02c130404107400325807041d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 545521097 1250 545519847 545519861
    0xf010b06070b1f0609150519260c042d03020108091009030c060b0301050628150323010b0306042703080109110306090f0c0f0f04090501091404020103 66
    0x1604040f1020402008054560b4481d8440e20020f4480b1030280088004822040c14840c92400c0103401c03c111040a26401d06c0c80000c4030040000c00c170600194000150075129680030766408406540c106481d425005d0b6005005440a184070030a108012407032002c0364500d8100d600740d55050107811503004462002c03020345030f05610310034040102100c00700c506c50352041901c43d49070140c0601c01c07444e01000745d401000003c1d00c00d901d4542001403940f43c4030300f180c82407820b81c400c0c040c4128024560810340010b035003106400364040c058900300305402da84800700d00c1014184448090740064841400201309004603528203070148003003800c17401e00e034001c20b1440010041c810000128103550303014208101c0c41c145c0000700d0820040026040d0b0740301d00448660703442241455032514038041154100c02402290117188040001220620340f04107540c940c13521031203080c3c0e4070071810001c41c801e078210303001d00041c4510b1b240000880c4610340c03244108104100349006984d5403160010b500034500303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 545522347 1250 545521097 545521111
    0x411060304150606020d0806030a050703060c0512010e01031b1a0a03020702101701050414060907021c030c1701050f010e0303131d07050705210403080a02030c0f010b06070b 76
    0x41c0e1009000000782c03e014a0002d030003d0b9005044101c01d845000f080c44074081c1c907150298102482c90004513a000c940382c0d0580b40c0011000c00c001c00e0b141c40c11903480c400d9007241c05807060402c1c00469080801ca103124100da029201505180100c1026000885071910a030314942e0700b041d42d5103e011001c003014141d03011041c100181800303440d03000300d240c40300d4502070000028043d00f14a51420364904080d409002c05580c10424075042d075518100000c805001c1611840d1000001000f8034420450a050400307450800807030075000e108058094501c8111003c00f1900200c03440c4541c6405002ea581201d400070910b60219080100549000c0d400031003c0750180030421015050420102e1000300908044600319084418034030b41e0440000007816900c100107040040c0808038070005901c010300d9100500c101d000c1648404a4111849980c1c0004c05050011601158098001c400b6100d03d51007207055951104581c0c2601d402c81d1405c182203a4411400e00c80400400c20301a60203502c034007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 545523597 1250 545522347 545522363
    0xc080d030b0d1e0804090902041104060203091201060803161103010b0a05040c030f020a050c0f010b060405090c0c0109060b0f01020c03030f0d020c1c120908030109050606070b1501170411060304 85
    0x1007203441d100030175400707500300078200f40d10784107a0000c60429200312080501c03030140f11801c250601034001e480341708243e0114441e54039042d0a4880c58029072100004102083c2229502d01c420034080700c18095410055845a1081035031001509041c00740c5415050000c1c8a02c00341c605020421004281120400082503503a000b14003034020148028504054280c4800b0380f2200c0c0c0c0449185803d0301401107074000c0c1d04110007078180b40c03101c030141c40942d042140c0b5000355545606c462102ca018443d41c0340c0d020360901410b00103010855019240d051010384a0500070f0041c0707001680e0310441c0f4030016070160f0080100380700d20000040501314000c0701d8030026192265500081c1d1038042c451100a045004140012101c25000351340000c6280854006100202d11915026080d000504c1901c01c4d891f2104006a00c035a82e4808458282e130340105415070030b00708060902404010f1a0300140415160b144048004540100e80c41c40380303a114a00324404074041e014040e0700d400150040390904 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 545524847 1250 545523597 545523653
    0x1020705060f1602070e01090e1501030b0411061204120306051503070215011508072604030909090503090409020d080423041b0324030c080d030b0d 65
    0x380c0c240715580c000e4803040040c8000742040c4000700e50089640452205650045504012400d042e0b84001e0440b000d0250008a560340740c0401c604100405c242400003004000002c0100700e0ae051a4a0260380107520001d40d03540c1d04414843c8038800e240c032400701444c030f5a00190005030300070300b02001c5c0403036031501041c20b80d941d0000c6041c1d844603501070310511b070001c01001402c560402102800c403051503207a41255142000412607402250b160350300300595000016000d90280701c2020303440380c1c07a0b00c5012002c0500041c514018005880440c0011124040021040b0b03090040200107038020011f503203032070031500810008240c94070b0121b03000552030030041d01140000b0007420040441d100c88101490702c1400749962000d5412a00f845545443e40d116003401103200c42c00075001442c280021050903042c3c0c0c109450385607607034904d9209a42c1c1c0000c0100503c0005040803111000300716103080e190580189d0589008054090300b0091122200f0041800b2408100c03049010100b01e80c101e03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 545526097 1250 545524847 545524853
    0x51206151c0602070b0601020105102c09030a030b010503060f061c0c02030a1707050a112104060219050a03051c06140906030106080d18170c1c0203030a11010207 71
    0x400c900e01075400a5020034034130b0610410002e060b43c80b00091000300714a00d003c08441c03a20000c0c074001c032902034000003c1401610344280000c15400d00703101c0d59150030300d040c04500e980c95102d00343c96000241031500101142d400b4406580c050303030000b0b20150444003a1410b1000c1600500d0b14400c88040d91252101044200c0c0b103001302502840c0c0c059035862140c824054215940c00c0b42c5490f511628408118242d58030406032442c00c0f01514003104801068581c00c1c2c07804680340c815403101c4041c10128031054812200400c200c07400b903001d4901c004041000c0016070f21244602a0081d005050648002031042c4020100700d00b08000d01c5101c0719284e60305404507469500640305200300501040c1403494000d0003030b039200074220b00a02c0341c4d40c10b200e804c5444045655500f0144807220040458820b035030f010343d03005002d045194280c201d00a00c011681e4082092020b4050b0181c0c02e03404440c9c041042900b40c8058002d0010340c40d002080e030f001c03100c40f001c4803518030041d5400c0c0454000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 545527347 1250 545526097 545526139
    0xe0103230a0b060904020d14010615030522030207031a04060609090218060a080f010c0f02031204080304060914010e10020a08010308070c031407080705120615 70
    0x18502400c0191140031440c1201200c2000604203100300340d02050300000090388840d50780398064002d944840c4107480d90303c042034116081c018000e001c2540c01c2d45c0300242e050158004000c440ba4a41a1880d031007a000003030b000c03518107440009080c107540c0c01085000c00c8190240a4551107803040720200ca0356501c48003141c04140c000607141c1410803044c8404c2c4101802010301404050800f002801d0f0198000742c441d4080e1604070f00940c002c100007410300d41d038011844004080900541d228501046221350081445082d0500410b82c0b40025540b15440001a207404000340360003c00c0c15103035610b480d04113030802001141c40d00d485040f0344000030620040d50b18000322070f000210f151030407c100c071404d1a42600020300444c4c410b020449078180d02c80c8005044a42001c1d90075654040c50501c0c4000580540024183c203080403c100b0700d60400044840c115030101e4103981e189500d5508120390b503a01c2d00441101c560060001c50074a08001000c05110980144510304203a008100e44407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 545528597 1250 545527347 545527349
    0x12020721020102040603060b0a05030a050601110a03031b0e030d2703080310142202160b0106021009030f11010b030601180b0405100e0c0903160305100c120906060e01 73
    0x50b5000704d0108010703605406194058000d82c5421401c191034008000c187e400020240900180c84002084003a40100004484114040b041c0c5612180b14203014001c0c00b1040407187c541c008203a4100059482107124005c468001406800c5450030f446080ba4008000c0c1103842092248260151011440c00c84170b40c0154820005a61a03181241040b8196542c5070302c807054560406600d0041566180703ca800c00c010340300351909001d10601b00e02402030081023000c04080c0350101c152401d000342c07a0740c440d04940d041d90880e111038903821040c1d416903816a400502003001c0a418090306d074010700100103030f20204000011b505090b880060b28012003a40302003001000d400300503c21117040c2c0268001501c081d50103202c1402c02541000d190b107803e1140000030b40120021030222943e0000f02c0343c0d0380382c0082c01c030346503000300c20506000907c0c50b02c0200d03510b100f180e0f011030743c020761401076030510007003521200c0e110480400802c000d040b210074222100d540c0c901003ca600704010060358 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 545529847 1250 545528597 545528663
    0x5120307150e07060f0f030504150905030d02041403060a0903020a060e1501060302091203040e0c0313060509150619050f01031e050402040b010908060c2a010f0b010f120207 76
    0x800fa9201d201c0002c0d208046c0200d110082504241c1040042047c80e0807640404526020010700d5412074100b0900707601070700c0044150b01e40009000507400b076100c8100c00c1101300c101c0980f4140e44030030b4064011903a610310000c0140c3c000d20702d00800300312198040f03458081b8040655102070501410762848950036080580840d601254401e814181044c40041700300c00040194606410001505002e10006103000001d42d80040007600c1d0030104548149c0c00f680c4103406010701e0610281c66a01e9001c03400b180c081d044085400211a480c10819071f101054181482c09a440d00781401d00402107524003070345050540399000000042c880c3c0d40c200440405103280040c81e810140704210a80c0ea072020450304103c400402800004008282d15421800c0d03640c00380e42c0c4200c2014150250707080d003c180010040740000b05c3e08041c82c190010685400d00e50801c11802460030019100c1c20b9026500c4000960704a0b0009100390040d0b00502056004900341c191012003a8502160002161000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 545531097 1250 545529847 545529857
    0x909050a0f0e0a05120a091703040513060302060d05070e0a030b0f0108061b16060501060302180306090a020103150e04030f094403041d0105120307150e0706 69
    0x44424244242e056669007040038121503422920b44650703070002285941d04010001a4100066005400f140010305c5145c00350140901402900c980700d4010b80700759400380c2002080c00e04004128070412080c0d03a0f00401050400220b454580000c14000b442c100034401b12111504803a510b01c000a00150302c104200345845c0360400105441d450181d0151456900490074850b14504410203144d40803181d0031301e2511100d0078030100c1c001030342820004c0d20062a100c008a00c1d00d0303044d0001c024088900c0400c00800725040d00b4141c1e2400101e682003065089a00200300561007a000700c01411800381058106a84400c000c00e0fa44d002a5801c8000c00c650f21030b803040a94200d400c94000304030b0600c00c61582c650010202d0b00d45d1007002c05001402030b14271b204902d80d02518049a1200d00c0faa01165104c0351150b003120b280d42c1c0015900d2080300780c920000100341c98801030b80301c0c9001e400009141048015591a0800d074441408072003017585448902e18150800c01c0448020140c3c0d40e24 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 545532347 1250 545531097 545531111
    0x9060f140d060e2a03031209031603110c030f030d020d1d030309060708090606060a170703060807140d031808060403020d09140102120a0905040203150114070f0f02010909050a 77
    0x30a40a0746425219001810429035055044c2e640100a032075510300048100c03000f0f40d94168500c2c2c15407250210094104211284081c10f0503801b0500c0c5118016480444d0303080040307403082507942c070740ca906500d1940d8070802000c0c90340328964001d4903007440b091001040d10018801501860b00916a0984c4ac0e030740017004011810ba020400b15030009202c2c1410200b40c2031030345420f038466000900342405814000b4081032542c0c0300711500082010800001103040c00c2c0a40b00801828040c4141c1482d4030880d0008204020384030004040100c0040c24031032074010566042e80c800c011680300c414148400840040d8800e0180f188a02c01c1d4402e41c0584854601403101a00d65003507074104404000e00280d501c4070690300007a0700801001c801b28820b448001d070a0341181c00e8103d0307404c0250002e00110502620908018040ca0030001c240c8615248802c02003014000340074400300039140a480c8000d40000c102c24000f0403800c98018940705820545a0324200c0903540c0a484503180190f840030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 545533597 1250 545532347 545532373
    0x1b020a06030b0d241d0a060c0e0d030903030f050c06130204020f0f221413060f030c091d120a020111030106081005060a050904020c07031208040c09060f140d060e 71
    0x4500641d20940b0f000b00c07134000d410341200b19501c031b0303031031800902007542c1d0407002a0b0030b401602d0300307848000d0003000310203e01d0691900810010540c40120302081c2d6284200e02058056015240000a000300034109a43c480c0c50544110140e103800741d8201740d003006030b98115420b0f171004cc4003100c1a1450259540f141e169060541c0f203c0c03042582300d0700042c00c828001071000550742c901c000d00c1191060240300d01e2428550003000c0586c84507011652140000040000841c422030882d000d0311400c104444148240c560f4078509400d0a07111504018060003e032254503010b8903010380d4510001074011001c10b02c0260542c0203030030007000300b14001c4c1004100100740c1011303030141005441c00340c241740040f0b1018000c2d001b0040640c0c40340c0d80125110603240c2007081000300070b6410071000c8014844814000d000310005840c03e072500c825a540c0480c2da03801e81d02403442105c00701d1116070103591402c00c92154070215110401da10028140603000864001e01034007202d1b146a0300a03110602e6528 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 545534847 1250 545533597 545533601
    0xa03050d0905030111030f04020a050307230603011a0c0703051b0f01020c01020c01031802041a0a0914160e0306190b0a050a0909170304080a1b020a06030b0d24 70
    0x10b403055209a04200c000050681c1e01c10030b8940100c0b55020707182d100d480380e20000b940710362203801450705442205400605c0c6a45000519500c20f0414540c4211407001c9007400300300d11090103114507030301c0403c00001d202210000240380a1008009441141d5103a58420b07040c0000341e000c1189590000103270059520f490b0340f410304001c80900081c1120300800d00040d4075503d0000d840d43c180765076100d40e0b1011070341c80c8950155041c0c0c018070400c10b11069203400640c2c07520a44085010b072444c01c4002c91480c10302d00c00c00840e480240790b2071032155241200c1050a8019412403010802c0b120b120a4590302d0800030790740926801e034a0f1042e0642121400c0c005c48200d6060b40f84036a043c20f004100a17101c9204040545100c00804100c42d007071410320b04901385039600d415001400004c1040705001200024101959040e0768030002a11169038010341142c80c504040c2d8003110001003007000038021750100180a0001e4550324848c8030648985840c07400f000f5003070f140b0105441e2100215032170b40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 545536097 1250 545534847 545534849
    0xe010806030a03170c09181b040e0c070c0e100306050c09090a0c020304031e230d1808030c01050405120a0909020901090306050a020c0d080c0a18050a03050d09 70
    0x65005140c90006074034001c00b034020307100062011114903000308200c1c010050480f1803c3c6d20207001481e44c403170304100c4485280070446a00408410b6403a0003403281005000300c5003101c00c080f0851107907494088001e1403c0d4414003040ba0079250b600c00c0000c442c226218113900c1140300290030800c8615500380300090760401400e800300040d0400c0f41f60075595441404c41c0c2c101e007110a0000717005004a20a03440c6101d10b400284c09050203032025001c0500180441010038443c1e6013210101000c4250361004800c602c584181a401c11050b51302e0b02c900c18080b44e00402c0c03803401103408240c4d4039500c4a00310340c000d4014265694540c020401070040403c201c0601c507800fa03810718070741f02c40d080000703001d20764a000b80701c01d107900001c0c0e084250b0302c22a070220182d904854204040c7c01c100b99140025031010f800481c55008501c1020142d40c020032041d4411500e40707104034a098500201191410a5800f03500c111402c00c5c0d001040a0701d860390460f0180d4440c3c00148051544844041c001c0b80c03c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 545537347 1250 545536097 545536099
    0x61d15030303090d0e1311180402040609030b0a090b0712140907030b1e0a0c0201050f010501050414040f0504030801052b0308070c050f06011d010f120813060e010806 73
    0x20810a00c5000400026002e5a24004d031070516503102031100003070344240b45c2800c03c0315001d040a4040807583ea0303c00c002c103924070300080800e8142c66403005020a0b4042c2e072003400007088020000300003141d40324802c1a409140f40000152410003903580780d48030001920740344002401440030031140c1d0024443d14000c186111303640600343c5006c500303d50740d5442c240030042c00301650034003085a028030b4401c4416007614a582045561030528038000041040395100c400560909020483c0e8648000040307043c2c68069469914047c1401e040c5103c4501c070b1813509030000d40d56210040140702078403a01c0c2c01107119944080341035151004126a035148107580e01d2880310140310440c05203100010f0501007590500301300c005a990b1010580d9087e802c4030010344107014114404404900c0410b860f8180c81400030503240d0032110143d80c0300d0340c1c4c400b4081c110006030200c50038041003e00c0e105422030148520350071460009880c1c0003a82c19074460340424003198081541c0a09580c0040c0340c0e641c0008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 545538597 1250 545537347 545537353
    0x61c0908090a0807260f0d050a0f080f0c18031e010c080f460c1b1419060218060304320d02030c010e0c090a0f061d1503 53
    0x41003481d12410b41c00031030301c240300d845c11840307580c0c0c0100c60510030341901200d41c1003a6500d96414110180c03d590280c0591400103019040c241e145500910740b99010700040d10320740d841c0350b85950f001e4296510a5034a000c40900c501c2c1d07000032a41c0e040000c880154040302c840f10320707640310010050075a041c60301ca000034170056008106500418a001c1d65000380c1c0707801c802e104045801880c13422000c5000440003c0d10300444400549001d01c4444541c00140c1c0c03504211908017008106d1310280d0758200080202c031840384030404900c4076007803040c41107070110076503008858030740000380d0100c51020111403d5401080c004120154407054a004207001d4511500d9884c00f5500ca00c20003070f12500640c3c05140304400c540201380442e5000000841420890b541d010814002035900d0700041e0318900291b085c03032800148450040b420f0100c0060140c119205030b143c0e10002d8026218018904d0f00a640d01c0000295107400042e503544441012886640c11742441640f40721503507031035840603020354 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 545539847 1250 545538597 545538599
    0x807050301090f080f0409020d05040528080309030412050703050606030118240e0f0f0c01050a05031306090602120a060302130c020c1206090d030603050606061c0908090a0807 77
    0x6802500d420403600d9022058964514843c0f00c00017a9024507003281e000341d071000c28101000003540e800709000b5400707001102ea08142141c032041143d88441400c0113500e4603400320500007001c500c051500110780c242500d00b003949500c1c0c0a0390300c035171300d070010381385a030005808000f405001c1c030800d600104140c0091284401080c514004a000000e0062070542408602d50040c026040340c401004216081480b4039509542c0007985e5401c0c1c16200070950081c0d88230349545880006e815040110180c440c1c0e0b00300805a40c00b51880e800007040d0314000b180c030f2406503000070b003907115003000684540310041c1c13140300107500b5083d900d800a028503003c80ca8500107101684d150380c07074040f150440300d8000c900541011800ca00b0031319031208440e0840c0080000e5610010041145489140010115100161900b200703e0035504248805060307504030401003141c07030400700000d100c1d40c0b145400c003808000500d65503004403003154806035621440450415400d18000031700d1001001c88800600e03580d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 545541097 1250 545539847 545539853
    0xf02181f0501020a11040e100b0f01020307050c0402073816201608070501140f04060c03170f100603060311040209180403080106081806060d0201050d0213080705030109 74
    0xc04d0392040181183c80d103a8030b40300c000c1d81d41750003107024041d145064580a800800f1881c000e8604007407010700c2984401181d2000f544000f007039403c566080001000503c82d66003d200007540688400d5850042d52102c40e02d10f80c0f121500c0a420300360055482c400c840ca0580305117080c642c0034000646103c41201c1d00400c2d80d0b44000a00006004a01400f01c078041e40064a8070b0856420302105820540d07110000b12050040380841c100e0300e080e01c50100b01c05c15901c1c44101c40c8186420380000c00400c2c0010702c2000c2c41140203844203071013410200c048160004909a0380c190443d10702c1d01c0c5213003440800c000c40e038500c00d00070010085421305201440c00d5030786004541d51400310090041d640481c180b425659501002c16041620200390100e608150600401c030040c24090780b0081030a640c0031070001c039075101504a442064a02404254441c40c0821201c0381d20004160304000c1c051240c42e006094a2008144600d00d441c01c07020b2192401d07005a0500b01c85600246c40380c0d142007210408 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 545542347 1250 545541097 545541103
    0x42d020f041109030a050309120c01050301030f1e080307030b030708150c190c060c090f0b03191505090a060b0909130c15030f0509190f02181f050102 66
    0x110309011100400d80c0510340000800b01e018070109150705214198000041c410044018990580c00b612440172407007000c2d03a056a51506055042e0010310308000400c040340a020800243d1482003406400c401c202d1042d0a00c150214032080e0b50b142c0c0e0000c248428281c041c0b207160340c111000e4014000681c50300d51801e8031420040d450310031180341500080c225030000b0084032460701012100c801c15801c40d400040c0415034580080300c3d52482c200b141c60101c2d0144540808030345686c0e040514040c04c1c03003c0810346400103018116428108185038000d15130b01e000e0461030002c072105458600d842d06d070420009000180410a1181c030380300e028003e03010040c040341c02c40ca80c20303240f4216640715041070400f58401d41a020b00440c1c1c03102c402044102e0042c052240b400c0d265136041c08450041c00e100800c07644c05480400d1240e0249405240b2151142c81c1c003001103014400b803026808550300419003800c0700e8010000308043c00030420842c1c0c0c0d204001810125031102104030098104000030b99 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 545543597 1250 545542347 545542369
    0x9070c030f05070f020a03030f02060f060d03050c031606020c0106210b060607050616030e030a09061809020403120810030c050f0619032906071415042d02 68
    0xb0841c002490406000306002030380800c42e0f02030b105405055480c01d00a0061a08501400c0140a1000890b56008001034418000c03540100320003040030150380d003602c00b03922100186509010601100343c500080405551950340122800345c1e0b100c46003245c00d401c641060b0481c038001000c3c14003074000320406e443e00c0341c501c9602488441050310380200144030740c05081c1006005200d403a0810011094a810140281c82d154a05011400641c0082501c0340580c2e103220000810350042041481e11510001101d2030003500003803c5039031a00101c005980c05900281e0307180560840c1d1003a982e0780a2002a8070a100c03c000c6c4008900319911a607001c1c40360303c074080c840d84c14020344107099030724001201c60b1b004c005841c12100030348400000c0c01800003940f40003094a1400d844188000036270144007600b41c0002c080b240381080325942c074402c01701d07040c10103e0240b00c0c490782d415150100e80c10641c0582c1c002c13103505d54405442982001021020b803841d40729641710700c066200603250204130807 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 545544847 1250 545543597 545543627
    0x1d2e0302180f04091202030a080105010504030b31141506130504030e060a020f120301260304082a10050d02160203011e0f05070c030f0302040504060b040509070c03 72
    0x18481e0812000140502000c0078045c282090340c000b0401070b00c1d00080104562243c0d600d803c0303442e070399501c01960103014510003c3c0031490b4040000d84005c0f040c1d40c0c1510000100c0f5250107145081c00c800c00b1a812001d00c04030380a000c1e507003600400e90002c120408040520804168403450000040b03290b0340550307001d401808ce11070001c40c0c00c25000e140e42d0f80795400c000d08105e85a009040c2c009580d02c000c506042558020569000409094041103d050701d0f6800006442d0680740c1070042240c0c4c0d0030100d00e4086000c1880080340d401014400101410000700742542d0078030308480c0480320384c000c860820f442410f180700da51044c19080b030107844c220204404016280c00700f0907680070450391800300003503142d444c1c840054520703507a807406403003039000c5040100001d5004a5101c41240d6058903803501180e031800082d00000d103d0000c2200145661401506196591010074142e81c51900806414800890140300ca801c05400361548484180b800c160106615200138001c0d1a2015801c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 545546097 1250 545544847 545544859
    0x100303080f0903041a070614040614090325080a0905010f0e09060d14070b1b06060f100c0b07080601170403080f090f0304080a02030118121d2e030218 66
    0x800010000030300760350301c01c7d802c034805115059042c41050706680048500700c40231031814612614102040380c84500c80d541002c0254a81103a22010100b84460b0b0005030407401412000e0100003132030080601200c100702d4445d1800c01d030900c4009084800c00c4003c002c00c1040c191b0404d681c5a49103401d8503000725064903c0d20001300e0f10b040c1100061160b40d081451032140301c400141c02074080d0001d1400418040c010940c0c80c102038090381c0c03160810b443c06075102d1500250203c0038901040c01c42001c03105410b1446810045a841104000003200d10501142c5603c08000752560402c402c038556116080c522071140c502690003801800026041c20940c1581a00141c00030504004c010b00840403201182e0700e035984c440d0740340d9640d14500800c034042d509041c100f402c40c0703045820110003181d009071003c14174002c01c442182c1e038034045034002c940c1407030790942034442e92200c0425a40348001102081042c0355055255040001c41d400c884040510401c40c41204881811221050314411105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 545547347 1250 545546097 545546129
    0x170a030612030c0302010b012105071106010627030b18070b18040e01061a0a051207081e0606041205030928080c09060105030a060e100303080f090304 66
    0x12002488650001e40601140211400a02d40c0018854181c03501c0707a40203004804042004580c41c1070101a80d03064000ba600d5600c1c4030081d16001503070300400c1440c249102c1c090030480d4610300642a80b051010680300406000c04001d02c49070582e18006509018015515555070500100c10090080d80403a00351000981700c031506102880c01000950400d60302d800002110b01d95813021489814452460131820350294807040c00303440300705c0d45c4000d811060f1861141d0504140d901100c10341c800c0040c05c0003090100e694004509020f070520369203801c280e20302142d200c000120303504c150b6040c50044100f003050300d98802080700e040d14005080c0040b400340c186403044c03450091441007640400d1601c08850b03c94510b40700500e506000526408003d9514001c058139170741060340c8142c03c120400c00203441540128002c0d42c01000100300020a1070343e034030504090300000d903400e5042c0302c1421820400c2c50b512094058005c4c002d4070100203941000d1041d10798034403c034881c2c038144100c1c10030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 545548597 1250 545547347 545547367
    0x4060c02070512071e060f05071401110d05070306081b0303040b030c0a02120c19022e0e180a0504031832090406022d032217 55
    0x100081c01803030050b002c02e5031003403c03200f41504c0c0caa01c2c1c018a400e90f43d052014400a02940342d07070108940b810b4540c1c0301168542d0f030f0100c0311030f030103480180c5840d03140c16002c0714050300901c40c0c80c1c0c0010300c031041035071209091501d80059a2015090360205402d2560070701c01101e001c6a6035001c0340a103641080808078250100e030450185610000c24681c000c0104640703080e40c18021300d89298540d0070745040d004003c102460900076804c0c00d07425640514140034060b40c00741410314840340002d16444050f080315242e44420100c10412080810175442001180c542064883c8040c140481e000a20344c003100000c521025001000301c1c0c00d603034450000c078043c1070040d400286640080803401d20200e481c0c0d0101d02c0445d440207440e00070384103086c0703a002c22404241160761608000401c44a0030381c4a54541501035080300300d40051102c1904107240542c01c4040c0c50380081c80d40c3d040d42070340300c1c904540716034204100718504001d88140c0d09500800140c400a0320208aa02c1400c015102e241f040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 545549847 1250 545548597 545548603
    0xb010b090906040518100e0708121608041814101a0a090e011403070b03091e010b030a0f050c03012a09120302100e0c150706091b090b0607020904060c02 67
    0x1540041c01d1b02407149440050005a0800c4250103c0441103850b040d64944080d075442100100421102005104020513004819400c0d54050b000d41c0c10340341882d4803030480300030743d10300e2146002c1115a10b00c00622964138000441d58058811014604040d140180655a100021888071391980000410306a054090103d03000a800f480f500f00c201981c4400c0b06446030314003110320a10074854650002010f803a81412680324807036400251004101d6180044460b10111150594554807051001201d441c1002600540350194541100c00b03d800c2c18410b0070840c0d4003e515010764180126500c0740015a00c00190034100c8840342840c0d400d49090032a80c00031150080014210142c0600c4185940010000e80a580520003000011001203600b96140c0c2048121a04140b4418000c4110681c1801070450302e0300402c07011408a1942daa140a1031513a04d02019049900050a01c0044014441c59480d40c070151413240c50071100b41c00051049400800050006031100d10b0a01410f1081c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 545551097 1250 545549847 545549881
    0x1e0609040b1503010f0806091c0503040c081f0b0d030206070c06090b01030602071b0312050a030e070b040e07020303040c030209150907090812040302060a141909030b010b0909060405 80
    0x51411039140d5844000074010204c15103c3c20740c1b28840c12010501e10080454506818410f025031a400c1c4800a0000e5505420080090360545000d0800003030060040c02049603590305082e140385c0c0504506401030456600c078441c00e001c5c545203000440080d40005d000c40d00321080303041003850550545009406401e801e0801040e02000a00000400032560007030003403280301e640110306118800a500c0118a00c40c80003a108112140a64070403500580082c2001031882c0350200f48640e02901c22841c1c2241940000c040c0e600001d01001201c101c810407942045941c405940f0b941041c0c3c82d4000091858003001e4030924824000c210701c2c3c2520700a82622420181c45448240343c000f03405015041c9030300c9810305a00884110b4004915840121000c0c1c9500424140c10f00d00b0090040300e2244089180c1294804c08100483c80d460824004042000c0030399940038600d400c5241c00b66060106900c0480d5841041c0280d610690b21134461991080d41520001090340c0c0e0402c1c600f54803589 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 545552347 1250 545551097 545551129
    0x1c030e01170114011b1703190c140901180f0f0608010807090f0f23070309051509011e05010833090313030602040e06100815150d0b1e0609040b 63
    0x106c90700c1101e446904400b56103d50300d00d090f081b400a1501150030b083c1e5000861250001e45400d0080c0301c4120424044c10300b1001c185800341e03030b100c609003888080341e00d16004450a003100c0041004803c02c40c1e00400e01400140c54480c0c525490040c10320354405041c0108151151140190580e030791150b40441e1f200d4109000502c0300320000450b0300b07200a00230b034500520385883c00000344424064080c9992a55110000303040a04d00c6e90385040e40d135480031301500150b540700d44500c244000c3e51011900d1441d10508001041e51400070303041e14003109080c1800460100c0501c55420550080000013030301030035010404560381c1d16202505511440349075861004d08a01f001c018082c01d5030191060f180e50f01c9a00c40d01d40c41d07003c104900c088070070002c1400121500300181c4000500d8481140c9100007a20100182040f030048200903000415080c004075070341c0c1e012041c40d141c42c10141d18031407500c08918099510140100d1903d10500c07148074000c3d07803140c80191150300c4100d504182810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 545553597 1250 545552347 545552363
    0x3031a0a050315062d010e0f10080a140403080f0603060c09060703090e0a06050a142d03010207210e0108070f11010e0105040308010b030c0412021c030e01170114011b 73
    0x9000204403032070001740200103000800d8180300b088582880ca1a4111a501c0204052410148640200c4810b58000c0605c484641c079110301480c16000064503134022482500d810140d80313000c8014442c1060020400c070720941c414420310000051003001c07540884003d030344855488460781802e540700102640700000c903001082c1044400022075000704d068500403640303402055552028012580364404901d035020004100c2c20305046200602c1b140009100c009221101e0000b10009003283c201d07038000d80c0c2000801c96a0b081c43c00aa048040d140c2c00682132090038000140002403495100509a0081c020450030058815004035103080540c01c4407002884040d005010480c003825041c2c8040300450403040000c10650505410303203102e01c0741024018200707490100c12401c00400d090080c5d81018400001031030029070380d5003600d4814003e450342d04002e030014000522070034030303140d0b003801c60890000144020514005040f81c546004d18042410f244043e0303001c01301681c0e17400700400c009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 545554847 1250 545553597 545553649
    0x3150a08060105010f020309030709090f1712070305041208100b0c03070c050d150504060b0d0f20010503010e18070617010501090e0f2203031a0a05031506 68
    0x200c00040c00a043e41c0b400e0761401c00c020455801a41d0703d008408031564183c006542c1401102c0c8150710595a0900568860851021640b00c0010303649005404180d41e00380003542801a0f00072a00040c0c02c825140b5040100d86010380b140c0c0d040042e145407032010059140c022410080704c1800c080c02034044090203543c1c0f4945110400e40d00d6004480071560349010400c0000c41d8545400692140e54204845003011050000803500404000b40201c3c1e03ca07a54580a910360348a8121440440d80300c0d1010300f48102c0542005241060200d4100815042d2200c102c9080e03640a0140ea0440720404143c04203070700c88002102d50042001a904036234170882c80c000400c2a40030300c0d03079030a8444009804205913224801114515414010090306481050100d10390315006c005543c1c0c8002004584420080d1120a0444410300a04150002038a9519062448500240517150342000315a440645460b000c04607071201802d04000210311107070310005585c1e4454108951031085500318604030030b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 545556097 1250 545554847 545554859
    0xb0d0902132a02010501030c09050901063507061215032f0303030c030115020708030f0d060b0c06040311030c0613110d1113090206040906030b1f0b03150a 68
    0xd2241075848503902d004040c00310714040e00601c41c49050329000300101ca8454188160200035180240c0350f8206036507241d00c0000c008e0440d10804c41406110b014803404040d01020740540001013a0042070079800090007000980c5c3c10001900c40761144400110740303010345160320026145541d0000d4400c500051101601c01100c501590700f03007032083c88030700030052100241071762070100303c42034240d030902080140900c540f07090710140c801743d0f41c0c4101c8560315250780c200d50654000500301c6561250108621808402500861025003101d0219506042c80c212025980d200064005400d01c01280f1411051080a204451003001d1910484106007884046940044c0d040207095910004141e281042440c0c020b01e640105600107928985214580c8100032820403684c00e050401e5a85900c00700050311074070f014000401c034030040000d4843c81c508220200d001c004200e03445102071107000100c820b180101d110f05880c03078100815180d81c2d13124429100955042040d50788540320785800584e0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 545557347 1250 545556097 545556131
    0xe19030605180105010303080f220305030109061e0308090105250209090c090103030e0102071d0906010609030302030403150b0d14010e1603080a03061d1608010b0d090213 75
    0x5081c20001c071403002c80c09044480c01c0310380038000100000c4060b40824901512003040c55000364140301c8201011031988035070075a20482d070a00310086000400100f010600a10403a4020800c01c43c54440006200c0071859440c1c146000c010030180c1c000c031314082141d10940945000a4218004901000050203c02d1020000c034204074031609820000401485001c1885400240c02902480e0b40343d0071039809455062014040d14114420740c00c0c00030301c0100074034542c031107200c1d480110000d0342854902241071540c1600008180710b40500e00f000007a80c00800c171070880c0d4108521050030b540004001001c0d210440f0020341c0003c050000205214005009190900040c0c0082200c480304990031605c0720b910070725003030400300321079000c0000c100c1030401060892030f1842c00180882c0c8039030129507a4440c0d00c1c100c030701c0a403610080151800400e4102005808641011005507140420309101e0340b0850301c03508c00281e100c0700e10302d0454440e504a015030f41c0d03280c102405540c03181410851 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 545558597 1250 545557347 545557351
    0x16030f0506010902160f05010209030d0c0b060105190e03010b060403150609050108071701020c1c0e0d1101050c1608010c0806040b0a050d0804051f080a0c0503070e19030605 76
    0xe960081000003d07081c081c501c03c50b40c040640c004852009442502c44005c900c404603010340d1155000c000c080c20503582800700c944000040c0d110b02c13182603413905101c040f120005202c2810302c84204420b8050f54140e031803540a607400b901e8482402c0c80740002203405010700502e0250081d9003c1400700820610001c40300201308040340401015549150781020b40d0001c3c07040c2c6456401100d0240920084103200304040e281d602d00243c0741c10546400340b880d0800c01183c002041c2045034107484040da01c07016006141d1011a2001800315154031110100f1900600b042d041c0140040c0c155542c56061240d60448690369404c40c82d01a0b440655501030801c0b2296500040c2d00203001462a14041c81345e2041000080c10100d010717803d200030701020303810a040c01c0e02d031260300703000000d8190380c0c11000d02c01407035050120341c00840305440046c042c1c0c0c2001e400f0703034145401c00c00c2004403958000150b80c2d02074402d14007004502c071b41c074002c503216a81200d4440200ca152010100a01030613400c094 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 545559847 1250 545558597 545558603
    0x90c1303240f0b011b02060f04090606021b031e0c04090b09010e0a12030b01050c060a0204030209060111061f0b040e04050f030c03031308040e13020a0504200c16030f 73
    0x80300340b2506240341d1080380c04202c0c03800c1c01324000300c115401a078500c4020701e400c541b003d002c4034900501c8800800840d000340c3d118400164503900203019440d41840040c428507000d00104280008510000e62114054884282ca1214854410840810800c0700e0703c003c0c0006042003141350118100100402022100d42c1542e600308131021000a5000900c141c143d40c0100c90381c1c81400d8007000032400f51002c0005981082020b003c11140808244800b40c041c451003113005075120300d1481445100d440040c000c80c18400c038298031034040f44001c102507502c0075041041c101e84844144c0394404045503908101454007001c0f601103418943c2070100c0340280c0c007403011101c081d554440d03119500d11500c184500c00b0780046c03002c41d80481d140c1c580303070405900c906901810551180305100382e0300720469220f000483e111406a0940c2010b1400304040d1100b501c1c01e00c9100da02010307000c03c4001c00120061145800148515213981c10301c605028400c490700355100040d564103003402800c0c4000000d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 545561097 1250 545559847 545559851
    0x2090d111f021209010203041d01060f0305010e07120f06030311071728060e06040c150f050c010f0504050f06150a0501030b150a12050906010302090c130324 69
    0x3540791000000c000180300c0c4140e0300401e924a14040d02c5600c0c1d402815505055220a02c40491007003c0100b80701d03940c80201110440541c50000020f000c2c0300c0c8450315000341850007005002c3d40e0a000b03500f036030080396410300580d140c44000e251001400c1d207960018007030745820740c04030070103600c0b20704a103901c023458084500d5035484a03083c10b54840c3d49920540b143d0b2000000e40d9182500403506000030354066020780010780303142c80f04415100800790f8003060390840c0c1c0c2008100002c103030008016044500a0701a03a001450014104c1c48050102000340000407802e440c04140c01d4000c071000307280700c000c1480141464680319070748891981e0400c1140c00341c1400601c8814608410b002074110060100d0300c00c916040065000b045100341140c0c2061000507a04d0018004000605110740c8541ea2020481c00a6001500b203500c0900a030280d50401c5004002607076514a2894100030281610f80d510400f04d0210002034189500040070484c000214238060701040703845000940f04c442d01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 545562347 1250 545561097 545561119
    0x70204090c091b2006062e0e190803030112021908061608060108010315140f09010b0406050d171c020d0605010c020306040303020328020702010216060c0807030302090d11 75
    0xe0449030108405540c1d296440500003030003d18100e11950181c0c5030303802902d00000301c0c0418a0103140300c0c00540c40c0104030608e540760842d080162400405141074580a904141010b81c400c2d2070348818822440340441421042d81076585440381403002210304c602819180b60784905460300c5483c220381c0703030008585070b00086c117020307000b58840c920a2344c050b501c550451782540e4404000405005c00602c09503079a082107280388042010060140711441100d89103890b02c508803034291510f15911501940c1404020007150f22060b6420242c140d100e0b07941f1740e4040e50107620b5816400342e40030f44110039010050f0012400c0e02640104400301c3c2842c0c0038056607446400542c1d032207185590013505540130b07200040119120364043d5400103621405498000b0b50400741e00952051041c0c21844070b9800185101103607010013130500c4510325200d200038103a150040c0175207507248040b00544506c01c0001c580081609c203504649000d1802403d13200c40050504246004070b00c0450054007500825030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 545563597 1250 545562347 545562377
    0xc1209141203041223030f18030a1b060209100903031b050c01030915060e09010501090b0618030705061218210705150712051605070204090c091b 64
    0x4100c0740300b540c001c02c0140e80361054000458229401c882807030880200041100e100e0003401c8019030040d14203a50b5130a840c1008c06c0b010100b0091008100701a40c02080b03540c52050308803440c05080e1a503c2051036000645090000c003a224501215500c401c40c00840c1c000076402c00341a000f500c3c083c0d85c43d60504021a105c0840c0e00580c40c201610541c05100102003641c030a80006006600c40d206c2007032150343c0c2007580c90030345c0e1303450700003e519078018820000445004d210f158014054070382d090050640301d03004100706100b5a1070303600220083c0c452603603043e10104040c0000380703130203000560758044200b00190070110a6404e0503580c41d9140002e1001d82d0005480040f4140e01148112030740800c84c0c21904540c010202200c0a014941c188040c4641d1500d0161140017036403a4590064050007482c4116140148900c3c0b44010b40005000304035405410b803100680e06a0300010b0148032410000700850580c0d1022404505146160841c501c0a0a003501003c10646039040036500980c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 545564847 1250 545563597 545563633
    0xb010f02101a031606140a080402040f061e0608060303120c03250e01200304060540060f05190516030207050a09140a020306010c060f050f0105010513090c120914 71
    0x1f0b0722030015a02a010030003502e000e5105191403400b10800150700d0340d0300e4118503816044211340320b202da9038000c0d04000681d004900c013980500110069840d2010201900108410182c204084100d000c0005001c10158621039440c294900714129403100500000514299100329010b0002c2c1a054001d0b07400700000e150072800c600714030007840c03d040c00d00c503044401e90491405417540c000701e0701e0840301305141500812a8501a03842c041c0304d85500c4c01c49840301d080c1e558056010401c65802c5004425480002e9075581018881454541d01041000321001e01680c25101803d8810400607410150001004812100c09440c500300c81a5140600c00883d0310f042e5803070400c1001100000d00c500300c5503004540c0507605046c40706200c1035540700d00c4d04541540f2100f407622a601c005001160042c4410301d80181000d10703005140000074421003201000a1040c0d0600c0c907260b80000c0e101c907006500e00404402c0074041040441e42c5400d0071440302101e400700c000316001d014640b9512510300c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 545566097 1250 545564847 545564857
    0x112080d0213210506011406070618021512060105070303060e07120f02090607080d020c0303311e24090b0c0a050703120b0402040b07060b010f02101a03160614 70
    0x401410941e847c2c43e0070101140d048804650f40818204078420005820780b11365a060b501c01c65103210503c00501c1849611105084561541c0d0b00c20300c101c4038980032000425502003002e180c201d458005524040d0054040c0f0342054480000c043d04020102d5400311002643c200c0c0c6400078001120082103000480c401c0100480d0040002c00034040400c0400c00107200a11008400510341519030309011300310740050369030b02d2500100300007894035610003100d840c0c40f40d09501041d486022195032041e420185607a00400e5540d003075100350342841b10116800200030040f00c0411a12034102c40124014260480211106107400c00840d44030150401a01e107103040035210745260031602c0d00c050361f03220103c481281409445140300d00031038550b8005000208070428480b030302e58246103850001c0c1e031080d00442e41000b800031507802509034001242580c0040c804800550101d0740102c00324100e1010740040e0705445010b0011512401e1000380c041103072030300d6a0301041c4504021500b10b07640702e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 545567347 1250 545566097 545566103
    0x51506040f03140319121a0604121110030906060f050a030b0c0d060b0c010b0d0b011a04050907050705060705190522090507090f0b030112080d021321 66
    0x1c004240700190701d0744480c610340d8803800c0032641054416600042d09866140800000881c844141e8030303101014000c2c1c0b00c002c00700c011002c2503d40004040782d0a8000c0303105406140440d1440b907400e0003070481c1c20303840740c1202a20220b040d820744034000d00900707860081107440740c0c5095000a00110048441000c0c0c503802804420014515200d558440c4070180c40040700c0300c010072104800040ca80308000042543d00c2c00251a8000201014219100180c1c0c03180510014261313080003500c400174030382c15070701590070609085042c43c500707071858006e0b5040316802800950500c540c098201c4d010700119407141c02250361513501d401040b203090003000c070040500c00c1d107245411001c2d8090400707010000482d242c00004005c04000f810203007a000d501051a02d0303544c4042c46105036000c6903842c046c0c00b04846400059260038944841444148105640300308030302c10500c20400c510707088480f0b0041140c025500c46040400c51804589240320b08540d0320382c016034108100703210481c1c2e104e2240d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 545568597 1250 545567347 545567369
    0x1e01080703060b0102150f011805060d0311011e020405030c01140702060703171305190c0504090f14010203092b0320130f050d021509060f070605150604 67
    0x40785a4a420140c008a0161410740c010400c1500280c015694218450955084411080e5141c424181c801450004089074000d04020401449407145004110010343c149030103a000b90142c440140140080c00040661842c0c10407246940c080c0c54020380b0580d07004030241c401b01040071005644043c1402a00078501c0d509200210151030140302901210307020f4107284d02c090125200070800d00c5800c03a203500104880a40150502104001002e00540d09179510200301c003094440000501d82c0b071141d0391140d512050810200000b40704450704035030384019004c1e44402c50840590203074004548442c000e11a001c050000012030030b061002c1c007147d041507414030601740001103018004810400c0a4030701100380c1480e9545c3c01d500104014130030300f40301d06280383c2446107031414842682d00031403044a241e90703043c0242e0341e01c00c0a0b0340207a031051496651002e420000c035466000f061190861036002180f83c60030712400380c001d0740c440d600e210103c4852400b0403040090a0042e8003c1a40001c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 545569847 1250 545568597 545568599
    0x9020406081326120702011806050a27120c020d110a0e0a0605120601080303010e1506070b0f0f1510030b060a030c170103080d09060f060e1e010807 65
    0x5006a04034501d6900070080d20b0f0344844030001850820f000d2482614031201c0c001215481114803418142d00a80944000c3c000c45103055500c00e0000c0f1304450280115950f08042548078126900c1918846c42803401c43c41c3e00c00055404d003103094105c0c0c6042c2d55a01c00ca8403090701c80b0340301e401c00140c442d0380101a1880000e0304e40303480c0580719003090380540042d0b1042e0040703600449940c1041c402d48001c070303001c1a00d070b0070141444102000a400c0100720741c8400014400d60101001b030340e041d00d039a02c81c64001030f9241c1e904941500010b0030385d0b58008100041c5401400415251030748334420015152036261141110300750803030000c54821686c19811918903a062070320191038189403c15240124101881c1400038040e54030000107000413913500c0b82e2110449420084070400c0213498010190ba66140d512840303401d1045200004000307968054041c20441140d12000d451f0b040c1e030340d00b08910380d00c920928550b90003c1d0341c00760403a41190200c26900a450541905032600751001d80201 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 545571097 1250 545569847 545569861
    0x6080f092806180b01050310090f020d0302070b0301030c1a09011403060d020901080a02030106150507020f062802100204030c300804140603070c0f06020c070806040c0902040608 78
    0x581ea4402003152203d4503401025411200641c20303204440c00342c2e00c50081545088100740c90128a02c50041d200b6003000005804900e0003801c0075a5503405944080000d0450300e000c904000c0c2581024600030790210010040c055070802074020f946001c00c9401d03402230051503003203603030080603801400a07811908610056150002558119101901d03260a00d0f003603030300045500318241c001102c15800701c882081585000d008090080110f01e85440079124103040c01003a1b403140110103800354079103040815450b100c00c070440308035040a41e48030520010750f07001f4600460304c688102006108140201c200074041c1e20881e0200c036845140b00c0503035031a242c68807142c545a0603150b0800d52a0760020144415039501e1000c550b441a10300980c3c49040089515004000e465940e0290b542802007001c501e800230894900c003900080c54522020241c640100a4801e0855000540c02040c07000500004000360701d0b400389101d042c041c84810b483d90a41d50481c060ba00c141000219420701042071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 545572347 1250 545571097 545571163
    0x11b020d030908100905070509071e1202071407050a050625021005030915010f0b0714100e06130c12170708120a090803010504020d021306080f09 64
    0x18592003402c1c2100035a81d981030301c43c1006030450240c080640c440200f002041030500507817000e410121031a4065003003001c8010b01910300004051600c0714021110402d46000340c04a885850100e0380955842e210762400503000c06a409080d201403040340004503291618104a030240d510141807581010001380141414414202a4a11915030702c4405801343c4c0b03880c1c0464181032200d80741e05030389040444089290440200c1030900d60f8107220018086d01c0c0d04c800080003112825201152a440d040c140343c0c0d003030700c000b40c0508131134824001c8140c240c0701150044804004050169a06907841c0b843c02801105c403640f00070002041300b8018011034400c1e0400e40800740c026501407480c4c42e010003460340564001c21080d00c0311640420034140315586600515030024140c2c0c400d010081103641c81c0300d880d01040c00385910542e00072808551809c10b99041cbc0350191200342045080c00d95520000e455002c085d2a5144050800760028034068000502e00d08400c64080602190340103020b0702d459 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 545573597 1250 545572347 545572369
    0xe18091c20030301030c06090b07082101080d0906020102070c0302220e150108010207050703030807030e0604112b0314120906101208070204020306060f0f0a030b011b02 74
    0x1007807200c1185804840c08041203059030400e401c000640d80c035411820400082c0d1007990148003046040303401800949003000c259001c8a0f0701981c0940c03135803298500608803107014a480c0300341c1140200001400900003501003942e08180e1120315043c0d8a0b69030032400c0c0c0c03203010006002e89241c0402000107007401c08282e00c030b0840900c5c00444a03078000303001005031511202400d0300c035400610700ca0700034410708522600504412000b1807414500e503440b0b03a00d46000340300140c01c6c0034895000030001c901030703007102800e40c0e00a000c0e41e0a515041c41c114940c10520500140503070245c6419003405c1c91942d40c0c1a40d5440c46400c10303502c0c044155800c503500c82c001d000144500c1002e2000140f010310406aaa0146403a0000707042d0300c0c50f02d0f4a11080c4c05c03040b80e07c40c803208a0010320540c007140b000c40403611004c0d0162005070756640c611000c51010f20131040244051000000c6403a208880720300904486406560140702e404898001151611030201c0614614440d1000680051410484a030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 545574847 1250 545573597 545573653
    0x711060307050708030906010f24030c02011e0504061802130207050115080f0f0102211503060405030d0b091e070e0307290c071a04080d0e1809 63
    0x2840c14030b407503031341000c0e0350425640601c85034885401800649044509480038065412020030480341741c0701803000c1c005042c0c10000074541e5600f940d4040910030b41003a201601184da454031900a029070312001840104e4090b1481c2d842c101080001c408412084a0459001051030381103249031720700d102c000e40c0300d80c5044550350741c1c9106c590030282030400c84000522501001d0400510340303030040740c00c00050703c84020141c2d10411014482c4100e800040111980080c4c02c2c0b41655145020310001c488003070359490303261041c00c0402c001c1240010081c0030a14201c1c0050049041400a12070200c40a46000300b01034190070000c100c02124699280d4400c0071450901c449403803241c0440c0c00c0c090250810300c0241c000152559440403010612a403011009071241d1821003410340c01a1111a02d01984030281d80b181003034280314a4050030303280504041800e86105d80080d15000c6c21030500c0925090103440c802802c1c010790300c16030b030b10948a8010000904507418180814107008102441a4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 545576097 1250 545574847 545574857
    0x70e0705091302121006020f010506061902031605070515040302010905040209060d06090f180f0f02010908011503060605040e07170f1002091c0302030703030f0b040c02070611030711060307 83
    0xc0d078134284002041801128403000301c1a0b04c60030210000d0070301d05240301120303a0340e0503e000d005458440604032a07275040f01d15180b201da0f12540204078110701c24070724000144103011003003400b400000300c2c000302100c0301250340c6019558030004410144c021444040c0c0072030788404080009043ca80c000b802c920100500051030210f981c40c00000700c6e45a50098401c80eaa00e070011401c8451503c40c2108450800304c4400c0000305070f955400c8146413220300144140381d030180b10400c59014072090000380200700001c7c0f1219440200070416504988800d5481f0b40c06c0207800203590a16209044503500d001c8003030071240f03060400d40382c818090700f5000002c1d1300c0340421400c0317402414821111111003800001d692010f12600300500e1905840255018070100481c0000080c2c00100b200c103401d41c90304001c1080307140300d1851401440750280031a04141801c510302c030201d038041a0b0740c054914603103d007403410511a80320741d500d006948008000e0382c144c961b02c10051908201035a40001b00b40b80ca = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 545577347 1250 545576097 545576107
    0x10318030f1209080705070302040f090503030c0901030b060c01092102100c120204090f0e1603060b01121103040b18030702130e1f0605220c020708030a020d02070e0705091302 77
    0x1413509a035000002c00d442c107400911051045140038007502d9170b202c00c44002032013180c100d500d0380e035201c0c4406840f1461507a00010020301503406034000362048076000b4503240e240d5800d80381d103d020b84000c40c07080b221059041c0c001e619603070340034402008201140e401440d940c106543c40100900d142c03890001441544001c0c641c5810080c001130010703000015012490708500390030356047d201d0306404012950410040c08029100d1203e0403011280c221101082e81000301d40141c480c400014095288242401c0300042230503900401107010710b00c07840f050503803a5075074007050b00311060401c503001881c0c00401496004d0714050700483ca043c07949501c0010040907034a0801d00d0402405080900d2000015804105456a01c10900201401e175200018500d800404000a20129064100301503580c0e01c081c1c203481c42041900b029080030002c4a80da80c81c02d06010f550ba040001a00700180300d841004110020081303080c9029110a4481a0a11000504015030522004925000f031582800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 545578597 1250 545577347 545577353
    0x60d020a080d02010b0402070b071404090603120f0e0919060e10080d08060105040302040e010f0f24081c1404090b13090b0411040b03030c0c010318030f1209 69
    0x1250400410000e4028021625282c0019003954074000541d0310580c811312150700443c2d903100d11070358030007058a0b01440c0540180c4182c1128001d581060105c5840c000011040101c02050b000c4070556584942c1d6054042060441b000514124004d8000c80110041400b8145c416031902180884074000302d051030304c036103510340030803811107030070300c0c2d041c446002080244820300804049440d54030b0300b01030b94a80600080e0441c40303148402170003180c0d290344c0000c0200080d805008500f5109400340183c0041d04042c41c0130f000e4120b008800e5030202c1e1131018013010f0462a6404841020018000c0c00e03003903080001107542c21823041028801485040c0385540305143c010700c040c1c500c242c40010802c00100a0045409100301d0b00b0344124540020040030070a946501984942c1c0251012510303111000454050041c0001d070750342611020820740c00c120408602c003981ca640a80c0e00704402001034090b1442268032440141c00700c2c501e0000904551710074601ca07000f06400d02004503012000c3c0c0c1e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 545579847 1250 545578597 545578609
    0x7020303070b150117011a07021008040201140703021e42060108060d05100603030905090f0f0a0906060b0409020703021002031501080405070317070303050a110a08060d02 75
    0x1010071910041032604110fa003803c00d1451504000003031810303c1600ca020402200d6495060243c80707459041040010740c910310700c104482269901410309076003110407605c0684040f90a903412404150011100c00e21103408006403100d0b150958024080c00350682068915001801901d05017801040454044a80c250b00200c943c09400c00d0380801c43d507420700303401486058000e0341000d1020b09000f40034940e0390064410740c02000071039040c650028039103403e5181c24910307910031005030305150000092640184a40b405c80b501030b21000f44550300c3c0d030405200040300f16501c2501007590300204110096513840286103620902d000140d05486408e410842e8001c3c1d030101c0075003a00011300c20200343d814403501d81080804001541076003451014034500c4e04941e5407090401c20001d00080502c08100002001990402902c1c507440000c00f5041000b54400c540c04c0e408682010040b481a0710b046c8501c0c1c411440920301c2c14180109010f00325039203070300600031980c042403041c680c0b005a40c0315 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 545581097 1250 545579847 545579857
    0x41106040303050d0c0507030e090a091b03051c0c15060302221401081915060603020a090602070b0412062a030c0908150c0c0d020c0103110c2107020303 67
    0xa8861544844c02c588a03101901c182c176143d0001c00070248400c20010b9000310841d000c1c07600440d4018107070f0f590100f882c4000c1040d20000340c03c2d0305000000c008000000c903940c01c25a030003001510455039004034000348000d1901c00020004813244400c801040c000c820144407401d60a002152003a903e80000d52440b01c50100b10458000041c1c1c01800050740e445421542c036404004014950701d8041016256034280e1407000343e0101000c01401002001112081c80000040f0100103082d00c43c2d0009000750402c41d40040810741800300414003d000081c2e48040300c06400d44589083d080840d80108510443d104441075a151402c80c40c402c904080c0082c040c40703070010a50954034a501c4014140c2e42c40d5620282030010342c5100780142c207408505c0841c50303100000d50000c1d503250350003c05514811454040c0b080e0180c549001c0005034007250324942d200090b41e05109441001446081902c08d94511a91543c00f410032418903040c1980b8074145007190308640e5040100303d802190540d400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 545582347 1250 545581097 545581103
    0x3051f060818061b090a05040e0a03030501081207060b13180b06010c0b041e0c0f03061416030c09090f0506180405060403110705270105060c070b030411060403 70
    0x1e018104004080085400201c01c64424010062414400300100c0740c000c12900c040070440000612103044d440b008213820091030054010071040480780700340707074813900400300071800641448000101c1078400249030041e0500440c0c1e00c1c0c60240300e0b554013001032502d05407403501700d50f207881990901d860300e21514a460311441e9144610040303a161014411760020452410b0010f1417006201003203507180c6191b40954840c075001840071800c08400b41c8c0d4034415000a010113a045400b054842d241c004507022a4490790050203c40c0c560300051007010f1084800b008444c000c42d181031021031180d0800c1a501109040000800c3e40301d170a0030060f40d4950f00c0c480c2d1144c0d10740c02030110307600300244000d040c480c04c1604003203d0306041e658036446880150000c2c0400c40c11485c84d010700d160034041030005000090011201c0110850603034003881291aa107035001e000340c0700004050034403601b00c0c0c88180308400901140342c1805c1c0d442450f5000940103490340070541d4810001929014002d0001d140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 545583597 1250 545582347 545582357
    0x1008090d1b08040b1902010203090a0305090a0b03090f060108011a04020d0e0106060c0209060f01140703110a1103011802090a0f2301050306100f0e04050a020301091b08030f040603051f06 82
    0x50307030b035680c00174861241d8500c104580c81001000020080401c64140d510b505250140e507452080c00050010601c80c0c010701070103031000041c04144c150016a5801000d103000a42e00e07182c1e40d80c1c210f44d089a402001081c00c0c000c00f1a0381959a281641c010090020042c10000d810b0f0983d003015821103146070480404220000111025854191079191384402c088488400200761140028801c1c0c200038000c0c1c2d0303c441c0c04107403201054001c11128215200c9442100d1002e4400d090043c1c40f10b41d510b02c00b5001b0751a28131800405441c0444040b072403600034207550381c59140d680d1042c0042a010b4602c154080d03503441c0000d02003003d040110010700d4014040fa540d54101b0301018208440a041280c14007450b40f801c00c096511041d18030212202c03590424a180d0f12030030068281030110034029030551902d0250020444106901c80c10642d45641e003c41d901d8641c3c0c40d40d0365a204d440104100c5640070b02c0308000d43d501c40d410903944224008204805440c5d400c8482611445940000020403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 545584847 1250 545583597 545583607
    0x7020a140c131a06070317040318080a170c0a1704090c09080a02060a090b0c010603030807170109090804031a09060a1a0906060c0d0305061008090d1b08040b 69
    0x1103000d040b00b454200000c80204035401e6110740c0e0102280c1c058001e5800f43c4004222002814018220904a1810868050041c0c9010b03d00146914a83c4042201000010034003140e80c03032000501503603c0d54000e8915590400b0000324100d81d0f00070400c13000340e5102d4003d180000410068000c03075012400303120291103c0c00c10b403100040d508080070140c100520080100825400006c0401ca0160103482060b0380354170348801111a00d4860b04425905040052480303410780055000c6421640240e450005940b254442115030524080c840490001880014000c00c40e85901c0070310a144a00c00716494180d981c2d644500d0030901001c0b80500b07100700b030208144e280c801d1111680c000e41c84c1e4010010702440201c440000c0000c40c00d41401030002c0c0c0001070481d1210002c8030a41c10034841201c01a03071244500074081d0104072090b900940d108a20f00c0302c50303800741102e44d008000210280481d990300030000c03a40303494407401311a405043c1010000c04510900c00400c040c01c0d032480e82c1ca50716 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 545586097 1250 545584847 545584849
    0x209040606050a0602160e07090303080403050d09030f081f0e1e13110a1203081003051b030730110604030c0e180c06180622080706050702060307020a140c 68
    0x1c980310f540303c011f0100100c2e040095880d4080020300c1625031600300200c0030b0300c641c2801c0303d050042154100017207150000321320a040c4c000041549803d010f9a540c2026920301c0d602c1450000781900040b0740c0b50718542c003880f03c85200406680c0c1700044000c8400290b0010a4020208505032180fa000709110706000041c8024001800d4050700b0981c1d1000695203030452201c00301c000ea070800f800b00074155000c90140314400030b030640210741103000c6499920301c0511103403c00700e010142030b10078401e0401c00140c05808480640d220003203448446101c1c1410340003000e03000f080c000c0484514180c000c60540607034440c1e000c3c1000d9030040c40072712582424015a410440320240c044940e01c60100e1000015100004283d14043c80036140e143c0ca45280840b2183c0da0b007810b050040c1d0024000c2016a00c01100306039000c82c80107200003251100c0d60741d66686454050900480c00060303420009a4013500b004401190000003510440748180e2440c3c680703102d14080211103581c00c1d04500e40150003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 545587347 1250 545586097 545586133
    0x1030c090605060307200d36060302030403170f180102120103060c0e0915010206100b04090209010e040c11010b0307050d02090403050c0d030504020307090908070209040606050a0602 80
    0x29140000c02005154140030004140d8000108440c042100d03482c8460800c2080445e100c11400403030080320b050041da254094401021500100000800c015a00506e080b010046101400c85e005401c200e1a0915000324081e61004100f0b6080c002c101341c5040025042c4da0b107480c410700804e01801000d0400c0000c100c41964120380f01d2400742e0051104072440c060a82945044a41c08440051826221741c400d81e00c08000f541c2d01980040c411081001e44601e02d99180c03040502642900c440d170341c0d050358001c40c104803802030a41d4014284404c0c0181c42503540200740042050425003440c500f01000641500d84d80030b0343d10002080c5c030b003080c603664500340128203154100b28085c0c00340c6802c01d004220300301c5118402900c40c60b8800c01040605004408503070100001e03000340e94892202030006001303000c056408034000d100d840c4c40080c0f00303001c07845007006050f403086180b032400c030194007041120607020780240d8205545110004885e611252190024081900a010702003a190010310f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 545588597 1250 545587347 545587349
    0x20a090b030c0913060b0c011b0516060c0905040f1a0604080d03050a0e060106110601080601141918060504110403030905060c0120030103060c03060602100c02030c120301030c 77
    0x1590002402440000880202030b5100f0740c005480300005543c0503038034a009001c2541c0320003004540003130200d00c000010340007c0003002010480305855100402c1c05c0300e942c803d400f0a0050760035015940d100043d1319812100c2c0d440c04d01d03c0c02100780d0b5114000103048034110b500e96032490741c0e60306001100e68404e0383d6001c8040380454145052a140140700b0f0303101c0c0707006020700c01003540c0c4000107401250345138400104910f46108903913035580c44801c090310142420003524040d10680000188903c030000d200f50580b0981d801c8502041c02c0142441160050341c425041a186084d0000c5000814541d4211192400307450220368146030101b40801c0781c0c041400407810308020401400442d800c0310440d0110b80068407080d0303844104107411360040280c2480360401d044103081a40344401498051416030307020f6542001003a00048040d82111514841d800140e0442080c0c44443c04080c0e0050303e03124500d0054034a4100a07401080c1000e00b116003481c3d12282c088014014000070a034210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 545589847 1250 545588597 545588609
    0x3030e030a080a050a0207120506012603040509060f04050906011502010b030309010c02190305010501050f04021305060901030e01020f071b080705040b060706020a21060605090d05010b090703020a09 87
    0x2195041440e1035240b0184945040d42013806000561541a41d108020003001400080c0c11072101404500d040760b2034030000e02c16050460150402c85460030b1f2102800e070003101602c00150314007440e00c410700c00000e8000b0400703980f1403c3c0514075040b54460b0f000c0c0611854604002c0c140303960410610524400c0c102c131040045a14220801815403000000c41e21803000908006004000030b1000a01c114403900c2c5404001c084404004104141500b1282c160351003200c50303c0c114060981032000720701900440700c03801950310008100c1828210001c101848061401041c40280c1c3c445a40c26a4030802c7c00c0d070480000051032500744410812200221400c0e07031f11a2000c0e078600928603650315031500905220b03566171064120b859a50000f240c0380541d01203403d5458100400c40a031105441c02c0c00d16035980095600d80000004038420b840a0302c8494940a0500000308184200c560000310112202d40d41c03800d031000290f41751040b0714421003031540c0159030f4401240c00149030f400395500c10703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 545591097 1250 545589847 545589853
    0x203330303041406070f060506041a100f032405030c0303120703050c070b070315050402031e060402162109050d0201052206050d0b0d0f02130b031603030e03 69
    0x1206069030003200b100e0071906049544220680030a00180852081d00801000c40d072076031481404000e040c0d0411031040700212010094808407512440442007039919061340250803151070720001d401004209004480b82c90000380341500030000300306114084008100300d04d91200c0070401c5280c10410b424451714254081e46c100fa80348141e50301c0d00c4201608070700600d5102d4000642c48054031042c3c5000e03d8109055100a040141001d8000c14000000036541c898400c00482c1c3c030b080038022a4085c12991040d00f00e2a0102d40080548060140c6240e034019001c114908012000c0e11505003840e0044a00c01200c5001000c00d00e40b803086952030347c00780120020100556698452190056030b02802c145650b5840840d65a0901011110300001d42429070000300e40241d0007009071800c140d046104004e4400e280003085125054800300501001d0609446001420f044001c620458035454010915071540d81c0046e0910310310700440c06648404003c10410701d5840220081000401d9000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 545592347 1250 545591097 545591191
    0x513020a0b120609070c050607030e0610050a0612060f1410022b030905010f0507090503010b030606010c0c080118021c0f120203090607111216091a040203 68
    0x1002c882c1c01008000d41d105500e2000050001401074911480260713001d0f0035101c4600d00510081c004003240360000100b481007030001200002e4041c00ca10030b0301e000a003031012882c40d020301100c3d1f000304c040d81401c0703040e01c0303400c00a6240300d0303503c5560140050340840050510414217001c0102568001c400c11580506400310701696804015103901e03807820152240718403455002e401034807401400608661070f00b0380a035104803455000c40c3c028040c503561401c01540e0fa5041600303841510800c2a403581160307011807105c0d8003600509180c1803155482446180c0c0e1050038908481610307800881082c005100001180b91050b9031040900c000311101c030048425803146140d100c1c1036403009240305682c41d142e00c051802001a2074115070000c20075581d6160911340004450903001540b07008402c40700f890740084d00c003c188587c400100901c0d00c4d00c2180341203002d20140c9540041c0004600240001c504c0586990000314480d00d102c4030300c4c245003072600b0f1414400b80d50301c0c02d000b5001480005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 545593597 1250 545592347 545592367
    0x90b010518040903031d06010f12170a090b0703030c03140103082703011107060c0203040612020f12070c0506090c06070b0618010f031e0c060305090a060513020a0b 72
    0x1c1e40381007080d4191030020700114545000e50041440c02c07068956005000d00380130140b000007030400e05a502c0502d03120240342e66125900c9000c1c40c0f004000300464a17132100e01e24030751945401b4000c0b41059243c01a0515950030119621350302000b01900000c0c5c4550040100940500807441207030381c94414440e50b589140c0710b00a45000d10f1007a65500c4180310051038a81954000c04c00282000030000c2041c0950700c0e401051540c003140040380c05904140891049600100541d0102c5100392203200b0030f06d0f58501d015000307500c541c0f00000420001d018a0b0b184100081032688942403a440b4181ea4510f1410300524003a4010804405030f80b16140c02d05040d00c40c8030981d403415a1004110007151520000100f8024401c020301510302001000001d403400f8001a070001c8030b000c0c01d8900d50800d02000c5000c50b45e05400030180044c601514200141d5100b03500c0581e1000030203041d030780b2103070459031124151740c0180d039650b0360480505080c80661400c5640383c001071a105284610704960300c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 545594847 1250 545593597 545593627
    0x10312090b07170d060317180307030320071a0307030b03210705010e01020c150108010c020307030c05031201060207081005100905070528140a0c0b2205010501090b0105 74
    0x6034402d90070f210042107042914a80f500504095a8050140c180c512088090042c0c1034010440d01004412070184481c064200860948103803074041c4c3c2d800b40c0300320000c1d240446083e40382210201e180700704180007070070f50074004d002030042c008401080c1d83c90618034402026aa000808540b00e1341040100e18000700b0f000c1c585440b510400101c1a803280f6160034038900400d0384002020316540009541d1652000c08a400940ca9100c0202d16207140d0f00e442c0b44500f210881c01c01500564010400b0300b001c0303070082055070706091041c0e089a280180c3d509403038035609000c0e0f1188016a1102c981130040d000203001d4000c200c03a0840d800c10062400307198180d10482140706205640d41d6880c04070b45524410422a0009031007040143c0300844948100a00c00d0700d0b6483e80c100003a2040340c40200400000202c4440d0103c41c1e440c00305860960b120408144809130070428202400003406001c0100c98644025003405480001915858180e0307074020b07502c03076000f4181080380400c02081c00c15011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 545596097 1250 545594847 545594873
    0x411010f02100c11070315050f01060203030f042102060a050114010207170a0b0711160501021b37120c1505042106060501030b030a030c0f0b010312090b07 68
    0x680c5000c0b83e1103204210039126400d0304c054403c101d02804401000340318540c030080c901c0c1c03242d0311010800d030380e14000106407030042030141e0001a0030410114101800107844550054010320b0003081800494030580081368800c0c0e140b20158000408001c18207050b072103002d00400c0b50910400548103841d00007512070181780a020500c0c2c0c01045030f480c004400300b240d00501e5070301c50320004103403c2885001d407101c4202c1c00a0100e61080c0c1002d03800d50783d0140000802ca502c10780042c205540c44820903220070305000041508103414510020300c8101001c56110150074800610400310043d8245005190082d00050320340a40746408200050120500078100c0b003000c0b4443c0b0b170f262030890045440d84200e40c0001e0a4291900308142034490040c01c07821020305c10300080121a40e03500066068820500019600d43c0020b814000880d000b0751481c0c030000e100e0b14a500030749100341d40d00004100c00785c005a0b8007500d45510644616000462003001e4004141e21504041150356100a41648 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 545597347 1250 545596097 545596123
    0x21e0a0f061b0507050f070f21020301110d05100f05060c0313090e0616050405041104050d030306080d02120711042009010e120a060c02190b0411010f02 67
    0x6403550002805520761000c1d102c8520304034100d50310910003600814903044071200f5600d5009001e5405a4204005200c008a60070310651400452030201d400c003c81181851781c6200503071255186005070b03002c0c4501e10741c600c1c65071441915107105c0030441e0121040107042e5250322006202c2808400d41c0b0010440440d08111001a0f4855295420038154060b941d50181c8001c000500861141d28540104010003801c0e01200c146544181a66034003100c08500400400c404020602042c10301360440400c60208200113442d0903a980040f40481810010503400207070b40f01018050b4034020701501c00c400c5458401420400c540c040b054448d032003541801052103810b9001208152216081358814414940c05062508210704802c07159078440c0ca0924005000c0300c04c44490761402c02000c500140070640142030400c001c0c7d5440008200d001200e20039803040700f080c0c0001c0e0a240c100545024401d805000c06030425190200c425002d00c400b142c1805190f810121850f03600044d40c901c0030344 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 545598597 1250 545597347 545597363
    0x3100504030215010e160206130204020d0b03070f1d070f03050402040b09100602010b1504050d1a040c03020a0b0901050a030c090f0f0f08030c030a050708040509070f021e0a 76
    0x803180350903441c15543c00c2507403d4441c1c0c0c11000041c0ca05012070381c60711440100b05e507045d9103108403404a0325442e00b110404400b0154607403e5000d42003d40c064080c41c041c088000944058030f1002038500400c96011160000300000d0078004a141145424030040c2d0221140c003d81c200071102403c1441458103150401d5138800010b001c0d50b40e940c0060b013903018003610000d42428141c41c101c484e4100c0d0700400e4003560811003001d1050800d111070209142a44a0b0f050a141c141400c00900d1119003409035070050522202c2c28013624003840d041d0150b8800c401e6068028a10b2041c0076907074446511951a44005001d81102660044112000c9500034680042c41501c8000107a801c01c1007070b0420001c81c003a44002003201c2180401c03020a031040c003000400d141d65076903845035882c0f00d034001d0050107030024003c00c80c0041c010006090458895207001e41030030384074008510300c000c0495010700001c2c0381421074084650184042d0340050020200c14501000d0100308558032404100c005206407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 545599847 1250 545598597 545598601
    0x2070507090b040f09030503070e03070f0603050415110706050c040e04061805030309010c080108070302150c0106092a1103030114040e060108011e051005010516050a1b05030705031005 81
    0x380e5282c0c0500681c4c074500d0002c102c000038074203000742290000c59000e001f140307800602c00380c0c600d030010340f1004480100c1c074560045414282d04402412000d0804c8911101440c001614600f481c09016481602d4407241c80e01d608050030040195840600441e0301310200300b209004058002030029842038000f035000c00c1102508208080700b200f040c00c0a0320a020103c00d0014030303801900210825421035445014070790702c58103a1500c0f0203551000035882400211603441492150380907110b070002c000000250169940c1c950401d554080d00507203080d00300413000d000c9050311501c1103d8440070915140c0312034100103a90641e03134881800751100300500d010302900190340359000381241896030400d4548a503034030b4240d5406001e84030302501c04078110924a001403103561107240c0c858400000f040d60b0325481c3c030006440d6a4881203c0e04404030f03501a10101090040100c42195842440301c8800f02500c204040780d18880741d001244a500441003c100c643c0c1c00140c482000240c40ea40002c080d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 545601097 1250 545599847 545599849
    0x180d02030c03070605041d01080a021207120c09050c03091b040b060f0c0f06040b07030515180a060503030406020601090c0e030f0f0d05030f130213060e010312020102070507090b 78
    0x801c0c1d1810655251140c0303100881c100c0e500c00064021146540c11f00c1e0174600042540d1107039100240960710f0035500007410350740945404003100021000b002c0c103403400b0a403500e6800036141074108003038880040300d820420003500207104043c0e002c160034941904508007000d8807a00da614075100d071a40c0900740b098041007503565901c580d2441400404465894807820304524042c2c00c980082251805421603404901c80e020540c94030070382c2d0101d40241c40e40d0710504185c00a14004d00b0b0503984002519217001c036900d900c03080c800c079810b82d0300c0396030340618095000009403940c40d00201e000340c009000400c00e650300010b00c1070540781c0c0e121740410040b118482c02c58145107918132103070b070610903202e002040305004106441c4464622059524640c0307251402d0301c40788025202012250030000c001480410055524960548000d0850206070806035040c019101030f5003101892000007001001004002510010a415540025070802c08981c9589407101d1032032151103a004d072103640b82809 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 545602347 1250 545601097 545601103
    0x6070e0a05010522050d0c0312030507050d0e0a2910080307030e03280308100b1c2405090906010b19051210050f040e0607030c02010204051e090c180d0203 68
    0x217040e0150071091620f2003424050b060111621045c0e803941e00160080c0503482c801e00136548200c2c0e654545600d8080c85000d0b250090100030748000c024015801d841d4000f505806244545601082d89005e0700425814124010880500182d030040441c002c20001d409020007a10503298041c02c00c07951006100000c20b040012186080c0c07a1045415041d50302a84020710340c8c007026010384d80394031695581031103a5060314a64080c00520030414014000f01031700d1891960490100c410300892034400d84c4c00320303202c0450072050052001200c1c100a01450901e0404540d1050b1007800030100b6514121140c0c10030f2040c00020b5090100d814003207202d080c042c0c000c88001416038850804685810b081004524045001d407510406144111402d189481c0c010150480b1104010f801c990311f0f00b110035401007140034480820b5540074000000e00d035988201d86030b40001d2800d4600d1082021390104072103184014400d10500a09100c1104101d107020040c920700142560380b03a008903d54000689 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 545603597 1250 545602347 545602349
    0xb0904110f0a15091a071a19050c0406110a02090103030e01180306150504020703020705060307030b0d080c0f0a2d0525060c05030904020904020c06010806070e0a05010522 75
    0x803060280d0402401c3d1603070000300e01080390b0030400080030402c17130402c6800c864422100b01820904140140c025505098a2050341010040720792150030980000c2c80c80580384200e8800d80390210100c1c0030402c0d60381041c20040c0b0240500090a0b10303644650014941d40010300020b01007008a02140303259034002c03001000c1c000d40410b00c68120300d94a16022000e044111075500082c02d010000040da130501e40280c0e604558150050320159090038188038058000801545c00c140d15240f0700c60060701da4032482c241a80c090035100b61b80d0701103064a240b801243c4051851690300c03403055034003c2040c0403070f000268144113070f04004903a0011150f00301000307125405001800303a0300803411010880b1054018241f40400c48100d01955104196000b12040c0d1000c0c016401c03c01000c101454154003c148810004000500301160101d0b910311306442600a9802c40d402501400b04154100c01070070b51403141140d4040c802420040024641d00403c0402540d03803111a40c1d212111030220f03a420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 545604847 1250 545603597 545603609
    0x5070c02120d030c0503130b100504181704080d080a14160e10300915050a0c0c0201050d09140307020109080d0c14030904061403010b0904110f0a 64
    0x14980001c0032649688480c0701c41000e802192030721140401c3c8a001e40d050340c1c46100100c0ca5038450051603101c541e440b0b98000c24a20703103203003040c1001c102c543d242d20034100c071441c00c518407c00c0c001480c542050103240c01c4041d1800307120103110802c9078050016440307084101c80c6c40d1503000358980c070410501802200480383c401a0034201003005100b08081c4441e08015590b64852003201c0960603c5407001151380414002550f04443c1c1c05034080f06043c030100145488504400455030149000458a80000440d11100f0703890744401c800059009a44d000205a4400c1100c0b036036010001d0440004804c000b0f041c0200030a1411742c1500c154040030042e078010300c000e091a4114440551645d004000c120301180c0e1940e40480e007074000103044290441592a14070b06210151180c4565003159110511940300410042d50039846d90b0051000410307025540c071070b45403c1d5804042c2514030111209000d0720042007044081144150440400b00090340c89007526140c0e040401d040e80c0454105c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 545606097 1250 545604847 545604859
    0x1140d1b120f03020d0c050c010f020c0607050d1e0804020907030207051b040f1401170f011104141c031407020405040f140f030a140c101a0a0b0d05070c02 68
    0x80c006200e602c0c0c021a524911aa00b511000c146280c1e06031420305c1c500c000504182e00c140000c90155010b60b1200c0356030202401140c1083c41603800141131981700384c030f04660f140c01c0f42c11602c3d43c280c2c0110726442041c0781c1c141032040c3c040042000a0280c0c1c0c009002a00c1880c801c800700d040f00d406a41150110b68004e02078440d405007101101261113121080710707000e9031415039084654400340c031070200c0342c0303c01d03070550703c5c43c0c0c0d02c3d1400c508664468000501705501070340140640001e8248911040980d44d011a203841c0c900d41a1000100809000c41e24060005001c134082c20029048490202070ba05080101c17903d5111312000c1c10134000c0b03403c02908986000305100a0062a402031080584110040c1e03070300c948007844180e220154030303211659a078000d1041846581c0620030140c5e007140301c54246070078010308a628515041440f500e01550720765400c0b042080c00c0f4861080900380c0d000b40c6070300840e54900802c03001d00b41301700b010328001c1e681c0d11004501154401c00260007640c2d002454 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 545607347 1250 545606097 545606129
    0x302060c2a010902151c0e010b100f020c010f12050c0d06030b1f050108160e090f24060d02070507080730110d0302071809030801140d1b 60
    0x2000b80203000d00c000036441410000811200ca80074001182c20110002a1205010034240d14040240580400c0c110065488000742102038a4011600900304043c0d543c3d5a9446481c00d000307810081ea194581e130400c0500020110340e99009084013000400740080010659140404450a4010000364507a441d003407a6000007403040ca001480c0c010700382c14078452901c2103941800392045030148281804903040c500002d51280b8682108001080343d41040021111580d00145212404485500705440020300b40030048140386201d220700400740c170003e034607550300318001100c501038010b034446556000580340080000500408008214506c102ca1409450303020f241c0d00381e5070507104403624045444881c5c03046c02c06401340e22880b80d00842800710703003c0e0301d200340552498100740a9095118100d0001501980260581007803030210000003079800f010700c2d004010b403a040c2e10040814a2544040655076500d40d0080c4410b5070100c1c115809001c0481804284040707603100e04400800010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 545608597 1250 545607347 545607427
    0x3020304110f1305090312090c0d0b1008030a0c12032a0221040302130b0d02010c02190608100e061c1e0c180504030e0f0102190606051503040302060c 66
    0x6c06001c28400c4840480c00a030740d6400c1440d5205503500180e80c3c07150011054030040303100140c500e50080c2400c8c0c81c510791a501d9008481c0b45601904d1210001003803412384c07206024810b00280c80000507840e050002c40c0c1d05541c0c28140d071101021039050140c282c08100d4849008100c1140c0000004101610200110030044003540207488180d0044094040340000700d0014482d90b003039210001e2444450022940044400e64031061040340c119031881d50f5905509840c903500b0008200950381d1003000e1400c62040426045075910681446a000c7c050000c590390b0146000d10b040d02130148420142d400d4200400070028a01561210300000c2c4499010f0000c0d009440c01580d00f4003000d4000090125004070480707000b1140600010301e1295020020718001e0081c12028034140704665240c600c2099040f01480352a1088602c9583c1e08000c00c010b0421204043c00c0f005503001c29821460310752006510340100170b0400c07610520011308501502d4441504055411840d04210401c0e00d4001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 545609847 1250 545608597 545608603
    0xb0f04152f01180b100b030c04120602070f060c030b06070503040b070c030209010e04120e03031b030f120f0702070308070f020d0c081e010c0507060b0f0910060f03020304110f130509 80
    0x21700c0781c200302401c603031022030305c015044c048a008004950f6041e02c1c041c54110781e04142c6242c00e80841d4440e408004a41c0440d0101c3d41c9613201c1d034083c98000507895a4a13034094200c035040c40100d40a41c0d0b00380b20303000104202100b6203084840a0304071650702c5400785401c050401442d0402540000c1020002c0b03000d00d0b65000061103988502007409180c00c040c4d0382524900d0341111015455401000710121000f5454001e54500048900312030911482d900d95400d260800e524051402e0445000c010260a80a18050304065180050300c252400c50b115020140300e0058003401504404031524115154401c2103d40704d60030600b24101c0c60b480f41c00003a19070b10000d0724000b0000440c05860240d07801031188100b2840301d40c54a51034000c95503601405401e07050300f1554840003407480032000c2e0b00d0304410300344591004000c42245505000d4060200040c40d4802c608040c414800c20001510503a04171186c0c0e03074200d60060040c0442000203d2007481d6000c41c5407034508103000d10020f00800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 545611097 1250 545609847 545609851
    0xc02030309060901150b1c0e01020a140c070302010c15050112020f120c01030f0e01050a151a030a020c030c01090501020310120c0b030c040b0f04152f01180b 69
    0x2400c10b49031035807240041c072820780340b4003280c002d050010306808005010840d4010003a00c4c10344600d01d9075451036046004111940366250354407594002860342411940b0240b252283c11000b9a85405e0040c04400103039502c0755404028144460301d9240c400740490000340040444445005004640e160341c0d83c0304142c20380c1e04080340149140c9072050a00d16000460510440050008040109100c801100600203001d000401e01e40e44103030038040301c0304c02c7c024103100e4002c01c1404100c0107018140104060542d51040500c0c0150700e034000c1c20401d408040303075008100810050b03143c454443c41142103200384243c1350306a6181002210030030030103401841c440c02c15000c50b02d095555a09852004c1c0b00e10320001441c2c44801c007400c1c010701056102542e00894005c0c00d990402d600d906889410750f10050b0140a10840441c08000490701d02c8002d04081d07030340d40761105a1081544611202c8000f094810a91038113146040c14410750075403000081c110100d040c1d1000c081d05d8281092f0b2001d007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 545612347 1250 545611097 545611111
    0x12120d09030e090f0c0904062c010b0a020703030521040309030519080702060c0a0c060306090f0b01020c040e12070602030114031f0908160302010e01151211130c020303 74
    0x2142c41010711803034a541d0b92880b4036503807840001e085d40c55004103103056109000d0030794450303070792400820040ca0701c05240c0c103030302000c80900030803050341600a081c1070016800000c2c104c004004c055001540400d8500440342c0c94141142c460703040c01000c182510681d445400c02c002d0b00c50030001819400009007003200d000b482940c0100154221000180c10380d01805001039804200b1000181407190082403503041e5603081da044c40c1c015640701008211543d0103070000a4481da824007c1c40601d102d18803c400074800b0402c010658400080d403260400f00c1d085108a5941a20508015081c440d440d40b1022642410340e0720801d5140001c001e400c01c1c01410720040c0c43ca0b90148807070900240444d0fa6842c5500f0f25411120b6050088011707003418501122030400034040c100c6400000502e16000900c40d40001c10f140711101125401c403001541560381d07481c0050010070000700d0001d4403001207500030080c2c1121401c2d6001184c54a62604000c4012a00e8a140074a25aa01102450044807 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 545613597 1250 545612347 545612357
    0x60b0315181b09030106051f02010608010902010e1009050402030127020708030f09070801020a0903050607080412030e070302031902090709051c0201020a02040507030e070611030912120d0903 84
    0x10181c401c0c5052580858007004800642d110040310500b44a02801c04148014004a46d42d83c907a4042074248402c0c210f28400c400c1d0444a40303850503021300421024050440081200322517a80000f0903d03446005030311b0044402507101c04c403491180d0000000b4150240c000c0d903881d40e5072820038015074405201080941c400c030850058440580c000c8503102ca400080c2e0f24103544450301109135a0070040d1050704280700b40c4100141d4080e0070300180c03140380c4103512003c40b2640b6500b003041c02c0802c0100030408010300b140801001800d4201d00c25003007842071070300142e66800c0e0800c852030704000e604040c1d49481703880d80d003200f002c1c42d140e21002514401c0d00c2545c00c40e00c5803402034460b4210f6015103035000a00b03a046110301c0d0071911a02c00c103d80141b04483d40d090305034010a007201d4058603500b000980721552420008001c0101400609261502000c2c4180d0840066180c0c040c42d5400382c4106403c1c020300011100400c50480d0203e2040b20460742c41c1242c0d40310000030521003c089000c92 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 545614847 1250 545613597 545613619
    0xc090a0e06032a04020f1e071101112a0a0e0703110703050a0c06060b0706050103050c031204090510031b140406050105030402040504081c0525090b0c01060b0315 71
    0x1111600316540c60b00815000c0140030f41800d0200406500075050040c201907040c01007043c248001413604800000381d00d034041d62440b850a10502240c0000699410700280d005869003180d000518103403801c01c0c40c007980303010301c41c40e0160303000004102e0802136004101c03803030105041d01ca0014450141800c1e440401c42c641501c14001071500408902802140381484500c4541d40641c00c1344034940c1c410b1000113a225211070302c0b40a07a80020314251142a0343e40d0060080240412200c001004c048005107245401491074200d24403541c00340040c02c42c3c82e007010807400d141585e400e40c00b070759104d0303081c5070140e1418205d0b41000702c0900c0740c101c00d00ca080880c0310003810300348203003015503c040c0e4480c2d04e95510b94003407001500d4050011516a50100034a9070804040b150320782403802d9202d000301c0c5504000f01103601c944180030302c4d942e80e06981c01d84501c00c10341041c1401c0840f0000f00703141c0d480e0008400c0d010300400599001e91100d440000c10041e1200341c480050300c0c009400c507080040c032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 545616097 1250 545614847 545614873
    0x30d03020c010f0e0703170d0c0e010201060509060604030f051e10050c19201e060109020313030f02030d050f0f13150905120d021317150c090a0e0603 66
    0x584c1c40144902d030603811203d801e10105010449400c0d800c40003540407440d200c904140e400c1100c04140030f903000107210041d41c0e8a01d60f8280250001024100c805540c14101540017495611852000804003445c8000c51800c010040c0b1100100c0c002c006044292aa6a52843c941b10242c00c0705404c07500c1e103820001881d022405040e01c503001003001c0c40c211520002d020a0740e10003007610090802960303880e0b4507801000108052048418042c1c01900c42c001100482441d242068120940c0c540c010700c10008056043d080445000d038140c68050750311217900000760b085100b104190300b0040e05020030000e203164030f040001e008030207800059030540c0d203d0000c0555221460b100800c9218202d07c20100f0b82550f0b041440103a00800c10748409400d0440d0205042e804100d0b2512803e802080c4408132485a03024a0024180c51854150103042000381c50f17240d4440300c074130600c0f0200c8440070400291055080c2d03030304418060012030005403140b5510000071001c0740d14074840c0c441c0e5a146052 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 545617347 1250 545616097 545616101
    0x9150503071710020306180a0609110313111503041a011e03111c050106061b03050a051818041b0501080412031e0b01090603020901050306040b0a05030d03020c010f 72
    0xc42d010000340900e4400201690b001c0d40c400b800103a40b21140714840c030031900904540a006a50705040058010b14200c4003000380c49642c040c031041504240200000c0680c00e0741e507840c20640c003060849945001c0f10000d050100e13403501480403008040100003c220644000615510401c40280300c0c46c0c0c0e890300c10f120300301d108200200300d01d0701d01c0e1000c00c0014102d410241c0c0c2c100e401405103040300441d001000e000c140c142415070700c2da03454400810006070022510b45801c0c0404010701001c04954602906a21440b001c0d04100440015125503d5603095104100b14100070b2038031011100c8503881707244c171550581d4191100d9150302048240051060172040840b407043c1c541220319951511000d520105100d100014141c0f1911070001c12001c524030110003640f082800681d03003078008001400c40c40d0340d400602c14940704100c0300907285e82003070569501030310442d0041810a009004038608219071703440342e605031052080ca106015010b802902080000c10000c000c03c140820402c02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 545618597 1250 545617347 545617379
    0x60e0114071b090c030501271a030f03031005060304030c0b06030a08070b06030d2307080d0504050a111005161119050108060604060f0f020106120b06120f0c0105130915050307 77
    0x908c101e41c800340d001e1300002c550450342c10b0000314031043c00c1e2180d0407004039084c601d080b421000f40d50000020040c1c050f81c9110003c000d0042921042e09600e001e0360042c0842107080400342c072410700350000032600e5808100000314154405c880300d443e001c95141079001e1030425608640302380250000e104c1030310312036040f0080c1e540200900c00c241110001e440b8050340c4c0520010340710b10004101074041e480300c501409025a2050b8001d220038480e60600444800c07400002600c241d200c0310001e0381107503000e01658030075028290303226101b041c00c3c81d107400c0d800d8204291304e4010108082c1c0c16066075100100d0b2007120000c0c0c0764011a0790f1800b041007e9807266019080c0420f0404082d59607003446849515848105400001080b80d25100d03074074400c0b50f0409044440055690802809060103082911082c40203070040c81c00541c0c5044142d210020020003a04202c8041842c81c00b941c42c1c00702c000000c1c05c070fa1f03204200440c00454408449035147c066640030784110240006c0c10091804100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 545619847 1250 545618597 545618639
    0x8030a052a070606030204060b030708010e0f070e011e09080705030c0a0306020901050c1209041409070b0903010221100b0f0706020318010c080f01060e0114071b090c030501 76
    0x8482a41d100300020180c0004400307542c0c0d240c0d80e400110060729140b281744042c0c0000b800041c3c8a02e40308100400c0114160010f1381074130f12000520500f828542c100c2a00800c150520840c80c0c4000c40049a00c00d00800c40090740380b01d00747c0b4192090750812190800c2d02c01c0b42041d641c165480300c052656840c2d1800000350400c803664010004546664003a0a1640c0705245c00707807510f1a84071006160840320140f22441d00b800280004041c5054803484000c104106000302ca10701d4098007640c1c40d41214410440d40300c0700015034a94544d004c0d811648514001003207100464900c041500089908841710207801c030701d00c000807039007403c810b0545580010700b440b04c03441e0807002c1c1e0707e2601940006d070504101c14460302c01072020708001c3c0144c0e1b0b1050070319542c0300041d103040c2c000d0256590040e4032800502c040160780181d0b59920444130400205842203050740c524082c50305903905081070031819940c2006100100c0c40e07a9040d081803d00030941e66080c00140d8940e501401e80810a041075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 545621097 1250 545619847 545619901
    0xe150708030709030c080d02030708160213140604050103050a150f0603061b23071a04050d1d012a05010e1c0305071b030306080d0504052e0c0c08030708030a05 70
    0x91000602c03000c0042094410b0f500cac03a020cc982c642c0d40411050b108000084191980700c15500300c076212a030032000c3d403105089409100355495134884070307100c24000354064810946101d0050100c1602d411091103003440410070480c650790381c00c009005010440c3c10350038540446580041e0780b441080548080c03090b1816640c003030002d4801c186007640c00303440d003220403d214403c0c664550b42000d034218495809400030b4802640603000040400d0304100c6200e0098103000c8500c001660301c0f0840444900d14405c0c42440c1440f15906070042d0001170304000d01070740c2494805200e4200106142000164504140000c011101015401d46508a40361400a600061542c6115940310880c40302c05000341000149030b5200d15040c0d0921040c2040782011620001d020081230409001d011040032a80000c130061600381d80400740103481d099089010003100b03428400038004001c0b0300b00000c011250450399242c0d00c528200a1642048991001c4245080005051442c0c06540e140400f00d03da104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 545622347 1250 545621097 545621107
    0x1401230303180d03090e040b090c030714040b06090a030323030f280c0918051608040503130e070f030510091127030601150e150708030709030c080d0203 67
    0x81c000d4207200c43c0404d0301040b0441500080a0055402c054003540c011904111145094285140342280e000003080c041da000c001c04011610300c032038090800440407240480d41c1c41e1a034002414034042d21030516403007440d480c0c0000800d40c006d041590f2600c0e800202c006607000e42402410240400c5440607000b80500d0006521801c180f00080900c000640d9840540e400514010307003213402049446020459040d000e11005281c0c42840e42d0034548104188407529104030000c000703203101c0703003a4000d02c5040740105d4100181841034401a41440c54201803541d82c40301c4c03484803070b0416a0800007141d07c000f1a05c03e010310078001c181c441c011840300b2142552a1003a1100104680d070710115514105002d121188144031900c1503080c2002c01c406501c4460a07403c050900e181079205804072050003c99907101c90700040107e4082504403400b800c1c00340301301c0e10b482c1c0b140324091004040361400400c212626810a5511040e079000d44414000d241d110055a0740e43c03000548030601503801841 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 545623597 1250 545622347 545622349
    0xe060105090607050a0b0f0c0f0d021803060a050109050a0203090327030f0c03070605031303121b03020d050109061d060409020603280902010f0c020301140123030318 73
    0x510001c00060a80c625101060b02c0d03990801d0364560341210201d0081c0c2c02e00550010100d661171f048201941028034082c0d0783e60300003281d48a221107480c229074000c00c9150742420689072030070120401509449981c6810780c0a18020002401001d03090303490f12021410740c803803502c03e807403040000400a43c90032803c01c1c1c502c1c0c4010b4035010301d8865100d28080941e513980701401071011004180d8000c0428000c10007c06051150030f03008071381000414000c001c1250b0304000ba4000480d054104003680321204d000e00e2000d4100e806140d08041001c042d0114070316495801130141044036081004140d891b00300c1e0742d00365010707440b900c0d414020f4001d407856020022040182c1124000300002240501503003c14000c1d0021901c034900d030520311140000c0050300711462980144201404c2145180c0340d0300117868000e51400c00c104028240c6031201c215142588244040c01118201c41965a56242c5082400941d844460300c5a1846a40c0040f44d050000c1545d4003032000445480210341400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 545624847 1250 545623597 545623607
    0x1806030612010c0c0b090105090a02090403090906062601150509030a060515180903030c0307020c36010513020307091e0501090510080109050703090501020c0f0c0a0e0601 75
    0xe41081d03400310391121026088882485443c0c5400f620762502e03c455200e6090080d1110380041c061402641414100002c4a001149281c1c81c194100c40f0079687d030300c4606044a000e180764000003817507440d210001c610160011440b004001c1d0001680d1007040d00c0c05004d0051003001e200e0b04a84c07200c0305070a80c100c140601c0c0a401181800b800b2580f0302290b640313540058507820b0ba206c2030140d02803002402c50707040410407229992600c04140300c550400c0c0e1541907492200a15145030494080082000c1ca8828003000480d8107004048820000704582c0c0090b00349440c2d00c01d41c05005422900760480d15810342401d040300c0b402001f4904030080c210010019502c000e20b02020081c0341748000c0303513160800040d41e44c100c0b4181112030f00103042c1000500b4421840c0c1025100d044602c02c00300310550310401180c107541000c1301c00b25042d250354100f03401500f00100020308550000c5914060804006001840005407108170744014150405220403904c141c09464030181c94440091465409a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 545626097 1250 545624847 545624851
    0xf0215091510140307030519020105220e01080c030604120201140106080402030c18070f09051c060f0e2806050f0915070f0e0d0b011701050903180603 66
    0x106807010034080d6000703407210701c0048403004101a06030b81c0c00c3c081d600c0940e580c18401ca00590040040c5800c40d12001d646285031041e0816005030701c40b007041164451015219007010000c07c010800c42e0304400565070013a40e0040310b241200e02400000e0704180065582820300003e0050030240d1070b41c3d1949441103a0408440056648518858124980419100e4000d02c002d0f03480c8901410240b04240c2802c000c2c0c04024810109000c07105400702981440c190030100e182040204416000800d032001ca00542c00554805901100c41661000c0aa20010101d115020030800c0d01680c0e940b9408850170191013401580c81120080ca00041d030b0301101101c54030519848c9910315031542d800d01503840403628044040d040c1d905000740c59408003e00c40b03201514104141961402c4080103003100c540d00d00800820034400201c080d503407240d894804007541c004400e12141d6031074189082500180e1081c1d503016600e410001003405602006851012120806062000a9a9080001907000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 545627347 1250 545626097 545626111
    0x60912050a050f030403031803030f031e050109140a0e190311031c0e060601050306040c05070803040501022203020a091e060306240b030c0a02280c060f0215 69
    0x69041c5a5000c1202003141803005000040110740e2a81185801010385803440012000c2c200114814030021707400480d6810a8403040c0340000303160314141c10340040701803410640d41c02285020000f05041d109500f00c3d10000e0003603c1d40e50034603118006030704201d6040c0f0481c00c074142c01440d020600d8081c07040c0d020f82c040e4000d2130a5000c10300710041d850f0865120383c541054041d61075400c0b070550035850258540020768103024022a14080d03002801c903200061489100c1d9559640c0140403900401c02e480006800500d4644c0300d1420b460428000d5002c40c1e4020441040c202c412185021900020000c0d03e6000d0b00d1105594a03007101c0b0009080c86040410303090450203524040c010320761169400660003501e0210740d1000480c004440d40701c03040f0404014071010030707061040d0036a82007180d03004107030714034a19500c0407a160200d0904078030300c6036801205a007880d24000124584c415100300390080c45c86180c410f40c1c40d2011340741100c5c08203c00001d6002000800720701600c2c000c2e11b43d44864 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 545628597 1250 545627347 545627353
    0x604030e060415020d030501150c020111121b0724030506011b0516060e030a0b1b0c030903010606050304021c03211b030b01080a050c07020406060e040b01030606091205 74
    0x512a059011603c000620900045e0711000c1c5c4211095418000d0368014a12251560142200400000c0080c000b10300041d040c420a0a10041c25a9040006020280000d20401e8a038060a044d0580040d0b25440c20020340c41881c2e00400c059040c03000e00f0201c0000d05d00013210a8240c080c040c0e02811008001c2c506114a02000102c10418805100b00c5180300c0c038058400c0c0201020281944051034001303c040001c005200b5006480009100c0007442c0c01140b00c603215918119245410007014505404d101008100745c40742c4180000a80110710086009001d41601d604044855002c00c4a001c0d601055140e03010034503000701c409040a55010713192501168042d031010805080350342a4480704141d840c00f01c01002c544d51000e02480f40194542404004086400204040740c090881c0441030340d02c0d40810041d045801c212484a80e0180007405010307074460004d401d100b09001030500550500c0c0074140d8a40c402e0ac6403000380d41064a8110341d050421010118404c11a00c0403183c0788 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 545629847 1250 545628597 545628599
    0x306090a090611070b0609070f020d030905160605070605060d0c0e090c041806050f0105030604080309031c090b06090f070f020a020a12120f05040b25110f0a03050604030e0604 77
    0x4803c00004042041c004c20070301400f030821105000c1d4030030000300007008004c8800e44900d8005d42c04915007201c1141c510300410360041d80e085c000d08014920441c1c05034001c50f038100084581c2c001c8060b01490740202d901304080e603118801d11510384010f010051402c04043d20034040ca0042c2800f461f0809503850842e40c07103a4111001c0b40031680c041c040010303080c0c1382540c0c4c5030400485000b4194403186024804805514000100760786a00c0a00018440350001c000607031103440030020743d08100c0c07444429541946824404500412881c60700b82e64001c80e81e0002401410560010740c0501c44002074514544e0354100d040700c3c01191200007008600400c450715015a45003125803001e4a50003000c40c541e04410703d4000c12046c48000801c05000c08951800c40140d0040199001c89c2d00400702c01d9500c0b11801c2a00c01c0c08850b142c3d00344030a10b0780e2a1150203200140c8000d240e01c0308140c8a0710000c00409007004085007440c03000a0032a84040d0025002034824002c0311100b05000c0c0a0500301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 545631097 1250 545629847 545629871
    0x6011202041d060703061a19030914060403050a0906050307021b030109060905010c1b1101034802030702090604090c05030f0c03150103050c0f061e0c070801020306090a0906 76
    0xc00c10913155a000030b43c98034400d00500a1404050030800080d5100a01d004100080e230300843c86070284141c20f150b0303600f0902c4144032404e2241d4542e900782c0c1069030b00c1717031030649401350050300145450303800a071280d980030481a01400c12280a2a02e0760000c0140c25080d44200c0b83c3d0600c404a825055502c46180310009080c80c002c080569200ea070020a070100e075250010130a0389110044901d0600b00603003103010a4240284258038402072a001c07c4005c00400c0c031380d250641d00c024151640380700000f04c0003038844c0b5480020350b45580c00f4100c480c025485400301c0e80e0780541c1d00d020b9401020f00010441c24540b952180d96414401e50011501c181d40354002800d20610751803021107900907000300d07103951a0902080c20700c0007084461100c00e50440d15110368406280f80c00c0d178001c00c14a5284c00301e0350f40b24001d4400441c0c0d0304540c200e804002d2414040d80b41c202e140715092a125408001c603414a042c0281ca00c5181c0c0504001055540e00d00503101034940c04806a41c19603642c4504484 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 545632347 1250 545631097 545631103
    0xe190c090503120d110307051c0b1c05070605090a17010e03070b040b1e010311040e030a02010b1801030323040503070e1e0615070201110105090a0b0906011202041d 72
    0x1150400c034107651300c5040c1304444205035408030600501c540c4080040142c4250804103982d040d1040c502d0b58074035840518103040040440d0030800d035001000e81ca0369683d040e01800c492125900c40d10a03100389a541d00819207080c040c52411036801401c0450a010903010446116100c1c4a08000891200c144004250844d8002c84c2d050b1a1201070808000900690003416500000c024a10b20204420f81480e803002c900306000003441220141d0450560345e8690700501c9103400b80c801030760754800310342c1c0010b40240303040c10392280209200d0741c6000c060848402140d0490760561a0408039400310440c1400c0241e4946090001c0c400070720022840c0c2e00c003008090064030590101c0002420180340c0b41001841c00809010048000010410551108c01c40d04240d581107080b103a0319900f46100603070b00800c104a642ca1551701e00006c010099400058141d185802681390010030389500400c0ca40750042400361b0305814800d20340c8a00142081c2d0700c801081802ea42e43d028400c0301504c900d41c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 545633597 1250 545632347 545632363
    0xc09040303020c0d1407080f0702120f010e060423120708030a050a02071a0709120c03060b1c0201050d020c010e01051503010618020f090a08030a08010e190c090503 72
    0x3000030303408500f01c2221441003102c000c030209035060040610060016a94180c172900000030419100490181c20995400c015201c03130550040207000000c2a400250342d460380e030800403c80307560034002040301444020441c070740140d800c0b120400310300b26910240da4943c0507070408411a4803903614451180304034500900102d030f21a44006582c0c0c10140c512074240da201900d45003405204001c003800140c240f10b0f01c0390301040092a8a030890b41c8a940030350f00c07408030b03034040c1c42c00b400d80c41c2c001c1e42040840d9100c175003500e01c1464104515901d0b02e050041450742c1c00e820306901010703141504003540c000c1c80500420304500700c025150000b5500c11509480344000d005502e030f0745803428004411019400c200c06940140d0080050600c0c00c110110901d400050ad280f03090380c0054004000d01400d0100c0d420940b0280400030590b41ea60801c503070320b078418045a40010002c40011461414810503079000709940d2824060080c20f400d8140000c0c14a048080148044074000051640381404456 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 545634847 1250 545633597 545633603
    0x1051912050a020103050114010507060506040e1002090a120203030d020c0a02042406022d15010e18010603080a050c010b0a15090f0b04060f0c1506180b130903020c0904 74
    0x3150b60390841c0300150540b503040c0c000640440c84441903001c00c0e68003c0549040300d400640c00704d0262910340115005000340c0140e100303940201d51205042c180260018002c01e181074815220681d40e5200d06005443c88074002035041e041041564003888050b000703805080240303c1a503030b200782240d00190440301e001c3d4461804001d05c2000c0004042401421001001c0f1030014001c140b2090500c0c1d4429401d120203481041881c0f401a07804a8003004034840c42c80c826440749206e5615200d640b5217104044503004c080c1d0200a11a96544030103010700801c50b507010082c2418216001d10544894024449618003907585030b0710310716265590040107005100d8132030f0b01c0f08510603100c0001c0102209030040440c210040d107041144e100e083d0100c0c0c04a0704103140c409581c00e5200421034901104100207410b15000c802122034415003903000c5800c07174119031912500d610290407103605131641c640080d5400300f69841030138441d01c15500900d40640c400c1c4190381c0003038503180c0011294a0103540c2a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 545636097 1250 545634847 545634853
    0x406110d050402040f1109010c030c06060e0105090c0702060319020d06090b28060f020313140f010f0c030516080c010f0506090405030706020f16050f01110703080105191205 76
    0x310007903040c50f01c80d028107071030110003d209840e00c544100086108003038800d41004002d001500038544200bd1041056521a0040c07044994600121003014028062244661415404541c4640c4400c5c100d450a41c1d0180c1070904640d514002a000d1030303841070450b00115000c0240d2104000c241c82000d02500503840001801900030341402281c5c10498124081302d40004240c0f10700c14603010583d0225170307880c40e220043c01c4482034204c1c20741c02800450000040c90041c0400e0040d14806415a85030301600c81016161555004441400c81560501e001c60540d0100d4000309208100800c0e40c4050704507448481c440660b5400e5065018246042050359070303800c044500280c601606821480c111060700d0141807a8455036100e204085005080a0340041c049210824a03002d84906090080c404103244803141440780c0c03548000814500c46501e0120036a98025148040e2171246415031303100f0030240e003407005024030700307038a0002102c403083c0103200040d04184000804101c2807050b006 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 545637347 1250 545636097 545636101
    0x3030f0207080a08011e0503061815071d0402210901150806010f05030604050304150912030e031507090b07050304080303190e0601050f04020304060b060d02070c050303030114090406110d05 83
    0x280420441031040d0b0b06d4590301c0340078100036503540040e5140d040030345860b40d03151940045282c0c1c0d01d003400401000040c42000c0b010010300d59003100d00c4404004481c54403810342401e0304c041204a110340c920300000d0340100c4400c0300c010b10446084640c8464288000a15686403010409506980b5408940300c0e91100e0f0041c009800c05c41d0140d401484150300030143c905142da07505840b03010358000c44244141d180408002d0510421000c8010f01c0c01840b0360303503051040d0500810700080400c07028000d20440e00100749804400701804d1140c85569202445541000d106c054a580310420031b441c1031005000114200e10240300a501804038404207101d16455010a90180d5035006d14042c0345801a00041215448090210b0340803a8102c600580d641c2e0b0300c2c0b5241004003280264150031440101d40c2d000ca02240c6e500038002d1501990420035615a1501095035911090140f80d4010848101c402d826003001d2140c1508140f02e464081400d1440d4840c001b2681c110300301440d01d01c1c0c4c071601 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 545638597 1250 545637347 545637359
    0x507030c020a05041b18061407030e13020d054512040807060504030b01090e010f060311040b0409112103070812060301200d110f13050603011203030f0207080a0801 72
    0xb001c080000d0046c045900070718107940948207103080001c0d2009990005030f1310702098410100410414802000c1d1800d100d928a2040300941106022007580ca08d032001040070300c800d0720010003900047c90150100e82184200d181840c2c21105000c00e500b0040035038409031160300303001c6404081c00504e1940d0b210751a00c1c5146140c5640b991040081c04810001400880c802401c03060544103840400300d011030000404600604181d4080905989041c0c0e021081010000841c40049012501406042c00b88000c0100311807640000030190340e880040141c140c11b140800700442c1e00c840404c10040382e003145181d415544050030849814100141003030703214641041c19500900d090f03000300442c2100c1c200790110102070225904200c013020600650030b1100d60488000390f2040ca107000d0301c8014a000021050700070003000070040302e1100000c261800d00405803412101c049029401042071510260700800300116101e0100d60200009000b10b001d2000410003010103a851450940c9020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 545639847 1250 545638597 545638607
    0x911070f061806062306390f010507030f061202040507021908120a0c0210110d0204030c09050603010c120b1f020a140613020402030a020702090c0408011406010507030c020a05041b 79
    0x180b45111b4002840813100c0f007607119a060703030054804981605203400e40d00c07c540700c0006200300c0002922403650410800d04064000600030b220a813403e00035440280501420b075101c030b00881d60141c00040c031031ba0140c83d107600102d80000700bc1c0143c07102d100c0c40c1c00c0c0d6004140c07401c02c0242c0703c0010020f008921a40002080340d40aa0a042d08011001007040001d44801100744000b00c942e03100d550074051202c1940440b2001c1100c000d085542c0c07603032807510306c2802c58903108140710189030400241075428103018480f5080c4441d135035200100c0300f041ea03810090a02a0318140c11010900c4400106004c440f5611820035054005140c2c4041600e81403880e070340707103070301d184a190050710511080b40e13280c0c1c04c19010b890b4100c60160722070f610742c3c09030b000a0103030000c042d51211454044c4101e40b80c05030300030419070300340d0030090180b0381c0310020801071824260b44450001d103081020402003403180ea141640c0610080410403866518800a4152504e0340501380d01d0010351920303500c0150f004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 545641097 1250 545639847 545639909
    0x108070602250501200f0705040609090203121c0227010f120e1c0309170313020d031b03031d06010b04060e031f060911070f06180606 59
    0x40c5582c0b0074141c40501c00c04080d02840b5050500441c01a02c400202c1c5c150b80301e480d900e0846044500c46010350400c10750b280483e124050040d07180c94004159450b80d4025110180c0c0c010340141441010b0f0a5100075a510030201884440c200f0590801c10405500003414040402c844d25040303500301d000402040c1d41214802411311140d0b990419250780c01c48003080780c1d010013000015000c050004e006043c2401c1c1c4104883c0210403c40c65480d00d0340641c0700c12009800b555502c0f47d12207c1980590300740c4410303629201c0c0000002090001860032824180c0b00c030b446031070109982d84126803545d4070342002041c02c07000f10f42c8502294606417600108507078509580e5004101e107503d005030160151040b402403208000c280486610161820000384002050440496202502d443c00103801802d16024100496080c01504070099a000c0c0940d20b50a070070141203a0700c80ac00b5510743d0010400511036100000411a1400c0811080e2103064001e148910503400002414800c1408210300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 545642347 1250 545641097 545641123
    0x3071416150506091303050306030f0f15010812031504090f1a090a240e0307050a0c05010504140103050714120603120f07170d0f02093309060d050108070602 69
    0x49482001907500c1100451740540750103050680c0c0d641c8070317440802e04112012031036803503d20034002e1100a041002a4100e281181d4030181113051740c032445900c2c2c0300c5a42202c05804508140080343c481d00e40a004072101e10802080050b0480c91035969004106c12410250b0300140d41c8004a0055541ca407070030ba034850090400751030b0329000d90303031006070150400140407804990200241c5070040d860303116a0780c0320700c14011207448160604e440d03550b4040340e441c201c5400d0f980b814001541d5004400341c4040d03410034000802900070301c00044008050040c01eaa042200031391602902180040040050400c485454a80391030301a081c185011911500401200401c00048074034685000941d00b40c2d41c1e0043c0100e080e1202400c0e140914026071101d001c0180c9065410075020426900412809034151040c1031200c5492480844483c10540b030390b100100c080c400d41440500e00401444c3e4210010400f0b410b2502c8600f801c1c00712a403d03082003c0750380c000101840160340402c100e03c0403034a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 545643597 1250 545642347 545642359
    0x203031e0702070317120112030e0406050604090218040e010b01020c0307031e1505100603180309270603050f0709060f060305090f2b09030803071416150506 69
    0x501c1000255101400d10005c1c121a0092070291540703121a4112113041030700130484250b9503140c000c0030400c0c03074801c0012004500c40f005c1403441803e1500a01c022104010512403c1a240c034a109020f540911480000002504121209684c40340700e034403180d42540000041c0b2440305800a40382101400070144650f100480401c00905000e0a07410760030406c2d58420348d03207a0f4510300b1280b00c1d020221020202030600d010400c403003401400c07940840d0060b90b42401800c05681300402c1070682d419002e40090f8180e1000e0044843c0140c0c0b04554100114811040302030001c002000c035000c9800480d06508211000d00034101e04104040c040e1036140030802c6008d10304500808012554450007040c90386401c0090f450010074418044040c1c8440d060f10010403482300e81d03022100007420456140700e0740c0d401e182a0284110220015290710941c0c1034a03548540d8019104501c00c0c5140c075550007000c018440800b000346040038442d40c801e1004404401a001c5c074001078070b000422041c007a80b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 545644847 1250 545643597 545643601
    0x625020102030c04030204020a05070b0a1a0d0b070e011110060f1a07110a0b070c0302040c0e18040c03050d090920030402040c03020d020703050408120901023a0203031e 74
    0x54924003280d0480b0b1b8125401659008441e40030340d41809044000784c03048285200700040b080068000c295a4041a00c0703e00420400808011740c4603960302010f031800182c04000b0303086a0146600201c96041418500000340038040102c0c9018003404981c0300c0c4648501040107207440c0c031011000900f00102a840b180e00c2113000f8980c4500030f4510150560101004402d0310b602d6074a142806080b09c1c4000640d5003986060080007020a880f08038081c91508030808a000d2140f05d040c214214018038400028085644406210002400c15515641c1035640000003a0f010031101000300c400e921844140342c81c2904810889128040000a0109844030040311480050850790b02a60444001403007100d000003c800901400060303040c0580300040e18400c2c503402401400450300841c0c00c0769881085400a81100d000d03401c00c840c050f91080d8004c0b46407041d00100c001c0011016008084600003c1c1000b24a02520000500c050780000041c04494000401c25803644210314026800074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 545646097 1250 545644847 545644861
    0xa020a140705090406050a110a050903070f140909030c0307051006060216060503100b0c1f0204030209040b0705130909120212030c0c03130e0f01150c0213020705062502010203 77
    0xa01c50040006040317503a120300041c0fa4002903808212104402c3d84080d0300c6801105000d819a80002c01c02d520a20070b50301c000400c01600840d40702074503182c2d101c1603c1a0110000d00c1350440c80607003080c0140c041408000303081a070801c00392000038000c40080c0700c5030040480e090101c1c1e900e6048041190025041002011881c0c8402400c895503860b00507501c1d91043c460140c03500d600d800c0105450b5000400480701c200024100c80481c0c01c2c1c407032403440381d0030207a201c400324403980c1300003904511400000741c0031503801d1015030740c842c1c418104586088891400c000b1820031541014400035034640089040c0402e800f01c42c5000d62f01400100721248460280306a43d010040403465070500000c2d41890903902070041d1a00b150348403100301d0795030b0b80f01c18207d48802412650800241e056400000d07040010605a000b940200d072030b04e40700141507400340b220050720555134402c80303902000342000003170007003201d80d21480c10061540205401c82008141c4070f071904050808582c01442407000c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 545647347 1250 545646097 545646109
    0x1f0e0f0d03141302010c0f03170106031505031c0f18030b070e0612160e0a0b03070224132a17010b01090506131d0405010b0103090f03110102040b0a020a140705 70
    0x113103030303088098200c14034160324045949c4a03986010643ca0140140005400703501034105032151070586d000c5014141d1100241076036a0b0104400ca600c89080d130b54a41c0da82e5000704d80b455600062880d060104404410890309103280a40c0115484c0c101c4e802007013501c0341c0c45807050a10500c101c4242c0c0c9451507107100784001d00d10150581c03007915503000d1080320040c000c1d00700c00c54000c0058040c5405666480030301c1034a030400c80f0104054050900351400b0030703c03000040009850b07036003030103221900c4680101c1910414243d003100c070f00c3c000000700342d1800e1000035082e09010081912002301c9007022204ca418490041c0c220010780e060a168030000d0307030002a41010f880090f07951545a0406106460708089654485000d82c40c440c004560000590300080d44220300941c000d0040e80c0c07060b001101140c0c1d1000d0040c12030701810340c2c0500042d1144192946182d4641d001500306611040d8080080d441501001c0141c4e200f129880100626100364a002e0550701c0040d10700240f901001c40c2d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 545648597 1250 545647347 545647367
    0x30201140f0a05270604060b06030103080418020f04120537020f0d03080106080f010b090d0c0305190b0603190b0903071b06020f1f0e0f0d0314130201 66
    0x11251184006110441142c4114001e4103413100005180b0a4000480d52030302c00c260783c1031314400e0815040003454100a41100e040ba688080340c5440d19182248907011810210720749a2515003c01c1194000d039480000344c0090454480b45d2942c00199251041c90610f410b0410b10400348136548942112179070a000110954820f450a84954007500c00154003091070044198010100e44103a01851350140c002c5040e1407058580c8002c0b03031966188854208401d2088180140b03041128120030304101c07174400c1050b4495902c0f0009183c49903661818020000460342e81000b510b2401c0050001a010007070700407074103501800e200400090150040040544007800b00105800400d18840041040b58441a0020003005003502c1c03800300740d5844d0000d4400e000042c480c0c00d0703c8a040c2100420204400664454010100380880c0d011a0141824134000c00f8940500344001098510610185c0d80300030b059038002801250440c2d65480c50403000e0100e00d0b2408484050304010303600208903034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 545649847 1250 545648597 545648611
    0x7050a0c170d24081b13050c091c120c03020c030a260c1203061311090405090f06040327090902150309031c020712030b03100b0a0b0a020c0a080703030201140f 70
    0x580f105c0c0a07500890900100b030920600d05a25001c01c00c80d114118030042c0c01d14003011541026074022488d00448901080c40d0007034084500c541c1ca881440c1e0242d04050b003040d100740141c2d4016944480040e081201c00d001c161100c1240c200040c82180d2149041ca1904284814490403c40d294142c2c0e40d03a50340040b86844241400004a54183e9482801f207045800840091003c05510f400d8130380507803c0a104580514100408160a82c2c4080381c01031003001203800602456071039440c00c807000e0a003041401160070b10030051100c0e107800000090007900c003148005c1180f00091040c44600300b42402e141c00ba40c1000d1047c003a641d80301100f01c0e20391040d2092003c100c96000d0020348001c0c418440300402c07030001d0960011942e9055040792140e0f81c000c4050b10400c15130f002c0140d05664030b4906203503211180711b409202d80c0c4050f01c080c280007500c0744112030080300d02c540030516182071f0340c229030f4042d40100c50420406609000d8480b0110b000e0680d012107083c6541104240c4801500f50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 545651097 1250 545649847 545649883
    0x10915030507020c1005031603021c06030201030b0114091e130912020d140d110c01092f09040c090c05030a0c02031206010509031510030b0a0507050a0c170d2408 71
    0xc1c0c081c0072702c07a4060740c42d80ba0b00c1d4155500c7c80d00308a082c03000100320920040780440d040101702881d540c01803500001c003880f50f905a500d4040a002006128004024061103590821081916039203820303a060041c0f090200740010f0b002c4540c2840f58104100003200b10440d4425140c201303080d940b051030007202e800d00002e000e481e4028a00f408000d00390075100c0502c10b41020401c0382d00c10005410074035049015000100c6003902039080007001d601c0420355064040f07600c2d1a401446c1c2000c000d81036000380100e16042c1500c0d11014042c0c15100e41145910005101000384040d1403050301c202c19440030980000c40c40c0003c002c02c100d800100c01041e140c184200452092901d0b201400394038800301c0c1d454050113191504ae4401c0340e10f003a41b40070a403003186080303000682064040c80b071103014000c1915443c0c20401006021901801450002c650440700c00d50841542150701000c0c1c810b80600c15000301e00960940b21103074454015035080c0000c84103d40c0e040154000110703c52400c08082c80e05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 545652347 1250 545651097 545651131
    0x90e0408091005030a23130f050102070f150207020d0807030201140f070e030705060304060510090f0f0e06041109070219060b120d090b09010915030507020c100503 72
    0x1003046004840801d0380040744811204103140d480001940b082c00b181000f00b01c00034001d40ca0b42480301c04661380303045600d03e00f07000c01d4410190280280a00d4455001280e00724400e41c0c0b81400d80c0c00040303040340e02040341c1c0780e01d204110b03000d540d0000c61001c00d5411418040c45400240034519000f001400552000800c0c00c18103200b03422054004840d4120180e05042c0402c0b40c590201e0110f82d240c00041144200700c9003460040384103002c483e0001c0041d0304585039130b02c0720713401418080d000100f03142242200107200c09660003644604600107000144a490700c04101003544c0c0c800310505002e130020001c00c0005035611408000f0403400b0380c0c030011a56102c3c1000ea240024000060641000545c911030801025400244a40700252072400a900420020310f030340e0540c0c6007810002c00c10b00f034402c0c800081410081c00e6041014500703116281da0307500c950745561006040341c4002903141c2d810000340030303010000c99500801c142e881d031494040d0240d0041c401c2c0400340c04003498803a1020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 545653597 1250 545652347 545652353
    0x1110601050402031510090f0602030c0304210c06030903120501030209042406080309030111250f080706020306090906060f01052a0604050f0606010c080a031103011502070510090e04 80
    0x2400c5171030078000e80134100400c0c51400c0600305280764400c002c0a903440206c003150b15840402a100354644020003141024104805400901100c0b483e041d4240c50720b00950010549220000340104a15200090324507154200200349450204501c10000c1c205401040144c40d1000c910354425000944032a00f0f4100d501048402502c50480e400075505012001c140e040703021004009140f404c1b4020404951204280c40c043d0050120403080da4081140c031010720030740014407622039485503400380010318180c3d541004680011400351201030b03000c0100f002c0ca04080401c1604030000300000d120380d1402c0c5000804920310049901d04100c00811498030f65202281030101c1824101a41040e241001400c0ca035a02c100302c3e020340303480c070804001c01540000804c0050164406940c1c003001c400050b115010143d01c580c03510800c040d90f44950b0020044101c020b18040c240c24014080c500111090013860044260449440364108102d480d1035142c0084060045856101204540b82d4682c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 545654847 1250 545653597 545653621
    0x3070306031407170a0506063619060b18060d0903111603020a05060307020f0604030207080705191403070b18041b02061512010e0601140111060105040203 68
    0x680001c000b04180688440030000200300081910a4040092a410295a80541d41d890440e501a000b43c000801007581410035030383c40307825404490f00d0303201054851212007660802c0304a404140f101c40c101031015090080030380703565441d0301c242c1c18131003141407090740702c03481c0308804004500711034a454801190b2201070564032800c01c0341c60108030908003803c024180c078007003403c50f0f21203020300340c1e41c1d0ba074403040c01d41c2000607203401408072003401d0705080c180103407980050801d0055105444101340b4481d810484c45204078841e5024000c45490001040e02e4181640c00451113000308542251100201c10760000885842c1e0f030700e00c01a4417400002c203061100580003031000038400030711b1005041001900c60304400054408008030a401c941e4000200c1d60500020010b8200c44d0119482c0ca50020084200180080070441502040101030342142c8205608488a0b002080100001d0b031b030078544207040039000c0c200803030300e40c0a9003075840e15500140111803080f680800400c110b00805 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 545656097 1250 545654847 545654849
    0xc100306030204090f0c0b03010e0105040f06081c021e0a080d02090d061406060405011d0102010b030312010906051c06150506030a140108030f070f08090402040f0f060e0603070503070306 82
    0x40e204010b560344034103140c5ca42c10045d81c020f0b41c0300e1701e6807080000c1c0d96034a0300450f07041f40d0f04c0011000341c80c0d0a060800c0f000d845010b08201c189a01d50700045464542032018032111551254000402d955018010781030042488070b642603a0b001e40700f09980b415000c543e146031039a01169070741d560000c1c500d1a400038026018041c0d0001e880181120400c0102c0c1e100403603110102c2070f1216599035850820109200318012940090188540e0a00842c07071201210300b007a4050002141ca803c484000c82c0c0345801040b4a03903004903c00300100414402e0740701d100040c0806680fa11071000451850000b041c00c2517100400240d0380d09501051501140c51450140200500d601e80e02d051508483e800b400c0048040071040c00144000560781c44000301b00c0700169500400d180c1080322544400240e0316041109440789003003006840d00b02c3e40c136807004001030b00355004d15001d0a401c0075000000703c411b41c3c101006001c202001c0910a540301d0054940c0110f0341c0c9001540e0b0390303034101d00301c1c050302c0e503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 545657347 1250 545656097 545656099
    0x121080d060602030c0c0906010507060e01060b0a021b0d030f0f0908030d14070306051f0306030b04030c1a0f0c09030a0c030303020c15040c26060702011e0203090c1003060302 77
    0x584071001c914554080018030310180307444110707118000140100f02180c841a24034a0200d041000040c0000d0384541060580001c2071000040d4103544880d00b403403581c008020440160003102503242140d10703076160358101c000c09440d9070300d10500c81e40e0054040c88070710140d0414405070030781900ca014802d5003008060440441a02c1d290f00b155117440d4041c080e101128003c0c0c0c031495000481c068400c1c03042d801110b100400c00c204600f1201040986045010380307250030551220004030104a003200d04501552203503a580c41e440150f8180801195800140281c4600c2d0300c109200e840d03c011a01990403103031940032582e52f000e56a001901c5d05500040041034041c0c80700340001810b805902416a0b00034443c140c132410b00903052083e03543d13441101d005040300b81501c028440d9150390402171402c010a000c915200c1c1c5d407000100c500e27080d022107100e00180c0d100e182d040c00e0381c681803a0070108054086800e50850510441c0c1d00c0d220807000c107150380110319050610480d5031083d000f0100440d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 545658597 1250 545657347 545657351
    0x190305030f09190f03030f110d0e04021303110406050102190803220b0103050607020a0510020c0c0a030501020a02070b0705300a08010e160c060911060f1b01050121080d 74
    0x2d550400c0184c8000d00e440f00350301250202c8079032105039000c0c0041d10000d03c0da50001e4103015400203010343c1c1d50308070810759035003040d800d01030842035960214040014500642d2801c4804040800300010f03651a40c000e00d0441d000039000b580300382045006150460340c4160744a44907510040184070b450826050100074008041c0d100c014030046440c45810b880c040d02c01d072803055494035020307030780e0741e1281764020102c0d03103d0810792400100035800b42801c252844242e0743e00101c00800a0320028039500b0a0b24565400150308024940410071132000b0301e50922514101043c42d01c07055168101200302250042081e8401c05e40d22090741200150300300401d02c0c460301e4128054004040e50302c01d000e0409115214000304841d10007104980d10786098980c5c6a103911001c550b100b0740501070418040300c040c845076243c0d0503c0d40d9110007800c00c00b01c03403402d2a0340b40ca408d95802a1511141c511038080c69142c503006000e803814144600e08a450459406039504820b131810301d229220b144001c80d1514 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 545659847 1250 545658597 545658599
    0x50421170a030c0305060a050d1106130602010606080613020703030b09130308100305060c520c0b0705120309150a0e030301060e0103090506090705190305030f0919 72
    0x519002512001e40540c0d001c10100c12a4502074040728401d40f50540d101c20742043c20003c0d482c0400c084170f24148100f000e1a00d010614000c180b007500446002003443c952501c2c1409401d5092180b00000c00c031900d00740d403581c20150041100e8a14510042c4d181903000283c460503d806a040100b900801402a199518201410401698041c84200c00280b0014082084502040030420903641c00c02c0240225450380c003008180b50b48240c25281810154101442c1480c09551600c0c5400110b450300520501d030310900d40951262042c8406d106081468002000c14244060001669070090400345c1e0384405080c458038001e21035180d03481c104000410005120b1000c19092101c07000c3c080c04024940350f1039100d03404d886001010880030b500c2400100951842030380095886413043c103001a072000c2546581e401c10074122a20090365200ea8010040c604082101100c0c42c8045180360380302d9415a907a541e164810f40d2244039002c44041910189541c82201c11903014609d696001981 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 545661097 1250 545659847 545659883
    0x7081507051c02130605090a0f0e060d02030a0f060f0c03180b060316080d08221101120c0807020d020a0507030b04061503050a061103060f0d03120c0816030c050421 72
    0xa5124800f492301450b0020400203403003035506518410307244021580b90003950b5440034040710b020610341c240d0b8944501e070821004038171085c01080d2428003d03c00882c0902802060205a645070240c0d0400c1502e01524900192b06001d41d150354141c0c080c500d4006521040006031070032250b501401d42ca05c40644001a106100060101d507185154550062984d564040c800c040028940c1e98821078491240e0385d00050b250550410804105041514031103480420200488a0b4031207c40d000c12000014405025010810310f5000d4019100501d10890b846d90380540390911488001c0204c0001c0020408008280c0c015205903100c4005012005075a07090a40c0d5800680030292100c501d40341a462130b12072407904480c89134030040c240503d00c5460f403043c040e001c2c103928010b8040001da00941c4491040740d018004102c44070359a86002030030705c4200110802c2006401c0800d052500d60708480b1140c00070262070894900040d2105c1d08901d0011305000001484130007025280c103000e8044072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 545662347 1250 545661097 545661107
    0xd030c050d0c110c04152903040f0203060105060c070b1605160303090b070209150301090b0703060609051234060804140c03060a020a11060907081507051c021306 71
    0x81c103c50001240c40401c211014002150314100b5407200c241540c074402d004060481c42402d1400410140b50f1130100c1b420881100c061b0000d980881e000540b00280c0c509500d410404a03000d020225000c5203460300c0b04195a0780d5150380d119034212001c02003959080307040c00c100c000540359001419203410200c801b4014440b0748440c0011804a11001404105588d02c4001d440354a84d010341090301c1c0341c5402d101d04081072082009241d01d99214221200015101c404481c010380703103504e01140d00c3d82032920191081c525604541c3c080c0800d40c240d00031501e400511b01c2800b50000c124011303c0440c1844008004001078280000c0100480000071b40550110300d15114901805121104454070b600180d266003403d0020b5a0641c07000c40440c1100200741c0c01001c080b5900d040032000c185410b0300e580e0524008440440c0640c04c514002c105080381401191010402c2000070300c080d01c0d001d200900180104401c00c03142d0b640100300e4071005900381e4126048050070340e2050000941e14400200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 545663597 1250 545662347 545662367
    0x6030606090807061713060911010e0114031612090804060e0f0f040c09050406140117041707230705120c030303012c0a020c011803020d030c050d0c 65
    0x10005007415400a203160012510505807a80d544d43c070007062502c2c1c000c1440801003e840d286100060100ca200080c030284203029101e845568100d00c0c4d500d90740c0c0050002c4055226840c10301807400d4520004131901401c41e135107d9074000190881000040b0b045619450413078150744401e03d4051802c01380a04507000d8401c03904d89a455107903581030318003070001c5c912007100841d411080d480c130000c201c1c1c43c29030450212900d2518000695541e5003000a0903a04154030040901d01102c0e0402d2003541c1c4540710418001d0108891700340760600d603558041051107c5201d0b0000e62002c01d640d400c00c190586a001c50b0116400425a41451a050141c0320300c19445194490081e80341490f403d41c13000714080e0300c200402405103007160718001614280810040c400c0c0858110000382c03d69085943e030040740100525400140c036840c80b03004042c02c6a042c03910303040c2c8006440c9042400240d0002d80c180c09148246004580303420009010b1f00c16000703d80d505079010b400c0c0312440d204194440300142d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 545664847 1250 545663597 545663609
    0x1505060435030d061e03120f050d0c170f040b24040c0f02062401031104051f03110f03041410051608100b040501050f07080a0903050610060203191404060306 69
    0x25a420340c100001c8600b017103644402440c103a424490001c0b0031b4006d4403001d160401c241409490800c3c000c451070203c42c8040212000301e26446600215110030302d41d0f542c0d00404035a0321504500b01525004128400104103416086004540d03d5010000001c8030945510141003841001040385000d0202185400030700010704c1440000342122003059649000f400f201000510701084150045014001d450121000b11a041000060035140d645024034103481d02525008124480000107040c2c64003c004c24110000030300070304100380038a0040f44d412503404040e185c800c0440007041810000070841c60f0700c1680c03610041100b4100c0909a00c10148103640e40c1080300d695810302d4082003901400b50090111042c0410320203940030340e00400c1c090030304c030511504040159035110050b40c05030f00c0d40380001d08941000c0007000020800c0940059259414400741d03404c0000c000d69a00502c410b0041d8040092a015180d40c000e0303286080205045060950343d0340c1391500507000d041244103039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 545666097 1250 545664847 545664869
    0x603170408060f221718011101290d050706030605040b01111c02031207031b03020910050f0c01110703080603060c0d0504060605040504061505060435030d06 69
    0xf8a2010029540d03034802c40c1040d503c9503e1103801180c0003200e070703a0f003102203484035100e4484801290040001e003d000b01010001d03c11880c998000602000000043c05601d80c1050703412040411072880908503600c00d144c84030b284040100000b07035031a00c3c80e040030b442401502c0c404991158513401c202d05540040d2810b010020000c001141d6169043c050a982c0380c04c1500d08503034007500003000c20f40c08800e910461f420080a240c40c0300d0000010340311400460395603a90f40c04210304904c0d01181681041c28118289a450004104101020100ca01c10800c00007140c001200210302542c0c108502900200900d800d008660540f1f523000c60303029004503d811001603404d19001410b40d21504031f4041d803e0a05504030343c4503000e44806042180c415450308000310352601d0b1031150905c0303180692000f01e03284000541d02c1410342032940100780140380c100002e00c420a640c40d10b071000f82e000362000c082148503e40c96241c00d1a002c0142041601002840c0d140c171042a80149058810705e41d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 545667347 1250 545666097 545666101
    0x615270a0b0a120609020303070b070801061707050913060801091b0b0c03070807020a050409050303060a0b04060917010e0312040c08010c1202070c081207030e0d030e100201060317040806 82
    0x1040602d00080c0705980c1040c401002c2440059040c0c0c11020210740701600716400c244003950382d0f40c0007010072138084000503403e400400201b6809403601303480741c980303e894501504024030700504911801004034010540880790f80c204400e40d40c4844002c3c03503240000c22072a102807070204040c124504883c14400d100344400300f01141000221601242203000a6150250650300e04621780c014000c03d99201c0d160b841c0c0060162524010b082c08248038102070340e60b904d899410014000000d402c110000c00c000d02c03080c0a8940c01c4000d040c01c0d201014001e0b26a82c518140c464050007030141e501e04540404162044a2610180351500a52103050070003569034880317605608a0b9800150413000801031040051161016801000418000c0c143c8200c0d25896100315854800d0f442d041c2d80c00514002444030138151701010054501c3d00031144501d160500e070724010b14422807140c01a101e071580982080e0818000d6002d10011640700b05002514066a2403100158006206210081c060400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 545668597 1250 545667347 545667349
    0x80f0606060c1507120c030c020114220807050f0a0302070b0315010815090403050d1401081002030907120f11010203070c27020f04060e0109080615270a0b 68
    0x1d850380b91001000401c144480301885411400d000b8246070240905d0601c18003c54445005550003035146403801b2030b101c0610103000f0f003161007806640e000f02c1c0451082c416802a180000d04080c01a6003400c200001e160034948910b01c6640e000920500c40c41d5890409c66901045490b02c0c14000d400382c0d08169a1540c1490302844200c414480c00c4103140c421001542c080d0784401c3c0c000d45c4454500a0b00c0807a840418a204d00580f0b043d0f01042010030141c840030505c0c000c0414001c040c0c001c94246501d0700d100341d66901001c02c00d0740c0ca0641c0100c00070b5203a0504018150051504560114a800042c00c0603202d02940d04000d81d00c001b002d00d410000c650000046407a4154441d4071041c4a502d030014901e0b00c02c05c10070148425021221070440204c5850010f007406d16030800c0015074880c42d0000142c900e000b8049081e0502002c05010002c5d4100031404540c1b041d995130690801381002d0300001c0c208925a030440045101c00c0f000600c0c0050700301c03243d40c46200181801c0000c190508 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 545669847 1250 545668597 545668609
    0x40e0c0a141002031c09030e090a0f0f020702030a0b040303090b04081e030f070e1906091d331206160216290301031a060105070c030b1009020301080f0606 68
    0x2580e1840a84da143e00b045c034211003560041c04864002d19103030215440240001d0012401600c0c01302015464a0300702d00d111685108080e0100c082030710440c54052560302207502e81140c030744081c280c10140300000b414540242c01180082c0d9100b0308020103441d16140070f8540360820b001c1e521040001203039200000750b0704001c40e40944030030017180e8442d03607030842c0403522002c0800f0441d4201c40d41d40d1195a10440e1454840090545d40d201d805140f03042c1214044c6400ca182412802c2002400a122046102e00d609480e100c03001b1800c5a40c0c403500c051100d540e10380104005412004441c040140c0d10f00c0030174914001c6440d101c28940c040f660000480ea107405400704a94940d623148800c21900c3d03c14203082d15100f020682003001c030100070140319010b030001d900558125000b592120890b03040e03105440d510401c06d00b4903034184006d5480703091a446c0c840c080280f200108001045190708951002c200908a080040d0743c0c0e50384071040e140c3c0340e0f220341e0b4a14000e4421280890028a0301e9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 545671097 1250 545669847 545669857
    0x708060f010e1017090f0c0402030609060d060e030d140a05060319230f10060e1b0910021b03070302150307050408010e03030417090f040e0c0a14100203 67
    0x50b9149400d101080040000348550f0850a409000325400e41501413504080054811102000580217100000c00841e00f440401c5c012288100d00c100200141e40d6144d55000d6042402502d103250083e9052030440300a004180d03940310203100c00326000e03070002d0f9250495070045100000c034a07050784549080005580d0f090715040c0d41a00001d080c00144039810303105c90004c078062072141c10f07004005202d540040005490021841d04904406280d015080180b1060b64400e081d04009407403612501020f080e4024046030b10f990800c070780e0410031003a00c00941d2054403008210103c030354a00c01020359500181d004c0d50030420310f000041602e6141c04904001101e402a1000c100005000028581640f00400340418072034248404030b4682801d11821400f1080c14004594030f0800d4205480103407458600680409010403914645844d03100e400300701024280e4010901c0c87c90004500d052102c4160078039000b50160400148020f1031b400143c00da102c05a85d0281c01100c80401240c6034818 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 545672347 1250 545671097 545671099
    0x130c03082a072309010b04030615080d03091110090e01091811240705010b2704020f0d05010f0c02010b03070303210c12150807270e060708060f 63
    0x1c01c1010104103c4507204481521100d8842d1408540c0000c089000c01c0e00041508040820140200849407284004240c0317003080d540c078074034680181c0c0d580e50b0781403c0684080644070509a010408101c1c2c20b5034450400a14241c1045d10784500100104410300c56074002011700800001c41a0552050103e07881d8030540142c44030350307651640740c0e0701c0445d141c169801125140c0c903210203143d070041c1c03030701c40070300f82c2044690741c0102d428014250380300002d2107441001000c2101c80c014800c140e100c024000c00e802c0303400f525502c5000141840a400ea400c139000b018078a404c01c10088198003100c1040241e04c0100000d03001da0208074200c520000000350142d010340380c2440424003407022000704652070240760045082c00c245c00010f41e9071841c2140c001c200320100c034100444050040c0a0350a00102260348201e25044e0466542c03007403072080c0050200c142e908200319000196102c80720b810041c001340001100110420394501048842a002600c0040401c01528201c00710f084000e030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 545673597 1250 545672347 545672353
    0x904150605090103110405060c0a1208060a0329090d120506060913090206190219170d0e010911030d0e0d060e0a12021c050309060a05130c03082a 64
    0x80002c0150003d007044210309102003400e100014070781d0780d05401882c0f48060800500740d840018034013041c03c0c02c0408a0075007808801c030100001030f1204100c0030216034001c1040b014900030740c21240340401c4088042c1580410010401032014000290701e00d00c80d4040d550043c620003a010003d0844400780ca040ba402203003080402c00301d18042c0144a83d824802000140340021580014041e6020b01d95400d0294189078103510070940500c0384004441c481c454690032011035540790180c0c60169003d11040c01c0000c60541c0003040603500a200040300724008009840142c1071504c03880d40b041e44900e100744141020b8840b058822061000c80502c05481d011520043c0d1390b43c1005884005015146403003001040d10100302070341c4550524039025005031001c400352641c522084150201e1480c20300004005211000000140340c0b41d0104201e81c0015032602c1d0140b82091291803442c003e80900c0c902100401403240c5140141840c01300c0032001d00c0c040d440744e085c4140e146090b058403441a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 545674847 1250 545673597 545673607
    0x20d260417150601180b0d0b0a4103100203101a160204230615160f020d020d030225080627030703050403060b0607051c03020f040b0904150605 63
    0x940210b14503001700000491120705030b80c80c1d074921400d580104610040007500c0344079440d041c0c2407400c07900c00a400d4100300c800020b0072110440c54116100d10348000e11b1821641da07001c01002c0300150050500300103041d074200c02041c1c1c1c0201c01035041580d4100c0390460004000610811066040410b0b04803c0c8015043c20f403151040c0e20b00320721400703060344c20540f100c0300c8402060f58054416860329181410072030724189201402018442d200740c60b82980d000700700d414102840e94400c10750b150b90111003080010a03a1011440750307010800020b40000c2c4032450641019004689203c000c0440d20344403647c100328000b034145001240c810400340d90403507804101c040003070307403c000e40441031603d0750080718031400445071540e400f0301d030241d00181000c9420700c1081202d00682c40000b004940c0f40d030401c0d42d151900d54a0746a00f032040c0031408000c1d020707007548078025010389100710040388c1083d1300d49583c0c0c0319100c5968045070005103d1480c0a14070005220550b05190075500b481d9941810300c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 545676097 1250 545674847 545674849
    0x5040c021005040317071706090c0906092e0f02030a120b12030a030b012601060507030e0607060b031912030b0f100302040e1302030604020d2604171506 67
    0x800c8043d2054080011202d507840580307410b014a80c0c0651003e0b640c01210750440c00c616503d4032005400103100f0000d600c04d0001144003401a140c401600b02c540668800c0c407200040e14003032407103240882d5010742d510f04a0b050640b000e1820444e01ca06d4848040c46540e15104986a21559010b079000c00c0c45001d080082d003004d503128a04109018244035a0480b04c1140e10749150040c0448000080c2c0750945040c265a00c865006155624003502010881c0e10510036510400b050041004109010035a2000d240c42900c02d142c3e040005046144e881c0d0450074044007910485465500911401c0302c0007078546903c00d0040381881d001000e2007414038180c4c0c000c074064809400f186910054280703000d0019665443ca00a0100032900d00503591490203007a030800d08002040f8046100710307890481e0240c3c601058160340075a0480310012070080c5482c01d85039410000700042289520070b0360504100807080000d01c00e84074001041c0942d1640030f440d030f80d45c0305002d1052004a640c0840441d01c1e07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 545677347 1250 545676097 545676101
    0x1302090904062910030c030b0901080d110606060d0c02120c030d06150c03140c0106170d022b120c0201051801020c120a051b07031101050405061e0412030305060a05040c0210 76
    0x40500b0511f000701d01502c0f4040040c0c43d419080c0c00c00300c41034214800350004580c0103480c188000c000f50000e08000c1c41c5c420005a00c60080b440410081521081455400ba1081c0080c8201811180e2000d846802ca02815a0340703400ca00c0d05160750030b1030100040740c0402a010200000d88140d40c0b01e0104001e0350340c0843e4200300c4e04d1420141c100e8180030112484000303000fa00d000d44400380c6642c0c49101d400b210280740c020385103004420354220b6100108c0580c1c1985c00c030304180800201c9400c455000780c40448003007002070080380c881440c020301c5605056040d00074600603204406206caa240901407440d08034401d500c1d0300f020940c40f140300c400d40880301034054582c641c0a410400d09011a075483d05481e698a0b0200b4180c9812020b0144200301c020103145800d00002c5c40e200d402e260a00300891098820030040640c8203441c0d480e0f100f2080301e401c00f01c0c1c007d032480c8014404105a149806000313402c041d9002c510441c0c86102c04034550402c3d2049010307c00c804d600900304c12074a4900100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 545678597 1250 545677347 545677361
    0x90f02040e0c131b09080d0f0207030f03020109050624090903070804080a1203020415030b030f030a2309010504060c05010b090103080a2c130209090406291003 70
    0x682401441c2d403080071a500c40c3c03440b0030941000c0c0d0700840d000e090340740d014010300141050001800a0300340144544140058445415031203818904803002811006918101c40c0e03070700040401e07a40c411030108060f41908a601c0e42d03072103541100c4250700c0b6008207040d200160384201001703001c92140c0200b1450082c0e1103d8015060784141ea1400800781c4400c24140c0c0280c00808041c1d00000c1e4000400c0004001000b9020103843d085042c83d060800a501d8010b502009004054640154941c5560144561000310101200f16651810f8010024003050030b1884215010a194810080f0040340d2200b1200107a2050352518a460309061046d56400d00e042c0303059404d99030320030f2030114980398000c280d8080c41c09035030340079240c1030740c1034009214410f400c02c000b2000c0711002e5107401c0e0020180720b08001c0c003403c42d16100303000a01100d1000a0107080c2c00c0da6800395a810620007803111643c000d0704048181d1159030101d505201d22400100c40303e14010744c00c0034221040c80c084501ca50b000032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 545679847 1250 545678597 545678621
    0x3090305210d0b0103060f0f051804051504030203160606080705030106080a0f03120f1a100c0308061815010212120406151805100515070803180d0e040c03090f0204 72
    0x144858445407d03e540102d076802210320f1782032555040c04103140109202511921207a0144943d1402d0758500b516102c5020103410200405800301d000c25000b40161001108154101d8007052818206000036028520541c241030103030140c08200b501f010700944090f58645402005079210b295225803201c0405207040d07003080194241c1c45940c0b4201d01801207110304212001c680d01a04070032150320242d480c002c403842849807022507005182c100c0354203038945406041981540da94500459003482028510712403003404102005104480002031000081782a402c44105558051581a0381d1051072420000643c4140024002403903580080f05460802c1911511403036858102401049200e5502203415071150104010a561244400d0003040c0031154000034000440740c01c9202d110b41322028086000010020341211035801c0b04040008215003140c1c809801142c0003807083c443d4200451065007410700502c03c483c441c1c010301c3c038510b802c0320b1840c0210301c09508200050003241c05071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 545681097 1250 545679847 545679851
    0xa020f012c0a1707030c05010827010e010905070f0e010810050c0f0301120303050f0601050403030e0a051203030106080708150d11040c180509270109020d03090305210d0b0103 77
    0x41048400b000c3c4004101001000405103030303003580760490b8004540d0304400d04005c490820800c1001d5030340c08801410008a064400301e42c101e101180c00b407e07221000380499801c24402000300200055017004607201902d206000d0f0340c4400c030445d4003005c01c3c400c203484d83d8412003c8000e003020039030000d9040900345076854500074546410002031703002640140120b5070f040d1903103400e0641500840e5845107003412400c0c984d02d081c5001810700c3c001c501000e820005140c0c280c3d181a203811240c03002a050052030b000300400d030017050755aa07a009020303120014201c0c0d80440c0301c0d640a004014001c480108214003054100c42c1401390407500400b05440f596806440380308580c99900c0b91141070300c240c4c2d40301007502020100c05041c204103079000502401e1030070b04100740d0805e240104d20380c01c9918011300b03803e00c1407141181c0c0505241d2034082c1d03101010540722001c154002000d071080301e210300c0680f0202c6254150030402d42111020494199108208100b08000d950344083c8012005040c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 545682347 1250 545681097 545681099
    0x10c0207051009080a08030a0b041e1808030421030606080609091006060905010e090f0a090f05030a08040614070e210609010c17010f0b090d050f0a020f012c0a 70
    0x1a485c5800c0c12940c040c1d94400000041c000705c41a180070b642d503003a90990f0248520620a820030210404680c2c0b2000169980c0402e040041703054603010a070382c3c0d0008551902c1c1e0516007400b1080d500c416101d2041020000b4015085601a000c1d0718202c560a803250206036940710140504c0d45402400142a4000e860103840420000e204250240c0306681d9980e818a062500160100c80320342d82a92084c0300500070480a543c94400c0681d00641900011071420901c0c42c15240040140c24000c00d10b01012a1060b904d50784060a40c0c400c1340648000e0085020b442c0004004181c1a00e2032000905520b50a44a030304200c00030201c070410340070382c401c0210580300945041c00340c15200740d1100c0e5100e00341755800317542c0000c42e00a040710151200c00301d54507100003040d1600451240000720000810b6100b495520308401100a54211040d0b50702d40c5240044261280c2028004a202e6468801e0b00847c9500c01c4004e25801d8981e072045449040004c0a0041d99030741d40100039034800b08641c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 545683453 1106 545682347 545682359
    0x80622090309030804060e24070f0203071203090302130501050d03030b06160b0405010e03031612150807030b01080639040b0c060108010c0207051009 66
    0x4000480d2080e9103015240601c40d030f03001415291000c1400180707250008103403515018110b40b0000c800407400582c1c0710748009107080c1c0310844004d2012000091140d040d84220a000070121003140d1f65500301c00c42c200d07111803421400610400380c10411410b0180f02c02c40a00310b03240c41480030f51f0401020500743d001c5440701a04050700d406015140b9150103007210590852240d1040d000ca5840c03c00100402d020740c0c0c21500c9618051020308030081c04015603004400c4840c07459110780ca84881141d031880112601706105917110400c402c0101c40c00e60301401000c0381030250100c540f03542802c3c826901d05034821041c2d038000c0020000c051044420401c03804540d10003841c41714083c0d05201c0311803480c119003401d000500160120b8103488143c045c000c001402c03000c0b0751442e032b00c0358440c40c01e0703c45080010b00075a020102c207016908e000105c41090300804d2403c0c0d600956295 = true := by decide +kernel

theorem cover : BRFrame.Cov 545503597 545683453 := by
  have h0 := BRFrame.cov_init 545503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 545503597 ≤ n) (h2 : n < 545683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
