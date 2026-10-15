-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4335
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:17:15.913158+00:00
-- url     : https://prove2.me/submissions/13155d3b-9673-4d2c-9f9a-f1335835a32d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 779496402 ≤ n < 779676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 779497652 1250 779496402 779496407
    0x51014040908070809010212131508060a0e06030307020d0c060306051203120601410a120209010504170a02040501171f0f0c052d160c0b07060203060a0f0510 69
    0x459003401d030448c0031b03040f403e9001d00403090191820405502c11151054a00b44590070a05150701400701885801002c00c03495a0329000b580c01141c158880f880c2803695600d002a045100e4031000a601089007000c4030b017481600e10141040d2251914204200c3d40c5442c2000f00c1e0b20307490b1048441c140c0c01002030b082c1c40c041240040d9080803060509903410031050251007103844401000010880e42021030207000d50700c80c52010000c0305540304a070703d40812007200401000100c602c4080141d0005a201c0030390744140c0854000300f0012200000807000b0400f21526415a282c0584c070480c141400072542c00c3c103001402084401500c02810303403191034902e16019401041c03110003a01d541e850302240000c042d00503400d80c00041d9942c941e4503035128401c0300e10041000340503900c3c900c128141d010300d03068440c1110080080510b148440d040d90746060500c0c603c15030000c0200072000308984040050b00e40107107000e48011103403c00c2c25500d4202085442246101b025805a030711040c42d40b4060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 779498902 1250 779497652 779497657
    0x702011503120c15050f0114101805040914100c27050a08030a0311090d080f2505011b0504060309381b091003020c010510140409080708 60
    0x144034100001c011500713449980d00840140f000c83c08084d1160100302519200049080c00b4100520403540f04c2a56000443c21200c904030074102444907d442e0503120711002d6110784000c21000300244414299850102066116400381092511a40308241e400303079140c1c000e00040301616a034110072a2070380b0007206004023000b4503064030b00506800204994a032459040064403001c401150b036501c505a0090481e0301d0340b0441041201c045c0b02e070301d030340d03645001880c0d20450b000402c040e1070302c4090824080521501040b0400140305000924455100d100c690b92281e000320020031001d802040124405402c86081400140341040305014650196108409144c0122401e001c1040501d0007a9510030b074641e040e001c0703072103211484e5034015000001c2030780c440302c11400100e0640500c10f03ca4243c1c01181c0c1d060348141c14810386140c69030300c60350603a220601c2c8440240010b080c007140c2a000b5003250701034089041c40c5600500b1b01d03400e02d4000d004e013095100c1d821914100a030348a111098 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 779500152 1250 779498902 779498933
    0x111070308073f0f0b030d08060a060302070813060c0c0b0304030e10050c01150e0c0c030409230403080403030c09050607080f04051e0915010e010f180e040b0702011503 74
    0x980d02c12002d1240403c0344030b1800400c6100e840000c1d000c040104052424690400a20800152504002190720390115074030480d070780c500b001350f1107a07001e10f410b02950080114005411040d1407000410a900c0700103252540d0041c3d500c414410f45036030b42c8071841e10003140c003d0081145d0081303640442c02c01803218440ca10b114544141403070514860b043c01e4580414a502807401e03460300c2840600121850243c100d640c5d201c8191030401a00c0903251240564801c0030000b40c0d40b43d084503100800042001c9508444080c0b1107040d00c1d040c0b901900e10941070720140c0000b8945002484a140500306000944400130074070b0f400c164040d550715603241d00020059460090911000856443d2030100c0380101c1030b4035a805c441807041c40d0071700c441d00400503c203444a01751008200c00b280d82005080403050070a00e092003007660051400c0d909689502c0d1040710541088100046010740d440700540283d01c0361b852200b4a4071030715001c9003031320007502d820500f090748290100001500d8600d0a95803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 779501402 1250 779500152 779500247
    0x7080601080c0d090602250f0f0c0902190315050307050d02030f010e1b030c0d031805031002090405012c18060406090b0a0908031b070203011107030807 67
    0x141200380344820151240304c5030466510340c0102c3c0441040078140300480039901d944a0700e1135210041e0716030040b10b200310300001d001410450701301c4043c44410000070b0050100c0701c90542d901e00780c170a100403010040c0040c610019203000301600415440c0c000c4041120310050043c890b060400c030400034190483e1070100c0c1e05201c1c440d4030007041902801091115241600602040b40010500041c0e0a00340c0b02158800c1d0029103103641f080d03407101d40d280300d850303010f203007100500400c2c2c1c2103040621280c1d003240d9810b1054542c40c0008036900d4006000c961026141881142d0342e800003907007007181c0c0302c3c5020410040c00c62901155115503000903801011041004416001190043e041c500d06607400c0d140c142d200c003940c01c144001c0300c0b000c94001540140802030108691901d0882f0300000e06080a00c0740d01da940c50324450707444020741e0380945c0c0040082101415a054146242d400208100d000c0703200f8400144c40c26001703074550540e100132100c02030110f802000000740d4400045408074203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 779502652 1250 779501402 779501407
    0x18040902031b012006160215070f0e030114011e08030301120201090e040c1d0609040305181e04060b0a0e0f0a0e070f0905300705120c04050f07080601080c 68
    0x107041350825684ca58020f111006403585041c941811000b200d5010b07101e00c2950304c20440692015003031260719a04c481c0600d4807070041c0c2880201110031000f240306669041d8244140d030381080141c813483e80e040f5282412030100c0f888148a900c0030440440c03003101d0941d0014001080132409140744c040005205161021006403181d1081d04c0c0c03a10292419210f0188185e01400594140d05410021034969091040c2501e4401c00103490040014002401c0040100c1c04010128011081582901c8010150080c003254805032031914006009928899418150009440c1502808450500c07031559a000840440901070028000400507800d41044002c038000850344690b81e40b240c0202a65500d00404c21040d80700141088880c2c1c100b00d105070003840c0e100c03481010814840b0070100b8443c14407060040001602c030304144460340515000400311148070396101c0c000c01e44048a1004071401c03c5641ca542c88148404182201c0341c40229010b01b02040d82c640c050a04a580004045c0340300e403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 779503902 1250 779502652 779502677
    0xf150903070b07110904050a030c05030f1c060e01060c08071a0a0209010e0a18050a200a0906090608061e1504210b01061b1718040902031b01 62
    0x7850190356502c90100d800020803100100551204000702c48601103a1107100c1d410513444035903e510031640010140b003e9140304000308042841902e4140c00f0b01200b0b81c1e12046540369270009590f0811811003200d10300032010480c6491140d215041e1080755541360111450b075500c461007540480d02c1661302d09190aa0034034407124141601e4450400c0030700158803410044000350074000540c00341e9128008402c403c0c0030306408142403481d03d02520202041d15101c4104140003014042804915003c42003003a4030034000000090074100c2c503d56400ba2940c1d950700d0116020441802003000043c010341c0807501506e00b12110f5105600755504503540c1340303403e0000442080c2d10200c6c19240a001050410100c5c00e41800741b10312068480030011040810b0b40c03002244a01405402c09120050100050005d46050131400a65202410a022903803234481c4010070b030044095145000d103107420051440c10180255820780d507019004040c0c8218581101d071080403400c0d0804d0400c06d9411084 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 779505152 1250 779503902 779503909
    0x330903130f03140705010221040f15090b120a0207030e03150a0c021903080414060907030b01090218090a02090d0f0b07050310030b150d110901060e0f1509 68
    0x2000502940d0070448070a490742c54100e546024001e082400c3e50004401000242d030042501ca240044500c0c40c101000c2102030a81080d001e542c00c14010100960008281205500100340b01d4a000751980c43d149591071415400c184103440100d00e0721240e80000c598403060680140c0702c07091207400c190002c4000500460300e0300141c10f80c20b0481c403100e142800300610031846100c880c4120ba01c090071400700c00808c0c440f908071f41c598000702004454400a0213000f00100c0c129444d55540c0b05541032410080030f46540c1e8001800140e03034000c8041c0000030861310b1442100e00c54203680041200c5000e50104000030141d00400400c05507408020941c40c80c0c0d14042c0d4150601c1c451074110311820a141409030030388400410720b406122042042c041404881c1c40194101c1ea4407030301a07042581e5000d0410b010300000440755410420001c540000c0082031000e41405030000e49003403a840ea83c954007203500b08414840c00b0380106205c0da44029034202079403040c400800300c0e840e052401a0b0b01011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 779506402 1250 779505152 779505187
    0x605060307060c0b061f08011e03030206220b0a2a1b060605040207061b03020702010c0803040201020a0b04030e0108151e0a1a0c06060a030b06060306191403330903 72
    0xc4001003c7d0f000602160800010601e00e1038404c0320814032150440d80e0180d82e504025100003881c42002d09a00301540f41d54219400031030703100c400203809003040d015078009810b1030700204031440d50100d03000c4c0801440ea01940301c0d64010350384141c9040f1403d01e0b0102d1484c00200b0540c0d103291180d2020940b0345582c0010300c40705100b0400040c59491300e1840c01301440c03505d440142090b004000c000b0250380d0041620001e41c0d004000a81d480d01c0368170041c1d140c0020568000e0182d405201000f0515800041c013000c03240303003030305d0b2a02c7c51303582c4240c941c40e018034401d0841d41c0030340d5258001c12011101118810101c4014140b00501c1d500c5003198051080d6050464503020710003e80985541000d00810790441c0081e241800c0303150440d510200c40c1c0d00010074050003014040001020303555003a595807126419402e40801264581248501e1241c90400c564000d2049410790309003510f80880702903040038100e072811030050f03a50501107102c001c042c0a81140344003c0c4500000303c3c0e904140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 779507652 1250 779506402 779506459
    0x108010e0a09050f0d080a0c08180f0601060504050907020f030d0f24080d0801080d0503070309060e2811210d021509010912180f080a0605060307060c0b06 68
    0x7001c0701909030000a146c00c4004201c0b0010600b4000b0040985411426150308800401d81e2861814100c00345249810142018600c240c0f0982c400004c1e07654200c1c009209843c000e54000800f41c1d640c0c01c00b80d07901e14000ca45800640c2c0100581003000c01c0c00e500182d202c629a4a0200340c40000c503a468030392140403441d0405c4402200d41c108840c502c100a82d071a203031820b041000361b562426900c0780d126001c41240c2c1050140000010791914441e500440c0700382e0340080700300400040c04918a540706100400c800410070f07540c82c542c614000400803604010b511410300100d00110900380701d0455000e0995400030400285138801122040c40440c0c1c00c800c40b41c0c020a211000103825a51500700904030386190391401e520f50000c18046c6154485074010350505031180c80401d05c0140b03509400d64401c000030b030a210340115440350013143c6a103019001d210244001c0d03e0310f0040540301d03101d601c070300d1000c0303810015100002a202030007154000381c010080c0b840540d00c140303400800c4c0a02c15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 779508902 1250 779507652 779507683
    0x122f1804020c010b120d0203030601120f020c0c10020a2301060302060c0a030e010f2715020f0c010305010e01060807030b09152e0309020a051513090b0108010e0a0905 73
    0xc031131140b00c0c14000d00703c401c00c0721464001d2450500c060300203501c17840003030301c01c0b4100a60700300a0140b41c081500044a03924801c1c1003155201c141c4860207848007003120200744103521150400030703030078800200c1e21491500118070515403000c8142100f504120f0300c640900719520341000002607034030000070340384032500c04015050a41d024078004100420703800f030a81c1030104011001c1c03034095104070a08508112091261b030340119101050102201540c00380702d0456040100b581840d60100384035800c1040d0404907840c0c0c0c1003440c010f42c103440c0309015140112804500400020b480356141541140d02414001001415440407482002044403403040c544840f4507055100e0502d18080340d403041c02c40d5200200000007400140721104412283c03020140c841d2084000e55a42981150040c40700400840c0c201401008103000c03900140861040c0c051800c1000500840600420350305220503502c481700c5a00742000c140840d1006401e90420a69404000000440401101c8082400c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 779510152 1250 779508902 779508911
    0x61b010c080a0b0303030f06040e070e0c070507050406062102221502161401020c0301020d0b090a09030807030203130b28020c0a030f1101050106122f1804020c01 71
    0x480d9840035155001040d600031780c810001c10a43e40e00c0603007580d030440d50840300440d00c1c100c01018180f4050785034020311502c01d04402842a0580707100024044a4400d4040d00d1130300e591082000b04440c803620519000c0b40c402d100300400d04020b5840013040070000c05005040405101c065420320710309204512070a1940e0034103000541d201c544100c5000003a2008104640750103d200d000c920103482601c041c2c07003e02d0f1802441d603000703101c0302e45105005002192201c104400318005050400c00d6603001e000d6540111300402c61500807540242c0d05a2a40f01035070700d9501007100254401803002d004a00c1c43e6000e400003c1e01d41ca8083d00905607101360000c041c605c4250036a01021032603007402114410442020b80d24008a0b03004011901401c04001661825205031040c02451149400c40e51901e400429026080310410b8120707004050304004103415102c00000300c00012441400c4c0c04440003d444a00707940c88000d04039018980c1c0c0215129002e00042016a00222000b1000380d444 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 779511402 1250 779510152 779510161
    0x10e090f060a0b1813080a0203040b16031b0302210f07060c2c0d021203030a2304052d07030b0f060d03050a050f04031202060406050c030114061b010c08 67
    0x10144d60200b001e151495010ba0b4140380c0201d41110b05892002030500e800819409102402841039034020a1030304080c1d5500c1800000030412500384030f03011030110f485d0724103880a0040e01010345603070542c580c0042440d501100019611000202c940740228002040b40500c080a404040d05103248a64400308e2102030704d5078040d200310849068071940780d650706040030b10601981280301e544e02098504101c100100d00203d601c4000c0d4006070b10755440004244918801594490b80e40c040b03966464940b480c01c00d0001e6a050308040c1d80141986d4000e0180c61540080008004005102048402c81d0200c87c010300c9428044a40d10030349000700148100f107489403c40c01c00d264810000c58400e1503010343c6035000f9085014100e07029080040c0030814000c2c100e103034001c442c0a903030022800504882c0c0c09030000d5513650122021a030300b60410022440aa480c007060740e042c5c550021620b450b203046241030284a410003045c1071000110500c98264040c0d00307100b00c005040c990b640e014103e282 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 779512652 1250 779511402 779511409
    0x50a05042d12050a1d0a03020d08070b04050318040902010503061c0b071d040212040f06020405060708210403080105010e06042d060813032f0d0f031103010e090f060a0b 74
    0x10441043c030b0b0501c810303d425403540d21b42c0804419070394100d072042245003035070400000500440b0700c01402c01d030a14003800280000040580303a060b002001140341c540940382808241e03034610100034046030b024004560f8030720f801142d41c0401069030000000c800240c0c1c860001610095444001083d00c40890240140c1211034521806109130380079407074a47c0c40e0010303000400300100301411040c0e0700000c1000300041a01241c005180013132109403140d20074103044c800c59000715051390114185501c6010440c0b00030120a01c143e416031a255802e81c6043c1c01522521080343c54554060b03001c1102054001407000c1c80792007150420801051a1226404101c1c1004150440d000344150354080280210100b2070190715903a06203003035203060304001520070a200340380000515011542d5401201c030725000405084070301084d07441240e00c0c0a4141c080c3c2c2217070791628140baa40c2c10100b0040c02042042c01195400c076004104481d190790290601904002058800d048010b8442296801a18 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 779513902 1250 779512652 779512667
    0xc070b0f1b0c0d141e03070b06121209012c06030c0d2406090e01302f0108040605130c0608010509100b0d0c020f031c050a05042d12050a 60
    0x400c0755285c40f86901c1a940d503e5581c0a00d0174000e25084a04c1c0000d20b15403154078000081a40b138008407801c0312418910441542c028003803850000340c104501c000310b4a02d608624902015500b0700c2003000e0000300034420700d5400244400c50340c80c420401445124903511a14401d012049810a5207000101420344104001e6010000f000b0042d201480300c03004e2070040f40d0450704a8200c1d4003007003003030080415508041e07440256420003141c04074003d1050140002168003441e900106448141c40e52143c20751100b2001c040c002203c0e4000030700004d4a030762140b03411022106d4a5146081d01d41d8031150341c14403a03044803002440c03c03001080315040041407940c100000680c0e1001403030401c40440a01c0c041d007020082e200f500d41c503140d11028000d010350110420b40a058035038031202c2080c0106103035041c4086242607451300740010150640c51152601407503002c81d000c80d0050417070103040c0064120b13030121600038061549281c0051010f00782c0f015050001d40b503058a9100b800e00c00f600c0d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 779515152 1250 779513902 779513923
    0x203060906030c310c020312010501020111040b0d0b030604030c050f01090f1209090c0905030c12070e100906030b04050c18070c0809150c070b0f1b0c0d14 68
    0xa600922a0829654514103c0c010021100c00c20392000144c1d800d00310707a000040c294100d8034919001086004a40c0030004012507414030903000c1840c0d80e100d00480c00c0312a004410303e0f1204040c00140f08110041c0c000f044000e0180c400800c0c001c808800080c00c21006a400702d005c01c201081c60020803000340300c2c2016442c1e41310b0003008440a9030311160842090180001e0103001ca1480c0607030600d002d400c506010300b074100d80400c0700501242c005007a16100340130b000d01c02d1043c9262000c49103400c000300580c0d03554000c05091414a401141c0e603000f0b002403c0310f8506030004401194442c0f50344240002540107002803a642d0802d0304040f414520b2499a0b24000d2a00302c00b10841c941e051069560407203501e25000141880c03d04110209024100000b41d004030860041050081c0720005000301a0b029400e8494090761403004100e64401c6144142e0b050006104004600c219140030319a0004001d0942d840400411300048036a0314090707084400084541748207164000800c00101403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 779516402 1250 779515152 779515159
    0x90209011d090117011806050601180308120705042115050f0601050f0c0f070503070f211103161e0b3a060602011503120305040809130203060906 64
    0x10701c110880401e0280c6014044c00400285090824814038401d602c1218030000c2c086041500c100e042c50484043c106c1a901940007900c40c00da108200884a001c52045a601860032440c019038104000001034000300120140708090000040301d2600c0b004034900000c0c0642b00b015582d07080d21740030900311841071441802034901000c2000d2405001c110f6504100c090070030640f80c00c01c070b92841d441da20801160407550f002d000f00c038200540340080c2c0307401600c60440540d1076554590f0b0042100510921a0107100e0854403000716215422800c4900410300410b5440304a0100e00f01192a0001c0300c00c200c100e14900c000c0410200e04200e0514a081c0213185c600c00d209071500f10241340390f0041d40c1190511110410074001840c03a03982d813401003072181d01000031a4401150800c00100003600c01e04016500305414000c2c4051005503000c2502e501c010100c5049000d10804c60051100500403600b09108004420072035849041c4001076414200015a407464a507043c4030314104007030b028602 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 779517652 1250 779516402 779516447
    0x702160617010b04030201050921101a0108071b0812180d03110a08060f043e1b070e0a09021e010903080703030b0603180118051c030b060409020901 65
    0x47c2c6c0d01000f203d03d01041210280e10f41001ea0702e0a00d60318041d071030010241c0c41221600e4500d540300740c10143e1a16820b000414034404440015581e218003147d2050014884007070802d41d421080210181890042c240c0504100310401301d0f406040b01550428810390b291050f4461036442084414144689450207201e115002d6014000d0782c00f6240240c01800b801100144280c1c035080413440c20b150005109000405881e021034100fa8000e1100f00c580000ca0700f10020500d003944503048000b21410201850104c0c02a0304076203c261951003544580070f0001c000078551a900d41c0313680512140a400030b00940f1901c100500e522420b0322405001e00040d0480d040390303801c1107009048a4000240d00c2d40c400407494110014915182120b501203000703c01e000907040e18040043c030507844500200243c642c0c403001c032141270000010082280e80812000d8030810744503111210060761508000c40c400100e00d00044507504150030825081e039001c00c5154007581d1200c0e140c0c1071814140308210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 779518902 1250 779517652 779517659
    0x2709070609060c030c0503070b0f090a0215092d031005010b04060f0212030a06230f01030c180e0a0b060c0d0518060c0604020103110a170702160617010b04 68
    0x300749100c2071044000380300c510a02141450301031450301d02c4040c0e01400380c039903955540c0783c0b0842821047c0c50050000d4510000240e0304540000e200c05d425800900314031005020502e061415805880b0481e08100107116440c0206c1005421701240b028601111400c0c44172070060501d011021120755003807504040041101c18080001c036000d860782450800310328103c0100591421400d4100380f00b00c2e0100004200e0a0311043d4040c0081e21805100700e52002d085d140365514500151552076030004150f484a8503a44c0207600004a00e0014280009942466007200f000c000d2141d0210020030144407c1050180c01880b6101c1d030324a048440030b0520105519850303844005009210074010002004040440700708100080e000008094960303d041c0300c1d408a40740c2a094800b280802d007002c10505e00d4541917400e40f0840c0f032040d540d15025200041558040040c05003100302507000d0303c115502e15405014150001d020b00d0740314208a4a808a403502c9050741c140d001c80b80c41c140030711050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 779520152 1250 779518902 779518907
    0x4060c030b0f13090804090b030d090311090406060909110a1715040305120a091202060c09040203180604080c060603060f04031805130f050f0c1c020927090706 70
    0x6202101c1c041e0f4040d041e90a40070710002c01448144d6004e0305501d004200011621a55080180c04a10903000da444207402c142c415200620140001800d0100d0025030409609042c1b0034141d020340202c1012941036170b141082c6044440c000e0041d074441256001030205070400c00c0c00302c001444c040c1566140c5901c990727052610b81c00c1650419000300c103284041401d0601c20000d4410b0360581c0058144181003000840300241103050007201c17010b0004031020b40460000c24028803404260001038644a01c03641048006d40c0006e00c0c0080100d8410007031540c403081004094820343c03042c41035070364640144519919124000b02150302c41d07407140c02084485250308025940255150800c05c1c070244000a40c007010241c01e42100d6006170342079604940c22015a04210629201543c08000c152180440c13411a80e900b12003c010070401009450042d88070b440d90600341590800e00103003840400c40002da10008010038a81c0200f00100204444603061030003141c000e070080c8001e1010b070780b624801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 779521402 1250 779520152 779520169
    0x6080303101215051005040525050912070902040e09010216081b06091c0e181306020c010b1c03090512070314010e0723060a0302120403030504060c030b 67
    0x1a8a514846103501c0020401c81001c81c00d6505003c403401e000030b28000407081340007401c0384500c41c455803c0c04040360f10241c40300c00000c1c03200340529030780c03008d0140d8100a592641c03005122a070410a061440303114200c0c1401804054019002c01681e903d20f4614042c81c083c00181071010140d1041094100c451210365604003003c2d486080c0a0300c5d00e80d09282444d051030408a0030035107005190400c0081c00300031501020384820328104c042d415042c0101120702c1c00d0006183c9400bd02e00c14084104030b0340441ca03065001e51105001040d840d103a0351000142d80007555200000c0e910741003207000a14040541c0c0070401c4800e800b0600c82c6a054030020304c802214071420340540410703d40241e20450a0140902640d08103940034600750007030300e1041c000d00b2400d60300390351806045408141842c44104400d065070000c01c1d50580500311904102c180e5201c40380441c01d1640c20081074010314010940240329078003c3d180001d051032326080040170780346000252003c040c079100d04020036960300080e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 779522652 1250 779521402 779521409
    0x21002270108070903320d030e010605030c0d0507050d0501060305010c081509060103020c0111180604150806042d05060405090d2601150207051009050415051906030608030310 77
    0xd5a40510904117014103071b041c600750100b01c0b00c8000c3c00940c0c515100c00201c400303842c84555400c112071440d010741c16080b95807901a06038580c000075543e43c0b030342c5401c0c81001ca0041c01001a104210790f80c400044050305071510844180c2d44803031007002481021322400c034801c0f08a04240036146000800319141d441c111141d01e04c81c180c154041582648a5416211881c040308002c104d03511900094404039004084060003890764141e01c000a8100326007914100e41c510000070a441071442d406482e0301500410b0b59800a684501c0600d01c01d0f2111285003600d0000e0703041501a2140424132025101c00600b510300580c2400d082c0b0412210000e1050a020150f103810700d0301450f9840f0010080c1c3c0480701c45040084007000105892a0003112011241242e03000c88201a40c2c07801401103101e0701c0b80000001c06d41007682080141015008003450080392010b030b01c4620b4488001441c0404983d0b081e01c2e0b4849070740b0007486904c0d01032103058064081c020007541149015514030020400500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 779523902 1250 779522652 779522663
    0x617060622080d0306030c0f0509071b0210080124140705011e0507020f0a050a1e0506070302030709080c13090f0602030c1c0203041a0601021002270108070903 70
    0x85160400e69403001c124040c245500075155564820b581c010040e1000303002c20b03511090f03146000078514410b0315400c002c0382c101600c0d06000c0d64580c002a034141380124292030158206200890059072209610118039942d070702c0f43d01895041400641d0341d42000c1e0910b2041002c8030000760589600481c9502c0395a070081080341e5903c0740d914041d4003410031884006801e54804220741c03918a00350300110303c02e91541d42160f03864210640b480365610f685100c06415900416503100c0403c42850300041030703414514400d9003030030b0641e44e44e61800b4412034004000950110620440c0740d070240b42c0704d0003408000010700d6203031007000c000b03001c0c900d01b00300010245940e80c070342a0030031801e0201080002d400020440d01c074a4179825042440d4022441e070f03406942c9841119032810341078400d8030b0080350004102048a900613486011040d8043d103440d05500c00d042104080d100b160004010070700c00015100c20101059450414903000007035907034144030380075040006075603001000004907034010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 779525152 1250 779523902 779523937
    0x40b010c1b0506040312080f010303081303110303100e060d03170a0608100903020706030608060f15030f07080d03020a2a1203050402012a0b060402190906170606 71
    0x50164444003407095200c0c0342c000d540454000309000022444500814050701e440005a1b00d01140300509942400002d020411030380c0850220041071310300800052280c10010701d44110100303031a00d10b8004650002e9240e498881c24809004444280c0d500000d0607201c8440c000110ba9002e0000c24400c0e6825071445080c1001030b002e00340c29046030000b451504265030f404040700c6ca08002408602c0c0f015005071040007000121148640300b250100c80d030403800391000b0344130b14400b40c1608401420603540407182c41d4030600c2c965401e2188017440c0000300000d2003e6407810401d1402d165039041c44605052041c40003005164020007841040e08a9910003040066503c6920308480207001002c0c00348503041d15a0b800a580540c4068002c1c0d000b62919100c030403a01e9051001200100b405400c1181d6810010000440f0910240d0b0416070042000d03041c0101100000c0302520894103000c002f941040c8100009504a134803a0902d0309981803a003103920300f20700480d15500c41da803410300008044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 779526402 1250 779525152 779525183
    0xe1c0c0c0b030f010f0608010303050403020d03172716120f1b05011b0c0b0f160804061103041d0402031f0c120e120906040807090f0b040b010c 63
    0x108400c00d8040d103500c41c0910b44034107200d43c500c80c43c0d6009008600101c07481040101700c03a03016007074940c100d982c50798409243c20f00b16800c1c030000943c0f1b44400c07402e000c0742c1c1103d1110111010702c080d2044012031010100701079003a810400304a2a0844c1c2c5040380c01401622440d1520540740d5800c1e58a80b9070410122440c62030501682810349801a10021f081d10001c00711010011034241180d000340c2c1e5030b01c4200f4500c48603100031503482c81c1c001c103503503d18042040800c40020140000c0b4480f46100c90801e154003403283d80103078000c0c00032110b038180010280000e035000310340c007104404010001d600703050a0440c3e00310030701d90014081e000c003442034000804643e410001841d0402c80e015500b000b1121001045019141303c0c4202d00116400034010110314003e41b203000368802240b0000d010341041e9441c00f84455000d106a00e8200104210114107802c0c20403584004001402e00001e003454030405400c115103000703031903134031490500300300201c03607030740720311010032031604141c624201800c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 779527652 1250 779526402 779526413
    0xb01090f03080403060c26151804061d030706021e0403050604080304061b030509100c051602030a020d11011e08041106160b0604060603050c040612060b04120203010e1c0c 75
    0xa00e0701c0041c040317400485840308140b44002c82c0f2401082c00300004036440c0950740401a1109009e80b40d10740002d5036100150120b24141c00000c400300b03180c040185c10301c0d0303522041410759211030401d031010342d00007074203549038191a81c01e4401302e880f0f84191810241140e46003502c580c0c0c060005045444040046000d10400b58009104403e14503404103840513510405005410308035000903886c000e12075042d550350124041e044840701c080d0703036513440c20030401441e00600c0c4100b14181e030144190710b00f05005840c4c0a40005090703000d0800180c0713241500340010038015041c103440b2485814541c174040440c0d0810170039a0026489911402618508004260350b4010900101c0401104040752818010018185400b40b14152418006e8070380710101034040d60b4007540d000150500c100404c00400c2d204030b00500d0249450000810559640d080291568110390040b80101100004070800c61500740b00e0901c58424400142000036105030103400300c01da904299809020444210608002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 779528902 1250 779527652 779527667
    0xa170f01200c03040e01090c39150c050c010e0321060117011d13020a060f0302070c0b03150103090c0b07051e010504051011030402011101140702010b01090f03080403060c 75
    0xd0280328407419980e4a410120152131482d074454081610451114204400e2758014080092410300703a100c0c804000142c03801954240382d003960302c00c0c0f07001d140d400301500c1030091100048003652007076141c10020b070b00642151a038101038034469204000c480c940d8151520749110207106022132002e150360701c8005a50b800d520802d0f00c1c5004420f20004190000c441c0b0006211080d01501c02405a0f500500203011403040e00010350b001707140001c10411380b88542c80c0ca40380c030b40c0945005804c2243c25070701c01c001d18400b83c02c0300003240f40100c00c001e5111500e900c01041c0303980900c1c00344118611030300c03840410403050099101e04180000d41d80284001080100b0980b14450201214881706103441c41c000c2c001520212000d0045028030803225105002d1101b41d40506030207545561190390043d1036000042100030725554840e0003100c00501b0440c040b9200e52426000401c903429204c00046c081d00702504580c0114881c81700a0010401c60419213060301c0d0322500016514105501c00e56004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 779530152 1250 779528902 779528909
    0xe0f0711010f0603150c050c03070602160f0501050106080705030f0c1303140d0908060103150504020f040e070801060611061f030807200402191d0a170f01200c0304 72
    0x201d040c84000000c110361740c0242e10701003040c950b0400c61094901011138851040650b41c106c3c42d4820b100d4200070503c1a4002c0919a80302d103090241c1c50f20f203554440d41c0c26564901980c0b036075900ea004210780c80d006502c075075000843d458102e01c1e6162101c001d602e00140507185050b030080c08200072882131190443e44001d59081425400403850240e00e03a95200391644031000022600107001508403000100c6a06880d0b00503440300301c0f8080c0c80da03881c00070700000f0b0090781e103c41d54028100180d11303184a803011a55429000d488a01c1c20011920300f92041603200c40304012064554820312440800d08a4100d0492014894074800490303c07816007030720390340028012a0340018480b0410408185021b0020340c3c9a88501109515200700720881c050564110011007204c1961540f452060000400f4080c8c200900c8600100d450f0104041d00d190740c100005100e4000707050140204100306054401007100d000384140707101c01e2100080c2c040e01941218828002145010645000b0f1050b036029 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 779531402 1250 779530152 779530181
    0x131401020a0f03021c1109130506030f030903030427050f071701060c030804060912050d060f210213020d020c010e0c0a0b03100902070f060b03010903051914030708040c0e0f071101 79
    0x103c007280807003234018441580c1141c400c0c030a200c643c118a24011050b1003000c000180518209440c181c0c9008003c030584119940600c4843c0c10724031102041e22405021f20780c1d0000c25903403032038040000b03081441d0a91649110000a0004002d040da100039600710960740351801040d039494924151003e0014468010485003207901005000c6512030080c1403101102e91041c400b4a40d43c01c48031240f589140201d85049000000000300c0324840c840724070110b480600110145049200100100d8000c0c05005400d04c0e00003450342c001440900070845684014405024400080c10003c0e014401ca03118420100c0d50120000e00f01c1c5e884441101c00802500d07400707554409491030a220101054041103800383d00c3c02a8401c01414140b1565040c9a459203d0511b008842204482044582451034042000600c6001d8000c060750015500829181c5c65914090600b8503182c42d2515041d044407215840c8001008240021800242d0304034016060040020b05480300c040c4c050318045540542 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 779532652 1250 779531402 779531419
    0x10206060108060604210c2c15010305090309040510060e032b0203040f0620150c0c010902060f040e160507021905060a0c0b070f090905131401020a0f03021c1109 71
    0x2300d030403001c6244240e2210ba6038001106041810b030102c07400606540c000b00c12000041d00381010350003a444070f90000e40c108101d03800c3c04001c02c0050309884c2c08071011141004200001c00c0b400b50040001c00e1000002c4000c2c081c4d0007184009414440302c0e540c802e04030320701001030541c80c05000348110780281c00840061511252150b1000e0b0400824880050300340361407003001101100c001c10414140c00074001e8503403603500c4010f14051507400010080440e5540c0712040d1005070344a00c0144400314424000c5520385203004081301c12020010944a40c500c0d040c118020f40541c070008483c00c0c80d41c1101c10b21441003001172031005412864000641003e800100250150b4001c00c1d407091282c802c02c00b220141d42c500030122203500c0030890400100d03c0b006801d00c00508141c020a50080d29608810659181621140c00d14dc10144189400c0d940c00502410b07030319404160019080564242036241100382800316081010380d03030904400940d908548030b80340d14464210307026650300624920 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 779533902 1250 779532652 779532659
    0x204080c13110705071a0301080d1206093b0303040f110402041d01170a0602070501020c0102130905060f06181f181d0417040503010c0c02010206060108060604210c 72
    0x1652100c03030740500711b1442d007900007217071403006020202c1e03041c0d841a2004e050f8070720300c412050329041814084011010384900c401b19042000b40300d810341d00c1c0e00380e4188003140d82011000e118540c05080e00300c44984d140140d000c6600100104a9412036806450504c0903c40e038101249801030200800d0351040c0001000039241d40c101e00003110440c000c0114404030b907a50702c603d1100c034417029000da00c150080a907920210f00c00398060a0300501a070005460901d000c04082e08991021500c8101804150001d2215031024480c440c0e100d4416240030320845282d0340011001d009485088180012a00d5900459200c88600c80f09044401c0c0c80c005541c1c100c0180175113000311441c034111200552920014a060700c0880781780041c91000308481842e20756807200c00c014400d60800d489240e204000008064038248200d09080c07a05560390503c807922440020300b00800984018100003800c802d000296460f2412201210414504041c0034001c860b20703170580b04c6030840050041d051018000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 779535152 1250 779533902 779533913
    0x30c06010f03060f0e0c01030e0106050a0b0c070b040e06060d09060906050610080114060c15040c03170304021012090b0406060905011a040e151f09090204080c131107 73
    0x80080d03030710603e000c0c026801480d81c682c08a80704405030001951100c580c2c2103295003c1c0d0b00c8502a203081500204100781c440307021964510041c4c2c040300c0d4203800050011410f090902c01d14018003411002d2901e420314066200b1508500074002c6481400c0c0042c608480e00200c0c1d0200541584c4100180280c82c40c0e03082c228001c0808035900c40c064035544034290281c9100b10302c49410303160003111a084442038402031000c541c1041640307485a110741c140030381c601c40da01642345125510030650488818103524001c2a100349140000031041c00c24018880141c0c0c0d901441240c0d00194588807014483c228004009400e0075000030b42070b00c0d422414030013445640d4202c07070203036000031600307011503642d410f9069581c02e20100748a042e00410300003403108801c003d0055070071406d140d1211180205e001c000030303801c0200d21540a46030311405601e00c1c41039041882c1400a02d4070060850402d03141c014603e88030165002d0403072241903c81e030140c450540707031383c00b561202c5560701040b40c86002c51f1a1a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 779536402 1250 779535152 779535179
    0x160c052d06090f011b0207090203060301140f0601030f0b0d0f061e020c0d410a11010c02030918060607051507080a0504080d0917180a081b090405030c0601 68
    0x100701c425420050205601c4005c00080d810304c140350350041843ca880d00700300d00029080941080e0b07040d501d0b80000441003241c101300c58020a400441041241010000501216800c450808400c0e0600a580340c1d00c0e50382c8400702581ea070b0070000f2043c0e004101d10301540200b00d8000c44c40072420340020580940d140702e5001d4a000d4806c50120380b0a06110310040e0351840040b19003412808802c006810070341d82988001d000070380c18402141c60311400808014880d00201c401800040c0d1070429062241424014142b1000f02800954940328030300c2c01051882111032601071030400c055001c03440700d841d620111a10305800c10155000309203001c0e01002c1c1024150b400742c00180021000c10302e02c80132440780b5801a940100024545550050443c018210902080c3d9102c0000312010f5440c1807944c00400c8042505a6005640016a000c010314681d154200070940e40c0040c5416a40611000456240600890700b0100d1540c882c81d2141c510710840c26924020701810000080d03405c00b203802c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 779537652 1250 779536402 779536423
    0x106080d080f06031c0309020315060f0901050f010c1403070b07020610210f0c0e0a0f0e070614190f0906030207050606040b011412160c052d0609 64
    0x45a04a40d210180002d04103181a540240e041c1c20010b00c91031540c1d4254009240b6480c0f900700850610309076000a400c014080c3e140440101c160000c00180346442143c440407044126904801541450040303402403081c0c0c50802c0c1401120040041480a0000c072a199500e044040785d0b50380540340751903808400d050307500002610a06010854040040d80c03038100b43c8002d440d14010881c082d000a03410b003110351038141c40703070b013610b01e6441e0205400f184410f025091070b40300d14890f81414814841200c500000300040541b5180200c03039040b01c0460f04204035500d0f480c0004043d00c81c01c0050f1a144600014502e2114490300800d0085810450400300c9a80d1500d441c100985c0d03916094050f80314070500140140c005a00044079071070142d001240e043c02c18075102802980c0b45101480c560300540203103041a00c40c400308600c10101c40301000b180d070031900d000c3e842e84456540b1155a0146802c15078400344641007148110040d01c41002d461500200444015040c40343c400b03500c8102c07160313 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 779538902 1250 779537652 779537657
    0x1d011406010206010b19120e011d071d0c090910150905010203030a2a0c1b050603070e0f0a090b150a0e0609120a15151202060a030e0106080d 62
    0xd03415800450400c0c102c1c3c102d20841890984a400d2007410103001300303040790a00034009040078a00201c4d104039015022450000540320910100c2a040000d404038104075075404410148000d032940c80c010b141e031300e0382c40c10b41d010300d51101c85100815002e01e501c02600700c0d0302001000386601322900d0743c03002ca0707055166490103140b500a089440c11201d0141d90b001d43d100f00f01240700c0640e154030452080c8800e112054031103128901d00303482880048608400911046001801d0040c05080c600c024180d28007420485490480842c01c070740030050407541400070700604100c035500d80a9005c5c0400400401582031151980140402003144c007035140d000d0403403a40a44000d248840c00c035140b04c109070322a0310100e01c81c0c0040201c142d00441040341c10002d2084141b40c900800c10a0007c0f083c442c3c0c440c16070b9002d2005c441d2003101c000b00900190000802c40410080b1500d10200503040d805643c0c0e10355400702c3d40700542c0030b0b01c840808142c0c25864410002841440881d647ca400070300356 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 779540152 1250 779538902 779538941
    0xc1c0c05010201060b030f070c02030712050708160608100f150210090b15010c0803070504180603020a230a0e01090b0910050f1f02010618090f0b09011d01 68
    0x45004900f04c50132802144030810040010035401e241c14181264030079411f11300411100f50070380c0400e080542c035900c071149540b40380d020101044410b125800180c03040703e001388100441922000e070701c40d031140300321001d10201c0004070344441980d400e16400b030300c50802c520128031342d07034490b40303810190b99041e800050086010038a1243c0250207426000c60f0484564941a250401b04481c144e900201c01414400001c2d0081c00281c4994042c0d80302e8079044e1100d07030315186403901c0882c1c68210f5120703d240c46850f00005000580c1c554002c1015221040704901d050001180c1000c44440121036483d40310030700941c0001c646c0d00e2001d0450503180c400300140040c1c0c00c044103001c603040094508200409070341d40103125500b8801c0341c16815110080c104426008944400d00036800c03040740d03d0006075101e040c140600c121a007184580b0720420b500c01c0181d0a001e072502e040080000c00c0c02800030b03880c0008180e90007001d4001240101c19000d20b00708440041c00c00c0ea000300080c4600c00d400e208071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 779541402 1250 779540152 779540159
    0x30909090a020904080a030b3a080409021b010f0b040b0f0609040e0c1206040201090b0307020c01030906060503011112010806131b0f350d110c1c0c 65
    0x10540c0241e66074040d200c40c0b180e480310784c2e40700700541002c1002c3e0100340c1d070381d0241003441e512002e03091091008002c0500c480e207408800c0008007400850740080d00381070ba030f4400303001070004c40441e001c5840b400e00040e1192480d03030030103402c06241c2184150641c00d260107503030000c43c40c0d881b1010902048500b08952200141408003801f050000c41c5d80c80802403140c615141000c0d004070850908050544036a84107420000c0d1011021528415455211400304021540c1001c1080050b260000c0050b055151100c8001d65070802c001303107241095100c4070243d040004a400c254058035008001707214491260200030819000303014101088565070000040c125004110305004042c1d0101d080b048140a881c3e00d480b001414100c40c145d17031950500040c0a4003c989038201401c2c0e100029203100590428410070214289a04c2182a181900f010a51180011041540406400c0c0300240441c0080c0301400c103401c6202c0c4a810841603200c840c0303001080900030f15070074400e10b4410f0a0545 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 779542652 1250 779541402 779541421
    0x5090609061009020c030405120a060b030a2f04060b0a020105060f061225030501060f020106080d0f09090f050106021908070b1306090506090705011b24090302030909 73
    0x65034840012141c0103018020302c103c1d90010420300501344100e80c54195598040788200d0030448e102c00d090341001290070304118141c000c2921004007140102520321254640e2110255005510001c0030926540070510300c00820803075402c240c004000b00201d40e40c41450520a5100440c3d0100552078840010f000349011b0031030540c0c095026004c241403031168140c011a01001810703001564018a80491301d010790180303501d80c0c001c8955000700d05549094006040c41c84030b041c4560a590400c0001c2c0402e140004000241507620701d0041e100b03c054010136105004c00f0380010001608000c6907403101c43e1142c203c28102e51059003150700103203848040d100c2a500350031000b42112010400c2501043c0c640d140c094129011508800709407801d42e550300c1c03c44101075803c8915030088400c02842c0c00062210030000c0c40f003806c0001c02540d03005c418042c140c0d20220b006020140403000f480c0311084c0001d01c411444003c041c100115142410301950380d070414a8860703c581c1020f000038454a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 779543902 1250 779542652 779542663
    0xa0b0f10050a0320130c050702040507050c0d0e01050f1305090907060f030908120702102409090507150c060515030c0d05161202100207081f0b060a0305090609 70
    0x940010602020b0840c020004650400412203190300941c0401c441a40d0311780b5114400a8044c56100c0503a6800e40b80f0600c01030312001000401031007024450000c03a001c0c00319800e01c00c6070107480c0c11036401c150500103998a00031085809034402011400d010450200203101d0207495080b2600f000d00e941d0701025540e640d44600590001032502400f80401c980a0740100302001d00c50b260840c14075181124a0401c580c00700d91403001603200c50b0803c0303602e01070343c0f0821031480900e1081081c410501b441050509809200da1810701e41d40301124030610809002010140040c41e46003101000c8a003002042d40c01c08a50913542c091070103010800f0f14448540d4800801d40280c00303042c0c0380b01c1c3d9104001c103000001c0703c207444030300901403e0f0002c0c48200d16107030701910300300b03002c0c9070444641e0041c08070103c0e0030b00c3d07184250352060000380000c603000130300030140d810040c1101404641c0202c580340942840044560020400f0409a0240780c040c0c00c100d104010340000c5030141d5941c079107500e030f031407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 779545152 1250 779543902 779543909
    0x6090f05040c0905041e080708070b18160b1e030106110c0306060f0904031404090608010e010b060f030a06080303040b15030703030509130e1002190825020a0b0f10050a 74
    0x2042c0c0340c50015031443c0e1560f00540c00034090591f0f2420120300740c8640607142e000107401c58084000e4800c00144824800b8600342c0b008006008240c024054421690080c0d00c6016101d070845000c074203040303000c0814a042030f0181d001290592a541e4441d809006600324162581241c01740c2d114012450400080f40391064a0003048002c1d20298242070156021024105400708a0000658041d941d042c900620050800c540c0000d00c40d464059480d00f12258400c075400c0e164101400c1c185c25954020a03199200c40d444000b6950b9150000c440c0b0081405501200e25800301004000c01d20817003205843c402c1c18100742d03000302000300d242010f84880361800000c6c00300b82c0c1404500501d0601e80798000c1c40d0a50303104e0000300305650303104151402e015022404c510503000181c2d20f138101d0f8064010218415103007071495950500442c2e000002d03044562409005034003640d0235607868070812a9100154000001c607005080000d01c021048508480c0c907072900455400020361400c1288031b24049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 779546402 1250 779545152 779545163
    0x90c022409060112080904050709080705090f07030b030a0c0303052a0d03150e0f04030f0f0c0f0f0614010305010b100c0b060111030c06070e0d20010306090f05040c090504 75
    0x1d03a03003080d00341c03940820104d10584440c40140080340442e00c1c4c0e4403034180140c0c0661100e07040d49140030840340c9000d1160304541d01030b09094041c00420414208010b801c0103144c10040b8a50400b0b0001c2441c00402a002400c031442804000060503040001040c1c0c0a540c202c00f0101da902c0c80080b4282c0b01b245100da40782a50000f140c421600348694080c4001d508584e100d030907181d94441907003d07903000c143c4400e90818005001e200030540c1210210010780003e05140317290380012800038204c0c0000039400f43c4155910139000303040044a180340500380b50b200004200009924101c015100310900045035558682141072040c0c3c504002d044680d038502c1e0303032502403238062a51040c107808000303130a503070511104034046c2601c0441803000d40103401b110801012503207082e89008000000d5400540d000380c070081040804100c070800c04074403800082000c81210b4060800480080c01c2c194044001c241c913003036038160a04401d4014034080d0b40030700e0400341459111541c0600f1640d040d1402040e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 779547652 1250 779546402 779546413
    0x9060e13030806010c02270f070f0801060f050f030906240a120c080607020d0201060518040b040516090905010b062104030e030105041109150102030a03020c010204090c022409 77
    0x1c5942c41154040c041c40e101501d004040000b844180c0d078800c440729644000714269030f04004480d0451223045600049901e014119820b48510180034400c041c001d00080000c41e514104200d4010022900e42075180d05d4410b83d40e1070404026511814141d80c1c40d2160030b001c030324075000489000c10b000c400c2407006003060b034060b01e0610183c0b03100304141070031101204254400240041c041c0080c40c46002c441d0064001c480c5175800085c2158000d400441c85521a600702014081000301d000340d02c0b0b1b0340940c800c101900c9500f0103038602031038078142100c004d64113500030443c15002d0704852207083c8100b000340460718010701000030500592902a0b0740c410350003007000d02034a000341320a40080c003070300704240580ba0803000f090079200c046600b41e0703a10380300c4040c0d0111414a0010a54000000d4959065003003a0000013500ca101e841c0d41c1000b0142c002c1015000e29400f07504a40003020118410003140c0909100692514020005001f600042c2140c1c1c0c100c21110402c000c1c03040404e1030283c07a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 779548902 1250 779547652 779547661
    0x206130803070f0207090c0509240a0309080c0a110103150e07051c3801080c090a081510242a0b0402130207080d050402030a02060409060e130308 64
    0x85409001d00598030461140810020b051b600c1480342404980b41951a151743c1c4000718207121074111500d4000c0004a400c0840c1c1210b10703000d40548140303545519020650561a003000c21480c05020050113260148540910070013680b2018851001020b88051020b410b92541c0c0c021000c005100322802d80e0031180c0010205880b0300001c10725540c2011031200640c00481c60042104d5000700e005000200c5c5ca40f035003803d540e258000c2c14000c0c00000301008940b00301c00008242502c05030005860140100e1402c0c1c081e030741c220a040250040e40111002c1c40c0c120555042441d100340c2d018641c2e801650004a541880320010340700e030740c0012a807003ca50703280c00301c201c52036208000341c0008aa1000b107407402000216808541c218085c00d100e18090900f0300411080f1420002c48500b6144100044000602c030b40054801d2000444000542640c0300d00219013040d24034100250701060000e00801c1d203400075031040090703030129801040c41e55909290081e05148820001d008a0000300005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 779550152 1250 779548902 779548907
    0x603030403261c1a09010503151b0708180916050703122f130504090f020d2a470a120605061b0f0d0e01020613080307 52
    0x180300c902000c1420740703405141c40d110703624200c01070300d00908561520310144c03044034413506642010104a81402e5154035180009030307600041c0c88410401c1d5826070026491803040c082c2501954100b09600d0355030b00b10792230019900c2c5d1010b817005000782800c1d0400b02c90740c10f00403a5140300d0501240e000b500f11b4100c000c01d41c0d2540111604a0820a01068203000c1108500501080840280594030403150400364600c000c078040181c00075425050114466a404072074005048400c1504c0000b0307410301c0b03410000460b21078400040c0d000000c503120a0104103d884195001c0144001000a01201c0751210380d14880386218184084808a507040500c081030f40e90b540030f400351203194084900d0108213240c90440c078480c42c20b60301c00e004a00d40200b2030f0440350023614140d50715001c0010b00c0c10580095a00c0c052026400d940c9130010007001e41c800c80802611408003001421140341d401c0c0d80400800c8241b0241960340180100f0001c1080d05902004041c140c80d441a502419651082800c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 779551402 1250 779550152 779550203
    0x141e0306070507050f1c031d0c0103090c08011d100501150809150f100803130303050c10060801021b010b01020a11060f18010e1e0411070503031305060603030403 71
    0x161145d0180382c80c218514075007040103042403400142021120000e0b10406804c45654000040085800f01d031b00021650010070b0b0780c6c4400c80b0074240040c148031281881c0e1995912600804015882c0441d0351a08074900c5250b4041004000201e0b801c4200c400b40c40c0d4140c45081c840d0a90300039074a0081c04010b0301610050394090065800c43d240002281c0707410300500c80c15900b8041c1101c0f04018081ca204503862850007400301c110066141480407030a03445050701521018042104c00306652024460070301001c0700c050032101d01440079589481c0014000e5003c80180c081c090b00d443d0407000c0c0540180a910b0014038160083c207541005921060000c9440c1541c6907032060f01082000c00d07403403806000e000825290341045d1401c041400014000c0994150500d01c2032040702404034850540c003000b520766000c00c3e0740219100c901200d0460305d074084c10100a2003400084108440c1d00c801c0c80358120304a000e00e003145c03400d07240c0303000345500c910446c0030117010760019505128141d01c0c514603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 779552652 1250 779551402 779551417
    0x3050306120109030806030609150a0c17010f180b06030a09110d0317100302061c091203050702061803121e01030c1d010b03010e070c0b01141e03060705 67
    0x4540c444030008169a00f1205108011400715030741d07105104041c2802c1009540c840140350040c41a691025070803c00c48030001c09601c150740c0c0300c1d031603040341d54400e602111b10a8241c4a0304102540c540d024040c1d00e483d24010920080540701102d2064207281c080c410b10448003070700c13062464031005044006086250000d890346503c07040c403051207460300050418036601a030f6503600828411041d440400101405040004580400601c0541e8540044030100c1c107003610394010030300030303045040003030000300c500a042000440d60003466150103401407445044a9401c3c0e6029550702c40501c04094417409609040d03a01c18004101c5c030100301b43e40b81d41c2090a00e10302e6076030b250703010065000044c804d0f081101d650404540400802d4105103910070088038400440706298101070301e40c0301a020503c1184c4c0d2049036080455000341c003c10b061003080740c2010519080e581c40c3c600c03200404800c014200c2c00b4400b08040038001c5101c4213a070003450440200a00210389801030100c403603401a28 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 779553902 1250 779552652 779552659
    0x609010f0c0b1305010f09080a0c210807020f070609140f0a1d0c121501120c08090c0d051c18090605040b060901020d11150a06030c0501051603050306 66
    0x81d880002c20746076001035210340041c2e601008058141d20f0600e00707540c0c0080e10901e50909110b40403000629950a440b0200c03240d141c00600e801e40e608050310320115050001600f40d491085103080306078441c00040c45203481d50210782118040e6528150350303524502c6010002070f0580300a0229030421840c4610408006000c8800d071403c8900140d01004d0a82c0403440c020106043c0c421680032010780b0546c80702440240300c2c2490304485240d60316040c01884013110703040d5414514000d80c011101640c04c900e01031410031222039039800142500005a0321045140b0554101000a1500d1008610015444800781448000c15140100c044685106100a00c48624481048001c04d03801d41002080d075803502140691401e4140004c0702d10010100b8000d100400000030181d03000561440021224a00070401600010966040c54420001007408680b03100c00e000c1c10b6a1260400b1060f00c1c0220003035109181da6400664503846010b0341c6030800340046202002103805040590303404800503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 779555152 1250 779553902 779553917
    0x6040b100b0d0203160e3303130303060f030b060402070305040b0d0603020109080307031e0c050f060a0507050301080c090c0906070c0302030c040509070e0606090901030302010c08010b0310090f14091f0b0609010f 93
    0xa0302008020703082114510071140030030403049c2c14540c0c14050f8a00412003811900f9081d8110340342e140c2480030080081e4000d07500004d07502d08040c402d604850040c00d02c1c070f030107980fa1083e04501901030700051000ba40000d100f02070118100744080210342031260302d5114001c0c00052441c0d00a00124460f11328014001c04170548400700c0d00500c546200c1c940081c025040b1440d00a0342182150400ba001d217007001401d10041c80b036007100080303c010758a0210343c503807601d0b9104102800e59100e4100c0c8650089408280041044041607010040da0b1084043c4c03a0b0346030000051000300e890458002c802a445000101f00f48a0322104a9802c5400a44000c1c540714210b808210300352001e0f4001c40c0180c1d51440459000e0381d0140c005400350142c40d0f0301a1940c282a00c11600e018454059404915943e80440045699a90100161400f180b00c2e039600d92510031255502c840c1041038041c000f1311001c40e11812010203103d90b25507500000c100d142890100001150000513190300c46003484900d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 779556402 1250 779555152 779555239
    0x103050429011505091011101118091509040804030c0b1207090501050f0f090a08010209030d030902010914120609060a14060306040b100b0d0203160e 66
    0x40810200040d00c000011071540b41c900d410b21001d100e2400e010402c0700c02c0c08448120f5868214180d1031000f07a10b801c4801c80c20002c11a418904500310307a521140c038000c81d04a030b8544810140c001e05402c40100d03ca1492584117204c049581102c46111a190842d03641740d0500d040c1d17081e0380d00640540c9900f401d05460f942c68201c40007540c0c100c441220000f00341d1203051544241100c0d80030502c0c1c609003403100d00d0607001030705501580105181c0880e011a0032611075948000b640c0009000504000c0d6060755008894001d5100d000524017902524401e01d5000e4000c0c003076812032036810f0703481c0c00280d840c2800301c0d81f242d683c3c102959802090402030700c401d0354003045558020481c00c0041c0006083c641c1060040f21048920264410741c004108101d6580106030301d1303441500a00600304654500b0409002601650000040c2c0f020200c1d510300c6e079007007580c0074503c15455802c01032452540040c1c240c0385149648901544103040613004001c161004000101d0504007200b008002d422 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 779557652 1250 779556402 779556443
    0x9020304030c2009060102031215040b04110405011803051207110301090c08160f170c090c0a120203010302220e15100b270a12030806040f06060e01030504 68
    0x803c050800d99080200480292070802c600c144c000000340011450001446448103410000074a0300c00309484807090303200705803500d40114003e180010800c2000c44440c0c00d003242150082c2c01040c1c0040d208801101440c50301c00d003000103994025004007410003949000d0f035800d0b801440c2c120b071001e2850581c400b05440902a04580c144503c5400e094103090911035450550301940103189400e00c14001c00401000f003030b50300c09441c01188400380210b00c5140302c9261032000b020082e0040062010000000c0300c81c0040c1c618545583d440740030a40d84110418240c0c0028013000c1e5100c045440c0050710385984072001076000101c00700c042004000010300f1401d201c504440b00700b000300c403501003003807901884010001510041424905014000300c03840c00c960284040ea0040341e803031058851031a56081e406030020003601d070380c480103601e440c50000c0c201001624058022420904080304441e02030041ca002d450090b0744801e030003090140110302a00c00031340244c1b04403000c5d192400c00070b41f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 779558902 1250 779557652 779557673
    0x1f0b07060213051f2d140c0d02031902010c1727010b01080c030f04080c031c020403120804030e040906061a0316020118030507060e061f0504050c030109020304030c 72
    0x14130031140035861441d681c0d405880b8443d10b03204880e0317200c20040840d110f40d6040790100092071461801c11802e4641504125591040c55107090443c8906605803140e654000f00821010000300840c020008028030f05901f41c611317407034024010406c6628000e091013406502e0710751210320794080703156071041c5c0035075003030764001403000c0452594442d20080020351b00702c4020f541210407418010310314906000e00e11142c01000e04010309608000411058940c41081580c0c2a56808287d4940003603048625000a5001c0c2c8012a40344440008038416903000d0001c0e070344110f4040c0c07500740f0a10b107144201710040c5a0001d00304d41c00c0340d80717140106000b0320310600740c480f1400c0841e000d03640b8100000d02101d0b4004100c0000216030401c503410000c841a800c002241591504000352116941d29052002e40308640c0c03070a20520801e000c020580801e001e040d081e06031400800c030929a1248103102c00c1d034508590012003107104000411501d2180c4e4029a4440d00a160400c5e06180e16a260311101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 779560152 1250 779558902 779558929
    0xd11030d060b0d0b0607080a0521250507050705010e04020c01020c030901090f1404050a0b030109050703121d060703090e2a03010321090b0f031f0b0706021305 70
    0x31040410340c1030080040d0722444e07640e10421103c0609200256540114034421f40d208a404c004010815030301084843d80b6400c01f044110090034401c4c64441c0180d40d280c00c008203140000d0480140d186a150300400c1205c0905810078041c14403a424400152070742c219200701c158000d907003000300d00d416070f400384040d003241e88480c005140e54011141c0010a100e2554000c4001c00d07044100400c03168a0b0300214644c1c0d1141900c0224040c0c0e1201842c00080a401d61501d81550030415150704000c000301d00da034240da04c82d14022a407207000ea0003c8514142400c8410251695000080700d946806c5000d80095403003461310164154903000c1280c4507441c10f807540120030fa51680b0010310764003801c84900d926a0100c0c4130354215132441c0c4410f00039034101d00e02d41e041300765207001e0f1600c454407408803a005055803509880c0d0f900d0704c0311404017803a441150303040c2d001100c0c20041c0c000e031000c60072540c1c00c680e03c1070b10050803c00d0544030780c00250f2000e1581c1c0d41c02207400d080090103132900306081441c3c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 779561402 1250 779560152 779560169
    0x170a0b06040506040605130f080a03120b06030a091a06011d030f01021201031e0f030e0f1215010e13080a0e100e280b1602041515110d11030d06 63
    0x141c1c91001001c0c07d84984a4000c0800f0440c00002481540c8001800020b45600340c50240000908800d001c0001d008245545400800010800804c04c81d1070b0012000244206a16528010300b059002c81410041e140c4600181e1900c0701c0b00000e03c202203048002c96030082c203951460030415111401ca9001019032580d0306490b034010030501c20a00c6420308208424040910201c91030fa0354400185a40d0074006e00b40410b03100e81c0d00b01d075120041107280642d8060404000501141403040e0b44110244450301320122420000c079905821404e0140241d08251100388055590f650b4402c480e000f80d46441c0410200f803c09200380e68a00c0c03d44108075a0a441d081244016602440030241c042c914142c2c030308189168103054038801e00c680104880c0000d8219440d111503150981000c40c41c1e410195105081c041521045a0369090203800c4800e95000403a42d10303c43d0a0650f0301c400e2001800495820040520002c40c3c0038001102c1c6910455094074500b88425a4650860700c46400140a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 779562652 1250 779561402 779561407
    0x501060804020901120c05040c0c0609200d02031c121b1103031317120a150806012d0e090601140105040b0409150e0c0a0906170a0b06040506040605 65
    0xb036007400c06525000d40900210140f0301d4a441e101ca21200f20f061250300e002d6980d840e09103034480c0c030408007080003d030300100501c192009400c119110000f04240c525111b2004005000949407000145181580c003070082e20744404081c019022807441110310b901440b03d90848801000f40300c0c07144c040c42001403812035107008a0002c008000c0d02c0c6040b40075446a00801c2400111201402c010b6000c5501c203050148003250100c14045070b0003524011036040301060207000c011011500113480c2e515400003e1104c965962a0ba5070717546100780306082490501c5e100704004007c010381903540d4511104400e81800d5070303600085554110480350300046402c0900107101034400701c007005010490901c2c1c21420f0500302040b4003c184101d1040508059070740070a40b01d4002d2f0441d20b040100030040e84091907282802e22814a0703407001d0b400c0400102010004180107006000b600034191050300c0c0d0003841c0d07541078030401c0101000b00400b98405810300001800e40d481d20002d1004c0c0ca0b15541d00c03034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 779563902 1250 779562652 779562661
    0x1050f010915020d02060c251b090b040e0303040b04060b1c03050307030e01060501090b0c01150f0e0108150f0405010b090903090a17030307050a0c02192105032b05010608 75
    0x24201403000c2c0042d0f0940c40300300001a40040c07240d14803048c0404191201c0d07048155480d000c02038090054170f40009806114001450320380d00c0d8050340c1c00390019a400d22064000307141240e100e10048800911a5845002040c0803444940c8001d0540c20080c15125250030100c8025a0404603550b00710009100002000000b40c0e05020340c181030146000203001d4075041400103054442c26000b41e00a000003c1000a41c00e203094000b242a0900341c60720580e01c41c0c503044e00040c040514050911492000750000132494800034103038000c0c1400342c2000c00140c807184034096150310060401e4030b1644d21507840c441c00396074a001c01030144400030010f6a03a10b8554051009072495684880c040940340c20380c11f88500d101100700c0780d010b44145001c503600c841808003031300c0180081d44065005400a0b400e0201c00200e200a0303000c0d5482c2480090a40d142030004d2604c520507150001c001e07800c10300801103901e2038040c0c00c00101c8103490003209180d102000e10422201c003603124000003503c03e002d02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 779565152 1250 779563902 779563907
    0x307022a030109291902090112050c0703020f030c07090c0e090a050603010e03210403180b0a08181c0201020d1b0305090a1208040312141b0a0801050f010915020d 71
    0x940c0110f81d88000c0b40c00391900c000c1c1a02c5e14103074040d251601c1e03600012140402c1c2e20844a800151051480410503070901c405500c00c01c0d008200c044003d84984c1d080c00220345800010354074050603200040c14560300308400c52018000240c4420244615000b8601c020b0341c81c05502d81c0300c0c58003140c000446181c41000c041c251000c0ea40107181c0e82d0820400c07215484510301c201581d101941054101d2900c46245c21144000c8207821208400150903020411a480f44010988840395a0f50725035541c07102c511a5988110411801c221940000e40e51000e1401039201407d01d0b500ca4000103040500c24400e541c1903881d01c500710291481078052504580b03826100e0071340c0048070b2400620920080e541c921080c80c000304e24034001d1100400005040500c140f4035049540c6050000344000300c0c018010700c20012043e00c00c0c07070350a2466900c0750310344580c0c031050b54803100d01a035034140140d20708418040c5003a201161181003200c03108001c01c9003400409400000d82165008180300c01405a00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 779566402 1250 779565152 779565203
    0x1b1b080114072c24070b04110f010804200d050f011103061c060b10020a020901051c030e0d0804180f0506090c0d0e0f0f0f030307022a030109 62
    0x20a03c0d0b5081450311200300180220418152034095600a1000306440c50301c0b2540500c4520044402c2c030b0010f4250200302601c640c941c001c41c82041d0380e00114140c60301300200d901450001c0b50008006400180116070354150955200d065441e24400b2036440c100030801c0c0048110082d205075203d504420400c580911580010400b001e4015066042c04000142c120815604950540c1841680041070104542c00903491581c01042000c03a49c082c200040d4850f041650264840c1e00c03e42c00029050030280c0450380300c041e050a441280f02c0c55940c041e12008030041241d0303045001940920009800a00204040d1003400d076090508288401003d003a00c0c181ca604e100b0082c205018450f840e1104171a0319000074009010540365440083d418006000b41100303d562807055030109140d020b4081109192b840c0c0c4030084d036000d8280078aa070756a034070003074441c5001a40143c00c1c21065035001c0c41e440d000305031030b403e40d58002c4200000081c250307101c001d41501d1003104018900143c1074000304 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 779567652 1250 779566402 779566427
    0x613060f0303120506011b060b03100911040501060f11161205210912160f080c0d0809041806090506060108071d0f0f030a0c05030105071b1b08011407 66
    0x1004e0015142100008028400d00090550b00d02001c2c0f0240c41001400c1d000000480e802074211065146840000c40261200c400203651380011141003180d142011300a45050302c00d292202152407001030012100e15120007031003202c03405000c87ca03900c62601c242684e0000e2200901c110745000c0c1d41e041141c1000c84000c0304004011076090300d4035002c6148016116080b10440d04510208101c0c140d0500342000e051540c85010295400030800410704440f81003952001402c0325403007081c3d1000d000041c40c1029001d401ca000602082d03020745840d8100c07903000001c240901c02440442c6c2e550388296500081d080740c0341d81000c020005156445070304217901002034a8188091074204140d11005459111000d016403509444201c550706e0300806003c000002404441c05040b69003024146100d103070091030301c2035081c940030402c12031088000078400b030a44000d52000d6040d0380d0f100c601400a400503400d404000c0000020701c02804e21031540c001421f415a0740c81d44c508200000e1005000301f5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 779568902 1250 779567652 779567687
    0x2803021c06180f030c031b03110607020102120a0504060209030f0f011103010509040605100810050405010b06090625061d07050108071407020a08030703020304140a0317030613060f0303 81
    0x81c00801c03e400384540c1169018245254100001e0030102c0300c41c540c0075006440c81d20401100000c2642c010110313001b421540c010341d441ca4031003000480c00d07441110885515600c98601003070082c1807036031001d42c210748500e40040c5010201d8000c642000440074070085140c20440c0c10104482c001c0c000c2e40141c0d00c012040e2803556043c00b00051140e28041c001070141540c8200207072900380d03285400009405440c003103904049000001c00090300301110100e03602c0d406e080140d20141803020036544520002044281420111003902e64155044041091402c0c1d240f41d010340414150321905159040c034009583e00c081074048000d20b009000d51003207040098140802000c65440222118200e420240a503560032040c0006541041203401c888058000000d424041540000003802110384520701c907402c01c2c4584007045140c0e860f500c4040c5c1203011040c3c4984124a41100440c1e10440c0244040ca07909800c4500b101103c40d04d400007844031008107010300030700d50800e483c00004005407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 779570152 1250 779568902 779568941
    0xd0213030c0e010e130b070309080d02130f050d03050711060706020c0606010c0224070b0c0c071703030a05040f12110c0429010c0b0a0207031106062803021c06 70
    0x2811700c9402c40d41380f4070000c2c1c405682c00003c61b011902c2904115421508507040035151000170707820380000d5100d185141142c1034400c0000420741200448032040312002030913040210842d88054030301d0341c0820000c03680c1a000a488036650703502c10b17000c3c08503d401403030b00607102c0826880c41c40c940100545400e051005030030304940142ea0300c035994540d02c4c8201d81c0707900d034404079405019164025454028884100e0508001c0d503d20000d015140310302181044584480d520034102450b8803400c01c1200b0550010000540441e28940042e50001d1003402c1c0c0542d21581500d034a0490b428401907800010240703215254044010803259410b41d01c122000c00210010030f00151504040c0c07281c2e801da4010b502541407c0ba80148111103d4a4002c000200310385058100d00c4000d60000400720040b40002021200510700000c4071446200040e1118190b03803501d0f0790802c946d82104644038508940100d0220050300c941440034090050441c095940e00c01e9481d20005031505075401c6422500d41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 779571402 1250 779570152 779570161
    0x32111070b30041401091e0303061e141315050108071706100c0b012408090309013621050a0303110d091a07020105010513020d0213030c0e010e 63
    0x1049503894119510003030820352515030f0200313280503002148024052000310041c858407206045001318000d031181da0104000e0343c0b01c49101c2d81c01d500180ca550400c000c00801440a00f102c1c0e004910140c0d40100144810b0186d1040d0005681c4480c03043d080300001c001d4208020758000d40296007215040c100b0b12608000d0030485e060900c40140407078803c40e1105264060140541d03101c00d00241c100b800482c0c19030311048949414032002d030000e03140c0d004940074079920901c6900114000c08803100514a0302165800450340c90780050262400e01580100707482c8424000540302c0d1005c4200c07038a40014516060003040c000c00001100680c00d0404c1d00500e0010b08040b4410800680c1810300241641400029145500a100007400360344d10b0102d441d42070204418401d408501d04017454071541d03951440c12802d072502841442d4001c90f10324490740307924000360003922a2005000005091150004030440400f02c3c5500070f50782080c08840510039901d003030b14000d002d800300b11050310a5050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 779572652 1250 779571402 779571487
    0x60408130b0c16050906030a200910030510110921030d0b090603071a030a0e0105010902071202011b140c030307090f060201051603050604020702130b03070f032111070b 74
    0x4072000011b1001d02c2c81b95089d111500f24090340d80001d01c020380150308621381803041c51b80d01c1c01c0902094619102e1050720701d0040340d150264003002d500036a14181040b0040701440001040e10407003c031b0541c040600015905030801c040d00030305c02e8001c008500e0ba542030003400641e0501520140c001d40149409010602300301d89409400d40003601e181d5507075503c0228080040c2740344103200c8865400e207400061554182c4e0090100c460040b540d090050307601040582c2254415442c044000c900e00b60401042c500400c002029000340c0340d00d8a10740b00c040000103056900481e030401c00b04890301d80a202800303030356103d07001078405030008000314141009420798080b4000503900c03c05807a00001480d0340c50b00e40503240150340c090705014410541120543c06002c203255018001d12410200181000800403500308494205000d00d114200881c40b4040e407010035002c1d402400500c40364060328031000c20818008151b00c0039030580b25600360060031508075030040b1040c07001d029103140091030207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 779573902 1250 779572652 779572663
    0x18050604060513170a0c091b08090f060f010e0c0309190f02030a061e060e0604050a0605030604150f27050c042d02030702060408130b0c1605090603 65
    0x128981032440d107485082800c2490050f07960400d0300024822101d0340c1c40300e40c00103545261244114001018036440311900c0f4100d98852081400c1c5180b40402164030700c6c01140140c0d000b10040098548402d112201e02d403522100342c070054020072003000100b0024006000b02c68200c029684a0761540c01c02620256480c62003403406074004030170380c003d07800f08408018030f0285264050302b90381d02590039043c4800180641c0b5a03550040c1c2d030110404903440c0c00c921030784043d500e0400309001c060712414240030040100415440101ea0303503010114282ea000c000c410710640c0310710050019420500064401d44041500c01e10005050425090400450a0b840511640c00c00b400082142c03a60600525205681401c0c0b030b000780c6064495040903851080140725881c40e00d07554404103c0703c030100c1d0100c0c4421601800160030000c041000500d046005004003140c0102042d66a500c1c0e4002c40307140d074040404680c0b13583c0700c008408040382c001c0c2d0034800144011a4080c01e6860700401294031607 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 779575152 1250 779573902 779573909
    0x16150e0109050d140d23010f0518060f2110020a08010311150414280b0f0c011a100906050f0d060f030c0608100617060103020c0a0b060118050604 64
    0x10303640100410501200080d60a8105196818001036061050010f48402c50702c40f050320400d56000045401c1000c0480c000484901030318a071005c8040188148ac02e070030103440d01c3c1c0d2000e000c0c044606030b6681d81911b502e464514010a03c2026400410180342086004dc0b00c00d440c3e00500910032416080903400f81141e4001200d0390403041c050b00080d0350802c001810317021b0040d000c1004580c0040804078942d040d072095998892003113948000e60b4a100c490300325007100c541c81c000d00380080395070b16015241850350311040c0e03424002a55410b030301399401070b09001c540004c2d8540e21a51860a100251031109050829811440c1450303000cc3c04c920400a00400340c29000071042c18001880d404540140001c48415014030748914141c641d19801d4810300e0001081d44011603a6401c100304d00714200c640c0c0303455500000d55240c14405180100401c03203814181d00b800071400c565030030320070002c25503c100c0e002c14691800307100140250140101d855000e0f040c103c0144203640340da2040728180c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 779576402 1250 779575152 779575157
    0x120e01090909230307050f0106140a030b06150d14070305010b2a0703061b112e0b040f0e0d02120711030c100201050f0105010305062416150e0109050d 66
    0x400c490a0f001c0d1075407084010044c110b22a030700516443c1001036012601b6100b840040305128445602005000d1909000c06060104201d001c10a1882c1040207e91103080c0d01c55510700b018031b13408410045800d5602420001000301c4204030315a41d061145601402c10300d4200703801c00000d000c0440d086070700102603010805e20b02d07080c0701400608014210003190701010601086c558620090004014041c40c900854505111141407042c08501007581c1303100c007400154040d0002420302d55903c00024200384c02541c0700b00d410129201ca0050054100c00c10b0008510307484800c002030320f000d01351541c0d00219040450820b41400c0c107c0102ca00f015002001d0525011903003002a00780349105024a6012003111307060381415406411075480b03007124409402c100e0307036910015019503c0454590345d110401030740181000c288020480480452a5092030500a842100d00440c818803001540c80b401d40d4149002010498042e5090125603038009022040032551038a90710100721240005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 779577652 1250 779576402 779576453
    0x50a0c0b07030e0d091409010806041203020708180312033904061e02060f010b03040309080106090b03070b04030b04020d080c060f0a0b01210c0c120e01090909 70
    0x74240e109411442c0a9518101642da480410010140203d00c082c402d105001c0560342400440b03107080d0980e54101d84400014004c2540d0b5940d50501d190010340400040c140c0c00d012560208807050060100001c0000061144141c0041018139101c10100d2412078808200104170b445c0c6500503c042c001c00c0c0c024001d081c18092048484040720340c0303001d12024000081000034000e81d00607001045000540d40c502c01d0007060043c00c0361a114200c0f5155620765015004005003409075009540c0036010b03140903071000f6241c0110b103082d039400364400c0d0a01c03903c030074842e4400d140a1064000420032501600c2c0f6107869560303144505e120042000c2c3c4100c80c62031100082c403000c03204940d88000e4034016a0020320704106162038505d000d179104a0141d2402210394815401108a400d912151120348007007220030204540142100b01041e104000001c102c1200062001d0100310b082e901907141c030202d071803041c0300041003a02c440e84400c000d5800c1035900408079a80301881c003441d13480091b0110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 779578902 1250 779577652 779577661
    0x3020c0919020a090e0408090a1505180102030c01060b22050307031211071d0609060d11010c050f03030906060d080711010c0b04060605030c220b030705180115050a0c0b 74
    0x107808803940d6100170642400c01040104000d208402000b410b04c0460b904280c0c541c60b4a0f20f440e100c0031485010000c501e041000482220309050140c1002e01c0500c126440e10010751040b17420b541d1142d0001c54800d0000c0b03210300c96042c0d02c4454406801210b016083c000d842c0000195852410748400f0b010310072000c8a030507006110300480d00d40c0d00701c0b06080f10030065640034440b502e00c50420002440041c0413010581c2490a98580c030b000707400080550010401d691181d126200103564818140409a402c50002900912420340324070101e201640d168580072404da400c003100241254400e4500da121100011030200c05e44401e15040300c902c5840e4882e820069407000c44201d00608000c2d5410200000c200941c0c00143c00cbd1401034041d90403d0b00c0600610408203211054444116040d07500c281107100641d00541c1403140090031a03414554900200b60143c0000e0381c00034803501c0d01ca00500c071f85e41c11a201040582090300c3c149181000840000708410040c0000800611811000c90b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 779580152 1250 779578902 779578907
    0x20c01021b0603070221030619060e010e03030c0a20030a0b040f050c060c011b0201060f140607061b030b0604050a06080a1d030909150603180102120a0903020c0919020a 74
    0x40351044482070001b103044e2003005000064108440161045504800208110414001500449101d40c88180d40b844c4200d005656110904040c15050b201c00d0044000e0084204003880046016600c252a102c20003006804200e1604150b1800f07a07000814940005045519444e489030b00040c0210640c1d0080c40d0050403e4002003801c1d50005012a0342002c00c00b041d0f01c110b802d4060010040c0d1001c600000590903207400e0b1043c0542011005010007038545928010029120010f096601c1c0c04070310b42d203c1e411a9072080d2040701c0d03205801d42c000340c001d805100d01c2d1200f40c021158a41410324100008000c1e011a0182d40c00300140c0d480801c000c0d001d1a002444200c100c0c5a00c1c00301e00e090309000d96a60b03000a0343ea81c2c4100c000e200401c1240f13441804088000703e0240c0b41034a50b664880d005441c41c90f4104016105647c204891010401c0002000e80a000c0e01100031842070f285040c001e00e80020200d9441c800d24840042c014841200000e40602c0a0441000350301c0380400c000030f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 779581402 1250 779580152 779580163
    0xe04090803011e270e07053003040e09060109060305120a02150f0907050609031015090e1606020318240706150803040e06060d09080c0c01020c01021b06030702 70
    0x1c8191340c0c00c01926540e0404400382d9040360810303c04001041d00300b11003680e40e40c1580718640d00692440508004181a000904608202242c0c0d402c084290001d900349942e2182c2e0080e0307044030101382800030031842800500e0041c006a0302c1031114508540f02d564503400c418500320030964001900d102458000d010207c0521042c0c0091203035440c010b420440b40c80030444908500c1e000312140400c8500e044415502910f0000d801054000d400d44410001044210000c05003180c2c4001d001881e51a50f000e61025550340c000940500c1200185406442e50660411019500207000600322035144009007400c205d0304850b00c52050112034542981000303000c4201458040005034401880000d03040601d10000f154403000c02c5a64800c03900c0e880703020709c6c001c0004416070400800c100d443c021003c1c01080d100300700000ba2526155441034a181d0141414204c90340040007000c2c03096030140810b000c160f001380050501c140c802000004411400ca403617078414480800031401c0103108005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 779582652 1250 779581402 779581409
    0x7080a090b0a0906051305070e1806040f060c1d0d210914030706080f0705090406031514150d1502072103060303080105061b06070c02010e04090803011e 67
    0x1620341c2449082e400c0984902c403016500517007003c02203484004040c5503600b8240c0c0281c040c0202d6400c1149640b02007201801c903090040e0081d0001440c0d80d014803499004601c114045816002d0038a800010b40d080d4031584420301c0620b070121094107443c3d4400b0680307008200c840e0041b4000341c1c50800405402d03c0f441d07110004c01d18040300302194001d0302490907100203507540180341090f5801c060b0345014a01489002a640304041402c4114a00101c1c2c2c10843c2410564100f26091010604851160740b023956400c010b282c504200c07440314400c130b0b2802d900c0416600c00d03034600000e1000128601503019401102904203190901101d214809101c11403091306569828090900081803000c03c000940d01c88440d01682400601920038202200d9041d04c03500030700e0b03103028100304040d0083d030700c2a0307204c0620400d1100c0308941401540d00c9002c0c0354032000c1c208052400018405410a03600b18003135840c2120b83c00214102400b07580c1190310b9001c510700b1494450301e1045e0926159030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 779583902 1250 779582652 779582663
    0x3120c0d0f02220b0a050a0518100c030807080610120f090c0609080109020306010302040c2f0f030403080d090c17010f14040b06010e0a0e01090207230607080a09 71
    0x2a4840c3c03449050711840e11400032280d9140a1152240204400d91142050007004500c2c2046480380440c00390004d024a0040b0f000e0924154a031400860051495881407100040c0300b00041020560010703041500f000700c51611aa41d460194081030110b00804054400e00440c141442500c059982000c160540c041d0340c240f110464500e8031203407a03603c3e4000c1d400890790710342002c0740080c4144954410710b50010b0040040d40d10790f80a0100a094500c008003c0100702c0264100e202d01c110046580503101003003200b101010341b035009040c40d00c5580e01656a4000700400c101180000702a2814016050f9000504541d40c3c940341c0ea5408181c1d11640d481e50300745a0000c14040190b0210025034020401807051340310310960f444a0b0790007102e0042030700c400000031407501d5205901520100c0d4020b0114001540c540c0241800c0c0c4209900043c0c40b540c00040c00410042904800c518041d000c0743c1e00d07801510f88054180d00d801c0002e00d294100544035001540202d01a000501c1c102e4005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 779585152 1250 779583902 779583907
    0x90711210c070b04030209061909021303080309060702070b0c060406151203261603110903191b1a09030a0c030503090a0f0f0e09010b100804120203120c0d0f02 70
    0x104071030403884d00144410380c1326020f5040050002c4c00c25215901c9800c41000341102c0041c03d051b6024000c1d04107910ba881c40c80064000840041c0e0540300660003140e6075001000103147c90f0b82c0081c0340c800c543d0044450f40c0d0061144442c05c5100240300c035001035000d400810350107004400103281d1a2650b200800011902141c00240754002040c4040d503181005900090070003450b20281002040c0c50740201e0300a41d001704c0c03003064401d0340041100b200070040c02d0300d4100480e00091400c10b07800d10b070444001d003421544042020008140103030705601ca04980502c1c5ca0081c200d843c40d802c10319045a507400c0003800d94060358042c00408041070b40445040b80081d1a0b082c01e50340c9401c030800081c01103800f0440030500707040440f400800c40340c0e151004900c1c2402c00e2001181c0074000303003501c82959260350f01004540d45180004c240d03945643e660b03003101d2505042c2081d124074000e80031415500100106a0310400300d4078415400801d5804250303861003038200110040004038510100b10340302 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 779586402 1250 779585152 779585159
    0xe0706111b0d0f0c032114130b0309070608061002031e07020604140f0f100509011b03022103040320030c010507180801022104080f0c0606090711210c07 67
    0x190001c1c0742030768080e46c100000d8044e01c00d01c0c080841c02c80c4e03080e040800c070804450054004804002c10280d07191003180000d0a56074041c008243e00141d85480007034000360403e00445504c2140c032a48200d00300c40350f5003184d41d20304000c2d440b48118a009480003488c6680c54008070060000c58103000e40c0902090b6a0306d94420300b80060f8001807045074850203940c2003d4225282c90003001c1c070169402042c24540282d4440180c030564440c5011606000300032071038400e1005400c070a04c1e000b90181e00074114a10480380540c18129001880c03401401e018030a100200354420085540e00c40c1c20300707020700764804c04200e2902d5802400b00c150340d1703507007840d0400c0112517000c4005200c181c40143c2403583c8948a006c02070a0340100c2024500b070041040890f4144001001c1d050380083c09484007034a4a02c110300006181d900054001c1119404042407000c2405c1c8007020036800400c80c508220200d03240b0568940394002101400303421241403506e00441c01c0148105c80030f13401c0860480c0e002954 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 779587652 1250 779586402 779586413
    0x308070f14030c100506010f1e210f0b0a080d0f0509031c020c12030f070212030d02070b01141e0433060207060504120309030b0a0e0706111b0d0f 64
    0x10880413512441c10034004c40c178154000c200704051400c444c1c4411803898151102c0e0311440c0080781c4003500300141101d0b418502800c00304010122442d017800880d02c3c4560803180c3c2c0c02d60711000750b190b0086001c01000c0007002c4001c110080911114a0055014560020200c450b4040c180c8080c1c3d05015a01c00d070707008610084c42c0150208115000d4a00d0b01004030100800d20b0455a000318840d0010000c043c4240f00901c020702040b4402805100c200700040107682c42c5402680882e84a1130f40015210140f0440d55603a07401401007000451035030b154035010a190701c00f00110715050080d030701104811541d65402030380400390410043c03821007060b1501ca03030304a580c14040c26212445000041a414404110341081d607a41d92070b400e281c20300d0320a400c0700d1801940000da04210b100080800011070b210110707401071502c00404991062844051424186994051410310119202d03003414800082060811202a5042514500003000c0171a10003c1407a034010300f00100c8519600030480f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 779588902 1250 779587652 779587663
    0x4060e0a06090216030c150c0504140d020109140d32010204030209010b030c0423030c0d02030601140f090f19060513020d020d0c030c17010308070f14030c 68
    0x60010106100d07459840c9250b504a1241c5000001c490102800c01380c0424011604940d14500c0303142e03000f2480b0600710078242207452409002000448c005000c014110414420460700c0c0750445004e150f8000300d44c0060142d2032070b0b1084034140b4861412400d86560360b0840840203580142107215a41282c01401940800404460429602c203240124102c001442500e082d29406402c0d6683d50342802d080421a8200610f4541c000c1c00801c00030422001f10301c0c200748885c5010342e152082e400c201081500b40101d45100074080c81000083da00540e500003142030460f00b40c03440241c5094150404159110200c05045030480a10018400303810038181c0d0692017030b41d0041c00d0742c0100141c024154165070203489942c0e404030500801e405c04040643c000e0240b03903003e80c80103151095011200003034070318454084001c030341d03108040490366800000080300c081010203035001a60540e60b80612501600e90b000d00b4031681240d0000030410314000805440c0300380d804130380d16032091360603295072803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 779590152 1250 779588902 779588911
    0x2091201020a140403170f0d020c0d11010c020d051e0c07090518060103061125050d0e0102100b0f060f03101508070e22050a050603070f12050c04060e 66
    0x842c5100f1041d9100300010540d403d0729030048005d40340302c83d181a800740c0c40d0040100132032880b07030800401c01c1007041b030310007045c10300e221001418801c1c3e8601d901420f11742c14803508580d02e034100000b100f00703d9030128854040c41003509029840300f80c8507a5030b060900c01700810703007850314000070782060f500d0700019546c0481d60340310300c18003480da520301a40e003000144c002d000900d030b440180107000045c0c07660001030001d40c2c046071850511155208041034086840d10500b02c030310303840360500140041441184c46100007414001301d02e03461180000c0d50794160b00c0000d01882d580300b46c0300900e60380312032200b540640300034005070300d486100d01450b16680c4150340022032041d051800103140d05840441080c000d041e501c440900e81d64105040c1d400c030074031328243d07030b170210801000e0454107240128420540003c05000a000e181085042c02124005408580310398803175101000a003d84141a0741174401d10405440c40d0000780c41d010b40b82110300490142e100d4109080458803444480200340715 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 779591402 1250 779590152 779590157
    0x311090307030c09050702030903073012020d031a1c0615060f08010e0703051902030c0a112d0309040f09120906050906090604150201061e0e01090c020102091201020a 73
    0x45e521000d00c01d9989210b2182c0c00c0b40c00d03400581d020010080420203407410381491412407590419429500070314460100c40803148070704104d81650303060788d042003417461000460504114803019500b096103074414212000b841002c81c1d02d51511003550070000c1c8112940d1100c024031071614003685c1649110304a0180400007044600d03840c000911404006d8100c0d03290040100b00e68560002c218082d080c000c00c070809030205401c907900140560710080d885502c0f0344d04a036880307010003400200485803848441042d03078400b059819603400411300c2d0042d1890002c1251280e00b6010000c981140500b18000341c3c0305242a4252000c00d6070750b00242c04070b51250162000e140656281a140c081007801200005a0188550402800c040c4000d0220880040c2982d081c643e80b07a0b07200c0d141c2041820300b44010303511880200a0b0744100c000d15002078004007807c20783c6c5400c1000708603070201c3c1407051008007500c1c2c1c1c007800743d814000c0d812160203071400390001e41080782c4a4040c2d03010b5440812507500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 779592652 1250 779591402 779591411
    0x3010516110111030c030a1d0d270b090a030b0114090a0c09170102040e042003120304020f01200d0f0306060e04090501240f0e070509010311090307030c09 68
    0x8200103103c0d20520498003800340c0d0558440c0d100c1c800141d00024292864179641c1c1c0007081c003202100d00b00103401401d920080202d00c00c6408004d0000c0c4000c1302c0b1401808105220482640303a41c46c900c0c040d1050f680400d5160000c100000d0a04e03503850340301501c285601c43c0081443c21107207016104540342541c3c03c820a8940907406411a1100e10304040040d02141e002d1040545001410410540f900c0c00582015150588070140200999080380c0360900324950100e2014001a10780c0c200500710064801790781c0c032544442d210700c40100002d1084c1c1e19855800e40c02da006a139030081e48910f000080c241c218840a0175980e402040149201103800040864440c6200380140000d803140c603038070001480c52940c14403018002241c1c0c00c80e099501c0d00c8038000007041c80d40c81c200b440c1c0410b0b00c24040700751604108054850741500911f1110700706408207c0d40325004001c0b100308000c06e00c0d0018501c0e40c400c0445056000b80c407429070703041c0100d00c000014048018801350913130b030808a0401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 779593902 1250 779592652 779592677
    0xf2d170a0917030114090709330503011505030406091707200d0b04080906210f06010c1e0b0a0902090108030c0a1b05040f060618030b0112080903010516 67
    0x45031800309105940e82c1c290f48010040c402d090680306d00e504450107081c030031a0180c441300c8000000081c050307081a004070310868800020751400c1c40002100031414254503550400c510a407099141d8a40c200500071300001040c1040305541c0440d26040c0c103c6400304c5207070b6403902d22940d5a40041d9040c0d802c2000c1040039180740d260300c40039090341d01e0010401c0d001d0441580c3c882c211480020030a070b5012100b40180c85054580600400c1640ca0303404032000b05190100080c0500540a408410798130800c508002003a600700c103000e0304a80d007101d1611040c2a401018908141e0351501c02003d900d805402d00c82c000080da0080c3e40e68070320840348140c49030303254120240e8034065004420026070180d1107003030204008040292035044555131035015641c4550101d0252a41e03240c0e10b0000030b648460411520b54031641d209004003401c2c0f14218804c6c0b03940c0720f1014044042c0a2007684020340403010040000340c000315443d280e006002800070b0301c0d00c008240500508150850042860308130f034039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 779595152 1250 779593902 779593943
    0x50405060a080c0103090204060305072d150c390603021e07031812060f151503090f0506010801051315050c0d02030906070f2d170a09 59
    0x500c02c0e200403034020700d10042500011005008001020790304035588040110104005000600207414904003003408440c44c24000d00d103118040321000e00b207240c081000e1080c0061100c0c1c1c00ca00d4242890041c0d0b5204240c1805038a110a40c0c03001000d01941640b03103840200310445c0610403865000e0440d10441e9141000e8007a40306040b4511200c00700e95801d560007031000e002a011842c001d10b0b085003445c64080003070003841c0700b6402464001146054450410840e07019402c110345603020140402040900f1410441525014000d84020701c003805141d0315100c1d40c004004207030000c1790301d940c0034014104540c440801b8015885254244000149021030554081265640c407400380014845400340c004000c040c003820b840036402040100c0340c208000b07030000d103021f025107602411b2142040c1c03401600c2c4400c1b0210304820300441200900303a04100c25007907804000c11301c03050b000d101401c00085910212103440d14040c400301c1000d10640c03000c00d0b884a41e079280309601d4030b0960b07810301808 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 779596402 1250 779595152 779595169
    0x120702010806040504050c0306010902090a14010f031d0709020c060a0203010e040f020f10080906090c0307090e0309060403080a08010f031101030f15121e0503040519080601060905040506 82
    0x180c042001503000c501d903800c02d9402164442d02410a49038464904000642000f2081c0c3c080c458058010952081d1071030b1960130403000304036125a8008040c0700c1400640403000707039400394003407651380c8181d104265803500101007010500c0041d120b2180e140c08900c0000d40242050100a2007218002042540e07544220ba041c0d410141a9418541d16a9507952284c820781ca070898000309a44c3c01d400d055203411000c00103400032501c0d100164940102924a000d80007004034046501590300503005440100e10300080c0c0d01ca20b44040f80e007450071040039143d0712900300c0d183d41100300050b00000b404000e40242c607044039141e032a40001d0340d03038140000c2d4001883c003000c1e195200b00c1107003601c5580641d024002c0010441c1303022640d82c8400c074911848201c160702189008484075200070070048081400d41d01c134201c05201c218050a281c99a0ba41d82c000c030b010362402580220142020300c44204104c0c802000100d0071140b056840c1e4100074040400d601c1118021420030021a91a25143c0716 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 779597652 1250 779596402 779596417
    0x60c121803041205010e030f071203090b062419120917090d17040914090303070f02070b0309010f06120b040204020f0f28020604030f1808060a0e12 65
    0x850809051100c5000c843c00034a404543d5507583ea06904622030013403010f4244038000c21000340d1102180e003070815101c0c1c0211000b00c1003601d006142d4002a040c80d004940124059039400091108902508500700c0c50b8981c261402001141010002420b40003070018404a42e40b1404001e21140141d001e442c641c1d4001840741d02080d20400c21340c81c0000240800b542c2c0102004550010380d01d9003151070600410f442c2581c0300000e402c1c042d540c0240a60814103007101e0380000d0a180945240303481c1c1c0000752841d000c22440082c80106284204442e8019120740c1c900e45540c1d0a069070b060b030007840078a250100c4582018800503104442510002206410800c0800389564a0342004001c0d4400003500000b20380a00004901074541c8010b003101c55418862106000c881c0307070340c041010904100170011507001c20202300009031b00c45c1d039107060402e89050030344c07010486030038a0100d102a034002c55002c0c41964100510188503030000e4241001c4441561182c07000b400441d0024400c084 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 779598902 1250 779597652 779597701
    0x50c0a080a1b05041e0501120305032d0c0c010c080c0a0e03011d0c13090c0e0402010c0b0f15010f0905060f0403020a060c0c1d06130b03060c12 63
    0x48421020035a00000c10b40c8404410551510300c5440f83d000030125070328030382031184007500d03814030fa6039859180c031583d40909040007002480c0c1086030760040c16888000c0000100d254074182102914a5401c9214a042d11111043c90300d8903102c0b200310007581008200c02031660801c44104000c6029030003050080070790844c100d10340180a103096440c030000800d22030701990b0f100c3d41000c0e81003522400c00c0401580c0c3c80904136407d000800c1000c6400d08584000c107161600045100140d0f90048120480300100040905952280016268241c4103140900640026002c00001300312407140d81e8811a080c0040d1000e41d041c1c5030044800a6110300d9803000303d010000d05000c2454540054030009800720721007441c05407a90301083c036455440e8092404146440e80481c200441e00c241038014140c04c40301c03413400101c252070008690101070031140c040e5440e0100840703030850b587c200e0301c81000e0180c101c40680c01e01040c0c0c881ca55105944000e10700801c04081903604c0100b969100b944121031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 779600152 1250 779598902 779598913
    0x121005010320090f0306130516120210030213030b18010b0603070e0307150e0123070201030c1e0206070f08040b010501080c1207030507410c01020412050c0a08 70
    0x560604042e41e20006989a008402070200c074420b0350100005449131160900c0ea41d28801945802d52500800421a15031034024940c10f200341e248107186401c0c25a01140ea40e2000f607440081a002403062505d00d0f010010306001c0402880380102c0081d00075030130102c6680d41c40b0804811282201c072032600e050fa100301c00b0400306052502c41c40c240c20809000409494003244e6a0102102c8402c4031440c030008110300907542e103059a08540c406030a840240d0785e460140c0740f00c40e1150000d10800100905061b5510203a80b012840340d0a0007414101da525014600d231502c40300a56100000c032403200c00030351940e56441c000d6100e01e0041d405940d101249400d56402c10380156229440240076104644c002d01400080c0b00c00d01203ca4025051921700081c1400d01d10170041078108000c038081d1110703541c0c4210b503c644159032810840d4541742c04e02004a10144030741242603114501c0a841c0e03a600100b004195440e076441500102d42c80390045074203000c80a418840c00004c9031003448100d8000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 779601402 1250 779600152 779600201
    0xf0904020f04050c0f0c1005061c202e09030506010e072c010e0604030b06010e011e02100608060603060109050a0b0d050f070902190e04020403081210050103 69
    0x103030450f0ba04205140341d20750509400d010691041d030000c0900a9455200a051114124840c032489410100a50302d20401c600c0750182c3c0b45500804070707001405000040035100c000c040490301c10b1006080101640d284486e2048841d080400c1c4103904c1709d4561800c40e03200d2040b4000e410440440358400c1c06002d03240c2c40c04515803c0c44000400c42c009010018990440c1d6a2003c510400041e0b0030590029160290900040074008480341180c01004204014030204107d6511282d200305d003441c00c0200202c0700e00040b06c00a10b0307000007103940d10a41400a100f01d8000c1502d8103050280c2804004040d902c8101960b6000207880540c2c05030052001440fa80c681900032651054002c007000c50190b21003404120640e2891006444035000400080b405803c14041a0020a410401581071409003182c40c604102c0040c041418848942d41040c503a44a42d0140c40027950800c5201c1d40380c0c02305911242d40601c0032524100a100c44a0000c0b54940c001c3c07156900c41d81e581c05411140070301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 779602652 1250 779601402 779601409
    0xf12031a0906030307080f1804050717090c040f0b0f060703050f180d0b0906070f020c0f0a08010608030a02101107080306040902150c010c08010509060613080f03090f0904020f 77
    0x2024100a8260000b040044082540580209420056549003523507403100c0b1340201c0c00d441e8250711064410360030f00081c4013107241e0001d510340c02082e0000d0b020b407642e222102420715000315100c4168120b030a00028444d2045140c0c032808500c0380c20f41e0b0510a184007101003040da84911140100821010710a9071001d11000019200280e40c08070040c041c9841c400001d441c086030301e43e04980c2d002c101d00c100301c0d4040c0107210058110a05043c41001b1100b6050702039101d00c040d4609a00502a1000f03550040c0d60b020358190081109500030461140c0300c00e204c1d500c0ea44a030500d1400352084100b40481014140b041003d41000f107080b560030001b096036003410321b038000f403c81d03079129442e45001c40140e50b552241000900716007040c1d60340e82480314811802d48104101c400144100ba0004002c02c1c0c64152060f580310310120ba5140d520381020118201070742e400c1c0c0140101d48034825483c11017010000091414060840c0d001e100c51030010104130106608540003504501e4a4040c03464504 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 779603902 1250 779602652 779602669
    0x206030103080f0c070e040213022703010f090507030b0c0a0e10031e0902010801080102040302010c02101803050a020301050a0509031603210f0c0908060c13050603040f12031a 77
    0x10542084030b858903052001c1359140c802c184e0469520451140706110840c030707204110114442c031140080d82041f058203000d80948103045044120030040381101a00d6607401e5108819152601e041084800034604210b961821180012a602070760b00010500b513150307150640e00b00918968445000920300e405105000c0b889504d0101030580383c507500030700c0405600038180d4400200a0000b02800e0f1800010b04185040c5c1c00150164410002840942d80c040c030010015501501c500303800c181c60043c00c50700d00c800d02074540c1c1e50202000020041002c082030039042117000710004e00c1581c0b00e807150038007110303810b440354180c0d90f20800c021110004806080e101543c02828100942c80f141365846508000c98800000c482d96550f08140b0111000d01c02ca04c190300c2107151903402d40f070404e6402680c40501070f188580030500031400a15000506100304c024100207450700e030702e0341410700c4d1003100b172010762404407000e5040c0c4c500031001030f1180c41202d00c10780c005c58181110381c403840306005025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 779605152 1250 779603902 779603917
    0x81f021c0c020c060a050d06091b1803020603040803010e09010212060f01170709030c0e0f13080915070209180309040c021510170c1807030e0f061006020a020603010308 74
    0x43c0121000100d0b03d076184005404080595110960741d1305002a062044441e10340161180c103242100521860a18000b01c0340c4030415818080c0007449140c00d078003002d401c182c0c002944100008108003c2018040c051412143c41c06580e40300ca446e501031035401d03806400c01024040714180001201890b04488800842c070040c1040300400348602e031541d084000c204c8000d00810540c1d44100108103980b600103000300141c45c2400c1103824022144a400a405040c4841244c030340b1010400303109100c82100c8143d03900804204007554415228038503500011400da10404031080007800707043c000040840740c240800042e40c942594442040000c11a42e0b000d0750851003146a0110f00030001c4a04600030460007842e550007a1400741684180c1200c2000403026400c84c1c1600f00e50342e1640c2c02206521a1140352003e030715034030f0712030031001411054a05c4c0a01e11400f10702c1c820459021441d140190203119555070340c261220030580c1d84d10620700009400040410040000c036041c0009046d20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 779606402 1250 779605152 779605157
    0x9051e10180209070e010e0d080a030203060a0b0a0207031a04020f1504030614010f061805010507021807080610140318012d0b0405041e150204081f021c0c 68
    0x1c04803a900850140481190060040f40c00200e01054035038100f045080005000c0301d0b1002c17051019034a0b501240100b0308401d0605030040702144d000e99070104008082d00e00782030400e440b03401d829030096603000c0601c0b059400b071182c0c41c402c1040c2004808a1072180d6005010713200c0c403101318010300c522013610b121031018011042c8000b00004149001d000c106141417040f02040c0c1d41440c000c980085c400d0381c01a000d02080000810940d01d51b895600102e650908100e0b464030741500125981d00d503d485d014412003c00010840310641200a59004140981d261000740031440400d4a000070002841c042c1400c0a0001030b100d1a4100480c55940b80c0349000031075000c1ca414046440e00c00458800d0007039030101500b030055a001840307128080f5104690501044c00c058540c00c040c4107098900c04641c0403400e46110901481000342d20015540400466550740d031000540e4694100c0001d1540341d203040307640012a500c0500070786410340c0321904004403024081c50080010041d10079281c2c02e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 779607652 1250 779606402 779606441
    0x3030a0804171305031506030a0f0f06050a0207150c050409020c0c10080f070206010e01030210020f0d0908070e0c120709150f020607020708060c13081009051e10 71
    0xc0050600039103120082805040c0d101401d1400301740c100500c441c441c80c5c210a5540070407410740c0c2c00161b60412590409400000704605007085032010508040103041c003820001440317641012540184070103402443c800032210450480c0606840c92a004c050006034184824400025141c0c010030081c1300d40c0c8100c484c40028a00461900d034020340c4030b1340c003260b070035003c10003103401806540e5800000380c030140c9400d6040100b162142c1d45c0601000c2e00030301500380c1a11b24680200281040d010700001203500504d64888000d00344031440c091820306001c0c040002994458405a050080300409211801c0807001541c040c450600107014408101c01e18000207881795804684524010581d0381d28441c40495100c080e24041d0007415078001c56101403005c000055001c41e0080c2c01003881d91500742e48120f00480b0b102c041c0e2141e00401c0060245108980c440314013071348a640006d208000303840d68070380031041001c240c00d042c1c41008025001401c0d103000c014415070040d281c0d82c00038480c408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 779608902 1250 779607652 779607683
    0x709090c120e010c110a0b2d1006020d140a0311071a101409070e010c0218090f0a031e03140a05041713030f020a03020d0302010212100503030a0804 65
    0x90079202003814035001039554030a0400041c1e40614005d080502e131100030100c410040d40d5001038040010003040d20320000005800198000c400c3c1d000d101c60701984800b0003402d0070700aa0300b59134030030f00c124400b6220b2020b05198007801141301c0c0e0700c500c28241f8418104603a40d20260090044140507800c54070040011500250410b42d00c4801314144803050394003440d041208110021042d0008203444c6040305a500305070707841d0140c866202549141080701c1e5100040141c03410910040000d40c0000c0100b8103032400c14952040364400c810740000c484011402c81e02c59034507480c14031000b41c0010b0003d1619502ea281c0700d0b000e081c4030001483d0002d40700b00d0360700640b28504020381d900811551a00c0902050142200e4480c1c105008441040d00d031990240c050400120980310082070400203040000655880d284044011600900120260446850002e000303503c40c190000505901c01c0109000201e88140041a0f5401a00039890410301800540c0d4289004008862101c521040c08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 779610152 1250 779608902 779608937
    0x1808160507060f0e06030108031b010605130902130c021e071212080f0c09040b0604090e030d050c04031a0907090218090a14010b07050111040e07020606090709090c 72
    0x1c600805a55a40035114070542c44001c0410a402c05150b2241009000601c0071220210450301d1031900c0140300c20504051864403805081d1310303408a030380610902010701140450b500b004003040d100b10b038140d40d403420380c030b03081c4c0100c0340600e081c200140e0254514900900c031140c50600200e03040d10803920700594400e407040980c42410030480e0035001c8024030306d0070281c101034070503009100020841130f18a4451040c82282c0140341075903100700e1311002a503010381c560070308850260446001c01c0c4a040c180c524225500d07800329070b4120760305d8035140000c0e0b030200c000c0c0c060f10150781d400810314a01d4040904628212140601040740b00c1c001c884000402101d688024605240006007000100b103000c000c001070390310020070102234142800f0040300038982c0a142d54ac1511000d000441d10b0b807840c2e050950050120700d00a900500c0001380201d05423100200e0184503440ca903080307075010f07603420040c0414004c0588000001c0343c00300e001400744c5c0302036410034220100b0524000000d14120140c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 779611402 1250 779610152 779610163
    0x301060c1a1302040c030606022512060b0a0e04021005090f09070810090513170f040e01050405070f020a0227040809032e02030c07050f1f18081605 65
    0x10480c2c48004294034003141050300412011410341c1c282004030310311f0540c0c0a91110180c40301c00004604181002448251110150300645103200450a0400441c0b500200a244003800c05c1d125a2071801e0020700807100031580d038801c590103000d040b04c0154001d030603181038100c000f5580e4040c0c401c40c160310307090310380c51201881420b182c0d540075038504180040c001011581d0300074501080c1840d040014208414602c24038081c0e0001210024444074204078607280103101d01c10015180016000035085814141c45058600c2150300b00b01a4841180946042c0301c513803c40030250300242050b1000d4504003402c038074600088441c1250246800340d4620281d6011242101d6801c03010070b40c1e403503604003044400031141d46454201d40c40f001900c14104400c89001130098100d800000081040c25140b040d103848030f5100c000c80300c1180000c2c1e80e130b50319106050928a81d07445880282003070745403140102c17181840f109081507a10307089600d852269501c010710700c180308a0758415040008004124 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 779612652 1250 779611402 779611411
    0xf020f0a051c03030f0921030e030d0f23061221130602070b030c03091006080604030e0415050607111011060f040b06010c060b1c1104110301060c1a 65
    0x4002400b50642c50064100c0b843d825041d40c0f480d15000615001401841d00001c1c0c1c40c41035085203c82120707140b800c4001c1c00400300b08a10b10300002c0703102c2541c0001900886d120303400c50302040c0b100c1c99000c10b9032100300010904000444680c6004107210f03041a103002c1c03000441c0c0c83c0650701c1c544912a107102e1484550a40000001400290a002030010716000310141c5890720207003c100b850700b40041e0311030001518400781d96500001141c11074070200806202d055282000b800030b180e84030042170301d40108443c2a0007241d48620740500c180707054443d000328203000c0d1003082e96680c107000600c001600b02900807604070f11201d1164001f9039a000d829260b15a1a54a6208100c541d0001505145000d40711814100c3c1142c24000042c202e401c00e6030f0b200a0a2901402248160506a018101900105400c00820109401003201d04034000009600420f041c641c004045421700040396400f04102c40c1141c0148010b00180380728885402c5030364094a07030f500350321820743e0700710381c0c20300c4143e6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 779613902 1250 779612652 779612689
    0x18040603230c0303040b09190e040602031e01060f05070206070b01081c03021606181205040609051e01140f040b0405090a020c060403211407090b0301030f020f0a05 72
    0x4001d8045494204412000e801058000c0d608051500164402d18080c0740b0145101d40c1c60050011000400c22407444000c00003100801300d5424103042c4000251b1055503206100700002095960015070311184038100c0d0403a0780d03041c00c40030081b803048400d5081084100d80c49801008901c0200e41d007000c22901810407040036020703c0b5003e40b0468012241c0441180916006124032400a1a801c07115140e85400c280003140c003422a02c4160500351415030001c4c02031128903024400164840e0140c02910482e40391900201c0d1a081040f074050050750440041e45641c01d800340071940f01e08246022044004110360034462a214411115000f036001301c90030810101c1c0030086898850000c136041492070702c04500c0e11650500070f640310300e4018030140601c9a4400b261203251014900036500301c0f0300c684100181e00d10044810003e04041e164400010350822010448007000e10849049039448241542c1900042d0b007408110083c842d001c5a00244004000665455080040384580c0380031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 779615152 1250 779613902 779613953
    0x4050d05030a090e0f060f0402040b031f0611030f0a090b0a030b01021203090a110f210d02070b0d0f060504020d0c080f06030703080f1e03010608011a18040603 70
    0x2d21004111a120340c1c0103401c942d8140d030500c6000383c04503012503084035040d030302100b00c992140d021401034415a44800b1050000104114048401000e0b12031070320044c601d0103a205945800498414034a0000e826482d0800c0100350803404210008141807030300c60802d099907940c1c8e0000103071990400c00070500400d4441040865661741442991816000d0481560540c240000e85c0350b03030f60045010041070520b249202c43c0090342c0b920100760281200400400d0302daa100b025004011440001d180500d200d1008110314540c00401c594043e200c0c54010181440c10190070f0720042c02800c0c00080c030031542e8460104107900d85000410490300080004501e0840c040320007450960020160903010385000c0a001c6269030104501e022a40c11036081034540d2111038290350284110310400b10040d062540303052034511390101031030403901380380c880c0090350380e0328034100e10303c20003424078400d12480c2000100c88080c038080c0070010105000d0000920071b07460396103620304580c0c2c200c1100040c4c00f80c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 779616402 1250 779615152 779615167
    0x30911060c0f0d180e0603071a090103052409130209250c0305041203050d02030f07020d030203060108130515090c040c0908060711210a080114010e0405070504050d0503 74
    0x4201040940d03945103028040d00400500d007070754101320307400707541500d1142002041c140d5408000c00805015010103040c001c28031444206002d81c011b00440c1d0101b42001e0010308117460400d040c04032035400d00e0040b00c00c68219400c01010302001858000456030103100100540ca44060380b03885105540040710603a81120400111001595000c07003c010000c40c4220000e5404400e44040700d070f1001942c90803000600e0143c51500400f100031850700d05c040100701c51001030314a001e00a05440c1c0996100e5407407128100d05921040b610180810712060200c1c4040c0c08000d04000b45c540110265650001c80c0351078000558403e80d86140154080100c482e4603250a105403c03030b180040c10a02810361401098549414000701880103002001d0380c1700321800c0051010b00e030750300d074504214103061641c400c40f20455080401c005000602a0f40049060080c520252026400584508507000c40c0c420401000e8880205001d041000920000555403503010540d40b901d8030407005580c0301d418 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 779617652 1250 779616402 779616433
    0x190504030903021f0f0318050102070b0402190b03150f10020601080f030a090b090303090a06080a1a18090f010603031115060d060b040b0d0b0a0c080601020d030911060c 74
    0x81307a030000301e20040340403c150245a08002c030804480514100803030009400c0891107000003106074090515400002c141042000c2e100390340f03100d28805c41302d80b4801001040201c02c2c0390038a010f0300d4a03460080011a54040181140c1c4640b10300040c110100d2080d0200031800c8000075114078000369000500500980c80e05010700d00120382c214004608125000400a04149041c801c1d100c0089000079040400c0e20144100c901012000d0403842202d5640e160003420090215580301c00c551400b0001d1010764101000d02580c070030018810302d104420400000500040640b0107405441031410702079203030800303001d80001103010791120181341d031100d9002401e100f4804140701a01c1d0b401d00401c10315590b016400d41000e80c100e200003400c0900303000410000c204e60500c03030b544060041303500c00400c401810300350300c208010002480400c1c450041a5000b80c815550203025800c40340455214500c02c0c0e100d04c03019030140e606141c8111584002c50015070024210451541080524402510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 779618902 1250 779617652 779617669
    0x40209040e060a0501150e04230c1b0a0b0c0d06270b04050105030d050a03020c03160327060c0206120406150e0402030d050d0b040615140313020919050403090302 71
    0x1c8108018040801c001b2801170806d080c1240c2c43c2c3c4125651140e21941c1071401c000000320540b010513a084a081c04100051250082c00700e080b0320b5042e0007503c4540c840c0c04030b01244d4240d406401d100090312040444540d41d00309901814046944070b20018000c500414150743d022031f080300d1254040d41002070311040d15111a001c0340900d04003c010003098400090301700710300304140342c0a40ca40c0032084045000c2c5c811110004800c2c8004140c10449060180742c104202c2e10036200c0414059400c1284000d01241c0c00ca458001a19504100501030142c0d40c43c103020f0380300800c120f00d028450b860a82110300250b0b416107271140e50b08030030048808101d06901c05841c46006c10380603071800703900180d47c456498000004120000c90031940380300ca260080d400c0004018400d1080603107030100401d00101000e0000300280c42d20803051041c018070012a80152201010030025603426000e0050a9070701034507030136220313141802d0044000c9891080074000ca1007540c40210403440c6004100001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 779620152 1250 779618902 779618909
    0x6120903160b22020f041e060e0627390306090c030114060706061214070b04060813080f030705090f040506010503060d1b0b071b05061602040209040e060a0501 70
    0x307480c100310b4203003d07990300400990448000c0300c01082c1e030001001f54010700030f0306501c03404201f0b041000211303181e0040000c9501c1141d00303891a2410040c01d40340b010032008400e00d160008040032010540c250301071902c40001142c810f210881c040c03252901c1049000c00c0402400e2041004020f011003032030301d00c035081d810509040c22981554140440362201c004c1050100e442030200103104801c1029a0f0890001400c0313000c0921a20f0800703041c282e6141c40c01c0349142e0500c2c00784a1001c6004c04413231003a2802c2d02c0c0a5580e00c2401d589103945007200404005068031401c0080c0403080722500c0c00700c000c6200b0380310341e0754050700c50050809008800c0c40e2460000e11840c180010886141d134414166544114101d03a085003546590815104503039030190020b000240001c40414000e01d0307100140a0305200c2d2104030702100c00580c90044055560048650094082288515400416440703401c000e00080c00145414212000107003141c5000020641c150015820084240901d2241a004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 779621402 1250 779620152 779620201
    0xc021504030516141c0609020402042d0f0605220f03060c020a0b0c1b06010602011d060402090112150203070e030c0414010b0f0403080309030408061506120903160b 72
    0x1428020f40004846176078203a142d101044d01030213030070184802608a5000302d900038104560f40e43c1c032006180250f051040d000c0071080d0703202d1408405158140b10f4401111144411900c0c2641082000c0381c00f9030101d90300300c81d640e040c020084c14694903160110700410f19000d030750346000c1c0f552910b030707058683e41d458a006642001681d10045110f0f5000300da4418000310245a89040000c203207140300104699500041c840c1c0030010604580541c08401420203080030300103484140c05095964500031100213400c20b99104c01004442c400c51316203420581b180748000c2c0720507802c600000480e041215050300066010fa403000180c14240141c4250503030595040c011120f1141d00d603450103106105040e00010001140c031113101025054601856101000d981d40b41420105039649411074060214903000341004111240c0315940340d00d2400f00054505802c044000d1083e00c1d40300c200606003503850004004600d68001040301114003a807050b041700c4800d05082c03801c000740306a11b000c000e46 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 779622652 1250 779621402 779621429
    0xf041d0601151e0f020a150f06090b03071505040305062703031b09060c0703081b0607021002030406060e0708010611011a0607020d020618010f0302190c021504030516 73
    0x30311410b004108405011824651213010558900324030b0b04030400313000791041a0522081e044034040e030300702e00003030988404240074058550369901d08440313040002690503440030404001c120442c05030f0740796002050500600b026980d444250030b106003125003c080c01425404490f03541130031500b40c14003550703100040d400d61804440034820050449400c0c0c0c100340000c00d8100b0303180d540314121110f4040c3e190035250381566919080400703030022000409005203051aa00080b9030001c1c004d40325114583c004d10100cfc40101031200250300140c01610400e880704070100d000551000380702d0052030076a90740900c80d850600010220740894130f49000c103904010041c1012680803080701c030001000c4031041d55131001407001801c1441d1034800207401a03008103803a41034285840039800361050a07216441c036040c6100302141240b1800c01c040b0411140f4452508a440c4600d140e100d40d5032020b070040400249541c502d03000c07500142e0044443c1e41c4034000101190310048100340050210341e000d01d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 779623902 1250 779622652 779622677
    0x230a0f0e100c2307031703040305040902070602070804080c0102060702010b06040e1801060303121b090e100308270f0a0b0a09030c0e040303150b03060f041d060115 72
    0x144042041d002407410041403051110521401c008080032094007000281d082c034126240441d21142c1c54441900d1a440611152140c1400c61046910a95242c0d581601d0a030034600641c00030b402030344080d03e03096800d000300c1c1c0001d0300000061002c0c040080060501c0740e05200020b181c07040081c0131300c5c21a41403240744101521030405407810b80f00d02e40200440c40c0c0d05d801c0001922401e40344030311200d40c201540001410307088a00b085680890400c01c0c400a1040e02c0c0d100040024581090000791400c4030820051000c040a2034016544549920500e036598441d0581608840c0816642403040d441c0550304802d61003000034080c10603500c41c590040c0c1c080000b598454540308200c5900000280303280880d01c81c1c13a40320050360b8840c0341f0f1801c032902e0b4000086560000c64080f00400d16203540054040ca030214420102c1c0e241296091665131650107005c44640c1680c8010703045900c1c0c040e641c0102c0380c4d055441900541c04030040906624111100f00400e00601d5071206020315090310a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 779625152 1250 779623902 779623909
    0x20c06042607033c080406090b04082a10050c0c040b061801020f0a0c2111010e061204050d020114040c140a0905040b010e0703020f030610230a0f0e 65
    0xa402c0c00400d26200d11101d130000381c10f589030024541401070540c00e80c904d4079040015200141c030945555588480c0402d480c1c0b60442041d210714000c07415180d02038032100400208440d401084010900200b0b0304510002002c074064400c42c41090020070404640640318010070054400401000c0710203221140c04030002c50401c0c440c0780541c464407a0741c103203440d8440c2d0080040703070f03071018180080751203082050034502c480f0b00090141c641440090384091804411003003a6480003508104e05402002c140c80064a0400c0c0b440038a0342c10202c00d001042812902e021170b144641e029002801c0d840070b52080007801c45040c503210071001038201041c07201140c8080f9030581520900103906c555186840c000075150907103540310b51085804d003030400c41000b0b03a5100d458100c64580c60b00c14031540706c40b00b05034141d00403108003103030340721003030000850070b1608181d072a0b2181403a05002a000d032941c180112282003003119050700312800518400c00f1940051405a60001b61810450b0360718102c000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 779626402 1250 779625152 779625173
    0x40203011a01120506120304080123060603180705060408010f05090a03050d09051905030901090f1206050a060503030a2102042402012405090a2a020c0604260703 71
    0x303001c0742e562200018500d0f1504000740800706c00d843c040f02e40311559126203034041c2100008107281100214502200c0c0180300303d00c68000d450007450359045590380081f982c2084a9110784908911901c02d00040f141c075030b10004c2000e8440710001281482c1c40c06408001d607840079008402d00d034019101d04010961107000da415815540001098001e140e013025403402080e04901110300c0c100c1c0070240d08108001005003003161081c0c840340d403215580c03640540e1015440c80b81c080640b00989214000484540c803081c2e00a1201100003051915840883d10310740100e4810001300ea0360540910025000c540001c0ca002000310b01946058180b41d03060768102d400501c1c414404004661a202c13541c000e401c107480c5a0300802e14004400000b03d03100003859458400d141c014507690000c50071561480c0034056494101c4419400d2100031400403001c0c1049452818045001c2c0052510007551802c0003400240403e02c000580c0b241c3c0610401c0342058200030500703845c3d120361403c10000741144074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 779627652 1250 779626402 779626427
    0xf03090f0112060911070b070801050f0f030111070501200406050406050c01020702130203010512150f093d090308060910051c0339030521040203011a01 67
    0x24003620b03190615402001500040e040040c8080c01d028510003626480005082c1c0c441c050520710385251600c4000740d4040384c0c2030050503080038103815070392003505140d07198900300c040180001a89013001000070304aa0011b00c01201e0301e075107030040f08040030361070030030201501c04403e143c900e42840c0040c05405445540300d12420311a01186c00310880700294150788a41d40c0292a01c40c80c4c9210a4400000b58003d00038184200103016052001034000113400c1c4844e200d08550344002d403502c180075001b00000a08404451103101d100340460050005000d03121103e180880d01401e50b50b0b070740d50860b402100540c00d043ca1400061802003036202030b4050b0016019203d02c80192075500020040001d0b0380c01041e0850303d00c00345c04038074000850415000c54025034030509058161a07004004060100d0315002040080e13120040c00c0340c00c3c92040f010107100741801881c2042115400d0014846105804c3c401e541c14001c01041d41000c1c080d408514242c001d45003911445c907070010b000d4150809 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 779628902 1250 779627652 779627657
    0xf1b04060c240b030f010c050405190b071101033914070506040b0c070804170a2f0103020a0203041202030a1a1b071509020a030c0f03050f03090f01 65
    0x680c9505100d481c0d801075548078140780555600c0781942c41c1490107025030390109402480384032211500d040e018130031808406102e9485030b10389840c02c020070540e101d00344c1e183d0a5010f002d0038001000368a0303000400d4a9442502c0c09021800440e00142c03c03103130720b02d0b1510500c200519900080015007400c020504041d68551103a05440e2801118603081072a0a00d82404e0001218401e2020028005200c1e0344111101e19155545e03c1d105206401405001085190184401d01864030b003076502000d0100c40104131030a5811603160006d0003800301d1000f414041c0c0400d08031010002104080c04100c0081c00c2c00e51502410303c000950b070344a648141c0d401140c0c4001c0440031594140300c982c12050700011604922031200c800c5510480040e20701406051140240990440c801d0003030f0f904c516008078840c50120500384d90031016006110040381d0008843c84007100094041240030040c248121038903002c1030840c540985030910b0007110220030750051090303000e503648a0001c1840c0b21381c2807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 779630152 1250 779628902 779628917
    0x20a1106030405150910110c0a03050c101515030e03180f1810060c24180506070e060405150c030f0a03020d0b120a0b131a0f1b0406 58
    0x703040c038500b840c0b44812840c204c18186000c1c00008680004e142c140083e480760200311000901c42035214502c42d02d0011411a04242c0c01100403e001f180030b451003898440c10390395500c0315212000100c2c1c0301c2c0d928044400007282c1c1c061069042e07a0240ea0540c24150074104080303c424100c043e0b84c0d0141428181e9007005881700c240b140e0f01d80e480707034042d8110007400a02401d50303102c02c00240c07490101d130346103803101d1480c100240d50380c803415210400d15045400c80400f00c40d0b80d11300d4500c1c800c03150002607880c2c0d02c60b041100340d2181d08582005050144016200324100a80700806112814800074070440e4140010f200b999513080c084040c0054521150341d4031200d891019085002d840009506240085184942c1e01c1d01074000b080e1f11307064030400304490480387e020025a006402154115544070301e5484000510490301c46030000a12900040411000e0382c030081054041480440294408400d1095107403003500b403940c001c92190041100001c041201503414025481414204001c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 779631402 1250 779630152 779630161
    0x1205040308040b0c07060509011b090303090308281107050d051b010c050607030b09010905040312050702010612080d05090102040e0708522f0601030b0405010c020a110603 75
    0x3424205e445580c1e12020503c02491b11110550081503245490304015001c035501130030b8507214043d9101660341c581c0b15102000c7c215216080700c4e070003001c102c4821051050506007212070040403030380c00e8039050761242800c6401c541590304082007540440c1c0203002206083c8009000801c500c90040036050030500300c9210080101c50f000ea18410203041380c064034046c170140b540d0640154101d550150781c039280690342c0d03804403011104d040328050002481401c2141400300c898024a800160510010030700d01d45421031910440003100342110311000008400d810315203180143c1d68000d0240c0c00850910b0303d060800e200003a0020444810000307100c0014240e1a19440c0100e42c4181108512030001c03c6a52406010840308992100d01550403440800c666484655200d0194095913541e9940080029014200203c000040e080c1000079040d140c6030b503000c00c82c9a000b0b5008020849013420581449401c41c0c40b01c01d4584115005500b402c1c011a010150040040c1d50a0314003e949698 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 779632652 1250 779631402 779631421
    0x822060c17010b0a0311042d080c09040201081905070e01080a0b03030f0703030f02040e0402011808120901230a1413030f02040e070602010e0c0405090705040e150907061205040308040b 81
    0x1441d04580880701419903008003408d201349a0354910440030f00e14084c11a110342c1082d94800d1800c0001d944040c1100c00200194418080c80c3e8202c50f0106403015850801260362082c0c9030110351160000306c000f99030140640c0d00c28012034114014440801107403044070003007501ca20070000703a04040c6400181d40e8007050711036404600c0e60035101000b152503940f1462000c038030820a440a030f00080b404c0d60003d011140740801402141d80a030010804444030311183d001c6600000e8600d4184140521a0b60b40710300344022908082602b618617035a03034184c03800c0240a4440d203000c5081d80130030511040ba00c1940549140d0150382d00301d100f0419940a6100017005450101088034981c042d419000800747d8054214106100600058480008a00e0705210480d442200c2c6103ca560241c407040003035081540c00140c0c038055000980f0a8040e0350301a90204400554211900d50321080d001c1010342e13030041c0c0180c242c0d000070205008904041e10002d0071140c0103040500b0103625000811001c85 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 779633902 1250 779632652 779632657
    0x16170114120307030e040b042c010e06090a030f0801080d0513030f0c060905042c0708070608010602100e0a0201140d090807051005090307030822060c17010b0a0311 72
    0x140c42040381c0c3c3e50310032481e000304542c1c00c48034a14003880c1054801e07515403030280524100380000c0103244010300380b132084030401c082400307540e16040d5513151044440b0020522046200300e890000a1021403c0d6180007081c003414010b0807000c20003028010300400d000443d46018042c3c6929040d920385004482042c003807509640020031826051b1000000c0001012614044800e01e44488442036582c100340400d44d00200b040b03840c1d00b0740001d030f80440034080d1f25000828103000c0c000c640e1026211050070345051559005400819032500040142d184c0c10804220b110303400b600203000240300300c10701d00d41c0c0c0d014155009040c001c10003000c1582c2740340e00c03064820356041800c09000d0541e2500f05140140d11048065640707002e0302012050300d886900882d4000e00c030f0b41000314602446074400b110b41002c094020341200d5048010401010b0702510456000b80c02920001031a4100010142c10030201d1650320340d0312031240f030041021907904015261409500d040c08240c42c019501d041907580b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 779635152 1250 779633902 779633929
    0x10b28090f0303020d0f030e0d050d060b03070512161d04110f040314010504050606060f0f040308030a0f0b03070b0c011407031b020a020a05060901020109060f0516170114 75
    0x250814400109166001070365042c04170954407901ca445204a41c11015190060521700b026800004000e1040c0d105000400c1504040c500000f10107807036085030022640b00340d500c030000541c01708049003421030b90251142c000600001a00c2ea0450681c400f03010303444240051045088d41040400c0305072540e400203950704000e958120f07502d21124180c1c150640103070201351501112085c0d400d0341170360144a140c0c019604a0007c0203180c2d180010400e0070342c01500f038080c6921007488140140c030f501d1400781c00503500c50300040d0380380e06d0109a9402180d0346070000640c90360908d801501141c17808212203059907922a0510f50340c0d040d0011480c0900120005030800c0e030034030f0341040142c991540c01b000806154569904e155005541e040342c0c3e408014034013070340c00f2100c0d40003003180b0300d40030008152000c0d06000100d038001d42a1142012500807044080c0c2c0d05e9160410407400c8108043c03040f0761489982003540304480c01007a1000103941c140114040e1601d5003c5007103860f9143d00004011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 779636402 1250 779635152 779635169
    0x30906010510180303092c0c03041e12111c0f020a0b0114040e0303160509041e0504020f0a030302100b030f030301030c0801050604180b070509041401030b010b2809 72
    0x40c0c1c1e1304d190062110113180b0460540d12075103082802c0c007540c1c00401e9000c0a1096055941c1c68a84100883d1580d002410844660784042d81484140003568804500d6502400b1500110500203c0103444441e0076550b101d8940c0014411003084842e208500003801d8261070045c2d200518030009a1916001c0400a4030b0114020000650307400410b04016000505031428001c3d00500300440d6034030f01003a24444408500341019a000f00d12a00c00390401039002000811150041300301d1400b0001c0429903194942c3e100c801300402c2d03040c03080000d00c0c0c800b8169840c5226500e1505d0007074a440048190604040c1c80d0030391003000c0e035030401005a0100c01201543d0303595943e441c1400d032010381e83c03060170425402c000000d5803a01d460300c03951030601c4a03d501130200440c1c5603104014950002e1180c070500c03105000207041600c03144501c0411000303081c4610031650541c04c200c3c2e40800141d03c00c041d011030401085039800750b004072240c0c0c007400e02840c010b40a038580006888100040d08144407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 779637652 1250 779636402 779636447
    0x60f33030605061c0c08091c0512011e140f12030c01140a180209040201050a3b0a0302010504170a060f0c1d01021b040209130501060f0302030906010510 67
    0x90002c00c82c004d01803d0031600c010048010340c0c00f01070340d4602045400003001c1d00b04e907518007015404940e20300c00790006e84c54814940300400f0742241021200b038000c55661030403243c0341c0d800c04080304050700c0a04480c40582d8015000c41001492a1180e0074605008a0070711284417045907041090f01c034190700441c020b00c519480458000e08407101203450340b80141c1010503410301982c1d2601600c2c1882d070060444001559541c0040d43e00b03501a218330410489921110a04928035210040b08800c80407544540403a0103040e0384020303c861a2103078441c4184a10400040c1e82200440b4121110011140c6460b080c0161060400281c48005460f250070441c041c1d00c00d039803583c022071180960751100c1c1d04800c504210810221208505540580d0002c41080c0b4804104d444014075404d00601c0586408040000300b2840040520410006a1500010302441e9000302000024a4482c0380441c00c515000203201c0d0f840d81d044c132440c0c0c000c01c8140152505140b0640381213058070b003100740011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 779638902 1250 779637652 779637667
    0x1801140f060d09022d0402070312060305030a0f05040f1403150a0f0509030702150c12070f05150403020304030602161e2303030105090709030f030201060f3303060506 73
    0x8090184010100e00c12065040780c5a00c801840c45015100c010005d024a40038190300180b01c000d51043c80283c0901100c0e071212449036101d40070310b0010f54881d202440d241c14080038060700e4043c03c02c403400305008061200b8070080014405a4081300c400d004c8020303101030306d01c001c2070501e042e5400b0400040140001c00103040318a40140b007482680e00800c0010b0764500421a0b203038050954003c1d0f00220101d00944400020000f401c40403504d1000c0d00d181040c0302c1480c1007580d2200d581100c02c00040461042440000e0001040c0900031420104c0c0620742960025201c1c407a03804001c05a590204000c003500c143c1c000c07030091f140d038003040b120b401c000d10b80c0a0503241c0c4042c9100700c400461314100707001c2502000708270558503540700c0000c40c216401c003403c007c0c100c00007c3c080e00030002c41c0440000801c0c4140314000c050b0380643c000160081c14605d10300540700040d00b00203440c414007200f901d00100302c1600d40310b8460809855902400e8082021000b40c42079600c0254403030800303d1940c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 779640152 1250 779638902 779638927
    0x2a0f0d0f150501150509060a1d120a1407060c1b0b36010c060906020c0118110a030f0308060f06040b0405041401080a02010c08070b070e030c1801140f06 67
    0x2c40c180c45141d03010071329030218088125100e110344410a90048000e20184d00f0340340c000c0b407603403d44441240d81e942c1210081c1d0085084480110003c2c14140d10400c102420301a17160400380d245846e600141c1019400d16101922900b03c21030001c1249119035581e8500d1968049142c0240c80050359003581d030103890984503070480b045030008500e2042007003902c03101061441c50b46241d86042e1503500d0720003003d0301d509004105144003039031400d40801c54210f14840a20035441c440b0b1244021005282c800d040141001d20320344402402441840018004590f10712100341c58254035180c407248955850012406203070703001a080c0d82161000c035010460300d00010103041a164242c40400c130030040032454825012081c0f140c400b039500010440340155220b1030304140443d00440d00289800100c3c0c0d0740f00a001c1e41182c0c1840050546418080c031440c06204d07494000404031595800140011800c0700022018420412500000c49012030300d52a001d1100c4815200142282c0c0c49c8c15800710309 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 779641402 1250 779640152 779640161
    0x30b0a02042d03061407120e12160c030b191a0405130b010303030c020d02030304021f090e0c040306060e06130b032112010501170402011808030307022a0f0d0f15 71
    0x2031b2400b284007041c26510b40041407140100c0f446401c0001d000071030000e68040c400c3d6011080c1c485441d000035200102040e11040b0701d80083d0f2080f607244170303517182004041801c01c060b010001e02d540e00741040344a0500c944001040700b43d4040380c1c0010143c455064160600c0c1c03030f02c1c038010f0003c640c40b00004189905948103101c403c10540a5a403035030300031a01241c0b2840704540c000d40c82002208010001c500072007102d003a039891400c040b544940c0b15900c2600518080b1146420301800050905c200f00050042600600c0788601d00c1150317044c6400040d0000f4004c0401c03402d4940d48401d03810242c2c0d410400b4030762030252800f144410401078a640c070720b20f80c0080d101e480c1000e1580c00001d96544209d0f03440c3d03170320101c1c4c501c0444551035550045809818400e1420302c480200c90010401641c148001d50051a1603001454214030241101e58418410800c08040c101115035403421500e4941c4082c5c01040d0840324503a5001c2c0710301c0d003162030441d00b030400f4003010300c040502071031100c80b94803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 779642652 1250 779641402 779641411
    0x6091c030909060605071209170a0203010b090705070215040909110316080607030f0b0406060305070315080a14030c030301081b0a0f06050c0c0303030709030b0a02042d030614 77
    0xc4040c0007a45070340460050340c00707510403480069810000300307010402c00580003840b0b040b035280c0658615a50b004d15071381840318050303800c02600314414170011441c09100d00c0c0181082901c00c40a1850030b443c010385140034108001c0e0040c4e000b8200b09591300c8260b012500030380040401085a5080c0e400c14200348060070728500c0c0680314901060140c4c0c0c100fa003654003200c00034030040c01c140c0e80e458001c5001e4291900040982515110100016966805030030050840c90758000b0b124502102c1c010203490f982481000100d0401e10240220040440d007110021b420044068440039020011440c0d8403800d8000707881c9000c08000440c0007a004524100d4100e5848508031801d262401080b090850710312079040d1560340d0708410006036015a01510702081c562081e249010400000700e400d44c0e1044440100140c442c2d0028800c0054811403241c00507000441141000d0a110310031024070803000303041c00d5a41c007032121200e072403800440000166038090000d101e0302d248000c0c41940e121003500e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 779643902 1250 779642652 779642657
    0x12020a032c07300614070c150e030906091804080403030207060806030319110a051e010207020607020d080705031606050a02070c0e0a0e0303090c010906020f1b06091c03 74
    0x40d4005110343c4803080800d40721031186084400e0019125220091112100b03044480a0b00c80c824044002d6203145034620400464031450340c44101450682240305070010030140071403600c207007910920303400025601d1003c000e031031007507072000c0326400514158203c00b805c1c115080080200400c10021078003400449120303800720307054543c0f9030100f510070120407034116805078401d11500204405030201c0c0d00c00144141442040c2035900802d55040c000c85440584865000c2000120b100011400d0301e0060880c0b18001c50504090f030340002e11758418020046c0c45400c050802c01c0a11650008441009920208a0b0350310b880100c026034041d401c405c0305451051401001031450f41d203074001c481d60745038880c840e244103604051020003003450103055030200135501c0303005003d400c008000460007007440764001d0000c128084001428810660808070842d0050710b0009800a80040e12614603c2d0540c80c2c404d050240201003149401028011548044190350b0285030103a06200e0060725402903 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 779645152 1250 779643902 779643913
    0xa06021c110408010b0108280605040212100609240e0d1202282a090b1309050607050d0f060b0901030510060f11010f06031b060f12020a032c 62
    0x5c50040da85038404070303210721014482d4a002e030101060840700100303411030610001022520303a80400e040340c00004c0141070380100c105c1800000b003010700c03440b002410346140a582d001d04080c00448082c06109280400011180078040391f6070048207074101c0780c6400f0b010402c020300a41400f200b005d00019926001d40500c103000d880e01c1412400c41d0341100c45254044500c80c3c0640c0d2016417440d0791800700d401d40003a01c5c03e03013264180c045500300d0040112000100d805a9004200045188000010413205140c06090800030704080b40f100d0b8000302c00d0030b259132079424208815015204d03082c403507800c1c640340110200f412500300001d040c031241c081ea810400c2e40d492503050302c144d4000e8040ca101054045400010700c511450080035840d00f482d0003c1000d51040800c00c0554039140c0080381d042c000611148140301210516030014070062401e41c80321288140080d00034903610060984540c1c00041e03082c50b640c000c1d0020100c1c00140841a403e1800d030507a49440c1c5813100c001000c071802403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 779646402 1250 779645152 779645171
    0xc0b120a0501050607330e0a03020123012603190f02280201050c07171c0c110301090b0c04080c040207020906270916090c020a06021c11040801 63
    0x42050301c0b6203542c056245444c0c20402c4003442d0004507a10031002c441c1c01c0b40c0ca0310031b003005914001c1c106040c0901005045601192401a007581c5056018010003070031148501c1c0380c0326080c4070311411147e107000d5000b031481d000d40350803c4221001c14806c0d423920000400016541e854204244401342541d955240184400c2c0c08076103034140c3c030160300014842c030090706001421040140c1040ba1050506914182000081c941031002d181c0c007003c158481c0b0411034005074070900c800104031910740402c0d0303052080400302410b02e512071000600072038140302200385151030035400307607243c240c0044c0c0103186880d0144446199900502580c00785008440c1c02e400306d41024005e071401e181e030041c412200c0b6a921410310543d1006140303145500713080040351043c3c140060307000d44e02944000000d8603801d990340007017010821160740200076451811004240c140c0d03001c60f1100205504c0100541e403901c036500c0050265015507650b00095241904010060385514020302c08c9500301002030000790403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 779647652 1250 779646402 779646409
    0x30c030a1704020102060a1509060909030e0d050616030e101a150f0a020114010b2d07110103230f090d02060a0b0301020403080a030203040c0b0f0a0503040c0b120a050105 75
    0x1c0544009016038060404240030080940080010104a0844498046d80c3d01021300179500d082e80410070031070f900c1049409050f404040342c500e9401c25074000d0b01085641d60b41e5562404002c0030a5800c2500d003a4600e070151081d00501d91382c0381e88a0403609114040c1000340002c0c040c662440880070134152220125082500480c80c07600e545060b03550802500c4018074005070f220522400455595415400760b12000c0403180d406040080303203203610f8450071454800540d1000c40840a580d001400e421400c0b102c03081158072170342d4480d030740340c0e000d1680600681c01342c03003c28503031103200942d0b00910390020b46040c4060300c40c41078040706181548800c0800e0361241205e01d80d0100503000030f0700003a07600c0c40e0383c1c20192054001a000619003681c0b42c8429050344c04c491002800282c0000c2800b06008603500000c014204100c8aa031801207440c201081a126013407800b0144400400010140900844028000c15480450543c3c0350409140414000c400710fa9078070000e440e0800210b11400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 779648902 1250 779647652 779647697
    0x40605150d09060237172502101a06040504020901031b0f120905070510140316030e07140d1a09060402120c0901180b03010e0c150711060906040305030c030a 69
    0x1c01034a808101e0f031b140f030241100010f4010020700c0c84154500c0030811200740b21503040300d2a020f50b8042c0c6031844640107a4010303542440300366620001d40302e0082900707603610021901290310481700180c0c0c490f4940b0068001d0300012038098191040d104540c10415008100b1100703007251603840f0000801a944030004455508102811030f9011076400d0049091254214100315041d00300b04030b00c11350000f40ac000302d42c01201d8100042600b05480040b407901070090b03c400400c124041c04010742800c44004110400e244014071030525500c02740e092000340d4001d480d0111410501000a1408003980d59441c3c0094074103c1c080e0f00c3c440c0c64040d07200008500d05090980092103929264a0103010700c801204065103e890507176a500b1482460350244030703090b448040000900344042d20141040341c02c201c0c040020b13050800030401000001c0400003900143d04007119855201c1c1280800300302c1c540a11340009207a407000040103520080000081d10040490b40c1d900d440c03403c2c10030070206811 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 779650152 1250 779648902 779649007
    0x80d080103050c06031f0f0e13120e0d06020409090215160b0402040b030a050c0a09020a050d020a1701060905030d110a110f06040e01090506040605150d090602 70
    0x3034120203ca201645059001150891345040c075054130711003071034081030068030158802400448050020400d80c0d9050701d159610000190548840218079164602e00d990100041801c2102001e80360015544903403c41c9034080c0c00c01c07001c64a4581720740c0003000625041e02c0c00d034450038088450901082c040800c540b06d03090445e0b50303083d400c030017503841c1102c0b40005442264440d48480040b00603850411030000c01601440003085c04103101028441c4908198102c000141d00400800200c40d40100c1103403200300750800e005030b441900c40340072550460340c50000e2443c00280300c00001d21507405000902504c03400c81c00e645101c2c00103c070036544580050058445900000005804604403600b400e8000c04058180120b0750100c0e000218554880d401c03a45120480d8001030040300c01d0352007401c2e400b0b1010b40d020409103040400280410320005441454607400050801d015072a542201c402680d00220035500c800d043c0c05280300303140810902006280390074070719041c038038452010708851 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 779651402 1250 779650152 779650163
    0x8030705030d0f1d10050a180f050304030803090307050c040b0d0b1003020303030901020a11010e1c090905070306050102010c1823060c0a1a0412030c0c06060609080d080103 76
    0xd24440303030b244102401041c000740d07042031340d07403444090f1204842c0301e0b08080c1d030b0445002d000000c856200384412a8005001d080007146072461000d0f60500e1007056103d030b5500410891140c0400b4034206165116a0b00020508034021060190942000000d440e01610420650303000c01c07491810b000c100c400e64584140d00400020700017000c100070341e860307a82000607070f100300896540741e402080c0f540d441a0307084151b9a41c0011464800b0f54444031401c14401400000c0c41280c0d42c220a0310fa554064800001e814a180e442200703400313006407198001450800001d01c41032a0000b4090010710492040c00c0c055401c000201c400d036840f450001c002c0160f00f410710f80140d4180309004040c0d05c0e90300b11056000100c50088c03c516601c09020b40300f0340c00c0480080803884641d117424038a6200010041885101020501000410540086d0f005460342d185c009001000f084040340c81e428440000340103c0c3c5045c1010030b0107980102d64900782d0b25107408440e4030b041020b0084585203001d1101415 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 779652652 1250 779651402 779651407
    0x2106010e18030a2d02030a0905090405030a08132a090e070618030209010b0c0708070602150402011e0c0308010609030c03060b190803072622170708070803070503 71
    0x3510b402010224035103040e4030072404c614880e000f040703000d03d0358611602016034030115280441d550700403005405010300391030042103810f055640b150350303000e6581c0e8502070207a5503001131084d422640206030050303004074a043c84651180e091a54105200001c040f50320545900441c40346400d015850302601c03058004c2404901e41a0110713010005400d80d4501e0074020840080035944400b13400703010f0302d80040ba15542c4d8030300900d00c1c5d1410b10301d9031080d807640d0032110302040301c107402017207452061080000c50201a0307135901c0100c801d200c100041504d00d283c80745000395503a6000325a0341100d442a100c88170303030f40d8803102d05903a2200301c0d1100030401e2260074014030000d41181c0220004140c098605042c90b20172000101c1e00440d25041000168000b06040c030034001e11055805001c441001207040140002c030411400e44240c031001100250903800b501007120b90300c440070004040e10145440794881c61890380d40c848446200e15007a501c600d0034003054004020048981056001c4021031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 779653902 1250 779652652 779652667
    0x806120a1103030c030a03020414010908030403080702130f0b01020606120c040915240e01050a03061a100906020115080a1e0609350d0b2106010e1803 66
    0x604494400c80706a0507001c113201c0c2e1158801d0030405000c9142c8039440141e207803410014101094002c48020a04107c0c002c08104100c0348084111810b407500054102c2c1e440103540081140e0b00c0c0040a40b4001d2440d200c100458040070303038050f51821a00340d00741d8210741c46901c10865540c0102c20701c0440c3d60040916445540350503800122500c1c03140e28a452810740d10159401110119010a200504100229094400701003010740180c5409180b07082c540d418030001c02c444120a00006014540d250860100301d46007a841c1c02008030001d01c3d0680440046000034210281071207600050341c200140240c0640f00b03451003e0980702554010305440071b09071101050019050030500c0486560010180442d116004081c0c440740a10704800c040841d00300007640709445910283d100ca410040485440d0b550001250884040c810010403040c00100000b5080030000c000c903400c00700c501c10400c0740d6440110b5414101ca01003504104da940d02c004100399150001d0740310340c4c2503070070402041c07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 779655152 1250 779653902 779653913
    0x1306091d01060225030212030306030d1e031e15090b090402101803080a0f0e0105131701110714070503120d15030b04060e010506010504050105040e0c07020904120806120a 75
    0x8040b68075640341a00c80d0f583c86d004102e940340310480010721604000300300096401d0402c4144000440d9107087c5608003003601c928105044080c0c403032810183c8801c50041001202c40c5544040603440300101f055441c4c0804034040c40e0454440d0140460038039040d80700914206040c2d0748580e0300a0700807000c40f00c0400c822224441c0c0e0907504000c001d082003001c008501440083e12003070100381c80d0074500c2a00b4100161010410741c04440c1080010004070300d01c000c0018150b0126840e140000220341101c2088a02420041d2086c0d4a20381d4081507078010b002621400f119211150300560b84605c1c0c556040c1505c031100c0314140740b9100400c1040f96041c10340d551101c2e44003031740031410310f40b2a61a5550f4907000c01042d14140d5185403a1484201030300d600b8490141c001c5c00074208a40f030189460001390580c016440382e1000d0200340c00009100c040b2502c1122080c513401400071450349040d24046130001c0d80d45a03101c0002d04900001001c5081c041091f0f60140ba522004280c0e1960a90f42c4c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 779656402 1250 779655152 779655193
    0x10c05120f040c1802070204060f060c0201030507210902092a16060f090c060504260a081318090f02060309010b090a0b0f0a06231306091d010602 64
    0x441c0d000e1410750380007032201c0c03020032035121000c0310200c0586c0d0707410903004100680344585c002c0c801c00b007000041001a0340d00800861407055082c00d000c01d00b0b0f561080e043d228806415803001904410020310255610307141c1c031114605108032a000d6841c0c940c0781e44003180c5c80c00310000f00c51244145009403200c00303000000e443d0f0300c60352420001d4000141d683d004c1c00c3d1780140900c02c201c3c5807900159402c021a405000c006400705241550a051401088036250401c0d03001c0403106200c0100800c0a10409000702080c084d0080c448a03540ca0f2200740440995000d44500c802406030400f22205000b2a0700030023201641200e88500b0741c94440c9c0030070001358006000041c403590307070f501c4001561b102d08110521400c40c208000850b41d49000c140880066044106072140084000c1403002a8215092070764481c0e0510f07110f0504028004d00c04410b100c0c00038055a1482403010024066601c100700000f40c482e6890300351605d003000d105a0098030400e009a9000d82c1200b0700c80200700382c0002d40b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 779657652 1250 779656402 779656411
    0xe0303070f1b02031f0b010809031b01091a04031206140f01120f020c070503060609010311030307050303010906050a0b090112110d0911150c061b0c16030203010c05120f 74
    0x1207101803810190f0000b440c004400d0a0b62059081c01d050030401d1290382e1013552015402800c283c0c525103003a48019459200302c4460004d021054004903100d814254880894582e000024a03032680640941c17030030002d8103c504500040301d00c0d208400350806070250104a41c80d409001284d164407608001d0100c0300174001c0340c1000300c0241851000b0f69180100041c10040e0380e40140c1d10141e03003a01c1c41c20a04150040b0f402a0b00160612043d51100c1035024116900002c80c2d04e000c0b4241e1001900750b108815000d44035101c0800040383d41d140a5005030b080703d104071707200b40394240c3c0e882082d4014003694941d940031582c0100e0010006d441034020b0f180045400200034a0b20440180280840340d00c404140c880016031000161a0300b031400746040f071203c951100d1030402e078111424603511380008004080750b00410242490302001c0c1c009a44c0c0240d548800d8079058205000051515002803005030b100398281307400240038501803000c907140d4801e10741700340005c0d9039541d1041239020f20150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 779658902 1250 779657652 779657687
    0x120b212409070501093b0a06060e030c180c090d0b0619030308070807090f3012110111040602010507020d0503150409020d0204110301060314010f0311040e0d0906030e0303070f 77
    0x1040e6104e40b00c40c02064483c20000c1c1c1c000981c89c0c01d1600040c00d4000100132180258030003442203400769a0002403c040f0400300c410400c480d0780394044c0100c2400748103511a00010045840420885840001d6208080035591151684040f0501a00324050351001501046a00c0042044684101c040c141e1010780f508280e517405c3c0c0e80d001000000c042652002e00001070945080340c002110b21411070742503010b034140c0c010616541d21001034610702110507800384480c003020f074601c1a40a42040316504c0380040b070756843d20359401c0b0290203040c0458100b8014043c2c1410000c1d82409942500c0c000c0748d100c0060800307000f00030103000040118420a80c3c5c0080740003001c2e0011ba5075406148080d844030709150b1703202c1d45088000b80644403400b400802c0321039000018402c400c01d03500303d4001c490f080ba02c54070b202c50034000824001d15100554424a0042101c821580c1d6084414203003100c843d507408201c030a0880103059180c1c00103480103c00102c44a6100744114410902000d9414501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 779660152 1250 779658902 779658989
    0xb0a0e0d02031c021b0328021305040201121401091d0102030109020406021009021c0615030323030105180414030406030507120b21240907050109 64
    0x903000245844541034040f03141250042c0710282095061080ca140e000c40d89600c2c2000002d40780001e0f032034048007044481c49090307114412407040408200491140d4001d4400002031405001c080d01070300044405a0100f200c0803141c4407001c5141c82880700b0341039441501da6450b42402d40300c2000e8040348408100601345d520130700418803801c1c40190f0083c9052170300180d4562824501908081501207880040e40c0340c9014a00980c139290b03c500c01c100a24104038407180310608d8040700401842d040390152038040d2001104060b0820380d0038a5220b9a092601010186182a03e59a05c0240101900a02c140e03050522102c4003080d00b6400c41c0c4540140303000e10a0281c512803941e0404c1d0310150001c0c0c0c1319010700c404160070540e0380b1070040024800744640c902020224546002001d603400c0c0e1042460b80e00d00074100c060110301c80300c24011307c7c090260003015229000c0c4810690b5584640d024403000060650f000341c156004035940109450b00103607103191480650303809a84080f0210340403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 779661402 1250 779660152 779660179
    0x803190213030308180a11040e0a0507060305011e050618030a1b0b190e030f0a060501090501050603090d0c21080901050901110403170903120c010c090b0a0e 69
    0x450001c0d000c103800300000c50640754070b1410001c3c84100080c203292506004015030300700d05280402d191070526000401c2c1d44000e140800490002c01600c50004054040d600410381008008140c444c1220401e0364140704c00d90f207170a64260242e40c585071001450000410410a609100b40070b03203003d01c2a0302181d2003280c040c00120f814001c0030b6000f12510540c90892040302d0542c000d40308054284040c03928146a40705900010f08024040c80b44140200e0040d01039446d50304100600d80c0d0b02c10041500c0d022001454250302900d000e001c0c40704820700f80000416542000001c1d42d224009003801044810700e600d00c2555084c0d2840d130291800490b03050807000401c40e40498105c5518555142005458521a403900311480500465103503418504050f4140e2031a00a6070103491b0020740c0c034594000e000e10f842c041e502c11995140c0e0103009048440c440c0e0102d51010f01404d20f1050024008010801c100701c444076880d004000d2405001d2000d201e145118070b24004a081c00940f0f80d800c0c2198 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 779662652 1250 779661402 779661451
    0x6141c0602210f04031715060c0c040e0a05031213020607030c060e01051b1b010f0606140a021002090d060e011a0301180b100e04030215010b090a030803 67
    0x5000750418803804461080d0002c00c12425540a401000007400d1828556401400080f88100450710180f2980c08111204014a4890040c00d13000b400c00343d03103550f0280c54a48440940d075403035224900c2c000708140082e002103100c00d8a913901130050362400e408802c06800c2c40b40b0240481c108900c3c420000001030311900020b00b040c2e8002d480b0307202c80c1c031107901e018816601c107503042c01c5083e4109020b209a103050310f0b442d8504001c1a003c2c030781d12001d482da84604081e156882d071148543c00c0011711411074889500210690703042d50f03100140c0003018030351001d9500ca03102d10440183d100c184070000420250340a09504c10000f0400c440702c041c1501c40a0645105d54807440060355100703a4030b0309010402c0544201501e09030024019900311000078610306409140c0540400c680030000b554500780030f0001e00140401c2d101005c00b40c10710f130500950305e10900d203403480d103480010004034a240c03120054880b4454001e000141483c115501d0785000e07040a008120075458101d5454030307101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 779663902 1250 779662652 779662657
    0x180b01060f09090c0c060b1c081c0906090b06061827100906170307110102011803020715030501150f05091806130e0307140c090a0f0e0106141c0602 65
    0x40303250b55502442170307203400c100c4211201e52a805201d28102844101c41c40340f000e0030102019003001815449800001002041c11185009400c03210f241040c0b81c01000050750104160740c0c0074841c40764042c4c0c0c542050000ca4402c612440844d032000f900c2d40c4001c3d00d044441c02503054855207811034090070324281500340c54000c2d41c2d101c1c0c440341c500c842845918040c1c4200c100406089003075a00400000a09649170305c40e050021300403516420042d58181d00035005640182d01c0c149010b0005102810300079190403042c050b4103814100d540d07023801030510902407181030b1560040410342d4001960419140e0740340d0100d1175020711030180280d41c0c60b40d0310450003071000025078122923800d1400b04104100100070340540104245000f5010040b07030340010940f507440745d0201e2001c241c03030349210605103082c42d6401015405401d0360200700860700107801030b284404a81c00700b40022080100501d0981d401405407242217030141034114583d18010b03460415030382c0041c03074820096420b6110724043e80e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 779665152 1250 779663902 779663921
    0x10504030f0c0323060a15033507030e011e0c0c0f0906030c08120901111515010f080c2a0304090603030801060c0309030b06060c06040b0901180b01060f0909 69
    0x15aa24131138000010703070600c041544500c104408004440c491210000380a01d40d000141c030043e0202001d40b0720040c80002d0b000c600070000340b00c080b0840c00c04540d4002c4e500402003100060034119130000a0b50144070002102403150000320490114800203d91458007044180c444042c00e80b40010280c80fa5204035000d46040000031070b0488c02d41c10841e102d0320141d030018070103034041d0021400000700c2034180c401504091901038103401100444502c0c1019580f2101c2003d0030710f0081c80441c07125203681c0542180d0a885241e012100303503c0599001e40c0c01c6230380d0382c00f170b0350f00b041141c40c00200840d186030304603014081c0f00920303090b6a9625141d600030750000c17050710381c1d101811300a1542004c070044c0101224a000d41920410742c0e4002d14948240c800141401c040102050682d5106000e5a601ca81b000d0100d0300c1510b403d00b8a41d800781800ea620341c0c1e03c5c0d442c0c0442a1464160a00d5071603d154100d0103a8003140d1030a01c2c1100c0c2189840605401c008040c140881ca00801d40070784443c0c2c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 779666402 1250 779665152 779665193
    0x3170d09050c100504080309120a050718050603010b010801180e01060f06140a120908160b06240313050106030510020a030f18020d080d18050f010506010504030f0c03 73
    0x54032011052201d070030350710050311050103c244001c02c40000000222384402400343d54405040a00074074851407c004108024920b001d211000b1820402c01c0101d40d5445100313140c14007607034032000181400c0702e181c40c60725030002c0c25400051010031649130a43c1a050240000040c40c0005088a42e00f101c2c0b40340c01c00d0341440b0740e8030010003103142d0004c09110000c01c2a00e8852900c00c44a8014142408001d00381d031040e502d8500000501c140740c400e60346200d0001c05001e420203160b02d001c1e001c2074012900c1c1889041c510031030240481c1c0e010301420040015034061895a01c0e01c030110000f0141c0d2040858a82d9200d039000b10001d6414444520859007008016031108810740340501503c0402c800624400d14000081d040c80d284a4000041b244c1c050740d51062440550500800034840c0140b9210002e007464540100300c4207540000070410301450680b024403080d9200b42d0b003a20400e0b0341c0350340051000d20040c404510000100c40c202840340742c0e0a003440350740350340e05500000100740d0f4041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 779667652 1250 779666402 779666413
    0x709061404020301060c0f0c03080408030a0338030c0a15030b010c03080a020c070512100e0304030c0302221424012a020d061e110403170d0905 63
    0x108803510050040050129020b504560500c0700c0108101183e41003d0315041282c02810305100381c400c0355801441e0000a4550b44548a4000c2503903540700d01c0c66100001d00d40b01424841035007074040000008007460a90b20100072030700203800c2d4003000c1c07000320754180190499100c0c00e42c1d801d008200141140b0041600039042c0e510050200c510782c1c41201d040c81003e0301c144001980c8070b0050f903480b280102340182ca070200704401c24a40402c2e504007c0e004841d8515103000701c0400100b0041d16001c08001744401181e5500461b128016440f0081089440e20014030042c80e1040008040c106406140c05d21114105101300a0b075003503180282c01c10706840f00b4040251520010914046001004803841c0d83c01000020f018480340c0c041c0c40d42c02c1c8800c064403004a41e811490b6540960010036001c4410007600f020f038020b0840700b003448070707194101582c04220f000d14041e05409021160b10541440e00d162200211240000315440c00c421040000c00030011881c804c643c50716000300c0081c03c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 779668902 1250 779667652 779667659
    0x15040e010f030b10120605070c32191416060c140607080f060406050303120a14040f020d02040603021e03011a1f051b01020d05060f01080402041d070906 67
    0x9440d100050810384c051007103c9010b1200c885688591061035900120000305a41e40c2c0c00d040b03c2280c1e540100030011600340c041ea00740c41c11048810310490f42004020f080580c0c5a81d480380d50307081e0300030070201d068800e01036010108401ea51000324841100d8152440e560f204842002c0a82071307604800007040d01c0004031000d00c003c01048040b401c00241c01815103082030031000d042c4d0301000303085240300340b07940b030008960307407034640141005010180c11130380c894101c00100d0b1000d02c411601182d5251804105551030b821604280e40680d030400e00e0044107135040d4007400000492400c0c181d0300181c0741e01001005031284880603907101d0a1402d90192440800101403c0d518414500308105035080007130341311503075108215815000f0354050f200814200070340a850500902c981c4420f203a07402c80c0b400e000010190001c0c40e030651040750412007955004200090b01144200c03070381c0002d681c00001801810581e020581c444086034080e1440000304803510b1910849070040705000d91609401c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 779670152 1250 779668902 779668913
    0x150705072310020a021b0a2606090d270e1504060e06060d020d0b0904050303070e220f150f0e0105060906090904030e0a030b070809060702070515040e010f03 69
    0x2d500b19540399005500d0a10340c040020340c0c400801c0007805c00283d00b10f8000600b0340c1c80b030b40d0703140c014074400004810401c200a1002002c0442c60600301e6140242d40019260718808200c0012550681d1a481400a154081c4100000283d050b0b20509000c89801283c1051903014039885910000c0300d00e000d6800c19020310043e511164000609010740500b44081951840c2c207403001146403040060b00d9540c1504c44001500c2c00076041d6401802030000c1c4420301c8004401980f04100eaa1140d00c1d10010b40024403104201c10300044001501c907404100c0c101829400a0501001c1280041400d40743c6807000000402c0340c0d880032001b00441a01040381c64040703120580100012600700d400c00e0b010001241044c410305000c0f6224500110003e0109801014400400c42001d000800d400f03403031b0300c0c160b183c095080d01c030030307011446100c002740010800040c01840b58040b0b5001c1e0802c54548401d0150f1100a0541a80081c46c188004540710001c072150900900940c01c409494501c1c50810 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 779671402 1250 779670152 779670163
    0x120c0c150601090501030c030b06030f0f090a030507060903210c0311031603052701020702121f0b0a090e0c1005070b0601050a030603050a05070509070207081507050723 74
    0x54000c154a803004201190ba00601d400c01214801e09000c104403942503402c030001d0590b41140d907403003013001c818003a4030a0410f0034070344200300c5031064a031291900c00c1641c0e5629081507000700001c00411000300003940350303000140321a00c01d0a00010fa2141c3c020b080c0c0f4111400e40d1720b64186591600c1500007144d0601480426032030f035082d54ad2a508041e00160b05400c4007603a001305050b12074000c510021019415190301780c403036140030035140307010420040c041c0d48040c009a102d04c00054401030065004606044248602c1002d25042ca1700d41154001401840310510790041c15044002016a994090718031a6250007015005019224041008143d8203003100f604001e000c0c004040007070104191207401c01d43c24200703203868800c1590102c0141c500358000074142c1c0615244041080380c0080d02d081070780c02c2155260055076503680201d9071032200d440b800c101c6074084518401e101130382c00d05554008000740380c0f591400070343c0c0d04c4081d15000c0031070301d0b2200600201c1100000001c00e100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 779672652 1250 779671402 779671423
    0x90e0a061805071205070812040303030501150804060915020706023123060c0102090102011a100e0f0d23060f190e010c0e1201060b0f0f120c0c 63
    0xc0725030440c05945645035102150300614501482e03000324001482020040c040051240c5002c8032403c54000507070b03c0c9a07401070f20088022134101400411642c0300a0003800d1907500b0340d0746059803070740d40c0d482e00c0000d0451000c058401d540780408952031100340b0700080c46018001e0300302503540d0b94044c08030300301040030102d01116119042ca86041603d000c80218081741d010350114001c0d602000441102001d240504ca544400c1c00203a24041e894190003800005401745c00070401d2640040c02611045881400c5550040104c803060800304d014910072028580f0141074007000200c1c11000c26021202010300380d4224580c0c24440040d2045580c0c2c00e00c1d80d048003000303480c043c100035103a280c807240041d0a03221b016070400040810681c555000120035107051000784844018002c0140c809109417807080d0288104810b0403081c0c08050154804441e68440c02a207003603144442042d494000440d02d10300d0445c00c1000801e0140c684010034050b4407120b04255541200f803482c1c6180004544 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 779673902 1250 779672652 779672681
    0x40e0303240a05060a0c0309081501031a07140d061d0118090803070804021207030311010b06070506010b072102011a010206040b160507051c0e1503040318090e0a06 72
    0x807001d203e161100b800303484804d121400c10000b00326461505645080b1540c000880520075403410000640c2051039890480307000e030805a40c1307d48602002c18070244125821008503800b04420030100b0700c07480040072201c4084100182e03640d1101101140d0f1210301c808629251403070070040c0070a150482003180100d010381c02c10000003046507500e60860000070b182e5414040700d180004c082d034480002c50090080e04106440c0b07007075160f1a0113064940301c002183d0329513182000749005410400c04548544c0d82100c01804540c2c6031820311002a840744000b03c94140030081101c0402000b60010b03441c038049500085140342813051441d06884410900e141194071800c140000718040441d07954001c80d01e0382000c0d46103540c41d2820345031482682801841c0c1c0c460a05200310001102910b031412400030741e5603514868a1404110001e011407841005600042000c600041c2c02681d440400c03494100b502c203809540e40702c801040715982414910950050000b03102040003600ca12008441000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 779675152 1250 779673902 779673919
    0x60c05030103170a0e09040501090507050a030c140312041517060d0f020411070b06120607020d110c1305041b06090b22060207230d060b040e030324 65
    0x548030600d40c0042c0f903001c4150002e00241c1c9a83c440d1050200c3c56080c0005041d42115081501d000c900034540701d482a6014021201c000c1142d14020041404998000180c0710345181060303100d801140340940c0b60359141c030074602c104400300c0f080310285c130007884494282504441010000780400500c100c074100484500e030b08110550b51024200341c2c03500d0304055680e00e000e145101203001000003104a1842030000f103040c4040010701c91043d0f106100035201c424030700c25410301150b9650740565441c1e0147e00081201c25400b07201c0c5560591007001c0400b100c1819036003901060717000b140a25042e51840d141d03420130090141d00100c481c0444010051031000525200c4010f112a040340034045080b81c6c00900111000b1009100c400300c0011450308001c15655488040e40c0c03805644207245416203441ca0b00500030400e407043d51206200500070800e03401c0e01c2d50747c40d00104002680701c2ea100707a40c0c3c1c19499884c80c0c100050b62041e070030301e00e115204680c1d111190499610b00010300307119030380a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 779676258 1106 779675152 779675159
    0x40f0216060f0b1f0e0402040f09150b1e040801111e0328020d0606030b010207080106080d03051312024b0f100207060c050301 56
    0x6007000c001c000040d40300d41d000d03252040c0c143e036032100303811660303201d28800308080c0250219070346070620307002c08401c0016049070020703001380d10310300c0510700305200705401440f650484483d0050109c10661a01d060305e9141c2c483c94040054590103555001508007450003514081c104440080c081c0503400e003034502640e0004a000c04079a68814040244e1440b40d40c2160300400c2d06140c80e1000318903030038a010400c58448031300c40c400d0707a00b0402e0020710400b43c8144005032002e80d4000c562510103200091034a04550466842649440e07000c214448000070a000b908841d4200490655034212254030481c200c09805080b002070b1003940000a0ba0208102c072011903190820740c2c5000865844c0400c921310032b01d03220b004a0098000c2c0b510000c42c88080c00c0843c404400701c601e0500c140140d80d00700100c40000d82980340e00030a92038100070a900640000342c0c141c2ca802820b5624 = true := by decide +kernel

theorem cover : BRFrame.Cov 779496402 779676258 := by
  have h0 := BRFrame.cov_init 779496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 779496402 ≤ n) (h2 : n < 779676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
