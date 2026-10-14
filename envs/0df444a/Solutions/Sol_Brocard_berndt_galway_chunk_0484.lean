-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0484
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:02:36.158475+00:00
-- url     : https://prove2.me/submissions/ffd42abb-5398-44cd-ba83-241a3068053e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 86870504 ≤ n < 87050360 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 86871754 1250 86870504 86870507
    0x2030c0d1806140f16050f04030b1e011a030c0c0a05010501062604150b210d0f020d180504090309030c0902031b0304020a0509090a051e070e09070b1306 67
    0x1040341104000c1049421031030101d8001c3c0c071440004100044036070100011700a0a40245e04039030050b008441190b0b40c441c0c4a041c040401c800540e5040844a22100b044850440b00c540c050f040c0d8001460521141c0c0c5982c8081005d90406044135140e50340402003000420410054180d420b0b10030000031039250b00d8024090202c0301e01c200703200141c0348020150a0095294200a035000f9485440090380019009490000703055105900740c001981c10060b40c58082c0030442c1d02e0b900380010003280d00c084480901100c038075564110400151323100030301d240103450159040582c1000300400303849940c2d030b80710700003025194405400d90110340c4409060041c01006413503180981844041946507082890500501c3c19078036080540558005c0089000c56460344800d03001884020003810150420184050301e070007030002c3c121024440c941c007000800d0350013090485680c3c41040502000703440e10701c1e82402000300404146081c015001c01060078001e40340a404a0300010b9850041c0c0b5090080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 86873004 1250 86871754 86871761
    0x10e01050604020c070b0f040509101401020a0c05130e06010909020117040807030c05030c010603060f050a0603050607030207051608030a02060c13140102150702010c02150906010902030c0d1806 85
    0x14038016801040101028a000070714041110440e480a40d51401c482c020940302340242e800c6a54410421070074030034900e0418140c8420340d9440341400712504c00c59801aa0b0720901a14001c02810f030910040006290020341100310f45940c1501181844d60034603d83e0820f00c00b60000c1742d849903207004800940d64482101042c80841540c5400e8605207a01d500d2482d005142000301009004103060080040910903108940309000007840115224601080a008084941e01c090f600d84000102c07075400c180501c0301203d40100c05000d41d030712141022000b942c00f0000554840c86081054030080b02c06410040003015060055074450310503010017801c1440103040740b61542c1d01400000400603002c15182c0403591503810440700e40c1803040041c1d00741038507850400704200b194002c0012080d019005140101c006a0944042d00c2007280c03503498054003582d03400070303540c482c10050108504603802107422007000110f09040029280746001683c24511510440030505010681001070501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 86874254 1250 86873004 86873011
    0x80402040f0510140105120f04210309060e030310060806040e06040b102301182102090c070510090f05030403082106010c11040609390207170304090905010e0105 71
    0x80c106141402c0b814031f807100690040c10310010b44400c10302007020004130201501161000d142c9091000210a1014004192030141940c03078500701a40340401ca1030110450388240544480c0716600c508180b42164078030401414690040e9549046520803001085445d1140d8480c51802c501d03840c003d006000e50403010340c04041c00305000300e4902d03640308101445642c50316081c41d000024600390640d07000001002d5205000e1103202201c1e000c80c55845510b00060700d030098511041d59128050b01000c1480380c100041d02503001441c081c013044403181c0041c0200b5004554122101f4029205c0504562042d801219400400219005401e40f4508441004c1054400180007031610134000380000714140001090144880142c42c2503544642c05272024000500c4200548900c0028407070180f0076282960754a95440c3e13250145c0300380781c600354803181e4036182d0180c4500e5151642903d0700d01e19210000e5910b0106100200b5150760300e126965040303000303d0001c5402e50020904034215800074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 86875504 1250 86874254 86874257
    0xf060905062a2d1501032916030c08060a05090a020909010e04030305060a03151e06150305010504050103030905061b010213090e0a02010203180103090206070c03020114120106080402040f05101401 86
    0x3038082070113194880b0740c040c1180e40161800c1010080c0c8026102c20030116130009805100f80f10502c41442400307100e1100d00301903602c082000f6a400c480c19210305008032015035000c0703d520030034007883c01c102a4550b0004501a0058201002d41d00082d01490007600940a0314098208000c14107a02d40145600404103803000b903619810754075940c03042d0364841002400d82d0307100e0600c040f480420000301c0010700d1108004100850b140c056002e01941c000700c010340043e040000200e50b5141a2080c1d504a0f5499103e50960624050900c041c1ba00700014580e000b000300345148209860038002008007a00f82030b03901c03070007600780814042101c0014241d8212a4007404031040142d03000030480b2800c0d0f4a080e20004000300000c0120043c002c0c00c10025044080403404a00308032901c2d000d1000d89100343c03a000c255001e43c0200ea1500d020321402c0102c0340c80ba51004020441c0110010394109001500100d80707480c070800c50b5410f507101900e0703c19401c1500f03c42004400340c003d0540f41d54501c01d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 86876754 1250 86875504 86875513
    0xd11090a020c06010b0f090a0e0105040c11070317070804030f0c060f0806120a0507080102030915040f030302160b0405070e061c060b0d0c0f0f060905062a2d 69
    0x11121010f50b140014041d06046050000300401d8075698002990400840180f5171000c054031101039116200007840340074000c0d0700f000c012090300c5000342150211030014034002c01086145403900515941d142e00355001003442041481e01261004006002a40c05581607a0300c01c00c031480c2c00480b0020a50001c8200f1100064481500354010001900070104031080b0308500c044c44149806c01120180003440f80c8100d1200003035100c0190042e40c401c5c1d4803482a100c404902101c0d03801c0c0360000311070040c10680c8010015000074040d40c0900001c0c0d04250030300042403200c1d5520703400d100341560705888070751004c03608108020100c1d840661203001542c5c494040a2048102030042d190b60301c000300350795180c590164580d00c1d100207120070b064104401e0401c0c0c42da036485142e81030303c0714081c0e0204090048000701e6114000c81540b01141c20140540c0d00c1c107142400c090109903000c2145800680068100314414075007004180b6050b813081e06402c1c1031880381310501c800c1e004108103000c0103400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 86878004 1250 86876754 86876767
    0x5070309050109120312060b0c100c0306050603070503040302030f03010320060f040306050a09060c050c010605030703030c0b1005060f0c070e0f010e071403012304050c041205010204050d11090a02 86
    0x3840752091035164142042c2d0b2a41b0100d00346c2c1c00c003030b10554018144802000c9450b1000100c00242e003280c802c25110300300040c3c0c88004c402c40c180d8500380592600000c0c00c01c041082c03d403042d03000355071203402441602e08001056607290300a5000b81c1c41a00c02c45080c45600c82c41810468200100c0c5004031916490300081c4903014000e4050342c0710160525584500180e44076020760420030382d066101000700031b1010600c1010b441030f003060307108030000e600c3d1030300c00700d883e08001450700c003a00e416441d42010ba01c00c80c1e4803609945001002c55140c4034040400040e10340715500909400359110700c00d50f8842500110b827901d4090158081d0000451150074881081000048203040d94084540180c040da501942038841c4c2550300410309014a000000044000c0080701c840030304d4680845000720482e01e9820002070b920103030303104121208100b01c1000740311030044c02c00e0045842a8009428541da501c00100c95242481098440b54055200303503a29182c4104226400305144004504105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 86879254 1250 86878004 86878019
    0x1b0519080609010b0c0109020307060305090d0c0203030d02030406090209010f14090412081b0319060501050702010e0420040f060e10020303010b07030c05030d0c020105160804121e05070309050109 86
    0x208103105420304030a0000c1c640e401003101f034100d03018854000e0200d8000503501c06008009000480d8804480e0045e0020354407118403450140c00340b2500240118144018141c01c0002580060001c441035640c4694040068903042c0d065030003040b109801041461502641c04015400080701074031800c0e4880420001554002c40d0310030f85c040b117103042192a52442c242400002e90051034055400000c000c0100c0300300301c040c0c0d810100c04c1490082c80002d42c2d9400640b01030180d1400203002c0766001440010074185540080c81c2882c00c14040135584e103900d18085030309d1b03115412001003c0610407007486010707040307100600c2020703040d981110800c0c1d540000940702e000600401c1202e0200003100f00900d48100d0000310003d8200094940c0ca101c110000001407a14047c0c02016501701000150400450740e1943d5018400d0303102e1034099a104d0340d843c90303030020004506050060310f20b244541c520922a4803039074644903031a0785540361120305002d40300c088140d1100f4100100941e00b4400b40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 86880504 1250 86879254 86879269
    0x2010813020117040501021c0c0201060605180d0c1205031905070f0308060d0c08060f0105010e0f0906032506020705031b0d020112051009050109020309120c011b05190806 75
    0x800c3e103252050f46032628038007240a071107410031410204500d15010b101c5c0f262554880510a0000d4000700106a5512000c1e1081d005c0c042c200283c0b00140004c0030080d091802c43d0401041c071440e03152500c280c0f0380c5800020201e082c41c054a150b80049020172224043e030100060001e5941041d90501905075030755a4400c0031840300500308900030011400300e8980b00c114101c1c16511606903590151a018400d0b1b4840084444405e42202d220000519501540c0d040d800f1000c080c0409500d28448800d00030038030000390000380c25105850a0070b8141c0360740e0200d58100718040d1144141945042070091412020340c100074440c0c0c2040009041c50800014403442110084c5c60342d0105580758001a95144111003c13407411900301010040c0041a01030b1903c190307079842d03400b000340f66203c0020504034081107451030b01e581d0281d0403131b050903410ba4015041d110390380800405c0040d054540c08a00106070f20340440403540100d03602d00e002e0203e00312200b00c0d001314505000c15150004c001541c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 86881754 1250 86880504 86880527
    0xa0302210109050d050720030304050d111509030d050306010c0605150a03030306080f011503060213081f0506040c02070302010f020f1c030606080906070806061902010504020108130201 81
    0x50300d03940e200c0040908400e400c0480c4181e00801520344000c49080054155400000100c510403040d1600440400c445009484d010304098021400c250511080c1301c8400742c00708044e11000207c0c21001c40301d03a6528400348441011403000d94540c600c141c10705190828161505061020034000c008290340d00c1185000c41a400c086c0114154882e041500d070807149030107070f494001000e00400300605400d60001e0007180c1d4640300b152105c034009108182215111038040581110409041010039000e402901440724843c4d1505001c81c0c1e5070200e1844c20f440c0664001c1003046404020103220440c1c81100da10175030a903010f21064050b018000d440c0c104c1d6000083c144964050000e404910030401c6d014002e07040400c480804440c0d003010b19920f410104000300080c01d2850100d501481004064041d4074200c0083c41c20351102241031320b030700c03400415040d007081040c4040b800f0b691110341c499074049403a800025003401d003400010f0041030004c1500c07041e4252142d2440050364400b60030f030034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 86883004 1250 86881754 86881789
    0xd15050907080402040216020402070b0603071d010e0702070f060c02030c06041202040f0209030304061e02010c05042c070f111c030e070305070308040f091103011202040e060709030605060a0302 85
    0x3d03241c041c11f00c1d1036913510250708043c1d00a0320206034072080040f1441d4090058001b1021585201c1c0d82d2807040c00b05020079000d4170002e00c3c030000108034035903005d41129049080307030045e9452a81c680000258001c1264010b20008600d40020419814140010301e030b41c04003034542e50b2900d82000700c0d070032055070006c030003e010f0342d580c9044002030646607050b12180c0b0306c010700740e035583d0b13076038100082020b0f204a025445904061100d0141030b4014800c0d0110900c20741ca0700c0d41840e02d0248001030032a5964a00803680d10f5001c00c4149081c1c1c899803940c490f15080e10740354030348660716500500c0071500a60850b40799100044551500420b0032406446040034500480c8072a016070b0b0040c10415182d1006060b80b0989402000b000700c180c000d0001d890603100c103152403079030302e40b90300c016140c404590403008102000144940c00c006441442c94500107400401c0f030b480c840410901c0d0100c21075002e4001585142d003802004018000c0c03a030083c40444900c42140d00f5500025000070151040700d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 86884254 1250 86883004 86883007
    0x30605100f0c02130501081515090403080907091529042112030903080703050f182b110a050325050a050a0201270501140f0d150509070804020402 64
    0x401c540e07641c04800c5202011013010b1040c0d584d548610755807240d81c00c011007a808410800078086001c0c041261201440052424a040c0c40e1500c003541d016002400b1804103018803100811021014020000c001d10600d03691361b042407500c1c0882d051b4100c414800d8425a01d0740010814039490305041c0c0d015114846070118081c5610f07a5120880d07050400005c0c59100b9152070515540c0d095031000444034002d445010ba030743d070f0741710040701200c1044484c12031000798500461200c1c0314115080e29840191300849580c1400e004040c40440c40444030f0880c00f642448202040903070088125581900d401d00030202ca0040d60385160302c0e4024070208a04ca0600d42c64482e000c400911003200ca0240c0000594030f5920483c1003139502c03541e01590990101e1725400a241d914a1406412100c86006a00090703006081c00d004440c101c10310008084005024003001d1590400c00300240100d1015800c0000c01285411900024680e942c0c803403403185003a642004a52600300700096441981142d005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 86885504 1250 86884254 86884277
    0x1020a02012f10050114062502040b0405040b090f0106080304150e13060f140603070f030213060905090a02120109110f0406030e060a050603190606080f0d030605100f 73
    0xc00041015650402c0342c3c030a01d50340d182010060350085041e80d50381844a408560b801003401010300c903511303050700d0700507001c00c6c5c41036409a0f00c8102c141c490301c0104086800685000060207403081503405032141e116910601000c170104014042c0442080703402840300c18a0810a40d0700d038041c900c510340c00001243d413000c50303c5108280101480600078101d071203107810054114001c00b41b81c001c00c1c040749210003010a0855800c54400c1040c2c100418a501c0e5075955101121090608003001041c903800b80951003038506031400d058040c1c4003c3c0d5842c29058038043c200511000081c2c1101c00252040000000c2c0003156560b042c1507840c9000c02041e014400015045944184034020504032008103000c03804036410b4010b500b00038200f0341120000d44580310007500f199020761380b2551582c03280c0c4840251800003500201c1903030040c1c1000400641c4e031604941000c40c00b100c0700b50b054000032800c01d461074041c4038440143c0416200000451020040074101c070604c0041c2409010764803011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 86886754 1250 86885504 86885567
    0x30f1503011802010813080301030c080106060504140f0406030209072304030507030f0507090c030509160608060f04090203030403030201050601090821031801110a02010b010c0215070c030609080301031101020a0201 94
    0x1b1071283c0c03035010203910380e07941e903030704081484000e00d00030a007a550808000240d224411800d46080c1c0d00c2c1040c24848101d004000c100c8002c07001a52142c20a844090000159035008541489103003d502e4046441d612011083c0d0882c00a41402c002c5600520003800400e1000400310141c9034044440c90404c0d0180c00c025141c0b207015401a0b519900f070010042034203a0580140e8056280c4001b281c102504100000d0451449230003500001103031240003503402e107420303004503c0c40c107000b6100048240140e004241140d100d5001540581e445205001580d40e021705010014402007015000b8141a2250005045d00750304482c10700c0030b404400300d07040d109440c1600c1031100c0e000d002007200e0304080071400c80d40c2d041941d90700099441c180c400c9811354001c44030b0142c3c1903801401983c0c4c0c0940c81c2c1942c680c50300204026910b2440c041c6012000a525110b1645841e00414006807a50f2452902407255040c0701c6015046401050b181e40051b60404c0a903008030b0014201c4450011408c0349 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 86888004 1250 86886754 86886781
    0x702010210020309010c08060306150402160b0108010c090b030705370903030809071a070309120b09060a060e070e031c090e150105071101030f02030f15030118020108 73
    0x1e901c0101d10020502940240552041c441c00d0710700c0d00c50802541d6050105030b150202120022809034408002c81054581a8010701e41e8103070f030340c0340e0100200b2076031580c404600098100300c215070342d28000d04c0700194000c000f42e0300408019500e0b510718540b5610003030050240b8040d407255100510055500003c07a1240402004070140400c40d005440320b0000308840f081d0710098005c00c1001c400300314094404101202503400d01203600340c81d00f21000391340c1c100c1c1c2e01018082c1d040050300c00d000300f03110080c104507544050144a00848900300010303200d007001405002d10711b002d850148204240c07541201c0c1c041e1311a0140c01e00034854048800400c0c2003140000d04058501e025100c103103007454018a8030350075940d089241c94442d56540032410040070120220030b0110b1418444000018850452940d1415041c0350108151040c0076181090380c1043d50032001002e191070070440301c82419201c40c008404110b000b8001c000080401c0c54240c1d007104400b038100306101300003420316400c241 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 86889254 1250 86888004 86888023
    0x2011b060b06210c04060f110304080f0708100902090106030e0715030c11010b2404180603060c0305102c040b040b0c070b07030c02011806050a0f090807060207020102 73
    0x80c0308581c1c4143c101e2410700301c502c02d81d040101410001c1d010601680a99066074140e0301d8a07119061000c000c0c480549484948160841107840100300c0031070090010300c0b5164480c0c03401c0001308425803c200c1c0640c00c0440c03807550a40c400c2d01d8401c011000da03881a058904464041c20b000540e01c0d400300c2820f08001143e004041c07108092004200d6280d4198020701762580d50f5658000c4021180200707900f62100c4103103c0c0d034402c91601001070307844d0302e00c1802500415040c0c032180c81d01d41c1e98200011001c04c60a100c60340640c0d259020024852107000300d00349110340b0700d0200003900c3c10f03605d11400c80c2c3c4903009600c4c0c409559041984900d03410102540022100728520009103018a030204d41c0e01001c9600b101c02d021840c0104154454050030303540c502d03512203c4c40c5030300d9580c050110002c01103003170180119900c80c0c90011a0421601c00f42010a00414000c076052804460318130a6810016000a6446c540b5480d000032032812000e44000c1e81e40140c015a0310001400104e241c1b40225 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 86890504 1250 86889254 86889259
    0x20a14030c12090607110606131113120b1501021b0a031b08070609081216080a030c021c050403110105040f1203021005040312090813080309040b060702011b060b 71
    0x20710520002900018544d4419050741d03481e2200100303940f4681d5114401071394150741100040d80c0d01c51406c6116000441d82941d85421241050007036030080c0c41480140e840241070b00140c4c8880b8050040411550354410100c201d602615440600001d41d1292105205400010301311422748440d0380f4000030170015900310110342040880042020804c21452007041310078816100000b94503805030740b07038004560b2400c014108085510b040b0050b1030b80002c0000e0381e5545501040c600080e41c200c080d05029056503000900040c01a5000e483c1c900c1102a4000026a03051480084c50340401100c003640d51184084c000306d000c0400584440c00f854102a0b4851000e04000c1801114815481d0b1300c02d000e40c0c2115000d08079104981c04a03041a200500060780d031400460360f030800360f002042000e204440d1a40341480c1c90008003288000d980140e240b0340c00c00500b03d1840c0c603080c000c0340c2d040d0f0022522240b91184550010b80240d2442d40c04191034903042160600b40000d80c1e229a80001d4003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 86891754 1250 86890504 86890537
    0xa08010606050d0e0606010203181306060c020a0501092909150c120301050d08070c080d020a03032a08101508011511060711100603050604020a09020a14030c 69
    0x1110380140250f00095422114280b410050f54a030703010006501d0300400e07042e006585051110801ea80a4074017a030003c0780c05c00c81e52181710901004034883e0000400042d59620200b00b154410014031540d00da01c04c03410440c1010050101d8100300b000d03010480900d0110040005a00443c085c050048442c01540460909502d003811600303000104000c00d41481681c1e0101c140c045c04c54410f0000303005013508150748000b41400209020003d04c240b5008814840c0810b58800c0c0140c60400d103000c2c1c84c80160444c441140070150107000c2d60031201c0684207a0500299101c1d0300c0501a00b003108800f04000c034000108481e2802c44201c1c801501d0340c507022080170b00d00d000c070140011200f881a0307402c0c600340d00a00a003c6220700800340c170784055800034100d1501e45a104480505401040c840d1902400d41140c01d4900349201c7c05c0011407003100076210038035150040184802d660b500928a180c010411009174170307408040241c0e5402203102c519203e45403002951002d003c2e401f46020200038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 86893004 1250 86891754 86891759
    0xb0c1b060403020d11011a010c020f030a20030c0906010f090e0c120702010218040c0207050409060c0201060503160e0c04051011010b0102070605030a0504060212010e060907051213020a080106 84
    0x18049020104c900250301c54030003000101030807908071003180d00e4540007813178a90800d01e2035610590310340c0000c900082c00307604500902c03c0040c2c2041440c1c01c0884250a1411381d0540015039410145264407003100501a044c00d0400840c0040000420103410405c0c00c007880e100403806190300c1c4004d0501500b43c00401c3c40d0248a51080e039010a00b0400c504241100140ca0a8414000c0f2100118120441079909480d1000d100c00b602d032400180040d8054050045020b85131441104144e80c06080086281c0e8107020700642159500e4014900a80002e611031080170895030a003000c0760200b40003000c980c0c0e035081e020465801103801a80d8419010b0044803080c980c81408001e41c0440b40e402044081c00b01e0006984d43c9941c3d03c150b4010410034000500c0010b5a40d000640c02402591702610b00f04002c0440513540c2000d07040701e00301c0c0140d0000d00c422400e01200b0306a0000013030803d00d1508452048400020400a00900d55440a12981801c64403400c08800041550a0003071145a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 86894254 1250 86893004 86893007
    0xe010507110609030a080d1512050a06110d020c0106050a0501030c1d0102121605070b1603030b06040306090b01080d0305010b0313060e0f0c01020c060717070c0503060a0204140a030b0c1b060403 85
    0x1c107006a848d00d0f45034040d03021030400104403901c1c514642c020001c10200c5c0d25035507204007400407200500780603281403081d000026102d00003801c1c003440e0400001451030410003040b50402d42504600d0415207031243c00c20f10703581c000208011940c5950b00d104d151940b2200100e1a2003c01c00351008a80400718529044a07408486080c003d0300c188252610192950100c004601906a085029040c12036040d80440c0c084e0b0b0060443e900042c083d149091b88a840780400c0e6000010110b44c0f000f45040100102c40c01481104a41a020314040c030465142603014500ca020141280e000c020100742e01ca0b003008440e40c40703101710881030f0040c1d41103140124019a1940b04618205025010f0701808201c01e2500200b01c4a00395881030031001048007000101c0195040100c0444510040f5031f0080b50b0750b50100000c5c1e105400c04070026a40300c0c2170000c403200c4000420484c50140005000500c00508101104c991021003006a182c42d00381e21500000c2c50032103028000100e0180c8402d00c024507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 86895504 1250 86894254 86894261
    0x140307060603060506010f08070c1103070b0301060206010603020304150b01021501090e010e1c081b0f0d11070b040312060306140a0506060732010507030c0e010507110609030a080d 79
    0x42e40550020003150341c0764001981c10500c44241400090807a03000503407030728052880a201140100c908a03045810000480d2130941c894000400c5e403030022004008440d07040021901404480c5015400c5040c580c0d1410400301d0708460301001251560b80c40d4803264402c201c03068121181003010181075944090440003002c0d5505442155420090164a100b02c0091180c0c00040d48040340002c9025020302207581200107040e03003c11510040b44005445100f0020b41401d881a101550f502c00d048851442254000b201608031034200780a0303a0045a509a9000c1d071043d01401c103004820320341030400000300050b400017401c00d49007070350007000f001403000c0e214461400703150300300244c0d100e0000700012030250010045c031055408842c82c84464080040180c6402d4048441054040410722a42510001c4138088002596040c880f20029808000e501d200d2100307003085890500582c03180d20150540100c1c0600503440082c460940c1d480801600d882540c10404140e25110b4440540018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 86896754 1250 86895504 86895509
    0xf0904021305100507020108130303060b0309030406030501140102031909080f06060a090207050d0e0310060608091515040506031c0903031214040b06030f0d05070501060b030609070c1403070606 85
    0xb40d600c03403c3d240800c0c0c000c1089400054058450f281e4540e40c0440b0f8485002851800701c0070103440ba000040e250200c54042c1d0f000d1001000516262414000000e04440059014411940701c0881048480e40c02104403a8807501c0c001e01d02040382801c0d0800c7e9440c58969121000502c00c3d0a03d18035100d1000c078046000388021102c000304a5a03984020050f805107140c040d08940000848000c0e00d07000da10609138121000d001e4960400b010851307001114503940c044000703c0c44e840200100304a081c0820000454a24015451401c0c04010764a07c5400011180d01950340c03a808100b803603808021161003102c0d1071410000081c0240c00040001c2d070300d0312007200810300e2000550041c000e540110b40b20724214259070b1100d613a6940390554a113501500741c1317415000c0d265411030a104207001e0310400d900b480d11100c2e941c0445240290840b1070562042030007130b0041c82400519696503660030740000031854045442e00c01d5003804018a2081d0581c0f0b40148400a180b20801c4541d4001c2c02c00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 86898004 1250 86896754 86896759
    0x506031e0a060f150b13050603190b0d0c17030c01060305070519080c0d020609040c03051e090a030507030909020307120e010b181b030408090f1008010b0f0904021305 73
    0x2e43d00f0382c0d5119007660080b6031110340b180c84540c014130404c4214000382945164002c040c0e10300e55a60004545242e00503903070b080a00c2038010701c0e400305508a0250b0b26400c41c080c0d940d00890000d603240e45401d210980601c0c6d89103a105060b140c07820b0010416100e003408460000c000305952850000d90303500700c520600e4000e0180038021461040c4281305042220540030240445507640c0080001c101000c1c0b104aa000e5030910040c00680c0340c5104240c0d503a20951000540750030b00095500280380110901c1003004901070400415031004140b460300359078981890f070744500252030300340c13403840d07090b006071501610120400003107651100081c40c3c854400030341003152141c0882d00794281c03000202620380006000a400444518480440390300209994419200b003c881d9000700032a03109680c10348070490f000c11044c5032407030800310000440318121071195410144040140c00900e0510441101a0b00030464125500c4402c003150650340c0028030440d9a110111340c4003401d046a800f6150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 86899254 1250 86898004 86898011
    0x3090c10091a09040e030c100b0f0609040b010309080307030501061205010b0a08190c030203060918070b0c0115061205090705010504051504030206040b0c0c060f0703030506031e0a06 80
    0x611080c001c5100c441520020620810002c60020b2400016801511029002907513949040340101041c805010f81c0540724010b41460074100c0c00d100c00380e801c0e1031a45485820030300a01d44070380c0d846104036000c0c09019540421020a11030068004110500002d85800310020400c8221581f65210905071303600391703c6415000041512a0040342c0090062040715103042000403516400b58001c0c55004840c0c140d60200c0e001c8801000041c1d8001c00c0307003080840c2e008000e2240e40d10344469101d40c0306101d0410301070780501070001107036600701c00d208001810500003410075405d03600703421003007201c845040381c050040da0390038004000c0a040351424540a14250100c1c110240202c2d403042140e070142d4605043c103091408114902846511100c00ca6104110000058990a000e4070080c204410503d072181e0503e4009030030050902100d600c140c07401c102d042828002c15041d9181e182d0545800130742d60f5500400301c0e140c40200c003a01c1140719003019118101e840b00145051003648104402e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 86900504 1250 86899254 86899279
    0x40b040c1203080112110a0f0503211204030e04110703020c0405072f070b0a090f030201090611010b0405010810060e010503030307080403050f07150e0a0b0103140c0603090c 76
    0x810890085078004001440d080300400500484180c0d0440190098840c030b80130001d00700009603480070340d502180f86244001c0c010043c2d890140521090382c0e070003406186109034000c1d00342085116074030010710351400120203d000d051080c20784005040d0042c10800c0407412400450000c0e400c020821001480b40719410b0800381071a000700d40c001c0207947c84400305000c0c64182c0640d00910b06181120b520701028158159070404c2141400030a031440d0302603980c10910a004141c03030700305d030030a5007260414081000142d90248d103a0048407035038500b91004d04807103500b81d4090f169208080d54014145000452048004995645410300111381044015900c5420080090003440355580c140c1040c000a0300381809005540e900c21302c249000c518101c0c0c00f0b0801c01c000c0d02b01d01000ea90507060244201801040e80c45400400d104e074100508040240f40c0d14814000e0050200400707004440d1445410f10408020140c4400001007826880349012840140d0b030b2012910650b11500c2100c005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 86901754 1250 86900504 86900519
    0xc0601090b04020712030203130507120b0c1804050406090f110a090b0d060b030102042102132c031306030203040606050a030201051803070b0406020d080c0310120218040b040c 77
    0xc484410341e0040c48028060005d002c15802500000d140c105d034008000c1c02c000000320144498400b40c0010f60440318042e601d401c02d1141554000d004420040041110f419218145a2072100c001c43c112004941c03503071035141510140ca8540d0f0001c0c062407882d60468204400040c1c052803511040d01e00c0c402ea40c6c2d0b5210003005a82900301107540011085a8050124405c2d41094000f4000503001501d800c0c0e0750740020196444c2e00700345041103c8142d041208500c0c2c0400918a28038540ba801d0003010328001050318586008035403034448043c1b10591403491401071054a030640c8480403c070309000c0d95101e001e4045c1d03000305d034100c511a1401002242078030b8901103100a81c0d0301a03483c14240724007002d4008207151030b060f24030b501d88207410002580141000080020301290703405400041507005002d808640d000e0846171140780d00b03104020b10322015003003010440b1714041d0082c10042c202e00109402a11500c3c6c58400c1c140301c0d0007040284101c0c142e0250047d4400d4072011000e07960f5002c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 86903004 1250 86901754 86901757
    0x15020c06182e0c080421030f02160b030402011701120203070504020c030403021216120302011805250905040c030c0b0307080604050a02090d06150506030f0103060c140c0601090b0402 80
    0x18550150640d40d0b000d02451003240241803840c8a14070b01c0e4540781d192540501e00c107202d04c2901000e07900719841d1104255001c900d0307003000c0c001303400141902d071100043d24482074482d00411407141000310000e010340e881000c241c2c03d02008902c081096584640c03414401c5107451509a0181c850448005440d04061081b00c40d080c506102039820241154200240c105c00010b40b0469841608085d0700c204049000b4074004245002000800f100d1074500a402c1d40e142440e000040c00007600d41901242c0040385107180e5000401d603c0c20102c0c0f03000300c10280c9140d40d4100e00c0003540f40000f044100b00f41c3c02806400d580c0a270701c6031141241e5454070010b2501c012200000021610004524617007001d411041d0429400b500c05400c0103010400b056020001240507034000da02c94025650800c126800503000d44415664140780d0710f0308a100e00b5500c1c0041c0700040000e81c0ea007425103981d92090b1285050b001d000700007907580c3d10b407c031400341e6241c0703080c000c0946a610303080d80900310303180510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 86904254 1250 86903004 86903059
    0x406151d0105060304030207080709050411090f04020631051203031504020d0608012405060f07120c020603040f06110414040906060b040f0e090c030715020c0618 71
    0x50580541c1c0c20142440903d4002a00c200c1c1544504240400e0b40c500c280080070103081850800206407915003001026101414007850240102c9000c0c0007007800108107040d44250162021540d070a0101c0c040d0102c01001d03410b0542c040003006105e20100c140350070752411100100c0f12800030001d00d804090300d07480281d03422000d80c81e0030403c220860030940c0161442a588000010b0101d56903040c0d14291022408840a021a8100e9000420407001e104c04003030b203015640c0360b041c01640094440d9a00c10f94070050807448100300d08c040c006209920494071564050441c548174245890010a0b41404ae4411211181041d100001084900080d02e0440d00240b40c400c0f080c0c4a0304080c44014104401d00752520340c0c840c0008200c040001300107000804071491008103543ca0029150180c0601612500043d00301d04d04a91003594009036080680d1030600c1140078840c40524281d06d400ca00c0d280968008001103013258400c00f03401d101070301c6010151505c055446010500301e11040050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 86905504 1250 86904254 86904299
    0x3050403061a1c050307060204083a080c0415050c0c0306040206030a05090717070f080a03050403080a1b06020a020c090c041809050f03040305070f0302090f0402010314040615 77
    0x30b00443c0d41c1d0701000c801c0441014080c80a8a14082058482000f6a0301c80e40000000e039200801c1d0500e419560f8442d02081c0f1081024403a0b079900c844210540b45980000000c200300c41807001c5000f48145108640c014414518138410b149a0b02c00090000d4010500d407110300d010b03103402e18a05003008640248200d0b4000c03c1c5030320315a503003941900144006085107400c1d10030b00002080c20451138009842d959076140c010a187c80c5001052040c0c107801d03802c481403a41081c0704150020ba004020b41d400c5c1e0f68451081d81c0c0b58600c5100407a80c0034404506180c440806520400a01207141e00230b184903400f0b03900381c0d41c5618030f00e4140b2007521f17020b0351401d0504404000c00c000394804910045100200b142c0f01260040064807039070302c0e200049180140c180c0001504008010381004400001c20008038414516407030741d00040e8403c200103103102c183c11143c000013003c581c86a841a04840301403654440c1030308060070400014040748070300500c05540e8410216070340402440782d281c2d40414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 86906754 1250 86905504 86905519
    0x5040c0902040b040e2502030903011d0a02010f14030a14090105070c060f0608100c02070806090a0201050702061204060905010605030c0d022e0509030105060a031a040305130303050403061a 83
    0x9280d2a0302004400408031901d5066003401440306c1542c1d040c0318007581c1400c0d4000d40d00c034850401011308560282030f083d910284858107001c461140401c2d54042282c090800b1021000c48407816100c0c401421740d04c0118030f400008001001a240d031000b042441c56041491250792a4041c05d0300300c0300240c581030041490076171107000094050b0440020500c0504000c00c4282d92103000d645840c0d0864500a0440c1d29034960320f201b65070400c80c540003004110010525803d00340c01494a6071902c18020741000b07400034158040d13440320030407216000c4100940041d80c0c41c150908900900e010401251070b9420044000342e42d140028604091207401440507010714541d9003084024410305a1078401020003920146000710000d01070711402d96143c64061f036691802c42007508440c8000c002c20b00c511003a90050010130780500640421030005103c490f000d49907400c0c150390601070308801c03144101c0151004820164003030054030469105960601c11040191004082d16440941c5160020b42 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 86908004 1250 86906754 86906759
    0x6130f0b190c03020301030305220510110f07060512100f0902070501050a0204180906090206070b04030f090f0b0d060b1605070b0301030f1511030a05060f01020615010f140a0305040c0902040b04 85
    0x6500c000d20320b40381c0c10703510700c0d5405c660362f2001c100442a4154254049003003c00b50b450850310511018104000400c0609007142c149032011303042e402110204200c611500c4002407103200242e1882c4040d240705006040d0090b6125410000781d0300182d4205c44d25400d001c042101204903000307507400e84520703c00703288921102c60f00d80f20060880c0076041e03c1c0c00391121950005603d9241c02001d00d240903510140c018500307802c0c082c2c0400c40500340d010400c22840300c00c000b00a90031120400361041003a040307903202d00c0a60020080d0801e03420006003580000394201131500c000940c1814903114030b069031541c1d640c0e0220303020240000d1202402000a43c01000000f13803164841e0340c1658106c0f50001002c0c0d6500703840c1c0032160411940c100c60f440d03880040c84a14941000040e01b1030500b403008050318a000303a00c008840720043d030b295040c005104c0c1c0d280c61280c007400c15034201415050510382c442c401d031900140034000560f01a140c0680c11540440e545909000312030070354440140e420b15062 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 86909254 1250 86908004 86908027
    0x150e1c020115081b040b09070801030c0f1505071112010e10020c030a050705150903030403030b0301050603072108210717040201200105090601060807030e06130f0b190c03020301030305 81
    0x84c031108036503481a9903c0c03c000e110b6690070b040c640a081a039842003187d6040d4a01007615050542040042141d8040304120500c142c2c450411400e8982c46c2042c3c80315154600081c0755107a1107003040e4494074010004801c03c01c15442020126140400c41d5a01c01e110465101240b00b10020010340340c2041000f1000700780070320006c0c049284144202c3e11861410109400c0801084e50300c001319401c000140010302d58540034440e0744000c200c00812507403c11340000b95070741180b446400100741d0101c0450500034160034800c145550440c40817503031a212190000d004102c240b62480c11041d107031010440031071298004051000420100220945950300155625544030000d00f1402e4901d40a0340f00d0003000703004080c01410364a00406155051000150070010000c180380b040519020000130300c110700003100382e003101c202c9968003c600c129040403403105200001c0a006040c078181844001000750304004450a09070008101d001107084080b01030303100a110207000101c06008209010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 86910504 1250 86909254 86909293
    0x6020724060501140a0e09091c050a1d010306050312032409040308060604090f0207020103061a07080c0132060405281b051c09080403150e1c02011508 66
    0x20215410446e1113000b203030001607d40d01080f17914840582101802580300401c0200030b018944442c00e21f03504100703803070a004041b003041d5900c1c403072451004050894240d003e54071000142201400f5548a9900c41d6841013140d8015294440080c254800028050014441c52101200f0003084040300303499a890440c0e2080b40a07000e02d40c440b00402001a1052407841005980703541c0700d4000d600e4502074000902181c03080d038400d510034804a03030030032800300010f01240c41c81a80b1500c4552100c201802244c010012003004040c000390001000c10404102400039411001d5042c00400b255114030620042c0c4000340c2e040ea4400ea2000d40c0d40e0183c202e0b4544c2000030040020000410034090140c4030101484980004042070340019400003214190401c0e2860381070106050258810341c0d607940c0e10300d204a12000e003007036a004a02e841044d100ba0003100300c0b601400f084580c8e80b02c05148a101444040400e5409580703040d81e0340c0c51140050000c64121102c01c4c014100d01d407191141c8001c1d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 86911754 1250 86910504 86910517
    0x6040b07120e0d0c11090105010210091a0421020102090a0302101e030c0e15070602030c0f040f1502060402180702030706050c0703030c020a0803130f0602072406050114 74
    0x382a02c0d038050000100e020404800401141c1c1d45035803204003e401c19440d0000c0600829002e420254010b07c410b07600041d401710710203081100000c0c80c0d88207050403c500140c094000c01403610324403d00081c00403000c0d60400803140c00f408400c1203c1032400c160300b01d10460380c5140c0c000741e20a40401c007500d40070400100408040c14031040b000302c40000304200c0b06450000d900440e41d24008240b29960007070120b00b0f004000d903180002c00038510b815000a0140c24402442d290300000003400c1d01006100341c445140c516080180c490b0703165090000880e910f030243e069084002c8000c842d03590704c001800303801950040c01220301030342d4444501540ca01c1c007c0c002c4003544003c01a8900203000b41c42102d215003500b051041e01c40249140040a40f04e41d9a860821544041d0610001c1000d02c01182e8100104040b4031120000901c0c041c0081450f611000c0e18852001c80c1d000180025040f0000e000c1282181c032201c0c8032081c04003402141c003d4043e460000d401d01010000d2480c446004005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 86913004 1250 86911754 86911787
    0x10504030f171902060106020105060604080a080c01150315140f06010804031115040b0702070315020703020a1e02090a02040609090902240712030c080a0c180f1706040b07 75
    0x34003401c0700100c4400f02098110003006a104000402c140343d42072003001e4014100310b038070501e403910784500903507218440741e00a0007041d000a40251045025840880c1c00440c04044018003503880c144142002c011075208036941d0b040c00c2106415540328482e076845210f0500c903070740c055103072400111890b241c0104101c0500000413542c08040e4000c00c282c511481d11621140303030301d29240c030700644410b07005002d62081d0f5002840902c00108009400c07203c0c440c0310a0f0040c1c43d9261820224545401c01001034189800d07061440703881024903102c07143c418000e45111043e600c1e107079039000c101c7c03040344617210000701142418410307103000c2e0308146441400141520100f02842411200200c1c0e0f4802c076210312880021404108008044500d04200142c2002c000c510a030f070001034451100200504000c9640e0f4440b4450b2a0151100f001e040c0301d200c9a981440d0303102c90001034a10924005e0313000303482c1c4030b4410307407a031050019441e48166480014107500ba01c5204c0c0a465080c0984006503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 86914254 1250 86913004 86913007
    0x50703020301300215250201020a020114070213020d0c17060f0f0301020a0306060f03050f040b0a0e06010f060e09190e070b0c101b020a03052214030c010504030f17 72
    0x141c0d40d0005c1c07441c02d03050610042540d40611b84989030740c1c85510b0341400a00b040d0084040007603070300415410700454081c01d00c020b442500101100b0f56205820000398003825038040042080308940c0a000c9025010000b040a401c10040a444072000c0c4015003940134440400101075080c0b250803600c6500c00501540202c5180c0d10000c0e003aa00000c1c0c0c550700203a0360384410801c00e94011002c8031501c1c503904003007243d030400c002094648100100080d04510850f170100d00290140d0f4080c1d84000201c40540702c8550711090302d0050340d60b0390312800300024104280819145421001c80d0300400d88024075401180010b41d4001c09009607a1104100d40554040051031201c600024090344510801401e9030186403a401011201444c0380141c2c281010a00d80c0345c01c9400069000f00e181d00342c28115105d803020000c100d0b42c0d08009544030a421a407540028803001d82ca40c001140708821401d441c4000b421000440301801144000350022039040d04d03c01c0070960120528010803440e50700785 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 86915504 1250 86914254 86914349
    0x905090c0c07060e030f03040801240f150c050307050606090601090b030a05060402070c08011401090b090708040510090b0f0703020a14090a03060507180f05152505060703050703020301 81
    0x13811a000750b4081c049c2e03a5140c43e882030810184004c94100c0300008240161110704203e5030051940e107500458004070400341560024a024100701d00314654007200712580c0b05020320b0f0183c0c4540041e12200d000700002001b051096005640040a540260b80f40794190343d183d0303c540300608405070840350029030800146e004200d4200c02c000c0030f46136280c000704141d441060b840c54030410580c04850b0356440d1407403d8a690f52148440780d004625490114001e8031541007060038001e82110b02c4001ea03141c40b020004202c0440120b0f4424110400403444642d41d0031015020b901c540d41c00e038000510341c07016040401c13220384c1c00352040420180008914588a0352494222003041d5407110210300341c04200d0f40b801644102000240400d030482085080c0303010003149001449241d0384007000d1010031812980c2e002e03c0650460f91058400c041c0c02000c05040c95901c4000c182c401c4800a8245000140c64a000c1d00132079040b40c034a031510842081d54403441d0380d0041642e02441b02d11350039020a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 86916754 1250 86915504 86915533
    0x902180411040503120a110102180405041401061508090a0201090b0a030f020f1c090305030a1a0a06030506090702010c0e0d05031b0c030c09010b121012030905090c0c07060e03 77
    0x58000c1010104a000d03a504000700d805070800912002c00c82943e80100107001440424001c10709000404bc2d80106a40c4c480340b5188011503080110405158a004000180c0028074110b00c100281a5211444240c50303241c4a10340b54903080784068041a5a01c100300030390351001009000c21081031030001041d00c2074116120907a4070045900144150100380241d41400103581c3c0204081078040c02c1041034007135600030380b050100500892506681c0c02d00c5440505d4459048030781034400408900307802e51982d201400409003a901c17240508000740c00034140302d00500c00c0178406002d580fa0a040d08541e0000c002071507d461400303e503140400d200090b100b5160034880000e0324500c01c00746c01c100c0440020f01d4505450004845d10424101d401042004180c600325040041142510446591000704401d10b07401c19500a840c01c2010404d50024581d220102d0825200c0c00c80350b0601c640c03a5000707006401d00a414540f5007541128408000a9009801444a00703d02030240d88651501906 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 86918004 1250 86916754 86916763
    0xd0903090f09020a0f03020d09020301020c0d030605060406080a0b060c061603050915160201060503100b040b1e0f0a0506071a010509011a030408040b03090d0201060902180411040503 80
    0x11404180d03403410a0211080c2103046501900400301d0460518180e003a00411100704140303400141903000400e600d022080d030b00054140350b00a0300955a420343c0040b01c40d075420201801000007440e2035008503051400201300c0e070855009694007202500c030352100d100103115418001d5400601004204042c43c0d041c00181e201e00860000d06040d0412a04043c055400c018640182c3d50410058140701c02114a80d00b40c005003818980c014807440c984050340104510382201da4517120b42450b41ca41010280c001102220781030310300b0b129070003202c020b02115043c0c1440081d03440714065820b1348c0508100c1c40b01c20517800005c090b422029070750381c08940307141e2161078141c41e0890914544441d210044d00702d00c0c0182801c0d11031000e03940c50075010000000000c41d90444a56000010600f480841030075a40034190711491b1070741d41c0c03d028001c0c0327940300c50a04400000d942003200029000c0c41c580700780c0303002170150401d8800090511041000038100364a42c0f03400a0000c4c031010580e07407800c20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 86919254 1250 86918004 86918021
    0xa050f09090c030403021e0703080d020f04080a03021501140402030a0b0604090207060501051e0907050408100b1206042a08060a09050609070308040315020d090c0f050f030705090405030d 82
    0x100c44070765130300707140c1002828a0103151706c0d1522041101c01e0a00c504200060b40401c0f00c0c0c0210305107031203200c0f0307003010b101920900c0380380648642c01040200f04194003081541c00c481c802c2d001c49514241c906920350030017409100780c142c50300c2c001580a80b203091a400542e4499000040051219800301c0017418a42280d04250300d40b941c04181c1d4000c1222610406026140894444881b40c0340404030a01500f420b455241c080c1c2c56100c04280228001e0741540d01030007010050b117410060031424107009100a210701072244147e4480404c2081c40861514040c50f000700c1d1603444602c8c0e01404819655240a00c1c3c00c400e0014603001078583c0c2d09000f52802805c142d4004907035001380c0c1c00c050380342c00c7d00070301400c80c00d8020040070000124a5000c07981101c0d802841c0340d46030450b0b408031000900510710041c02080c18980c01c00d0800c603107140c81c60191804885040e404c16200c009001210b252502c20b5a01035000b880144114645824825480b038850002c0f20b140c14107032415482034540d0346 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 86920504 1250 86919254 86919271
    0x9020a03050c0418020306010501050a050408061e180c120309040501140a08150403081b13030c14010c0b06032107050d08040f0f0201110106030b0a110c030a050f0909 73
    0x41400d00c0502e06070040082200b14003131002c10340b1807160002500c843c418460b6074148200000c4016000d4050000d49008010900903500141307801c40321341851070b50301084803070014485170000d1882d000141e9611001e1030720348010700c0d60507454130500c1641da51b08042201d0510003400030039030fa03689078090350780030b0a9900180704001310200b043c048e45203c030385c01a06141d044445044003c0d80c00b46205c82e030043d0189400709568480800350002040c0c1e9a140005010000451b42e0b40821048a0501241d200d401c4020740302d0381d203480504000d481103941030300207050101c411003c03542e50750955800410040558402840c8540b070010050080d840100c40c07684c3c0410303070400303103d0107100c0c4030048034150908800d245001e5a4070b1400c03007042c0200a04c00b41c40f0005480c00c2da403265071504641c0410000030003120f901c84c140b03a48203210884076078507410b0801c0b990701d131203594000580b0f00400e0240300447c20440d02e0700c015986da4200c3d00248000d94401d01c02c00500e0344d6003803030460050b010ac = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 86921754 1250 86920504 86920513
    0x906093306130e10110403031704170c0c0a2907050102090a15030b01021f0e0a080d15140102061b0705010213230a05120f07080c09010e070f0302030a09020a0305 71
    0x180c078014040e01c000181c0440c021a003400100080f0fa042032711402c501d90b0080e00c038241c81d50381e4544000d442401030902002e002001c120703556444000200f030308409400300c9800144036039540c0120100d030200714006034480d81104d8000c82600011001e4030001d40701d80d00150900410f04003042031340810340c1c850b40d000780e8100349801040d03030144142d8182c000700f072018002c15040409006207108020150030941136680380105641c410501240400d1588100e02c65a2440e507a105100a8001000da69a642404c010300180c9070719100c5152211078410f80103401c0c181c0d40c2c0e060082c33000b0211215681102c02c100880c0c80050420300c0281904600a003010741802d040405031001140c40d840a013000c0a5000070b0b0840d030782d48a41190080360001c94401d43c000305070084d005c3c01c01c3c40d10000350505100b07409000c6014035000c21a20f050306025100d10b03009030703038902850412081c29500800420480041c818555110b600150341c013a41510011440854a03070108001d13140503402550250803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 86923004 1250 86921754 86921773
    0xd0507091707080622021302180a14012003030103030315050102010b030a11010302040306020d051501260403170403030c0807050a0504051c0b0906093306130e 70
    0x141c08030280a0110001c044160a000c081641c40901422201e0041c1d8000c1c0c454041c244d00102030100558050300f417003c80039907121101e01070740020080d001036460403102030610341441c10032031003100e0102c041d15160624060041d65180c03400009007a403022650031001454008100543c000d40c42542d001422001c0d103605800c0c4080150002811641020300016543d80c0005885c1136039500490818440c20b00400143d0091003070340d01c001c01840c00450302d400a5503169106038420890701e0317940c0c40c20303081c1c0900450b9264110201480405106440101015007021025502c00d01c682441600142101c0c484c982a5804440c1200001d4860300d00494090b48042050707004121030401d41e080c5581071402600b14001c500480740140155101e80c10702d240800b010b62503140d0070200203aa5401e010740b506071261030480d0011b100c1d104250754202150841e820a0389040d80401c031225030700b6556681628a01c00181c6215030041d6032072010651080d462144240740e0031880010b101c00903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 86924254 1250 86923004 86923019
    0x905011514030601090605031c0e0a1d0a0902010503040602070206070b040b06030c060406051806040902190323060909100e070609090203010303050a0c0302070305030a0e12061b0a050d050709 84
    0x43c160800c0110038105401003010340c80001b140200c0301d0351703405c00c0c072a419078116080f61fa03030200707000c20b540c800c01c40c243c00030701036820409441164950301002d1a144e034a22190f081502d100d040028006542080000c02062072b660203010360700e2008000d00d207401c280c0d1325030622074141960b066801d0078901050103694a0204800b804103482a50528141850001d021700f1501405007202400204202e40354401c0d5a4481290040c1000749401c54a840324a003040380c0d02403a01081c000407070300c2c000902154040d040c480382d00c42040c00700382c8012030344e55009008070840060480701325442001034940c0d440c11980141c0d03410300c856900a01a41c1d180000c002c2450816174000311005104000510200344c0c1b0a003103404c003e005051a408802d01458220316094640e80060864080840d0710841039a11003400440700a040b04c0503d0003220021103540c5840c030a50768a1070b14840704040f43e5540c403124014002001c00390030901d003050702c40101c00007510743c116407581c00074403049014130110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 86925504 1250 86924254 86924263
    0x111030103140d03050441010e070801060315020f0d060e060a050609090a0b0d0807050102040e1f03020f040e030d09061b2106270e12030a090501151403 67
    0x10091490140220b08007034640007440d0083c043c3c82c2c140002c4d40d103e03101c6043d4114420003044418100540040d60421f80d4071740c002c0a001a00540c44c3c010310b900003580d00c10502070441640e401c60950410b10951000d0030000354041c0f240ca1080100602c51803903250554411903009018595070011789103009070400c50020b140da0006445900107206280454840580c559840140490005030110b04000000e81c100c0500f407000f8140c0c03e0010f103000c108081900903100710794445800c010540c440502801d04401001c1d02c5910000025800f003000d8541030801b0803400201400004a1180380c600f481e04551101c0000c1c11180c0e241d01e403200c20440300c0c2c880c90a2444101013010064414598018070102c01500d0103941031310211080300004241d40d000d00300501c4038450788840d8280c1080c00780b420884460070342c00b8251074004900c042e10004100010300c2c2c4d000c42c92441c030b50303550107408a004084042007515603660360220702c200048200300340b40181419000d80c25070308548200300341c0760 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 86926754 1250 86925504 86925523
    0x6030302060a06030b0f0c070f08040e060d050d08060a0906060207030b130206040603200403030f1707053f011802040f0510230423060912011103010314 67
    0x2e003071400100304086181040006c0d048440320600b2807060b180c5014a0406010300300e030281011803411400340400008100130001c80ea2202800041a6907500410481d04a00c0001030041c0c0c10400f004004a4403c00685074040e000810309002e56444400400131a21541c00c1400941d00884080c414401c00c0c02c00b00b0362002600c04012845c05c0c050303001c192203010341d111350302c103254441483c0300202c03407000741c034100c5095212020b50b02c580d560304000b40301d8251214940085001070900d022a400340082c00d0b40305e00101e48405103040e10354500442d00942603848a80c01ca003c0c0341076040031400c03030b50741d03001c5e2002100c05200065040c00c508031580c1c0d1140f883c41240c41e104102c104150720301410b085048035012641603e51245201c0241c4000480301d4400e400a941200414803d4800802610540e0f19a001c0c035145e480014606101080c00c00152540c842c03818410101c491070441781801e02c401c8614008240c40c05c0d489104030072138000703070002c41e501c03400d27145600c01107581007011144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 86928004 1250 86926754 86926771
    0x30703020114100b0c0a06050a0902090714160c030b0702012715050402010516030503011508090a0212150109050a0c0503061e0303070203060a09020f1005030a020a030612060603030206 81
    0x4280c1404850f00f60921000d119204405402203049042c0d071206100d607013031058104100780400c2c54804a10030051044d000220b20801f95640440d16003442101c4528a1a1001501614215082c0c1c82c0124181c0c1e0035a00b22110080301d000840050700c0c0711815406062150000714105e0381c4131041003414200b031422080302c41c0a8503001000b04041c2d900d4407488095403100041d46407101c0c00101c030a4402c1035081c41c1a0840404400b00f05a80040150704850705030f00d095401d0b540d00c01c8100c43c49501966030803010b5000481082c00b6141034004000d903600001c08070758040070030902c0290510360036481064640e6a0314104050500300780284480110986455403840c903280b800607100b07a01c0001010b9000103280c000115a0701d0401c01c1300d00c80c5800400702c507510310300b1035002e070040e080c007020880c011070019800180909003c004078035503803451303158141507554100c0007070001c2d080b05160b40101174032040c0c006100240041c81c605124005d000101d4400d0850401030b241010140040a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 86929254 1250 86928004 86928041
    0x100b1210060c030801030803060d0206190306120503040b0a0c0b040506010303140c190302010b04020f070c08010c020a0f0c0e160306060905030a08090f031e010b0103020f0d0c030e0f0307030201 85
    0xa00282d408040135064075442071503151280c0320b01000c6503502d43c12840083d0411000a8034822024208080d440c0084650b5403d01c0065101c0000800494201c07800404540c8148002d00104810b070005d03002420003490f040301d1030202e9485502072003030103540c151402d400100040c020700d58011600103404040d01022403034501d40812182c0d850b0f08000300d10182c180e41c882228100744c400e402110300040014400d64540d012081c11707489a51150904070341c040c10381e01c4001034080041c00790002d038803815000342121102c0d40d2510f00c102801c00344101d40b403650100010803c1c6040c041c18070f01549810305000d07000c40503040f0190890341950440c1d004c0c00022181000700380d500040d0940e85941c0450020740741c901e1003000c24290840507006603810b014618008000213500314401a140341d8a40c024020284d036800150124803805443c2442000f0030020300451030b40d00c1e000b805400145141c00150f042c001600c031070415044508030a1103810010740c2406041d824007038001790500000303601 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 86930504 1250 86929254 86929277
    0xb0f0d02040f14040b0a150e060c0106090e01090305030601210f020a031a09060d020a09060b1c060e07082d09100b1807020f0303070e0a090b0d020405100b121006 71
    0x35074100d0140308590fa54024840000241c0e407080e80e1030610303100060500758482c2c1c40c001618bc042d201d5401910840c0b03141010004480005004900b6210340540310b880c50742d2605070044074046904021166041c80c05640c032000c0003007034840c500c0180350b5168016241c482d60315000301520700d00798030010420008a5140159991036500942000d4100c84101040810f8404103a100f821340c0d0280e8111440c16900040c5002c0040c02014170300110f141025144040590100c1103d0082c011098031003c4d800001c1d0086015403109a04541c11192130582030041c60310890b00a10814003808042e107009e8148520702a007001856104000e81000f0300814441e500480d05500e80d0000ca0050b15807108080340b04903000707000082c0d8003034a810a69960b40f800710406444c0680900c1501d0140ca541000020100390600c03030007140c03c40040c11200c01d48076035003c000c0900f00291850070f110700582000268458124020010300300d482222071aa13144c001804580f42045034440701c2800860190b6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 86931754 1250 86930504 86930509
    0xa09060507020f130e060a0c0207120519021c0302011418060a05070309021801030c0e060303030403120e1501050a0602060105010c030507051608060a1508070b0f0d02040f14040b 78
    0x382848500948220100d413600d40d81e04000342500f183c413032809004113004d000e4030071129040f1941e108059021581c0c015034070036400c0e656118440000e031550b01306131120b032081c04109020200b801e00042c50300c10030140000e00c3d60700c0300440090403805031703660b400940d40c40743c4600f40c0580e015418101c14540044030b615941d480d4900140891030fa15641c2c00000d8100c1d019a111400540e0042d142c20700307407001e40384c2903406000207000c1610140e21000380012400c654201140c803985000c0c02650664440355015a01f440702640c2c0800280e40f9002c0e04035482c407003048a00e071002c040383d05902d1254540740500c91250400c0d08080119084030700140a141d8201740c3e202441907162920595505080c2496810700c00d09440c0c00b190401c0009000410002c0066428001c00340e0700820880c1200e80300000c00441c0c0039104941d8290041c05080003d16808000340c6408200020400c0ca00b00d42c0040c818201d074030a0b0404402e800b0034000911206c00145020094203405550402099520600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 86933004 1250 86931754 86931769
    0x20904050a151e090501030302060a1103010302010c030c0507080d020318041103011e050303030c0c010c0306060915031104240203040e06090a0b0915010e0108060904060b03070b0a050a0906050702 86
    0x401020b00c4541450622030054622640000c00d014a005c100650b103a1070000d4441000343c030580300182c00e00e0181d6000500b50021681207035816155040d030682c1c160390984102044010035035483c0288040040c0b5084240300d40190200c059000d1070ba659900e800e80c0c161b4007150601240160314054250014504001c1102d040d120b410a59060903801007410180041950b0003541d0980804414000c010f181c1c0d80c040d001d4440c1c25002440b203d00f40b66001c40c1264924402d000000e260b5a20422000300800c00b82994100985408a1744080c0101d220034ac7e03610a40c80004c8503551801c0488040038204c0c00340c1036840c020701c003441ca0320307140c145000c20213030016149a00c03c850007800b144c03010360f407035001c0110014003401512030b503d0868413140c6004c044105090121700000c244071160741c4100c2895100713081c001c003a41201d480d6919004010088890f0454240c4140180803403c0360f100c1000c1c0c00c0212325641c40b25550040d01c0c400a10640aaa018000f84001840320f40010382d00c0e030b41d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 86934254 1250 86933004 86933009
    0xc0323040b0a09020d05030f07060e060601080705030a021b0c011403090705010e010905040911130c0507141504050604170a020c040b03010f0207080301050306091f0c09090c03020904050a15 83
    0x2001181140190000680d60030040000401c2c520000401034042400f2350301812085008400401458001a2000c1d484183c111040ca00086842c000030321500e0041015542250802070700604050046c800c0707507a0403442d00070303030b04c07080d4000303d54501d0641c3d020171800d100c1c0b22104201821401d040c200d9580d1100b80b401414184004620b040b10f899120b03001040003040000c20a00200d5102d042580000103415141c034001e0060504d00ce884a4890040700a4095540c0da06450090551108551a080b01d0700842d8a8040c0d0355071040300482501d00340740581c0c0104e0242505081a02d800b43c49000014014070620000f800801c2c025500821603400400f0300391004138003406048002401800e4035940040d105101040903800e01075044040c50690340203800702c03502030b1280c1003074503a9410100f00001c1e43c40f60103030959505100c1600501002445800c10010958503114550305954070340c40c0c4800040ea000c182d40312545018011341c0e410040000c0c0810207070301c00c0000c41c0c00052550 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 86935504 1250 86934254 86934271
    0x307062909070c030c12080711010606021504050309090403021005091209010c050106081903020105011d0c0d0209130b040b0d080a1b0804120b0a0b030706030b130c0323040b 76
    0x450404113040c0150010880d860f0b1203034a00390414200301001e41011001e03502d44001402d10003000031201d00c14810802620000e4008210860720340a80c44910b080c0188110341754041400f00207000c0c3c640d9240103008504c82c2d00907144e0f01c1040e401e40030803200300405581c03196001c000350010041000b8212490711500f840d201300d100b80c950400030f0250090b036100c02c14500c140c0c4840c0500d414454154038075a4400da0080c000340e40d90741d003000045050041e5420503100403802080803803000b14001c10045034141c0025003000b10880008007491082000c041045440f0300d09080507242900c24480d03244d10890b02d5841000194030380040e680603500f40701c014450360a902017400c212520144c4030182d072020b860344da515128210861032108103071023181c24200440108405072594022908001c0000d002000e1903071030280c045011308102005a9000b405800d6180d2100c102c90103100980646c584002c101d4079a100d002d1948200011aaa00c0d520511024000000e044c030070b00d40d8000e101c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 86936754 1250 86935504 86935517
    0x1050c090d03050912061006030b03100216150204170a05060415060305060c070b07020304060e0d0201050403021c0201020f0109031205041b080d0806150904051503030706290907 78
    0xa160503941c071301c00c61100643c0b00303169480001aa14001130100e20450003950040e4005944a01c154282c1c0d81d0a0400d9603d90492600c00c441c40d00c00398003501c501051158a074451140503103a100490341000c81200c80542c001406000944a11600b4590000001c00418086049072070303035900c500d00a0001052140810040c1000103401d40242c4080d5400105440340b6040183c001010360340240c0b0115946009200010701d168004002e5030708a0b1141d40341da03c100803129040000c00a034043c012414080d00380301c0840503890f5020300c0340746102040704441840180e4000649822038001f46e01901381e04000303807040001d07805000126100000d10010a003a00c4910701080d080c20680c00041c80160075030380001c2c00d00340004000501145945402074581c4416041c13000c0580040c80d12249203c04010402c1d480c107180c0d012950001800c2401180b00821600090840d80043c2c0143d910740d8490160302a820b449150141c0e44000d0100041c20070015400807803904100101503000340f020303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 86938004 1250 86936754 86936779
    0x3030f050a0e040f0605040c021b0a050d150f050406140c0a0c060906020d090302102007080c0723030c090105030d1b080a0801030b100b030c09011403040c051201050c09 74
    0x2076582105c006410014028880200c150700005e41ea4049a100700c050441c0e03140c40d1000c40e0a006050382e060311005441402042c20540b8bc5902c80da86158807030350807954a501800215202d03100785401184541c90109504100001400e01c13004060000a003c0508112840102d42c1200461800562103d00481da1186a0400d81c0081c000d4990401100b400c0c101d614040640c04240704003d88001c680401110a232114040c0082c10b1841c0200c034500b0041215a011560800242c010a8144401c6814550720756000d0038001c5184484100d0700c000000e804004c6140510211010311011b80b507081c4298036101c00696103027004041d030024000c0e110500b99100000c03245400b682d90300302011700d60310054075400410183c0248401d03245084140081180c05000b01d961030100c03007940750341b14207580303940210410b03a5100e80e150383d0502c0360b44800d01210750603c002640c42140100e03400d1240c81c0c5081d0a110040820081d00001c0b6403410b4100b100701c1c80e07507006440001ca02500da4841410703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 86939254 1250 86938004 86938031
    0xa05070509130908040b120a09020f040e0a1a10080a02100c150e060105090c03240105090a030615050303040609090b010c02030604060501050102100c020a1106041a030103030f050a0e04 81
    0xc91504050044e040009000c6500090540280030408005409501d42e0b40c4640e8a0302c00c45500307010007580110300070802c1c5031170311300b0383c001043e54100c50059a40c25805a56440d20754444100345c40d0800140d40200b0880c10166170940cac004100d48d10160442400300c0d400518408103110000088c003061000810a005202c8509480070404000801c607094806c1c4171240d46071400d10800d4412400d420001c1c03520840c03c81500d00811800010b407141207e140407842c1d852401201c1181088024062058141d55044000000b10b0003110b00041003800c5012031040460a500074500941c0304100400c0f03030640c0810301a04442c401780d80002c0001040e0f0040300c0d04401d2413400381d4144501d105100902403107500090490f2070980844124149441030f40d4190780036541e903840540c11041c0307a5400300d050314a0105001c58000c1000d0301d09600d400c0b046c1d52803030401110b103814480100040c8101504030030032445840c01801c0c16410049040c0c8000d10502c04018103d001d95140d20450181e207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 86940504 1250 86939254 86939261
    0x2030d021b0303070903020a091802092a070c06050405013e0102030603060708011220060a1e1d040906202104031713050607090e0a0507050913 63
    0x8640002a03d5480c2000403004200000b40e0006a20450036404d00084240551040040c101c0f40b40c81c25a085840c0368080000c101b0000b04440040000388100484442c0d96007601300042006180981d100d20f030508091134240c0c1e0503003041c0c05000e8100300a0000d81c2c0c1202003d0b82031004e0503107070302420381003a280305195442e540c00e0f200c60111003101804289419006544101c5091301142c4031aa99004120303007885d0207114451800e210f1541c40d00100300c2c88018907450a4200005580d41e80c01c0310701107031041d48500c41d00c4000a081c41c00c8100c14a2074260611a2000c152404004440301d03a0560300703a20040342082d921556a5058030030400a0703d8001c80000c070b40881552061054901d049040c640c00540c9000e401203801040c90325070964000c07801c0c055034040d42c490050900b9140d2407a0700440281414050302d00060780c2d200000c0041101c1441840385544d100784487c91f040b007041010b40081c20400100c1d041404104055a12074103560369800c089482161030039a842c08107008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 86941754 1250 86940504 86940547
    0x21010f1406062118010c03050411151314010206010b0a022a040c05030a06050409110405180106090c030c050703140a050c07093206010c021c06050402030c0d0302030d02 74
    0x100705030541040348018041000e805150794440c020302186c46020000c908070344040b40c0c01403d103c014100081c0900300300b069106113426500c8070300d15020028000203000c510319031100400a2840d840f220007940c1c148005801400d4405001d800c0c80700101c0c02a49070107680c0c030491002c4501801d000c10448198a4a40c807a05001c0c00412226804000080c0315610464490304103905282000416080c0351143c042c216401014070401e020032041044044d15010303145000e44400b8590780004110f082c0701d880010b013400400003072a2400f240300502a80c00603510b103002c1c0300301401044042900402c480c01c008000358141c0703a03a039095030380650ba207000d01071440d0b406100c0d403000444e03800500d921000d00a1103103042c941e02c10350030039804580e10030880c0e042d08964544002258840d4040c1142c102c200b80300800741e03220310982c1002c2002c10f2101400070340340720781c9400a001c00d41c201409060614482600c03012a096031545003c0d65034420091003c1c6190341c00260b26001c0351403484020b41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 86943004 1250 86941754 86941807
    0x603060c020a0501060f1a0d110408010204060306061403042a090e060a0c0525020d050120030c0405010c0204060509040302070303140301050a06030e0c21010f140606 73
    0x609150030300003580e9002e5000110740942c41c1c22400306009480e1600441110001c0740c0d884c3c002c5031400c2c1d40181a401c80d180d0610303444c0c1c540c1b41c42d18580d00e138040680701030b2460b81300041e01c45141004c000c2c1901c2242c0d00410230f000c004101010711440d80011641d005401c45041c003004807032101c001c0c009004c00e0101c1c6114561035000071a2024451704909240031022017101d00303a48601c0003100c110740c1d03000508004a4030800144841c5014a01e101d40e1000d40395460380c2402120740c01080c00003501030b0048540380d660381c00340408801c2108090000c55001e00220341149010001c1143c54801e80c040c0e40e051001c508400421540d403600700001420b0090b00f0251181840c0c07030040d54905882c0012030105101c20b000686080300f80b010350381210001480b8035a030300d15104041d401884542241d1006000d900d035441095191340d042c0c181042140d0200020b0030001c1e400c0103084480c20945031000c0d03404c10481403103449002c0c0c2400c0d00981c0884070b0304e03a00c0f07421030a284e8032510011213916 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 86944254 1250 86943004 86943011
    0xb060a030b0117011a0102030910050c0106150f0c030e011b021816110c0f04020c0f0c01030c02010908070b06131a0a0501030902090a0507110a05010603140a080418060306 75
    0x542410388900b220204000400900c260f01440c0c02c01c0722030b000f0012417140140d1041c048003060786001c1e00b1204000c0d40c039045c501c0c0303891242c48003c0c2c252041500300c180b0541052001004460b4440c0d80d019194207145440e0b00703803400f030741c3d8010304200d1007001040c1001510450038010b01c1e180e4480c13138580c0d5401000110901d400c41c0c40340940e42c0080700c81c601d8104001c0d0b5050540c60160a040ba24071031000046c011905400b410810b001025405207a0090750a108962200a04100804810650344000d200c038031144800102a2554040c0d55001c69040110450000c0e0b20001581c0c103580d48001070b074400e9610000424103080e03800d24440c40b10341c140605401d418501c241e12014445081e104c100401d80c071200150151124a03c0080d0003614480006050300150b6100c9034220070f451801d02c05491511401629166078128281c44c2650744840800800c031b050a100d4031a550118080c0c012261b40c0d4459407003d020b03a100360b00424100c03600701a902c544960000c4003540d4402402c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 86945504 1250 86944254 86944259
    0x3070f03051612080313031202130f080d0207090c05090604060f1e020604060902030c181014010801060e0f0607080c010501050102011118180115020105070306050d0b060a030b01 78
    0xd075500502901d08400500070302c80400c52041c0030b44000c00c1e607508206200c0c99601d4400c0c04810884c100e940c2503081103031804004203c10074500003000042c0740750144140460a01158910000c0c0b00c1e03109448aa200000000c2c90350740220700d5400721034481d01d000410440712501581e013442110412603105400140c0401e9107608156440e00764001541d17841034a0003c0c0001d042244003201040c009030740000000350006025400c643c490714805001d45101d4508030b40818000340700321512982c203508410800010040c3e05814100070701090540803074400314600003801843c0180510403c008804043c48185d4980303400d9809580b802810a5075506064105002c442d0803c0f141d88000c0d500340000022990320501441c0001525030302c09a10b440c0c090303000700b160341082042880e004200d0071880c0c001000f001e440726000b42888000340d101a00d24031002403c5440c0245100700389850080d0a202ca070300e90901451449a005441c0c10043d2112800602501c0303142e40300a02102e08400003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 86946754 1250 86945504 86945513
    0x20406020d110102070305090904030c0b1e0903030105010e0907091e030620040506070c03020603130318031208070512040c06030c020c0d0f0c15020c1f02071403070f03 74
    0x315884030307069480368803502d49903010909074480c0f640060005130041c00040b4051401203400ca40184c0300307080034401d03040596141c1a4450080702c1031744032030080301103a0b91000d0b62001007507480003c070000382d45103604103030000e4030000c52002818080d5200b6400541c1840c0980e203c40e010f0188014540e1052a00d2990b0071130302803445c0030440d5050704000040031100390201120801d000300e0090b40d4181401d110911105420660050702e81210326040040035031501c00c000c40c06010f8525540c8030486181c00c1c0600351012107040c400d00048214010408103404030150982c0d070589241c1a0401d44074040c0846141c029a070450480c000d01e03105200030070501210440440310380d40c0701880041700c8007070180d84803046080e85540100c40d4500132400640c2c0003c00f070f92801e22441e140310030540c98191051000d02104071400c0541d21000392200a0b14000100018440880440e003401416903480251504028421064040c280a045001941d010300c007040c00380a4243c252010182c1e00e050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 86948004 1250 86946754 86946763
    0x51c0b2d0f15010c0c051201060e2a160803100305061005010807020d08060d0f0c09060905010b040302030d2003070b01150503132004020313210215150402040602 71
    0x520101078480d000d965803980d40030700220501c3c83d40000542540d181b50406000782d43c811303003001000c29580d41d44081080c00c002404036002e440a80242e03030020300b03041c1e040d403541070007110f101903460010b2000038941f400f0500740e40302050f40250555142d8440b41c4107d43d40e0b0000b900000d1290042d0303002c100344140700190b002d080b214241c1c0d96864503200c01c1e00913a150030801451304009180c11000500c2d50a0810440d0400d62080413120b4450095032980d40390405503421400400e07440d400b0070064440030b801064094020700403200e00d040c1c91540000e6031260007106081c01d002c2c0480c001c0d000302810803400b008000d040030070340380d881e400c5280c500b041003001d000f800c3e02c00d00503040710121107100f00241ca00c9000205000c0e0a10b00c8240c8070810340d240700388082c001c03141701070385d01800350303185c41c0040c5014142e8187c0525060703040c0c0c1740c4000e2110481c1108844c0d1815080820440f6a0010ba60604641c2d0b1030b50744003d07030300c400740c60541442d02045e69a41140c00060b0000d03049a0016 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 86949254 1250 86948004 86948011
    0xb040f1707030e01080f06010f1b05070e0a060b0f04030605040203160b0a0206090609070303120b0301020712110633040e0303040201170c040b030703021c06051c0b2d0f 74
    0xe0301c0400c3c90361900d1b400c400707000040c2c40450024022424810b0018028040500341c10466103495611018503074a040c60320081e42c0082c40b481071004144051141c1d1802000042c003030010072981044001094442240690f1002914864480d404241075460078440e580000c0748003901c142c0c0c00c603101c0d20040b401d03600080c1c107000144240d00002c0c2d01402c3c04110b1754019446000134040c21460758408071004040d0f0300090740300c19035800b103d144030b603000d01c010070b900e500c240182d18010004000280c01001104144080703a00001d0401c826980d148542d840c00310310400700e20320301450fa280a444141e00c1410140d41080c5050f00c8101d41c800000003451046100b40d9a40d020300c02c1d0400b038011802d800ba240b0305810312050000740704040303034203018580c0103443d443e0060600741b140f1400e08d4034890080d50851001e1b5100000d120070700302a000a0b0f01c0200e030380190462507410356511042944010641c00040304001954028000359a031201500d401c00b04c14000c0c54241071414520701801034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 86950504 1250 86949254 86949257
    0xd060c03230105030a060203060112140a0c02010b031c0201020708040b0403050d0504030803131a1009060b0f07060c021e0106080705090601080609090f0f03030907080a0b040f1707030e01 82
    0x1c8041d0001e07041400c0854140d0348082c015044c10340e03259490001075000036105c3c9060040030702c0a0001104944038145044080a1101c81d250401c900d034481120100031350f1504590422030f200c1219100050708040040c1d101200c400350f00d0180380d04900901404800421041002800080c0744039894003170001d9070b00410941d910003800320000e0f5941e00c12440020000d40c82400010b207580c900700e5252820b00d00502c0243d00305200e0403080828500c0485e1141d07042d82c0d00007003d00c0100b2140c07050001507c8006c0c01d0528010750010700d15000e005100004000e1070301d91001d9a4142d109124841700200c81c00e403104c41c5841041402c2d4068601c501a07044507100d1007c0004681c64440d0090b8000e080686400d0070079120340c024880b40200080142299200d00c8418144000c42004181d0001d4000c41c091900c0c0d04040510310b05201169100b00c40a80c4103c240c0400b06489150302500a80c0c02200140b02c0074640ca07100e403100041c0703214a004480d003c0b49110074036400c070038240b00c988400d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 86951754 1250 86950504 86950541
    0x40801060f050414011703090d050f0c010905010909090602090402030103150b0411040b0a2102040f0e04050d08070309050706110c0901180b0102030d0c030606020d09150e0d060c03 79
    0x5510030720013103910705100b040301d60341c0303840c01044001d8008508803015400b80090300e24000700031000c40c401070807000003118158820440440c40240a00003007003901403d2070700d5040140350500081000c1c1d4203024100145503651005000c00c001541100e0002c00c02030002d64036581d503800c010081c06080080324031914103008110840780741034800c22190034002040141081d081140100803a04814000c0301440711040059028003080082480c802c0c061690142c0c1e180c0c100300d08002c02e0070260348441c510a141c04244000034802164460140c4090702d41903d060303a5882045005e00000400500a40292a0b0200c0e0060340b25044030f0300401884126450480d02c1030601500440034490780c06100312800c00c1030503034410345e040010050014070441e4104103124030340e03030110703070400d03440c000441d549039010001d00742c06005840300b40721242408045549441401c006000a07410300404000c0e0244c0710b9041d0782d0340c101000c3c0d00395400602c10403100c0001207000e0003d06103c4149820040c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 86953004 1250 86951754 86951759
    0xc0503040212070b0406050a0507050a080c010609060b220e0f040b061009090b0607081c140907030201030c09091b08092e0914030306040f05040210080417040801060f 73
    0x20f0020441d04100300303592602e45418021142a009503254070100542040580f01144042015100c074030f00401072581d0300c610365041c1c81c0c2111a9903001e00f44050410b031040050f1b6251109994140d082417074445a1000307480088032440103150003100a81e950281800b00400200165030301c1940305103603001e42c0c0d40740c5030208107454034805814000600091010f0288003c1508200c0180b400908401e00b4072445585000441d0000c600300340b11044880002c4200200301c0c01001c804c09038a500d0804141804003407151074452a020180c1410386a810682000744154840381c01445440d40420890b210b15040b0310a4440b0f13001e004000601e441c01003284030001180c0c0d9104205207280248132348a11080b001d40c84441c030010b10307100907078841c02c07100030600e020040401038015001640d0ba9240c6441044210384040358403000d090300d04020000180c40b940c050752900840350070410510354a6144c00f072044415007045640000012078001000750054002d0400d58041d01d100040464 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 86954254 1250 86953004 86953039
    0x7050123010509070f0306050a03031806140421061103040c0806190e0f03210a050c070305030a11040f050f04050f130804050301020a2006060f01030b0111010c05030402 74
    0x903028040c5a500c2a40000481d1442c0d002e42c1c60004111641d0902041140c0c1da8000240d210340b1940c02035021440b21001d0755002c181e00910315010740070f2400c00700402c0c4845c0d030404040e40694001d03218500e00710003851745000451004000541c2c1d20240901c02c3c02c120001d548225042941d04a48080442401050450021820364407c042c10b07071300c40491003082003141c405828070002030b45143c0200399003083c01403030030320041514418550805644082251920301880801800e190b030305458002441150f00000040328032164051030f045403681c0f81c0300390340c0d4020208001540784900c400100002c0f26409140d010f41110310860303018000030402d03001e00040d40c070105c61070307144102d000300007558802080d05410742e2280104c000f5030905403a040880d08a92101e041034020500034046010142082046000c034115944054042d50038010042003020121640c101e051607210310f46007040b80d2041004030b00b43d0f44054001c1c000900d2429016100d980b0603681070303010300d0451440c541800c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 86955504 1250 86954254 86954321
    0x301110a030f15062d0207050103020a170f1503010908031b07060e0c0901121203020d0213120201020c100c02060d0f0e06060f0f01090509150303070501 67
    0x10411604a5240410404049009115682c1c8007a00b040c2d4800c401042c503a210314441c4054030594440302d59400101000300d5071040c1301240c84001c0c60403000b000e04000e90204882040b03400a08004d80c40b1b445150060720300c40044160742c090f2072034410800c90a03982913141c03a40203a0041c0c1f81000032131401410306080e15132a000c0501494801c0020813031705d0900c40c422100d90541e000c06541440c81550b41c8000740c40408002c403801e1740c0044681425440e103d10242c6c01005803500c0746d040d0312103d9842c03c084062440b0301c2414141c0c089015041016660112041060105104600c154a648141e01d06031085d290036401445411001819070415421281740442107890b4881155600c0e420000d455010b091185141500c0f072840d0781c07241d04a4000c04040341e500901800c0741d03142008c1880000c03941e13601c070140303e01805046801603981040703c6200f40d03141581d00f00c0280d500d07000f0313110050382d03030140454251000043c60000d0140640c4081e5044140301d400b010404144c43c4800f180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 86956754 1250 86955504 86955521
    0xc0e030a02012c1002012c1b01030b040c020a051501120609020f210c10120504020402160b0406060f030210080601030b0301050c0a02060903040602060105010c05010b0301021305040b0301 82
    0x450108295000f0307600c25001920304032041c20450750030701820030300441c0641505014400150b9102c88080d007100000380c00348264001c150340e20030100d116054450755290b191080e4002d515540300410b44c41079100c1c1d00401c0000b90054824400106890402940c5540c000016500d60252a007480303010006072031685c0c100c0e440c1480e042030704455500c031440103240895040340e00c4003c003903010a40e9180ea10400b650b0f20a2040c10f640c1241e242c0c0c01450034808a004c0b090f21aa2006203407105603500507820681c81c040824001640e50788034030210f03001b4491103120520502d59a00084101b00c203109019200c3c51050703038140102540ea4800e15074889107400000c0d4086158a4440e400521030701916500c1601417501240600c0714202080c04c440c001d54001c1e042290015207030903026010401c980d0000069001140307070600e0624000e480c1c1d0018081c1c541088200e64400d070501809410000c035030f00c8000e00841d61507401c06020030f90702c100c601c900c40c0118146070040b0034034a010b2080d03490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 86958004 1250 86956754 86956757
    0x803010b1812120a030207020d120f02010e0316050c0402030c0310090603080301050603041b060801170a0506010512030706060f170d02061801021201030b0a050f090726100c0e030a0201 81
    0x5800112440101d154104c1d540550802d40d0a0120401681d80d000b0780c984001d014000c03080149603501402000c060f2070a003007805680c180900c9010611000007120510061241030006101c1146085400c140580d821582d20a0020003071051501c146801140140401d03c22501c041c4c3c2c4d62907e402c299491844041d00b1007405200400950800d00003c44e8000c0c464400001a0310383c01d40f104200049030b400c0400050b50000043c4240c00c444044004203007285001854903e0496503401d83d1200c050003658001e2145200850560f1001c10543c0c0a8540c4503c052010300d446682c07810b103680036841544200c441271014a03c2c81c1074003103403072105003101e5809800560789148004036070029048d0407180c103640c200603801c03503e02c0d10b520f118080d512800040449040600c10f030400d03120090541c090000c41c1c80e040c000d207031800169140480d00c22120b0442c480b8100c25420f00200c44649030f0300d01c0c900410101c008419132075130003100d8540c0720b80ca43c83c41802d510403d140d510781d0001e80090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 86959254 1250 86958004 86958013
    0x2406091e160309020d0312050a1104030602090d1505060a050405040503090f0a09060e01142b02061902030309060a060f0504020d180f200607060c09030803010b1812 72
    0x58902201a003840c400d01460308001c541e554007580883c0844042d0700e41503002900b00705243c99085c87c2401069000380300200c05105c0008030b580041850701c00d41c4001080240c1c0000c158a60740c5808460b081c140d0b80103449020b131600e4250100c0043c0408846203807080c4c0c2841d0010070a49082e12615006640020046003442442f009111607040307000715881d804100b1039400500a0b00700e02030f402c003038010110814065450004001022100b100b00a0310450507000300046540200b0068000880340690403160060700d070010600502c100c0c8512924084001c02c542d200d5a00040214003401c4558125105e6694007072441d03081b5181030180848850300000c0030402c610f4180c0140c481c910852000003040540801e005c00c04044860b0b00321490118840843e051102500c400440b00801e00e9403542890110f000080383d5204481005148950702c02040310780612940d4010091039100f28030a98a585441c0055890f0300000b00940707844038001d500ea150790038808205540060644c0050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 86960504 1250 86959254 86959261
    0x80304151d01030b0d02030601170105011a030f040602160b180703050c0f04020c010c0e011214040b0c09090403030506030d030b030a021210020a0c03110316142406091e 74
    0x450180000040c129170000c80d1400140259800b4000d00e0f001b000450054a03402a40034401402e44105131300c12030b020113a00c5100e0141c00007000441e0f60005e003e1a0212107a955868144000c0c0140210302e405c06a0781164003080200d102c5101307014201c222520068a43d011011541d02c038011300005000f80c2051411040506100d147d0300410b80c4000c101501b4102c91000b55821600c5e40f440031000070382200e06030b411558204084d41103003e82c1a070244404000001d9a1400401c0030b40700911680f4040300190814108a00761404603400403c6000242041d040040c043d201c140d03a094481d0041c1c042201400c0c5c001c0c4218440f800010f009440e01050640810401c000108000c0c90766001d240300500c00101640300030301080c0e0361030701c5110040406040040110517198400f011701d034000c02c8140c41007906101c9c1000c000c2d904c03540765000e10601c41155030800380048100c29148884501404001c541d10300801d21418080da41c441c0290341e40349101a040c4a2004110580c624180c040b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 86961754 1250 86960504 86960507
    0x10603022b0213090f0f020a05120607050913091506080732030d020f1018061a0a0f090c080705190c0b180f0105190e010b0a080304151d01 61
    0x3082070f40004001c0020748850140c40c2d440c0c140d0007140741201c04002c0030200404600c0e0400000c00a0001038480c00310381203c0180303240d91004060106000d020010507101a242e4455402035900d42c2107000901c1001c510345022411b5100500740c81d8581c1d41800c0000c10f400400040e24000caa08841c1c01c0070786252065056512450341101d0503030300710024503180917161000c1003080c85007680e0f07034010504105200c4081e401c041012180c80356050400311842041804a1041c1046a422000000d83c102010075192000e0b800c100e441c50700014106000110f08101d402d016003120a40082404030301c0c003111048641000803203020000c100c00f4801e00340e0302d100300c0d90b0302540c03420750f81001c000411058503800f0542c3c0046814150110b070f052107010001100b40245a10400040f000b032056061031a03201c2d0050002403800381440b0340d0f0301c40b0807401f85c80942010b40c8803d4041d1007a50b8075601c84500c036489502601072918490034845d80d141e000c5d8405c0203050032000c1d51032002038000061000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 86963004 1250 86961754 86961769
    0x305010b0c07090b13020c060901050f0402011d1809010902011101060b0304080c01020d06090207110915040e0715020d020609030306060f0706020d0e10180206030f071206030302010603022b02 84
    0x1002c4c1c0e00070b1600104150300e0a41031000340456458a001440303540b80c868809402d4910003007141c14408a64001d010050340c00003149810f607540c00c00459100416403020994448100c10403c0c5104c10780018010300c10f40644c4070b0001e1078001ea032900140d01c03261200b18281c90851069040b404800c07c0094003140310507000c2e00c50b0300201c2c4005443c5c0702c1d000d5121000e65070309400803000a41d00007940c108015840421202e1002e058950100902d045500c44400d80080788605003d40d48a40b65401405020300c941e002134505c0d6003190440000b01c0b60000d40d28000740f942c000142c8651070200b550144008281c81c0701e0740d401172605182403c1c1070a0960b207178000c92001c8440e81d80038410440038400c2c03401000c510b00c2c2010010001800000c92070020380740d5410741d03002d8400c03140021101513150002146da001c190388803004035688404608480103044444150400c0d441c1c290040b08055064001d202103034000c1b5184043d000c0e49003403803c01e000b81019030f15904080d000002d030040c00c0440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 86964254 1250 86963004 86963021
    0x30c100207020105120903030708090a0b16051b03131d01141807080907060c05060f040f050a03020706090506091c030e0d060f06060206060109060c0f02100503070305010b0c0709 78
    0x14086082040e09a0020411071046d030304211903400c044104480c8070350169141d070340600401c0080030414141d865501e0129030142c40c0a180700c0c003400110108500a0003199880090500801000c01d420030b205501e0380c0100d034100380b054000070000504c0fa40d042281c0c207941107100b0405040c40c2d00e45140300501401d40c12240750008103c140b0081d41040a003034192151440341c441e00000d28000e00c949041511503000602884140090340e00402e0002070700c04c0c0d20480f07240654003181c441d0f007090241041150001043c40c414500c061081660208030041250300c0c0d80c030340c0c00384d00d501d4504001090061200c495017000d07115158100040c2e095150004260290811000d81d229440120748042c0541d00c1c1502e49135144e160b010031244203403003403a0003410184060040c40c104600001d154010f141f041004000b0b22040c0d0100b40164207052854042d4024451009a07c00080c09001500100c03200c1d0b002c80e103050300000301c400390041116423109074400504403580c1051701400003060480d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 86965504 1250 86964254 86964257
    0x9010b0a03060306020307110c0907020709020705160815070c15020a0e060d0b01020610030305030117070810230603060c0a0513080313091505010309080c07031112030c1002070201 79
    0x1c10002011030340385c0c401180990b10f6a515182c0130b00c40704000b81d20b45030349201614014007080d8200700209501180c06401e440302981c1c01359039400b0300e0500d00e10380f108075107110313806058242000601d0700c0009141d0042d01400300c1d00030b403950b4030000241c414041d4140043c3c881c516000000c0c002002e140e00a0038400307518100448401908000f1950035082465150314644c0d0b2040304005e02d40c0c0410200e9440242200380084143c29960001c100c0d01041c441c900309000350440c24041d28106000c800e014140035821542100c0c03103808000b000d852104000450744c2480e0345003098550300e484111b031003041c0c064002c04051f00c441c40000c1c0d042c0d01030300176142001028009907069010038608403000700304880046484800e40d1800f8102ca00341c940c44440001d2030030a020384c200200c40b0f40b01d4105d034024200014400301d14203204090b4881c03100d80109900441402004109100d0740c80c1c06132050548260641e619503003101c40e9203224180c60840a41d1059094218020442c0c0080ca50035106 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 86966754 1250 86965504 86965511
    0x3040302010f09110a0b04140d0201090803030403080103020405091c120914150c031005090c09220e0a030503060f0105040e070306083d1b0c02040b04090209010b0a03 73
    0x1040d1080226842c0400481d9800d42400c038800c007070f02c5c01500010290038082c1c0380c1883d182c982008884100c0d030f07042802e40101a03eaa9075401d681c02030984ca80200180740a603681ca2800b07140090508600f400203d1245281c1000f00d00c44a070005000206e814250030540041031f000181030743d0300389961854002d21510307804224005510854011302c0507840da0010000343d03000041c1888a244010400701c1840418000c12410600d001071120880d4015280b4580710b44811050600d40c0c030a00302d83d5900300300960b018080481030b0341c10b102c0100c0007403007040040381f40d110015501c4400c1204060000b0700b05201040792450042100342807607105040c0f0a1500c0d030369020914010400300e034140080707035803480200003020701400740c1110300104180d1303401100090b05001e410004903488181007040505064010444150f10500405414000c580c0680c90340d010010000c1e060703040124022400c0c01d42a1010781001d0091440c002e034001c1140107280c1c00e1a048030301030303080050346908060701d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 86968004 1250 86966754 86966771
    0x90409080c15040b0601080606160303110403050c31020c0f1606020c01050702010801031e02060d0902040b040603081215102f030319090c120213050405030304020103020304030201 79
    0x10082d8050940070a031400890345028140400410001001c403414861080d080103010b46d17482c03045444c0035600b0300010198803140c0c28110014501c503407007403d07046030004010043c4640003c091601440c00c80b280c0c450620b846480d690601010420305e00b400d10360380380f80c10400c445138028144092814048610798400203440d14078001c1201c890f1068840010707401d0054641c10301824901d444c007800d209181108980c0006d02481c070510024100104640780f107e070318541180101c12080d00200203e46502c81c81442d01d00501c0201400c84c80b46180209110380ba04040c000d8a0440c3d41080000d82006000019104800002011460072600c0700c40c02d11150fa45403210004030b80c030b4503a507000b00c2c0c2008658494203a0501c40312140d03042400310300c4c410424030000403203510640005110405002703015010002d8a811030300200352184103103000c10002090860111298000c640200011121126800c2190010385024000350401c10004001d540650010341d0410710900c0001001072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 86969254 1250 86968004 86968027
    0x15030a0f08030f220303050916090203071205010b0d0c050706110304022d010e0307050405010e0a05181b0d080c0105090d090f05090403090b0409060f0b090609040908 73
    0x4903000c0c045a22001c08028081800b00741c07102207601007041e034030441c100110b1414440b000103010b00c0090030144c40f000018583c2c50305100b003200381e2025021a008090f01d455450001e5042101d40f1130009000c0c0f80000401c0314540103541c1290261001145881000102480900151404101400410401180040e944d0321500c0742d81c1012428994030b90400d40304001031050b040c2d00805c00061041359510303203030070542a240080a002d007445112417201c2d4004c6414450300d58412644145004000644060103c04607449441c1d40e1600f00556500d80c954031360309440000d50300c43c29620900c0e801e030303210710301c00050b801d5810b0007070604660515aa807503c0741076000c02c0b515540c0b079441d0310910280c4d032000c20030351110040c02e080c6482218202150014003c450380318041c400c41c2480042020315008400040103043e02c1c408440e507580d11142000701900d070a1003076204842d48154002501c40140c0280e6081020080200340f9140c10101000054074084c00c058030422420049a00c0d0350 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 86970504 1250 86969254 86969273
    0x70e03030304030903050c150d050703061503050105091f03030503070513120308010509130b0c07020307120512040e070e0406150f03050c130308070503070b040b0609150915030a 78
    0x2103210341c1c1c13185240307415032500a0400090b90030040c050130114401d03507001c0200400340da41c07014034824005810381d5001000c5010301803640c064044100d030342c00c50100702e07541500251b050b82c2d400e07a00a40ca9496800240c208007140c0d04200f825940c25840034400244034a000b03680005035860324904201242d0f0482646150380da0042081c0c6041a0f0039204150300300c101d840c010101101e00038101d1034603180c03d80c400d05451800030094503040c80041c030001060070642c0d0080d9005021100c010342c550b003125480c452402d00540305841030740c20300720b403811a80707007140c0c192159405180c03655290150140d46562080003003a40c410303154000803550f10790010b900d03610010380c0c4c0e60300c1030505d40d01c550203000c80d680604035051700802000140a40000c040e40c0000310b0340d02941c0c1c1e555441c00c6083c0582103004e4201c0c000e0048500d9001d001c20b00000c450391a01842048403400000d4464802c10030b8030403154000c00343c10110300800240c0700780c002e06220020f40405800e0300c40701d80103540e03003c081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 86971754 1250 86970504 86970511
    0x80304110a0f060f0903020609010311070c030c05090a0b2103120a0c09050307030c120f05030301090606030e1606230f04080d0c05030d1509090302010b030c01090617070e030303 78
    0x605240b140b04011140d44a0000542c50341c0c2d07802e0000e007180c1143c010400901c42c0c0e01640781819100d41c121080506510225044d5075044074044003044d88a00d440e41a8580318402d00b40700708603607404150210824031460900e52002005008030f080c940d01c00a00c4001c804200400d6400284802c10500c030710999a203105144d2808001819403c54101605628258000324029840f0040a0000030038508a117030070395411113826076184003140303040340107051840b1000309980800300000403880041d411440995940343c80c14030502000348169559541c0c0742580340201101c2000400810740a440c1071140c10000c1d10310740e40d059a1000d1083c456038007190041d41410000101044040024412000b8072410741c030f05010007165070303141c699681c002c41098001096540303002d40804851409400000c010000c01406801414200039000780711010506002c1d006590551426610420a0750b00323035803d0b900c07407410b2407076502d645040c81ca00c001c00c0c0f8400c2c002e0001d82040f85a43c1040510f01c07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 86973004 1250 86971754 86971769
    0x120a03090302011e0215062205070e1203070201210e060402030606100f0302030a0f050703021e040b0d02070206070203011b11030a0806010507060b040c0e040e030412080304110a 78
    0x1150340366200040c20300c455448000030b1000d40311291013605502140c0305c0c01201002c1c2c2c40703050340d072501400640009909190024000c2808500303960407109034009034445c000c103443c2e8100c01441c990074050b540d800c000c040140d41e08104000710056014000303026402030489080c4603005242c0c64081c0440d01d01540100c890f501a00800046140410525a200e0802d6445503d4100c0c500005019140151410424142c011001810800156020042803509501e00b80100d00341002c020b0001d500c800e9000c1c0e0400c41022182094442d41c3c02282c045401d1a04020b160150814003240207401c240d03002ca90000003040410096907090080d0303140400c120942241c00d40004402411211885440c01d09540050151000c090303000720b00241e2000c02800c1040da281980d16000c0000c0c145000c140798010300e89110030310b10b01d61290041044580079282004000d4503c4002c03550303800743e44901407441c50343e100220001a0000055a041485042c0480d41c1a603107400103294020035412151 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 86974254 1250 86973004 86973017
    0x4030b1b032701020a09030b04081911010b1005040b09010306030203010204030308090d080112150e01050705090a051909090206070507030f0218130803100803040807150513090506120a03 82
    0x2040102d64070904800710308680000c40c541520124090412166031201801e148a414002000e01a15800b141d010a0062044801c10114444083e002c01900251400290b00c0c01c1020718090030700598101c2180c0154a07424201032800100c0700e00c5900c0180114105919840000016103003400a040a1440b90f10741148900d03099900c645007030118040d41040221703a40041001e03d9040d03186040882d00b10045041c0c070782d5011031100280c40001810399142d8a05020048000e6212000e00190101155002045179541c03041001188040b080c099410b41e00b0441080544c4080c2d01c03a07016584082d01407400c150070364640300d0800620780e00c1034910f40403c004036021854400a002e03201211a24100810309105290290210751040300821061001012500c1142002d400000030040b90044a64980d151042161a08034511503600b001e90810361440c6094015010343e40d103208898080e052103403401e1041c0020f00000b5000c00e401c94041d0340402100601444258800c0b80241c0702c02c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 86975504 1250 86974254 86974291
    0x717010902100507200609060a0e010f030c021507090302030607020304030c12050d030b0109090608030702130b0d1203062c01060912031107050904140607030204030804030b1b03 78
    0x700c10303021290030704030802c03d0801400c800148507210328458400f83d212890342d519038810110f4990b1003441040c0b58840301c0440d40254295200a00b070028420a0341c400c4140d0955000980540f22000c0c1400007682004443c07071410020340410b02c0d400350852500d004055501c2e0003003810101c0980300c84d801031b040000d0510900c60140c5540b4000e2807001418000d1001c5500e4107504c615400d582032007016124441d10340680c0c8591950f401800c0e000d0300030040c099035401c4140e603d50002400701d0044c41600284d031a10403461050141081c03000e419a900c42602c0d55034441c601d04000301250038107540e08808114031010100e80d42541c000c0146584885a5000c2e003a1031603a4140e009030200403120070203016a6005205501504d070345401e015813048a103140080c00e1400e960051504249480c00704418171400c01d011510b14100d42040c3c513503035120840114260f00c528000038010740300401042001605084020b40d104002150050f015907100d400104d1652040d603609020316043c04c0c48 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 86976754 1250 86975504 86975509
    0x40203030f1210150804060c1709150f04030215100308031303110705010e0105161709120109020a0e09160803090a09020301050906060a051b0d08070824030717010902 73
    0x10080a042401c01100c84c0454512004180c0741c4000d200408290700e80d00050300c958000d000e07100024100d00362003451846d1680e00a56180070200c244034542c1c0885000c0f4410074080701c0c4d141e000d1601036005c0c11041c00d108040a801c032001905110b42e0324841c10000011584000185000e0300740c02c1e040001c1c4030b0a41c10000c091040140711900182c0020780d0411903a80c22100f60b00b01100c00f0f003031990f201d94500b03150b40140500440054080005803500d0141d00410100500510710111a034a4a83c44809091800c03154002d0380290001400e850070700c810800c680b003040c0e00440280403100d001e65a10001c81844025920400040d4804100c050291410720207160180440b00811411503160500261f01560041c000d00d000320000581800518410030490745210507160101c0c0344600003060041ea20024030700c0050000f2041c0011038615881212481d000c0d8913195480602c0180c03100c503062400303d4001240360305105284001458002018040c0c401d82d045500018050304107005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 86978004 1250 86976754 86976781
    0x21306080c030f06010f0201021c020405011119030c0c170f1b031002070203010e0316050105060609030c130b0d0602040e060105040303021e0a020a09020d06141305040203030f12 78
    0x7420005070418010007511002c0d403054280e00800900c0c1503468003003030f88010b0340240301c0c0c0d101e0305807514449030642c8103c0c20642c00a204452080e607071001c0c1d0000d44030000c2c0d00c0310081c00601c0207180c80b049171840464800c60000b0400c501500d040e40c5002d90310380c021518800445500f5446402820140e2103041c018080d0903000240781494241c0d420791000002e407a5480046290240c581c042034040035501e003540824200c089080440c1c2c0e40b10101000d9402544c5065403c480315801d0000080d46820004140c03146076801600810040b030300c0804010300d85089960b0201e90603924280e11500b40e440d4403170708070001e026410059035141001e03e0140e098400038005414407070100001c0000903030000d640812100c00f440c4a200803840c80040900301500c00002030b512100444000c0f0f642e01e0030740e0051002842d40502000340075034424103500058510062103034041408a900c2481036617a400256005100400b541d02d055020620407280d5040088028444628802081402d80c103882d0f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 86979254 1250 86978004 86978011
    0x50712020a02073f050f0109170904140c0a17040317070e06030408120f0106081503010605030105040b22020303040605090103020921120403050304060c021302130608 73
    0x104103601d892440d80010750b450000b441081340510782c5414200300642007059008418208003506143c6460310080240f48822402054803580070f800e43c1105041c0d030501c03c0c0050a80c3c82144070300102d280d4240644c0507080b01c240950010788540c0300100b100c0580008a100c2c100301820310345c031040b903c00010100c1c50001140014400e40d0307000c1c807000c01d4010003500644015580f506115944014041321032034114008e40f904074070b000c03050000304440400035042c005010092003086544152211840007000e01c110760104184102189503d0300024240110079005000400d0703899482c2c02190841341c0c125001d80d0282498002e00c1150b40095042e0407048285a4040c404d2100c035400298a0f80b11314403c000c2809800100100d85074000d1701501d0580364010a031401c00d1800300700c0c4081c1c4440140348680c240c0250410b2203000791030344050300c1c140d9070050011800d0500300681130f02c03034529411059030f01c1200384c00e2120b01e00446000504103130320044d101e0304030103142406c09081c114014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 86980504 1250 86979254 86979287
    0x6060504061d06040e04030507060905060105090c0a121a0d0c030512070b0f0a180f0302010f020a0c0605070c0c03050a0506130308070c08040f1409010b07030801090f0b0a0602010507 80
    0x71180100c2c15941c07201540d0640e03d201405c0c45494603249410741d40e07072042010042105d428013200405118000c2000e504880b020ba035680d0315980e924101c1e0585101c4d115425011a90495072000e80f01c29940c001000300040c5110b20750128001e200055501440c08400c82e2203824003481131007004401c2c0050301d4180240c911003030614085030f071034040144004001040c207010001c0065030700076040d00414010401c2c052240f2402c4800c0c100052540100141a405903081030707003071901810584222200b050090741c55100c80442c596603540036040c0a00448100000c40d601000424001e0100c04010340c8614001d0100d444649010360030300300020801d0b25980005034a000c0440c0d0800f944592041041c50001d4910b0b03010b10b0002120b000d10740080442243d000400b04d0f10480310400d4200c2e822044841540c240c0e0f0750b4000803024890f0b0040100058060f50041041345525000904115889600031500000071004a605c42e500c1d944801c0060707446005200d50240c00241e0005802c1d04c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 86981754 1250 86980504 86980547
    0x60b03090705040213060e2e090e1003240516080601030209010504120212031c0b030307020d0311010b1305010905130215070201050c0109050c030f030a0f0c06020c010606050406 78
    0x1791505242d8401c01c0e4410740040c45040c0080d405907a66010b095001d000684c0e4900e5081e16400c1282e2405001403d040d0000c59290701010038a0407001528901c14804908059801070a60b038880760f580c088140104d04000c04031101c0300260f1114081c540c41101d54880c0e00c08407a042d840c0003404060050309160505104012442440e64808101d0b0152514040305048443e19480450410103c28004151600020503501071001d59007103503141e000448c400c244880e140000c02c2503264402d0410085d8801e0101007440006130240c0f2a03000b116844400000b06030465001181d811480051080c460300d0352080180040f200e5072003019041a50345091080d80c14080d804256568507071580c40044450100c2c04c001168031030303000c84a600605034001d00c0110321900d44595103848407402540b082c000e0000481e19120b000040c0c51000e02942d07180342d125800c4131820742c0c10728401c804c00e4502503020070810f681c203202405003800910f015941d25a40e03d14100d0010b1189400410b10521105e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 86983004 1250 86981754 86981767
    0x709020f090f030a0b01062606060306091e0c03040b0a051003110a0306060b130e150405180303040b060f031b06030c0c0609010c0f0905030d0f0210060b030907050402 73
    0x350400350360022200340e071507803521540000080c0c40c0c075001e90401040c4030b182000110303032140c0c0000c48014903007040f910048204124403d8402d00c00040710340c02e40007030042c8002a81d91403c4084c81d0340059525101f04031104840c584c0384070190b011664503503106000014001003080d810302ca20f5004400510400040c20003010818880c5005e20016041800001c02d94450369254225031000310f610404c00c015199807256001027507040400001d15584406000003803e0107103d40b61845281c0d80081b201100b62a0310030440105409004010105406018241c03040010001540941e00610210516103040d5007008410412440c043e40240c100f134910729600c03ca80c05080100e844103e035032503125560031082250ba809400c410141c0d034441c0c0c030280b200f500810350240c0c3d2800e5144d40c0340c035101f600000d415070b09600c0da403243c0c507050782c0031111843c125031140601725030041651040c2c0382451a021180c0c800d50321181c11080803110004180074407420f081006000608094405504102 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 86984254 1250 86983004 86983027
    0x703020d1b030c0302010209030307051005060a0f0e1009090b060f03070f030b0c070c06090e0c0717160204020a170604090c0e0a02130306090b06030f060c0f04121103070902 76
    0x2081c0c030000400303002512400f0001c0600030f4040e01c006071005412030380c0b02c03000b50410315517a03102100400325440c5060046012410102c242800b40d4251a8240c0394075468200d05801421006207101c681c000640d40c0070441a072140960a03d40c1d002e0650691241880810869524400791351b43d8801d6101c5481007242c803824913043c070b040300d40010300304d0140d40d00c003c0014054454140c1c01421401c06071404545982c00080802c01d890015100030000c0d079030b10000400394841c690000c0d0500070041410104241c0090003000542100c0b049101400b60990200c1c060340c00c83e040d03500200c5c0c5d1614584038140e01c200e10042d0b00100c101c80c28841c00f0303441e840e2041ca00542c0d011341101c10a08800041c0d4152164044407481c81c030008032040020741c2c81c1071a070b0080140381411110254003901080c0a403400195000c03c1c15110000b0301171944511030054901e07885144080c0d00a2000e0100007482503aa851040185014a640703400c03841904040605048903070308691040c62040c0134035813414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 86985504 1250 86984254 86984297
    0x130606120b0109080f070806010602030304021305270c0111032104020303070f0606060e011e051608070f0b0f13110112020a0914060913050408090d06020703020d 71
    0x480010300080c5040080004070703084912500200d11600c0703210341c0002480000a5090110303150743c3e09079003507a6215502280c99110070398010750700c84040c1414020201e1030f0703809030b43c004100d80c404000400b4003a0300340001090100102d011600551003074031142d42c10403034081d02003651742c4c0558644040e0106100c038214600100700200c071170702c10001c0d045440030011901c200740c103c51010701220207883c150000c7d0200d801503400103441c2381c0200500d940241e100314030240e07244900044042a4160844640d08090581768034842000f140c00301107000d0070001c01c0508d000d4001051102c03802d05001401d148090420703420720082008210100c24404052400a031f8000300f6403038494020030040351400c0e2221041583c00e071001502403817103a00b00000c2011902d884c02c0e10115542034034200000790051441700c0ba0040c480c6880181c0c0c03195a603202552041c450f410050910703c410340440e0141c80e5040c000c4802d40c1c1e000541ca03044c1501080148603291170307031a054841119842d201d4541 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 86986754 1250 86985504 86985527
    0x5031504140c0d08090a0b210c0d020c06010503060705070f081c0204080c10090f140607080708030411060403080406030515100207170c030c01050d0902060f0306130606 74
    0x880c4007111081c000c04090110340448070300148840c010010b242407039511548041c4d0120320030110600d0004108000c00103035640e00c12480f840d45a01d401041501c10402001001c00310b11100400400b28230891074070180c280c801c00d1500514030741d81844241450160042d04220502100b40103030800200c0d015403c5881e035601899140c3c480805c0380c0c050300b000d0941842d0b0341c070740e50011401150b90440050794400b100780841e9900d19102e4960001d40300c05619018811250044401c113001d000c803032940c18010301102901c028541005901c90007003d170800b04040311040303400001d0009214158101c902039002c11103a0600e0149165540b0441e2f03c682d2240c041410703140c90020721845c01e0803d00003c210b03405050748001c0a00c42c5e50084d1035058900607126410308003d0074203044140024170490054002d0001e001c1441c0300c40c0103441d02e81000400110700c6031205180c00040c2c6490014051000c80312100948a042440412280c0d01003444401820f40c580b00741001041d80c040e652a50303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 86988004 1250 86986754 86986763
    0xa0e0a031211010b090a09021c0b0a0902120d0203040f09062108070203120405040c0801030b04030e2101060303031803090302120705060403110f01090324020c01050709030302060105031504 83
    0x40c0300440c440b50390140203080602507104807100200000311225400540c034203407084401e500a070110040c3d40556002444014002ca0b94544c009640003503513910003c0d115000030202c000c40d0000700c5407103240000310758101c2d00680000c90708008a4514800316405060514402d0240c0360038401d03060401c0a16038505c10041d0381010001061000980444403d15006810b0300c043c0e18008082403000d0f80070b0b10807540228503054144c0d481d10f20a0000790f040eaa48210f6542140e19141c80c103e550032090f1074841c5d481914425412080032022504482c0050920000300f90103155040150482e5080100c0510b4180b03d80703819000603074009005010750783d04541d28001d942c28071582c54580000b81d000b150b0461700006000c401d01c0302588070702a500d10700320380890a00c888000110703a21800c0b48030082c51004541c0005001c4007045550314054507600384018103000b201c21480c2e081d92816908440400d43c1554140309241c0c2c140103a40c05407100350010030301544178100310091010000d00242 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 86989254 1250 86988004 86988017
    0xe0307030c0b1801150501090915031101051c0e120424050c100501030b0a0e030706020a03020d05190c080c18060708130e0a05061509030a0c09020a0e0a0312 69
    0x402d90050781a41d501110a001c0080050079851704005111000d5802500d0124131000380000d5404454060344240d80e0800000389502842c41d0340d850700d28000e1200c01414048144000e0800c10141042b0041300b409a240100318079099140140c14008408900445030f41e08000034489a001d1080341e0103070049194003000300e00d08a00c0c0c111081e0241e00c40c0580b8a0040d42d019200605841d040281038900860401d0300741d03241c03481d80e03004507030344c007510045c1030b41083c4106801726400794080c140e030000c1410b0161502d449540004200d8604580c1c04610044207503003100b080c51b00748214101e0344080d00b0300c9140c0c0d08140c101080c0074002d41c07004400002c07031a004601c8684a06054640683c0d1103d21a074443d440c1103510b0b00928280c1c016501081d02440005090152a000b024020310015140164003942d162000441d503000310f035119094801d2020040c0042c480840303403401800c0e074800042c2c41d18001c0200801081c801c00f2418810034080c0d0042c4040390701c80b1041004a0510300301607 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 86990504 1250 86989254 86989261
    0x3060605070b060126090f07050301090201230706020a1706010c020a12060906050109020309150f0402060c01090b0a0b0109050f0f1021020d0b0d330504050d030e0307030c0b 76
    0x840c2d17440341600d000c5c0382503030111080c00091392000803550601c428640640d0740d0903480b4401d0508a5142d1200030340081c40300b525000c5401d417100b440180c0e4030003280c0810f00c2e00c0f0040d03c070300080e68080508480040d00d940651100c40783e1040980d038122209191201d03032010280c00240c007c00d1236004010041c80e09410b40d00410a45512040c0080d5003d0414880c1d0360355a07036210025001141c81840c0c902505082405064400803150300c2031302e24102c0398089480300c1d02480807940010030600b030390b5980d51100501050240907010700c5500c01c580045030341107003040010005001036200a01410190a0b000410b5444224a00d45108140c1c1c0e0403651481e44101261150001800321032049058131204068540310780051460b4201e83e80f0901200e9180414014860203829000c0c040d002d1000ca0307031200c1c1d580032008084e1801c04400781c42d04008215400740c03c4403410740d000c81310360344004841441150540035070140401820059403c2821540b00a8240310b1942401084241000c000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 86991754 1250 86990504 86990537
    0x10e0702010207021c020f01020f03040b13050910140607020a03060504060207020d0c0617010b16050102130b030901060602030f07060207031701080d030e06010510030506060405120d03060605070b0601 88
    0x60f24001c98004000b202000f805039028020311004c0f800c1680110380c4050303940e030f8035400000d0291525140030021441c09180c001c40349915001800c5020704052204400285035440d030785000d00039019601400103452a010171800c0d00d05040b5401c0303008020521408001d80d8641d0700d118216a002100800d40b83c1e500d1a200000b03101e8040001e41c4410120548414400c5219010b02070f03c0c516214071601500f14408001c1d8020b09110f03203030158804204412000c4020388090180c1c030322131000541880850000c440140e070b0f690b0000540703aa4003008001944071300f4010f0800420590000d94500081c2144104540c400e0b820060041c54000075420b0405201d010410381c1c2c080d605d0b551703021958480c25502d8503801e030070340200300003810710f405100412004103016048500091000f40a20500d44082d405002c0040c02103511420600001485454951650385001066405000554410500a01261000d8014008000040c0241400941c5220006410000034240000d0a2015050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 86993004 1250 86991754 86991757
    0x1030e28050102130e06010905281701150911071704090516080a0e0c15040503030a050403050f010216080c0a05010f0204051005120a0c2015010e0609010e07020102 72
    0x404561000070010220040c0c0f10000003942c01c4042042c01725194000110f40854680c003555034010041302820200c0010100380003100c2040821103c0c5441d40c034543c42ca1040041e120800f41039440ba040c0320603480040786e1000c017170308521504025620102010420900070650001c00c4050003d03545010654103000360340003401d599400307006510f41142d0403d1101c0e0480f100c10003149101c00800c0034111140151007010801c04020050744040c5420050040902030300200c0006003007102141c03c2c2c4041c001000b0522280e1941c66945195150192400e50312a50b07158560348103102e440703014403402c00140e82d0641c2090741c41e51030707044d05503415045c41c0500400030080d41c42d1950900d055642500a44101c88048400c03010350000c460065440b8481d80c0c01d00c915000d400c01c000398034030300d15502c01c03501e580321482c00e14010410383c01000d680f400310300424031081e40801d0b16803e409000b105181d0150491844030b031540e0a01d44041841800c042c01a00d4100c07900000041600c0c2c0b00b5030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 86994254 1250 86993004 86993083
    0x1502031309052205330a0f061d090f1501050d14030d050411060a0e1201060302180a05100b0702010c060f0216050705030a050604060515040903050a02070501030e 71
    0x3091003103000ba035140c003c1ea41c404c40404c948000e6403030260a0b440844000c041c0f000c080003501030242d00e1b51481d01a10040012000c0840d80704d80d00c500102c1c0c6c081c10403200e820321300307003000c15403d2a0401002c49441d02c20800b08000084e8170480c481c180700c0102006039411140d0035148085c1c1c0454518001180d001601402c810b14800400c20032180e0304942c00041c0140d01411480180350502c200b80f01d950303c209503c04011441103122200035080c1450741902c52003004000041882c0c032680010300c0041a420207010300481c9e0030a20040780514402d4a410000b403052565500c2d203070401c26003a41c000c030791010741072101e0005180c040c404d26800070624017240c3e02045507150410400c181c3c100c0425030003510380f4414003c000c00c00d401e0018050034090b800000030041641c0399038403507020b450003c02c01021481c085500f0700f03103621140903005806200b600c80b192209540b9100030300d0030b5040da02c03c43c101402d140003070002380004a814400c00041042c000222420a52414103030502c1c403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 86995504 1250 86994254 86994301
    0x702040603140c0a050613030201140903010507050d0c0206100905091c03020705011118090711120301031b060f030e0106031403040305070f0807061b0b0103050601150203130905 78
    0x41e0000c2c070203860118481856000c100c0b00e0224041d00c1e10b05110403401550f00d41155150401410300c00b646c090114202880d60417049580b4001c01c00700030a013920300948840c4c1c0071503000300d142405541075001c4c6c0c3c669101c40344010b00d07540c5030101510890111500c00c07000200e60300c00110704201010b00c141d0290420507001a1806005003000800030361041c038064900e9403034148002d060f250713001c0407140394080408094901c161200204180130340040c01c1181032101240c081c070400103041c01024030b110203001c1c001d5120b601d541041c07031505902a2500c40c12000f06c100500866806c0880718000d01414540000d0180c4070944a500505041e04084c21b44542d0780d203a480040c1002000b8815a84120145c03140300c0c3c1d80d01001e83c0041840c4c014103649400041080c4101c900c0b0b9050810309801003100b01c03408004544071052528400e03042a00e8030f41040c0010b00034034142c00103100303c060f1180b008510749481003c00c080c41181c01c0c059095101d80360340c04034034160304a00394011140d056 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 86996754 1250 86995504 86995523
    0x10020901110f070812040510110f0109080d0c020102070f0803071803060c030e030307050a0e0103090618060e12030f070519020d020705040614010c1401020c0312060604050d080702040603 82
    0x2e05072070a80e2107285200e1a2441c0c4501101880c1c0a8010740943d401c0b10406003142c0001c010580082d101080c81030313040403152141030f1600013481024041c2c5c0030140c1c012030483d9503070440504030310305076000400504150780c0104400c5001038005110001c983d0307000341c241501c0e501c0d035642c101e400c841001910904074510325804414081258011101d40c8a00d850800081d10184c0555840f03001c11618100410000d00c42d03000503601843c0070840c91a414940056070101d10b0382c03080104c41811001e0341c1001a1b200c0c00380c041001c544030721006000360b0310040580080c00c0000782c0e1030703110091402014650201c00b1500b12805001666208141e03050300803482c4126407130007540d4450b60780344503005104184000445041c03038418641901c1c2aa502c2c4500c090204006584201c02080212941203c030400e8000902c2d003031024185100f0140c0185a0b10300240d0024a02d45c440613019600c110001c01c0308010940e02c1c5c1c1c03001e00c07000ea4008015620340c01c0380e00001e4001c020340e62000c1e040204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 86998004 1250 86996754 86996773
    0x4030c062408010e0606030604030207061206050406080c031011040504151a120f04020105070b180f0705271618030c060216030c05060702041e050f01090e1002090111 73
    0x19000320001c2019502205d04550710101019610722040c3e03005405a0040c030014441e1034841d440c0707420711003404a00401e04664810104045422913800b44840390490003061140c3c0c601030103c0081d00440310400d00800310b021032641c10070b00c00d61049034800d95179440c6042a400380c3c62120401080700c6da05081010340041c840005545c040300c2e10140361004400001c0d0b400406040c0e2034019601a990303541060aaa42c0b01001d07407102502500c5e815004000219242c4001c1003804440c050100140c0b40141ca07200a1140108520094503031582c0301c0038590f00c546102c0080d03554008034003401001464119402640d00015054a0b02409001d203a0080280f0248044000c1210030543c21140034440c0ba42c0000c1c6030340c2050000500f601c203890400c01841c03a00001902c042400148002511003a83d44219520501003031102101a11941082251030034004240e00420050b501400702000600301d09441ea1601030100c62a1640400c0b24455a48152242c114000c82c40d01103400c05030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 86999254 1250 86998004 86998019
    0x203070504030c090225030309121d01110c04090c0e0a1d06070c03030c020c0901090605010305070f0906120e030c06012102010905060307111501091404030c0624 71
    0x107010b400306549001c5858400514628907100f00e80d80e010b10704003100101902c014880120040c40300040e020141c443c07206401044140c4107140c140c5c2082c2e00c0c3c01e0485a0724002e506600300341445000e061010100e40103059240200303100005400071500020300d8006403908200310303070054000144002c2144200300000f40d00e03a1218074811262440e4850007800b40e0925561400b048490b08000b4101018036000240203402002150700036006881843c0c64003400700390800c0003640020789044e11020100142c2d41c00d4442c09401000b5803400004c5061030100181903e80584501400c00820f03402c00410b409480c2c2c803101d0b2049c51113050340d40e501d08021071300395110b00a000d04200e404445144052500d00c40141c0e2020641c1a1104502c151518041118170b030001040c0030184003000325203540c1c41c078081c0324108007883c0c0802004815410459003800b11444100b24141c0282c1c1c4106000110343c00c41031f4101141c4c0d10100104080b031100300f095191021802c86290843d03090080400c468 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 87000504 1250 86999254 86999257
    0x30d15090b300307110109050f06070b040c090c02060109140408030f090309040204141005180f0402090306130c120b13020102071a0a1e0e09090304080d050c060a0605060a030e1002030705 82
    0x2001e09907104187d00b510303074041004590283c1034440e4060001c00c08440090441c03c2465401400340311003d10b207035928a04a0240e03158000d0020041c2c01c800d005000c100c00038440c41c82c0ca44c3c0c51141e030180c245031940e124122031002900300400b603003076071000800c490707820400c98000c0d10b001340055448513500c01e04c3c200140508002c0074418140d54842c2158544200143c1e0720082103944942c8181d100d41c0c0500c01c1070920f942d84290015001c009140743c94a04016070f600034851549885040c5006007454102804240c1008201000d030200c48000720700c0d152050307500031131080300c5030b540000244010303271901c0b007164402e190201c0c1054001c001d08620402500e803210032500d07104102d50f011608007074400c125003003000200d43c0268840d101030828810b015441a2550100c0e031809440c1e02400d49006001e4071800009000010404107421081c8140d40e0070101164050100c28140000584140115003c01d0105691220a103400100412582c0c0301c0600d5100219a01e0030308440c000c109 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 87001754 1250 87000504 87000533
    0x803161b051f020d030e0309040207030c0b040b0412050703080708060d0b0709081002090303030c090607080d020319050f01030209090106030b010b040302100503090703110a08030d15090b300307 85
    0x54012032461130040b0b8002e00400c00310303042e400095484c04c09660204002900100c5040d03040210074110040050544010719000f01d008102402040c5000c0c9400301c03c030b4400841003810050248000c02c0000c0d00000c185c1d4108044d4209444540d4502010800c40f0280d080060410700414082c42180e80e080100141607804075010341d52040c003007403092001d80c03080b800c160b034065004000191001e07901001400010000400313082c6807107150740310110150044035010302c2081e4000140048400d0500c0500f9102c490510140098035000c400f8154180051001a01840c005400500c070481c003076000802441d4003180018095071205a2440b4540050104134021491981c4840315640200c055070320485c1c88900401c0c13400c2c21075139000007900401c00e61540103640e00724045100750051010303016110324030310001414000d03001c0034802c3c8551030340000f03070391071074050b0304003094039800c1d84540079860030302c0042030004000c4841e4400b0410358140f191180404180745081101400980b140c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 87003004 1250 87001754 87001757
    0x303050403021b090a0e1204060f030614090a05060402090d0b0103170304080a05091c1a0f0105010c03181e03050115050d031b05071805010803161b051f 67
    0x2038265040420350f8005451459440d4000303240344c00101910890b401c07110401801a043c2c80340070240c075807007015582060300014041048007007807040395070f4107210b0040200380b112404a1a55014000b0484601001d490504900e444200059094450390120b50b4040341c0a040d5011400300d90a200074128400c0c0801c654403e443d00c44035501c0d940103002c1d2401146c02070580380c54019016000c1c0da407944201845a040088405800407010120318205511800781e0891100c00c03107010220855a900140092081c07900d200061140d07903880800c80078826031506010176007010240b042414003001d07502c490000e18450324103000c0c2401d4101da42c070480784200000c1c010b42100080104c0c880d0b07814007034580c004168100c2c2602081c4a5100c1000d012052031001460300c9994a40c00d090400d01e4000c0040d50030250600c0300c02c07280301cac8255801010440081e6040030003071004500c01d5005100043d040406082d5400101800d5001c901c00509008103012088400a500d40b4010100c0010703040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 87004254 1250 87003004 87003013
    0x60408070602060f04050c09040302070f030b0a0510031104090c090509010225031b260306010f08130803091612030306080f0705040e01020d110d05090d0806090c16030305040302 78
    0x44c2c0415a1103034a9000e0b17903020000d003407001c0044040c480a5900180140d0851003008030018514404c418144061070285c0892900e51900010700d005a441c040c0520040e030f5411842080480d540c0c92042c2003035282254080342451a83c148001e8124030b03500030100da03078030740070611404c100154001c1c202104803498180040f400c94a81040f0100642c80c0980451101d0803081c1c05944031160300040c007403080d040e801140302c6082041c108502c051481075503900c1c1c0001400030645e0816034840402030103107402491481c02c03c1d800d00100100c0c440c018610100400460b054140920000345541600070040000540e070f043d02024800818000f5000319240800104100401048541d0301a18940c000c2550a1809044c4001810032045401095601740802d00380550b884c060640340310442c10303103103441e0104e00b2001c204445000d403000d015544018030802c142a000390030650711407c200d40c02d01c100c0d90740c5840401980700e101020b041408201d0041010590503501480c0500d01030b03404c44 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 87005504 1250 87004254 87004261
    0x60e0a0b0a030f020c0a060b0d08030a050c0706020a080f06030708030f0a020f1605040506060408060628060e03070602071a090612010b070b09060903071103010e031606050a1107020105130506040807060206 90
    0x291440c458000640ae403c01000003c00100058010030b41161350480c02624090064036010f040740c000c0c00d20200001d51201c18001521a0104c006821500440141035520300d403176680c982d207201d85074900c40d0880c008295024094000e1040d8402105004241d41d05038a1078401044501440c1c05280e106034941000308041c0e041002c1602c0642c0c084000500380da89656081000610800b250f580317403045150b1140c86040c6480c0e0180300201081e032140540010540101414502d064120108550141c941001021148960781d204121803290040e524403c1d00d0120b40b080c41141c264400040c00300e0000554603650600902d400d0b8011170040c042e60310f03103066042c2c0f602016240c06110340d00a0000e540410304c0300380303800302c5044001c00015803900c040c1c004a0464010700d60142d032502503114a40c040c45018040c0aa211502603810003400a050540040301d0041c48000303810002c0c0854101080c000d40e8102101030000180030303030b890716903034400c15540d07840c64040d0800500400d40070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 87006754 1250 87005504 87005509
    0x1060207120303200a0c111801030f060f060b07021002010b01090611010204030c1d0a05070c080a110105100602010b0a0f05040b01051b03030a06060e0a0b0a030f020c0a060b 76
    0x1080c0075201075844468941030203440c124080c0002c1c2400039540e00003031400320005507003140200f00c1081c840c1c4900550544078100710007d8001035106c40d0280322800400118904280c5000d41500d40c010720358541081903080140c020003d00101068403440c0100c00b10b84c0100c4100a403004500c202c130040301c008c01a2400300d003680d022a00090202c2c0900f00188940c1e0b0050200203c40700100000500f0584d0300d442d0580c45114903400810320741d5401c2e00e07122401801446e11307a80310140394028030003810301e414010201d42090318090510807000c60740f03645843c454007800c0c1191600744003c0c00641045086408905041d100e4103025610b003a5a000450406075039400c01c45001601c1d0b00c040c5460b05040c0000b030300036421080e040110400507040280c04c05400e00640c201018011070720384c035150a521049482030780000040c0b021200c221000e50b6108001c0009480d081580682c84410300c240c21b0380a8440c2c41d064080c030b60300201e0301154950700010418042d03806080c0c01d000843c410401d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 87008004 1250 87006754 87006763
    0x190c0f0507050a051806040209010e040504080a03060b0a091202010309120809060a0b0f1c0c060903021309081b011803080a0f05010803190c0212031c2702031005180105010602 77
    0x15603170410341c42c07603000625510300f07540039040e4010181000031001150b0380003d002c58500700c8003103c841c800402d54054560781441102c001d0680308030342501c1c02d815803101400c400a03500c100700c41030100c540c848085910039045040800d80c450000c01081464050191032158116080b662034401d030000110541400e0041881d040d1000d4408503400341030030103208205410115008801c0f00d03520740c942c0040d070002e9181c1e0007132146d541c0710552141907204110358400700c44e04a007005820046400c0200390420111440c401c507100e00c85600510591407640541a05002c00c400b0b0401101d400b8145608440d07240c0c0b10b405844010005045101d1091040710821701580b01c05a00502030001000e121103043d1a0140517801d1403011204940e0014000d010310200b2200d4940012601020281e03210358808242000c4200174018000048460040380040400d02a06070f40842c8041c010340d202401108002240441c045c410352600860141190800400d501e00b25881e000001451900c0440c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 87009254 1250 87008004 87008029
    0x504150c11060301050a0b0706200a02010e03030105010801060503060d0210030c1101060807060f0e040f09060b030606091504060b07030f09080d05192001050702070f050303190c0f0507050a05 84
    0x1748001d42050034280709a43e140c010901c00c5540c60f40d01c1a56001c20014180f4a83c402c24140d5601a5621042f440003406e42e600c8060486040d8010f10052010341e030031901d100c2c1920054580661240d45401c0090031082186502075040011030940c81c83e030f5035240d0001180f40c0c46945442c012078140140180c00c95219200304456900808400d0103464401c41846c0c07254421894200707c0d0400410009040f104082e4540d4003c1d951840404c0c1044218091030184000840251035640703814808202510402800380d907204c1242940c19416580d180d1208020301f0108640d40c2d2504014034020b8118408001d0a0780401c140c00f03400200c0c0040040c2c01110041c1594580c0e0500d80c0404140c680d406440e0000e90038010640781601a103000403218182d081c910400200c0c072414902e8000e410a045500001c0e904200310000f841a074500008651040d8110b1104418512040c401118040d13256100102448500041842400300003da050103940e000c0b905503414564035402c00c0f40810b4030071b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 87010504 1250 87009254 87009259
    0x3051b0604120f0503071403070605010e090c040e07080a0b01170a15020a030b090420060c03070b070302040302060c0109050c010f1205090c210106050402040503030414010504150c1106030105 84
    0x1d02040001481d0f40400d864152184084909000d250307a00d4011586a409001860380d102007001c1c0c0901141c0d006c2e030303801065040040007035030825202d040d40743c580c0300079081c1c041c0751209403d5220350810000d03d0000d100103429141c00b20140e1910800000003072180c0350034001d643d5036400301040c0101e20074420039809205c48080ca61100100c0007c0d4110414080c00c0c150354442082d40e50f181c400c80e15100310300c1010160380382c118a5103002c1041040c0e0aa45020300810f100502d62a8000070841d4441c0c0c0d044880350301155504241180030f0310079908000c2d00410301180c0082e40b180c0540225104d10f200b0300c26581c40d0b510010044581e5007920949000140d04c1e1000014546403a6000d2070f00502c001007600c105a000002003100380c59a90814074051401c90200e03140f484080c0f10312006403008441c298501460100045c3e61790060b4003c070954000811906034081c1e000300100c07030052200b050700b071050740808000a801a6200d02040da150400004800900c8c600b00d01224181c1d20f00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 87011754 1250 87010504 87010529
    0x7051b040b180603211306030b06161a010602030c07090605010203070b0a110403050d140f0702101403070e0f03030405060717070c03060902031011031602010b1906120501080c0108190603051b0604 86
    0x8800c9406030080e55440281d83c61050203040e06024600d195616013b046039070025561042850092480d01907646d014414003860b010062220340e9000c01100e4034243c100240929a440d600b400e500104908680914a02000035000082103030100300201002c0c681d46076100c139421f611088400d030b48034003260845442c1041003000700618046000040702e045910300410400700700001e201c419031080e2200c20200320000c1c4444082d141051440c032000e80140c0207581003a20b0701d4081003003070080a0b00108041d0140e59010070800b1420281c43d00700d0b80005140d82c0e80c03035490800000500d043c0206038040e00903080500c44a8445001d07550040f1011560185183c1e10411000c24030340300e000401e8115507c42100b00744603922507040343c42e01500f0000b400d082e5840c0110245c4880e130071490120a040c140700c01040705000104200340c44210130f09245880382ea400441c1111068026100e034805442d00d000031051040004100c43e11028035003824001030140420810340380618460032580d00c84 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 87013004 1250 87011754 87011767
    0x6021e070b0705010f09030306050f01171501020a080a0f0924050c070506040b0301140907020d030c05040e0907090507020109020607060207020d0807051b040b180603211306030b06 79
    0x140ca40108640b40c0184000108201c00c10348134400c2d64400042600002d440f0f9000303100d945001e4040341c1c0c25500c2420400590903200c01a6460f003c1c2c0101401d5a41ca000000c1d0545a40240010744032143d00844840c0e444041c41005004006141820000107403d40004078442183c81c4505641c01103407549946240b800071012100c552140c01c51843c540038141001445460703040282c400341c84000310300f50322907050000151040c40209a010f125440b03280c240028290080ba40c030711019600d00d004680c4108115042d603030741c40345130b0001071758645401c200248014003003941002d48800403030501890721603900403400c1e56030340c0d040030707500603820803401c0300103241076009101181c406400c5601d070800035240c4541640024105132065007007017082c01c0b008100c0084100400380115002c101e10f01c420000305902d101241401103560680f40d008c10703150380d0100701c110b44000300c04c00ca003031f00f01d01d0300304052b83c00c1e17000b950200c0711414080b2070204032180240513810001d840682190708055 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 87014254 1250 87013004 87013019
    0x809011406180910091a090102030601050d09030201060308030f0f0601090f1e03020303070b010f091503120e0402180a15023406090311030d020304050f062206021e07 73
    0x54900060f500c50032492508006a07802048005070103000a56440303510701c2641307101c000b801058808264410070420031142c3c2c010303040d100c0c40a1019000510401c81d49020f034010071540d000038001c010040100100012081e03c201d116820131520400e0f00c0d1034080047d02d0340301c602e00514011207602ca01c244000110a022590341001d00d41d040c154080c3d0766000b080c207541c001d810a460001ca020f0041c41f131007108007007003c01000e00312400c0004541640480c250720701d0340e0000521020782a00d040d0f80385445404c0781c4201d40300080c011541e401c0004e0421003240b1103555a07501986604078000b80006030008403508816543d0094580c6c2c05d50908011451000500c00082000608240b42d045082c98007590740500401e03102d01e442c080c20760408040c000c805c02c0302c10b4030036444152404a410360200940381101e0b41510b25040b1945d15400050f450301891030071103ca4407081c1601d250301a503001c485004c94800c0d8007a1035280704107940c450719884800411241c01c5e40551000c11190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 87015504 1250 87014254 87014299
    0x151b01110d0e16170f0604020a0302100c020a080102090a1208070308090304030506070201060e01080115060e0114120a0b01020d1b150e0a0203010b010507030e1e09070809011406 78
    0x104145060300c2002c6140a240c80c1450b40ca90030082c01d405441011000c0000108090400201103100801c414031f410f40c0080c40244042c00001d000311455100c01e0355050055000100d016801000e0311801501d500116000f9081030380d05501c500c09081000507100200c5103043c0400e908149080e01d4001c2684040e502017501400d4005d05120030880000480c400388150b50203100c041d400464680e18101c000010000181c00c0600203034503009581c008103442208030000c580050604201d0b0300c41c4900140c1d000640011001d034010f10000d071034941c00750180c074041d100c0c0802004c02c02882e0340321401280c0d02c1050002402c04202524801950741c0c0c404202202000e101324600810f031000c1180700d2055a0020310482c41d2507106c02401e03811031400380254008901c0070301c1d201d4148011074600410480c0c040c000c450148100108107030404c40750034168a008900030700007499500f4528401481040b0031030f0514810b502c2c0901525802c0507460708180038000c010004650100c82e4246083c11 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 87016754 1250 87015504 87015521
    0x2070201020309030a030504090b0f030a060b030102040b0406020606150913090204090f03020105040b0c03070905091305030412060506030102130b09030c0405011518050d0818151b01110d 82
    0x65100c03e1181c1401960300700076a1860b42d205e0740c0c6582d01c40b46400011400d50340018a40742c450550442007030050f4400040d070700c11494021801056178120302c00885c0c0240300303582000103a20f80000300403c40a0300050b0702e60203a00c050300e00c148062111400d80c5010702030f8000d100d511034031007600303544440c64070341019044038001003000030001c0c450f41d40d0050885030749d9000c0340941d44600c204000d2100030a07009610030808500303207185182c1000700a0007103002e402528400d060400101e898140c078040b003120b010381c0c4882240d40d2035071a01d4ac20140c1c0000200304561503401e01d000900642418002e960789000310b024a0301b201420000004d0a98004259054041c4036007410340c480c954540c000c0c135000307142e01ca403c030303055a884042c0245040d5071a600c40350080fa1040080005490b0300314181c1c2c1981e00302240644403d14804095900f11121030361036442080b0500c0b1111204602008081210100760510b5071544800002400d8030307041e41c2e01c4200d0420500c103916110341386030010407a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 87018004 1250 87016754 87016757
    0x6140d0204120f030206071706041a030105010b0301151e050a030f1508100911010c0c03170405010323041b090221100e070c030528030507050f0d02070201 68
    0x1010b48607050010b54098003203042e00c0c54519603800c0300500d60140199038012500d07203000904200c21680921183d0009880d45000b1980c80d001c1c0c00e425504411a54000d8000500a220950351086c0c40c0656402c203010f101010702c903560040041038000c40d02610741e801ca0b840d42c4007610018040596164020341d264000381903d800b8004002e0940d44944804000301c20828103019003840380491070010403a0019030950b00e01600c510100d13484101000d1b50340b5003440d0071045007016140080319040150300041503100d4900200141405000c00740c01a92000c2c4d034100f0045584145008480901c004400d4144072a04007003804a0300c2c0d0520f0403008085546c5e90002c440d85c0d400c102e4100c1c1d0200b642c60b01001c50032010750640480003000d40e500104d040f1040c4018608141281c070301e114024000005200001e030a0ba4109030040040d85c3e41e03280d03801101c1c80044420480800e10380c0d405d4443c080085d1500d00003800d041d0052058801007850341c6c3d00d850801c07101c1c1c44148001e50004c10144e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 87019254 1250 87018004 87018007
    0xd0e060712020a0605130f02090a1407090e0703140609060a080f010203040b0a0c050a08100509090d02070b032716060c05010506030303040312020d0b0a060306030312050106140d02 79
    0x340414001484018105000d40c000c00344458030b810241c04550700a0180c01040154504850100702c807030030500000c42e0100c9007816551909a000c20060a004c1c02c007443e840c024408014000e0b0700070200d40c081f604201b882c1407156640d00001c8040711255952214100001c2d404a68241000a41c0c950b2119015103940002519085154600251401c00105176900081000100058481c450760010b048440c113102c500e48001c3c0c0070b030590107034825210410807a100040c1051003190644402450044c1a6524a0410441c0952114100e81700c0c200544104180010718000e44800c4906c00e03051a0800c141e41e41880d201700200a070244600c14042c420310745075840c3d580d10081c16070300415198980501050319854001d094031070081006100750814420000480d030083c84082000d802caa03401a0b8074140401c6902c0200712100c5482d0704921600b10200c2c180b60558000c2c1d085d03900980f00c0c0c5080405200391102612024028980007482d8004240340590f000d802420720380e40308403000f5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 87020504 1250 87019254 87019267
    0x111008070f140c070501090b0705030304030c0c03021503010510080402010e0607080c0f010209190302090106030209040e01050403030e010b150a03021e070305070b060402131a0403050f0d02060c03090d0e06 90
    0x4074850b4000d43d045824135006200108995030f0800140001415021103960400c413003500d950380c4034000108054280241c0800384000c010100200c02c000d10b5000300543d050810051400000c0c0c4c009005150213502d000d6607030000300c2e000b485642d2255905a490307e0019103804180b28160f04080c0c0304480703e600901c080c1c03100702070603c074091150000c400016151000041000712460f05c10300e251146070b107014020b00150710b80700001415039607242070250f40c80702078070040381c0207040301d4100c0203095203000306204c2010380c16000780101c040c81d28001d10004440904001851030000200c8940320002c000402040d4029000740155405e503003000010540d40c003004240b9540614002c80016000080460402060b28090707a081842518210f0900700182c409140e40880ee01400705143e450001142c00421400d0454010719484400d407101400303c1c0c0107403a5111041c010080144c000d500002c2c02842c044425244070300e104500601c041488420305940781c0340a500f4150300080108900b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 87021754 1250 87020504 87020537
    0xe10060e1021050609012003010f0605070c050904030206040308010504020a05030f040309030b16120c020604140111040b03100503010504020d0303090c03120513050303160803060d0c12111008070f 86
    0xa21701c5080a40c001280c9070350700029400f95030f08032040070003000c80c0c02e2006000400c0e003202e4a0f002e444490601c550744038410706084c80c10b241154403e50380034501c00c0070441015800318515000b184a521403903c1d69032510f0803c4140d00851314203200007881800022022544659010703007042c0207041c00020941c8030b4844020905048452503549021108560b8000b0340c003110f0394506540d44801005030002a00009499000290001e455a0708174049c90060002c294040103880c80e02403020744c0d8940c1e44015151841d041114421510300e964000000c1a04040c0202c520881d4014110401d0b0b0032107a41c260000e1000d860203840030803803200d01200042d180c81a2000c4425551178242d10b80c040800c01e080c601a8642005020b07400074070500300b09100300000002d00680c0405959121b40e0380c0400300b604079051400c041c000c104090301c0060304000c1c46c038502400501035000c5420302d9a4500a20030500f90701020000021383c0800010b0515200b404800c040070f495103080504280e40c1603c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 87023004 1250 87021754 87021763
    0x1d0c040509010e0403110c0907180b0d09060f0905060f190c08041515060c060f0207110a1202060702040506040e060a0605031e030f0a11010e10060e102105 68
    0x320f60310384200040c0000d15400c80d0300440c204030004d0042098129841c0854590b140c05440ca0060201c03201140301c01c0503080131014090451038400b1926051084140e0740079000e440c80aa840d14a0502035094201c1c880c020b00b416650080c0040500791a409002c188015008042e426102d07909803010800c41e90b14010200c81084950b0ba0b03070007904080c1071083c000c04000184065581c03a14030901d82080781d084411040b521542413084402c1500c0c28071202078110240c81a000c03620003c0c80c10304104002c00140060030080c1c4810f1442921216000900380850001035071101040c0702d000014075198000071741c0301c40042c002041d540801944945071000a032407080495458920511441c10f04005402e10400c08492907549120400225602c80c4103420840070080f000040700d0321414015082e082c0501c116a000308041900340c000d180e128001c3e00709240e0a1400c044000680100407245c0700e02030344100010700820740c0b500b084000b09840c62906800120200a41980421030600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 87024254 1250 87023004 87023009
    0x80f03180d0b090d03050a0e06010303050d020c07080a05010606050c03030118020c0109060e12070807060f0605030708011a060301031509061107060f1413060c050702120115060203041d0c04050901 86
    0x20044c0118804564003600b56800280407c0c2003a18080319850101d0300002c4e0181100d8245c185903596419819140001c0d10034941c4042c0a4401c2d080c0000384104002508003000c0e0250000700000c0761554012502c3d44169000006143d006100511181082c01051182c8014a42d030040c6031803d80303101c6500359010f07914141c0e00c0c00c0d55a103500440080038062a00012103107001d0340d140c6002596041c009001d8203e000d4050369540680c6101018654060301c0034000090450341600d51b90000680a0b000c1508182c40c440d544007004403080c10140107890599600481a040c2001c0e990010002042c1c0d507582030750f42035210390024502c180ca510003820514095400480c0c4a8150034500742174611210285900c00840810000c440041a04000c0c0c003940c810408034643c0e014903021a014040c044010b580040600b12100340d0042c1540162101a1100f440c0d003e01a0b407008140e85031b000e03074428409102030168980c0111100d00c20b505922030010001c00b8207198403a8085140c508098 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 87025504 1250 87024254 87024271
    0x3060e010b0102070501030203070c0605180708030304200f040f0f021306030b0d03170c0403080d091101110d030b0d0602040605030103051005043c0b0709080f03180d0b 74
    0x4030603904982d40e0500415000c4e100a00f02945103041003000180100b212200c00b4011603620342c0030940e10005100c4d42d4580000a100329005141c45520f02c0d51240e00513941210351544040e0905000b0107000c00740740c0490030090a1000c482a910241720140260401c55014695075014401010f0038610260000c03143c00d514801c042420980003034100c2d4030130084c1034421804a1100b00010f58007980251080c001c4101103005503c52120540150203035401c0241106404100060a503040d940003907141801021190b0340350307000740019079689407260040c0f550ba400c01c0d0b29081000e80240c00c40318102e40064070b0100d8011a58031200226085900450001a00000108103000007002500d50000c40940b00708940e0410b5502d0903011010000360b4480c802d0900390f12a01d1011105c1c0c540d400c190301e40c44480c03c00f40c5c01e00c3e02d00d5009038126450340210f5400400403450400004900020450401c011403814042028944104a00c1c0c0c448a6200e0036107000000000ea24210144c061070b0759 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 87026754 1250 87025504 87025511
    0x6060806040c020f0604110a18050a050601080f0609150612010806010501050408070315110304050a02010206070c030c2006040906090606050702030309100527040c0f02061501020703060e01 83
    0x100800c015141c2007606401194010220f1311000308001ca5116007040c0c1c08041544804031000c04103414808541c0080b003001700c0f03403025030041d0f1519000b55203d51a009010082c0b6034842c0c0040da1024015115440c4030125100010000d0030071028031760b00f0062210800c14050030310000102e103a803044081d00d5000303201c840100304481003041700e28050102424840e081504003d84241e803814036200c06481000c0703c4a903000864420b9009241c0e9a030403280155880c545818a20345e60103107200120300501c130f10750000c7c65a074071903482501099410307902c0c03200094003504d03030025030044c0303000c540034034841010590644e17542c00c0300400c0200013001d000b269503454035182c1c00885e01d151780204240001000001c0059801108451300c001003111036200d9514144170131146402002c0311902c000031003401c040b041c1c10348401d40c82070209044800707112034404014129401c0040c940820090790082e8040703000c10700030101600d250001032045403031b016629250181510340204100c0e100742d64 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 87028004 1250 87026754 87026761
    0x6130507090f1401090b10030c0e040f150602160308070c0e07020d0908030f22081002040f0506040b04150e0307090525020606270702250510030b0d06060608 69
    0x340b0b0708006004090066040007506e51100110f42c030503081c07003001c400b05503880321245603240c01007060b81441030002c0e104028840709c45071894018059602440c1507900c00b030400140491002132041c0903c12b0300411030172040d285070389160258110440458100581c1e443c0402c04094450503103100700010fa000b03203400c00e18400003600254140c1c00082858008101da99001c1440004565000c1048190304600d04803804201030001102d4010040320f00a8040340a00c0039103940160050341d004c01c144484055a801c01c00005100b50b110b890069441030004101c5500398500c4000610000d04020811034042c200003428401103812003110295104184800d25059041c2115203c2e18046012202d220084002c1d541c0d04004040d80d12441d003490421940b007680300301c49c826501c4051503030902c07400c10107030107521102e4049040c010b80764216000f22485071100d0311502140c0001c0c004a91440c050442100600f11500d00a03400a404031a1040020302038415100100f01d1640c5081440c00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 87029254 1250 87028004 87028031
    0x908030c0910090e0606030424020a02010e0604020f040207080d020f070c06050a02100c09080f031210034b0209090c09060607020109031505090114040506130507090f 73
    0x20058000b0740c0401040000c1402242c6a040e880740d0440b0341200d02e03507100d9880d0301c4d01910391140070008480d041034103126031290700c0564001c1e00382025950000c1c0b200c1d146540c8602c1e52032601f00d801941c0644500c0800809007480d6006100c403901900d01180360208440580d42680d0045030000102e4030001050400e0128a0030b100001c2e050131314040d40741501540000350384409070300b0b003445044d554050044000c2d004d0702060004001e10015105272103940c9441a8413500325801400589440c940000d44107042940c81030f007600e5215500e9840c503000b03522091750142510301c54480c05c61400240200d0300c581d1506c0303203001018003020032610080c544180031100307001400e88007582d4044840c052040c0d07030b5040c08540c03095041d9191501d42c940c3d400102e83d8046203900c09010b41f02e006a45402e90b440542105114005d02130090126203041040d0800c4503808841c091708542000b000309810700105c29041102d02e010320201c40783d40c1c0d01d98070b540d802c86100181074420aa0390f40008001035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 87030504 1250 87029254 87029269
    0x19020c130504030507021011010e0708010506031f0209030a020d0b0615031603091104050103051e0703080d0c170108010b0f0909060403080414060709091a0a090c030908030c09 77
    0x80601030000d100e01c0c20155409040f80c0142e2000a2040f02d9440d2182c5d4414413618141840304031480c0280418226808004d8841c041030160340042d509081c0081c507903060014032016441940002c603c140040c41030508001d401005c001a454040c480450300545c2e81c07003100496840c050b880140d0b60b17080603810488862111034032030a4204040c070402c8100c21820382064510f400d9810089408041441c2c40441d000c1d9441d450355000749420008414001c0010b0702e040c401c0501d010345100700410506082d030f11202c900c80200840d400700800301050741150008205d0303181609100000d0444590103d0300000b098110441a0b075541c81c00e046c65241c42e002c41c0c81903000030f0314840c1250900700302d100e80b26a4000c00140c203111529010804002c0001c2e1840300714020803041c0d803214103144ca0014010003003481010800c0d81041e242c4640140d1b14050034017203041c01410b60f0201850300e80c029010f40707995503800080c591b0b0b541d0071401003209a00158400d03810359400c00e40e14190402004080c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 87031754 1250 87030504 87030529
    0x220b091215071d04051911040902030c030115020f06040f0809031b01030f02190324030609031d0306041707080412021801080a06020702040209060d0902040b030a030816020319020c 79
    0x1c1c03810721040c0103034829000c5403001b0324914602c0104001e4041c1c449100b86108030b61000c0c41003031000040102403c0c0341d0000c0c40c142c0e1902110102e081d05415400ca0b81c440300304080710410381180c0042400600c900c41c070250414481d103407080c200a0140c002030704018070442c458983e041c590b4056070007980e01d445070880481000c03404608040c0ca02e5801e003d003101041c00401895648c00e8aa80410381e2003050b80c4664007820050514141c0b41d140c51405000803507401c0300801c1076482c1c844180c111a8a42c0d8103240e10250081280b07548588440f041a42c54428003480c0c404104060f002040e007040040002e0035000207894606000d6105004018901401d04c001c03030451500140180d0101050030030855421038030160300e032400e9000050003031080d6102598003610015442c003c5140781e0300b060000e540211010840b443c254020b042c0c031800028801000942c00782c0000d5072a00f07d01d51a007110003942c2c81100d040266803100715107600481204a00542d101100f12441850418400e851 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 87033004 1250 87031754 87031759
    0x1b030f0c0f09090203150307140a060302070506042604060c020f12030412030302040e0103060f14060609130207020d08070b091506060705010b060f220b091215071d 72
    0x800c9200014000c050b00d20034003c0e650300b90f4000002c0b139410803e250030315402080050035145015640d00340701802c06000c603000340c003602c088440000d8140c0640b082d154201e4020000d414296159592000c244880c003810380360b1070700200c3c019404031100c44080e1000c0c03c110b403115011500329004200c03066a060350b04c14810202c0403154400c800c004826a01100d9076a01c0207aa80314091506501a01485e00700c2c00b40d042d440c200020a0201a420208910000a0301003050081c1220201400c070b40807a030a5400c140204103a414a040481450a40f41401440141000c456500145200120003025a04940b02080503000d100076108800d40110503040103103c8254100103103081e445e401071074944200e6020a228051120a41001c1a01440103019943d202041e014144084e005203610428503004101e09440701e0001c1c00c42002514629601a810070000504204c0d01301d0f0042500c8040303000380c140010745212035025903800f03090a03131070f00980c0c0c1c40342080d07921103030400400052 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 87034254 1250 87033004 87033017
    0x90a060501120c060807020f01021801120c14070303020c0102070f1403030708070507080705060a0203011a1c0207170705030a0815010f030f061a090306130c05131b030f0c 75
    0x5140d183c000012120780f400d252610359100301050b8101844110240710700e50000910081c040c1c21887c0007034840400f6219900c00f440c4070000d0b0400c6580300c91a5001050144a070315444c0e0b02c54901070301c4420b2092401600c0d0a520842c02400d98200701c5049980c0007440300101c00b0803540ca4000d5a42c2e0030040010760451800120084c148000685810144607000400c2c2c400d0003188012280b9a98024085a000b03042c03203c1140000e5000340300c0e408105c0840c03040c510781070303e03081d08807911550314140d07000d1650701144040b00258020201214443d502e00041c0481111500c050054a40100003450312107180003c003400d5040001d0210700425402e034114105030383c0202041c48188411f280c0020303c03110700ea055074010f11107030b00041c010740b03a02e884601605c0b80b92401004c624000b581607680c10780b41c07621141c0043e2001000100303840700c034090a104e5800c02c2081c418805504403000305028a809500c100e0365a6030030103400029443d8035468220140c0c9028030a11070010340b0300f14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 87035504 1250 87034254 87034289
    0xd090c0608160e040b0301020a09080f15150301090f06060330030c0306050a080f0106092009010c0c1403010b1c140109020616030e010203131418090a060501 69
    0x1484019070000b04a818031185501015583d15107504c220710142003d0300031550ba0b054007030042e0044101d442600440d105107445449140c10106c0e2160415004038111001500d8858440100031402d0580c160113650f10140e41002c2a031080204000034000c079000036040b801c504080d991001d0f5241102300c9400e03810b5500783e00103040d14041c0b0207a041443c00181c1c541003004102c005d050141e00c21030303000704611030200384020b000c58081101c1c1c6200c4020010700b550380f0401e0301901c00100841c000000504100e00141103944014905400705140071012400940c0d111959910340b40c0042e01140e04110000001e41400d12407103101030310032159100200c0501240859002c6020740080c0300240e07883d800c0e00c91100c250406480c103a030003042a61580352141d80e55400245010040c0c002030604d03920a20b0f654004411560109503283c45c2c00b50031402c0085148008094448040d000085284d0b482042280020b0540c0280749017405410205018142042590411303041a01c52405071080d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 87036754 1250 87035504 87035521
    0x10060b0d0504020f04020309010204080c040e06040f08130e01050102010c0806150702040e060f060a060c030e0d03050912100c14091210090312060e07140309030903030d090c0608 78
    0x5642030051481804221503580784040b6040d40707120304409812034004400d1000010b41034014001b80d0b0030005c01c0300d80c81e8020304100000c0e01c0c40b4010002e04d642103003000c1404210009440c1030114020441c1524000303824001d0354841d101c5500c07021851140000501840da820b0207440501005840c00d01954100400020000310229104442a19000400c00115241c9800002c030b4950504181c0e01e807443c0007030080c1005841158000d215203d001804500300e400340c10000c2116070140c1d00c0c900241001d030140441c0c41c011030303825001d201d003d0040c1c00e116900ccc8142d22618680c030001921a0b070b501070401c02e00b95002c4207940800d0240b502c0b80d54015400710025225021801c80e1702c4100d40501c0210a400c00b00d145000d0403509003001110820b058018102c0031480701718030810845190b0300c45c2c00c1c005401d0292288000110704001581400c11a90b01464000168000303030780c03614440d500020304d5070744002880c0c4a2180c0f904a9030b01889104075140d401010941016031091408420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 87038004 1250 87036754 87036757
    0x703031e08190b01020c040603080409060e011d0a020706150f090605060319060308070807050607050a120b01091509150801030c0e0a18051e0c0f040b120109031110060b 74
    0x1d4070215070383d03040440360703038420031081d0031041000d00304019154413410491020782c0b00340078010742c2c0e80c1045000582a103845117150b0483da010030f61710420408400c03100e0b174024005040301d414940c080c4440c2c0c0104c1d05600c180c0700040c1810807440b108174545481c016400e080b035408004000d00d864820041912264102c940c0405d00e90480c1032130002502d0110000e01c90345c3c00c05443c1000200d100c104200c00e0700001c00d0428002c004651403595010300c202d0349403048a40c03002c00186c020501e000300d901a034004d04141401414034000c12616905e03480ea40c4c1460000e41000555450020801c911241280700c0b100480d506c4c0c032504a40c195203848030600101c0c03117180754030044d40c80001c4c4244800e6220311900c0140102c0e40503a00f086040481c0c3e903107456000301207403000352420f000d280307075000a2031803100001920480052186800b044010181116143d40000d007120b4095041e0b54207108021040c0e00c01e0301d4134081115511912480d05d4080014600004d14199060124240610 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 87039254 1250 87038004 87038041
    0x100c0504080a151d0a110a03030507080d06051003090303060518040210030f0f06030302010e0c210a02090403020307030207061b11010302160506060f0f1008070507050703031e08 78
    0x210841034148094981d03802441c9038809008102c69103080340504c0c42c07012079010000d900682001044a01c131341c003000228605480000c003c50380030802c1c0000503425902520741c01d405084000349690780c90300441c408120340d5204100095481d600801050b41501c03c000240c00700742c88404007202d441c03213840b044080283c0702070b00c01c6001280541490f8425080050000b251840030300075201000f40203400b49c181030000710007650030220110114000000c10280a90009003501e040c0c8000082800b07454504c80c0600281d030040000f44401350b10380042d07841c01548240e0041d50380b2540c0b0b090003030030080c0980100f01001001d0201280c07091058030804040754000f07401041c03810250005a000b07215402041c0c8007906180041000c2c04004140144500000e403264180388074090208074600382e12002c0e0560240700110800034061040d100642d11405a00306545090420703103607145405d8250340202c0000d05140350807411000082002c0352143c0c0107050105003400c1102c0c0c48042d100000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 87040504 1250 87039254 87039263
    0x803030c280903120f08010603020f040b030f1e0103050303040b060f130e0610081e0c09090105060f0405070c06090201050f0c0c0f060f03010b0f0d05010602100c0504080a 75
    0x810030300c0000c1c80ca01d00040c080606403041c0110745406500c090301c055954030040c0c0e0f0840e107906440d0307411400303115170010030080c550715910b1036801c1100550003508240000341003158140001f02d80c150013400254001e44003151002864508900042d5018a0341703000c014010300041c004000003140042541e8009910241c0070200b41c0d91a40410085a8080c007110790202070003144c41145000741d440500250702e40020740c0d995603034000d181414440c5500c11400325034031204c0c04024a0b103c800e85844590402026075020b6105240007075100d40040c0c50302030b540e9554809111482c901102c080010610564092040c0d01d480340b409421551321860140500303865129403011684203008031011088442502c545486844490b540d441143c1038044d401000d809006000d98500361040c0ca14120307900702d000b0f1441c0c1c2807807104186c5811265980c18545010703c50054400c1550141d10b029052660081c94641c03440880700303094980030f40c503030070522104002c01d0043c1074010508040e190b400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 87041754 1250 87040504 87040507
    0x50d020d1106190806010906030e0a14151608060a050a03020904050f0610080601080303010e04120207050d060209101d01030e0f0a0606050325062105090c01180803030c 74
    0x18500400c0040c483c01c81e50881900c8440c1008410365004151503006480a80e191162140c903010705908079405020080c0c41c0380d10200c4001d0015480c11145a9110340f00e4094503d1314800440398520900140c80b1040c514140100c0c0c1400c080c3d1111140754000300803a10000c00380d01d00004200b0030030580c0000f1740034180c50400141400f00800101c0c00c16030729842140e1213450010490100715049000c0d0201c9030042d600001921840081940c0c1601c40f0300124240e140c0b21035450205003080404488254000c4440005880e0346004203e50842c0c051200503980380f03210010000589942ea0f008814000e12804440e20005540a4020042402c2c00d00140ca06110003031607141010031a1700b04194440c0c0030701c000030000c054000710211281602101e141d10801c0c8542c044103003088000d0810362460010801800b132107611400440407207032041113042c15900c04040c0a40e80c04031903a0206502603062491507592043c016005084404c014404090030000700a0f00d0384006000c98170035034070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 87043004 1250 87041754 87041783
    0x3020c01020c06040c0f06091401030207031103040e100e04050d1110110a092408040c08030a08010f0501050408120f1c1a01050c06040b070311040905010906050d020d 73
    0x25030494207407148190860f0b005207090302e80110819994060500340303004402000840d940076204420a60391213407000318502c0d81d4500110001c0d084013605404204030143c0b45610b1000030700040001e8456501d030b04000f40782c401004540919194808802c2403249010800072610108502484500e01e25081c0303d030186c0340481314980524181e4080c0b0981c0b820b036020144941d01c3d002040f41c080b040d191880019501d584142164411342c2d801d145001c40d20300740a080502c00c5058a52080c451110781008603180d14080f850342e0404500180030403400e600520140105035140001000d003482c00d5407a050030b09100070303180d072105407640d00c403c03102040380008816840d09a03054084a40301841e9000e0040d030742e030806046109c00c0040419400411410710354414001c42d100c48083c4402081640c545a9411000c078400510000826540d80c100c0300c61009100c3c020001400c22040215a80d4140494242102d400c0d611040c400c07800030010030016111420040d44003504200e039280c0954 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 87044254 1250 87043004 87043027
    0xd0f1704170f0c0f030a09030803130f0f0507080f1b240304110109120209040203010b0405101a03041106181f080a0504050715050c0703081c06060509010302 69
    0x203910102070a03568101068524011400e900a0318101d5034000895844001380d1402c0c60700d911135201e210340040e03000102400411280001140c200e00903124800c1014429100c0b0020b4407280701013201c409400305450014801c1c02c001c4980a00300410181c40520107041416540d00c4040e9034580f03041c4020501c480c0d0303a90320201060340400d002896417a40590002c0080c00c41d520480c0d007107400350840400c4000c41d500c6203d481007501e6240c4600c0a00d02a540c00b0410a4800188220380c15034a82480d03e1180e00c0d1402042c6c012003c1808841d20f1741e04008614804014160b1000164102803041001052412480c004005016211703991799080d02035105508034070700920182c01441e03c070007401d2520341c1465500c1010703d060307641c0d0000b80c0301c420000042e100203840140030383c1d101d04c506020b1802041e800051800041c1845898100100c440702d080c562141d05c02c1d203856101103000c0400c4500d103054440300b96070a101c100001828200c001d0700724095681c1443c109503003c940840540d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 87045504 1250 87044254 87044273
    0x1f02010b03030a111005040201050d050919110102010b0f06040905180102040e0601030e0307020a0312050d050103080405030105060306041703133207180b0303090a0806090d0f1704 79
    0xc0c00035041da540c40054580151846034644482051446403500c0c0007100c11032842031500039941651054030380b10f82090001c0c09820b014151004034061004001c10901542c0c4062040900c00d2200000e24112207001a08480c0d0842d2841d0054040381c405902c1c550320102243c0548452810000c1e50f920b84880107959811007900b03010030b9601c00100032400901550080b44140c10998042c8004114141219140c1c043c1c0d1400a4005204403400c3c000960074003c002440d001501c2c155041c25561520303981618400c0e402070390054170004007800076090a02401d41c1c807480640050440d81801d681e512880400704503046001d48000c000b046c07000ea01000c4400c42c40d0381080c0151400300b056060303000c1c8515001d001288030600300500c41501000400d00000f2518109103420025000c24034400240502400c050750501003001442115a12085420050100030000300780c203152403042645020401d17a10a01400082c1141c02107107944a4064110f00031840c04541b066100c900e1709a148 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 87046754 1250 87045504 87045521
    0x31005031006140d0503030f0a11040e0906072a0f0602120f0609070f050c0a05010203070c0b0603030405130c020c120a06150e011a0705060103060f1a1f0201 69
    0x10701820008041c0610690051000e4841e081c02200400c400d030000c012104118100090550b0800c0c000907401e80001d50005038000ca04490100308816000e00c05195507000750811012901d5243c08d00040140400c10396070300c1082c90801c1400c60000d484200d0f140070803001c180030300d00151205103042050b0000016107490307002000f5503e80540d8a001a415001140c284940341071081c0041d5091500747d051f03500400c030a44419120399881101150183d03c101001c075214402c3d00c0d512170019000b440110300c0f03440a0f0b074032802c0c110b48500e011280100042c0c07080340303e64010b0000b8407456503105e4168026200d440380005090884003001d07418080c0e030803000f40c0e1180c50071050380801c070004941000680d1180c4400c021030340303203a600300d08800b003d03000d80700b40034400c82c1c014800081c10716403041d00329000701400e9080101650301c86213003007000d810840f441510b41192406140c02800703800d003001d0958044180038030301000455041d656410b05240325101044600d100d2600070b40c0490341 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 87048004 1250 87046754 87046759
    0x1b0306050109020a1209110415030c0905060102070902070218070315030302010c0216030f020f0d08030108100c0806012114091e060c07081803030a020c0909010b06070602031005 78
    0x49580d40b4001240250801301000340810820284400516a90f2144030a116400704c0d0282000e4036520901c00101103a84445440d80d10081000c00802d00b101e503c100200301c1c2e14404995891312800090801c1500e600030605640140070030b81c0160384113024404d0b49140d0110140f403660341c40c0011400351040040401503090940804018154190041a00b0580320780844070600c9840c5240d000c060310600c0054034528030518140300500d01030f195804107002c014020180e1100b50303254a08141d2007a8403144180e03002082c0d810482e80d8038003482004000c2d904101140340b902c6000078008901a500804d290301c0400742075600140e1551082d04848950213100406140000300340d49c1c2ca0305045940020180c6001e040743c803e1a00042c924400c002d4242c1280c10aa85039a4059032074207c41d030303460758600388046080700b1503d04001500421025034020b00c2d1020000b82440b11400000d0003031075a69050910104194850070210764441d03071b02190040e81c950b100390302d0030402395281c0c1009a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 87049254 1250 87048004 87048011
    0x602090109210c0b040e0408070624060206160206061203040b04030b0a0e010506030d0311091804060509031e07050c040c0503150603040b0f040609120c0b090303010605071b0306 78
    0xc94060240d1402070594801c0516200050b100c89241361980204e00c542c68811301c900000030001945034014000c3e040c400d0300d01003420210064071600c00c030900b486030075405140040810ae5181e042008a411280c2500f05421a40301c540d0029142c80004054031702620140400ca203543e0002c004070f03401081d20b226a1510b89490707207001c00c43c0b1801616580340450802c08203200c0071006100d0345004403c0100200b103000c026a4041e400341c0201104021685028440c106094807005d00c1440440000000f43c6024030f041e261410803286c02500d440c18651007405000b001040da142040c442c3c82c54000c171181c488405107019840c0a02e142c04880e00142800044007501e80c102019500441c9440710ad0246080200e041c844d0a0204030341c0500206600d2001c2a02c162102e045160028000d020106d080c0e50030b515603244000c202c83c41c49000031035091340c20f0305001e54024659004007101001c2c51440d450008010100d0162060203804281c810702620341516500c280038005580c0400240f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 87050360 1106 87049254 87049289
    0x30b0406090e0309101b080d0f0b01020d053001050319050a17071a0a0e060903030a020a050408070b04060e0f0a1502010b0607050f0c011103070602090109 68
    0x600c003d02040d180001c5845080e0106caa00840a16948a0207182003208813441d454218005a01c3c0011045140e82c0c0030074000c09080d103c0c13801c079840d1810040081084d0645001d62030f004180e11540b08250350038101143e040b5101201510440051000702c00309000c000711009000381c00c6504101c0008001544140f214612038041c28104039180c0c1d2006608000070400010300b029150802c140d5030082c0c014a445000034201500306400c005602940e40c0c0006001499015000308541070702d240f00e0342c01d0303074002d19840c1e0448410b5560303141c04d00e03020340c403a005190018400e2412102d907401c0c200e00000b880d1002800031042c2e03602c2d00c10400e8160061000c04802c55403100403501d8a40c2d25080600f624074010b0f805401140c200107207a61602044181c01d5061142c844221070304e810020003900c1e42103420100259844643e000100d80d05100c82e0030507076a4441c156100c = true := by decide +kernel

theorem cover : BRFrame.Cov 86870504 87050360 := by
  have h0 := BRFrame.cov_init 86870504
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86870504 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 86870504 ≤ n) (h2 : n < 87050360) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
