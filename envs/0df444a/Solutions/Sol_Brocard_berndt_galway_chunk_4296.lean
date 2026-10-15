-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4296
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:09:22.918917+00:00
-- url     : https://prove2.me/submissions/30957c95-f852-4227-b486-b9982ede94f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 772482014 ≤ n < 772661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 772483264 1250 772482014 772482017
    0x4030e03100606020a1430070c06090812090906040504060e070b07150605060a050a0203040b03010e0103061812030c1e02060702190302070e04031205090c0102010c410310170d 77
    0x48540c840d02c8114036008050400011f004c0c54544200c98451001c0c080c080d902c424000361982404024000e810700068a0a0402da5111886c00c001c0704002900c855018050740d1089603113401140030489a6440030031549010b0341980c070341c1903441340c1d02d04168002b10340c1941c1e40315045524203111415441148241d4a00902450500000240840c1c060b0083d144100961004000101d0500030075005540244400c1130503051547c1940380100c182d603104401145500d0005040c0b40014a55420b18602c900d150f00c1c0000f554500e600d000c5814006001400b00407001030016038200c540d0101d042c510400722502210340440e40d840003003100741d62048000e00180c02c241c500b401f812044d180f644d60024005d18013120100c4240302d810049590642d4156925404444000003d58083c0a0000010041c0c00e010010b080c2c4c282d0303060004810048903052004000c04812180c0b808400c1801c0c3c848080403150b80c03645841c0c1c2865400460b14004d95210100701400f22201d1200040e0310a0a040b29 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 772484514 1250 772483264 772483303
    0x13151214010e101a0717070201121512050604110303070c06051605030a0c110a03080906070204140106030501080c042315040c03060513020a050304030e03100606020a14 74
    0xc0c52491981d0034030283c54541c0c185a410000102d0f045540038030b103c0b480030750703102a540f542070746040c0c41080c0c0030109041d003030b00c001e00451000d42c1e046500e0064000c2a0807002c41c2c1c10060407103d504805154006078031080c060360303410b01880000103507140f145106445021921070044101656030282c2d14004002c1042140300f8000d02d44200050030411690b600d101040414a54800341507800c490000400a041801c003042440302c29003420202c1030003920601e00b01400e40d1102030036441104038150207040c0020f0000110345036940140401d510403040391249586403034005000c2c181c280300790141440340c440e84840c0c0b403501e8460380c00c45803000e0181000c10341100c9c3c004440f8107401050541403880201c000491500d982c0210f0014001d0b0ba580020b0380740c10142040742100301c42c88516100e0f481400b01c00d408030b0304102102e401c030360581003901e0030600e080f00003450103111149008007107041000001e0b541e074001490a13262841141c0d002030400001e00e445599000b802c68020440f9135 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 772485764 1250 772484514 772484519
    0x3010515090a031515050105030606040e040f0803010f0306050603120316120c030c1d011b060219081e09060c0d0e0303010f33050f1315121401 63
    0x40041c60340080103090881c280b90380b5264514000b0b0040401c80700ca07a00d55030070b2240039100c189100080c181c2401d0190860411001140380c900075030090040700ca0b03600000c01d09000d440c800c000b540c254805002d0340d1b0f81d80c498a107150104d00702e1000708c0340f541c14000426058580800c4024903d00441046130441d035a8000382d0700e24621100b0010140b2803180e90300d01002045002d9900740805a807404111940f003042c00820801280a00303054600c12288081d1a90707901c0510400d0050200324100600702c442c0c00d1a0009100307245011142e856074032004024150030184d02031040c000340d40d00c1d0b003d400c4600c0c91b141400e507040361186001d030086000149121958009050600b031025000642c55081070021403940e4020b030460803038201484002c0100d6800e45421182d0f25844d13905076405035000f0a82c3e504d07000c10b5440480107024012407100d22040b600ca003951903007924800c2c0a41410f941d4020385504503400035106002032500b001411840c46180215a9604151080c04485a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 772487014 1250 772485764 772485799
    0xc0809010603210c0203010c05030601200303270a0b0a18020a05130b04022107110c010305070c08120403080c1c0b03011d030a180608061e1011070506030105 69
    0xc46414004e00003590003000140e02c091040700e001d8046034643c26660300f003000000d05080341b100c221621040c4031080e189164140072041c0c030303048030401510301c400c0000500f000e0010341420146018520800d6246418010341d00082c60103681010340400401c44068503264024a11082c043d42000030300e101001242003200790606004c8103082c1c0060141c4ca452300040c241d9104410101e218400a100c85c850800c0350004143c002205061101c010700010841d02d85803841c0340300c00c0d414560b851000803038030350190708221a00c1d070f841141c0503a1414490f50100c083d404c2510180c1c00106043c0c0000c2c00704902c502100c01701d2402c1c00d40a4500507140312208041d01c00404195019501d64030036503a0403803da00808940040c1a010b551140e50409004180700350b620880006000d078440100310032600040c900e0703001282520381518580c0d0080d0000052105084455080040c1016437508154800e078a24103100c00c40f0240c540d490354038000c00050780020301038140d000d10748034400528003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 772488264 1250 772487014 772487063
    0x151412010b06070c09050606070f0b100f0611120c0a0204051504020a0903030e0a0e16020f1b19060e13060819150c02120a02070b0c010c0809010603 65
    0x1024104004106004801c010441c40d400c8584121442d1094101c00d0103101c85600407281e1160b800d0b59150309190b55030300d4140c1d000c0890b10340a00060f40c000c010680da0742c8000817460160091209040000d592090010004e01c10072032107403650b005140f800d00c100e413181401c0b540d00034450b0000304480f0045800b040002e02020b00a42c40420307040000082d1b0751154000380492032255200c1050061450801500011000c000d02d40b003412000c1c03092181030200b036601d40d00309042641500c1181c2079240241c0c60140c22824032231507407044810f00640241c04d01048490301c00c099071100c81040700389100b000e031540c1034058217000c14114002f104240c01d111351000c098100015001c40d0950391070000d981012804104402c12038a0212800c0074070084a010900012000100300100310034014025100c010000020040d03000001d200e03d4900d200304218800303803040944041c1c0d280340218103940280b00441f80400465018000181010301c1881404200c9800c0150b0380064041c071203445144 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 772489514 1250 772488264 772488289
    0xf180f0907140408011104050a120209070f0c0624091b0311070f050706030509030903070e06030102090a0f050a060f0c0f171309050c0406021c02010b130f1514 70
    0x1850b082c04005035450090141e107030403051403000d80365128203103824041c00000359004210307000342c003102d181d0058035601d0b0303040d0780918185410400e1203505001140d002c441d421003d02101e003400029043e030500d04520100c03034034642d41c01442041d507840660040c1c41140c01e05045101c505500304030a68069040120a051013114017898910941d89052091241d014143c8080e4418181400601d806101e4241c200351054021414103840500180d40c40c41039001d1f10784881d000314003103145c3c4d071001d40549050060080c0500c0303001703868070303400b5070504501e201d89442415410000507a19018044184000089550305000d1828039140c000d425480c0110840d0140b205135000121105400040c2020f13540c0042107415461421900741c0c00c0e03400c080c064015145040000700f0070240c0000c0d1180540900d074050210303103042c640c02640181040f10450784c21000308801c01c01c0480056010320b11300c100442041010710740d05a0380a08114a0303000d40403180c0580c4481c0341c41c42c0346c10310380da498 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 772490764 1250 772489514 772489547
    0x90201050301031b0f0b090102060a02091f030b03030a0e030d2321090102030402010f021f150306110307081303051b070807090c030e06040206030c0f0403080f180f0907 74
    0x1354942e11500c070400003031140d12000d0700700d00c045041022582d052250b10707004000c015003035003403460050000d403070000000c10001c2c841a001005000f158080e800581a8480c000d080da5181d0a164502070034107216102150312a000f50400006214010560801c40020181210160103400c121010455000fa0260008917045840511440c406040f40503c58246000050780b00c0c1000e10014106000e03040f40c00701550888010460504c1800c410004403c180e42c0f0081800050b4240622841d0341c0c4d030304043e000d0f0b0306205191682c450000003c602421080d1f4850a1a13a591600c8035031616150000400181d8200464103000b81c104001200d20070101060f038203801d50300c5031164907081c001d41c090303c034aa403209807241c079654141c46101d110084410140c601c6150075400280030b4800242440e0380640085450f0b9001c01040c1e060341c020315800389034140d40d200802c0d018402900700030464180081c08184022041c00c1c681c2809607048806040340c0c606484402080d50102d00e013041084 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 772492014 1250 772490764 772490813
    0xf0201110c06010312052a0c0d0816030c0501141e070e0d140d11010c0509211c050304330507140d0608060906070f0e010314040b150409020105030103 66
    0x104080221480e4120246000d01c80401d81d603007d21045040c40c8004110506c130307140588501000c1002d480c03c0b14010000d101c0aa180414549010b950101c4040300c068042c0d860000b03900079aa02000101d40548201c03203540c0c5014081080a51910700200c40660004000034140407140c01d10402d012002c52203011050b1302900360700c0500f4545028203807200d0001e07401301c603000d0310300d0342c280301d0401d0a00180c80c10078500302544011608281d0205411040c40748024400200042c041c00200e014401401c400301c844041c000b0001c000d44c0040e502500e0013130000450003405526001d000440d50001c203000e0005001c407449000040600a24410501002c07281c02021032011900400c1100202c2c40300103816802d203d111454803000404030303405a8846010300291541003120340f80c441c4540d1800f10b07555000d50b00101d02500703402c04010f20a041c440103110030021041101803051035200d5184180341d005200304019036080e0b00d03019020540800c0140701184200c5600704051401c0316422 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 772493264 1250 772492014 772492027
    0x3020705010e06010e090a0506010e090f100606030f050610031d0723031516030212070c0614330d030507140703020a0b0a030e010204060f0201110c0601031205 70
    0x1142074a82885071841c0303d41080380140803080300d8044560f00010880001c4c0000740099944568805043c00744003032a290000c0015000c0788100030380d073313003505640741580c01241c0d4414480303010340700701d0248001080c14000480004c0340c1034452070b0701c03c2c2c1004000c00ca5141800700c0560003070440c207150540201000d22041c914000c10496500202140d140c041c0850000704441c0070140071100500f4840d4214440600c6030208072659030b034000c0000d40c050650380790703920415002031141d00301c00400e40b44514100480a5005540c00b0f54031801260305128620003003c800845480440c0c200c8201c404081801c086213000145c007144030142c2418440f4103c0c0c0030400100d44043c4403204a0001e00005a03c508001700842a42400e015000080c6007207815980080d80264440c010079504c050041b41c0780024500c242c000c840000501402159a1604c5260090490049840190240d800c08c0d40001c0c400300c10320100c0c1ea030454514050012079003560b44407103841410300450b42c200302c01802031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 772494514 1250 772493264 772493273
    0x50406031e24050f0312030c0c0714090901050c0319060515190212030a2403051b06040506090d050a170703080106021f0b13020304151104060c0f0201030207 69
    0x1000c11480c038491400b103122803416110300040c000303a0410b5000b40c40b1044002c801da00c0c000b0707461245260b0510301545136907030300b88a207409004400c80c801042c481c0007400a040381084810b80c2c0c082409035401040c83c2d03101e105090984909503050b070000c01c81080007601d0761006024909504e81e00810100f10940c0e5200010000140e02d40c0c42001400002500b010401019401d45450100e6001030448000e08500000c018000241450182d07a112404a17001c1d84908100d00720b01744c640c00c0b5102401d5100d041440d17544000b0f40901d0188ac1050052420350329103203040c1c1c0c0c110748000f07241500c1d080315841444252102900222110705c2500a0300000440c4181c5041d8402c130800c20301501c80c4102e044c02030130141c06a1142c1d0540d0888000c820510703916030400021151200f00c007049041070800814081010600815003142c030200c1840108241e01503507a190080d450800d2001d028031001da150103109034440c400c0441c000320102c800041d2500e001c910940c0c014100103040c4207842c0c88 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 772495764 1250 772494514 772494521
    0x6030507230c0f072d061706120a05150a060b03130314041d01050607030e040b060d0f050a0c090609090e01150e07020d3207141b10050406031e 63
    0x441a0030b40b80c009900d0b554600302054030800b01030344d40300200501b07240c00409008001d110310b80c80b100601041c00511251201900da0403c1070a000413205c5c0d100881c200f00d070300c0701d40ca10000ea18461032200030414414440c080c000c16168288401807464607003101200610201a4007102482000c4444038864000030b0702500c02410101c112010300a6001035110300854160000c80c41100280810b001281c4d1100341040c00c200b040c3c40000da52070381e0b207001407054007a1070112280700c0e04080c4c0180300c0c40c503107030403040c041d00d40003200703200c0c928501000755aa0f00e214001e540024014580400200c40c09400070a40e520a0600008000000c410422040050381d040b00c8000c20344071082c090f03080ea0400480e40c0f94040c80c0340c004003030f0307410b01e4880400001c58002c030461000311462120403031000008039840c00d9409010103030040007010f006c40d2662807000c0000e0ac800d2504617088051b00301802d550040c0030752580c84601d8203040031015001000158032224841b2094804041801480d10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 772497014 1250 772495764 772495769
    0x503120301061403010b0702010c06200c0c0d0b22020d080703200c010507020301020412050708061f0905130b090f100905030a0c02060705060103030906030507230c0f07 74
    0x1490a5503076050001c050650b0191203810496041c080004101d030092107015240b85983c24070317120442c000c1c68100b0b10082c102c20b400c850703072103240a0403200e4200c1e511001000b08032a44426a1400c004040400c403010340d42c540d01800040f8044000748040b40d881c0c151042410b15130318110000c1c074054000c01e5010303a82d01e03002c03107000c8000550750003031681100e03080814480381070100840d4030404000c0d5443d00c600c0401035050100c0420a18115a0203406076405440f0034240c030032032121141400ca039168614400c015442c0203076004200440301955031038100480301c1090a0f01d26280803003100c0280402401206480361b900c13000c0c400a41c60810040c0143e40f070000401800444044042c1049403c80c4806401071405804c8400100302100351100c2c0101410200c1401d0541d001084030b610910700d0041407030003800008010180c20160713103400e6603081d0790200640e03624403e043d1b400b621040c1d41c000311800f5144502c0d000701c500303400400c2e210409034243c920000c445e000131482d026594 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 772498264 1250 772497014 772497043
    0xb0106020a0b091b060a0201330b07031b0305070b04140616080408030702011506051201050a1d0a020f0412050d0c030912060b09160809010501080c13060503 69
    0x184100360a0040700030030b498009108101500e0f000021070342991540003529401402280f0100f9007041d098000c2d0b021108084965090041d060700030980c0c0159641d0042201095031411180429122180d03025140403690584482140c8031303c030711f50380781e500d18007201c02c41c02c00104000020020303034021500c5000314842d5200e515805402d06002c1c1c200003000780745d4008034000280380c20101d54010502500319412240080d0380352a162000c03805072004102c403154000c004980019003c0e841401420301c0c5190804001d000d07603c0e581000038581441c4078020202c002e00a0400e0302003070582400d504038a0700d2100501d08040348009000c5508694000031040400c81c0407241032000a00c2014000800f510700f0f200c6000d05564041c0ec0041140200c94007a07825881401c04c001c49075004148200e8020264100340c82c2840b4400c0d00c40c0c2881d0820000103110700301040c00303a407050286505907001a03000d072140d1b0301d6500070b10000c92000303586800707419150039000402d61818440c0350200c8119 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 772499514 1250 772498264 772498273
    0x20f1003050a0605120d03021b2b090f09023709081c08040318090e010c02010c09060507030c1a06091012152306100512010b03130b010602 61
    0x282403540110f4601e40d1241740a0503000f588503100390300201d5107130302c1c0702410b00300161118018800341c0a0001c48801070444c42c4100c4080314400364078411004a400000316620014884c003010441c0c0c0702c010392040809003400707030b1018020107840c2d401500d100c0c02d500c151601c2c0154425a0480780109034031450407081c0401060060312584408080060101c1d08002c21041c0c0d0700d00c00030214a68050a4002002503e10114041502c0b43e4002c0440d004ca034665129440d0316000d044004003002c050380a241d6107403850b50b00c490750060190200031106071b113808107e5450224192400e90100c3d5089040145e20501100016185200325944c4601220030303035980d180c00d4041c80244040508040011040381704204007607122100c100301d00903809031340005110400c10303005029001900700b6400040300044420000500d0000552203480d00719030b19284241d5046080d18203215041041e070030494000c1c01400500500c1c00116001a8a128426803000c015107a86240020a03041480160413 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 772500764 1250 772499514 772499521
    0x70c0302160f1401020a08030414120705030d06052e020309060c0604050d08040503040501030c0e0306090c0102101415030a02090106050a08252d021f0c0503070c020f100305 76
    0x1c00b03106003d0112000c0c0001c026004003511000d2181c04010002043c0954552011141c1c00c418000c0d4500d250b05240c0031030f02c0700e5081c0b41058990300500440b80d0fa040c50501c0004640c50a001c40d040b660036241c1d4102150003500d00c0995440310741c5c48401c0c080d440100903084481d01e07801c1c010021581c8200107040c2da8141441e115081074080492802081180d000340400b0070380c040111401c4440c242000280f032004480f003079850b010040c808941c103008040401800040105903800c23902426801c2d1620009500c41c041c1c220b940303042c100d034018134014000810900c40d13042641610078009041b50100e0307425600260651900b600300900050010528070600c0d600180219040002c840520041b51020180b81e10217150b002804003c102150315130103100d02c3c506200e9009001c2850003450309515680010f5507074883c109840b0481c83c10910300620f282d00c64070400074002c40c2a1303240b40c55a187c1100444100b060328905983c40925102200341d2036650071051400040300e9100850540f0303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 772502014 1250 772500764 772500779
    0x50d0803190b0109140d0b010806061206131e020301090302071e1401031d0601080d080f040c050d051f0b040e01060602031e09030303040303051f03050303070c0302160f 74
    0x901d40340c03860811070700306503a07200c59a8011550109850b042a16415403800490000d404800791880103402d03200680c001007010a008908d680c03140310144c07044025041e4409025507600c0301240e80c003500b4000920b10000050449074040b52101c102d04003d02401115000642100c01c0d0010440150b4041601003081a03040c000d591852000c00c41d0300d41d4202d18141289a02c015940c221904065486c1d1843c18500e286564507009451903c08a41c82580c5401016607074080040d8a82c002c0340c406400110340405041c00e80340b0480c1e000340001c07586407410041c0003802a0704982102c29024002c00e41c509074404440c01c100c4002d420038040f40840781c8801303020843c0c002040c45121a41003d00a100d003c0e0000300b10703440508600e4144100c9101c60381d00300900d000d00100664180000000c1c0828035601d1782160707001d14902c1c041d01c400075807000302e055104401da1000401d541c200744005603010b4001c207044e5100303a0080c0161180440c000052210a01c10380d0018050814000c030103000c0311 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 772503264 1250 772502014 772502041
    0xf11031f08060702060a0b061c0b010905090103050a080c0f01051f0501020307120509060c0106090b040605180115110a050601030303110c0a06020a2601080615010522050d0803 77
    0x100280806070502e07040c0f140000303488500c011b000301e2450b511854003401546420040710f51540c0003140f140008514403a13000c000e0640044003d0005103c62008141c030f1415681840c100ca82c08002800500502c4d42d07095619000351900307807090300410000d00038009081c01100e11801c1c6c100509003504500c40d21070010049a5002581154018000c03030000070500b100010b83c50b11641001600c860401d4000341c01c074031402d10039070025400e110002440e00c1458106502c002001c035000e00c40661200d052041d00554917400641c900f903004010003444035804138043c82044a403400c0700c2d19400c0082100e1070465458411100f6900500041040c19410f1040c9200d40d00450035252410460f050400e913580c824035009810a81c0c0010f00081c10f9009180800b412460390314503895800030740298100e280400d05c9244142d006500005040c58070350042c42643c100140c451604010b21400100e2840b81c80c10826200032071441c070f020504c0d9030342956134140c2c0703885910b01503604e1401201c40fa002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 772504514 1250 772503264 772503269
    0x31b03030314070512100504020a1701141e060904090f020f061e2d0406020d0212070f02120f011509050f01051e0405040609020f0f130f11031f 63
    0x440d07a180c018894156030020454200f4000720004c5822606e40300400c1c24000c00c66442150300901c00901c01c4402c070b40144041c8420031602c010100c05030f9852500d0303055440407031030707450340220608c23001794219400590300e40010101031708150914044c08042400c6400c2c420045d2111804111450704624101d075015000142c141c03005801c1480c0c2d41d050042251100000203410034021440441007005032003404400380d0b105425554540c10360300c248066600c40d0103440d006001d0a0b04c1c601c3c11500010b400607114072101006480c0c148103440b0540c0385d039189034040382d209441001c6800d545000700041208142e00c5c03400001c444082e2101c2d040c554003580d004000540c20402009000343d21000c2c00d904488068a00550764412400f070040444c1811202ca0380c41b5103040140414002141d000c1f40c0388510070780d80000700709500002c104a030b02c0c0c242c400c0c1d644598a800c10010000c500c3c0c1251414420702c6ca4049480040b041070f54a840d001122100704e03541c2e060b080452640c4032060900300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 772505764 1250 772504514 772504541
    0x22030522050a050d060b1801030c0902070804060e030a050105070509011b08040311061e0918061f0c0807140d051204020603060a03080a020607020d030b030a1b031b030303 75
    0x155894540070800d200d41900c0f603d07201c1d5a2954151040c89001c0d0401e84221344001c00003403441d0140c1030b04480f44102070001303503200d8007240c074040b90042e9075200f2204510303000004241020300d001000ca035140840304886405014070b040340c400207a024000c1d0390165140382c540380d80700c400ba00001440d1001180440200e0781d085603944c80803600c2c0c0b2040390280ca4001c00c00180344007411303010030801e101c0c85a0540402e0403041c03450840d0a160702c0600071a40c0c0444000c0c034112001000c8216203881602c80641c04200d0070504c03191200c0182d075982d02114241001a4a840d9a03121504e041d00320708d0b400d9a401c42c000c41c1c00c4508050522080610f031041e804d00604000d4000e6101150f4480100003c1c041d5100201003041503075504110b0005503400384ca01c0340c0c4e41c40c034118001d488050581e1a4409480b07800c00d601c80a6009000e0078a500b840540140360001041d100c07596615948001a00e8000c3c40500200210707020b100803011425052082100b85403071440c0003170031a40100c0304801c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 772507014 1250 772505764 772505827
    0xe0c030d0302280309050a060c08070309031b0c15030510120c0303032f090f030d0c0803150411070c120209060402030601020c062712060c03220305 65
    0x50000c0c282980703142c1c1440a000030400b00b40b1021410b500170900325002400700c2c8030381c0c084141009001c4e04001d01e0030350b05a48043c170715210700b44180c00384e9004407002800714446014010b00f9a40c16030202c0d854600404601100550310034032003183c00055080040000d4543e0100003440145031500c0005044501e60603c85c0351003038540c4a100502408000c0c101034817110107a0407034a11408100304540908030880038400c0302d683c0640d003a0300248800780030751102000c11030240360100d404049031001d83c441c00005541a0740d1002c1a03400207022010a00728180c0313007403040d1201c0c82402081c801310303002d00c1d9441c071481c24010807085059000320020703a03010342c45800503210214410342044080d5005038807038565100503424a0307240d0180a4012401140c0c2600c80421010403440381e0140807040c1070750b031410905108250740d0302070b100642c80d800300c0085030454400000540d4805903058030140c825181031465451044820700c02e0340002c9005c5140307454001c81428903646c26400401c2c19 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 772508264 1250 772507014 772507027
    0x60d0c06020f1507020c150c0105070c061508060109020f040e010f0e09070b070611070614060a0506091f020f031306080f0424091e060c0804050c1905040e0c030d0302 73
    0x6d55a5185182d094002c0c4000321004c3e100c40e50040588140e0b00000000717001600e406031000380402d1a00f00240c0f032660030702d850a1040d0308240c14130801d0b21041d0f070103400260b00f0003070310001035802401610a001c03030401c8009102081c880304a40030b041c610f480d03098400e2500c0385903074140c10050510706080d08075110422030b0821040480b0242c1364842c41c080303084103646000413990302812901400417820a03092816500440e9807043c070407882140d07200301d45611a002e002c2140500b1509075005040f18012244118001c000390000e041c01e4411100c101c69608621030460704140140d16140a20070000c1c801e540d003000105502003002c00c0416644e01c0d19460328803403001ca81e05135010b40c1d50240004000041150841d040060300200e642580c41c0680c84e002113941088541501c0341e91410a0580c103062040070300602a0703420400a10003445035008001c0f1255071035030400000c54007040e0010f00c9407034500400000a0b1032402138500c400c540e10a050900840220f020304152040080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 772509514 1250 772508264 772508267
    0x50c01080115211505040f06080a0b06030309060403051b04090b270a0f02030c01170121120c0506010512030703030b1908280b060108060d0c06020f1507 67
    0xb80404002c8601e40703a14115681e03426041d619848205400041c3d042900d4107440a0b08400740c0c0e8200c070410740d0304001204003140c66001300e80b03a5014031030168110b1800301c00856004924650440d0300201601c1c42e181d41c102c0011990782c06580116669003055490b071000704404418040e05a00030755090049132056540c803815420000c0800408941c0d1081a40b402d1102540b591300d0944540102d0303290300041d04020120040743c8800f00d20034483c5201c0080c10713510428480c003141e0752860440c5500e9003082a2030300d40e842001d05807402c0100e02840c07580071562081c00c40d600017440d5100d8100c1c4510703a040260801205820241c004d0108584601014000008031648107405150019006080000040c1140825002607071110350300000407407424004510046524418030590f01d405040b10072010ad9449105c2c0050001104100060104d50044448a0380642c0c01800003509480301d80d1001904c03c025044000141d000e0780704c8007120082041001084c00740281e0808039490075800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 772510764 1250 772509514 772509539
    0x10170604180b070e030609030c06180a1518200f0f04091103120a020708010501060e01050a170a05180c1c0201050c070b120a0219030506061c0603050c010801 69
    0xe0080044411000240da0f503485055030000c00b11008080ea00d03035040480c1c1540d50794000c0d10a000e41802210040380500650b204414901c070307050400346c802c505141d211002d0000a800c1504420303912170600d12081098905050300d043e11a4030003100320005800d403055545000e04000d40038075160400d00740941e990800e55028035030300b00c1c0c0115a405c0140380c0141143d685081c2c1b00e425118644000082d5035070300d005000050407960031665103558038042c90342603c10a2190f1004202010104039065104070000d0a1543c00c40c1440040c450011805001c45101202c00f18210307035840c07050141c41504210441d22080e6145d004000e50302500740003401c01e44110132030b41ea4070f6070f4201403d411a4000c40a9844401400003520744d52517a4880e0030388994440020340d031420b000c440001c0e0760a00c02d403003902c0300f00501803029001900e8000c003e900511b405007074aa40510280316003032941c00290030075643c989280c1c001103807203407840c42c01318508240540c030389041c41165801401841103428 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 772512014 1250 772510764 772510811
    0x1211070203060f0a060f09091a040c0b2a010f0b03010b06030c130b03040305090307060c0b070e01052b0b0109030f12031104060f1107060215041110170604 68
    0x45048904d4461200c00783c0184080e901800e5070b1140320900040400c000d5000000444c0100040300c1e4006903c001c130400241c08030340040040b664403030207010801011020302101e2200c0d040c50f007213508070b04420010109620034402c800da916602d81020301e030390038001c0e021003000c2070700244800d4a038000050014000104854ac1c1d13000301180c05c1c0004504498610010044003000507600d04150500034001e40c172850310b083c046c0c411100000351882c41220303110121504402c2c8041d107a1102d80080346c03410000140c0034100541841010501c141d560810104941c89800c01c1c0c0c003c0c405000d0f21420703500269400703030600ca010720080000c50607003100c0312800c50b0b010304521900d40d081e40d8250010844c02040342107035030000c280410501d40110307040750001525180d40341c2031168541034655038000c83c0107510043e000110003c288441450b80f07590414440d4504001c076680e070101045500303502c0351200c00001c4c040c500d10b14a88005034039445e0402c20566003841b060034100d100e40480410304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 772513264 1250 772512014 772512031
    0x9080a1d0f010c110612040c0806070f050c1c0320090303040b03130b10030b2401031104030605041b060c0f03050703031401060323090706140712121107020306 70
    0x51a83c0000c004c0403e0400e060356200402d425202c007004811070440740c108a4081341c040f007032000e0106001c0400164107105103d240c0c0c440d0042c0354111001c94484e003010640505510031919170b000c10740301c01500424440c5d0503503030020b041d00c0c422005128114440408180700c40c01040104000d840100480b07064690b600c08241da05c0d26482910035031a10f8040f40906644103800c28080e0724800c10780f0310001c60b0b000382d541e110750761542ca03581c4203885070810b4039a254401c0c25503244040c1d4000d0300203c500e4054402c0003410941c2d01e0310768500b9110101c8044540c0c000304d0b00701400091a0002030000b410083c608020598069565404054030790700c4007600f4808041603060815200c0d4106054901681202002959492202402400d002c80100d005c2185030042c24a9a00c00e5020062003031030101c001f08a078030301c2c0003811381d034191042c0e02568000104008103004a030742c00045840381c041e10754030300003080080b401c1007040780d4601340d0003c406041001043d0240e038001543e00c1c0c201003070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 772514514 1250 772513264 772513277
    0x30a1706090a1d06100e07031415010302040536010f14120a120e0103020f0306040b040905070303080f0f04120e031014060a080a0b010603091509080a1d0f01 69
    0x10140403d800c0e03a110000071a00d4803490041003003070300c4a49031240482d03030903150031561a11103000a070240c0302c014100c113142d541a14000340060079480f41800c11603034181001850305444901084080d21240d00f0307450700550210041d12004c0d41500d0040e282101211140c520394100f400841c48242144075214500040002e0507803290b4802001580724a0300108807028036200b1725003800c1b01300796200e020340072401c02c840074407980d4024000c80b2200b0b40140909455680d42d20304220040c0804000c03680c01503651002c02000400420401c0091806915400464034000c1c8407805081002000700a16461031001d1100003041c89085100b20000d609028100c00d010002092601c030440b11502c0000b400c2141d0300080d0003039020003d00514098851100311900c90641c140d881d08c070210002c0407035100340010003080d44203902c03c4040b5880342980703a00c11240400d11070f040e1540d852059591201c009114464a901320080300c103149015807e81c988280c4140020702100068035816040c03040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 772515764 1250 772514514 772514531
    0xf010b0301060210022206030c030e06100302011b1403131a0301210803010f05120c0a0e0a0e07140f01031a010c02030102070b13020112110703030905031b030a1706090a 74
    0x151881e00390400d40800c2c40004019a00e2030001c0240c80b4142d027030404280703040c035080b008010226036548203682c031280001d0940d02c0e5500440704403500f40384111404031516118800100795002d1008109078500c000c649440041c480c1e000300022a0348008032000d0b82c19242d00036100000b064a04445500c10440601750b0fa846260007044800c060003010218004004500c000f500748a54081d104280d903145100d0b400401e81958840040040c16400520440d0800a080442060740e5025071010303004901200d4802040c0d1911b03410740c005071440702e01c0320026512800c06107450311000c4407d00e001d002c0300c00681c40062603081c60503d16410040e00c102c290f025520250103d50615920070010640ca107014405000408084c560072030000e89071042044a1000078050503400104080000b80303080100d503001c3d8010300d072034103084402d80400c1c07116444110b22498080324440b80113000d542d41c0d01c22000d004000080e844c100c00c0c540003002003446a66140e0380704195008901400c00100e581c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 772517014 1250 772515764 772515787
    0x80a14071d04050a021201051503120304060e120d0b10032918040b06030f1b01050304020f0d060504020901050406080a0b09032703100e06041205040f09050f010b030106021002 77
    0x71402c210194002120707044c2c1400300e1b401540507510400e59a8024140d00c504603080607141d4642100703415082c6070034400f19010640303d0380000104126a41140c845202c2d0000347c0e0044e03000703014440d100f01d583c1d0300103034128140030210f946825814a801c02000500315803088640e2142017010303000703415100c1c04032200e071030b03c14a01207444151180b0144910b41450511020641203d0990007070003441111184c2c4400010324102e181c000039004070000c18414011210358200401c185c0e407182040500c080f40c3c1c0c54a15548407580d024020100e86440d140c014441d1406060b031080c1c0c022440c000080150040c04a10317044419480310030740384540c07503c0f0369003440d50044104403005503404081540c2c1c10361400b00f80c5048002c0940030750b010307045043e4028044440c41e00000c2c2668020300d0008000646416040e8080c5255050840c1466100c2100340c1e4168265040368011607603032000c3c483c041c4210080280101074102d5401d00c0c640c1401d20007515640307198444c45400d86c000c40e1840078903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 772518264 1250 772517014 772517023
    0x11070f02040b0406081c020604050604141005160e0105040b040b0325270501090e0403021f0606020c0d030e010819110a0e03010507020316050313080a14071d0405 71
    0x210b00510070b00c40740761035981650715080e241c0660740d850403840021504440c0040740543c4120b4000d4090580e903650798030303000000c0200c0e032115070050080c8548140c6880c030030310907540035803803600d07100110300c0810002402c0056180382036410b004051100704041c4486404480581355034419450303d0b0b0700d9192a0300900b071a00c407100716000800034104441560700c903000c0030940303070b4045d416054801200114451890b030b500640c3d00003030040d801801006140302071076800c40c2c46031040300da600a40c828526280c256010820001540b0f400c0304011141e810420000344c4007089404043e0351440799001b510042620f0040d9042c0160800012100440013440102c14003000c24140491895041c050074164050002440810440c0c808240107060510445118810301d80003186080c50030101084502d070a08800c480d58402000004050181c00100f08000e01d440402005c5496051500d0000e00b4070034000c00c1d030250f119081c10040c07465036000c2d00e0740305d03426602010150f45944c00c0c500c0c1403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 772519514 1250 772518264 772518281
    0x1230406050d060504020901090605060723010606090f09050c0909040c0801020c1f0216380117060c041e0816140a120809010e131e11070f0204 63
    0x101e84400802d05018150700030034841e5108580034506a078907501520211500d5004080e00034005200c00d034005034501c01101c0703900300b0305074001041034000c805003403d4407000c0c1c000e0400141c19142c104000071444518502030308040304140b040303180904000c120360040c1e12010b4450082000800c0601ca40c03194200007400c40c0708029580c071024002403555820f04480c4038200074201103001d8010032518030907202a61420b1903a21680c4030652584c5907182c104500d1040100e00c503101440d40c401001c40000c90580000c000340c00158500030104113950301075151080d4680111042020200d01c0c80c0494007030701c03003601c01030401d00c03042041358031074941c1600b00707502903c1007070098007454544110440480c0e0603481b84118000c610014810740c0480d40c0b085442d21070074030002d0300002e07132010003a11008030185050300c9620313180c0340006c041da502030041e01d50070356941110380f0141515007203080d04400d4443e400d02a190b03040c0008215485a41009812020761102020840d0754075002440c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 772520764 1250 772519514 772519519
    0x803030a052202090f040221100b0613120c0914090f011803050903030d05010e070807020601030201201f150807050d0b0c1204030509180123040605 65
    0x440303240c0480410010002555100d0001c0ba6140d2615102c020b02d40501d03060b00c1e405403449403140c4803017041c04180e45019000f207921000c02404030b60780700f4001500700640070807000180b00071000781e03540108580c1c2e8002c150340034a004004512640c2142d6103103004690440902d90703010082800d081001d41c0d03c5402c282c6460b41020f05820403242908440780c011100442910300c2000d40400107400ca5510020507800c42c40203010100200780500054141e03000040d042d0713440c10a8102e01c4000b00c6000742c00080f025500c503800d1040e00c5a000000f55030051960000303200b02e50454001a1030304c0130b0415110700a0096010701d15145070140041b642c025650400701c040448641e5401c00501280380d20034010914802000503204070009908040720341c081c0c1704036006459911005495030380203000801d076941c1003000140100c080c201c2c42c0d1043c0d00035039400f84c03550b01c504108039441054130b0300342550b801d17100c00601080e209003540c0d42041080c40000b405058012012401800302a840b856 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 772522014 1250 772520764 772520767
    0x303020d06030b1602281505010b1e0313061e091112010b0a03060e150a0207020f0303031608060f09040c060305090303090309061608070f170726040803 67
    0x4015000442074001c444c2800c02c000604004002240c0d0356480d04502e0180614820145984038484110001420701807440040c200b0040c81008003554400c3c0e101040c42900001d0070b0803907100c015028080c1d4882004404d1460070301280030311250b5071101e000340c001643c82000000c4110000781c0b514a11305480c405100005050618054000111344207034000c00f086100389108030303010310030030f030240000400c001082410b545419004081403425070b013046c0701e0151190b83c10440b013950381e440b0307900d101005030341c0b911075206101600080d021031034001c1e0300a00512050740c8034601065103880140c07a00840300e43e2a203000403801508025072940200600041c070081c40a090b1080d030a940c0640c034140629202d90034560740d644000c8414074070341d8000384008030715480c018000b44080900003200840024003601c4e401425072241000b03c0f0382090032504003041014560130115400d08403280c16080601507142c3d2098111141d180760307070030302d1400c1d0108004175140050b980544140c0c000c0384d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 772523264 1250 772522014 772522019
    0x2a0a4d0d08090f01031404050a11010c0203190c1802041503142a0a0e09010806010605220b0a0c0302100b01050f0d060b03040b541606030501090b1c0303020d06 70
    0x9a212000702c1c0098800ad0a809009905540035100348540158060000d0689448540006076894030383c0340c0440700d01c003040310001200e0391a100c0c01196400c140b040107945034a403d40d00300754654003840002c2418100204d00078518001303403c642c0c2c0b020984921400500c140f00c0c000440300d85040002c4030640000c920707000d009030300051080700544240e48480c0180d0b250700032075544080034411140000c1c810007190000b0341e01981e1400e0504003401d401040329403500b07841c0c08150444002440020802e420000605078108900b051036156940100000700d0b210000038903510400428401c080c0740003a541a100d83d540c0e1011000304080580961a410b09150580c50f8010658480c4050000e42000b10384401c4000c40359106001030508a143c0b4111050100c501081914600d642400c1004200d0450303040070301100300301403461809840107a0401c0b402a00301c0d041a000380cae03e980d00d448a8510643c40d45a2400ca0b01e0310305c0221203002018078a0101c010384202418400d8050404900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 772524514 1250 772523264 772523273
    0xd020402130302040501081227040606051911120f0c0601060e1201060509060405040f12030509010e060907140607172a0a4d0d08090f01031404 63
    0x41001d4034400ca50605c42c13030340d884000541e2001c25040608206d0b20030002001e404030442d007a40a0016490034907580907514000040417074001e50711080114038001450780d070301c41c0b1100b14040c104140c9e0a000b0200660b06c0b0215680b144145015520b070840007403130380035014101081e605880307110002c43c3c2d41c5607100c80d0024035130015451585e005507a143d5410f400d40d44103000e25416200003501e600754079666201084054240680151405c1e056950398001041e68601c9492103030758039441c08241e40c01d02c131401c1c42c01c5500120002d05035401040c1800350a00000c41e143d001c8541c3c1400d10130000420a0000b5558031405030000c2100001c1a029050700003000701034100449000c00c1202e103101d612814000100500b001020a0780104000700d002a00c8984e10405110810086040c9138007043c818040180d035183e00b0780000ca0a00c200010740c00089038a00c0b003500b4050341d007815440d1007643d810b4801d00404009030b2040c207100000301f40316403180e0b1026007605542160401c0e1030409090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 772525764 1250 772524514 772524547
    0x120f1003060e0d09050a0308030a050a0b0d1a0114030703060228030e070501170609090c0d230c0a030b07181d06150d0906090812100603110d0504020d020402 69
    0x15143d01082c8411340003d45450001102400ca0343c020b901d40740b9540d111102b91008000080080e40036a51750000c0501d00d4583ca50500c0200c0c0c41414040d081d101448568007519005900c240301d02501120801d0709914007040c807204032a44006c1c00760301e0f442a103109954854211018002050071100040b00c1c140c1c1c16003141e11102c195100fa50503260701c5a004403204841c2010344201561008045400ea0034403070708081c0d1100c0d101c81500e030101300749000600703400040081985e1a0340c8103001c184000c8500031007489041d40900007000f2800320307007003c1181c101c020320001c1e08942041e40050701441c00385040116030802981c180c100240ca4032000e16656074a40c2c5100c0982c50401d001841d14280344c0c0d07100c1c2a26501d0541c2e42d04100c03404010740c000e0200024200c40240c0c880c0c0040d0300044a01c0b001c1c10800000c503004201618151303403c009102c0c000d41c004001c05081c000c3c0c001744030b0b16035001c840e00341c0d100f07250215581e07a07140046100e080c3c80600094000d4400030b00e92000b804c4100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 772527014 1250 772525764 772525783
    0xf12101e060902160212120d06180501050d030c03260a0f0b03211b030408061b0403030e012001050a15030203060a0914070f0317120f1003060e 63
    0x308100721441c0c4a01411040b40900e103032145008a052030f00380094a049050801d00784c400e2822503a088480302d103150281c1e00203680e04200b2076140c40b028001e00e5a0300b4040308042c8241da40401c059072501001514420070b0960140c00d110102c513002017454440d120500709501c54128020036509181c00d01c0145940071074840720360a02d4034030003141e04c4501d4011003403849801401080500c40c20040c01c03038a026054401007800c0b000304081600c00e012502e0081a030341d54000550b450700e18000034581808402003110000740328604208440e6030241058409a80d058580803d0039240f11005940f0598510281d515035841103c0350b0351800070540081d8426000c0c450140001c0c0602c03071601c003250a55000c02949504940001a154403880d4440c0c0007403800b07100e0440c811100e4402c2139040003129040b00301484c101320018018064440c0305a00c49045d204c07600c80c50400d1140380004c00e504003074601c0d48007140b640049014110a2070008004d141c108408109080100304810703a56090138 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 772528264 1250 772527014 772527071
    0x70b03071701051c080f25120207180b040f05102103120c030915091118060108180f1617060112020616120e03010b0f1210 54
    0x70449041c544500300c04038542440c0c44182143e6035440120039000071b0401d103440c08003440100b9026085840c5000100445107004042c28418140082d460411161600940d40041d004101d5034816420700704508149034000103816039002c00017005030010406051166041009020320443d2941030002201c2441042e02180d001c00c1c84a40f55070140d40c01c024002c030303034061249854020b0680190303100b2024ad1500061200043da10318440c80101e1003084e15017036035407031080100100025174070005541216a03e030700841eaa08554a0443c005003261304102070000442c16426898114211160410301501e03068000c1141096550aa030104100310702100440000c0302c2904082d880e421a00b04006032619a08026000d2401100240200d0b0800e60400c801c450300c154504900c00c1080c800d103291490b5010301c802c0108020380700b60b841482640341130803052880d6140b001144481c3c2d0207440d407171500805404030a04111003222982403d500b04444601d81c400040a1550110707800f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 772529514 1250 772528264 772528307
    0x9030819050108190501140108100e0105010311130f050112020103050a0207020a031e0203060708090f0705030c0f010909020a03020a110a02090f06280603060915030305030603070b0307 81
    0xa440000c2500c0d4280300b00840707034000900e20250104042c0c800007145024a0001c160080070640d00c28101d070099000100c117402a56032203032102451b0182d8542c81070884028071655045482d83d04072208481c690b01d00c031b40341c418540c01150786190420300c44140359400c204050742e50ba03e02c01d84002c06c4030104034006440c09001881c80c80300d620a40d4022900039056401c124116590207802170034007000543c5440e604500c0400607074080000078070036240e80d40e818446081c01c4140c01c0c03500910540c0d081894000d09010301554a001504441c0c0c0501250401018010500141c1d847e0304c00f0707006034003e503000043c043d11858054004203103c0b01c940ea1400c0b881c1c5020048a42c45440c0e80c00c00a6111000c200811510340041200175040b0000502c117001520714448605000340c0501c035001003c00f40e0100410406416101300d80081040c500180040e15800c60300c000310b921580002003c0c4200400030075001d032410001c00c0040c000305540507a480c1400d10b005460311000442100f0200c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 772530764 1250 772529514 772529551
    0xf05011d0904060209100206041709060d0507020714030f0a1101140f070201080105010809031911011d070b0406052d04091401120b070e130914060702070b041505040306090308 77
    0xc001900d9209070b40004030102401801c007018160bd6000c1d1924542c40b02c2c0034050f40d080e040241c4551402031609400500301a480d2048020300d150f042d01c801d81c400d42145114805900f00410203180a81d440f88105851b07844060041c1c5000d26691850356440401040c005e9680e0050700041814500036210030310b86a98030401103070000c80c21100001c550f04103000309004801007402d2165552140c0c2450048100041c04640c21140420304100002c052200c1c0d0140602d010301c2140c024241c00f2003030031326160511401802034810101446a0218072880c00080342003085801410300d088014001d81c0da41e661840e54002d041010942c0c401104020000102444074130251000b19901000d003640b183e0f0307141400e90340c4401c180c500c0c0c1c0e0083c01c200380300e104401140c415810100c2c401d01a00c10031305c02c0c00c1c601501e003000080003c4207541c060b00b028040031900100f43d504813130251101c0c1003d51011202101c05020f00e61008101c2c034240070219003055008001140b040018075000280d481 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 772532014 1250 772530764 772530767
    0xe030406120510080d080c04180c0806060a270305150a0c020304210201090503030a02210406081308130605030420010801171c02010b18010f05011d090406020910 71
    0x10f29210b490416440200910b2005028003405503005a0140c0b00130308207550394a03803001e070110701d1082502541e03961040034007540e003000c4416009102900d000d42030004d44000640a402c00e0920105404050b6900401100210070000059a8060290f034280c402540344586100d2050f503d0010850400980300c040b944000251030848100d40240c0c501c42034205001070000d01c0c50741c2c0903070402080316004552900d0400040001224590041001801d082d12a0900e000c041c028516440c201b00003c0000c02d41c40031000c0e0300a00902050101102140f0b000440d41c0704825681c400042c0902001449541107000386100740e000308048009085920302403003840c480000c0041c007080f24503005014100050841c51000b00f1280d0880b200b40103130210700000c400c02c2d2240c0f040141e442d0030848181d4227000301c4601010a03105401c844a50500c4004034504645000f0a4100516044110802002a242e581211402070035181044c1028148800030354042205c050144100c00680c48049 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 772533264 1250 772532014 772532041
    0x1509030a1205131202030a1d03100c05070f0b0114010809100c020102041e061b0f080f0d0519050c0a0203190e031b0301060e01180f0e0304061205 64
    0x34021961400c1d21410394400d004010030015086040a41e42c402e40800010181035400d0042180c580080d81c490f120f01c500141246011040f1000c161030b0b17092301000759200041e101040160141e000f0600501c0c1e00021659400b4194000e00382c00d0110003103105008003400f0a606880c9500e041010040c2020f0040da540f02080e038020155500c08118850003c02640c4400c1065002d8030002d031400c2c4e07491401041004c4150f1540321040c140a1040055941020190184514000000c1c00004a607107a5110000860001038451400001c100c10b44449a2040741c0780020b65050030000d600b042501403a004401002c940a002e1401c3c0110f003006030217009680c0002c410380c0c01940790a04a19100340143c1c050950303c8140610468408a41e030760500030b03c400e840c40d60b064118689030020801d42541c4036540504404985c040040c0404415026a6a6480c0d1485004203820310300c5681d1400a1140d05251702c4940004a0042242c6900210450380844140c0051006d52501e40014094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 772534514 1250 772533264 772533277
    0xf050906071d04060e0a051506040b030c07080d050414070f06051b061303020d2102160204060803090f0405100e040501060503030414010f03052404060504020a02150903 74
    0x1980d11440020301c1062091240d404030b502040400b018020444000c90709031003a58002541c1488200204003481c02d09106290740b00d60481d80c400103221081700400e031640704500031030312194000400901c401803500304860b0115802007800e41c1e6814540780d40002406c043d41d040310b01e030422603c1c60300c0b203950001d102c00599030001c5243e000c0d245403900540c0c141d8401c1d1807600900340c3d00303040c00d454007809014091168070000031803d030154852600070700b002c0001c02204240320030481201f2080b0310b1a0a94042c4020b030740303801aa51800c241852041060710140250702c1420490007081042011026201c6001c05640c0b089103c69a14100801d8800803200300d8045120b0000030042030340c0c0400070325002401074000255241d110300100c1e085038040d400082e85101d40c0b170714518495a10002448a03007600745070820007800e00401070348065900681e010308003108108290190b03034031544010001d10b0020000c540e59410400040d403110f56107400440004030350000510315080c04003c9604 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 772535764 1250 772534514 772534531
    0x20406180e06010e130213060212120f090a0f03020c010e09063601060c20130c110312060a2412140a050406050c0703090308070305090a0b030a0f05 65
    0x10301c0c0c2d840500448201c403807104102c0d03200c41044000c20344207120384010031600303d0b0500c0c030700c04007401d0450103894100300465445a040341006071001400c81c0d1000c0c2d03900042d105c5d10f40c0d01e0307a8440841c16482c01700d0005015005a110a0000040603000220500003840070b8941c0004080141c0411580b4902287c9254200d555402c141e1808041110440100105041d040c91510b455180f10b03035030070800340c20040214804a445030203000c1c0c040b0059200b42814482d02c104660500b002c6154070681800d400500c50315100c200e480300e40644290680c07a49400120fa803964510400e0342c100c00d6060b10018001c0b1006040444e43d0400308003045500310420441c0034401810500c2140d60051318210321060070350301c542d48600b8101c0307040c0107801a003044201260900702400c000d42229000752008074062020000980003e421600703020451350400340705510f5000c541010b5940d4800c081701c087d8002604e9201054208451700070f14010424032600f04180c552a05059040700d0042d60000c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 772537014 1250 772535764 772535789
    0x80411042f04050114031003050601060201053c0a06090f0b04060906030b180309040504080a0801060207080d0507330608030708040b0a03091b030b1324060b0a0302040618 75
    0x40001d90410000c5407c03028500c040042c807a90394640a050207400c1e088880140d4550080c000c030000c21264800d10f0851140c00308500001c0c3d040032030f00030800040060007030710b241d100080607000c20740d100c0300091400d62024800000c000c10301400410241c00031500ca0361400c0700c00700c0c10000c140b140c1400d0308d500040c02c444a40307410390342e040340c00c0441926080701d110400c0000d040d900c032806a20b00a5102c0c280b40e0742c403001105006014210140c202e1030071580042d4042040032000a03240600b80407606116507101c015027068a008440201c4040311060070240d0520100d45c2030241c0f424030011568100f05441e250307800701d0384a10411002900c4d00100b444148150b040f100c0042c440300203a800c002440602c55550010403401c03154205a280e03040310002c00c20f004c080901c1c1a40844140d07040341603800380e50740e80740e1440027034180b070307103104124007110b48a510f5a035003c074018009540340c070394643e0b45032140280654000e0103140002240c080710b40302c03140d00543c3c0801c1916002c80105 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 772538264 1250 772537014 772537037
    0xf090105070c0f09050717042d020901080a030206070512010501030b0d0c0b0912010b0d080a110a121101230c130306091e03080106080411042f040501 66
    0x444054205030300554941c910b9060014504011031403c1c4000c0840e540c0102e86840d0010020700041580108080e07002400e9041000052840c040240000c0e81240840010031b01c0d5402ca00700e26070308600003500803e1090000c20107150000c0c009803228841c0d402c40d6007030380c0c400340100d03007a000c0c9111000507440d080005000c10b40c0240c00c40318940001400313003074540807283c0720400100000c1d0b10401c4841c1c0009508407d034107200c50313240e03141408000240102c810100224811004144000e0050300021031b10741d2115110f8001a4090404a41155520505030034985c0041c40c0c0d0008110105188a0003200e80c582c06004207280310020350307058140c40d0103011069400203001403684034804000c018282c103ca080b11050b03400380d03005070000a50050b00c1d140100d500705c86101100d80c0c2801950017500041c0e8400261415500e071841c1c80091900d40e481c0843c1c0d80c0c520810070542c803900700071164640700a11843c240c26031303180c0030840b0301188403007200c0c403141c0c03055025040c00620b400c40d40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 772539514 1250 772538264 772538267
    0x206040308040f2001020705240d02070f11030d080603060a091e050708011a09150303091519141e0409090c0305070e0f0106030b1206100611030f0901 66
    0x41507110f401006488040702642e44c5205410701300d40c004072005202003240400d1544e042203020090001030710202c1000c1030b10100400d418a070903115141044000031f42c01382495140d019903c3c030b25071080c2c980055140a00e0184500c81c503032800ea0b40213100b0285840d512500c9240450b0250b040500600300e01d880e40710180e005010481025960f00e00d0008920010030340c0040042122405500506401800d01d800b250035500f5000c11505ca0745500000c4448950b940b502d00c03900041d10b104007891305009100400d003540510030f602c0c0d510000920307400d8a1107500b20003c1c080e5081c010845024406000d1080d25803801c04145050403c13010320100840040003101080c50f02d040380c002c43d0416a842c43e00781c040d5032070b00104880c0543e01560030000c220741001800d01130903001c0d9810180e49031a0258100d1910140306c0c0c1402c1540701c03c203526541c1c4402a0748058203449c00c050f0341180c60114072108141040b03101e15800540317010523072aa0f04030040f0070343e810b002c2030781042450403000400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 772540764 1250 772539514 772539527
    0xb04060503061f020f060f09030901050a09031703040b0906040503090d020a0305030304082205010f030513062c0105060d0b061504030606060f0c0b010302190308040807170d02060403 80
    0x1450341c03c0074a0880e1500703c4021040c090320f036a5959401808400034041041e400c2031001b502c00e804038110a020f000c5d6000c00070096032504a02847c015480e240303221401c848409140c1d00242103211a0300d41d00da40340c0c00c510300951141e409845001e0094807681d0700c0c41e50b100300841c3d018007190004e11040c4450706e0800300c40180c0c07600041101c1c0c0d400c3d4a0b070300c506045600030346003201c450000191204000103080070700c600c074a0688100d0003803503241100280101170300d007504008040c6d8850014501180383c0241065283d00110200321401c64003541c4004140044844400000c8609861541c440140250762003031002801c0b480d0500711580ea03480221a018012a0b0321200001030341c54100942c2010f0001940100c00118000b0716040307015001c03241040319802004001509a40481c0502100c2c40c11240d050780c0e002c0c620700041f07880e035404481e640c0008000000000300082d001c50005540010307034082510080802c1c0c3c2060b0792640d988014007030340303016810501c00203021034081c01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 772542014 1250 772540764 772540771
    0x70b0d02071401021201052211190e01110a03140c03120a0516050c031b19030203090f1f120f020a021b010306140913020a03050312060a0b04060503 65
    0x8050305040e61650740281445041c44254426940450501c1704954460303101d40c01001c00351080300840485580c0441854070a024040b00d458841c2e01c00741283c0400307000c845080111009040003550081001060040e0219049001801d0307946011101500829a408800c0d0b02d91a000300c04503500042d0b8400d0b030400c124038140c0d4042030000d900e80c610b1034050140700d56010303e4000786a181400515800c18802c0c1107100420009101e10301da130100001c00c5880c070a4464030120500451940c50b0f5240294500541c004121032402c2e1408064000024106c6280100c4807441010340b0320b000d0213501441d14840e50341041514220105203401143c5401c0e168103d20408141110040d110105aa0002c5000300059004000050b1005c2000c01803038003008003460144001454180030080203c00651502d00c103107404008907000d200d00a0200404c640c0c09084600d80980d60304006032290004941186862642c10000d5000e1070701c12819401c0c0c035454003545060034100082141d0941006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 772543264 1250 772542014 772542037
    0x509010c0609060c051b03030105010e0d06110a0203041a03041211012901120b060a11190302010e1c020a08090612040c060f0305040c27050108160b070302070b 70
    0x2e801c05000f05806003d0003605103869201c0554903110411000c0601e11020f45000307554205000500c4240c0c0c0c002680c0d002c40b5022512528514180c3c104100205400303c0c4d440d400d20b03000500b0707054164002c0007500031104110044020442ca6041d511340a2108640003040d0408500c00d50161600a078500c0a05c0c0b48440000940d410340424140b52a071362981d150201038403103000ac80c1e441c0d80c1c0106040071010201c003043c41500001804a4298080c40c0303840341c103001c06051000b0410800708007002001ca9002a10321241c0c0d0f0900380a4000c003410621804180141040d50a803c0c1d4400e000b01c01400b181c2d0f000701801c0c84035071110441340c2c01c1001030075408242000340a5003084c000d00186c0c000d40c06441044a454030301074000e0954002c580d9030320289401d00b003c0101090620314440100ea5203014401081c7e2111400340160412014007420600c1c50807001003807460f40090b0500d0240c21200451460b140c036074080b40c0d080d0045000090040e4018a0284100007619025000200d003c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 772544514 1250 772543264 772543271
    0x102070e04062a030f05063a05120409050906010605040315091a0f060d0b04020d030c0503031816080c01030f0605030a29270c1f0305010b03070509010c06 68
    0x1d00c0b821880c3c014884000400262100c3c426140022280305042c0c02410417180201411550b04240d85000240140c0b2900e101104a1426401c0710044000d0446588007080d20a0072404506201aa800c01d00603081a6480c4c031000030010400050274605070b071459207036207007004e155981e04103603030140000812400740c48220b024001807462400782455814070b8503070900c1e03150030005c505100c0b200400d810f102d525400c0256001c5486109219000380d01500c94000d41c6555040a681168400200500d180f00000400c0001c040744c02443c80109000d600b40e030304485c03808014030035503541c5024101e81034200c170011103100d6000b81d0000d10210902c60001c00c00d1562040024140310440d0b10599208800060001d12a14007a43d4024500703242e0700d03080154103200f031446100c004503001c040c4100a4180300605c4060003000391040c0e800000f04091464a04100e003100013411548200b80420308010010680f00a04800d907481160195119414038150b00011550300c0700c051000d5448564 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 772545764 1250 772544514 772544561
    0x603011112071809020a0305160e010e030c12030a12140601200d050a020106080d09061d03101a030a020f060f0f0f0c2802040f150e150102070e0406 65
    0x1a0f15122000b04000308005171201c494200240c20369000800d03000450800b0703841000c0b600c2d00300d01c05001042d02032070020520021500400c0c0707002c00003148564040380d0f0500499100c0b00010040929103005d650b0084000d0100005d40255003902d020740003000c10303101c0000e5995118000404040030400c0000c41145040040d030340c1000c16270389081000450000f041241c80c2d4090043c0c000a02c00c0f01c000b040c10800910000340509000c1c0502030800000144001780c1e20301f14034071140060002000c1d00d841081e40700080d40107000980c2d6013060180c8020311000185408105403a660b50080c2441e06013041003010080250710002403c100c20205102c0003510718007000150805a07141c00340c540d5218082c0000c280b6104901e0100612488030300d40481070340209615440c21142d0503100400d0081e410f0751110301821150317030700c8001015011f00000700c0304020b8031264017640e550742d1444a06031000004a0b11106d9038000e486160040348040340000b02254801e581c0c14004028101c5c900c403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 772547014 1250 772545764 772545797
    0xc030702040e062d01090c0c080a0305040326070809030706021b0c060c0705060901050412050c01030e0111070f1406090705130b1309031112070605060301111207 71
    0x21000380b072812140d800442041010480340300ea400341000c8070400d0400000801a0140d1085414050341801940719403560700101d0080c902ea00c0800c1d030001c0300c0c03910b0b08954003005008003001c0f9000e41c000b40b1400c00d07607031a2621001c032003070259440c1841e10300107a8885a0980d01640c001e414079055100411502002c20201d01c0580110495042041ca01c0c9000104083c40c2642c00c00000d4401d0104100d144104003000980c0c8007107036000d40343e40d0307140e031a0000162101d002e030364000d4018545144080d0704102010a2510300844262020045500c03040c0c6500c0c00c9501002035400380300d00810a4401050403400028a024800c0c030480d40ea01c28402c50302e42c103040e01921442140d510540c41401585440142c84a190240d0070b803c000204440000811402513000e500d42c3c40341c0c2e039054481c1854400c102000316078259100b11481d40c21240f0305001c1a902c0a43c096542c180340401042d95840d040c002c10b4459001a59180d04201944003c8100e01c0c1c1c000e080760052202c10211f104060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 772548264 1250 772547014 772547021
    0x1809071b080c070e0606120c09130e0d09140409080412140d05160213060b0307020a0c05030118200d08031905011809050f06011412070501050f0c03070204 68
    0x851065240c262540242c6408620b0500c81341c000110f00c40e05601000903d884510641d4a0520034414940241c6c98513001071320584510300050303801048a4072100e20441194010f020700800e50b1040700c08040045408071500031040c05100c400c0a03000c0c0e007694a41c07400d500400c107214003821050345450341d01c0c00160071a200340103040700d000d8809500251003d41c24000f04601c4001403c01c2c519021342c004002092000c0000001d21903040421030f486000500ea10140141c1000c4100980da802d2280c0d000e5964200c54400315003006035650042003a0030180540b002080782d40c0e8000e81d00b10300b95507441190300b1001501c1c1c4c1491004030f216140941d42c072840703102c015001e2020300340c0d281003030590b9001d140404d0700b00241040c240001003102c0c0a0301c0c1128000c94451490000d1401c886107462404d190030540c448000d07100f1080003045200c8501c01d00c449031300048411005050540400c036403100094481c17140030440c14000d006e039940000e0010709218402c00290ba103444000d5000070202c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 772549514 1250 772548264 772548317
    0xb01020715110d03020c07030f060f0f1a120c010f11010f05100506120f152e090e0109021803010f090b0a0603020f0f180403021005070302180907 64
    0x20300c0042d040e1008031080c48404600025841d0551600d000006510782d250f40314400105910342241582c420b00c034003640058050801000144020035081c100c0038040c2c011654038076074140c01e1401420061404100c0303485000351402c090071103181e14038010b5480c441c02c0d44599045c44060407510400c12000e2040d039030764004c0300000040c1418801210301071030303582d40c0000d40602000c10200c0b55218802d80d80700d6009110825a40150340c640c3e03407a10304400341100e25a00040500345000700d10100c85805062030a01f00c08220103001c3e1250b00300e5007440d09121f00329017150000c005010701103c9800034550300d02c4003441c01c80b07a09603100101c1c0c210b584d41031450071000d64503041c0d007003041007600d08250444000788050040509540004100d26140d01c0020b20411059805404031f03202c100241070099100304d800f198134605811301135118a9030b080414003c03890040080c1600d03000c0c0c82a542c610303128051030f07a91240468103200d030504000d04590184148a04010400700c01c039402d6103403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 772550764 1250 772549514 772549517
    0xb0c03100b0408060a0c051b01020315040603030804030c2301090c06031b0804061805030319090f15060902160b090d08160530090c060301090b01020715 67
    0x1aa440c0c08035286030020101d8000000c0004100010000d0f20b000046650b00201881800141440040801da42a106540c8800c044120109002580640640c06144181c100c002c2c50340240540758100700441d445400001c0200d41c2407004900400d02c1480880400c034800d0145860141071041000803c80b1b48240d0085541c0d1907405100070011030030440f20040c041c5050500001c400d00b10140d04010f03a03000014100021200000c050020540161510801d00d014000402c009400e01c40d80341c0d0300499184541300c0c072410044180da48680305100d8403d40005428600c00300541d01c81b1080c2c82c015111785100703501c9003c00703d401030b828401400b40c1446280c0210400318035260503224400d00800403180d64002100027038425400071401a800124180c1c025448a6020816a4240030360212003a00301102991080500c6515802181c804100800398105544461200355680c145c0009640c010805200401c000085600041409034050068451194032844801c8103086030020400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 772552014 1250 772550764 772550767
    0xa02131a031c050a0207030f0b2d0703020c03070c181d03090f030f0330071e110a1b050109030323070f12020d030b030c1009030b0c 58
    0x50254191488103a8100035009401d20007100205008400c2508000d041400000102468100d00c24000c880255a1204c00644c170340c40c80342494200c2080840d0341002c0e80707410080101c80c041d1030391050150f0901d40d800d120304547c0c80d803208034040e4000410109040c44288035010001d01c0c40c00009024004200c081d90075005188100f40c250f03a4100801d41c881d41501003910300002001c41110325081d03094401c125041d040c0d01c04280707410780c001c28003181c034007004c2030341c40040b403206264034010120f0000c20600c002c0707006075003241d07450143c48400129250701c0d5104400e0000400c100d030b20301d00b582024910030401500d9613050580c00031040b80c00c03004008142000241041001025040a2030f002c1c0103030f415903a02410b04840e4a502d800048508007400c41244403001c2150032680c0c1c4415a600301c101c441c602222090f0b1844140405030258079600078190740b1a202c0c00350762a000400a0501d2a008401c3c8511600803140c1081007182080020010030f640e44d010600640e01111403d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 772553264 1250 772552014 772552031
    0x50913020f01030b0306040f050a05030313030905010905010c030c0c050604090e0613050d1d2709010b061b0709110301080c010203040627080706030204030b0a050402030a0803090a0213 81
    0x641d10116041414989000c0c07030140903860005880d030780298801800500001e0360b007841ca1611000c00700c014a0707440004201b010407007404500511461080d21000042c64840c001501c82610901459002912101020010a1040ca2b40b20480d900440100d9120390f12100440d405074041d8102c6240b00d52600000c8070307040402c0086550040c14411072102c1d56140e643c2e1591950b990800c00020405140350044030744441c46001641000000d10781074040e541c079941640d1040000a504500d0315208001924085040c0244022104002c24252505402030103d07031103403400e0820450709224040d80031903048254803455680c02d145105c807030344a40c50039044910304070020701c225045400910080080c2500524107144200d0324841001480c0d0700c607903065035244400d0340710300b8a41c0304500740010025015070040c8180d03405045d100e002580c0e02088041074503002d03100203405600c089082d00106a5260207550451621801d984440516800007500c0310120310381000c80c60340d1810074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 772554514 1250 772553264 772553269
    0x603020f0d0c15050c07260d020d0530011703121801140a0f06120c120201020a0f0b1603050412140702040e070e09150a090c05091302 59
    0x40210006003103440345040d181c641d907000341c60320b042e12961000c031030555144503034503000d04241c400d003564407012200351a6403191140c0d0f1030400800350314010844111039560203100030460714030014280c0c00401e040200d0180032200c2c0d41c030500030241046d24008550705161102103c154119155884200065040c160159850040d00038804050b03032003004241c01000c055000c4d6036010700c48503000d0700c4006011400d01e01400b0303e2510704001d022400704101d01b03454542d010170360000301c5420400c15070361075204840500040700400341c0740000d00c3c0c034208020303c0c2d501c0d8164200d910600c1030f2007100ba04c9683c2c030182e5074003940f41200e1510100d810080c010010060380c44030030030180781c103000307e05003134070b03100a06060b058442080101454540011803402c1e0211004d00d81d001d48100700b4440c1d0740040f01d0f00e451407070040e0342c3c92004a02c04183c2200d80050100b40e54480314a1003070301a1542e0404030001d103921003084581103003900340003c1c503555408402e0b00c13507000b1303064040708880203104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 772555764 1250 772554514 772554529
    0x150603181903110304031101030b0f0418050708010b0310020c1e01020403030f080c0304260c06150108091b010306031a07090611071418041a0c210402010918060302 72
    0x81044a544c4140001c00205d00103480310b0f00000307028200000c1001900002c00e6101c0030342000c0b280c110303060442c10b481802d10540034031f410031b010701d0503659055122566035003682c0f0f210a600d54503a00c10000850121019401820754100c03003000c589002150071a1052215481a900b00c2c132654046010020704d80c01c45054880703034401b0310b040748562409010382d012602000d000509180c0e403043c40600f0840e01203080c4903518101c0d1403540c0d1110200e002c0c0039942e000031600494914052280c141039035010f01d520b64041c5035104c3c0034012801e00003c0700040c1960840010b410980c59400002c041007c1150100f15401000f04402503860444c10240c00f60105a20182c02c2150307a419000c80002c0c01f180040a07100068011031031011a00c000800c400d02040080c0041c0150341c2c18042002800000c603a02131101451401d140d40e07840580340140e000c0c505000c2d1070342902d001c803895401c503100c0160303038032500c14140350240300d458455103441854401d2aa2810f55a1a1024025850900d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 772557014 1250 772555764 772555787
    0x80403030315050a06050c0c090a150801090b0708070c08040e070215060609010c02030102040f1203020f0f070302120a0605070801080c0a18050c07150b120303150603181903 76
    0xd010b01c0801d00c0d1902180030b00741584140c0c0c04108000c44c40c071110240c107020328031204200404080d03c07030602441000007802410380c07100400d00b54260004902c1d406014503605250803041ca510107548802007500e1402008165504100401c1c2034080001c8a44019101800803107e40800b9441d00c200064070701402c900504105010300801c2100035aa1b140c02c64141301c8080c0380103e0100d80c0f62000c00e0281c040e0740c1145c2c17001000302e0004076040d8039548107442000d01030b60844440d2007002c0e80c043d4803840103680c1c1450b02d402080060001d420480201110140307810112260101140c0b14074003243c0d019126030000402401c0100f02500e002c2040b038507989811120141d44514090f130140c1c001d041c20b0302c41003116450320001420a07070160305403a00244c018401c084902c900741c031270600512565113194403d1201c120a00c12035103002040d83d2060307030001c0310342080c11080c4080150a4100402c00c117440d83d0710030b805400f202c4041c003030ba440140c51040c0480075181c0601c0d0181080c02c581 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 772558264 1250 772557014 772557041
    0x20a05031611250b030103050307121809050c0c03070f063e04050a03050a0605280f0b031014010503010c05041802071e02010801320303090a030804030303 68
    0x5070100c1d003201d00200c1c40022840204264010f80001c480c0b070404046043d0f8845250050f003c0000010310a010008246881c4039102411403c0311052007600c000c48000000f00026040c00400e000301c4443d58006a0016640003d0f103041401e5044007a145520440c4115070724060036071120b0400115024900d1200403680d0380d014900c5081001000c1c0c01c40c15100303154284084502c0c881180d000a00b104d028007406040981c03207a8890070595070355080030a084400038078000002daa14142c600d01c2c0c1c040d644000c0a5511401c0c9203c802d5000340010505414038a5652212880c0607601044101c405500c1c80d440407848200311181c2c1c4c1143e1805031300c41402030b410300c01d80e02c40b82d640c8141118160750300144000203040385407200d040240144c400003850780c036a110903041002c01114000d05554402d071b80d04007150b030b21802c0703202c600030075031070f0481402e02030703503403200883c07003904002c04004d0800381c03c4900301104c0c00300050004c00a54800d0b60100b40002d07060043c1179243c042c1e95501030300b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 772559514 1250 772558264 772558277
    0x190f0507060206091009111203070b06060f0703030504230d0801150c021908070e24011b02120a030809060708011a09120d02300708130801020a050316 66
    0x5804584174101d0500c200d4105030359902440420070b210946546400c80505401d898203440c0080719a65070001c0b030256690b000020001d803480c94032000311003500008852803810410a6502500a03020103001107800251000c10314100c0c41d603c80030241060003100c000c00e800714032041c0145c075071001a0402006e402540400180258110042e14141541a02d9a401401c0450421041401150090f408501502c1d40024002c00304140241c05680389040d9038000c80d15508004800d02c5800001d640818400c1c0c8621ba9200c6200d40356040302400540220054000000c83c07070f041c054910800c0380230900e05802d001801c8820410160b001700c4605161460794103241464850f29100f0b004224161000030712440340e511818410440000c00c00d08441d0340246031217019484042140940e800c1518000f440481c1d0490f20605640c3d0740041010b992500744143ca5115403030f40003d0154007022081000003074150000d10081c904004560f071000d4880c10044100e03c100150b081148040106 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 772560764 1250 772559514 772559521
    0x23030306060909070c14030702040b0108090d0f0507020a0e100e10270f061401050403081801051b060403180e1602010e0a152a0e03190f0507060206 65
    0x95000c2200c0c41d10100f25403000484d030314254200d0ba14001c0c8407009150099000f1a84c2c0d480d1800000b80c12403900c220307003e000704a4440c00440d02e8180440f030f5050142e100d641603850703035030144220f03182e0030a03e490400c1c9800081e4001c650b10507200e80c0a40261804074042000c0d180c00c0c00101c0c0d0140030305c20250005802d0001c1c0e5400700d6409400b410008c0e07110590813109400760307040a03c242e9590b4031028844190050088002803c2d90b102c0d035068000e0010300560191310035003c55066a5002099605102042156080410402c00c4a50520600b001a80141940100c0c0c83d050313001400c00528040c5800d1070000c048807020080d1181c009001c40c1c05000030800d007451258002520b100d4105900262402240580003114a0034840c0c0560340924060000c100000940e02000d81e0062000c00580d44840446128a0030708032940b544031a840080741d88124074501c80048001c04441204114001e030881282c0550300444506050b00c00000c108041400303404010321160014040918 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 772562014 1250 772560764 772560769
    0x9050702031206011209060b010905031f05040f1703070e0f10050a090e0709050913030206040b091002030a02040512011512050f0d020d1803020303070b0403110a23030306 75
    0x104002d03000901145800103049901ca1800c001c046080c0c00d03018041070466003007060040400210040c009024184042014100018401c01b518900140c0740e8560f0700c84010240100800b820481d07c0301102c0040c003000c140365080e110b00c01659580075a95034105400c0251400070000005401003a04001886145d074139441c0c0c1039100d450302c2c00c14a9031184288000c0741c10040c990850240140c0b5030080c480341590010b01311342541c10940b180d08003912208180e14101c00c041500034016885100050001030105031200e030403512030400c48030b03450403514112003030340c0084440c0540c45a0200d802c101a1518565552401c48604000c010301c0d9055841c107100e0060030b01489034401342c2440c1c28000c0010070000c5010b01c50280042c0e81002d46210780007900e90042e01d800c0c01c0046c1c1002d280f81074442c905440342c002c5035030040045242c000f60f5034846135951130040041c0c0900851b500503100550045c4015044903100342012407410052200ca9420341201890b400c1280c1d009104000064 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 772563264 1250 772562014 772562017
    0x61e0909014b02070c0b04150908030f09031f050f0a020307121109060d0506120706020a11061210240203090d05070b0d05090c01030b1f1115010905010905070203 71
    0xa100d80e040c282c8248001c0d9414002e4403480c44001c0220032620700006500a6001c050b0099800c0a040e00240c051103100880306c43e102030107450146d4208200c4d01340c40f1341e2190020100a0300182c2601d1000704c5003558604507102032292030700c1498a9904128a0b82c040c0d071400d55220306000e90442c10343c1440e007002801c0800d55080380c00340d1030369088420126180001680ca15aa00400056403900521103880c054030054480c50b018128100e286203412102180c003100390f690036401004203640039219901e5640843c001140c1101342000311940b02c0d01e444a04a00c02d20003403a2150206207808508084051342d41000c00d0007030380b10003401c000164040101e5039001800c4071400b50300103403400c01038200701040c0d20601d10b110000440400d02c140b00c0e049a48203130701c0c00040e80e00100707940300194261030a00001e02d038044000d006000e0035034528060304c0030f51b008903d0f0680594510101ca6440c000344509000c1000c1038000041008401c94001d0601400c8411811710035420450300180d540e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 772564514 1250 772563264 772563371
    0x10c03180204090c0b0d061415070305070206070f050a1101020d0207030b0a11040e0a0b09060a0302011d0604060309060b0d03020d1d030102030c041d0f061e090901 72
    0x40c1d0303c1e5507951061162030303ca0321004c0c15076036040c55511444415010b00402440c030610b001a04c440e600e217005840c0050f42c0110f44080565001c0c03400c8003541c0d045401360b100c4903049a00190902034000030500050000d00898030810013001108240d05100d50381d075011321099030440d07000402c0740ca06990b0100d164011250b000c1d007141c40a4480400c0340d4080c00440301102102c10b00800e00090040103130b4142030040c80380440800c08480000d05014445408032120f64021460340c01c2080194800c03220007031444041c0120145642503100080d03070562203a40048002900c400c4090180301051107481035402089940400707454040d600a920b504d000300400301030200c0030315005000c1403101003241c90110018002c654a181500c071088850b00103010b80d903090800c500c1100c07004103000303031001d005124403e04ca0b0807585c0c0b01410030420b030610340b010b82d0071030000301030f61800c540700e9050050080c030410001044658040754035040e034401c00d0030000721208240c00c2e0a4024110340c020303643c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 772565764 1250 772564514 772564519
    0x80307151d0309130902100e1504150807030b0306012d0f0b03041b06020a03120c08160509030105040c0905060a030308221b44070b041502010c031802 66
    0x134810000d20300f800081c0a540c0019420840b2a001c030118161700c200c0c1150910001c5803031104500301c052150300c960055004521403006200041200903004a4a0503441900380c81c02007903054462022074240b070403ea02c805101100a601303154140c9500080704600181034a58200441c82c05400300f5540f0a54031070003452410005c049001e2004080d0405500941035071026402031351041c000317550318002c400540025100250401e0303902c01034003030907660480f641c2e83c0c450961158189018a10851304689050100800c0616242d072001e0198502c100d00a91100000350700d880f1134582580e500034940703072144450f00c10910000341c20022082e0405081c210f000d00d099026446080164030307506000d0541804040003219000b50700c50000c003039400f20003047da05800c511021400c998600024841091201c03070118003040c4c0c0030100540d802e2820400c440c4000d646001305030303045e8401c0e04001281e04c2c52030a465035090702401525804401490104040f403013540c0500800e07654038000a2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 772567014 1250 772565764 772565779
    0x605010513090507180312120b0f0f041b09030c060302040e070311070204060305010b0310050702070b18191517010b031308031305210f13080307151d0309 68
    0x14940e510172110080d0400198280941c10307601c034100b920520822110000014a074003170f00031811000f501501e84100342c0a01801c410707894440801c195981e050f4030490700581c0d556001217030072a01100c288a111a181c803290105811400d1107105900307160004024980108010030607001c141000780c0d4000100c4c5030008030101908001c0032944034907000030b50721508000c00402440740c10351054070082021000c4079000c0320200341280c00d55004403070520240e0040c1404010407032101c1c0050010994601c1d0314820882c1d61400a081c00401407898203818040761001c1c00f801e079121103519010441400e1031b599050803000f503040880340c14014040194404004035030480b200c0045840086e901c07184031500e03071420031a546540030340e480c42543d15105104001b000c0c03004590324201c0c540c550004007490b1070300014802140744d104c801038000e860720300701c40003035054000d0001c0e10343c0a2203140e04107030341c00202c06004180c0d05600b1801001480c014046034891a00000b01d0360511000c1d15000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 772568264 1250 772567014 772567021
    0x6010e0c0d020405130f050f04200a0905090a03020f06130f03030207050d11010c21050601090f03030206011401051c05060a120606030203011103070c0605100b0a090906050105130905 80
    0x7001a00455100541001d040d0585440d0a4090740040b10612801a02005103076541c01c640d40381b403c0d0a55000e0079808011050180d10380014400310441034010342903495850f0344088010845e8021111981181c005005007420903505014440d84000c0140c000c0c01c0d141081040d1005d480c8000700002d0400c80b060102c05d04060090301510f185035082800e8903202c0d0968880540b010518511582c400e51078203141444c1c02d80036080348000d0a0041e9080e111350314140d9010707802404007510b42030611500d080c000070840e81145224004c1d50ac00c2d406400154540800345850030b1081142e141441018002c0c41c40d214a4102140010056840049103d48840001c80c45082c090f0300020320780c501314203817203007070000540210045a00c00d800030410114656904c1d02e1602080d41d812000940702003441c0003052a035001341d6000091002000035990f41c83d107070002e141c0d221100400c08a48881420400481c041c880c94008050a092051620301c165184044600144c043c0001c60342c1c0d24400b2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 772569514 1250 772568264 772568287
    0x140a0b0c070614130c15020c0d110d2a151d0a0303020313060806130f060b0a0e100809030a03110408030c06090106060309020616150f1d06010e0c 64
    0x21007000700b4800390704030007402c1014040b00e00c4d8081070000d07900b01000c0740000944c0d000340e030700070700325003280f40d01620960048104000ba1000c1181027a11444014801807032a681c54214050410744070321181c14040340d158120038205c1d10055030000c09266000030400006034420390202c142e1002d0324103217134142c400754401103c04011020043c0c1156503010003204154000009109010204007444199076a5007011220342000301ea5003a000010310100c07000d4240c00340c0001d686c00c0950100030507080c4d256110300c11290001248803000460042500126060100b00c40382410780a140082040c0340801d11a5542d10990307201d0700070503941d004c03203900c045100c20603035020b400702000fa03e64070b20003500d07040d0b901c14080c0c0d0204204d510f4030b207000400c140179101d201745099006d003489041c4040048040061302c046c40069811020000a80000105a102d805804040c42c100000c03d46101e03003011008842509180400c3c0c1c0c00400140321a13682c90700300a9100f0307114580380e581d41c072102e02c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 772570764 1250 772569514 772569521
    0xb0604050a27050112020a0e01240e030a0809190605090d05120c010903090819110105070f0b0a1a090f190f060e0703090c051903051504140a0b0c0706 66
    0x100209160300d0f040004c142900c5691034070138054000c4071094410b98a412000e00d001c10300303101d0f502c90b9070078040310a4a003507018080c81c140c840c002c3c1840200c110740d00005c40d0502162800c11102120001a101028641418140060007403a085d81c0b0b88242003003400383c0b483c860b16240701e10607030780c01e00e100c02041000c11000c0c80600381d0b14001a00c0b034500c5400a80a044110f801301c003c9950020003103610100002c2092640210041b22032070300b082a100d8411072007441002da410040c0401c40380000c910080324100410b88503442540d00e42c80c0040c00b09e011206e0100b5402c0081b4449580c1d400a40c3c0c1e2a9a0607030000102c50071a0307030301e46448060b030740040d0380300300c22007050f0f17041c130320583c0d99821650f02810888200030030082d5107a598600850495400680c01408400350100078813403410042c0320f0494001424a01c220019101e84640d441c0103665081021080515401c11080103c0c06045501c55402000100a0a5442d03916040b1420006080381003003a0040340b581c0034410140c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 772572014 1250 772570764 772570829
    0x40f05130321060801090228030f080f0a020d0201180b04020910081606021b100327110a0501051201060c0302010207081b1e102f0a030b0604050a 64
    0x38040290f290b403024101d002c0d00300d000701640b10301c032001d1004018220f03203008071a8101c09450040c1e26903007169581382c811207a440050320020000d000c400c01d88090407000b84107421854008040140c0d0200000b4203640100b02c01e0310041c20b141d08140002400742e0035494100380d0440d426440c99541c1510522180016400f201c0c6c903200d4003842d04103094280c0b207040140c6145a094034070b02d568280c004ca120454800101d60050309075a50302c2c90061180d8824004241c00849038205400b540c0c503100b803085441d04c425a0007400c6002180c1e00b524210440707800810f0282001418950540030707900402c01d0501c103410a20a54103045030070907100f941100c4640360302c00030440d19a4081600000c59190740096a0030900c00c1c80800180c4402e485418400100014000c0801d445101c1200d4081c0c01c0c0c0304404510a901c0303a240010740c144043d03c82540c0021215451307110300441034014151a00c0c00f01090241600704800d0025803140c10801c1c04cc6e40d01092107545403414040d400c143c8103c80c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 772573264 1250 772572014 772572077
    0x60f0d020307170f04020618030a0b01270504030e4e010902091303090801140f010f0b27040e01050612010624021507050405040f051303 60
    0x4100100c8640004a210411a5220081d4499500c84d200f508144a040d00c0c040c0d40700a09100000c614250307000c10000d0304001505407081000e090355110b0840f40281c002488100400020841d650320358004082682c0b04504240000d0400d0303200079160490b801083d50244080c140032070840c100d07400b115580032524411821084c03207400004042c2103405450256031256130b40b80c4418401c0140141906c15070020120501ca0700d80d400644101303400c00c4070480078840e5401d03001541c91420300c150400310700d040c1c0b100c614030701d8402100c18024205070002442024620814070000c0c1190054582d40e030b001100440d0030191012203408809003400c10b82d5405414002044032014064010900030032043c0c0d4089452000c9405083c283d504031b0040200c0d4003921442c482c80482c0340c10758500e003500c0c140195103400301c001750b4851400b94102c482c0c401003000050200039a003024030030800b2259a00301c0400690500982c0348074003a502e044081e0030450b014408040910380c0e4044400041c850 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 772574514 1250 772573264 772573267
    0x20901060c0311190309082d1f09120c0309030b181608060a0b0f04020d150305070f09020a05090910080f0a0b06030607090603090c09050903120702030a0905060f0d02 73
    0x3c0740d06030b202c032a0f10040210001b030381d1340e0000144284000303025198200303000e1912404041080348080103040241851400d4420440c52035030000700000110301100b900200410940302d1810000705600f41494104200f1950f45400b50100e07034080d01b90030a0741c1d0302a2807003220b40c480c1c20001c811805601f10803503890188494000300b50282d043c482040f1064441543c07040d9442d503a10b00304032240e200965070040a82c0c2c2c1d6060885c54036038010001141000000195104100c1d0201c2580d0855041210030380c1c00282c080c005c142d00716616600600b04500250702c0c2a00c4c00b0b000170310501032818080d0045c0104d40c0881d400481c2c40b1440340181c01d0007401c9489000d01001810b07901d03049034031f0a5400728408004100f6038103010540d50310403035480d01c07529402403400408030002c061290098504902e43d20020405142a014490050010b00015a1104403c0443c07031342c140d0002e056601036601c104240103446800400050132100221340302525801c3d0400503000b280310f80b40030b010070340b0310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 772575764 1250 772574514 772574533
    0x100b0307022406030a020f2e09081603020d140d050a080105100806101413060e0409050606221d0721060203040204090b0106031b0c020901060c0311 65
    0x41c0001c03034142c04440c44468a0318a140350b4094401403400307803600c9406400001c2050094140a407030818002d80c094103078081005981600c03441e07502c0c8400e1004094811340c656003840ca601001a00c042d10602c00a018561080c02c040481d0720140d10000f070044980e100581c0500928003035401e01625070310b00307450404291802c010b1096000c0320340b24022810480c000300301d50030840d10405c1d810300c3e5910340d201d040d2143c80c204458480104020350070014490860103c514111001d0203001d80c02a01211005040c407201501b07030000308402c540118074143c0140c01007400003034950b1f0480000d90340000c0410300580300400140740000340c2d00d07016003018014500080155456204e40130381d642541c4104c1e4460b8130002c0340110b18503005070319106d1041c1c0e46000c02c040f5401960441d01c020000160705400d0347e105002c0180c26030004001ca42d0700c010001244005010260400f0f07041d1405c960f40c013400c1d500103081e002c0103001d50410400104060010036001b07030f00d0991302500341c2c8112800d104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 772577014 1250 772575764 772575767
    0x30309090f0a110f0f2b02070c05040b030d03050601030902060c0615010c03140a0e04090b01090e24040c05030703050616030501050102031e0d0906090210050901080a05100b0307 78
    0x440985040942d5403510f490356104115030010f071046044040c540c0ba150140b01d41d030584280d00306c98010300410000041c03131401e02254545082da04100c0f0700c000758940c00e2a041c06a403681070b1b81d11141c059800d104081e03946541c04244044030b4042e07800c000800340c40b0303000101e0082240c040300940103040016001001040014210301c910a00c0c0068560300c1480b030011240c0315200d00c2c00401042b130240c101031509000700c01030002e05946141c005805c110000000d41515141d03c010743d84904000010f1086030703d01c1c001c0540c152902001050b100003c1c030741010003581090075030309041100d60041000c1001d503040d844001c01c2c00170101c0e03031303d2a1203081242d1a4202510306200c2c00c400640d8950002d4083c2c00b5040c100d0303005030043d5043c9146540c0418000c0c0003e1028002160104074800005216201e2000c0c094010000000c04100c1c07031050102d070102018821044c00b40500040348542ea10006492f8001442c841c045115200da0508283c90304613504004d030020008001c01400300d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 772578264 1250 772577014 772577041
    0x706142a0705130b030d0c0c120305070b0403110105010b09031504060f0608060106020d0e1f02011e021b01090209060105071506090207031e09060309050c0909010e0610050d02090603030909 83
    0x2ca01141542e621b0780c1d00f0001607801822074040280303020ba107900e0812100e01d50100007216103005e03050807843c0000340e54806030707142c0c81182c1c120701003000c0da10030b01d022100900c2400e000d0038002000510304100700d8002650703002a1404040400c401000040401a164001c0c081d0000c2003001408803e8443c031078141c558809000e120018450010102c81d9a48500041040160060480315400064000c0703082405005031058041d90b4036580c4204000118201214031300760b16200045c1c82d40c11050f040b010000d2007040090060381080350ba000580e6031000c010741c0144003402c2c0180d0b107140d2450f10b140341101003000802141d2500c80001405680c0707800030001d261085d51845440c100f00c0d4104e02d260480380c4818400956100014412a800b9622001d142030099084031034003513a88000136180d001c00c64940b00c03e039446412601500c00f0030041c998000c400401ca801c1c0203403c010114040d0058182c010b4880c040b4000030600644017801241c01d8014007a080000c1c5144c0604842c405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 772579514 1250 772578264 772578281
    0x30f0f16050c150f040e250807121a09090a0b10030b0c03040b01051c1b091d0a020d030e04020a17010909050316050c060304050706142a070513 63
    0x514983d14426480b640c1080032a00b04902002ca400d04250900d81407590880004065814000071f041802402c80c400655508200c07031581d40d410a64948a20020800030740d0709038010b101410712201940040030455042492103003a21074010582ea040d4400d031800c0e01d4142d020f464001e0160a0028611610fa5041c083d00e00509440000e41c8907074051440700e120840b0090480c154a074014082d170310f031184041c481401201080c4410068503160303070601a01d40b02e4008000c1080010400445016004461032107450f5454070180e0200c82c0b1070551140e0b1100c0000388070707180d1481c082c010103007d030407c5001124058001c548034544800c020300a05c5610f010303260240a0b03d8000181f48525004a200295101c006541012102e8400c403040f80ba41c403038129000c2c0209103180300c00b601c2d4400a1445580a580140340c2d5038038180016020102e6400c840107140750402000340b104002403910500740d200e0303e0000001c3da41600c1028107100158000c947c0c041403000c0c03010342c190503d030400c000703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 772580764 1250 772579514 772579519
    0x120406020a032007260d0209030c0301061208090105040f080303040219060f2f16090504020a05010f020106090f0b181005120a08030f0403080603060108030f0f16050c 73
    0xd808051000031040d00382103d000d42000000300b060350f001408600b02d0718007800d0300307856514000f03142030000a144e4002c1103071012034a0b4042031690242c0780401502c82c40c1e030f40a900800440d0b043c18521104003007150300103000c9420028081c1c0190f440789080394020701505c80f108080765292601e998803944161010f900c900c1c0c0c41c3c4810303c6128148a0036004444d001e445e080c0100209140035150340b20005440d09504400e0340340175250080001d15004800c000700d004d080c58884640f1500755140203500b05c0070806152500300030040c1c41d06100036040d5007090810781400d01c500310b0101e014101c250000030041f42010303025450f40009030840802800c0032228039060700c0d880495010040411508100800103041c41048541003c243d8214240300d1082616610141615160aa50320a8070040001e00c00c00041005159114600d0fa400c0003049019100d903500d0000e410380e40b80150740101000910000794007801c03140c520216034980a0392116080c2900c87c5003003261325074401c0d00f2108e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 772582014 1250 772580764 772580771
    0xf050c0c3a0e120f060112020a030203100501050a0b07050606060d0207050d050307030c031a061b0106030c030b060105031b090415120303060f1d060402090607050c0a12050a0f030203120406020a03 86
    0x220710090201c1d44d25003080380c040c01403000343c1c03a02d250016051043c16042e80c1114400700c0200240c0c8062100301c060001060001c941545000b05000c0d0040e2581e10000300303903006025641c001000814040c1d0085022034003240c403000400d824100034402e040000b04148541010580540c0d00900650321440b01500e040121000c0e404003501903843c03054805028403a0081803660074a4000b015000c50b0842903401032880b508942094211201c82e00196480c0040a2042041004a05c01c583d485031007842c00c3c0303080d070400c0c503910300c4005054180101001804030310a1300984072507001071500c003481035981d007000765210341101a10350012025800030381042004150500e031662074404440010400c0c01d404c0720005420750405c3c0b0050b01d003950050302044411391650b917106c080e080050091004d030555210500420020301c106501c202d5890b2080d4548602081d0046411070110381c009880101455062404908500c559150045030017001070921080c000c0c16130180c10010220386041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 772583264 1250 772582014 772582039
    0x711041802011202130b0310080714030706050732011103100602150c131802091003110d0b0d0b090604030809070b07030f030b130f050c0c3a0e 63
    0x300140d00c2817004807501154640380810207034a005000b184d001d19031825210000740c0b2071082900f00101070744640c0303510080360343d000718610b400d0001c20000c00480c14040c0ca01000d59862480c909070408401c54070070744c504071b0400050030307503c0c40b03034108138519000700522621448404540e41058641000c00040c801d40800c0141c0000b0b000c802082a0100d1f0f07610070381d07400340e0b080c2840d03000000d200c80341d41d0000da0008480343c280340b034400a10694417000d82c1380c20459041c04960300c804011001014181148001036484a40846001110164000c030740c0781403180c04511101a0705100625030201402007050010010440a000300c2c801c2d9108003041d11800b0849640754214003036401d4561041201c000000e00135682d00ca401a0b03a410081030200b10140000c04200303501d5401c5111944961031940e5000345407003103d91146091000d1070030000121340c1a541c83c00c001c000e1b400c0e8100880c904918140d610042c00c9402140080c0310b01005040d0000142025003100b042c0e401614400c804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 772584514 1250 772583264 772583297
    0xb120d170907062a0b15030d0215060f0a0b03130c0602030f18042a320a05070b0408041a07020f15040b0723030c0601050105071104180201 61
    0x14000720f42d0035907509101d402c0c0720032040f4070a8000d60700350b241e0200d886201500180303105003001c1c1300c0c80f03a0311801284000350b8800e250074125042d400b10210342107403400c00b000d0b4645103092504044152000ca009118450100c0c0002040b9049111802408000c0085900036050596182803280c440702540540e0781c8401e076601c2c020f05040012a0030180700450bc40201002c0c102c0034114000d00215000c2208034551001c0c01d4110444403040340944465141190030440c0810a0b0192700107081031010280300f00700600b0448005598064000204c500c1c18911902c10340c2e80842d00030a1440701270800e0315009aa1b40d01c10b01c15508528021418640c00058100540c1c980ca0740140c01200020103e200300820300c032000101d500d200d00c0910000c1082c3c1c4012000c0d02c600c40c4280d2442401c002c0010510520b041c00c941c4012007a481000303210404140410f080e811940282031054a44442d40b0b041004084440000c1c0c1e0400e241c56420007650042e03040c100c4a0702c3c000c0c3c03201c0f400901f02c0b405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 772585764 1250 772584514 772584523
    0x1d0d060e0c040e0a0b15040b090a09020328060c11190314091c140a032003090d120e04110306010905061623060709030b25030b120d1709 60
    0x801412100c0c84c000001c0444454003c80d9a031b074240203000082500039403001844400055a801400d01d0342d645468045090801400d1015281c0606c0100d0150f0038983c2c0841ca4a40c1ca0402410f007610741074070481060007290500000c2c134401c004d89031154450740d81400100441c90b01940001c01c1c480f011801408000e048480e1804007a25030502002c6000740c00441d80c594100440d510482d00740c01c40340d003002c14052115050303c80c0c0d80d491210306202424138009a00040880410b400810020b0443e5070303511240c840309680000a603000b0540c01c3e070142c070341c00d0100103100c0e00142042d600c00d1102542c5401140b003180240c840a1075540c81d90203102003030040200302121a54460750100c00325203c1201c841d0707031490101c5207048040c08802d04908111081e1400c401141e1800300034000c10020703070459a072003048955010103528010000f02b01001c42c001b608030034580c0d40c080d0b854450f140d1020014190b0a41c80490340160302802004003941c0c5401c155102c80c5d02c0010108075148c3d030209 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 772587014 1250 772585764 772585783
    0x14070b040509040f03020703061a09090c0127030813150f0906180506040b0702120c01020c0d050c09090c011407050d0509130c09060f050304031d0d060e0c040e 70
    0x4107490000d03507595444088161340e480041c0c00f5031107018000000640b49000340146c4002034080d44948181c03403400d1020019001d0407040071038004030004443c0d6640008082841e0201c0c242172280458254004502c1e01040d800c0035003001000100303241e050000c2d46001084850025040060b07103100c42048803011503081c001c4001070713809034041146c42d12a100c3c0c15a07003201c1c080380200841e0b882c40014075907403013075010907062100486c0c04001e602d4005035004000b400c0d07001030107c1420307181c0001c1d02d500c1b00030004c40c814448800c1210a100040008d640003031006491190b0714101113500319551800190200c3c0020105c0076000070045c6d9001c00d0300c500541c00002068600071006003690320b900f0000b5041d070407001001810722201c5050040400544650300d40b840c8070350500d2401069500c45a40450910804005000020b640211519510003e01a45104500c401c800240385001051405004c4038180480c0d2060a070703000c036154400c1103080700d081084a0800110907182c81610 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 772588264 1250 772587014 772587019
    0x609030e0409030e060d061e0e010608010b1911101d030a080121020d08030a0b0a05030a02010e011404030302061501031112040f02040c0c0b06060c0703060e011814070b0405 76
    0x107800d0603a040001c003421b02d40d40341d1500414501e85031151444481c0844400121000c1d00350820001401800e206a000d4402468080c6035981000c0440060b8841c1c81c480b4400c000b441e55507581500d00c107840003681100e030841a60b40e05145202480c0141403580391125a401c0b80d1440c403101c1070700c000100e0382207226585a115007680b030101e6203850f11241c1c02000e044200713040c0c1d0100042e42c808030040030440c03281e04038903200d0900946620899500c040300034000c3d8944082480742ea500090003031003555091030400e044030500401258565440c014686860348003040106c205500031640d1417060000041e49136440e159040110300b03580d9030f01c20710030201c4010020740c00e40561010a40d41d0090044100c2c4e41c1e181016804035040301c00544200001500380c400520421078440328840e003200048803400d0914003540207071602c074065407000810003503850b40c0c907805020081d08480d549801550011010300100d060941d0301c00e2095900b6403140c0114140404c030588280151070139034201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 772589514 1250 772588264 772588277
    0x105040b0d140a020d050610060c020616051516030e060c030f1b040e060906040b09070c110a06051c02041202010e030313150905090912070215070609030e040903 71
    0x10390316044070020204042c04490702806250201585420301e03601c00240c452001000d513031501c0c102001208403940c000c50704002007010700364007607601c41080d1100b40c500a06103140107203c52920b45d1901e4102d00c08003064a164070200455165000e00c1004a50b50b952418400e5050013010382c1c0e124079085a0094481c0c60500205003080544056039078440c1d28040701040342040e40424250381c1d080b03988080881030b0403808100d400c0c2030658003a600074105544c03e02c803151034400041c0c401e000080c4540204080c01e11240300344402076148540c1140f000d000805040d8a40a0040c0f0b1070307200100c114400c003000900052440e580340f084604899040d000092190819801100d1078440a01e00f40d03071520060040e00c888003010480c580050014001300c0c41c81c46c0082c840070341060b5460713228601c506245e10401540c0e00006c203403503424000325a0410f80d01c1044d8800980c03421414801c4a00d074210108140c010821558000c8000a0283c0c45403401c5481300d1003007206039001d40d500200004c90 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 772590764 1250 772589514 772589539
    0xa020c0a140c2e050c150106093203070911090307050a03050705040b0f0907020105012103020309061e0f0307090b0306031009050c0301151e0b03150604050411070501050105040b 78
    0x9144592003c0454a441c1883ca4401d02160b001d280250341040d032a07540d40000300410880c0e0300100074070010405041a4219203104e101030640c003202d0015400030001c400c1000600d01d541c04c1c8282005002140300804c800e2040c580900925041600418040e2107540c42c041058900709015804a90340b18004061031410182480060036041c801c1135000444d85240e003400380d0b69111050b104601039400000e95600d060b440d280021246008072521001d0115220007095000c412100f2000040d40d0a50751f501945903403114180c08051b121072101c1b0080b90005285045000450254040d030f03699614054075104144043d20040c4c451581c10760003080c00c41049481a000703240898083d42c1911080f06282012038250b580070346138a0403074981042c05000a40780c002e0300d0b07000c42c5078404503251000d0500c005c503251440302070810180d2450b29564a0078175501d00080320701402010b04248030342d1519031800d44164004e0300b0b003110035508090000c9254101480fa81c00040c0000300300b1041e120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 772592014 1250 772590764 772590829
    0x11e03020c0a0c030f0314090112150f0b0d0605010207060504030b040c171e03040e0f1b0f0c190b0604152310140708030a020c0a140c 59
    0x500101c08801140288000c420103c0e140d101864010350080d803c041c4804264900100b5080052404d0001c0308001e0003855596603004010f10350707018513074000044564100000f184401060f80c003480100304103d002140628402d006015200d40080080c03201a0312031005a1320b0740c0c0d10b4011940000c10510041000c81c1d00d24007926080741c0145800b42c11140c8403011510000d1450149a907150300c00e03c00000b09164000c107224144641e00c02950509091004030440044060481e0750240a00c1c0c003c107003200c86803800c084800001c201c5203070340c1d4000d90030680802e0300704240c00c20f818041c00407903416044600d8910b4110a030720a010581950310a002c01004040805006410f031549400c0450790301c540c410003d2540c0b850008900d82104600c04001c0c1c00c01780080300a04010440703940b40804410300c02901d4940d6030024409460b6690f500c0070000034041c580380006540b00382118002485803098080100c0c0005100303507411044588140002c82440e8080c125110500080d588002c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 772593264 1250 772592014 772592017
    0x21306020606090c16170a020c0406050f0f0112020a0e090702032a01150305030403020a0b04120602030a020903061017210924030a0f061203080403020111040e040b06011e0302 77
    0x101c0101c007856080011506ca0303050311001403441d80080340c00022007645640c0c0400002c50411800c07203044c003490b810710010900b40c0b80b0240103d4003e920402d1584c0f000d030b01820b20000c078507005440854a0302c1c0702c0d00e002003401c1c0120480c1801000307901c002c100b140b8408022502e2040c081c103400101d01c400751908040801851480884656031410001d05a041c40c100d5400158000c9001795103450640c01045141e8129034044400c8071400c20040007200300300700130003a00301e410140c016202d0b500c4900c4240688240304645a0500a05007000440d00d0300803800c405460002c0e510841030a9400c8049980e400f5920800e60003183e000790f080f101c2e51041004040c038030006480c2d202c2d40541d116258280d00410345a40c500d0031408030400110000d40d03c240200035000b00750512003141340c600424102c9004140c0541080510000501858001d410081c0400c407a5a241941c1d5a61540d80381103030041514104d48030400c0802042e03c40d0710461000070746403050807482070f8080f103060301035000303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 772594514 1250 772593264 772593277
    0x9030a1e032a12020717060a0b0a06020619020906031936020a03080c0607030c02060f04020402090f0901080c03100c02060f1503010c0c02030105070c08030604151701021306020606090c 81
    0x131403081d0400842e03e424014040c0d03c422400078000d25060500103807240c203440e41c02d100c050160101c01c4081041395400035815401070591403100307000c19610382000d0302034800c10103041c0d00f0140003c24440e08d01e9480090038004400c40078208101400310125070525041c5032068641d0315a4072817001d080c007035100304402607a44004c0402c141a90f41c0c2d545c8051a030840031184219411002c200700348241c040c000d0b40301980c4184050829813601d111203601010f0b0240010b03005a5001c54007501ca5140c5d441c1e014540440144500300329a9200b00c09540c420408a00b035000c3d0003140d810580c1d0880728000d4514503a210b401410310340d0358040c40c0c246085401020a050750303007800c8484405031400e1149004204550340d139264108c84c40d006160039900007801d444200401c0c50144030201d4080380a030fa401c01c02c1103402140340c01c42954103002c024140c0d0070418450400a48016400c90150f009200c00d100c11003842e4940d5623924002c3c0e03190300c0700f2a4100d81240003c1c0001b003110b11301d070004282 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 772595764 1250 772594514 772594517
    0xf030717011823071d130605010b040609050301060e04020910230a0b1c0216060614090f0c09240d050109290609030a1e032a12 56
    0x8600301c03800c0c02c07003840c40500d180540c1d0b0840464801d00740d901c2c00300b03c16407428118078000c1c00c5041c0b51141050002c4401e240c0d090501c082c10f000304210807040310b034054005030019028420b86d40c44800298555000d40b00b22b0020500c03000000032075003018002c20040b039003019000d0700c2c40d999603020302020f1880100306030411005114003086000400c2076010212a0003d00402d03291000c0d028452841d002c0d8120190080c0d091103059400318000480050b0b0054512015840707c0ea8803e50f0b0f4a280603010006105500b03000b0701040f0300d0700c070100980d1514811200361200d6159160308440307e1805072404404000c01304902021800c0241c0300103100b00761109091141d98141615805a03002006080e06164664004110410050145461a01c0c03007188a44800100380c1c078654150b901d4a0b0a06d00944010035002125501404100d901c0d942208890780240e1401d81005000b250084007100801c1303c90b12080c1c50401400c8500c610550240b81071340341d0303a4413900c42d500d010000c080b0f40300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 772597014 1250 772595764 772595771
    0x5030c040515090406140f040f0f0c080717010b0d02030d140405040c0201021c060b120916171015030f05011d1e0616110a02030102070b070305060f03071701 69
    0x1640d1a03e89003944a903001d01800121149010408000b404000e0403800300b40c0812418400403841c4d0068205690b50700240081240101d0b10b0142040c41407980300d9515805412000203c00d9800b19000351549006c030020805052050100025500c002c8000b03505a8040170211703a290b8002c4410030411500000e04074101541c85000909882c1400c10b80c000503500032400c03050394003580101c2a4400700d02d003414044142080007a00041c0200c400c403c4d88070901201241910b4014042d90915110503050346e450b81d40c80e5104100140c2d5484c112000501c0740584003000d0300d10303d204d4803d0b215504020010000d00e180c860b501e10504050054605541c2d4840e0307148111b015051038106011600c0140000c103071000312140c0f00604c154034203100e070780040c010890740503580c05400c0c46822540c03c0c8121202103584540c1d01c2c040c41c13410001d405620002d103a8051010000310a80311310079a65042c86169545c400340100403c00000c07480d09640030070001d01011184040c110544841c050001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 772598264 1250 772597014 772597051
    0x20120a030213061d12061303030b15030f18030706020703050c0a2406030b0c0a11190b130c0302270114010e0d0c051e030a03120c0905030c0405 63
    0x103440b000e0390368000700100300d2411400400350102080060000c1d0103c80c1c0c0d001c4051182c0c1c0c15600e5040040c600c18480846e480e41608141c0a5480f0025110b0054552400d0340312100ba504c0c100c1c0d005446c6501d51840b06800a0000c409418040300b20901c500040c50516106540b010040d400050046081c4001444040150b9100300150600d80d0b00812440c0241040044106201102c4045034901e41d802d0400500c040b8002d0040140c00c0354154610590b1403501d0312080341d00400c41e0791441d50302d014072008400c8119403010039606550180c013010b0616110010000103070100c0b86001005002909000c00240c9061101c1d8400707e1000e24031032000220080320345031181c0003604113041b00340f006038444034036590141040b86e00e140e00351061010010191100d2240700b0940c4221840b64403c1100d02013014a0680c811001c0303c0003404503844a289440d002d003040307a00c0300c0070380c20322071400d82d6802240b03200b204500b044031006809004420000e80510018200040282d032044500405a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 772599514 1250 772598264 772598287
    0xd03030e15070f030b01020307110f030f06090607080f061005221703040e010e040305070f050606100912030e030c03190326070509030c04150620120a0302 68
    0xc1c0e107000e250380c03000c0c1000c0380340241c1c010f031420180f00700032030806240c0920060103036000001c072503410360401400b101c1c107205d080c0095514180030600326018004c0c14014007450200044182c02220b0300e00542e201c558802d03d00716000e000844412452201c00000304680b42028669501c81110310b1a00d0b51404c95003800d8039807c15400c2040a240454101c8108501d170b0260f914203020071500d0700950315003031922000ca4400c400c10f000318039180d47c8000202d01094000d500b114102940008180240d00342ea043c80b6441c2e201c1228507502544e4103015007801315104481c802c040d10003c8491a44910b640c3e14102c910743d29809845406101d056254401039408008108040000e180300381020350180c50000c02d40034007806200c4020442c0000c2c0806804a1960070741d001500740751030742c0c564007403170b000a243c040c942d140541c000d03280c0b00304050051524883c55003070312220748450000d051501c021014070010141d0902c1c1c190001c50b10130034280e03070b140b0042c000d101e080c0c640503040c03100c115003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 772600764 1250 772599514 772599523
    0x110315011b1202030703090e0c0901051602030709140603010603021003150302060c01200708120405030715020310120c060f1103040602100e010b010206010b030604090c080a060b0d110d03030e 84
    0x2c01025030f1021400e001010390020070040a4045680054110704090b030480c80c4902942004905000d0041241c4450284460440324095001012181740550703c01520000740003000b000e040030410b000010341b0030b080500030740c1c0882c0e17400341100c00314454a010481c003c11202c14490342d2240e0390500000940c0d20f400103468548404000040e200184a0302d204280c04062450151b0711800d01100c400704841c84285c89440d02d401002000c1669103181890851141e41001070242c880b454900101d2007540d03001c1c40c8039184c000c2c4441c1c1d90946a08500d4000d0b44192401030100400038402e000c00c5109007440303128a00036003413403400c840d8207800050079a04241c001200590210801010f1030360940030340382e003a410120080200f0004400000d4031040705004903001070100002180d250740f255848856400c0c0c2114411034403d4544800c240c44544040c0103179291402c2580441e02c9280004a10b00f1140c0d0180342c40c50342458070818400a132038641b405034145642c0c0c6020740e104140030b00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 772602014 1250 772600764 772600793
    0x1a031e1b0c010b09070f050715060e04240b0619020a1e1e0b0a0b01142107090e01032d030e030f01060b120a02090a06020a0303110315011b 61
    0x80020500300e42030000c0c004c0303810008058800b00086081001c0300540c020381269000341c0c103d900b50b03010841c2204450041d100c90780c02402c1a40c168401c000501a604244540304e0b403030341c3d00720340004a003500084142c0710b1b54012254401c500b04024030340e151200d00c00c0e203182e45181c01620b9002150b91104440140b4103220060104d00d511841c1e0700b0414a0390f03400047c68444501031007191995129aa402880240800c000365910074015031168000c200c0015010300d42c03a4010781c3e8507500b900301000c0d03481003c40040c0010f411004944d40314080c164020544d4070143d250640f0b6840c5443c0c01e0403021000000c81810314000143ca1a10b15103540e0000400b80a52920307814141c6c801e0500d440c1c41d00e0141d81d030038641d150401c188414603144045070912008082d0007415510b80d07400e80303002840f6a01030310703a1090705100c000440c0d03078011950190040c0291003c005c802c101d0f0b0000402ca00c003c448003401d00080d10f01c60200d94cc05015aa400d40015903644003034406a0340d1035511750503030135 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 772603264 1250 772602014 772602037
    0x90e1c110106060c0f02040203060a15170a050402150a03110f280206070309020f0618030712030507060513020409060605120f070303050f0d060f1a031e1b 68
    0x15038030400c100009000318401015030b40340c103044440840c0c8070395042d0780c64510300034880d640000c0407031031f2076980200340805082400c060000914200c100a041d8038104a10403080c8515400000d200c1c40c3c46110b018420394000e060400303c8540c282c6510b450740e00074803240b4181590f4903a4000d2000d10f02d0301800003981d0741c020170369aa01d2410710301401150080140d94640d500305640c0c4490940c0814083e42003041da0601040d040f0a030710001e080c0f194140d0200c0c0d040a8040703083e4a1a94200903405140b800c10340549803416143c007480c0d0f0f2107a04c05c2c1405004510104072560008407240d010b02d5200105482c1c2081207202035001070151800c03a603060342c41039180e60041c01903103070400184003003401500051611000080c1074a481d54540d12000d0140080400c12a00c80c0d08000d0840348400000c96041101343d032204c80e6005c0c0b20525000e2071075582c05210031080d40061010450303020b0060030700705d07410822601d0b220924030343c0d0043c0640c8680c1000e5402c46401345540d0301408195605 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 772604514 1250 772603264 772603277
    0x30a0224060405071413051c170c01110c0606011803030f12060302031f0b0a050d120c0b09060411010503010608151516110306010506070f050c09010308070210080709090e1c 76
    0x10b0000b00f051114681d44d41b40e140820310180c0c20000f841d0809c1d524039901429030301c680c9031601940c4a50040a00c0c0e10a81c610075800680c2d58254200401d11521849091701d0b107401c0e0842d074400e03000428566000c0200030a10ba0942402142e010b03036401105c1003c054008500140c503540428100a9520122000c0400182c01c0340c4000065000f0b102c0c030307001c4c142c400501140c605000a01e04806112000d003402d0040e4030010001c82c0300d41100d014064100e03090700010300b0603000c1d41c2e95075601180d003910520071301c48803401550b21900443e0f040780d031180e440e83c4550302c074510f01c0005881a900d141d0b81c413169103400c0b02c540c1c15160016100300d1520048070a4080007030300380034501c14500101c8500c240c00201c0180000d555031020381c0c0c807c0c1c0d00290681c003000070b00d19069107020a0b000380154064080000041002281d000134000a40709950030190b51101d050140c402c070009640580110303410324000c0c0000c487d59032041031000070b030300100c0c0c41a002002c6404d20070000e100c24140019074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 772605764 1250 772604514 772604519
    0xf15220f060f110d021804091208070c08030a05190e0327151c020328050103330614120304060801050d061508030a0224060405071413 59
    0x4a500c10384a14010700602404411004803400019109084800c0406a80892001204001c440c46a401b030360001c0d00c10000d140307031820100080d9291b8240b400009103481c00241c03489200c1d615100c40326500422850031070b200c0c04001c501500c2c008100c000e4620748415280d0300c0190f6401140040d8226202650742c0300039000d9404040c004481032941c40e041820f40ca900386482d0b11060f2010b030441141003588581d05851550740c40008040e030400101c0c008001d00001d8a180c42171074200c000b008546a1500c03003410303400c000b65182403001400c5603054001554104501e182c040c1400e002a840507025035001000d0141101d00c2e50f04481c0d50010803041840031400c0958091040d6000c850045040c9481c1c241c0040c9000014002c0c1d901400080c001541007007001e8006c002c10613400703514807400a88604981d50340350040901d01c0014071481703841092251035000c112104d42080c01340700007907981d08000c2c04090f1102a01c8007003080804560380b07009000d04000317409818201340d984003d182c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 772607014 1250 772605764 772605773
    0x103140705180913060203060a0b040617010608040c050f061611150301030c14180403080a060f03020a091d1c02011407050306010c0c08030a03020d0606020f15220f 72
    0x5006a8109000c0c0c103080d003e100c0004029413500c0b0b2000d5020794003507541d80c0c65002080305c00a8641c459804a4400303d40450401d401c09195528026443c2d1481400d03030345e450040724402410b40f03025007600400301e004d02281c1044500b0410201000c0c10040c5001c03a090541802c0f075001c0801513440041e4030b00980c0d4585481c081c185141c0c0d5401010340c0c10b42d410750700ca000d030158891040b4035a4034844144440c1c40d0300c0c0c450720f02c00b1003401014008100c0c41c0505010300000b50032626030242a1401c00089074182e00074043c8010b90b074002c0d1940d10380904014102c030040440c0c03921041c01d03030300c11208000101c0017001826244010041282e0f10311001c4500642520304410b03c0c041c0340031440081101d21984030055070fa20407003d280054141899003017921500300315400100141c04005410b001994160b002030540d01d51402c0d00300b00044d602c00007282c8030070007140c20502d140c000300740c0b0f5022100c0c2d0384681900101541a20000c02c1c0000224021803001c150301180d605440e69500b03002e01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 772608264 1250 772607014 772607047
    0x3270f0215040b03040c050613151701032604180f14070c05010f0204050f1012022a070317180406171507054806010918110103140705 59
    0x140b00a40700141031101c40c00680308050018003035000130030200c5c50124a1a40306807400d2f1001507480d8400201540c5131304045002c40040e180c0b00c80b00c00690000030400c0c010001c00c4808a50020100c01200000b0345888009415140e201803141038031400c885140030b203040083c90160ba42c1d504e4084101c5118540030342510070404900c3d96091061000300035a40320100b40c40001d0400702c554100a003000401611a4a40129211070852001c100ca600da000c04071000010007149251581c2c2c2c08c441803c07c90754a19190000902c20036000d84c100040c03041c48009441d0881035000e5101d4030460040104040f2902903025084c0d07040a0340350071010b41e5051080d030a00b44001c02c45807245182425020344a403043c10100c3c84618005c186400708001070009a2050303181c0c0d5410240c000030350800c9045900340c22603030040d003402030350300001c0c200c8201d20444600b50203450a030181540d80d501d50451003000f0500807810b05403075126a0182040c1609107910400d42a15111780b01c0c450607501640340c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 772609514 1250 772608264 772608269
    0x120f090c1a0a030c1106010e01080c03160b16060e03130b0a170612011a0901080f07031506030525050604030503121008030a080703270f0215040b03040c 67
    0x850905501d16034110008000c851a1a801d410045030500700c030841221141121019a0603c0c0511000410081c400c40440c030f04071886002150045075100c07040503110f03802c104401b000300c0c0406c50104102d03081c4070050700c800c1c401c1283c90700b80404181c90341d2050745c520043c01001034200280c0301100d0200040c460300170306641c86801c0c1c140364a0b62805803da481c062a0a403500b5034035000281680e032541c91600504030080000d010307032364508030514180c000c220540340c030815190300081241d07400055403101111910005152030341ca5620740b140c01c40d0b55950750301c420303d486020103c00700e18100401c01088000c2d0061501d8510b0308614080700402d2070b04454030540c810801040420000415645903681d5151102c140341c4030100322861164559200c00c0c601c2c0400f00385848801c1c0c0101c803581c414006910284000300d0203000e00178405d10b00380d102c034141900e25a510f4003c0fa0081500d11102440a0301d0081141c5040c180d90003207400950001c03801741800020001000802401c9000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 772610764 1250 772609514 772609529
    0x50306070c02091306060b070f051b010f050307020a12020607030f0c050a030209030106050904031205010e16030f0608060112050f031206090a0f110909060d0309060e01120f090c 78
    0x250401d50700040207400050104540c102e6903107592018072805500250080400c0d4400380d507101c0e10307490a10546c0c12200c005656500881c44c55482900e0301403001c809212050b507580300e1000410400761415013014007944110705c07030000442c1c0000c95207902448101c00d103800500051600380001419100314442c0c5126090800a480311200e4108065510714000303400d0160b01e0311003050110b8014001c0d030703001d60b0b0310941c1002030205050f000b24003100403d82c81201404540c3e00c03002c03001c4441e24140e94187d000700c0c110000c82c101d24407a070300c00100c0031200350000c50a1581e90003200e03d442e0382a003081000064014000c4100b20041205c88131071400302d0055400c00c4d4031419500c0c1f94260082c1004c0c000c00010b00028904407140e880100e87c1d10060a0400412040c07803114031882d009024014001c078032440103d6164031345649854400303941a91030b0481c4a08207003040701c90b040074004d41814070511240c00000c00270a40503882080140c0300c00099aa806810300f810040303502e0340600b1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 772612014 1250 772610764 772610777
    0x101a0d060303110d230d230f15090a0504080d050403021006081c1103040909200f0f011d03060a02030a0b0105040303020715270e07031e110412050705030607 69
    0x4a01000300e000c1c00d003440194500715170b1070b0b0a030341c10444090100c40b8058007032480c87c100315074503500724021024050000e0a4220586507528286d4107203500d012081c440d8007200c0640001c0d184549500b02035072191160f040c20b410b01c2049002102603883c1909d0032030141e080f10b800c0909260346807140d0001070813010001e10712580a50152244d440e00c25071003504104800c41d4600300e1520805c1114020400034508104007074a038100a030340c44031710720901440301c2c8605580e113200303141800703002d0b4103158010304c05421500b0080054810030510780e1040ba4010740d41c074a80206d60380038070810784526960900941d41e0700c0d2850302841118034000c07849041c00300910040c0040317a0700244000989103a00000813210340010f1041d5246c0b642c1c4071402e842c08029a50214051038150f0b42842251000081003510342c4602e03000750151940341c00300c031074442008100c003079a120b603070303040904c4c295140411107240c9a1514100710340842015802c2d24030754000e00c1d041016003407c10400c0d0384801c1516001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 772613264 1250 772612014 772612037
    0x7030c08062d030f031c0b060703050a08180109111306080607050d06051c030801140d170706020f0417060c2b060f091103101a0d060303110d 62
    0x10b441901e0300c070030014600c00001c0303640c801e103440403c552181d41d04240b0490740c882010640c2d020466013884081107245003420b550b5040d41c140325043c1d030216541511a28145a04490308803900c240051060084051a0041300c079042001e00c540c00c0e0a41c0500d0f00019840504414040800074a04803100c010349448400c001012010801d80c3c3c01845503d8400c0e5218090300103403029000d59000903900c18200009504613040d4241000a024480d031900c14683c3e90320b0001c62920f000320300c115608610b04940c40c8000801400c691351141c034807040704a041c005151a1903007240c0102004801c8080001030034445003000364060304000ca4140018815480d2003178100c040c6000b10310b040e5040901d603115414154940032102460f29080007010081c1c2940c82c458054105400d02c034000780320b45010022a482e0038900206c038407509c0c3c0341a000070064a4034000700c000700f540301c41700480503030144000324001803a80a040000c40c082d80c1c07003111880c0168101c9050941104080c8180424181d44 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 772614514 1250 772613264 772613299
    0x1e141605030112030207050913140715030c12050709031a07050a030f0e06040b07120911060304020d0c0b1233031603080a0f05180f06070b07030c0806 66
    0x449040d036a0203c001021440e00d40b030184c0c500170041d00403a501c41e18200410001d04000f5007034241c0c140c010700b000741101000ca11541d403201010f00800041007411034050031000c4c000d8021b071101c0d00e92842d04004800345240c90104948e0207564180010b074088600b001804011203001c5008084d15036540000e0a00680c050702d1446003420080a140d10303a04181100045c0781c1c080d101ca20344400941c0d40074074141c6000007031031008840ca00d000c80c040600c2224180b900303100c0e85210340d40c003181d18031102c0760100411074941c10060040b41e0080c100445c10000589224149005003409403003144c031900807400481049800404440015104207040c0000e402d5404808110709404503001c0189001000803908003200c40d11072030880a0b00030000020414180007d001a40d00c075500e043c40c0e03030510a81114a0b2050407540e080c14015282d6402031443c2040d01d04e03410500040803d0300d80010b035a60540b426400b04d0315400800e035140c00b2120503582086007158460412610050b00c6000e8010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 772615764 1250 772614514 772614517
    0x10080d11060f060d080703020d0206070f05070f1103100c020715080406050714070506041703010510270602060a112106060702041514030304060e131e141605 69
    0x500ca0b2003201640480d40c1910303500c1001407595003000625540d9400c40c20040d58452502d001c0500510a9900091986120386107030342010381d1607030f41e1600e0403025468444516150324410f9414180c09448010b8a070350401c100c0703007582043d40012512026454000c0d060000c1a40b1264403040001c24660341c1945c40511164041d41c84040061182ca0b00300c0308a0b420100b080080391400400540202807220004541d40305500c9941400400541c1c14103180b03140c0805e124440c2c0102c00d070108002202d001c2d10956034405001e400011b909400744125100b4526541d02410241e04510140601d201c028042c641008082c041c00514003100c41840d1400b5900502040c0030b4a6118008100303155195011520890340050091250030000001809084500e03c1502031034520b00301000c0440c14040190f4044605640b40c40280030300040c10300c40640b0140e001900d0307070340da10b842903c2c0300d0106006244a0415a60300041c100034945407006c81040c0c0a425422600100d80e103503092243d2100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 772617014 1250 772615764 772615771
    0x71e030f060920040e03041d310b0601020105010311041e110301050120030315130606020d030c0203040b180616031d01080907050118030b10080d1106 66
    0xc508100354a0400c0001400c0c4840001c1101c03040d02c005480c03401403080e80c0e841c0c400c4211410400c4214000c1d01980c1c038490b91180c0c004a60f04010240c0c0340344820184241d00100d80c002210030400c0c52810451280841261581e8003400e14100750103009540810076800304080c00204015411600c0b0380c0004880603c42d68800e40d2107400c0c68284040345c00b14108400e40e100414807040c0e00c030195044a5420034000c560010315001c11110a40d450880f03103000303000000000c0c40c996212048040031030f8988a00b5180c01402514402c5042042031269034010411940a82107590301c4c004000d0680344400c02003804c40d40103100030700142020b101101e80c42c2080c0c20341d114032807120030041082405210800c4446605e000640414141c11405a90400464448045070040a9001525002d00580304821150701400c1c0500142d405400122503800c4200560502c543e5a551580100e29041b01d50301100030b094082005807076801c105890038541c0f103041c5550391a420101240d82c0c0d11009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 772618264 1250 772617014 772617023
    0x4030e040c022503060e03070c0302040c0323010e0c070b1906050a030501060603050c0c100c020c0a080a0b010602030f0a0309170d0911030706170c120106090602071e03 74
    0x10078401da04940200302c041c10704070480d000d0a92000784441c400350362019601c8240c40803810310b5240100d1b100c0100444905d03a91102c4039100d020300359003c0c00300502400c1f10341018141c0d0303180b80e000044224541207a070f44036042c1442e4043c0d03061080b18000d640c0084c3c0080c000341414000c0700b0008405055881d486601034100da15858000d804100c00342a840d0700c02d9800011511001c070512030107400210903906162410311032500d5200c9942d08c01d11540ca0b16032919000134000214884940c0c218070260210f510495140080702400a0002207440d401850150700c805484402c1202c1d11802a0050030076001450815040341c0c1c8001940c41106541c0701015500d00d54441001496a02090704140030100c032912405c0c01400a4000c010341c1105494079120600390000c41d1900146034070030740c0c4090b500e80d1080000354107501010400030f00350302d40c03604060200e070841440300041c5031b0080c181c9a03102890545820000303820b2503a19045161104404004a900c2036003a80f0900202d0703901 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 772619514 1250 772618264 772618271
    0x6020607170615120115090b09060a0e040e0c090f072703060603030e0103051005010509042a0207170a020102070b0d0f051f0603272d060509010504030e04 68
    0x7540c0c0083d4121401140c00ba10000003c54042d000c0b14980c000d40d4140e03005e11100e40d45803112030ba81a41c10003000d01c02c40750f039031004004082a80c1000c10180c83c00f50b603282415925107007100002401c2e0b450740d2443c01d100b544010440344252401c50740140c3c01c084802119106814400300052041c10035103900d04150f240200c1c0c02c40741041129500d4020758000504109841e100d02e8014032680c3c41200c801e0000c0e0520000c24040744c003d088480442c3c1e41615032600e00640d5070144006841c4103030b580710440b001c090300081c40068000314007100090650207040440d0403c4075601c200c0100083d4002c190340329940010050760002010000d035005140820b0300d030059503103840c018000044540318820f040c4000d1001c0c1d100300803c01c10f10310752115a880002d07074961208071308542c1040e030050340c076521416000c030361000e1038169042c10034010b103a0010322075200c441d03041110302d00d00f40d4402242da5856100c0c061100b103110b0140c001c03032020000c0c030140c1400d88006003110001c003d5144966035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 772620764 1250 772619514 772619521
    0xf0d031a011419140d0c0806010e0d0312021c06030303200d0504170a09060f05070b150a08070602031806040303020d030e0c0a080a050105090c0303031506120f100602060717 76
    0x495200400d0081c0c42021a40d458172a8915405081030700030581c080b80014021940560003030b00740045800c00a40b0300e00210880707481c00c59441803041c1c8802e0f642c690801c19074410422102042240c014000b0380441c0b541c3c5503150040c00c98086401c4681000e0015641a00104a0304101c691004e000708000c205500c5c0c1d4100103031445440d809540c41ca46c4005040341c11103801400c0d0204a55103a104e000b05c82900f50400d65103446000e0005012486040002d880041c465148000b04200544071204144d2500006443e12000d03800c4500940e0011a5606903605040e00000100c401595401d040615581d40a1356955800e8110710030b142d210700038a007201a082001c000c22140090116482e159108641901c0f90351040003035402e5402c00000400780d05002401d0034a0704006001189140d5811580703c400d1034003002d0066001d401000b8007007400f186084c03410301070041c500b50000141070800f50300a40ca038169026109640103e410031003915008008140c140f108240032085969 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 772622014 1250 772620764 772620767
    0x70c08090112020315010801060807052a030f0414040c170402011101180311011a0d08070c0f060e0f06040b0c0703020d030e1309120c050f0d031a011419 67
    0x503002c40d01d007030b610310110401240b09840c07155602c940b0303801e03280c042c0d4590700e85100715600b60040310302c080130480c02c0009032008802c100c410004280441c446100040d54158814215805540708180c080d9020409100140d040d0702c515440e4242102d0410011054010103041803d0b481c001c0000d001100c4005402d59024190110401555000070001d002d04139440d52030615540d0030580000c0c2d040419046581d105201d04000300c00c4a10004440041700d008100525070311090450307010f4001e026150015000c41301d19000391486d44100e8100c0c605085d40140594803d402d480c0c41040c81c051803102c03a13200c0d40c0489041c0d488a555143c0d03100503020003203251003401da00082d000f01c0a0441041415030081d244041214221440b004410110610f402502c007082d1000d82007055070490b10307041d140944a00c0f075100340f1600aa0303d042c0001a101340c14010100c3c0ba100109072119040803001145010f4040c4401c42400d19030f1141812110703040b0f40780102424041601203081400500c01d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 772623264 1250 772622014 772622027
    0xb100b0c0d080723031909110405090f010203040c1a120606030601030204080a121b0309061209060914010606030c020a120c1506140603010e0720070617090303070c080901 75
    0x900035013102c000e0a6108a14443d8661007125a0ba03903881c070400303603c5950005401110091034010f03800381d220055030004c006c0188400b51009019220782007104110142c280041e6116501423003220346076074a81040c16080000811100000303c4082141d003900c140e801030410740003201a506107403690340d0400141e00a114541010310a403144150302c000f0042030100b841000c11036665220230395002014051284040f01e00024003041e4100400d12174240308002d2249052072354040820010115200c1808030381c0c020700c2c26901184501411300e0902424080d01e0018160303071404200044001c08020748030b00e0781e24401031060343c088034040c0005105814a080719504014a408050501000c80b8018016403096403415090751400ca041d6260aa003601c0c1280c0740000c80081c141d8a015040740c5150046034912209424a090a080d9003010043d82e40502140d4a4002d42c03070150481d42001490000c01000d0213900404c100100d8960081c40701d09810b51200c1c0d15503d0780c40c0a801038880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 772624514 1250 772623264 772623287
    0x201020c041514010309150c0513030b062d09180105090f150601120e1606110c04090302120a05040509040602040303030b18130503070803040b100b0c0d0807 69
    0x14240520b01c140307090750310b411504031042c20580908245408005401b510700216015007030241c128241010701d011508a00402115403510703e160129065626007003901503001500d10301031000c1003203080d00b0424500b06407403245440c2d1a0000740c0d039110291140c003420f00b40714010301401000c00c2e02001c076070700b5500000c40e540000b440685040a6034541d60900006940e40c0d61041c0600401c90b84c00840030180101410303555010310404080ca41d0000d00541280c4075100c0c401c0c0c0041c1091550500203000c09840681d07142080e458902503498a4003480d4030003107100754034041640b4006a000550180340380c0c08c100d502a22200e12004c107484601950340090f41001a01c01000200003240d03004105581c4261410404040224180203400d41c4070178015002e10007510228010322030068100b41480c2c8258112403405007107941f9000660010f50f0111030b42051141032100c0545002285006014000503180c1040c01d1840a2560b440d4040c1444080c805c07900003181c04540700b0308041c4803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 772625764 1250 772624514 772624519
    0x220b25050601030f020306011706130515040b07090e10090902030f06091c0206090703020f1201021809010e09030706050a0908070323040b040b130e1005010210091505040201020c 78
    0x80b0360f507034200030030705440342c440880c8a0302444001003102d24035000c0100000020500030714842d03917203482410001702e050324280c5040c400c7c001c0b4102c40c504841c9000c0e200720b1248440c0c010354200b0000240031a022500300c9840c2c010b080f000c00a114034000c0d4004101d800d00103020440040354008203060168400400d03481e4041d43c410003215600c0010091080c0c01030400b00c500075010004201e80f00e170000c1d1400d402d507801865040015140c561080016590b000702425011140d00c091142268400001c0903144080c1021144484c584020524010640170300034120030b140ca4400b080d03c0c2e00c03508600412155944010420900d65170b4007030008540e01162982d5101210300300501030070800300e80000c4a08125100010051040e015202201d90604450f070815042c05400d00340d40d08040d42800c0e03241116840003c102900050040c001c03081c004600c00c101d4141302c00207040884100520300340f142030031000da000803641844805a420b100c60001540d80755880100d0030510f2024440d503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 772627014 1250 772625764 772625773
    0x4020904110313030e010c0b19020409060f05030d0305011a13050603010b030f061210021b0106062606010504050609040b04020c0d080615040b0d090512220b2505 71
    0x41c0fa08074803603048410034000d03211071001d541d0007001140c4003040309900801c0400030034081044008041e44640726000010400b50a041c0c07264105011a8519800716400d4520140104210308003031003980c10038101c500d0240001c2d8101100001a5000003001840c9228000740100b120724403250550040e15008099039a01e59513040320217020b400549942d80c0044007100800c54600d82003500f40d440c04000c10181c80d007005503001e803000a400034050280040c0101e1208403061000b8070605018100341e40b140c4008a100e42c0c899501c1034480100c2802141e2400c062111903a00b0005a60840d5021290035542c1d4603114045400381c00100f1101e6017050020445e0104540041604040068280e40b100b01e56955041000450000061503c02660f003c000038041462090024014022050300110f06ca1165542c1c19252080107401581d01500200b100c1c458001c080c2c44c140a110701400d00e0074401410950b0f201369500ca8490303104100c0b4208541c0c48a846001000c41802075008401e45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 772628264 1250 772627014 772627021
    0x6020d08100f060e2119020a03021c050d0305090c060a110106140f0609100c021f030501060809030304111e0a09020c01060815070c0f0222110c0606040209041103 71
    0x540005044800f13180306003040202040088610b19040810351400d4004012514028a020034491201c038401e80c0c11002202c0084007580740d18294a8003805128010742c02240b80d81401400c1004c0c806d421030815041c102800420500028500143e55080710820741d18800d000082d90702003030319445408a5404e0020004000d109086000c15402040da00341c803080c4e41c0d5034100f10061003140da006600c0034500d91074284c041d05c144a2400c80702d1026084105807a901d0300b02680130030f842011000040c0c0c58400511005074817081480e00140c2c44001035045007815a0f820180b0215000c010340142800501d40080c4000a00c0104406101030081d8001584804801000e90300060030300c0f1840d82070040000f001d040c00600c580207581d50301140300454468420444111100000c1944c055901c7d810b0380b005a40c2e140802c0c440740d0360031620420000f142ca003203841942c801038035040408000740041015194003003480fa9002e00100c50060340d4528003800540200310f80c4107883c03111040031007003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 772629514 1250 772628264 772628267
    0xa030225050708030a091e03020312070c06140904051005060d02120702030a080a0c1e02150106020708070e0c04080a050307050120040e15120705010e0a06020d08100f06 74
    0x462056010314141ca10b900d440e200010358a1081c1c040c03840c0050b804040801c80020010054902c1c4034814440403990b03030340ca4002914002c144003810380416070018a000c20002400c0d800300081205091000c45042c4500c0409058080ca140050084e80c54200007208910208440800344c44000c01068803608146801c6009400605240d0602c4010380003280c034036400002a900851a103a817444600d903110070800c0c0c041e00b82408403a040c001060800d103903040405524001040150f40105441420182031800b6072106a0107007065400900c1c0038440b08002181c8402602d00f40f0010b03c0040e1562800c1c0d8140348078580c40640140646c1c0040d0040120110040824a0150f0024810600003c1c2403502e000d6400300100c0503081e08003c1008440c0b43c00f444035600a00201401c0c00540041010520f00ca4198003602c0150700011814091580c000e5142c00e00d00806450102205092240181da1015041075040a20106034005520400c80071001f00241c005a481515120340e01d080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 772630764 1250 772629514 772629577
    0x7060b0a080106170f0f19060f020403060b100e090c0c0a0c03033f09020103200d180c03061d0715090b0909070f1101090807060b060414060a0302 64
    0x1340c81c011402080f0300601d0070b020004001c101d140c08100a170040503006008119a00c8081c90304a230100e460380244a4045158405800254050140420485500000c201d0340c0f04c1d00c0c822040521925802c403940e0360b1610407216900499210030641e4452040c80140d14000c07440c0d40041880109441c04010140d00548542c0320141c4181244c105230b0401c03800e07040f08607101741c900c0d0f614607007012540110f190340e400c4014424018100001d400d02d213214103802c0f00802800c2480c0360b20000500c0340b4a07031076505c500842414540200f1090368141e581c0e00c0341c188000e101c040c1140d6124000c011180c0c0e00d0300d210790002d010140c11103040694880030f141d000c12400030345401142080b4000909512202c0841d01005030052200c041c0b07550314182650514241d441c0081040030012881e10b01040c24455a011180580c1d070b200c2d19000ca03072030004240d40001480c40e0191f841130204000085a0900ca12950309044940c142c40c0d103c5103008034020701901502d100055400c503565608520380e1007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 772632014 1250 772630764 772630799
    0x40209060f07021f05120c190c0201020f0309010c06020c010e0d12060f05030a1b090e030301052107090e0a02060d0c022b08250225060507060b0a080106 67
    0xa83c1555410448590400700d011301400300c202084080140000c000c01903c54954010710f100a0a4100400c4020a20400c4851800800400d18071040807080d9a010030840720f090401000440c600154800020468500402c0080c01c040d00442c480d00a0030085d0068141441c41344100c903012404404010007000a14502c2c2d04820300c3c00e9130209400e03003408200015650007400801c010601d40d65944041003c641c92110304030001c020210750006a03014401c2520310321401180c403541450100056512510305032000c006189141d009040000f09000303084a010302c5000848540124845050014428000758002400961244003102650003110041c100c0c2e030844252031440b2220305c501d054041801664548410607a0a60031310843c0b1603a480b14504034503146058002c040300003283e00c3d0088178400340c0c0000020143d100202e4600610b9a120000c04c2c0100b207191201c00762040c4501840540103a0716000075010f41e0703c4080c1984000c01d0703000c0007040090b81da5801111300d0016003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 772633264 1250 772632014 772632019
    0x90e070c1e0b2406211503031c060504020403030f110c19060305070e061608120108061801090b060d060222081506031b150c03031009090506070806040209060f0702 72
    0x9040e80c10b90742411400c0d01ca5292800c00f1003402170380c0065126807820300c0280060301315003a44a28410340d03101803020f0079010100b0b00c805005000154165002e842158001c3c034000c5205000070008250b00c40204a143c40240c2050040341400700d220900b030100c100505508480340c00780003030041e80035400c0ad40440395280e40801658450030800c8965600c51000c0c1e0340d000c401440300c0e115410403807103d0120184218907851a007081000c00c1c5503078800907400000d40d40c02c0350042041040d0000b0207401c0300035854008000e0b421095484444443c40a85114020341c0c0c080060401c00415504841c18540000b0381018903103107031440460360b0100c9005549060127085d88000300c002e51040c01600134100200a0070201c80070042d080c0c41d09823085040e0b584121800c1c2102c985c0c2c800c241c0181140d000c108040c40d600e18203010101040c22040d8801d03400705180500d048042000454180d400c000e0604d0609029290640003902a02410541c01d51103200002c0c484148040e0b1401010060300c203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 772634514 1250 772633264 772633321
    0x110708070b120c1204120e030f0606090f040803010603150b12100b070b0103020423070e01020d0801080c0409020103020408100203190608060a020901030f050f0601090e070c1e0b 78
    0x803d6280342c0f0a02078110b005244401c5000030a00085c10a03040554848a80c07501240345040b110009103030000103031000440750020001e0100760b080030620305502640c10315045065041035911180540300502c40e0800701540d6000b2401c005405220020080c0040320103d6140d01803c0c0e40d10341d8510003a2a2880c503418441c000044807011002980c000c1500007600da48240c0c83c6400b844083e284411011310180c42d03900495000c20b03a4004403074080e210640e544407128500e107002900d40070a01c1800b600340040c910040262650005402c0c1c460041510042040481840142c01034061034000201c039020760303240720071415034981c05180300b4608190f42c8240b004244c510a000c440c0305000700c010640203000040e10b111026001454a0b04040c0340002c0d00d81148403241c0300300e90040d9a9400520409014403201d5a8480d03603140207026080150046403c0180000d000c0703641c6850700900407016410b60040c0000c088403000552034101d518001e1794038002441008864030350320f03007244801c031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 772635764 1250 772634514 772634521
    0xa0f030f020c010816030509010f0e03070506010803190e0f10030e0705040b100c030c0f080706290f0109090e070501020708060405101a0d0b1005180403110708070b12 73
    0x20440845019012845c031144119600c01800ca01421008104240c41e6403241018038101907244201c50b400c010440c09140c070341855140890070000103030f11080e141c0d40107020b20041310140711f209200300382c05030a0903c07404a1413808503102c0c120980c012a40100481c5d4a803581a406030000000e80c0c038030b441500e00300c82d2113404020440e02248001604900303540c00350075619004181e40c4041c00d029040591000c951030365012100c841121003114080c0d0041840802c1042c24080c1c5409014481585440210300030742c501c1c01118a451014410349030b41440360844d90003140745a000e0211001c0510450745001419580c900052084a005120701400026004404104c0e940503907403081c05480d140241200020140050401c20088101009400c004030f03a01c0681800040f0b110780340d402824900016010801c050039030010303004002a680c0040c80d5440c0843d1070f83c0c0158141841c40103071013008041450040103030000700c0e06204d004c00100d810703400d15020380041d050081c2101d0141c1d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 772637014 1250 772635764 772635767
    0x40909062d0c0903051b030f070303021b330c030c01050601020d020f0c010507030905060a08010306050a0b0114070606030b040c0e011a03241c050d0c0201051b0a0f030f020c01 77
    0x8070b1900c00601715070000c00019084646004c4d08055200c0001d04445001c604c604209060117416842200035074011040201c1c200000450341c042d2010480d0000500036106a4031160843c19000c0e95260494000a14103c4244441620f49201c032400440f81c075224201001c900816080d50b00e180948641c180564500b44002a90051025007030301a08522141e60019903a941240c00c08a090000385c82e408a40780d2103040203040f00b80090317903070760a540d455418094212840513050241c407a00340008142140d0708914900c000345146003025030b07109810300b0030200900f4190001401440384806000510414081075800c0c0c44440718600300c0380e45da90713914968144040d1010b182d99a0180700080c0040c02e5182d0340c601e4440101c0b40000d50740788410024010b154442030740200f0722036070500c20052002c200440b050b00381507030400c03003403910490b00060034034060b22640e00107002d0900c580110300802440f1200109030700c40110310fa040718518000d0000045a0450001446004440440c56 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 772638264 1250 772637014 772637027
    0x60105030a080414030705060705060615160f0f0c0e01061701030b01030209040615150306050a08070b0f07050d0c050c01020601030312020d1103010603060f060311040909062d0c 78
    0xc55100d450310f49440c0c40c040c6a50007459031000702650600946a00080d00c0e1900342c010f00c8041d1245014001c2c0c0d05d80b0b0010081c80918801740c08010201c00d005411402c1150000802c0343c039000602400030200516090300e5010803844010290f44215000103000c009200c07605041c0c07401a1a50780c0c0105d44c6400d0f003183d200d424400039010b02c05503401040542003070711070140c005001341c001190804500501c1d03180b85100c1d40c000c003c9030441705c8280200c0e0b5410700ca41000703003000311030342c400a40ca070031002c907610419409540351030100040c48407074503030b0404219980c1603400820350f11074040d80e080140c8190002c0900307072f865000c0c100d6000100c0d80b010a00c1d43c140d03541611b6000351101c150b084400290000386808994541c0c2d84090b801402540340130f0340c000c04043e070b40410400d05041c42001c40c07440315800310080c9400d112229500290381400e07034084d00e650180006003003d481c100b02004c0c00e858040c0020f00d2104601340c1c4802881510803103d0101e910780180019204003600b102e40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 772639514 1250 772638264 772638283
    0x6052209052e1503090b090714040203090d08060a080d0207050f0f010909020310082d030f041404111c05060303090d0605041407060f0201050c070312110d020c010e06010503 76
    0x682011100f48a00c203440a040d594000032854001a503400e01d0341c2d100c2842c0f0040e00c030320509a021440c20040c050114000c2d0401000c251000d42c198100545030f10340c0d50041c000f06105125803200020026140e404a42c2c00502201c002c440b00c080d2401406511076050340590350068004025881705820150010039154a044c3d44001d00e940c5000d034a04005d4101030b0a04001b2001d4400006000c0b104006010010f980c440c122119003c0d21030f25014000c0d03030300007c98020b130000e01910202d140c0340030a4408546250480034420024840010014040c00851a07031549002c44d21075010140d003078074000e0024403000104803e84402003056605d00030111080c0c0c0c041c19421301c1c440060400e801c0180c0207071186140c003546200d000c80b11401d00185800c4400081c1e2003d44100c1155424002c8580151050f802140b409000ea02c005104016410894500a03115008003010380020700445c0c240700318207442151030b000d504a02d640a81041080c00c40a48031740b20020401d4078010400040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 772640764 1250 772639514 772639591
    0xb040b030402240c0705120a02031203040203101802040c0809100b0a0509090607120504110d051005090c13050c121302041a010f090f0605220905 64
    0x40d03a45550801c5000945454160b55050801c8666000e421026001e003203405648009011034900b00707001e0007030003031842c0340d185e0044d4002e5002c600581c82c081201c4141c401403101c6503a40b582e1781d0000c240381c00c0c6d601080310042e0340f03061400081c15055051007140d01e44200d0f004c0c048030411920465503250b00b5566464584c1091a140d00d08401d0ba0f4810001040064054495a0b03500c00008614110407582c5006a40006041151139a07104800ca043310902c40d00400c5541841e03100c1d01985403000d04641e00400308050080d003840000c00c07049403100c000c1c04040c40307e49400c5461079210603141c0c000a001d04881e0720382200c4181d95005840c80703204a6034001d4140010103003100600b41d4080c00803403180040d0019130b80540c0f140d0085030034804a00d501d1100080c1d200f000100038150134410201004045c0314107000c11440005000c0480f0344c585001030701e6100714404212083c98450b0015120341d0b012800040459068005038450411a03400d64543c03202d27940c030b128508468980b03101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 772642014 1250 772640764 772640767
    0x60f080723160c080105040b0a0204030f0b040f020a030c1a04180b0d05070b0909160e0906030114090a0c0f060e04110d020705070807140604030f0201020f0d03020909010b040b 77
    0x40d265690040c1500103014610501201c0c00c2d40c0341c0d90055141500030030101d0751610204000c2c80000d0020720342080c241202146001e01c1c6883c3c0c10030404598030001c20000304135001c00d05000c240d0008a1240d5001081c510340d4540d00d140c0b0401042c0380d403044080400104d240da10300707580341009440032900b0b100200481c072820155a5030040c80030310644c070352000007545450003251003002000e025060548141c5e5803040044200000064018500c0f465660244034580516a11203140e80072f119081c1c50441d841d4035104000b0340900003111070355120b1a024402c0100e801c2001815054081c010007401007429229420600003d0700340c040c1e0720100d007011100307010f141819844900400d03443e1408504003003116051109076440014103480daa808050140500c8606100e104001c104045181220b0844200811054081ca01c00501a00b02e640e09070750541e4005d01041124061100a40f001200004400f80017900448600b0340600340c54400410800880e800322400c1c0c400c1c910015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 772643264 1250 772642014 772642067
    0xb010e09010b07020a15080411040902030c0d210c12231309020a1106060306060d17040b0319110a171008070f1a03160c050115060f0807 60
    0x1e0b8841d0340840d900301e8010750032600000d4005100d07801407075410682e9071201366500b814200b0300e0a5280c4103000c02d1003186014600e500680d0005a0418005007e54114408a80341c0c10070754a00d2000c001126818203041072221100c5500401403040c040c421000f0390541c82200c001201c000c03203c41c00020803242340c8000000010f6182015110706d0505a031705115a80c2c848040d1020707030308030110003030100b840e2803002d0500220606c0748951080c003e5008107550300d13142340040c04204141d000941110142144c0148050314203089401510a10a1070396803800e140c40d4017440072403081c14200c2e9940c504504600340d080003d080792001302c081d40e202c0d51030f00c0c0d8a500302c8046290140a010001c030000174000f4504105001c034030010045003060920451030008200b400d514503c0341210350281c1002088950110f0712a1464100058a408034000440c3d04e03105004101c1c0040907030783d801404000141c82c640c0322485102c3d00f10b242d0754a500a4541401c10b803102c80b026480c0004102d184003e9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 772644514 1250 772643264 772643279
    0x9080f06040f060e0d1205070f080601030b03070e07210504030f110c0312030a0c05161101090308070606240e0103051f0312081b0a0e0103060503030c100b010e0901 72
    0x40580d040c0c0241000104c10502d000e415181c0207248042e50041124040700d240b503000e451080650180f154200034080000c20710004080010040c000b505240da07550302400c5a85007003004801800624070361440c24140b42d0070241161800d02100703070354518051840701110b010b0b40a424001d90741078a4840000503c140141c0c1c034a107070b800d0101040e110710f0700020340035034040003514404107544200030394905201c5030040039182c1e968040000e10004000701d010040d10b13560a4540d164104039000065213507040100c030044007075840600060b00106d5914244945980054110b5058010181d42a004000806001c00b0350340700080101302c2c10402c030302e4a5400303034100b00d6204500030510003001700e000d03a41445a1025030401d42c0e80d0060042c07100d2207103030421801da4100a140710742051942c01d6181051240c454a80aa02000000031500d1560390190704984046e040082c180c239115500804420f071f4402185c086025001d05142e40080154050440003002c1d10000e00703260050303802d0862 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 772645764 1250 772644514 772644533
    0x3210702040207080d050a0903020c0a1d0c13030303020c071d130602040816050324010303030b0d022101050a020316110c0d03020d081b0d0f15080a0309080f0604 71
    0x4113584a0788100078850b0208603030f11905100d110140000200f01c1c04604000f46072241c0c240c0c804e40909030112044c0507144100820280400217403803c541c482d903444d1a080c1c090b0141d00250850b10181c3e100c044105501074014013941605102200c800a41d15013800401107503885a0344c4004e4030003008a0800c43c40d1419615a1500450016160030350301d054007441c22070b00014400030f00c1c40714101407007145014440801400501501c04240c018180401824100184002800d0580e220b00060f41c603200c1e0350484248a40060a05a0b82652640c0c140c10031814000107d0480d4601390005142c55041d100307590094444a00030700c0c0d1502070000c1503d002c41624488281c4d8030451400c2d0345160344803d450b00080c0d03c81d034050800007008600140090801606c41c0c3e403201d070b03c9442e903000714154a06031243e20076a00c1c0c1c00300d4445410f94061006100e01107284104d00c061040100e018140000e400600714800e54404005036510140291108032000c1071290581151010901041d0400d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 772647014 1250 772645764 772645777
    0x101a010c030c0c1d06060a05160c0b0d02041403060411120114270109080a0c02060d060f1406090a0b07020118060c060e1603080d060810020405032107020402 69
    0x1014882048603032600c1821001d00da104011070a048040b42d9a2030f404c0c030380800c3c1c221405503202400e10740c600901914a014a15102c07520200206500040c030136024203980040c0040c40d0b00c607035690f2000e002d020203507100b4019891425031810182c480d40c00c000038801d01c00e17a0060590540b100030003040100d80e9415925081c1e081d929103246240790001d10311414040c000c0d0200b40850404442c18100d000040ca01150740c40745d01d010038940218007424102d03200540c40340340020f580301c101d100260242c040c4940c5c1d039084903d000c9003c00c00499903541001a030345480b101d0104090008200303d400d125401d11300c0c1d005800701c1c07820041540c00c04050042c0c0c510504040007200c0e5a10821380010303446500400c0003821060000301404002c0c400d04640c0f009502c043c00300c003461403401c3ea021140130300c030040503903a002a0021000f58241d208001500a600c162451111813500e801c000e03400901031a84a80542c0151910f1006e0001c412050012140388450030300002341c081000270740061 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 772648264 1250 772647014 772647017
    0x3020a03030c02120c0102071103070605090f130207030905030613021503060102010219020606041401030503030402101101230606040f090504150f05040c091104050d052b02101a010c03 81
    0x564611044e0a14001804204130030f1000141c4828041c01c12070388000340322441c64042d0308010307010f0040079400400c4811503281070f112407481010380f00108101640050f0380c840424400300d103103410180d2000c0b0100c201c035012030407142d0316228525900d005500b900d500a6001406040546030700740070f83c000e142d020005000060400800d0032000c02c021010021903c01600720a04204051806110301b09811060b0314003000e056045994907a1b0300e00c40504068844e4030b03003000424540340b14092110316040d05000034010304000c04a1071340b412842807090005c00040800140080c14000d0544e0100c60074159021800d40c9050003002c002c10001e4030665074800d40e8200404100304900072000218a65600001e0b9840c2030b041c04806d0515580100050a09015007428034410201c01d40d400c1c0da20844000c021020180b420624240006445140d010709a40403c201e684501d01e400d40210819002c1d40c41c00102200d000c0c0032900c5241c3c02a07500048804051050b5218450800c1130074401e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 772649514 1250 772648264 772648273
    0x60901180509280506101101150b0403030e060702090609040f020405040c0503010513080d0c0c020a08060f0f0f07111e1b0306060d06020708120c09100c03020a03030c02 74
    0x158008a02002c50485201114150303290044010010071450030940d802d14200c100158105072000610702c80c41455918100110169405078081081d40089510700d07200c4040c0545640e01c0440700c2058101c3e2000b903020469035074889019003410780071100600da00a1001c80305e075a4420402c01000700280003501c0440d83c403082540140c94600c6528001e600441ca01c041140c0b41038100f500350341c00104a5130042103440076600000d900003040e9a5918040100030403411b0051200b2a03240441c0381019501c4458036800198252000c00e0250084c910281c180326917503103410003084d40f584280c802c0d8841100d5900010030240c400c2d0254608280100c05941c0c6603404880742482c03407220388803071414030340141000e4180000c26000c44144c896007a0701a14140c0b03021000034000039017403a0058400350700012100c0802c0310038030481d00125811a047c0e000c81c140000c038038200e82c0080f841a401024a0039441071564003507418140d21130341c141e00410000703c0960b0100d015045504155007503124 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 772650764 1250 772649514 772649519
    0x506041203140a120b0105070302060a0c0e0303190f1803031407060e0105071215090c020f060f07200604060f0e1b0406060e0a090c020c0603180c0f06090118 69
    0x11808010807030f03281140c1d90a660f10b404500500b088036040051507040c450104206030000f500411015400104600e00143d548040d84060341c06d07556048031560306000000b00100427040e1018403400c25229034ae140104a0010407048d501b0440141c3c01450303591004004200181c45044480045503c0a041c10700b884c41982e500800e843c942d501c1c0340d80300c4e51901c0401c2009684a1664401003d02403401c5c0310340c8048440e5014204047e000e485070143e10341d200845080e0081001c43d01c000f003440100d504516246025016a40f81500c01200007410005100034a421100070422100c0c01140030b00001e8a960392401c0080000c4166120740b02d4580008400c17600043c8150882886c4000b24400b480d800002000111000c5811140a018180c1450041510784049210960310a6031000a4003946400160300d450368800b170566010310000b04210002400c0249801944490000c0700c1c0041503000800c100d440302d0304007840d082001402050181d40c4114401042c40c50f81d000e14001098 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 772652014 1250 772650764 772650797
    0x703022e06090e2a0118030b10060e04060302011715060a051e0c07060809030c060c0c1501060e061b030703030e19050715050d090516060203040506041203 68
    0x110760342e009080307071551440c010205110504c64031010000403121a5000700e1241590548002e840718140c0c10814404070082c031070004a90544042d40d0040c07000c1889240c911003440442089000c2c000c00200f00044a01031814a0700941080d680c0c140c60742400d801b00414694880c2100820b0180101100450085030380c0b9200020304030b0501c1039135925552000312080b000e00302540116441d55110801402c480d02c8004600da1054070b440c0d183c81821602c030254442c1c80d5014505490855000341014440180071a100400384403d20358143c0d560301180102c524038100d42407052401040c202d58201c03540e860050001d091040340c84140170300d000840d440c55072568001100480100f60348201d01d20198404208800342032420041c6000030707880c66500c10340c503091031740300322960410b50402202c00140190155046640425410420000b41e410b0680d51490388441d2203c990701c1e040f00214495101104072400e885014102c1d40c40c0905e0300c0101007180034503d1040d400c010744a2015041d11 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 772653264 1250 772652014 772652021
    0xe010804060209011b05010b0114070b060d050f011505010f0206090d2001110d0513030f0f051b07170723010513120506060409110d0519031709030703022e 68
    0x5c2d400f450002a18404c450700140c0000c254024001c42d2002c180031002c0081d000c3c140c21a4040401d440b442d41c2e4012501d4501d00d0300d4030f0f6100b407501c15401e100a0b1000740600203060012100240d03144031002603644410381e283c440680f03800c11950020b0312211205809003064401c0810103907840d03065250390001c01400c5407040d07101c0080d58100022203034080031290240315044021407240d401311041d29a800b03404514040441010310040401e007103419401401503400c2c4101004c551134007260b400d0f09490300d42a16000300064580500d2143c6040a0006264420b9500100011400304450890481d4100c44480b0f040d04010301001480b800f0044110350400402a03d0540c07c4002080d14040b420041c0090050740610300e03007100c14021401d60505118032050980e04607922587c94140300b820102c1c1c0b1b00da20100300640307100b041d040651008800181050700440b049842e01c41d040617649038880c141000d801a4041c031946074100c0c40480c06c900350722404071003096044072140e0721481607 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 772654514 1250 772653264 772653317
    0x20040b04050310060602031e0904060b0c15090c0111011508060114060f0f090a0302060301080d02160b031f050d060207050c030a240f0504050d0f0e01080406020901 72
    0x220010900300000d040070400c505041801c0c0b01c0900a45040c140c000307559000b0007e0454034040b40c0701404204c0c090b0036040700c9001002620520103076445480c00f0005d0b0780000340385101442100141075100031141c40ca50300558084000c1d1400c5200840115610307018261101c405550310481d40e00070440c000c9028008001c2c1402400e1607601d40b5a00c8102d42c215002d0450260b0010030201781008420307012108003d800c8285180c40d80d41110200d103680d03140e5000250400000000410500000150716581e00c01560850356071849010242c5081142071054600c103410900100320015001e020703007030040c500840c2c15140e150340c41002428511501000366081c036400103040007401010f0102100c40c400540091980040c6544c6003004a100c841250386a00c2c95045410700c0c01d00c50f0780001c90701400030a014007560506003411504d803c81e0311003000210f21081d0101d907005000d5a60ba2102950503160344030180e8454484101940c80180418104101076070900b201c00340c0b0358002c020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 772655764 1250 772654514 772654529
    0xe0c04050a061503380d03051b070e06011425120206070c08160227010609031502091503160807030e28020d1202010b0904020d062004 59
    0x80052804081c0710020f10001410010981059002c48480403680d10914000780413041d806001095807082c0c01e0906000034035a0b9000c8195000c0b0310070716a2041c05042d085001150700d110340803c0c03107030203a941e0380248110b80c0c195101b1800280b00c0d43c00360750811512500404800e250400c0d491840c42201003601c00800b20301c0c044420401403090700700607a00440780e1400100b406050020014000b540c3c40900140844c200040c030042d000e545203640401a030b400361003441c2c0f100c40d901902c0d00c412810090381c0756081d1f548000003502403080900e80c00f240c4d0010264160240311800010195000131440e540015900d94518011440c2030003e5204044440c81c3e146c207282d04500040403204040e0030f103800c25041c00c23070a5685000119400d00c0c44120050030780c20241020986c0c040e20042c01401039805142d0070710b14002e1090400510102a100d6070080020f40d44440c00c11405210954020750010210342d41c000000300315501c4555100b44184100000c08200320f850322055000d5003140c0e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 772657014 1250 772655764 772655771
    0x2040605100f080f091c0329130b090403080a02090a03060b030c03070f05010309140d0203070317010e16020c04020a0302070c120305310e01260705040e0c04050a 71
    0x1202c00c1d41c0036242076082890740f088984581449141e41e690303041070014041412030030000700f9401d2400381c0c0c00100b03020340004415143c2e1070310860624101040d82e025a0240c030218040d407500306003900c14046400300003820200b01c1e032580d0310300316451071006011000c02542041a80e40c540e540c644640e00640c407444010541111500905080c01981910240242d00c00c60003880b9084290020b0002d940e020f10700000e420450b800c1000401c406046020103500451100d41c45103030303004c070050000a01035110859243c01c0304040842d0828240b00f940e0300d0240c60004201034610000100d600000c10b8811510b100c0140c10002d002c92348144019408240d0001d6170320108903c039a09500100501c8204500ca01010b403030140c160703c11075641150021011014010340403001030490800d042548008403ea81c8800c42050442400c1c0243c6014568805181c40307102c1c0358200d048081c07405080034080d100d241006000261059800b200c9289c043c01150b003546031070398801d840c401e0081c8400403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 772658264 1250 772657014 772657037
    0x71e0e0919151e1a0a090902040f05180d02030c032b05010f05030f060103050a080310030b09030d05011707170c041103070905061306080c1204030e030606030106030209040f0204060510 81
    0x40116440d8250081c000c4540448041d410b0742c910000c4001c480b80086d0120b1094424400035005041d1160086401840c0c403050105031145a00942070024004040701c8240030700714800d981d6400746408007000e0703a008100e11081c0010800815040811000048209482c801d142d4410f89500343c001c0441400b10600801c0140f6042017807060288088002d010781c0e50541c0c80b0591107159000024210140000120b84d070350800f0f52000000790380141807854541441e0742c07002d07103d601081c200e43c91300c1c0c241000412407500d801c0141d200c0c858040000d05d0020301d0400342101411800010b0306550080c2440e5401980f601d0141c0501122040507140e640e24050348050071a00c81600b09a0094005000d4560407a81011101080d10380e2401d000319665180e600034802c6200b4005038821008401c000e120401d81c114842901c148000c03000d80315181d460b101410f0886450348000782d481014200403d0105080c50313513002d4880d001074000f28045440d00041703008458490440c030b0000301520b912 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 772659514 1250 772658264 772658321
    0x40b0126010e01050907213507020f0a050603130512070c03060f18062705031b06060109090209060408240c040f0902030603010e071e0e091915 63
    0x100014240c1d040b40b4140c141c00c2200c0820100321403003030043c10170841c412071401c43c20f058204135002c0d50180501c11461005c230300181c2c006400100c001c0b4040d02c1103a04102540c600400a4020b4960181100b82580c1c1c5118603070781600c02402003610940a000c004000080d11080100500c5008a0f0141072440c514070f4424201c5200c83c46100c069403502c1640084400c02104010741c0e190000c1001c62020004011820803030550700e003903030180d02505c1120341013050202c003819100705109001d0310180060050b568441130200c03591400200a400d0901c03400c0d05550242030962000740c400d03410680c44e50440341c90442c9012880805031241000054480701d610b0f141d42d40044040744860800b4a8109185190b21060040400e001e402100081c840d4400758400c19040300f10200704c1e60465660809841c540d41141d505600891002e080400d08000c0c11601d54000c0704118001c00700402e8501c0724100078583c68600b2500f0b42c08036040c0d42c3d01545940900c0c1011a1110440000080075600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 772660764 1250 772659514 772659523
    0x320070f0f1a0d020412150c031418010e25080a11010f020a150203070210020c0d20120324100e040f0504050615030303040b0126010e010509 62
    0x404804100c9105041c01651252090310102d01c10314290203407980e00342d01c40a400f0b13009541005850040c10f90003802484140070484142c0d00c5041810000b40c0c0921031f00b04c00352a02c18182c0d080d1501614045419000c61110b610102000f440001030119512035050303052030411803202a15001d0f240071164910444081d080080401d2801400d10721240d03030302c40b000c80c00e0f50030b0007505001c4140307280340d107180c000c0c46840495640101c0007450f2142840059009400503203000c03005108444030020015024400c480680103a4402804c4150020030110351042442c000d00d10700c9298030314001c0c81e0750340c100030461503098450b11960322890481c440392222030040da0070300c41d554003607907108040c0d0b1500100d00b02d0080407850800328005880c00071074040c02e601032640b92808d19040800003806030210f070300c034001e0340c2c4408101200d203031110130541e5900003624040c10440c05140100309007801c00e40c4031442c8603e509000060281a000c9150840f42141c40c6090580d44070810094283c80900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 772661870 1106 772660764 772660769
    0x70806072c122518020f070503030906061f120509070f0803031501030603080d050a0f0e0d0f03020f04050f181314010908090103090320070f 62
    0x41c061603491820b42c2c3c0540c0c3d01c1112201c0410002d0385010742e0380480d02d80c400c02424600601501400950000c3d411034000c5a08202d0b24000a1040c00903602c540400400740850b85400d134240090040c04a11542d40c0e50004c1d081000c0711600459090840341741c4010014540c0c0d10815010700d020707400d0300b199040078611240000d0340c4000000031803107002502d18840c42810031000540c15191540070061180c5000d0080b540d0b4949030b03600583e4405079000000c98401d0460f24034200f1283d40e1800b0703d81c07a8101c1d100400a00d038110454650302d0009140442c549407000d01009200d0050703021315440350f00342c0f00881515035907146100180040c92860507030541481003500100802612080302d40700e00042c0703642044a0188181c8132885d070841400c503d01550b9400440c0102003041084091044c0040381d00800200c0451680346480f4407001040c2c03450418683d4200c901855 = true := by decide +kernel

theorem cover : BRFrame.Cov 772482014 772661870 := by
  have h0 := BRFrame.cov_init 772482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 772482014 ≤ n) (h2 : n < 772661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
