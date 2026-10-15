-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3904
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:00:51.57081+00:00
-- url     : https://prove2.me/submissions/52602d2e-a254-4c8a-a8cc-8e4422dbf01c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 701978417 ≤ n < 702158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 701979667 1250 701978417 701978429
    0x11060904020325020a03200718020c0f15160e0306040c050102150403050307030c030b030102040b0319091a09010e010e0c0a050619140c0708010504030801080c0a050906010207 77
    0x4144280d0800500c0b00c1d154040b80403074036101c2443c0b001c1040b40c44918100c00640000e0704803805600520801e0350b062000b00d028001c070f60f00a03070740b81000c03c8003950141008201c0c0343d002c240070102c40000c0c4180d61418081102410300e40c0345000c11940e00038000790030741c0380007450051602d280c2405a02e525200000041c103c5405290030b01d0a42800c2030345000e0304e4014000e1982c0104200c00d01c202882c0981c6d40340e211036040d03039a00d0710308800405048888000305034540000245c140c80a1004002820340c0440441d541d2400c80340e000c150700d1500514404043c544503510f0013144510300e44001c0b07074007200101e400e152110411540504070741300602c0415480c001d0040b6807510700013003690001c041590196101c59903041000202d0051094803460701211000b40003070720f0f100d01105040c91410706a2941400d041d02d1909240651640080c1102e030b40d584140300a00d40c0005159006003580b03070041c140810580d0200f0405803091080d94042c2c0040c0b00420143e81c0248006400307400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 701980917 1250 701979667 701979671
    0x11706090730150e030304030e040209210d0f050a0f0507020a090f09031112030109181b0501140702010e010806130903050304021908211902030d14090a11060904 71
    0x1809041003c20f50041c540c0d90020f140c80c100016213029000f00980c1e00c1250180c960b0200c0015041c1400003960000d4602c550042c510305010302200b680c003400d20b07500000a0010318242028400c003038400c00024900d102441410b00810140d141d100880d061103203114a0800d0305c0d008a031010aa52500c0c6811040926040c070300000003100c0d4a42c0076800c4c0c1030107030b42c03402d0380b0f4581c0410311070b118001300038990f4140004200600030100b250704440403405240e4003410805007242c403803960700c0d690401c60062464241c80100072940e440182c02c0d8220740c0a20b01186031900a42c0043c054410621880307043c086c411002501d556240d1301d02031004403d81100303000a04452400410b2a030080360304a01c646528541e400240a56001c0303041030300c0000d0000d00080180464814425522076080c0c04100c5041190005001034081d120307a10340c00c550000c40d1504000c0d031088d010794080642d08500591000200322500c0000580c6040b1203801c80c070010490f01c0d40c0c1000c43e450303101d062616070b0058 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 701982167 1250 701980917 701981009
    0x303140f0d0c0f0e0607020904050307050a1a0f2502070f0f09060b03010b03130f050712020102060f0f1302012a03181d0a1d060117060907 61
    0x107003240c00401c80044296120524148501410380c0c00010028006030080420700c001c900505100310020b80050084044a0500026540b01c5140041c40309007100e10b070185000240d140420000038076040000f20000186614142c01440a04080d0144024178084071401d08000e0f07034020f01001c40034215900c0d4016845840b6981120309940500c1001440c0b45007240001e4074004440a0b60305072044c040300c1ca1b10350b4803841481c4c2c540e520007680c15030300d5807403412602002800c100b0032403000b400c0445190003071291b20f000190400354014130035010018442c08200444070109011a0720180c00746d050f1582c0e030700c0c90004949622810500e15650f40d40d1000c04200e0b4044030b012442d2540c801d907100844503c00851143c0c100c403641c825a16148525a149040100b11924035a400320708150300050f00c6480d40ca000d10780110004409a584c0c000e14014020030840b40c00d01d21545140d40b009210f0390510b01442c5658017118425400d24003180c03100740840a200c482d852500c4010406c1e005446 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 701983417 1250 701982167 701982187
    0x70821040506011e030203030d090c0e250206090703030807090e0a050a180321020d1d010c030204030b0c070602120c090a12080702040509010b060c1b03010501030203070303140f 78
    0x640b803c1c001d80d200307000c03c0714804902d60000412907050702d502801842c10010043d403030401400150800b01c52800840c2000701e80c040d50115282d11655401000180c0b203806030140c8401d402500d0250011900b21008115040f6000a0480304607541460104816130b03455101712a000042c0d000b1a030000c882c1e0050165055868100600035903d52000300400071640305100106600140010042440405500301c1c00da100440007400d110015005827400003845002000c0b80e8900c0100d1005030508060f64070701803404d1044c001c400350b050808600e042e056486011030303520010017881d2100c200213002000c0003440e0301504c1c00c4606451202030301c0c1c10100b100e000590041800f140c051000110000792a20307205940c00384068101e0344142c541842d03502840042e21005207401065074a5003031060079515404001c1c038813002140042c16040d800701c146504044042161244660305080060001d80c0d4045200812030f9454203100700c0c0018200c0040c0d110703000c0c0e0009242c1100b00400d000040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 701984667 1250 701983417 701983423
    0x90207030306030b1e04030e0f1c260912010b030f060f0c0f121e130b10050901330f032301150504090f0204150c080708210405 56
    0x183c03445101c031001581e1710004001d600d030810491000c03110040c140841c000c04d004101903c840400a420400320b8801c41e000319480030383d210201015002000020020b102d00c0310140f26942400e07800128003080000c80324500c80c0035402c0c0a40c4074410300108c03134800000c250f1029002c035101038251100000c880107019242c0758111010700006401b5800900c000c14810202d48143c0d941c4140582800c510380080c906100b0024824808150b00c007049418048030089494480e28035400035106030503c51904420211000d884c0a825441c007007006d11840c1d1321006507038117541807014088500c03c1001ca4000301158900581110914048010301c500c41c1c4c0302860f0305140703440352000d0120a0501c68814107c401014001030341c0781490b001404000e0603003207020109001423400c030742401e48400b000412036044806030b02a00d0b0f400981002104451440e0800801c0c1d141055848542640c451402c5c6110b402d030000c4c0f1800307001800b4000f20074107103e5407146150581c0c4c045030a26040c0340140d9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 701985917 1250 701984667 701984669
    0x9051b06070606081f020307050307030c0c1703090d020c030c0103050601050409050a09140a0f02090619141801060c08091c05010b0916020717071509030209060d200a090207030306 79
    0x41d8900c080f06122911750712030088038003400c030380d0b41c40345e185d0b503030304c1404a0080020325030765420840c2203035050303020134000c01180078002e80d200c281640d02e050604525141030b00303210f10071080d504104040f0380d180d0f9001c40c0b1000102002e090204017940c07032400482c2c4501ca03d80040d216103181805110300620070b50300a810031403007803d804a0140c03509010684c0c9400340d0f000140309500b680c14243c014104602c0306074000b000505000e60404034814500c0d2003005d59040b41040c5000040309980700d182011007804050075090321030100c1d50424000030b0074980a40005419808002022a036580b15496000004109421545c1c010841d5280140c040d2240341d40b054801d4445a022810920400050080c07145850300100946c44c6405254200c0401c0800c140e90b0901500c0340005032946004ca002c2c0d000e02d451743e1206c211a003103104201d52048085c0ca818050260069800c001070032015a0342c00c00b0500114008012032040002081e59176141c1210506034000b2542004058140e08640 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 701987167 1250 701985917 701985943
    0xc030702010e010c080a030902010e06210a02041a180603010306020928060806030c030d0c030f030b0607110a0902131d04051e01090c0609061209051b0607060608 71
    0xb4440c00028011500c3d511a01c8020700f940004000c41c5000350b010380e12103440d00c0e2040c1044d5000d1030b980c4001807804e4108048684c00080c2c40c0f817000318400704120035603070f01841a210440c246424120700c070350710f40300340b013410003000600041c0803d69112458402c45468001403505076a0341c3c40346051070107508044412070250540c0081c40300c007030848481c10320361032051140a41540e0310703042d0300700c4d0034400c05000690103028094111015440a01c0039102003160382c0c481d1100c07003d00c2c4c90018a14516404000101845c20102400a0359414200c0f101d454102c40d03a0561744020100287d0080c41079800441e0040c4000b400c10461120703100740e0001c4a02c05408074421800c80c4942d84244201194020056040300301d80b0814112508101000007202d00c0000812016a82d01e00c51a0401c607082035000c141d80c02c01c01c00510707038401041d0510701c02d24581400120b0881c2d072100e507101551102901801020510600191101d009490056801000c10300c0400c0da209c6000ba2261424000e81d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 701988417 1250 701987167 701987177
    0xf0a060b010f02010b1c031103030c19090305060402090403050c153709050304033f091716091d0706090b07020a12050601080f0d0909020c01020f0c03070201 69
    0x404010b81c018030900a684401a0000544007854501c5040d0b003440320768101c0030b000300c2940e81c0d110010200042d51244544006090340d82c1010b01b0301005994440c41080704200300e9003014400120089452904568190356010540e00c461400fa034450282c0246100103206071045503c0002d11014090b005654680000d4003401c180c00c1540100c0c041a16001205040c44040c0c81003c9007075440f0000c0b09008c4c80950381020746a990b414440f80040c100d10300b903540b40310603502a0485080942d10014160395034050041c108403070180c89940e6620645004212110600d100f14005008524101101c05441c244840d04c60949800402d4801c1954901e04100e45107500307450310020701c203c181c80c15903c4110000b0319041c2c040345c1d150310200303003283c0050003600d0000394031170b1104980119911410281005604005082c2d290060ba03644c903100a900060700040560b8111000c1c009403105c0d05802b41c3d40b400300c5d80d8228003921400b48030a001003070005002a00b140048050006140300760f80b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 701989667 1250 701988417 701988437
    0x1002060415090809090417030f0f010509010302010813051e031207031127040f0902151603030510080d0c1a06010504060e0406171020090907020f0a060b01 68
    0x5918110303019102d0003401c1c00800c2007004214a08170300f0745030740288200030310341c1c044090200c0d4500c40c0e04180d5600d032109020300c00b400403070030240712030794003500003170b14000714542c51a000245440c001414041e0380c011405000818170006001c101c0c07004012140f128102c80c9012002940da0340050078111150f0142c10105008900c240901c11001880d000464140303c42556100811900e5166480000380c110782c03015825125801001c211a00501c00011380150f2030042c800c0780121505105001c0c0c100708505d00c85212450000501d02d50140340000c0c450f591410402220303002500036072101c0c4108484081440c0c0d00c4500c0d104214450600402c418440d81404042410103481e25404030300c0a000910104d8801d080a40d10725400030030200d00f180da11121107080d000c200410710341c0c94109812a1150a249015049260307170388842d8a1440358801c04030014078003c01280c2445490b00d4000315017080c1c42040140401c420700380540d28044054501000180305030b90b5480c0c0030411401ca = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 701990917 1250 701989667 701989703
    0x1305040e0a1e03020c1002031c06080f0a03020d031e06030b1006140d0c05090907050408150f0c031008060903070c17060103150f0e03040303090506040b09010305040f0210020604 78
    0x41510b0303a80d058009008029590303003003000283c1c0c48192030b0110700c010300c021054001c090080c10640c03428010009682402d00b001070382070210044041c0c040380d0200c0c0e488030010b50700040f040303900c000a00d000a00e05950419200081c012806c00e801450f061010100a00070250729447c011014440407002d416a500000e80d0b10104882181d803001c0414080d43c42020031a4201640c0c152051a00714a09510840080c818480544240e40041d030082000e00550340c0c10000000005078001c80c441c0706180168010941d22001400100d101c04040040ba8444085ea400280900030603001ea07078041c54440381c1207550b504005000da41b50307110110006800d0b01640c03642e130007400700c000103002c9513800d42c0c4400c01c08074892005404501d40c1c525503005003070308502c6100c401c560301a014540d42c038514100148401d400e50042482038108010420010811304c4c12030b8605070007801d001c9829550703030030310160342c250002021350001c2580495000840c4c1c04241c0d14480d40c41603482c100d02c0710000d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 701992167 1250 701990917 701990963
    0x503150c031b450f010c0519060c1b06020a02031908090d0c150506121212010b0a0c0b040804180b0a0b0a0c1103070f031203110f030a021305040e0a 65
    0x200c0b071806020b85822015200d05084181c000022018100104140c04aa481c18a4041c3d10300f0000c1c0c01048c0408120f08103c00c42c011a01d1a1525150178041016010200c2e6400d6840450040c21140c0c00100d41204a00034030035100765800c0c9012f801220900e1100290035003008640b0611240200f90f28202d1403801803c04c0e000e1650000349a881c0c61010403602c200808000e440541c0c0260801d1812000303510800000040c010348900d4591114560250815821410303000032200f500180306104005070700c5000750b15000e4121010900356140c50402e610103104130303040188030304441160b0340740b07554090304403400e000030030740d420b15450340c0d03810040241d802582910b0300011070074100080800c0006e6008005d1410040a0b40c40c110750b18010f07070140c607002e684116060140a85545812038046c410320001d15440d40e4400d14010305c0d178400f0904c1c0c1c4001802129840c3d804524030302c110a0580d4054054400a4003c01c44a00c0d100306a5a0754441050200c07403543c000700030a541c3e09814 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 701993417 1250 701992167 701992267
    0x313110301200c1c02030c07090903020a0f030306080a391707080f01090b07020607050307080a0207021206010807052218080403030e0a0503150c031b 66
    0x1403144480b115040341c400e02c1664410403988000f40b1403400848501c0344007860303140c00071184d50020342c0c1c0c032401c0c100d40c9801d010300c0da27001c40d803981d20300441c080c04030790003050f018039841e4000b110310403c04507072400b6801809c8030340206100d442514041400c2214204000601c69458003800e81480103170f4031401e56442443c1c007060078100300c0c1da5042110300c4070400c405503540f1a500941d81c80319111442e0324500412007441d1302c900c4c0e4581d4500c00600c1401c10030544c104000e03102400300f610f0304143c090f0482c0300150000d0100290383c070024000322102ea05413507050f6801450b0340915a100c1002c603039181d03001c0c001c520007801205800556032070329180352075041d25401c051021204980101d04000d018200c0c1020b002642000d04200268060700208040c51080d2a17400481c0d010350240b0101c0c4620313810045c06640501c00040003208004a001c0d401801c5d6580b2568907500c2e090402e42000b00201d00d18004403001c18030346961166000410070111142d10200c909658405c2d448403040030b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 701994667 1250 701993417 701993441
    0xc1b100f1e0f32090d0f0e01090e070c0507050a1a0304050313080703170a02060a050726010e090118080703031409030a0807181e0b0313110301 63
    0x100c5544007641d12819005850820881d42001506034421034144841200c14002c000c10300c101181d040a0314000c50321003d400c503a180c03008101170400b60307030050101000d03940603005010a000e4080045ea106c0d2452402910000c2002110340c2402e40000d032441401c41c10413034003405202404101801c004103c0000c441002c1315203001030b500c1d43d180d10301da40d0001d84291401c0c0002c014015002c5c903042c05010082481741c00824003a460342c01c0071a5844003c1d1407040600108001c2010010390000b0780c580c101d100f000e40011181c441000c152601205030b0019501890510f24444031031440032203440c102d9030150482c0d00540c0c3ca1202030b0b822205110800c40200000b44a850082aa100098600705119050002d044d1200d40904042c424003103404031072607880042c50781101d0354004c4541d50806c016003441800b00d0f86020300c003030b2800003d000d04804500748103203070b041c202d202c5502c0f1001401c500310341c0d507605e080c40c1203000780454036000b086d10a4400f90b44c0b49101c0b800c3c14401d14450000f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 701995917 1250 701994667 701994701
    0x102a110306160c140106081c03050a050f0606090f04180c0803041217040506130503150f0106030b04021209300406081302100201060501350c1b100f 65
    0x815548002c009410b0b00b0f01c2c031303440e50b681c1d50300826400420000b088101e4494101c07001d140076007138401800e4850040a08400c08e050005108514240403001134012404484660325002003001080c0034032281080740c1c2e4014201044901ca0b5a260320003030000034054500c1c200400d4075008080c6d500d00c5184161561903800e540740b070000c2002c1742c9410514110400c00d1a00d01913a94001a1050300035030b54030749102c02c001c403003004503180410071400003c80c0300441a02e5864100c000300301020301441080207140d03c0c1d00d4010700c0c2e85c0c8c45604a489030a4410200102800d181c117401d965101d2510400c0003480007441c0c003004042041040b080d0f490305408049242c00d0800d0422180390101402171018444011a040010b036599011200260560707400020071920f004001804194091030b0022000d66101c9001c003140108824800340c401703c4a940c0c9490b0300c880000300c0e400d01c2100020004520f421400615522020821142a4524510a1283d0681c0084000854000c803460109e541 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 701997167 1250 701995917 701995937
    0xd0c02120f070c18021903090302121303020a0806060102060c070506040204150b1c05061e0d030c080307020a060b01410d0e070e0105102a11030616 65
    0x20307500070028022584102c00702410140c0d201140d102040e0f84101da20203d40e004105d01e034029034480540004a50146001c0c0510451602c0282d21054410401c948200d0b00140801d801070712040264010340c1e02521280c0b805964404058440c003050311420300500901012844030254081034400643d0028041c0ca032a0300d542c2d00300001480d100c1c20131410945203100c0054586000f0000d40507894032982480114800f04c403d103821600010803040c07103400c80843c03203400c02540d40000d10b40c1200c1603562103010206410280c651051510008000074000030801031526804980003110a12541c0140100c3c0c0d001c1c4010f58109103603091210300d0304024000214155080415081c262002c860804c40c0700d803000c8a200c034207502c1550f50500340c81d00c1b00c00e4191340c2c420402003031004040c41c50880080d541841c00203508030360540b01640400c8002441d908180a102c2e0705e40c134802e07120040045420f025454441248400d008445120f4000e2000182c49508500c601e01e4101e4081e980d0043c2c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 701998417 1250 701997167 701997187
    0x11e020306031c02150f0705071e020a06110d05070f020907140d06050112050f07050c0102040e01092906041a090414092812020109020d080d0c0212 65
    0x2500000c0440ba410f00c00c5100c0c0c0484008421a510901e01180d4042c048031104e80002500ba940050840003c0f2081d44081115290b806802c0d81c82050f48007a003808545500f100c0703d41e0f8040c10200295111003084000240542c200c00410003038280d03101599240e8a44400941d014010340002500213086402e010b001480c21980b01d503844985818990007030960155031040c4e94000d0500602c01c19920801881650f0b0483d080d4050401621800c0c031132442c12000d0b0760f0f952032000e042e10080c880b000c103103845591070a405035070140a018042154541e03407260b8050180c21408024020000c9500200c03810744c4560030621509400500340503c0c00c0e00d429403801c515400d902c250040d10780c050240c40380b45c0e9600d010727080581002c4c540da203002c0d00700040e00e07900380103002080010721400c0c2074000c800c105982500029064200c1d6009000c040c58110683c0546400e10000b51b2002c61a0811004c2081d200701800509030f10407020042008100000c1e6503840750034007601c0705a007040c040c038200c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 701999667 1250 701998417 701998421
    0x5060a270e161505180603061c11030f01020306060a0305090304030f0c05010809191101092102040c050307020703260c0106091803080c030c070b01080303060f150904090c0f0801090b0603011e 84
    0xf010001e2701304440e003004183e0318291500c0c0014200c903154198410014289030400500444182d898021031840c20841c0008599100328840d010906031101c0001d51545002d00907200115001602d201d0b10800914100c4c0042005003d42400b04240e030012130706c0c4041c00521000c58510502805458059584441c40e4401c2d01c40c101c40e04115010102150280c2c3c016050988400b1f1006140c905031910303c100401c0d1600703006407d0412409204000806030300040350803c0744e4000340c1c84100004820118043c181d6404103002c1050400602031580107015031029044400c0004100001600b9403441000600303000d001800040d4500f01051008207203000454000207500055840e120041c1e951495004007640700c1542c940010080151038240345400d081201c2c400c43d1000548101c540300d0001318064280528001e9a88402007c1000030070141c120203407140fa80d9140c01c403a542c440c803d010f403841e894100c6040341c007000410b0356030405000324491204400c2405030b51800303105100c80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 702000917 1250 701999667 701999671
    0x11d06031b041104080604020f040203091f0b0a120314130e0a0608070303020615060a05030c070203010902031906202b1e05060a270e161505180603 65
    0x81d02070b036980c082440300c60382c48000348005d240d0f01c03015240600e018010040c01841c5821954001c0c6d00410410900744008a1002c00c2446185059030341802c0111031031005040c6a040260403400300140890803500c24040007406a100380d49018a0000140141035140106810102060b04044052190704920840c0326030095210304006011662070141e517290451590083d005604103200384030f03459007100c11035040740d0000d4903d1442d0030341c0700130020000e2000030210747ea84500450f8200441d9800c1d04040d0403560010111140400c0d40c0107010100e4044003801c8031118a0000841d40c0b0602603500014061401100c085c2441e807840422100d25a100621419002a91400103504642031088c086541400c0d42d450245400d40d1600108803140038022a110390700c0c0010070401c0c4242c0c400d10f0400c41e90031411074010384044407050b5001d05080c4c501400740d4011804075800101030500c038201111032480d00c0c840c2e0002c02070030544481c41b500c019002c3c2c45405031855201418482c000710303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 702002167 1250 702000917 702000919
    0x20301050909011a040b0f031c11010e071a0702120c041a1c0f0b070201020702042703030e03120f09071203020a0803041e0f02040606090e060907021f05011d06031b 72
    0x1400c04d03034528001904241c900550038141d8003201c802210010f074410a10140d06410800811086001c1c0e816a40e83701920b2061150204840c0a0480a001800151514070758040d001c103002840c19498079843d1500800c8881c0518549800384110420851007441c0700c0b400640000113640c50f0a90180384007841c86410f070b80d0840c0c030080e0000000d0150740300303030b2040702d0942c0016100c0785503104001c10303503070100d00d0000300b01c100c03a107442c6010b8990318010603565858100010800130149045045000b404044406410b00c402002648a03489000611139510f2001344e555036921142c19440201014034040d0069200190207000a1040001540c0050080c910051000c001144411102000490481e00c88030b4a401d000b046042c5406010040d11803418040052401e080c0e900d0407043d001003d0314031480842c00401c140034000d0182450001c1085032040003114032841d1600035010a218003180540c5290301c500ca02100d503407288c0c0c041ea10040241060401e2251081800070305c4001c51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 702003417 1250 702002167 702002179
    0x618021c030f0c21050f070b0108120c1f06090903020703141501030f033608010506010e130f0204030c03050705150a0c0201021507030f0b060a0918020913020301050909011a040b 78
    0x90f07000c001b8003130292941c0e91240020003e07540c14400224201040b090868100039028008032080800c0031961022801281d000030300d2150403050481c0180010768042a481440c0030750b0f038414185c4c00b1030464203507401502516032aa0000c0d6109035903084a520302c02c0885a01e80c014030019400103040302c0a14003900d000c2c55006c0e1000202062803201740004d1680e5502e54101c01c000c0928545034000400703080f002040b003460400f002074407408412103414490680c40c14503440182c07266000d01c0c003e41200004546603a02c0c0d1071320610048413400240c82901c10b15000040c00e1401002005040480d000c0503800c5c800a00400c0c2e4001b40340407012030640c01640c00c90404010880d8a9034445c60030342d9000310b0400341c01d140840840f0b43c00c5132801c0c05410100407850304a07801c10843c0c1c0c111460030601d10a4003e030407030003000a00a81d0941c9a1002d803a07036507001c00c0c4009030041c5068480440c4c901074241c0342c0d901c1140c201e400c030480b02403090020500c10a00380c502a40f0906050300007801c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 702004667 1250 702003417 702003427
    0xc060a0903150c080f040309050f01020111160201090b03060310051e07020105070e15090108071209050d030b010206070c06020f0d1515020303040308040618021c030f0c2105 76
    0x16602000b58580748050286942e851881d00c01a0701400c0d0310703040035982038500381d5820700ea14000c08000311b60041c00e00500d008494103a09074802d51104201407004851681c40d0142902c1c544156030344a42e0503030010780c1e00c4502146403480d90040744c1c080c480c000c0003480312440b0300303400c0b03c0078080c001c11160303c80c01d00b0490110314050748040e031481220680c0c00010303140790200c405041030010101090044500420361080d00341c070720088a404480c2407e29007201ea5602d03500b211090081714034061454100320103141009000900d442c0c000e4150748090080038814001269a01c07012141d00001803071280c40403010911130b0380140061186002c01c0303440e00c5040032002094480021241c10542c00b0000200320019045070b078403244421910285140d803d05460040c5104400303070010740301a5459034110500300700368001c44c0740c560380138040d482c44500580084c8400128030200b5400f20341503030003c00000b403054800c111810350240c05840380740c0c2d081a400c0d11140681e50000181700e41040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 702005917 1250 702004667 702004673
    0x618060405071b110108011a0301170309030d0f1205091b0a08011508010c14030703270812060406060203121308030405030421030915140301230609030c060a0903 71
    0x11040c2070041c09003c4d00c405001c00b19000610000c0164000301940b0301003007600c0240804402124112000c9000018124588140c6030303017507205003662994180b14812003035100b139400010042c4100c0541e02c1c1c01c00c0c440030040241082d40c0c811550715000360080c00b000d0412800840d4045a00d0707202a1a010606446140450842c3c180080c1103c00300f660510070400312030240520848480c041c604890461824601031405001c060054014151164102040e00d1100c0d0740810b0618204000003581d100c003414000b10942c01280d58a442c488104000f44643c2000e0040320100d0b003c0b54000d600e00100c00ca0b5621071003002901690000101303100043c0418813071005140120300803000745030303902d10f00500180d0198101c0a03c200f1409014500350202e500201880122503038203510303d034100e0001d41e040701c410744034401104500e40b010002041c078050000582c00c80c0d03031102c000084080070344000c02066008024455030706500c0721000641c1424410080d10b405c044e2824044d038810f88a079 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 702007167 1250 702005917 702005957
    0x51e030702012703021f1803030509010f0e0c12120c0c0102070906050901180209030a1b080a0b07030222090203040209010b071205221d061806040507 66
    0x6a26a030050703464103801c1055004000500c000e41040021060078041143d0307019444070708a00c00668010003280038101100030f15044002c05500c1c01c041c14400c0c0c1c040d071070041e0042c001610001e070290b203441304042103010144180c816000214008000005440e8100000d4104400310f10103903000d06800d008141000e030003d482002e0300100a0030410380200002403412002d80c0c040e07012281010402c0001d40c680e810610705480505800220000701c039104000070344503c0c1c501d56014414460b441e414040d0900d016080c0c400f81d00c079080542c0b665505c4e04d0740c0c8d80307480700d0001c4d01e031605c078602041c160f50003640100310361403406949031712040950310010000c2c1c4e0241e11282106070000208011450709502403070140900c25495424890350383c442c0c035441c41c92403d404040c044d000a240991004c100c0403482e9401e0700c1e80309405641c3c0c84416400d11407201112007800c220004001c1812840c0c07607030a0704071800c064818800781e50344031001c20024080140c00e04050100b01c8003c44480d807901 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 702008417 1250 702007167 702007171
    0x21e0f1603051204060f030b15030a0e160501081609030b04120806010f020309090604020409021c0605060309060a150b0703110f010608030a0302070c08031314030a12051e03 76
    0x650500d203400da00e181005420403044080c010940d2a0400041c130215402c107000031040019481e0005041e850100130a80c2159500451a5a008084100f2001510603000a00d041002600340c41414501c201e98034403211103409a00d000c1010480010114044040410343c4050103140c03981c03201c0d030340791103a40104a095030203595250003e070924100b01d4014900c10740042d0b003813070a040440b0080d0b10007500c1e0700030350078918821720504000c19a40e5855405603000f519050034219a039500c107468000c980803210480300f43d41400c1c400002890311700401980d102c0c01b03000016140c2903407041c2c44031000781b00101c20082c5a48403080e010aa545025018201c61791080e223031441800c452056103454480795040c104003507814100f003071042a038007006450640303c45040c05030303c0c0c241c2460268100cd003141c011803114172010440e450700b207070315804040071661142d498550100c0b80d201855240c415084000d01002031408010845038031030750040124580310103c004030894980c400481c16441 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 702009667 1250 702008417 702008443
    0x90a06020d09050a030b07031e0204081e01060506030c0c0304120b070813081e0c120702100e06040314010b040903091505041401030b0d0501060902070b16021e0f 71
    0x30809a01c1450300b00e10550050070080303410003101840c40e655101c00060040050041640301c050a0700b031031031904031f00801030941303460030b541f101c1d114014141c1c0c82090300401e007603405650001d0070380c2c114184509400d5582c040d194920307651780c40042031a280d000000c003500900c020000040c40402181c5698503003881410344580c9030800d030000800399000503203030842105514040d140001d1420084403503c01d5480642440c941295212041502984004402a006200360907015810000090841c00c1c4212038041403c882880204caa0665002a854001804010a1011450500c0d00e03840f118048000803071008000c0f400700e0140c40101c10704401007024044280801c0071542c0682d94450858074180b41814034203540d44000d80001d1f001d071418107595820724003450303c40e003402c106aa60000c009002550b5501040c00080d4000e160584030354400c9401700e103604c0150304070900d95812690017490300407800f01c5184504070701c83d07286039420b1081361030002070000140400c50710400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 702010917 1250 702009667 702009673
    0xf1927020d0510050a0e060609150a170a06051f09050a0f0e0c03010b010516060c02030c030301030c06020706050405061e0c16080f0f0a0308060d240c05090123090a0602 74
    0x17058110350050710103501600032142c00480400c0502d407a00c10007242d12114907010203014146810203d070180189400c40800308142902c003410303002c00000c010031070a00c41c00d010821a5a03c20182c901a10040048114410326120410080c2d115400107900480d2800b030005502c0b002e550305000301c94413605070b1400c54101c1802003400b46000e00c92190518001c0c20902c2c9040c0d40f608200c24410020100213101e240e0311580706968a100b08241d40803c4039541c120390740c9503120704110035140240e2103104018400c041000c0740d403030321980035501110001b030201818181e40784c102a030508007801c5d06800075001480b814000750810072072404001c1540ca01520746a04142c0114204205241005883d900842c0102e20b42400010184200c80e003510f0502d229482c3c2030001620758501d44405040c140001030050855401811070400d42d505d5083c08000d03003e00110151201c0c01403c800c54042a1688202d80d04a0000154409500003502d00305140c454214001411038400d40c100c440140c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 702012167 1250 702010917 702010921
    0x20030304171f0c0806150417030c01020309100b010905062a0715031109100f0309060606030b120105071d0d080a02011e0b0906060c030c060f1927020d051005 69
    0x60f40112a06070400310656541c01c0c00d074201b0311034000901c0345204210710780d5102d08143c54203030313014001e56017101c081f600295030b00e080072204980d139400d4007030308089d8140c03030300c1610780036903000701000421038001619950400d46070001c00c254903072040444040340c08080710020315805040c003000d0060310300121100d01c80c5900d66401411030b07415009607001e4040070004000c4980c1c5202c51347c40d00780c546142951035026000d07012009045000d000920356818864041005038068100c0001800181d814061018504030100d0030703103000341d40c4400412065000c500302d01c02e100e80ea002010401a00920b52400301d81e9410b60b15038031041c010030041c2d5580c0064805048800802a00d03030300700709414400040751b200042c645000c0580000c1c400c40c1c0006111001807000d10603200442c1c04401540c12526052030070300c242c1d1b00122100681d10751803d10450344650244030751046088298141403a0100c19004041841c15461060340e0005020800400040b41040012518907544001081034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 702013417 1250 702012167 702012191
    0x4081b10050a0e0a050a1202031213030e0306073608010e010b030a0c050603190e06010504110a1704030207080601150e01050901050a03090c0902040b0720030304171f 73
    0xe43e00311a145045404c504d22540100e20005034241400303800c40d210b1396503500c000d0401da107540704540a60014030b101c1d00030010301c0c40540e0103c0400c40d010b62201a44d0340c0190382055190f00040740c0b400c003c9505520a0000078640e800e441c034646c4105807070031201480152048400341c01d00d0b400414141e44845000c40107000a0007002c1004805600601001c42140d58034990000c581c01810700030003002c800111100641c4556010781520704204000d58140444016212034007406440c1c040c600f0070948042010710441281c001084642d521140b21000c0c40401c0103049000e001076085105184001c105020203006590081440100401c25040402d4021f0b00c803401c1d914659050100510040d60540d800500f01c3d10003010038500041c8810003890304202c0c4552036009510750500c04507000c2407032646c7c2001004441d0150f8010b015001d049105e2908a82548413180e4264000b84001c0041480d01c80c0130510005400066400d02c41e001e00301411070449000c0e01c9448a03031161100960 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 702014667 1250 702013417 702013421
    0x307170907050d0f0516151107090608060402010e01090b0a030218030d0207080c030304030b06091e1006080a05060a03030c0311010903120f1b0c050102130e0f150904081b10050a 78
    0x100301c50f85440c000514604001d40d841f06540006400038055290451000c0d00c2e01402204041c10310101c0400038a40c450b1101c1e0b5031001c08407408c0340440d0030114041050342c050311032142100c0d0501540c130b1a201f60408210040c1d048003c4200c407071041d5509206c25a030b0180407035418514070368001c00c480d40c070f80701c119813811030001010b80c081d410400040c804140c3c1d4a00301c0d5800b0000762001140740d02c8002c8aa00e0034844c0070303042d6500200c2d4109000040e400e00c8040c20468403280d0700c03101c003030f1540c40c0c0c0c4404441003036900a90200d500349003000024000e294407591a0700034104000c0c469070104510b400d490200700c04400042c0400305804040ca007500c40d40129003202603040000040000703184082c00e403900c07048070610040b8041d000401500b50100daa0080c0c110b403409000703075520582040d41950644000c1c1c2c030320620348001031018503a1030401c0c100d0034008046000c952120f03180e84000d580400c5107100c541115200301d250020041040c4101d40814007000039003032a040c450241 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 702015917 1250 702014667 702014683
    0x1303080408160b1c0e100c0f021b100c020a030f0f020423010b300703060e241f0804020108090109030503010b0a0e091303140307170907050d0f05 64
    0x10f8200500c10b6032803d1005504210810140d800000b944410b030155491401556181c00f00c041810072900000241c0e000c04281c82100350307a000c580000f201c0c1214004812812403200760494842040000018410251301c841280041e0411030300c10740ba9140c030301e03140c1070107407060303909100400708802181042d10410215000000d003c10401c003058444451304c51042c0304002c241c40e004a10854241c4001a20200101d410114200f4243d9030340603040c0c80c00000c07506040480e28080000a03403200c00c0849031b106110030180303c00100d5144000d0018600512540f80e0401e85540d81d1100015400805405040154460808a10382440010400c00c802000c40c0120303410003210000203600802568196090799100a484160100049525540b14000f04e0b1b0300c0400c12044c024800b8030003107030012a6009942c2c1c0c2441c1018046a4103641c84181c48582c0050082800d94900c0c82d03a203a10b55401400290568524540d1034002401c01021000300350b58480f8501c03103401c00c2280802c0750035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 702017167 1250 702015917 702015929
    0x207140c0a060c2102031911150403020709020f1308011406121e01090215121005130b01020a05031c0b0901060f2d0c0516030203030a05130308040816 66
    0xa50f802d40e140da83c0da8100c620003140324050825800c0e1424020f0054a0b0403c9019486100028400d44010300088502c04481250301545501c0000f0380080c40c032081c412074050b00104116480c1980080c000c0d403009140b40c1e08440d051003940100c01210444000410507d000401d640f004500311184004000e02014071504a15560343da030040007151540d825009506d5141d400448903882d80e0240c00a41002548544d48885124811121401400a80c072800010008503a138402002848002502074598008122610910f56060305e40140c0c12200c418819550681c0f965030300c0314a19080f880c1403d40d00302d08100090158420380c401c107048010102c3d8030070b5040d458154003034900041502001d082114640260300c078540201c901c0c2100d10b0400045403034a80c3c60160042c03c154032010107c90a0142c0b00103415021307080580003040d2a0010003031882d040e808402507c2c00c1e80300781051901078400c20000800718203610058001000054090a81c07003408003522006880d85810107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 702018417 1250 702017167 702017177
    0x5090d02010b010e101103070b0f0703060509040f022823060412050a08030901020a030f0507211d030a020601060206010b031302010509030d090501030518031206040207140c0a06 78
    0x901c01903a48044030800703210083e9112810354604140031201054488102801b52000080300e104009241210b06c0c82450001044041d80c1c40d4642c3c00ca00345c0f010b61150704e40c012505400714000c10003006d40b01403807078401008050450b130181c1c000780c1c1545034200c04480c241072288003000400c600c48400004004120310404802440f80000390340b0340690302401c420784a00d182c0000820404005203040c098020400584a00d003c51440d8081d6000c5002440000d041c114400048002405034901030701007602c0d00464401c0d0000191503480d280142c080d0340740c1d105d8803140c40b40c45448507045002500c08003c2c50b0342d601c4400010346888810b900c21000c5600100041094a035403009030b0360004034440e075082c600503c40c00122500e008500702301c5c0e0b050041e800945092504401d0300000c680081c1c80c103000030340e42c0c5240000c070411b600c00c41403000c1d04100440c0c101e02ca41d520001d9804400140010308140950f260240d80e40b02c44c030601c6440b58018002115036103882c0b07203040c3c01091140f0300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 702019667 1250 702018417 702018431
    0x5030607020706090909050102090612041104020a0807030510150e031e0d0518090a0f0f0e10050a0608030417070806100b0733050a0b0109151b030305090d0201 70
    0x10040c084ca146204441800343e42c0c00018003000020340455006050003410a0784841c0c8070700306074190a2048e40c1c03c071042c0d184032480020340d0901b40241c54400d42d541d00c5204596980c08001e9014150045c03000840343c454090109405100c0b69840240e409144c0e6079021880e001028503140882c040c1c42e0070b030b0002c44c0000010340b0303010011b06090400703581d143c003980741c0b8803c03460904500d150030640c9900500100400140300895400001105041e04050180d810350300d081004942800a180c00b540c3c0161000840c100706a0300b00d00c0e0041810040068440d0380c0c3c0404504540042c1c001c8204000f104940200c3c6400420000c0054400c45000c1c0810342801d4190142001091158040103280810a041407141c1c080c2c6052203c01741162000c1444001051002008a100c003100c00851410011456402e558843d0080301041078468082050500709400a2070900034500010000f0560500c0e010003441c020b80e030845032007520080b8560800b4250380342020140c040d5002168075140c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 702020917 1250 702019667 702019679
    0xf05060306161206080312041a1b07020307050402040603150e100501140d0501080c0312030f0c250305031e1308030601091d0105030c09040b0c0a0c150501050306070207 74
    0xe003035602503a5414003c001d0000c0d5050380b405064181d02900550002103110300b94182540310480c8598400c095000b0f0f80e9042e664000381c0a032007903400c0080400c802c070100b6402c044460003042038074002401c507000c9658410004090303034025005400000e454002140b0760305d9021076242d0290607881d007060207074504072303c414000072105c0c411380d4104021248103d4040e00358330b086410300e1182c014280a40d6031598181e03980c9441a03a03ca500074814600154502c0941d4020380e030189906c05444910380d25200344030350040d04a50407060050503003203208000969180600204036102e42c448079200d10340080324943c054664500c4024400c110001c2141110003007030299091584a04c6003903c03601e810380100da801c1c002e90004d041e0302821b485076140c004102044203040300c000710201d54900c0d2080090140c050001d480080c02141e500c070114603051141030141c4641001850301c070103004036944422405d0384581120402c0300e541c9030018002401c0a000351540000070b1300090400900e006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 702022167 1250 702020917 702020941
    0x106030525080a0f02061204030e10090f050d030513060804020f040203070c03230d021c020f1c021201091415011b050a02060a020601080c041401030f020f03030309010f05060306 78
    0x1c03c00810500001150324210b50310038058441c83e0050f0b0802005600d420b08c0c0c0a041d41c010710403003621540307116451601c83c504c5400c4030b500fa03507840c1c0505210781e03103814103121802109610072424403c1c1407050031204041d4036030360b0004018950310a4618101401407003819261405824040d0b4010801c0111140e0042000524240d00d031030401030000000707202ba9550340d2941c0180410070000108055420302c40d4020301111b11f01d000040703640c0c070482040301c022407244031110820701c0360030304c100028030601020010fa126003a203809450702c11081008000100c0c240c11000392913a5503581c06d510822202400303540043c2038402c40c0414111040043c200404902a508003541a40e00c00b0041007010f00c003042c0d640d54040c00340c03a00e400e40d2600283d11902c00b401155014402c000c1c9210141c5031500542e842e6000c3c40c65a454070b6400d40c0c842d5a03c02d00d01100a9030030038008040d1300d1084d282000110310401c0144000110480b1255260042e60006005103109510070401d10480c4c00980d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 702023417 1250 702022167 702022183
    0x21110114070c0c0e07020f0105090601050a12050102040509180d020c01050d0c0302070b0405030301060206100501080a0c0201021b06011802120c070317040302150109050f0c0307020c03010603052508 87
    0x64182166010403e29269540380003d41005014410190a002d900c42d000580c0354032446202000340320341e50f601e1000c541c2e00c9100344619684511400f20405c25001341207050007000e800b400000d898151184003140303100750280c1d04400294282d02480000c198144a01001a441d0340b020b08220841400000c015004010600c8941507903020550b82c060b0081c0d0460701c801d580443c00c080a843d0034103102c2d842e90402d00c2000054001c400004801c0820440200c0071359105843c1c01426440d1401104003c1554026400a541d401c002100800c030301034582841c440c000300000e0020798107108004020f0341c66400f802c060389005200542900e0810b540195000c03103c604402e4480006040031501c3c03002448100fa81c00302c001d01403209050713000c1401e25031541e0380112442d659903242a14000c5510494202c170403404400e0100d051407011000440d00030781940f04031203003250b040d40080d00b140d600c3e91086500d5800401c1c15141079140b1200b05d200e201600340c02140840c41c0c41e140c40c0d121960 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 702024667 1250 702023417 702023431
    0x3060103060c0909050c07050c01050a050a051b150a06060201020a0905040506010201111c060b181207150909050c04030302120d180b071805150c03040321110114 71
    0x440c0c81c003482d91803040403c040201980e250911260501a0f201920307980491000d46044c050842040641d501441c102c401d146055031300c50746080341552088420743c204a000102134507424824204000080000c8000e80790400032000c0241082d025002c00caa14aa00503001e41e401030003414022504042031404550055601081590300c903030040b401003481a681b800125030124404d041081c04410303100004081c00c600300b0619131101020410b0b4005c400c0c082c2820408954100420708088481103102d01d414400c6405040e00c2d03585c0303c042101614403000010ba1948000c0100c80c0030340c01031542015810020625007070554400944503031400c80720460101000501011012150340030703003082002e0020a800c100300078034003044001c00a8881800040d412005009070070080b510312401c07514014030344040c080c040c548010391a0402d44490920380400d001c0003021a11044403000a00c3d850030b001034450302d001ca8064119114088142c07016850003200c000b070005000062504410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 702025917 1250 702024667 702024671
    0xc030804140105070210050a140402130902150c0c0d050d0503330907030b091302010c0605040f0c080105040804180e0f061008060903040603050c0408060708061e0306010306 76
    0xe2141041d00d0740340c402025000300796181c4402c114080c0d5002c14040d107a0316004005210703640342d51000c0800c0ea516064003058900c0110082001481d081220b0b042c042a88680030400c0b80d40e580000d21413502c50a5140b143c0c00d80050316550480c0240042035000508480a0b609514241ca0f06680c500409a40c0d000303114001002c40d00c04135420604601060682a0000316003c5001e00004d40305e4140000d10700556904011644880c0280901c01c0f541c0d002415880713150341d6640c42d5001019100000380d0502100300000e0010a6081c06518840c0b030054110201c0d004081c0b4000e152842250b1003004681d15010910000452840032601100c0c050040400169240300d408030040c0450300c041c20803840340c1608203c0c9041c0c041406441981004541113841d903407030200c1600c40320200c5445010343c104000c103001981c0281e00890300126601c601c01c1c10700380c9400c006840c1c0b10094402002203031011003009401d1070001204083d002c10501e4211031100c0c2d101c0800c0d55418180030050140d6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 702027167 1250 702025917 702025921
    0x30a020901090f080307060c021f020a050403020a0e010302120604030f0c1a09060912040e010509130c030f021e0904020d05011e02090a0609050a09050c04050a03080a03060f060c0308 80
    0x40c0c441e07203102010f000c0580d40c90010603075510f0a00d82e00c0c1c1c42440d0071207001341095652005079001080000d103000000715503940403d44020b110b40258400c040350014048180808000b58030b802021030040c100585c002481e95046004101326002c60030003940c10707a407062080100190b48501549042d58042c00c001c0540e9090341f40010488400c85100e0109038880800c001c0740840000e0024000c10582c0c0c1139803900d0f181940c1410a92059002d0220204074400040045090080d1703682d91040d6806d0480582da0590781d03462030308072a182d00a4414400c84140c0c2d500b94038151900b40c20b098191000041401030310004a0341c4290b0062010380301c0c2410040b050103100e42904a941c0100d0042721000c81d003201050444020341180f12110700603907502401288243c0110403088c180caa000705100505450980d07013002500c002080500d050702c06200014042d00d4100024024510a8281548038103031140010211030055000e05550746030a40d0801c041500035402620361134040c9460b0500d0703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 702028417 1250 702027167 702027169
    0x9090515040c03290a0b010e03030c1b030c040903170f0f0a0e011506170a090c12050106030206070b011e0303120c0203041203050a17071b14010c030609150b030a0209 73
    0xb01d25190002025980c601c0100214040b01b6404004907110907212200f064400c1020305035030303014101c0300184a5102d18884626220004520004004001c003120030681c4000041000d450a444044012981010b04003010101c0c02c00f0559114070740444501162401100c0c002c1ca1102c043d100000c500e54440890301c4003042900101c0f80b80c2400803114600685d1010010040980001c1d00c00b020020000401c1c0000207900035030f44000d81140c18a4022828401c0740349581640140c02c541d03d40d644c41e00013006131180320141c0380c1c00e40600d8407042c55624002101a1248494813400315848104006000094106031032055548110400084150f641e0205034a14455908020741109200d103a1130105988a03009141c44042c990721103480b02442e040300c0088040c10f580400109a00c40302001c4401c900d0420300b00c501d4020414005484100251035084034506440b2500081e2201402e012100e414001c500000c1501151380482d43d2414500070024000a41200315094001071a4105 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 702029667 1250 702028417 702028463
    0x40605071b0803090a09020c0a0b06180a020318150c09010504030209010b0d18260409140103060b0604032006040b0c06070e0103060302030d0309060f0609090515040c03 74
    0x403000072100c0c500715151144140e90350380d0000b80800b8400c031100c0c8000320b0a10340c1c5000703a829034120709000304121003055031526803105004000a4008130040040400700240b40c000c140510b490500060340c83c205081c440e00c80c1d14400b200c2c0390144d4841481090068452500c0701d60104140488a8403000340000494051190340d201941c05410701c0c5c0040b41e480380420040040d040320a00401400c10041c09840071250f81c00000b410003003509401d2118914214841581aa1240c0e03240f403520340c4030801301044070203042c0300d0307080e10000c84c00602c10011a0301c04c0c0b10b085072046030b0681c141481c690320402c15040e580410300b04c40681d40c4050101e0b85642003030310b0140c040c907846243c40e001c0402c03a0035036898085551100244c891840010503501030310030300007074940160152900c02d0603004240e0107000e40329812140250f0b50080d02c42281500e128036400780011481c04180c051450815910700100c290054402c402d2210078031000503400384032501165806055a8240e44003010320b810 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 702030917 1250 702029667 702029693
    0x60914031b041121010914040308071404090903092913030c0b0304030311030402011d03151503120f07020121020d1b030b2b050a051f05070504060507 66
    0xa8108404560809407076130070b0f03507112418144070702880c1040c1c0e603a0103440d0548104520010b0740396030020105011134498440d0b2030f445403007401d094402c0100500b02800310341c01580003656035035a172200d0320101030340081d800004203000d080280b074044841c528004483c20041d4941c520140008040c802031000070000401150001c81403441d0b42d5840c892100154000c0310101d0001c2e281c200c2c030600c0c078044c64050781d000c0c64041c2d50391502900c1000719107101240c1220401e92510803a003211a08044921010748a10754600350080210281c0b4241894156800072400c25120288040ea0388103407482c06030380f040c0e602460b15512012400e400d4225401014003846406800003070081900c6180e5000003211403028264038070b00c414612011001c0311004000207500c480b4189101244064030340000b8009004122442d01c80c01c000d03546c0720f15000c00800304a50315004140e02040800e9141800020410184410f00c024908440000c140e48250700600c4213000d0081521070500007c445940 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 702032167 1250 702030917 702030941
    0x24030c10090e0a02040e0a020f070f0812100510020307110d0f050d0e13020306011d04060b0706150815010e0c0f0a0c0212031612020c03030d0204060914031b04 70
    0x100d1070600c12083c0700030794454080c3e0660342c80640c01249984c049882151100c4070406071081c00e12943d940c0b0041d160240c00b005541403002800804e42c11a5102c180c54002c045941580c900c461910062100c2ca04001280d00c041d50014089100412525544c10ba8149411a45c42c2d202c02806c0c5403080c401c500303014019007244940090b842040342c001480c0518031354200e81c2503203a400b204000400b0fa110031581d680c001410f2050511a03007032090310780303c40120b0060000c6000d03601c510020a05410440f4140d41e102d07100e22100d143c00350340d00002c20203401c0e40340151641404200501d86a100c0601c118942410301d000043c4000c0c140d94160303010341c8030722840242c1e03e01c40347d04c0042070782510070001e0b40701d42c01a410452500c40004115003010035961000401c41d485a100c40e99510030190307020303066019000112499940c244001c1501001c514801610340f400c3c00ba0040c24840c0c0340c0c1103444d1440508403985201c0e9030010b428540b0038048103245650205610100b806884210f13000d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 702033417 1250 702032167 702032189
    0x9030109150b0f04110a030c02010609020706050f010b07031d0103090c06080402040e0708100b0a080d1211040518150913060e030a17150a03060524030c1009 69
    0xc0981c5100d02e400c195200041107900e01c500c442c6110420007110010a40380c2668103080101010060190300304442c2d01c12540000900c0030383d0303981d081090383d1100c281220a1642c2d002001081807440c080b0b64050b081c40030340541045056078014048095044a01100c4510305072080b0f400d83c4a50820301c0800d80c00404140380c00c0c0c2d5510301a01c0c1036401e4078124412424200d1180400c03000184400032500c41d480103224440503c1c0c01c1e07c004202180310150005010310b00804d541c1003c1014503c0e480389982d0b020070126005011004583d0600521000c002080004110f203039a20b00508290f480b0595071824103440310f8504244008103140c0480c1c0002d000010040c0341080006241c5400b80501e4007841406010342d001a100d1241501d520080780203455803114503100e000100da800b209103c007201d80002860b00141c2c1d00e08047e403048600684800400842019443c000d00301d0014110380c1c001e81d41e00c05800281c89010090102d406441407021a0728050310440058004000100304 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 702034667 1250 702033417 702033443
    0xe10150503040c0504110d0506030d020607261609080706080a05090c10020607020d08040b0106080c16050c010f08070c1e0605090c100908030304060c050f0a110c01170a0209030109 79
    0x81c6c00e1071a00104624a6250700e05400910141000306a5090500b00f036405444241c0c0c481c00192001001d007110100100301349511040d444040786a00b80c040c2400e00b450400c048500c8000400c2c1e44440d401c00903003a04a40010041181c104c511960882031080307000c902c40c8d40303001c003840c98001000012940075442c20107108009401107200390103000b46c4e03425540110308024060300c103004256001414045ca080040203101e02c9a442d4640022041c2a1545012841c100e1450785011b8902d040c4c54507044548207030300c1981c00c110000b00001650600310034524000b9000740401d6480000035102d00c219000074018003030301600a0003101e80c000400c00c550f0a11074409680c038a0019026801045d02280c441e85880c042c58103281110b50440042d841c542d110340d201c402801c0a44042024804103002540c00500e43c0c030050b000c00c0c0318076581e99035502c010b2069985000844c000140c144811403130280c0c0c55046414540b98049201000960386001210100f40104031000000d8040e5010141c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 702035917 1250 702034667 702034691
    0xd09080c0615011b030905040207020102010914030406180e27011514090103050d0c0302150118060e101e21060606080f07030914070605040e10150503040c0504 70
    0x40e18108407200780c4e00c21181c074044c2100c981940702c00340c0340980400c0e00184200064a0130707030000c3c4400751040c800410180800e80d1224142c91814120442c01c0d000890b0a0101903800300f070388200b05038038400c0c482c400742c81c282d855002e854002e00103000a5003602c003101110264030182c0004510010020001c1000b90444401080c08902a040149002c0d14009200c0c0c42c0902e00d07079059940010140c0881c04440d01c09030f0705405001400c90950203440c040017a1f6000c42c3e28114002c004101044242084000d1b42d0b100700c03810b98100d200129440818840001d41000b80042a144812054401d40b60096980c40304100b0700d0307104102900030080c040e05106250700440380c080f486490f080c4080c5413a40004d071610a4111480c0c54803030600c20004480c2c41c460b4020310b4481d8001c2c8082e141002d2076004503800d002d40c5400c10008107030300190800c900181c00044592142d0354004c0a10345030f007010304211a0f24a0032010004005c0080042014002406800300041000610130070200240c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 702037167 1250 702035917 702035941
    0x152e06030605130504080301050603040501060302030304061d1f03021803100e0607080601052502032a0612041221060f05064e0f060a08030d09080c06 66
    0x100841d40101c0d03002d03e41c000b0000305405054080d82e0b00152240c01d42c1e013818103021480d00300820540349992a0a800809038409100801c041c1642d6581c00d900c12000300190110600300204040c003a1841090081c0301e0740c07241268a02241c05443c0161703aa24920140c1d909241880c480070740d0600404442c1c40c1211019032001c100e00301d00900f074804540d2101c10683c1c00003800c880a0380855420000206080d09000c0a00c4d6a40a01030f08a031908240f90086880c0180004000101782c4140103101000340c003909915011000803251580352103d000e00705010410040d0000780a413403038003201e944890080c01382d50998180d0210011101c20b0fa20110000303404240720fa80803525072a0f201144030700340f1500300c49554461071080c00204511312102c4030020000900d602031148601441980341ea0348080c401044a1030701d400d145541000d10071100441d40240407903100d0141c504040128031004006d41c5d02d1a60080300001c1d039441c0c2400e0000c0180700f40309481d91180201703400c10590802d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 702038417 1250 702037167 702037169
    0x30603070911070507150f0c0303020f030f04020901140102151b030c12060f010507030e01032306040c1b0b0c13180b04020c0a080f13121202152e060306 67
    0x39421a4110703a03a80d5a41101004506d5855002540c0c2000c041c0301c10380a48045035030f4900c0384ca001032030b0000c0c0b2443c031111900203413010f070f143e45180d01c1840f06614004008901502908100100d031010382d00000c6d560300d016146140544803500000341e19406010030580a0007143c1e044580c0d00e1401103220910b90707104641e1404504005404190181880d0f6400011b10006845942c5000c1403920140d54142100c2c441d10304058590244060440070200e246030384203c07000d032803007490170144200f000f81c494604480c420043c003140807a01d2341ca403450700644c0c2c060300b00301440c0361a220ba0041480500c00d80000c122050b00c3c20800240101400d940c1046a01411004100c0362160100f00070aa20810041c0ea06952250301c02c9400310b101a801040c0802100003903d1403c00255004c181c04092a4020507070340c9580600e500501800641c100174a00b03281c800303001c00754070140020150400241c9028030141070300b400b40001040d22110703076500803000c0c1250140c2c0c0b03507100c00060142c282 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 702039667 1250 702038417 702038423
    0xa020607080f1b0c0f100213050d0b0121081903051806070e01030204080a03053103031b06150f1715041b080703110d0b01050603060307091107 63
    0x284000240d00406507005280129043c00e54900780a020401c0b1a00075040081540410b02500c9040602407000b080083c90740030ba042e00160310361009806c2044881d03060f9000301e0140119401c21800030340300031441419101c4034000380000c01d0f16016a1200c10030241001080030f200050150406041d950031240550f500395800d000513540c03009041959200510104450ba000e8000324040c40c2c0915542d0b05480340c10b260040c1010769036014286041120b99069011076400554410052608180401c09201d40d800c5291032070030b44035404807c551144006000c0100c2c90b13075100501076100f000050f0071034100c0020300c00c9010003042910210300300d21902c1d5614445104c0001c100c1c0e0340c41d000040b08504600600610144459182d180340d80c0280116030356101c100080303208802891a00c005006840c0c0245002429450064041848105814450101c07200148005500c10350b109054510907280c1980702d45800020926040301c0e900300100c00d90424800d00f280c0001e500140001c240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 702040917 1250 702039667 702039677
    0xa12051c020a020a1101020a08030f04050d020601060504090b01140310081e030706110906120105010201060b0405030c010f1b0303020c241315050f0a0f020c030412080f0a020607 78
    0x580114640d0403032148000500240e08090000b070041000b030004c3c002481d4042c0151030100c00f0903500c6418903401104c100103c111070405001c18804c08008180c0002080c2c00204802c1d410264050400d014a20881d2142602c40e81c4080203644503070540c2c040c8050f00c04450b901e905000001c12003156a80c0100d1500c0d101d587c440340307400511038a9018070100540003031841c04415807030b450040c0040203d406000103080105000f59201c0c0d8006111081030b00103401110750401000900f901d6842c2d11a8030300d454184014089a139021900100451090030031402c0d00145035029911602e41c00d080681103023052000100f415056002880060404000c3d50003d48100c8181da2507601107200340c4d204d43c4621400944843c5108803004099801510a16103990504202d582503a9048a400f025040c8000c14070200c21014017400440c0b5009050541c2031071801c00e207040d901d010718072441c1d40c400100c200940901c24903404803200e2032007010810b40e4900100e4006503884209441a1000070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 702042167 1250 702040917 702040957
    0x19020a053603120405120a02030a0c0914040210080a0e1002120f270a02060a09030203191502090604090606050301050916051602180108060702100203090a03050c0a1205 74
    0xc9008180600b00a844103003c80c00d2904100c10701c4100401e802d5905418441c1c2541c1c080581c0d01003140d802d419206400d200700060401e800f60069404440b080c040440003002808010b03940c000140655807542d262042d030b1941c5942690004d400c00f040008003034020b00c54003621941454000303080600021101d154207488144907082c813a0000c4441c0200d1301080b14160051000510200721401e510350103d032501001a00002d9540c0e21090740103020900601d4104118241406400e003001c2403640801a4115280c456450f044000001d000445600261103c4240e0710395054502a288440040141d96220030000e0041d0344280030740391003101000300040003030203450f51035900404a55140c90030200203041151286000750812a88040f014040350f58440c02145564000d11070100100007609091038068142007901c00311114013401042000400d40b40010090403807580341c82c1c2243e036449169130241c206509040e006010400c1b01c89054500c0b42d02c031003e00001c00350000600091 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 702043417 1250 702042167 702042169
    0x1a1006110a050d0c050a1a04021512041b090905030306211c0c02030d030c12060602070509070203040b0f0711011d04050402212419020a0536 62
    0x104581c01c030003061603000491094025102d07105500e000d42c824800c54080c0f101c0340d51442c80320700d40d58841c0e140390740c4032900300400d51600e04201c0c00140040324019190a4903c07810500c070380c0c0c000740040d101500c184041039150f0002e221203c0144440c80c005c100c0a1621f00c0e0a07600d80d4000e444442c40350f1460040b1440c551458421010080c1192004020400b4003450105255040500c000280700004400070003603141444195082c1a050703130006100044480302030001050440520130700c81c9045d070305200c030640020b91181582e20403200c00740d8641d90100d080346140308035000b0041e00000400c0d042c10340121540500b134464421000080a03060b5800112120300080000c1d042444100c41b5502450034540c0c0081d4002c0c1c00580006080407000744845402d460005001406501a41c2000700410540c50182c0e00103400c00241c2840b81021814580581445e24141c4825079000984010040c015411541e021000c8001080d500c0e14030042c0c0612590003542501e40e89612000007a02 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 702044667 1250 702043417 702043423
    0x181b03150903070615120503120c0f09010302091302130602071d011509031b0f0e0c0a0503070318080903011407021f06050301060321020a031403041a100611 69
    0xc500c10700030007141030050588410000d0040d0301460b00081c444490081010a440100d540c00030b40610001d42c6d480c3c10015015261035802091041300640c14002150002c54500440ea80800246405600c0307000c102c00280b02c5580c01802c0e180040d00c00103242d02590010414181203480f603400b564100c036175403e101d50201601503c2c3c0c880136654a80144142010b541407002420182d00d08003015035200d40c0e40d040d8501145a922501c12242034003003064001d440d031000302810070001c011415041040c07507103920b40a00b04020003400800700006810b00d11035400f180028205002000c000e0343c42e030419460642c00090914001d5080101844c0f040000b1441e0724010b4581c7d80c0185508807441e200b04454100e1003d0b02ca42c07070381e194500040c15a03801d0240c0c001a50017590100d0078100364140202c20a0040341008003590000c40e400d802294000725030314041c01c81e01f500b0030764036946c6107801c01c410503e1a000d041c5a145200521020304041c400c079605417070303540e00c0d8038101101088442d55 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 702045917 1250 702044667 702044671
    0x20c010c030c08120403080604060501030e070302041d03070605011518051224010815010312050708070206030f0a06052b03030204051c0224070b181b0315 68
    0x2000c698400c0000c400030384104414207606004036034440c00d04820140012082c0815a42600090f142d84284299450288611001801d090904121012460048588540d010701c030280c8256580c2d0000111507684d652040190480901540d40d10001d41c504034000303040a00998803400b20707050300f20303603858018461810780d268032031a00c0c2030b0315240c0340410600321181045401203010301030f0002400c01d0440c0664002c10090600e0348025070410702e99170f18022908440f03880080318900108003042d036002407903410710f01c546421907844401d030034031605510411200941100000040040448252030240e0003081c500c0b10510460f90b0300e07002c1004012014603100c107024420b4280c80015468101c080c1c06881c4641405820f041d5180c0c0094601482040c42c05405010031407010704522700503201442c20000c050a1001107104220f0710b003000e00900750010071050b000300120301c00e260014094a0923109000c103c0d003050408500c8044018039004036207009200d02d2580010b003182200c0518 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 702047167 1250 702045917 702045919
    0xc082d160c021309150612170c010c1d010807090b18090708040311010c2c12030a0801060212030703090c09050109021e18090a180602040303080f15060913020301030c0302010f020c 79
    0x5580c011f4035884035140d0301c07040701c400c8442001c20026540742e00002c1c00350307000c00407280d26580d40820b6019902c0680a41302c88030103040040000c20044c9858000700024240c4c0e10201030709486408034402d42c010390340c0c8241d800c0e500810820400c07521a40c403030040c0780724600c41d0791035803000c10b882450113080c1c81840010383d0104809101c804115592200300d0341c60a07008024106076480344a01003024103411059035081a000010382091461f0810078440c014031080c070060041c0b00c50550311070001d01010740070714105600c4860010903c804402c09038050f140688042085507950700303181c0c00070b41c003c2c80445c00310080811801d640b501c1714020386448001e6107864011040145040205c041801024485820365030f40f0a40040c1030003011942015114100c0181d585080d42406001414000c0030101410080c908001031900683d15170010440300380e4665850b5501c0ca000101e0b148001941c000207144007000000610840c5084481103034000e880c0d440640e591400100c3e1200080c070912 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 702048417 1250 702047167 702047189
    0x3070e06010e0609040c02030c160807271506090501090b0307030b120f0610050306070e090a021e090a050d11060702040f0c082d160c0213091506 64
    0x303050354040d000d0100d0070760b4010200351400196000080803100c0c0c86103200016403000c288048000b030100000c04040d01e104600080365490b06520950300d010714082c0c0d291041030083d480c124148440301c0c044151940c42d5052044440c5c842948440442c1c0e481040d0010720607680001d40c079401400d444c42911180d080c590f1440c0e0f5661820340140900d1590141c000307921540100030700100b400b041500b6035011001c1c0c10703642005000389000c0d90280e00a141f04e81c0001c014808000d8126401c0198607200f600d40c148556601401c4100070301802c1c04500b02030064000c07411a80030070800404001c1c00844500006e5910391091025101c0704101c01424004212030450320392610002a10700f09200400200700400440f10240c15070f08101000000f0504a200380070300d020006c1c03025902601003060b80c46821402015a08002e440038000812401704240b0045090f4400c2550070107154014242c191007100501501c0020b14400a00f0b1710710300b921040c0f13011a0010781c02044115003940040d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 702049667 1250 702048417 702048421
    0x312100f0f0b070f080d0618060b03190b180a050f06131a0409060f0b0301020a051c0b06030403090e0105030706090311032a270112030207120c090b03070e 68
    0xd041c40c540d1003c00140c84a000509000c00007400c581c006203024245d9078804591107160409406c007100a02c46403121140c01d04809000c010703500310660707610031080c0c514040404424003a00000f4102c0c0e40105800404091075902108402c104c0780b030240382080c0e02003019542e0050a4030a0b04d1041e00ca45a110301000c1c000000750009030007001c100d100c01c40d10040c287d0040000503045079400c00c005c46600da11031a404014441c5442a01100c620a8000790718100800300014190712400400c000d68141c4010041014507455201e89113103100640416541c6c203040c18043e1144915204403c0d031a4084d0f000807a843c10085007903401c40e056034445a9403e401c56803502c0f44043c00b500c0309a0103102e05022914003880400710041c200e0a030300500c210101c1078200340101000c080003d1111010007806101e1044070030203119044444580700d41e03034207002c5458101e0816145601c01d060712030302904883c1c284802143d04404658044401300255107402d8149510703500c640c481c0108128a01300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 702050917 1250 702049667 702049679
    0x260a0305072d0510050f0604090f02090a0b1f120903030e01110a170402061909090504121b05120f07020301020f210f04020f0409050312100f0f 63
    0x20203465050322490b070310b8401d07114003903010105102d095841d60042c03840090500074858113010f00703103205041100c00e12640c030b044080544008000740059026a1380d40180c542840785000034151003e80c020307ca25154106594164003408190080c0d078401d00b0800e0142c004c240c00d110200c0060700c01501c0f4040403c0c3d00e0040000200307100d1200354203060311880410100d04081c8684c2c00b00d00303040840035844d500c201000911a64100c008810300e000c4100900006d66500001e503098041d201642d03108650303022104468204403a80a07000b0b0906003070600c01041809460341c444030000d50b6520010b5019442049200c0c500c1c500e01500741e4201100c02e82401d0481c400510581914004c164640040e60340841e00326442460707050790420000c03802d0000076203e500d8101403800c107c6215501800c00c1c1c0841c480c003200c003030300003407241c540e12600900c1d94039680c0010500f290440c05503174030341c1800c40c0362507407001040b140380402203a404400714414030040000005d03142800b02e1101c5032404c0070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 702052167 1250 702050917 702050927
    0x105011106100b090a080a0506010e07030e030714190c030611090d0b04110a08011b02010903120b0301060e0c120106110703030e1809030c0105060616030e011116260a03 74
    0x41140c0d030052020321006c07800510030440200340d14400c10003000250b150010204801ca40135000004040c207110b10b00301b200714000196201d168000c1048410316404a0009107030a5041580385002c0d46011310071018480941e520800310390041c3d400b442000790340d40c100410703071103550388440c0d2210603100700d0404070322010121542306109281030301180d607032170001400f010f81c258404403250307446d84103042c140b458486000038080d0090009210300d00a5a4000d040300a060310404455941d4850300d051b60740e003d402200c014031000782e822070704d401d1400a0300502e40c04600c100c2d445000310000022082e1091001540104524014001850030761b6401c641e11500c0110044d4480000d0450385428200720f41c0d400d010b01014401155503204c408109402c1d80e60050140b80706001c00d114045140d072901201c0d0115540c545002c40d5164035540040c1c58641d080b88500783c040c415580c0c0721a41600d0014860309942030014142c3c1c2085110244041c50042031100c0282c0c0d4105e1207420740040c1c00f807 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 702053417 1250 702052167 702052177
    0xc031407030b0a090222050d113a0b100f1703041d0907120f030e04152306090d0809150c061602030309062406030f0105011106100b 58
    0x10005075059030364250140503a081146140070205001441405111b030100008004100554a8994584664132503e62088450013080e028007001d150121a0104102e229644554030f2041600169142d01e040c0711401903545d0304030b4500f00e80c20b004c6181111302070440d0045500500b00b10486030b0408640303a1120402d004c0c400c1c0544420700003c40c0c129203041025040041454420400389004030100b0302e032070315170b502940c1d001e40709554500106d079904d0389282180341c150400031461354485011500030100c0303440e02202c4010401005c2030f08510150940c03610b0600d44405000702e44000200007180c421403803800d500c02212800c060005002c039000e400090402081c01c80c45c400740d0709200c00700c1d910005030006141c000c20104041c0d14415090301e0407400503803000714110b1802038580c07562008040e000a5420207440b0084c0c03030400c50030341001000b150103400941c481c105512142100802130007110b0114201c064800005200010058401c1003103030700080764989172114103140f0f5440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 702054667 1250 702053417 702053419
    0xf0a06171015030b0f0a110a02120313050a0311010507090f1802070c09150608040203030306120c0a060504051c080d050a020d02030c070209090d3e100c031407030b 72
    0x30580040416914604070707124015400b901d5142d4a010200c441c07c48a4940e0746846102c000d02031081d44d1940080c02e240704106110105a41383c07030319121520310300c190030401845445403a901200b0590304c201224003490310807000f4003094503941e60540b901c03400c500038142d00c0941c404042282c84c0c10031f0006401c501240c80014034000c4641c41c1e112030058180c01c00c9045da6101d030a40078840d800d481c4900d0041c05603241844040c03c4c00c0c0d000980383e00c009402d0b540b00c0d60034000482807000c2c080c080f00c840303420001c140d10380c0e00d0703079600010f4034075007080c40b60600c1498041040f0940e941c00556041c5130952040e8960f2800d40001c0703c4600401005c8c100b07151241d4240445140080750b4801140a103059400c8580c031020248100410080000c140008a070040d441450f415608852404800703000f280149442403203101d41405d060000c1513841214a1202e5007001903104041440c000c2804440c2060203452ba50143c140c0a03030302482c5141b186075400d10001441c8038032030350090010b480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 702055917 1250 702054667 702054701
    0x706050a030b1f050d140631020a1106010b090a051009170d02010e070f0e150d03080f1e1b0d05070305070206010807080d052503020c0a050f0a12020a08060f0a061710 73
    0x2044003445c0200d801c101c180308045040009189840b08040203203e00410702016500d1a00fe450000704003c841d891041c0c40c024241002d20204050290506001a0401841c1c0c4e03501460028280c65680705030b80100300155207482040ca03140000402d49600391803421150079401c0b860900c2182c0282002803102d104c000c87c2d13451040f41ca07a50301c1c40100d9024000d5450a5907400c00038400c20801c40090030358401030b143c14822800607a510b00031140e000342600c00b030040c500050010320f00244501208448950b140c08104103160340c041c0c1c070131405000d499080714420fa8903518113540c0c6410318042d42d20f565200c448003400603442100203019403d00c2a01100c2046c13044070401000c0c00c1122000c901603080348610a03050705004205600030042165090320340c101c44008102c0b203110314060100740703d80b003030010015920792020f500005d003079a50407181c151804524058a901054810040d0a0308000b0000790700d122035404443c11903841009084021018207600000303140e90390903040124 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 702057167 1250 702055917 702055999
    0x304020f0a0e0109020d0b0301093c1a0c13140f040f0b041a1806010c02030304060c060513020108070e0a080106140f01020706050a030b1f050d1406 65
    0x220018000c0b5000303040380f28015851b00c000c210408141d8140c07800c0b942c0039a01d40000d00002c11441d10500c1010a500194006440d40c0748d10411580400e40002d4001c15000b070007400c00700200f144040ca0f000c4003050f021411500e03918030460300c5100c1c21000020880c0c0c842414008075507012100400060010010301c0b07100841404101034a038a11441032500f5070362102d85206042c54010410a09280c03600d6400228039400041c42240c6078900e0030115104010028006901070f00100071804e40050450b510ba1b030742c4030700003030250030102e10886d401401e1801188469501d50403002c02180d050b198103400b6030302d41404452450680e0f104940c4000707011000103e000003807069101a00380e0088a03058a22000203010101003075404850456004103009c01c801a07001d01910001c0510345404101c620020001605140c046654552508001c03403400c0b20b05ca40240040040d00d400340c50030300140d400c6003045003409400300d8000e034014142c806a8000c034011400f100c0f0042c807080d21090150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 702058417 1250 702057167 702057179
    0x6100e1503100f0e0c06031608090309060f0a090b03060a060c06110a0c0218040809090a0207020402040e071d030606040e070807030c05031b06090d03032d060e0c0304020f0a 76
    0x41c0700101c5080010340d982d0326030104d01040522659240c01d0f1705588103460b43c00d0444200002103040d102d50720402042c8004980b10130390074030460380114001040d103030f281c1201030814441540b20292000c0400c0c0c03c40c0300090030002443c140c0307104007030050514400c6850b01805036a101c0d0080c3c0100c4046507101e88454910351600f016000750400c581d030f422400301c0c40d0b20502c00076540d00e0803c807a85441820401001a84a03c119a40d200f4282c071020400e4441c1040d01029008102c4000d50050010a000c101c0d030350320740c0134507110342c0340c1c0da8804026202c0080c2c4820541001550160190080c400255040c106500007400491043d0101d0310100d5554078000c1c10280c0c0d54000b200c9070b800340e00d01003140b0301c0e0400c2884160b00340d15408509188540300000c2c1c5a218040b40ca81c090020701818805041c069400040c01810080071a40c1207001258042584103100b509002c07402c0c500880440e01d049056481c0b442251401200c1d865511140c00300311490010008103a4080c170000d002240d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 702059667 1250 702058417 702058421
    0xf0c150d09050c0a0611070909031e181203090b0a2a05060f01080714130c02060106031a030703060b04090210020f0712030f030e01020c0708070806100e150310 70
    0x107980148050801001c0701802c002280200760b01610070009844081c44d206580424500115500420001013000c6686802d40d40f21003055140c20311940d00c800901c8600350884c80b0018151410072603031051135184d5810019204190700003900046808609101680b10900103055003003140c1000110001c9503440d0100d0440400000c420240c1d40040c0d02042001c2080310760703044515210318012640c14100411360b20501881003402003d0f003040d140f0142c0c0c0303a11541814040301100184042221128007070351301c007800e2141c080000e01d8038100c0c03094100315056400c0401c4009010344840c5183d40c40c0e00010301410443c0c4c650181c1d0f20702c0302000595030301c1c03010f003664203094004c2c241c41e041104201d4181a00c6910160000e070b005800940065030054484036a1249400d00003401c0b00803007225802401031030f0701d00720030303214040d4042140c00002402e20100c40501e001c0b1460759882120040c903180f0701d407144681802884002c50301105800005072030290024084440c1d0ba080d0a0300340003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 702060917 1250 702059667 702059681
    0xc040909060f0605060418020a05070b010602010507020c10120b36090a1713030209070c060608150c0c0a0209041109160206060f0301060305030301150207080f0c150d 73
    0x1010740d40e070b8192103401000d40c081c1000809048907418205864044405100e5940520140d4401d134006540b100950088041c2c07070f21280c00096024981da1601c01c0a4000c04058450001500c507510780e04425162401825030211410303920136001d00b204000e108050078140511551100d51400d41f0282d20000c0384141c050311600b444800d40084c0710660004c9001d6014101d03540d0307074100341040707004074155120329a60640103010040d641e8141800c0b905842103141c0001758088052801c5c000c0e8140c4c40082450154080c0504000041e41d41c806549e13280c40c108002500d0007869030020b9417501d03442010f0311795041c000d030507035016039030703c0e4000ba0129600b110111170290b0380e14418852410011011a03012142c844130702103101007000065030320a0300a0007030780300c2c4440a24102294a00b90800c100446e07010040300e80700e503150101c821400c0d25000c04400140b0602100140c40d000025445400003400005401e0b4002a0402d10061842003402c9c410000001c0203401c01481003486404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 702062167 1250 702060917 702060923
    0x2d04061407080f250c050d0f020d0507080c01050705070e04050a0615090e03072d0f0807020103150e0f0a06051002010e0c0406051309031e050307141603080c040909 72
    0x70f030b880f4501140c030440c00c40c1c41004c4070244035203248000c1c001041e105418064030f07002c4410000220a500e40340c540020f642c00700941050304207551000300000014800250707451001610a25104c10004440c9400b80340340182455002d028100800004c00403083e0700b0601400a441408140d42c9800c003d50300349440c03038000141410030410660100e48503c1c0c3c00110030b0409545012042d45540d03007100d081c00c0b00c88800c603003440803080540d101c0b078265070700b1154030010b0600e84280b94186441290405d00d016808a0b0070111075601c510100e01c03a100aa400d1404210f286403521080c03001b04160042525500a64484002c142641c0e42035260103141100c0c1d002096008080c01c4190601c900c00c105c0d14011400c1480602460b501c01d03840c4020040e060100142060550500716094a010b001400358a040742c1d007040801030788240154803d003055101e141801c1d80606889150707101310b0921400b4890085507100009105810442d005440c207210542000d490380b411104a82e4074940c12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 702063417 1250 702062167 702062197
    0x7030e0a0608090c0604031505062d120705030616050d051302011106070c02010e042c060108030703051602010c3906051c020d05010b2d0406140708 65
    0xf1042140800c21480040d4096400504017031641e604c031401c1050001d103802c2031584800020b1519218009000c03840d1244442061100511282001c00c002000801d58041c202d00404560450800906a4100c403000b4000f44141d55500c0f60700005811514495020001c080299040540d028000d19005100c00f41d011003113440300e44000b418000c40f4030741459050b08030104002c000c0c0c0c1c014245840b9580c0a091a400b100417600006004000c3c0e8400118030040c020100710b410070500013010411940f0900311081640c0714800c1c580d50303010308100240000c400700903020380f02030051000700c00c0d43c3c03040c100384548000a50301c1d146a8040b101000c0c40650000c00110302d104d186042000a600300e2166103080582025001005449112010181d49040449016844003603030304592a0300c86e007031005c01003940c6a0101003c80d070300c00302800192000009c001340c1100c8600030107100d00301741006210302e400d1030400291948034008400c0c010b90b000501240c40400e1480000781240840da03011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 702064667 1250 702063417 702063421
    0x3080310050f0a030b280204090c090e06060f0d14010801020c100513030c031110020711090f01050f0a1a0904060602060907031e0f0302102403060207030e0a0608 71
    0x502020030214040e00f480740c51554810004520701e41d4486400c0305554120380d40d06d48440302d5110890745e0040602c030301e0610004001980301c070300380d01c15005042036958980c1060f40d18418406006c4003542c02070b60024042241c0d0303032031181910052403504801c20000c9982c190400c0551060310090744180d405035000540d01d55814428401c2486000300741804000c1820000402c44c0d024080510003824861030116140c1450300401d20442c90014030011600c403c0d2140c003000019410400c011203008a2441d4804428644003100900c16010b05040043c141c5c03070802005960032044e00100e4209594000100d140000409420901c01010001e00e0741c41001c1c0c81400100d40d082d170311400031500b1541c01d01a0041e8041450130480750840c00980362803da806411a0030fa50007400145007800b5a81003030308150b00402c2d0740e00880010802006546603924000c800f0709000740c101c031148013003002e003071001550a80c040c01e5014001d1820b5070400c01250f0100301e00e02c61030b800034030104d200031003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 702065917 1250 702064667 702064669
    0x609150c0e0607030203180301151e0e070e19050622050109030f060b0a050916030515010c02091504020708070c0501030903080121020325050d03270308031005 70
    0x30070000e800a0a4032910728004142e100251240264a8034944001e180300c80e28105950035000303c3c03d00c02e500401740c00e070740d5900c4042d005903e0300c158640010751114200081d4040140003400e03c5526282ca48080320184079041044607a2040034051104034100000b0503e522140090b0250306403d2070909410618810403510414050384070504020400a0600c002603404ca800c4201d40d074411804100301e148540002d400780e0168000c150004201d40800420250300c4060401910880d03c0c200140e0321526400080700089801c40340c0495a403d19410040c00d01044440d0301800241c21a4250580d1400040a0364480f880c180c90078840840c682c014464400850340003020300b402d04002c5248555406042c08005208443e8409005018a003456681171001080e03154007c0c103450b10354580180c1c1e00040d1820b105035840c02d242241c00426182440c1c0c103d016000d0300741e2030740000c00c00f181c0030300252035500c0841c903212000f500d8070000004041c2009075004840b1402180c240c2070400c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 702067167 1250 702065917 702065927
    0x70f061206090504032c04022109121c0615021e0615040b0f0d080d0b0a0b12180d0e040b0108041112150a050f060108010e130609150c 59
    0x2c1c1100032258a0007003440002a0443c08000100000503262903448403203680c0b00441c0119918490340040c00044ca00541d0041d100c0c1c00200d88242c51092445500e541581c943d17a110040445a122032040105610140e4561660010344d0714910002c203c0326100d15010f0340a000040300324007d6404641810540025407440703940b1000e9440040c00546400c000285014000b078160074001d6654210f40111170f1145405400c55020140014122042070f280039512540154080490b0520f44035904840b850610000303003c41e158412028188145050b010f091100080c01e41030b1026035182480169071400c0c01103502170b01058560b004210548000c1c0070a41b00e0040403181003040045c108400202c480b41d44c85500801510000b1a01041081c5140350417410800c0407915180d460402591840a0308024400c01d1000601d280a45aa0005440010003030196064900801002645548442940112490148101081c400100c2d00c50105480c05c1d01e00008116485009010400d6000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 702068417 1250 702067167 702067169
    0x150209120724020f0c010507031b140d03060501020a08090102070509190f0204030816050321010305070603020705070909050705061b0d1b08180a17060702070614070302070f061206 79
    0x103400a04519440c00c44c0450312400e540840d94148000440c21005041c4500c04910700c1a0b40c131403d0300700309100e60420340c451250401408ae010312600244001c12031003409180c0c00c40703d06800900d40184a65134004968000100e40ba045128004000031079580301d5807114005c0b0f01d0460340c0081d0011407001802501d484045804007a4010442080052180c008940c5410300f1070000304145d030b0b507074502107046205c0d4004140d03003442501c042d103114461003030345541280e01c98021241016510340341030b0141d00510300c014200e500801400c002ca1007282c1c021610b058400c0c01592155925540011496001131008911140d12002441039911080002d41500825402c1120b00043d01c01c1d050010820300450007080a40f002c80c080c4d10000d00c0080c89410903100038960380e1030340d407a542c14810300008000e47c1240b5200341404208100d002003500c0d02075451554444030049901204040203910240007281103202d0044001901c28074803107042d01400003603a03003511010070291030100381d03081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 702069667 1250 702068417 702068489
    0x10e0f0d0308041b03020d020409060b0a090b09090109260705030a0c02120703170a030219020a2d1e1a010f0807350601080109060f091502091207 64
    0x4c0030301440581e890b50200706440d40d04480101e988160b03803821001030000c464801c2d030402c400c0e01021901e0b15042d000445491400d0b90405000c1d900c0b038088509940f841e0358040c4c881c2c40c401caa82d4114252060b03035038210061400d03065240c500541e95042c0345511254040001600511441085140502207490200c04240c02400d00c3c0d030968031140f10020004001404401c00010705004041c001d40548000321020049030842e00715415003c0d4440e5444401101d03030b00c5210001180515441e012a42061031204103e87c00f0425940c40c034440600000381c55458030481c1c00c203480001d10401102d82c082c020400549641c0d45084035898a00016810075a00c64112040900c9140f0704215261850340c4a102c08000c219481c4001c00360030f22202e96410786500a1500200d0100c0d0b0541140152a200b82410001001030030400d030112071070306034028440180c0100098135004070390041c06164000814030780349550b003804900d00e80390b51680001c6c80d80113214508080386250b104a01c043c201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 702070917 1250 702069667 702069713
    0x80d05070b0601050a020607080a0e0709140c0a05070303090309030623070f0e0d0c0f171b0d02010e040216060605130b0a0b0304060207080a030f0b0402040f05010e0f0d030804 77
    0xd04084040c0d202e140041230341c400c0002040000d502d0356011382043c52400041001e59a0f000d8441d840c07007001d0501c0c0025044080c490038045200c403a44181194041c9036143d513124282282e5590840c05010310340c4080d07080203805140840400d01c80d02c0b070740108500368003010300c880305040345003200e02c01d00800c600c041c020700c042c20080c1943c1000248028000c101c0e0032208001c0545044081c0c903801d13400c612000034542c80d020641d00131490340c00600d05c1404040f43c1c0200c4800c3c400690b8414a207201d543c00c14102d4606000550107078581d4001d003a4010405418282440302c0d6040b40010490192490740d210b2404000c142801903c458440c16488401d01406504c40301145800c0c0c10b40c401c080d107160300040000e0620070507030b040d00c0485070302560895548c02000300040c040d00301e00c178400c0003980c640070801d0741519040c421076085440425454a00c03510f4400107542014880d110581c1140400700b0078607842d5910b101c4203104c0c84c86521404e40320b05082c100031f081a00700e402d40c1c0b001c40c0c1e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 702072167 1250 702070917 702070927
    0x503092b0f020706270e18010b0901030c09020d0f150f140306040f050f0312071101050708190204031a040c09060303051e070b0c0d11040b07060b030304080d05070b060105 75
    0x245c0d0040368003142e0030b480c01c0d2010000c0213250708030819021715840b030006c3c220b0f010300380a02800122103103185851035030001d000900d006420841d900380700703100c02003110f0010074040004000036000360110044000000940395030841c01c1c04141c40341c000000c1c004201c084801d1080280a00300c8101811a0740d40215403801004080b03540c502000c0c0000c1d222107050700d0404100039007005005d0038400402d0642e07844400c001c1e0001d0520005941402c041840103806001700101403240da441018642c0c1ca40d0a40d48480309a6015201134008001c0d91710380030040480850400d22a0100c80c0000e4960100d0500d0300e82025200d040d1160410820282010703810800720b0341c84001c0d9451820034420100b03070780500c5422500c01d4801d080c2c006218030008420000c0340d0080c44050000595140c6050041840700b810340000d9124074000c54100090502c004800b1030b16039401850407030030203000c0300d01d010b48401400b4a00b85420b41170000107680003880c2402c0100002d01e01da0040401e0078141d00b8a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 702073417 1250 702072167 702072179
    0x8180f03071b030c0801020403140a0b150d0204091b0f06080103020906010504180501151b0b0a021210050f040c0c200402070812010e070504060503092b0f0207 70
    0x2034480e811000d055051450078665540b4035021400740119030244c03403400b1250355054a24003075045480107a0741c41c0600007800c80c5240300810a1a00150301c4502004243c1d61244141c0c01021881131650700584251840401a1668414410035901441060303101401d655100f1041030010340143c4105600310301c08110440d001905075065070740c119002080c50350380d48c004035220700840c2e0201c80100e18078001204000c5040e40704034140c900c80a001040d02400d480d00fa80c0b4188242c095905c103400da02002c0c03000c40e9941c2d0036190000b00361040546400c1011580095000003034800019080744014100700c80c3c6014260041c81120a840c140542d00100b1400340c440121004040c007c05036065112800100f009c0390160340350b200a204548524050410600720b4100c54884840d040d01d41001040480308525603074494401581d400d07142a052140440f120380000d40540c0c0c46100c0c100b0500700c228440e90420035905041179090401c0150050002d10982d0102e54400c1550800d40090000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 702074667 1250 702073417 702073423
    0x9040210050f1b0f30090d06140606040503150603031911150f010501030917041514160807061b11060f0f01060f020f0106060302130803181011070608180f 68
    0x30742c0701d17451031503400c0c43d42c0d003d0b62000d2052007050365000030003402900420100d5442100d4810b500b00320224155608028880306102c0c40c00380651507800a078181c00d240c1c0c513001c0e034540d10420140c162400c00d40a480c515034500380c4203408101085a40c440750300000e104100444022414505040c214140010007511031501802a40d04041e2142840c80034002203a91081d4100425403003a55146d03075592054800400c01a60540001c1c0c2085060200903e035405451414034150040d160301c00059851172503503407101c4011240e2540350f043d0140244c5c0030b8207500a808405440d16100c17017030082100c9040420003070000c00048848002c1c00908084000c001c0d0540306c05040141044010070381c1a4580100d030000e8400960901d035020850990607006041c4d84d5100304c00c8503e07010303100c2c80201d49901903040340418488490340d6540c20303490503250380b0349001141d040c100543d4012421007814000d0581100000c80d4004050005601c0030355641c00c10652100040c0002e024034880d030540f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 702075917 1250 702074667 702074713
    0x150f0412200f0c01031d060a02031003080d05180105040b0c0a0302070b1006020717030307140c0102071a150607060f24090b0402070209040210050f1b0f 67
    0x20030801c00d07a001d10100e1070410050000140400325201c94002041c5a59541d95020f20700340003d0811040c104c0c240c2003814101000d40f8140d0207001141d1700c0c900b80000a4100070031042c80c0480d1403000001150700031000348401c40c2e1201e030120355403410000c40b1000c0000c182085425a25120030000800e000c032400540000612b00400c4c0d903041120800c0380030f0b0150302c101804209181052109078260100c0c60011107440f5000c1e2044165985268001004154070301059030300204006200b40c3d124034803138404a0b11018072541841946d405450032a04100313012200c0c85600f66030650850565110715501461002c3c030700704802c2c0240b004c224a03003c0d60703200900741a00c8072580d0003542c1043d00000d01402da80d20017254184030320078078055041214400e030505145001805d003883c0c21329000322840c09801038414507040d200d503400c2c0005d2051220301a4108401403040f5500000060b00516a0200400607442d002c041c040041e418025540040000d03a442101140c00c1b001308540495 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 702077167 1250 702075917 702075953
    0x10606020624040e120d0603050d0903050607080c1204240203060d02040b060702090f0115050f04211b08070e01080a0201080703140403210e10020a1b05150f04 70
    0x10506510004131240b0306000c03964941c0b00d40801207290110001c45034000030889000d00c08840a001d100700d01075032001c030103001c003400340d030003080c0080c201902400e080754000f4401c01d64285810200341c0c046040b080295400c890010b0281041c00405028080e0440c550a80c03c80451450402c040020200d0200364002070041d83c40b8035005002c0ea48036400d544e081a00500740351124501380451b00c000da602401981c5441031507051030b20400c1d2061055803805031040c510103103424181038510701c000c0201c00d40c0d10008100d10034030000007281d801009a07803260840c2d4160506041401407414070125400001c0054018001040f100c08006075480f4055028245401c040d21129800c8020705a80204501e4420603802072004041d809a100d403502c0c0308000e0031148031203140c18240140e8101030500802c031b9120b50902c0d440c4c990079a005058001039414100784012454010b080c2d5500f0624041e262900b1010200b50340d00740e403107055a03102100c07805103c52890182d5549135100813804c514 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 702078417 1250 702077167 702077171
    0x50f15220c050412050a120302030112080304150e0705010e01020f060c1b030301030f150e06072a080403020109050303160b1008031902010c210b061b01060602062404 73
    0x202298501a4040f01c0280c4140700c4818004a040d0400603a94030104000f21010030300c1d0849414014820310031b6a042c0e8400a0120002407000d484482c40c94101500a40d44522903034046c5103000a07070710985403c000000050a1140c0c5458005802e41c00e464070558195000940c0c9500a00c0000c81c03500d50007440350700c40c10f032903226502c074042800388007020000141c88004008018001c00465505601344104032580f1008104c00241040e03454003991b060180c1e00070781c04150100c3c051f030804004a00e54181000011311040c0c0320b0f10161440180035a1044000a800e0056590102200c40a00b006030300440c549200743c0101c000d500c0e141c08002d00303800c641034041110440461500300041c000b07082240c0d00d0703500d500c00c00280c04103d49241d102540c40e14045a182c94011500722066044110803a81c1020400705840050710041700c20030b621107410171190417182c17900440204045d08800001480600b0544041c3c42d00134040c0516800460301907038100c1107903170300007030082d00001030b500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 702079667 1250 702078417 702078431
    0x90c040308040e090705060d05100906060c0f033c090506180d08070b10080c01480302010e0c0f0d1502040920030c1615050f1522 57
    0x502d9061030381745d80195500030800601620407070455003103540a005403030040340045642e441c00c0c10446a181c81040089070240c00c024012402d902d5040140d54000e040212000e140c13400c00d0070140401c0d80d14840c00703901c07280003007603607070752049e012100c1d42d10728209100080d09040c0001c216008160280300a65800750f1101007685070141c1d007994007944117003686c1d1140300503e800351042c101110b60501100a4110001c3c5224000403010840c000607180c0d0360580600d80c280c50140c2c0300c290328030f07900c015804080d0341415141424030801405040303c0c039240240285002401d4a0304440c0c1040386a001c405440d903c3d070340d41440c00071003410417a551003810362107180031702c10400c00c140e00c1101309202140c001480710058010000300c1c02c801200d002400e84160011003d80020ba4002c0300701942440415061605610580c0c0708901812105034a0401c8014000c151181124039803c0181c814041c800712910081d440d500016013207030703540a90840c90006803139803000c035040e07140344d6174032441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 702080917 1250 702079667 702079681
    0x1b030403050d1e0e010b0a2904151709072c09010204300605040c0312020c011103120408030a0906110a17010305070b0319020c0c090c040308040e 64
    0x108070ba20707607a02041c062003508000104068151985041c102030541042c2800320444018031550784240b20007407802c02c59a041c01452143d04201010560100788025511003080b056540034000a204188900b0001d003c0144014140082c075208560305020150034040c0c0c0140204401c03003030f02c0e00d00c00c240110843d0b0208aa4085144085408461404a05028081506400420035124000048100790b01800c450700441459610201041c0200381d8500000a043c0c2e003005030854010070040c6519601c07500c070455003044401c21880540c1c840031903103906581010303105c42440910f1000d10308050741442c1107040c40000920060040800100050802d405035012111081e00702e58204005030170195410000d078020b004d00c13004201c522200c14580d800c08840d01e07040e00d5000c4040c081940c41d009500ca45600081c1044000184904081003207244500c0038022001c8074200030500e040260f828800490005414068202810001400461a030104640031117080307a0b5000d21981e5001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 702082167 1250 702080917 702080927
    0x327090216120807080c0412110f030607050c070609030f0311010e07030c090605040e1905030405060c010b090106020102030907030b06060702060a170106030c0c06050a200408151b030403 82
    0x110041002e00307129151400c65501280c0c003841203c1c16210352005031511040031349940034074030602200101d488881d000045a14820b00d04040e00a0110700183c010030000030b0500c64103c400b2000a080032030700590000d400c115030f9008180a04021600074255101c110740089081e2000d0306011149a02891a5200b540500c0071080f01030140c400c19500c0e0716001c0c501084920842e80c0c61401c1c4080426a031810b80309620741119844c00a02c860425410301c809000c49107401624079000c14440042e080e00c8040041c4a01c0181d04000142c20072000c0800038144010780020085a10500c101301c0b030004005000070507240c0200c0410561ba658100041d401d01c02e48d10003e40100f00890310300baa058000840d0010805003040c00042c580c2c841408908640360031184000241107004213001040c01c5078007242e0401e81c140780c0480c60301c580c041e2503580d502c0007031000e003490100000c0c200102002404060104510072031400003e04002010307042c009050b40c1c1258030300500201040405002d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 702083417 1250 702082167 702082207
    0x4170d08040b060d0f080a26010608270703060f0e0a081c0f0e0c010206010602390d0c1a1804050c070b150108180d14040509040f03270902 61
    0x4400d10b40c0d070304151f40d0010000000c51070184060041c0c0b8020b000005e0f58440440d0580f4825a2001101d64490b072809150980203084100080d001201c1d9038002c100030b2190360040c0d030040c1c9000c100a681c100e0303100201c4007249040140d580044609100046030001200d60010503107040d40c00f0848100e9084000342108041070f203085142c40400002c1e0000400c0b50303509150240c09940c20342c0e03600c40041c1d8407160500d00c000f99225910804080c800c1e00071324218121440f501401000b4903551011420500162400b81c404ca0b041c0d03c420010726285007410214602100025420000f2011010740c2054420310f14521603070b15107000411058940c01070b90030741900301c0b040030102d080c0300200100040d8005180c40c00200070354001410104459850342030000d00781c0050001c141c44400440381038200c00803200d000001044000740b41c0d51040c0c0104d02442c042c509003021500e29140c06030030340031032407c1032aa03078031903803924010300c1c6c80d881d950030488600d51405660b0385030a0f15507000116032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 702084667 1250 702083417 702083423
    0x917100609050103020f0909060609150d05070f05061312050313030c0305071a0a030c0e1e0306070e090a0f060b0406050a02060907050a03020f031204170d08040b060d0f 74
    0x19000c00062280341d1030708440c0c100c070b0007507401d6280c11000d42c05001030b200e0203c88039140c0d548610b0124020707080040e51039034401b040743c000d44260740103440090404030440206440c1caa100d1841400060324910700303400203020440d80359150a0102030002052a544e100c1d85440103144122041030190910442e03180c1c0f5503100c42c1301c43c0c040d10707441c5c082e81110190105589911880030003281804140b030b086c9401a00c080d9806051005101c811400381c05801c00000401c041618100451b464544541c00317050522a96041c0100d06c03035060528002006051a08202a0b00300801e10303516620343d000e80161005d140451000044000a006000c00d030b840650307250b500090006102da4000d020b840d9500d15582918a1503c03151943d640d58407049c081c1d1540018070700000c000519154a05804000015003030341d1047c10071026020003a00070350300c048040f64174001e42081c00b080500c501c0603524001d040180c1c4604290b201c1c0c4035400381c000c0c9000d009070f407a60440740c04c1c42040015800c950354 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 702085917 1250 702084667 702084671
    0x80612010b0d06091b32010e0f0d02060f1b03090105041502030903030703031e0506100e1305010609180c050d0f090c0f050f06121b0c0d08010315050601091710 70
    0x15603810010b84442c415040c000c1c15652840048401c250120000004448145d5900403c0304166040080020402703d4072a4029801c80f0507900503200c0700050660f5600600c0000d032aa450000c85100c680c0e0421001850340d00100840c1e003241e03130040142ca0554003143c04099581e18600001e134a94400d018440341e00d48800b0031031804159260708221110071990080124103904d08000c1e200380ca0064030010b5100701c3c44071009a40700d110303100102c0c94101c0103140c8d45070500c600c49600111442a0001c0d0f0020307440c0303881800450034146400203c1601214100450802c040c4020160301410791401c210940b17400c0e540c0b5080206800c10f0b0002900400761949843c1c0c2c80900640702011031185501421120046410625005040e20543e0824260140540d86d41d0306200f20800d000c003e10020000c01404242c000000400613132014510585501040394198201a401308003205040071200b404d0078100030450342d00560640c2280c01b9211030081080016003580d0410040203e00c400d50340c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 702087167 1250 702085917 702085919
    0x803070f02250f080d020a02010e0609040509030304050c18150105040806150a08010c08060d0309080f01200a21021b06060a060c020114030c0415080612010b0d06091b 73
    0xb46030911078000c9400c203040554000c2c1d83c58502a4039254050290809a040010280095406096200d81c1280000c00207450030101ca000a000c5840a4441c244141e20200420003084810042c07042c00c400101d45180e220b03480324448140d17000b801454580844820071075020a070740214199006012a03000f600c0640c6030020614900358072010640f885286850400210044184540099030ba2a50b071054015950207003400f0703100405810440422003400e034006000380c0140001c1403600482d10011a000c250380044200ca4100800c0e440c0d5955810008081040c0d040042c019034002480240c0e04030f02040580b402c000c1c013a4008100488020f003074001000040402c5852160008960402e40c0b1071b03c400044a54041e0702d440240860000744400001c091000081c6134080c0e003070101c040c1352a031202d440d01d101a5000e00c00402049080b1b042c802c00b89011114494003440e020000c00280342c110001881c58494000701800711503035031800310b050061704c5081d90240304004031141c41c55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 702088417 1250 702087167 702087223
    0x1012061407080f010501080105030a0303051b0412030306061d040b120d0201092a05010c051006060e04200d0e0709110415020706080714070b040303020d0c020102070803070f02 77
    0x5141c103c0b24800307044818000401c0c0e40d80a10ba809040c0c0720094002c2100c0c520f1035070141c0c008c01d00038092038041740746070f0001400c0f4030403000100050701143d1b80c007180114461a010b002d40d05103800007418403c1c20500d50754603041c40c0d003014244c42c004680200d144d04202000c101302c55101048488540100300c00d00e01ca06405400044050f841204006a40340c00072940300d190f0040c81483c401100454642009658403c903e6040d103207010750259a080c403550700400044500d10f0b4080008508030fa03400311000e1500d841400600c40e40c040495805814012969180303205540c14504459607d92441c9404101001040041d040b90141001108003001554101d0341151049101c182810450418824404582d41c801c0758041e840e0192a625107200980e242510444500ba0a810520040307000c1100150700ba40154069103006139191180d100c500c0c00d98005503150815603004001200000e85580c2c01c90364801000e242400740d1082c4120300b00d0600c20035800c0304006440c580d1102000e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 702089667 1250 702088417 702088427
    0xd050d120522111f120902030a0b0c130305100e1902040c0504090e010222031e0201030f0519060f03080306090907030f030e0f0a35100e01050702061012061407 70
    0x50007130240c544c1e0324545c212030b801c2e00c20b40c0c034600c2000b505900818142c00c0000d0548182e00c0d041840800f00b60b04290310030300080d064070b0040c0c1c020b9400d6446050320310030701422886200c034520310b01d0008c0c040070341035402c250b200c000c40c20030000c0c05540c1e0348500454480c41081644d001c0d00101c1c2d003e205151410008030b01075005000030040c0d2042d2080d46d21802000c5580c03003800c03203501c03c000300066a0510030340303808801e5401c0260b042c581c40c1c0c202c5664417012841043d1180b0742010407003440c4c40012175520b0841c0ca558002c1e42c4602040741090001c5000e0005036548044102d401c10100c1c3d69004000e4200402c6900c01410521400783ca442016004400040000c90035100304c00404055000c0100f203284610400400c0480d000300940d04100b4004c0c81d54112103408050440d5100c081c0e215850030120140360340c40300f5541d0f02c5d00c1400d4030080c040c040d00301e12988014034290074400f040c0c0d42009460711406001c501800010010171100f504450b50600300440c0ba504186403074080644 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 702090917 1250 702089667 702089719
    0xb07050c0906120a03050d0207080d05100e07050d0207020a0308130e0c19030209030c120d080c03010b04051318030503040b0601020105090303061e0d050d12052211 72
    0x8070805071100007507042d007401d014031540e100354240102242040d90714291842d0b4041e405000b91181c0801110300441c1245006040600c0b80302e270300203890300d0b00d68410140c092940d00a0f0340d084013801d062080703c5074004207a46400180701d20040c1d40d103205100203000b00b030003039000078000304003c54220041c00d46080740b2000c48002060354082e40d580c1014000b0b84c2d104210400816050748108101c0031032095024285102000d0200d6407403402c044001803408004c014074124581c80050901ca803079611022140d00a640644060704550405401040900130b50186d6401004513000c00741503001c0399000801c7c050340c84811203c414610b42002000780c2d02c21102960740e000584007190040d48144101442200000041c60035619640b0810982202486407481d40114042c40c20402d0340c0e9050781c41c101248500c0c020503030000040405030500c1d16903928550072038903100c1000000200303402d4141d44907100c030826040914107484c10704400611024015048500e800030384040082c03042c213800c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 702092167 1250 702090917 702090919
    0xc020907080115051c051315020406021005100b0f1209210a0e040f0e010f02090306090a0c030813080a0f0b011a1602060c0610030615060f110102040b07050c 69
    0x80c1403440401c1d0190380d03034817a1030b4105421111404e4440d85c20b003040d5010300c3e002462091400601d228644600030703030301c404018803a03105034001010080990104441d10003603283d0f607018810b81c07410580382e4030000d142d841966001040080c661420900010445156054500d1204154100040c0c0a42c0d540c5055030812110700300602c40c0603000d0100c0090390b150780040e40d00d10400f95814030034400a4200b441c0303030030b100540322030401000f1002070160b101c155020041c01600d8030b80d81c104040c0740480182c8191803a402011200010132000610b90043e650411020741c1d881c407520360b480724a0112540801d11600900401200b004000a08400802c1c020070300e040c01c6036204d81c1d0701280701c00ca41c1a494051a000c028074801800b030080c8501c286400181090b003003101c03d452070b60601c07104841c0d000e2850407010060081264074030031400c00c3d1403504031003c0700500708140600b64003942c51203041846410b4450117034000003501240d01402c00d41503800e480340e0a03844e041340e490082c60945 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 702093417 1250 702092167 702092189
    0x1c05160305071205030318070f060509040b090105060a0509130e0d08010806010b04140a0302063007120b0d150c1101092102010213030c09140c03070f0c0209070801 72
    0x241c40f00124883c0b0703010300d0f00312015500c1e54694102003048201013400c0c00a45000c0c4040015800117118114802480251511076445514800b04004c0380ca40301601c620486903c0c0050000391690020740d08a56403900f0066540c80342000000e0400c110421000c20050030700703c1086043c8404141c4c100d2144080d2190342050340ca400502d03840310700074000c2c40302c070b0300c010b02c030800440850b9031a04400403005408810343c076460343c000c100160702c82d40f89409072141960483c0220700040c41040a00744400e04a407003e41044000180a168840000400c10391034030144206940c034070f14010356082e4000b50302c40035000c6900d00d100150075103e10f6000466040c40b443c2070100c006002da1111180c0c8501c4220340b101d807030748824065480c4444200b085641c24000760b5040f111400c1a00069030249100c80030140c80c0240610035164590032007081c3c5419401401180c500305020f89400180700d00380314944003a01c0104031a070140c03080300070754041c1207a01840b0000350442c00d0310381610645812 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 702094667 1250 702093417 702093419
    0x616030c0207030314090a1d091009110405180109030e120703080909180d053a020913111201170d230d0c1d09061c0516030507 56
    0xc00da0b01c5a41511015010407140180d0320f99200109004001da9031009003130a01c000c3c0c40710301c0714a69800392031420740005415401d1100300c801c10040810041260318060101080750754481c207012200092103400385e42c0350004210041c1036503500030700d4858000001c114140303203030800030030f0003001c1d00025005801c1c0e107210500542d0f01140744000e803600301e01c0c200e141c18010024030444032001020104001501100c59050f800140120210051595603440d2a6040b000400445030b24608001000d04e14040e840d0108151524007107200030206940181c8810444000c0f5103000541e12960042a192090452a03032040401404002e1400120902c89a8031003050442460100c0700c0003c3c9a407100e5a0300120364460000740010300144600c0030340007550381285a059800001c201d40403981c540144640d2154040c200758185054040c07004101c002c0d90b008035005c06030141001d8012042c800d80c2002c1d000c0c00000c54102c995000c4202c8000d960909a007031900c00c1203000c2207400cbc2c050144 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 702095917 1250 702094667 702094691
    0xb090a0c2007150513060c0b0a1a040c0203161b05090714030a0b06030a05070206070503070f050903030f0c0601060e030a03050a1d0301060f05030c0301090f0f0311061603 75
    0x11081d0719150403001016024204100648521101140380c01042010801080005d6460b06840d00070200b41d101d452644a103440c01107a4140010800014076180880007102d0500c004401319002100340e50008081526003012030540c400c0c1c400d43e40460903a41c949404200101d280705190316a0002d02a8407a501d032800c11004e02002e507000c1c0001030340701a42041c07615401c0000c40d041191000000f5030a0240030100c1c0a0360821140443e41d10343da0303030400440325010b01c800740c0c0c808030030715100d807039481c181c140038103200c08080030601080000706400744152010801c46075a4000062003075150111260050358516090140d0780000700c45280c90b407524180003400801e40b691603200e407400d00c0f954040456108400400c40790100f205151064040c0d00c0a208034409010080c1d10161091305140c24586808610758400c5d000342c1c503090345400811036112009050b1342d0b0185251140340510304080b40c50000e441d109003c90300503941031211140140046001621040d1810b1084105140d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 702097167 1250 702095917 702095957
    0x1305010e12250b0103060e010f150b0a0e03010203010807230d0b060607140601090b090c03011a0409020c3301360c020f0f1b040b090a0c 60
    0xea14903070076062040601011003200164100058a00c92604410554541c100e1100003a84243d610564400030500340e03840a0042a80c051140307002407080804014240c020240b082c801c001c07074503901003401012144030700444084540010025522540c41320111911925039114040740c04101e000340c414020152400823000d00c10081c10100c00114584550038281c00003032840e44d10601c10040303000000c03c0c0e00320005004030001c0c01400700e5810550500212021414260300c103248000400811070004001c03070703040d00c14000910042e03d00005000640c0d006a80110907040d0000ca080c90301d11800240c1c0c007031002400d9016030741041d10500e0741000640d5018000c141c0400220050148001e0b002c001c81c0201c840484054130003000800326a8030100006002c1129a1121181d00140350f0401100c41d024030502c003c0d101d51914451071603550b510306601100560145000c01206a480758070501089001800b200807510300800a00e00600320001c8110104181e40c0202e11110715030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 702098417 1250 702097167 702097183
    0x61b01061e0f142e17090c1c05010603020a03030315150f030e10020d0b030606040b01121e020c16090c020307020402031305030a050a0f08060d0f020a09051305010e 72
    0x4040c03907040a010030044c001c642105001842400940103400003180c211320110020401d030580d00c0d4130035185070000b002e40c03c0c1c1c4080d2030030801341d20030040c0da001c2d603075001c03240c03482e032035040d1a45d01c0400d903545043ca0140039241d00103948884000c10000a03da0036812465903000201001c00c0c2c002e46441c4460144243c04014500052000e050009000d000b41c0c095440108227030f0032140034071510740c0c03400c060342e0058901c0f0031866150841445241010044140c004604230f409000035039184000074015201c1101001c0c40c0c0c0c0d111050036180034610188078007a42c0e149403042d5614140c0d0302055507070b4004150281d011114100c4001141ca0b1940b007081240422680690710f00402c513020070001e900f0150800c001d040b140190100010020802003d0342031507511041c0e140c45c14001e010f025003000f40003900034801e94004021481ea100c1030711042150380020721080c150043d0004c5164a60745411581c0303254500b4084c404c1c801c10110100c1c124510403002070121b08032100c40c2035110400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 702099667 1250 702098417 702098429
    0xc040603110603091e160815040b220c0501110d05040b0a0e030a0c0816080307080706020c0a050606122808210106121505061b01061e0f 60
    0x1205005691410200031078101001e034081700c206841158034403400007000b8111010703541c0110641e07110804a558124000d03c802c4011b800c1030503545025000802c40180000d0170303001004001003a0580007010346501c40005101200e10444034074140314094038500441780807541100040074045d50000388103000c8181581e44609103450b00b40c081516401010240007841940306c0c490041c3d890822541c80054062006c0440503403800c0300715420464400944800b0340480300081c003d0300c500100302d520302580071001d40d13640c00c91401c00c1c0000380a0340700010f4a030700a440084041c4100000da05000b194100c46c0c14101050947e0402d94400e00c0c0700312040f10191100720428202064018040011700903001145440001ca040c0d55484003100c0321034894100c8000107006282c2c0c005155550440381e0441040705040d01004102140c90504c2a64441c000001d2030b4600e0001024400d60384851220080c0415030b100c20800c200c0c12000540c13840060010040043e0420a1034003040459503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 702100917 1250 702099667 702099683
    0xf040f0513090f0803060307030807061b090b0414040b04051312030b0a0911040b0c0304140f06030f04030e040204091a012d020a0b09030c0c01110c090414030c0d020c040603 76
    0x50594130782070240c00052045615004801c000804940442d0090290602c19100000c0c09600c00c038500d4800001994428200326148a0501c01c0740882d0040305c0c00e031031003904810700d1442c40c5400a006810400d611580090030030050201c2d150300c2c40c010043c0180720b81c100c980c011071034030412402c844003a0301d410b038401c00c3c1e0700c01040286950b42c071441c005c0d00090151403810b038a40d508103603123600252003010300d45e00001d41003001d00d030951085404c0386011100c0c01c0c20748461600040d650300000e4240c0d0b03041c04114020a040600a280003008420060710540d20b0344d030344114600041078008240118914802400701c03a83d1702c515004100c032400140315038505d200d610f0348a1000c069050300641580b0400d0801c402042c040c9501a01c0703400448020341d035034003800456604000303020440030f05000351091501d800d0740006c0b40a000c901003d0310300d842c1641d2241400c070405901608c0301080740c080000e4201030300074085903070715160303406400b116241115a028001287c1c003030b00c0003030031501c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 702102167 1250 702100917 702100943
    0x2010306080318042705031305091314070f0f08160503061305030d18030e22151208121302090402090c0c15011503050603100e030f040f051309 63
    0xc035141c1e001c0d000c2c13001c40305601d182e800080e0390910351010422109a40680c030110b0100e03c10444024130001908045d240220ac0c0e040246c050040710001c29001070031a03104013058080780c001041004010b04600c03000601c07059580180b04a100714501401400340100f4465018642401c0e07407180c1100d00c0030307009092a40d81d40c11525000c500044088a06000820141c69501001e001d4002017100b40043c1148403515450050201401c941031b00d0300078203c0c1e14a04200d043c8144480b8542c54001102142110a040850400003d903030006041440b14034014004d22075414050f0002c507503d5440804562600d91180c0e41200c11488020f40c00f0744071500080040c100500019003290303036038098a0070440f00f81011810440180ea240950000c020010030003964504801100020036081c100001c1c10104040b0381c490030560107482246441c0e0079907003194181001101c810f0131480e40c100d500c0320784419604a084051b0f10800307100382c000c1c041140192019204100d034541c0c0c001c032106040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 702103417 1250 702102167 702102169
    0x10804020a0905040312020d05180105130b060112060f080609030c10020d0b060a0e040507030b03060615070b01060503060415060c020904020609030703050a0606060f080a021804090f02010306080318 87
    0x103070100030422030401c00b104a00242c10191b5001400e07840910400c045100e280c43d00d002200b0030710040500c4401d070b04090611060f4811001d01c41c1c9110303000310303401460380e54020050b64018001c0701400702103880c2080c0040d0150855402000f0f461007281500c1c0140c50346c69040742d8a01508610004580011201c41c54400c0d986d03004104008071000049a0418030600251880d0043c902910120704010084c0109213401d00c0b80d44d80c0455681401c004600303401c004031303642c0d440040106005000102a02d0040c1d4110f2041e40d0440f94072442c01241c81da19100300400d907406c240d500900036410000b140100d000504a0b100c01e80d108c41c0c2c0c034081440070039020042800030103401030381c00c514100400307401c6407000c0c807241d8095400345005001400c0180782410844500743d000c1020000c06801e00022603a02085641d08007244060150310f51142c01d0610319220010203c044d40207180000880c04c00c514100c8004070305000b40c030100a12a5100b5031a0344034820ba90010710b05000038000081c207 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 702104667 1250 702103417 702103421
    0xf090605130b180103150b0f070f0f1412030c030604052701060519150809010e06041212141603061a0403021c210c150f0605010804020a09 61
    0x20720041c1da4900c00016589006514699124034000e2106842d2080c0305182c13960580121090001003039a0101d145240084414040c040ca03107400b03209100025444060004107144030007620740019450444240704d28103005104d030340c04203c1358240504200e049021045c502a2481b0341d500450451440c0d0352031041000515000b0240c04a42580001117029040070000b0041003d450380000607085050004000003600384060310f0a050741e40d01001d100c80542e603c05440410058103010100d51a08201107016000c0c1d103031040418440c0c00d0400c01402015031280c0c0c4460040d80700c2024043d0400491016a004c0d07415401c0d6448145021400d001840030a1960b841c8092400040d0b241c2c41d441c2001d1101582c01403241a0500801e05200f076240140c8402c010303c000c0e9005030a120302c0d581d0307080c000394428451903410000c0410180d00d414058582039a207030f41e12020007280d00d0b01488504008051000c020010720380342c080c001c03655500800c2c180b40075039001008074182314581440280 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 702105917 1250 702104667 702104677
    0x5010f0b03220219060e0307210b04020112020a020c0414040c030b090703170307030b0a03050a0b040804260705180c0a02120307090e1605030f0702190305030907060f090605 76
    0x1802c012003003042054900d02034416809080325070345140c02d80703031860101464603a0355000104407000304d1121141c51896024509e4110780d01940203881590f881c00180ea00500202024298600000c1d020110550100307601981d000212000c010307112a22007914488542120010314801b82840e040c8049110105074590115000088030500c98403640c030b1105001103600302036400c00d400710502070226018000d8001c0701c1010380b20028903501e503848169540c042c0b4000500b02e202e00c0c1c40031800b44049030041700c000c1c3c1121070403665150410a8400f228103901b6600c02100d000e01400820b581c03070410f101030704000c02c0030406440d40d117400c091580d242c1c0c4015426000d40c800c80e4031003001400f4400140d841000d2580341c0c074442600d0102041342c0711400070304400c0c01c144443c3c880d00b15580c200050740c0d04143c1010f00c404060756051816883c1400500e600410306c82d0b103840030030816920000440c452942c20054a441c0c070b540365000c0e03e03c0101b41480303074003048007007105000c0346204d040644 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 702107167 1250 702105917 702105919
    0x120c0c090204030b180a30020105010315270218040f140c0a23030d090f1a070609060b0339010e312307140901031e05010f0b032202 58
    0x400a032000020018501b000d1f0360080c0143c2d445100400911501046c4400440d1304d21505004d048210400a0303450b142c1c0304400414a3310b075204d001c0964440c3d50800031410980d800c080200c1c105424110440c00c14040100d601d00380030100962180e01c042a0761550300000341550701800d051210050031440089030350f05000109803140d00540c3e070100005041584141c032600d04e10342c140884010000c01a0308040c60401c0c0c07101c03969240487d2a000c60b4000342c0c000d000025559010314001e0042c0000c280034071b83c58420303c0b4a43d045203513079000940000d48008221503418495070000350500b0602c0031400c0c0030819007540081d80d0700700b0310b501c036048403402c6c4400303416a03c2d800800d02c20140d12213440d4504030f66482100603540e1601240c8034442c1d1828403c0366003407401400081540070140700280128001296150700c5074002d81104600f014500541c0d080e03903103030000e000000c107403d2180c0104000b0302c0e0800201760341e441c1c0440e401840c0029400150807403000c026824074007000412 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 702108417 1250 702107167 702107213
    0xf150114030c0108070e040b030d09150503040c17010e070602010219020105010e01032607050c010909141b0c011803020706050414060f2b0e0316120c0c090204030b180a 74
    0x1008e210342c3c081c0210405c06403c1e4980c840602e09041100d0040f1011007402c00c14810708005020114400646e1a01294000d002c615103100c05007450601408250034025034620407041d0120304107070190041c0141c610050040714115001c08812800c3e20028410542e03040e40d0000140085255000380d01d8184c0a56800b030345085210a802e480d50354003500c0159036603089000508480e40c0d00c41e00b80d00003051190014071202c182203a03035004070380c030140490312080341c800e900c01110100b10b000c0d103611506400080010b0255840e610340d0b0101804802c030014002e29201080103800b5a00f5034064803030400320301d51040300e50030a000441d40911100441d20805001c40e40d41c06020a00c81e0080d800803000b42c1d040101102170100c155001e0044000140d00144403428803509648400030307016401500c8800001c080000c140c030078105504010704001048031000c11340c0c441d03d400400131644902600b09850755141c2c030314030800e56100780500c03070340d0416070708140420004215040248100d41c80c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 702109667 1250 702108417 702108431
    0x9070207140d081204060b090f0103150903231e040b0301090b060d0c031b09080d030203151008070e090403051c060509090c040612020a030209090f150114030c0108070e04 75
    0x44008482c4100d0302252195111400b076080c0381081032350640c001a611400fa0740950659940c120502c10305841d0014030360740c42102809051044810411481e00c1e04090300040c00c1d031550b0116503510050050300c6042032004002e40016480e41120202c4011054050a40e42459403a03c040e0070b0740f8800542c050f10510031080c0d2009a446a000e2008503610300044032071600001c040741c4c074440074a5030180140c50b00108080d160124000c03207000c0d028a03005941c0c0d540d2a40f420403500c5110001600100c1403840c00401a801444a6001d96959201c4001c4848800208000704208650082c0003c0c2e0a110003801c3d41c000c0c0e003a8644480300c1c4400850341c55182c401180703180c8801c650038000d580c001e040c0043c071030038a481440094424442c070390f01908050b4010a800c01c201d844001c0c042d4910f0720003e01c4842c824000880340300300d40701c240c511b844044001500280000c2c05010110030383c0c2404d5152600c4c000524801e1740c01d06840d404100c1d074030104c0680d805182d0185064005441303050f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 702110917 1250 702109667 702109687
    0x20d0503040902161103060601020601090209040f02030a0e06130f0f050c09150406050406051f120e0a03170709060315080304120b0601050c030d0b18070e09070207140d08 75
    0xc3c06611380070b40d169101c00b50389405c1800c038042101c50542c1c0243c1110080c0100c40e41d021440c00d042d03c001c04005640c41d240600441c0040003007450002c2c0322440801402664017468010340c1d54400b602c4120381080c1c49644021204130b1514000400c900240341c4803100140840d2403080a150042c800d491041e251f42010407102201214014804000c0c22490030744d514080c81144040c0000361020401c690400307011491100101b03022010b85090112280a90392043c022207070000c84200d0f041c000448040f2215a4404a1080c102c003c522000a500080c44034002014451240c40c1c1e01c81200603c1d0a1050300109464200303251103101400340418007010800c0140000d00d10940641401041030401d0f0040388000b420490401000f0498085070340e600005030343c1c079101c00c84000940300600c00001100c0c032074003090000e200800402003255580d0016200c0c105a1810707200000c0d81c0d940d60000704e85951150140c8040a09a007a00c42803a0400310480c140180c861050181340c101d03110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 702112167 1250 702110917 702110921
    0x30b0708010302100906020303010b16150203061003020c031804200c0f07081b04090c03080a030f0203090a2a171b150a120e0304080f060112020d05030409 68
    0x150150081005440100b0450900880804900f0700754640320941c02d0070704c41c0094403803006101d604442c080224181c841100707110249001107600443e41d81d451146001107801941040310024490070051004111181c006d00031208005881b2010310304e0102c0b00000c0b003074898a0050829001607840500a8003c0d00450007010820404659030b500c400c40307850118075001890303c1680a60704048801c010a0130005a03558141c20840d0805221f00c00f820040380c02081100300240100d1200c14000041c04440710003020304d2516580c0c244503010030740389110144e1005449220b81e41d4045002840800c80c0301e004604440c06940710295080c1c075072000c41d048a1a660043c40d201280d51580b280007000400207541042e04902100c3e0040c1c0b80c4200003815042c0540842400840005904030643d1044280c160100c4116408001004142006643d45d8101c0d00445045116088a20350040c0b40020720343c1c100d450b90112909448116428080e207800103440c01c5490384001e20010031800154 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 702113417 1250 702112167 702112171
    0x2107030807121418011a0a060c030e060d0605010813170a0e18010509161d12010921050c070504020903030c15070e01050c0d081306020304080301030c0b0a120b0a030b 73
    0x40c0d4400c1a8030142c001c4c4580c04c4600307506a246030814054850080c549881c0120701c1220303a10308015061898a090554181c403552001b154000d000003181907122440b0340c4140305892080c2d03910800743da24001c1c681d45112005201410f0400d0a403000c07189590880b0043c01110b942e842c14904c810107074404079080c600406070a484062809005203c1b5003804145264012540b0f0951081050100700117450194590040d503280d03a1031100c150b1054503013080c8490701d201440000c01c0024610f0900801e0804603510f0004941051001c0c041040d108605681c030300200740010700921454041048001d42c00040ca40c1e41601040c80155141082400035404240040d2034007066071509402c000c00800b88000024140542844001e81501e800101c0915a00740d0f410300780d0840d20ac540b182c0c00c00140350f01004000500010030802004482030255048902c20710b2640c1400d601c60f40b8039030b01130054103040c0340026007a0340d08140445003034101e003802503030103000045090b459031113100417500d00f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 702114667 1250 702113417 702113431
    0x213080a140d02060f06010815030307061a0105070201051c1d011b1b03031109100513060c150213030b09031b030c0a0b0c0c030301060221070308071214 67
    0x41201c0c0d44041c04000e02800c01e142e1114405854603180400c20501340300c101038082030400c07142d200003a40e1890000740d14409050300404807511075003107290903c00b4050005450540502c65820409954081d8081e1140c03036505031912410a1a0103250015034200800d011a02944821007421082d500c2803540325040308404c0007050390100386008000320040305000d6007c001c0700048030f620005402d00710b061500d6140ca408101124203400c5c0034124010910b00507803000b5080712010840c0d41000013800036240c03000c3c00c10b2a20b6078443c0d0030f444402c085d500183c0309180242c050600300080d58002c082d5024001581000d50789c0780c5d00d908040290464107861558400a0780b135036400748214104080842450040d0b240034404210360f80c5648041200030100c41000c008919031074820415190340003400c1381105c0d1a50b0f075404000303588a002d0700c078104c101d110b02480040e02c072049404070380300940c01da19080030300e449048003219001e840d40c246044007541c40404403442100c2100c141d01401d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 702115917 1250 702114667 702114683
    0x1051c1b0c0309050604050603060f03210901081f03081e0d06140a150e0402090405270f030414031906021c09111504150801090c031406040213080a 65
    0x320b00e40900490141e8100700e01c140c44c140b004100982c0e0303900850768005c0003502e1070042c00d0300c5000400d1910100c0c0c0300070041610f0320030810f041c0e008660043d0a070079400b683e440c109500c0307402e4950406070b5142490062410004000d03c00b090324940240101544416114955182450060480d820890b48032103142e884030403c200344002c0000f01c17003000d82c084400c030783c455140180700c0131142464100c11040c07080b21a44164156180e5040d0340701544064420b2200d8607107022212010b1084441c084010752100c5007007080144e00080031441c0500a1000710b2600d810000d103010400070311201541d052092a66000d603100208001d6564188102000b5031520682d0007041502c91804006090851800070100003084110341d20030005501560215440201008046007a100b281c000003005403c042180004aa0001030305048447e0840100a0070800e044110240c0369020310681400d100750b008a00e280c50f041c1c1c000c11190001c281c400440382c0c0d071040704a050224491060322240c0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 702117167 1250 702115917 702115937
    0x507170601060908010e1b040209190302011b0305071115210105030c0a030b0a27030201110721020319031a1c030509031603080702100e01051c1b 64
    0x2a400c50b48080180900c40000c2c866120500c030706d03030703034030840349800940c60b105071603030040d041c0c803254100c1d200307001e012308400d00e40170000f0b5120203114901c0c401280003c01081ca00c80403801001d002e201c600303501d075071401d2401d0000c2d15035641c401513000407994001081160100a4000d072030092940c40c044021102d0f18108040c665160070005900850080d08881e40c00c19242e40c07800c05030340c141c0c0d5002d50480100c0d1107004c000d4008041c918200c514020414520803500348020701c0f8603c0b900d00c03d0b40240701105501600b842e481c01340756401020228583c010221034120804409504969441140e0801030f103203a032880b59101900107130300400e0756010b03e000307109000c560302d03942d903407064803201003542d0801f070690a50404070601608002c4049074175003e0307690920107080000e1114040394021074a070306120840d0340c88210202c1c45910000501402c503400340442c1002c404050b121035081c0501182d0303078928280021030b22004140c2c0e40320105249009001600ca51004170354441440d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 702118417 1250 702117167 702117179
    0x60903020d05091014090312070b0c041212020c191d161d06040603020a080609240102011b020a1505010e0c0a03020c0607030b190e130507170601 64
    0x800403074414141009070810007207580340c55100018900103804d00c1c01030071503155600c0d0840c503405011282940f5020704083c6104900b0104064100c45000e90300309074507034a0f03407803003681c03a440b543c49103103920160001c4990104a81541d131020300d0482c0d0055800f02441c040007e03c1c07102c103000c1d04810030219028103106283e02d840d0038035001c00c001185644103040c00444c1d507a0541e0311031148803c000303c00d000c866024110030000c1c4100100a45099155900c40d000a0b019400c503404501c0041c41200000d215403401540490003118440c00c0344d500c6100340c036a9916500440d000c030300c1c1599240c140c400710360ba036115420f00d40b042d081d6000c0c01e12401c9034a02054001c1450b00040340060412005000e9440c0001d005c64001125240969503800c4508054000c1c0c020030b0b48080007030250f001044222074040d0840000041c003240d500c881d03000b2001c4205003c004038040c089960300c98000292400c1c110043c000f5480780181c003140c041d9591851403807590301d0102d10901c13190f00510010018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 702119667 1250 702118417 702118423
    0x91e050c0a1106041a060307170601060e0d0b040204150b030408030405060702060709060c0c0801021308011107080318030c0304090b01030513020607260f0705070f0506120a0605090406090302 84
    0x2c070a18500203841181803607100e2140156800708070074400c01070400460080d680411170500204200900c001032100c005d200a5141d940c02d01c121004a1019860b031000c61070000322400807150b00c00000e2040d6156602404000d01c1904c1c0701521850040c07501082d80d14498001e0342c80789100311040b030341c3c07450146405400d248003d0840801d42d80103030180325503d90048140015030311207140601d0091101c0c2007804002150764040c5400703510000300500241881c440142c2600e0003900240400040003c649403544140d072400b800014041c00460803003030464488821440e0304208403420030005030091811036000e03500c0b4070699a07a17440c25203100d5800d805240e034091000c131044845441aa00424442e124100c80200b40080902500f2000f014980148a6418000c200c3c240c03143c3c021404c840007035000c0e03003054942c0d1242c100b0004410303c2400151040e20005030040f4106600302d07142c001c11704405094902171507220400468551600f44905118902402c0c2c0440d00819505000c0e003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 702120917 1250 702119667 702119687
    0x30b060d0209280326070b061503070e0112060e0f040b0609150d060e010509030c0106081603080c0a0f030e130b0906060a090b1308150907091e050c0a 66
    0x141000d4030f2407000d0009010180310404907908148a8102c00301c1c004610140101d1542d07500100420101c0c1d11018420350005262207048291400301c441500c0440090240c041242d05c04c0c0001c0d42091000502d51280c0c10700c241c00da5030444040780507600c070180701c0111802107a42009100402c81003100b40001d811001e43c21100c140d0b15090141400100c0f90f0f00a01d5010082e4017504030904040204021035100d036130284282c5000b00000d0074890f9035540c0b298001c99a100440d8200800403441060100b8011640b900d201405407000b0b2540d038908043d5005034402d502c0d03d0040b64070760404038140d4110140c80c03501c00c2d0380b01003c22141200304801540c0c20b145040d051442c0c80d20310101038036a803d45682018085030f034280c881c81c10080071209071995400c840d00d04000400e0170b01030076002c10503510a071032a0740180d64014416103080e040309042250080c4c6036900034103080060341020760048114680c3c000c10481161855140241030b120300340c80000d202c920002d40040d00030790060801c0b07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 702122167 1250 702120917 702120949
    0x7060e031525090605090d03050d05041112010e0d2303010b04090e010b0f04180606031b0806070203040b07060e0610080c0409022803021815012c01030b060d0209 71
    0x2080f45007440e800602034000d940000d8050f1801248a6003414021011380d0340826001006001038680b52030044c080100c5484005c6c05014041c2001e102d401043c040c45004100b04001403d00b02440c0030215010400303003d00501155120141c005110015130045000c2e1445d1080c0d144e0756450480480222840380041c030380da592500f00e1030141943c410102081c44002101c003c20014802400121000c2243d20700a002600e010030000810603500c0400041c45000b103500d00240e9918202191104000c48106005810411003030001c03465010240075828024080082c4074000341d1580303460880c080c1d41d4000c240004050820a80008000340c04800e0000d84062010365800d074003080e07254540000104051600f981d03030700c102d0f4130303d81c0070340c00150340041c005100d01c0600c6203004840c00094400e00144e120008038542d0369402010714540b8034240080603507841001e00c1002c00001d94a8800a04060f01c0d500e151001d562b80d040a04103a02c040f030001a5038501020400010480c2c2c01092 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 702123417 1250 702122167 702122177
    0x715140403120809031306030605040e0703030807110c041d010f1518020f04030308040b0106020c09040b04171b0613080a080a11360307060e031525 65
    0x1c0c0002906a1002c052030409401c101c20305441d403030320131170850150403003d80018500b06000990268540c00000417100150f0f03007000450b42005050b0749610580c08041d0114482c0d034003085040c1c1c4241d100d821041e40c80002e607000340170302c4800178064540c2c0392508a650340d020f12140400c108280714403070120b5521181000a1007800712002c95914080c4528903040c103040f009400c4c85c17030964040b22000322486031600e03070315a04c13880d0251070342400b03030b900381c8208a1b210000b0440720300007d484076111100811080d078a550302e40d510492040024000c0341ca91103504e041c40c810300305130005070110f000c04d048100e03010b040e69090f0714a0103d0040c6680c502e040003050800100341250200c0780c070740c9a42c1c50408403c4d034607040c0f07e4000c0c140709620f0001c40380b000500882228007580b560340c1c03900f10788041040c0303008078186408280340d4191161139158200c0401008224001c54407c445e40d80c010b020741c3d01c0c0c0c05011504e414540340403aa03613015085018642a07910402c40010010100c6600300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 702124667 1250 702123417 702123419
    0xa08040210111c0c051c1d0919020913231005010c140d090311011d060a120518010b0d1a06300c0a0b03040b150307151404 54
    0x4039036607032400e080e21802419940f094665038501c40c19520844e1508502114070f003141d11281c0d074040a04e620b0702c1c1c0c00020542c0c048902c0350140a410340c0301d10880205840c1c1c880d2641102c000250041542c2c030b401561b403c1107103060743d45501007600c12200450000151400380d0805807405620500c0014810b40d246408015803c5142408041910004c1c6048400e15800c0c1c46c010070f003003a50390078803030541c420300c10701541007540030b6441303001d481c402d00d11074481c540b031070006685151161030700414000c00d074462082541400c1d000b0f81041705062526a45100c141035402040750410380c1c40d19030b0321201800c0265452024013510641420a480c68450703c0b1032a2640100f014580407144028500ba50100d6001d594404024400d00601c0031070703460944105489000440000000c4001c501941414150503e01082d00c041115943c2030340520f1546c640d503a00d100204014015056000c0a009441c0b5584081240340701034030103202010250701c9004400b0303010b80a0f40d0b44d44502c00d082040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 702125917 1250 702124667 702124697
    0x1203060611150f060a0f0308130608060616020114160606060c080307030c0201110325030204050f0103020c1513061b0c020f0f041b0e120a15020405060a08040210 71
    0xb1045030b000d8040504075180b5210030001600c00d0245910081c420440103a020080c021020000c1141007a10f06902c0368080e6600d000340c4030090102c0d0b400b0781c800320521004020300503e00301010724620501d007601501c481c0d4a010821a00405551008407680f08981010070445200ea2809041103041c000800400c0d9920004c06100052140e02095114021608624000d40103052550b00300c00d0816100d01c0d0043d0705c031010114104003071600b280e9803034564504501910856080d10030141c0140d101004e40401500a1340c001c3c00001c1c46842100c80481c40d40007138842e964020180380c000351301d110140341019010b8844849001c00741400d481101c941441e000030406204d0799040d02e14400c07181000d000604032070440f0040d29001410000c01e0511445c04c020307903410142998881c0c9280031300b00010300c02d4800f800310170001c0b0740e4040000f41c00481d00280d100d0810400015000d031416403203d0200f100c1d07810901c403150104021006110031440c2c458900c0003c03803450b103406101c82c0c1605d2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 702127167 1250 702125917 702125953
    0x304140319020a0b250803040308100e0109090507081209030609150f0c0d0c050c0d050c100e0718050103200a180902090112020901050d0804090b0d1203060611 70
    0x807041c04071310100022501e1100401004640541507440e0150052006504000350a43e004440440c001031120000690a82c180384902d0242c4d0110f49002c0c2440e0308000036a001420050015a1188146240001c440d1070030031603a4140c0344e64805064a4904da8003e02d890719a001d4200c0003150407080c9000e1410080ca2040760b4008080c3c0c409540e5503c40c00880011441200e41e80718000e0708000680703640a4001d030007805005130343c90446401030b01070303542110300e4050342c1d40c444440c1c0c002c0888402d005e0002c0d081014007611080c255031115540d1401c9071110500c5000c0010116118401002030088504010300c1d6080030080c243c1c0792002910019000362807901232aa10140a00904d68958005501103110035901a2807040a942c48820700c1401505202080748651440340000c15036042002c1000715441c0e1062a0034140b034140a180e40244c6043c8c44440d40200d25441c00d5804508581460804070025031400107041e810010002c101d665000018401a403006100d80390811202c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 702128417 1250 702127167 702127169
    0x712030f02060f06210a030804050d050f0d0209010e06030a090c140d0609030932010302070201170601120606120c021b060d0204050a03050303010816050a0302060304050f0304140319020a 82
    0x11180369912101c4142c1d2440000361740e0118100d42c0c403803030b1300e10003c2580011030103015074002c404a031441c0040c1e800440c0c80744103502510780910000d224050092043e60050b0050400506020800208143c085040b54004440328810315440e0791142007030005c07506c130040142900c0812a016170a94002203a4511248580101050f9491085106042c85030b44180c000d45a0001d480540000841802c90805011039502810380c2884509468542c0684211801d031581a1204003150302210308116000b1401400141845003a940301030000b0800d00c1010042c0c115070320342402c42d0301050801400c60f07140c6281e40c4199030281c152420201c14030413207107402c000c04550031f69441000045840c0039008a5100c9604158020070220802c034001c8042c5050707070001000c84004803403d800009541115118003904659241410320160400c04011540240900c04a405100c40301781440d1071980998407200d07580c55039103d40d040c10300d014842e8070840e1a6030040b28070282f000e500081d2001c645 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 702129667 1250 702128417 702128419
    0xb0108040b1902040b0a08090d08010e04050106050d06020a080711060109150306110304021305010312080c21090c090412230d060e0a090f030f0201020c0712030f02060f06 75
    0x1007240082d0042c416250002c0a000e00814207544955a0708107041283c0c00ca070300c2410214200700c00080105500045058250350941c0d2403007030903443e21109158449020348217039029500c1d41c1020442d900c2e1103141d050510320460006aa45a03105801054000003400395020040f07684a040d41c980c800141c06419a0034004000441070203801d100080107140780d0000300201c0c01c2104025070510100040e61040307009a4845100541400c0c2c000100ca200740002070404d01d4500d100e40716140b1410041d64004000c1142e40e10704982c02035000350404404020862500c0c200e03003000702c400400e00040e14161000c0c0c880c001d80e400d250351007004400d200740601c410460400303000d241038840d1400360145400350400d416921001000004082c00081c041c0d18410b804400201c1c02a0600380316003181c554000540c2c021480d15541d00302d030042d41d040b4080c07007159004d0100e000220400e10800000300400700800c0441850740ca00503082200410218046d504540100700801402c0e400302c82d48028 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 702130917 1250 702129667 702129683
    0xc07020102060403030e16031211120703081902160204110a090504090203031b0102030609100b0d2408010f0b01090e18120c0a02010e0f0a06050c030c2407030b010804 73
    0x20302c011b4014a40104a0140d041603440600c000060000c02003042680450699610412441810072180d8507241480c580040310b00400000303002c00e01ca6130820390408501c200c049000c681c0454400c0680c3c00060030340d4500304980041a003185441d214054080110000c2c09051170340038040540300152a205140c015030b183ca5109003159010b000321001c050180c0004002140a082d400b8000d41049501c14011200d200108000c030800900e01c1d000c0f10900742d50389103030800c5907800c540038069026030391852600203040340c0c804d080018050f0300070780100000010702482c2c40c811013082e0745d03a03503800a0500801007411300051860300c00460340aa10f49201c103e041d8181c0c5c581524150100e1503034021110089015032081c0070104051b0300c514000d0780e5200d40e07075040c00c04200c200100c4c806a50350005003e002001081d00401c0a806a060428180d904000c1c0e041c40150414540143c0e0300782c0581118058113500003c1d0a849030000c08600d810410100d8500000c0d0101001900c0600b17050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 702132167 1250 702130917 702130931
    0x5090d0204020904180303061406031f090f020703030b0418080a0c060914060a140a0c110a0c1d0f0c0d0f1b1202090d0327120b0c0702010206040303 65
    0x3445940440c1c0a0341d80281c41004229520480c000c2c80f85d180c00d90440000c0e050031000100100c04c0c0e60230800071600141200d14540712003500c44909100d002e84100303107510001002440301d0701e902c11039101d442143e00159403000d071450000d0442e02084c0c10280304502d0a0102203500540c204104a0366900c80c000559540a0b84c02c01d5030501c00b4000d0003070915040c82075650420154106c1c810070403035400100c60503600d0351031080c1c0550340c01e5441e8680c0c070303111100042c17000d542070f820603404013103281032600c02c90b07a90b4140e103030914002d04816100855913110030028401040c0500c04c0c8248800c1c03007000c290030140550201031001802e084000f40c0c0115458200c92170075444290203a0307840d0800c02c0442c2c810030040d80000a244018000300b80c00200308240f505645c000c45034501c0300207210149014071540c003a517480c2404030350b504c4030381142a4140c9003520443d440c5000780140c071803050742d00205480c0104804c1d0b0010a6035150b04818046040141d8000030810b8106915003804a90a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 702133417 1250 702132167 702132169
    0x6050a050403150f0501091b081803030907290f030a06090e0d0e010504242303040c05010c0302100e0f1f0c08060d060c050d050c210705090d02 63
    0x64050354001410000341e05000060540d65a84100440c1c600c007a4107211507030341e40001e8011200d03c0d0007801c19020f00f92a103004681e00c25804c041d40032b0050b80141c02e03003c15010b402451908111003407a01030307004800c24003158040400c0032450705104141c1d00303942d00d0780d8070126a40c6d00400c0071107180941d000c070110365800c2844e00400083e00740b001e401c1084081d89801240d0306d100c424410004910705d04032600095110728121030540e0640480c41300c45200b03821403841d901ca1171410640030486202d1120b0050a1a003a11015950513407890584905060800c041413000542c000c80c10311692803e0200080c0d008114000700d122103a1000a0603010508203030305140003200000b44500602002c2c40c8005104014070251100b01081044207141070308042d11809400e45866034800c201e5980c803400944640c0000300f0301c1d010780c5080c0d41448056000030040e607000307a50301d040c0c50f0800b0419880400581c08180440c03c07445520950b9410301813409401c80c420401401d014403803128002d015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 702134667 1250 702133417 702133427
    0x708030c0d020a030f05151c08090405040f0b010b070309120c0305011b0e0603220507090504030e01022a040f0623090a0b090a180c030506180a0c06050a 67
    0x2001e800d440c4255070b2103154000c003d008044030400282a24501004241c1d081e05031190110090005021081c4400c919656011020380f914001c4503180da0800c0366800580f0b4038007800d401603120710b0850705021a1803138800e07640d440503006407143d0682400310b4800329900030354120803100f214528001070ce00318240503a8003001c0e60005000c035170030b000c0d4001b403801c40d84c00c0300d0395485001d95640700403607003140c104030f04d078481500c001200d40a8140032400d2588010f0040d101507104000304e43e4039070307565034202d820385d042242d0a60214041c4080e84401d540c06003c040d803d422040c580005460006c200c0c02d000d40c50080c601d0740100e2b9650603a45410200d039000f14082c2500340042e01541c0c800034441001c416078086501d0007905840c003c1a051181c6004074024910010981c60841d90342000c8040105005061441d0714401464550b002c20700f4000070201550140e0080d181518101d141500707a00205c0c00d5040940d03200380e0040020440c50216007041d0b580c075203800c0c0d60741c446903030046071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 702135917 1250 702134667 702134677
    0x9050c041509150b0906160c0605030f090606030a0b0a2003011401021612020d0605151f120c0212030a0f060e0f0414030d0c0801030501140c0708030c 66
    0x1030000e28040c00240c0d11142000706000b1600c04031401d101d00c900701c44142d081000984640090442c042c032520003a85451030160903044a80076000f243c030300d543d4845050080d0207a0107a008200e0010900c20850594140c00d54403c040600505060a0410200c5e0ba50240802d010380010315840119060a000e41c0100070140144004042100340352600b025440d8020b10410311000e00c0b20b040300e48907500109004039502070762400c02c1c00700e6140c519003041c044d030114030403039020001d4030030440051054441c0c58028a01c1090586000500000380b243c0302c000300138680e202d003132050301900d101540306c4100301d660000803c011440f00183c107016454140c80088410b1201404820010360719060b034460f80344075100d80010301c846540d4615103211080c4c2502e5400320b00d032141d000207002c81c010210301c20dc8034440d0400c5034502400810094211380d40f055841c0001031550380108240b203400d02484010000b071041030502810034034040d5015100702c510042441201100044802c001101919 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 702137167 1250 702135917 702135919
    0x506010212040617010602060420010c0204020f22080a0f050106050d03080a150b07020609030f0106120213111204031e26070906050d09021c0203150f0402010309050c 73
    0x16803100d0312208040e10000d04c01c1d90701030b00ca90403440001400362000503490302035504618080d030280c22144007212250b04045085061007400d003446001a103c610007420090300d034000d400e840b981c0729250481201c1300048500c810001241040c40032400c0030510404165102c0000b100a85032440e01038003400d41641308075804000b02d03002006168000c2030007481500a01d004002891340c2d0000d610038685240070b00c5c010000140003075801400d2a00090402400040481e40208010101582591055005000340700c00e984803000442c01d000e4074240c0c1c5214114800c1c0516262502d4114603802004e411200403461034000c40c0030f0501a2072250324058100f600300b0f40007081c1d0078000e44002504942c02e40d0411000407500e004109050f40c813405104542e44480120b40361500c1159260031134200c940445603103652401c010703543c1c0c0364940e03284245880c01c040c042199004140c24800c1c0b408886200c088a030042202a4408407102030303105509007000103100e500303420040d02d04401b1140385 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 702138417 1250 702137167 702137203
    0x64509050408030106080c07120f0215090313081c0e180903031801050402090408180303180907050f03220506150f030703030c33060e071106040605060102 68
    0x40070500001100950581c0d4190300d130f0300a2030301c610320704003028400c002001e84940e02090840d0038461094054081a00561044454519440034004c90104049d076400d0b0340b95000143c260380d90400d00c460b100080c1021070181a48100d001c071a1640405191303410000c020701d800d414807031903640298440741170000c4e1000b8011843d010380300c15a00d40c400c1e22412080c1280a4854801541c14000d00c2e00c20b6601074550120390301e660740c4800d0aa0850000c18082e0803101903a0002d50302c08002070240f0709030070b144298065505805000b1000c80250000c0104417080120751821031410088070f4000e800407118400807a081038001c002d1203000c0d00000c0c1a4011313241071080154a0081e0307580d10710411600d03001c1000301901090f03540c6040d07200c010085070384040d4007030100b032406000c203081030800f101140030321580a60310a54004100c54030860259100018454500310a103125405400c0c1d0401c00c00c107072081000c017581c525006100401c201c1c1c550000441a910a0050000042c0c9c1b155030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 702139667 1250 702138417 702138421
    0x6040c1403011d06120c1002030c1f14010e011514040b070b01060e0d030c020a03020904050304030b1b0904020a140c010e1b0a060c14070f06450905 65
    0x5070340212591080e003d0403039200700100f1258501800c4544c90314640d50014070004034444140404c003207518100d101580000d01010840890500600c9034000340c034844a1986120049000111449043d07070500340e100080040c041480e80e902c6581c155201e10645409a1055140c1190a052905da410002800200b40050380340c0005002e0502248258040403450fa00ca14084900034110018180d0010740110100302207402000315040b03050020342070517585c5840340c0100d0310001040d202142c181c0c1c000601001488081408150000204000070b249404000101005801201900383c455540002c0603110305001e6960000c407260306510700c4c3d80341c0780085200d034000c0c20300009100e018021101810045452103070341560041008110348802030602c001201c0501d200d24084690910000c3c000c20140030411001c00103100076003035000ea003030800000800c2c207401411198a03040a0707020f015410004240d4030058181d22804001c440301d2480d801d09002c000c56848800d4480c0f41c002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 702140917 1250 702139667 702139679
    0x1205090d11120d0911030a0b0105120a0c03030509090f060a0302040e100515040f0207080708131a041d09150601020a02060706090210050c0a02040b0111030c0a02210606040c140301 79
    0x1c0c60304c15000c0d00510140010340ba05254880d00b810900800d031610f03000060101d460301c21101c41e035040d1400c040f2111541195a043d1107030f80c064200741d02040010030144094944408802e5102d209282002c0d41418200302060321102a0b00000303100c2d40e00c8060300c9103251010041c100000e03d4084040c042410880e000b05540d085000069005034208040007100211500841d400349600003291490a100d075101d1141a0b00440b10016042c0e00a5100141c0640c0b4003334201c10085451000307582c0c0c0c40c641403181400c3c1d0f000e5440c6001882c2c281e820400c00c500042158150808441c4504249a480e400100e0030440e454000a500c008041050001d000e11f40c2d02c0896010702c00d40301c0992462101a00390b4050055100000072540003800090040c105600910315090060500c40c1c0344490b416462410350b00541a920100c0e449101850113510705078900e0f12010008000204540010b243d034a5240c0000824450086407a49180c040c1c0511401c0362402c5481c4c0c0c2201103841b540c41d10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 702142167 1250 702140917 702140921
    0x12907021f20010213090f0b0a1706060a051825050d110702030a11040b0a0803120c0901050702210d05030106030c090b180a090606020d1205090d11120d 67
    0xc10b1042034078010082c151507075414403c650a034078165410240343c901c1c0403100006030841c4c2c10341c1d00b2010f131610702d009900e40311022000090301008540d44558031220490314035000d001040a4400e150380413081055844000d680a0842211010342120755a1804114072401c80300040501c07880101e61917103400d9607c507028002d051820102070020000c0c42c4032450342e9005000c1b029506806c014076800c0060301201084203080c1d8043c0000c01c146e031581000802001d800c1d44000101d130400100c201c411514051010707840341388800158200340f45100000c00d540070300c9400030301820141c0c40c080c0080d101c01d0700340e0000c0c201c40000c94a50145003c40100107400c01e12030100864240f260000081c2c1c019244001a01d41015540d070401f004510b81c0314880d1102c08245400140350f450100d5100b0079400f0b440d000d03164540042001c1444401c0c010018038445400302c07a42031410060050104001c9041000030030903140c15201d02c0c612140040c20610038407000ca10700da80001e0120011a425 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 702143417 1250 702142167 702142187
    0x9010302131d1e060f16030b09040309140414150d02030118170304050607050a031d010218150403030818190b01061805100c020306090307020405012907021f 69
    0x5550060f42c0700034049009990780c0301900c485a0130003069001505881a60103886005080da20f000710300d4455030004503501c407400b502c082d00002e075499001c0c010800070507807030000f146e01681c0401104942d40d90341d224198015152012540c008440101c40d83c0d10701c10248841ca1b00200200110089035070610314944044000721540068494440f100c0445281501d00c00da81200240c4860f0b43c90301d41c22036182d0b10502801c1d045c5655507080c0603485e1512105504051590400107942d50481d2540c5042da1101f01c96251050548025282141d24888141c800b102d034135051141154461a0b000e0b654044411240d440a01c0782c090000000c00e0410310495015000d80180000c0341d0301d803501115591880d06041e03620b000c030010100b00906149c04458150f14680c5440b04110000d82c0c00070b0b04141003a0b90680d01513201281020640c505807158900418001001100e865110a00000c00e1148411324828040303010a65406545900302c28501150094000540849a602c0d0240c111085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 702144667 1250 702143417 702143443
    0x18050411010207030512030a0908070c03110a1d0a060317030106080f0603030901110c060403110411090d03081302040c2d02190c170303090c010e09010302131d 70
    0x2200340803955400031601e0300940390840080c2548071900c09a0096a074030260414094907680c00c10600400d5410001d851520300c80c0e0b8a50074001d256003403000f4031800d45030341e81e807046107041000c02c0003c070900e0400b982101450141d04141c1e44040c0c00000034601a0310140170b000702c045800c0300c140301d8040190305172091074a4060050b116107079031041c540401c4508980640c42004801a03030340c0a4004d1000b000e442000325518560b090f0003044058025500c2211001d103510b043c00700b03500d042e01503452440345e40c002e010b06040d000c80020b00b07580012440038051042c520080b680d0000c246400944194011308240f0242c0050800203000d88030120101c105400c104400b070f240e40b8010032030360b054110310b9030003000840080d5032505456502154100c0e84a0032a0100285180603d134a003503124903000d01558891625043c601d05162040b07078024104101c03d6070400d0300d0b9440506183c150fa4059403591481c0a40c00e001d48020032000642180d05000810540078024000490b400b407008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 702145917 1250 702144667 702144683
    0x10c0504031205030f010b0c0a05030a09080c0d02210a06140103060c0305090d030e0f061314060108060a050901020705100501182022060e09010b1305060f04180504 72
    0x2c80c1000c122014041641c485107000c454800410114a0303c03c0a030107180144c1003982c60a0b8450799800380340d5403146040d200405c02c2c8803410440c000301840314504064040d43d4907115400143e00040b01c01000b80d0340c81913946043c000d28a178804041100a040302d80c01101040707045102c006000c24003100740b0045801c60b04254070b2940c958803c1c050079002c3c840e1240117050918203040300740d010f06800100f412403441150031130718003090704029580c000d040060000c1114211030030500c81c50f00310514803049691203500100310701840003c2d03055000c1484100020345807190380b40c16029119141021300b0b6413242003030005581820360700040c1201d0030320451b000d001030042c5c0310006680c440d0910b0320b801c03450794560040960b101c40013007000d013201101c0c2c04101207210303284103914a155006440010b0382c07244c3c40316860078a0000c00c0d000d0660030380c0d107505102400340781034170000340384c0581405071030302051008400d07a0440a8401404103495085030f1080000e8203030700102800c4a095400c80703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 702147167 1250 702145917 702145943
    0x60a09270b03030a090e0c0f0f03010924061d0d050708100905060a0504060b09010e04150905190212010f020705100207080d0b0d1e0203010c0305060f120f010c050403 73
    0xb203400012200ea040c1c680e26a4900280b40c010800002e400c01042c00d0703032901c2d00b080147c2d070584224004014041070034011035141d5050821000486034480c00c0b2020400200682c10508010069800100c50061400d003d108a003140c07030851004e0003001050708001070343c600000304203000c0385880039038183c00c0440c0c004030f44041e0504140c44402e000541150400c5004c43c0c0216159002194003900503000407440c2051400894480305090380400788200320721041c041001910503030810305a0104070240a105240e84510f500c803690f00b0002e007a9640440442e03021034444040750900850340000030055004400c008801941c40060222014002e002c04051a45002d1007587e0364660071108040c244510204140003c003400540d150388090440d12000018885800b0b410081034036401e034610f1901d051060600717441c041241003081c103050030204446030310360072641c8541480441e84000b006c0f4210312601e040502c003800111495003000c1160500c56000f40c01001140c1c4110f0b1140c1d044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 702148417 1250 702147167 702147169
    0x12020a0e0906150d052502030403200a050105070f0210110c061305060a0c050303040c0303120c051e07060c02070f090203010f050d14010c03200702030c060a09270b 72
    0x541c43d22400d8404120910035040a0703c80d9900c41e513808069555140b013041c120007041640d5003406400400180e000182c280100949288503503c00306107125040301160b111800682c3d20005400f6032410030602065074001c0c412135030181c500d01a00500300520210b80c0141c01460550091a51585440740065440c1c01e41841402c6800d9800d140d0030068005080404101e92903005076510020015100e1102000c641d090004500462244010700e811a107189406420040640c9202e0703001c901c0c1196203540ba0390040210340d0100980c11002414515120030005207004030103000d8003580c5044207040900340c0004061082d039646801103582c8075622001c1005a110034007408503000840c1504002504240041804842c8030301d0f0301010109022030028211800c41da0390300c000903128040b1000781000d54500d0304003103034039407807481c075200c03294010a98a03001e102c011800f45030001002c800382c61007088800090002e5200c2d83d500c100e11008003800318a44442c1c4012280c3c50316003c4202 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 702149667 1250 702148417 702148429
    0x9110307051906031805070801060e011d010612060f08010b0103050f1005060306060c16051311070803040c2403151410050c1002070c0b03010b0409050712020a0e0906 73
    0x160a8110084555203400d10f00114080d0500140c001d0390008030000d80d00001c3c0c0107000c0302c009040904000220b292800801c0d044c024010b81c001c0c1d12a68801915201c2c007007040c0300d0b0a05403051804c044170002c242021602c020440c03640400e80d0790481810129010006402205c45007800f40c0c0c0a100a0f1683c0350f6006000d035050301c04840300c8038003030302c00c001c0e900b8070b4005141d10006c01000036062406c00d0303060608007000c80f040804101c0ba54201801189001a0f001c1e00307810322080108040003510074460840e11034104054204040400004c041050042c0c09001414074100c40190b1584ea41034400107100600002101007130418440860240c0100a0306d01241d00e04034101c283d14600030305018542c09540d0f8071000308003080000342c1112004022075904080801d100507680c5e1043c1c2400320700706186801140d0080010401005001d4040042d5000d4803144000041c0b45d40300c001080e150034a40309214a1040d00100340484a81c6d0003490303250498000b40d62401143d941d00c01040a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 702150917 1250 702149667 702149689
    0x210c0504090f0225050c0603090c030f030309100b0d05031909090908040b0c0c09011203111b101107030f110f060d0906140a05010f091a01080405010f0911030705 71
    0xa140e0000032a02d04084c0303004040c2c008a940140c0c10f4568504000700804c40c150300c01c0301c81003640e5000d90411902400c0070007900200b018441e008d1401c50500c268207c1d1a03400100421103520340b40d06040e01d80b1f6881102081a995026003201d60b5104a89072103c010002c030004180807812109002807414114005e128080350b011510a2500d0304005400300590012600d0302d80c0391144a1180c00079841d546160703406010b0b03510001c5500c1c600d5213002401d000c0d1440080c0400c2d006842d85009071500146012840d00b02110624400504150300f2108000c0c02c2820312864407030110008244803000c0d000040d9140901c20200d9540d100c2c8050080c810442c0280300d0308181c04001c40690b121240e80305200003480f600022520071111001014041004d0701c0314502903540700010407440b0700c414500700007020391000a002c5040c15000403a5800c8082006605001c100c0c0005801c118081d40020403201100300b042080d0182402c5c0171a80b800d108041c0d034024440d103000801c46241a06401c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 702152167 1250 702150917 702150937
    0xe1609061e1208071e08040911121302031014070e01050313032303011d070f020a15020c0a050c0109050f0a0306110910030f14070807210c0504090f02 66
    0x602e20300280e0784094a07503002d80740680d80341d130341c1c401185403484104642c151810b0203a014183c94070b040160350003c42c0c0d0744004100c0d42000400111103141c0b80804240c1e0301ca0032045a9041c02452800407908059070076200f440080e15001d000205103020107a11405a90307181d4600319003c0e8482c0064070284006e40f0014240035500440800007032107400030313018140c1c54034045580341220681069a1790805e80000ca4031303203010810b16030000641c5d0809030b40502d152602210240316243c0194846507900409044c1c1d00d02d10840500c141d6840d0110354080d003905e000c44a10101a003841c2c1d1711584151551030000700403400c0041d9071301e03200313005000300301006100410461950b681e20000300081c0e030011181c40c03400d02005000343d55200076144505c1d615200810103800f80c009040c119005401940c44003d0103d007842451030740140141c0c1e2100b91070034803070440070368a05004291204907000344596400e201c0000c003a01e0b801000340c022941072010900c4022207a1005001fa4000c2d0940c0c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 702153417 1250 702152167 702152189
    0x516050a021903020c1905120102030105091b090918010501060207150c1e03090f060c080304020607020109180f0b0a2706050405040c06080f060306010501030e1609061e 74
    0x50102c0480926041d20624401c0c0110381003841d2a80100300c2d00c0400700d107042e010303036003048041001d030800841503100c4145000085107190b04010014144e0f04018010005051b80318480c4800c01c1c0c1d800c2d045424018008080b0bc2035440c0c58801c1c070392a505002c00c030b034645500f40b00c00042c0041c000600d510031f43c0d030700c6008100d4001c08c225084404440000c0c043d10600f11001c1c41d20701c01e1002039103881e8140e00135a81e00104074141407059400c01d81c564803081c200301e4001ea50f0f00210310100c003520f400c1a4115816566409240012200501d45800078110311422104030702030300c50b07964407007000100d0051043c000092a0001c00118031228803030341c80c2e400e07411282c00d00110020001500c5841085500103602070b241c0c00441d048450440e400c95002a840405201c1c1507002b0400c6507000040c3c07400c80889246c00c5010988410040c0726840c14581c8070708680c0002c1c5018400c0020f1061810507140080d641d52101350080d1101e44a010116904040f2841003000081c412000752110f851030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 702154667 1250 702153417 702153433
    0x403060f200a0311040f150e0904022106090f0d090e2e03030f0909020304030e060d06030803040c0f08030301060f0810080109051c05090f0f01020f030d0516050a02 72
    0x41d015400030b00350500b0960740d003503044001c28400001d007000e45482260b0700c103041d00704401c205070401f40400c40707002e00c40720140c2042da55848407801584039a05a4410000845480c482c1140b000c0020004560f405a001000403101c80010a03845040d0800125841d6000055080d14001c0e520300034088250b18100005510039001015100300300c09c800041822700107428005101411641c200b103001030a40d240e42403038140c0c0607121401603e02090304500e0350800343d801810300c2403d40e1003203000300c40200700c42d11100c6071540884011a00103c80c075540e4506440e11105c03034074250040d01c0d00040c00c084045108840002a42d06036402622451500074400b581510f03561001012480c0c480700c540b80101741c02c5021b0103060301051086004180b0080b268085840400d0700946903c100a42400b586c41d81d9524900305c1c2d140c108007507944401980007800101d0a098140c110500103110004080480c1105640004e01c101c03200d940241c03a1240c408000c86043c031811140ba00160f02c1504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 702155917 1250 702154667 702154721
    0x50f010806090411100503040302120301121214040b1b0f03030f040c170f0609010b10050f210108010b010c030503150111060c180d03050a140909010306020403060f 72
    0x2c2050340290042510b9440c002c1401c0004200c400d05070381c550006000801400109601003000290910000307010324255810030419040240b000d070405403c000340220610001401800c0d50031101040c0d0400070790345e40c0c40c1d910151443d441100c4603003108899078912800c50102150030220484404003030361541d1904050080311120143c410740b8904111540020301d402c00800030382e1048001d50103040c8501651048504081000700b84442d1f0307904200e18030409070741d010a1242c800fa050f0408135205c1c07258540404182c0121000c032a00d4051107161244e024455014250403907035500c00034000c3d41036080044600c1c844840d03000b0046941803020550b41061560051603250062501c005401072050322549019415511140c0308000003e503164040181d0301201c40411054988285490060350020a5407051300b11410422603220038040c130500400d0300b00c40380700070020446011942c4a0820314000c5d807041c4011030781980341c000401201441801901201e20306040c1c03c4010040810b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 702157167 1250 702155917 702155929
    0xc010c1e05032b020429040503010615030e0a0308061002010b040507020c0306010609030b010e15091f05010503010f030311070b0703211407030e030f04120b0117120f0405040504050d09050f010806 86
    0x1400941b84801484081981c0e1002d100d00001030135100d50010301d406040c10b01a040312014410219a5040b0800080110307400401d1980c1001050720810750010101200b203004200034031005501c5030904051158240c0d001400c1800390034120705485440c0d80c0d03624196100e040c3c6100c000c1a00c108000100300c6c8103280c4401c10b6000f80c450b11001c0341c81501d000080d42000040b954454072408180401305644230b0500c006004c0d0800b820030910755410b00e51120700403422440001d0070403a840c11321000d04a0103000603001461484803440c0c0390f02d82850050702800f0a0402c040c400d40c0c41c40e0203600042035500441c401030a10103403a11050f10b444100b01d0182c40c014000341542e00c000c20140c003404100800800003040100411200d403240b40c13038582c0101ca4180d00c419001d4100304c19012010b18042a040d003852600340e54a40e9540c070319076060002d80036075408181c0c4286080c04120620031b0101c0d569028400b00d903140c4004644510410200900341d0503010700248003000040d540342084 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 702158273 1106 702157167 702157229
    0x5090f0405191a0112020901030e10051b04053a080903121c051b0708090f0a0803040603110903060103031d01020c010c1e05032b0204 59
    0xc18002000885d900e0b41d0703d0759a55002901c12a283c1c06580620031415500003500c0c59885044c2141004110840e068101c1d20004d1341c3c2403407500403c0341202d040d1140100f1000403400d1041c0451586001d03810400403101490180041e1000d4014125511034032031211560340b8a40c040c14075081110494145a441c0828003500801c0ca02c0603140d10889801007800182c1580c0f101c4480707001c2c281d501010850610001219024444180d00610741c0d00b02c01e4811680e401c61580a220011205102c0e4600a03002400240b09040c440e1300102003140d00c41d2070280c10503010b140040d00344902a80300700d0200d680d1000c108480314408220b8503203900240050181080360900290030040300b01001802440300c00c000700313601860840c8102485400c103007100d444800200c100c0308103290034210a603610300304590301d030080300300e42c002c031015100920b0102800c0c00b54040031000030004 = true := by decide +kernel

theorem cover : BRFrame.Cov 701978417 702158273 := by
  have h0 := BRFrame.cov_init 701978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 701978417 ≤ n) (h2 : n < 702158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
