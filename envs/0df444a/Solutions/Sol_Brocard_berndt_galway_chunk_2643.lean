-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2643
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:19:08.701444+00:00
-- url     : https://prove2.me/submissions/287544a1-9dd8-4e3a-8dd7-ab0f2dff8d6d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 475179856 ≤ n < 475359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 475181106 1250 475179856 475179907
    0xa0b0402030403050a080907140f1309030206100902040b04031e0501050406150b04030b1317040b04030b0601030e1c051309050a0507020a03080106140c010203190b030109050a17 78
    0x90b03506000e42c001c0c0910384d21007004001440100c0c1440e0274103000c44c03d813034449801800501c000d560a5514640000c403c0201c3c0c60040010882c80c5c18025039515043e50780340c00f50000140041303490b82c03850084409551401c0c0d40c01d0303d0140f65684e10821088010000f001481c104024000011f0007802224060307030250f000402c2044010a0094000c01c0c140d00c031400c3d00104000410000e42402c0300e066010484603401c051300c0e44030303040042d81c903481c90142210103840000c01260034070f00a4050401d490003125000343e0b5035500d20055048440d0104078140580c81140d1100009034041041d0700140907a1800d2030803c0c1c01234448200c200a250801c1176039030340318410070031000d0703240c0314440e80103d0600c001c1c1461605038030080d04101c4180076a00800c00121603403071241001804075400034414500031541d034a00200140c42d45000c1c181c5131540e140c10803613902da5500e014050b820603260004003404654500e5580c01c080d2038241d180ca4103848909020101551400e5010034490081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 475182356 1250 475181106 475181117
    0xf020d0503130906051008010b070c050a08010510090624020309030d0207091506080408030a0b060d05060108010501022a0334050103061a03060d02040e01141b09090a0b0402030403 79
    0x240b0340764a00340c4d180342d00a04e0056141c190580d00099000b601c2904480d114100250f43e032003a42000218244260082604072081e0703c000200a0015030006200b041910216040b2503218001207040d21441d10440000c403a0032403100d038043c0c0603500c10104444090045914042451000c00c1c10a0716101170000540c000300c008200341041c601854985602c519401079085040400241180c3c20141c0050125803020002901c4a0f05961141c0e0007420014105a00c82003454038074006044110b1300701c0d00241c0e5400000a6035400000c041780000500d40c0c136000340030b9030421500e00f005982e0b0b54042c0c0c0f5104682d0411318080d030301391119011700e041c03c5600207000460045154011002e5010f1810949031400400980c1d246111000700e144262861590342d81700c51000030150350300c118000e0b510528010b81d00084017015401040103204103541241180e45c0c4107910040f03071516204d007030050300c400c021145103464a8400340386d01110024001662220030310107e0120b070401c0b50120040ae0303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 475183606 1250 475182356 475182359
    0x2041d010e0a150c1b110904150c1e05090d0206070c0e0c0903030f09030a02121b0105120117030409090b0106080a0903020709020d06090906090b0903070f0f020d050313 74
    0x20148640f5115074501d48144000a2041e60003800b05941c2204001a0a03003068041c082049104820f20448001000d00728242001d05110001403050480b000d0301a24209807a41405d01443c1464251903c040680a0071300c3e0280040d900780d40b281c1d0025501c014103811450042c0c0c1c480001d08006805680288107403030800603008440380c00030f40240e50b8014140f010021950380002100c07032661200198a48444002c00031902e85100000000e41c0800030041c14147d40c1c5001a40f041d00d90880c05245102101840041d212842040e80c00186c40c02840c00500412070b14408203e80551110110380c0782c0740d0341e80e003214104d41c80390004484221440e8010404039610010f85078103c01c080e0030170000300300a0340d0081c2d42c400381d031311480d00016004a05411030101c07a50000009040403c02072201e2129031400030300030b104e4040101d1f001041e1030041180218000103840b1802d03030004044000146a032200c1079003010b415822640003202c0030388003002540600c05030680340304001d05220f00f40d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 475184856 1250 475183606 475183613
    0x1806030705180601120605060a0e04051b03010b071419060506010f080a0b060f120a1503021309051204030b09070501080727080f100b0303040f0302041d010e0a 70
    0x24005030310040c0b2440c0b1030100314146220704541e1030340102003400c0c9001007a1090300340d01e01914a5501540e80300b21f0105040e1122600040d00d0444808103c400f00016a18602e0340174001a46035040d070100c010a200504c405103a0900800d101030080c400e8503000c0181c600302500c0c0c0b10400003105001e14030f407254101049058094141c101d2824240003184038200100203242c0030300100701e0004692030361840786e12134680c48202c990165250f0030721556959840d440030403179841520014091450041c81200b0411402c400d9026258000c1c4950320612040c40311074050041100c00380c3d6140503000280701f000d440100140011031140c00c20370118a0441102400e004481d8401410310a04400300502c4c56404105610340b42003e10f45108401050326240000c40401e802c203075030314803030820341c03010051001031300d80e06a100d4603a0910038444d035003060644a02aa10800c1300e1440501d405000615003904929111a07100744851004076402c280603096070302c001e005454680100c003d04050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 475186106 1250 475184856 475184863
    0x12070b0601020c091302120f0312010905131b0f030b0f0a050f1f03060f0b1f02030a0e0d0f0308010503010b011e050901050c2a191701020702180603 65
    0x890802d0001d40305101c00100800c0c00620001c02d505025030541e0010011540c42c9000385481e40c0c48481214100c42c94840c00650380c4e80325590420303511401c0c1000107503040e8540162442204d602040070031090b20381c4e6030400b4250107e20041020480d204020440c450010f200c2d4005601890100304141450340150705408400303095074100c2c074202030402428403500b07840c20b5044440c0d059142141d59054580f0b02c0c2144150300014400350612882c03859030000707900302c03c0910708201e50896180600341400a0781904202a090140c0c000384150038000d8080c00000030502000381c01d80c900072501da503500c0300c00301a50303c084000c140680300501c068102440380d69280c0c0c0c028244071803080f562402209800741010b460314208000007030a6056a403180b4252521000b0340303c1240c90101d949010103280150340428010a1880000103a850b45005100014005150542c5044160400030381100d41710000140d20104d40d0208810001a11011009400b2a10b615251889410254101805c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 475187356 1250 475186106 475186111
    0x303050a05060d1112030f030709080f0d030b0109090c02010f2d05040f080a02010603020f060a200309100309110d1a06010e040c0e100203041503020c010e12070b 71
    0x1030451524041120a480754941c1640f0103400c1400040c4582d07000300054000c1d12010590b403060b01020a449074440e01c0000590700900f00340d151a072841c0d4440404070350b2821038446491041d070109540060781030007544400d4000c04107140044106498064201c196480304640c0401030b9920071103042030003403503c569094a1048620100c140440c52028040344d9480401040c1031035448001c64100545000344000b07095025009580304d03420079130b020780240f40510082e8020b00d0025004042890321404880f002080c90b00d428280d0140b11004070902000fa5101b0782c0c533440200181c80c080d079116000c9000702d521943d000b2401007120325000100c0c2d070300c00e030401740034005900400000611030801004100d07052642e11150b07603520f000484000044a44150300130b403030802c110381d01550090b200c050301030f004d82d440d401c1d0340d0300c80c041265280301d0fa11840000310320100158000c02d210f0340080c200c0102c0180081180134024265500788000e04d10144021070340000c0314010030220452069 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 475188606 1250 475187356 475187371
    0x813090501080a03141e030906060f090127020c012c0c06030a090204020a050711091b0a050f03011712030103081c0212070e010e0915010c03091e03030305 68
    0x1100e540b40021156030703007500040041c01d01c00351036868203400b200001590680303140007201080c50760514124500f1741d442642d010020740a290001a881c1c10700103101011410050000602ca0707103090301c00b491500c0502c41c200041c2002004c7c400200c003441c00680b181e21450000000d030300c0714041c41b5202084072800c0341007c0da00c034901007480c4598082078180a03100103403003840e901d2340d400c5000d100408a280e0001d600520110b801440954000041c1c9007052080c01507106800c030110400104010172a1480000d0001002d82030404103040090030780c48445040050400101094944c2c49400c00d030405422415030204444c04c4e00400c000d050249043c1104035072442d41951101c03607180c07007550200308029054440c03111706000a5412100051052840c4400900740040c008140d412000b14481c0040c65400c010401480c005075601d0050001406a1020102800054503800c10500e015014000340e240b0010b10201c04007000d401c0031588000440500b401e40c03402804940e40681080b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 475189856 1250 475188606 475188611
    0x10e0312070b061c030c1218140103020c010204030f0b011a0f03061c0b06150408060a050c13030f0605280e07090204090204050406150807051e0304081309 68
    0x8640c2181500c21180150b800c40070000003607454030082900c1c00041c02e0140110042401d40a00345070b800741c5035030441441800c0c440d041d00784103c011100c3c551801d03000802d118000034100884207443c00c5000c1860018100036052184420120742240c000d0350041d00c40d03610114040080000890749240500001c5000d8030060451411480403401852030700015200004085213256035454a0241c0800c0240801c00200000b890001282c07a001e03034002d405108070400a03502c1911480a40e010b40f40c3d444010440780e903c0080c110f000d880042c00b0315044d20810484203111884500308140518017078030816440f001c440c5014011280000c0c90a011a845102001003008107881044403d00700b0090108101491100c1d50317060420591019100600c001030000700707102160050403c5032004c0710204003040c0d03500034495101c0c1d84111103400045035600050b00701c82c0141e0190840000d15040b03180344507102c0d40c9103100c0358030aa43c2075420345d5010884110806282c03400310054900418103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 475191106 1250 475189856 475189873
    0x91e09060b190c15060b18010e06070f06060e070206070206060405060d02130f0c02011a040204050906010804080717120610021c020c0604060306171605061b011505010e03 75
    0x3911042c01d03a04003100100100c64904900748009542c00001c0130350150030420000d555001090f00c581e200415190003120000145403e56026402d8210520390191200c0e281c4030303c503036030810704a8007120115a074981d500c1010540c0100b80030582d00c00e9242c1e8000b042c0c03034100444080c0c941040200f00d035105a040a04200079911148080817035640c0c142c2c1c440561140680d00100504a524201c10420386481c2d40540301030b45c15040004a07008000100c0d500c0c03400b060900050388100c0c02059040380380a004211954030a42551794001c0c0511070003030400e40039560b043c0c8000f00302004407049820205840c03080c01f0703603216084e8103c1c1c0105c40e041c0d500044500d02948880a030241142e101014507520400301e0300a1002010054008000303540d034603100d9201400420144c0144083c2d080e800d036100308520800960320058070380d844e0344064450b1404040001c0d07a403211102c100710980340c2c00c01000030350003402188025074070301100d040c2d0710b81000001801c0d00701604407584282c3c402c641 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 475192356 1250 475191106 475191127
    0x21b15010b0c030d020a0318031e0903050c090415050705031509070f0f051b0609120f0f0901090e150306090a030e19080610080706030507021c091e09060b 68
    0x211420b05003e0f050146c0c4692105500340d0051021000c2007105000f0b80d840341c000c059000032800c000c1810903c08a0300061300303040c115035005087c040184154050501341c1d16500d040000a54018411090400d103400c0310744080058131000e44002000c5800072080c0032081c410301e07070440354030002500c2d030f0b043d80c1c0b62001d801000c4507160140300e0188241501d400d0059889501150f0306a60003410301407503d0000c00485a0b01d0500712100e030b1040c010051503101015400f401c8034862410340d1000c6081102c010092455503000361800c5040c000c0000b0300044031815040000d00c14182c9440030845114101e0a2509208006040b480c481c0c00c50309620300042e8105000034a2200160b550b90f211030303848000b005070031450b50880740a511944082080101044a5040584100c1d81c1034904444c1d031400140c0c1540d03002e03a81007015800800078131840d9802140d2030b1308403c1042c605120070750755880020320002052030740070036407860a920a00070000240150f000503e542c405860ac2d0004494 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 475193606 1250 475192356 475192363
    0x2070f030e190b031806070903083a11040f0b09030c060c0a03031808070b0a0b4203040b0403090801050a060302190806010612021b15010b0c 62
    0x40006040c060a44407000140c0c840c000c0903200110500c07506500e0380e45400340303520f044c0c10481c0e03001c059a01c0e00b0640404000003061550150380580c4030700f0341c81c40c21603440329055005512042080040100034809400021101207035802c7c655041c01e0252101c0b044c210151050400c0d200150441044100001014079001008440d04184019280d40c0780000085c1081c41080820307600c22004100903181d4280401c0540200d4440d413410402c1d8020b4031540350030b40702c542c070021f44184000d205901c0402e42010321254030041701c1c94009204441080000c14440030004810145548092094480c0b401e12000188245501190501004080c45124640c0c480140003c1c44220000042410140241450340c068060b40009010307030300c0e041007198000c04080c40240d100b04000c0580121180c000f12400d001c4c0ca442038054000c580c00c1c081c06440012050014101240d420400c00303081025072903d00c40341d8081d000c00b0305140f200d0036114001039901a004400720364000c0004072400e55000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 475194856 1250 475193606 475193633
    0x20c01031a04020f040f030b0105120c1311070b04120315180e1609021903020309060a0c110a0c08010c08090c09040606050415061d0102030d050c04030212010c080a0207 74
    0x102d501503900d42c111362659078640510f90000e5a02240c03410007008101049440d207058820a83e000005107075815551035036001540c00540c4c00a180c9032514100d085182c1050554240101c0c1d52031501d26107a07980745025904071800c1d50f007907007000d0a41c41003940c10b00445c0b412040383d40b8501d4003d81007041c0448628111825181ea040c3e661040c1c4140301400c3c84122190110484c07002c0c1d0583c0d550403104083d522030400c4038024580403007c0742c0d80900034401e030703030003644220000d001c20b0361200080e100034030b00c03800c0f54410700c008070a4020000000300300c00500c191040c1c001d111440d28200f2b260707003510500303c0450140900d100402c060004006445942803500301c030700c007025840380e00304000204125000300f0741103818118105d00710300c0622129011a146075407007007890260200c02c403a0502c10840034034011f0b0410801041215010b802440d0404070f400d5400b03160603541c0e40000c100a01d11910307040265101c411718181725401c0010560300815141c019450102c959442c200340361400e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 475196106 1250 475194856 475194859
    0x2010e091308030c070c15051206030304150c110a05030a17040504020c0a02090a1802040933050f012709140c041a0a0b160c1203020c01031a 62
    0xc035001581d005103030906544500e030001c0a1a0752030800c400f551900d80e00545003500d02a811060003e202d9035094006485102d0b075a0320b103403c0440910303d0702e0900f14040c0650f41d052005010107d808800c0c50102028002c003510358403e010550314042401445046203180b04102c0d1031800c1006441c041640360b03149902141d10b5031040c480790340460300340c0103541000e07401034030101e05800c86c2c1e0000152010090300898a00b18903a44140006041d00e0440c4070000d40d0ba5042d40c05040142031541082d00040d101d103040b481020000142400b4008175503a0248032820303609042d04084e0154402c0982095003090b01d2000c0d0360402c07070f00021119a810b1150814814988642c11855031a0300c100b06a651025140500ba00e42c480055a03036000e001c2071520440c030740814030a20a400c4484030f95100d6024002070009850480e0b165040d80001c180d5035201600b162590000400d4200d0072005080f0303050b1248015041d40c1030003454140d4144849040c14940500b6000c40f185510074080d4a100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 475197356 1250 475196106 475196119
    0x1009110a090b030a02041d1e0705090d0204110d020310081207020907031508060a0e0c030705010c03021f050406060504150e07020f010204180c051c0b1c0c1502010902010e 75
    0x11348400c000700a22a50f803006215002e490219529103500c1ea041341d00402c41080020a8034070003140c503001d82c000684100780400c908115001c4070741400c108004495000a1001030071401180c030619040d4003013601c00340300a5002040220780304e10982201d000d0015000200703445003044400003498803803500c0292050400c070740000c00e682d110b44c002c0d42d40110113070250000f82e661600816640c500030f03070705540d442e4200064482c28902c001101c42c2c903c44010003c01a0710718110041d0317481405500c2c01d0701140503e04600c01411040b0000002e2001e8240c2c001071585000d04162046031000c2c4c21041c407a40c01c1031440d040b0418280409002e0302c41c0c0f5600d01c2c069441e4504260315103010005902255400890002542940c10300c0507030080f41459418070246684c0c01c3c0448461107400b070603004002510302002111407e03a400809614400352103061142c01d0012007214550382c912040340c0c2c1c030040744420300072086940c11512181c031140c0028001c40c0c440d580040c04044180c4229801a076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 475198606 1250 475197356 475197361
    0x3102705060f040e010902030f010b01050904090503160c0e0a0203060d060509011805060a2007060b0f060d0504150e0d11010902060304030206090f03190503060312031009110a090b03 80
    0x940c2c000e400a011040203000b0041c80f488054182d01811040d4400e0b442030151030302a0000c408103000d0103403141416944d15103410031107001c000003003101c490240d503680710070b001450b030765040c001134004c88500581140c8400c600d001c0c0d2210041a0040011068900510a006480d1940900981c050f90310503404140d50381c40307108603401800104404403500c08400c0001c2c0c20b000d00800c003d80252a00718090110350140d401542c0e4000602071302c0e8074802410064500800c00541c800c98190000a00014001d52500c001490b60340110108401d11646c0b4003d11040007042e01e09021200c045080c140040c14100590644800140050380d041c00151030100440000039400600401e41c0102250340745d06160030020341d15801222201d03068403c0702240100001c000065402c040700084400138007405925040b140c6400107000340e80c15100d89a04551a612443e024502c0b0b0b0802c804058106482c0c6820301080ea000d445180d00360860810002299662203d000e00503280b108181c2c90f40ca4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 475199856 1250 475198606 475198609
    0x108010c0c03030c0e03010c0c0b0a1a2403270d1d210c030d14092107091b050c03090402130810020a030e0c09010e0702070306020c030310270506 64
    0x4442009103150300d03520746107082080c207809c50072810301d0300d0040411601d20350b1400d4201086400c0d1050400403482112407001079450720382e1004059034254000c142100d2001e0000400680041e21680180100d200e0000300f050342c0b494022481d20f42800040281d6845804080c00c880000c10240b180e00300e00d40c4c811382c030a850b40300c24002142c0c0420303101c4909698001c00d0301d8541125101003071081c0190344085641501c900c800003e280d80e0300b215240b4100320311040240c01c1100d4698900d0003200004c015026000500422009100315103000c00d17880c1381c07000d40114800108483c0c1d801d101c014040704071f0809000094903500172040d20016a0340d44c00b08038481c103035182c0d1b41c450308143c420004250355080c80d5030003034040320010380c40507c044081e0000803a105e810038045d081e044011400108840c0c8045400d580c4c00010030300584804540f29103c000c1aa4400d244444551b07000000380311070400e614119100174200c5807500350716201a0264190021a450a400c000640310390204509 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 475201106 1250 475199856 475199867
    0xb0f0603220f05010b010203030f130606031203050429041b03020316031a01181d010c180f0612050c0d0c3b010507050c0a0605030f0108010c0c03030c 66
    0x40c250346441c0740000782030382c0c9000b800094540e20300300c58550030a00c0300109540004280c9000e1016000f00c0d202c80c1ea52000e0301c0900c2010308100707a40d01922000b0010114140012043e52900d450390082800e25050030014079401c41c1000c408801180e440e02c075100885140060354100d6405070344001101d520045000329907540d500003960600540c00c070805440d50480021741140d01ca0703501040039000b1180a0307a4012000d108400000c01651440c00441c15142e02480070f03542644003858406c3c07030041d2124212550704c00079001254100c0d40f2038040c0c00708480c0140040101d011b40c81a00713820407c000f420104103400150b12240c54001140300300c240c10707003550100218000200940c10185c10001d19209806082c0c010000c51454400c84100710525846441503203400d2445428035640d00443d081d03803050354141c0b0076000351aa80202640d03580c004e42c00800050b59a25200e0a002e17039000c3c500c03501a4405c88280e8540442c40070642d4101c1050381c901505803c0c0042c0c0002c100c80180c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 475202356 1250 475201106 475201141
    0x6140625080a080403030b030d12180c09060302031002090f09090a080a0e120a03050a050f0f0d0219020d090b0c0f2b02010531060203070f0e040b0f0603 67
    0x800200403480350b0300c856101144a01c202d010740d4051101c02c43d60824036854071030750301400b40040c40801604401d044903400c80c121001008a25002109003521016000b041a400058034243c443c00d0030401e5280c2000202c10320b00746104111b01d8a001d01c2c0c000ba2411440f15046400b62400f44005804801c00703006a80c80c00b600604d020b940c3d40c13583d100003403240b0319030300c921803240038100000000d8581c0003440011b05945916003502c0c000c18114144c90581080b0300391054040100103856180f8040b80240c00d450341d01c128056200d01d0001981d40c070b030340c202804100865101200031045a5405940700d81210303a91075055540e6481c50b0341e11803c0c031a20200d640c681d48518401c0003020f8105011001911140c403aa441c58005406000c80c20b07102c09444180001100d640c01695086c0301030102c049110340807207030f4002c28a55607525000d0707802c1240c0e04404900c116075541625a0400d0844035900b10072a01000280301342000034100380600b01d525030242e100800002c4201c1d82e242102030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 475203606 1250 475202356 475202363
    0x17070909030203040906120c030813030204091101171302090a0b120703110a030503040e0c192105070f0807200c0a27090f020402041806140625 63
    0x11800c002420042d64030b42c8948941110035141120024801c50014407050020740d2180304102c4031072458440000c0e0703802c40101c484101c440e4510000043e83d69200b00c40150788134036101e41e020710442c000500a164180ea1140050102104010000c0c00341400581119030499030080a9150200701a00401070103031000c1c2c008038a19016000c2c0c3d0800a20b0600b101c2c4900403d504481650007807150342da0aa20004080c2e90041c0300c00d210b0b280c0d650322210b03405250710752102d00300300c07400d10549103010400c1001c00100b0340c1c1d15080510400c00042c03040710303003c0d40700091185042a04005200c0c08c1215103c004200030140860451482000c1d0646148104018a16505840840940c40308180444244240829400002c014019000411800642e81d11b00c02c1c040c005484030304064002604111071000c1000706207401642e0b64805403016008030107100c3ca51490080100302154803d401c45054604810800c00c0d2a95070b41c001c030f40000e42d106a030013416184080105004442c00c14004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 475204856 1250 475203606 475203611
    0x1801031b0b1b0102160605060406050301020f094507031e0504170a020f06060f090f0a090507140f0102010510050d0c2103020721140c09010609090b09060604170709 72
    0x105c14881c0c1d9030021405850100d5080180035038400c00c144c01c074843e03482e44c00d420311030034072601a0602e40480410b0071048034212200c07800724814064100282212158007a01c0844100c081c281d416248006510581c1410300704030010403201e022a400c1c0c2c4420323041d0409500c0b03500140801800607644090361100340300440c3c5500c8507803006511000c0300058403199105042c0051400e00d4500340b00c01c100b45010308407040d1900c540545100c581c0009290484071501c8200d00b03000907004006e2940140070760191044045812410000c119241800480c1168101400d01c000848030101d00c40c115001260300d10200070f6546489101d0703903116403000381240a103110507035071240c4404c2000d500030700c04d5003034420307032600d804030058885031516510450b00d441c01581c000081c00386007200710306010308007115030569204c0c0000d420f40d4800d0300881c00068040c407081101d0881400340345014003045620f500726280c201c0c08903903240201d11962440440544084a03906002d2260300c014014030f0328107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 475206106 1250 475204856 475204897
    0x1b04060c0b072303010501020d0c0c05210f0105251e171009060e010b0f0706020c0a0f0c080c01020c040b010302041e0e0c0f030402040b01030b1801031b0b1b0102 71
    0xc0f8089810922846000d4020341501d25403c41c0300e00303200301840b0b0380504c0c0f1429050624003403040226070320384104403a402c501d4070400d00050800a06002c44000e100201d040d2920402c40d2400084a00a450104c1c00091107105895040400b002008a80c807181e0a42414814011a84400c0680c1500c1a40c10001c06000c0449000440d06040d20525201804520384d5622092004403092041c505001c00c24880c2d1801d072a40d6000805d01c42e40030320070140c10b00d10b080742800e080c0340d07416200b102e540d01e10b80c20000400050000d000000e00200b4083c009010308040042c1d01c520340d00381c00600c61640d40c400e078000c1707030701a9040d14040d00168169260400851a0b02000361140d03015100b013080c0c04c8000124120006008c440003040101d0015045403290307400e12000c0c0041d0b0521506054842c2900c2a1640f90095040f0a0504010300322015500d0340c20301d528620202842140c0c00080c079001031105024071011900d14000460002c10039040b421840c0d4024000c85030356172001c2100322003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 475207356 1250 475206106 475206167
    0x91707051513080406143006061305060f0d050f07021005040c0504020309010906020a052205030d08090f01060f0e09070f090b0409060906051b04060c0b07 68
    0x191036440d261035141c00c614603110344a1035115424414001096100108418011756204d2100d010101c030702000400d08000304030081400c100b0880d9003480c0207043c2c0000103501000d50359403080d04600180c03411803800300c00441c10000e800d03e600506008200000d0000800c2c1428000c8662102c80c2c070368204901c3c10310484000c41000180c450200601c104055410340a5191041c40e020310380c4403884070f104900d013009000103504000c00301c848555907141c100340410280d000401c01d504256171120384c3e815000068004080341e00101d00c2202c100078805201940b00094480d91091103810440d010b692140802407600381c402c0ca10079225424890002840403045061006481c98042c03088019611160b01c143e4503801c52041204ca4211a2020040021264003402900341c001e000030070403000035150281903501620049070099501c030308210302050004466000640031070502441e10b807905000921605103e0005040344941402060b40140510700320403160a04004200981d0305056 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 475208606 1250 475207356 475207363
    0x402210712230f100501080c100c050d0806150c0703020d05030d110406030501080c100e06040e040c0311012c0f09042003070612090215030a020306010905010c1509170705 75
    0x1450f02d01c9105074018054121050701031241602c425a0051030f5030240b00007082820b61020300c500080c080703807044040110b401401aa8540000e540ba0300e0200d05112047c04520300010401d100f46010038048055128000b18100044035011185035420421b10300b40b41d0300b58896210103001403480c10a03071700880046080a03104491098404100c0350b0703030305c05082d500c2d0000c00c803100d980104128017091400e80100500d4a007408050200d9003882d85404500343c0c116000d840a68072681800010010840645080101f8803000e00e410345a000209402405043e80c9101000350b2031039440f100840c1e5154039034003520f003900041000d029410281080c9000504c0c4003072001d200200d04442c4825800c00140071000c40b402962041c004500b0100000f000b0912120b00301c4e480340c84501303092a00b900c041d0195010710700205d00141d4030b0800d48000340c0311003a00c0e405103040c44803654440000c2000c0803c1d007960801085c8000c509445145809000202c241c440d020b042c420203d884000c1c0321000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 475209856 1250 475208606 475208623
    0x1d030c09040f290609151011010f020d050907080a03140c010f0501060806090109182402030412030e070308091002010e0607050d050105181b0403080d05040221071223 73
    0x1a943d403401030b00c1e000a02c0c0c0790a40450010303500301e0360322207602651522601c40c0230032041601000240c00e00b0021400303010380e40300035245c104e041d49500138054540d40900003040140540d000419200340155406004000e11013074000c20103902050ba18903640003900407600c04020000c0800c01c0f980c440c200640100700603180c0a008280407400030559004a124400f83c10300351f109480d464041d10b03540d0301c00c1408080c8546c00389510210810610f02a503001541c09944181010190f4554017040101119000e404580f501e034841d4804101240d10541240d42b41c0b08c1c155030801c0320804074102a07008d003600100340300d0700f1710400041000b03035507202004d0440c4c14810301d002e1004c0d0340c0e030300d08001000e40c14146900c184560307407003c2118081002d00148000b4201420790b03040c40d54948903100c0603000380044108807a2918104400c620300201040d0601e0302c2404011094040e180643c0d50311089405840304110103800820284200390500c081c0d08003581000350311300344042050a8a40341c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 475211106 1250 475209856 475209859
    0xa030f030e0a0303080112081308030903060a150513091209080c0405010b091c050601080a060c030e0709051905090a0605010b0f2505030a1d030c09040f2906 69
    0x10319001c10640303081d07000141180d400d6580e5244590a2205084000408207004c46016004208da44155400d03c1050402401c10358069920754045105050404500801403031505c0e2a00d40b0760354500141c01c82c4202991025a401641048040e00000003400500030141280581d8098a14910360068141090f01c20b10804e440c445030403081480301b920f40c207001d080080c160038003c190032170500b502810091440f0303034000e8000112940b0f41c2810f1040a1300280791a0700030300f40c46414803c82d80500482c4030b9180c5410003500102983c1e050300c0d40c0542c010610f10130f8890300440c001010751020000c042d50281c0d010030107410019000340e0354149070b85003294258109800001d500440ca0b065800c0f88150000c1035240000784621300e80d0f104010740d402c08203408128400c0e004180c0420103040c501c41c5507224420030a1a40029001c05c3d40d6aa000f14030981c80003411207401d481e120250ba8200b58054000b4400c03d03228588042d500081344d175440b4804002041503280d20340c11040d4280200700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 475212356 1250 475211106 475211117
    0x303030e010204030f020f190602030a02010b0f090402310209030c0303030c030412091716080613061a120d0e06030402060412031215050111010e070e07030b0a030f03 73
    0x1114040d8600380d0089100c090f0200641d034503004054207100020f40d0814000610050002d15688501504140079400000c0140c3c80400c40e51403140d024030a40341c0300c0000f01d42400555178100300003035020300002e1001740501109003800a521201150301c9030322815100300e0302400b4020111460003034208020140c820322400020b204182000320407640a440184045480c59440b900d92204804041c03010b00100300c440340b80000d0000180390250382c0d0503140c201400394102c107078240c40490500c90b04580003c2c0c000c00c003403050b080821644c09200651005020820034010310b5002d1404d141080303803542104506040d09500c04002c154489607000d0341d00d480c00c12034a40b000340900c44c0422140250050400c100c188220340345580e02d07240c02c502ca40341403d1130005280000080e9030440310f214011110354001800f466810008824280c03420708000c00a80b9284503001d5915502840365200790700160001c20344003442500b1240b803440e80540720010072592072418080c41004281d06600040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 475213606 1250 475212356 475212371
    0x130f14010915081b09030a03030501090b011e030b0406050916020607050306100c050a0c08010c090e100e0612030304030810050105190503070c02030a14010c08010e0c0d0f0e07030303 80
    0x1800300d041d0020b0403a69903a6412141e42e00000190a10640c01a544a0b800b00780120b800c0c030fa400304206ca0080d407083d900451036500d001c101c2e00a5034520201181405842a0350050215060805a101c41100d140c00306e0050703145400b140080c1403541002da00451004c0400c2000082c50224181e040003a600305d9101e6a0350880072a907601042c0c40940c0e000c14032403034020000f44260070400d60940100143d64045400d80d0303540001d0005584039000c1c60f5181c10303641d43c40340e400080400007420b6107018160a03140c0a0b0f0700c450508840c6c051a411903407640c0104085440d0742c4da404446402d2981225900c1c1403900f80980a0342d41114040b60701180010301080a52044081c0d60f407900f0368004072906806080026200c540005150404010100e04540090f03607007003003d080d03002c1c001c01690110000002d50903003501c0141040606101007040100058501100700b543c0c0b0016144000303031900603210305000039200f4010356298060400c50440040e14020802c03c040ba03119440400c0f854 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 475214856 1250 475213606 475213619
    0x8010501020a0c0515120a09030f02150105120309030a060f180201201f05060a051f14070b0a0e060906100e04050106030c12110301090b040602130f140109 68
    0x102d0001e00002c0403011040010082410064200040189039030a91401c203103401d1803081c6c1c100011113464440540310804002895001755002c43c0303240c518405450221100380907544140018492a80151400040030355080d9060082e00d481d0000201038070400c00d1142000740140450300c02550409203001100b003c41010140c5c0004c0d41c0341d06841c0c1400507442d0703900b083c00c40c1044158006441c001c94a05001c11a1a00350081e01d084104c01d000580c0e0502030244800e820340c43e080507001e4507039031141aa640c06407980340809102da43c075003150030351400030b40080360303005800009001183c0c0506020841820381c200500f083c544c80c040702c000b90f03910f00001d55a41019541d1544005101100384407002440b01d540b940035004d02c0001c0390b4980c7e20342e2194074803501503108020a859900341602005410100a0300c0460704400a00810b4040c1c3c46104148030007500060400d540000d040c1d0300441ca034131000340141607100b0800030543c2d0780c0249000c0d06115a000c6400240200d4000c07400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 475216106 1250 475214856 475214863
    0x15080a0f05160f110715090b0a020703080f0913021b16090903021203070816021506061c0c020f0d05040f0605070c0305030412061b0e09060f031b010801050102 70
    0x203000510350310000c049030307120b05407019141c0740419810048100c214aa002200b0010007000f00945c209005043c00007940061189026030000f2212190800002d5142640020035009070303504520b00780d03601c0c0c14103951503d03a03201782442c5030303082260704455440301c401070b601a0510703840312031450340f003250944003580e10750341c58002919641c69a003c003405402c520b680311803046c07480b900448403000720900820900303410854404000880540804c00000403440e004600903e00e4002840c8880c0141003503802440c004140900036440410740350040407030640d21560b054081681080b80f0401d00d82d0082d22244104c220803001e200d510000f01d074003441007040b0f034201c0d80d151031909007441c10980308844030f900c284415070304220f150101101003103080c0020001880c003d0b081844014642c0341c40300c2031310f00da00c8a032a01c80d84000000d03608142c00c03022410911004035804406581c1701000919607005401075641c2610030800c4400040d0042c540b1020545801d0302c0c1c0a00c20780c1d0700c0004999 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 475217356 1250 475216106 475216111
    0xf0810112701120216111002100b0a030623010b2106010e0909160902120609040201020f010207081e07020604150306030f051e0f190c15080a0f05 64
    0x504019841c000048601c901c58910141441454032007107504446030990241d80083c1018060014240903120400000d0f074008001e80714151170390400c0e00481c031406512600340301e0520f030321152a0168054140d072050304440242d83d211004010200e10a200c2c148184010218601c00032a240c1c0041105103066058070003140a80e0701104441032800340c2511280c00242a85050000040490720a40e58542c00d0078825200e80700100b410742c1220050000080642c4d005502a510401c0584124103100702000e500c400e0541701140300743c880f840100d140c42540302019010f0b510104e41a0100f0188100400728840040ca1321581181440d6039049981315400000f54401c004000070400f180200c01c80c84404050303070a0000e540c503580c0d1182000c4141c1820100d41ca0f8200c1621815080102500800082695002091f50100c4c22920f1303a0f82d0610042000f000b008108201e80400c4800031018010b05070b10521441c108074810f801800511080e151000443c1c2401410400500540315551 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 475218606 1250 475217356 475217377
    0x109050606011e0e06070204090f03020606041b0804030e04020a05270d0b150303070606030b09011a011809110406020f0f03030402090408090a080c0414040c0b030903040f081011 78
    0x180c0d40f02a45083c1c03400094107000340d41105050020b000981d0340e0f0b110ba40314447c050506c10002400341d2a00078100500200344130f20440c98501d400c01c15600101340d102c108911807c18941c6034849040a442d08850960195802400040c0340500a0f42c494003800480702c4403501601e400e80381400e200c510b0a010400c49401040e4400502e002c101020000e5404c498180b1030007445101c1200030904540c0000000c1d1031664440d04c080040181502d13007243e000d88901b000300316400880b12303828421800310030064104070340f410001c1881d003903070ba0311a40202a08102040f840c106101000c60740e420a104850140c0280c40301a19407607804201404012070001c003a6103190344075403c1140800001d0402c1d1a850401e01108240e034a4540d6040c3c050110b80c030081c191595190304200a80d9032a110048800c402e041c1840000762501440c44143c694003801e450312540c6000701d082c0b441c0603542c8400c200070301003000091202408900c2c0300e64a50300a400f800910003500840d6810311480110b070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 475219856 1250 475218606 475218647
    0x5070905030d0e1315030f05030307080c0712050903120d0b01110d0f050d0b040e0105040b01150903060902030a02031905010501062c06040909030e031005070f0804030207030c08010905060601 84
    0x4c4204a90581c041604900400c9010303030804e0710380d00c8442031410908801c0b20142c0c0000140405550000d0003158001e40384807801d49407030b070303c0d5a401d46a80741036a9043c05010000c24030101640d001d10000b018501d41e86403258075550345040c10400b030044101c405010038806007050262180125a800c0c1841e00350b01c48281280c00140101c03a0350307005210118a4a542e8200940350303550b41e01480508851072400031400341454104101e03c2c03001a40031103030381410442095183c9030042d074031004482d0058400a403412a500110f400e00b0072802000390b00d03001d1401ca20000b41200c50070714500c0c41c044d4000f0400e03a80c07203080c2940c1d40302d0b449400701461300c001350316003501c4207400d4440c9401c000302030801030800f1703580c0c0c41907030a44003545011030100301420401c801070304042101540c0c0c4440c0810910242c149503002510464600501808001c0c4150000c0c2c18103001301b220400075903200212903070f03256850802c54001c144002046605015034404100303c0e6100d6007020741481c0741c4c100d80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 475221106 1250 475219856 475219879
    0x9182a0c0f053408030415030f0e010e0706020d0f1704050f01020a0e1503010b0913090507030b070f02010e0c10110109420b120105070905030d0e 64
    0xc1400201ca040300846451042da80700c1c24840844032080300c400511a804103190660041400618840a4000340900e900500c020443c0c030802c9900ca007928202d6040024000388400070740c00141074102c6041500e0340c24580b00d95035a0764002542801c40360103600703581e07046448500456080f103202c400700780028281d0302c0c08290b1541b04c54140d40c05c184039000300d91214241012003426a00410346d2400880c80c0624416851f0401104105102411814052440d0305001409404e07000b03d0780b800c0d00418800c0038081400001e54004512030390400219459266240360010f2541381c1217401400061413941c640b000540140034003141c5812580150030794251600038095218030b02d41c0440c0401903160b202d030300e00f00313007e21500c0380ea03074040c10b00c078450848a820703c5441d01d0701c002d00748100d07584c43c4500700c03001c448100020b0f8852801d0f15004140720f4001000181f050902d84400012540390009124069411656840844030260155102100c0c1d1a2099a04415200c0101d82000700d4111 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 475222356 1250 475221106 475221113
    0x909010e010b190c020a0602060106090801020c060f041707111c02030705060c0106050405160207081b01050a0c0812040b0a0c05030c0306031204060324080c01080709182a0c 76
    0x141c007030300110380e49004c01c41c42006170009004280c0c00d500840243e040800148010f5501607036100103450680021340c0380007019034250ba5144030050040581440d95004581002900d01d50403048612080885485800508021003229000f5025900c21100c0601c03000c8284100c07a80700b40700c43e80080240117414940418040c1c1607000d003030008c0c05550b87d401c0c0451195550300c21a4020900804d03008105540d403c1d0107460b0640c5c3c0c1d0080b4645a0141e9031000c00d0305141e03000c0700c815840070301c1c0080c1c49210031101034a285c200310380001c00c01c0710082010741d0a08000c0218521550040001158946030418450103c03180f090030980016001c0001840b140b0b4140011034010901a08031030b00c0e01101d0030720402d83d410980000c00007075151000040c00b0080c21002242d0701c44060b418415052078035102075650241c440b10300341803000c014002840320340125a40c1d0000c0880c030039070b01e8180c07100070030880003002c00f642250000301407916980c50048500d0b140591040a584861220704400c0c0c030b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 475223606 1250 475222356 475222387
    0x112e060806040609110a090f1404051f06090c050702041514060f0d0e030d05100e0a090c081207060e03070803040b040512070f120c02060a210e030909010e010b 70
    0x1081174072070758103202c0d07150615124850050024020b880000641202405010003942d007041840e41050b030072003061001003040070031403060301340d0701c844001c6454501c402c0100180c10181d0119910307038a44400c91411941090060000c00d04c00c403006c0110150b5134601e0381c0d01000e2801810740c03802102c1c01207045800c04600400614260440041c2070500c81c1c81c22000740d480c08021804140c0010400c40c015503003602071190020b0096105804290800030883e0b89070000a0007040c0c404c0d15400810b0501883c243c111020344031340015034404480102644201303500582084940d40e1405105189002c0084203131002598010746003440c640302d54580a40d5900064019a040d004000c003204e02030b00840014010780c0d118003280c005c00081818002898520706400105210030030f90108010307502c000850303802c51528280910300c05e483c65030a10300341012545000b149031800300c1854004200001130718010008880c040c013181e0321442041e8200800703104d040030780001840715151049059 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 475224856 1250 475223606 475223621
    0x129040b0901050403060504061d1207030e1809030324130b060c0303150a050d0209061002070503070b040f060f090b03130b0406330312112e0608060406 67
    0x503d4180e00f041d440b45c0380d1004640b001d4508592041e680c4890b03010070261540802d520314000005000c1100400d11850b0a41c41140d40042c1001042d010905956440c0c400509661903c40000f0031145480340c01d896481e8400e07103c0b640c42039018842d2401c0c0361680d0084000c2420040e00100000004944507405050130500c0c03207070310240c1802080844a01007010754800c00400e148500007205e030341f082c808040000d420880c041c1455001d18405a15511200c81e0440030944011507240310030304080342415056000726a01d4061031a00240c02144d400142c801c0e10312192441d01c1865840780305039514000001c0100c00314510039020060034101401a56100388030040c040480021640ca40e001c002e0201c1c0c0071250075035114031101c1c15031140725210403401c41d0000c6403030618440d045120200d81c0903220041c0a8001045200b884034410718503c00b541130020b048400010f01090442203100110000640014141c42d00a6201e042400380c4004c8500070009400c05880300d0301c60381c010705240c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 475226106 1250 475224856 475224859
    0x4140d08040321030c0306081509010e150402040f0c080408070c2402160b041206020405040c02100e0309010c081b0d111203010509070507060902040903080129040b09 73
    0x1c0c400040422500707220340c0c42041214030641150601220003408850000799502d0401d45001028805103400143c0420304104041d1100d0f07803035460051032800b4200c00c286c030401c980280c1140d0501481464001da0055100301c0e4180000005014941c044428010544002514130b40c04140030a4200b4010705445001d40205407407503403103071800e9201c126440b0000201c101c0790701c1401c85481e814081040c5117455124024041c0d4946802c141e4a40614000c07440c2c0c2c80380032820395003044a154112401000301400900012a0201c0d003c1d481e40c0011402280f040d0a104884054244c04411158181c1058440e04200c5a60392036000c00e6401990050801c61503c045a98000004111004c02a0125078540790004100d18405040012401d044015240d00340018002a501e4081c032030762105e01403800584844250030004058484a03c2c040c2d080381c80c0080200505038040748081c1a40c007116074a003060301180303c0c01c0e42e0552a030700100d910000107002c01d00400c0403000003013114640 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 475227356 1250 475226106 475226123
    0x30201050a110601060806040e0d09090f090b0a050603073f022107090908160203100203010b030708150901030633140a08060a1e05090d03050a0204140d 67
    0x2c900c030146040c00a07000f202c003084201c0200900c40ca024000c40035101e5200c809400310400010340601420618010f90400c0717521035010a0204800c5c2d4004100e054100c00d015401d0704200721200010901540e40c9402401040000b02e100003100407881602a072440603c2503544030400c0c2803030143c2000341449d00d0300c4902d40403000540c0d1030a003070044a14404031084810100c5410480c5002d9080c3e00540300300307041904d00d0010808000c15503a0459624200c4003075140705100180c18880c04441d034501492000c030020a08a26045c0614400c501d40e4880008a888012000228081c041403c40d40000104014000039280fa005440c07101050300011081e846002e801c08491440c051190518801400741040380ba485200c00b1114241c095400544160401d030748151600001412503100685410510700c5180240250082001c87d0050400c01c034201581c5e56512040f42807001000242080003260074841c2e14401c5a0482e09400d200b04006107003034043c0980c3d0009040140c90808 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 475228606 1250 475227356 475227377
    0x1d0402040518010c02010c081303080c071b03030c11090103021c1104110d0b240306060712050316090b0706090f0206070c0807150e012d1206090213030201050a 70
    0x7001d004e5550428260340010410b212001c03c01400060300401c1755010340c202d151200c011070340044115400c907140e20340d001e0750f458450804a082c0303042201007082808032200e00000781680080300d1a21184aa40c44090403000201013080140080c08007a600014040d00640c00e03504c42d00005a6252140ca03244044000c0080004d0441d011800c80703603980c0c00006100e103085045407041e043c01141c1110302d01075920011242c2e9942c0d41c4100c2000e4108000000030901d03a9032010280c039605580130f40000a4011f82c10340041c01741c0c005403100280f40c410078090904041c01003d03003409480080103600d04011040e140d00d00603000f02c2409440000c0d94610240260301e501000b40f2003223010760f514021803441e203100c191600510f948207000c580200090703400f01e6030380700e04054a24402480c003c10760306034411252024840b542d001f0310141e080c1c2d00d80e2031440707508010b01545410800e0010400b06581d0b550820591040002040204083c0c00040c80150300a50140c2008480d42c9000c2c0240b8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 475229856 1250 475228606 475228651
    0x504090620041707031703090109121d0108280b1903020306130c0905060310090c090b1207060c1704062f0c0f011403100602071d04020405 61
    0x803103003080114607800300000e0900007180c4140205500244200080088901e591160805018a01c00d0000b24200c0040440e42c504400d400c00c01403190040c8141000a41c0b2600241028100d003da203042030804c400504d00315030080340c900344100b9180c00c440d41c00745003206001c038000b42006001154982c5d03a00f4011410384548058460280080c8a084003840c00e6004140c98400c006040c501011902105800010b005420f618120f44030002c01003826114400020305000c0d024051804031442e001d802ca0038050480807001c02c0710f42c0c02e64204803e88100701400146031926040c00d54960007103004110640c0304245040d01d190280c40c012610701c040d4010019207510a070300400c0010000707044a0b4151454811940c41d201c1801120492115401c038a151128850f0080a00c51580003020090503400b502d81c101c7e00760701625809a40e4908032070074a0081c206800381200611440d440407035882d40610740362001c0419840003807419501c070b0b801c100243c04001d2800082c09914070761401348 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 475231106 1250 475229856 475229891
    0x703060c120e03120c0703210b04140f0603031e0915040b0301051309111e040e160510210207021201020a080f0c0a050d0b150c06010b031005040906 65
    0xc1000b140043d59503902440c1400d0500d00001e802d02c0c50401c030070000000003c0c0c20500100c800240132403801c0c05001c07003040600007080f000307840f15003050030b08034840c00e03541c1c002014510550b0300d022141a69211041415036074020304020f140074840f9014011413a01c0680b002e0507090300c00030024244041c035550509a90740060380888030780c800202c0144920301d0203070302c0c01d41d60350052041040003442d81c1d2680802d089121030824007500d07942951000d0295000000c003198030001c1c00500c014142d413003a039543c8201e100c1460180c40c2c0d0703020001c43c461601c0c0d102d01d0100c0c642d80d80ca805054020f903801d646800c80ca1140c5401c3c085d804c0094100603140c3c00c0d140c5480d21030301000180c68820904c800b400b10b8030002c0c1846007442c010001c02900054200943d0807454051510a440700c038a125030070014495484955400741c09540b142042c250040000c4c0051003282043c0c4d420f80c2d030b030b07500c26080d03074081502c1841102d50b1b94075040c0200d0406922500b00e4901590b00401ca105240302e15148 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 475232356 1250 475231106 475231121
    0xd0807030801060e030d0e060a12020f0903060f0f07260109050a0c020a0803130f02041104051e031e0319021b12062d0112020a12050703060c12 63
    0x880c18000041003c0780d0000d114030b211610950240c11a180740304401001c44041401d190710458011030b030081ca1760711810004911130a40300c011035130b542070310110a00d282c102101c3c580c03007441840d000551100040f860240540703120089074680703495100f01900e120701c034040810b110380c170030b2803a1503240a41e5854050003018604070004141c00d2031104101a14541003036a0199401103108200064142c4202c2c0d0b4808142c5480b412841c529190a00300c11100703000195009091040d9084031540f00c0008004503002218040303034440d0050f070b405180c5c0000c0380034a98035411142c803800e2304045054004541402c00030139645001011080031001001c1c8080010050340061140c2074800c0660074800ea603e5421190900040b0142548a070f80d5079004000010401c0000300508080011480c144c0141d00003c82c418843c0d0b0f1203180b50800350390010030aa104501090000030000c0c040040041519004006401d006045848030400740c0b201d41c0c2030302c04110050070400c05d070f0710140c403a409 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 475233606 1250 475232356 475232363
    0x12030708031014030f060f0a180813060903050709020315030d0e0907111e070e01092a05031b0409060b0d0e01180f060f0c2715030b0d0807 61
    0x24028140401031450b07000f03064000d802a400044032100c0000001102944000360f4006120146d0310010140080c2041c80c079900c40503070520a00710200310501000d04901c03011124110741c601c1d40c81c03404072020101440084c000f600310b92418082d4202d00d4005550147c417007100428001d0140000c685413410302094030b00001c01c908100d080034a000140e164000d8190324101044100d540c40301900c4014110101803203882100310541c10340001c2c03150b100202040007c44102d981c0d0345181c03402402004004141d2041c4100c00425054001c0e1619003e008603a500c4a01390341e904190240c019100c0c42c13000e405900d0501000034200541d00403a0052b01311a0800350f1691741240100701510035103a04544513074103084130491000724489050b01c002c4c0c0c0001404120340c0840c10060028004103884035070315424800181c65058000f01001c1c01c01c200e04048101e2800411450145141035004a41e4010145411141440e00c0382d0020909010014444104060a0703907441a0951003c04204d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 475234856 1250 475233606 475233631
    0xc0201051605010906050c090612040c120803071202070f030c02150316020c030a1e06110d061701140a020d06080303180d0306050f060f1201091a15091203070803 71
    0x44007089a6401499000b80344401100c8c20310000c0b00c0001d4080c06040d046034016071034000041c09228032503842500a00d080402c03101080c1c494203002c03a556004684990109a003c0303022498080031384204e503403880c0c1240600c01c8440c440d03582102c1c043d841c4d00060341d1200500c0d2184070400d0b84500110302a101c84aa00c80003441132140181c144517550341e9246c4a600403084810100d815400c0f8541204240c8210401c907007030900d03180e0b004001c01020610205030202e4118501c404983c840400d88210035070615140000c0018242a2030108054940340075030240814041159500a441c0c400c0c1c90b03035004104e4548450401e45150002c0300c400300c4191034811007691140051110408407001d07894207101841c00c101c041002d415a03044028011300001440e81100002c0100341c58240d0009001d4001b296900c0510300007030506512100032800144841148529045541042041c250780c0d816003050481c070100000d12284200c1d0000e00d0204010000001c1c3e100c0008610454001220 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 475236106 1250 475234856 475234871
    0x30c010f0f06140d020d1518140a0309090b011b05030a0908030f0a0c14061e1602280f0308010801050a0c080a1d15041e02100c020105160501 62
    0x41d005072500e55008021105160122444039111420052141c58050700c40e80c41600c45031814031050511100495081031400007080d0b4081d0035603828425041c05100100301040e0031000d903686030740120700d0080110341604001c01494020350003c0440d408141011046610501000a00c040f9141011919074200250f546c41180d0040c0400e80a0614080151309080c00380329144468440d6840708024080500105d50030000c0e03031145240c0c0503001c1c500f0b441d401d0038483d8858156280d000c4107410040350060000340c1c04005401c05005080c5654000c0419038980380e09402d1040245500028030b41e440551900811103241a00d1030681c441d0f80c07001e103290704d0002410700311500a06141040307401e002560740c400d94801c400c1078000d01b0401000500d04024038012503052031000101401c3d0244000c205809400c007041d4902c00c5006000505083d206c0b000544110b0140032070033584080203062000c401d078403554a08071543d00c1070514070700d030802004452108006c00d90048500ea07445481 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 475237356 1250 475236106 475236131
    0x10203060a060306050a06140409290603090a0308040f05030f0d06050a03020603010b0c010608120901020708010e1f140a1a0405060105030105100302070b070915020c010c080309030c010f 82
    0x620740003000e0700d150402126080c03000060f0150036511509040149102c2c940c58032600d0b24040f100140f060040c200038841c40d60b03007496802e14148009130802681d60b20500c4290a0031000c0320b02c01c40a001c044c0000c1c003920b07902a10358a1019005540303010310749410344001041000180702542c6400e048645070728410441000b52030164001500881e400303042080140c48440680b41511900c10741240c486d213200e9800340c01002c243d4420840382c480d929585e070014054030300512421000303900f075801498441d80002e00b6281c42c0c408004e000e50145488002c1c1d0040460094034000051901152040c415158907840d02c00c16a0030304001995452107a062016022407001c807900300341c405010501c0d022001810500052103007500035012552684e000d01c3c40381e0304880103076902c03c000c00311608041400400c5051540140d5800c04640d01014516074000203240c03540d03090581d580d0000808a039140d40040d00080e01704461480700348003120308460f00303021f9103003a0f0000110010b0706201d180d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 475238606 1250 475237356 475237369
    0xa09111308070f0602010c050d0504061401062f0d030b0102100e0d030c030e0604140c0618120708030f280206330405040c050d0c0807171b01050c03070501020306 71
    0x1e000c4e50035603145c90305103078a96400c181a590015400400020310340d6490805a001d001c80d4030281c2056564040082560b98110602440000203580301c100c1c1960750080c9000601d0f50006000201c0d4401500c031005a071080d00541590441031064400445c0085504015586809001034498002503e043e008035490300ca0040c0e1401d0500d018482c03030302d0b024801511280d0152001d080b85800301039020611404200480c00c111004d8002a6903035500c090f07020b01300d102450b119200d07d0384a28920011400010060b003a00d11040c0650b24200d0515020882548080440501c48104120114202001e000b555110740c846030003030f04151070024811151034201e00c01041d40c6a80c41d0f08a0311003d6030042c41405c0e07901d030590b000180b54441d030030112207070030300340d030103c2d40c007006a40316901000360441115080302c0b448021038500355103070b20784165007044038031440095600216500229098100c09003800308418100306141000440c2240c5c08c50348807140503103030740e90004140401d41c00c10b034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 475239856 1250 475238606 475238609
    0x15080703062103050f122d012c0403020a020a15090e0c040f0312030e03040308090405100315060e1b1210150f0e0f0a09111308070f 58
    0xa1408100d075030b0400e02001800d0882c204201e035091030642904003014081d2086525000c260f10b0300c2e5071610300c521258104948100c03149102c080300180b4180c0001d10f180c0e070200150500440c001d080d6820228120071846140820745c2c0307204034400c003000c00d618030040d03c01e00440c0240e002e0041c185450041c0014514075610007585002140c00c020180e41c1d0003009141580c0940a1558094440404000707050141760407030150fa4449010010400c440f441203100c800a07a034070144041d182c04181162240600e10001d000407804022251841c90998070103030740072041781141450a038594807101d06111840c141001e0407a61800d0a01200015010744c40e80290f105200c1001000c030007080207280c1c09811811403401c0c02100104005204e842800c00240445644100c4030304213404008001620401c940c90114500003d015194200090b62281042c1d018020f1030000d450204200e000f8084100c0300034400342c051060300003c1031380000210040c145035004096040c100503d040192885 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 475241106 1250 475239856 475239871
    0x120708130519020d0c0b040608010803040810021605070b13050a051c0c0b0d05070813200103021201080c090106110601120201050910120614090c0a05070203071508 72
    0x185612002603000074032140c1072900d203803002d0401041840459001007240b48002c1c44045c8202c00801c1c064180c0c4050411604983d403920066641c40401c80c0c0c40b0301c998041d0010b142c00145a81d0b03440348040d00105070204041400c8044405981c40d43d90401c82c40e41c0011070302420000d20b119008118074041c80c064502156000f0640d8605000030340d1554016134040d940c40d24010ba0441846013484a4600601d00c1c4800c05994141251440000701000c4500d02c0100b181d041c040341103100e0405540f0800c640c0540303401c100e1140461402000e82120000504041d006c2140d00a801c8217415524001c141610042021030b42c4a420441c4200050308903100308965281c2141d2681c0300000c1080c1107595a43c5003100c04501400103c0d460300c1200242608002c1c3c4030303505a050f43d4441c0d501590010f030134008000d003a860380b41807030b075034604100442d43c0015200007181e1181003080003070008803480c2c10128600a4154046402c1681c0c9500a20110319440748102c41c903904841c086900c80d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 475242356 1250 475241106 475241131
    0xe062514010c080f0912031302100c15200f040509011406120a020702060c03030601020105010e010b12221203060e0c03130201030e1603050c0d030f0f050d02120708 72
    0x182d2000b050705a00130905041200b00d240811500ca4080c0980410a140d241d1200d64074908050702074220100c1080c124011004284145010340c4294a08401203034003110750021100c03001c0724400600b60001c60815600703118610804030414080040240410300010692610300c0d020803c4504070301640308800300300741007050443d181d0b82c0c2803c9903803000e2081e02e80d4076503031034007030f426802070042040007504124000b41a40c04828008099403250000764024000342e0f0f03c480c0000c2c040c4500b032050342700b0b03403000f03021013003000300044081a0f005210004214450410203442c3d07001019022090750925200481c0c040e00c6607050084901814502c40000100c0c103046c5204840c0d03100090010800040c0560014216131103a00b261401c41200b00031a07031402314225456000b41c91a20089400b40300c3c000034459941040c00e0444030160f0103440d000d404080f40401641c2d40035030a1051020880e0400408042114510244c6544900403916603900e2404110180c64040c01601c0740f0340010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 475243606 1250 475242356 475242371
    0x70303120c0c1709030706050705010534030e030316170105030a0602030a0f050108030408210d0b0d050a0809010905041b050a05121311010f09060e06251401 69
    0x1a008440e20140c142d200500c0c51208440302031503c8103014041940f03a150041c00d100050041d4030170040c00341d0f1400b8500821403602d40c3c401c1e050045041c020201400d04c034041048031a400032900c2d802c00000c69013008144400e20101d80c40c1554821501e1101c0300c101d030030712200200e621000445518200f2180c1c203085506000c0042d60b500720320030005240325000000505c0c4903150303070004503811000700c40a1101f545c40d4949992a504103001d182c00c0740c4500310f6019915211026410120044950690300c0e01760310100e4000504020990940c120304241b40c03000004d142040800000c3c2d01845800d515040010001403044107254001072003603092400011f64600700c800b00300280100350400036078551022a096030715000b1015a610710006c142c007000039070b61690300003600040c4900805010b01e00383c038006640c140481c110800018024000c2071106c0b9026605c07500c40300500400da6410300ca10040070303081c020b01d40040300d460058070b00d0500b02040980300384a404040329400038000754 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 475244856 1250 475243606 475243631
    0xc0a020d020a08031f080d020a1104180204021b0a0c030201030b0d02100e031e060103260316140a020114091f0b180709030b01290c0c090907030312 65
    0x74040a482043c5880e00890300c980c00b8105d50040c2c00083c4290420b03550300042c12640a5100c8080e0070f0140e13101c000000b5180e20f035207024461103580700c0f944203091500c0c10302038081c03100a400c4164485208644e04166072001c000801c40030b8070440c89030f0001811a421440010140c1d03062002c1c650091001851b43d00040e81c4c1d1541ca00300b8021585030442040c03200f200041e00e482607800080859541080314044001000324180b8182ca00511010101011880801d00381010000030a10044d5080c40481c2890030070002100b02444a841d100e030518602e5401610315900200c0c0e41c10250303644a0009a001390340c05103059101c010000035100c1448114650030071000e40c046002d42d02d603507e4010314459601c40300c010381d081050341c036a082c071407610560160420444c1c0c00203031482d0701ca2600000c1c16846402c0a000030200307001c400009075079001c5680940341c02c03200140101d40035015903110142c9900310f07030a00c10500900241003043c99810060100d0b8030030b0158104d014146181d03070820 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 475246106 1250 475244856 475244873
    0x318030a0e0402070c051009030302060603070302060403080d0f0204090b030d0c0b06190e0c221a0315040f021b010b18060a0e090a020f090f150a030b0c0a020d020a 72
    0x1c9070156000341e940c2c0c1e81031800031261111a00641d42c09090079008580059104404e4000eaa100303800302c4807161507590415075030301c801d4071000f540030300304000074000102e014000c3e05034140d48030004182c004040d40d84074207a800c203401001c1c3c50f40e03403100160124030b020004a144103000e4117060710000c0396500ca00c49803000040c9198040ca080403078046e02001c0305c0e090000107011345560b10030f07039042140c0b4513076440d44a10041240300b008007080310f0315841d8001a0348201c80b2b8200301038036100750131156029031ba00020805040744001e190342000a0700d550182104040d0354030b000582d65910782d603001c0043c02a24000605076894000300103071171307119010302c00c030007583c400f00c4020740741c0d141030010304040300030303001192043c0f28407003407202d50340b00054503ca4280c421913044203d29280b10a11889000c2213803245586900000850103400d9040902001d41d2005810341c000c0507100e4131401114141a20707041026038000440113180350b030500800c240c030a2288060480c091180d11138421 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 475247356 1250 475246106 475246127
    0x7031b0f08010b0f0f0c0105010f0e0c0301031707050a1104050c0c100e160305060402090105100f030f180309030b0606040e070e210f15010b0a110f060c0318030a 71
    0x41500010300c0d1390420856400e8071002503010844943e2960601c00c1c0070b0281c1380c00e200e924003003000341401182144040c000d542c45684085e040d1400c0d40c0c07854a40c0700c283c480d000403a01c141002009084080f03030090103101d40c040d004a0584100e40785040c148001c581d40100a000001824400400300c050086000010314052120100e10891039610b0320b403e0041240c01c642450300b80c00d100108101003c10b50703500c164001c8510741100c1ea81c4d0001d00c030407003809417441400501840004102640250b0080c464042e020500040607a00500108401c0c44112020750200d00c02007010000c000c165404135074401c40580710541000e14189104c0c1d028007001c0c09000c00e12110400724441a110400882c0704400c2c2c005004c101911a0640d01c0c2c0c4525000300904070343c0c041c5d1058200071030344540800381218040c04120345007081c2d08504540ea80c210852408581c06111489060000300b0030055014090b408081690ba042411001c064864100800303e0241c00c1408600d0080d9000700c0c4045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 475248606 1250 475247356 475247369
    0x1101050301081f0b0402030412170f0723031f080f03090904030509040911040b01030603050601050105090303040902041707060801080d0305090c040f050a140c04121a07031b0f0801 79
    0x10f01c21020200d18001a003615041e45030424800301c10441407010007120300b101801b84c0d49640004504040f01da054050044442d490800e0740c0b100882c08080c450746840000d281024042c010302810407103c558542d000f038800101800703880c08803d04010440130a0401420360100900c0660340cce410156881e802005845071156003c2c0d8005410300d8002c804a8103c814010020070803d242072406000c00110b1a00b5203005610741540c444495000740b0800c800c0d282c004008003c03e031319000045070183d0041c804641c00d400140b100056503001070025001500c103c8000c0a050320701400101d01d400c5160713000d0703000c10001100400500c01c020461104052182c5000314140d0385026145240445010505030401d2904010032503002141d4401c40c01038a00700c400340902c0c82d1140d0402d008000c15034501421080404c010090741c03102043d800c0005200f5500210005405014079003105421507200000c00d4680e9800c031800c4800e9260001c640a55040069080004c240010f290420501505 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 475249856 1250 475248606 475248643
    0x71208070c05010606050315040515150706091110020d0f0e0402250c0512120a17010f0305011d030703030f0e010c180b041d280207110105030108 64
    0x34416510415907a5540e40d0040e0092150540ea40b40003041c1d40c1c01119100d089407000082d1604510300360040c40d000b810208803034600123201d0700401c51031400d1440d80e404190010040400007030228015100e1050064454440b0010440240a501d2900c0340070301003150403034061224144d4000042207244d850600d44440501d8481d00410001d00c5402d2490050000c050544114008125500d41c0c103c0d00c102109101c2d0340e40d445c1031009070b5513200030701499034002481c003040d40d04405000d4070020540d440c094880d1030014441034603005003038002d200c3c840d20a020500c1448424090342880245029001d074490440701c500c0c40d224084c01c08001c04054a402420800a649800003410001c01500030090f109504a0143c512903111440c460128100140080c103031415800780c07021150b4080242e503000904a1482c00a81c03c01040c803076201c1d03100c05600d403184010b16122a413a110802006941d042c680c1024140c000d1034001490420a003003005005480c8049465070311441801444d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 475251106 1250 475249856 475249861
    0x102120106081302131a0a1a03130c06201b0105090a081009020f03010b01051b010e0109060b010e19120519060207023a060216080a0e0105071208 64
    0x4103c0c51005209004e544080c400d19401d841403c280e0003011894040100381d8440d4480c0c80070310203028260b01c10007903191000c08003c3c4414184c50700641c0d104001080404100c10075035240400300c040c640110000408841c2280075900700c654040d455031110304020a81c90700c4400600d0600c03007894001ca4104040422070b916a500d0381d05040002d0921001510301d010121074a1030000d054166041c1d20550280c1c42c010300608041c07168076854001a50380b10719203084840f081c3c9c19030310050001e101642d81c0d40c03503441c800c680030f10801c980c0910854000c1140307012580010f0180c19480c030007030f22405a40308920120f112545610080703c0861050741108111820010305128a8208081c50620905291802c0002c0c960041c402940308445c2c5054480c0c074080521280b0440c0030a20929031888182c018404001c140254080d61007008007628004115800d00290390348030740c007240c4000c1c001c03404440d00c640015109042c001c0030701c0e00c681030201c0340e11040e01c191f184070506070500802402 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 475252356 1250 475251106 475251121
    0xf060513090c051c05012906120105060f19020c0114090315090304030606030807020108010803031b070807020402120604050114060702040c1e1d01031e0b0a05130f0509010212010608 80
    0x40c14a95000b00003001854080c940180407410b003080c010310b1f50004812502854a000c000b910b20b06145844024290b80c00c00084c40300517030080000482120003070001303850020310001c2d070042840c583d038090400c50080340b0000d07007203491110941000d54400d100c0d407911601c0005028807448001c2c504150746890310000a411881b032a00054081414610080705000e0640024541c26201303903504032240e81e031807a009890b4002621086400e50418007917880014290003e0a101c1c0d0250b6480c524141c0755074006801ca80c03000144144550540f410008603107410b100345801004090743c0e1607400c43c0c1142c0080d40780d00c18084000c2c42513581d0114042c40d42d100b41419100250600c05101d40d804168001403c41c3d8024414644c481c41f004803103d0341544203003d01000c40f14441c0c40c09990745158050381c1e0180c4006c01d402c0fa0415401c3c880001c60b80c0e04e03281c1c50005e42c4286100002d07945103858907007042d83d0b00104450715580c0108440c1090701c46044040741154881e1900704500d880e1000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 475253606 1250 475252356 475252399
    0x24130303020912030405090705070302191b0602010f0c02160e190501180c03090b010510020f07090e0f070f12030507020409080306041505010207090c0e03010f060513090c05 76
    0x242c010760000c494070840b80c00361000100820507108100c0e0041c1d072a90340c11404591510440d40000c0041c1c0000d500581540c2406050046451140c2c0c4580481811100c039041240140e620690041c4e44820030708220f03000030f01c14072910040700e2001d0144a00382d003c0c0e5a1030004103219203240d0701c081100081142000c40c40000c1c4c40c8403100c0060242d9651500000c0c6c03a0055800d000c60b06515008142c0e40290280c400c01d600f40707500114480041e07282c20104001e0240059070b01c0c00354002d04004202202c0240b140201510361446e00240071000365032000d10b4071f010f11034000450f510413007040c4610446800500202e07103a444821000e856541390488140c01a040000e401c40c1c2001c0b41c100c10855000c02540c400e242c140d0341001020b103c3c4840202d0410a44543c03400750700507a1080c000c400d42504280c8003e54207003082c03400c0395200300220b0f08650200c0403030b8030810743e030b1380052100c0d10300341c000000b0b10072000c0c105110303c03420341e140e0700d48130070b040d1050f10301c41c0720b0108003a40d903080c540c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 475254856 1250 475253606 475253617
    0x150103090b090c01271202030102070501050103210512040f020d05030301090b13020a0804020f1207030c030b0610050d0f11070b07020606030a231e0c01022413030302 73
    0xe00d00c60071034140b40b440c0300e5a400c848000c0030f010980c160910a100d1410650354010203c40310740c060a0325107420340c08524080850307401d0343c15540800c103030b101080303090007694000c2d031040d1601c81d00780103208150a503202c020380380c400801408100e4000d8034449c1901e0990401c0d001300602855880300e1000401600e1a100300030602d001c003000004003031040f80d01c80720348a841074914600094840b0100310480c801d03904404042640440440c01504200c02080c0303034100041c0c60102d031002c00c0010a450f04d1081d5100319524500081c05204008101201ca60842000e80d41003192007050341c8040d102d03000350f420141e11603549551600c841021504086200c40b40420015a511194204085010011180c0501600c81c00303001c103119050028100c10302540146080604040001074403900308c450070f20042d010310070313101542034080394002c00c44490052400104002645000007a0810700a100381d85882c102c41441140c0c19440300814a500c00c2c0c52004140056516190590080c0900c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 475256106 1250 475254856 475254863
    0xa0b0606040f0605041a03090d080a0f02040b0c0f0a05060a1509020a030f06141c0c0509070801030501050c0324150408010c0912120f2a0308070c0b15010309 69
    0x10102e00280d595000b50040040d030310580d11060800002401680141c40700f42d640500f2940650309007000c80b8850324400780c00444440e0042900741c4061810403d03a003003904892000d07034000442500c3c00100300404914100c0c910003600041e4031589805441d0f0400801c4040551385920b6440d00b581d0100b201c4002800d841e0320f08648424107064000c005003045030010b0718544c5001000700754074851b03003800c0f440520020412030051030b06036941c4044001c610b4046030346c442c49200c0803440d55514038100740f182503695103d001c0c035032643c100f00b42950303c050103411035030f9005c000340407840704014401c440309103602c1e844034050240d441c00f0450401010048058907034001c6008101c0203019040f031020720400741d841e403100d076031519001a24101c1c2144010048400c0c440700c0310440f400b905030303004118618100741d000d01c003800c40603070700030b154401c2103440c40c84500218800705a0840a510340040591901c035403000d40d41c0c0d5840b5501200034085a42d4142400116a0700b0381c82500303c041119071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 475257356 1250 475256106 475256129
    0x170105030703050c100507020a031103161815050303040303030e2802040e0a1202071e08101116050619021c0e1e03030106200303130201051605060406051003050a0b060604 75
    0x40da42400bd00094045040714440d02941c0c285203400d02600440301c05840d0580c2101c0600c030b40503020b031001031005402d919000135400200044030f950030b20150008502a0f05c01040100400c50f10609200070381040080c000803503c44091a000306000814860394141e400003900455000e402c6d15140e61003000511600c4c107031144c1c0c4c4406501242d04421100800614030b240071000c4041001300344035010f010b0140c2e01c0304002000742070302038000c240b883c6503002540b807a1400c0e041001c1031100c10041c064606621400501c00c5800c3c101740b0000ca5080c4a000860400d04400702e110300c003028154100307681645514481c0f504020600941c160360701e101c107608480f04007a44030141c69400910600d030100d0a01803641c42040c00c10511042680700e100b0245143d0f0343d0301c000031204800b00c80000c1c0d04111060110107014084d00f0380d807403c03041c0203100420061406241003000e94a00900e40520494413840410010300700007039043e0000e0b848024440380359500d5011071f4141c026544818009007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 475258606 1250 475257356 475257359
    0x1603022802010c02060115021005100833010e040f05120d0603020414010b0f03090c0d1b0b090d030c06020904020412030908071d071e170105030703050c100507020a 72
    0x54055100f021044a190240c1d00107a030317542e000c40700b0040c0070000500542c000c039000548140d038652000d03030310001710100c60341c0403034642220910f041c04100e01d0444048044c1041c00041d40140982001d298000d41c01ca249903050414503000074001400087c00420000c0d219002c2002c140300313a114005005e901c07107031120002208035014280034401a409030742340c00c518070000181904181c6c140d82c02d80082d1031a01044901c4003074a944000c140c210326002d05041c01e103c0f5580d1510728200c01d4021440429421a00ba010201010310b562214541c59810020780800f9210007103007000d5141c0600b01a50308000c3c0c2c2c14030700080e102d080803041e0f00c0741c030015001c00d41103004c801049055010380e8900c02901c0d15140080ea03103010500642020f5803c06006104c04000d41120316444440c078039107070000c2c40b49421504504214030407041c000ca03100710a82c02201500d140c05a0062200324000c0040916648400344c41d001d803410b00301d0041c10605440980540100d048912a40d0701600c80c4000e036 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 475259856 1250 475258606 475258687
    0xf050a0203030d0630080307090503030703050d051024021e0303040b0906060f09063f0a0803061011060408040510020a120e0a09050a050a060806160302 67
    0x100390030302640195008502184400e1910502c90040400080507200f2103017603217440e000388640004040c00108604214049401d4405002a10029200b900e910f900c82071181400000e845e0010704165280407100800c1284600c02000b1100c500000c2080c51a0741c0e40301c042c22800c00c010802d1800c0100c020f03001000780002e00100441c840c0d4000c420b4212240c540090380c03621400181d8400e68404900884603100c0d02d04281c880c0d400860041c03000840b20055035100f680e080c10382910701d00700710395004029000c001040e034a0f07040a021002920b440380291740e4008841c0001f5041728040e0050000a100e024007400c04480b100030034600316891b0b07140905e0310342d4942d441400340c0e41c0030712550304030750f0655030000a00354032880d40b101c180d085203a041c032400c132450814542c110340d211465090008007640d0600c5518003841c50031b1030128051138440ca600055415591095503140d00213010090b41e40c030400b0341150354a21034900036a0307500364185002141c2c042d44d240c04401e42d03061501d030a1720 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 475261106 1250 475259856 475259861
    0x20c121305010807020a0b040209190e06010602010b06040302180709030f0602030105010f05030121030e0d1103061f09110d0e0a0c08010c050409022a070f0e01050d0f050a0203030d 79
    0x807110260303514032032665442c0c8200d80352890b10302e0040c01100b4800100c0d006203044000140d01c4600348443c030030318031420a0017609450b180c44040d1003a070032140050268550a0280b8400044141d443c88d1401d451030f40458070185020201400c01104d807008506034a10a81100d4025904403070b00245054107414010020342c0203108590100d00c2d070341c0030412500d000d4002e50341281d060788401c03142e500a144017a949000e201208504100c001c139182c0d4443d65900289401aa019140c81020948a0030030315103801d0f40500365682c00c014915248601000d43d000400c1600d100000100b800c0100101ea030f1034900400d07480c08074060400803891742c1d881c2d0008bc041c040a00800045240a5850381694201c0b848040440006102080207200c501c610b0b80040c00c5144041d120749040380c1c0320307006804c0c25170300c0501c0e200301d241c008803070820105c82c00c5c43c2c04002038000c01d100000710354500340000e08204d03030140d0300601d00c00030009440c2c140527080c06401c00080d0040c09483d41c0d0032159196800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 475262356 1250 475261106 475261109
    0x2060c0f1204090c08010609140d0b090a060e010207050c010c0c0509040b06100c0b06010e010e0312040302120705221d0606040c1d061b0712141906020c1213 69
    0x83c4585401d99100c1982e114800b5a8100d45060302c0e2070a46508101071007201e2005100995000f5105051b030800180b86401842d108900c50006444000c003076240030016241c2c0344400c11200ea005004101c041407001c2071180f0101800d003005c1120710110301c1e0185440041e980400d41c07000c0c1c48400c200903c1540c9420038400c10040b1a51010800701600643e0000c0b0296000f81c610007034140010080c0d402030049402541c0d05060000a00c035004000a00d0280420112041520046070400c1141004080d0245070f081040192090904203030214a410b0001c480103488000d00c040446460030381a84035411203524800380221404032104410f45e00c1c2e10945100b4003d514040c03400420740c0c4181013055941080780610b1100011300d0303040041c070350042e000c2100070300102c14101801203420030084000f804251410440c81c181410270161f007880d005551082c6800904c800d4900d000e039407039990150395001c48016151012810741520b490310300030020b9821000000e2480711400038181410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 475263606 1250 475262356 475262369
    0x1312020c010e0316031101020c04020c0304031e050c040518060a14011a0306060c16090902040f0b060306090a0e0f06061509130207050a0f08070b090f0a02060c0f1204 73
    0x70302d0b058050581d01e070010010a4401c3c10032040500002d10411554100b8010510440d00403000a50002e000c03030744410510710b141c3e48005420010032021105036030070315000d01072401c40b0705095100c40342c50b080440c079030a2040390740e40001250b510b000585a00344107020030403a00140742c0300c9607120041840e5000d60486480101c0000383c0078010300d21003441c038100016030904603140e4030284521a04100030b0720030315000d8003102d000821030142c0044010b042303184010900e80c1480c01800100c4241c950001001030500d19107040b20b890711030413030b41c11100aa0b10410305540315007005008010b800d401d08041e0142101e650300480340003840034000d280440e08600380c4481c1641c041c845102d170707200b00ca800102550001c442c40e40d50f0342c094400d041c010419200390440540d500e01009650b00c0003150040f001082e8207040c01104150320303600103d440300902d8407803288000c00c1d40d50340c204180240300c0c072000100d50320258424805c089440e11484225030600700e0188000c1c010760090300491 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 475264856 1250 475263606 475263617
    0xd051b0d051b0901120e030d11181c0b0601031b02030a030b0409030804021924030b011403150a030f05061806040b0711010b10090512150f1312020c01 66
    0x95005400c2c80403074500343c005031111190000301c80840c001601030f000680185000a020700e903003d02c05401020364612002800c3ca60b11f440004003915083c884210250203a551b000721007180200c00742c0341e04070854020200d010642c0e29100101c1c0900740b002c02d00301c1d40031000c00e941c002041d00040500f0440c00303035032420b0092180f14802d0008841d00a100a40019030000c0881d01609040c1c03e0449140844242e1104064550040b80f07900b41403082030100000804c400c80d4015580351280d8140d144091a004100031040f11450b5402c1c00040e1a215655040718144d001d503a5030008824002c59200b4034040014801c0d0400701d4581500304c90980d9510002402405c02c4207010a2192155900250f40d84454448007421a100c5580441d025515076990924250700da445400c403d80c6105a0f50302c4521042c100018880c400e5544e654403900713544048045400e0500c0140340c0c0b54050040703581c0d21443e51302c032141030081c0240c0c00e0300500990004150030171482d5020541d0010024280c0b40c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 475266106 1250 475264856 475264891
    0x171e0c030703290f070c030c051501031101050c0d11070e240a0b19260907061b02120c0a060c050105151305090f070609170604080d051b0d05 62
    0x203d011440341103d4030341482060030009034044c2d014a02540318039000380b401800340e0200d81d8a00349402d40c0201c40b0141d00d6014401001044028648130207120400e103071082c140000444c2085d03035080b0074500c0e1011700030305804100c50b0034001c00c07650000300103000000500b8103124409c54a80d031070440203911142c01c0000c0c080810704000b00c1d038070111948003103403920701111a0003503621800740389452401c02111803080f511102003903156101c180e86001c003201e07031030074815003007403078081260303c81c0003808588007503c0c07910603a0b480c10b08112601550800d0701041030074900380c149007035142c03c168803104120700812603541c010b03011240248110001c00c4961a0300310704160581511601681c803240300c20b4400b490141ca500102d400c154540c0c11515004041e2560b0f60a00f541030b0440d40001c1c1d618001042034907040c001c11401860110042c4c4071030705050321501824071504000e2080c640d1908041401103100120940b140c90500940c0307504d64001c01d400388041d1005603541100030070300b03088 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 475267356 1250 475266106 475266173
    0x9080d060603290604030803060105040306090602031f05010e010c0206121812090a1806030c140108010e0408030103080a0e03101b02150a0b0f1903020a171e0c030703 73
    0x40340070f0003490051550742864a595a444407962000b0a05410401c082c000000050304901503c0b81c042e206a80250b140c0c0740000451200368005031010329122407152041120f41d80188440c40c1c480005e01c0e00605086540c00440c195100382240424041010020030940704207240c1c0028414942c82c06854000c01c4c9100302034883e00601903403643c011a0940c0400c0300044111050031000f00d0010046a016035a8441e042c1f491100e078051200382134204200006036901c903c99601424410750907079110b0034507883d1444140014013000b00b40c00c7d80000e4408002e800384031401c2c8011001411607a41c0e43d074281640011340841141141e0507102d1456010042e40040341c0c000f020302c4c40c841c504800c0d0740c8928003e4003400310704100c540c00203400d4400354020b4480741c40031084101e0b842043c01c5024a14414010130410756404590764114040c407441440700d0118000300006070401d10100320511041c140390401c0d102403442603040c403e4071400000c000e4289440d000c44480440660b41c0c504a042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 475268606 1250 475267356 475267421
    0x18061106010b09011707050a1404150c0203070f060c0317072f0a1b0b0a0e04021813050109060906061b03020307020d11090c0c030d09080d060603 64
    0x1058054100da001800286100400340660000c1454a40c003c6000382060003003010b0241c0300480000e20015a2407011604401581c0e0720b88000640b40345440d01d00101c180c400402001c0300802c00030001c920310f080d0340d02000352030041d015503000040b80564445001d000c841d0040c0044000c12a140b0b9030040007071098004a125151a4450600200e0b100070031040015011040c0800b2207001c00380b5420343d801c10801c90701364038071130b0b600c00c074400f4542411208800032030f0740002d403a807a040054111903944481030a0002100b45c40140e12071401d0441c0031740c0031004120043e089200008503640b000b503a5000503040720355580c0c0400006441d540050162030030380c010b190110f038800c5c013045802582d42c8000200d9074040d1044c0ca080c070019600007010240120f005545010842440c0306030391a02603038541c0c00c80b41d00015149008040002d41d9280d020300300074001d100b0b695600800501c40e2850845d402c02c04101810804640c50382805401407034420040f1b200754001310181815000c580d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 475269856 1250 475268606 475268627
    0x7061a030c100302040801390507030503060d02150706050a0c050702010c05070801050c18100903140106030816031d0a0312030e010f0c17240315071806 67
    0x90040d042414100c1c040c0103000c0c049001100405508203c0061105003c0c816642401fa00042c0e059294895021019504811002281551034401000204940c1000450301c0b1300c1e6043c24441e40303981d80c510005411110b08000139410420541200c10007192150003000240e01c41c0004200c5078580291602c00c8400c1482054013151003007240c0c2001d9801044003522151184007160030980d102c0d040682901c400742c0d621480c010012641c1c1007040c501c1b0b071a005841d44140e800c03c000180e5072900411308000392002604401d54145070140f183c0c0300b0b401490155400010280c1c0d50800004500c0e148026880c0513000555007241342522141d4003854218103881c01000800303000e0850701c840d410000c4000b4000c080c10340c0c9003c00b40c8402000e008001c65a002450700140805442b40081c0c51400b0b02100c0d401c640a0312800c000888444601c00d030602814142c080080c60f803854082807800d000e15602c0c0310400c3c0d40004204c545540a100e070060720182619440c140c6030354100c01d80d00134900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 475271106 1250 475269856 475269859
    0x5070603090618051207020607020406080307020a080d020d050d18081b0616050307020a140105011a0a1403100b07050705120312070e1302030405010f060f2702040b0a0507061a 77
    0x105c500d0391404a6290141010900080145252074016800a0126005079020324850380010809500350303d41a4544c20041000c20044d1081041d40342000f911989214440000c0c000c1c00314011200840c0c690000c050107a180103100751074501801c184041c0d800800540301c008000d41e40c0106507842c04140c00c0c0c05040f10601c00101c505840b0700543d0181c200400690441c4580c0c403941c0c001c5074000304801c5800c50824000500c0d541404c0565406000c16446101c880004100351180c0c40d52040819001d40125416141ca98840082c407441180c2d091380321441410740401d810050160120307104044031003c403480104540c003020159240d000300a448403507554450300082e4111700503034030551a80e00041080003107040c0002d81c0c0701242c000765001e60b50390390b4a04100c48281c02508c55007015043c1a00e14450340e80c501003100403042c02081c003138425031308a00b11070100c0e231041d5015a0040c0032494520703902d400c0030340303401805500310f01d10940b10710f0b0420080d0f40410b15240040c4907241070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 475272356 1250 475271106 475271113
    0x110a0908010b0418060e010e0a0f02040501120b061207050d110f03070f030b070e1302090a05011e030b06130e090606090c04060f0e100c0309080114070c0804030507060309061805 78
    0xc0340c5e218840100700a04105199540303400800c20b04260a0103000040c511a078040300c00c80502c2d0044c0801c41c0c00c1600110555458429082c012500e0b6511907170317018000326000c100003004080d4080c108032040e407009401010009045c1c00300074560021003d4864141d4940925040305420103a44103254440e581d20400d00302d00500c00f268000a81907807110050518500710000079002c0388640c40304110304864164049504081e503c0d0500b0b008006010074030302018000703010fa4071134401413010511741c810b159403040d00c0c09071a102c55058a03036005a00d03c0e4402402c0d81c600c40461000012550b4010600503040000d5607440c0881d1000c0c05042c900c0002801c01e070400d202500d003d070400c0c401c1010b01c405401c502055a68116040e4a04000d983d80c0d000c284d0600e10340070b0408d210362b0300842c00350390410b28510891580e55500c1a4405c0140c03421034416805800c1010440c85140c10190483c020520045001d5406400c440252071060301c00b048130204042c142d912640b03451100412540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 475273606 1250 475272356 475272401
    0x30603160824070e06071e080d0c0f02030a110c0a08031908010303020a060c02150a0c12090b041101090801230c0702090a0b040b1e040c1e0f03110a0908010b04 70
    0x30034402030800340c1d128000e84001c82d180c05203080c40840000000701c502c28000140b1350300c027503031600514100c1e041034184002980b0071400040d48900401c548182007208000400d075034044104121026048003030003000c249a107850480340c50303a21819000a003030000b60301da50b0441303124040b02d5042301d4265000e03001c607109569034040030340b50310180c0404500c5024511840405140d078000e00940140200243e02412110058440300c600e4010b02c02c1d041c47c201c88040454404100c05a1250b03012405101c840301100040e2031038142c40d000840c556103040000c094090300107070700841040c840b083c0250b941e40e40d0b6202808503c1000002508240c8403030201c0d940207107903082600094001007020411551080100d0300840340c150801c500b210701041c030304241303080910490034110f9951070011200742c401311124105594214900003013048034051188500c0c0321303501000e001c490042105035158550b59001b8032100c02409204001d510301003004105180501c150390008800110011449 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 475274856 1250 475273606 475273609
    0x100e0103091401290406030f0b06041404050a02090115050a081801020c03070c0e0606030114010c0606062f0c12241e100b030603160824070e 62
    0x400007400102d520080805045905032400e020f04450700c90076051510b20749100d032280008060601c9032460046251081c14000714261044005260ba000719204000383c0728800418028282c1e01c0354441e00b080d07070301e052108202c0040f4440600034000c13a0425a56600c403c1030098044407107040d400420030800100420728094482503070b0044001d03403100c03212981c2440702c2e426644550400601c03608000b480501300003110300d4050203405145170801503864a074000c180300f4031041c090701c44081d2400060b0701d0144e11811a140030154070074028085030750345400182c040b03c2110591420000d9415512981e1108129214400d05050000f0044400c1c01014052403410072034500009000b0151464a44509084050010451004c80d1110392505440d0b2220307415071404140e9076400a2001e102c0e9511204009006807100d80354501e5907600c444000138580b481030034030700d9610081c201001640750b401241440c035185807205208920007461608a08040f012500600030400d05000c00400713 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 475276106 1250 475274856 475274861
    0x1701061206091704090f0f05010815040507120b0603010509011418030d0606170109020a09050f06090a060801090e0c03060f041407090b15090906281202010e100e0103 73
    0x82c050700e045045200300c410368502a07809a040f2040b8039898a519111b58101c41c842d17003034407121701401001254108200d1070b45031100c24804442000c7c031040450203110050156000034a88001d00e10109003080c6010001210b007212064480c0d442e140019030120410f002d456208408003034030b1415903403600a06414240806a103900d148800e1103440b40c05100b622845024001c01e484101031850b222444460000050708090141030044c880c072080107400202d0031098403000c852510441901e138001c62128040d01365140c0d1300c02c1c0c40e20030018407650040c0700981610b0000006102c405101010140e5445009001c2501544251700040b440700107105010340162081c0030b0100152034080381140381c1441d903080544000c0d500c0300d0024041c9840c061804503050420b42c03090500d400d5100040607401d00408803401600c132000040682c1c04041c900c58805c50801c26512516a11011550a4a0411001203001c40d0f265031406034540b038554400141d6110b160340e002d00b21100078004501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 475277356 1250 475276106 475276121
    0x60903170403031d1902102c03060606040807090218060d0606142b020f03010347071407080306120102190f02011407110105010609050604060c15050c03011701061206 73
    0x4001203031060010203d401005400c2d104200c0722343ca2107102c104000c140c2891000780c86544501000c100400821501040d00e808607a111000161903240d0341e559400b0b01410103003160b9000342d000440d452081d140d0303800745040d20303696541c080350504400c148450790f1080180c41003846a0704650814080e01c90a40740f284102c464031302504004c2c0c20441703200036070030a03041191203203290041998510004600c1c8410342c400100d40c01420f80d095401060300740035481400710400b20020000f84094000d6111826110709481030540e2101f860905200a1b0000d0390424031510040300d00c402110b60500940d200101c181e101c48140580440e003d4502040c0c0c130f07010105554070707560300417030740c02171216064880c4007962501c01d00c180d0b41c3c5400d10f003128416001a018031449480034402c9481d0b00c03051b6010b9400b1820166424102e030700307020040c01c80c4040c42c41109402c01c003c01c00c0883d00303100a18122002c80040e01c0700064030448503400e03213480340148098054a2180300002c18140d402145 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 475278606 1250 475277356 475277389
    0x1403091311040f1211040c0c0209090a050f010e1c090608040f080a090e06181f0305060c090a0608191d0f032113060903170403031d1902 60
    0x14030300783d512040d40d0b039500750f15444130100c00700202c1c1d100140118041d44d1011500115020043c840041402604008a081d0042c2c0102443c500103051002c0400102d00a241c000003142c0103d456200924041c01012030b040e940d5024495101182410041e902070710380704140c1391000400d0a011003111014401001622000702924034900403030b01020041c003003101950f40390f807103003420b040850340800805040279000c0c440000e46081480c11041c88590404882000610000b945210310002404180c002800381d005a2050150b150303503240c014024410181e901344603055442c2020389011a08030350960501c500428102c22180740c99200421181c00200720b82c400b0251409401c1ca40b03001c500c01c4070a15840098011904c0000c034000e09000a8a00030400251a100c008501e18010403440101610b0710380114600705800b0f40b01d4608181c904c040d01c040d1510341820300130050b221201105840c4046440480c2d08c0fa80301140b541c0248034a04026000208140e00b03010f82c40d50141c0912 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 475279856 1250 475278606 475278641
    0x705030703020a0e0702210909060d02090c16080301080106031112070b09060c061003170c030d05040c08060408070204050c090f01270f03050d05091008131e14030913 73
    0x945c0c2c042040d41c4112841d43c15200c7d00c139181d00c0f2032024000da1040152246209805070105400107a858134403075548428100c46407a01e40400d0354100e91071280003180206919001700001c44c00c0403055011008581c050315130242d9488014081c02000d1012002e47c00307042d0803102c003c0c00f03d0183c04c001800e042d0b10152041d494001201794079810404191001c80c03180500d50820814010454401e220720a9441501071a0040a00b110f0303035248034500000c103595880c5d00004050103480c038400c100414409040d1489450541380951580d0301201d0101c0c415407519011520341d10804003070f6411504007070040c1095480340c1005440f000c41f00c81c6500154655042c01c4208043c0701280c1c01c009000141c1ca2001c400c0c2146002402c0040043c1c6080400105000d604101d0351062101c601d00310441c1042942ca4a03813101040c1c40704003012015104030031003266035048155101c1d0149640e801544d4802090f40548103031910307440784000160b1700c001d41ca03810303600c000c03402c0e80031804500011407030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 475281106 1250 475279856 475279873
    0x90c180102031204060c03050901020a020a020f04090c12030215010303080103020904060905160314030a0203030105061b010216031b030e0411040f080c091e18210c0705030703020a0e0702 82
    0x401030075030f01114222442612580c0c018009501801050740151403c002541801c01c400c01c000d541d906401c0020748105090030611540b42c8859103d041103503040402d44409548400204800041c4070b082180103200f698020170b807030b40d010039401c1d060b29815079950800c0d034070310b03000c00105c44c00103031058825070f55841c40f540c00650b0400c03080345628089039110345514950704000654403151100e40c0041d4104000b4102c0496010003241d05450003140c80645564084100c0301e411480c00b92040021340c400100440384016a80e1002402c40c400c0d51403540c0d01c01080d0341207030000b1014800501052034000c40310028600b0307400413440841060030150402d130b1744003502080114180e001c0e150b140c0000d0051500d80c10060080c1b50710648440c1c014051281620042d0b1b40040c0c003c00d041080507440148000c2103c0602c44088120700041d0304225140c2c1140d11240c0365808901311000a02c80c000740000d1609000c6412000c603034000b4070342a1700b9468503608074041c80004009100714040c82c0705 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 475282356 1250 475281106 475281127
    0x2031005011413050103080d0903050f160b0112031403070c0c030b09060c0c030f090a1805060906011b08090d170c1501030807020d030306260c090c18010203 69
    0x3828000c00c0c0003121007204a0740d42050100968480d070404560a08100040c0b000c120302c00200d0344800c1e209000016003010038102200d03240142118101c10100006210202039405d0400c2c40125004000004650766514018482d42c114050000e01040079201e1000c42c3d80101d00245600001c60f00380740b14008883c0d91507120f01c60448d0400c03034840d1003100c14056443c100700105d03544000300c2031466183c04817005007180c0d20701961150780015940080d1410094507600321800003000340504d8080d01052400c500009880104c1e40c1c01d004002d1240007802d5580300388540301d039002d0040c030314a94003000e40e01e8210541c3e00000003150040a072402d0500002c24040c02c440c2c075604403104c000d807203010310901c1c9400e152111440100040922005002066810048803001a41100d900380d00301d059203000d074084d240d00d0340b14040e801d43d01700b411002800c00c84140c441d0b000328203059900f0316040e0030400540c0442a0b031503042c04101440b584005071829168545004c00500440c0e040100d00b40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 475283606 1250 475282356 475282361
    0xb1c020f060408010e0f010c1b03051c0b1e0a0e041103071205060f010f06050c07170c03010b040c20010b0d060f2d11040807030506060307120203060112020310 70
    0x51050800d070b9500c1401741e80101c01840300d2003080800c2c1c03009100c000f52400b030090400182000180c1e5060340b01d600001014003030422500a8144100896503400384090b091004242a2400c0d5000e0b03803803501030094541e88800d0320700c0301120007805c0c4c0c1421414428000c00c64070700180100c4014141c0e071416041c9660400001000b0828040d0481000390649441d0b8103144e40688110901c80103c0018010f00c0341d8281e0410580340c05247c00c0d40c55118802c14140740c005a91700200044040d511841ca00440200e8143d65111381a8006d1021b1540c2c14148011034a01030034803070000740c0381030b002d01c10403a020120004140c490000800c07001502d84c0061481101c2c0102151265911415410400d0090080d0800f41c2c0001e0075041800900c1421041d9412844d90b484441980d80c01d581c0c80c11008c3d00003a5000343c035004044510b0b050f140d16103107075908800d0340e40d20300c603200d100300008000c100e1105580d4910350140150400382d00c2e00d007a1846921b0300721002c0340e042c050fa000940c4c0f4880c01c0e2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 475284856 1250 475283606 475283609
    0xe01060e04020904050f1e04020f011103090414100f0e070f021f02030a0506010318080a230d060e01031502251b0503190f0317010e0604050a0b1c020f0604 68
    0x18181d06c401c60910120f082d0300c0300c0075020140200f41c961000c010240e954101070154220003802e0914002c3e0000240c941148a8001241d43c018030f080400e81c913404030001c85a101d90601a0180a2180c4540121051a5070361050a07080c0b0740c0131000a0410340f00d00105007108801c2c0c01241d144000c407003007549046409608000307503164080108080c00c1d04034051990010f8081c20f04003c511040f0560300341007400e242c40501180f1000450780c01940c4030b000e11030058480c41c10240d160325a2100d1481455026110340840300b4202100810b440a9000045040300d9100d06003d20900242d4802e0001c1d401503548954011300a003004528065410340f41c4034150721426851001d400881490380066690f40c002038060b030300105003c0400440e050b0201c03401a08a000703510242114901210542440403650011076035507400016811041e0389800c0c00760304200c5080c00155502417907030f400c50341c070818255800b020000703842c40184414139152802a001620240c0d8070b1504a021507800e900c20b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 475286106 1250 475284856 475284871
    0x2010e0d03090c050a05010c38101d01030b04081903151a1215150a03051e0f06042d0612020604181b080105090f010e01060e0402090405 60
    0x6a154070b100700076a0440c00c60182004607401004581032200081064691a0300140000e004d80c0f010051a80c0a0486150000640048032400340e114980040356000c04e4441007483d019a900c00300341c5c0d0846040c40242103c1d2104860320036841c603254a00d03e550080c105684d000310400c1600031500f9401803000203810781382c034085005e440b5540309001544070382e400b04000b8204000220a202c0054089801114030000203041d9511083c0702c02e076a401d9130b1b20a0940c4000d000c43c84544642203140580b01203440c85d101001140c0e10500b1540325440d4000701d4041c4c0200b4880000d422004d4183c0f0541c2040c07014200080401480d01104070101200403a03074468810000c01c032a02440384c0c02550040c06118214142101d80c95011401500560048680d020107650181804140c0c0b5401683d01850300f44a45801020302807020742204800c0c0100c40c001c40d580400a880361010b40d5406040350391108460800d40e18141040340c00780d0301c1d842d0300c50b4010f0302005009815940c82c000c1a014101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 475287356 1250 475286106 475286111
    0x100314040f200310020a0311030f040b070201020711091e18070503010e0d052203061a10091703040e0f01081e030a03020d0204030f111309050a0f0302010e0d03 70
    0x1598106164125071480c0c00a0007000340b200c1001190b18085040141d0101e629009600d500d15120301b50b000d4000512902010034010042011032224640e4060145000f80340741e4840761984d0100302d007030780f080040140c01e107002418040c0450903c813082540c03086400c80700f040f5400100004c82220b030400c1da0400541f0581910f400c10152040c04104000e0508030002c228003010f81840c80e4940004202e604240017010420303080b64010014618521042340110901d650b489103440001001025081d188001c08c0d06421b05050502d01041c0c442c0c4281520b41c10135107032401d2000400692030700103d980601042c08002480401040d02601501c0a100f40f0616036050000c2d45140c0304e862909900c01050041840c85281c1e8044125204104c81e8580584c1d01d005039080034002c1c3c4580c0c0e00082040300f641d550a0f05100342c41c2200d0f40090400c0710900001144a0002420388580c4030003c0e050760080031a0000040100043e9040f1501ca400003149802003412030328241010a214000400d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 475288606 1250 475287356 475287383
    0x1806270b060409060f1a041401050d0606050d0f0c06080f04060518011109030d0516080d06120318060e130506120604120f020109030504090221010b040e0901091110031404 75
    0xc0e64249446c1c2a07003078a08109108002d407145212483c107101d22402400001011070501210f81c1088000e000007a040c44030b10344035441c00c00b40c012015501a83c414200e24004030701903105103030315405125000e20140c02515241c07a8407005042c0904a01c8030440310aa05242c0c03803200780174155200c0d90300d0500741d85550b480001e0600300205480303c801006410042076140c00e071b648030080380d4260440042d50300c80384140103a0000b007580b03400c04544055402c90403401c06a00044412492000003414018180d60304c1d025555100c0100c405603200507000844182e0b031055503c245c0c4d010b0740c0241144103a000d030161041c2402401e0758161086070340029a0b011844e00308011510255181c4000c1041c40b03519100140341d4040d0b0301072008400d03000200700e80d1900c00d032803146c000040c00c412440341c4c950b900d0f03051450562051082420108048002501c0018180b20700051150005140741d541c072080c100704020f07080e8000300c10041c507036149155030b20000d203580002c0c815881401c4280390b00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 475289856 1250 475288606 475288631
    0x601050c01203403050a170a0204090c0801031101110a021809190b0f0606190503100b07050a24061401030b0d020109030b09101806270b060409060f 65
    0x1444824003c1588095103040d080e85042c014518900a0305840c3c140d88501041c1803ca642c84031000340741e01a004090300307000000c01a42d009004444445408000c009a064801c0d01c45107824440585109402034840c685da5008020f40b10380344040d01d05036400c10f000c40d03001230301e00982d03495411004805441049001e41041000002051b403129550740502c00c07944c1c4214490800900c03094050700303038102051a0340c44100584d2144d0b118035960100c032281c2e180000f0850740003240c0c5400000c003200000200c810341c482c01c50f80c4503500000903020031102a203038ac544082503540307005400c049000322103071403000d2442032038094910620005e5001c0b41d0040010300b0384140d003060a2040c600c0b82400700060b07810103000e4080700c0d886403c11829541740b444184c00c02d407800403490780e0349003000c211a100402c21142e60f68850b00c1050100040c000724215481f1411044c1d41a05483c2400900c82001c900c10b043c042c2d6003d880140040b404107110707640c020030395116202403a1581d440e0394640000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 475291106 1250 475289856 475289887
    0xc011d0708060f04110111010e0a020a0f0e0c0901050c0f060a0605150a080702010e010e01060302210d08130c081011030c04090b1c030903060608150601050c0120 71
    0x7828900000c01003030401c2c2c0c600c1c096141c0003802c0209031607901e1250203401c5e4001c1d1240501e40d0b604800030840091521107482c3c40303400341203080344118105200815a009a0615001500d6030416903903910791303e8108503241540051252414800103110007411000200807810361002c07424068449401c00d04c2410301550b07000c0d00800c1c072400c0481060b50b020300f0700304262148444686007580050700c400c14143d0040c241c03400965985d500302100744039007800c150400400c59100b41d900600c20840c2d4500c05c000c510320907425084907084502e4249206210350341507038204000340c200f00902d918559400e418911258888400380d0032801100184c0303101c5120b9007202e014014583c500d18503200c0d09001c09032046000704242c0554898404409442e45607440c1c5ea0300f00d01c183e10350580456810050050780641c4001c503601400d00d200803500782004a500000010200d07e6801e068644100642c2c1e5900a4000c0040c01d65030781031501c3c0c502c0040d901030100500000d00342c95451815a861641 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 475292356 1250 475291106 475291109
    0xd0b01050702010e19030b01120201021b090105240403200d2406030203010921050403033005070f030f0204050607060b0a1205030d0e061510050c011d07 67
    0x60000600c00840540d03080202c00b014000c2c12115040481e00c803240d005c0018605402c09412200c14000205840000250b0400064001d801703d681521900d14520303407900240c9500768000c100040100981c1c1440280c0743d072282101e561044070720143c03c2103890aa0000d50090f42c01c0301c46d1070080c911010181d040100e58040558400e4808421600c81203080c0046003204044a244007820014044155110002450b8010020f11540340c5c0f609029410304076041c1d030030302a0011840c070903000a01610488085a03850303203446640110b0070107442c080c00d031011803821207480c80005980c185c040b14070941c1e10580c01c6481704d01c044a10008020b00300c2d89034000f1400401d1040000b4060fa42e250401c0e00d110030340c03005010a60100c01c401190034001c081d48030f01c20605000c0d1041e010000084003030000b0a02031002048100c41c0440e006648140541c0c1281888031440d400303c0250610320409005e04a1a0408030320b082e403220f202d6070844043c015000300940c007415100f460800140010700 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 475293606 1250 475292356 475292359
    0x3060501020a0b0c030604230108060106091d041707231b0909010e0307050d080604060308030403030c0207120506180d020316020307180f0e280203010b0607080d0b 72
    0x21541c0b0940e40c8940443c030b0041c2100b0803071a404800a905079403a608001c0004038103c1c0980840b002d24852408041c0c028014440c4030b008074000491554801d2a985080f969032000102004030300d00001000d00c00007500584440b86132013a2007c100100400400c132481c07003921500b21020300f116280c425840e100d41d41c204c1d144c0254410112a451804441120340412614140507488490307003507004211002001c0c1d090300012403c801400008611034001c0040f50b100c2d14055682d0104200c1119641e00004050001c24008a40400e10030351044424940500440b4045901c0c1d40001c030510041c24402c64450380514100300041d03000100380e51554101034006d1141e5050a01c002c0e44a014043c0c2602c40c0f5109203040d0810340d90208584402040d1303098000c1a900e00b5140d002010b451914502c2200c1c41c200001c483c010400083c645540401c010042e807140208489084803002120360166419034032078581c00190707076448004101d42441111000c1da03955101101c0401e07191861640ca = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 475294856 1250 475293606 475293613
    0xd0f0201110f0709050903070507031406150d030f030609050c041a0301080a020d050a08040b0c0d020a0203031b010906020d09030f09030203060105060a051207090f09290a030515010302010306050102 87
    0xa50b8102e00007520016180702c40808105941c84011052031401802e1003d040c901c1206000420710012401032a8200380207015641e050b0b6850080031225950b4030030007038104035a89500c102091040e0341c03400d203410081c5404601c1556400d9840140d610a89138940410000101046042664916602d42e016a03040a9095601d0828002e480d0700900d40064000c3d0f1903201400e003007140c140951240b0b564401e440c2038949460340d0000240d60442c042c035900c544161061121645d00015510100d00d500500542c03400350701419400c1c2c1200c04803544901c0f9074071b60414200285150000d0544032403003500010f500005410000d0503441d10280c21014082240d109002580b004a9000d041d19002c0e64015a0b030750100d2400c66683c4941d146602c0740300b00306000d00c81000da111550000301c84040c0183c9842c9926040080c08582202e100c0a0010070001001da208110700700840c00614802004c068006075640c40e054140f19600c0844801402030340011700840d030705482000064402031005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 475296106 1250 475294856 475294873
    0x11010b0103150311130c020105063c060c0118020a0510080a0207020a08060709050307090605030703110609130608060109111204060e031b01060b160605040305090d0f020111 76
    0x4000b00300098040078000907224000146980c80311400c030552450308003410402a016004c00900a20f070a0f240f640c17003a041c903804019103000742d082d0740310402d0a101c08035420f400b95082c00349100c00003401154102805010704103550800703104540903000002040300e401001c0d4810803287d5410391708010310491480e1b044c0c030400d03030f0b102c09025404008408010390343d40403400000c80c1200d440d80043e443d881103000700700c4e0b8140d00c034180308121481a4100c0b908280c5405488054406600030250150b10428041004c501d4186022340b05d0031003d030405140c0400800421040c548070040d4214054407039004000a01041002c207004092404d800c100007001c003841502e4501c0381404120498091380c02003402e000301d9600003404c00310340d002141d030342c1c01c0301c114403410a410f40c3c90291495443d0900009101d02c19104640d540700c5000c4050f006210b10783c1c0c90100408014000b501003002c1403041100688030410101e14032801811410000c0745944001030a044107850490256000b0600 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 475297356 1250 475296106 475296131
    0xc0d05070f0b0f0a08060f0d1a090105160e040e01141b180103050406060506030115020f06090601030f080f040323121b0c1503060127060f021c11010b0103 68
    0x15102560441d10b40381d131742e5403903902c0020344509000c0d14040c1c0c4a07400155680c10407180b4281072146215401c0309442640d21803480f28201e400c111041c1c004905080302041030b6900c5050302082071030006000140e84240c1c07004140c2190b03621410701111801b158184080c0c10300c40d1840c0811a80c10000d42490010f40384074007410290b1110740b0b43d05044e20386d404241007143c00e4006901905015004503100d41e915080034801104217840240907008480d0000c3c0c140802140e41482101c0c0c4400520841e40303191703100100009408026a1051004d21142003110340c5074008200660065085000c180e038040358408800f00102d02d9003503540d02c05003501c407022050100b0750701c064181001d401d20a404800c90f0340c1c14036807003080c0294800480e00e05034442c50b0070350b4042c40c02443c00381e031100d0b181e511006100e400b6247c0589510700764107204c003003000b2070351103041801250b807860710641e1a02295207040c20603c200b0a4808004900028202890f01200344100610b190003413030184010760440e02d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 475298606 1250 475297356 475297387
    0x51509091b0904020d0210050406090503030c121605070f050a0611060402010e01030b0409150c1103090d0309031e0b090111120601092301300e0c0d05070f0b 69
    0x128450b0050b0300000003d015596203210030710100340c0140c01c11034010003444009007203910500510020588050000c262400c0010aa0710302007803030750003020304410b1380002c03005035007105880c02e00392000342d203104c00003e1050050300001c01d11034421441a5080004100034419990040c0c002c0011804c40d0302c100b24000981c05420a0302803c00150031164800124060b00d2201400d54006051020304020030455520343c01418503990300c100521504a10708498015950032200000c3c2e005002429080c0303040c0c018a01420721a04003203100c0c0b6500c0e62082100ea14000c2071155503081551844180581c86120a03400f0320010000c2200368050406103100e0b01650807d030196480c52170014550b40d0107888404023410480c1da40300c20701c1d10b480d0001501c0360700d2050054006194040032450102403c00454040412581c01da10b00c2c80030110300c00b0003821280c40301101407042003c0c0c504c141c1c98010701440d841b40108050300c2294109191540c0e800b96681c8507502183c810480e181481c52102d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 475299856 1250 475298606 475298653
    0x7030c030f0210141801020306060334110709060609090e01021b1f05060105040b03060406033c02031f0e030f0d0f060806010501120e0105150909 64
    0x10706000c14005070741c0384101d28041a105464820519080600003403580c90b841d214441c88120307018820140541036010300743c1c0025212a50001d0f42031000c5074480c5100c00420804d8005600520101c8520143e600c2100c86440e01c1c00010480c0d442211185039018881e0801502c1d00070303000d000351440c4c14801480c0a0291141281041e6200d41003400010290100d0b03007003080017284018081e8141060944403210748c4100c00c09031040035401c4515500780d0051501c111816155141420300d844279440003a4001003050358455038078500030002450440f402820041d0201001e41c50f2161208503d039002c1c40b0904000ca440c1c4408000300060394005440004002841c1114480d100040500c8002d000d440c006070000d0301001c140041080d52020140241001c640c406100804401ca126012125070307000792082038020900500195004180800c08800b81e07074000240c5285451041c0e08580d029140c0410740301e2154080c0d1504c1c5400007a458000640a024201c209006050140b101000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 475301106 1250 475299856 475299863
    0x4060302091206040c060f0201060602070312050c1f0c020c151e030a021306111e0c060304050c0301050c03090709180b27010218040906110a0e01080c07030c 69
    0x40e44000d41d884840680c2c04081801088503110f007801c0c030f0084d200c1016401150002820400030a481620502a5030111805500641039242c11511160502115404880c09004040081040c21141001005e50301500d945000301d8400000d81c00000342c8020a0440c41194418141c001c6c285d0341d49080000e08044c6154180d41c0c642d89441032190694502d45d40000c00c0034080200601040150024005070609016200c02c1c26118041a108980446c0841c41d00380d1141242c0c001030070510f40480d503101c0703011045035210380c90500020f803568000c4404a40641100b210740c14582024092150800e411220541c218035100074520f070f517004075104103c1400d032103001c981d4608500c9140c9091190b08179420b50f00d40d00d008070150541281c03a6013840d51190700c01c0e111810182040c809c0e03400c18010303180781c420342c0f402d900308000190030f00070820b0352020ba07261006159201e000000f0851200540c07540c240309100c1c9000034000d0040149a4a900e410030444440042d030b000380415a003550 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 475302356 1250 475301106 475301111
    0x50303011211130e0613050604020411090a06030f0c0806180a0209100203120606031b0306031006120c050d08070f1505090a0506100807120807050d0801090f05010308040603 76
    0x80b400e01088100c002c0da40700c3c1e08520110396041443e401a0044000404c0800440780c26840302c8101e01800b0054010241c4503403c504042001031900d900700c00045922201c3c61810117044400054651419600c01d401103952090707040000340742405483e00654047c1090742d584e05d0301ca00401c01c00310200218000b600d0010700041c1c8440420703419101180d0000e440e9111015024401958030341c85010100c030f91804050000d00d1a240003412684240c08035280102c1142e40400200ca80390409007840e681409601e418081001441c071030040203007201c3d00c80245602a5041c2602015070b6500601e001d540851202d20110740b158080740c01041d1312071021036840b11181401140c2e103440070405484541002c0910a410030002901000030780980160346a0383c0702e0018000500c0d0b29031080ca0030603001080100111072404410160060003000902e26100a40e0750380c07030920000c4040301000c200058014007100030548070b61305000918420410640d41191100c1d4082e000703600c9607000701038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 475303606 1250 475302356 475302389
    0xf1a07050a060f020306030c0409110d21050324010525150e190b01050f06040902030c031611060c090a080703110405060616020f010c05030a0f0f0203040305030301 72
    0x40e08121162003550455001c2080e6154105080003135401502c0192103480b82d92040300c003500d4240720380810250701c4010440560001010701a03800080802a20380300c8901040c100c0d03000f0322142c1048250711942c0c0c1c0075aa480c206080141c001c0b1082c0c110a50380d559480c418409036000021201c8245a00100114000048441c100c1c50512400b00411544841d0031041440c22030f40c0141000340c40744000d492a00744d40c2c055100c0b084481ca4400782201511000401403414840c15060b4090009003000349410f48403079540099038029100c54550038000800c11500d4826100714117846849440d21104001300800c0303865071210b0182c00c0081031800010f80c280d03281d0300d1595100040c0403440596008681d0f904250000039440750035140600e08000015074645000000c03546100f1944400c141c000d542034081c041a4007480628a040c420304040711000303d8010005002070500ca56a03e07540d0041c034040040000f19103d00100c25035000740011300000760044192030640d10328884041d4150b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 475304856 1250 475303606 475303613
    0xb03070c080c0a0c0801111314010905100e0f010f020a060c03062d120f060b012f0705040c050f0f0904060b12061c020609010c0c0b090a0f1a07 63
    0x40c07092044448007071159810f1442041400500714048824a100070030807080711100c0040750740f10302010701c0101d00200006100285402090098003034061401d001015240c17000300d005007258042220100300d003c00c8945072440c069a10f900e00c03071003e1070090225940c07558069a0780102d08030080c41651100c4c024100544a07501c002e004040890707540010b500810940c190844c1e04044d0b0340b10746165543c3c04100d0100c2982002d90765944620300001c4075102c2e0700d88000400340c841c00d070381c10813102740130450509408000a440c0300141c03a54038420b01404407185441d1941d99800740c0e00403030502c171008641d00d8024068880003000c0300706075a600c03a0303000c045000c107100e50303000194414508000400c508565401805100040380700c018510f441ea5001c100c40b00c0480b18031103044502491031040103040107009000d042c0810705003000d00c1400f55a90400100c4203030801d80c1103c00215107180b0500c0d0144424008000c04c0c0d841c0181e941c1460140500708000a64078003843d4000504107080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 475306106 1250 475304856 475304873
    0x1203051c0605060a1b02092a0915180a0e0a0b010206040203060a09030c0507090501051002010e06070c060209040504050303160c110f03030408060a0f0f151a09030708100e06010b03070c 81
    0x1700c503402021400e5620300b088000c042c200120246001c0520f101803424011200b0808640190600820392184202d1102001c5a581e12000d101c5200000b0003500b107010303449201003440038040324620041310f07240030f026010031140c00785486411580a9804d000140e1000f1902e01d8000d4201075021800019070308007500c0503903a0759801081d611403030400060807035103a4403850603918100e0701d040044d60000822401ea0340780b04800c000b80c1c0c11032000315681c00e0003818160900380c82118058100041040080c00311081120b0695841e0070002c10071040441c8149568550752a5007000d080707105064542d4043c1d014040140350140110384640022641d00f001500d00610503403049036924907000c82c486014001006511903031a041005030324166805000d0102e0204d060703601409550b14240c0c1028901a11454604180d801001642d40644003403040102511403803000b0b1407180708040b140e200712142103016041541024005000011500c0100c9820041e40e02c0c200e250261542001d505 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 475307356 1250 475306106 475306157
    0x6220c050c0a081213080a0f0c0f03230c03030604020a0c0c030c0501080c0f03190b151e04030f0b0a0f0e0c01180f1206061203051c0605060a 62
    0x41c07084030040301c1005200c03c01001d4004191a00344800c3d180d45c802c035040090b02c00c00051401e001840380138001c4e442051411844600c9240030000c0c0001e9442d56580ea802010007030700041e0a040304d41900c140048250941000300040303291409409a24071500c0b4040030f804544525000100359103542c2c407d20840038000c0c0c2004c1008800c5503240f0344103000c60080e104d41400320b02440002921303600c80105a4680c4655040d0142c510b94424004000f2080c568021198207036a44a2070147c0c3d44a40306004100020000781540d1800100b070207a0b2011034030030424244e400e04010520025024484000185234058100019a00c0d0034002c440540482e142151b0f4a510b03107800c032042c402d00040c0044010400780c071881d0340030328905d10107480c510041c012010822504901080348017822185010068000c07400000e26a480d08d4410b103d120300e0210030350005d400400ca40854460500213080d002250a4041209603d0400881c0e41406a504010103000100001208018405900d07c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 475308606 1250 475307356 475307377
    0x40b0a0e010e04030e1807081305100605131109061308010c1d030105060a14041e0c0f05160803040f0501090308400c08010c050a0806220c05 62
    0x46480d03860b055548403101080703405070000780c40f600f20800c0906240112400952a0840c0c1c110326a4950405880c010000b44c02c01c1459240d4000f030401040c000d000c00043c0320090100466203030716000c204490b117641e0b40b0400028a150034080341c24026154100c0d600e441c01521607a03100e07201030f0b0503449829241ea00c610955420f001c102803455a001ca1001c0d15042070b000350a0340411141c2c203140c2250710841d0010b030080350146042c02003c85042d103140c09008000c1c000701d010201d901a0072104403014101c000742944800200c0d050b990451642086600c1514029007049002e135202035070b5440b600000b40000318000080350034080120011030116810100912030720506107001005010121003184800c0114a80000842d00c40c501140c00e0000307041c4a000b0b509141144c81600601e1248100c0ba80c00129a000030a12003e00582c00b04402944469807640d40e47c44000d81030100c014042b51251800e00740c500c0140c684182c9005c203079404001e001905504c1e0340c0083d03846118548581 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 475309856 1250 475308606 475308629
    0x7020f030703050d0c0806130b060d1a180f06091003080a08101a030c03060103090b090303090d030209010f11011116050c0d0308040b0912160b060108090705040b0a 72
    0x81c18550818020283c0802e484001c00150304c2443d0215241401a182550f00c141410700c0340301d4507a0913811051180c41e00078812172800d0315141c012004c5501c3e240e08100b240340c0010340543d0501d0b046070144500358030b002c400d6005140002032801d01d0040140a9841012a48003084040a07944c0c2150040c60f4007000752680e0701160580238002d94800c48030f03d940b00745550000701318803a0100c1c41d50445051041c00d070b81140c8492040c2241500014019410182d590011001040b075064130300d4010200c6402030341e41d03401e10004203410032806840007000c0c1401000440004e076030158081381480c009140007050405008403040c00f5055414070a44181c00c046202301c020003c080601d1a80d5119a044850034050340d41441100440840040d0100d9440400600440d42d0081078035400390000044c0c4420051007100300c20340750004202c00d4040c1e03201c0c50440b01000b42d401c40070741d006402402c001c611403800707180065851101c1e0244501a50302c0703841d281030b16225010508046d210f1040d40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 475311106 1250 475309856 475309867
    0x30c030706080403050415181401121a1f03050a0b0a05190305070602010e0f0604082a010f02030405190c09090503040506070305070506100e0117190804140f060a030507020f03 77
    0x345041900c024105800c400100009005040d4580000303200c2418bc441e000e013000743d141d03200000c0220b9403209501c00c2c1c013444942015601c00100d511040c88420145503e2840f9440080072610000c2440900501e0404011000e0703468a1016040360070441e4401d0065181d0000c0166020302940020600d00c12894003049440d01034000c0d12100c00e0000032140e040c0b136403460450351000c041e1009030040c0c004010400c5006030710200e4080c4000e211580f098200c03410a00c450031640724042c0315564a5006c41403004101003802101c80a4180000f1202c0305041e540f50180e012019224071400603644001c40300c1084401d02c25039006085c01044907445560700d00b00034005601038072044419020f55400202040030056040f0242d40902e80c0781001a1b0038010030522503040780c10140040d100304500a81c03403502051200c20110b100c1c50b013080d1102e261406402030302c5c4500392000e00c070300300900e5183c1d030a40300c180585082c203800d841d000c50300785c45010060b81452540344455a4500000030f1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 475312356 1250 475311106 475311149
    0x504140604061a0d0b130f0c06080a110711040510031b05010206011d16270f0501020102120c0702010917011a060f07030c050124090b030c0307060804030504 69
    0xf0461014114030060400f8070869001c1004c8014980c0d0700404103444900818003802408655410540c4142d0b54880e10849549812400c50742c568050b8001441c45810046000e18034095241300241242417641810859900c95142c03603205000790303014030340d64030000781807100d121101c00046402c0b0340501c40b0718010a54020507034245006050161240800004480300d110381d01440c5661030814003000d030f0b254105100b6101d880a5900800c011a0380c604003080011480b031360b0085100780c1040f6000034030f013a0180003e80040d038006070548e4410f01c6003040300507020a10359400b000c0003007220b075600740d61720050b03452154079008290456501c0758043c0c1c1514056002945042e51b10480341c07002c21980d0304000c1c1c581300d1b8450320003032010203028071000607008800c0f1656a51003040040382d94916401040c0f031092074102440310040888008000e001410f1048819801d001e4020b440309000801c0803a560341e00521030402081080000a0f05052040701900d02400c002c10041c401e1207044030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 475313606 1250 475312356 475312361
    0x121b121b0905180103031409030a0818130e071413020f031e0c070b18030a02010f18030905100e041b02011a0a090c18080d020706051804050414060406 66
    0x2c1e64090042030448840b01592860600e04983d0f25581c0c1000f0fa00060100301c855822203e241901442920110030001c0c118901402140d0100c20003c000044001c082040f01000f00201c0703414589800d08611022601003800b4090b40c9052161000800c491400308141685480766140194408503101001484e208025400341e03020400360030a0a031400804c052000e02500c06d030711003010401c40000003c4805d445240d112841020814003540c0310340d13059065034482840300700140d658030001c1441c91035038450115206081601c403a01c0c10202d6070b001c0c004800d540141c0d4411410000009000e61040310740320f55603039014100303004503c0d1002fa150340340340104010704059424481c55192100050712040c4441c030005240c02123051400c05544024900f010000081188001c00003000481d24000340000700307610401042c0e8444071610003410010650444c0d010094100030311000c0c2c1428086c01d03c03841c001110001038980b250f24201c001c83d244403881200310f004000410007400742c240d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 475314856 1250 475313606 475313609
    0x3040b0706021b0f100903030b0312091e09010909020d051203010e09150a0b030f031c0501050a0605070209060f090421020d02031b03090d05070501121b121b09 70
    0x464035440d018100f0102d035034441842c60740320364260340b0000840c88020707081d40041c41c9041c020300b0005a054101c3c400f00b4101190102052141000000c02c0c4007582040d0f8620800c0d2520440b4805101c41d00000254100310103114050803152600300e05011341d43d130300301101f8403540c0c401c040700d190b0301101d100600203810920400030070030a8440058552074003c5588900c6001c60040b10035030741c0e1100441c2000f84039907070481350188940e03007a02400d50010002060b880450b108540c2d510184403040b841940e5058204c070303009004807202000043c0c2c0101c180d642a030350490b640780c023a58454011542c00c40140c0b00d202d0f40940e40340c090009100c0882d000780d0115202000400d281e840e100d030140c1c1d6440f9544800401a4003c0100710782c07034448840b0300425040b000307041e00e02e0300103180b002a041e91142c03601500e2039001441d080209603040311003182c00241008081c4a000d1001d02140700c881e090007803000511014001c2c2d00c11742c01040e88030041c20508009010381d00d100030325006040c40d405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 475316106 1250 475314856 475314877
    0x140c1c02070906140607060f0605130218040b220b15070308090d0507061e0c090e0912030a0b030106090221010b0c061b090303120601020d030908190203040b070602 72
    0x40990208144c190f07031200b44429000a0312042c0740140b1aa00c10004260001d0304020403940d544000c600e90340d90106c0c0d0081a40040c030096241c2012641d4001320040c5142c05500c101e14050840e040c40d196010a044d214404900740700280540510b110040c020b6001c6041d88030000780c0070030040300c1c0d119016106460083c1d55800c41951803182041e0340e40251401d4801094050202d000010000d0b00102d5810006040c062100e500b5a00002c09840b200c0961502003403a0f44001d1140c840001035040d070040d040002030404000c000c04200c828803001d402e90b032016840b040355601c81d8809420990080825071411503544806008240f000c80c0b02081c40355803049032500008400422505480d07581c0c411002604154842c0b060203160b4220041c084542c250040c8009a030542e010300180a1072810705d51152020714101e00024103011181c41281c09161400b06114042680507043c0c4a91903802030198011814a000a92a501641d48502ca044000003150001c2000640140000d841d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 475317356 1250 475316106 475316111
    0x3060136050f0916060e1507080d0203040b1302010c060e0a02330f09010302070510060b03160810051c02040504051e0312150112050702060421140c1c020709 69
    0x100d0706401048207100c0c0f039000540c6000003035094503240c0452a000744010345168031b81240f80c9d0350880160040464004920760200401050110384050310f5070129080c01d0315440410540d001900d41d0b0a0041d000d004e403661341c00c0ca001211780030000c4404081e0020080a080c030f4042c0c060314000b0070701c0800e13140d0f69160742c00c0039070001052100342c810501540c3ea4541c1400e210381d0044009400c8080155602d1150440f401004521486008082c1460b01c622603903d03d4100c0782d0850f2944441d80766800c11106a04111100440312a84800c1d0f600440d02d540e0303d1781c150505000c01c05900c0002030740c41440e000074841007010004180c00c0e000c1c2540340c41110f054240c0d14243e207900540c6501911080e10100060f03880e111814882c0144905060aa2200a80c903030480216102181c10070090b0788540140700034840c40603101d80ca502d40509841305168140e07400204041a5441c42400d00600801d55403501d0005011040c480380f1100003101e02d2080301c03a0b0096840d002403044545c901d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 475318606 1250 475317356 475317373
    0x914190303061e09020706060b0304110f010507030c0b09031c0204140102030703120b0d0c150801051e0d050a1a01030b01060207140105090a03140a1103060136050f09 73
    0x20f8a00c080b0343e1078030b508500700f5a103526201d00c2c4400303035202020440d803440e41d40341c001c10b85c4e80c07180f8042d50156004051200403c1c55000c01d001d441440040e900c0d051217070602107100000c2c4c0c00748140c1601a030007207400240d41c2384c0100551440c000e10310107480410004070341c1c184d60226503001d041201d01c51501062003d8014005903182e118400b40070300090300c04034503812030041541200d5907040d0060300c8000c050300e0035242c015041003207410001b02d40d2050105a800507903c0111980941022100041e004c0b07120003c07483c90005520016000d0281440d0601c1441018004000501d0b0401ca1070300d44002c200e6000c4d20070380c80074001120050f202800109416200040c07007020388484c0180641c5d41000c040c015645074128004555200b4200e81c00400040c015030008244420752394001c03c00400c461810710703070b0b07040346c05541c0f4000e41c480030040092950829001c1144c50071140188580900010401462202015020042420401441348100107401b4492144005500f5580b41c071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 475319856 1250 475318606 475318619
    0x150e0a090f06170c280b070b1b0a030b010203090402071b0801050601081b0c010c0f2007060c020d08030f0105120102070f03270801020414010908030d091419030306 72
    0x303c000300345030400b6408600c00c00c0346824548207403220684048480c42d00d0041c2180d5910701031803107410141490f9400302e120020404440e20854100c6100c0e0001a05204018400006c0d07014260503081090f48801e0f10038000e90080c81190b1544001501c255038592440c10902e0500f640034010082280c4060310005403024184134090040c10b0580d10345909803908210580324580319420082c401d4020003078103030440da0074030920700c07981041d80710308038288402c0c0009441c2a8424001c80c110000020080504690100e50402541d003a420010b00404160012035400c04820300010500c54000040c080440c4034858030394101e4800b00c82d01100c51010b02c250360300340d01641d500140b0494510b420710300000e002e16440b820142441d1078007034003045488000204801c0d01c1d400703104680d50006041c04400c03000e02c2201ca09040a00300002540d1030583c45542d248194440301d0040355843c49810100401026103044e03078550202100d084901c000310600d4040c4010341c0450100c0d14204002484c1c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 475321106 1250 475319856 475319879
    0x30c09030a1406070c08040504110412050c040b0f01020601091515020303090d0e0d06050c160f020a061701180b130c23040506091c080c0d0206060604150e0a090f06 72
    0x170a40c012104ca06003132411050202a142c221601d403020b00060001060703512444c3c441e2405075010300c005101c0941500107020894405501440c0503070b170b140321a1601c41e600042d01c18119088a01c001a08440c07400081c4c6001d000c3d41c010808416406030410713642e0340c0c00070185014540c1d10058852035010b1000c25551000c0604e54160408030f0426030101189056100d5984245c909050600d000408808914501102101181c4210b10150780c0400e5041202039400606250308212172484d980381c01464060005100e1518024915501c10011005c0c54020b01c0c80544094000102c00c1c000045010290226800410026014605c5240ea220600051515441c800c3c0100d614090401060114503440300c100d0759002020a20305815003610410511401070180700c3e91a2680d802c0c018103401c0520386c18181c41158402d0081c0001a0f581c00110f030120340b1900d0150741105107000c1c2c282c5848020701500c45e88940c203030400040f4007250360400401d0000d00c80f410850a925803c01104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 475322356 1250 475321106 475321127
    0x602060f01050a0b03040501060519090e030325020a1b05090a0b0f04110c0706020703141501060c051507023f030c040f080a02010f0f02060c030c09030a140607 70
    0x2030001da0890f04100da070003603200071500903028a00116a298031139003c10004c0a4210b504d08110980700d1013000700700328511401ca08040e600b0701440c510700700182c0355502d0b608030741c121449420308213801c8030707845000f0022814050750180d41004100c61462986400b5036a034804c0e00e01070301c488000610300c0840c0384101d032001100207101810380c80940c1c0030f020007492115200c00c145241000107588c4400d0410100f0010030707146c5c0c01050103600350300e04a203002d50f40b45450011613010902c00b00b00d490000441d03a044d5541443c150104510b1420020300e0525090070b1403502080c05018010120b90218034a1560785400d094108400300580d11030081c0c2c02c4640d0480300d0060b043c00109a1118071f0b50085400103224660903007450348030544141460041d6011742116032104581a0865070095030034032824075541400c0b00d0716216150060f445044c02000b011201c0c2002001580b0b803010007003600c0e85600e01a0488207404002e1506841d6a005007807219842d01c500000102140e1190710080d2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 475323606 1250 475322356 475322359
    0xb03100e13170a23070602070506010801060e0c030a110f0c0d0f11060c090d020306090102091801080309010f05130e10080c22140a02070204050a021905030603071505040602060f0105 80
    0x1d25400131016150342c1c507607440710500300c10100825004510580090031f04107000e0320140c0080e524000200f400c44840b980411131955180040002e403201e404192035000c0444d80e00403079030341d0160080581c0391140c038000310b60080b00070030540362607140014000c40418a9032a180c203598000300c0c041e903041910503040d544a07031140c800241421210005000011000307007503000c1780040c5900107418400204c078401c0d40b50b0343c08201e8204510345009981205142c2a12000095042985441e100e104d00889241800b0030482c7c0c59126620610403694a0341510034a1280039856858035420080c0950350f0007480d40c0d000501080031500072441c01d030320010040040c49140c08000c082d00c0e2540c01d00c2d00c00301e051a903401400911000c4026840e201c1e416140005a0b03038101803040108488002c0c00b00d0702590300c1407024274682186185141c90b000340c242856500ca99400000905d00900b582250b82031442408020101d21b030450083c2c41919020703002c2d42c06079501c48591031500002403007000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 475324856 1250 475323606 475323617
    0x80a0b0a150314030c0106030302031905041401180506031317041d0703060e070e0102160f090b1f050c3025110103060e010f0b03100e13170a 62
    0xb0030020b409100f103442c2d242c0f01c50703003600d007484c40e00721455003111f015a0040e4050380000074038542d903104252242d00e0000705800d00d103003007900701060310606003210074026050092500c400c0090840c5d040201005001c01020b150b80c07403408204852030005443d80c2210380072080241300468011510640303080c2c3d00b002040d6180d045031450307034030ba031368001600d080c091650301c400101d860340c0a401c015210380402d840351fa901d144003200091800c480032803a600381000300c6034140a0203101940d4882104c1c01980c0104924400e44001021544410044503c41c3d05035004140556004000f178a03c200c5c1000c02d40d018071003440702d60200c0d081c1071034031040f03110408000c80e203a4031401400b5000019010300c5040c0c44403c0d90031341c1420343c4002102900c0d81034013402a00070030369250046102420071214103135511351506980461000c001e00801e6100600400011f01c0003032420702d504005d110707006541c46181024032a242640461200c1501d01408202c0c2003407040744850b0807115030359080e83d5403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 475326106 1250 475324856 475324859
    0x120c0a060e0306062206062f150a1e0c0e030604080a03090f061410092a050f030406020c1603030206151c060501080f0a200409020406080a0b0a15 64
    0x2c02c0303025444540742c2c4810f1000300d4254417141d09541310720005070215440301240c1c225000882d000c440c903074841c90118100340012100d5014408038a0300e6401e8091001015541c03554150320700a0200715841084203034401400321841000c40c1c206a100b95075581b42d003020041c5c01d8042c19110202100c1c042c103215000c00180b842c0c40d20942c0240102ca025040205a00c60b4135a6160107a81c602c0c4420a00e502850b41417041c1803191005620003400c51903030400c2090441c101c5607490000b08080442e000900c0c00302e900b0207034000c03402c0721050846192115603071701e42450408025040706444502c58440d103144641d01400d01725181c030036203070076800030030866480031f203824403040540303070419008070651210005e8034040d0508440114465640403900b507062a440c1450040c0e841e46002480c4d200d0008200810340744502100300188515500c4c0901a004003c40c001c0c1c13480f294000d400c149003840000c0d071840e002c1504d107100c9101e27105c080e4850312a040e605066806d07064100500c410703a40fa0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 475327356 1250 475326106 475326109
    0x150129091318020301050601050c1222121202030406090e130203011e0b0a06231324031109121005180607090620030702120c0a060e030606 61
    0x1030190414001e008030040c0d11881070440a481c214001010540259490402107180a0088547c400020f182aa01308005500d0241d80c400908184840b60326001400b00281e20103003e2152100040b11001c4242941d9106035140c10b428104040e5011045103401910f010b01c003004860481d00d01d5900c140300c0e90b080480c035038000080a48042405110340c102100107880a016541038080b504942c0141c00d00950107460079201441103580c407510340b13084148485508103000b810020140061344110070254030103480640f06103103c00003030702d62481e80003444035080805000c0aa5038001842c080c031a0f0700000b58243c44118402c0c440300303d828003001d900344c01e1007241c2480c0c180c0c0e61001c83d40340e403230358035250011200240c3e40c0501d80d401d81c50f101000484200540340d0410400c1c6822003030185890802030041066049011006008410400c00303900e042041d0750381560020140400b144c2004510741d6100502c040003401542188800150315024410000100c2c1016000d070120303985400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 475328606 1250 475327356 475327439
    0x6010f0510030209031204090b12070306090309080f030703140316050f0d021305041d0c090a09052a03010603051b0409080f040302030c040203061c0507171501 70
    0x500c11402c056090002c500c07195020000a00d8108844500e15038480c1031010110907140003058660042004988500c030100000554074202d0b030700104000b0307043c0390b180340c02c130303010700d6141c0c00004c0600ca100d422075a0004007000070040c96210b07403280880000c403642c5a01082c007044a140d48003260281c4a0500d543c090300c010b00300c540301004000e107041210340c1030074120b8010400500c10240524400c0c0141e051034030a203181084c000900003101e000141e41140d032552882990f501070100d41d0040f44224540d900074004407540072040d070390009101c0d144004404c0b140384803481070900070f81044400381010b1050f00144c0b03404c240a1b2408030f00d803440d021120384154061580103640c4d4000b07200800d2450000e00709006016003180e03076852031401090324004000110503c202d02c100240007080d51034603a84141ea429070340440d8110300c0542002c0703081507141d40c4035003091051901050b01d841000300345805261300c009010b103040d0344c80c1c10803400081102d601080f441000103249400520050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 475329856 1250 475328606 475328629
    0x90c0e0f0904051c0c050f07181802060d090614071209050c0607150b030303150d0203071a040305192301020d14061c0510020c0a12110f06010f05 64
    0x30381c00c40b6100d8401c80020b0a400c400110304c2000510141c001c3c0b0100002801100c80142c0060014950700c2d00300050100001a20308128040c142c1d1a107102d42c80c00155480a1900c42d0020320f45074503244032056110280140a104403241441c0c40f408070044400603180900404481c1e4403010141500b628503001082c980d0f10543e024440c02ca41080e09035075410090001304c4c4540480b2444825411403c0240c44440c11107a10941040c000c21100c0102c884c041440501d0441d19503001e02e555002107410712425801580747c451600650143c10714840b001403080340d1240003111049410343d15540c2882d80c80c03000042a0308522000341c110100c03a411407103555182100011314001e03145d200081124024500c241145ca00001000458540f640228440d03442c501a0b5158620060752116141c000c55901c40070002e602260801e511601042101401c2c2e5111890030226200c09001070b005580e04c0340411500e00c90441209604034010924504840e90313034420710207480c00c5c04204604441d06 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 475331106 1250 475329856 475329863
    0x51806070f0e0d0821011a1b2505220b1906030903110c10030f06030f0f1202030a080402150706020d06050108130b01031205120c04090c0e0f0904 64
    0x70046205410799469524880d140c0c442c1c49007607580c03170104907480240001210b0754030485102a00400c40d10303050081d41c41000c0700c94007001e5540c2152440d103190440d000003000380d481c403424008404191401420705080400d2520700065030756100d04000e018a21400f85001c05802c12091084400f0315030802c0d011000020521031080300300d14a10560302000d0f6118000290721100200700341a000783e001480e501e45031018041a10525010800d440841ca80b2001016a900204d40401c00640d1240303020390b900000080c02d01e0000d00f0942c0074922030901c183c0e403880f45c000b1280349290001086440902068441c01c0301640d49030200710b0306041e22807a4800c150340402010300001d61a1008118101000c0d00000714103040000045c00c00d080240a4015a40750042c003d021518410b0040e04407039000406000700359080c50101d40e18081c807000740020b40307103400034010320040040c06001130311342501d41040840e80c1c240e0b04403000c0101c1d00350190001c440000b6a50642400014654401d02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 475332356 1250 475331106 475331117
    0xd1b050f19060f0c05070b180109140114071710170615030316110a0b07080a02010b19171f0903020705040e03030c071502030a0906051806070f 63
    0x1280009142481e14091402101d4504207152004101d041e00c540c1d0203054a00404102084200070f02802c1e5200c3c01e14040c280001d411300185400d60700c680410081008000240160f40c00e61905860b0710b0b011046040155082145000418100d40084ca104078120303560191040101c042807080c0910150083c810342c24065070100305514050005560350032410000c00c5107103007440c25025001c1962085500c40d070020070542d081c1e00b1020440c2c901c40c0340c000f003038000400d07640000640403200c4d503806a49200d00c0030032400706002c4028041c04d442201d5800a001c8250b4100030031202e00491904c0103a00c084c0500301f84040c0c1c0c2c030440b10454004000d8200c4608100e5004924401c0741444026140c5a45a1030890f0415906102001c0240300c142d8062041e11a1518000e40302c1c0401400081d1a41d404075072030043c0251411943c09200078140304540e20304181107050054154072006a0380d5904140c04544004540060300c2c0c03202d08044090055515288000c4658849a14080b0200072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 475333606 1250 475332356 475332373
    0x5090a1b050a0e042a090e071101060510020a030807030509030403170702040e01020918090d0e0a0f080c090c0705070b1b330709030210050c030c0615030d1b05 70
    0x840300c5c4129140c0c007024000400040f041c0d40089000201d0100202d41082100c2601b0881001c40c40d078519007200c0582040018a040305040a0040c0459808580c2c03011545035107118141c0c0101b1101c164078000c2e514207641d07640b03840c404d40c10799174140c0342070340070b6401088100301080d08110300005881010b681c0301d2034241c5a0300010f059814a2084504a03540003039042444d10b80f81303410842c110304401200701d540c68612441034540c0340341550f40d01449200c4604818968500203604054524003140c89400d40d107401407070350380c2c071184049280122081d80c0418184410282552000c99100000b04a61800c111070014590403d0070607001804148200c0854400c0902001903482008244030901000c0c440c1c0503114001d04040c607404100c0100b0520484c44d038800d80e01401c0c0ca805459112107035180c0e8008561501c03507e180c08030140030100e80d012a0703d401244080c0a420090003601c0041d07074501c01c040e2030707210b088842e81c089800301400c6290941c064409120302c6018a06440458 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 475334856 1250 475333606 475333609
    0xc10050405040509010f2301120c0512030d0612020916090b040905040b1503060a11090901060c050d0f050d051b0705062a03040b181605090a1b050a0e 66
    0x1a00c3c10381e00550030ba51101c040102850003842501c100340000421407006001d190305034440780c1c0d811b000e0098044d009501180600c5101c00c0c500000b03110150006c03001034031545a1940303940100d541e08180d030341003c00000701515007600d8050301c5a001810408140c545c645204100c1c40345408000900c00c01a03c000b404040260180c8024400b20700f000c68940344ca4904522a40700080c417404d44132111241e80d11454400140c40b56020041550000300e6a4540b100422240160301306c1591080c0c2c0380c0c001003102640441403840252040003101d000c940d5124003a241e130755901305410300142d03040c88444034004203070304029000000001d088010064540d203010135a4040038096400368001d03418080d90011165a01c081c09011012040303542159820094252001030b00c041d1a4184010100708015032030a1342e031150b01440d07411104403001c0105086000e640d20320525104600d1500001c903001d8144c050040130440904200d540070f0040401942c45802404522040040c2640038a026 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 475336106 1250 475334856 475334861
    0x103021c05120f040305070b0a1403190906020a1e0f0f0c06060b031815010e04030e0909060711010b0d141203070903020a0b070201020601050f15070b25020c1005040504 74
    0xf00c0071402c0881d540b50305508040d4503003415070b4401c56281c0020000c1507155640300307401c08161410a800c66540303403038084140d00a420340d5421841c14901e00841d070b50030480e183e40181800405a00c414040b120381010036412502420102c0001c12507400c00503130414030804240008502d01e0528154042072a01c03a0000c450541c2c0010120241c004140f1840311480140e4241020000d0b0060203542103115581c0c1c0c2d03c5d14180b065940503080c800106007098003e4603030304110f07500507201c000386282210407903558000545da00000f140200401f046501740602880c1000e580c094a800c00b010b0302680d4219003841000380040c5c55018407004210840c04100003140a04070550342da0100d14214010452082d029500120b66500c04000c20310050342c0110b0b03041c5c1119000c55089168170600303c04108003140501036034203074480000b0b04a00f0007c2816455018402580030740c01345105128100d90b120003000c00080269101c508541c043c1e00e400c009003900c44200c0d01c0d140d410310390b441c0c0c0443c09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 475337356 1250 475336106 475336117
    0x31a150f13090608062a071505010e15060702090c0c102004080c09060102030c1f05010f060206011802070f210206060d03110a080a05030406050105090103021c0512 72
    0x540741442030104458600c9005001c083c20860010b420b240c1014611118400c507001246414140805d1080d05038a85000030b80e804e480c0c220300d60b82d169100c403455003130007480e09009402280a810000c10390102c0042c040411818025000c030745003140c580c0821021460091414060410030000401989000d01c2084600c150a440c0401e107101c80f000d10360418800003a0255150b10306000401c203490002443c2442841c040d140c41141e51607210040303085109803521400944501c3c030308107150141c900c4034200000b00c000d00400640c2d0f21140241100b40c058410b840c01a80900c0c014060413048016100d08036161010042c54441d5603030700d0b610031080c83c120aa807500000c10403000b0840490100182482c1540b02800e20351400b04006681071648680140030000c2c00c00d00103506803410000e1803e9250014401d5480380e0b12040d0041c40e550003150115001c908080c0001182d04211100798141d035401410440e0280b003420480880c40c050910984040c40303035902006941100200601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 475338606 1250 475337356 475337377
    0x180c040b0301092a05030604030e1c0606290403020102060f0a180804060f030b0a180f0e0c011202070309030b040614040602090a0608010803040b0a02120a021c031a150f 74
    0x490b91390f840031007203000c1ca5a01203406a0403038030402c00003d902c00704100c2101c50894205101c0b41600b816102480110758004000d146410300c0407640b49828a046c5000d1580c0d0001141b0a4656806010440c040c43c40000d025921a4001c40c000c0c42500419503400343c0c0b5014000f607208861080403105555030142580c0c42c5100090034448903900080c003020b004643d042c284501c0c0b0002c00400c441c0c0d2106d2040341d50140000c10350304020f0b0310503008401401c0d10a4414020005d90503444c544407840e128082d130104440c00d80a039034001c0b00f0f0003074540c0b8070b4068460b4008070385961913a010300000100101d9000d42c0d030343c00541500218140242c000c3d07000d0440161208840b070144074241490f42c0040c01842440ca00400c4032070000402ca8007503541070561142c880422030001d0b0b01d4413030281c40b180050b000c00b2070518440f40d0f0001d040300c038000e903225101c05821f0301e45406800300d80000091142c0c56000b51000c18150510032109100704103603d031007515006c004240c0441c143c01488480 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 475339856 1250 475338606 475338653
    0x53004030c0509060603060d03030b01020c190509012408150d050a0605130206040909020109050d0b0f0a0212070f0e0d0b010312020304211127180c040b030109 70
    0x180168280101075681c030000c290f4456255047c4100050404a0581070040800d620790400c1d00740b9074401d03c04810783d02d5019140003010f507040006403a88140270701410b401070152800005143e18100d00c0b6501d48240004084240e4441140c1101da0000040071240000d00e4840d41c0c04140d00c0300c0c0504102280198003034138416000c4c2c5046d40a03120b0162500d004a5500344e000000340c1d5491080700c00301d98000000082a450328030040c1c3d10700701154030069200c81200030120500414080e1240300340c19051706111036036609c6104034220b001d2500010340d8942c803100060445401071004402440b240d080905460200f0310028800300fa00b64412038400c48180010010030000c0000858006850f0020707500301810034403c007010788182c0f4050714a82050540007401c1c01007144071580703003201c040c10301000d10107007403220f09a050a82d18442514803001c0c0000300c800604ca843c000801c85e8801c082c000050581040202409098108652555880c0304440c005405007601c50521001903089 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 475341106 1250 475339856 475339859
    0x20d03080a0c051905181206070e030102030f0112140d11011a0108071202090414091509060106050c0f0102030702011b0302040e0f0a021b0c100c053004030c 69
    0x4210640c1d07180315440b42402001e000f00c0c0c1c00301804600b98082010720349401511000d0b0410100e102080300d0030a0758101808100000c0d03100004030794a07200721031541310555503c00700c100b071600300d1004071680c4507510000801445409807031250f074503600c4e0003a1726103c0440c3c1c407441d616081c000c0100e405408540b04141c24018090207024034a0200643d949004110305c9440020300034a134010030400400140e0050051401075581c191504100080c1c41080b034443c0f0680a0b04129400342c4400d801407050401c2810b00403481e02c05984074610000140802d039181c01c500345c0c2e03d030300441c0303107020079000d550302c01e848070315003440a188103001c1a80003213940f00c9841c1c6002d013554034400b000070401d8010041480f44540182180d40c200742410041c00450360394019010080c002e214000c0640340d0800d82c0c0c1045c005d4005499000b505e0212100c040404094a050b0790201503440001c00c0354001c800c0c2e12044124030161503222100c00b0b030000e43c10303d040403030500030b652117a0812100d2505d0300c0070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 475342356 1250 475341106 475341121
    0x1c1e0302161b080d110c0603090304030c0308070308010929010509090f010e0c0301060906050d1113050910051c0c030b161b0f0615090207050304090c0203030c03070813020d0308 78
    0x1d410701301540782042c1d40d10301d002d151900d40340c1c8584480b4601422000011400020301081198000c40c1c005131548001d58480c0340c20307070450703104210940000703516100100b1b4801c094814880741044075448000d000003007007140c4000c5445020510305111060286090649840d40c880e4440c01c10012882c1441d81050313903114030350501500c1c80680d00010300c01030200b90f0300190500251062130901540790258801d0507405041c8102d5130441021000c00c1c0148218600c070008000d40c0c5044940d80350300c6d0340c4d006045500c1305540c03207002c0e8481c401e00322101c42240600303140d2136103a0003904003000094803501c400d000c40005492a000b0f4012541e05803003440d5200741c50400050605944020081c0e2680700c071703482080e5040001d00103954031011000000400c01c41c44008042c0000c00755141c1842e406d0903034683e0403a2140308009418090340c18a000e101100312481201c070032613642d042d0344481c1000c580c0c0c90002054000a51000c1e4400ca016994000c0b4400c070712446030f580c40c0044d240c26407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 475343606 1250 475342356 475342363
    0x140d080115020d3c0c0303060b1e070614090a0506070206040b0a0c030b09090a0302070906050a0b0307020a05011d0d020a030203032e03051c1e0302161b08 68
    0x3072810086401c1681c01d511020f0380b044004d9208000c1d2a0101040c0c0f5004042c40040706003184001c65a9004500000301603402c820004c0c2c0950194404000302a6681007024151241d03400c000c00c0b032800b0104c1c000c04c22402d40013620881b406a40c0009804030500c0400600b0081030f02d003520254440803056040100401c00240d11072260f1020f0a0642003640c0c401c0044500a004a40c030302d074581802c840721a01c25400401ca460005100061b1814449103441d2140f100c400d0507001130141503008030f107016050056008489024102d440311131301d0022050440e41029003a50114040c40030340b1400b00c0c109000e231810700555942001b08100203400124948418a504101590032119601000c0f94010042d664803210444601e080c8400510b1103403100f000d5400340c3c4210100110011041c0540002c0c00c0280c0c0380c4118400c1038202c0059400d0302c02d62001d02a40c5d030004040c4050b500224441d4003e88516002c803c0070b420201280e6842c1841c5880c1c41d50340d030400f210880c03070402c003c16003007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 475344856 1250 475343606 475343639
    0x9051e010204060806040903030b090117010e030c0606060f0f04090b0a140121140a05070215090c1512040f030806060c030d0b0f150a090b04051309140d0801 69
    0x4008502e0540741c9003010f0070142004003518440c40e0380e001008140b60281d00b1480c1d14050043c81503440b9030316000c0800682c0a020703000e100c80e41c42c0c82c64400c80c04000008a405034050b020042626a548400304801d0b90700440e10800c5140c410300a6003880001c81d0090005000c49071800b10f20302c0c0d940c1c02440890b40311303580455590100c10802000303a0742c1140e820003140c9001112080000d82c1602e10f0700c00340c1040030705190a0351940b801c0001c0c2041b03a80c0100d0103a40503070700f520121403826049071420007040e0b03401d021603005200b034800a0318103034009152801c148003100782000038540104910090444003a90210803441c1d00b6020141c1c003028481d40468201ca174030f810a50300c60b003000e0780c0f4000e203140c1010351603a40b4900c1101c9e5584150b03003451301000912208010282c482083c0f40d5400404c956404580c20142c041203201c3c0d907006607402d54801a04c03414401c80c69500072400f41c07500903405d6030b00d000281000b01c52080184162200d9108546488105500d80564103203007000c3d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 475346106 1250 475344856 475344913
    0x1e031c06060e0103110d510323011503080a180f14060f0307120c090303080c0d0f0f06260a0201050a020f060106110609070b0f0d09060905 61
    0x8007058500d4001c454400d840c1a10500c901c0000d80c0082040601865044015107d4102c2c50708080151069140c01d078041c031907403c3c1c1c1007003c1d07804451414a8075801d103a020080801c0e401107800039020149800f0142036004a10000c242060410700088070701090350401e031040c14000600324452500700110710488911810300c8042d05181c4100c0d4a60b920141c022400303180c42000382c2024503519001509e00c00d0415035600c40e902e091000010f0405041100d01e040c619007412600035a840c0140300d220200d07509074880444a0b5100c04825146a022030070f002c507820781d128140722044105102d24481c030400e8070800500c8600b010712030407090500728500031604440486111604a02003030306002d055081c00c0c1242c41d2001c2c10700c103034140078084142c882540708010000032450751010301924602c0e00301007659a01e032501450a0b40b200b10034040c80e01c40d400e04001601e140c140d007a00905061243e8207001603a241e0950310002522803007002564543d1202c00e501005000c8001102c0d44040e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 475347356 1250 475346106 475346111
    0x503010e0c061603030b1c0203100b0d02100c1b0603060b04031532010e0718050126091501080a03090303081b070c08060a0e1e031c06060e0103 63
    0x1490030010b003851242800112000070f40d540d1480800d8003d400000ca0b00b400100112000c0c403890b0400000b00d0300c1810240d20900c45c61590707580e51042440741c2c51420394003034844400442c86409100071118504006800c100300b81444101155074041122210780090700c0400c4900e1401c58000c0030385e0305540041119501c100410800a4103299840c50074140c00400803410804542d41540303202940c000140704800495039080c0c1031180ca0041506031030705894254100e44031004215101001c1c942c0410890200a1041c0903560084400541c0e6800c203000e880d14000a001d0000412003003a5640d100f0b581c031008440c1581520b40c1e54040c00740518100604460045440080140d60503101c00ba081c8249000420070305000c0c6c560b4001c4642074005203503500c00040c6400340c00c100e158450041d490040b4804243c580916005070002070341e04d000101080720061500e040b1510444191101a100802031010407001c03202009442c01c1e101d5a001402030714040026002c070802c0304050b0304062 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 475348606 1250 475347356 475347373
    0x9150d1a22110405060304030f090e1e0a110f04030605010e06090c090102070b0c031801031104270c020601060f03090b22020310020403030e0406053111040503010e 72
    0x1e15080c502501d91996a001c00c51070681038144005110395040240c0107000003040006242e040044411900007599416030316598541a000d8808016a203c0b40c046007030068010341660108066078021f40c6885000450081901c111903c0780d1100100484001002c0360800904c03445100705401042100003c4109252940008001c0078004055003000c43d070206a804030359108202c0e81e000b074555604015664403d9040d840c3d900d8000a81804244000b842c039105254400e00036204d0b1391100d0a1158201820a002c84090030f10401c0c150f580440c4405c08521400340034081c8440480c0244c002e0040c550500ca002444589450100700505080008403030006004002c1c2030761041344810b8a622001018840103c4001ca000e00030754144110100303078a109009174010070031070380700e612079003c0e0f01200c5080c042590200d10420703602104210301c41c0d500b0130b1650003000760000c4200f05480031404200b90481107660741000b00a0450f40400c05220604092041e0901002490300500b40f0a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 475349856 1250 475348606 475348639
    0x220b041a0703020718020d0b010207030203120705150f09190807031b150204081e0a0803040305070507080741031002030108010c030c0f090b09150d1a 66
    0x904803802184280100001d0140a1610901c11803000e425001c0b02145090b482003410b10280d048404c5e4151920304d00900050258000111181184e034080c0140139440512528498503400c1b00b0000d07542c50140c514078042428410301624420b40c0e1148a8030503038141860306521300ba5180680d10f59a06c2030081500100b4501015115220b615150007201c1841c0b000c0c1740d20f20b000310844000d024001d000d40103080301d410b03600a8000e0381d520348100c070014a0a075401414900503080c041645030420781202003c26140700042d68401e00a080081c0741a0703250741d03902c4c90402554095010307074101c1c030382c2405841c1e8a1840e15605402c40e0b0318007075800d0380b951107865001d212400750203c0802a03410400c41c940b003e000950005100c024215160f6954101e2140a0720390ba1042c01c0c00240344c21000c40a0900410048126a43c0760350356540e0681000003980140c2e03c0845079546c400140c4906400030705550000300340100107140d02051401000e40200e040301c0000141b80d120b0521010b40d2200b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 475351106 1250 475349856 475349879
    0x10b0102190b0a020408030304060e0d0504060921021201051605252d050c190e04030905090a02070c0509130b041a0103030c0b01090203010b0315010311220b04 70
    0x3050300000e50002c151540e184080081c07081c2c0e03002d48076900001c0104410b004943e070040e010001503200781c0d9500350040404594520590007040c02003180800140400c56443d0844040e801e4034001d09001461107400080c1d481c0000245030046070b4507041080390540c2c3c403842d000d80155180c2407140c02c1805141410000740d401e800c2c0404075007005075052081c481c00411a5421006602c41054090881000f28903030b01001e140590751441030240303a4a680c140060040e100c3d0b03080e01841140c180c00c0060754421a40d020b48183e08000c0952170100e5503550342d4048900540110400590b0f56449240800962800b90300c1144108181410091802c03582d803043d2103500d50140090782c140c0d07224544100c0180d4488910780d614141400080105600b0108040c1200d0180e07480c0e0358203a1f40ca641d00c030141e21090040c5800984c0c01c2c0f01068108100c14080b40440c0c0b814180850b480010301100b1025410004001040c2011a0400b40c1d5109980305160041e240083d01c0c2e6103410305000da1042c1c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 475352356 1250 475351106 475351153
    0x10f0f1d07020a170d14040f0209040f061407020c1503010522091103100917090303120a2007121413150801082e110d020c010b0102 58
    0x21503015040028031034038428000302c08400d0b8000160801c1401103602d40880d82c0100b00c2c001d101d1841c20f840c0d6228506020401403203158171a000b1a8180b50036400e0010095001d8404c5440e403401c407000d403001a10b280146c00314407500b00800500ba02e80528000d28040d0310a010074000d1000a030740000803017038030007100d054601c10b5490b40650841c03080070800406001002c0a010b5140900b88020410644480903210030100c4c2101c594004080f0030b01c040b5860841c0050840659000203900c1d110b4000c040c01030002c0003403c0c0c0e41003031007126081020710030890380141115903800c1495a040002500901c07245ca0292510742440f1042c1c5d201003144003605169400d01c03442d810680301117400c80080b46c54031035200f030b42500d00d00e56640c000d43d41c0e00c19003550900482c41150011401c4500064501c0003c8801c00d81c1c000e029910340d9580490782600100250300305e07140c01b8060f000c2151113005007012490814010b95481e24081303020f0841d080030350a01e045401010028082c0241000c00c286e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 475353606 1250 475352356 475352399
    0x6090d0305130302041a010201061a1801200f120a051c09080a0c060f020c0c010e03070f03140d090803040b09180c130608091e010905070e010f0f 64
    0x2079560078140c904402c96412035000a50141c00c100c080a25041c40c00e941e444500002c0e0020b00115803200e2505c1e40070b201071a40309034142c000b0300040c498032815021244281e50103051002ca420741040d02c030b0340d404560a07000a0070751b028640844d41d11008008640d004121000c8880c244040b661004106200b407184c1400d080d1081403403000040d4050340248146039220702205c0e40c8603020400036011007403400e400e03901103290401d9424078407854000c480103802c00034007405031030f40382c900155025840f2546a075010700ca0604085103803416501c654024601501400c0700220348062068604186c9007001070401188102c01c104001c0008103039000e0320808240703035445410010103d012000b40c40c0c0454868141c3c401802160307803142e001407044801e0040e004a841d07032254003c0d1172400b010388e2100503503841440030038600c02c00000c1d00d012501d918800401c0b0120780d07407605480c0944540000d184815940010040c141c0068a031300018401120307450171091070444176a180b1000842d640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 475354856 1250 475353606 475353617
    0x20a080a0c09110a1808010203100e01051504061d03011107050105090c09010e07030e0319020c03060f06010509040605030735030a121803030c260117030f07080a030b06090d03 77
    0x441000317810301d2131035011b00f003054003c641307915000101140300c07482c6204030049040c52100100301c0e07040480b20403c50303001605040d4079052404c0340499030070f80f840881180f036800340e505101080e0380a004180c120850b506c0c4041d100c0000d400c2c001d0860714042c0c1010f8050340409040401900d40100040c1151a09900050695140307081078001c1c201004000900d4040020100c11848204144a9812a150b801c82d003800d0501020f141c1e4514056035803a035190000c0b4002a1039612a00040c40c4900001d00007207034150795140440c0c9089220303042180001410300b0b102031010015103c043d40d601c4c144901c2d04c00c02a58560b40c607168801c00111000700300d4240003060004910350800f00d100820104218156006410000d00401158802c400000d00c10b00b20415103501d92801d0b04242c000c02c07038002d80564138004440380303015000d022202850005000d101c018400c440701503e1500d020f46a00d0340d480c04981c0e0005c1c1141c1c2070500f0b03148110818000e100f125115001c04042c441d9243c00c20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 475356106 1250 475354856 475354877
    0x130803040201181e150e09070c020d060209012a08070f0203060f090d0525050a021804151a21070801140603030c1207020607020a080a0c09110a 63
    0x129501104403420040a0000e4000003a01c003d4600f664060101c22000c070383d604507118207841054105c2000200000ba14505900c1100c3c5071030240c81760051258240032003d14602c4e40400c44854070034805444007940440c16010b1540c20400c14007003002c070b070f0001c080c80c0f901c0d075010308488402c00d20010384460804502070007003010045603030090a40080c12901c0610f44107000b801c42450844d40200d5601584046209250064080d1000c40c150f40448220010004000e1440301c03103002005d40d054840c0b1046c90015865039000007203d000e00100d4a48035282034282803188081600060710007070701d0221180d1104480c1031040e4030046c1c080310040341c01003064245d03919001c64008000e010340500d1000043c0902d0540c0500381c90a100040300d0b04035602d04041648a000d91450701c0102e8016200c070750440903106004004c0244020081340c00c1c20500d1300824140c101d01d0b081394601c0e074041903000052042c4403686400400001001b0300c0b06062400e1218010b00603e901c14082c020345985 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 475357356 1250 475356106 475356109
    0x21b010315090b040b03071401050d020409110d060501140f03180d0e040e0f070501080c120703061e050f060a1707021e0607022805011401050411031308030402 70
    0x21101407250350404000410303444180d0302000745469040107103d185452000c88107800c0c0412144200ca00e00c0e030820401010031401960b40741d05c1032080a040946c20440031400700e03911300c20380808144c5817102544071a03625042c0012543c040e000ba5040c0444100320409a413450412034524603101c011a503107a03191303907486810700c182100d481c0303001c0c0c0540c080c2c000425510080790450b60303a0480f801d104030031807103038100c0d1078a25800c0c010415400084d01031089501500040703401040e000c0480c1e20340308240580940140e070039950000040e0b2070300c10402c0155505509403860054002a00091030b00d400700050514506194140c0542e2012844001d4903005160a503004410030140203813915203110300035201c001c00f621f416828282145420004000040c003a4414941ca400038145200e140c5007120040c80003845020250346210300038000602d0070f010700781c214140840c10144550400c0100801c2d903034038030000340e800c560600c10460401c0001000c0b18004d50480c2c28039981c4d4a0301d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 475358606 1250 475357356 475357361
    0xc031803031207120b06040b0304060c020a06090b07110c030a030e06070b0c280c030320070b160c0302030f0c03130b03040203010f090f02040b0a0503120301090506030d021b0103 78
    0x110310400d0030030a5020003020b0743d00428031849180303616500b00171640800c01009084e010394025a082450706100080014100e540684900303480b07070044408030740300c03640c2d00341c2a10213503002100c86000f5402404502a0407404e4600302c034050030042d220300ca0000c00401d0740c9015400c0050b0802466184c3d071055a124502150710b00f40e00542c6000203440c05050200c2c0f698020510480c0c50017800481c2c0e10548050403100c0009031035982c401541c1101524110098414028101008800740d0b0b04015109040002004054400d1512403881e1501c0f485440e061707071800120b10705000c0c0481007000000d5020007201e81c0c4d501c00e405071a440340c441d0000c44d459402102ea000504005400010815080aa018510035482200203204524800d00c4500a86041c080014210104218150018038050300b104051b054064a0005840d944100080c5404100c00507840940000401444006124040c0719488041a00141700f08048110005c0d501c419481207244224520002c0c01210b0780b1a8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 475359712 1106 475358606 475358617
    0x5010303120b0604050d0b0603010507020607171e18070918150b030303150f030307052508070b0306030d030b1c060f06090501031401020c03180303 65
    0x1c000018002c68624594484024400032455454201d10090b000d8010424002c150401209250031903101400034404c41d080182003282490b0070207400765448402444104140e9601604410210f4120b07003040c0c60b09400406101028402d462040e44461000c41915003496454042c0c40441e00c92405080c0012008400200441c480750b1000e01840c40c03100c1c000c1400146a00060308580c42100c0001c0000d4070b101600800b0f007007221481100e4002640114644501503d40d150b0b94100082e0342c0e100301102c4206046510841d0341050010184039040b2110280c45014902c1103030001c4420900a2080c0da0326901414400d0044000a0304c0180c0b800c0b140b05c0040c1c11070060320340c0d44207040d00c0f210f444a180c0744044116104640003454203007030008065056180540c11821101c08040c00303a80103000d02c004410ac0407040b103a40900c00180c011443d0400000300b401c0d400394 = true := by decide +kernel

theorem cover : BRFrame.Cov 475179856 475359712 := by
  have h0 := BRFrame.cov_init 475179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 475179856 ≤ n) (h2 : n < 475359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
