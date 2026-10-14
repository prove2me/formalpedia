-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2058
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:33:45.447175+00:00
-- url     : https://prove2.me/submissions/273a0ab5-bfb0-426d-91f1-aee5d3721321

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 369964028 ≤ n < 370143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 369965278 1250 369964028 369964037
    0x901030f080711040f020304060b01021b062a010c0f050f091012090606060905061204112b0c050103020915180607060e0607081009020906040e070810050307030213020a 74
    0x83c620045425600405408280540d01100300004d0061501800e0340c454000d00c081c00785c4d124181c5889420119003e4040d0080c1300c0403450300340c190400076100303a0b60304114102d142200d9030003550502810301c11021000146024032844803c0e8010419145c81605040f03c203070404000d81c084c4654504408555000c00c000d142d0b035040030072280d114000050b40101c40100c0c0312410114060f25011841e813085008000800102180360186180982c101d075104e0b15031803051075480c001400d42207032010b400003800b005001c580326011018140c651210312a43d040e040d01540c0d00c00540490065980076504000245105628130480b1402051892035854006000d00891004981140c01500044a41039600c14082c0c4c0340900410607140d010b10742d4170307000e079582ca089030003564046210320448440a40100f4200c45560380c00e01900e01034291000307542218030300803600920100041d03906800c501c80f44a00440c45040c04200703402174a8001d071185000451500e070f41c40081d40072100013810803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 369966528 1250 369965278 369965303
    0x516240512130b01060207030809040b030c0907120506010c0203150910020c101802010203251203140106052506060503070605031e010302100c0c030813030606050901030f0807 77
    0x580720031040d00e0041c0d0890700e60301080040ea00c0e206008400c1038100205552103040e042001407080700c21220000701c00e41d400310714080d50034040391030102e44050304d903404200344040007807075540660100500d2038411002e00c1184c0300c66006490958004101035016089000c184122030b0a182c0b207603400c13a2240c030840d07440c401d049100e00200d030002100044140c000403e1038588451034003815604891a440800d4507003450350020b55203100d08042002001c0c6529000442400c7c00240c0312540f0b500a292882d100102000050041400f95012000c0b1094076001203a101d1007141640c03000d61020030b1107180d03c41800300e822104849503204a400b80d80b1548045040c0d10240900c40052410b505d800c2d8403130a0030b483c0d1603030180000c401b07805400041001040580d8070070244039299034031800c1c00d0208815070b003014074000c0d4403504041c01c51400090700c10407026000c2844021a0b010301000c002a44c0c44804000d0a89001c0c48081c1038104e003e1555004201c2c0a801400194401d1002d00002c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 369967778 1250 369966528 369966547
    0xb0a0905040f0c090803091810050603040f141507030218060a02030301050117193318060f050603090312010b0406110c210a0f050a05162405 62
    0x5403401c00c0800b1900584400100c005070b0b8214040c50094445100514108000903002c00c840c5050b06a81c01c1d080b82060010a0b40b5421003860724001d050050046c075902d1820f070070030301c103e000581d001f2540c0f0301c401030354507500d0000807078541000c102c1035070781c80c03142d448201003103003c0d400c403006c20245000b0390081140d06603a95001051100c1d81c036000340d03841e0742c50440007528507918404800d004103203031400c2064421070706810407a44001c0260001303421014440000d8121114002d40c40a05a0070207400c1c0c400809038040d100711030150840303000d132100900c0140c080d503e151151075800c554900c01071180b49459406154481d60604c00c89040c480c20b101d03a04240300c3c0a902100b543d46c000202030108990000322014030041d400020005100200c0c081888207400d0850241400c0410740c038207980c1d500601c0464015904a04240b49001d05414200d403107402c80017045070140310300f0151503031036190103c10f101101c13088484015004034541e24200e0401c80d10040d00c003000000c1060800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 369969028 1250 369967778 369967781
    0xc24030124020309210f07121b0b071709040203040b0411060c0615060f03070305240904110a080307111801030c0b07020103091e030906110a080903120406020f10150b0a090504 77
    0x103050747c40258804403841e0900405070003a08800d411a034468271000e121442550080310b0600750300c180ca1000042c0c84640e0103d5600990700b48591190001040c4014401c2102c616401a03004034025008111031000b0000c29100c1c0645541040e0802c40020310b4410059858040603800176080d40d26046100c001c1d074089900840e140341c013003607542c070a000c50324002c130100890603141e0014030b5461441d404001b544c0c450000b48000e0070719411408803845511920105c4c130003003812004694a42545103001c01084103400c454a010b00207072b020308044280d440807400d040b290444048000541885080022603011210590600d6100d22070703100081d8072582c40d944040c9180c0051050700900e0b2030024109200c55210004004504203020314411002c91300c008402c0c0c3c0540120f554000000200c0e04200c0c1080325179070350700404180021025000300d10501c0002e00c0a05031090070010800140403140d10a03e4480c06088031401480020701c100001e00b03c0c1185800c0c800381c0c40d90359000140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 369970278 1250 369969028 369969043
    0xf06070930050f0d050424020a08040f0e0f0c040510180303030b0906120316060b030601060806090112050316030215090c1206090c24030124020309210f 67
    0x2150b5501180340d50046180c1030048299260951500301c6c03800c3e03d02400010890401d900c501c000301c40802d0081d40c0706000304402801182e2100e00c00b5196591000010001d5903107100728a004803442002945000e034072043d040c4030f9822908502e0401d4202014031040c403c511325170030700b40003130a40250040300036101c0038401144a907802250304d202034000d001c0c01c0c40b0040c1209000d40308070b0f4a0b00141b4880030081e50310703031500c5250031507045107981010406001c5804545070103020740c10000c100c00d50706c030000f44e00c035050513119102079981c0c03045945401080a0b401400c503800c00d00030010903040b031141510b02e00d806441149c20200050041007020380d01561520368541c050800c10645c4d09190f00844d80c880e038000060600d5190416409480311500c1440600c5100704200074201c1c8a54200d800d6810880401d0349a101d60b1030704c88140c404500400000c0c0e8240342c0140002c00c06100004403001210042c2980380100b00c880c00e1740d01c0c2c0615028011701d6a00400c41030a821802c104241c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 369971528 1250 369970278 369970283
    0x305012d030b13060b0402031303030b131103071e0c031211280525051e0303010303030605040c1b02040609090615051f110304050d0501020702030f06070930 69
    0x40f808021629200c030845155802c018040c5005000304020390f038241d03403030040312501401c0201c2c544031200300103020b6020014000341c0700c52820707044070403020805c40030b10300c211815118004c06561800000303040401d442080c800203918170040c000000c1c426000902c4c010180c400104209401202c0d02080d41c11140850380d02c00e501074000e00e00141141d40080403203109003051454040321003c0440101c02d151100d0141c0020503050504205041102440b0000402c58240105690501885d02c0f50300a20040e00000d0030004007040c1c61a0601c200650f114403030302c82400202040000424040c01110140c0e40075079280c800103445c0740c1c940542c1d072065215250008600411940b05505811030b50000c0d4003d034284282150b814241d410380c1400ca40c25810244006814444940d01e580310b00e810803a00882d40d44503403020080150050304900b40f0071801d84010f1600d52007180e507151400c4650b0340018401e03040030800300b82100300d980c510305081541402076801038101d0b80701c07070000715404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 369972778 1250 369971528 369971551
    0x90a090203090c0a05060901030207151d0c01031e0504050109150906050109020403020d031422030b0a0c0801120201050d022101060806100e01030b150a030b010305012d030b 76
    0x20400b0480090001151411048406500c52030402020030f015010f040f00c0c0030f05140c3d0011f90141800045454101e03441e1450006100c800040703142007014008144c00c0950b90f00c80e907074002c00070358028012010030f103003005800c0c042c3c240c0b694419030107840041c1045d515950303204070403c040b960b001c0e50101c6000c4801c1002c98007507990328240f421208140d00402d942d0b403040c4401c2c001642d60b9401665459058a07241d1071000081e40c094000e413141002c0640d03580c091100390711000c2d10006001c000ca17400b4414008843c1d80e608418010f903860075203c0e10000700484014098803d0402a0240150040c90440d06083c82820207004aa001100d00f040d0a00084000c040c0c4a031112481d5000d00010316015080d400c00c0800304030054104000c0b1401d0000310f503c040c6099200f9408840c584030000c2508001301d02c580c00301101948520203e000103410682180003035402401440c1c105c03150b1018036020002d1200310114006107000440d0781d40c409a070340c0000482e0741600b800c0c2c001c0c5158500d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 369974028 1250 369972778 369972781
    0xf140102030612010b030303060405042904030e03010e0d0f0908010204080c0a0f0602120304150207061a01030603110d0302210d05070c0818031c20060c030c0f090a090203 75
    0x4000f24800340300c9038600c26a06001016060352408810742c0e4101c1c8003035030041791a40f40c1d840c14098080504901803407150680502c8042c051440f0701c000d01031070103900c80070b0345e20500781c092600760b5072680207148032680044580065a84500500d210150542ca050016582c4400e8102d00366031060303021060552115980c1171851424074989001044104000303034007140f0301040651201c8a400407485408004000502031080359810b410ba0f80b9030b00e102c219500c20240c503081d8010402d010102403e04000143e500240d400b03807090109882d00702107146840c0140a040060900c1c00190440450154600300354440641e092064240140c4070241d40c0c030344070007251000c1140c00c010180010061b043d07400c1400310b8503400840b4030f1610110340403004071301c41402007442c00303483c440500000d0f24255925244c0781e03404031030482e0f8185552040b1289085c0d00c0c80b003a6590f441510104000d1b04c041000c56943c40103e030007000408141c030700c450300308800a4002091700e00075500200a4640000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 369975278 1250 369974028 369974041
    0xf190305070e0a0c02070603050a02040315090b0108030c030706020702281a040b1b2e0525050c010b06070807151104060e0f0607050c01200604020d0f14010203 70
    0x50b0990224a483c401c00030303491504002035540d40188549424969141c0105d031aa040360b40441c0c02454101201c808441403200754a0010001050141c82d002c43c0f4900100d850000803049841d51000c0b64001d504000c50784c4c0fa100d0003540907910807603020420305540780b8a0321079803113200743c1c41e41248170204640d03151802c102500400c2802c1c1402c0b0f424204010f0100c1c3c0100c509480400d249003040b0700850f019008850f244c60060b2125490790a0030344000e90b0300c0300d0100700c0d0005540aa8005020a458000d0b001041150340c1c0c801c0a02d15290703410a03008a88660054140e0301c454400200d005140c034804920103501144069500c0d40e00050850309010000700c0411020311301075410400c0200d4080a0030090265019110811000c2054003d842c2d4035040c01d0180c1c2301005240c150385110914006680d140b01084150103c0c43d0100503410595204c4036004a1405030405000307280d541303a007001a0f070f00586500301d8218009400c03d030082510041100314040d03100000590f82d04203d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 369976528 1250 369975278 369975299
    0x10b0a0e090a091703280e060907090f1a04020c031902060f0105010c03170a0e10061a03071b020a03051510050627060f0c010207031701050f0f19030507 67
    0x10a0710341c040701001409501b9214a10984152448810312078100c070080010001030480b5404c1d002061290200780030843c0c03c0402d04808031000c40c00200034840140c4104810780300c1183e0401d022107c003660400312402c09800524404104500781c0e803901d094804080c2c140c444138038001300181d00160402c030841d582c50030700c1405440c09090040078140956001004903000c0071240c523010310071a011481c041c2c1c2c079402040303901d540706d07055640c0c60151554140090600784280100c02424200b200313025400c0408603400360f2074035074540c1c204850351405060131040c5600c01b00d0704401b0182000000c04c209101d440c641c1c0caa04805e0b400c0740d040c80e40740040b908d1143d4107d90312802c0100201d66940c1041c108a500807a000c4801c0300c21a16540002a0789001c0c0a201b40300c49031000400720494001903004140c804c0c4a519505809030f1316150303a40c800f68003405450b4212480c0d0185400901d072040022180102c014a00d44030011f9840b4082c0c1d01248560040300da42d44055014403025015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 369977778 1250 369976528 369976553
    0xc010f0b040603051c18141908030711030c0a03080d0501090c0f0e0a080d050301080601140f04020c010f0608010b0301181a130503040b04060216050108010b0a0e090a09 74
    0x494040c0704190850304d40d00d4450780343c05111905a90701c604000700c214010506916a011b40740c0c00d515071030b50b5801c21040da9094100e1043d10503081002074030314140c82204240c1c140d61001c4000e50601d640d40d0b4441c04010b500b049050f0f410300c500a050380007540e80d10b0046002e144a540710070b4480250011940c150340c01038022590700741c20200456416548245814166000340c038003410003075118004600303d44c8032078101038070314041d0708618a803141c0c000340218100d8442030101c5005030303616204541c40715a1100c003954030104955044803070349070a4000d0b0600d491100000642115040564000c641580d404411a41d4507082d20580c545800c2c440ea04200f0344122400311203295036078681558014170034101924011081c08074074104814451250b4160b80300b070441c0e40e103a07100c0302e200e0301a401c94400c10005204e4000d0014460402c103c6200480d0b606844141c0340385d081041d50751140e004900348100b00b00500b124944075564030b4804500407284003100207038180103410101c900b00b10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 369979028 1250 369977778 369977801
    0x80d05221a1813092604180b0306071e02060f01030609051f06030b01080c010c0314161b061713020409060c020c0a0801140109020c0a05030c010f 64
    0x84020003045a8646025100890100c2181c12a60342c6500d86450310207126903000319070842035620014071511003603807003e22400c0c0254000000740c0340d07072426802103060702c4810945440301480204882c000c403507801e4036282405400411f99103000c0d004a4501a000c581281c009828111910a82101d404420040b1441d900c05804140f4182d20700700c203410818800189100d59540e92003050100078000f42514010154601580c2800200324001815042c0004e842d80340e0440c000040008002400803d1114103031180880c000d460380301513800d404600c1019083c14010400e0000c5001115060304100c0d10641900341908030200015800ca1040e4100c4814009045640d51146940a0140c2d070320004001c0400c2441c1031030320201e0b014140310344000f4111420150401c552075008070b400d400303503001034560060315a500c07040c40703090b10060284400c030540e0010040c40502d240390010b000c40c45000742115940841c1d03a88540c51644007c0c05d102d40d9956035580c82049501c1801003020425 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 369980278 1250 369979028 369979087
    0x708060a0617040210031401031401050a090f12030612030503010f0602061e0a150314011a10030917040b0a030501120803070507020f03010c0309030e0402210a06080d05 74
    0x51840c0d0607480c950b10701400c041d04c0f45003940340840d00c480c4a07070040c03040365034642e44855807540d492410201b616043c2c08103004550270070740041d00410a03803091101e8540c010360825285c64044d02c0e44412200700c202000105a200c40010510b613090201d0454154860760b201540c0b50300d0319400f07000d0f4980582141c42150000002d0201d419180b00380d1600c0308ac03107110f40c0e1385683c031218004001000c013030603a880c00c0d0036110400814440d0f4019241170b541e1284001384030010380b200f51885055000111158000340b02c13000070031300c00d1181e0300080942d8410140c1100381841c0600f00c06080d005503101c000c00c4400000c52405a035854003030716004045603070003a00d40e8406a07407202c074075010081c114810804d009c680c100565031010504003107410080c000f00011030941c24010080c1070944010743c0403a945007801d000c03d00740f070b100711482d00c8005041e1050701c208041d80000392602c090881500c081c0c5448001c2221300090214403032100c082e8440c40d5440440c0311205100100185580c40380d42d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 369981528 1250 369980278 369980297
    0x60f110c150307050d06030f0b060102010c1b080409050a091209050d08030a090f05010506010216030b01150c0501060f0e1602060105011b0803041514010609030305030406060503060708060a06 84
    0x1034588226001001007058005500da60b41c0307070b00c00c5409014201001050a050200000c18030809119602e03c55002c0c51040c006940c0d810300680c00c0c1c0b04052010000258001452480c9070303102500c0b5042188904002840e041d40d030341246041e00c000703440e8010120790780c81e8210200541003404046640403410403508041ca004001070400001c0c08002d051010700000044114580ea0b00070895103921119241181460f82003950003400100c44090141c410385c2e41032901482c00c0b07640d1340100c0303901c88440b100316030801c1503031580300c2c9042202005100101041c000041c400303004030750207000e05680243d6013500c2d101907098040d0002d010b41403075081c811035141d8069404120b07141950028284030072821504c011500403030421003009004100f0110620081041041c4001800c002441e400e212050341100034001090081c03040f00c0200780a0721040000078001e0002c0c69206010b48400a0800d5a60f07022a040150449000b0300240443c0100450b9182c2900e030000604a00d10303140182 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 369982778 1250 369981528 369981553
    0xa060e06031b1c05060405010f0606020109020d02060904181b09020a05071b050307230102010b06070b0402040b1c02150c070e4318050906031006060f11 67
    0x5001e1a150b0039016141c2e03260245001032148061140b003e80c01011202149068200300e402400c0f1103402800d1107080c0200040d11030320502401c40300540083c0500442c40ca10340c04c100582c0d0080076440d421603100d1483d0125554020704d0340042e540076040380e01000902c1c02c400e02e0550029040407068a2040c000c1803005580181614403032907100468081c0c002404042c8000e00200761300056040c840d246c0046014840707007107030b6110f18441500786c4501c184083c00580c261000c00c440d59030069410b00c156004a408441c0711600940003810005e03503040c01e04042540e61040055207441a0324000c43c4c00300311f041c0300c10306490050f06001c106003000c544403111a00e844441c4141314080fa84a001b003040c021440c91848105580600c8052142c2100b000304032489200307031100104550600c9a841249010300105070f0070200d840110304005041408010701701d0b4025007070b9030b00740c4110f040d000e25540f00d600c07500d40504001d41310602c044003640781c0241107080c0b43c01111200d4122040742d020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 369984028 1250 369982778 369982813
    0x1809020c160902030f0109092406090509030c2d0a0b1504141302060f030a061e0e0a020c0c09090c04060902070512031e0408130608060d02040b0102010b090a060e0603 73
    0x10b5410b100d20114548d40d16040c41d8065910107104414120781c54603000050f01e0042e48280c08440390040280b0203541c404115507164025540c88444e40e42284800c240f0464440481020552400d4810754890000b241540d02e40b14600c10121100a0a00d00744245880d4581840b81c02d41c0301168140442c0ea001e0f210f031218084054980b1840100c4906000d04660f03034a000e5644c507164881d40e2030703280c1c40e0038203d07d4040d004620802c094044508440000c101c0001c4d006c20580ba542c180300304035911a142c1c1c80303000303520800d0411014011082c00c0e42081d0360341081b070b502038001480101001c4c2d59040400c402c54a9503400b0b1400c00384100201000584045218065240070300c402c0c0c0c1c0c41c0e58469070501d610020000c258208004d46108100411107650702a2000d900c10900c880c1c2d403141c03640c8044d5813030401a0790b8580e1080c980607051005140c25008603400301d0062002003108803c40003c00e6100c001500d1188000b81c5481081c050120141580366204108400811118130304500111 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 369985278 1250 369984028 369984031
    0xc0f010615032a08182b210b040501050303030c070b060d0609031d041802060f12040605010305150405150603031306120b1c03080907121101021507050a1809020c160902030f 76
    0x5804c40310352608014441c2c041c0503074034000400d10000587d61481c1d10540d2005003030081400380b02d03d00c0c1c200041038a040000a80e0305c2404802c41c0c503450480c09031602078580b18003d20195008030180e1410000400c0f5007c0e107145648a1b4940c290b0203090304500038000560700c3c0c1c0840c0102d14269002e40c42840c0f80a500940f145c05486440e550010b030ba4a60816102d040c0358401440b44810a200030004140e004c94101c038000d000f03544404211491a0016400668016046601c0030500266107007000d109950031100043c01c403442e049580604941c0c40096901c42e03004994049200c003105c1c0042c2c050b41040d00c1080b9000340c0300006000065605284444001c3c041240c0e00c80001d46441c810840b82e07000d411501c17010029031825185c4151003a030700010040c014003070161050810f61001450501580346c0d912100d0400d111510704642070351000f6078041c02d070b0481c0c410010340c1650718030007040700840900c081d00442403c02d10035118581564442ca9130184100100018195042e8146 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 369986528 1250 369985278 369985333
    0x307031b09170307020a080604110103091a280c0207090621030507200f1206130602090904050f06010b13050607050a0213020c0f010615032a0818 64
    0x80b00000c95a02031910310b000e000002034015442090110380002c2c00650903108503c00e002c4141c4028900c401141500c0c1c480000401c0040d02c5d80200304c1100d907140c202c607070181e000c000a8410390703540c4199520301c03c0102d01d84810315903070703807417849096030b0600040c0d01a0030042c200744202460480a0031039035611400003111510644c2c2800200341c0b2400440740c520343c202c800d10380c07400e28005d42d44481e00c90b4804560303c2004204440c22540c101103100c600c01298071381c00f800c210303a0f8003940b2a510300b65440c07044071800c0d420000c0c204a980e58103080c6001d54003a100a00810150f641018504941030300714803c1c14005001064800540d043d0804c2506c41c01d07100e44d070312031101d460000d20b84000000025840008407012229001c055400381a05e1152801154201000381280074200d510600400c4a009c40041442c0f04180c00380c0c021036003da0303200100d171402905072184500d190202102450001e20341c48240943c40c100c0ca2205100d102000c00a0941000001c201a0f0038104c5140394 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 369987778 1250 369986528 369986549
    0x24092c100b0102070f06030f0f0c0c0303050c07080705010e121305012006090c030c0402070521040308030406020d060f051003090512040b0903010e0705090c0306040209150307031b09 80
    0x16075030b900c02e00200009000a80e5407010180d01d401000c0d001d40048441d02c0320780d5143c8510040c03200348500505e074045240351140c009401e807903201280a084001d1a0450758030040004e10000b54040c4e0040032264064000094201c0c0001c49840c02c0100c007507809800d039681440100190210100400c003115000d09009000d420200364181c4040307600c036201c0100d0b01482042080d8a100440c08480e91f800880c2680d041001720310401049014000c400780c5103a001e5014403a01c00d00d00b8600c0c240d18064020b005003031954030741d03d05002d13500841d401c5443c1c0d500403a2218190f903080c0110400342400501c070362080c6080030046050080c0b0000103034109034440c403458052002c14001c1c0d880c03842001d5200b80d0340301c0d154480e5a0096004080b024020b600c0c003805151406030104540c0190b61000740149065110305818222640001d080a68045c1c0d00300000601c41c0e58290000452401080003103840c3d2501700c001504035004600040c030920f01d04040004030542c014690070030380d01f00b03011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 369989028 1250 369987778 369987791
    0x5090103150c180e1b0a1d0d050a1511030f0f15120f0708060903040303052506060e100602030307050d180305040f0803070c0924092c10 60
    0x3011144003022404032242c0000700c01022504149010304c452144245106060b10407041092089040c400d0800c1c4000060300d10782c0c01000031501540d501590300b4014101d40c0e0840301502c441d0300b0a40807001c2111692010030304d02e02d0801d40c0e40984001164805801c4d07040d4030308070300c3c00c6040300c1005240d120101c40da103000400c10800c0e05403c02c101e000c060210310381c08102d403d040350360f040503510034903107440f40200010706418001426441410000051400c00c2d155580c00d40c0c00790004954401e106111040c2c07029168810242000030b913000c5d80011071440d192400c200015080a8140071401d4040b400a01070790740c00000b181d0b04061503190182e0340320202e008503401400c0340090300a505180901d44014194410042c02c15924220f00100a280d41c5044007503584c803e01000401d82505128100406190b542c0514902c021042146c0702402c090410442c141c8080d4000c0c1d80003d9440b0360401d2220308002d40074800320041c1c40d15a00813800c920006556070300080d5150341e200d48590 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 369990278 1250 369989028 369989051
    0x30909010b04182705031b060402030703110112050c2a070e1005120d0206070c1a040305190c060605030c01210209090405070e07050a080f060a08030f03060301060509010315 76
    0x903410710103401c0e0f0303800084c1a4a091078410f441c3d80c02182017442c6601e00c0c103c1e00c4554100407484901170783d40100209100ca19654a00d402442154001814003181341041c6100b41d0060041c98810900170807025504e06141100e0061000845c0c01c0c0411203180c203030700c1c1c81600c0f00040c0301402d544051003411090303a44c500300781f103480d845034000d29000650030a006000b400c0010b40c514443e20703580c09582195a40b2101244c1c080f03200c040182c226440c82e4000c4c0070b204c05402c4c0d0507802a000703103002490304540c28804005580c620510000140a599400c001e2040034403600020384000c03000b4000303203009000024800300030401c0b5454201c00c00d0181000320b8541d6411a03040c00740c043d00e006070510705401d100b40c8903c15441282c502021407400299080c2c45401150310422550b216020143c85650842ca07000500600c16a08540035240100b018030f01000549170b4183d0303401680d5620b2902000385401d407200740c1c0c000c0b80500d101000505c001425000901d109440c51040004c0084111 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 369991528 1250 369990278 369990311
    0x4061205091006090b0a0e0402010c060903021e0a02040c03050c0708090d0209041a070503061f03090b0a150807030206040510030b09040803041202060f01050d1401050108030909010b0418 82
    0x2e681110307149191410020301d121640c0c000d0845200c0c12910044041d546c5c100841c01071b81e044034024001440c25003c00002102c80d4420b5200c1c50003881107529103050004203500d407108488071003415510002d00c650031480d2a0260301121000361400748241c1c00c21000000c00b500620700b000340103800108602005464100c5c0c2481e040d90018048840780c00c0500308801c581000c00c4000003020500000102464052030450703005190103001103c0003035201d00c01e1480307a407040d40c0e49410940c030b50f1402804940e03d21102c6015409441d400911404c528600801039034040e8044441a009503c0410261340c07400103440c2115000d440601000070311040407001410a0f821640c1e100c40b048051000380200900034511561107800c00703042825054600b80ea40d48011113920381401c00290042c415400c200e1016040715124110110080c0e82901030103080d10801d0300861080d52001c5441407003440c01c103d481d401010030455032803401e4108008480038120804091060700e0f1542100c0b080d02240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 369992778 1250 369991528 369991543
    0x21f0e06010314011b231c0e0d050c030d02071505071e080618091c0c020108010909022112070b04020a050109060c060506131e0f060e010e0406090b0106030b0310020406120509 77
    0x180c001191300c2c0e0b01f05203000146000f000c400d05030312601805420240c050411147c02e4030f40741e8000d501b41a003410850000c2d5000110403500e507182540d04540118076401841d0249130b541c1c59489034050390400c40d80808038410182003c1041807414080241c466224103d1020710100c12221a9a180000980ba2500402e4019000729a40803940182613011400040041c03003666804203d90b80c40220030103039072110038003952110703810700880d003016021f02140c00040d1144054074031a03054280d00c030315150080740098403801100c504200440c0b5001c00411301070002420b1034540d50b4101100181001101280106529a10408a0f0803559002c03101c04200035402d009014400c1c1403c1003404403c078941d0780810340f80c00c2c4040340021004034015041a50b003c124a01541c3e0f1801c0d00a40340036402500a48480d035441e00c40b4008924210601c3e40640000e48011490341c1c0d115003494075088811005e821441c1c4180024407100d42d21000803103081036154800f003071544074208034a041007070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 369994028 1250 369992778 369992797
    0x307140909160e010306202d2106030303011a1e03190608010614040f020702150a0906020a1208040309082a0f01021f0e06010314011b23 60
    0x1696100028504166100f0b141601d1061078103024140a05e078900e885880c04d480402d0042405008902850700c0d5868000c6404c04c40d100e0561041d0039105c54a0300d01c0c4e02034140442c010155074544000d0003524482544c12010940081d841c40d031400800324402250044101030440001911030801620350210310304154840103455580c1c10b140008404846144569105890070001c000070031040601ca000102c903110154160b0817800301d410000103000c100d40b0110713a40d41c03c0c0074000240e10781c501c800d14030350480700d911035a030000c099000e451106190301c02c400b1940400000340c0003a000c690803c880d40c5c400e05001d030340d5454900d000d455a03510b540000034280305084503030302c402c0001d4000700f4072000944038104506607501c081c0460301c60307007070f8045002d2780c800780c400300345251080a024400d0200180c00070309a47c26802107801c0007000e900985d000c00000502980c00142031140121010032408002e616196041000d403006440c14001181c4917803032031441440b0b120290880d003000c1d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 369995278 1250 369994028 369994063
    0x27050405070f0e01030b10030c0918060e0a0510031112060f0604060b0903060f06120d020d030c0309020a051e030703050d08010b03090303130c050d030f0e0307140909 73
    0xa08010010b29a0815403155400030700c91416101c3c09500a10494a00e550080e0419804040812040d00640311880d5084102300003000d00182d242002e80380490300704140038002c94128034000460040701d90290121085504e881c0a00c10700c242403030038040032282e0091842d051900b864000500803610342544070b00d10b0244100300100480d442d000d552140030204c608204139601c0d4440d5212a0042c1040b00342c240c0d1080002c9500350340079040295010000130050360500c0c00034038105003000700407004000035034400351158840325050f004040300344035186070410022405170005022103200e4854117010720180e00e8641000003032002c5800d040c40016080303c041070703602d19000d0360b5004503030b051000080b1500c1c008620a240107040b42d005042500040d03081d07403104130311020300b103403208021224280280c074002560349542e40000038450190701c44000340452900d0107400488102502442030300021401e01403000d82c1c0c0c2522026601c1500e270f0100c85d40e00e2005007481c00b03154409828000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 369996528 1250 369995278 369995281
    0x23061003111f080402130c02120304050f0a03090602100513020f0118031a130c03142b2a0b0c04050316140913030f020703120c1b0627050405 62
    0xf500326044600582c030913903010000b00150b0f241d00007103640328028540107812021544502e09104070185400c10f009209403000c130b866044160385041820398046021500200c01040341c1a01482424882ca10100301404549801c0c519107000002d40f800080c41341111440554850b441000c00c43c11a42084d01c00900340364030390401d003110013104422302d0070400e40ac000003400d10450400d50609642d06c000250516801c590f1034810740b4400000302a2240728805e4000c1c050901600022480d1000000032402c0c2d22040c10001c0c4040230300c190030782c90041c01c0308840b507113158005402c840c038941003100a01c1686505500b154103224070341c8501d62521409403c04603104c070131210701c02200d602d00b6030b40c0f10003410b0308180401e0352411a1103075002c0801300b92003070101e8056101d0164140341e5106072100306403641d80f2803842c440501d014030f000800c1c08841c0020008020340501c80f003048440030810561802e8030081c0310f07543c083d86a191207158205c8225510355005e2600014090080090026 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 369997778 1250 369996528 369996589
    0x40c0b03070201020405030c0d080f0a12021201050f220f02070819170c27040c0206011401020a0c0504270302150a0510050f0d020d2306100311 63
    0x10350010700031b0f28480e0140f0015080507140142c800800c5682c0074180c2400c11014004003d51500100b0314a801d03ca480407004150000d02c0c4006c0c06036610710205800341d541428180b150765000d01c2109406009400344440f1512080c1a614107104100080032820f450038070840006809400801410b603d000b0600f12004c401d0951403c0860134030340d5030840d014262a8800b40307101000d480841c803000d4204016240c000c01c0074203842d0303070919065195602c0c0c07203d80c020608036009150603900680091005100d800c0228031107e10303542091000701401c9a860300c80c98402c8401e032050a202c1c958802003e455600c060910501c407414282d8415000c41c03490a029480381c40a5490350441c0260703400003001026140b2465000c2c00c00781c40c0c1c5071000d60503e002c3c421404220b4200b545e001c1d602d55510350069071480300e252200e82c49415210a41d00d462451940307590130648034000103401c59010080b074491842c1200c0304803600558902c1e007951028011480b60403808444400d02071816650750074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 369999028 1250 369997778 369997781
    0x120c2702091909020a020f16050d0602070b040c06120b0108150a0f090b030606041404390302100801050d03050f0706050108010e0f03040f0608061804030f08070c0305040905040c0b03070201 83
    0xe003c2c50310380a4500405000140c7ea4540340000040c6103d1030001c0028482401e005545289040c85100c0040c64210641c8401100c030f1021103003256800811034003400495070040002004a04400d02070010300019000a029140010704080019078150700d51980c45d51a031240100400100808003061a210b40001028051f441c2c6880d00038454880400c032503090034400c00348d408000c120418402d44503655000d0306200c00100d81c025208101254050100e540c002c00742c010441c1c1a0441c603c149148144003202000c40d03034450500c004a001040b60780c5490400b16010b9605242c030641d6141110784a00160180f0403021780741a180100100700e4041c1580201801c040f980112030403080600000e66036441039010300400000c1d460382c204680350050f000c69800c084010b081200034092030003c940d650b60115019000034240c1849804456007003002c207a0070018501d4043c8181c0810303240940184528441e6a03c1c40c0d666600141c00d0000114059014040700704200740c0e03d0620300d10090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 370000278 1250 369999028 369999037
    0x604170a080304080408010b0906060a08090f0f24090c1003090c090606080f010f0504020f0d05070c290112050f0601061211091309020a0807120c270209190902 70
    0x21b000b0b41c0703454140005850058105849980c008040c81c1c0b034881d0b4010120303003200b000780c840065441130400e41d140910041c4498520082048014841c2c03000000380b0140c0b001074001e000c481145500c051081020303010905409844082e141c00700d4402100301c00302d00500c0d11200240c18444110408600300c1d2481e08444126040c90fa200d58054403031000c6519105d1081c0328005189904039402c00160805801410041180d02d000c01c1c20480410b60f2402aa941181c4079000120440c084204020070200800403004070700c00309910124000b9030042c070002d01030142e640b4414480c0310400420004100700c3c000d1400c4d10066410a50303690f400501814a0f02007080042d6003030204144c41d1450340c07001d0f50010b04000300318401e440708103803401008011851050340c020520843c0402d6401c004c005002c01090301000c00d100301c0c0058244000600c0c016004552014100c00300c5c504110742180e0041000340d07290000580d607007a10307800201454117244032072070b61180740103001400c07a023364042e2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 370001528 1250 370000278 370000289
    0x3010803070b090c031515120105071b0b072102130315090f080a020102041d041208090c010e0301150e180a020306010618090e0102091e0604170a0803040804 69
    0xd850640f03600760415101c2010000341c03030b016031107001e4160b0900780c1d0039410380d04600084441c4920b1060358010a0845011020b01c56061717458030180164264070603902a47d880b10301001d101c0080f25959010f00512000d04050100405004200201d094540b90249060807000d011961050151004807604074140300940d040c62400b00510712a0138903000b40c0d10b04940c010020144184599030f906100d0b080449041d00b159800d00011034806600d10000c0011604064000d08a2400c0c0c41c04049455402c804501042480070500c408040000f690035000768007402c045140d9040440828010031285840f0050f10200a600141080807034802034011311030700c941e000c000c0c6041030038990344005001000f9015817000d001002101d00c034400c4001d01c4406604400f00d15070761a04040142c0b4005904520f450750300007000c20b03803840c084200550700041c551089181140100000b106400345106a02c100480c400116040700818440480300c50707402180d060300c90500d400c10340c1103070b0002d0290 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 370002778 1250 370001528 370001543
    0xd05100c050f04050108130f3f120b0405011e0b070b0c0c030c06070f0807090f05010309031b080403021905090402010507030e10180911121b0301080307 67
    0x1803022512950444000c0100038030300900d814540300046403400c60050441e070040c0d130f039911410006054074442c5056940207185010030601d9071610030701a00d20842d100c2d103010f40160658900120080500d83c01b00c0fa583c20480d81c00c01d407c1c012080948402c00225500916100012030340c2d8401a22006480401c00c100101c05500d450343d81103288a00d00c40a40b5044030f6800250070341c810140107100c01c00c6010140e0f0304240401140c103107061826540304011500c81000401050f921140d02c0340e021440d844d00b40e41c6149040ca4100e82a0b286001c0d00d410191070b801c9035801d0501582d18540b1230105d0802c1c0c1e4a5814480c10141059001400200c0c03060105ca01d07680d8046100c48844429034800416088a5171070315401912142d2218908806100149625104503a01e40c0c0865031603071840c0d100c15540d040c0d18110b94640c0d4140b504140c3d542482e041c0740e1160303585540295201d40140e03c5130603145032600180154418081642d40e42003240000c0003280c00301c0e020001c1c002e0644568403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 370004028 1250 370002778 370002791
    0x91b060509030a0f0201140406170906100308090102160e070905060f040b07171902161419080f010c0f0e0d060f0e0f0604020a0f0605030c180d0510 65
    0x49400380300c1ca000c4140d0550001e483c0c20049196103c501d03411510505105640b240c2c000b0f80d004568005038803000109406202d41c1815814a0160940c406195005405685061606a605d50303241d40400b810022001c00c20301d91710390080203404240e00108828091180e65104500b0311910111074500001e04140340000c0c103814650b080d60402d01c0c89081403030605003403108042c0140c11001d016289001d4101e01c2c00030704041c00b0f00401140c0480f048511082204c000083d00c3c046030840303840398921540303400700030802102c0c902022411007203d103030381100313002504003120308101d0304a001c190003007840307207203054505602151b4550500c0e03c40d00102c420504055034490604c000e120380240d104149080014a958080d00ca40720041c980040d2a08420f500709151851600e10700b400ca034040d10922003946072214440c002005419103e030070050810030000c1c1540006080c004162201050500544000c18000c00401001503d04440e00c241d030304219507503108030402680308500d40403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 370005278 1250 370004028 370004039
    0x601030221010f08120a1809020319051612050c1b06010303030c02010209150a031401061101060b0f07080705070b03040c03060c03060803190c0b0a0e0d050c0c04090302030c01091b 79
    0x2d080308028030626042d806c018030b8100c15969090071403040e03001c0210303680001c610740343c45101850091218003001c80e80740c0d20403100042210400b40800603941004081e501190ba884010550311241010700490107450321a00d0303000714040d400320b5001070b43c054910740101160001c1e450b4104c034000e60342441031a89c01c241c1030f0308074403aa00d000e0380c0042e40186c3c0b1000caa0024401460600b0031485c000540e240583c03400808000207800007000038032260224141c003070090140314003400700c5500c11440c203a40810040a94811a24014484e08020400400340001409004018a44211019a01e250514019036845818081119001e14061186100600c6442108141d50813100290324100d080b1004a51f20120fa04410702000a00700481c40081d18030b181d501e0149280c01c4010442410000300385050130720150340801002428001c0d8654101d00103490560101d0a540c00124050030342400c034210301c60010200c0c615070070015071200700220031861106861207400320303c03540398403203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 370006528 1250 370005278 370005283
    0xb030616140a1e02010203090c0118050f0607050a0f02040e0a0c091a04020d0f0b03160b1b0303090f061807181e020301050f09040203030a03050601030221010f08 71
    0x8544250004800645540c41040c141c8014a020092030606188508119400302c00f452202941d4400603500030050040c910010000d243d407081003400c028010403400240000707050182c0c0328942c89900847c41840c4030f5200c0305d0071180e80300d07040f400740c540003415814007454034a600d1000320f0145284c00281483e004c1c000c00c21014040e0301c9070112160350710f4040100041c005056280c0f594105941814009659510040c107040c40392410100781c124840403604111055210114020380051062040c805010000c90003590085525241c861080c240003d05040d03052441c1d80389031000000384107174910700103a8841e81020840450b074039503a50007000440c241c441d500ca0072032540505400d00039480940c2c007159402e03904000000308902c20006200b00da9141c9061040703002d90000041c409810203440b0001031490554611009007007c1e4080395032071040200010405a88101140c07440c3c1c803a40455140c100d051217090100c0c20002d01100b01322a080c803680300d5184140c0c23000a00040301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 370007778 1250 370006528 370006561
    0x206011410020c01080601020102251b080a080f040e150918100f14070906090e07090302010503040c03060204090f1407170408040909060204090c1706060d090c08010b0306 75
    0x150b02074090300d01402c00642c0e40d200054000c0c0c0c15035401388904ca1024106016503070480b0030702c206800500c800346c100f44c8403001480b90321110b07244007180140043c2c0e1340014003a100d107602801051795107181c22840000ca0040b03030041c403409407a4005001100b141250b000741c4008c411145c0c032031140c46081c442d80c501007a5001161103504094440301d40313219541d0180c050321451035008034003010111010412188101c03030f8580414068407050040942c0004048080c1801e00149034603030804601c0940700c9100b521009040010002c00607042002c20501e01004640c018030640d2074540b0b4010350f031b0241c103800000d448200d14100c00c10304070120038003141d80a40401c0c2ca400511070600300d44100401d0000704243c41fa00da003003000080c221400c3c400e0b86800c0f03009900050320740c2c0c100790502d4140c50802c02c020342004540030201d601c81c03c80b40d00c0c0a410a0341259003554078050350018034054405004007800c84900108000744414040d0401c0d0700c0000f00302d05030399540d03840c140c00c11400641e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 370009028 1250 370007778 370007809
    0x50109050105071101151401120e07091d0a0302070b0c0f0a05010c030e070b09060a09080a0318080d0207060f030902120c03062202300c130207030e100e060a02060114 73
    0x580019081f0789501802c803c541c80e40e030f2004040744040341210f295152031100c2c2d00c120485a07440303490f10045400304040350039604000c0d000c0c0100f0f0885480081d5150114082c000320b2034800200c0285101081124210175114042034039003020207414041e00170406090100c000c6410040c2c0c90b50110000b00b000da055818803c0d1003800d201c860f80500030780ea00800d56800600520401c0400c00b00010451105240d1080e0b84242c07100c000c814841600c01c1c59a808006282c0c00203118143d2190041a4802a20581d00c3c2100d0300c03c42c244401ca016210020307001e50400ca0b076030700c0203400f00c00200d07006030103010540441d01c00703459038600c1000052000140400301501c603107529006142044601d140759222100d01c840b01148034800c8075101c044220010155449082d03001c1d082d040c00032181c80c44284801017181030403104c1c2c5025180c2c4040414807440340c60f41c849a590710318040c00030168a60409050360740c4030380000c50040c1d5a108d08ac000d04a0b50303001c807018043c0030b10780149584034624 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 370010278 1250 370009028 370009049
    0xe0f0f01171b0d0c030f1712130204110703021b0907020304031202031c0e011d0703020f15130807091107020603060d08030703020a180f060c05010905010507110115 72
    0x45080c10412010710201c62603a91000c3c0052020001c00d103004914409076000e079549107207040e594540700021280d4484103810003d4207200c05006110f00c000c02c168000d014100f21a40e2080c9480003078000c1001d0000503d03014000301d00041410341c00103180302003c1c2c4960b004010802c81600f001050141243d9100040c1e00420060001444001c82d10f558500a80110390410b003071542000005030366104008170440d0f0300c00030f1a90103442405040e0450040207011504035922411035034035944a4040030380280b0080751308040315200d00c402d41d18080c0c22040e040d0748421180c1485500001940700d908098804c0c07150101c0c1410451140c180c0c4100c4208125103401032542c244011504000c003050b0b444044901c900003c980908000c620520407039400503510740030b418016000c0c17080a007100e10b000d6180d03c4103129001c4405290400e90f50907050041c00c2c4601890020b000d071211030b0f4000d00d5542031605000802d6000507100d160782d00c0f203070b0003408a4003041e152042400c81c0c4c0c1c4035038540c45 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 370011528 1250 370010278 370010293
    0x27020103060f03260904061203021014150a090f060501020d0509310c02013e070206160507060f05070b07050d0b04090809040b032b03060e0f0f0117 65
    0x5241084c0c3c0140b0484005106401c0500000006003113681550012252100140e040b0b030030903905000d0343e00c281c5080d85040050709100080c01110f203600403c0f040d820f4821200c044110341d104280301c001400e0051062010500c0920820f000d40664480d090240c4a01c0140039038031401141502e01c200c0014000d911000e0346412114129a90a4080a40341224043c14920b801080c01a0705803c11590008030702c068080c918400070381c0003500010800c2c0300400741c110050150069001d020115025825115000f600000304184110082a40c001c4001031900f0b0030440040341030b07012500140c8502405108074542580c240c840d54100400c154000c00005003440d0040313001c0d01020300c009100040b800003144c0801c0865071201e2096908140200d00f0404d50b180c14000d10000c8041580500020540c42492102c036190380d80310200d02c004c0c4c15000f1a01c440c07207130307010300014407074000702da20320781442c204000050b0300130340300310b001402224004903130050212105061035016400900c2d09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 370012778 1250 370011528 370011563
    0x3050d170a0b0a080d080103110a0501020a06022104062c031215060705100c0c151107120f1d01020c090a150602030c07050a0302010807110127020103060f03 69
    0x2c2000c0d05100e0b600640e00741010507030510420484200050744d8550740400d50450800790001a0072040e400d104842950090016903404546d02c21016848a8056116000c401b07044001907650300c41020442610400c00c010320107190052a18030071524074070041c0c1082440c24460038000321030403016035130080007000e025001c181c03d102d610075004905800d40c0080c440003d103640d400148103850b41d600c0b9141d52900790100303110300e6040c41a10304145641408954031500071807040501e501045603505074990559040204030303a40e480e4444402411250002000b03001220031111107000204131000d140f0310a400b40b103004d204a075058005010705a101001c1044064008000d0108540c61b803809510300b4408008c41c0011f045540c01968031070602c0042030349021001c0e0312603440b65136200401c1000d03036001401d00750413484518140741a034941045140c0175140030000301d035445070f0001103910710a8028141041d07c1c3d100366400d100322a0380d540c04600f1002d10380005010302e808400b40c03628 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 370014028 1250 370012778 370012781
    0x90914060f100228060e07080a0b0c0910090e0f061e04020f0a020601031406011d0c070209040c0612090c0611070306090b010510020d232203050d170a 66
    0x9203681d20700c100c0d0f0b80103501004040845800c10080c145540507030b445001089541e0064000701c400110040007c649070010031541c4868101001d40301810040105010070100c204a41c1100304c05044083d0420060310014401405071040a400b104481c0c08120207035822549280110001004030010b00c2007560201345202c902c0d01900e40c0b1903401c000c060401c10300340000e0041c9507082d40281010f58554201606c00000c00718051603103030815001804404021840000810290794030002c983da5507010040341403150007400703984080301c04100010460307450004400d5482c01e41c5c2d901c80558800d039001040e100e185400500b086006c0c0c2d0b0034051036101d9105407070402c0681c0120f455682d0369407541c071304035081d40c3c10596801158070014089404d0140781b0042880480c8010112100806030040840201c4080100030000d901240b0300b111340c0404c180d441c0c195840002040011829250b60000791a602c4116200d0007400c2038007000d54081d20f14043c2c43c000014030111281c3d0f0708001c250 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 370015278 1250 370014028 370014049
    0x903060b0301020a1d010e09010f0504050612030711060c1501150903030c17040b03190c110c0d050102041a0c070b0a0c06180b070305040b240103051005040903090914060f 75
    0xd0400c07c03426084078141d074424150034001d01c2d02c6800391407031908010501059aa00408490213441000d80100303900c034000048440c0c841e0400c84800380c590210b400502035104104c51010280b0840c0d580c5a600d03001d400201d4100d81e09510442d400a020040c1510066068032018010500740304086011840030506094850010107036540390079222800408960410b89104048582c1509080784030400ba110344140420346081151540003582c4a16548030805050070f0f016030309041104041101c00d4058601070040c5500400c807500c1840750040c0c0c5c2d60086030307420300d0700c1c461204000f400e01480c004445d4001c601e0754480b22481440e455003c0a001c0030707804100401c0c0c68008680c04540681d50150040700c2580e4041200c0c10542000c01e00fa01015103011546010113465150581009402070302840c420700300072401e50341700303401d410292005500440e041b5007407000c140308042d800f9404100780c528040c410408480418842c103082a01143c0e806d8100004181c04201c1d0316000c039440b07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 370016528 1250 370015278 370015337
    0x6020c180a11040b030103030f080c0301090f0f05090c09010b0708040506030705120c03070809060c270406030b0f0705030603070506090d05011d0106080105060310051e01060903060b0301020a 84
    0x109889200320003548072a4050750200725582d13004401032042550006041801400502e0000080d00b054240c140d21840103100301c0c29000c0c0e4601001900c103195400c0b50b0700002c5e42c1e1038104054503021070002d466426411142d0310800051001080c404a200251107a940e0000364060805040209016160b813003e00210140b010911402050302d22041c1e420388142054456507131642884c20029181300005891004140c0004080040d000d49860a44d02a01036900704c00c54040e40101d0001c8000c0c60340e105407a00903040040100900c021a042180a1011114507420b60342d03c8140c2242c19000c140d440c1603064000c1d480c10003e41c64124054a42140c008042081d48003d5540305821101001c2d807000e03c800100740d46014a00003840b0f018000c0c107040d4000c0c0054680313400082d49403502140e00c0c0701c0c070076a66004135000003d0040c000700309108440300c48200b0350b11420040d10312082031000f10340103800c0078201d00883c2010300a03680112000d803103030010034040a0b000418083d0180f0344 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 370017778 1250 370016528 370016531
    0x170a06092402040e070c11090705090306130b160c080a050d020a110c060a0c020607050304080a0516050a060203070605070e101110050f0408070c18140106020c180a 72
    0x510084009140c90361141030044006030f6941c40c1032444440c0407401440001030240e400310b8000800c00f000162007409408403100986030381c401b48180c4107401010700f40d40d01403044d0b0f0700304000d00d003d001e00f109407540108000d1103103583e2040c8a5901451003c0f090000600305503185000076160000b5084848072818840c0c24440540840e1080f60440007031140015888150140440c005000800842c1000d5484900d414694040505060710710880207000c0c801c0003030800140901403040d03501602540040d194840a01d040040e692040009200b100e02c090a40c0041c141c5807036940324040761804e401450801483c2c1d2100c5e0024070b0000e03c0304042c08502c000c07800c0c2c50796407100c00d00c0c4400c0c01034440a1000ea00c040095280c5040c1d600388110f1380d8600f005211130620b81c8402c4580c040d9000000320b981d00305234039000b0819000c1d03500601c62801e80710b03c4032882d40c0440c0c1140601c0e41f00030079030030b001e0381e82e90100b240c3c0e404192146a4100e940c000d034a00490038450203da6010300c04c1c080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 370019028 1250 370017778 370017803
    0x603050705090d031806030e0c01181e0306060503011a01030903030b030105160216060503060d0c09141608010320241207080c0a08090c09010915170a0609 68
    0x11072640c4641d01d5003200005c400102102900709204a00e40103050b1501d01048120701e0210b40b00c2d661400e4135a11030601c10081c542d0380408200c140d44802903c030510164041e8003c1a0004455900038042217030b22500700f450204003420141300b1213605201c00700e0b101e10f4400c0d10782c0040d07004165030f51061b801c250b103540f1500040e1310240940f50140481c24204042c0856a0707500a04101102501d044108251602000b0389079100c010349800c41e40440740c009488001d4500083c8441302c550141c4d40041c1000c2d411900c40d040d0180e1280708194209401501e100d0a410171503400100340001400095001a07401c66400144000140c01034003074103040003c0650520ba03900c6110b01040c005068400052804000c82e951450f242c01c04168200614141451000e9030014004c060560041210801c0003a440c402d04000203000c02801800e02034040d6102c6402401809000740c16901446081400080342858180f059540b1504400030b01940070040e07550b0800340c24903410a0310071805018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 370020278 1250 370019028 370019047
    0x20c01090501030207150c020d030f09111005040911071101081b03061c080306040c17040b0c040915080f030703080412110d0c02090c12041b080102070f0c1e0603050705 74
    0x2247c01d00c000d00c690020b210301014524020191102e101074201110309210b4404002401c00d084514045021101c044290001203411501c50103113078030400b0010700b010700400152540c4402081c0e4580615540032600c54902c0040d0344810090741d41d06841300410314a21100e00782d00020f55005840200341168107007034540390680c0171202040036240100000117004140c5428407a0120410503800d10101d130590020503079000c000d000300045c005181420000d1462410740c0100d8000d04407a1104002c40f80b40350310910318924060080b03041600ca680500303185a1400003e4424299150b61030031842c1d23455949900d41c00205480345c0c01408204261840480410300c20000e648055a8070680e080c0410b004010030601f0141204c51501001c01c680683c041070003054580c440e8120008405c1310a00b801100f002c502654440c604551012490300c1c01c0142c6000c0701200b0500070007182d40348584030350144e190b02c031103100c40403880c0c1d05c015410442e00c0d000e604095840002820030500305600b0742c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 370021528 1250 370020278 370020281
    0xe0703052e170d05070b15043b07030f05010b061c050c041211030a08031603050903030115080c07061422080d1508070b19020c0109050103020715 64
    0x4480d8070440d0051800500454600950320040c80300504020a402480c407400030f442442480000f81100640b500001c0064560000c0c90a407428054020420000c4c108441066041040403104500c80061403200c004444e03420106032145045c800b42c01c0142c80c5a58540031800d41000442d000e540b280858900e5650382000b900300303104280c44608003810b240b40120308650004044603102d43e0b05020030b12a010030311406400c1e49602010900c041072640002030311f80310b8040401450300170700208001403d91410004568040c0e0781c0c03818000f81d1600f0020585070f02090240144640550b600c03030b541c052040300059000717404c06040c070b484c011031900c4110a9940a040d01d50800b194601881240b01c1c2041021750941c003a10305400203040235070f4801c1c200d407040040c202c0d5420303203500c44141e5012448015500801d00407086034006c0f035035007950981a40000d15034044200d50300803603d191b0342c000b061344181c22105a5426041600b4a0015002900142d27000d903100040150719240d5200305 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 370022778 1250 370021528 370021591
    0x9060509010501080709020c070b03040501020c070602100c021b06031f03081903090c05060906040b0313120203040305030d0c050903100f0b040902090a0c020a080a0c0215040e070305 80
    0xc0c1000410341e50f041c0740a0a2409805500210149204001c4071504040114412042d82c0c0400384082e5281c88a0038000e000e0700070101070500714000c01e000001c0450300020080010b404084e420f001a1201c14005d0341c48502c050882c2140700300886009100d4030b000303c0190380c002000403550902c2c80950f9030050402000d500100d850450002e42180745c00103d10702c01c2510740891806101ca1129030b903d90306100c415120303550250300c003c12081c12341d42da4001a100075010000b5895241d00e842001c60814041d0800150368104200030702c0b201961020003250152038114005520308031061150400500c1181c03502400c0150a006407440d0350b4040c4109960103c40020201c0c5030b00c10322803c90100c48641c1c0199202d10300d004030003801600d9260103968400b004950003d01040300d090144d0801c1035110b0700804107100040c0c3c00800302d4108894025883c02540c661000860030009952244501d02030700c0c6001242200068545129400540d0b00281c03030f41241000c018809000341c2042ca1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 370024028 1250 370022778 370022791
    0xf0609030901171302120c13021b010605030d0503061503040303020a020f0601080a060504080706021209060a09031d01020709020c010b1c080403030503040c0b0d1b020d090b0d090605 80
    0x181d0010740d90380c4245051503c90440445441e1803c0188070002460402400240a0f010b1036840b102c00d54814080b54103e600058080325035070301c04182c1e54000358130040d00c40d0350074408070341c031003150710014400d10040e690701400502c14140900c00549203a0002404035500c82000b090442e00003040d40c0c095030240344030f520050385881c2407103000f90420074070005102d4142d100c180100f1002d800000c1076a003040e00124009801d40b1030341040307040ca100d40031340604224000181503628005801e111442941600b00380c1d011b944415003207800b500c001c9900030b80041c240400a140c1503180c9800e80404000500440e84031079540d04902c402e036000800d81c000103941da440000e61509281c0c5042100c100b00d2100583d191105035107482c628082d030700020342000f10200001d000c0095140310040a80300c0840c01c5901c172240c520300c05000e032811003225000103801d140c1230791400780002900040d80801e030301c40600d80d07801e00e1405075071034101048141a04e84c41d0340700c080109003548506802200c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 370025278 1250 370024028 370024033
    0x40b07141c0903081f150212040f0314390d0606051e030304090507020f030f070c050913030516080301170c150f03040c0b0d0f050112031209050f0609 66
    0x40d0b81405010030000070580030030001c01417000b401131218840c2c80d00680f14400c0c802d024054014a040349040442c48200e105c1e0b03680018041a03a110907079000040300e2007801d03c020007502d070b01289038072200240703e40f00d681d0491a0300b4001b00440003540c0d040088004c20303a0f0740320640300030001e465495100d00c140c40307142c0e403a4020301483c00c29150000c084248140c9185400c40c100340820b03940d00c903610500304040d60300d0010420036482442044d080d0031100086075100d0040c40040301c0301d030f4880402194800c41c03c000000d218105184024030139200300a18142218994a003a1000d51040582d00c030140d07c1c0304440c80004144001542c040c080a12847c10801d204440d03491900344842642c83c46003211540031050f4035504170444003c0c040e41c0c143d003620390b116850204145442c13900060360500002c00c0354032184403540e011052240012100340a02d998401e40c0b8404580c0c00900680080d601c0e41100840254a4100030b40b641d125404803241c60501d111424282001a2032000721038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 370026528 1250 370025278 370025291
    0x1030b0d23010b011205070903020306100602070504090201050d110906070c03050705030f0303070e01020c090408031609062a0507060207170312040311010f020c0f070806040b07141c 80
    0x184410756100440650190080002c0c045800028183c00c001d40340815502c0e0b01d0f04000340e0072a208180c2100210340c058100d49090400d2003e00820380d0560203180b0043c403407107400281918041c060319002c0d43d010b1b10380920b44a442214000940040b420b4508050000c1000b140c440e103803807005041e03280c095150020b03510f046181603801d0a2440d4407003840380c0d103c0d43e00171798081400300032250001140d0400031650a440c00042c0c0c10031030840e0000c0c3d8091204000c1009100b080c03002544070700b03c26800700e01b032583d1059040c4c441c640c6034000d9200250307a107080b8001103000a10058190300ca03c0140c50060203143c1c1e189494000c00360403480040e0410302d010030a042c2034803001c203080700c1c065010b58180000c203040c00d44140030042c0003a040101880700010440000c0d84070070040f005d485c906540d241c0110f50305503035602c198038000c0c20901c1000800241c0000101e069030241d0303400891a0217907200c030101214402e040800b1242028410842c21410140c08248030070012003061011502 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 370027778 1250 370026528 370026563
    0xa020708010b040606170415050403032a0f030209030a02040f020702011d0d030e040213151b050606090c0c0706030902041803080106030c0c06051812190e01030b0d 72
    0x2962104000d5034043e83c1844401e11549070040c2c00301c1c1201d200031005201a60307031402c0001c5c014000d20300e0303000080e15000500050691682126038071000581802c0d01d800719085130a4000c00d42031444d400040d00c4c0b00240f00080344250014080c62100030102d0b99403c440740c000600b01c600f44110900c8503a07000890b00110750b0030a820b02800101c400c400303181c654619001c24000380030120000c042110203002c110b070701c0ea6540d050754415036103107000c074032081c0c0c0302d11010540c41740e502c02e00c202141200040a5840c46030007a40054194840c0c090445500c8041c01c2c0002a24003500850300b920b0103205445804a04201030002000c955401190901e4140184411030b5900c4c0c007442049036004c40940c000c2608401c44504481e103d01e0006104012024112061020400010318940c20007060001942c2c80d110340003140350b175000076110308681d04800b80045200d9124514030084800580880c541d0007000180c1d2038110604001c21031384d220780d000078080000c0e01c03001c42d04105000c0c003c419 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 370029028 1250 370027778 370027781
    0xc02090a0e190b0702071a0306130e0106080c06090303071b0503030703180b07020f0907050903120d0b03011503110307090c1e08100b031801050c030a0b0a14060d0e030a02070801 78
    0x42144c014005010440d081c0180c141c001429400e20440000002000c41c03903e484003c01c00035440c4441108220403040b510045028081d144240c40c503512441881c2081442c02038121011980000e0080d0702c1c2c007046035a580d00845070550b41c2c14020b59078070000110340e2424070040200030301c207035594100f403043d504215001c0180c9070003a00c9038010504c8444016242c0504035076203c0d0301200c4040990b51408030407206482541c8a031038041c018501100000c0c080d00c4050031049a1144c000e200005009061600300d4405488002c8a0450705500308007084480f0300c107100081029059950b00d40d03c40d4414800c0d1900413900c0d40024070708034500d03060007500d80009200302d040c0b0316105200b41003803204940300104a025200c0e11080c000003041c03442040540c0707100c40b680c405009001c1454904d0080c032560f0803c0b16660001c505055040300c81d4a0410000d60507030321046000121340c00610300f8400300707811002003002203d80c3c894000a02800c10809441e09842c1d940c0182540c50034101d4090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 370030278 1250 370029028 370029031
    0x9141803030402010c11030a080f09010311030f0f0a0b030601030c05130509030d02221d0108070b0a030e0c19060f090e040807030c1208010f050603070c02090a0e190b 73
    0x2469a0024400c1c0b000507031340400800c0711650490045002505c084002a0034480204401008600000350030f0b400e0701e42e1071002c0c111840b8241c0b0b04000e0201100310b0000d40d8401201c12000301080c0900080c02c0f908900111600140f01c3c1d440019134000c248042850a18280c1065131000b03c41c010800042c90140352070700c9130003008031090040d81060301c0300390354031300601240e8107005401107000b2181000d030001501c1c40a05403400d10100569420a9000c210251b0403020801c506250006c0303000e0100003190340440340c1c2c08141c1442c00d16100030480040211130740101b003d00030348010826030380e03c100100441c844640c4120b05400c0c605074014001c031103107003408e0003405445403041100380382140c0d00740d81c1306800418045e82d40910340b808a46a01500000070a0082106130490b0b0241e40855004c1c180c40100703d6000f02c03035440300c0400450307000403100040003414244980e07005042540c01d05821a01484004c91061136484100382091180c0346641c401e05000d0910340107101d400b03003445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 370031528 1250 370030278 370030321
    0x310080309010909051f09050106030e030f042601090b150d050714040603120201021c021c0f110c0604020316050907050a050412060209040510060c0204090c0914 71
    0x254649003071000040c015054a202d5800b90f6a550800110954001002c24070511070101040c100e0300e444400c12001003200303000384c00c00a80747c004004d09508002044594070070f880200c80c1d080919001403140501100304c4903042e00b0400220001b2450424050a04010310035807840f009850040700b50b40c41d04140306115440340740c03002441404918046103000035146010345100c02c1030540800f1501500d8146c0c4001e045002d007034050050168190302501c200c650351079204000e9884840c4000583c0a2402c07414400709191403c0c40d00e1006a910a014603c42800085074442080180307000365003041e8007107e1503400540800045140510850146559124030005520b0604021440c040401068081400780004a504400d4018000c2d41c0c020800f074005069003030513516121020f50010140c5a00890400d00031a5030300d0b1491841006844a0ba071700c2c40c0c403100490b000c00002d480d00c000e00b0750300500c1c2e400b0007040140c030900605801ca403030304c1d400b9030769414080703910200e03400c860114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 370032778 1250 370031528 370031533
    0x150601140a120b0d140f06040c140102280219060c08160f0f2102030307050a050f03010f180c02100903110d0206090114060d061806060b031008 63
    0x418803140046000e880c40ca1066240c44090394604401c984028003610b0109580040900385403000c1050020300010544840002c0d5825000c03481e032020b5840000796401801c14100038824090b40405c0d070219061080e0510448070342e68014817116403900006d08500e0062b000c3c908001d07081d404c01d052800e0032038098950b907940700361410f4001481071005080007486510700040900540d5001c0800e01000354104200070090406c0f450500c01070086000111004041c4814000b04c0ea044104281c604c2461034002c0d501e182c1d07520100320303080d41c0a5465001846828403c50030b00c0b013200c5018502a00e41c43c0309040d001c034109403101d16520720000032170005a0030440c400481c0d80d13002c02c2910401030320354004513000e5540e2605440f900c1010010030007a20407056807603400c560010303009000c1d1fa0140004c0064581d0364650030b0305e06404aa155802141041040000800c142d112460070422000c4400c00d5011550340e8604ce500141d2100e000c03900040240108100348106d03510080808100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 370034028 1250 370032778 370032797
    0x3010b0a0807050d210801090c110c06130b0c030901032708030a090b190f060308120a151409010f030f0f050705030f0102030a0e06060112020d110408150601 69
    0x801e9503582c00600409014824000e5510104007030000a83c540a0b640111036801a403020320042880909100b5503074914100803100c26034500a01d600804004490090b203500411401030151a50050004000d60401668001092212800500540d00b900c8024540e22400600014203962900e10743d8080c0114841136a056030103441102804180c0c0a540c60761aa690604031100502071060060860400340c000c11420600e80c420308103001050810401c0081c1c12240c841c01200c56501004003648400c00c0b2069101c016000402e500080c94800802c40c105400701140c0c00070030a9000d0003144040b10500c100c9444c1c42040c0601404e032086403882c03040e01d940c8170349011000205018000340894003101c42480f00c140400d50180001030115150300180c20780d118000d520032218429070a140400c0c4161204001c51298018081655041c980e580741041c1003000390f01c0f1740440712449a40300a0351b4800c110101c01f90004003850310180800030041e058030b02032581d0007001c007810004940c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 370035278 1250 370034028 370034039
    0x307050a0602071a1b0a0c091a150d06060c12020312010519051e0f030a0506060108090a0f03030e0d0c02060d0c091208030103051005060105040306050c120106030b03010b0a 76
    0x19910219891118501c20741c12003226031130a00d225008401c40c50328041110101c02040c0041d08089a40c81240c107825410b5842c40d142e0300f00c444001c0000030250141d01d8554503854420408a144c038141e00c46035180804c00c2c081441220040d61010010800090030301041c0846c80395044000c0c3e4460003e1481c009860300b030066112070502496125100f160541c00038440300c0b03625200030385400b900e120051404c0041104c1560b800c0600d50307104011002070101d080c03c1c0400d10510325507000f002070850f0307111b80c0d00640c0c82100080c06401c030343c40795820800100700e0780902080002d000351000541001c08090403801d298140c20001c091201c81c01840005071148004c58400c41c40703415001450310300c1c10038100c50864a640c420324044201d01814024801341c2ca0003181282e200c1c40446940108414145003603410840307030310303001c19414003003000800d000d0380040c0e9000754681d50302c03450b040c20801203800140080c0c110b0300000303580b100d1446007410b09200e0603640da041140e1070078100340740c071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 370036528 1250 370035278 370035283
    0x1020c1507080720010917031005030c0d0326150f0f0d0303020d0e0105040c060201060f12060902063006031f02090103060b0a1d0402041809140a110307050a0602 71
    0x140c003600c10360500060307402d001007080d808000c41c40d0b0f024004510040b407e92640c85076800a48a842c10100c0c02c2500244a10700058004800d240103009481c0060041d03c050b5884c01c2c68031a18009400c8000078003843c101c1810340d441c81456203511403081100074106000c004081542c420340181e03283d44520710a0741e645115800046e038503180241e65242c02040d58405880022907405140d828842403104001d41d15034448140e48869000700840c0c3d90b1005207094044c0c01b03100c0c003a440d0103900c0002c3c0c080b40f090303007007200e5860010780700602d0021422421440c0340300340580b03007007040b0304003084140c00c003002003243c0c1c2c002e0340840007002d112011040344400305800309103041010743d00146544d082d034081d0b00000003c1c40b20f400f00d40c4d1654003606c0064002c1e8102440c402030a030507000310445500c0c091082c2c901303076000080317507000380d4440e104008000c0c060603800313460f006040382c80c000000c1c030300300203c26003944281e82011142e5292000c0c54540038407034201910070000c050703051001c50fa00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 370037778 1250 370036528 370036547
    0x30406050411030703030206190213090c030b30070501050a2303010303020a110604030804140a05060c160503061e13060c1d010e01020309010f1101020c15070807 71
    0x6840000ca0391150325080d40c0c070b000446640741d05030050003400014150081901841510300422024658409003548000c80c402c00035421415071094005000005030303a808041c4c000203500300029091f0200000a680780704140d412030700c94100000c424036030840c808066a0003107002000f0035030f483c102400078080740103222540f03040184052090440f5501500500210302844c140b03590b481d40c40f07050094480d14500406d0f03403043d854104030411410240112811680c0140680307051a00300707001c899045000d000309a80c0200001c1001c40c2940d504401481c2910403000200309801c0c001c40c1280c0b909802e80e1003e482a0004400c01c000f440020400782c4440c050602001202d0380c030161f6a886001700700741c000c1c108038640b01100c3e08640e00140c030010341101c0c1c82082081c503d6000c00440c2c03018885580e090050304113200c0e0500550141112081071115401d01d40305271010100e0131402c80c1c2100c411458194400541c046001d030720b50fa401600318080b03103001d44952410010260a90b0407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 370039028 1250 370037778 370037783
    0x50a0b1909240b090306090d020a15020c010518120418050903040306140601090b0a1e0504090e0303041101111506060f07380a0507020102360a03080304 67
    0x100c80c11066070b01c0d00000414400d0698015245101c40c0d111150034045400200080d4080e2185038040365a01d500040c44c2c00802c0855401031014882907030300d0b035100b00700400b0301d025925001c1c0802600b1060a01030316101da08076024020030820805000ca00d81405041c0212150784200424410350072102038045036003d04d110045150344541c1c51680c0356102c0c540c8007a1007240341900c14080305c00c142c414a4010002660749a2540b078407842130718124400e182040380070994503083d900040640f2804013a500700c1e241851410590368013560003e44003081d905484903003002041100300304c510300014400820a01e81011405035008810390340b489190303184040b20b508580061801da0302d2400702d402002c2510035850f2284801d242c00d403110318151820f240078003070710320300c8030094440c400543e040305106800c06c030415114107030404000d08019024108554007007111004884200c19550003a80d01c0c15030440d00f40d820700008504000c0031444552090020501c01c001040000040c0c1e500300d038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 370040278 1250 370039028 370039031
    0x10c030618180203061e0c160212071a1b0622080f1b0f0105060a0314070308040b121608010b1b160501080c12010303140409050109050a0b1909 63
    0x400d4408102e007a001104020b50520a110803c54910788003001c01200b001c50000c620965202d044445030305003e010560b02c15900b070304404d04058038151150207030300c15055050702c2c00c0c161a030001640c0b040419a0004400000252002c9100b011420f4103450381550006003005082c10442040020a000c0c1c0f400c804215007200307081800380080403240c241d441030303c2071035440455481722003462880d512209030314000d50142c0c90a900040c001d103071080c1c0d40140720340c1d8085d0450703035101041c85400c801315000b407040640200002d45a05c0090024003080c4940ca42c5943c03100850a4411100a001404005803050501d54454004145a041d0b50441c6e001c0c0e074494a401d001c0200b541c0301e013134a0031030901c9920104031034181c031041c0071000e40300c0a80e6918059030f01c1c0b080030f0b00300340f0540c0c2c00c074102103c40c6001040030a100c2c4c200f00441600540819103825941d00f02582500c5081c0c00411100d5520030030f00c03048114602c14004800e9081d0f40307981c0800c0410400c82c1070380400d4891070b00380d503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 370041528 1250 370040278 370040291
    0xf0c1b090f073f09031e0e09070306030506011707030b090a15020903070e010305030a0818030408060f0601020d1d040b0901080604030311070503090d140a03080405010c030618 77
    0x354000c14220300c0390900c10070814007042450000001041d0511242c18009403c41c070521802d050500590401d00d425449071541070042d01c0380d0b0146031132694511410041c00c6004061a80d03507810241c0d0080f503041c4e601182c55401d42c180a0708180c01a80031007010b041540c00c4042c403507404284141140d030003924440082d0360700b0410300e0070070015034001424441c0c002442c10a42d0050350152103404415412109a80e40b0780c00d00c1e1840078000c0c00090015802401500d401901c104a41ea902c40c19507403940130624480c410700c6240d40c02036003260140e50001000c00c5461700700705c2003066100342d00748000d20400c080d102d00900b01900011022150510f000040d0742c95840d244c0143d8081c1c90050b0040c5c4840d80d40c0c800d200c2c0c03a0703030301030703800301c1c000b80c02e10030a00c4a1f52041000e503950329401c24082d6103085011400c0140f10010020101d61403c0b0010f0310041c0b4800178072030001458001e4071014103904c0d052900134210b03107000c0c01910a00d881d201050007000d11203c200540d03490400e20000e0b86 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 370042778 1250 370041528 370041541
    0x100209040b06030406050114030d050409050603011e090b060f0108040311030c100605120a080301121b0902071407231305011215270c05060f0c1b090f 66
    0x1e0305208a050340c01071800402d00040090740c1d403181c0d0490300c2e00c08410030051040420107443c0c0c907000100c80c4c00540c0c02d00003841588803603402103030000c0c401800050145903041030181d0781d20700c2910103c009a60741d9843da050004419141c0d5101b08200c51001d1081c01e00320000c3c01000d0b014001404100d80080d0010483c542002211144880b600440d581724819044000250a05001d01c601a403054000755000d000c00090300500c2c45d134802641803c6a0a10725441c44600c11a40c0c02e03602d00b0f00c3d080420030b50f81200d400d900007401014a015a844086003030075107400c10040000c0400780d01c602001c00c041d803055000d01418001420703c455814640d400000e03021003941031100307445450040001881d040324a030990b5100c0c8601c01641c40c0d003192402c1c1e1400c0703401c65200020094a016505440d41c481a203400c100c141c0f19450080c2e00c10b49642c04501240c01c0b41000304042400014840985002080b82c004240e500c40e49000c9034140000c08144540c0c0041c040d640d407440120007081c507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 370044028 1250 370042778 370042781
    0x120e010e06100918230a0204090b010510081b07080c030415020f07060f0e010210141b0304080703030207031b0302030a170708160c020306010e0108190510020904 71
    0xa008034244210390305030074504102d41c41e2100382d20615220301e00c0c2010050b440201c00d80c1c240401500414001d0120028a10201110885500950607809004d0b800c2c00140c0e1a1702c100802d144c091000c03016203604250a1218100104005105101c00f1404000703100045010040d80141c943da4443d403200501d14106c403050180d1000c6410354000404d01041d240b4130150111005500c5600b101c6e9065280f008035a2518041d00a800005001200c1d000030107001e03540301c2503510b00610442d021108105183d00c00c0700c4091880c0a002400041405030204003034558600e0610f0044070b0910758102540c82c0741c0d852003140001030a058000c200345081c580114003018007010300750614840c0c0070051500a44a6202c0d80015003c114550300b841412416403e2141c4201d401e40c4400200c0e84030400c5004190b00390324180780c200610860303000c0048e1002c0c00464020301030b0003810002541007030745440c01e207040c4a07031b041403e065a00b0304030b001c180b0008a240e1246418400103940320140380c0400c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 370045278 1250 370044028 370044041
    0x204020c101406010305160801050910030b04030306230102030414060906280507120c50030f0304020d020907050304060e0705030a2d080a02010b060901120e01 70
    0x4501c902e84140114035541001440d03105241c240e80820155446a002d0401d0351200440800003544000c014070580c1090003415400460123010b040c0982da0300c2c0e48d0010f54134821078040340000d4840b0700030070000c3d01d04242000d0302d10a0400400181da50030000039928000c5203d1640e20060625408069031a80030440d02c00304009003a00d03030740307080c6410940036815100381e6007100d00030212001d04401d4418010f80780780c5640005041c0120040a004844024981c80705a42440c4510a00fa01d40e8a80204800400d90000e0383c1340d0340d010500e60503074410301c42c400c0c0c040341c40f850740c41892000380e1004c003c49118106000e00c1c00d80b20344560000c64900b220820b0002d4102c00c00e101808001500000554401c40c8036030005c0c0640707030030400d00c2501d4150510446801da444440f00c6000942c0051050030700141d0715100c05505806020409002c00342e100d8182c58031503002861095842e070a016403407210038103440017031030424000c00081000004c480b0495040c0d507500342e0501a07000c2904400e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 370046528 1250 370045278 370045303
    0x16050d021303350910030902130606030b01080906100b030a0204080106090209041a13090615060504061202030c0702040e010e1e0c0411030408090d0c080604061a030a0204020c 77
    0x1603d1109081c182c000c0d02e120301c1e40e100c0c58800d07071803040401c80310490032211900c4000d0310240d440b1400c450240c014185d8014100d03880003941c80012440e030954407441004000c0c41d50045182c9410342d0024220100c05000280150131000411010505144c1c8680844031000c8420f0354a40d990702c0c10100902403900101c005500784080010912810340240414580c04c4804210700522076003881c007034201c59076585411104c030718460500d6600650202110b5400781c100032a203492041c9482e40b0414454000701c0101c6c80c04a0148a00d079403040c50503009480c201e40840c07550400e40c4040c81e2074058030b00000d10540e00d13501c0303044076140c00303401c554207405012080b24045081d00220840b415517408800003140f0503400d08410030700c0c0c28040c2c20421f071054039034180707142c444d51909205a41b045031302d190807443c807140c80c600203000207201d000200004009402a400d11785882020340e1a0b12500c00700d80c641d0320b0760740348003030381e0105200c2e441c1541140d0060790b51551040c03050401f0f0321446038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 370047778 1250 370046528 370046543
    0x12012a1b080a0e01030902010e09070c3503071704030908010e0619020a0503011701140109020a121a0d21030603051005040c2312010905010516050d021303 68
    0x90301042207030780140009030425203c003200c00003103100450849000000181c0015100c400300348903402c05050094020070503240c0404000c41580391020001c07500031341c0c1c0b0f9040303050705a40642d00003000d03065500f0680e1144414510304202e14020480404440c0c514021111031010604250042e06810005d02c80b8500900000c9800380e0703016169182200c0c891120039080c00c405607909000d208554549000b07407038031410b40e42400d0030990402d0050f5440d284075940c0312941c00c1e000b1080900b85000700000a40075039510403000c0c00034031002c1000c640b000b0044c10021000c0d600310b5882030103410380409441d1016816094146410900b00d021805400700d500c054452800542c1a00400141c3e80180e04507141500344980f508100c480071540608044500c01c020701c024040103041030401888804401d107071116803000960140e0844800d0403481e0b654111400800400307002e111b44c05040448203401c001d0600c0c00103000743c4240d011701d881940e400600807900d80d901040100c09076401004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 370049028 1250 370047778 370047827
    0x1504060305150709230411070f1104020703090902031e1006091e060507080d0c0e0f01032c0a0f060c08010b030103020a050d0204141512012a 62
    0x901d01d485034041d440b4080c80b200408001040907001e1410b000c2161446801500c551019224415190b003010141580c441d44030605402c0001030070000c1d1000b0380c00340e64110800541450300031214122120450f008500610900c80803940140ca10011960000b4015a403543c2c1c40001c40e000301d000440f07692003084423405001824044040390303420360741540c844502842d2134158222103003000011202501c40000000d001091045010b0103a5921462070343e0704045d44100488182c030141241e803000a00300d400300d60194a008030409040c62020b003400c103c941c6540107040758854014403007240da40302038826001a1141000000c416a40100d11510411802d01d860009420b90352260000204040000720306d220824045034100d030b03402030507001c0407480c3c14148a2074055982d0180d038041e990350101e00d6640c01c00c0d0034443c41290b00400c41d0403114144810029009914000320f1105d13071400c1032658009032071040300021241c6072400020340841d40e680c111800e014010310014204092036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 370050278 1250 370049028 370049033
    0x5092103070e0f150405100e090c09060f040602010b04230411030a020411070c080615011404050613060810051309050f0d050301030203010506090c030708060109050d080403020f01050f03070815040603 88
    0x501401c10359000307c48a00c040d098500c42100c105082910740750f0301005900120f45410500780c02001c0700d0b24050125400d10200c150b2496a80d00151301000160b5160b202011092905201b4031805281d580000c0d13101c0b04e602030f951554a80002c00041680740c01054043d46680c0c1080340103003a5a0040050124058482c000f8205070864402169036140320000810740c0d050100f070b09886004030503a001d041081d01e000440300120600e007410702d442c104010109250319a0300c000d02c0b0040f90b1552040d805480c6c0f20f80200000c000400b81e140759414410709004a6598200041d070080c0600e5020600c0c2c2d0b0541400c60800000784600182441044800d90703020b604403020354100e0f80202e0080000e9038811050007200030007100d40031500d0000700001541640103001c1c240d0491010b01d400d2061071b4403080410404403400b40c05039806100464100f00f145060b20f8803038071940d000c1ca0420708194035144c02260a0101500da04140901d00380090003a03031201c7c15910700580e004100b03100f0140e490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 370051528 1250 370050278 370050319
    0x7060f021c020f0a030c060b0a0e0c090d0c06050a11120409020c03040504180b01080604030816271a0412120203070b01120b0a0903020318030a0506090105092103070e0f 74
    0x21001f1103089080120400c01d0386081d0000104a455030061000b007655861210300c400d1740b00d4490160700844855048020952200803600070b0310306074890700e41d9a80580c5000c0c007911350140c0441184c1d4880c2c8040e2551000c2181600e04480600d0000750b119841c06584c6c9003540541d801250300301d40390140030007141300ca0203000d203000d6004081c01240c50341c0b00c124982c2c982d131703045070081e011034681c0e0046025403212810f0f480390b00b46030f03140c141513120b518480d1403c3d41c044d0380070800040d100c03004140840803444002c40c5404034250062894585880313004403c14241036405004000300ca2078660145000380100c0f0720550b884000c0c42761035a1182c8850f8128a001c900c20b803042026140000c2100c00c00d44511606c603501900110b0901c140e1485121620882150f125014000c0d07442c690001501005143c0c0180c0aa00000c2031900d0a450510b10b445002c04194000d24a06103081f85000c451908030b98004a41c6e00c1c09030705082d04031010444422950b03221075000840d4a00500d29031001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 370052778 1250 370051528 370051547
    0xc12061e1005071a070f0201020403050703030507020303091f261815010312030c180510170903040302030c15040e07200615010504320a06020601050307060f021c020f0a03 75
    0x3692140006c041008004908038003031804002c216920004040c0301203409403010f0140c552000b412280f03001101000b1030700a071400b0034aa40e0407005000c21604464001240440c1e032040a100c440314080f4411500321845009082244031038112101c50301120014089030540219000c01d0040a50f540c0c644061503003030302070702c40c000a03103401882080b039445102c0e06500c00c1c4210403844071003418182080b40e680621440c00040c8004694001c588910880c03049204000480265448500d940103160829000030036031442201d0060007285044041401d039000c2d80c0041007824059a201d5a06541c070706a84204907251034032005108a9100000681511a1900724411400c6048020054400d80547d0080d5450f8000c54042c0c0700c840e000000c44080007186d101020f8200320700460210303d400c182500705400580110300184050304040244100a100070300d0000d000808032030000b5281c900341004440051180540032200510800602c00d4800d5100c040d2003808403586030190444c80d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 370054028 1250 370052778 370052791
    0x207080105100503031c0e01390813050a0f0b0a0606140f07050c0a0e07020d0212090f01021e0102090a0f0e010b0708070b0c12061e1005071a 62
    0x30000000e0072140b0502040080790409401141001da001c402c11290300030760481040360035913806000852050900910b80c4000074841c011034082d400355440c400c0710030507040708032880035418120f061850b80100041e0348000746510b10103030740206150140c100700c0051405000004002000300503c5082d00b850342c0242e600e80c0d41007040ba55205403d6a80310300300590f0914104007441402000e00c8a80010004244a00d040d41c00141300b00000032480c1d00590401e480d4070441008000280340c04100d00b0b1901785031400100322000761903c41522a200e01a0010301403169242d4901a0340d008200b9100c001c4014200c1c420f104050740c90143c003d4003c0521107103d5890070000060100210402c4425115617052203a460ba003401c150a90550218030103d91400c020003a18010031041c403844d0b4040c8440481c43d0b60354956140b001025542c02400d454410043ca01c440707100019032440ca642c45c02001c0c0d400d90329507414940142d66a010b6084054102d2030701041144c1c429800401d01c234410385 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 370055278 1250 370054028 370054031
    0x706020a080a06050102190c05040c0e031203100b07321e0d0f050706020c150703141b0705011a0114032a092d03030702030703020f0d0f0302070801 65
    0xb66802600c00644500f0b2007880e001d6007180b240c0380c150405c241110104180a803200601e200d550710b01003012101d400114a0020340b002440c90721600d8144800104440d03414040341c21800d01002c1c01d4480c0103140704403807803203000042d000b04201008100a600c1c02201440350112803952804101918088210401d903005030318102c840018018180c10794080104024560f10b40300c0b0900b40e8044070b500450f442031003024440580090740e940000d041c0d0103158030190503000500108200c8501024080c1d0b070625040c02c80003240f0139540c1400d1a4010441c0788030b444696040342104d5014170507103101070030301c0d42000300d40585409007410642e00c00d54207a07140d428900152100c000240001c0c0c030341c40c20300102d4881040025001480002d00003540c0c81d000d6152080c1c0100107110004035840c03200d440d6400f44001c1b02c1000d01009170503012034041e00610b2920100d0b9000039205c02090000038032070448650a04141d0f1220824410700c0c50307000c40090701540d01e905006e0350b90381da68854000b682d0f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 370056528 1250 370055278 370055281
    0xf03090905090d17090f0f070303090f060c0210200307020f0105030f0109150b071103120f0702061c11030f1509040f02130203150415060c1b09020706020a08 69
    0x41d000003e4005210741d00d5070760091001100402139041c4100a04860400e03c11b200346580344007414031001c002c3c04004402003000300c1c5149409819402c0640c05002c040021200804c1501d17003101c440c0e08074950403141e11090800ca41410354424a810f481651200d00304503210324000d4000000700b10090080700d00c010000301c0b01c001103a25220880380e0084984558004000c0c00525401095040003003400951070107072100c440384910b4004040556101e0007400159140381400c0c00dd0340c8038a404a4034076850700001e1640c81c2c03120311a0030030090044100044580c494800044c41d4002d010800e88244a00d1049148080b0306400541d0038501c01d807281d001161024038507180860031a4805028010641d40c0c6855114034495011343c1030f6040310861000d00c3e40b185030f030720045104210034060b8540c1d0340303560300500040742c10034920009200c03110751003403001e590054403100c03844e03030b02940f43d891405140301119607400031940252145800844c080040021a4001d0940c545207580c428540b07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 370057778 1250 370056528 370056541
    0x21c1b06120b0a0308070f03020118080d0b09090615030c1002010b010215090d0806010315060206100801050405030313020102031e1c091203021b06090a02010201110a09050103180f03090905 83
    0x4a411803000a01c01c05d420010400092000000700800700d009000003c2d00500b80030000e070148401d20700c11504010001040ca0914806105505484006554140881c0342c01c8145d250f886001030441055100c483c40c501030b00380c2e4108540f0100100c040c15803d416411180003078060004030001074003501412611500004d40036103014403d11011004002d034941000041e00c00c100050180c904060300c1d03440c401c20703000030700c01040003c1400354018001442c1c0031442566400145c0c01401450741008288004190000262504008140001e00c0c14822030f00c0140d01c0c521480c1d240121803d84649540040661180580502c1c4103201c449210b0741040c010200850b04022070040c401c2841074801c41e5101c0c80395016107010360040940710301341c201c40074440f407505204450784c88985e4000b0201d0300455a081c095041c81441c0000c031142051403040d00a00301900c280580b0341096582c224551000d40c8600d5a2484160091313660340c000d11460500401003170307490103810102c81c00d16000c42d42 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 370059028 1250 370057778 370057789
    0x7050d080702150402060405040e0606030d020f060f070908070b090301050c120f0c04120818010203040e010b0d02040b0316020c030c22060308031312020109021c1b06120b 75
    0x80756490781e014010080c80464100b00c3c0c601c1c054401d07a00031509200c08a52070f00c40c0d201c3d032000c101e6424000c00b51032502d04c04251614044050442c11034100b0481038808000001c1c0c0345400c01c00c44020000d0036502da6104030380b021469480904544079110300050b1001010000700200c40040d0000e1140d40d0b500308101c0e545200d6405101400e0564000090004030240409600800b940c0fa01c0361a06070f440c842d1420706055840c0030f4640d4000000c8490806500f40745140300c0740c5080c0080c41c102881d0400701078082c0c6052140d46c030010340000f90342d01c204205038111000b400d614946c2c107488c0d0030800d4151700d0614292105102504c00c50711190701c41d241c0020280d01700c032002409100c0d4505410481642640e03003619021981c2d4441c03d011001495440246115910204031000c980e6590709200030030041e5070b411a810340e490100c1c22005622a40f12011101c0c01081c0780c0c94185002c3d10701401d01d802c11003201c003010800d0301c001003580b59010305140da40c03012240c0c0a0115440d160100003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 370060278 1250 370059028 370059031
    0x160b09070806070827030a0e01090e0c04120303111201050108060a08030f090607060c0320030103030815062701030f020408030a0f020741030c061e07060207050d08 72
    0x41850400028018011500102d88080354910018117220080c840030b441c40d002140da850229100f03140340e9201c1e50f484403074400140b60f070518200d503605010101042d42c0c400e45c040d801c848010420f210040c14081c2d084a0407002206d40740a0b90b030b500170000120555002e008031070000d450300001c20760782e14080301c010085c2c0b903420015501c0d01c09842001d00c0e003540504880360700a601401004003241035407080000041d101d850210703070380455000750101c13859a41403040d03050034148018404070f42d105c002d850f17000c03001780d42c0741003280c0c40040012100e0050501541c100031400c0240300414a4080340b0000c146002e0301c0901500700e6810412040c0c0c0601d00401009070320a0088281051090007000384070a580e00581c1c180c0e6445800b40c500707000e5001c1824659406a6079400e0f03104a14034806007420801e1820001036105030400242c0b0307103181e2000103101d510049031058045101c9040041d030700c4c0440102540d01c18291a0000180d00722042c1518903009039004401803c4c01085440d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 370061528 1250 370060278 370060291
    0x50106030b0a1418070f080105010906210308070c060c0c0203010e0304030f171308030c0709020a0203180a081905061303050d0c021603031205060a05150f160b09070806 74
    0x10760540d684c01d5200c40d02c203091442008800e21811700c0010341c81c41e02c492a0000b4015000001c182e075070400119006480b031940c82525170411a66200e0000c1180200d81c00300103515240030f40443d159040304403203031444e50300c002d000607192400c200e440c0c40d04440e80300707c3c051017034000740004850101340d5900c07401584805803003100c400340c0c4030002940c515408012100d4070300c00f80e0b080c55403030705c504031305220a0380000304613500000c0d28414040c02005150001d1502c40d00039440c000800e00001d4481c004c843c402d400c180d800c40b04004040d698501c03010081c04242c000c03035002ea84004200700c0054180d0b81c00b0360300c41c010301c00030440303404518070203032001600b544540707203441c80e00c1c00240c0050140c20007480460154000b03003121041e90302d00c0c0d02c0c011806036450083e0b10402400e19030441e03102403c61403082c030b04204100012f84803509003030030003000c0c01903094803051a600b001840d807095050b10b6100c11864043e40040102e0540c02500ad5140c240403a00e5094461040b2550f510b019140c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 370062778 1250 370061528 370061561
    0x1d061603051608130501022b02040609050402030601020a150b04050f040b070f0306120b06011701210f0f06020408120405011b030c1a1801051302060a021603050106030b0a 75
    0xb4110b075030003207040344d41004d00c2500000e08001940c41e82804c98010b100002c1c40d8541c3d61070142aa2201c6041d207880707805e10282c085140600e0130350003800035a45442918040c0390088001801d40c3e0086c1311b00c0c0c0400383c020281004d520070207a95080241040140144900c3c5000d01140300c004d0411007051089070310600c2c404941e01c40ba2010346483e1341041c95a0205915400041820510160390101c2e0b203205407498042410050700141c40b5040c807129000120030140010442c000e2842000300c040c07007880b0340c568050255030401c41c8c480b890038000502800e4841809104021165004000301c8480c00243c42040350110100602c038400c0c2c0c40343c580011000e0221030300f4800084110110300d4407901300001100000c1d51030b40280c2e01c5c41d907517101c0b003011039204000841c610074641d40b040c031124400811962500e9a0088800540410040e01642002c03c2201c4501c0c000c005401c01c00400c080b2080304a81e0f00d2030413030702070400e5000840703481c1e8100004c00d80c000e24034002c00c001c171b10100785c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 370064028 1250 370062778 370062811
    0x1509050d0201081009060806070e030c0d020603060105070c0806100509130b191803030507032c030903061302010e22270b09070501022e1d06160305 65
    0x1115080c07806030130824401e126100001d01c03040a8465140240180000790a0a281c59070014060803d0551041e00940011105184c84d503200c41480f840303194100d039410780746d032030b0940122208c2c003070824001c18949445d40d0104100c08006442d80c402c5000b07501a17900c0701d40f030744148500d5000540380000c1410212080000061090394050b0f03200c14641603900d80902101d01d007800382c81141a1101280b01131010310028107605014141d8081407074141400001c3c1c0c0700c0600c004e00800e64940d1a800000340c880505030b00d009000315014070400038121551420001c5000008800c2c81d60704a0108903451064a640e0511444854007420307445000485101010002000380594004c0c4e4003106002c0d440b40840300c0310f50100110402e018444941c414582400080e160400030b8000c541558481e5184140c46244088119a0a4420889482505c0d140c4007080c0252991403c10481c50b4150800b0500110300054150310071b00400955138030300c1c41d050b0740c04d400312603095801c076040852109 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 370065278 1250 370064028 370064033
    0xe06030703081b12040312140406050a1103070b01061107150c02010e03010e01051e060f0d0210021207150b0a05060d02070c0308030f01060909050c030a090311060705041509050d 78
    0x4140c074003d0600e0700b9615005060800c0c140340d617100d81c000300d03024060000720000e100d03480710002d40380480904200c1d1825062240182c407600031200e14008001d00920460036000e818025940000d510561442955031144405031040404443c01042c51050010004451800807480700c0c000099484840906d044d64004581030461040c600d505992514006030b9611402d109062150358800f5181c51030f007043e040402804407014000310702c141807440c0c080c0380315640d105103040c4041e411282c0e00300c801d1400303030240e041a080e0010041c540801240704801d1241c00c1508040002e9241e00421440105804102d50002c0700c0c040d0503007000c803d1003420071181e030903401413000030b002c0c0051900403550707907403581003503442100c03c06c20031050400100130103600714107000040e0215500c10b008070310b422644582113020007800000c186407079614000030700d802280032801814008003512041d10f415603024000ba8400c0c403a0150800351010030b51401407007410014250b1360000c1c039807000d05d113468 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 370066528 1250 370065278 370065307
    0x52817060a02040312140c0706050c0c01081b090d0f05032a0619060b03040c170a1a04032618030703090e0c0c0a03270302100804061b0206010e0603070308 68
    0x36200c000c6c10100400c46940380e400204400402802c0c540e940658407a151b402290400300c00c038405074107104440051001c0031040040c41e04400324080401501d83c00d907003002034000001940d000d40300010740c07040003090010100060000c8400000d0f1050340b03a080188040d405610952a85031a401000100300500d0b01c952000d10022008000880da5648800f04a00154420b54085510440c0c8020802c010402c00901c0c1c98101c1004003d40061a40c948810034503010648004c4c02e02074800d40003608140c007644460740101484c0c50703150b00c00c00c0c100280c3c8100d68000d0740c001022504150409059010010441303c0a590588d10001d4082ca08a42c04281c908090b044101040061000081200c42000b443c101107010380d860a00182108420b6102003a40b0f60301070101500300740092015843d040000d442151141c50b124030385503141d040c02c1008054282c0c0744000802540c100140c516400103030f20341641e030315031082c84017501e03100e041540e258814403000706008414410000c481000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 370067778 1250 370066528 370066547
    0x1403040809150c07140a08060106231c09020301050c190818160303110309010c02130f11040f0504020a020a021905101101050a0e07052817060a02040312 67
    0x18984407400d20f51001c0d00c0c141842e40c140c100000c50005030309405150f01d40f820544c4028445107000c0d004039410003a005080686110f2000d403800c640c4480514100301500442d01028843d00c085070380c050808680c0406003081e075500340d2083d03081c0404150b14203000ca044604008908541e070710580d008002c00c1d40d07840c00090000d03150203c410700c140441034080c0304208000c2d84034030248800340d0030340c078019008290f0f0f250814400d600a1154503446e9811406600d81640c0480303a40da0b65003e100380394005050b10303d1a8488181c182131415110703041000180054072413402602504d50349074030510049001d010f00740001681708000c002d003d4105035a084440d40400300010700c800e0b4541000c1205035400010000c002030202041e0700c142007080c410306802c48a034680922600041901d1140d403000070f0b000305032140408110b04181c61030301c00c2460a480030f00b00340d141089503a40d206c000110303212007149003450081a000603450600c5200320750a481e07000d030801240c010100d10884503107a6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 370069028 1250 370067778 370067809
    0x20c130c0c5007211b0b2203030509060c010f06081e0606060d0c02070e070c030305010e0f0406110403060f0516110d0f0e03030705010e0d03020f031801020f120105011403040809 78
    0x59400c01044404400ca20102402c01e400b1010780d00c803a252041c07c0816185030b5441c00c0d4480c01c4c00d0902c00203501208807075100004660b92611541d120309940d0040c00c07440d80d140b01c0249000c100291014001c030b03010070b10010508400c01084003414036503840d41012621558000c00030041403642a0881d8400c1400304201d10440313000360f44032051401e812000380c1d8100086000b00b41d20404169060003031038023400e6212200e00c40c504001d0110350a170840030740014203654030307034000040d14586003050702c000710341019081c8003070710144140304000c050940e0551a05810300b0a0701c0b0b04c0300c1c01600311407102c09010004103090001894201c54403100c250301030042118484003240c032a5020009000c01320302403070002694400b500700722840e15401c0d0684005150042c008014005910800d4a40c040e9041c000003900c4040c6280c1e10340240321703032000c15119150104a203000c00910b030340341c14140c40003030300c401d19450110700050485000c102c030010f040c0c440c1005000d0340d600b4098248401c20b02c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 370070278 1250 370069028 370069043
    0x1103160212030909150f040204080d080a0e0d1107050904080a030e03070206030f06040b0f0105090d080c070e01060206091501051905030d020c130c0c500721 69
    0x4083c0300055040c060a450b20114100e641000400c1490a010791903e1484201c44c110701d4603140140e12500e501d028800401070040700c0c800150352555541105054200e107030156518286207a10250002a0b607440c1000c3c94454020003107110b082842080b0f0090303070420b44080c01c0c0983c100f411000781100b4070081402d4002840303c2c20040c0c980001540c019451660201403d10740403081c441159555003016116940c0810b103d0003030f90708036085602800c8141e0b00743c20203416900700f01010384a5a2902c983e00d10640100107480300e503590115041c0d4807640e0a80386035407503101240b030340c0d10f03200b503540010b41c01d02c40010411440c0c20f02c1306100c20305d503003500804000e6546000a08182441c8118409a00000c41c8a042440c000800050346504000c04000d850600c800003800f03114985402403000c440d4901400d6100d9500c01d004003450a0f880c1091124015200040b500c090541a500564840e4840840450001043d5403041d1596076422580004001c617901c2d4208101c010305881c1c08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 370071528 1250 370070278 370070287
    0x10f0e06130501060f1202040b0904020a15090506192007090e0f0f010506041d1903120903090303110105150103020a180306020a1e27090c080601110316021203 70
    0x951400340100050480210111b010b030036900500c81a9011102034511810b010410080166200c0c010314095501004c90041310415560040d038440760303660040e0707501501c0414444803005d04a030f83c4c1101d0104540c1e5041d42291200300c204410b11550004081e0703600106018011040e03e68040c1142083e80d404544c10070406501c0d060401e40380100030140399440380100700f41420b140c0205e18154540b030190820740c41b03e401d01c0300d8a503140143e0310901160302514020505210b203d04a07255003200c00204000055840c0182485405110450110f42c503d06651496507043c031802e840f41c40e164881c0c09000120a00450080d0303c01c0380d442040c803a04207280903240d00c250103604042d6204010043e074880c16298007030032402e41c03a150329001c800c0000601a00907403005010010f0032101000550503c422080561414595000a50250f1400782c00c4654203600c440a9801840d080c0c0f5240c241c849c020301d000d07071a84515076594580035844544d08006045c03918181040a0800081e01d080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 370072778 1250 370071528 370071539
    0xd0209010324061d280e0f010f060507021c020621060f150d0207020d060c03020a030507091401080405070305010509030309070b090f0409061d0f010f0e0613050106 72
    0x18148211041d1480082c10308082c0b101d540c01840c841d00703181c50020051314800b040c2000071131407030807040c0f500056480f40003814000f4a00c01001c60190900c0742d4010418070300751032100d01006e400d00c180c040c00c000f0f41c4000181580a481250881a00600118000c0c5482c641c0c04440b8950803504030b0300300904100c500581c01c1005900860250390409101c8281444001c00410747c407020b040d01c2c804d1300f880403004012103101088410804581c000943c5840c1e07940001340c6442c1e803c0354003800103418400c1030840c0a5065000b80003200d2a0f440400583d2500c100403600c9180c0c9019250a007860300d600040b466004004a9078130a1144045945541d145e50b1a01d0a60780159552001944007209105080400f0f002c1030025084000c41982810000e10010782d000c807003840310501855480718200c007480b00940041200343c440c1d2100d0b809008044880b2541c540e19404030210035440c0403075900c800c2c041801200410385140e001020300344c07644030800c403035015071420441b0b00d5960345400140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 370074028 1250 370072778 370072811
    0x30803061201180204140603031b0c0a060e2103030a0f09050a060b24030601030207020d0c0803041e050f010e0a1a030a05070203190f020a020405010915080703080d02090103 76
    0x35030100340720742c1041d044034130510059803c804100a030706800802000b8007a180041030380c0041e41c03a2075050f0304210f51166640e0a00b40001030103500418404404900e0f5034005014044110040c1d400d004550050381000c46084d40034616040250030410200e030050540760000e80c07881c1c0b00c06100003020b0304241d40e81e602e030803850001150700d0703a00c4004241581ca040c044540005024950400641c494030f4502c4845100c010034035411b1613800b05102040d5140e480b55056210750082c111203480381c480e8016503580d00140f0030304000c104000540502c0d000401800021140007904072000e80c0f094000641c1c0402034074031001e800c40151200025500140e4081c04603003c0030300105541c07803c042401c0416240001c00d6401554810000c910350a110b006030992000300b24034040780e041c01c4600c0101d042c655080c030080e5000e0304000010560700d40303c2d4005004080703c156040d0301e07995203546068983d003846c400501038100c10b00501c0714480715078000b480b10f180705141c000b4203500040b45114 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 370075278 1250 370074028 370074041
    0x303050f040e0a0b01080c0a0207150905180109060b0a021c030b0904030c06050c0702010c12090f0b0c0c030d02191a0705030f060906060912191a01050118030803061201 74
    0x5103a500d400b0741c0380185d604a8501c5800c01d081804152501c800403101030758803046480b0303c4561140800e40f611406220304840d038040c0800500c01c554400d040c0c6e001801200f02030042c000340c98580040018a150010700300c4101c0c41040e00038141580ea5640c2e5030118024240072603082c9a22580880759643e12640300c240b241d071090310b41d5144424681040381c11900b005102e5000031104101c8800980e0300301d20080c03103840d4080b049070b0040b0450b50040340c284106034003036120440c5122000c01c0380000036000d401d0190591044501c1282136400f05030b6a5090350303107070380c000d60410702d0b0302c44251856440c0d1321070031802009262012410a001c4d19000300d404c0300d10301c00040020007401340b1208110503894001c030301180c00b0101828688c001440600c1695030aa2244445401d148004a400e0110f0b004141c0401d10503501c0e9215400e1110350b60481c8443c07100020516400810b2942c010743e0f24a0000321203445d00e201b910b0039640c807050558800f40c00c290b4043c544040c1c0410826090103441c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 370076528 1250 370075278 370075291
    0x60305031b0105072102071104060602010e16150503070915050304031b030206060f2103040314071a0d0213090e070602070510030b0109030f0c03140307020a0303050f040e 75
    0x207204030740314260031184082c184000304000150450f100078036181030440d65055000005a440707505142890a041503c03210316001801c0400c0050300b540c06501682a049020090f10b00c403620306e1500c20b5440c103060045008020515020a888034070443c042d65018880e030420a0303840d0349075045042c0613a140d419000c00604c002040008246d8000c01101400107d0001c610f0b20095959001e0b465000c002c1040c0d01030f01c0c903a0000c400c2980c89541c10441400440541202044602c1c03a007034881d0701a0205170781d5024940c265019250340041c4040481c0d02d0102d00c20b0221100801400c610b034001c4444010350740e001c3c0410b0810788120050440102811000080e00010104000e4104820f0b5401042550000c6008026a4490846100b5060190b10300040c002240c2780058441c4070403500003030034102d01440c90b88100441c2002c8001524055200369151a801c070000903501e00c81e40c8002908040c04000820000380a1000b401d60a100000464201030702d070780303a000c12014110350300e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 370077778 1250 370076528 370076557
    0x9081605072c0640050709030506060d150c081812030624120906060a0821040503012a08011d0712020a030e151b030a06030503 56
    0x1040b40003500040c031841440000341c0329900c4603480440321a124402000303103010781145900c0d91042843d07506024107581008202d4241c00d00da00e6408460041c1549000150f10702d4203022465050045e10010200e0354407400600265891000344000c8007003c41080360404141100868000c0c0c60f4080d86060f05d1170356840007440d03d05203142c03400100e122460b054403a000925881034071600701003113076030080e000d1721003040824140040d500e03030580c00b410504102c3c2c00461250702c03001c16000590f0141c4601001c44050391585010019121814416000158091030044031440b071040040540d81d45d24802c0e05050a40c1c1d030700868255000c04083c8400740c050020b03204021005808940801d80440c5410000381d0704280d5042d002030062000124030800401c000350b6180d220301c2a003800610310359025500d65002070070144c0a00143c83c00203d59011340204801000034500c0d4840c0b08400300c02e2000e0004006603180380c4603900c044c114100f5a6290304001c4007081c2c04000030700c48103070121030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 370079028 1250 370077778 370077793
    0x4022106090a0e030f160203060910050f061008100816080616090b16020d080c0f010504030f030f0b030604081902031603050d090b1602100209090103030309081605 72
    0x41001c180d2008110328240c0d4640481680000c80000903100740c91501c0380c17201d60340c0d00d030600925410312410400a50600c180f401300716412201249030010171100d101d0501c455100c0c0200c01c80d90390411180990000114007100a8885c40380110580011000000c0b203c81d54441034214140325001e41810310074102480c081101d440d0812510f980b040c0003070b00810f2405107481004001030547e00c190014200081500e1600f51100000302d9000d95008000880c0000e05281c44650350700180320143c1d290003800302043e58800107018040c89140d240e43d41d440c0c1280d040740107500904081080c1c800380e640c2c8044514036901e0030440240550b029005071510f41000305096126650850350440071034000b4040c42d22254407003d050b84403e5803500f02240c0310001900c9441c0100030381e0101400180441052007240e0450306030b83c0c0a20181d0b0b50a40b80e1041139401740034168410a00d919805c031900e078004101192280d4071080d0203d03c161109807401c0e040c0350074103400c060820000e03100e075049881d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 370080278 1250 370079028 370079041
    0x50111030717130209100905090a1509030206010302060d0e030301080c100c03080604093909020414060a030e060408090f010e060a271d010f03050714040221 69
    0x40e410b200001c00324038102054541080391500710007508500070301a0104c42d0100c0c400c900100707075034409825540010411441d003544c1c810b60f900b04c200702c281c9802200c000d024a94180c0d41c041c641030203070160002e001a03461a402d0001e1948680c401d034081554850490700210701c00c1c0000e5000b4100040141301c40c03403218040020b90003418024100b48100c0340c1c1c00400003908001500e41c800400c07140020780b522641840b10705000c8116128110340000c042c11980c480c4103220703c0d480e030344030007a98040981e100c040d02812440346010b6504020a2070181c0c25540c40c0c41030040084240e0f501d408039035001140034030b5143c040700f910203c0c0c40ca076000c10345508905040700c0201d5500300920703148807800f4417a0081031080c468503804d80c1c20403a4581c1e4142011100e400314140000e1280a8401d0480e0b982d0b0394560009198a42400c0e0070034003000000e501400d400110781525009005046c8291815140d105441614800c90390026000d00a01840030303044983d180703030208920340c1c1d01c03403524015 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 370081528 1250 370080278 370080287
    0x509011d0a0b12070911070209040609050319050714210f04050901180c050f0703080402030109020a0603020408060c090102030a0503071404031a0702010e0606120703060e0115060c02010203091c0501110307 90
    0x403c46c13441c0c0f2100340074050260766070503100b5403c00c6e0003510029141c11181450f90840c4154501d40120342e2100e050b196203580d01000608101e801403100038418105410a1501e61480c1c4441050700c000e00c900700d0802c00c4800004090303184080c1c3d2414507041e540c1020544494090740282100310025905d0050604a4060b46482404c20324100d460312050b030014030390070300030404003404220b45480050215202540400a0381d60002c19101c04c203542c54034020043e52040c003801c20b05d4091040420f00710000700c415540d00f024143c001e18201500b6040031113454000030070220401c050790041a040b045a03800410113540100c41c0f0303003120b0b0002d00c10510b150b4405403011085a14007101302c0e83c803071008646540c010b00f00700c1d00b408050102404c690700d1b02010b604040c1240340b0388400d4095040c1c05502400000d000182c1d501c018960307410056032401c002c00c5001e405038000300030300e019a140ca0404c904007a018030010f0814500b103515003600310750401c0c00d130740d07202e100010a125499030003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 370082778 1250 370081528 370081541
    0x706031b090e040f0828031d03040e1e01060509330a0c05030d151505040911040b2d070c140301021902160509011d0a0b120709 56
    0x60304002050301c1c030700040302c0010301004102910000340400e000b42000410400c4598030a40007840084007900c8208910f0300e01c08421201c00440c0c07502c0c1098541c01802000c1e9403d038044c043c09942000d140200c00d4010110013040c0c81001606111a00b1490000c80da01c540603201d59500c0b81d480310301c06c0f014888411003c0010380e40220345c101080004120031a803003203017140c29860090300e0707100c009419500041d84242c0107205003c00305040701d0725034490348043e05031420a8500000ca540c1d484e40c00c014040401004000544200400e0144503c19048900b83c00c0c202401140b030169680b50f000d0380340d00300c285103100790303250500751041d4540316000c40d4131508401943e40389000c160303a486500c1000c2504c9000030144005400255a036030a60641c2d101d003913080301007100b4200301e00000b504d03040d080301a0340200070b9018020800381800c0c010507060383c180d07100c041d103802d4040488500b20540108810710301c076202d02e80381c80d60b51114507619620a003104010680c007800c041e11a020f6609 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 370084028 1250 370082778 370082831
    0xb090406081902040f0b0f040b150417010c05031e04050c101106011e03020904080d090b07030e03030601051b0a0c06050d0b030a120507061415040506040c0926070603 73
    0xf0503080410030fa880701240c0c01c050504540001c0e4a003507031400b090740d1041c60307404249043c42c04540033410a807a14842d2009492040003041403a408a03801d85e03041c00141c2d008043c10030780348100c171040c004070007941c0d400c02d01800450310b104456130000340501c00307101810000580c050500649203c4200440c502610304980c1107402d42860f803c000c0380c01e1042b840064881c01d01600880c0074804044100d0710400740010084c440c1c96a03d040003049a20b003604d480001030315114400c2501817010050760b01070744050b51039601d410350203a01000c03010803000748000719010b230f950960001600540d5680033050551100d58440740142e40840071504400045400390700115403400c0003400c156442400c0703003614140192520000c0c18444002d0006920000000b080c0809200300c4000c186d42e85200d0480440302401103541d410144019590030043d48008602142018051054804244a81683c84046201e00a64a001c000f490020f141c3e0094012a03564003080001c4501c00404013003008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 370085278 1250 370084028 370084031
    0x2306070e0315010e0c07030302090406090606180f0302130e1006080c090408071209030507030c051516030509060f0d1d0a0b0c0a051908010501110111040b090406081902040f 76
    0x10302d03084c0d0310380c4450f0009000c141428000121002003500950665440020142041203000d032621410310040009004600218007500e440502102c1c00500110a85800700b90351100b0914650901c064112195400190306441b010003542810003004150b908514540012072a54a00142e0790305100d02101d130540280c0b406810000400e910b20103e4102aa0001d8040101072400703400321203040740c40c0c200074000c1c020b00c000042402403518041c000d1791070844403080b480c040095191410300c03031804520182604041c461000c00d000d14091b00350910b0141003c3d00c1c0c294109170303450355948100442d11560f5521083c1c078040900c14074012015102c00c0b001086c2441d02a140d0345004000100740300725a50000030244030342c4c1d01c1501907405820b10f162007450310420f000005800b0510902595001a10082104c41200014080c5a0300a81c00140702403809044c421102400da20074090503802c02c4e207900c3c0014490713108210102c642803030031011004c500c2e10341c410801a10341e075449054070325 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 370086528 1250 370085278 370085281
    0x3110102010228090305070608251b050705060d05090f0a0206070b0405100606030b10030c3204060801090c2a0611180123072306070e0315 61
    0x209501004041c1e02c2070100e03010a0000c000c40c3c0100d5040d50980c00080540c0140f000014010f03800068a60042020035900b08408003680c46800100250f050002d000400c080f4825038502141042003050030300a5041d00c04e025290004030316564441043c00c0000c03580c0b00200110848207118890800e030714000600460341060700010003038000d005014102071142800b00c4c040081c1044601208080b0003000c0c04100e070344003c0a8000d00d14050114001c400b8000c003100090f21034440d600440c41c2c10f440f0f01549000700500c852a0b00d20785994090000c040b4480c10040581840141c002000d0075641e8071113543c1400101016201c00035810070501c40004480c2035800c1c0000e0325005030801c041c600c5000d610702c0d420000c024248800d070003100f0041c0002c041030348075185601699440800e8070f1300c2da00d115802c40000783d80d00c0c1c0513000400c1e2100a001c1c810010708580d0403200da8401680d0801d90a0900020305070400d0000c0e01d8507008690114030604e00317401d00740481e04c006d886441809409 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 370087778 1250 370086528 370086547
    0x1061a04080705042309071a0d1b0f0e040b041d07090203010806070804051903081e0108031e1c091104020a020d030203071704050c0306010e0106020c0402070201050c0610031101020102 81
    0x40c052180303c1c0e1401c5000701d60005103011000c102c3c02c40140210907511401c17942c0500c0044140d8080344058270100d050203142550f03001440d03020419140c481d81c921b41c15102003070381102c003542c0008144d54015100c01d80c0400a640d0fa0142d00903100b002210000b0411f45103040a2601900303a001d100601d0051004000c0c40c080401c80e17541c405194100032602e0340d10340c68103c0c28542e942141c84855240000c10105040d400700213641b0509407032540c040013940d01c102207100c0b0b9070240700d88803940e0306c01c000072840f04020b00141032842011850b01e0742404250403084542031401400901480d0346e070200102030242c0080704046809099404503c1d0010055000b900c23403804910362410705070008007081c40ca41c890741401862075071070741c4543d16030304141c9003464840c030011080034400d11034200003160007442da82985048610540007090f0010000c81800042c0d040544140d041c000c0501c8095442041840391078810364a10521200003419460000502000c15501c0c9045a00c1030150648 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 370089028 1250 370087778 370087811
    0x305092107030e19080712051b0105070503070317240f0a05040204030b0f0603072102180112140c010207030308040606031a0a060909020901031401061a0408070504 72
    0x10342a08014000c0d07a500041c20155503d4a038500400d0f044107443d40f001d80301d408010301000a81d11100107890489588420f02d00306000c040f82c0c054030903009813a40ea4031040c24007596101c081410304010b0b0034409203440705810758003c4081580400da82d40a500740d00e2090441c0158030401780311594200c0d41062241084040300e4041140c01801403110355102603071140c80840051400038000c0d035403151240f9156444072400e544103940303a10741038041042498081107070400d584207240c0a010703070907098054400e4a6510b050590300315215a8240840312091000c1d90301134141984254481c0509180100070988441d1700b00c0582e0b0031070100901e00780c1e404a1102d04aa42603e040079058a903414a18010320310780e0301c01040ca00c01c0106284141c0e1001d01c009116150030001084560f60f1042c20f402a50b0b46508003c5d80640550300500c005861005010045c4000a00020b94103464400b20400c40341440c400051440002c503041280f52010064100646420754051200140417082440f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 370090278 1250 370089028 370089073
    0x308181915061a07110604050904080f1c0912080103030e150d0c0305040326060105030a021e0408100e0304060509060f031f06020a1101080615070b0106030509 70
    0x200000601511407104035041d070840d401901200c95000c0400b40c804103c0207003a80008011905c40c09032000106140c58140161006c44a010380800d0703495840740c2e5084816808000d02e081140420301140343c0d540d1507081144070b403562202c000a806a03c3c0d0070009051074446643d0030407c03101c0c100520000b644080044809442071310b1200034070702c25076889a840d0160f024000c114910345003206802c0c5a0540120703000e54040c0e100c0425060103808501040c0c840010101001c400d100041591035204070700560340301121100060070301c85240314100c5051110224048900300101341030019000610103043c090580c45410041500030144090f140d0081c0e100341c4c0140000400c2c020700c00d498405c100e0302c1081c8404500d55032458000c4581c6003050b4801407840e07038860f110b00e010034940d000040320035074aa00001402074084040d001182c032410020107280c3c002640c100c65950080d0100050145039204802000c1a5170400300c0040484100410030031450b402501d61486900c2d80081c0c18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 370091528 1250 370090278 370090283
    0xf0203010614130e181002090916050406080c220e0a0209030a23332e050d240606050301090504061104090b040e01150e041e03081819 59
    0x85031768100c01000d400703002500d030380d0003409a0f810086c1080b05540c000c0409000407182114240c6440c0c04d85d41d99074a44640200115030100024403460303002c0c840142c2c4c021403034000c4510b0100a03000410160611000c18041150451014807a4104464070a0b9004041c043e08604101c41140040c1d682c240701d0202a00f000141207110704031074034403801103075680402c00807201d80da4400d501c1040b8201445090700380407481c2c0004c04c000696103c1105000f40050b1400c44510418032038400030011002e0f040f0034448a004000085076110b03041c05009560207002d58202030141c40310b01c2c3c2c0040c0c0f00354034400281450242c05006650b0408207881c150f03800704200090039902d0b0301d007003001003103020303214030f81c009003c24001411002d541000c0d81d6604e00391002d005080c02c52060f60700380c0d07130200c6210748030503107214003400201640211283e0183c09030344283c0003c031415008200c2c03440c4082007a03001401882c04c000403940c4e0244e842992106c824010140c6a44880a20b0110340802500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 370092778 1250 370091528 370091549
    0x306060a1b06020703090e060901030c05040b01120c0f0813020907050d0b0406122105031303260f011706220c060819050603031213060f020301061413 66
    0x920540c00100009641880d4400070865031204c481c01c024003940a9442081c2840c0c501d1800240941026140ca40c100e0341c0c45180b00824a06090070031001d0b101c00c8665a04000000c071251502c2c42c410300951404044584502503040d00600008100c040028012a48111500280c1005807103c2100c42e5021840f40f9213151a01249001c1c003014001c1302122940c4241092004036600708500344001003039105003800d525108219600307640c500305000d50300740461410b000151041c030b484040202010b00c43d2400803204c8100310115140746c200e00040c0600300e01e0010420040030140c040007809044080159880e42d41a90324581d0b071041d00401698039020b101092003464094007004032a0f00b40c2c04881c1d090103644420000700382c0b400c1242d1103420141c000e444210007105a00c1490b003c0c01002c0e0107035103005c0703016808160684000d400a1401d181b6a4001000306909106640c070460004002583e0780d490024010107450700c0000c0e80c82c01c21400c000c201d0030030b03140300100c40480340381a64 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 370094028 1250 370092778 370092797
    0x2e02070c091d0601030302070501031d060f0703200417030708070618120f0f030e060f0c0f0c0a06060e060609090c0409020a0c0501050f010e04030e040b121c050306060a 74
    0x2580d100c40007450b001d1074902d2150400102c101a000301d4510255842a80c0800203c81d15010070f80c5206044031002c409070b007110010031051580401d441d03910204600340400e652810200c05507112000084c41d00031084046818460164038418440082070210021420000c0c503444041980c414a80001c0196944003c042ca9145040035074403006500000914800c980c03516000c0d00800d800140000000c00305864002c41a00a100e01003a12810800a0000c2c1d13403800042000d500d0003410a203071122044c0301c082c5a13641c0010042c403541c5040c03006800c1c43c4103207141c400b040c1c0d85c05400014400c0700b01c0d000c01c030b0280c5548003501c0c1c5110341200d2030b90a9468040d182d4209100382d030000c1000703500001e480303400907402c04010f00103103200384020000b0303a94a1240c259505028020007803210300c17243c041004a8800c40c02100403100061002645050b1040010000c410030a85207109030041c0702c2070303050303541c00700502207a8a48508005146180002c0050345a100e00262101030185401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 370095278 1250 370094028 370094051
    0x18060f0d03141e03090303150a080d030b031005180f06060d080d14010605041a0a0206180705031501081902150a020a0f0807050601060c020105090915032e02070c09 72
    0x150b40402c843c01803403456030780c100305c0c03145031b182d51044514820000302c9550300e00f41810280040411103000e04050815190000320881c05092412005580762284800074820044640310b16401911a81d89280c2e0901450105900380800710f40040c505400090400845032070f400300b001e203180d60025038584d540c60b4201200c4001c1101060300c0e0824144000042030441d0013170010025074210441c2908090111840c4d03100038490315490b00d0058020300007165038165591034600e1011600003d95100a4451340420300d001d070b0345041421130145080042002071800d1281d03c2480c00e4039004c41142e401da54000c00c4036070b0300204000114800015803401164401d00c41218030f194005501d04d44090749003441c524076000400d00341d44602a2900000d07071140541c0204010759410b85a00d03040c0082c41040201000c001400101d040c000d5000c1d90b4115038081c030250300e0101c00150f5842801e01807411280718000ca0340701805407148104000c07008070b584020014110351002001044000121 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 370096528 1250 370095278 370095307
    0x3060c0a1817010b0603160e13140612160501051317010903090f060c0803060d0f0506040b0c131e030507060302030726040204091118060f0d0314 64
    0x603054840101d10000010442049411801c41149a090001e010703d140718000c00c1280d10095900c100d000003011341020fa0517000c1c134410f2600721001441405888110305c00741094840c403182401ca08130201c801c00006203024404604404c452a004180c00281d80c0c0c01d00401d185580192030500c40f004c90040350304e914550704003015181642034601004150307225a030203004280c0045011a081940208032034140321264001c464090b078400c0380f941039070348074080654405000e06400501251040300490290384003014043e100320018904c2d4901410300d8034587e4805011050065001c002d88a40741d10112555000d035010005c013203140913940281b2142d0742129500050150040060020b00c40e50140e000d18820040340d1228902c08401110003c0138260104d0f020000b010f013600428058101a070280b800c4c0c901c00d20902c441451007200080c5118000040c1a508840700350400185060030465072502c0700090720317070800f907402c9960042d148840c41070700d09141d0403020580740c403402c598 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 370097778 1250 370096528 370096547
    0x612050c040906180b0103060e060609010b0a090b0406080603070603020301080a08181c0b01080d210b0613030c0503030c06130c0504090309092f09010c050d030e160503060c0a 77
    0x520060f154180600d001c00045c90709100564240c1d00d0030000750520760010607130700e12905000344142d81c142e007025001e01c00d0782c1000401d0340c2004001680459100c41480040015004e1a118007001c0c3c03901804240c5401c03032541049082600510040001030301c00180d62580940c0001855100d40e0303018620451a0400828541c0c08201d02c04100d83d1036a2109507990b240f4040d4580340c40c240e890704182517490866600940000e01d0840281401c0500e1420f510030003910080041050310110000500c1c98000542200c50036286410410421056181d040c1c01481c05401a5041503c106176082d143c4000810309010501b4440790030341000013254280c800b410004008011141060500402c2c200d00f5000311003172145040700100c3c0300a040001c581e01c1003030901c01c55414038141d01085110340c0008110f00e0501030b0400b150400200280125001c0010550b000950f81c44031070050703442c024002d9080015000300c0c4500f8890ba0b20086442039201d03501c4c6400c1507541140c0b45c07044810303069 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 370099028 1250 370097778 370097801
    0xc05010323070302032703091e090103030f0f03110403060b1203070c0627090b120f0604051515090601120c111c05040e041707060f0612050c040906 65
    0x701c1c0c108107040b034059000c0d60240190f0242c0d03010000c2a62041c0c481c17482d0b0014402640c2d4030600c41911145044a020214500c1100122408001e00001b151703003135000382c100300e001c280110154048158040240c2c00c1175441c1d0315082c4a83c0b140705030842d50314412400041c041300e4940c1c05400c9140c80f40038244048030020303c00c0303990351401418521580c00290042d1000074a14041507a4084030300d140381107145661344c41000c1c00d070340740c201035000520740c0d5600b8980110402c01441d40c09135042c4608a503410502001d804245040d1401b80c3c140b0210b0f0b031404a96201c0300c130a2061829013070001c50110613041e40e40c21351580340d440040e64110802c8200650643c18400c42c103038001d52290024003071780b4501d42107405e0b403084540421960100081d50f44000348003440104812401d04503a00c0e04107004003064941c0c0541ca0080360a039034401101550301c0340c1c4604d1501e0700c04480d84654002050501d42400340c80c41701e55906901d0700200e0400520444d00c59500b00180502680003016410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 370100278 1250 370099028 370099091
    0x14030c130e010308070210050903030a230d0e07060f02031b280b070503070e040b06041706010e13031205061504060c020316060f0f020a050d2a0c050103 67
    0x103030f4924251100b41d00440303007207014503111003480d01424018820f0790040c00004000e1410550990000c031190028410203c2e88086010341d000c1041c1c6100c0c005164580440001160508cd01201d661605036283c0c00b5200f00803c44c883c400410342d0200c00e580701d03061310b4241c247d281c1489426952501d240c005008210403e800317460381c0010b440000e42c113126407140d1407070074241d41c070800155034500044a080000c28507180c5102c2d15440c00760701001040100a200ea03052540f252004180302803920010a0984d0000005010301d005020703449034040d080c2b64280d2101c10320303a42d0040c80d80b41204003601405071150701162442da10003440c0300e01d46406814880e151595044018860700351180241c2c000e0180c0b00c001c200d00744a4610480a0b02c3d441d4461076181f420460b800c86215512040d40e000b14003030606140000740c018403d444240c0c00c42d603528007500d240c2c203812400c0c0400d904191200c482540c2081c4000550480400c4200c440900b40000c3e10721036020100d202154203e212030184 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 370101528 1250 370100278 370100281
    0x20a02060c0f1b130b090109020a0309060c03020702031e030f031302040908090a0f080c060903030d0510030b1f090e030c01020c0106060e060301080318281514030c130e 74
    0x3000e1511181400811a01040340c11008410101280c2c84054215081b4500d0001445450130507001068600700300d1400083c2410b2a8907440100d40d83d0901030720010390001040001c0d0f140070007581800d036180030411201c80d80110f00032940c0344101788180c0106040400045c0c01c08160b016501300c11500a00b00b4081d2400c0c4d4a0108090b0b0710240a603032150600c03400118100071140d80c1407003592a000003e0038181c00e890300f008802d401c002c81440c0e01d03110401091969800b039000f400e000e8003818101d20355032421841d0001c1d10010003003503148007015032100000380481610300c0300100c845800e00001d100c0110101e0500758410480704080960001034000c40000055100c01d0840d880d543d5908024590340e800c22015100030b2142d20100c0d40b00307120b6042407038040768820420a00040c40c52030200814110071700ca24400518000703090400900801003503540349510441e0102e646028504081041c10104050002526840c0c2c18080440c507040038040010301c5001400f130340d81401e4038a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 370102778 1250 370101528 370101553
    0x403031d031902060901110412020f1f0f050903100e102c01110403082b091208010f18020d020408031309020306060a0804210f08010f06020a02060c0f 66
    0x641c0b0300c254a00c4010b104400c00030390300890610815078080b401201d124178042c50110115602c1300f40340403d90b0312181ca9003040c80a543c613056101c0041d500c00003a4004400390007c050001485a01080c09200d0100080e50842d50003084a0142c3e403e0400006071426620541e00d1510b02040360b40058113161005803030381941800c02c03409881090000c0d0011040b51024174070b0a0b62890b802c40342c841c1d88240810b000180c2070201a151020345420a84001560100918501300208140c100e145a84455000c01c0c45440d40c40c50010f10a1403e01c940b055141c940038101103078492041503806401c1280c072116001c0250101d0300a1350b0004801e40d191601e0724511030302d030752000d10250708036156840002a80807450007a00d2040c68003e00c003900341300d1991015150054020411030309100c0324649401c1c00c02004e0452400c1c00a40da0740c0c1010000b46210142c01e0a00c10703000040125003a002c1002000e600041076075256a042d655170b42c440d503d41c0c500c0703807030010b012058840c140103074100c802c0d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 370104028 1250 370102778 370102807
    0x905031b070506090315092104032006031b1306030b130e0d0309060207060c18050a05030307170c06041101260c0a170406021b150403031d03 62
    0x35030442403015900400d81d1a07007007021521500ea40e40c1e405402c8034544001c0e40100d19039890b071184140058410b00100c00c0042185442e803d46001120100880c040c001e010801a410380120032840760100040c0105000a00b1390100030301500126050130000740300300440c030b400d6444c044203030619844440d40b10034018001c5c24031003d4003030041744613a20300c600c03c205a0190580d010380403800740c03d018001c0c503800c1700130302a107040a039031a907020401c22f40014443d00c0b521200800550301c1142070303d41e01180c0c0e04c00d0700907580054880c00d0904424804c82d503010017100c0030a640314005000c900071002a000182c054128014014002c070010403007405104004e48950680c00d81c3c5030a01d880d4000c0d0504958214019464520301c58000041c5900d1005c800600b100b88940c244081c0859080304110b0f0741040445040300c020703402141000c030003200254082030050445c0054002c40000884459000b200100b028042585407680000e80000403100301e0349290141040e43d956404c080440381 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 370105278 1250 370104028 370104067
    0x40f120c090b0a1a0a030c0206040807110109050907230c03180d0210091d0411011101020d06060c050f0307030f032301241805010c05030c030310080f03130e0901090503 74
    0x404203003000c1f50030020070f10200b07029204640c0101b03100d007800842e44525010324000b0f08250b0601c2191031001c687c0750344886070309208100300c2d510b039142801d1884100341d4024610744000d01040c0d007480903010041011060b6800000a40c501c5001e080f030841c006a11000c1030f040280d040b4107103200800c4c0e0a0707400300c40403040d0703176071410010442102003041c0f682002044801424038840c101d46540b481d031152607031001e134405401c00941842e007120007440440707440398004004070309140030365030130048244140700b0101040c4026604042c4140c8015000040260002040564446198400b050340464849404440f44802c070481d6842d20502c40403103c0601d04054010f034014003050020f44280079071014040c080540762540d07490000150783c40c522110007110140002e0001e08903080040003c4c42c407540f042d0521071a01c3e840c0001d41810b004103241c085105420410185201942c803010201c01c440f1903401025556950419050052507100801010341c000000c658403010548043e41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 370106528 1250 370105278 370105297
    0x216080a1e2307141806210c0111010501060f18030605010603060314010905330702071a0a021c03090606091a0103061202061b06010b040f120c090b0a1a 67
    0x280c8a49495901103e004c082d124402d580c4800300c0407000513004804030710190400c8000d00030341603201c80b02128a5020b40c02000102da141d00844c40150a580c4c0088100c00158400c4020801941080c2000344034031041d040c50424803000c4080300c0c1c075842041307908000440d04090104201e5071601c034020060049440f064610381580c1c3d81c0c3c0011460103100c1c480c400c0d54010001c03c85546040302250b500c1da6000000d41d14580d24036448030040e802405c0903840741c18203138050710700941032004c49554541844d00d0012051418400007404980000b4003522401006561014041820404030082c1c41d100d0002041c26080000004030f014094000c052522001003580b810403042c0700044086070418030404010f90f0380000c00d0009420a00000e20b441d2603148105d01001c02080c4140381340c414280d1103161944400070302004911f040105800142884900020000046449000210605000b02d520307455546021000568030018071400030200e003d8050341540c0d64980c001115003060050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 370107778 1250 370106528 370106533
    0xc030c0c0803041403011401030204050720011d03120112060227030706230315030a0312050f040302061b0d150f0b091c06020f0c0105070216080a1e23 66
    0x790720307171a042c003491004809504042c1041d030310b150204000b620026010700d080c00450b00b203a8401401000f80c02051510300800450010345164100403080b890104650513030f007062080801486001c1121070444003030083c0b03800c9913169418400020700c00d0740d9504a42c1900c40c90505886203403c40c002040410442c1620340315660b0b40401e844821000f1150342d0664500a20007040e0300228003c1e580101c000c10403200d8204010b4040781c58a801e146095001c43c00f804000c54940c0c0b850302400360720000c040780700c0d010b0741030603613019540d8a00034010324060040e400c00c555100c10b01c1400d54003075440c2d400e810700900055910142c0140081e01440f07145182081c004a6500d05010454440c28005061819032112180d0641600791400340200d032040d80800011b00030ba5250030180c01c0d00b02d4600f00000741800c00c104083e04c0c082c1c08154081c80d00d10b000d28104220302010641000c2d20303030004544005c0c0c0700302144050707455101c000300030b25040130302c00120f19000d29584444801200c3e83c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 370109028 1250 370107778 370107809
    0x4050d080c0a081902040308120a09230f1b040515011b080c0102030421020d0206160c05060108060907080303130212010906050406020a0306050609060a0c030c0c080304 74
    0x14129400003044440c824a07940c2001805415440381143c43e901c0007080c0400100180105042026a03025600076200c074000402d025a80b039500042d602e4100950407000c00000840f41c0d03a4294040c80c0083c11421003555414081e182c2ca070030b000481c042d01d0312505482180100f00100d012410700004070901513031074a00000c1d0065154100b68001880503118544050315022810387c201c20400c50031175070b0071410b02210228007400d0024602841c41114031752100302e0340740d8564034090340c2d4580090865210301c2000040c507070003052050300500d55420301920710003eaa000d0340c103813401d04401026403060400005d00b0860210b14940100c140310240c0710000d030356502503540c0740070170b0302c46c442c12581051050300145880f84540a0004100f00040b071842c0780c584898040721022901500c40c1c42d000a4150501a8944200b41c040c0030225600d40c1030074010004203695014480030b090510410348070000a0502031000c240f202e0b03601501c0c40355802d489403011516a0400c1c0b003051000030f05e080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 370110278 1250 370109028 370109053
    0xa020d0c0e0d081b0d081e06130b0a080a200108191d0d0c0605070903080f0c0c10020d0905181501030f020c03090901090506031f0b040507080405 64
    0x6049624020020b044034018002915500c8040d0301400c0d6508014640c00580800714909000c91011543c07607444440240c034092218554922074071f0710054001460108004075680c034070141031003140c10b10070001a41002305000c28204003682d0032100d00c510540328000108107900900500141010041400c544296001903ca200c010fa03848408030302c442e40c100b403a441c6554081c464940100c400e0601d044421a00e8608010807650b0410004d051041148188221800791a401020350b241641c0140d05e10f46400503180540280e55a0210000902ca001c2500c00c000361242c00100619071020850110000f0b9610405040e02d00003141c02108005282e25141d0400d010620551000ca444c030b41d00d207410078440340822444a814140e880c07208102851403840a080d0303000f6503000855441140f0003c001c3c5040741640200c1c0e129041c901001415113001c11410b403078800c1c200014490b0340000b07020001510400c50342a40081c617100821070b10a80c400c07481c600646c0140151007035545040d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 370111528 1250 370110278 370110287
    0x803100e04020904030c050a0b070c030314060a14060903010c0504090e01061202041d030417120c0d080408090603040c060807021630060510080f070902030403170a020d0c 75
    0x100c4002e9402840300d4006800b00b8020007209042d21301c658140c50343d0010030740d40d60341850f400381c2d035610000e070b40c11444404158040c400e040b80012400c03070324602442c040000034040a018000c03802c824514071060030780c030744407003066801a03800100240007000000703000915640051280c84215820a601292403010605c00e090694084581e1039200d00415028000a8030800a146a10700c5581040c1d50800c2e00510141c0090440003890031070030740341da0403440d10305402404050070460003040035001d00c080c00601c1440e03002d240d0900108950b6507041c00c52a50141060154100364008108800c020368070029205807155a01c99044584841e40d0490755103001202c07010f1440200358080c451190040d5210300700815401c0c040289040740c050381c01143c15100011504c3c00d4030340c2d0602240c2100030b0015030182c00080c004014450041e072540e40d1b640020321401d11175660010100303082c1071250b0b010074481e003101c90000c0c50500344200002d0080d400040d02c210500e18011120441d20300c038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 370112778 1250 370111528 370111531
    0x150228120306080d0813121d0a0f05101e1205150d24020c01020918190506121e0712150e030c0601060f080708010819020310090803100e 60
    0x3110020a10944c50003070644801001520b503621098001401100050080f103115808040c80d80d140702c8003500c090003480c1c2010802c0000c07885003020b10300910202c0b203019049012250110b8040d860300790310780d5082d1580b074500d241141c180391305120040c1d902c0350456840c010020071131004118903520b010b405a80c01d000804000d03440303101996000c0c00b00d200000444401c50703041030800e80303000d0310080c588104c0e840810061307410394012682d41c0301494200601c2d6005902c1d01d204400d24600b42c03106105840f41030000c01c0d802d9503102c002c100b20b074071110003150101c1e0442e0101c45400066940325030702102104040380032440307001c0022078040018880c0503040756101c8003440e00701130042820b00107400d212401e00d40d140300c140010a007031038041000034000d200780d4442c500e400455100041090900800b4001800341010040084200001e60240d01140315007007d442d0504500c0000d0824000c2ca500c4480305d418051f40c20b040c0300300640117501402e00480800c000c29650540088940300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 370114028 1250 370112778 370112789
    0x7030209030c130605060d06050405060a03050a0b041a040302030d0b0406060509090a0b0a030b0405061b0909060109090507090810060e1b04030b0109020403020907020115150228120306 81
    0x100c25860030b1810182100310344040b40d180c000c10300c5501c03400402d020780c010034030030034400381c90b000c04002508280c40f9185d0843c006807101c41149056841d847ea64040c920001001d180c5c03a000041e085c0302c0c07844100850600046003004007801d15080003941c070b0b00700144883786140780811126040c0780c00c3c80f0308001c482c0252640c42c01c7c500c003d002c000341c0c00001001080c1d05a202d080640701030340e40c5d580380d0001d03501c142004d524504050500e145001801426403185580022400454024000a941007124115045169a070b29200121003507400f07a8014440d007418101804915608405d0b4030090703e0447d02142e9400d440b04840000383e4507a07120313100500d0400e00104200303800880580880c801040036141ca042d944e5078038580040d609900000e03440d41c4c00301e02842149491604240c00c43d080c0d2009220744000c0351004040c6564a00c5603054400f00042c0d003640440c02404488800700208030050700e0410300d207801402e20306140b02d08585800303440c4145041c1da80a4840d0805441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 370115278 1250 370114028 370114033
    0x1030f05011a280807091d0109020a0b09060d14010602011a06031b0403120302040f09021305010516050307053f070c050904230109020d0816020d08120703020903 71
    0x210140e03095074040d45262100b944983c421101055203001009010000c0c440f0640025113042c076840c406652917028182000c1e0b0307034100348030340300540d48000141c0d06560f918a41c5903690080310002440510440f002009001d05141c0d5100c0b1200342c1a01c1903040b198117400034044000b102e440d0240c0284907007103660384400f01784082030003030b241482641e41012648081382d1a154503500c8861010715940c040200003900090244031191002e04203200a114181d020b6080c8002100004003844060188604000e008917000303500201c4603a110050a4011056954402c0941007254480e0558000d02d1000750f80708180c1444002840042c020141d00e0320041002c9080907001001c480d4480342d820f03920b4020f0382901054a9960b44c18182c01144030f0744a403640350040744c0c4034854858409102280c964986810b88000d61200c41d0b1665840e0385c00030100c0d0362610700300e40521020380180d070041d4000c40805c14410421000300c000b800486504c516039200c607950300200301c4c26845201c081c1605034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 370116528 1250 370115278 370115299
    0x3308061302090c0d1103010321081e09030f04030c05040c0503060105030a230f0601030c09080a0807140d051209190b0621100f02040602120711030601030f05011a 71
    0x1040d800001c1c00c040d03920198089840c0343ea03501c100060f60003c0e002078900100400309c264035843c20a0340b445503a2a117041c02c1805142c091582c1c403000e42c0d01ca550303100040e0030301e00040502c8424401c88801089c10071407292160303182c1c20b04c80d64001c5980500c03030280c0d142881c55521b050046094070b20801c41650f03164519511400102d01030402040ca00c4106a06542a038544040290401e80700d960700c1c3c0b03018041071030b2410004054a080d1040350092103840501842401c01c0400d44003545900700c1078a941c0ca807864903000708114012450035140d8001e000014071600e510100401c00003084458001d000d40703c0d80c41154a81800c010300900c5050795000040c001864042090380c0720800400c030100d05901c0c03500500700d44d142c0345046406a0010102c00b04070b208644030300300780d0103000d0760210306181c10804043e503500b03000406031110140c08070348401002a842e01084410b000a02507801d256502d243c010321100c03084604460b9542000c45450b500e42c0d402c032403020f00400040245802 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 370117778 1250 370116528 370116541
    0x10090b011409041707050102070b0f070c0c060f1404091b090f0e09010e07090501061701030b060f0a030c060216050907021b0616080316050a05040306330806130209 72
    0x302d00c03503101d29400940034031407400810001e08c00303001010b008400210141c58a601000c2031568010701c54014030030f40074580740104103c1032108050b030b03101f4106140c00442c1214203607054000300800550071784000901041c2e4a0701da811000400003c202c003401946071403a070543e1b0200c2e5500075260f00407072080c820020390620345051a007005c6200c0000525114140c011414042507411041d08c4035112401085000e500488940c00b05003001181c80041d41547e549041010000e800d44c0d2050321a40424070036a540c40391440300441c1d005010040301a616107004c0d440c0e22581460f1f421442c040080044e0b14200300000238840c1c01c2a5025000c5881e482005101075100e44d099640c10400900600411551060b8003002c080d0007072880c1c2e5164580003048908440c4078407407140401c007060200001c6280c11005890076250720250104525801d5520a102014604040414551030b0440e8031855144000c00009440c40b80c0240c96a66030b424404d1484807014100017500b2940c05400510b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 370119028 1250 370117778 370117793
    0x317040602190602040e040f020f010c030e210a050c010306090c0c02010f030b03240a060609060e130c0503040311120d02070503090303041526010b0706060810090b01140904 76
    0x940901c5183c00505094542502c54160202118115103ea618400e024150f2a010b803550140340024079000c0402109aa002402c030300c03900344000d0191240b01610507071010065a1500c2e0b41c484c21007112003041c0c05003005562040d40c458820f02013450310704041030100c40c6019200c8030304100d4407458610b08140d8011610300302030b030480d072040503a908000348081c0d9050294403400c2000025044602c2071030407112140c81000382c141215141b406c1410481c8a4002010200311103460400c001004082004140b000d000e1a01d582c5980e440c1c500385c81d44d40340e0844051809140655103d0f51020010305000341d480f66902c0f000da6202005100307840ba0350450f03400400c00a4801c40070340341041104c2000c40d00d15001600410042030800518503a41e540c001a40304c4024060707102281e5801c084d000c1503403000418000c2c507506040000e10181404001d81280c0000c080d0741046649a00031080d00b0401411818000c40b2101d42d82c0c00000380c140e0100c00642400407005000070140e444030781e00c030304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 370120278 1250 370119028 370119073
    0x6030d05040b09040609060902041815050909010905011805060f04050c13110406050715020f0313050a05121e0909070c03110102040320010c03020a1b0e0c040317040602 74
    0x4c0d442903d17900040b4403204c0034000c00e40204a00103001d61618140700d4400e96501c0d20580e200301ea1450840100b141040d0500c0e030600306c400580d6181d5041e2500c00c00380d80900010400a80740390b0030a1100e50f8010000403a07402554000c40c291070080e00d8010182000040640c4d0161841d0b0204202052034584100030f40700080d01c03140d0001c1c00c0c52100d05403a2550b000faa00100c0420030104403c003e02c29011038114503000e540710118070704444031101154901014140c45030b0b048040c00c2c0d041c20400108240108590050f003214240140c000030740e5a0f950204490f0001503114110680035a4030100c00e944000318010030300c4c011079882c03500840f000c001941d415000c0042107609980300d2042840100051406040491151030042040e98202501d51070000c0c10001c1500704900420343c003140c0816410303401102000450b01120580b074510f001034100c10103132260784040c4810255003e0083c821240300e0320003e003404c0c040e86080401801035100340ca01513002031841100c503906074031401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 370121528 1250 370120278 370120297
    0x1201050906070f050c06010f050a241d092e05030c0f040213090203040c12030c030c06110d051f030c0e0907150f110607200a050d02100506030d05040b 66
    0x10385c00c140740175495616014081c0e0200c414800c0c40e26050040d030810310300560250040071002281a03072240380e84240500190b900300f080092042562076005240081506111401410107403207040448003000660030b0f82c41080e150481007020044c05a618954100896070010007401c00400c40c4424404400c400212a55100d50308202401c50412941c40513005810500300058803881c1600e805403440e82d4603000300f05038180001d85100026031001940002c1541460081c1d4164007c0c68018090448840200103071030004c600203544250641c001ca10490fa21881149440c1c0448081c8002c64890b01014042d41e0010006001c20001c48540381d8000404d2012074140590b0390000d6842c00d440c040c0180001a0101c02b08082e0f50383c0030b0710740a440c80c0c00c000600214200800d0182801c6e135207440c2180170324a4001c080a95038810b000590071503030050700383c80210706040c0000307480d82503510088011f145050080751042c1400500c00302c1d00089030300e45500c0e041c184003001a583e0071a4828 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 370122778 1250 370121528 370121537
    0x3020616020d0b041208010308090105211603180206030606070807020a0e0718050a14010e0a06030203090f0c091512161d04110405130611091201050906070f 69
    0x520042e2501c00080855900461201c5100d080030719000440c0c0c2c001d043e0403002c10002400602c0400da040b011558550790908000740e442143c61035003c0c4201e880a0700d07805d00500542040301040d02082c0001a00c0301030b590411503508012018040070b000ea150103500140c00303200142031030510200070600d80d4082d03004941840c0403680080c0c01404a07030003420802d00000c0c18809200c4d0804241030340e08610301c007469092810580400ca10307010a100c0d4120a4a55041d031040b0741c4d0040c0e030544010030000d0300340f540c082c1d205e49001c0d000c2d5000303995008141c031607000a000107100210308000c0101c8000c150802c1501c5e900c202c01e806403503441c00300b54444001c159000750903004015003228002d0005807404400e20b4582c03090115980001c1101001c1906410080010941010b2072510201280c0018807511845072015060390720342801081d60740303004454400c05416a0141101c1e0404a402924840c03440c1009401c2c1c0710305442c0b00d84180d0017940400d144134050000b040c10440c540c0b50 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 370124028 1250 370122778 370122817
    0x409110c0706030b22060504050609070807050d02250201180e010302060d060b0703021e0d08160311070303020414010507020607230111090301060e060604060f031805150a15030206 79
    0x3000c445c0c520745c07061120300042d41c2d08010025030074640141e071390100e011621101c140c41e20f4500600120002051b80b420020005011010014145c1c141e58a007440d00a600c8103080f4110406188044981d0042e4013186180c6054404030b841c50402009581a160429086918550034441d4603001030740d08500301c0e070f12840d000c40c1070f140c000080c0a07564003d500802c5a07011610400c8036a50466582c0d20041c3c002c5503507202025001112250801510010610704902205c000c4001b410071180020003000c001400c04141070341500640150784076808084200d826003c0192507a10520000130740100003844000c02086c48004c190f48005040b081034002081c0190481c0d007162860182840354000100780141d0504092040d1005000e141c541c0481d64200500002d0035030281d88941810049522594941280b19401210700f4140641441c034040101c3d240858a075011020014420706450000840e03101c0700e8040e00300c400e80417405103c3ca050440c1c0038400660301800000081c44103089 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 370125278 1250 370124028 370124059
    0x82203080c01090b0f011a0c240906070302180f0a030606060c050f0d0c02130b0621090c0a090b060f041e0e06010503010522110409110c0706030b 64
    0x24014500441c0a00000918035400e140c418030245000d0a011260a007000040c494030400c0200c00e50b06c6900e1145d4141c1341c2c400341010600c2c0441d0000291030300c09890018404554584507000e005d15800c0058542a681d03203c0118100d0180e061071912001c1c0302c0c19200300c6420045200400300174090101982c280d105d44030301e000c1e110f59521260004a0340c8400c5000e011051001528641c44030003c3d080030070781848010f040001140003c4e100710050310501003904030350741c80100055030260a55840710f02c0c0c180a000c408040d2030324245c04d20000d41c0042d50325180401d00c0728903044000d1801001074140328020000301001080c654001d030341000070b0841c40c503882000e80010003154100300c2d0020f5629003030104480c4680d005410300c426400038810315a8000d0144c80c1528000e5a500c0300e0078003140c03e030607540040d0003092030030107180c440700c400c00400a400420980d010440c0138041488028962541849400f84064454008000c280107440c400e401c1240c0c20f08006122140002e0301a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 370126528 1250 370125278 370125293
    0x703090e090a0501051f0b040803250b0403021c081e090c12070305070503030a12051017010f0b06040308030109111e030406060f03050303130327030b010e0103082203 73
    0x9070b030411080f008a030550109920402024000303003070000311f1682054078005a107541c9000c0c0c2c1111020743e80104202a4843c07625005092405030407001880e45030030039007800b81d00c13403044601e0b4406030150350002e18416070084295a0040d582c12055581e0f803105d41504603694000a008a401801107000c04901a6900c9000081510742c10001d456801e1451514a15010a5a000c54040d070011b0000c80d02d10b503007083c2d52060000031108045400e64405d041d0100c1c0300c00ea0307041581500306a00c0403005003241580301401e0001041030404c0b03409062420400580120311004110000c00c100501500e88aa040388007941c12001840d0300f042107038100340451507040c5108840c7d80002004201c1489140d000e8040102518100c0a0001d4215215982c413480001c0084007900c19104007a010184629a08801c01e801c40d0748203110313007580201d0841c0c5d402d054401550300b00c800c40000304010322000056070407070380d100800e40d01c1c04020030500c0c10384810400c1c40209812a0f20400800309268 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 370127778 1250 370126528 370126531
    0x60708030f0601120c0504050a0806010f090207020d230c03010b0d0609020a050901060507120302041a031306110a0225170705091005031b0109050103090206090d030207051201020703090e090a050105 87
    0x95499094441d8245800e2055140c440c0c0e0060304ac540c0810010002c123504286400d0590380c0107080942c0d542c0c010300110b40484202c805c020b01088a580115003201249078508604000f100190341038102000101400d03582c400117101e0f840a0f074502c644000440640c00031540902c05440429441e0399803000400c6420260701c084045000000c40c1c0e0b04221003044110704260302428118101802d00d035224001c5500d414134000190000008542d07907800c6071003601c107500e80c80329040c0644542ca0341b12803069002406131384098400c41042d04a01c3c03290000a42261800810018956192079a50400000c0d001001181400354400102d259142e0140e041d1184140c4400b00c92540d1525043c140381c140f0012214000151071040d20401e6030f0322202c81000c82d4000d03c4c0c0843da08d40c29000007203a910428800a40c0700561a85031402c2540100e0341500301c4408542c204000003880340b8560a030311031103500400186400d0428000c0d60004194950000380c62000c4404c004d0041e5200c6007100c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 370129028 1250 370127778 370127801
    0x130b0d030e03060907030b0103030f0e040e0c04110f0f030615030f0402090601020d080a1a03100603030f1b0204050411130608160f0509060f090703021305060708030f060112 76
    0x200240c2601c641420800240c0101411000f41303000341c9075480c0c1820012040c00010100712041c000d011600d44158240301c00d03090028002c1200000d8803103099035404104d8144c5000300c0c180500b1510040396441a03c07400c10040207070600d008005404036200f40c4c4000c1605512903072100170f0704004103092010714810041b141d9007000e036081c1030041114208006107900c0c110350225151900051b40022080d40041e000300e0045400a00344100d030301002000c01740107405108003074200d45942c2494001404490181d1600902c12a0b140400c48581d01c241c080901007802180c81c8500500b81a40065400790240c0000310041c000240002c0010920a03141e04d0410788604044c00341401c00e2140d800181d8541d507042d00454a0005d42580020403807060314418030b000000503c25803180740e541c0000c01c030020095079440c0382071500540250480c0d00c0000c021407400c40082410b0030300d0021100e1071038200d8005420743c0c1e1600130740210200e00412a41c100203100c0c8030405540102d000b200315000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 370130278 1250 370129028 370129037
    0x50904180f060f05161e11240c0301030302210706051602070504150e040f1406010e0601090308030f130503032805280204030804060804030f09030809130b0d03 70
    0x501c080801015034001130009440024504440c100c0c0c10f40194085c040341d881b540c000c20350303443c40704010354185003020400c0e90b080c080d8207000c850620b14540d025071080001d244114450b01c030a1110341311400240001000369110b450704140404601c2000c04060050a0b0100c0c600b603501e42d1242c0640303c0584010002002c8035512066a640500c10384c005003d0a99041080c4030203580d0300301541c0850f204443c2d02c003140c2d80116042c0150440c418a410b030700b01004409103403102600942d03a440922952200e000781b0000b00b20b07250311410811080f00c1e008002c072800d5403101c000c465880c00703000c3c10b0440640301c00c41210307001810034030107144540803000e89244080d40d002d404120301c0032001d0343c0b00c2c1198075103000c0203081886903008a40c003250b15140340c148801c009001390003c2c4141e41011f000b0750004903001865991003030100748554400e40d00c0380340604102c901958410f48601005000010038050f950b41030800c040355001044d00360f40c0100e4400041408129841c014040580006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 370131528 1250 370130278 370130291
    0x615032503020d0b042a02031e09010807090e0c0307020c10021b090103051902031501090b1002010e10050c04031527050c090a02070501140603070b0a050904180f06 72
    0x1180c5520652104c2482a94103111a501c3c003003007001c1900040085041d841c2418100c1c0440c00d100b0002d442d0345210041846d4079210040035101c03007540042c04000c1c0010444c40020300202e00c1400108116074030640400b403240c43e511090503681c0c0000341940d08510841d84980c07034542c1d5401034259a0041c1d9005450009043e5400ea401e0503000030805008404c10401080003400c0020a06180d41c4440e50b00e585902d001d00c0001d003082c140b5800703281c103161044008500c10169502c4400e440d001100d41c1d0400b8888030100f0780c20f0300d0709000c1c0c0d44410b40011550700502e034200d401041d8451600301d107640c5007549a41e10f4007540c013040d08102049540d04c929224111944a000915408140030340c0c4540000682d0b496a680b92541960350256501e41c3c045842070245030180d90704c841c2d102009002601c60101003104034034007203a01d14030034400d240b400030781d403011201190558070007030f910985000303502410f000242c001c100d901c40c0140251508900030a080c40c000c006005d105a0011410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 370132778 1250 370131528 370131547
    0x2210d1805010c020a051009261009050307030c05070b040305030c010506060c10021e04121502091005091503070807090915030201110f010507020a06060806061503250302 75
    0xc0448a4001e1414085070b003c3c40c0e0090b1307481c4d4000c0000c6600c12a103680400400120845850030950f0003500070070f40b19003414101c0200ca0540e40746d440401e03811118014800400c02c001d0b1503096101405581080204101081c071a020140c0d0841c0900b044a134916030b00d800340341c01c59100f5802901c0c00d4001040160b0700f09070070300070107070001c400300c42c11070070149078002301c81c0c0740c0f030701040104161a400110201d10b14034494080c1c016200f0340c03080b292900c1d550b0521041c1d2034a045003c590300d0080320180b030021304440c0300765905010b01911b46070a882c008201070369650311805005a00140705510342d03000a100c18001c43c881c0003665220b09407800c5c6444060840c068940001c00c0640c100104516400001c1100c801240c0e024602000030009480d00d072400c0078020307003d0908a500382000c00040781d40004080d243c40d03226603410480c43d0741c0c4008140e220401542d103036601c003403000543c02800c0010f0001d950402d00c100303c445480d00a031410701400181400550300440d8001c6a600c11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 370134028 1250 370132778 370132817
    0x71103030702330c0c010f0c050418090b0106120b0604060f080a020c0c0409060902090702010501060909060f050d1416030b01080607020a14010204030b0c09100f0c02210d 75
    0x410101d0440305882c502411a90300325080d4014001413101c080400e83c203840c100f09410030001004015410086007142c0b510043c55607029020b083c04040c00315a0585c06010103108134154160000540040f42e400c0100c02c8441c115070100d04403030182c88035458203083c2c1d00c100041c40281307190740725028100100600540b0700c04004002040e090310510240b20340c002d001c214610901412240000d03094020f02d0820b0062094500182d080240364ac20013241c1070301544014140c60107a01c491180e50380d00e8022070260b0300c15000d94121121041c1c010001810002a1a0b0341c03144541c000c4e840110340100c0540c40c01340d410101920b200c002141c10400d10403007185c0c1d20302501200c0094925031400303d50196895189010007024103103041c500c180110f00a5040da8040c56101ca184015420800e000500325040402010301c140b010010803202c0034001e0308030328000280360302e400004415540802000316a0184045c40142da1604010b2584605019021601e5610b031203640d802c070300302ca01c4d914 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 370135278 1250 370134028 370134073
    0x5010503030c060a0b011101020d051f061b0201110f01050f0c0712180f08061e1608060a050d05030307021b030c090a060807060c030215010b070803071103030702 71
    0x1030103900308002d2036103441400b29855910103103450020418800e07680048a660600b000c1e0b65006500c00726041d40c0d8281c1c1504818001d03440b000e41040c50954014a180e060301991140c1804038061075817801c60141240100665680141044c41da0060b2a6581c01e06100708034612402c16591001000203a1110400250b04104180c01e0a41802d0031540c4600307501c02c40e45200c005100d1021090104081100c0704200903000c600359030465190f6564074a503481009807400418595481c800743c040854503c141403140c01003000540011000d16030564840030090044c1750081c46c40074010a4507220108042900c070310038402541d4914000c18000c6c142500511824000304500712036070815030b00020860402c030300480d01a07000b9150380242000600c0c1ca076006001c035010b020400102d240c0c21603003080300c450194081c1c85200c05264151400c902c000d0013100c903100001c0c800c4801062001d8091644011241840050a81c003c94400d02c0c2d90000c880d8440107a020741009425465040c40c1e54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 370136528 1250 370135278 370135289
    0x1031205090a0b0c1606030c0e060f090d0311060f01050f0306062107030b07050a08010e0105150c0a050624010212071e0c1e060c05100b0112061203030501 68
    0x2801d2036502000202891414070404074072072400700d2180c03900c4406000005001404070402c51141d55104009006800c1382101640031641071030b019159401c2c61011120412100394926203425610000c0010610b507180007501000b000ca004e00c00c50745010420580100400070850010350315050401081122080405019402c2035041c4a11612105a401940714014002c054002150b40c41c0c18500051a44054510f8400200f0b006500d9000070007411030307030340d10340c2c6071841680c9800c10174108010a1181785d410040f05032007803090414210107040003004c0c5409a4800002c00c1d1981c1e45004000c2e1400482095003a4050760100d001c0300041c49841d00a00240082c002c90882c00c44840c02140400b600040000c00804008441c805060f4042c0d5072181c0e00481039500c42d004007142c2d052a405c0e05c0040c0c2e09400e8041740081c041e00d01403046a52150040100301d21012408020708100d105007410b0190b900344c807040c01383c0c02d801903801600c1b410268040c80c19503814003d09071a03060340f05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 370137778 1250 370136528 370136537
    0x11030d0531051c120519050609100e070c080310051002010b0306040f110a0602011a010e060d1a0a0602030c01060909030503010e0c16050c090106080603030d0b030a0f0b010312 77
    0x203101003000f5440d04040d01c5404244086008141c07408042450350f010700525010400c00d000a04030151401c20b503440700d08003c940d8420050050210064402c03980311100010200100071038a039645038001182d25040000c0c0341582c0c2c032421a80c106481c800d203c02d011440178845420007501c00394a00d50356200a21400d01000082038a49602500c054484140031140c5000c2c03102c50342e019200380341c0180200187c5075580c10024020020b00c6018051800d140a0700314843d0305c5980070300d0b040301c1d00416171858408200300b032200411103680300822030010382400007048d580c0d15030160020442e0750050340d940c1c21810042400c4a203a9013022248500e0032008402182c1e01030140c905440d646602803205444544519443e4040c520302400107128000020040213804109099a03400556000940c1c0e621220140e035250011918550907600900c07606400c442d483d08a0304040341c0280c1611030901144e01d0301d02d402544100280c8003c1219001001002800d91000781c01c402540741 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 370139028 1250 370137778 370137871
    0x91302010e330f0901030e03040b07051605060a0909020d0e1605030105250f0e04020720010311030a1a0901060302030f15240d0603050c0f030102070b0711030d05 71
    0x442c0d400c18091380e24082c1c10103a40e621500c0e03152030100212000f40c0700481d859503c5840c603103440d0743d88124901700c41c081c0880303409000603035060900a82c1c2d4004005e131981c01d400303424086600c00a4025015128516488403001d03010517105000c1003d000c082029450a0a0f00f80b4007030600303440000d8022080c12401164030b84c0320b4445ca4840103010400c501d08082030700b650304070440b405802c984d80550b00a10001e9454200154003400005d40030b02940021110304070080194201c42c9004e01103580c1d0502040000ca5296042d03110300d0441d60701502501c0c0a055039004201c00b60400d0700405c1c0801d40c000700340401150f903410410f074400c0380100c108000304c9400c008204504000d5528224081d401b13442d03280070001071000d4407071483e000e9208005560380d03070810761358803c003e00903580100484982c2c01d15904040c0211030b080c5030408282c191548a00204032600359007c1500c0c003240c0814465190941401e0003464051440d00c402c07144805000d0130651900480d4040b0785401c003000c0301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 370140278 1250 370139028 370139047
    0xc02030c0c03060f2206020f0702131506030209031e030304061521080c0a030f090501090b03040b0402030a12030f0606110d0f09080d120506040b091302010e33 70
    0xc006903440f0104a1034425229413070105c42c3d050030415800141340300c0c00402e000710304501c004080c0c52680e008031160f0500925820014040303a000f16095030400d1046a4144500d0340250010f28503444080c04940c0000012a161106400f0410020039207030000420b020a01c0018001e011040c81e08240d503904861030844220624240c602ca80c0350070700071540400040c840040b0540741c0b001840c2d0240d9a51228900d401006881900f0504021444404001c503c5501c2010740c8800d0f00e1000a50500d0342e1150303102d11001d010028400c03a450712950101c800003600103440c104150105d0f4a010840c16801d1890f071060312840d80005c0200250108034548440c00051011102445420480c14951150b0030403140c1007282e4202002d28070032490682e646170750240300340c6011b5948a10170002d58850004100581b215002e00d1a80a212480400c9a00400360980d0100d41e105042c01c411010850010600b510128065094802541c820300c4120014190549442c000013072855880e140030b0030b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 370141528 1250 370140278 370140301
    0xa0c061b020d0809151e0108190f080403051203040c06030b060307030f1d160b280201151d0f0702100b150c010605130e0c0904150c02030c0c0306 64
    0x150b41c9041001890340104046401c184602c660740d1030141800790301854131300c103140d07440343c1ca01c0313441d84205001a000150080c2c1c040390950843e1101041540121596101c050358400304480c05c1e6000b0008000000003c3c004001c50700600c503042e404030f5107910380b905204420030043c0d4040f41c181410320880146580d60f01d800c503580600c40d070600046003101c072884000142180c00460040c07645208407200c080200280315029050507900b40c00c080354503440010700c1400f0700c5820021100c0031907141d002d460003050001102400f5403000090b1030010260202000101d540141100048540089018107482d0340703640d402008c0300407066003414146002990786110403000402d50b595040c440a80383d0313400109010640c50104a1502d45011820a078001e1100e803048620802c0011010040c2d801e4a02445e50001d02000103000502d03415818051805401481290300806c000d8400d000707201c040c8107407441d103509a8015901c4c0d002070706903140303480388040c207041c4a0352180e0100076098060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 370142778 1250 370141528 370141543
    0x60f020709050c0c0601090b12070305120703140301030f0b01060c150f0b04110c06160801140424060e180a0902180405010e0c0d05061503120a0c061b02 67
    0x581d4030010701030351400c0d00900e490291041032505801070b100001644a52500500c11141040b00c0e44c83c1c2943c1d581c2034503030f52103c0d42c0c030004249401c40720f04502800025000b52018502900b00b6a000e0007603100003004950007600100c505041a040e800203100d000741e146405000f840c200441d003083e494a9210000b00e0750f42240109984581c0c2c640040210394004041030304002e4018004400c5019080301641c0101507180301d0341c0f1134000041d07080c4100c07030924000201103440d02c51981e400c040e080c8441c00c100b207140980243d11468802809551a1600c1c05019541c400c0074110707a00b0000c0041c10010103415180c03040694010800c2000110f1441c1900150400400226210b492010400d03810502c0c00d010802c4106600300400e000064001c0c07a082000d0301c00b500e00709455030003000740d2039007480405065a8881c03c0090314001c00820700401c030800080455002c24081c861040d10b6900a140440000301545904020000c1e540070301d10f281d014564203101c2c548640c91f80250364424 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 370143884 1106 370142778 370142789
    0x114060f0402041503050702210304060e030a1d27090105060612010905090c06031608090a080f1e0415080f01051509030313140109060f0207 62
    0x20680b00f120700755120780e4003039050300200c034000710010700b40102420158031520841081c1044000c8180c6003031441640c482d0740d0b07032519182c40402c2d00d031034540c035984507403092000e03401050308404050000f00c2c00d0740c90340910461580000e0031415210300c07140c42c074440c41155180c0900500032024865080000284804d032915018814944150300318194040303c450010301005046400485d04216440105c4011521800000312164802e60f92a62203c52143ca6803444540092200e54003400da8030151003610010745800700c0c06d1140b000f400350a0900041c58002c40c0809440303201d81c811010b442c070b5842d107444081c00b0300c181e800e502d18080490280f00000f14140fa20082e00d606903100580514071421414107011601c0c3c0060521a50500045c8581c5e019981e4144400008055808080c1400e100c5280050020140341d00b241041180c01c1c455001e0190700014200210354 = true := by decide +kernel

theorem cover : BRFrame.Cov 369964028 370143884 := by
  have h0 := BRFrame.cov_init 369964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 369964028 ≤ n) (h2 : n < 370143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
