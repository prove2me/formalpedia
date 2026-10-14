-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0192
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:21:45.675706+00:00
-- url     : https://prove2.me/submissions/07a11fe5-35ba-4693-92e4-0d3d836ee624

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 34352523 ≤ n < 34532379 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 34353773 1250 34352523 34352537
    0x70b060f030106030506010909030e120307240e01090c0b0a0e0d26040e0a0e031207050f0f04050f030303061c06020f0a120c0908070911040803030c2d0301090903 71
    0x1d909200306d40c06402c41c040001030310544d0b0306004182da2040d010f0b44e8001c120060420f484800b000c01191140e0f60840b545010403441c00c15210902c02404400da19807c1c0f41140d482810034045d046071450030700440003101c10740c0c1c841c00304440c18480c1880d11303c017086c0140c441a40314100b05c280311100c24001d0004200900c0c0b4003c2092047d806841c298010350f00018045c030044524851440e048503038620304000401c4c44c0c2003003035070740d200f80c0d01e03c4a900c4281c0d41c0003988151061084858011a81c4a241e8540180da01694500e820a0044601c00d0200103403030f171000d04000003a6480756400800070310103030740d01c814103c080704010901581d15035000c06c1041101403001c00100404450703640c86025000c0e07074911444c00c84004183e0a020021020000c0150321000203010050307c0980740002014540112100010300ca2540068154000403080102d1051598003404115200c240f15090102504011140340d8612641d400c2d0759441c18001441820000d03400039a40302c1c402c1c00c01c90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 34355023 1250 34353773 34353779
    0x12050c0403140a0c0b031303030b0a05030d020304080123040215120f041110050301050f010207030b070201061e0302210c091005041103010803030c070305130e010e0903070b060f030106 81
    0xb20040d0a14040045107900612402080000140c3e010004068000256046040c030411003103061314007080c040c040644403484030340c680e07590180020050074002c040f101040c411000c040c0d141d41140c8103020340365103480c003024562140f201240154112a100c5618561303210782c01c00c68111070203810070084510130b00040e00c50207020f154a50044024854888581c0742602d01031100f00c40d04110540604080c4030380c0c0d02855000000d5905480040f0b0380d50f807501000100413450661160700203404000c24500b440403550301036101000356044605003084180a49280003400141440000d400c19007a9a410440c0c20b41d0000d50340002205000307640a41c3e0090000412440c403e40302d0400309010f00c0e108101d249814802c1d18180c20030b849083c1c4c02c56241800054036804001c3c903800d40c800780005d4607010507100e20111001c1031440c105a010690700d0304410381c5040e009000b110280340c4400045001250000b069030601540007901c0145550307843c09106101d40d00d0507100760990f4036a1808 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 34356273 1250 34355023 34355033
    0xb0c16061b050702030601090b0310022107140a12020408060702010506040b01020d1409010315090c090f05061b030f0d091b050904030809031905181012050c0403 71
    0x42140180200e60109507000d8210000316011140d41d140301c1807100810003000140c501103030042c11125500c800242e81a80c0d08c020a0034584050226400c562001461408803904400400c82c0b5060101840c141a503820005540310600c0113079400300300303400b404527940315441600b0100300441c000b1409403c1a580ea050185400420364010016075120000c001050406100e0462903150034401001c984602c064094542c14140142071040741d00007c0c00005640281c000e00c0295200e09103241aa582d030707194100090500040801c00282070708000140c00f544000d0700001c2e00d10082016140a0041880c104088202c0f203c40c11607010521000201100180c091b20f001d400040c0045003038070700e51800e0700307250449000c118140b944110041c00300b51204043c1c258440d85c941000c24407500c941c411a8994041d0707030f030940c2441c1040d421b4881c0d403c0e0310401524103030300c410401008600408041040d60000808a28002102940036151184040d000075400c40807580c0d405140944a40395 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 34357523 1250 34356273 34356307
    0x30803070c14031c050618060409050604030c0302060105010201020414060702011101020a02030406030b030f1513050105011502060702120a03110702040204120b0a05040b040201030902040e150702070b03060303070b0c 95
    0x4a4260341d000070031140d00c1c4513544440c1c1420a14120020052071500c030340051010100300c04074059a1213400005480b0351a00d41c0020412500281124000d103800d14008111600f415800c50050003400d00001d10340d40140240c4060710203401b00c09500c0701c061000e004040e008980140d04015440c0707201501224281300602c19008150301440d507940c14940060140c07526001040e000f0ba220703980b0030103601c1020401040e042c1c51400d840d4515100c1c08507406074403820040c064415460f08000081c0b1100d40d403000201c0c500380fa000d80c0c030640e41c0d0301c90507611060240d401c0d1041040410401800610a0f4401200c091039840c4444c1899060b80100e4100c1e0002d40051a44840c40032081c010b002090001030ba10a1202805000520f490303a98010307a01c0010340000e042c1500e80d40b80c0b108658942d00581381c00540c0000320384040b1090a05007e481406548480140c040c0c00408510210000c00b101c0c8510400341c015494210250317682d152051004082010141044c0801d04c02584801c00f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 34358773 1250 34357523 34357553
    0x6190602060619031101030c0507120507120203030f2205010509060105040b030d020c060306060d020705010f051308071202070f030303060303080f010302010815010e030312010807140a030803070c 86
    0x2000703100728903103001800200074007030700b650803820540c107000c00005d038201900b1004014286404180707415240310540b818050204d000300065601c5241c88500c50384032015000d0a4011001003210122020050380c481c402a42c05484035018540010f0510140d50048100ea8000c01207044900155880700c501711201641d05500030341128004121a141c5400340300c0c0711140880c081d010305401c2c480003940d104a1600301500038503022001403150360703402c0c1c1600c13801d00e44200c0c255a21512803501c18000c1c89c80c0c8190300299031810002c620107281410803041040c0e4440c80303c41c5005040d40314800581d4500240800b1841004c40228903000c40e015880001c51090320086025401c43c600900144001400d05040c6625032004002603a0b01c040081d070010404058401c410070401d00494005540384800c5da0984000500e403080c0d16400358881c4c1c100d071044d0782654402601d5505c00344180c154104003650007480740c0011320100d0b54401c0119040034941c02c200e16079901c50741c1e0340003804501c0c403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 34360023 1250 34358773 34358777
    0x31d04020c06100801060807060804030504030609050a020a0b09150304050c0a080f0d0302030f07051303050d0c02030106140906210d050703080a0509030d1109130504031106150108061906 82
    0x201404000f0307050002d402d028184090092141609100704266142c8075442407408109216003c201814081d1003100c01441e00a001809200600c1c00c00c50f0361541c035208200d004400100002580762517031000d0b1501d00700010811001030500c041d8103105500050300c243c0d201e015404803070f20280d813214003040c01040480042d10b1016000c140325410040311507403400526004008000f0b01011000d5010740c40480b5040c21a00c0c2c0003d40c4160000d81c0968100510510506030140c0031242c00c52080759115200310024048a0b0b112201904401e22980c4644d81000300400841c609181000141626100107900740d20380400080c0c0c141d2910304020500008558000b4aa405060340a442c955004020310b005100d0b90400d40c10095592060f41c112001d00f517652112111220480c1d0100c1c2d6400b50001c04490800c142059a800141380c2900c048000c10301c030400d0800615800b14003030348196080b09a05145880342c1006681941e0014290f40d481280c6100d040003503081c107075507940506455 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 34361273 1250 34360023 34360033
    0x130612030206091e0705090c0d06080102090310060f0b210f060108070c0209240301090c0503010b090c030c0706180b0105040e0a0503031f03020d06090201170103020d031d04020c 78
    0x140c6042420b200ea204c240740d074454002c00c504048100300080344421190240c91006042d070b40d2540c2180a405001014410b0a00b40040060040815005468025421000d581424124140a4044403103600c02c4a900d01d040140412940d17000340090200d6010344150180d05418044004050350f104441e105982c0755440140940703540c1c0100182c0c1c0c0200f4034101842402c0c034540025144c918010011480400030811005e8490408408540700b00c41c064000c0c0906c044c140b030200395203181030003503070b009621745603103154145052201c1c240141400304082e0714589450340c081d812684210000e580300c5455442500713586101c035204030117250003480588410f50400c410002582c400c240e41da4030651210400f2004680044201d940018544401c2c0346c1900004e500700200240ca50b0000c1d41c8580900070440a001c200d401441101d8400d03a540c1302d0103070b489030304507900d100d00b800041d40109140c03180030300080c0500d041c031681240102030714a102c51504001000da900c501e08803e083c0c0c001e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 34362523 1250 34361273 34361281
    0x10621030305160c1203020c0114040510060b0a030c0c0c0e0402041b0509010503060d0c17010b1005090103020711040e030903011a01050a200d0504050108070f0509130612030206 78
    0x410720440c3d40110001d07046a100e611501d000800e07000718004040c095005044405540c1800795048807103540920b002800031801d0b01d1403e5a240c00220742c10b07241070150f903000c500506018403c08080d64504c10404d400d00c800e00c0d104600801c007024080b07043c003422007038003c0402c1c50407007072100038500d000662505103424810b0205641e6444040b00c1d030543c0030602d0003e4150040b05030b800c2028286080782d2285d4401340040c00c00d1191207005032000c42d5a002c0401c01020540030b0b00e031403020355402804030b20411014440c0b44140003060701c000038810f00c0602555880f0303400908956020740d0034075640a80c0c0d00009000ca0794124a08043c2da4400903049100e810203006403d08016078600c0741180c6030704600041d050f8032800181074100000e9000c020b101440d107002849500c44000d04a40d1180441c03007028040c0d621074000c641c003152222002519941c898092044841d40701e607522402c1c400807100b8400748414415030300c41c8864a60781c02141603541c0c2411014458007a82c010851410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 34363773 1250 34362523 34362527
    0x7030c0b071b050a090b04140106080414070608060433060e010509090a0903050706110d050f1e1506070606050907080f010608062806021608100e01062103 68
    0x200c1c0044655840c10790000c20295640603401c0d811111149000b1411006d6000001c000300030301c0b42400b110003811030000c2155079025240512a0f4807842144881040c04251603079203120512074403000032030303540026880b03040940040750000305c0c104060000d0441d00c254485c107055910003141c2c000030301c480d0410100340c0c4001d104c0200c07234080c20304034907103030100e0081048040004c02005030107885032241d0b400c03d44a0001c440140ea040b0b6003c02c074083c3c44030040f000c40c0d400144e0b03100240341800d004c20300b917203681d03e000da0285240304030403c0f8003c8800c0d00c080f8031100041c94503007020b58038007417501d00f030b180d04004011840c481c15001821034240740811802c1d20b0068862000c1103080b40030888101c3c1d25584160644a031414010455034400d0001907601c40034041080309040d10400301050380030006150700c29100d481d001c0c2d400703641c2d1040d022901c81e01548a84401540500440e0203ea81150f002c0d221088180c1c0020444584031340182280b0b0180b01105805400b2003240700741071507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 34365023 1250 34363773 34363793
    0x7020d09050f0d0305040f060503100e0c071b050d05060a0e0c1c020a0b04080a03080702060601050405091806040308010602101505060d090c08100e0f060c03070207030c0b07 76
    0x5165410544840c9003810040b5101d081540002c0340144001d00008082c94000c5003600c00070220b524000c110140c841c0001080d076001540c01031101c110b0140041009944c2c001424400c4804404d160706101c1c2e5038032000c0814600c80f9102d190800b0600000c5040d0316107192407540c950240d001040c050604010080c01c5030803c080c541e0711034101001178015651255803100200c400d401c000c450815a900004803603207401d40c048903505500207800200c8410104540352100c1c02511070f110140c6d0360740026a11444115021400030350104014003c9140c440c0d00c3d607411801001240303280d103071541c05c0e607440c2c90700994068000c14540401001040c3e410800294150003941707045c450381784500382c11011000a405400d22540f0302040505244066511000032a40c03c03811102000340c2d03440380d9540f0781d01400c043c10b03003c03800c00e40d84a24908000078003070500c103243c400900032603582401c1d96a894101801100840c0560b600010100304803480000c0585240c44215035641144e01d400c040072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 34366273 1250 34365023 34365043
    0x90901090f02010f020102040905070c020102010b1e0d050307060207230a020d060b010c02030109080301050f01110c01211506270504021e03090a0b091204090b01110f060702 76
    0x56814403440384001958a920600490b50a08103a10340d2142568282e02901950f00315458841c40c200820490320351003000129568001c7c3c00070000307405d001d028400000c46802509405c04441d072a0360105060100314000458010000d580c140030a0382d6072001680c1c00305400791161a8040101646408030111459880032548020400508660b000c207907004d03110000070f0042a5605900c600c0d50b40a954803108081d8010000c1144504070714100d01d0b00d400038001c3e0b50203084951010440c550140d1030100c040401c00004104001015004540302078a0b00c00d10005000320303d600d4400f0181600801034804080c50040981a080200041096030800f8240010711040107a50a0110602401380180e4200356800f42e81c40280318508220300c00b00e0300c3c4003420705c030001081010140012840745178080c4140011900743e118004032035a43d0181511490709001c003000204903042d8250701500c081041814158243c00c985a4102d0608035001c0074290345030003001c01c00010f15410301824480c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 34367523 1250 34366273 34366291
    0x50906010203040303080705071109040606140103060302060702130914030706051e070305040302030c030d050610180b0313020405280501120b0406020f0313110301020304242909 78
    0xf014650f071001455200701406070014840001803560901c210303078100c1c030344000c070243c81c0e05418100f078030700540104180c2c820220705003092003403040198880d00134042180e8006282e1414401340342c0800c107aa46c484101da40b042a079442c0c020000512200403800c440c0c1e01c99024540780c0d0500e0030010140d4034024107585509200a00000016034000b01140d0080201d20700010240d5440c81c1c264594440e2000100740c40c4800b180444800700383e07401061003610181ca07070440c6410406000d584860100100c4c0d00f11503d42074003885281d035001d014540c800031500601d001e550454000c41c040700d03001d80356103010f07040104000d9501a1010b14558951380310310420001c1c1d6160040d10080702074503060003031a01c0d50a0001c501813000d83e4047e251000d103096616641c9007824800c0d4515a1040351040381d8414403005030140b14074043c400c1e288182d801c4a124100e41d0005040d0050300542e2102e0036011580d150151819030000548909100000c2c0c0c5102c144000100100001d03090f000300700d000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 34368773 1250 34367523 34367527
    0xf030605010909170901090e090a0c0f03080304200d06020405040b150a03021804051611030c060c070510090b060a050303041a070201110114100915051203090d0c050906010203 77
    0x80020000541c400200b071318a0100c607120601ea03001203984a00700d91010542800d00000d10680b081c0100d0400c007010710a0000020040e6a8620b1250462040c400940104014000100030030100780102e1180f801d010031543e8400848000242403451411059914a9012805101e941880d2040900000f001c5849000391204480110880e00c1400094010150045499001c9040250400244c000b0003003040c031051402400c1d01c20700c40d20240012002480c80640401601d0000c000c4031300d03038600718018040b11340e92001e00090f1640320040884103841004500700e1901542c0c4039840000340b0802c00d201c0e00f814518100035484010f604040c0c4680c0003000100710390810b6600350050b541c1011116a01d6164a0005031144059880f540155508000300341ca00c807203146c0da485100b4990f203400c4240303258a9141c48000c50741c02c1c03441c03800400c60713009043c49245889540541da1150003003c81e482d210300080880e10b007990b000011500030510003028099407800807401c50b4020000c0c40218 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 34370023 1250 34368773 34368791
    0x6040b01060e032d0102040b030c030a06060c0302031602010908010504030207060e062115061303050115120b040c090c0e040606020613060504020307050d03170f0105010e040e10060f0306050109 85
    0x100c00490b1611030304500c10401413010441c010a405030340c01030000309060380e240d1502c41043c0e04158001c890a04a1300c0c41d0541c007280c128081c56880e00341c542c1541c0214149854059080ca0207100013405a0521003c4640069940703400d02619225070b03ca0742c00780c5106032900b81c0181c4400f00d03615005100310414403030030f162200300c0480010490013040321215036481d2a01c124010120807100180c002e50006005a00540840c1c89502224420002082a00042001a049020700340035401c211118042140017065100c01d445400500400e0014007007076031a0328020071030b44800c00c0940460000451941e040c509841540300512250010701040d142804d18000281c42c2208002d1600b543c4030b001c0380654074100200c0c00a0400504204007288141c1800352085402d901c40d04d088601c40000104104411807441c0d0403031f101a120540c560318200c0070803018011000080449214000380c10b6520b164038041c10000704280700d8486211070550130040151401604031801d001d040c01420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 34371273 1250 34370023 34370053
    0x7050d0f08010602030d0f0e0a050703030e090114120f0f070611120301060507030306180204091b0e120c04110c0d030219050a052b0b09060312160506040b01060e03 72
    0xa03040039200d5200002d0131f040c154100001400c4484980344a8400c4d5041c0b0010030a00144000980f03000741c480c80c090480d030308100424030400740580000b103450524503207254109407044035480320840381990386040907080c07990710304200184414110384c04113200304070441d004200314a0310280e5802074a0740101b4041603d03003620042c81a1410080c0c00185041494482c0c0d02c0000584000011041c10050410f0540c01a420a0145d011542e2419072041401c0c2006013071102202100d44030500203101c20703020020207101e80d0384240a03038000c51410780030303950b01c074070078003c3d04a02d41c0007050b00c5082c140559890455031031130007814180704000e40c81002c4040c01d102c2500500c14500740e40c3c1d42541000407604c5000384201c60b00481d00090801c02541c12074028500d18410202040241c0041c0740100b00c400c6000340c034001c0d090b030806030f020010154860018080401d038000b941c820248241e88851130484100d0701034801c400004014005507500069849405008500070201e402052040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 34372523 1250 34371273 34371277
    0xc12090803130203030f070b01050a0902090a0e070302070503040b0406020f280204060e09061603020405011d060903060103140616082a0703030b0306070302030106080c0d1107050d0f0801060203 85
    0x500c401001040b074140440d9000c000700e03a20b4040308500151034003018030740000c0541c1c0a004035842241117000103c1d00300c40c0c82c804d441c07441d00000d007003610003854030391048408003020b002c0d601019000c10085011982c01c10080c401030040c011900c1d40d451506500a08101081c10640d005412440400c01c030204c114000d504800e113014103045a81101d8800a0020441980194001c1c10b1080c204401004003103601c910030010007800d030b01200d0102000702c0803440380340210360101b001903503010364884034036114080440024081300d1600044000082c50310340240d01c01c544101904601d0100110700f07019072038010410400b418400d40c00c000c40a800500014004690401110306407019440a43c4da81c2c401030320740c020182c2e640c0d036035810010080c0402c149414003a11802000c034026a1280c82102c0c101c2d40c145da5000d18035154642c0d000700740c0d4411a0303140d400680f03030b5500566640e110401008901c1c802c8000741000d51103110007800e00b103a0590704209019100340100310440d00801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 34373773 1250 34372523 34372531
    0xb04180209030a02090a0b01020708030a0207060503151503070e0919330302041a0108040f0f0510140f0402010e010c02011e03021b030309030a0c020616060c12090803 73
    0x1680701c400660109240824032140a90300150820610400f890103910444c0b445074281c0c241c4500390f0711040b005540c0d108a100780801640001e10401c0302902c80c00c00b441e007043d201e0400c403040c5e40c040030000340c0304001030f07284101d003210010901003560307045041204240c9003501c4145181c070303001440303988100d59400052100703a01c590160480d040c005249050441d007482d07a00101803811090f01106c01041c3c041280124a481d085803000d40003004100385c001c0051b0342c0d0840c1a603c9a0b030b4184c000301d03d604110303041401010090005281030140340b500d4a90090009808140900c1c1d08019450152102000c100e10206010260f40c0c03144181c0740011082c2403101e0148607510040720090003001c0350700541502a021544d407242d00da0010000700c14901e074840303504098140300684a100036101840702d07902c1000342d400804e00070700400244c0ca000811240c1001d8080c400c0300c07038480c10440e084546903a20fa1071030300c07181c2c2c1100031030006400381f0104205420701e070b90718500c6e02e2201078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 34375023 1250 34373773 34373819
    0x70e19060912030c05070801060501021b0306070c15061e0e0609060103020306030a08120a05011703030402010f1707030609050c0f04290a0201050115110a060b0102010e030c0f01060b04 81
    0x404580c2c2890701401e900341d200b5500c0340444011036502c5e50514020300081c000c2e41d00600607892420216030f0f100c0b500c0c0308801c0000b4060980e0b5110081c00b40c2e24a108004d0486100e80c400c5041c00441e626071140c2002481c20180341102180c41039008091100c8030b800c0320054114040901102d1340b504015503034881e00c20700b80181d480d110600080d00e44941120010004500000c821054100501403d4050744202906211603609d450038100400800003403201194018000140075602c0384840603040f085509004601488102404010303502c00c49062001c641c41c0d0001700305230030140c8282c5a05c60703510710005003440312002841440d4440c0344a84a5081d882070080d4010403841c076440484410160407195584520f1200603000c1d050900c0344010001c600e40c60407a0050042e6100c0e00701c44030700005012280c0c6156915401030891094440c115940d030070381c12040f075008000030300404605600601c4080c1c1d413070302c0450030740b0180d070001640c4102c24001001400d07041c84a43d0080c012078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 34376273 1250 34375023 34375049
    0x608010501121a0f0f120321091b060d0603080702011e1211040801090b0f0603010603020f010305070311030a021206040e03070b1e01170f0d0906110a0605070e190609 73
    0x1040002d02c00c0010045c0081d03002e01c480c480200c80a10000041c2100701c580305c405404000054403d4218201c21070f840b40054000d4203048010381c402a1540c50368182c002e240a0829040d1a50101254616001281c02400c0000c50310103560f04400030b59491038544900241030769081d10014810442c880e1072546107511025030203220000b110030f4902404103c4020448440c4908040242e40d00030340c0c402540c003c094011805505045c05100b09132a0003820400d80d40c90501d004500070071000b00010304141e0f4826141c0d181d100d1100095000e48001e6501507241c021761545d60626100c090716030b80c031a43ca010b00c0801480f03800b1007602d8645401003184010350f5254009400e658070b004170010380449226001003481c0b000c90100c081c220900500f02c903080b41e15410800d5841030300d04014000300c1d00c07205003000200d125040e0407004140c080d00303a540520300741d500d02c403d4500607101c002c0410349101c0010950700b0005803012030349606501d0450800c0c64840044c16078001c501803c0c54880c20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 34377523 1250 34376273 34376299
    0x1080c0f0111010e24070203030f04020d0f12020f21031008070906060e01031811030102040513020306040507090e0103031409060c0d02010605060405130e010e070608010501121a 78
    0x3652101c4542804400038860058a00241a111760781e0502e103a885082002a41002d15601821588074140345e4006518644070201c81c4000303850028002c0368044618000380000a01c007800c201542d0b8843c50b81c48103130500f82d901c040d00b009480188042c583d44004220500c614102c014001c10803c9036800329500d840c1c0744002192011140c21a407440d1040003c00910030f06075900003811110305070b480e50000ba4090b00110240c80480e4000c100b621540b03d820400300381c1c119400c2c032054a00a0005140c0395558001c00c1c91420700c1c4441c008050707404000c02086050500030140e1105c1c140c0b4140c08482e080860041650006000c040c00304900200000381215040003143e031b968400901c40c2d601c035074000c0076060795a007201003102c00550801c0310000e00303403c01c042134030103844005000442c2c254401103a84020b0480c80c0540301190b48407080c8610000e024820403000d07145541c0d440b0802d604020000d0201130442040301c042524112421880900000c540c00104000302c1d2801c259103e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 34378773 1250 34377523 34377527
    0x5060a0b07050a1e120c0615050d110105041a2a1903030902062205030601050f010806060d0509060403110a0305190908030a02011a030706020312040312050f0106020f0601080c0f01 79
    0x91132003002000310303210b81c80e0181c05541140407560b40504c0340c1c505100740c1c407903c48110708200280c41495000342c18481c104001450fa4070340d118411030180340035800c00740d03100b1480b080c03400e9041c1d915010280010381101440300c10400e0b045214240340c80e0601f4641c039441d50990300d41b0b0180010510700b051542e200101071081e0013004600d03400500ba29242e91200310714200c600c0c0e546081c2d050074515040006047d05011a02034100c0782d004044c0d00584100b036006503012a0000c00166115000b0409061802c41d10720450740500800c0c001020710b403070103103009400085104000c40b40783c3d00410000d4006a4000112841c0c2e40400b05441509101101c0135580040c80d50481d821900012801ca00b2003a415803210318a0151000f102003448090f00c00e041d2280c03158001d07400141c10812092844425129000350030501c40d1600c40556440e12102c030b801c803035068803101000d0100034010048140d04111a138500c01043c40544001e501d0102011340d0b5100b0022044c1c010051014669620381c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 34380023 1250 34378773 34378823
    0x2030118031b11130506040b010201060303020309220515030d090b0304020607060209040906020a0207120203060403030216060c0c0c090b0a030b0901090602030103110a0b030103030203040504050c04080d0305060a0b07050a 97
    0x143c0213095421a21005140301010f070804649017800b0358542202d00c0850b600c140074185c12280c050b000f452a1410040a00007408000074442821070034001220401d04441e01c00c01d441800740c0c4122484401c0303880c5c205814501c00006142c1009040f810901c20101060f0072a50007a0723040303031016542e81d22883c004003c0d0241140081c1c0c810f00c0c1c0741a4506000058005019190350359098a0300c50782c17074482c5280c1c1d54440a0010703409d07500031400140003d00a5004019103408086010035101140c0c0d9000240c0742d060000d480011009902102000565a42c0c040a424000030521480d8090f00200315903078030324400074100c20860f0000c41c5148200f075202c0d14180d0b402a4040d544c0c1c1d81c40b801c1000742400c01d80069400780d1600303030700059888001400c0d039040e65450390155103420b180204000240c48050443e4040c032100b00720015078188100300d111010109a18085940d00d040310030413810744c42680c00325440690400940300000e4003caa110151a8000c0300d07200540000c00815401c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 34381273 1250 34380023 34380053
    0x605031f09050f010f0501090b0d0b0a03020307030507150f020d03050c0f070b09150408040306050c1306170115020a02060d0f060b030405010c0c0308160311030c0702030118031b 78
    0x45203410180000c0070700141d43c0c1c6060750f40812490304030f0b030399a20045500c001e0703a12412841c020144018540c1c189150003800040400421541d1917035140e4001074280700056008a4443e404030004000898046040400b03407885810200000302062002035107940b00112107004160340c4400050b80078102c0342c2900c000001000c1d8264448055250440c10720105030381c3e00c8014401c0c401015806100400d001e889664408109401c00b841c41e6100405024040d0078450b0804007444461060050301c00c0c01740007441c180d07940064036a00801e101c4907200043e000320000715000f00c110700b206a000601601038a40c1942d00c80e60340c2124000702d200030200704d0b0600d582035082140000d20390030b506c2c01650280e4000d0b0020820202655425a0246e1040720020041240d1000041080840ea902070041a01c02c0c10302003051070041c0d5860b07181d9441211080038641010681200350305091140d40d101040600e812a190303c0182c5016100d03103465400c095032a80c211048101304040031801e1030b51 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 34382523 1250 34381273 34381289
    0x10f0605090c030403231b0307080403121205040605040209070905011e0c050703050a02010212120703050403020307020a08070f0f0b030f090a050303090607030b0609131a120303010312090605031f 86
    0x310564007201c40c1264446440ca87d40c0340003048010404090100448131440d41c0314010300e2030f042c590381d6a8034090b0300d4065070609000c02c40b100341c460184503009051045100700c400141c0c5250a1040050803035014000008100419030288241d0340c0102c160281400d0722914080c0e4107900f100c040315401c1c0302d00002000c80c0142400081000300010301661041d02c00d030251a6400309000c21422103004036403041e592a4004400326103094020792099070094000c0c41900d01e003035040d8000c81c10305007907030780320310000d0380112030070400d030200d542c403840140031a400c141b0881440d058040109003c0685414544020640815110807081203200c903265440005d5944a01e041c002c2c983e150102240c60001203410041d07207420a182950484446400c020074031060030358034442d2000101a100541030040000004122040d92030010207854400b04070300440d80d07503066240c1441c608402d485600284819000280300950b042410743c2e034000030901d484030902400758001c410702401c540c4450a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 34383773 1250 34382523 34382567
    0x170c1003022209051e04030c06050a0f0e060405071d010e06120a03050a020c0604030f06050a0f060e0105130b0a03080c010213091a01020c10031a180405010f0605090c030403 76
    0xe50f4491600664802c2c030b401d8400d195203a1615100540d4610100c030010300003400c8000e03070400100c880d0301260300040074210000380984c000c030000d02201c0c1412401d00d49039204900b0882000000c218400107411031100321080c80c0d608043c4001c81a4060203854040c1304c80c18005070680d00c6103810040080c80c01c01c12240c40d0501820080e01c16132240c15450014001c000b021201400c1000803101202c1c0d019807030004900e603544034240201005002c207041c803030310354540724144015806000050540b041034180c080d49403a00304103003941c865810080c5242000c00d00101e41e42c40000d0741044981107404141d03910040303000d240c028421503030f103d400d0f03091920000c40d40c1060b603800405220035407881550949070320b20041e6958201140c3c00d0394041c0724110305c0401d00744070760004100c80101300c122010301480c04002615510002c05084041004601040180002401402c1f01c50a100d00204042410200403034445500106107407203222001001c43c042504c00c68100000b00c1c0503d150760 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 34385023 1250 34383773 34383779
    0xa05041805010c0f1404051305090a080d0b040b0d080403030f0e0402030117060f010e01090f0e030301030b06010813050c01030203060117070f090f0b09040c02070b070c170c10030222 80
    0xa4102c0304e0580c003503000103901401048500764040200e03130580700d0061403184800035090500340500270060404906010f0b80c841d0340002032215000c0c25218081030408103a0051610601c01102c100c401e205104d40110b801c100080361485d0b0441e0300341c9030580380c40458034213910b106482c541c0c1d074603070340c070780c20034400400041d541c0b00e0b10446000740103407030058540c0c546a00300c1c0000e4094081c000c0320340141d9100010043e802c010350040b400804010b2001c01d510f0140007419040d80c10036803060700d000d091142081107660313001004c507500171180c20940e110f01123240c0700c00c0d070388882151200e41415070000c0487c00c80e0b03004004114000c00c5110704c961b2145400000282902c140c5400080461290315010610010800f00325043c4e480801c251030819240d0781c10040a050341050302829030050032004100d03200c0c600000d2081c41d0043c80340036001d62a01740c4201040c14000b01e00f6405810056169080daa50940c2c03102054245240143e1920801c050281444100c041c480e582581501000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 34386273 1250 34385023 34385027
    0x209040218011211040203090705120703061a01080c0f0703050702010e060d1a030a110607020604030b070305040210050f0a08180a0302150105040e0a03080a0f020f0d05010b090a05041805010c 84
    0x100b100c041c41440500c4c000c1d0040000d01c8103900040d00d01e01003a401450041c08981080041c03a808440c1078000c03900b4440ea0384d2500d40c02c86840304080042c01c42b0a28141d4540d5800200b00d81e04441d490a146241542400e0310b07601d00c0c001c40328024100200082d4500640e8070422210007002c2004111076900c803805d802003030092460107040020002030b1081442e0600d00400d040360300c25000416452280042810450143c0c0018001c0360300800901020004c52103400050b8403812590b02e0005207428640100000c071043d41900c20f003003280400603492040048001c1d40c5a02801d030030414150b40391130180513142d8400b01e644000c1485010680c10501d03600042d400b682d0321240c0e810160f43c0e41c840040c07009490319500080055441f40d403100340024480d0fa001548520702c3c400c00200280d503401c25006990010300050122140032841b0310310400c50f48912401419032080d803a24204c600404a031610025103c3c80f8805c958030381013680485e58018040384c0344c5134400020440c51a010b800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 34387523 1250 34386273 34386299
    0x6050a0e03010621020f0f0a06030f0212130b090a0305090907020109021201021b010504080901080702160b04030308090c09010605090402070210030905061302060706051f0f08210403020904021801 86
    0x2059204201d4140d986d06141012028141c100760040c011440c12821301a007600500303009800440d185600300001460708841d44459401444240310060154941f4241a2012140a00b0400054018100d41b40010340c004003107ea00c1c803000c1e26071101607610002c0c260300411203218081d4200c1b030b180810104441c4194001d0a5a00709691714103102031110b03041c1030807680200d40041c80782004001583c200e6010703d003490740c03010192040b94100319540307000562042050344543c44643e0085428000c142c0c0095009900031800402000380340c3c0d80c0c1000445405040c86502c05020000913842c1d102c1d02c80c2d40442d0015030300a4840c0c0708519030200c0080050840c45d00c00d07202070052402240e69503044423950481250010030032030038841d06031200f9000f840301901d0401611080c90b45a89211804052040288ac10304a070003020b40c0340c02002824281c400d0f08100c03881501d800380300070103601c0d10261403e41c0d0b019910000241c2e07680c804a50a00060100400259104000021130b0700c00801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 34388773 1250 34387523 34387589
    0x5041506080a08040b0906070804090f05060306060a03110103020c0303090307020103110705070b2a0f010c030612060504030e060c0708010c03090b06040b040605040c030203040c05010203030106050a0e030106 91
    0xc2001030340e10005207407a88203401d4002e14001e41040200404081031000e410710100050050340350401507a50040560300c198845000940c890f04012980542031003615071240d41940581414503100e00094180d1103103000080c21020803504404840e4825816258220f00c0c01088940d6810418046580c94001030401c1703000030b040c010140d81642c8500c0c2035508055000000740070007420817224400031f41004148241800070f8124484021024010030500901c0c514060003004480c24800e501352040000d410050604000d0100008e800801c945140103401c0040082c0320307142c602d021180c0085400740b650f407103000468034007103000c0d02140f424102e44078480200b01c444500d8030150300303684c000722002d0b052440c407100244050901d1340180951aa00420001c2c215844200041c225101268407100081c0d02008200c2000030070102200036000c240011405d561500100600e0741c49000410010088040d894002c60b480940103100500860014108400b103107846820075401c03048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 34390023 1250 34388773 34388813
    0x5010506030c15040b0306010c0209041a060a050a090908070506041b06030c050f07060b04050a0b13050408220308070b07030c03050402030309060a0509190608090c01020c01080c07060504 82
    0x444050081c03400207082401c0e4500744003a04e041514001c4040721070b4000031304042c140005038008074010b030746803507005110714840d05991a4600030b58050b103400300b80085c90340303005003810301c8180800e41c3c5801c0943c0440b101100c01107420314580c9011081360042190041041c0300300030a2108101c46003040c038805807a403607080c15413203545074011015140c000c802030f00403c40c00c210111031280100001d0402c40e0180001180d04400d400126017210381c122402c01406903a0005c0b065546000d015a41d49080008000e0085040c1a2290303041e500c80c01c680641c3c84045113182c0b070b000b4001040480f0007103030000b0000343c03036401c58100700d514284d0407111a030010b8038082c08101124060310410380203540180c001d504152954062107480e921003040750301801014800b403a010741e2009200004941c24202610a0600d40003028010301c034040d00c1c4049075049201e00c0c5a65990009014116001c00d18040b55907451301c00102c4454410709101070045030412042009000c08040b40b490250841 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 34391273 1250 34390023 34390033
    0x10b0a021002070f020f03010e100b1504050f1c050607020105060a0e1501050d06090204150e03070b0d05070c1a041103070305120904020f1215010e030319050f070501050603 76
    0xa9211404034800d07480d00038410640c00da81c4e240942800d0f40c0506180030041c0c00058030a1001d00d00318a021600174107003141503121407000c1180d05000100000342c4a0f50f0034414245410300001415144854409901a10a00d481c4803c1c217580104079100c282d81020985026041c0002c0081c041e05080f54828020403820500007078405513801028031071251010080a035601e400b00450b903580c0000c0f52401a0390315a4000309444074540300a10003094504000c03404001000006040e694840b0b101c0c601c281c004190400043c801c1e002101c8983c482175500103010b0340d480805990a015186014000352110f03451403454011010355140524001c81059641c110311504060781c0e0b04803030000130320700c3d08180305001250310041c0140084520092015080680d4107100207041d070031122580c402000e00d5001e1184082c103440c0c0c5080b142d0401e28111100510307503808240d6034482c199010359155503440b01482064800c02c1503455600621482d26982c0e101401d119000e01000e40b2954840d00070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 34392523 1250 34391273 34391293
    0x602070e010510020a02010e0f03240903190e130606030203040506010905090c0409020d080c03070c0605090609090a0b1c03030b0609010c170c0717060a15091a0405010b0a02 76
    0x200e036a04a4022a801040f00000546c0110342c8100c010910540010349840c045a0560703007402252402540350000d4104c004030f0028440f4510b002a002c3c40044d041000144000c10b00c5a8612042c1d100c10301381480080550001304d40c000c84000070442e41140b6140300420f000342c1c036800540c000c2d170140041700e5690342c0f1140c400080345c0d82540c032251141d2010241b2082800d2039001203640ca800142001114003084c0c590108a600040701445d0680001418400700080d0790280400b070841c5217882070402c640d4401084003071142224980c0301307814403000503500700f81d00c0d0022aa500300140c948801001c03260000710880701012001c1f4007290900e000590242446400d17580c0781d041c1650f800d2512082625000c612100072441c500c0c0f140d40410003e000340b803040050f1402054140b42060344c0107412152581803420140500802030b00b00351141240340c021001080c1030301c0c0740c980700040890009003441c00f0340140202c150307001401c1c10000500c000d001e2001d03000d03c000a400b59100100c0b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 34393773 1250 34392523 34392529
    0x3010b0d15080303060411070b010b03090d0306080307060f0b0316150e06040b0f0403050105100e0117060103080903010e0a11010806090405060112020609130b100306030503030c070f0206040602070e0105 89
    0x30060042c81c1c1e541c0d109200040c1d2038546030b0081100180521404da10704039154550301e05414003600005640c1c8000020300c28100d00400480e044919623103420080c4905118030b2944030b100e4910080c161a4a61954031001c500d55440005140c1e4000e0844d4000f0074007070b07012104001c96104800d020310365034140000780c03406048030b41810400203141515041c100300000c0d400b03401156039110300c0e4001b4000400068424401c0d60f004204890034078052038039002e50111031082c16009040744100202110406610004203d81520380c4101c22a441e1004030020a006045040c0c1180b01e81c4907030805242400105a0254503c00080c0d0f141e845aa035204140138100c0400d50300145654401d4004001d41d50300d4520000a240c4021701a91424a5060014041981c46c605a586207941c5904d248014508800c000c025200310307040070b110302850350f10740c2601c81c04020002505c900002a0703800800200c04088205983c3c010302081d1219120800256107034a02c1c041c15524440d1940040f640707103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 34395023 1250 34393773 34393811
    0x1030c0509090414030c0706030b030c01031e2f070c060804021c0503160501140603160e0603190813050a0b2205040f0c1e0905090c040b03010b0d 64
    0x604942541d44840c2e50302001015004d09000c00e9000500c1410441101448020300400060b60301107a0813048000301401d01c0341d03c0702e2490501d4a052002a07100c0080303494003240740240c1000203075025201140c02e981c0c040d0750046250000b02c648070300511a81001c054668207008410784c0040f244c480505039589a070030350340a503000c001e003043d00300c01c10f01005c0f00cc440c080c822401d0764140310b58011003084007641d0b8482102c40b40d455404100744a00c0140b000c941c828004c600600e140040c41c0d0914180c0380d081c4c000c0600c508a0200040c1154900b0010024102e01c2c01d00b048501c0d130074908010903681c1024401c0c50440000e80400112072134810442c000366604000180d2a0032140421030410109248403800c0003007415800003140ea640344260324259040010209000e401ca4000904a1250400707000b5040d041804180300142d0000001090b25801d0307950000c1911121070301d003041c0c0640d5010000004c00000080f90220b000d4000d041f00c2084d4241c141301030b0841c840314021038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 34396273 1250 34395023 34395037
    0x903030b0301090b0c030c130617090109021c0c03020904080a1b0209010b09030a05070b0a0f090b07020909030d0c0f140711040203060d0506100303080f010b040e04060b1002060601030c05 82
    0x841134000880e600812110013542c1065450500c10703d840901300442c05560015030041c001301e10300046081100e0100500b441d84429901e000300318803070300c1d5800a20306440d11a089200840310044071400c0069030a800405181c004000403001e10302443c0c018200c3c0d004091810015070354210048200708012041e0303940c03907401800c080d010781c2001c02c0c0000b541c0105024950502c520f64001002c990103100c118044e2070b01c0c0201030350b02c01130300c44054100d014042e000c5040000303480c000c0001d900f4603010b503030380c441d411036400002da210402064554041c01100750852481c10113444a5140c108021014140c000d440d030034981a2140c401c1c1c0031601541802601d0070280034031074800c0d4601540250741c01070000306800604002902d6161501208030355060040741a04c8040c01416040070460707901500069040748158107101035540e50b805284a01884500702c80c01113400c003c96600072807034501c4082c017503440060b0141c6009503640d00944450b80800c0c030b403002282849100d00121010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 34397523 1250 34396273 34396283
    0x5010e0613060f090f0c060e0a0302010512090102040e090c0f040504030206041205160507090f0204030309120c09140601110105010510050c0a1406100503031c20030a0903030b030109 80
    0x10400a07190308029020640c10f1030f00003135942c1d400710005450a8450b0960b02d00030581050b0440c18648041c0c4008011a1514071511a603641000140c5e4460b04a4003081d00f407540b01c2c1a980c60755950540640501e42188003a0324110042040d40354001070400140401103680380003ca08003014401194410340d80540107030400d40009000c60445500080d0044071454036525241a00346003910421076000100c400b908400c4042005912901880c0f80c021140913086141c9851660040d00000b402d214043c0301007114502c1c5014490007003e804014105281d0510108642d005041000c2008a580ea8045454819000c006480500c0b070181a44c4015000420580741c155084d04c15030040401e200080c03081603032040004041506650f001e14424004040c181800e05003030f0708540b03040d044107019900c180496061861400f074407000a03400c9640c0010b4145105d150103c503c86c902903940c40581000040c80a4000240e100c0202c45000ba0740070095482d001c400c060030f0307a15103080582 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 34398773 1250 34397523 34397551
    0x10c0c0b1c11090a0b09120d09141c14010204030609060506090a05010f06120e1e06090d0207090c0e0405070e01030b040209060d0506060c190b18120f040e01030f05010e06 75
    0x210415400c0018003883d00011f00c1c0490031134801c0ca14a03c0c0c0880b4407044c3d400200403284c1004800149048441d807000200d4281080c1000401d0416000c078260101410401c80c1074200544c222082d812034000e550411018003800b0705504000c40030741002d680c000d002c0c15000300016001740031846128107071903000b40340a848034070384181161401c000c0b0b0400d4910507a580701d840005c0008105103800000601144020420b81c02041070070a40018405812900030f450b18a1100e907021480384c064840081000601650143d0201d6482540341e02c920740061400d428400030f117400001102c11403009070303014015980c2c04030030b10050380280e40200f0b8010000b400413000c0e0003600c0c0c100550010000e4001741c01e205031200c80502d002408111058810b0481c50508144841f294000780e011851124507110b484080300ca82e695902c0040450038a043c0206d510305a1482003021a401015005003005403544c40c1d0814006000c80504116459840c0900c0300e0081540402d581d845014141d100079 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 34400023 1250 34398773 34398779
    0x20a02010e06090423010501020111070302060604090309080d180f030b0f040201051e0a08070906080711070803041806060c030219050c090c090405060102070f05010c0c0b1c11090a 79
    0xc0a0b400410f00700382e00a84407290004054203e20992491184c80c0328030701d8165140000190858860000d020f803c43e800b0408100443e07000504150880c1003518000303115140c0e82001c8503401404d0708410a24003408014011081d44141020444607d904482440790350303d03c10880301c0ea08500c0001d054116110002e458210040c071070079481401810322615040e545440440360b4044000ba00100c10404a076035502961b2110350a5070140da1400e0003581c03a401d01001070f10b0070034003c04510401107906480642c0c0c1c0000c0c09140024280001100d85841d1505900c030f84080704401d50102061074000e0002c0c40c3d500c990706103030001c1c1d01500078080c0601581c405490074070058100303403954070030790b42002c01d00d40364014000d100e200c442c0901601c80c0c030100300f00400d880014144a0440d44907640a1041105130214442218400d0a00881e62001c514100c81c1d02c209651001150000c08104220200d440d40e030501d40d44010b03800b0800001c006400b44a08a010750403943e60080b40c40b203024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 34401273 1250 34400023 34400029
    0x20c060106180e101d01060e040504080412050a020604090617010c08010b0c03070c030303090201120e100207030c06090c030c09061202130b1005090319110f0d0804030302010504030807020a02010e 86
    0x15044001070313007034414198551440241d68400400f100e82c207131207110010001c89900031035101150b0b204030340a00080c00e1030f48440c0107a01403401440741e0b840f14461003201f000710801c2125540c83e400341180c0c5d19259101c101b080102058820341c02c0c0888007102c0302c11031003010711410080c946036841c1e450040c1d0804082403c640c0007a0203c2041e0702c8200889008641d40d0114500207500c2542c001c207107603c09100050005182e20f9031302c200d207070030400010f9000b180864a040c55410510780140c03240b400742000c6036061484000a4803407880c10070844107005c900301c174a40c20340340240d084490f0701da551081c44003102c605100c0d03c5541d0000280c5140145400036188080700c1200350f0202c1d8040d41c1100086405800c40030880206900084800d81410180452646541c0c050341c10034004a0a8840ca00068521000c1c40e104180d5440f5216080e0b0303801c94550341c04d580041e1000e03103443d22407030068001d100a890940100f121040011003851000400031420360307040c1e58165541d01002d0038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 34402523 1250 34401273 34401299
    0xb03010905061803040b040b0a09050315010612021b10050711071401050c0d0c0302010e0304030203030909090115060305070816020a03210c020a0615120803100504020a03020c06010618 81
    0xc0c03e031603400104030006440c500c080141028008413200c1071b940c0e01c9034103000390040645074880342c025000704e8850701842c050718406a04444003401c1c20031994807042c0d0184002d12640c0301001c50350302583e01d030303480b14940041e1340c0603205c1c03184504100301d454413041038a00710010b0203141c10300d03406002d0a1006101e052003c207201603044c1000b5007007050764000b0a0914400105080010385c0c290180c01c01d06909000d242c4203611303440055880c0608580102e9200d1141064460148100d1408901c02c6c100c00d600140c0002a62170000f500b29486103401000341c0000c3ea840750005d01c42d0004543d000c06c00708124849400b00781c0090407507518030780c3d0640e8460b03030944c0105810301841800c4240d400071400340c1c04210100d5400742000580e01d03e8244201c5500710040c17054920480c0062104000c0034580881d0580c0143c0360a8890743c402c1050b891000c096040030303800c68000304500c0360b6503405030040d01d941e04880d400c0e901e903030b030703d0f0030088030001d03405001300c032240120b40b50400500b4020303c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 34403773 1250 34402523 34402561
    0x2100c031b0b07021002040b0d050c0d020f031906050616050f1204060908010608061308090a0e041401090305030606160b010602030703020613020d0b0c1e0309010b0301090506 77
    0x9040000c28005040408440407125058038910301c5078042000c0668188450200a014a0003c600786410410015014000c0d4110075103500d030b07103001160b468034100058401210b503c02c0155a03841a07900d40510b1034100f628071210f44500841103480c1100540a1f040030f8540240c01541013586c003503410504224508000e50b914003400d500304408540030300201c43c841c2043c440240e901c0c0d2800100520901441d4012000d0fa4513051050007070345004601c49812255801903403090010074100280b0300d110b4840b0041c0e00c0114200c0000c0c0d41703502042440d125501841d4030a80d88084100031030b0a80d121180300400203001000000e4803442d1520140019001481604000228681c0d071032680520a0f080100580c1c03000c030f01101007540c10002107500c5044504600e2070038030b0b6a40030544010346140b00030110104500061044038a00c8140c031049060504041c0c5012203d41e0543e40a034001d9130742c48072035424a6529403040c201402680c42c041d9110000b014981d4600310184042d040d00d00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 34405023 1250 34403773 34403777
    0x4020702190303030b10020321101e051008070c1403090603040609020301150605040306111c0c02060916030209071403040501020c0105010614070b09011d030405040f060302100c03 79
    0x31420550a4a540e48204065442600c00184c40d10100b0200b051146c0459001c4045500c10001c440704540310381c1010302516624941c2214544450b640c3c20f403080313216001049081020000d9101c407a1000075100101c420603901440b00400b110400c495a440c100c840d03c0103d200c000c25079001900901150384500442c02c02d0380d0501c02d034000011040c1d03002b540c05584e81da0321205403c0540c030b402c0c820b14002c44494601e8103070181c5400c1c00070348203019900c00036080503900e0403d2000c0a54000443d1040c0380f0112103500e0050b1400e14000043c82061601c80c01481404000382e000d402c001110100603901103100001c481c80d640c20080c4141001f05035404103c2a818500111240000030b180110300c20000561a06400103855017103e00507030144040020500100d080401c078901143d030050781002c0c2200d2966104281503014003404100802600803c0284081d4a4004006001602c40c1100c0038404044c010308540141c406070701010f90304c4040c142c10b2013a0140281c6907442c03054428 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 34406273 1250 34405023 34405039
    0x7080306100905040f05010311090405070303050901020102040504180605090d0c1412070c0311010c020105180301060b03100305070801020a0906050304050705060d020403210219170a0504060908010b010c0204020702 94
    0x35601240a0342c03841179581402c0c940301c90060040000510344030f44546402d40e05140c103890310f07031142581c0d100148405428000c2c001800b0b12640d01c00c2d0101c402905010f8800d02c4000005d405c2d0301d8108110381810303540c480c40c08010034505040843c0e4004581c030030340d41e6610340320407a4441d0b0007080c01c000e0701d0301502d110f00303480145903039420000b07000300d80e000f4600b542c050b51850a044203090320103003280b03040080c100c10401c0140c2e005029904107c5080c5169180e00326401c02190041000341c01c500c42c2e0103408400c00800d800c0e00501c91b4103070303031091080e0345031240d41d18102030907802140c2001d404140071900c14040310b880340c1d0103542c3c8180180d003203034052923a90000c81ca150380070035080303400a41c0000d000d1080c0249009225804d000000f41181c0c1c2c81e403144d5009494488091044070b00100e103031904014003881e5100c19409120080d03445035546101103008e00b00b40d10922400300422201c0c400010f0888040c403541c00c8402d4107031603442002025a081000a61000340120b03446110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 34407523 1250 34406273 34406279
    0x50a09111207030c14100206010503030301060e1815040c090302030316082b0608030a090509070302040506031f0803070807060b0d06020c010b01080112020d020607030e061603090b070803061009 85
    0xb0700d0014004c1903001d1210741640c500c40b0522441625418801b019580f058004101c0c940300041240d0440c1c03030314074143c42843c210301c00103404101c080c41c01c04d14048882c400c0c000b0f010419007030301c0c074624011503013008001c1058105460808280c48003a40c960000e026500d141003040d49015071481c803440089181441d400407074003d282e82c4108605c8040c00d08801b15a1590f800d101e0391010f4007160005605000c0c1c078281c004c1802043c0d014403070044180703202140840340640c054401801f0003c01150b140d2400c44c0d040402d11284c0140c0d40550300386100b000034164004404c4500c6590001180c1d450442151074210243c06107000140d0000d07410501c810115410307201800294040d540085403000034500018000c1806810800c5c81c035030180d00c000010b9481ca0b00d0552507a90584956403140c807182000d03945c02c211031401d65017040340040c00703107100c0d40c590400d80e100c03030f1280d01c0c0c0002454075640a0103c90040a02c001c0ca02d010800c0809d400d80340500c50500b0619503450f1082c0c1c0320f51 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 34408773 1250 34407523 34407533
    0x70e06090702191202070905010509070e031f0203040c0f030305030c09190305030d050a020c100902060708070b100815010302091017010218030c150a03020409060608040501050a0911120703 83
    0x820080c09880040701144280c07420351741032210b18001e080080090156506000c002158404040c1656041c4003c0004910682c0c6044c04040c090070000000c0040c40d02d00500300c0c0000e588110760485d10404041c1c00400c900300c000700c0e80c3d801d80c0d4041c1d6400e81556590b01d103000b51b075800b8a211a0b4400c080e0558008a04540482c1c10050b42c818000b4603228484803070105c054501c00340085210900520802400c00320000e841401140c898401140c40011400407885601c100b070005881d020000481c03405226011305154011056543c00c5920641d0310380e00300e5103e00c40380012042002c5603400400240c07801d2220320741c10211103c2003000316a500d44550b00b5542140c07441800f070342d4011624041c0100c0f0312411048aa90940c09007100946844c0054201c0c070004610742d403200c502142c5c200318540f0990644000e401e086000704981a140d28001d407003201e0032503040710f00c1d40c2031100003581a4040d00900c10f440c0e500100c0354410791070b81c2c0c080100e0b035210320141595034460002c0c00800b0038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 34410023 1250 34408773 34408813
    0xc0307052b0801050f130209030102070602130b07020d0f06020d053306030406020c0f0f0c0f040209090106030b011101051303020c0102070303020c060d1806140108070e06090702 78
    0x1e41c0e5030015050040000148441d5400000c00144010300c8010025034580440d04030403d0700403034900b662441c90303a42180081c0a0300c001c1a41540c408247d00e0b040050b01d50040c20014059900c07003200740e0b900c0c10348200c0c1d417042e41c40c02900b0010070069040041c2404404131401c034442c19001d41840681454641101d02c201c454000c08003d2040c045c5078400c95414480c102c010362158082510384600100e44039110180c40140640d500080740c100f43c0700c0c1880101d290840250654100342001342ea801c1d5961042c1c10510702c40d00f0686520b00c0301d80707054800c03a43c0c0f24401821000d400d80c0b0300501580107003805e0040c2c0d030501002c2d40304003022010a00c901da01c1400300c1780340b00314100c3d0507042c005d140002004289040d503100d01c000b4408660001a8404503160481c0c2c2281e03902c45a51241018000c03003507a001c0301c41400000c200810002d0b4000120003055014900110f170703a20341d10a50740741028802c45580c0359100021850604040c828917a01044a00464910b079082090041c580 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 34411273 1250 34410023 34410043
    0x60c0303040f06060b0901081501140408011b03020301060c0f050c06040305060a20071704030204050c0306030d09060e130603080c0703060b0402030f070806150313020a05120a080c030705 82
    0x40001240c0300c0820401d4440c004c080c100c2c860300d240c1408603101c006441140301030301ca8030381000d08612140c02c40c0c0c480c900444410b0440340c4081e4031669a05003641c040c001102140100b60150054012014800d00c01c0e64101c134110b81d500b45524030386032120707a44202e64510641d4680926450596652107034001040203602c60002066245004d503201c034209d031168190f50f4940c0003c249091221007000c801e6615554210b03104114201c3d40254141c202d00c52640020340143c105402c11103017210100186109180c1642a94a1305009680450b120381c4a40122400324546800c214400d00b8003820170001075800c5440082d1107522a117a201943d000803400e12820b500105c014003c02c070b40c42c0907000c40f0603819a8203600f981000151820448002445902004401d0000032a2980c0308408280c030520f50041031641ca02b80502d2920f0b1000c08140240d001d20000c1600068504011701d9410b110100c00025220400003039445e000590f0000315030602621044c00360401082c000d00600c1c0c3d103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 34412523 1250 34411273 34411283
    0x60507110708030c01180c26150103060b090601050301061b05010204030b070f080108190201050d050108070515070b060f0d060507020a0b0105030109030f08071101050903070b0124030b060c030304 86
    0x549414401e41420f481580c0d4620311081d07042c940001c00070b07400019801c1688c0e10000416034140d1405500d00006681031205800f520074012200f1000c1c485040842c140da000c0c07801030040204070024445450b5003a241e45002880420040011074440c1404a0103a10b680702c400c403440110317454507409c0e40c01541080c1c2c0c00c540f6900601c0303403040d045141c807080d080c3d0a052a0203258540f03510790381c4039070180001100c3c4800c030240d508116840b40d01210721040c020300c0c04110558541240b1a0344040718094913014008a54450000307140f07500980e41d0140d40070319401680d0f540c2c041401f0000d02401041070708103005950400020303d0500409101e002c055005124840407410581d206220692156003e80d1600c020f42010030b9000400329400851400d005078a80c84032401110700c003d5084003032180d07503c1d003424040805004001054258000c40c0c80c8029a40c9400061180a844a2110500300311205c5241e20950207a01f0428081c0001801c250401c82d8008009085a00442c1d040360 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 34413773 1250 34412523 34412527
    0x6040b030717040528020603160207060e0f0d030e0303070b0a06050a0510080c04090908120c091f0306030c09050a06060e01020a020d05010b03030a050310050907090306050711070803 80
    0x84550b61100c0e519042500c0c80c000080681480e40710280c50b130a02c2880708030741507080621000c076000e11100b840034071036000d020181c0d00d29210030755a0740c20f90b4103000c207401401485c80000b00d00c2d02c0360100000120300205243c00d0005a002000400c40340441c04070141f1116004000b09554248040c2c4800f41c007500c5244002d160420140702205e1580d0080791085014041c01d000c980c44001c040b10002219080c019000c0d110180000078074040d89c0d02051002d420039001100b0403000c1405003148014100c04042d90f03481d11204014140582040c49400c0210840e91010040422030003110040c454140003440b1910b94690110040c0c6541054000d04d841d1828400307048114810360b801007005103446d040203031000c030000751107070410640684100480c02110301802401e6000c17400c0080b0040407a56601d48041c0c1c0600242c00485048100d0125050001501c3c00e0801c40c480c4035018650b5006e0040f41150382d484c00606019000c8001c1080c48000c00040030030400c41840a4031003400295 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 34415023 1250 34413773 34413781
    0x604141609050913060e0703050f0c03060f0108030922020a1106090d080c070c0504020a020c0109120f08030408090405010314161a0a0c06050f0604050f06100503060307030206040b03 80
    0xa0849002a403050740298264420010030214040705084410392018000c50711002c0240007e1030001c01d40c00c050994040d095000802140002d5600e800410503800c3e46e01d00d5030f418081002c1c0400910990905420800c010072561420407803521003010b050012880c1d000c200224082260080710b800000b1456038401c58100b1a401c000e05030f80000301800034841201c1900d0010b00241e4041c0240c00309202c04185441001501c10010020b410b001c0c0046448030010030300207645801e40301405010800550300401c0c2c0e05800c0164001c030036000b101068098850b9680c000b46640020400d44120800b400107030541d540f680a800d000798003a01c2c064600a032480707070240c280995544200d40c080c4807040100520000c400280002e00c0f5003810301500d0b18208402601c0043c0508401496540351000700500034155060190190b01c0c2178400301302542c2d8000a510800400351441540040720100c0c600c24141700e0001940d014201800307544481d682c0c0e07804520290003d81100c180018003200300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 34416273 1250 34415023 34415027
    0x1d1b220504081c09050703061104090e15010f030b04020603040206090d05060103020f04060e0c0702030304080f010e240a1505040903030506100201060501050a14120108010c08060105041d06041416 86
    0x2880b0400001e00c0104403280180e41c5d41e960300c0340709110041c1a140c56500b16810031645c031040e50300800c416201032082c074104200c1c458841c89447c0d890402810700d0400416181d80d03112002051f66130145008030503440710b4003001810f400082080303a0200c1d04224610454844c4040300070760318842e4009008550442c03040180e02d40c143d14650340114a081402c2042500c4581080d801003031b00c02e5036076582c14190020a0462040d50404011032003002060603a80300150304c804052602201903940c105512030983c08950200d0840c000504050000b00e0100c9032954082070303011200c03050004885581c1e00c042000d0340d4040d241680841c0c0e58004101c85401e280b5002007540800340b000b042801d0030500082d00501481e1400c50400080b031051210060a510449074800d01b0500300220960355090350901a00b41040f45400081118010805650041c82030758151850120880c40c840a404030280844100814940e48291500e041404001c8103501040c0a00100d01071121100c10340b03100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 34417523 1250 34416273 34416307
    0xe010609110316110c12010b03150103030905090c0307030c090906080a0c080a0f0b041e0c2606060d0807080d0b030706020616080411030d031d1b22050408 68
    0x1507005114645048031481d01c00171520030700504c4121001d440000340d4103460307801007d44500f9280c1603c5000b048071a03007441d89103414100e0740309030f4640b41c005848400b41314020409541078444001c092011604550291f048030500604a282640d1030703654900ca413006881c85035001c8840c83d0010006c040a02c4103000c3d43c0300c060409000100510001030351099034040050601801c990103090101d0200020009a40d0a0b8110748091000c03810135400c08403500e0314948110841450540d207840c2401c0c3d0248521031581d0008809001241d59003000c1c04040d9241c0141200e2f001c004010002c0001c00d4070b00a000084426800084c06002071403d02d803801c903054010703c0565005000b08504484264050311101940c2c0c03030607070002d444516041c01007181081089505008103c0b548038440d03815444480b11400154801019130140107440e40c80d2840c2c041c0d503803040785468400e954135080c044816030440481c1e1010742e00340d43d81c110920044860603601200e9144002505190880301205 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 34418773 1250 34417523 34417561
    0x50307150c0f05040e0601050a26070806010f0c03050913021c140c040308180303030a0b090109090f121e020a050105070801050105031504022a12070c06030e0106091103 74
    0x10f140b4a001e05002c03450501100052086040010020716035004c5482105165041d0680c030107102100c424400038140d242800301c0345000003030b1480000410f60340c8a041030409940040d201c0001c110fa0070344085410350702040074107802011408514411a5684c03009129a071a00754190784002c0c10161004140c909441611003445c2402060000b410341c0a0200c87c21070740e00071002030351064480403180400491859240e814000403080000d804601c0d04030f29102e100494192900e60380700c1009900b2281c54100151090102d0110f050015880c0ca5002c103560185003070040560542354144545401c140c4182070050b0002018082006024054903400103034034101070b1095030414000a001d800700410903820b54240501014058031180d0440f00307001031420160b28040e0940d40c030345600c3c0190805130306d0903120710a451000b01076580180c451f641d5002d507100502c0d9281a9044002d020510070803205556640d80000d1807040a00c1038070400154800c20750303201c0c07801110305a24814080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 34420023 1250 34418773 34418777
    0x30b01090507021203070201090f0f02090c04080705010305090328090e07080402040207060e0d05040e0c03010b09010c0c05032407020106080d110316050604020907021603030c050307150c0f 83
    0x10034042c00c03a401203280d0503440001c440c00360b129910200124050800d201028040c00e048004a0003440042c07806600400c1c001d8503d1880c0b620386c402c24103103c0c499403142103c3d6130812035041c030840d1700c6600322a4201030000c2c102c900b00000f00300c1c0002200c0b00034000c106040c90441000b211550000b803d18000c2540c19680d001c640380a082c041d040b0f540043c00244110382c0003546004111443d4088401e100d01d039000c490742d0001440380904640e001d406154514110400011703031620080781101c2c18bd42c1035490041c00d1109110041d641c0701041c110440d0f50070144d00020560343c42c10000340800050500b0811240202030107030b401001d001801002c11a418010b0501c100b80c800034000040c1100b5140c008800c101040d034240c02c0d801000321a06044101001181c1031101c001003446c0114003c0b1490151603c41500c145e80e41d24130802403c3d0040d4001108101003800342c5c0c8080c0740980603800307032032414401d03941741c0c00700d001090b02039640030b03075030b01c00051030150300c80c1541e03031450224 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 34421273 1250 34420023 34420031
    0x12060105270601050a03021b0c04110315120f030c03131e0b1b01060902070309050307121e05150103060b0a0b0f090102030f04060906030c1b0605040615030309030b0109 74
    0x11200ca18401d5402801a03061180000d1200719a45c8640c2c100d61826401c4031000e080001600d00e40ea44440c2c22a003014400e44c107114000d0980c1440340d003200d00440c5e6204a140d0340d100404180810600006c1990b4a2400b0759013a03030702c17521010300003043d40700c5009000d03665844a0500e031000004090b0040310201d03260300d44003d11082e041c7c0040046d2404c41500b142c03501d940d00190f050b880d125000c20585942083c83c0010004015000341116500c6034444185454954050564030b12880c4030790385c0201c002d10100c8000c80e03624000403540c0012a0a100240110764469500e000030202c03144402804240040007070108034804d0070441030040b181c43c881c06160034504a4280a50560f200301c40301d000130300307009980c02002110011401c03007003500d0301c4a40d10b40c0064000d6400c1d201d0f02d03001c01d040c4010819003030b120302e850400301e01c0001540201001e054494500412008004549881e5281420300d40c040300034070b07050011807103555040c000904614201c50a5101039118041c51820 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 34422523 1250 34421273 34421329
    0x607030f09020906040908130b09030106080327030a0f11090702010605060a030b12240604090201200718020406030e03070b010e09070b0d1d0d08010504090309030212060105 76
    0x11100320f503030442c07000c0701c0109442003d802c0000741407003400300390741080c81052800181035942d400035244400c400c0340200712183c0d07283c01e09922445203064501e030054141c80242001855000d0140785410f0203411115806040e40d151204003a201c0700a0742d810043d407580c2d200510b0000c821560101c0144000d018092500020403c01e02a01045c0014903441e80b000b6600341d280c20340d9400035200300508a4059030b015440254101c1440c41c040000c05030080c0004d01241018090080030a0381030b910001001c840c0c40000c69107c0800c0900990340c0125030000079081440444801c086203071510041c1d41d00c0c076004014044816000c4824000d405c1030002901107058074070701504594404d244c140303503a5201442076080c400301e40c10043d810039011401400e20b140300d900c004283d251a0124035801055401c425680f0341c4200309a000180c44100144518200b941001c212a442810304084440c0c0341e03400500c0c0c05600d203070801c107544c5c01100100160701c1d002c134031b803403c40003c08241125550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 34423773 1250 34422523 34422529
    0x30705090a020d0b0901140310050c09060304050102120103060b10020106140f060c0a060c0801080a0b010311010c0c0b07110a0b07170c0f0c0a230418050601080607030f0902 76
    0x801080c80c09a02e501003070030310341c0440c25004190800c80040c10b0300a250303111a942d00350380a860055174060300c110007401444ca895881030500a80802d64024241a00941000015440140122030954003400044888014000c2c0c5078040d610500f40441c0d4810050300744000000092114011a81002010055910940445981041c00b07a0310943d407401c1c5000840d0445c81405030b469818880c000280080c84403942c85000f9914030742e5140849641d0b5103050550b0780030702c0c1801800f4400000d004000080c0034050100c0a06010f0401000d80c0e84162940c0200c0039081c2d0108840c1c440002d0303010200141180d110313120050032100c03203401c0c5060485182d11030091840c0209140e12041150f4800304604040d03508c4100c1074002c841901c482000303a80d0307c4010b40380f40310340076002d11100464030003161000c4001d170803422200520403054000800000d0700440d1203d07180342802c2c41d203074004680188020303406800c1400080041d420101c030010200c40343c845140103080e1a0881c401d0043e9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 34425023 1250 34423773 34423789
    0x901080412030908040603020405100503160c060612030801030c09050c0a050a12060b0711040506010509150d061d0106032306040609020a170a0504020a030f0807050105010f050f030705 81
    0x140c0c0000601000315501c14064004156a20300a030101c48081000a103480e4150018002daa40a455034000c3c007042e0700701990640820b644080c406902d80c0c00040140e445500c80030030160140801040d460747c3e03500c021200795000c03117017030740024514001481401217015000008120954041000d131810f41c4101081b03014103c000700802a00140c00c2101d107108035903c054048400108000081c2da400f1103445581c03020301c1c1101c2240318400e0100051030f1038422944200010b8407207a10788a4144200301d910304051a1141c000003061041010000d080d1260750007520302454107455003a98401c04a10401050384801d003054101159184011120b07202000901d00600408003d51140400034020303003040d821856042d480403d00000305a0700040d45603d40802001c111b4658442c5141c1c6c1050701d100b1100650400702c01e81d010000038022500d81414940119900344c00d111342079444c2401d50b64281c1c45180e501000b51400d0010385001140000c07600000c0700105201c92818000c40d280d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 34426273 1250 34425023 34425031
    0x4030e09040305120a091407050a05040e0a1203050117030702060403030516060c0f090f050a030305070311070f18020309060c031801020c0d03050f0108030418090b070f08070302090108 81
    0xe26929404902054003c2081e1410100541c902c2106031502000980003800002c1c01590070b04082003a1200d41500880c030403081d6000501100c003860f09140500014243c20031000f26a40700d11198003010801070310060307041d131403990340120b400d500d4828510074680b020710450f00349400c00c206007001032b5940011501180d17418200283c4801c0d0311440c00747d075142c1608000e455981800c01d40130010f680407180c18000342c55a1542a006034030343c1c940110f0a900c5000342c9402010220080c030100f4082e04c0a848094882e20b070100703407151809405030408610750301015029040300b0301848010000c401904100e0b440e0704045055142c6030884a94441c070140030151102c2d00000407852581d001c5105806800200009543d900d080010480d0b4401540b000203002034034000200d1948c41041c280581211001d800440c100350900f5451a04016220080e0f00c0781540d800620340003400420080d4400e1649807035070f042140f104000a0840c420080034502050b00c1005083c180e1b0b03070000f41080d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 34427523 1250 34426273 34426279
    0x40b07020d020d02030610030b070216030809030a020607060b030601050d0f0609111503010905060f060d0f0b090c070314190809160807030302012007030503060310020a0c051504030e 80
    0x407010707240c0040380d203642110401039018011502008840c21070104d5240c2100d1043c200012a65514072003240c0341c0e0f4605410960f425070310301080010031a42405800d10f100010700b5102007001c0d607400504142e02c6540211104c03900d498504c203641c42c06100c83c2e40103080988414460311000d41d580c1800c200da50b440108260354400414051040d2103150100305031004c2c12070403400014203560b07003c80d0003d00c00d404801c0d0520000170314600b041450400f01e2f000141010b414400102581c102801050b443c481000343e803003070306106544e04e1034940703070007020380c0794415a49140d1800c000b03005a02e044800e0001d0b640030000d01200c1c4c4402d1511080071144c5140c081c056442e01403000e8184030610001e110907106113213010580c51004102801260300ca074000704460000e03404c0510304030030100c201a26203001030080c040428081d10042d940444020192000e6000c426135100890300168400c01c000303a0481c2c0da4004000d4104440e400900c8800030455840ca0255402031444584015041c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 34428773 1250 34427523 34427539
    0xb041202090405010905010507030b1e010804200301021602010e0405090d0c0302010b10090f0602010e06060609040209030a06020307090b03060a06030b0111010509101a01300504060b030c0303040b0702 88
    0x1050207420342c0403170b920740ea102d80240503900f0714080060141c8008001d10b031041c0c178105000c0401048503148138202081c1130311501016569038951464940c0c110001131303100002842100c000e540c0c01e01c0105030314100000c25400740205800014040700815141d40c1c000d0349080c0500402120015191988075a81c0c6000c1081882c0d41c54124054652141495003028a4014501d01c894007c1d080300d050740c800030038840d00c072a61090700300c0c2601d484040c040380b40d41184010a10b9410220001c040e42d0310b01601c003615051407040444d250129102040e03807941e90100500403010b031701a401c80010003000c02058254140000041c4031601c43d4800c10003411b076284c15200507a40a49081012a2250f500800480c944211465110f2010006003003d41e0710700038220100300d003540305501c020361045e9a1b0344118841c0080d404902d1341007007035401d1521862071000e42c0704c00460055900c583d20840c00407509104a8082c189449054500705200b600140400c0c4003600182c01a50310468040b52010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 34430023 1250 34428773 34428781
    0xf040e010603020604030b01060e03060c03040f02120a050105070f0c05030315040612030503040510020a0804021207080d030b030c090106050319090609050f0717150c0c03070510060b04120209 84
    0x34010400e580c002504808085030000030320054800f040d0498040351101000e41001c102010f440d031800701c4465544d86824000300e0089039140034070042852024007015107881030b00c42101d2901c0b4808108580c0e03030307454108001189034890900b003407601d4075040608044c8810780e0b949403a4007008142100020110404a4240d50745801140040c854500c007124540d40ba824014815402200c0544d003034481c42d60061441600b0b4070817100700d000296074080b02d0751940e1b401c0088031071035520780080601c200800814605814813101084103103d8a0000301c0501c050709041c02c1481000c03001c0c0c443c0030030000410982d131b046021a544010030700800c080d0280801005001428031080c0a81030500d040f45490820a00080200d41d108022045403002540e900031002e4a4501580414294001600d84240541d11550340c5410400024100742016059004980785411401040c0c42c642c0c064550110100201e2003894050325010b80e80b189040c0c1003a22140b50f291443c00b0090040d44900c00103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 34431273 1250 34430023 34430051
    0x5090304031217060919090312180c05100801060503040c080a0b04150b0a090f0608121b060106020a0305090f04150504060503030304050d08070c0503030406060306050a09020f04 78
    0x103502840d400000d88201c06140100108680158004944640480c0c0040b0300149450608070340318481d8019003501e1400c8030040a0050326441e002101404403d000c1c448513003c842c0a0a10400401c500a00711841941080b1903807030400c1d4070080c01110010b1407900d820b0392242506040d5481800c1a81e500d417940d241403070030301d00680c3c4848014002d050421040000303103241140a140030346602601c58003214241400c4a03084204140e0068002d40208103400c1c4540000c226100e00c0e0f000004c01a5441c030001e030030205c0e4044c45200002000804460051350204003125903035100d4010441c0f5030508002079601d40f22680b01805010307000ca2100c0c0640e942140d9012044005401404802d10b11190314090740c0d414018284180c0c10403034041101c1c1800402d80b4415a0007400070007507030010703000c2620102d801801c80c400300101c5517045d00102d201080114051032203003400040d40392850600354100c1c2c801500820495040c200f075507000d40c1d1403640c20a0141401c413000076044084c0814 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 34432523 1250 34431273 34431277
    0xc090902120105010b03011a09011d0a0b0309030702040c1112070c180504060f020a140f0405030f1c111c02010b030a0510050108070b07081c0203180f0609030409050903 74
    0x51441690708041c008071781c3c0d200d1140954100c898004036841c0000038004200c405008064013240000d000e0048582c4010613914405a403030b5000e00b4984a098444150300f800d64400c403110358040e4400140c0c0011418280710300801c22045107090703010350607496000d64490154810740090218045500d0b806c0c0b044440083c0024014190703140b080c80b45240c04000500001c54060322040d207411100750a00000c1e00072290750724000d60796001725510754544032825400252216006200912000c1043d480421224600b0a60800140307641d40c00c0d104801840c940c200385120030085542a1010710400004034103121001d8994520080c40840c0e00490040010644c09645886141c850600b400000308401c0b421941c1d0604c03d106aa817070b00720407641d41c0040d20034005420010403042010800482c0a0208411101e0030321582d500648200d0040e83c20581d0740601ca4095424801f4091000300b2542003000b20f107101420325444c100308020b85a028604c50620065111000030707259140c2401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 34433773 1250 34432523 34432549
    0xa060f02120d0e210f071b030309090b04110405010507111009091103090a080d060b070803061212031911071428020103090201020a021302180d0c090902 67
    0x301c010388980d40c032100c42c00548500111071070940180e001c0341c1c10604a0011a0b021346207600f82032803500080043c1d401c0d050b4441101616020140c11106040b0a440c4e107084000314040d688015145040420403401c484208a0042c807992420080030703803460400d420741d002c440007400c1298480d002070900c036900c90a5103200a40c400c03500d0754001451600409017500f07441c00080d04102201d180c103040d4095220a40c1c040913103a01207000000094035510040c80b64482120001c201c0310381c1c4603040c0c004c5800044080701c90302ba01004100e07440c00c011002e41c1742c1d8034490005180b03d1800d5440c0301401d01c0040e24201d194240800380c684448050b8014200d0324500ea165940d03143c0150400740e00030310006d405c18140b40521202c042c008500850f82d00d0506551800c004800c02c6560700540c014801c032070040741940106101e00026030f49940904502007c0001d02517503030180c035420506180c481c02000307442010700d80e14110100f09000a68000d8584041002501071901d00001b040c0801010f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 34435023 1250 34433773 34433803
    0x110c0105010602100b09091504290103111909020c0a02060315030607021f051e090c030106080d0903080f0903030a05090301050c04050618010905060406020c090c090a060f02 76
    0x3000000c1c0460380010706200f00c941003003082164451030020055022800c0c4c40135a8150301000888007003558005400780c100344561405050a00d84109803561101e0301c0402058240c0c000f00108244403e407100011002011280314800300d051308060901c400150040050442c2c4c00300b120004000200f003450300094006100310313268076052801d08850103106030480d0090181901081105000280300b82075443d090410000c49c461480b1b481d40140802006400c10b0355480402c0201c070310000740d444d070158a100000c0c14450380c00c0307000c1c582501c107958440030036584400e140d9080359500046400980ea440303204155900f4404c001c00303829004103406260300d40400a950900160007400034501031311709034024406981c40c002a0f08103401244103007a0021010060040f504017100402d03000c1c00414107045512540325008602c0e21340140c1c00035405a07000c90064003203403030700c5009240d05c00c100060b4076107090b400101103800c49801780b041c002800f4105100312a034030700030f00c80440d10041c01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 34436273 1250 34435023 34435031
    0x4080102120a060b0c0a06090c09090503031b030705091e091801050114010e130e060c0d0b03010b0f091003020d120806030a02030c010e03070506040902091905010801030204110c01 79
    0x480d01905000002d440700c40105103404000103501c0c1580c03098454411000c400f91080148648841020708200501203c007030b641d60f000031807411050300c41c003000a40580c00030368580c501580050001d140050014100b850140100b1888940c40400c03a080390f041598a89500804644160f842501000712241d002c00d000c0c0c00c114171102d01c9107001d01c1d6115590700134009641e84115030440d410209203000e001032000c00381c002039400d04071400003907002e0a0700700041e03050604441c14144881541d032010103c10014640584500ca4001c400d0300c80001c4008012580c0964005507108001c80901c034010b02c060710001e1041c090500c0c00b1002144c000c0c0048040c641a8070b080d8030014003103654440441d070150082800d5084c00908603400da0717400390082c03110445183c010741d036031003200428039807620811a000c10185c85e80710250000349544000941c03540700410420403c51240002c51004035102c48040046e6130b80314070342c00e046a0301500c00040344000b140d0382081c94440c0c3c0705080803560034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 34437523 1250 34436273 34436287
    0x50d05090328120f09061d100807230406110313030f02040e0d0903021c02120c010f080415020904180c030b1005060d0b031e0a0c05090103030816020304080102 70
    0x2c480b8010b0981c0d215648581d0307803a0600c04103540e003181e4650a4030001d010480c0602401d40656140350112015220328140300b2940400541d40070f500400140004030001c0600003060781103100302c070700d111003014403840d620500200c100b40c601603881690301708112060031810b400b4060044800b0350380600c20b40b4034030381c2d20703820320598401c40944102e0181d443c103c0164109100411100c1030725000d651800f07a540d1540c2c0802c90954a1b405a4440ea4403c080e0228016900c144550f0121480d100140c0a600704080026150004c140b03101e009000d546000c01001030b4181209101800794000c0041c3c803456208045002031001000152100400d80658000d101000c1c400000312441200380c1415903880d0000e40748140180c0c450703103821507000e0100300312624150f0407186190b4000b50440310012240d04481e00518064405003043e034120252a000b44000d90741c0701da01900007500c18217100c1d45165130003000d00d8401000440580c014041150001e803085c012100108070704030096441c2c0391 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 34438773 1250 34437523 34437583
    0xf0303020903061005010917030901030e03040b1b0105011d1812030901051504020f040303140909040f12020105060d030305090a020303030a0e0c0f0901050603040f05060708010e060904050d050903 86
    0x101307800f400e0302156043c000041c0d6010584505041111103030301441c00c2c40d000b0401940904007000e01c03001240418000414494502c1b00035005000c40d52900e441c140d1100e41030300d070031183c0c1070308102d22840d1019010501c1da2070f01030f1466080380d500028000c40020b5001e2060908400c865031070350010001050044070001504258040c40a00045917040058038041008910a18408a110758401d100420109009070316400c400da0461903810f14205603400000e09a2008030341c02c845541d000b403455818030481d2083c0f6a40000540000c00182c1041000621954462080141055181c0300040d0a20109225103504103034060101c0b616814040d43c41ca014160303901103500d217403150030003203216032405018003048054041e12440c03180c4d0a0509105507540700420a4411a1071807414030001a410050b4a1107105296942c5503294107100405001c00e001500c802d10444ca24000c1c0f0000c51408140c4a069036402d0a0131030740c900182000c00e040050b0340c0b98041c45003104a80402d4205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 34440023 1250 34438773 34438801
    0x3190203011d0a060602060a090c0e040c080706260405010e150a140c2d0703030c09170709020313080403060c09050907080127020304050a030e03070806040f030302090306 75
    0x81040203074102d442d42d501030400210748091250500580c40751000c0f41c050700e1140d2100b0505070142509007a203a031200b070700110f00c1d042070381c00712500021054100304240042c400ca0014012600c1c2c0500035040c0048000d8218540e64115144040c602c0049010044258072005014086a043d9403200c2280300480403481403c0754900101410424ac5a00c0044142d40da2445802480116810604a07040403059100d041459003480c1705007041d5600c1440e0031038041c00006103e40c0d0082846611510024070b034115940c021022404081403c5a20a20204503030083c0c0355803100c0181c41e6501c181e8540d03950079442401a018050001e400310502c541e43e0091b1400e044161107441e503a81d5038600b0300240c20f0086400c0da000503186001406081c11900001078500392241507035030905400151a01242d101307690031190ba03401500c50508050b0400201080d4100440103450000c0c034003100b60392902d200a01c02007419182105000405003e80e06481d01180003504440091800d0f2030070244c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 34441273 1250 34440023 34440059
    0x3090c01030b0111060a0501080601050f030a0b040203070f0308030a06210b0601260612060402010c110303070606060e010206010b13030303110705011506080a0203040210050904060b0a32030c0319020301 89
    0x2b8002c550011626082041d201070461f003001d0018484c094564442e402c4048000c0d008985c507000300d4200081d411010312469003c1d6004800040d42c0381001d07900c1c241103503003d5000c10702c902ca1815692544001020300c2c0513056800481c00740f0550b45820041342c91110034820b00c3c02020507050707002c0c5200ca00e00a854801c0c001030710014200c045c0003848595560301140c00900003000d6100d900b0005100e11807100c00b00d400941100c0c1030a00e0350741c07207005484c0c0035008500001c1c0f0101140400d9a8100f0115005210410340c543c507220072488003039400b110f5400040c00341a11484010100394103002150f00c410341010080000d01e001001c1041150028402d680020b0a1a400700d03261204610840c0e01695000300380301210a4100e80030346080d04102c858030782c27182c1e88800002d909828034008244241a0755614929502ca1020b20144031800c6c00130b005510480403060111036400b101141d401c000603104e1070303840e641d801038040841c060b1946527501040c0088000103407007080700025411 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 34442523 1250 34441273 34441289
    0x605040302091b07080a021009060209090708010e01062708060912030c04140301021204051c03090b0c03040813080d0e060c06040303050705090a0e090706020303090c01030b0111060a0501 82
    0x240c4400d03c04030450302480035010351a5504200410000b41408000c2046402c14010b0f1080d1b051246862000c42c0e00100090b03c1940e000079041185181c8011b03482d90140c56030400043da54145140404030703500500500c800c2c400da440340d00100030b0601c2065001e4a5110110030012904c2e203042c59103862080d41c0c1c60001d84640318600e2010350880c01603a00c6850000507442c00c00707180803842c0e034103800d5514440d60155400c0000d05851b0100400c25442540510000e0010000481d00d003841d040d510f0510004041c6040310300340008802801c85034000c5581800d80e5100d483d5414007218511800500c85062660940000780600b4085034000b01c020707440e16044070b42070b010001d0002c7d61145240c5048a90821000500020300a03032000e504110039181950504840e0070106800d0881354002000064502040201341c0c602003003c8400340c14207101440c114242801c0d4540d58800000c509414192a0112151a80d105e6801218058122401c0700c8050400c08160340044c40d00380141c0c05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 34443773 1250 34442523 34442539
    0x901080a0c151d040204030605090105040b07210b030312010f0e07030e101a1e040c0509010c0b0402190b030610030204050105040e1302060a02061806060604051003060504060605040302 81
    0x2c4250400004140d032007129211000c40d41c5104051503401c051000c601a07105a0030300001c40441c1803441001c0c450306c540e0000160342d05180c10481c21080c0014202000c0160040a46940c8845103000c10000980307401c0104100c607186000030300314000c508086074400c20035000000c0610242d42441c007156103041115074117449000b030032000c3c5c0f449600032142a5100608204201c4c040e030344101c540c042e90860300c0400c8210100050b18800042c0888072035011005604c0c100c601d004e105c1c00b0a16012814082d151039000310018203024840c0c0002b40c070303881d00c8400003815901c800b144606810704a500404a440e03da80e40203c180d0010b68496004201040080c116a4000d10840d000d40c0c10507100d1a007804d1400409001a001c002c1c031200c5c1070000104001d0040c4c8540d000b4003d511a160045c2c1601c0c40d0510600d200d03500301c0c0f03000342400d40c440014402551075000403141075031419980e03080048243c0005602502d642d50210b50400d14201d400642030390322801420030b0b24400c9800f01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 34445023 1250 34443773 34443779
    0xb130e190b1504170c06040612060b0301050f0108090f150f0709031e140604050d170609010303030c021e0706031409030412140d050d0509010c020a0206030a0b0901080a0c 75
    0x1203150540c12680400d000422050060300c1c050b00c0b2403000704d25218110780c141c4180f60301091561308541d0110780071a03541200c40007500010701030b00000d848003560b03081c210740c50b0000160700294800a41030600410f00042a030994080c812501030b0a0540102c80307524450790211512064105d4051688101c40c1010910017032080000c03100f2680c01c6003d440c03640c54403521042e04181e98540840300c00001000d442c1c0914001d01603248654081c0e0f000e00450600600040d10100e400076080890000c018101b08044c0e890711802070649400d45000910b1020319182030349000d0b041e40350f1140e1017003011b10f240d402075000502d2005868081c0c0d028820013410f1400030f16611380a9540d9401504248424090700003200507004e13400d03001300d18030610b507901d5030925420100342c184072600207140040e0b410390a1a903801803640101660000304400050160001e4542404040c000d1055100001240c1c0c4016560400030780340800500d0700800c0e51752041c02655904a581c030440c5c550100c44000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 34446273 1250 34445023 34445029
    0x8071a0f010609121a0709091104090c0207080307111206090706030f0603030207050616080307020105070207060e01080711120c03030612010e07031203060b03090102070302060615040b130e190b 85
    0x150740140da101400c07000014507101000350b02040103004a081142c8a0f400154003223075805420f2041c0d4030304840c91ba40320b040c25840c900743e5200d80300d80d009540c0f20050400c01003500200301c40820f900140c01c2071030540d4501c0003415001724a66000b8441c4030b02000e01058180200303280040301e03060740b01000744043c0b40c106030007076070344604c006005038010a4040103a03040c000002c02c144442c00341c0300c00c0c5010341651118801d40050740c030305006039528010004800e030100151406007405040c0b803c03100c131200c40001c01c040002404101002480c1c0303075601420508018075505143c130803c9003503c400c40508120b980e5001280c025115090508c401400440107201303040750800f1200c0500070a509548520402001400040c5c1c101a560300000804820200195014400d4107001680d00c4116080007441d001014102500c0350f188004441a01081ea0303084a00305c1d801c20f900d8940302c85424049191001c41540840c0711803018000b00660320214080385988040c9001d03040089a40403014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 34447523 1250 34446273 34446299
    0x140d09111008010b09120a141501270e0709050a0b130c090501080c09030d050d0c0f080a0f090804030c080714100804210203030702011d030708071a0f010609 69
    0x1c4c0f00d14203608101005a41c20001107501042000c5811141c2410690b550541e0701b2801c1003001c44290001c00c0c00300680f185182620340144405d034020f440203040c101c6081507402908041c2d40900395104460340c0845002c2c400030000b020203002c10002f501c0c0c50b1080c0e402030301603461081e10801d03070307194401043c20b40d9204140300c904050707807100a05d5050100641e41c4c540007400c0c05014101c00d025840380351b0303000c20080c180f5a03140e94074140c80b4820020758406513000142d55100f8071420001e00d030701c01540800c4950303000000e04000f0a002e01d040161400614070480083e121250024002c0140300c103448081c0304890b01e101c100c507100da90300c1200c02104820015260360041a601400c21118400c21001c3c0d000350140a03918440603041e01c0380506100155400c02c0503810100070056625028420045500c82d110742d03034040c600c0d640d607205849208000008082c1040400d90b1014004108460701100c00da010b00881c0a080034600c48a40311801d20031036000805181000c2050302903291 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 34448773 1250 34447523 34447529
    0x4090b0613031e0506040c05040c05070314030c0408070b03070207080a0f0312020c011803110c0a05060711030322090204030b060d020102030f0708030f01050607050d140d0911100801 80
    0x1880d0503525003140d481045030010f0b0051080c0300681030001c0380c08035400307000250046109200c2808032514010a09c000d841a00e5520f0341401000d02c44080031903003240c849401107180b00810340c3d41c0d90f9560440516402103130440c1015104282d03001c10b04000000c011401800c140e001c90b10100d41d1400950356078001207070000c1c203c244910360000028001c0c200d01c0c0d07107500070350005810030001c10702650850361032000103004418110144002e254018050310080054071020b031078408924070102c0d41c040c07d98440d40e4003402001a59001380082c074503400b62000360040903a80c2c0c515203069801c541940e24081a481a060403c001510361458422074044980c03007404c000319996038100f00a0b03203103549001079040d40010407040d101000044000c04c1c8442c41000d04585a08022160812501c070580096018a80c10405000400e000185013510040300f03281c1140200750100b0102010700072034900f052a03d0070300b03060a0030000380c4d2800d070741c4010098a0071403035003103501c000301d800c200700384 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 34450023 1250 34448773 34448797
    0x60f01030c14010c02060a0e13020c030a110c03060403020a030314150d030306030204050a09060b03010203090c0607031e11010506010905011d0303070f2103020c07050904020f0a03050304090b06 85
    0x1c03900b0820b5011084811200c008141860b0807581d8494020410513401401c244001031120403440b881803805c0c460420039039540701400c600307020621103283d540f8410094500d003130107186c1c214480c24840800036003600715805070640d001418240382c040c2d40e90341180800c501281c00c040144080d02c400c40c00c400e1141c81c42140300507101c0340e5081405803291008506504140d228031021016885502420f4004e501c18080041c14070780d60b04002c001c540360501540e210340d004000780846040005400c010010003115056501c0c0c1c9140f0b01030703c0b1102c54225054007130703090301035160307600e5001800f50649008070b00c001d100d16a1660011031b005080d9029090220b5411000d032006024801d4401c890b0000140449140100b142c91704106100542c0003205c6c7c4030640703505c4802040352902403001010150400703500340f14a031020503803186094080c0501880180b0001015940c9000410300706100140c60141507603101d0800a4603648180649917105003020368804082c280b81085440840da82 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 34451273 1250 34450023 34450043
    0x309060103020105030606190e0f0f0303030103140307120507030f020a02130e030f03040606210f080304170a03090b06120307080a0e060a0509031603050a030e0102100f0905060f0103 80
    0x76600654507a0000b40035160041d20500602001c03141108824110540d251520800c042201c01004a50305544580900a1040d50425451a1000015241500e40c000c00b0b9100c5100d030703403d0a5185000c0c00e04041e1a003904088020b0705070380c00034001c02c4028040e54031140100e508982c166992000b07120025040b01151070000340300d000720b41c45804406a00d4041d6407130800c0700300e120100f61708240c03010344001e5520601001748650000c01c801460803d5001144103090301e41715a9188061990702810800d4008005010005403101c11641c140e4071a064039103400f40ba840c01001800640012203400b203042c0041090b5262801e49a560114450001d501e4884181c0d0f406003e9044008004184034001d43d0904059581c1d40c041c0812007220360703030f280d102c202e68000c051074003103c1c44085894a91118060002c20030200b645100c0300d4050901400000d145e0300100e28000c283d041c403031402442d0249240070b048180d0081005180108100c81140e00d41c840c0c80540d6030001c1c400107243c82c8403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 34452523 1250 34451273 34451279
    0x2030606031b0405030a0c0518010b04060e0114030114030f03030903090103020d06050306040b0912030709050103090302101506030608030901020c10021f0506040e011103131103030a02010608060c03090601 90
    0xc400110380061080d0840141095038a40c042481d04a07210411941248001e03000d000c1c90404408400e54041c9c101704802a41d45041401c951b1803003240235035420821000c8500c025640114180108000d902003101d59a43e982c011042c8245181c46420344030780910b0410f40541c0c0320000950b401040703100083c51404d400f400c01500254032041020400359240c1e0b030001503a54050081d180300f00c0c019001c822461500348000c0d0f09000c188104220744000500c2800401c0343e101815406507007081c2000078284c0d0b05420306a140c00c5010408c80120780c200ba00042c4519850b075000300031501c013174505001c0e1a0700c424440e2b40301e01030715164a00585c405039115440e850a020700303140c05102801a00c4207a46c02c2a0013841c1ea4904801800c1004c1d00d6500380700081c02c140c450b11900c004030300c000b0005d40281c044558814403002c0d22824049001340a4682407140c10110b07000030f40c00080c01c683d030741d80030844064088d1116101e6800030b8028480028201c840700d004403445040440701030312140c1e00f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 34453773 1250 34452523 34452541
    0xc020105010509070e0d021f110a080702060307030f050106030c02010b01050915030714030906011d04030f030518010e0c19080303010302060706020d0c1d060a12050c16060501180203060603 83
    0x80201e8a00c6c2d00ca81c0401c4034001684030b085000541c6403050441c3c2c00d200346101d03005491003409443c82d6010b503108440781004990b4950648102960440d201681d94446010403005400c1044006540c0c0e0315000000580c148c041d400366100400c0da4000340b00940590005441c00e00561070355541241007034100524800d413081c011a801402400c21440380c54003c2884051504112a1044103a22800c01400750125003e03203114401498040c098a92400380d400a2078800941c1d87d403404d15031603801080c4c1c0c460440c10602d41480001c03000700060260503c540c2c1e99800e030a4810b5000d0707020303056403002034114480080f065901c80001145140d10f13560030700130340c1d51104500f0b03540d1342e600303010418041b0b0790b80c0a00c5040080c41e0381e0b560b00c4d604c030746100454600c408002c424403030302007007000d580559044200085c03964000c40d80041c4e80d588050101d11381c0c2c403c07060340711810041407100d0030030450a0790010b41a01c90b0968201c07880c5484088880407403105440340f6a000e1402c0c40016643c3c1c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 34455023 1250 34453773 34453787
    0xa050d0c0201020708040b030a1d0a0b090c030a030206150607080a0c02030102040b0309010207020a06030e0c010e06040e010e1f21030c050601090902090f130201050a0207080d030509010c02010501050907 89
    0x10351000514005503074036083da081e04143c1000300d4010700001880480c1320280035119410707041a101c002100190b603112075407003400c0b801c024004156640010341e00d44042c491039500c0c005c081c2c1074411041551400945407601240e4841e07044002d000707500440c0c00c1c00f0007a1780596522642d039030300d4602044820b60341d944030a40100d92564081101160b080c14050156010340d40e04000036848644602c104001940150410b404151078988644525600024500d050400a00b4403966238400140418580e2180790001d180300303080c000000803503481105519200d039144110344007607240900048424071000e0300c41c055001d468490050302815240b40b02d6010248a410050f815a00c1a61481d007861001d034010b50005584400c54019400c19040340c0d0b40c0103481300d480c0343c401c0c60702a00424207039514083c080c0c10050041340c00480da5008020200181218000300d40d2503952448008010348800c44001549509013000c00c88000e00501409050700d80041420013156501c4004503990 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 34456273 1250 34455023 34455041
    0x30201020327040906060503010e010b0901090b04090b070c0b010b130e0a1e0c030b04090c061b061404030f05070c090b010306050a030506070905060406020c011209140a03090b0a050d 80
    0x754080d00c01c446a03556036440f0300700f4464862900801c0c1b01e4900401c06085038000b40c5c0f40c81159047c0001c480c4507960b03041807a41035860802002800d051f04001240003000e28803001400c0100017414400320355000355201c0d07000341c0b15401420481c1e0720b610001c2418040c01c1c0000740810f90360b584c1400a9240500e24941c040d40b0102c1c001180c1800340c10086108881031041090aa41c550360010507580c18003500c03d0305441902d0601c0324450f0b03035440082611581c03166100700f10090400d06030401d6440d0f02c440426802480c180001800c8071101581d805040e1230403400b107000100c4c44032502e80180d040e03802e000c1e008070800080b00d1400540070301802c280d03195141050307615213021a05a6032480e40c1d40146009070010200f0340740c0180c015000724000c1d08040d03c02d200500c010000c0c0c035400560044401401c0c42c00004652000e0440c00141100b008003c1c82070813203d29280301d0300800110300042c0c50099995981159503594200e000d441010400c2001400811079000d482c03980b40c1001c554 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 34457523 1250 34456273 34456327
    0xb070f030302031816080d020f070509071b080a09050d050a02040c11070608011401020102040e0a090f060204030312050f070e1c0512040303032a0e0d06020c030a02060906010302010203 81
    0x13440c2490540385061220702014201c0780c682d4518180000c41c0c08100021441c00c8500007441c0e8400100070302640da84880c4903c51084c141c1c0710004843c0c5106504202c0071428407000c0d40c0d85142203150850140c0c011000300d1000130154140090b03940781480310000e40380d81100203403141c43c0c1e4035020301c8082d10702c03204182c060158110700780c0320411040000c0001800d1681c0c40d1849075040c075598105104000701000e045a005200c10310a441108410541043c0c000f0400141c00c4040c0c94014402c00342c10f500909414400700300001819003200712030780c0d244180c0b0f03410004c9503102c02c0c0004040c80d0540c1e042d000249000510045800c142100304c12410840075050105a059500c5601c0e043c0d100010300ea004030701080c100701301f6030107000320046000705036044040040d1000300440056214061a810411101d00800890303c0b8800058075a9400980641d44c0c4d0000140e11540c80e4000501030300103104d100002045d0000109501d4143c82e8141c2c05146000314542010046201820418813 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 34458773 1250 34457523 34457551
    0xd030e040e1e0703020f06191b06060e010302090a060312030911130e0f030307021b040b040f0501050a080703050a080c0f060405070e0a0506030a290a060f0b070f03030203 75
    0x104080a080daa002d551110402860441c1c01c3d8410320010b074102c0c9079454001c4005100d02848800b1068009110700c2030781c50f040031650f101e140c10404c005980900580713401d240c17400105000d00f0038035895060340d00982d445003868a9121850f01129554440031b0400c03640c06105418940c883d030807001071640100111034040359010000381e80e200701080500720040c0d40b00300c0c2c5c6041001c140320036401d0903040005581189490304010751560040900d07403441a4240c541b107403181d0340b26070200c41440ba000c1c00070003049469070808002410300703014807841084510070000d611400010018183d0b54080c001c2d22031000d003552118400d0304124080c0141d4050001404c4c8103100411246105134090b2005051280c54130b00002c0380d000000e8200201581032034200303d410340b400944a030b10340c3d61000704104105401c014001c0c0c8841c076416001c07c0c200c0e9a0060183e544a00c1d0802e03c280c0380300c0400c0200060b500d41c4040c0c500e1003221001046003107851000d10100307020342d0140da4060350042d640c00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 34460023 1250 34458773 34458793
    0x21f0c090f0906030b1806070e060d020d0b010201051003080405061b0f0a0b0f0105090f040203070b0a030603020f010f020a0605040809041e0c02011e0f020c120703030b0d030e040e 79
    0x390010701c96003080703204607a035010030803e100601740c440350440d4140101d00080d030701d41c1c50019282c510040034802400b103072000c0c1d0b8035191078000445042c8864442c1c11510f40000c680c02e800902a44901c0900544c02d00f00030031210368645140c00101c0c1d0f401144a4a0b107850407051102c1074000800040c0d054a00840094403010706120402102c00c0b1000500001c00e03030751070161485800074004d006095010001403155031104003080b071300700c180c0a06490a50781c031807000038038004040e00604c4c2c1d0880c010074814180e54141d0480c2e81660710071598a007100369540d004450304d0103d070302d2402c0180d200e00124008503905901c5240c0290041c0d00c514685001c0f84082025101c032901c01032400309600900d5601e2001920400c501a1920f200030300c05000c1d21152408904580398201c20b1039642d0b4503080e030070748146a04451403c0d0801c01035404442100c21000d0b41c43d04800800e40210342000d64100c02840c2192406038480c3d41606c5603c0001020410b200082c040421b40121a00c40e40c1005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 34461273 1250 34460023 34460039
    0xf030d12060902070b040501060b040e0109020912010606021e0d0503010512070b04151d150d0b0405040b07140301050109061121210115050a090b030903031006021f0c09 74
    0x1069050702078a001c62181c1894070b815401c5986a07130044212000034803003417101d8441440cc00b811180360400c00750b21807a420307000840c0d11003882c0080400e98600030740010201d402040d65001c1c030401ca0410601ca62004a105440e014078002e41c000003441000144110304d4506a00300d200c1e058102150f460a480d401084e44660141d044400c4014860110f24013259002c219480515007445c1078501a030b550703d0100c0c0c202400d00600c403010b00c001040c0307640245200e500851024800030000d1100c2d0809040401403080c054407400e00182c5621580300700f401800301101d040358810380d20741c4090340c40d2860072115250301c06040f403254021036418920000160b041e10107030302514a042036640c2e00c0904036a241743d44803801a1141501c08004004505024020000340701c2941060303951200188012a03000c05107070015011a5004001d2160243c40000694800d401c078100904409480700426a0303a9140a140c003044c86911100b0455419800e801101c404d80705420f295114a4803603402d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 34462523 1250 34461273 34461277
    0x40b030106030f05070c050a0803060402070c0e01030204050f0f010b070303110c060105120703030207030206030c04120b1f03020f0d06020405041d010501140901151b0501020a09050f030d12060902 86
    0x400400240c0f100c25090240d0028414a03030800294103098511401a83c1d40326102d12003603a0150991001000040c41d43d01c8a8049424859200b86c600b4400341e00ea0081c05420722007800241e008502c0e000004584410708101c850041c40340d0003034018903a2811514401650001e00100c041540310a41800f01000344005040d80603000b001038a03156050005010350b5900900050030f150f40425020800300f500454004c00307032038060710b40c6a41c0360f0f100b0425a03d1b0b03114a61140c40070403408040a0113200280003544c0c0500000e16001c14a030055a101400d0104d144c000a54450f00003580303c1420324103810401716541c420304025041a80c0c400018003190451100726a0780c0e1560301c000da0044400784141d40c00741c568002071800214600380815200c0005018100c11209580030082c41c0c43d01644d480c2001c41060404903161000528005003c0d402084805000c2101c5601c04181440c102d40c5034914000c0180003003c03100d01000b4200c038480c82540400d0145591180041900302d0320b400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 34463773 1250 34462523 34462529
    0x2503120501121202070f0504110c060c071509020a05010c26120a0212011206060e01030303020403061a011b1103030301060305070906081005060a0201021c050106021e190503040b0301 80
    0x300142c200056040c0700c0d003c011034400300400c540010405100e0b0007030321130310381c0b0507a6002d50300010f800008c00e4074a002d0348550141680d00f1b1140000704024400079400500c40c4507c60140f003650141101009415142d0700d0707100039440a2200b20502040d4444c0503034464442c00b44030059561742e16190a014038101200c185c1c4e03020359000034079016002c1144640c60b0048203c102c11441c06082c290580a504810300030020001038250052050101a0304280060710013903a5502140d40d40e480c0250095000e40700c00ca41d000c1c20010800103d0003100c0b88141209010303101c0703280002c1e445480908689611070101c40d1626818200b682d87d46040016601078502d44c0c0f000626400c060b40040d2107808151320442c00c011611042181c40001c2c22182000c882d003c3c0da84a4a03011003040c243d0182c050441c03011003061003506840008406034200c00d04a40b0107409681051420301c00c074007000c0502c0e04031a0140d5000c3d06080c15050b44901c0313481403141c0144150303030070036403511145281c4d80e00a80c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 34465023 1250 34463773 34463789
    0xc091c020f04020919240813020613090e07050f010503060108010603050c0c06041203060f06020d0507110405090d0806060a0903020607020402040506030901020408010b01170f07050c070f0810022503120501 90
    0x26a48440002a0196041141c80c81c21f1148140c68107510010429501c81c80c02030007024080341143c1068400e1080e00081d00c0c85003024008280c14150305660355039180b281e18400c9910f00d00300c2481e54010000c4901070f440681d00c070f9800340e0920f8803e4002d41000303008d031200600d0421a0b413111800c240003490269100f580c8200164891030002000c1da02c242c1c01101c507068500c03800300f2526800280f040d000b0070b03160074040d0f114009410090301e0b0320300301180690800d00700350401004840c0841c0030741072050a40c50310101512400e040c40102e026081c00c038030109010001c14000342c0740507800b40000a10081000d03184c02c0c0c44801040d160b80043c1c5030222107a401140c1071002d0002030240100d406000e1800315240c035484080807140e854041c1c11408554003040c040b0344c2961045040b22880100c800844100540d641900d502c1d2042c80d1041b00403034010203460f091301e0301860084035211002904400311140704130500103c5c10180341401c0b07040c00071101c1440d0440d80c40d401940d000781001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 34466273 1250 34465023 34465049
    0xb04030609020405011a040e04050c0405010b130e01060903031101020c16090b0303030f16020a0203071e0b03010609030b09030d05010f03060b040c0503011202030a08030c091c020f04020919 83
    0x10b0710502040c1c0c0c0301138020090002d040300c075010030b240100040e0740c2224608810004d20f40ca41f0308009041404a1601130340090505002103424040e4600401510960b460204003190760b0380850030561400b0b0280a0000b41c45860401c0402e200e010310745454034034200014641030807042814078004808480b034a0400200c4001c00c02900c8d103100c0c2104091090300618a145016400b5600d1404003c0060203513101d0402001d00c1e0f184200402c41400303902808840c10729403900c44400388500c04c4010a080f02032a1000410b41011202c01d0328101e40d00c40e100c241000b0f046a4982c441120000d0011040d84014410305003031201601450340200400d14035020240d017103040010980c0d084038040d0340618108a02481c0710350b030007002c50f411a88071702c0c8035545440131440024200100e070103015055410103c180a00401c4400050045840032188080382c00c031040d03140400e05a0840c1c0c0a0f41c0120000c040c0e51103414107800608a40710004d0601254100c0800d441036000800d800500155201d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 34467523 1250 34466273 34466291
    0xc020102070e01030b061c06090503180d0203100905030f0a18050102030702010917010e16050909060408070b07030204030f03030e0601440f010b01020c01031b080903040b040306 78
    0x6004203000782c101441a031245606585030480d01120141800f400f03400060020409181a00c205c216141d074001000e000824190030510b990b070700642c0c01c0304010340400242c0d480500c1e00c5000620a01d9001d8050b10001e94442e003030706d005100c0c20005903090f00007041002140c201410040031010010b4440000d00c41804c01c0d040301c007225a8000d5410355000b01b1844001d42c4e00500868105d0b4620071070751660104000040f4090200d07107980d50f03002e104409056890309903003003070001540c0003501c03921303407070b5807140003c9550306026100540440410840140031610b14809594031012908016203855a02e82e28001e0640d07902c0c0c02540000e42d2142c2c9200210400d012640c01407204882081b0090001202010b107a854072110820b89000c1100142c6440300069200203494421804e8941c18201d49080d10701030310a6080d01401802203221461482d8001c2c07151043c0b500c0d40c0506484025824603042c0d9024001520a40e61844148000510501040020805503104007c00f00e081c0e00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 34468773 1250 34467523 34467527
    0x20106090204080604020f04020d02070303021909031208040201020c0d03050315090606040506220803030a060902070308010618030819021020030403030b04050a05060310142e060c0201 81
    0x25a0300850403090040008200600d00020010f400c01c1c2c04440060117003800e1400140207120714411241c2590000c07071030605050f01540039060140c3c01080301001c3e0300f44100d04944060b07003030000070302e00c60001a490b0862482454441e1b44030b0301c18011240c03154818070020381205c21080003200020000000c00c0000f071082c1028040314078050781c410302207081c400005201801a0b0150718043c400c0840c000045032111107043c9907080b021303c5118511030f1100600c42c0ca80e40111104074505041510007d100380340747c07085807041609952801c3c803c0e401d008003110710810130a0080d2168005d4070021011580810060a80721000c040b08804101c00041c0a800d04056044902c002482c050302d40070f1101c08201c150356091404440e1907600da407146002da0040034040b00300b64010349407000300030140505a100e180611012003c480c40d0b070f88098a020241d4800e03030645e8055004001c0402c01c958900414260b5a0005c0c246c0a07427010485e004980c82240315a101d40c00040c207821034641956 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 34470023 1250 34468773 34468781
    0xb18010b04051b0a050d0606090501110610151e080108010605010503040f080306060c030d0c030b1f050d11070c06080f010602060105061c090b0402090c0901090b070c150801060201 79
    0x3800503038040c012441e100c079140c0a445150306940c0011000001c004110501c50000c4541c200d42c01d1108002440e1258002401120680500750101d0080d1008119450740054183c1c841e188841030b040e03441d0304201444260400d848920414880c0c2d96500e443c91001020224511044594400c8030a43c900600075096421581c440c0f03050203c204180b0022a400c4130501a805402209542e500d0f00c80001045080c8110048980309000100700c0148886542c5c10001c07540c1c10541d070a1280d0042c80082115101e4540600140d44035603241002d506802107000c1c1005006201d0005039840d039080f400503190307000342e0f0200c41030848100d041c07140c2c40d00a00400d800203581c05000c50760398107004019680d100b040c02290700c00c0c01c1c0402c1692000540c0842c203051160882414020000780c0d00c4d207a0301404060710200d202d0f45614001541c601004415070340808416968203800c0d07840c1204039003890303000a0b01a200c880c4940000b1403101d90586030100105440d81d1045030315071510400030300315 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 34471273 1250 34470023 34470041
    0x90c06030204060203090409051c09090c08090c0d05030d0e01090c0902030702030a0c0807210801090b030318060403020301020c070905130215092e030605040c0804030c0606030b1801 80
    0x414410b11007405081c1e800820343e10802c406640c00501c00409044c40f619144285292101003c2c0c0c0f040081c00e91030f400309462048420400041c0000c160010b81a80e002104079100305160380205032100d840d1405900408425018005403850032500d456980140e030500e6415070f0302a074444a0f0301c0c1c1003003540d0210304001c0096440c118150b0604002c029180e205d15002c4104000030200343d034003440348500032136881660011424040c02c2d121020090005e00c410000d10104400030000282030040c2d014460746603030020061031518814901a095065022600741d4003c14180310100042c0c03000d2000340300800401004215403840c000032032080d0f40d001400b04400004600c401c00060700c2d014850444c550b2603580880c0c80f503d10002054181000c4000d051b42500b081e40320040d400b06070842a41500c0301603800340500354940d800c1c803043c0d485440c034641c00110b140c030009021074403680840040d00c0c800c0101280f4603070f8035141c5400040b000d807003180019088640f501d02d0000300b4801c4100c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 34472523 1250 34471273 34471277
    0x3060901050601090b0c0312040f050f0f100e03160303020909011d01090209061c0608070b03040c060503040510060e1014150a030605030601031104050106091404020a0903020301020d090c06 83
    0xca02e04200000d004000b00e108925484d10b003c83d00c6800f01100b4020382c0c803200301080a5a000349080c1c00d040a010341c0640050327649000f201c0c40c40000c40e901107000200011810020b0030000503050f50362005001802e4401c0e8940400c0c803100c86203868040340107802601030394000d40c40b41c00d041c041266070030041c2e00141600e50700030075182c1a8840b480b240383c11540c18060050b143c00180c008a800c40c800d4203408030b00101602200e82c1a80304907844442610003540844d510ba6031100541c400602c415103026001c5260071004100e680d21410055601c5445038007981c00110320328031444150b0b56650006408114010108001028210502401002d000c4100c940300307143d00b00440c44ca417801d542c80040441001502c50b030f915001ea0094401000c0140869100b5a582d05000d14131400c080303c01031140c2d003840000202d0320b1040804606603016884440010b03404001040000d6000000d03080510011f114000050b81d000e101600e440c40c03102d40301140a02a924100000100070303001001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 34473773 1250 34472523 34472531
    0x303030506060c070605070804050d0c060f0c0f06050402120d050a0f031803030b0f03030c01020309061510080a110301080c0f03031c0f021303050d2a020108041103060c0903060901 79
    0x9075808000404c60300302c0300346043c03180d5101c0f660700b8040b049100c0ca0b003100750070000014459042103501c400010031620113940314802c1c2d4109140855040070541c40c00340c80407021504103404a85540d0005411a10081685601c041b443c403441e403c2c042c0c0d003203510002c100b000c5404003070350741c00000700c8104400500e0100305004040c84000c843c1c200c5500b01a04243e904c072000803c43e1100c602182955100608580d11241c2402081e40030b54401c0b1020801d9000c0e003004640c1d6413600d24070846003100010b145000803040014104d90947d8001c2c045000c06440c0c0d1040b040f5003603100020b41c06040040040c140d1100800140000c0012181c2450700a50040001c1d81e0b4607608102c401c50140c4030302340c0205d4440403000c66080a8003a4913103c9072200107c2c034000041080000c3c0c0415014182e407036450733441e628040700841032050740d400c84242107900403440006622070b03040d09074010b00c5543e01c08004d00044000c80e1501c841111584049000003c0361440c03490108009980207403e08001d02c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 34475023 1250 34473773 34473787
    0xb2a070303270605071101290402091f0c021f0f0801080c060702040608060903030402120109050c01121409070911040807060e060c060408030f07081506030603190c030303050606 78
    0x500040742e0700805860213940780c0109200c9882039014101d401010300092103d86466140380d000c1c7c00340401700104902030720108405a080034000d807299503070014020300803400c010480c2c5944140e030003244810009a0490400140d540b00080c12140b0040350351700070350191820014040c407a810b812001800000001000300c4580000e2b914441d62003510440d80301c8a40e440401e010340001e0700030010700c0c015035007004200070707002000c2d40c0308038000c8401d00007058115078451308132082c20b0400307003258000e041100899402500b0f481c002c103481c0b110000c3c0c01c0006071540171411400740c5d589107158110140801104080d4007550034101104200e441c80c040c58003028560b5002644142001d20000b1400c82c041940e0b808291040c02c2c14070000d44000c0e14292410001c030383d00c226500592801c0203c08942120310950105d03204024103216000c03030b81082000c1154030303080180300d59810b1007600304041100e881541c082101d54070580c0509044e07429454043d064170b1008254500460051001c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 34476273 1250 34475023 34475081
    0xb04140610050f010203040e0a0c03180c0308160f0b010306050a0204050a030b09070b03010801020406020706031e05090c0406030302011505010f0c080d02040504020a020d09090c0c0b2a070303 84
    0x101c11254111a0a800c0488220050f070460003240d0004a000a0407401c01900c5411034101c001840056a020001d00c41d40301074000d0350390702d0110050580300a03260f06000080c02c1c8070003803007007406100514090014964605541060907401201c1440d946c000410410070240510798000d01c95441c29410141000302040c0c40340914071016040c601c0d00e501140c07003c1018800701c009000704030755040c0c0c1c940e100c0b42c50300d0203540240b0808006108021001603d58803c0c4913030000c00b0f090f0240b4501080c0c0c0c003031a030009840c020301044600e020b60030314140e15903201e100b040001c46c401d40000c04c00350091f40c3c40840403621540114148000c40a92001c2981e2212410a07481e6011488584590821070140300031302503500101c4e0094400074402c1969600018080d040e10400d5032044400c07502d82003503506851501074940c010131501c40181d80068042d11046910940c8250062040c000005003a0901000031034400c44c80080012000281a03044c003d00512808490703400b40d000c03c0c603140b2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 34477523 1250 34476273 34476301
    0x702010309020613060f02070f061d0f090702150105060307020613031101060f05041a030705130209030d08100b0301030302120a0314040b010f0f030c141302070b041406 74
    0xa0405035a03400c024215a506010f8401c0000c4000c0050080d0b42c980300302030002c2c10305100340c10261003202d500082180c401d0240400343c0d0181d5551015000c20308580d43d161101904016a11201c2e10342c040e0b02540382c908803107210350b940d54020a5000b004010700340050a040c0c2040c0e0048078200308200c0c44540000e40345820400c2c03070341c00d600d440e5039905040303031150110583d0303000a5083c490b000445a0414980c14140c8a08460800c103203c080c88030303007144500c035036001a0182c0005100b00418907000c1100004004140d601602d44008500064107146141c50101c02041001c02840350409040005a02814050482c0c40c515415514080d550b03121000d04284610700018214141501c280c004528608408108420a04040c5080d600401090094410140700c2c641c0c00210411a0f9060f001100d41000d0783c06000c6003881054a4100ea1050046400088803c103c001ca920644018030040e80510000e1809080c240351081b008850303c011102ca0760b002c0d074107000070b00c15000e003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 34478773 1250 34477523 34477537
    0x30605040f090b1f080d0806010e0306060a030b0c0403080c070f1502030d020d060b03040506090c03010c050f0d0e030403050102040510030204260c100903060b0d0b01090507030f0207031806090b 85
    0x8195081d01052116440b0781c102513400c041000c6c01004074140e101904001c0050041200740c0310b0704028403111062503558072085584503800b4500000c1000810f40041d0000c2d080741000c0c034040e1900342c480c0c5401c00c40e540040100710035035200711000c0094460046404c40a8038a020101c056070805090080d528041c05100307403a205d40c0003800510020807640904020400b10150035140d10f406d0a210303846d44070440d001a82c0d80294a52081c852034103109511609005455060400c01e0172618207400e80c02c103e25030000c980e61751840c00040c0c2e034200003900040d40308400142c0c1d240e0038607052000c81c502801c162010705d40144818000c41c04e0000008040d40d00c445581d0040406040100d454402101c050a8000e44602d070814405640808084203880c020344007401200e0760030050041041c801c002c090485082c40b80184400b0403550045600300d145450003044001d84040004200d0740617200442c081401c544400ca204840e5030914801043d09003480d402c0c00d85402d502e40041e105080c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 34480023 1250 34478773 34478791
    0x9100b030705070c030b1801020c0a0305090a050301050c07030f020312181c2a23010e1009261806040308040909150504020303070b060f03060403030605040f090b 71
    0x1200003100c15120318150f40f07105810107034280e80566a03050500076400141c2c4c413050078002d43c019902c00440140200c602e0380d8400d10081041081c01e482c01c0f07429030400722840f45d10150400c40050107a40c24054140035400d0f03000c1c0340b03607264090329020303062981800c140400c0d500240140306195094101c102e910003600b000b00300d42c1c6290684818101040d000030044081403048620401715030000c41084100004003900c4c0200c070040886004003601058024100c28031560410316105138482c02e003c00e41803686c004503400c881600182d0400c1c070001070541d96103a13616147c106020070541e00801841030b100703500361124294031100400d03202e15440c4c00303603940e006101d41c01e0a4135000110380085420032503298032681c07504800310181c681c480d001d88010145400c202284520340c4200750003958020011464210a56901c00c8880c400810007a17100345003458007000c46c1c03400d0022030301c900c0c880d40c2c1c005411420841080111045140030900c102e02c1c008080d40080c8000d030708203820010b82 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 34481273 1250 34480023 34480027
    0x601050a0e04030c150204060f050301121112030a020a060f0b0108011502030f0c150603030a0e09060d020d140106060e0112020c03040512010207061a0d03030b0301020d14090c09100b 80
    0x207040c140c0303130b045032404024052400a01500b0b980c074106d9004d032081d108550b5623480018801d00085445c2d000030b000b0100c20038001811000020144a020304696601600c0c040455003000507403800c50b000341c072410015802c0703440018100001c52007100389811401c0000c010723480d00344000a00001c0705004d0189081c0b2441c1000600d203000f0000d071110680c00c004c40716960741e101c0d020282c4a0304900c6401202407450b502103070740c07860080203a0324181c0596403400c0c2c100311802c04210341014007910300303078104100c42c5416015898615104010780d000701c080d1441c9075a21420305003154090341c0410104550340c4481e040680c1c0c040c4800f008100c0d07110025031036680450f54203003584a00d42c40243e001c0f03608600e46c40b0325101034000d40051801864100080c02d400c00655104105004040b0380c090203110b200000070340283d03c61244840d0140c001402d00449a000c0f40845103800008044200e03010104a8a05020005000002000c3c2c80b4030200d41040b0005540009141c01400040180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 34482523 1250 34481273 34481281
    0x30405030702040506011e02070f06020106050108070e0a031505090607030c0c020f0f0a0f090b01020303040c0504022a0703150b0904020913060f14070c0c1404020c010f0203090d020601050a0e 84
    0xc50111f54140c0012800c0c003442c0200c07007040103540c4501c503105240c111400c10302e000840c0350061085404549042c0c50f603041070390310300a0840307410b01a43d910316401100c501021010031010b2142c0c102c02040500700242c54100044482e2402c0f078000e1000b0304145c1001c5191040ca9401141c1d100240e40c140e41c10381d10030400301e000459201c10629456004101c9a1000400300c0d0458081c00071a81d840104000003c643c800482e142d1004407030181400700c0c02c1c0b00400081c02c09900a0244994140183d10105c0d25861200000c07481c4100e00401a40040382c01c0c03080c48442c1c50488003a080203002080b1292908021070380744080100702030b101d0020400040c1030388000500540240c2d5208108101e85421856038400802c1080e20102d4130020039070010f203203076000d104040140e0350044032840310185030182010440524140b241e821540038800d60516800034011002c000e0466080580c580c40c052004a00d4042040a0303001154054401000b40e911500818015540c050104440541d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 34483773 1250 34482523 34482527
    0x150919050f0a08030402090a1a09091618060504050f010504020307020f0607020a030f020d0210050c0d090503070b1f03020112090f030206010302010e1002060a0911060309010218040203040503070204050601 90
    0x4503900c5003910a000c2e0002080411040700000d500c980e00c2240c4e00085525160032010845100c1c1280c0c0c0140450490347c04610300d0008902c5902069107011101d854103071241103d62840c442d4400346502200044034000880e0074007503840030f04002e5030100418034161070031852036001885101c1c040e40d4000b001c100b98510901911071107400c1d2038201c03007a40c1071102000b59a40404281900000c05070805c42480e548085132a4011384103540c020300c0440703400c0e0b0f0480010000601580d142c003c04009484207556240940104c80c1e00941c05503456540c0d900b842803060b0f0005000721036044444883c885030b10302604410301a640c080c0390040c40c0c80c826000c030800034000c0c10400b811646140c4019000c0581c00510641642e00c00c2c1d0300d4001d03210581050011140d080f648500140e0400c0001600c0140c0340c0d03200382c20f124043c4192807111520000420382562040d075201d01e09075000145440d4400c44840c1e03550004109403011441c6191a4440c15141d009014002303114507100d8012904a80c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 34485023 1250 34483773 34483783
    0x20609030a120809060604020306010e100905210c03010203040c0905040303110f090a09110d0b031c02070e060609060403080d060803040609030b0604020304030f081f0905060315091905 81
    0x341c2c0501d0007950a800a800503040c020b0032120004544620400500c1ca401c240c000d507030184c0c00c1a16040c03124418402080303811100540414204081d071200065103036101c0340c1c2d82110001c40034110500d1484449002e085c120303819200c5010780e00402c28000001c0e28281c0c1c4001302c03005000005415101d071715045000c3d01c0041701c00d050410f0003094810484048030001d1042d150200c510080031a43c4209d140242c980070390f00404992000e010940e00c0052a03041b0032190100241501c0305003400e40701d0b10036030002e0010342000692100000703200e0001e054075425040381d07049611608012002001403501e2003140402002031f40301052208100140d85c1055000d0402d85058989454458400070100c6403588000c2d140424000082049030520b40708480c01590595140c00c409000c4440945005001420040300c500c0031110740d00328900b0304840c04002d0200341c0030101d218240201010f20b010365102d02c55000041510078001241030000700c0640040b982128104414921b05107030b8240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 34486273 1250 34485023 34485043
    0x14030d0503090c090403030b03060a0507080c09060408010e060f010605070507170a050106080105090d0810030204360c1e0501120f020c0d03060e13080d2703030518060402060903 78
    0x4c40c80500340710030190180c00c00120440c0c20f40490350b142d80c52401c82030581e181a030302c02c0c0101e121003021810350b095240040204600241030280340940c0e582200e42151824102a02075420880c01c2c4120803180b010050b0043c040703403410504080302529410b803940124811214812408501501c031900148581c007146034001008010443c0c2d40c4c4c090a01030001181c02d6240e81c090800600da146006d4142240100901c00000007003070306543c00d110081202070b07200440b18491303c2032820074031341c912007401407082500c2ca1541080b0441c5003400450241d0f400005081c0c14514802044005012598045035400d2030070390501c020414022000340600801c884c2c234071740000342c02c2c1ca103900005291881c000301d86d40d081090035500c50050000e1f80042d2200d49030111202c0055021806080290041d01030741040001d1019655041300c0f0410f1500d2095041d0310350341c94541092503054820b031503000140001007000c150600710082d81316030000300001e10a61003c81c280005840400072102c103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 34487523 1250 34486273 34486279
    0x9010503070e10021b030a030e1216030602090306152404080f0304051215070804031b060f0e010501050d03080c120c071115030a0b0301091203020702010914030d0503090c 75
    0x1034038070303c0c0000a441d204098900c0c2c2034062141020100ea00b000128201d04907090380d6000c41c41c0070903404126440c3e00e0510118054401d25036842001284a42408000c44c80b4510040e5508030800c1850b0502c540100b07a107100c201c0f41c440c00999034941d030b2254240890001d40c0b0f0000d01e082103580b44418010b0b40c211810300d2144618110402e10000b0040040d504201c882401030840302440306e640364260b80300e00200c1e1a003007000c203000d14020004150010b2107030134030345d5280d4008100c0f00d41c511142070307050f6999500c03000c00c581182d00b90322480054034440d2009111642c14003001c51080303290f803407004003080410340002d83c0f08040541036407030341c1803807600c00841e60a180624102d181c000702d0041d102d1020700b140b0b04040d0702c0c2a082d5070080c015000c08407803d554482c031a0200408406040342c0d019500d0344200e03000102c1c032640e1040401415240180c5a034482d0000616141490304801c0b980703c0100c2c03980c2c10300d55000440c5120300300c0780e2510a035a985c03011842030a01c00d090180ca50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 34488773 1250 34487523 34487539
    0x10b03160903170d050c03010f03140705061303120806061e0906070501150b041a0a0302090a0b180402120408160b0405070603050c03060108010303050a030e10050406060602070303020309010503070e 87
    0x4289180b0b81d000302003402c0d10240c240b041703032614401c051b5544420b11a910220710000310801c009144402e0300c041d0b0009400650307080c540c0d20000704845a00c801c03c1311007415000c0c0d205108008103003032017407502c030200e1410140030300c1e02001142c120b2140c100310710001100305110030058000c29044035400600a8055511a2200d1800d180a01540c50002c01b0081c201c07000401c401c03015109417003c07200c20804030242c0303510403091120540e21184444080680810203c100d5031240c0c3e001c0d000070003420100301c0d59001d802000c1900c1048140906100f140100460035010950a07a0b8582058007c07011955510f0440c3c1c080c0b115511440c40205000031103400c000600101040481c100c801ca40c4080c415540c03120543c55042c40300300d54444c08154144014408244564080c042c00d0741c0741d040c0000c4d244c00f2503000600d03101c0c0c43d0141310010b61b1a542080108460b41c0280030003020b4030700040c00d00742e0a59a0117500c07401041c0321241049004000903160030322442d1103201d14240640740724 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 34490023 1250 34488773 34488803
    0x903030e0d060f1a0108091506060d020307020c041b020307060b0a08060a020c060f0105180621030c1203010501021005041e0605090d0809030406050f0d050709060206060405010b03160903 82
    0x3c0a42144904c1e8400c4031404481d501070b80d401341c4449841182d03a03d01400b9801000100c0000c4203d024100d690000710500c85113415031081c4c4011801107443c2d8009011400f00e01e4208425a590310424500018071080151034964001050302c0300141d01441c00b2030b40c40700740004284a80c90b6a03002028521501d02400100303080d0382d00401281143c0f10648006540708000d094012070280b00711a046629010138110000140c1c81c19604844014210b1100c1030410200440350789940000310b220340c00001b01d00c44440c0d000c001007030f4040b858880650440d031500b40083e450340418610501c0c19521a0002000c016035503410a150502040d8003806600c0d541c01e010005110807504005180319001c103800c0010701a1702d80fa885843c000000303500d040e0400d102140c0e260001d50500c000790800744200104200c2a0140f18071030503059591030141d0f460800000d24000001d8005c070f00842c503240c0140700c4050070a040b00c0e0310907880f4144400401c030513401146e010b15168005086c60110404030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 34491273 1250 34490023 34490051
    0x607020402160b0106050316050306130204060306050a081b10030e0d05030105180c0901050f1b0607180b090d020303090a0e27191b030c090606020d0903030e0d06 71
    0xc2e1031424000c0c000c00025a0b05c0b91015134192105898801801d141c1083c8002814881c800442d405a009440000603d808402060590b0450340101011135240c080520172404c004a5542c0100340c0351004168000d001441140705034501070080f802030a01e590180310050080d0400c114000d01141140c01d003000c0311000a046800030b00440703114403804170310380c0101c201568045000710316002c1500d1825248d5001560140e22040b80042e24517020311842424a4203201e0001c0180080c001071b20852501410003081001d03582d440302000f0411981c14000d030030b441000d551042d282680c1942d0201210300000303286001d94400c03150b0101420502084403030008003554010006c090b01241071401b01c000310002640007280c40c800903408500d40b0000e03181c00071141c0c1010750160307145545000405020701009981500141c90240300c400301003048031400e00c699401040713144090b0000310410500208680c06070f2101030700b000304e041c8584038913964200c424443d1070f500003010400f040202c085 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 34492523 1250 34491273 34491307
    0x309031a01051c0b0a0213050307030c05010e0306071d1f02010f1803050306040b040209030d03090201020706080103020906100e061b0c10121512030201090b06030c010f08060607020402 81
    0x8850080c01e080810148001082c401c01010903405204075139269503101100740250018107416040458101001600303481c1804010f006e58010180c1090980c20080007414100008541d240264043c42c200100309078400301b480c90307103124025604074080182002841c40c9040110f0714201e6007c10314103030b142c0c0d41c05510251050445402c00d114859910314201035140790350b84083d000c100c040000903403d103015030250821030402000141010050000f292030b0400821407400400e9607202010155a0100710034001402d1507c1c1580041d8155404240401005003046004100d14a810074149001d008a4240500d0141089455000c042c90b0391740084034403446089a0b000d50440040781341810030780458030032041d8880c122110101000a07005052b41c0c8284420315204080104a400d1500006c00c202e9010303074000b141e1002c4138100440c0311400a05031910a074419000300c1d0850760000891241c02805050040041e5210300201e81248034110000b94860320004400d41840a0303915 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 34493773 1250 34492523 34492529
    0x7092309010506010e011404060305060307080d0c0b0f01060f03050702070905070926060c0d0609050a050f0f0108061501020a0b01060507030206070e0d0b0a0207021e040c1701060c0309031a01 84
    0x41c1d020170b010140001941e078802d03005801c0c220044208400d104445c000d0704201c2d08800040d089816041d528100141865804440240061520030001c41881801d19a403900041c03406502d41d150751610f003020302a0105056444245901d800001d4001d41c000c2c40305100070220036409000520b0514001400b00c2442d0143c0b491080c54440303a0b0400c074808020b40740009400a009129588500c1881b400ca80c00c15403280d07040c81d03142c0360085028031450080300d006204410300841c1a041200a165111400621aa0314201d54400400124000145154022680c004040d410b03010100c0105d041540b07428000e440d40c2100c80000459542c06001003045600030f6003559142e8035052000c6076162041003e503940b02d9184030150380403408401d225174000361210401442c00d8043c1d0302080840da100e0501e6a8031a91024101a41e401c0a008200704c542c001c0c07508151403120b0044402950006028803000c011201c02040101405140f400d0003940d000340f0484060f130800451020380c403030240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 34495023 1250 34493773 34493777
    0x30b060f130c030e0105060a030b0c1306090f08030304020d02010302030907081f0b0d0b010504020315090a0e01060f05090c070602090d060902010311120f0c041205100c080402030709230901050601 86
    0x181355401d031203042c80b5880c0074140083c10a01000d10350b484014a04901070000700360110108101c01d5940200c40300f1000034155a1200100d00e0310741511400400190792280036a0380080081000507640c2542c8000403503030900340180c99031903010071603191450ba034120a84c0ca20850b10307443c40760051141c3e0b05414022140040c08511a1542401021003402c1d100400700280400140840d00e4190061f40d03000f8211a800450424400009581048165185445a50303211902d01c0300302c40a0043d880541301f00a43c600180b440c010110340c00c070000a020417002800800c1c4081013000d2070f012140d40400003015060502c80c00d00308140107280501049011a01d00342140c08002d8151061f0755511101c548044038540d03411620580e6100c00a0040340c10a204200c045207050303200a20600b0b13140203d0092400340c1480c810318040381d44511255042c04004020000169000a9401c2c29112031003804100c1c0c401c0490841c192852018201e100070f2918020404110015400039215000903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 34496273 1250 34495023 34495031
    0x101a030109030c020a0f0501020319120903050d05010e060d03030207020f09040813150c020f0411030108010c090f14011202120a0b01030c0e060d0c02031303030504050a0609050604030b060f130c03 86
    0x503c6c5d2100102159100301c81c00340c1c10900c02c095110a0344030b58407103500707800d0030301031025100342a00341d0892344048012000700e080410602068003561160310b0240485659071009800e184001544030141003030003d0415400040000464a0703240701d10081c8040640030b01d0341420180340050454001d001001021440d03000c1c0040d07c0707801c20603007220407a042e440701030500d007040e000e22100303042002040d500180c8440c5015244c011140c0250300801c60580005641d0b504800c000b0082d450399485082142c901e603070140690440503201e2038401e2000d091000c100c031408640c603000383c011142014401228002005114003550304000002c070b100740e80c10032002822240689810072009505500301d10288407003a80d02c0300551111503c808580100e03824403000104502d040a0160011000568081810043d80c01c005a0002c0900140c0c04c02190a60400c00400c2c032034001d520018100b2380554004c0307006521407004210100b0700c09409500c02c0c5001c1c480f0a0081e08401c0c4103000002d2078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 34497523 1250 34496273 34496279
    0x50108120301030c060302090303071208060102010e070e0a0c1202130311102703081b0d0c08071e0203031308190c030b06010201150909120305040302101a030109030c020a 75
    0xe01022039050320f500803040c51600b802c20750228001c0d0806411a605444200702000100760910520707403080320366540e46611407401c0ca000900352000d0f81503429040d4003a5400b44061a800d0403500e5000c090800d000482811450040369603108022030b03603050b00d02c0000d040d242070103c49044410340e80a058a40c40395202c0d141031215410202c18400005804030b140030f802c2c01d002315401005006030303000910515440f51581c410030b52050f8176101480468001c504a407220030301249200090f142400d45440c00e040d140c80c80240300381400202002c820060448050460340391aa90b0f558019080343d1b16864880030b40480d00d09180600c00782842150b8405460002082040c5980c1e0740c0301e40e4111001d851640c4800701c518000e0700c400d0655407038890780d624080c00c1641402c000d004900e800300c0c4840140c00c20b003031640f0741904030700f04040c00c1104120110b0340000d56900e2080320110005142c40342da1f42d503c2038a14099a6882c0d042d4201a00e00c014103600ca0703400500340740212140108160303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 34498773 1250 34497523 34497553
    0xb01080d0305161209030e1003090b090f03071401151e09060803180a050603040c090c0f081311030102030709090509070510180b07030c0b0a05010602072105060901050108 75
    0x103100c01240011800c0e150042c040050783c2009070b4240c8642441c0004c7e4400038001400303980c4412001c03000a030703a01009414000514501c03900550071001030100c60b440078070800e4491213522400380241840f0458450802000d40c00324118403901c82c1045030103511200042c0c1e0300011084011946203c1980c0400e0a02085c42040c0460301710b04029450a89034200f000d80c1700300321700140c540c03000070060300240544441c0011803103507104a040301001c900389081f010465441c03803d050100b01c1110203100e980c941101031690001000c4024240c250300c0c038134042d04660710082c0c149415500100501c6075454005844405895107214140200c0c2d4440c1c5846075a10b41c6485020791000081d070400d80c0f081e0080f50070078210f82c3c2c0d11800c01700c0d4580741d0892100f03961110400b24001106514003c0911019913a103541090100006020551600300001e40d984c0c0e00d8010495494100780031032491060008000e0b2015a210090b500d9515203003000318001c0009202c0c00c0d020740256206400e07400c3c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 34500023 1250 34498773 34498801
    0x3010b0702040c0206090303160e040f150b0f03010918050114010609060507020310110d060b030403030b010819020c010905070e150a0e070c0206070203030309011e090203070e070302070b01080d0305 87
    0x106c80c80000310300319035621b0583c1c1c000c0c5120062142c2404484843d014040c0c886000c1c1d9a40b150040d40c0102d41204900d0014000121170742c40a800c5031802e1101c80d400c1d50301001101d0441d0103a06e40403400c003800014a03c03102000b000c00401079032070110150090440c204041d81201c80c60b40380c0e41d0b01a03a803a6025180340c49a0f10000350b040d00a20041c0002480d154004071143c0210074034641000303400022081203900c0b58000d00040d0b40080108010543c0c50300900040315002e1a01a0712410300e10452244050b00c100f41c02409500841d02c15100d5100754818411560070030110b6014913665aa510b03c0070009a407040f40107071040a02106a003031244020040300d0f80d440524045a9580c04100c4480600c1001280d00079010881800541d90402c01380d801010207500001d1440441d94003420860400b2030050170107410520782c440540c0d808a4514102c0d80415902103030303980c410408400a02c01c501004060f640c001002040000d0000781f9000050303a03a4074100019201c5a02285240d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 34501273 1250 34500023 34500031
    0x3060f060b030a05040c15030204180207050d080405010f11120610021507053106030606090506090411270109030c060c0c17031309060e0408070c080303010b0702040c0206 75
    0x4074401c1010840c0f10f15194400c0e82d000d409207a03614059901d683c140e2880310303281401d01e40042e80100c2d0600040c000c014840e01c003850420740462810482c0d603101d90b01e03298190058414045014000303000c3c00800e40140600e907811403000c1014000c0740c0765442858004c0c84000d49004a6000041c94070304210b50440e00070305568005050011504801404c10900101031100308201801f43ca00c0c4100860b20442a240d010540c0c0d404415000e070b03a81c1039600807540100101400c28400300100d03904603007600b0944009640055564403100c0200d0301030546a440c00159160000340000e1130200305500401c000907009900440c0317001c600044a038014180400782ca0341142c0c0c04200030b0503028400244082d8411a40300501c075640d601140b45014101240e2440707a040000c2c641c40d1402040200d102400071001e0030800c107070a160085c024450000c1000f084c150000950070103204d140380c48100103010313070012a0b65a40c0c603801540651703000f010040740100d082602c000f00f042d001040c61340c49 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 34502523 1250 34501273 34501289
    0x20c0105010f0b071b0b13140a230102070302060c010501050306070c05030f09180103030306050a05010203030408040e07050c070f0302041803080c0d020c0708070e090d0503010b09040605030d0903060f06 89
    0x400035645c65042d0f14200e030001c1028948008203000864117150009400f07400749521400c40591302d010b040307140c80c142e40101d00384603c5000905000d07848616500d54018900c4485150403d0701c000300503131030114540c101a50006000c41c4001c003242054002505880c4203070141c1e1f070f080d2a104c000351200c00c81d5a40c000d185401c240480e080c2030030350b480070303002c00c030300c000c0000c4120b40c00f05047d6203c9510a0b0030540000b0307180c40060110b4180710f0b0f1008020300007031000f54034518040e20303480030300e01aa0041c0701c151419840807403180c0c3d20030400e86088100d100300b80d8000780d5940c00c21050903011403104030b01560601803241d00e101c1000849170715880d00f5071100545030352110b5149240351302c000440d105441d424400301882e400700700170000c040d1284c80000e29015090142c40c0d0070302c9900602070314042c1d010240036220b82d64060141d03811240802c41e80d07a01e83e51042c00240250000741c0105030548a814151021030342e005e0700300400c40b4051902000880100808002518030a01031901 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 34503773 1250 34502523 34502527
    0x503031015090506030601170a090b01060512010504111306030506010f030603020612040c0801060e010e15030d080a020f0f090f03030306010c1401200307172502011b03020c0105010f0b 81
    0x88241414002541c2c0172005150109044408a241d00c0a908049d600d0444031a69100c10314100143c00014a01600c41410404d013000c8a8454460000074140102401aa10f4060030070341d070030b030103001c0e205400741420b948602c03280c840d0001001041c00f00d502d980018114a45c0114050103803256609481c0c01403c00f40c0740540103c40b0a0000c4030141040b100c0325200303a00024105000c0c800d03d8080c00030440550880c8d4904565070701d0113070001c1c03d07180c011a00c50107800c4080e500000d02d007845656a0401c076040703640c0c210500700203004682038043c251200041030741c00c28038510001c00e644802111400c0302c40c0340a0051560300e0000b03e41c1607000c500129819008150b40d100f000c06202d60300d400100e500400c2e00200f513140301041c440640c1856000c824801d0540c0c004d6465502402a44101051407604021000c40c0000e2560100a515407101024103154400c0d08440c031003402403010483c11a000d11130080095100f0b0b100805a540b074440049a00101e603006d0200f100d40f0204818 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 34505023 1250 34503773 34503779
    0xc0d1203020903160f0303032714030702030d0e01120c0206070e0d06090809010908010b010512060303070c0b040f08120403030e03070e07080a050604051303030b0109080307050303101509 82
    0x2034001e52000c030400c1d80c144100014184004165144000500003414101d0503051651401400756014421200d030085d201840304960f07040079216521f0b07003d4106040c060b00d851407a49590451007501c0300a03405005101041343ea0795000f0240c1180c0f0712007070ba52030004030b4003100500300321004131800d140140c01c0800401e2000d8030804910424034401001a04c468080b99540400c036440d1a03403c60f66010040780c1c00f00f407036030054010360052145030024004103107010002460f43c8100210000144152004aa01034408005581c4040d601c0010600c0d00c640f41e200034065074011344140341004005200c003045210010603055811038074000d001e41031908682c0d05a801807000081c081d054401e20000040d054031001500c2c3c0250142d4840d040d40d82054101082a1a00145498084ea003414180a007052009803424011501483c002402e08100c0340101c40300c03047d40e800301c05284000300c0c500040c0000030000f0360062009054507003103180e6030306407400008400ea0001c008680f40580c10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 34506273 1250 34505023 34505027
    0x4020907050d020d0501050a060903080910090909030c0501110a020a0b070203120a09050d030506031e0705130203150a12060507090b03070f27030206090f0d05030a020c0d12 76
    0xa40c2020807030411500b001201d0340c441089800c00500344800380c0d120b80040015060003000c15000c1d0019190021901d42141c503440020b12481004a0107074203610480c04c85039200e090b907040940200b100034000002d05040041144080c02c00c2980c2035480c0100e051300810301d4a0441c0d50048075900074020032000754980c00b05002c001450103003036001c104040d124414042081d240700e00612140010b440c5e4490400070b242c982c0e42400c0d0800e161825042c06402d59000910011140901c00340c4111405668207060030855290b00c4150049038500b0707503140e0210603401440c4581c2040501012a0482d032040042c503402c00d00c101e8043c0400010a480030441c00d030485544281c00d414214030981d540c1c403081c01d10340d000711140c000007410003502170001544180c0c01d1107012100313442c49800e0b00700d050715850143c072075200080c460710000039041159125015440a1248001c0c842c00c0d88101504225442e80e125110040c0103003c0d80e100340c90586804403a480c0302c260403643c00f01004454442c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 34507523 1250 34506273 34506289
    0x20d050c091c02041404050d0909050f060603040303140c180907081906080d090503100b01080105040c0c0204020a0c0c060c050a0b090f0601080d09060203090303090609270f09010e060402 82
    0x205981280d190001040b201403044085c1c3c2c001c03840b41d070042030300c1180000002c003a002c2580040c184542404140004004400303101038001c5c804449507544d036203031840d05800920000c28403c0000c0120070412600006200107002450540904000d8032403600341080880402144d0310008501c8050116503000b0000c20004034810088900080d07041c0c03100d0310305190200c91040903000901203c2d0502140c1404d00c0b19110754034480c1b40502940855400103092003405020b0703035020b5903958240d0341e2258810f440e0b542045401500443d030300e01021200405402d00e202c0b0654092001d504002040c1e441a04000d0325107800001600c4030403815511902d2683d00030708020350612408014510f144418000da5000f001c01c100288049032072030300080d15002d01c41d884402035400600030003440d0345001c000c0350100d140859500d039495101c0e42c0000ea0724000703c48102000148111166030140480407004d002c0c10308071119101c01d0f40d0359400d080c05d1713400c0031401a140d0303004000410300508001403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 34508773 1250 34507523 34507579
    0x60207120b18010906020912010203100b0d1e020a030c05070b040602090a090f0504020102011503020312220306020d060b071a1009020a031d0a050312071404030501020d050c09 77
    0x10b103600c8030303401c42c80c00d19082d030745000390a4601a0303002130b1039540c2c0d242210100840b50441402581503241c141079800911007188141040f1400000e001025050030341d10500c092160b2940a443c540082002178ac0203400c03100c1c05001084c640344420600c58080c0068800050384002003030016529a0350f0880039410112101c0d40007500c1c883d01049111150040381640c409884000400d0f1401d03000081c00c2d01c906a40c1070354458032000043c400360f1008501d28000340781d41c103c4650740e0f00241c0060f0ba418440441c003d00e5804102d04080108107564000f042074080e001418800c581c2c07035404c003200c244107410005241800342c1c0808480250f201046c9548412041245045203656a80301001e99002e4203000c00003e50b2840200c14400c2620018810707031071140000d12514203240d4400d9030701d1080681c011508900703030700004c0074184101d801ca911680d040a00745d440e141d030b07494800c1c00303500b08104141059081400081c120001542078401581c0c00a14485841041500324080d50018803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 34510023 1250 34508773 34508791
    0x7050102090603070215010b03070509010e0d020d030f02100216030f030f06060504080618030307110109020303070f03030c020f07061101061d010f1a04030b070512150a060207120b 79
    0x2024440e560b5940c40c01a51060590b5005040105407501b8000e0304548160040290200c0038820b2140039a400703c183d0f03116030707002c0c00c00081c418203000c00140c4a00701d01c41d009500000c003603007420415500c0513101482c2d0300740d902119140d44000c600007043e0b0095005103d2180000042e0802081c4100c1d48500315034035905001400611501c529019650143c0049010800000b400c01012400f0002c195201d000001151042c0d00764854150301d03403001501c0d05041051390031031080100d00a6209040c0b8960007800c40365501c0300d920381078801105032001038001c6850410002305490000c11000c040c0c1e4103e1000e0300c552428840300342c2c0c9130591022008a40d641e44c80c03001c52010100d100300b0000075027119001c3d15941c50b00a4540480c1d03100e80084600241065143d505821445c2c259010750f640701e045ca0b00240c3e40e803070f001c840c58060f510035480f103070b110031040c0080e40106107032103110404182e5110441c0ba858810690b61042c40780300c1c1504500c0422000f0000c640c0f00f021a0b0781000c0c0d28 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 34511273 1250 34510023 34510027
    0x8060d0303090c060203030105030c060903030409050916080c011e090e1b160c0503030414040203041703070818031201090f020903031b06011403060403110c1207150504150507050102 80
    0x991030381e080c1510f59401a1003d607100000500c40384c0b4003000502d0003c0c004481d40fa25181401c0d0220307883c0d000d1445061401a100c00c082801c01c501488003a0000e07040e0304041c04150baa500040b030380c0d00403040206010a1080c04000d0b850002c82440c055041555124118814a401204078018400038044030b1800c0c00e81e0b40200c001040da40c001c2c201703856007640e0700000094606060503004915801141b1a500400c0100185900c0825070350701800c00301c1b070042c0c90741d0b140c1c100414a000707d0058a141c050001081140310341c1c01c0380d641401000c810000141002210f03890341da591145040041c091400d003001080045056000361003410700007072016007401c0010022070320b9600f1941540701c00c44d5851408102d9010200704d03240c014040305c14880c0d810100400801d40708c09014002400300200001038002c41c98007003207094200c3da80540b00c0300b000c1031440c0906840340c1460141400203100d4a54200c0d000e4411010b4078151001201c5202c0000c1003503000f55041e60003200125025502 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 34512523 1250 34511273 34511291
    0x1020102041508040b0c0c06010308070f0803010303080a15060c06091403040608070f030c0504030803041a010803040905090d0806090424050a051e06040b011704030c14070608060d0303 81
    0x120650850048880e140c49101c3d0902c1d24001303205c00e000420303030301e001c440610100c203654100161143c1103a80042d82c8541e5111181482160780902d24000761080a00000020805900040701485600c40340000c2083c0c48500340d001103124000d1150f4000588686222004a01154040716085e8070030200601804c4c1c0c032298250654106600400102d1341420030401ca0a4008004a0340b40e001c1e4a8204120102c41030050140d00543c000906083d5000c40020200a2440704854040111100e01a410343e90390444558a60050003040e1195080ca4003145564100250342008101c654480b685141c0d030313090510090f000e00400a8a2402111060301c00161031440050121740000002048600d4030403840d000703072000a0714406c65400c1c00440e406401c04400c00041d0013000c115030200708402c082004984110002c08070305241c0302413506100800d50844440b0f41d0030742c41143c40e40e04039403a0903006034403441c0c0d51040202140c1d40780c0010b4030341d2030301412401c461072080c1000154248 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 34513773 1250 34512523 34512539
    0x40b120c06160c240306180905010e0708010f060e010f050d0c0e102309040303020319020d0b040b010801180506120307030206041502071e061803080105040515030c010e0102010204 79
    0x7880c1c1c4088080c4402c82c180403041042241c1219540600e8101402018600b07e82c41c1291220a284865141e82d43ca800d0810001d0a4200314003100c108812150403944075604503009001910810341c62a280c19000207509842c0e5001c1030480e1007800800f903665281506002d03840c0001e140032181c80d11013002c0840d8048603142e026001d02c0d61009540c40c00f5040141c034000b8065001242218981d02081024460382c80e040e031070380d0080c0e25140168694035103120a000510110250a22a600220b00c1900c04003031903000d00034860f4103e505000340200c000041d030783e130603081c0110707014408503400ca18400c9900d5000f0507040038014003106400c911580815065820800d001c80060f0400001c0c07205020201041e16004040c1c0c0340e0862600d00946c0c0d510b810562100d000d02c9469800c2c602010134012503922170070070010040051201e030300b400c1c5401011010309004584c0301d18503110200b40e4110b440c007019500d982000e4010541d14003010015075039804660559811990200700200d1490 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 34515023 1250 34513773 34513793
    0x13060f0314031303080403120c02030a0201030b01030b060708031b0306010903080a0207122102010e07030f1104021207020615010e041503020406080106090b0d05070b030406020706020301060509040b120c0616 91
    0x501813003117280c8407410340c6003004440743e05c94209000c000307581d0221400340c1d03004102da800c0a982402c0000382c032104400141c003e08841100c0940c071500c0800c0e4042845000002148141400000b07012084100010790b0340600040d540f003800213200103000c1c0b0001e100c020007081c0036491401110481591080444094051450100c03003d6004800a0901c880e640c40c0c0d240c40351040340028041000c540302e41d90b54900769448064540440072203a0790501402c501500c0c01c006026209642c0da00014040300050f403070030340703100d401482583c000600c2c645181c0174070022500b0582d2040c404910703034001c00c80a400e1840b20140c1111b401040000165a036100340001841e083c40042403891426600701d00f102d00c001c0b00c107402001c80340c0c902800030700007054841c2950544500c058a1fa116070508800078041c48500a040602c004000300b0502d4112010780003d02d42114148280c181c2502809418105040410500c1d4040f03210501d2a2a080380507103c070000000066074213018546541d8002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 34516273 1250 34515023 34515029
    0x1c0203120109090203010509010603110607020609030303070f0906081603021803010905010e010f05060619110114040b01150f030b0d0203060c0306040b0a030c030f020a030b07080613060f03140313 86
    0x10b503a032550100110b0800303002d02075101800500800c4603a10719182c000394214580c19140c071030130740014014119926081500c0a40c00050101c07500ca107444140039001421004103440441e40b603036030002c0c5041c8642e0000788600001d10310080f103030304100c41c16006508600341324841c4501046019075152400d00c01d95584500500001c00c0d8a41180001802c54944142440141e0304140410026413541403c49041c0307500c80010f0000400c450f501191040f220b041d000002d5400d003011092041c00c4814400c0c0214003401d40468640d070388454240c0d00c00d103660052008100c204240c008201d010b0740c06a944c0c1c0e43c1c080d04141424149a00080c18004129621070820801006000d07007402c00b4441c8800741c0809607a441602400c0d44c40c1c4188024440c413000342850088011b0130119140d0040c00790086901040c00c013005d08100030060300e480801c070741682c018002900e1072180c121480c0120310842c1d80c41c1504844050854070703051815018142c200070544810843c104456800303a0080c070003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 34517523 1250 34516273 34516289
    0x509040c030e0f0d1e140307020102091206011508060d03030e100c030e010515060409091e0302060a0e0102130b0708130b0417011e0e0111030a0b040605040903021c02031201 76
    0x21030ba4009002d000281c164040045840c40c01c441500e10f26004140441b003100b40d000403a8696480c0c21040303000e84034503200700b500565140005102c01c000042c2040c1a100021f12560030b0007128070302207170070080807902c181c2c0c004045a81d00300824040e511200c0e50800010a03100d000b410500e100040d550b411051038002580c075640000410030a22505401c0b0000f00d111040550240c000200d1901850081c045142e07a5000c00104100007407181000110721100e41b8a0292001c0c203020b5100c4008403409031030700741071801e58410038106200310385c0000c0d03051482124050901400701c1c1e82c1e4101540444a00808214000403070b441c1c220070500400d58202c115030381c3d9003841903445514039201c090700300c1681003401c140ca03041e1450201d1040103c85c07040004240000070349081c0585210f041203500d2a1000091189180240e044405640001d40741401303559512001e0004950485402400582001c40c603203044034000e2682c0c20000750288116804c5c0130030403040c1010280c007a400001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 34518773 1250 34517523 34517533
    0xd0b0d0210020c19030c03080a2a05150103020a0b0a0302090307090905101103060603070507060603030302090a0f0b04050108060111010501120606290901090b070f02030c03030a0509040c030e0f 85
    0xb440d04d84030000300c141d110f1150005040c54515034805c0c08407015030000801150700803544a010610506446c86440c80300d0142100301481c0025408441c10155010340300c42c045c01d121032106400107294581200d074003030400c0884034a040c0c0b2148940d007080c45c0000405400b0803451250340e800b0480c0d4400340c40c41b0000081c1552042c903005103000f241075071400c40d013030914004901503101541603d030f00c0042902c100383d890356035110403206442440d0340180260325007040070061651642c090108000180e5840c0545130721200c2d80c5030a04014400e04407080410030081c4015449004619000501810701071141990303140f2141c25124240c21003602032500001e44414040180501e900410b040310613102d407640b0281001c0712a00701c801440e00302c0600050108400e910445000b0000c3c0345014640d41c90305200d24000000300418103003a4070a00c5005410001840c021003107070a1160303079448451030400b0110512001e81542032400c011700d903031600c078001151000c0c005100743c0196030300a00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 34520023 1250 34518773 34518793
    0x9090f0105030c03060f0406090f02100e0109090603020a181d0d030c05040e0609041b0602010e0f0102040506030411060405060703081608010b0f0c0f01181202030f0d0b0d021002 78
    0x1d40b0f00b03003050b62418402e0380198148071010000f05841500030790010404038801e102d034209940c0c0805043c00003504882040000d81902d64050030441c400c8100360f07100f00100daa10300c15002902c0340c60002a6110000d18410000c9409420b04000c1c51811454003040c180c01c40c5100010104118122010781d8001d070030200c0019074144031301080c0c003900381070280c10315045c4650010507690007403095010380c240b44080340034462060464080070002036a80d118984d00c0740c000034041c100080c0d0320320f140d00c2141d15210f4038002c10300a40781034440c003404007800d40d500d989031030111000407030555801c00030401000c5050f031621402450414025200c1c200381d03007056001d00310400680310302d0504018001c801402210109030486036844050104540c40361160480c1500340004202501d0003507103080e141e01508240004011262409460401c40c451500042640c60380f14415002d02d201a0800002244400360350001d50901005404000c800d6065800f04005c1c80ea07461014025038880000c0c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 34521273 1250 34520023 34520029
    0x303020d05030f06060c0a0524100303050307050307030e0601030b1806010302010203030a0b01020c03070806070210020a090303030c031419060609080316050f07030f0b0a02131a09090f0105 83
    0x2044420001d140c00c41c0345180c001d401c0b0004080c0070704501e22401000911032480501044a85009500305041d40c1c00d040c0400305074030350384500c610fa0310030319030584002400c02c103c526030ba202107a8040d112a403560b50317090400c45080d40f00070070f40c04c140360b91826030042d500c1d000c202c034174040d41c81030100d42040e0501a1504015124132800c0114a910803401400141d81c00700c1501d03000000340700040ba81c0e00c030000040c4d00300f100540c0b121781c051141000c006258107000a045010740000d800352841d000c0001d4101c811b9205614901000c030b410a00704100091003075100c1a0344015515000a0380c69641000864840c8107070365040d1114120181c44c2e40380e081a105446c000d1075030b400c2c4000c21920700240d190b00c90042a049200031603a0340100320511006002818018070050140ca2040c0d48138034000520b64242a02540c01b4620b510004e8800300b80c40c4200c400240e081c1084203d110728000e402c14000e40f00759410a0800000d00000715a619036140950003200c102e03044220640c101418 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 34522523 1250 34521273 34521283
    0x50304081204180e07050f0a091a2e1404030602030f060a050103060602060103150207080a180501030501030302031b0c0a06120e0703021c021c030804060e03030105010918090203030f04030302 84
    0x9200030fa40d15161a000892000040c58000c640040d50200f0b038641c4205e0001c0c00b107407038a600c0100c00900b0111150482411112450441d413011200101c0082d480c81000c5401252031503020035404204040000440c0910b03142003103418603144151406413a5607401090360000c3c0c8040710340400840603c91240740c00d00405010700750030300c2c0400110f0300d0880000c1d62542d041c84050b02404000c84808603031102d0b40c048943c0d0980080049a9903a095034000340100c40b858401003c5c81003040c004550b83d0312a004a6049235010b500840c141a0070070403c140c441c01c03850203180280b29084070718202e5142d035901e0000811041d201c03c00c81d9046006d60500303a409031944210342c1c0d000000d0070700040c3e80d0921020f0131100780360720f440f41d500001e20101d01401401c4c2c0c0d1100c5100c1c0c3c0c05001404040c1d11498851140384074240500520540c044084e59034042030003240d0204000302800c0c0a42c00942646421206070032501080040da90380120f4116481a001c0816240d40001d00340b040c5501000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 34523773 1250 34522523 34522559
    0xc02100212180a080a05060403090b0f0a03020c2a01030f0606050403030f090b040b1801090e06040218060703020102071b03080702010e031609020d0f0504080d09050304081204 77
    0x607054080604240042911507a0000b1103460704031491032155403508804070703002e05002811100c03803188505000343e40b10300403107003100010050240400d070741a000c005d41d420745078141e190b9820441003e2080e406504010700c3c50615210f8543c610046020510010f0081611203d245181c40290710004056a1000001c05411403c0804c10040d00390b02000715030440ba0035103012500c204c1c96480880d0480305039880450105008180410305407a0000100b0f07a0b000d0840354483c107104950019924001c4a20920007010113070380001b081400c01d500180941085201042080f42021001800640140e1000d40040c2c0d4041014801c100e90710343c0d5103c40c00780516038043c03440e1a6a4500556204080c00203041122940300010715890410104001840a464088171551100c00301c800942024601c811240c0c10812030401c6540980b042c14050780e0801d611600e002c2e0210f03011006008070000855841c1300400c4000b031001002d0080c1d648015403c0d514566462a1181d170b0308503101c0c010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 34525023 1250 34523773 34523777
    0x151b02010b0105030f2208120106031803080c16080403080307020c09160c08040801051302010f05070201080a0911090a05040c050f0303031602031b030705060109020306060414060d020a0c0210 84
    0x81c0900c1c540b05041003a4006e10451681030707400c150f9034a0701d50498091400501e200b0001c20200c4a824101511038142d60030750703408115280c0c0d0782180c0c001e022800000035007c94002c00c04540e820351100002e280d01c8400c2c1c280038040c00307050340d1402c001d035100b903000352201c2e20044180078210794184500714241320700f03da2141080c01d055482408a03a8141e103203006000310740d0907400c200140b403000c1c2c40003001d00710020441880c2000036001c803034140c91812400100d0b44c04001d00300c00d004100740c42c05540c06035a03074a2030340e4984042c0402440c04110540d11f20b999060030300d103581c3c0c440c03621070f1055560030400f081509043c074126000c8002c03034000a12400f00c5c203000308056100002900d5100012046d4541c0d9a100b07010103900318031031000e50f0a12800103036030030764103604000003e0201902c160b0854071180c0c0d9840c2e9002c103d000aa60a540c0050200301c2000081901000301c1e0f2500c3c40280040c0c9019400340301d8008907440043d4150109421103001c00551a10b0000c3d030620303603628 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 34526273 1250 34525023 34525027
    0xf06092105060c091f0507050d110304050607110d030903110d020f040203100e07030617061302060d0b04050a060801050f0402090106030c05090a080c030d0f080105010804151b02010b0105 82
    0x140e030340c01d61103200041560110f94800300d405440c6603608501c211450550184062070b0000c0c14034024101c0d44010000d4480e803048400340302c000781c8160a5a0328100711203000d1410941040c0400070076911008044d1000d0422400d2030300117903103000e1516900391082d15503605091552801c540d41c085201441d500c5007076640c03841c2015803220180098054030855005a8a40c0d49004156507000140c100311541d8400c0010400005c2e01a07200e042551012400c40c4852044800f00766603481e41161144d0310300d940030700038a0060405c0405441c035070301c010b1004a01c088510003c141102e02c05ca45c001006a2910801c1103180820320031141c000132031403c42d0304580303400d8000c04d03c001818800d440c10180d50306040080704c0e205206031440d0701c200400580e440c50b42c40c4803240c0e6840c240c002042c480c0c02803220025819024030145000d031111905c0d1004207a01e018015a11803100500544002071010040d2410000070b1084080c0b04800340c0380b0320440002908000c5c212510110440d041c4901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 34527523 1250 34526273 34526339
    0xf0304020a090207020306061c0b160905040612121103070521070b01050906040e0102030a1a03030a0c060519090605070905060c070302040f0b0306010306090201020c0a0311011101060f0609 83
    0x81603095010601307441b0320302d00701a589001182c0c003274695405083e078402da1081c0a0520b9102c00451040c1445980d201c90991700c42c1c0070807049032031074400e581103064030340d02846c006100803030070229217881c6040c00f00100d00b002021905643c00700100715040d405c607011000c884444902d29181414071090070301c1c141703c0290340710358038100103006040c0714251403030014050307540b282c00030301040c03086074000d549030b007042c04400d40a00310b200d50103950400911129101c1e801d002040c0d601140072a03482a4040f2641c3c0c03988001840c029047e01686d840c00000e00046d00d645004036071644d80f18010004043c40c080034024010540c540003944219020040703c40392486c00102e05060f45e40480300080e22100000003003009010f06080d20f905800350307500002c2441803d500c0000840d000b0780a540d4000e041c00d0801003e07810900000b8042c0341c00010040d5554402c103925503407401300d50f00009074103445e4403520b0304a500543c4840d00080000b80280610b6030b98140c0c0580c448860f820060503018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 34528773 1250 34527523 34527529
    0x60106080f150a0b0d0b0907020d0c06090c0e0103080711010e0a060305130606030b01080601090203060607062004090c030b04020a090312030204090c110118050c130609020f0304020a09020702 84
    0x8805048100c54120800c6a0160740d5501c1902c1c070000c00b00b444013995507100b202c003540080c0c00c070f0070718003440303040003100240ea114000f09481d030002000765220106011155102c0c0c0040c10001c000391410008400701058000c0c001c24a94042e500580241e9110019450710014244901040c0e504110a400110281d611a01c054a0130fa82841c2404910b5a4605680c048071404401025205034100a000001e026400c00d40078165011401a0344542ea241c07400d201c00c1e88826920301d50403202c01c01900000c280141d0011003a440380d500c4c000c1a034030003a41c003050a81c05c507030000001c440c1e6801210140e560075114400849030190703000e6041c0f0000a00240156070540300c0940503100c94942500c07014401c0d0304840c084c26030020300700700741e601d03186005202145c074520090056291802c5400501d2892005000e03290380000104240750500e02880340c83e00512242c00641c980380c80000c200309407140090300944511a070300f42c1d200e14003801007003440e8030320b64041401d0703620400c0001d000d61 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 34530023 1250 34528773 34528801
    0x103140c030109030f0c11130b03060a05010605070b09031b0601050102010e0712060e100606050706051311060d090506010905040201020705010f021b010c082209020a080a0902040e0a03080906010608 87
    0x907541000c0131b1010b000e080040100b0030b1581030136803100540e20301d60040c080c594003d4880c0b2005404480c0d80355680c901540031510203008070004100d090101e80d002a034520582c0394040d000700b0680b400c0216042c2800c0d8101c050607982c030040d4000d00c0050100b568248100300d060382000c40100000c0345031502d2201c41c0d40d61030f200034191586543c1440540d80c000c009000c21200041030400c511070303881710010000c0d008910b08a84003410320700424000001c00084a18450708028030307030000384414003005801c0c1e001e1060240d02a840e61101000f2400a000b00d9008180720b0502041c0c5182c90300c0024140002034005a050104244482ca51b42e07a0005d207041d4070b48183c0c00d401d044090315400580d0b541382d5002c001442c2560000300080c914588502490003c1c9c0c0c1507910341c041c2600e03000243c050707000720002140080c00b1600084c1081210750086500b03507001610001c1d81c07284441401e800d184d6501015000310b000241848080101000220300401640c0f410110604080d080364001c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 34531273 1250 34530023 34530047
    0x60102120d2307020102030403020c0a080d0c02030106050618030d030203070507031409060703031a03010e031e0906070b010810180f05070906091521080705010b090103140c03010903 80
    0x10582d1281d2008500c41106a4002980d481c2d0108100c03500c0e040c54002d020f51310441d402c8006014401c001c030641e090010040b0140d41c4020060700380e0001070b200450303580c0801801640d00d0741d20703803500040ba82c61f480014030300070000070420343c1036645913414180390600d0f01c06c507002094810001c000b440799014007520a03541c1c2c50f10301203c0b058402ca0300414140640c071907183d4020340000d4141c04254043d401480e075141c40ca1180c80500c045001051300301e0350480c61010040d003080002060340300501d500c00c00f001c001207103028100b00000303020413015046070a046620040200061200b800c04100540d1101c40f014800d01c084108401c006061110350741d030090001000140000c01c04c4424403040300902000c5200f04205a41c408569000d411124104042e107030a503080411380607048209400140110015070400030f520343d5408034254040c40f000c0d21995030700d20351781d807a80e034542034060700a50184000c0030001c200b0603c1a0305001866550501c00e81c5045110b0000039040111031000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 34532379 1106 34531273 34531297
    0x503030f0c0d091a090d0c0e04030810050d0204020f1603020120031e130506040302060a050c03070804060209040617060708010f0803030c0f040305010f0e0606010212 73
    0x1d0640b13000781203140855040e100041425003000700aa980040c01c1844099103a45440c032000c055038200404155202080c00b09050340300755615000703840e44400b020214900000100644258100240940d8020580116510300d20094031410b264031041c0c2d10304030700d842c90007d00030520700f103c07070701281040031615040103044c00c00d580c444c00780d103843e0b002c1c83c8034440c0211216100060820807481c9201c14004000f480038002c01c0d00880c0f09070002c007080e081000301c420603140300601400d00150b06100f004801d0750f004142640090304404010b035035480b50400300d0081d040340d4220082c5010400d01c018071b2400d0000300c552268999079074603481662076841d0b04180400300d2155000c213134000d001003410941c0c035a0040419003c0d92245924217941c95072190f081d81c44090f02008582d0303443c1402d1040d00004d000c1e0981c442000d02c040d0202e403074928640303130b0940617070000b10003 = true := by decide +kernel

theorem cover : BRFrame.Cov 34352523 34532379 := by
  have h0 := BRFrame.cov_init 34352523
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34352523 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 34352523 ≤ n) (h2 : n < 34532379) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
