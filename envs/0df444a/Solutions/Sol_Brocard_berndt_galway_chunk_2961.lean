-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2961
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:15:34.207799+00:00
-- url     : https://prove2.me/submissions/05fde449-01ae-47f5-8378-bad55cfa88c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 532374100 ≤ n < 532553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 532375350 1250 532374100 532374107
    0x80c030c15090d0c091509060609050307170a0606080d030501061404050909010e0f0f0f0a12080402030703020316050909071203180f060e041b0e130b0a06050c07080d 73
    0xd51a000070383d0051046101ca28002c400c2e003100b0741200a8592500d08420502e61400500400fa14103802040004644500c01901c1c1c0020a02c01c1030381c903522541003030016000111640b64200e00b294101e5021501540c0c0b4542900c0e002d0b004510340c1d0740080c18800300300d9418000c242c01007045051a9051001045481450344103a000e401e004d1001080800c02806007540f040021081e8802500d0b11080c80042003920344240015141c1248100811a607980da8041b400c40c1c5039a5204000c41c07044d400c00b5405640ea2003004000f0f03070f4503000e03c1344008056101400247d400c026081c030304680e0b0b582484200200c1d450050f05488041c2c0c04100c0a01002041901d03510510f0f81504140c1d000801070360100700c0d90b100c80d0700204030140303030302c0e4000410b550080d4128203585000c590074007107440d20b40031302903034076107804c0c0e12600144c1c95030404242400c04c00134945c11005c03501c801040c9040a40049440e00e40a43c0c800350000e203000645400e1484240041d8001d00007240190131941041003008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 532376600 1250 532375350 532375357
    0x31d040c120209210106170f0712030e030607030b03010f09080403020d0c09020c060105090f0f010315090c1e06172805090609010e0703020a151404080c030c15 70
    0x45155590001d03041100d561341000c034028950110810011880c219980a8060080780c41102d0140c10030505070303d10544d011604424808840009140d2030f0b2400e454080304102050041d401e01c2051411821540c40a005071361289045032404140303101c040040c1821581d58080c04030301c451403c40702d800040d0b0b000c41158100e82d0115a00340b40480d5034205070041319003941c0b040f13090705e10008002000c0100402c2c120704030f80c002c0f00d49074080c0da581c080403e0002ca0484182046041000050000404500014110392001f00000a00e4015940c0d036817454001034116030f0b08205040c12008018134036040a0740901504d00c2c1c0040c20000c501c50080105a02805402c41041900001000111281d68640014210a07800d00850a01d660074540702c0c030050325607141550914804001c2d110001030031030100c035406442486124605079456501198020701130041010700ca01c5c0141d001003100240010781151400303007800e081003034100741c9031143e403040103400303a5440b070a5003c04010352000d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 532377850 1250 532376600 532376627
    0x81c08040803060f0d14011104080c01030c0e03030d05040c05030d09090b0102100f0f1a1c140a0308071e0e0613180e0f010b22090807031d040c 63
    0x80c55140e40310300c00003130324041210007200d40048005000c0414480d01a11003180d8002c0f4400030007070355100340031006040c4214042c20315103a20254100c4010351090f88601121559843c2c60000161001d000a080d17600505400c0180394480f0280003e02450300000310040408170010b0000f500d00704009016000140302d0ae41c4803d641e41c01d1208a40d001344a41800940800b03020450350703204078110401010001d205201a9240a83e481014864940c0380c03254048002c001c44034070410794502c03180d141035019045031005094124010441d07020442403094070f00c40c2d22640ea16241c000c8000b842110101400c010204010509401c5690040c20400c1c54540a9079880da403091090005000d041c1c03181d2243c0040c40803a440008a105c4c40c2d44000401c000780da0554100b070040410041c240e50400403102e07480509120034400580e0009545801900c00e40d1002c148201e5546840000b500402803d50102e0000e469003100d100001002410710501154100711074900c5050007006290441803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 532379100 1250 532377850 532377863
    0x4020c061305030903060c1801030905060a200c0102031e1302010c0321020a020d090311010809071503020d0606080f010e07090803040308130e0c0d1d0a0606081c0804 73
    0x681030050900c100c41340032402604903001800c184210030115130000f91800582d00e82d13411032042c29880380c05004602600000208a59218000721070000c6c200711250b50325000310410359900020100014201200c641d00005031a45003114200c42c604010500b80b21080a80300108002c00038680300e41c412840d0207180002030701480b0324003a03851080800f10620f0307a92507268032908540850f0010401808903900381c0f144802d40c02800c0d07582410700d020091190420356100b00180d4401d044040d40502428100c1d00c00c59a0741a4a0245800c515850400030b6000200d20704807444138020300008000364030f409030040c60101d40003819070b401170290070045c800030ba01082d6024403c0c1110340c040c10036036080d01ea8031aa286030080d4254042480c800c00001d0b020340003d50f00c040407001c0b911540114000c2d80c903100d1740c0025030000703001c502c1243e15031060151401d6100c0508002c0094034901c42d1000103201400c0c00c441a20b032100c100f040101019002071003c200540c0820b92542180d403042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 532380350 1250 532379100 532379131
    0x110a0b16080d090c0303020d1d06030714030403020307020109150203030402130e0f06010e070f0909090804121a010e010b09060c0712050d12061d060a0b0c0102090103060504020c06 79
    0x2910a40790720410200c00005824003058105001c42403040c14100c074402e8080b21080f86a04038103480580c0305a000003944001020f140d03100c0d0506200560307021103d0300e0409022514030801e00810381091f5400e5005a00125010045580000c0101c1c0580583d1500c541c9880710500000e503603120081000f070090303004030072007801c4849075041002105542e50a03515030b501000d8100d80d56a109215106280a140d0045040c050085191501043e156920305041d10b09150300c0c00090403419a00b2200c28800b0040081d2031092000110210340c46200748001154405841000d40c1c0c0c41038100c98000700c00000100814652903040b100300c12002c1e50115102e9000500d82800c1400d143c3c071100303484030080b2803d002c000c070205224507040c0e4507844254411348400c1090049896074000c200d90660b0307200c025102130f1040e000e81c5600002c000c04040007030b515200211050f80121084080e41c0c0e4003c20300307060079a0140200005403000b40c40860074a20120b021a07510b920240c1001010007401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 532381600 1250 532380350 532380353
    0xf060a0c020d0203060702010b01020c060c0601061808100204080d0f020718021303080a1d0108010b0c0102130303050d0e03090f0f06041a030406050f040309060e011b06020403110a0b16 81
    0x110b969420640040907150545407070a0080d020b404500121801401948000c00c02842c1c25010345002290540041017161300b8440c080e201102024800004105042c0c00007923108420000180f000e100000090385651501484500e010201c000c08800d2142400006000b2540020007104a070183d500b0390306d1020310340c1041c40084c8922000701d012019510008001c2c4810403008003541c0d0b9075a036401c003100b100c02001307900d83c100f80070805000518030001042104250f0010f081e2881c6860300042c58028108010180074000398021030101328003080138008071840388140b41c10804518080d5241000300400078420188101c40d181c401c0c10184c40e43c550701e484040a0710007500b6802d40720320020481c03152005250704102e0741180d01d00d0a080009022505e810600c0d8001d41e45512220f0b0482e0501c2000d17103c50211103443c41c1040078500080c803020400d031140c10029030107018010303138682c203504110034050301008030107004161804003004000e011600710382d040e00031010b08600c0c0283c3e9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 532382850 1250 532381600 532381609
    0x6060f3c03090c030501061409010e0703050a0b0907090501091505030627040c090606050c0a0f0201030b221103090a2405091509120406110f0303010308180f060a0c02 73
    0x242c801078100c40c0c03054000710030800c2c15401003058481b140380031841840d1410412040c00000d002d00c6890b0b0a0540209507081d00030b400245d0403000701c0c080445e6000103480481e0080d0421282da03400a0303041c2808102650300705c0120030150a5040d2000c80204e18500090094440a0412070090030b10450040525201d08481342100604101d440c000c0e01380f070304107600482100e0107540c04da6840d0440005089000340210340702c1c0d400328405000c000195032544100000b110800343d040c15182ca40f41000340c0d4624500c062525041444011502407a41c1c0890464249041f1201090b40c20024800c842c040010111005036020a0404440c1803085034103006203d4444100d0416040c281072128001010131004240400101c000402d952103041a990b1070404800c00c02d10110b040005110040c07154130243c510b40c5441d021101c146082c00c4030245541d000340d00595494030045071080d0104541107030f81840343e00071030b12074202c6490340000031320f070744980b94846042c040302e20900ca046454 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 532384100 1250 532382850 532382861
    0x307020f0319081b011404030215070909050603010b04020c010207051c0215073c030507140f0f0a09150816110a02030d0509030709050c18011206060f3c03 68
    0x105103000b400540c00c0c00b046e60703911050645084001d80a401034860700c50380c40e03800e40d40c41901540d849203411031a204214006200150010f40c25540f101500d80241e00e0b81e0006081d1414100c00060303031031205003005424071502c0c4e048076241c101882e1f011002654002030b14811464400303a18980c03521a000191040309403203211a20681404031b82e01c800342c1303810340c000b029000c1c1c9038190b02c0c011040c4c0000700d00f103030400c840710750200f0078501d881d05020b1f0210018100e17629850000d540b4103e4101c095030810f0300310004100028070040014005d000003050101c0c07580c0318600702025103003003920010482c0f40068444500300480d207016136405003001c1101500c207a40140544030070303559000000300b00b80d1043c414103019100307020000480f030b8041d00c1910702c200d82c814000c80c00e2507420f00c0d50f4030039040300c12031550420a0303140b107555041205101d20002041c6a407248100d04a62f004050705c501d110086245201a9a803446456040b20a4020011104c0b41040040c9401d50110a900611 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 532385350 1250 532384100 532384147
    0x5011818120c06050c161202250305010c05071a060d0f210e13052d040611030610230d0b040b0a0b160c050d03020307020f031908 57
    0x3541e0500d0074035060342048800340c4107405000288819696a14a02c6a6100c0c03100c00d103407140b140c60082c4020540c000010100101e00384141c0380b02030750403070004d40c01c8041e4804819048131071003810002c0000c00d101d07520000800341840f900303244103912104240c1030034406140b00300b001880011070700da43d18250720303c840d5800214801d8080540c10f1030508034140032004c05105815030703e000340242c003a040302c2812a000620040c1d002c420340318808064803010380b030781d00040e2200c0d4842c511101c3e000f4401202d00c9128200d0b4417203151034140700e019030f80447c0543c0d041400070000d0005684a2602226980d00c890038018a0b6100d00003c0b12104d0600f045030480c00000401e103281c4211050300a8043c01c0710448d000e016405c400340401c030780307264644a0701501620812500e100c00c499500d004010702e024500e400e002e644d4840129110410b00e4804600503000001c4210461030090911481d818040c1d0040c10300c1c0702d2103140c50142e44640c604c00340c48040301046100354804031901003150308 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 532386600 1250 532385350 532385363
    0xb0f0a110d02070c060207050303070602071e050d0f140909040f0618140d02280203150a0c09050a0501030e030d02040e010602120c03030708092b1205011818 69
    0x45070001c024000039000350404a404a040040c0001c805200007481d42c10750307000a015602d81407071656180c0081d404140f0440340e18202e41000600883c0605650f880319000d400038000d07082c014a8014001e10100d082c0320280820740d200300c81810100310940d08401000d0307444043c3d91701c46041640c40c09880350002440c2e10f041035000340041c00990150034495100310400085c5040e6402003a0700c580c092180d00d80140d0001d07581a00c900050741010000f82c50a8000152003411500802d042000c580f1000c141c3c2100d50b010f104010100d88a082d1100798030346421404541400e0015809500303a1090174101a2140c4c003200659000780f040b101c011004c9241155655601c5804a0402d2424410300c40035005041000501c03c5076001107862002c450000f075403850356030389020303100034a02a041030840e10038000265000d4030040e280010480141007001401000400001c02100c0c1450220911a0905004100700d9010b502c4810006211f00ca002c520314940003400b401e9520215009483c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 532387850 1250 532386600 532386607
    0xb0a050d1109040c03090b06010503061804031e020102070201230409020706090c050102030c0705091305030703022a09010e0426090f0405160c210201050a0e0a0b0f0a11 74
    0x4688600288000101983c00380070040b20f4500a80c112032070305202514500d015000a5240d6108200969000d1001003014003251911141a500d40d0710446040b80032482c110b0902e030106c2403030200220300300c2a070300c002d40c54004a030380001c01c5494420f1484018200d1441103c60000400c2c3c00d4078064440d1400440d15003d0f5400c054024104c80041500d00c99a40800400c95500c0801283d151400c1c4c0001490064905014008582c9c402440c04281840c01801d84000940c248002d00010740642c0c018140400c1031059009104140c4104e42c1e00000c6081908400ba2180f150080c111150511103d8041c0c0d19403d010008181e02001c4c03461241900700d01c803801402a90107800d29907820350b0b80801008003001800308a507402d94201e1402d41c1c551000e6942c003031195200141c071a01c0340000e5443e43e8010a80d103c90300702800380f008050b0751607208001019406100710300e00801c8160080c52030301b140783ca40344007804001d40041041c042000008032a201c058001401d00485100d40c07540c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 532389100 1250 532387850 532387871
    0xc0204091e03091d040b040b040201121b02060106110d0e0409080a11010f020708040b07030e0603130b160905190f0e0f1e0705251101080c030705040b0a050d 69
    0x4403c1041c050346000d120003800501c90b440410301054030955000080c0c003c51b4503a40ca80722000b040041c001c0341005001246011000441c3c00380701c40d100051444101c640c0b441900190910005030001f00801c200e119004050a000050140c2615401d062000e40c600008011030050050100058030007000051036448080d845802c1a03041000c1c1d0000300300f40c0c10040300e280207034441d100c40607204540a02c02480040003201c006d1603a907100381004031a41c1c0310769010903c0e0360021107203001d4404000c01d1140500c4500d5854075400700980c441c104026110300c00181580e2200e000f1280902814034802d0035010600d80144041c150341740d51009419070701c2c0a0320b0310141d001c50765284000b02100104010640c0750f800445805121080c8640640d00c40c6001c0741c940d0040f94aa03a401c1d0261138411608650115000c0903142c0201441140c03841e24074005400c01d9400303000c26a404004004102c06030f9807081c107840503100038840c419642c0c001100704844902401d112030013080c1c0313000103007030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 532390350 1250 532389100 532389107
    0x2100b0a0f0608070909090c0b03060d02090c130b0f041e0f081b040c020606131113030501110304050d0e060f031504060f080c060714060702060906160c0204091e03 72
    0x61190800ba82d903c1ca41c076444031401026130f1440b681c01014031102023424401d10304100c0c040c5502560150040d0044000ca0f00040c007021000d84001d0891000041d50707071401082d401051014265104031917181100418100c00248264460040700c2d00c507020504040900c0b40125400400e075821941c000c40e40c559030076a44441321452903000321a51858054124103082c02417061030b05003a0050324a550b1240240880080b4004041200c1d550b2a1680004c01c18060003400c0186411800131401c142949052030844081651070783c0c180d2400d0080000050307000495080b46000d524120030f5020045000c03d40a0284100c4024104008820041032100e0089140b40240045909000040e900c4040507030001060144a11030303045810ba00400f418014018030307104dc0300d141c00c0c1045d0465401080d00b0480c0030348034240140c00c29002d02a820404100243d00b0090407110612001084400600380d156203044c000c0c0a1030303d40c480381040c0000740f11258440c08501c0d000741c00c1c02425241c000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 532391600 1250 532390350 532390367
    0x621111c05150a3c06080609010905041203180b1810050115080402030c0603070c0b0907050a060f020f1e070801060b072618090601080702100b0a0f06 66
    0x580c000103600052091481c00300188801c03600540d10220400c09020003401211500203140d154180080c00586101446410b1180040421b03541d005400c5c10101c08004074503a06900040181d82403000b40008548a00060300034107641d800c2c0003410300c0102c02c1410000c12115405000d0304500000c1029034401c0d9525040c451166200340c401e041140b040380000c0360310030301076202440c1d10101810300701e40c0101503468000b400113080350040700720400041e03550350040b90f00c003000418103d1400e0820802d1404d20340c00108031405405010306050200d512a04680b10707800030051005a043c0e4060300901c05900c0000001041d60728030944181600004508198551810303c2071a00010f0443c2d011301c40c0358184c070340c0032070034034580200c3e40c0306c00015080181c0e40110600121b07402003e000000700003000180c241d406a0b480c400d51103c01c001802d1401450103050000380010030031a1980420620341a40200300009444040030700424803100f250340000f00e81c03026042011030000e0300020740 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 532392850 1250 532391600 532391611
    0x5061e0409050a05130b060d0206092e0306081504020f2d0a24020708070e06010e01031b032d0504020a2903041416030303060621111c05 60
    0x500642e05c5500b4500540001c199000c0e080501a0000c1100c6113080e04050607142c0c0000c040c1e0341030030b80751000610051303040450303a012146141c04c2206407100e550340103c2003803080d0604009940c80d010500f80c40d0b01d007000b42c0c00c0f000054500098119607551800035007824014003000c203002c1f5684d408400003400d1410070209880900f444499074504540700d1402c1c1d9084400144040c03c40c128012030001c510791782e0134290b00400d0000304203e031003044100001d11060385a06503900b40301d0005802401d030084900e04240c01c041d0107150181c0c500f40c131303966840350070f140000300f9102c0c0c880c015080e12031131070350741000d40000080700c01000255000305010310300031100010110b03902c200849144203184130148a0380621038000001140f02805598020302030410010803602080341c050400d407000c10389410140f0b040f0418000d05626200346000f4181e203080c0250b40e80c2540c1d09a0751300311500600e01c0c016903101c9228040d8465880155548a092000150400204900c0b140d0190908684 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 532394100 1250 532392850 532392871
    0x2a0a031e050906010b040f0506030c120703051b0a08061e03070e0f0c040303020a063b07090509072106110408061605070b101e06110303070905061e040905 68
    0x40f412017007a804481c101c2ea2841c1c940c0701d015160909105690300024800ca0b8801800e0207400b4064040100d10340c403480b02035400007103a06d40710100d8010102c83c101441c40390705080c007030031899a030002c4500b600304004403010628054915001d05103210703074060071600350003400800902d201c0b401c045640503100d0700c42c08504030f5607100c10350f01403800f6071320000e801640321400320404542194002009604481049819545440b000100241403544c8031401c0a400241c42c2d010100c0134800c88010300201c11041c05581018424260b035801c6078050390f01070802c6800b03111550070404d46138010342503006c4401d00006c9070030110307548103401501c942809400340500141030f408044040c0040742110b500c0b400d051640c503803240716200400400c154100441500c01003901150210036040c0d403104d204d811032200e402c01c90010000c09040000b55a50751052091041d10358000c01044140c44043d030303074070361502c40c10003e51400302c1e8100800740e02c07501d0020b00030500050380e0b00420722074448200d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 532395350 1250 532394100 532394113
    0x21f030b01110d020607050714010c11060f040c060f02010e010c09150203041811090d0506060112140105062109010605120c0f0906010203070b1006082a0a031e0509 72
    0x4103495180c2c903c80c010880141c00081c001100385000300003900041d4051900b07125885074001926007180c10081084000c43c00800c1c00007103090080040342e610000700300c0d02500781d0411760380340038510701075028940074443d1510807004054401d42c080241314400e5802402005200440a80031282c1409048010100b001003031400340c2c0008120ba04840d02100c4440211a00d10001c0c4014000454401c0e1884410014881c0540d114422a85400d002d140684624101140058400c884100f100c05500342409502c1103114448030507039045505c240c406550b43c52403d43d40d08201050849110781e030880e007a050040f00fa205511202c10b80da001e0781c0e02c50102c14900841a81e0303000b01c1483d40da0207010502130207080d04000460980014060040301c1c02d01c01e0b165103588074a04100c410001400407810200010751380402c84582040d4102c20015096509699203000b12040c410b0000581800080d120005842540710b801141201000d424005482d040500c0203030009840d07000c0e0504c0781c00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 532396600 1250 532395350 532395377
    0x9030c0301021201141801060302070c05101d031b0409062a030c05030903090d02040204090204140405010b040b120402010c080301090c02010b040c170903130308070b01120f060504021f030b01 84
    0x20540d43c80b006d01840d01d03080304da1a102c4202c000e0350002070115070004030700c0c0c000155038840c1c00148512034520f0b00c1c0e4101040047d2090b0300135041c05070100d4480da00806402c1000324111645415840d42901d02046a402134109000905003604180c44080105d80d03e00c0c410756524540003102c40899501840b0b0410a0030b0101c407180400d82d000c030260f4100304501d0442e40341401407038201a00c041c20160400d603943d4085401c80e0413590060501c102204c045405900d440c1c0304040c00740c010b138071300c041c1000c0c00c08a002c1c0f0035000d0743c1d110f023051081c0701000c0b40c15607006404005039a54070a98255596850303d0401010789644da07400e401540c00c20400700f002e0700e054021102002e080b660340009900d8201e0750790201c1c0741c0c040c00c0314446000c1041906264a100c0d540c08000d10700900780300f40d451030549441142850f05901c400f0040701c046d1007201c0040c4005240c0c82d4481d4016502040380e40750350001602c201e41580011480800809050100a805401810b0f50351801d032151000d141d40b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 532397850 1250 532396600 532396609
    0x9060e04050105091306110f18151e0706020d021b06061c0312090f020114040f091e0c020f0f031c0c090b0f03270a03030209030c030102120114 63
    0xa000f819031091581001440100c0080e03041404030303004450200b03100c4218a01800c0a500001750718054100019038840ca034a0005c24440c9115000d441e8060408a4078650203a1070042c485400c118100341c40842c0701042e1340d1020340c1c002a800c200115a00c50501170740348020741c441501c2c448212181c802e900100140032858500c030f49006029030030040113640340b60200d94020b01d41202131141040c4a00e541c00e000d403041c220711920481c9144042d05044c000984003450901c0100303081c0c9001c11041c0200d00d00c814104040741c02c501f00110740d08407207a418040039401c2c152200b141c3d52078084402030180e0b00040c501c0420380f8000c15101c21103901c000564076403041301203207050441d0042c0c1d9001c0420540d03001403142c4255180c07070172100d07484203c41a81d55010301d0011500c00d034040705000482411031074030b02c101600f889e41c1816100d8045c00407134442042510103007d1541c04203400300e503600c0501100c40041c000500842d03036418002d400f250b401d00b00780100c01382c1d4043c04540d0503883c1407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 532399100 1250 532397850 532397861
    0x60607020a031205160510051f0b0a11100609050901020915030a09021504030b0703050405210913020705120c0703290906091204050f040b060403080a09060e04 70
    0x802801c00c55000d415602d400000b10804090301c41040710401c00e403e5010480f68040c3c2c5410301c0b94014001c000c91455680041d250b015100e82d006500d4002c1d4000300d0b40c25503800074103c41c01623606903101c101004090714031605c003c0ba4288540102c8000380d444091962109080d41d0000e00d0070403d41d10303413105542c200e005011500b0b40101340e4000c40e03c08400d01d04040c1da0722445001c0c000c118121590302091460721080381e604042600450140108140c40c1c0c0119804982440c040040d03141a4850654034602c0c001d058907440c1030201120b404000041c100d6900c8140a4601040410081e221130001e41c80080d080c0c41c0c0340a107401d0440c0c0740121004a0715110304800040096074119190030940d40b0300001c880450005030b2400c01c0f0640740140c0003512511840c405046c0300e01c2d02c08001810907480702100a1041402c200a100e155240c6a10040c0707040142c5e00001c1c1d0550303070b001160144c40b482d040500080404215543c0469001d81501300751a0390343e4a00000d80e070f40340240801d5031b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 532400350 1250 532399100 532399103
    0x7090608031e04050a180507140706091a0718083705060406020c0d09030b15030726070e0105090c03090102120709171f1104030c1d060607 61
    0x1c2041200404100c2c07030164205461107421207552030700b40e8078000540701892aa100203104d10711940c001903409600e00c1072950010303c608019103150380401c8985014400c07900014a69540c400004080c0003010b203044030100c1c00003106000300d0a1084000d007a030b2214503003940b8030003940c1c1004a2506800300300d4903a0540c030421420142d480d820281409048440030300e500340224018480c012950401405010b14050900160713201111202075003817001e489440d600340000f140041002858001200c1d03809a60b20068601d000c00c1000020b0a060442c1d02c450f0500030403c094402d0000c111040704140400c401c215050300390b443e0541c0ca0150001d10031a60f0040138800020100e600f100015a03000c04068001490014170b0a03045d05002001c0d0307218400280032400034803040400f03003030310208840c011005252445d920840700c51224041d062000d0f403aa1100c4050000a08100c1a20095640000b000e1305551b1540316881d0178500e582c114808030001c05000c12b0003414040200c44030346 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 532401600 1250 532400350 532400353
    0xf031303030302090118030b1501020f0c131d2d03040618120b07030f09050307111c1103010b04020a022d0304030c03120f02061602100c0e0307090608 66
    0x91440d24142e000b03401071586507040c001d900c040f1900c0e40c644c40031a000034500c039010700c002c5400d1440c5001020a0703408045415540440d11100c41c0c01c500080300d01107180c2c12103194107803840106121019000e00c003a103203001010040000440880403c011145501c1c42170040f0244100c05080712400120a80c01034258204000a020441c80f40001c500d2000d50b01ca0000d0400d40c1c0d401e109074075078580c0b803802d5840c0215507050080301d0364580107400000c02c802c0400d100ca0001c0d0b84807607460303102d07012004110507110401600e2980310718503490703d1040c1d4105100c280340c46c242031404440b684150503a03c41d518100041d100c41c5840d100781e81106060340e004080a00c020690030b0341c1c03d40385a5040b103001701d031100c0c2002851401c10041028521034071085186602e0b61800308807034015609900d091080660a800c02c46500098403540001d03003a0f039615100700d11210503810f00c00316905510006040010800440d030708500f90444c007600580440306695030328001d01080368100d0003091020f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 532402850 1250 532401600 532401637
    0x91e0b06181009050901060e0406020a02070905011d09010b180f100608041101030b06040602070302090606040b090d150f05040b060306040314090102070f090504200f010c050109060507020f0f03 85
    0x3e845250b001075404210040001103a0342c48500032110100c0840d1700701c44540e00001c0b244841c0398140038000003403440c10401d024950400c040180d06010009482d0b0b9484041800642400400d4022810507980541000c100e0064892140d0030300342c0841d0b80010307111402c008908403005c521005411074003581e0307685000c1d1700c413070b901e080802080c10512760400d501c8011680141e540d45004000130f00d0b05030010303d0560714620620040000061000d44185018081000382e03403000800c0b5480180c04591410300b1203070310300d00845240140e514404005142c02180900380310305521042c001c5026003606501e55851908040d0b8507a03040324024001201540404100148240500381814050054985c0315448181e4070720102520b9006a00702d945410a000a11400300b405002d203032440885160200c18000c007090414615005d9641044801d001d0f820900800707502c4451041e41c042000c1c00036041c1a0b4000b940c0303d44000d00388685004460407000c041900104840d4100c1404411150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 532404100 1250 532402850 532402859
    0xe0402100c0609120807030c0e0609010c02030307170d06082b05120a020310050319020904030e03060702060402030c0a0f030f050f1e070f060c06091e0b061810 70
    0x12104103100701182c2c01ea40310821100058070701c1d001c807451041d55543d5860b4074505024000c0c01e881d131811444007446000141d003665512254219a13080c042801e10000b04d444c3d0341302180c9548110003001c0c060040d0b0110070708c0d08542c40c50040c2204421500c061041d03c1d02c2d585100d4589502c011100c0501500d0401e18031202d4a04104440800460a00354200015088440307500441102d0044210b940081040780040e04414280e000d4541a0000d01450140d0480d612880102c00e00183c45076a034031002408061195040e03503251280a401d4600a08003490080d55610003950220322a0041203800455070034905040001c4035011507903056218550f807200301c2081d4403000309581600600401364403003041003280030601c22040482071410b0700081d030800d090083d15040b0b143e03144a5404c0800c14141d11601000788903410500000c0c40035100c3c40c03c1c0007210039114000d8403c5255103e00824040100e4406124103070580d441402045540319010349014104d070700c0c00c000c1c41ca8400070b10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 532405350 1250 532404100 532404107
    0x10f0b0913020f060d020301150908100e160b0c07051903020d02120d181e05011803021f11030c190507030c03230606150f120705040f0e040210 63
    0x1450340c2c0c00a864003450305200c0e00860040d41c042040c0d610840c0c0c0020041044242e2900d802414083e10b140c070282c29824000c07040d45600c4000c00d110740107601c811003091001b009100d504d00c82e0300c24120314500c5c0760b81c9810002d5540c2040140c1007060154a01c0011a8101f09401150028412000789203490071a8200310000d4107401090ba0001080044208200d10802c0700240d00c2d0015241c0000b04003455440c0b010004894020780c84081c503900000d244c90100301f0b5148140d8400742001012070300074091030b4403c1981540f010750321200c41c000110540c50b0054180c400049140c3c0c43c51004044008640d0744d03403141d09030082d629885404a9020030804c0043c0045c0240308005540c103255407603c070044040340703d070410b50310130fa061400207180381743c184100305140c210b06016254501d04480021202d4250780c1a442c070784000090140d125140440498480003007521150840d41008900105103402074020b401d92018400008590307086810900c512a81e402042408807040001088 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 532406600 1250 532405350 532405381
    0x709050a060c0f0b1302100e2b0c0303050903100207200a0f061205071b11060c011a040b03120d02180d120e01111504030917030c010f0b09 61
    0x10f6411801881c5108002034410210754081d0740c2c044c03440320030b40c0158010041000c103500750240c284010092000345e151903281e0030b001c0c4440e540e11203410380c1c0e40b1071000c041c04400c94400200944103d038000700400d41c1001c040d000e0b02c18141c0c212511214102e51310802ca00c11044041c00f500103c1e20386c100c480085031100c0010190181c4040300070b40d6218800c41d00c0440a0b08150040f50780c0d04400fa80c298014032640c0d0f400121031504880301c04120410400d0302c0300b40c520180003a550b00e108820b01e40c940d8021283c215803518001c1211081104008447ca41404000d900c15410440c2c0e0800b249400a40400c0b03011601c03040902d0656500701050095221048a4441d60191b802c8071080c0d81c0e51200640030540680c00801c109940030300c00610f00540c4034003141c180010640c0c1d203210907a0004060507060003c1d08014019107036410141c0c1c0c0d009040d400340000a09000c00000c01810100c098003403000c800c4000d0001800c1701c400e1006403040c1c2c0e54010380001004002800081070800d16 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 532407850 1250 532406600 532406603
    0x31215040207020a030f020f2b03030e0703050c0a052e0e1c02090a05070f031a03011e0606090b1c0e060c180406030203151806041203050709050a060c 66
    0x1850000980d010031a08095a801031b07030803043c20400c000650428445140c03044204a03041c0010455241c500c2e6800b0003081d00a100010203040540109400b07070b4401c1045803041011100001d80c2c2e860b03d5030340c422903815007031302514020b00005024103002c58444000010307040340700c0302d45034815007039502e0352403045203002000200b400c0e043c150344072000030409505014803000c1c0c0d00350090051040592001e080045054035100070821380c1381d4403268400b8510440c0c640444d1140041c00d420a9064080e582075034954a044140100079409041810401030289010b021199850005a0340d15009114000561000700a000b441c021a00c02249031410290000142c0c0910346800b18504282112000400d83c0c1c00070300c800d50141d40d07514a541d2203a081743c043c05594119800300e42c980d140100000800241d11b004a44442c0c0d01c0034de003080205000040361600c2c64a170410b0341e019903440b1110b902207032074200410440d51042612505603000a44444041890400201c03481ea080780030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 532409100 1250 532407850 532407859
    0x180f0305070b160206090f0705151c0e39061309020405030c0d0528060f02071e0c030311072d0b1303020603180d0807030509031215 58
    0x10030740000c0d0056a454095260752141107445410407030003a01e019800381000c281c56100c0003c60740080800038204050ba0f8050310005050000354146880c5401082030340501c66030b006a03154500d4049900c07407a40c0c034020400b101c0ba07000d9103030b004001401508450742c64034403100e09152001c44620307003040d95203400541114038204211200000e07566036504801c98941d000a0104014a401c016111042404494415681120707560b899a500b40b25501d1030b510b08130055110150055440c4a0b500264002c0c100340203038040c0000d04002503100c1034040302c41e07580b542940e25110b00349440e01c0f4400d41d030000550602c00d0454405607026140345041403198411104042502c0c3c0359070f03141912581014400c901602c0003480c901413004d5168018600b60b12062044540c0d08286c03420300300031682c0544002e66a500c440192650240d0849420103051060105541c0310560083c40c0d02c0c450314403030b502044180c440144242c2c60f4071030603091040f41c0344108080744001d04040c58189460b1002407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 532410350 1250 532409100 532409107
    0xf0f040f0204020f190c0309050301151401020304030206041206052409091018050f0102030603030a03020c010f050112051506010f080915010f0305010f0516030b030705040f02040612180f0305 84
    0x5c00d85004030501c0308411001440807080c0c101019000040600a850201d0090110000c40c0080c504041482d1156101c0e8040b4400c032602c01e41d009208032005190090b240036603d03501c941041a0700017100380c00311085481c2500194001280800040c035000c601c201400c241803000c8104070002c08080d01c070380300da1f003c0c2d0b0b40b82c0d0380d040c502841500c0c440780e081d605280100c015400e0107410101e62000300250399004004000240d5808011154400f0b601d040040c3c940c880c0032a01401004441598050f1524003000403030140300200e101c40390f0358420004c039200000000e0045007200002d803000c81c082802244100740301d03401404590b600411450450303c9503044900910130492082c2c1c0032550400d52810300f030003072200038003840c081c01c0038010003402035061445114080004000c0094101990b440402c0304950702405403130b00401005105014200704c13010701e04000e42c8076200740d10104002102c09094031980d4046c950031000740b040c001030011142d4540c0b10013040b065100b00c04101042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 532411600 1250 532410350 532410367
    0x70f06090e0403030f06180b040212060d0c0b030a020304140d140d0b060f0a0207090c051902031308100b031617070e0a140f0907060e010203040504020f030f0f040f0204020f 76
    0x6101da4002004451161209442d0303044047e001c84032050341d00d074003650040150111003a0040c0360745412107420f03148115466650b08003120300f0202900214030601c000414002800c5441c3c0140d400b0b135000340c4e01da03030800448288060b900c40e4888601e00c08221000d00a00f074401c102d00c098003410030031803004103c00c00400009070f66035014800d0303005041c0010500700344d61603040080a000d088210b030108052090103001034054000d03072922030141032003000000415403090040e02c0783c8034405000404200c0e21140d20a0300c030b460340c40c50701c0380c42c1c2d2402e581501c0e40c1c5000101d4071500d48201724510a81410111151000e03601c0011007030300c9208502d0b00113012015240d40b03521031548084002a68101e14103100c4800348042c0c030031110b00d6440c0090005803080840c04c2c0302110004d0400081d402420f200503070841c081c41c0d110076406440400c0e019040400030f40214880e00501080323000a549041d00480c04000944019090b00b2a1940120050905030300800507501e149403001d040c00ea15 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 532412850 1250 532411600 532411631
    0x309050f010210060e07030b100215151915020304052419090302091e06010f030e030409050f07020a0f0605060a05040218130506181003020603040c08070f06090e040303 74
    0xa40c0010517680070300003000301c82c0340c1c148030744400c240d1300310340e186184500508020343c1e840303061803200060340074907000c5420150020074000e0400750161980c4600040c20840444a400e280b040148024059401c04402c6101100701d030182c1340024001c0d0050740c58800c1c0107000c00003d003820140b50508000360000070020f180010813500b03459031041d142034258818005221000382004540001410b8141c0005400d0000264014000c0c42d120a0080032008214044c0020503005111400002004070b518842c0b038120510805c10b200c00b400d00303a124221b049a80703400500001e0000303540b002c0d0440001c0c200e9046260000001081954026205e50008040361312001411015104610300c84055052410900c006254150420483c52400c80007064903010034111280907a400c0b40000350910600d400054081c503006880301e40c6a1a043c5071800034203e0034002c02c06203205681d000200c0d80821010203055500742e6036410203c600e401000d1304110340c090011400e1503202c16115885200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 532414100 1250 532412850 532412861
    0x3050102030f160305040c0303050306040f0c02370b040503040f1205010c020c0901050f01051608091e0a03060c120908030a0c051306080c0d02160c0506070309050f010210 75
    0x403011442101410f0a02c0c200340c500300580803060505040000700b00100d800e400b0340008580c1c050030f0996482d0b0303e00e00020010a1602000c040301e80c505020710b002c0740d60000d00c0e0003810710100c120b0503d000c1d00381d2011a1301203a51064000b01c44403020301c040000c4042124070b8004e442041103a003060340307500c0440000324054002181411000c040802030003000d0041d5201e90b820340c0080d202801e51000454a0b9190501515024446090721085035900c030300c0844000319010300300c5001602d00c0b85044131941d4007011100d03128081c105100040038000d900e42018400300200000d80003880c0da601d81c4050700603503a0070300901649e520441741000d140c1c06442483c5200c0d41d503851b0740b40380042d2134070100d540c2c54480b00304006060181c40c0c000407074040d500c0265038a07420071121030303614440407561902c41c403a901001030b0300200380203914210301d00d400700326684211840600c961300c4e6018000580503001b4040e0004d00b44e00700c1044a41020b01242d00b0000c4180b05850014110f9161b07602501d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 532415350 1250 532414100 532414111
    0x130f230d0f03051e09090c090d060203130209010608010e04020409060e0307150e0705010504180b060f03090705060306091315150509280b0609090a050a0b040513030c020303040305010203 82
    0xc100050a0900201340103041142d0814641810308140388040440c9035024010815030340004001000740301c030f07910354544038189680102c0566517880c003890500040f401c2a20f08034001c02140300003240e0203003e8602d02e0b0580344000382e8001d10355140e800b0403000d811030703820944055540c1c030040801c0d15000d1008007603050091030f00719084018480e040e4101e42400321400404c3e000343e074003800700f680c2c00300845080b50141640c070358400006200030310003010124070481d8800c40001da0b10b050b010414024610071604031003a1140d09a58a080c040c1a02c03040b50714a6200d000140000c5d80d00341c00c07110040c00c06026410101103420695199011038031034500e02840c0c080d07008020025460070f8640c030750b405040c5000c1e06a01301c004606600c8859000201110f800d80c80309241149611400141c90805400500134070260620b803810030000c04068942400490902c0403821590a10b4000c8078080e4003081072510600c0596182124145007244040b0780c10f0008000000100d83e00340080d40c000c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 532416600 1250 532415350 532415357
    0x4120e15160308060316030f050c060a0903030816091511011503061a09071d040903210608120a1101020c01051609031203180f08130f230d0f03 63
    0x2100c090034090030007032004040314480e43c041c4041240700103446e10014116a40201c1c3c80380c03824100d02d40507051841020405d9089100841d00d229a158086200411a80203448081307503078448030f1050a0041c81240d40b840800d5031203c003088034280300501c1504501031458198101640f02102c18251036000c20001010b140921060041c84500e110b0040d441c0400300081d21445980d5020485400c4020820360511415062540725013414114084001c00c000b03200b0406e40d26249800b400c1c44c54510004800074076568144074018590b032190006503080280140303159024000050040c0d80b0082071a010010002001d030781c481c509002034403042050000106030f514029055403103c101c82c4600500300944000d0803c041a00700f0b040e640441d445142c0400c000100b4926403009111100000304200d0080c1c0030802480b15100161125150b0040500c25459803401548a020850300624218a103200c4080040c2d40040800700c2c1c00700701c080c0c018007004500d91910080e05800f08001d5011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 532417850 1250 532416600 532416637
    0x121005090d020105012103091d07080903090a05040c0302040306020409060302031203250905030a030206070906030b0f06160b0709060e091e060a090e1e030304120e15 73
    0x50301000d1040030303184002403000b001558540700c040e8000c4103c48040350220742941e80d50030141440313581c039940a8000c050b4011031503070070202c8500c40c4081c210350410005101c0408140f01e480c0207c00c41e004418010225156241028104402040f000010509065003000000002031550000d44018101b90000051242c5140181403d1050300d4010340794407142002008464920008410551860b05443c5081a920420161000891600459454451800d11108150b40001d205110700d02559a145503e541c1e0102902600c1d9100e441c190b0001140e0b103032407020b0400320b02a00031400c51102c07413a4a128280c0390000014010307103a01d00015001e03217051000710b801107000119090700307580301d4941e803401d0380310b6080e85400d900b1010a80510000403070010b5842001e17840240c903404501f00a0007200000c600d588500c8000d040c00040074032a1404071040d80070003540c0c40703103800200401d1851901c90303007113803030f140303004180d5500c10110b56171154415082409040b948503a8580c0850 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 532419100 1250 532417850 532417861
    0x303240409050c19060512040302101407170903070b101203020a110d080403021c060e010618060312050f040b191e0f11010b0d081905030105060702010e121005 70
    0xf0108032201009000c015402e00422001ea4040301f201c010884410320300d401030311540341c1281028844403902041c01d0911120f22116014050b0190003104207840300040910400002c031544c840403200103c15030014000034003c01c504400443c0d001065140c810f668070344031009100c2400d101903094006130701100102c0b0401503480c00c15080380301d04642c160401c20180d69601e01e24415408021b010b4190150360384d0881940303054110030380358402c00500c00101c4074175109008205a2180348404c5c0701d6845032400205a07849141c05582c2c01c80681761a088912000307a4030766000c0b10004840041c1000300082c807206580140c450100c0b5415244c500d000420b8004040100d00c54030040f010100c240da481e249504070740c500e03002d8015410b1001c0e9144c1c1d21060360b030040031800f0407550803c8114600c10700300041d40004100c80240f10f0041c500f19440204100c8044c0424052560405001c02003100958040d40c90403642e460000c140d403403c00480d801d0107090016107682012039036140c000744803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 532420350 1250 532419100 532419109
    0x2090a1505042d030609150f020a141306080403050f0d060e070519140c0105010b0403031103040e0118021c05090f010209150c0f06180709060302030303240409050c 72
    0x40424402540e501031030403070b100c101054506611001744019500d18400c4204110150443c13200c0744003100820a19240368496000380d40305080c000000384103500a01801400348042e10803128248040080d5941815030a0781c0070f40019106034180720f41804128001c0c01c442000f0310b610480000301140d036900d0701e551003007001e1015012006200341400144007124600c420f0400711041440c2c4580c1c040e103c50880f202d0340c411a0320700d051a500740703400810a21444030080089a210344d030350010341c03841031074401d0b02c0c0d000d81d0156040e200c440c4070041015104400c2c4d074107182c1c0300d060401443e103280d01400343c20f000b14440d0183c01c0a0385843c10000c2d8000306024415100140300001e42c90150000c0005040c100c115018443c803640101c0d0400440c0401c105205501ca0150100c401c54203042444000d0381c0700c903410249062252200106081c80c10780a0502241d6015004504603100c90091030495407810114000400c82e000300001d066449006031130516000d1400303404c03480708103401d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 532421600 1250 532420350 532420379
    0x70512031206063105100207080c01030203130f02031905060709060311040e22030c061b2c030d110106140a0b0703020f0a06061d01030203030d02090a150504 69
    0x200d01c43c150500041c0300308a5161203441c00348104c08042003100c0d800381400885a4015000b503500180002c0303915403201e400040f07480c196a2441c04a039a007003900300c0110140e2108880c0c103001d01d821050160000f40c40100c900d13300910080030364100169011408100002d01c1e5001d0b98076a0042061002c215005140c100c0034202d00c1ca403d200000081e01c8684180c852440ba16600f00e80c2d4000243c182c40250a0740302d01e141e005503603010001b17a907050040814012810664001c0d2600030340e82c0e888aa02c2d640964606c03a2910b407540c480c8900030041080c05205882c03814540c41c03440c521b0200e0740d4180322038205415661501c41159103018000d600b141c00e20340218042c030514400c03204040d51442c100d0400c0f541940000342c8d0b65203d91408a061810750845c180840c460258040108941508003000703503600c6001c2414503001c0103180c100341e890203100c065010b0b001040111460f80c0710b42c0060540700800703001940c1d5103070380c1c80c004000341c404425020005040881c1c18005990400c8a1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 532422850 1250 532421600 532421611
    0x4033305040b0a0c09060c080c030703051215130b010e0307080d0215041106090d08121506120f06040b030316060605030f0d031a030307150f0612140705120312 70
    0x30800c1d40c01c003480184c5542c402c1e02805061100b0300c40b1f05e50800858608a40c00c0030003440950743c580b0023501e80503009030041561900c00b1480d00c4002400c12211114210b40b20320020000c0405039114203281c00100100c944203410007200d81c40103403182c0c40400c00d0500401040004207a25196890000e00b802030b000a8010700100c071070188008150503600701e02151f0342c112001581c840c05280011281b42e00402d00034508030300843c4992541400000c010301ca0014500c00c02d640d12190b404000d564401d1041e02e0901520582c0030511140782105802e500c10000340001540440d9035001078a1504881c6417006d582e004c450303907001040158055440140780c02e80084c524100489000c075181d81d0000f20860805640390000c4c107042e078070220103195541020301a01d9403001039040400200ca03102561504103810500c13001c0707080d100ca21540c002c13201c0c941202c4180c80e03055900d0f05482c1041600c0450a84150702d404140760f6641040c0341544004000290742e1100508403002a80c10300400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 532424100 1250 532422850 532422871
    0x1002090a1e03030e0d0213050c090316050a0e040b0f091009051b0a0e0109270f050607020721291609060c060e0a0b0a09110301060b04033305040b 64
    0x405d01c0140c03100030300d1102044540740040b40300d5a64281002c454028040389950501c40c2000007446400303084070f080c1c103689003910102d1810303803126800204290150350082a500696000a0b101010740d200b50703410041d48401e964140842d24070310300c141e031a003000a5503190459000c0c0e2030003540d4244285143d450a0302d00010321482c0c408000c2300d42c50148640006552034074200205400b2807461041300008025492018160034180344800001440007207582c2e01c00e070008942c0300c1e400010500300300d814800c485011a405590082d511f101d02c0382c412150311100c81c090b080c503061304c21502c001184004450194600c0c0c1180c105065048200050003030241308107061045a40c0600c40c0341f040c1b0b400c44008103070349001881c404c0c45c000e0340c1c00014101310010001d0015414541d080780c0b01d81d90103441c04425511024040500301c1d2003d1240300404402080100001814080b10081000c04a0740c189007100340f804602c03460f01030b820200780606985504104c1000780032604207400c40d08844 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 532425350 1250 532424100 532424119
    0x31305040f1413140105040c030201030b011107050d080403050106060f0f08040201020303040f02031f0c02070e0609041b1e05010f0e130203280b03120a021002090a1e03030e 76
    0x201810000d0b0000d4418556046a07443d904188800654031048400b56131008103c04d01c0e15042004a505241c0400c900090600246000307940c440c2507140740c50300c000c1000d000d1b40361400c0c0421294050594048952040c14040000410300c284241340c0140000d0302c40204223140710000520030105c10204c401481441401d0002507640042600d80c0240c0c44825009214402d0001a140201400004401ca0844458100140e0761500901940041a0221203482e0344070304426254070300071940c2d140c00803c544001f17000b042a051690204101c154000c1351200c0c1c64441e0745500401e804202006070300103001c10031146d40e00005140070f110a81c5001030222442c1d400040c5a90b49403816404001d401101040001e401d140030050240f020354032030003034040c8000d00c4202501216211511a0140c000300e0790680794018120b5204082c03950107402c80070b4917408040001e400501000f0b400c4801704802050310081e4080820103500000034503100d0130300e5450020310b80546041301c00d00444502 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 532426600 1250 532425350 532425371
    0x100b040315021c1503110d03081302040b0a06020708070e0c030415180309090f0203271f1e020a020a06020f0f0715061e0e0414031305040f 61
    0x10a8841c180300c4500da01507030380d0350b5107084040c811a4200450712031902d0031010003104040c6900a40071a0710520b201088480014100002100c02800103400305d00002c0008a540d2303c912a480c02d00b82c0300910004041c52040045103150055800401c0582d00080c4107010b00307842000071100410011014403400c0c80c02100902e66400040c0005294102c0c0d4000702c0881080c0e5007007081544503001c2900e10400c5503090040c0f0740c03842407203003014880c03410080326102402802224030858500c9030403d465508900354000303048181c10007402da8059038041010b0003030441c01006a54034002000302d8019400005502d682400300c1881208a2041210316400c54010031128001500b1090068890690105044e01440740c00f9040d19844c500264543c1004021034110000110a440400c0704a882d8500c00c0d4110600480707030700c01058401e4007041102300b496905036005100702d24004a007003800d141c1c0d61568201e4029091041051042404a0701f01846409086e104064007445041c008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 532427850 1250 532426600 532426613
    0x4150e0a05160c021009030503180a0812161e03050703020c0108161101020d060b040303120501030803010e040618062301150348031a090a15080105100b0403 69
    0x100f400082c052207003101c41300015070040d25000c0046810400752541c504441c07810803d22800641410310658060b20701081900f030005e006c8640c1c2c240b030000a85010012584024042d059100c100c41c1484170281c225240d0070f4200400c1f01d10361090300c0f0315031075181700d20300070382050030364801d16041040120420907000599001d8a400400b1130030115510885c072401140640701d20001c000340c0071305014001807088112402001128041ea64580040c0000315110098900a10014004450078001030000010b10601075070024401d03040010200c90750305220000c4942c03094140d554942d60340c0b1708001c0061400e40c0e005c080110300085d031200e42c10720072900da0b41007079210940105540c0d203c001c0008240ea0703500c50300703244501181080d4101c40c82850040d50b82c2c0c0135192540703000c451101016450090140e02000296840741030340a58642040c002c2c00c0b80000c009001c1540c403149080c1070f050b40d00352000e014000007800400d852410501d580c80701d000a51200b103008000b0007040020612 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 532429100 1250 532427850 532427867
    0x5090402130203090f0f03040602010501080f0616090810050613200714060a0501030c270c1209050304080106050f030604060c020313060f090506130e0604150e0a0516 73
    0x1c140d00c0050b241d0710b415540c0791601d0400114103043c0e10440103d04458000040500201c0b08981d000740040d0380c07200140c5072581c40303456080006504c0740000c64140070807510999041350880c40c068017030b60350792101c0c5890440c41c05240703001c403640d4900744809401c2940000c40700b518560700c10320035802c24600003000940c8440c000b0100903000700ba460200201f40d02110701c03000d0040701f15050340c24010840340040c50203120450307003000c401200007a408050303030440c03102c11003e003180c5111480007400d8002514900d00004100808241c1e40c0042402e144039551800d030040000b15201d42c10f10840a084549039004503108440b203282811310340c2e4001410503449544204085000807103e82d042c0d1441c0079529031700200a400d5540850555440f60080b840c049080d51000c10041d03540c4244840e5116030043c03500f01c03084112040c013400e00c2054090b80c0082c00504000b4810282a030912107200e1190813400c4015a03072414046080c0440c050039810100c000a000391400c82d981014260f43c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 532430350 1250 532429100 532429129
    0x605030d080a0f050115030e070b09060c0f1b03071a04150210090b060f010e130b06070f0812070e0303070308040f0204050901240f0e040f081305010905090402 70
    0x490001501c1142c880c0c10081e4a449408010300080d40c5034100405c03003050800c1c202e00040d1a000c0d09900351403001442500311401040006d107094001e4041c03200c158400d1f21501ea06100303851002607072a404100d0960440c1d40c5244081e4007010305420141801391a600c100c840c0d00e82090040400c1c8a042c3c211000c8921400745503844620b0804184d00b00800700c2c82140c2c1c8545010045014840c051700079030322030003040704c0e0000145d4800b00151000c200031040b154100400090041041d400da5110f95003801d40140308a00707100035584c07400000e42610808442821011800c3c44103590180140d58000d030b241d05042030194000d201180e40d074099420083e0410802001050501090440144038103030046c1c010302140c6000b5034881d006c0c043c1e005002c20b88d55440710100b4200814184008141c032003500010800a140810580e01c041c0050030686800080080d00340008494400409011030804040781226260034005000510103a00890080500000f0440103a840c40170702034080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 532431600 1250 532430350 532430357
    0x31e091e0102040e0114031c033c021e032a07030e0409060609091208070c1a0705091819090f0204050a02040803040b0318010e0721170306030c0102010605030d 70
    0xf040c0000080e103005401d2810540070000c1c03000064a00784d06400c4200651009418229032505103001c0e400e421221242b24102024106450843c41000340c005010f00078415001c45100202e481c04940242c1c001e82d412150310802c0078410203038801c2815003600800c800501103041c04103d0320b0140446042900203442a130f5194024010040d03da40802c01134550041d0400c2000401e1078501d6a900c100012040803850800008101c0d500c26108810042c5d401010940908000e0f00c038030000400103000a0240082440100366544035104c54a140303000304030002c0e8450500d17044001c030314200b41c8050b141c8141011804030100d40400b20000c1c0141d81076900080315616010450024001c2c1d030450019800005000070744104030001131400b5541e5070b40300c07115185403600054200e514001c1e2507041c40d04150000c000c45d42c0e05440c0c0010040e05880f5806aa03100c50342d813001800c0c201141c00c0300034003001c800e010b0182001c0081215407002030008020013418000041d5582c43d45c801c000c401c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 532432850 1250 532431600 532431629
    0x609010b0d021e0f181e04050406060812190207061e020c04150f0e0412050c030d0204090e210d0903030902130204031502090f0402031e091e0102040e01 67
    0x1c1658480f084280800c0719501d4607111032200c0c240803082c1e480889200910815210044028608a0750516107039001d2045000c1c80b009040034440a040b008006842043c0d85103400241d038001400240403d04100400b00c1d0ba4000b40249055205603085000b021548101010312403550070080c000600f441403404410080400d01c1f040740750843c010702c22900503081041480c1410200300102d0181c031804c0d45413600e01c07a00c903501520319440407600580760858041c40c68840340d0060000304181c015000c25240b40c850500d68403400c0c0d07401503000c042e496a480444c0840420b00740300c075298040080005220004070f040b050740c058010700c0d282e602c0386035549150804050003a40a015100d0380030f04010303140c11090a03075030000d40185c88203581840c400f10651885403510703c2260941c1c00c0007450042c0452a40301404002c1d0401841d103854101b01e40401f20f02c442000d40072034801c074503200003005840790300b1341c00385c603d40203541450b00b080c0e00501040c802d1582614006056441103442c003982d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 532434100 1250 532432850 532432867
    0xf080c010e030f0a0503030108010c0c0f0201030213090207050606150a08041407090603060204060e010903080a08060f030a050109120e0a12021809010f0c050a020309240c0a0b0609010b0d02 83
    0x200b6603d10b02c201800d120384e109020030440044042d5049615440081002c001a44015a100070f503a0034028100f1080001d408010b60017071b03010b00500151032440c1100f80b51030b030110300100c1c1e0005074103031440d90207101006050315140da0302c0c00c10002071000c19403c103603044c1c2c005861024061310091031b2201c0c02e216030000354000c11030100105103560050280f2ba9590400000941c880d001d0440065982410142154060081881100d6202c00351a207031281c0c2250071210184050300f950b40c03100c2142d401e9640b5941c100080c0d4400e500800000640700380901d00314506480903c003ca050000915888810b0360783e0880003c21079408a9070102030250910000c0c031842151161694260640c8052002982056220300c85401424004004c4559014003d4569028081801005901c200090b0010b809c1110405d074a5551515440b10009034031502d204250b080050b2074001584042001c0c820300074440e0308281c2101c0255000c24181d41480c0d0009000d1003000841824290001403084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 532435350 1250 532434100 532434103
    0xc150e3a03020c03030706090210050903031c060b040603140f090706030902150a08070809060c0904090317010603022a0a0209090c03010513061a210c0402071a010f080c010e03 77
    0x40030f00002000e403030342d035065458064010302c0c0b044400e0340038160241d1010045405441261040c0800030019810450030340c03e05030411100108200b030150f19124002554030492000d040600700c16200442c508034840010b203000d5034010030708002000302e20b0a1180421020a18a060b51264900030550000500210b20b00b04070303915000c1e020740e1000581017a81ca40c4001d40c81d000d0901955214001d4130343d9103160307503038100c01e944202c9011003c004c1c450751440c03e42c2c4800d5400348030713050140c0c00d140c0407a8140da00d0f207400d1f8804004240c0000740d0407040c000d40d41205c9941c10b60350400140c1003200401c0107503100c022140003400355490f00301003030400d0000c00c00c414a074100103000348500d1800d442100c0986803807038011244503080c040c5410341c0c4807019802c2030705c0d21001b4044040081400383c0a500350f0341d034901a1301840c0201c0780610401d03102d0b400100300c0d09009080c3d085c40c10b0782d8801241319410f4140d0080181c584411802d00c2040d80c00b09d144c0341c80401c246005031540200c5000207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 532436600 1250 532435350 532435363
    0x20a121b0206040b1e0901120c0c0506150a05030f070b07031806050706050604050601080408030705040306050c03010518010f06120221040303051b12040c150e3a0302 73
    0x60b42c0400041400615600342800400107581035a100001c1340d0b840c61250304040c041d542c24140841c8540c40300c10300141184c1c3c001c0c8603014442c45e20b950501c005456907420120191501d002000300f210300c045050410703548c024001c150943c01050010403c0300c0340d41d107840e05801000c0050900003003032400e01d442200841d144c101c2054030400401d1f41c400f0702070240e50015200b02c82c0c5504100000e11189400d10801d4840d540684070104140c0d519a84c0d1140c2d988002d0000b030510405000c00310100d451440f45610401450724015580e5050100300601c4d8031900480d802001e00001c018002d42080000e450200c503c0d40c00c010b000d5410280b0b880019025072000b07101010030302e01d030f185055400d00d400240a1402600c0030007854075481441032000d00300c4540d0201c01881003050307044040150700d510b0b60090040d062502c0080c0c407402c007103025032420010b03d000501004005503092424600307595600c01e0900d002400305441900da00807e050300a0049a401c659018041c00c1c0350092100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 532437850 1250 532436600 532436603
    0x3120f0f040f0f050f09010323190c170304030c0605070f120206060a0b04120803060406031e030210060f050d380606031510030605030d09090c020a121b 67
    0x7403000079220040f0045940d014491544228080e4600a815050100010381a6a001391003c10344400c4d0000f064641079401540100c0c5200e11190044a040071000c400f01d1640310300a01d12409142149003041e8593381c24645174503800405c81000020b02d0b01340080c003210080e0070b0031074950002d4140b592190383d4a0201400e800c440d200440701d055808240944a0b4504907140140181ca8910803501e60089005e80321005044801c82404960004040c43e40164028008600ca0344c41c1c3d50b40c0c0d00702c0c560f0403c2c5440c00c50441e4100904164043c0290701c50a1802d1100300145460156004a00d0b501703403144a005401c01c3c0380d11014031942c401d100c8400125010914076680c400c03054400544496603041030310308055000b15580d4a004400c50380212000c5800403801e10740401046000482d24841405042e0b4035103000907151014011140301001d142c0321012002c2c6080781c1c800c203803080101104210b400504525001509611901c20840d86a10305000d080c195080c41000345440e1510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 532439100 1250 532437850 532437869
    0x1110a020d030e120c1e150d091205030601020a2915030106090e07031b0312030b0a060c0f03051e072001020a21030f0c03050f0603120f0f04 62
    0x1110018103410406600c0c5070f560942e0a1903900450303440c040e0b200c00700c240050b07500c0341c4c64010b0b8a040d00c5a1100e01e4900703150007000501d1000702103000d454954440d24070248419107950001c400e100003024842e107203480fa8103120b860b514215000035200c1082c140d00800e000d03260071004166084900c0007010346103a601c4400801d0421510b5034031440401640f19200e58200000480e00b5030140c0101c0f81241c02c00f6004080b41c41c00e581e80c000050b91569030b0703050203480900c0d000011640c45100200c0041041c1c400003210980b10090003080e10103a00581e0600844000000002c2e010210b480102600351500300c2d111303035a21009070b0302990340c0d1250302001c490204000382070003011001143c1311411918449840c0380c0b0b5100598592000c2940a00b180700c010020900030803105071044c96080451400284411098071001e0440d08030005030b00000303694000b00b0443c1031120180d9034211204400400c03200e44d52450034070342d0344600c50301441500d03008a2600b01c080d042034290b4000d0000c41e403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 532440350 1250 532439100 532439119
    0xc0f050d030e061305030306060c0c060301120213090308040605071e1e0e01120e071a03060307270b0406030b0906190c0c033c0909050603030901110a02 67
    0x1008002d09100041d14645004078000b00746402d05400d11600d0a41d4890050b41c215a6484d0802429030001035000302da03030061541420715680c9000045000c0d149228038081030745201c0c0180500d8031b2005807030f2148a8a4074400300040307604403076070340d030312941c401e9010036545d44039403040b2100c142d00002c048030750083d000d0408103039801c00c0d03103031948441040705d40c1282c80b0312450448011640c14403042c0880c00071408848003015603080210350006002c22910360301c0c0d541c2d02919090b1010812031051800110901110745010f0004c0c0c07009108050031346a0040a0344d205000300d8001040005285980b800116510b845070b800c01d000454110503d800b083ca0010311843c0c5030501110081a000166005222041001e00c18074040c8211541c40101c040c240c4c2d034007900d4406a506014004014840c441c9010700044126801a202e40f02c0c81d402481d9651003019010f0b4409030401c160142c1403008001540c0c0313002055681055003481d106280c10b80010000d42080841c510184d00401a074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 532441600 1250 532440350 532440373
    0x30902120f0f0c15030a020f1206130e03030105190e07021f050f060d1a1602070503120f0f0c030c011b0f0c1407080a0b01050907080c04060c0f05 64
    0x1050340724040c01e07841c081d9511a0b8144441985a20080e42843e5100030000340760050030009401559000d85108001803078046039038a003a100707803c444100c4070408109000c111042c2007100d074203045003a800c01c050210160001e03400703407203000500a03203000b80f201c0344680200c0640c488100340209880c100c84aa2400c005030005c2d241d0011158400c2c884c12205001c03144400b1a100b4103105c0e040d0f50104079182e848580400010600001054580b07590441d45810441e4089001c5401516103c24106086400b210060b092588982c880f41c480e400054820040e013030080304444081c1c521b040d066560b0242c1c005070698138080c486080b40c092101058080210341e05602800c002c0880c4400d4024060103410205c880d2945020190001011000714800042e11000440803a4285d54186d884070781d1181002898818508001d88004204100412507410000103080d001100380c580380d185c40c030340800c14140a1240b84912010804055440030600581070000c1380740c0e55101c010752780480c040303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 532442850 1250 532441600 532441603
    0x90607120f0e1506090115080c0c06091f0b03070510020f16080c040501080a1b0b070f06060603022503050423090601020c03250503010249020a03090212 67
    0x1188143c4601c01c04500c0820307076600d0030008850403601020303942000310109002c111040700c5c01600000281d01c00b070000e04907030103092211074800c02450300108190398811041c40e0b0a15110041154a2403400050400d29140825142c054980030340b41c60182d0b52102408903e00078000f09403a0300341c061070700c480d42a400601c65400c02c0f038040000300c407140600c1d07000304400c590b000c1c0b02d16189980300c2541e03080041d0a0400c2005d007611850801c80019640307020302c8202d81c0c004141140c4480c0c0000703101d42082090321034000a8200c1c0e00e42141414041080c1d03000d84a60810401108520704a4020425119104481c06030070200d42c4128022904842d0344603091820140381d20075450400091855480051424400c0a004004003115041e0400d988501c0300d04e802040d15503041d0300310204054509000800c50450780c19901c05910f000c1c184c0340a404811841da8510760500304a681f60804104100e00c074050300c0540c001070b0384c0c0c1b03032080c800e0700105141c40c4001c2d041a5500220395640d80d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 532444100 1250 532442850 532442863
    0xc080d052410090504380109080d0f080a060801060323010c050301140409020409050a050d050a081902070f0309210503030f06060d060f03030e0108090607120f0e 71
    0x41c0d0710450102005608000828401c5900038000980c128010440f030f00d0f20360082444021440c500380d1116158403800ea00c00b4040c2540c260640058081565a03542c3c080c02840007131000c44064000c66043c600c0c000d10b21040c1e0007105041003020700c0452082465540404014002c04008026586c2e6a14001a03080342180c415103200001c6290700940c2e0a06000704283d87c9074035a10a4610303801c0150f0017000300009412250015528045000188ca492103020641801800184030052592030302031304d8604812206400c0010521544a0300b070381010352503421070b81c10114a83e0840003045448002d0189850191540040c129140305160b0405039640584e92003d65a0b60815600c7c0f909521501306008010520303401000040c11410011600c1070700a080100386618209216080f00282c41b1180c10185000c3d00c2c6240401c20590040043c9005000c2030034030110030314100b00c04548a030030007403910045c424039400a510704166030b848010f26403010241080b41e14080c120f519234519 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 532445350 1250 532444100 532444141
    0x712020109060f02120a110a060f060b0f0d0b040912081b04080c04240f0503060f070206062202041d060103090203060a20030a0b1e0a05010c080d05 65
    0x3001c081000c42d1040c4074004049180a444d0001d0250361540c10006100794000040f0300101300042d012804108014082059200d002c2c013404104034940309441800c0310b0641d407210010503010024411700c020803c0545029030000c0a0020704c0751000d00214024000040000341071069030b0402902c0c094101030f40310b010f041504100b10100d400e0006005072481140a1854140c0c003900d00b00c3c503649015000302c4d010700b180310360a2000380052503403c0c0005a0301c0e00320500d00315003103000f40114182080300c01d80c8020b4115110845041c0311001a40300ca0019000b40e000e03025a04081440513903100498203041d058460455449544401c180c0f621181c82c1c41000c1c500340e070400031803020340c80307405005202034005024140700d44802030840001c04c4130003a0700f00302d40c2e851004d0050308000180a148240004100407a01c00300d0003041003648040d544004c1241002200c4005407611060317500c100755003082c00e282e0289a41404d080300280909900b00c0142c81c280b108100d8000000c042198030748 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 532446600 1250 532445350 532445357
    0x30a1d0610090605150c0c03031603030e0c01080609071e0c0209010b030906071b0606090204030203100e1f091209051305041a04020613091508030424020f07120201 72
    0xe9888980d850300b40c0780f02c0c1c8111603101070701495403207001044100910b40d01c1c0d4294100c4004c002e52201180c15900407400c06403c2001c418131000c141601405281210100036001d005210360000c0041d080203c081c2c140390041c00384500041106004840301c62012042d240001c2d0554016800140004081e000480c010544503000103086010740064034011440e5034083c05583d59102c8045950341d40465500049404001948000c50f64501c15000904904c0c540541e071942980180740c501020304c5c245208031481c000b451009524003083e41840480321645103860f0302882407511018200d400d401804180086d04084032098002c400740c000c503030041d50300b18040e508001c0310b1000c07110120760107403030b200045050040b0b075001044551303403091005107920700f40302607004c1100c480c00c41da8100c00016a030350001d0444440002c00c1032002002e44000440c6001d0414000c4841ea20a004c1c910050400891805075043e0081c44a0391001c507256040b214010394034104940c0c11004181c069021 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 532447850 1250 532446600 532446631
    0x605030f070311040207030c0c080303330105031003290c03070905010e120d080609010b0702010509040213180c030b0103020a082a12010315061a030a1d06 68
    0x20200d80e0000b00da40005030007818440c2c21003448041c2d400800220308022141d203a040000f140300c0c449c0009404124001d50f120b140c4081880242000700d440c903021030800380f40030751084c4006208008009000c0c0303080380d280d4640070120151260b60341c000401e040140101002c5045e45185000b050440301d80701000c2c103407180703030300050280707c140d4485002070313000700c41403045500411b928410b016000c1c16484a0f46140401141820a010703400c40008082205011003071908011003400b4000c001d90701450001c01d81d002030a10b100d0807001c64061500490b00c82c0440ca48018800008c00040340300351081c5031040c1d0300600400d60070b5150004a4130301410404554864820b44244210a440751250390311030304068a80072400c2520f00d030380450446001402903000c0400b03030503c007001c4002420036505515006254020041c0c410443d54507010080203511a000300d00b000d5100400455580e940fa9281910702030106d0041c804102208070300444500000041c04901c40c10542e03521540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 532449100 1250 532447850 532447873
    0x3010605040231150206060a080c0d1707020607050607020106090b0d06241203081608070c0f0b010e0105130b03062805090d090801021c02090103140a060503 69
    0x8038010303600000300401e001a1404080d85143c001d40034a06200000104030725a29407040d400c01004901142c0160401e00611000d420054920303805017600d01d000d0180000510301140f01b183c5082c1c0041e2100e95940343d0b00130900320400482c1c50450f0080d001070f5540f440da040c540e07602c86055803210b00540c605140081d40c80700714410786920f0741d0018091a44802940c40b11800b034a1588040298030410034090500c441515130310a00034411254101100e1200c0c0c100508000c0d00103062100440050510043c1c041e88540700c1035100d0400d00340050080e800d4140440c5003245509d009050405810021800f80018001141250000c456010008090b0089081503440843c6803030f4250b88400042011012091407840c140c0d45003050038072240c54158464029984151248022a0420b2400c146650b03480340352900070b02400e4000350710381101036000a50642000d8201c1c00000c1d80420381d589540e03c20b81200c9c030700304010b87c2c82d05201e007001100070000703100078817400e44240705020000a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 532450350 1250 532449100 532449109
    0x6021c03090201231615180b040332030a060b0a1d010309020303030a0c0315080a1e050610060f02070608010e0604140103150c03140711010f02071103010605 69
    0x48a906079542d0500b0b00e19400030407020301085441840e031360b01c00d0040d8581103104c40754022025010314464009501240d43c4a8100c0780300c4008012280200703035880010a00442d82d0710f800603450b242c8422010070340346040c100d80d17854400d2910496a10800c2e5140120a1005036000744d0b9120010018655211440e03006071190041200c00318a501d503032042c008110350580166240c040c18080b503049043e500083c190340c8112100001d04e40e85403c42090203905101e000d01015500d00381300b5211b41020300380d0342d41e4504814010482240100c07055a011402c001c0c8000050340a400c4508e90300340281c1c1600381e902c007070150800040090f00159280307032000611504403541c584a0a150b03908000c0c01c42610322000300066046521a6058543c900b080200079000310700980030401c0c40001040701c107040d40e0340300203210101420038007205108500c1050b00d031341281e010705041e46c600303550014403800340c00d5040c0061002440480c3c1c02092103020300d004480900120000c02c103040e200d10412 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 532451600 1250 532450350 532450361
    0x1809030d06060c1a06040e0a06020715050c04031103010b0406060201050405060f01060509010e030106082454031b010501080c060a0507051204080c040e03032a0406021c03 75
    0xe0008220326204c2d0040216000c80240c006001820200d0000030300c1124070315007010a44122000350740007444009010100a808521071a40d80c2c052086080944103080720340140c4c00098070041001d020004039940940c03040e05616000b4100b40445a0390f0b0b030000c1d000b400700304c0d001d13541400784200003000c02600701a5141070321802c0d00e0f902d09054140c4011290720009180064045d0b50307600012407040e00801c010740e460b01f040007148401815140050825078030251140203921300302c1e55000d134005141828444009007405007001101e1030f1884c01035000b05540203180c4402a03c07400d076440d100000c00202281d90f210580c40c070450554140c407500b00e4109104000381d680007a20303040c50a2600400800c07454410349046400c5c2152908c074181019002500e003e89410005010440c02c0d03000c1c84800c564500c121030400c60041c60491007526880002e0000241d02420312261f0754070580255041e45a050600d42241c070342c0c2d1520300281d0fa545000d21070004415014650715041071081c000e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 532452850 1250 532451600 532451603
    0xf0a05130f05010f02010b1f0207050a030b1009020901120b040213180c02060405150c0706060e060a05030a2006160803070801080f0a2415051323061809030d06060c 72
    0x4280c2e07903123002010286c0891100080300c11809465000a01c0d40c1d0384051000142d07020b1081902d06003821107e0003030780c00745135025034a0310307005101c800540e030707000034020f10b10303804201003c00c0d10352040300058000e02c198000c4100917400b044001c40c00c029138480c0c1e00001010031601304042d00d4202c0d0242d035150741c221002400ca40c0410303c08038080606407051074200b900104054244015681c44905130b4039190002011300e8144020051913107800b41013040101010f6006c1e0459050b682c4608120310318503032944240000405100b1059100c1c00100c814940103051f48803021022454440040d0380261001800209d41500201d1b0000c00800c6070f510a040120050180385081c0d13562145400c441d0030b80343d85000465851202c2c40109008500512501c803158801031810131081001200390011a82142403510104003181070254680c180700140c002034140043d0f80d07075400580312038045102418121000414800079203c00400b801b12544d82400c180040740c1c59605c01c55000c540c0c03400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 532454100 1250 532452850 532452859
    0x1d250806010b0a022805060a020403111203040803070609110a0b040618050a060f0314071b080408030a05030103050d0503060609330d1b02030f0a05130f05010f02010b 73
    0x400803121420300420482c842e0b80103507200403081c60140b41c1040031700103020210341203119645041110074010350ba48000060821170500d0f09644910b9031150503421103500035200d0425072848207034100180e500400f84182200da651029140100c06802c00c0c0c081122014040802d8006a01e00400000e055a40250141c2d00b028580340d41144c0300d01c05518500800d03206610b01054644500d590403001d40762a4030b5480d510314410034010100e0791000381c2d040d4032484520070f00c0005a409801c030314038040b03004a80c00c02c042c09401c0011180c41180d01c40756440c40001000d82c1e1031030b0850051412a0301a02c1500c40c000031040c1c0c00c0d90984001c43c1c1c01c540c4640100240152840d141d4400500408802c80315a91800d64403c2030616201c607040300000c0040100c2d0390001c84460f0b028100340c1c8006920307031015800d20107030b010b590780c007034101d603000340300400f20f4284461846203055441e40801402409201a0740c0c0307080e10b42419450080c030b40003c101d480d859605a00500403800d08840c06070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 532455350 1250 532454100 532454113
    0x40f09080313110406030605090f0703020a051909020a03061d0112140109060501030b16030b0303090114121e010b16110a050301050a050a0501050a06020a0809041d2508 74
    0x240748280744460700b0304980702082040807140e0303525144203040207180b062000085904040c01071a10701101e48001c9400b80d13106078000d00040e11400800806c5130000c0c0d0380404101c0d4481c80e504405c01c1c0c0c82d004102854400f1130056134240c2d06803c414202d0701c0c4922a802c1c400030006042c0340c043c0c800d004032200d0150b140c0d480400500080700c0842041da10000004003070440b0381c1d80c1c400343c0d44283d105551000f43c3d803083c807042c0c01c012105102d104070903042c200500d4054001181c0ca90040d5003075039062050680100c2111444481250001d60010550012a00e012410354007060130408940f0620b1003d0000400c1030140300c01243e0442564140181e0100e002da500d24040400c00c0703402c0d5810600400d80020151403d004050180c4075203100440c25290106c91802201c505a010030312440c100101044019000b1417031008064001c05034540c0c41c0713480004540640f5210a090700c00791660032102a00d0701c4d0114040c11307040d00480c0041c0c643c0740044001506602103001e84112900f006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 532456600 1250 532455350 532455361
    0x304061b08090904060b040501120203071e08061801060e06030c150c0703030831111c140601080d090509090111070503071202030f0306010e130e0c040f090803 70
    0x8040e540852061111628004841c004101c00c514151412500c180c2c540c0c500642d030b40703803038064680540b5056581095004080e00040d43e20705580c8503802c100281400e0b00c0500a44080303105015010400459026003003000382541c482c82d240d078400070300c3c2d441d040020402c240e101d00c0a80c01800001c00038282c0030704101c1040030000340740c1090a107100302041061440d480038800d1400460181d25070005604d40b454000400095220400703002c1e420340a91085840005082d0f0342801e500165045600300e81e0301c000c0f8a803d25490841e80424001c00908030400070300c5901c00250b10106c0d41900c007103980c1c07141000c3ea55540111140045201d060040c8100c1c1056a045c03584880c030b2000100f0108030417a81c41c203081d403101209032a6608005403000500041c1c600c85940040a48021880c0940004581c1c07003c1c040501000d04010224280b44160782d21001d4803506400c9885d420071640030b002080c259500f80e01ea0500e802641026203000c124803440c81003c1005410080f0303c0c0c910740e82d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 532457850 1250 532456600 532456637
    0x50a1713270501080f010f05070f0507060b0604150f02070b03180705120106060f05030f0115020a05010e03030709120b040b06010203161a0123060a02010209030f0d090503030406 78
    0xc1d0307a40c0c10000300d804040901e031960041a000b0314410000e0102e0a0100d04980d003521040750340042003a080405009509901c0701943c41d400a55180503510741180b4600840540340304c0d00e200d58880008100452110100c40c2c0e240024850307a2a4132070003031900301042c0d80f100708900c1000b00307404081c000a00881e100300c10002c1072031316510545081545940c000381445049941c0042c6580d541c44081c01115004030f03201d481c40340c507414024111710701030003000c001a005011b142d5121101c50140500c00d4000c00c10340080562000c028000e00c005040180d82e01e8000b2106800080e41c11500020b94810708281884e5098101242403216500c9484001c6944405452641184010000c05032518048405282c500340b04044450443c003200d008070181800682180c00c0390010080003101495075900000700b003100070b840150700c560001405a009028002d80d00750140a1348001e0703100c18501103144840106292036925045498009142d07407401540a01d4000c15490380011416091 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 532459100 1250 532457850 532457879
    0x2041403011401062a0c080111030f01062a03080604050a020703050919030b1303230a110102090a08060a20220b0f1e0a0905190503030403050a1713 65
    0x20b42103560070305ca481841032801c00041e4030308140c400d4092140148a1544c0c2070107441c10088503410541d0847c00c05129846c80d60382c041c401c410500c00b401041e044c2003920309611240c04002c03d03401040050140c00c002e03102038002ca030060700c22850540003443d14800351003958030154040c0c0d226401e140d050000d000d4046140303000a05250038003d00000050140c1d94020f20900000c102000c6900c4a468046d190b40d00340701d6150b03005c42d18141c06444008020094034200d440c10b160500c40002401a043c0c0203102d0b03d2002500503645607004111284001502c3d0300940c0000c208015000240115180c11304410061160a090401c9250840d14114607841c105580c180314002000b81d0340c445104040e4008030740b1a10030034011465851500460010304c0340a81d82c2607000d80303800031000000780502d802e400341e02d200720311448180a40c0304241c030502015000140440fa6034a8880c1807590f51652900c0c01100c0c3c0c030a9421225200c0c60350a0103844042102040361035000d03062102038078858a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 532460350 1250 532459100 532459127
    0x608130f0203210703030b030c150a090b0a02150a090c0e04150f05040b0f0124050f0f070b011e06080c1201091505030102130501030b03031308010204140301140106 72
    0x3c070380400402c3c00c501c218500340700c03041c2e28800740c0c0d6110342d5440d02070251039910080074445d8100c8159040c550302c40040182c00e05060b2000c040e40c0c0c062080003a10045c0c140d4000a040340000316050741865000110401d0001b0311003180c030810f031b964030121020b50320380000081911080d003804105040c100382c1450f40040c401d454040142d04401121411a00350600851106807242c0c10301041c0b085640c00580c104140810000300b030740c1042e402001800500e421012400042018031440d1442074060725001203100d1549550390711444400180e130b802c08202502c1d50910b100002428009a040301240c8014600c1020078080c6040400d4642a5008014410038030303040040204840040701e045020305807559000415444031a04441c0e15000c5410a5000b0f03031040209182341c108030601601202c00c24640440c0c050070a1010034214000e00c1140040c9000c004808144050190041c00c01d8a06283c984119124448205030036151500c0b041c04140002000600c0950301c00c0c100d810500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 532461600 1250 532460350 532460353
    0x1e0b070f0309090906050a05060904050606060a0311030406061d15041808031e070f050304120513030b2a07060c1e021b04020322260d060608130f0203 66
    0x2c943c0c80b034002065881c1400d003240d959540d40204000c100007031094640003541175981c80760785e00d400c1d543c5580e074100240082e4403a14011540e64002c501c2034028150010701e900c2d03d5174890409180104c042c001034002d02c0e00071030324807060902c07c104c45508603100d0f403966081c00c980c0110342001c0c80b00410303503450341c0c0610542140b00c507004501902c0003503006140302132070141040880c64441e000c40d60050704803020880300c09802000c2940c000d042e246c0154101d1740e41c0709841007003542950301c1d120b0600c4d10750109859403c00030501a2a50700148101914031005007010300300400d182c42c000740c09414100129043c000300c80484d015500900383c82d00c15041554000c0d00e01c2c00b141d41c05040741c454040059220424a451039280300380d071901e11140966041d4118200000300c207030613001400c0d0b00d250104d0400c0c0d0707403018010000d00300340850110455202c4020100340b071a100a500125100041506007400059000d204000591190f0080400e032076040809581d070380da4412007524207903450f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 532462850 1250 532461600 532461617
    0x8030a05040302011d030d05010608190e0a0b180c0303130b09030c150403020f0a03020f090a090f1127191b0207050a0b0304030203120702011b091e0b070f03 69
    0x21100402002502a05d0329801940c560003001821350607204160001010001d0752000c0c012059503150424000c03d24200011940c030101c15041403400000c40005481c0010071001c0c844c281105220740300580d10300400b0703108045c10035000c0c10390f40c1c0710349124078400d4014001c0c10010100c0c240054000701d2402410396070b100e080b03040002c1064070202001e030601100010108114680041804800b80041d10013400c01840c0d50001420307440391044142c05446140f0009201c08090f500c200701d015840b0a01c98648134941c20701e5080312103614550782c06020b01390000d00740012402104d0080a0303081c4204440740c3d507800b03d40c40d8048290b60031140340d545ca6011a00d060312540414041c554025401005818680340401c0603000142d448001c00c56000c005000200e0390101c211010f58218841d440750a0b1141e040883c010041d944260f400001c865100402c025441001c007811034060450845807407101003290703013030f00b60b0300d20460010303260401c105400103240183c8541035038003d0820066 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 532464100 1250 532462850 532462871
    0xd0e150d1e0515012f030a17190207030c06020712082503150b1903060b07080a08040309180b010206101d100b030c040501021e100908270f0d08030a0504030201 70
    0x9403d1768404841e641c0d81011400340269503000141c0544060400059412030500c882c0c8106105201c1e021400840e1b0005034010515008104e003943c803c1c0e0061086580b01c181d401c02d00a8192448403d03400a182503002c11542c902c81404030303034a820248581a803030711030000c0640040ca0381c91b00c0031444440c0d903540041c016000c1d101a00303510301e0225840100400303040d00101202c0360f40d0891181040280054404165444151f80010780c1a003807030b039030a40b62800d00341d40e4840a50301c948030f4225000306c0301c071203469507030010701030746800381c00f114a103454117802003055840a000d6000000485e1000c4131150001041c10303500324684080c0e032484241c50719012000c0794011030383c1d80040e94002400308003d5074100151081883d203070440301907030070361032601d80c1c1c480320540c1d000c0007907a440d00b8040c014000040308844808180d01810618400da0000014210a0146031588594154041d1000904010400d102075540c00808c1e10b14542e6010340c00002440d015009904640da07a51440c034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 532465350 1250 532464100 532464167
    0xf0409020f10180b0c06190914010c0806010801140d0206070b0106180617160908330114190509010b03040209090d020d0e150d1e051501 60
    0x42c00a21030b5200003078007001e04a88401400d955012040e1550100040080034402090141d000080100361410b0301705504d510030301621800d00050311540c0c00840c041c02e60001584581498a001d48411106580350001541d55103030900c900e042454110300352015500e010103907404440d100405050030040503486401801c03900340c001e00003041a182070b80c01120b2206003a2030003030203585051014860741d0000b1220101300030f04100300718129076044903945402005640050103d9a00300d940c00d8071542c0c072001c0d280e888050100100b035015010001034140307801c044d82c103840c80d002408600300b00f450240050f8601580d0140c01032240380c080402c00e0b43c0d0b528141c600030a09030500c0c54480c182401080040344001d0248021039101c0e81700910243d4021070f100d56800d03038a040c28030484403c00003040c188403a503e410a43c04800040041003403440b9444030001607d0403450100219910040804440c000c1d94075000c82e003000450744406602c22042074041007902e10610314011603070310f00f0a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 532466600 1250 532465350 532465369
    0x60f02120403060204030b0a020711040e030c010c0e0f04061217070b1e0a0c0c021201020403230c030d020709020f0403050d080f07030902090f18030406030e010c0e0f0409020f 77
    0x111075844d00000c00708203000407642000e404c103841820451400d005950307081030345070b030b24141b1710b00030ba445140107806400184180d07032507068500000e1000c10807000c1c0c002c05001e20a5a03a80c400d4440711244401400c061051030207a54004c80540082c1e206c5440d444801c1200c1c2c4d0300c00d000c00604000d40400204d5190301c0e2030003000104c03841e58640541a00c0c0c21020b040080c0152000c6180c284002ca049500108004c0c010342c040d20052095421159882e029204540003c1c2080b141c800b100f44040c5030a030a101d040300c503500700355040c0c50200802c051322401701249220059200c168140542e1324158000c05c14403580d040d10914281d0f403680c03007a0400c0b0b1100501000304000178104080002100c02956002d5402d01c0c00700040302540d40010011100078005c2190162204006040d42e0800c1c1342d8072440300c0050f0220394480790740e010018040d0400d50280c10495090025040000f402422159507900c401045042e509242c002804002e0100b401c0c03e9038400e01c40790b410300303c50300c0b100c900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 532467850 1250 532466600 532466603
    0xc301c020c121306050906090108072c0a0602030f0a08060f101205060906130207050a231b10030e0715030e011a010c030f030e030d0c0305060d020109060f02120403 72
    0x520349a418202c040c01850340c3c3e9600180500004002010250342d60034200c43c0843d03400d08103c202919004400c813022580c0b0300f5880b98990000c40d12441000040201c403009150899002d403815844e40d10481e101d0180b0800300c00107860600030440e940d405034000691024015069543c11102c080010740b41504404c00790300490742d0400c3d1940700c00341a01443d64007a00c00d030341c003143e00e0801e02d000c00c03030080204003056851940800d0b0401000400c0c0204001f02d40c20108003000f01171002c080d0910b0100702412000c00744504129000e00f060b01c6000500c2c103040040114441c1c1d02d45620030340162248407aa00d440b07024207140130500b05140d188003e050380301e641d0006180b140a54a043c216030381c5100300c11840d20348030b0008400e0782e40500441034256142c40c1104806003800000e030040c200918200c00b030f5000c0464140380c010b02d698405030582d03280c0e40e414412516404144041014502000303030000f08100c0003804a03502805070000900002c2c030440f40c0c01000410710710000c1e00607420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 532469100 1250 532467850 532467883
    0x10909230703020907140304320c010f12050705030105030d020c0a1403011d0f010e0601080a0206090604230112090b0a02130902040308040501020606100507060c0908030c301c020c 79
    0xb5440c190000d040800500c00c02c1c08027040c4182101d0015942d69201c3d20700303482c100804085030a81d40e81c0308548980002e10030840611107800d101da8054803d070801d00170741d80644240c841440340e00c0d100159090388400040c100700865800d006003c00741d030102e028502d03019034940040b01500031000700d142d00c041d4415000707400800518201c071401d4036100a008002c41c0e0000c00140007251001c58003140456044075030556403e491000300344140159444541c80340b0019002d41c014411140c02d449065409a0f11a61a0000e9003440000c0343e003041c01c0a014139031014009411104194024051950440b82c48916166120962402d0740e01a400407680010003040c200483e580401049800010403103981e41d03030240502009140e0b00507031b100541201e8542c82200c0e03400d80500132a40c044c01e20030301500e54440050f8542590b4408209841f07400b6800094580c1280c00c40740032030400e508012000d00e19000b40340d6094416041580d0010641907801c00c00038080d8002003016000740c100001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 532470350 1250 532469100 532469123
    0xe06190815060a031a030d0e100c0b0916120308060f010201061e1502010513062403060902031b15030405072402070621020c010f05010909230703020907140304 70
    0x180440036030041c0e440ca02d00070303071119080c54440c7c0e800c1242c0545610040c0d50461144070924411a01d0180740d41000d800c0c0210702d810b200d5050000710301c503003510708038a8030305140b159200c0a108040980d408040d0018101602050842c0b401518a040d4500144004110f558440d11801504003d18181a01840003810104080d404524044955800d140005c00280c90018040340d40e090072181d001385041e036103151000d0402910141c15188900e81000e416005880740741110040c01610400d9110b84502001c200c210160501188078164004d0403000188552154440c4c40d500003410440713481c01180d101082c070940c01100e001003800201c2040602031801d200107410300c081500302008002106401030109182d99400204140002c03a005960f4000ca800c0e9a006000c07c10000c001c41c0c0c100300001462800d0354120101c040d001d600c40d400075180d26054040001202442c0d140281c008680400261508200c6954005014145a408440200b500064550084400f1a072005248 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 532471600 1250 532470350 532470371
    0x613060302060f0406080a0603032f07260a080a1b060c0e0907170606030405010b041518140f061f03060614120a021803030403120e06190815060a03 65
    0x1c403140d030060003c7d441003102c141591402807000245c040b079045604020113144104400b02c0c0303407141d1280070001c1a1843c25807a0300c8106240c0003200a0828407441682505492a01c04120000c40d10b0340304400510b0300c640e0550542e0300c291004958a511a9074802c1200450320500030503004c6040c50740c8100000c0c40c013400b04400e480c000b42984082090601e0316029554000300d4080d00250120b41868407681c80307260483c007600030140d00c40d401504100c10029842811711414050314803501e0b100d82295200012101207034244520051000f500e0700c0400d8849412038000d40e00300201804607124401e0165080d030380780421003a01310000382d440100b003003032a030301180f10100701c0f040340072151400c00c1c4100403506101000d8800505564000b0749600a00f02d0b413000760381000700140580f034960740d490a00d01d420140d06901500800d015811051851820030110748010085501d0b90030304d1030071100101c0d40030100500c40c2900310b405040e024026901c10000c1c05102815503000b0401c03c1d40d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 532472850 1250 532471600 532471607
    0xf04230402190b030105090c0706151503180f02010512010b130902030c07200d080d0b03030705250909060e01200904270c09150308030613060302060f0406 68
    0x202840c40c032681c100e082c00d0095102c040c00300c0741103580032a203a002c03035101c20150182c58802d17024000c103075924103501660765802041154003210201c440741906860160380c02d41c260b6041e8100c2a51200300150f480c400191440b1200d000d03640180750450030b00c81c01c9109828980420303000420b4030344002ca60200d0004008c2c1800000c0c26031803c0660540c209044803124600076260010480e01d511502951909200e41c7c0f003809080e4000c1070305c1c0700800399003407080c200d81c020201031984500300400d40b102070a0020888a00a5100d4020401c001340921980095215466880c0c80c95001c800001040e141c180102c1803201d004220004603400c825030a10b0071140b004100d401210085040c4901004000301650003010040e6000300d542d81c030041c8201d9002c004a40d0328401e104441d01003509020650307405909640c160201001500c48480c07008030704030010311004014000800000e0158103020001803490000c0d20800310359a80c407580003803642e4000782c0014820800c04102000595807 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 532474100 1250 532472850 532472869
    0xf080a0f0524041b0804020f0907050c011503120f0302090901060905090f0c0301150e0d03030c0207080604080316020c040903030203190204081e100207050d0e1e0f04230402 76
    0x12074013002079000d00b4166813000c800345007148040c403c02c2e0001509544407228501c1394480f000b084a4014502000050703e1900a00c52100c0c6079860103402c05251030200c540c94080d6a0000454a8002d44aa078121441d80001038080101602481415841d8817020740e942d010f841d190721184031440c10001401110a030003807804640380c40c040148501c00104404580c1510140c8207a031030a04109039003a0744111042490301e07040042901c00b2014190f043e0704c241149074040e401c1e41d44055480300425614030301038401514200e82040400c00b2500b564030304491407851b50059800d802d4a410000d01212201e540035808a03400000300240c07a184052215076610040504605043c18100b515690b4040c407101c0000042d40d4108000b000c031820820302030311350803020341599104581c3c50301540360720b12205a11702164102080e0340143c9441d4200c1420707038943d5504464500c8111007041182d40c12402c403680c0082e40c03610001c0ca441c8010102001c240c0d500800f512860a051061096000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 532475350 1250 532474100 532474171
    0xb0708070e0d1b030c1202101e1214090703030305060324150d080901030609050c120705040f0602151b070b0403140426010c0f080a0f05 60
    0x800c0c401100c030740e946030500551140e402000128800880300f10f03061000c01c3c65000030b00841050740300091028851042280f005200759103e015100e012002501c04507400d0b5010002000e0000707403000302070f2148900d0094000c10300004034190903071203151018410242c17243e58054000410600525030540074468120005a00808107000340c54001001c0e81964051101956512800708ac00e10b04400c2000480d680f004044e0b481c564000d141c00a480c1d8000c50100b0302007400c2c0300f400a014011880750340e10403004907041c24540f084514681204c500010100c40c2407000034003021031040e88040d1034001410141c0c005101d41d101034003000081ca08002c0c012000c4a00700300c40f0030040d40e00342c019148250b03401040c85d01c040c2c80380d14080e50a40d00c91030b42c0481142e008640040d200c40500f1004030f03c40f1211040c1d03080d490118031007600361050600000b01203842d140c03013481000e1103184d413a5408075203074900207282c070701d00c80e80842541c10039107410710b04544610b201015030000520100500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 532476600 1250 532475350 532475357
    0xb0109150306091a150d15020f0a090608070e1305040309090c02010905070b040b040b0f091801210803060d02040b030f0a0317010e01090c032a20060f040309090501030b070807 77
    0x83e4860390001c0e400f41480c5d18000c0041d91f940841c0340c841800c50b0103440d4190114044a900d07809092030040c1031301d400d84503801c000b03441040490350050083d0f0343c48100320006003100c18040706003013030440036000280040f0100400a20000340b000740f9842620344100180d800803900030201e08109140101075040381c20000020402080340c00d40030b10403a01141c1c101050f0b691101941c403504000380c0111020a500f0072100c500d2006202d9144144a040c1d035103441040c0140c0208407c49102daa03021000105580020004190b40303140200716241850302c0100041001841000070a05140c0b410600c031041d603100c1400c2404258110070f0a502c5c0e00441c60780c080e02507140000604e4400018482e201850b42d0303400c0300404240c0b00e60042048904000c114500d020003040704416140b0702d0300d0303e60000554218807244021a04c46000c0002032840f402030185407110501c1030350410f4040d20450038070120200000705883c09002d1507009602034129940980b0700900c001e004604000c1c00001007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 532477850 1250 532476600 532476631
    0x2030a1b0504020906090f1c06470402040911040906060c150b01170907090e03040608010b1305030a0302070503060604050106022509061710090b0109150306091a 71
    0x131a2145000e0b00c0200c041125a94018003095011800200d42001c0d20149544684908000c6c4940b42e0016002e81841c6244e0803121101e000000b007204584401c03140001c3c50f404208191100d036211504c20b13034000280010b15041d940c3c0844001c030f0b0a00e81b0024500207001c00d04202c3c80070f1070f22401c0010000e07070400c2061452075980380c030603a217a0601c801c040c1665410008004e80d1040407685060b0540ca0000011410903582c268ec0c4e4000d240f081900040c01e00300740b04490900070050f1400c0361707030546400080342d0a11a07409100d400c14800d03d01c80349143c5200184e582c1c5c081145002040c041d4000e44115810041854200180104150301940c01c0c40010030200da070011702c03987c980d40b000c6200c0e000600320113048400380d80c1d0b96010b085000d0400c0c2001c40c00401c14099221808000400c5454005100d0020420360fa041d00001e040c020f03104004101c03c103180e030081c030f91744c01108040c80c2641d5202d50315001265402c1354140d5100d0760f00303071580c00e05800b0b48646523080011800740041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 532479100 1250 532477850 532477867
    0x2a040204060516060f090305090f030d02031b0c061603031a09060607050f0706020f150108030a08040c1a27030c15090d030e090f010b070305090d02030a1b050402 71
    0x3e01c594840241075411550f05081884242d61104c5807182c104c24040c420318845080040c0b45400c4042040d10031210b1000c0700d1000d18002400c601821050340145040802d500e68425400c003c8031514a080e0045164180a6035540c0c40206052508548e4485c00b04089080003801c81d00c00d4a0310914440ca0b04481400564448101075844442142c030250b599607280313049800c00800d9076944886104030301c008143d0310f401154861080303074507000f120745058071440142007030356082c03145541c1c0e500100300d008507451141134070552180c0242000320181d0b41d905211070781510001c4040d400d188010500d2000d078054007450309651030a020b10010003484c103d0009446030880000ba07407080421200000886031848140d4248802c002d2001c80c50001398107014050040e4802503600c40c007400c100250502030b451045505071071003e030b10306040109075a0140d95944c452000990f00035040040c401c01603400708070b442016072003258500c0401c541c0740d50804111201c1d370410361049005100414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 532480350 1250 532479100 532479107
    0x12020304051009110405180f0c130c020f160501090603090b07030f090b100312050c060610091e0515120c160c0308070209010509010302010c0209040c05032a04020406 73
    0x3042e500c03280800100c014440c94141180c400441906800c103041a080065901c800122580c000020106071540d49440000c00d940314003030b841035070f9030040c00c0001c1c14240d451960b10172480142140110341c10400c140f803074149822500e80b1008006401e15500b07221950b840003440b00207102c0c5040500240340c0b190b42e071464042c1c00030014410196140070144c0811260b80001c9030356a040102c03900c039800d0000e804060303850359000503105503100e40c1e0f50981851184044425000e030b8400079290581304e007020001c8513003070b1542c2c1004020300c00f032010403210f03241c1034407091051401c0351040c0591324010030300ca0418038950115100100610407240790742d00c070411156001000ea00003d954071001ca00c0c112414410b0740c8050140410514003000300140d01f0014005c0078000c9600b002603a90312010005d5040d02400000d0008040514010050a1028040381c225100f04c0590045688800c0440d2800c18018000c074030328407038071240d0315452012071942400312806803000c1d45000e05000f07018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 532481600 1250 532480350 532480363
    0x30c0f01151805063613050d030902130c08041101020d0f081009022101051e13140c0913022b06050d0602041806140402071e080a1202030405 62
    0x10800b05446000040469849406030790302010304040c05010f017040e2150560105407402040240c28440030301045960089151140c1c19a900500510482c0218502100070302140c5d10100c0e000030600da0320144200c42070050f03a0051031660755021552609091400c014410301e210f02d4155000014268103195100410550b902d106007040e11a41e203a51040c0c00c0c0024080d07200038441817002c12003070080320f015100644100004500e03220281d8a4a040004081048580c5072200399842000c1c3e50a060038080c207079403d5a598400514102589075890b000c800850b00d4400520001900c0d0700340d4540114480130b001075408045082c950462020391103c404142d400380411401c02242400000b00d03001240a040060117400b01c007501c03460020065006030048024102103907402c80c80c015a948200c004441c505000404024044000e10000358401141507a05004460550b07042c0c0f400b550343d80200d140315001d40c641d1044501401490041c0c05a542c44d003007030041090101260f400100c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 532482850 1250 532481600 532481639
    0x15040302060a0c1101090503040510140306010c030c050706021018020f0d0f0611250b0601050d0b0916080121150e0a050c0a050102070308041401050408030c0f0115 72
    0x240c0c11208502c1030710818010500c094603176090114030010054040050300443e04186c501d440390210582050301e10400034a1810301c142414000200d03158030652040c02824002d00b41002035038000c0d00c13100e0400202d6000000940e00091b415000b95000340b24400d000c071408000c0741421703451580064003400e90f101c0b45a201c0c0180102c0b99050100d800001801303a58005020440441d09020441c070581007401070180214003103d802107041048506030941390b034440c1c074031405030b5103240055a094120440946a4665a42d541e0149850f020a114000c1c2c000c1c2c0220003550101820040c540201604103001d1000b003079001741020304072560040b145550041c000340711000e14a030070000803d200501c819040c4a02c0303a000045c8140030036041001c40f402d443c0303c100341d40c58800690380c2e900c42c2d00c4002c0450b88200420454500f00349841240c0800500d0546c1c80c1c170307684d0502c191844e000058481c50a80207000c2889405601b44181d1810484004401c41e00c10714064040c0d00000142c0307903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 532484100 1250 532482850 532482871
    0x180a06020906130305011a0103230c1309050604200421170309060702010e030a11010603050a081314010c0602031f1e0e0903070f050a0f080c1504030206 67
    0x109103616030740303aa0580f410303100b6656164181d207030b40741842406000040c09030403c510402d4403201255100b030040401c41407041c04500910950020401c5204400810079121210309011a200a6000442d140000d048044000c151428a0010030046503085403558a1059290411400218440c015207048990380340c0100c156002448a420080394803100041036a0011144001c0d0401c0c15400355004100c580c0883d0040c1c1da400909a0890b9140e6440c0a242e83c070600c140c030f004602c150a00b4032440ea40700004070701107642e5643c8a20f410300c0c481085942540100b0034038445c90201c400b000007481c5540204105102080019000c4070b40703490090105a0000006010704c008240168a113030f40d1a072440c410503540703503034081c6004032020035001a00c00745140025003035050645280103168050145180c00d80b6569440d090b0102e00070105c4090040f110b10402041050300b020040502981d007080e507603407800314401d003000b421106403500e03518407405000100394000f07280383d0310030001c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 532485350 1250 532484100 532484107
    0x1101050703030f0504080a02010b040b0114090a080f0601150513050405130b010308031f03020f0405070207080706020d0314070905040209030a05011b0206060a0b07080a050715090308180a0602 84
    0x5089002d0f02440e003020b02c40034101011712040040c03417030003000f213207400f54020840004000c007084141c401c8501850b002540307a2904d2400b0084907001490b04003001001800010755500307015003801c07a0541403280c0c980000700100881d40c6942c20070721511505250072858880c000034031001c801054081c00e802140da8000262108801c07401d00202c80340c02013501c0c9007030345e50b920740920b01d9031045035180200700c10704280305045202003640d03030107480d03000f4451200019004240001031800804681c11403140c0c0c000022500d000744155005060b641e4083c00440c0c1c455a409000c0c5c0d400320310b94020a04041e010000c00a038000e6600003036600850300965a040500d0000781b5000104002604951820010316100c119041240200080d01d4003a10555981c50080183c0c0030750780d1081500c4000d003046a500080d90410082040c0740e190300f0180d080001030b44411007065003c1064422180e503c201d8081415001b0109540c01a045081803036030406045200d5151100800010285500030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 532486600 1250 532485350 532485353
    0x40602070b070c05060d1e180f0f1202030c0114152e050301050307241206030f05010f1b051b010b18071103071a19051608011211010507 60
    0x22241002400002c0c0f080741c946c0344400040d0001e000b0200f50b0020402840b0703402002d07000900540000e80c0340b840c8032840c1101e85807a50440704071f40c144115000a07408220600042c202e019094920146030300454880c01d001d54400e003103555590640640c2e02030102080100551200c00044404055813041c005200440303515001320289075840140b444c102402400b09507000f40070354100c0d4002c0702260110791382c0c3d412400d504252100c181140311b01d0000350520700c0c0e0081d11647c115040c241000210310390b0b00d8469154400c50840121110b0751283d801c80303061141d0303009a0b00109110850304021652000001d09548207030500741a24401c40b0f0b14180c1540b0b1b0a5106d803030000780c007429119260a0604400c001000b086411001003030340b100c585280d07160000181c90b03c3d00d03400000000c00705503100e03000c403460b50000c00b900c500c1d128003142c0c08841c0c481c0f40038042c041c20910103100041d41d00e02e0380103010a40140c02c960311035609049c1c00c80101b106034108211020f000c0c2001036841069 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 532487850 1250 532486600 532486613
    0xc2e0309051902030111070f03050c0a1709040c0f0509130204090501091e020723030c010f05180f030a1b0501060803120a02070b160315030c0501090b040602070b07 72
    0x188024155000b50041d91101080c85820070120700e2080380200459414180c1c2843c040c02801c00241c24941000c0500c070010b801040140061007541003110180710b0b42c0e40e1015030405805049032040c1340c0114000301c10381000e0041c0c2d04405403600700742d07a600e00ea4100040150049440080c451101041c04040d484410f0f8102c601920000c030090009603140d440c164042c2c20703194000c3c1041035100710654030752a0148287d58030385500c941031141074508071040c0c032000900c0d03541c00007890004000c81d1507602806d20840c80d1031008c10030b01240f6858030140454655510509044040e00409140700c41c4140100440c1c1441c48503003800030081411605202078031074914801040b6601e02000861070341b40c0040a0a08848407801046555540c848090301b40d01819034000c111140000100390194031410407404031440510300020014098050701206042d01c0c0e0007a20105841d620a0000b947e12181282c05002c062079030307a20f070a1030038100139035811161040e1070410302c0214107503041286 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 532489100 1250 532487850 532487861
    0x1a0306060f0111120a021e07050f011215090c11060415090c17010605010509030a031202090415030b072a0302030405061206120705030703020112020c030412050c2e03 73
    0x1280045480d0100c52816201182d884811100050b201c7c6107560321500c40c0c00c0c469620b10800c4e140250001c64500414000c2022220780c05a044c0705240544008505c0940b003180c6501c210651051a111700d080c958074200c03021050041c040280e0071640d4046444001070698000c0c6e801151820b040c0c06414184005000120700104000c41e82c0300c000442e1409000454540d5040d031000300045075460700199000d01c5541c00054054012083e017602083c060743d8800000d45c2d501302c001d407030a00f03110000703021100100c0400b407004031109402d109102d619102c1603400f541505100d50503009174202c00040c0f00900d00c0b001c842069040600003014401e000761401448003030070107034441200d0820290700010071219240030b5002c500c1d6001940000081001c112000a0080c3c020f60f0b045d9001158100034520505010a8080102400c144010001000184100d0494a198214a19109040031304421615101d2400c0c1d5050346405551044d903c5c03108050700b1610764001203c160158043d11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 532490350 1250 532489100 532489127
    0x1020c0105090d03060906030b0c0307140d020d180b270a061d16170705120f0607030b151605060103060c0e0604140d080c0105191a0306060f01 63
    0x14204070a11032580000030750070303941c00026281031000f02d444401800848038103100142c0801010800310720120405402903130410190f190a009800c0094524a01030380a9900c44210700d600107000640c1e400584108145034145440202c0e40b038540c2e80742c82c40c050202421074000449801c08a041d40c0d01c070001501d00f5005e41c0700542c3c204031141d060203002010341000c100703c4844804200e1394541c5002c03034a100c21440c0c4900d0b184200741456440081c08500c607000800d02cac842c558010906941e44515034030745091050041a400d0100d8140906010005e40514103250038154a000181e07550030411441c100119691038a0700d0010303c400c0c0850610b490f01a04600a480010050164a030062041c0707a81948658401607400c40902c1200d1080b446441c1084081d2074105460345440980001814040c2c528507045c0204515000c0c02c688042c1c60354940341c142411030341507201c60760040310840360100340b9141840f24201c010030307205c840083c44e5034450343d5a0503c80001740e00400294598a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 532491600 1250 532490350 532490353
    0x305211c020c03120f22020907080703152918010311090409050c150a1223150102010c030c0203092211041d060a03151b05090f0f060f070501020c 64
    0x24100700006021081003650302903002c04240459190070100c0110740300301b603940980b07048155680c0b9101100c6441e0090b148a04040d00c43c2c0940188680b05070025000d0320b18806080218030410380701c6c4c00203190801c0e81090040c0140450400190006a0400002c1c003e080116008028500d00545445000b041d158080c0c43e00d4141801d01c078001813a100c2e007040a646143e402081c040b03070001c0e18012132050200244200e01c1c4203a0450a9400c14203076407982c51001181485103c0011149800031240080400c00c1d00310920143e6a09003d400100b4100307080030000d5202d0b50000a40340d200d562200c0d406034070307034040700c00c00d035035445451480b8025960740800007117081b1049803500358003511890680e1440034031280417903000300022a004e10801040282c0d024a50b82e078442081c810004480e0350070780da0f048811010220b00c0755110034112141e580c00e66a244601c2040b500c141c0c04005d150040300c0c3c1c1070589005840b00382c125451b450740100055210940b500c0d080b8064410380503e0a410f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 532492850 1250 532491600 532491637
    0x30c120905011d0f010c050f0d15080d08090c09040b151201020a09060e04050f0708070c0b04141c050f0c1006030c030c0801020c0307021302090a0305211c020c03 71
    0xd80da004588078010b091588001c0c44050384000c4101e072a0302400b00c0880707900d0070402442d6482c9d00568012501c20201c240c0e96541c8941d10035441d402c00030742420343d03c042101070080102600d010303c8001c1100d40708640042043c00c05071106400c44000404c9450b2200e200c0070307861440c0e6540c1415a80051181009540e107010110004242980900c9410f0224186140000310352a003800f416209072480f925248903a9100318088400e803601500701024428040766007000324004d51942e40c4214003a403160104200341750255403600e1049900d2001e86281a02c1c2042c4040c1c1c440225400305a41c070402c26100c080000009080079604940750700388902e0590008200845601d044048a000d8880c1d8803e040d55a1180d50a038440e0000200c03260304104110130061520903049540c001c41d08400506109005010515854450300155095032050100c40010201180803600882e030010f00300341008100c220010040ca0801404000181c020501d8840083d0800c26070309003060b2030381410f03103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 532494100 1250 532492850 532492901
    0x30c0e090603250810090f02090c16051c0201230603070e04050f0607050c03030f04030e0d200604030308060907271a030f061e0411090f01030c12090501 67
    0x106040c92003020307800e020f0842c5c4a00070031254440e010b0700d542c00554001781904640d00700310007040000d0012840820503c03909406900001010844510407001007024403202110501325903031050796141160304010041d084400c05d2040c2400c800b9000284401035210100084d0900e60b4507000034951034086404c2000744000003850310254841a0b064a01549401008580302c0c410310420066642c01040454164070450001d40d40c841d0081c64185128407641c030005128806c0321805844d01e201220144550300c00ca003100c0604000100c5201c0d1401d0700d1640c0182c480c0d00000d08852082c1f000500050340180901a03407690060258404c0c0800020906600c011800c01d020b07007061404000f00c01c3c04101c440c00b003164041c0101c030203030740940da43d81010403030121300012001e68801810301000c200e43d11940680c01e801c40c036000041c1d13181c2100d80188082c00502652084c10541409980c0b410781e82c010200e02c001e650041b801055412035030400c61b000d031104550707659041d84c10035035400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 532495350 1250 532494100 532494163
    0xa03020307120e0d20040f0507090b0432100f090909030503060f01021c030c0e09060609120a0b0c040312020114011701090803100e07030c0e090603 65
    0x251071107582c0d8152614408501107038a8100c0b01000b642080003c003211300490170130100072018002c0d0030b460542180d03d1001042c01c2d6010100c0410b219601c0748280600990018003800c080c10216002c80e00301450a8030f07107841d003907134481c041c00261510b0604210b81440940310000141c80035101e0700404044240042441d044801d0000c0061540c103008610000c0502031495908c0d0950b8402d82142c6900701002482e2012280035411b5204004a10301401e280704101140200581c0300001d04200c0b03040003825190303103800864030884010381001156595802520b05a14080d00e404980c1491408101e18000f603149003d0503441c40b500800480c06030100c001c000b034074440c11014035400702a503030a84c00c0e50703520002407202580000041c1301d480040e51022001d07030a0600085010701050701d400100307034020303603801c0800301f41140f080c400b5002980016400c03046600e020401c00034500001003002e07002409030b40c4122180d00c04910b450342c0400000d0b60700910084080e003003031142e4a001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 532496600 1250 532495350 532495357
    0xb040608060106140a020a14030702090c0301140d0b0103060504080708030a02030403031404050d050c120301080a020f03030307080f060a0503030c010906061703070609140703080403020406090603020f10110a030203 94
    0x640054569895013464803107a00685610202980081aa11004e0f5482c188050608501e00361144028040307a00569500b410003400b0344be840c075040c1d949504141c1000c01c642c205400d0580500c49111a9034009a2001c100c0e40c1101e8009000041d26103035807074140081d109458000d17105540100500c01c44885590056015510980b820009d100d500740c1102d08001c82154060450f400c41d02c0e041c40468064001001c110090b4020b851220000c042a2001d036082a04038650b5039008401010450402180580421504800560451070084030040400b01d0080000e0710741c11506003c90031079162007500c9005004010156900d0740a0f80c80341900803c40200103a800c0303070809400080321000c182c440c0300c80304891b10140d441c201c91900c40380082c0c03803008001ca602100200003040418014020800510312a40d10345940b10f1a600410040e0740b295006460000d107404401c00050b40c40030700e07a41110809495170003201480304000c0c0d480c0e00d130a20700f065013409010b25900c101580030004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 532497850 1250 532496600 532496609
    0x31b1306022d0a0611190806090f090d0f03090209040303020a2a02010e1906050a030e03030112110d05010c090306110403020102150a090507230906011407020102010b0406080601 78
    0x9800c0c0310b503032003054041c0004084090440e044100c0440c04500e1039040740c090f00207400e203040c2ca05041011003004941d030200821000420302000d000072490107039181c13500b0140c0611164040d08055104c1911614150302442c1030043e10b00030404118040e40004244507001407028506141a0070090f0281d8000622030001844408605003910b400d02d000e401c0c0251f40c2c900d403100c0810250300540d658108011034640c0a902c48c900e1140700c0c400080d0f140e025041c0c0f540c4490304c49a01d030786c0150985003c2014101d107608284010b001c040700c0507008440e101c0d0006103410080c031a00c030100e007500441c081c0290040d420300119004154001921000301d900c5407500300208446000e1010f51404ac078000240117800007a50400d441c6070030203d164100c144400000340300002c0350380ea54506441644402480d0080d10007951a4a420080c03915410800750f83e006180c2c0381000000300503045044400c0c01840c0049821000d5900c00d40c442c1c40804000f8004100594071221065502d038001d204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 532499100 1250 532497850 532497883
    0x809091b0d0b03060a1a010e06090409210e0d031b0c0902130807050d0308040c080d1706041b200615040b010c031704080706090c080f0a030203031b130602 68
    0x1007003040005e4841c2c04c241101e41c104200800d03220400459040040702102c9920a20622040c0d1b01903a452040d02e03800c51050341040d4105620b060203040c2c0c501c0042540c401c3c807402c520640f03403e458456241d10010f6040c502606c44680608494150014003007001d0803080302d043d4013081c241e4541e0300611142e103840c0d041c044004e0b90386440d1070351500f00d8050290080c44643c82c400c0080c1c020018160020f108180c1040d019440c1d0f04082d1074021200031708000150b0b0380c00c954401191011413603030000401d8506000300c0c2100c18915440400c0701b10007400b0016210301e21300f540c407030414820004141e064203562007414800200902180007a01d200c1c0300c3e80c60aaa00420740d8014400d40388040e5040c0c03607010f03440d1265400d1400d008801002501c17805403c000d41000903010b4031401c41540d22444907000f11500f04038a10b40360030115003040e429a4000204400440e0300002900c2d07001c140341861844002000e4031003a001e016610720000c500d802e941000c20504e4011030ba00a10112141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 532500350 1250 532499100 532499113
    0xd140403110f030d0c0e060d0504060609020f0a0f02030d0e07030b16090303030926070516051309020307211b06090605090109051c050f0303040809091b0d0b03 70
    0x20220b456074021030410716aa071082124040d45076068200d0701418502e82070400d95600c1400100f0071540c00f0004500c0d00d9981c60080100f0002c0a2081601600200c0401c5040005c41c401c4520b403807103100c0b52002130164840402c4d00d000d100301304844410101c000309000b00c0224031175070b5940b07403e107000480b000146500001e04404440da04e0006500c0710360785402559155031030030ba00030806001c007600d500f0070221040011160038000303c140c003d0540c201503a00c0c2028101103051004940c51050000000c0108000c540d0710402e0000d40d410926030000b6002e041c0d0700c0003030b10f040703c030340e2190005c004a0311580c2d100400a000701e151440c094480701101c1200c0c0d903c00305002c225400703240041001759600340401072050010300450700c03040c1003955002e0307110030000d000143d110410300401a01400d002d010081d00b844508050303c090301c0250f0541c02c1507580c1600e90301a01003058050300c5540005004c050300d40c0101c000d11a800003a1956405030258031101408148a22500078480c81 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 532501600 1250 532500350 532500377
    0x40606030603170a0c080a030e4206130603060906020712030606170a0e0105092521020112050906070e0609011d0105090406080c1008150904080d140403 67
    0x7008a80c0e201c0030517901d40f8820182507403a603419401c0310f10408105949c03081c0280303001d101001441d00d00708442d0682250031424020408040b4a215200d01c4580c485a1308a1108210500c010341c002001700c901c00382d00564a50b241e03005100a90000d0802801d05400782d05004103a402041018000e000b80415a0b0300c0c2070060301641c84501c649000900106102890950176182035500070f88001c3e000314540c5101701d90746094a009580300e09040e0400d00c640307442c60b04c100c0c815001d005000e0201c0030b0b50710f140c052010359482d0314503034411035010010441001c40e8403808641c1c50540355582c04001e541045c4141513030724042100c400c40402ca421030f000c1e80d20314180c3c0c2500c5003420143e6888640d035062000400c440358003c0140d07414400c0600010015603204d000d0344c2e000e00b196034000c142c210b245c003041180c1d070884400003100b8090640c1c240440042001c0d034142008809962104035a2a10301d45102c40b0b110b904030400c032281c0b40050892403400c003041d4460043c1d000755901001c00b2181c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 532502850 1250 532501600 532501643
    0x1b28090501051203120a02090415090e01060b16030314070e031e0c0409030e1819111b070f0e090c0102030c03041205030c010603050304082820040606030603 69
    0x40b43c030300c1c90316540144011001c1d40422a00e180e44184108000350030060b46001082c00c2c2c506c6c030107403d50110641038007800405280d00c94115a6184803000744195071402401181d14800d482008586a060f042c112083c9406500503465003207040b0820310041c98550401046210b2540204e0310a0040400c00101c2d11350001c140703000c0c480081c02070f180c0700380c030841000000d001c58901102440352801101e409990b464405032811400b05150900f94036000880384400041c80d9402c10200b458800c1c0c0c6100301d0b1592058803216003007000800c400288800c1c0ca03d203085400e40c01465014060200810702032040f285950064000508490360000000016a00ca000e05d0002c0311441e4401d100030402e400d013109101410034001d0003541d2504110030205400e580071358006407250340c4006000c111460041240401d00e604002503546050815034219400020707200010302581c80b90081510002481461140102002801008117542c0d8140140151001d484240d44c1e810300e400030145804c5c0e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 532504100 1250 532502850 532502869
    0x1c03060803130512120a05120109090503031b040e1905090714040b0f12060403110312070e01260601030b04060e0106050309121318020c1b2809050105 66
    0x2d06100c150340907052400b030000d21403076502000340038440c00d17140b2080035604000030140801c542c3d48295440c6c0300140d0100c0002810382c0100c00d180e01d060024404101c0220550340c001e4002c0003000d561040551244941e0702079908403000ca903850a0500100400101910401e03c0e030401e824003596644500780340c0c50b651188191422188803101500c40c5290035441031042d40030060040a00400142c08035280803460503000007290f01c180d0900c424503801030351000200030b1540041d171521080c001d1050f0600c1c8050035481c01e204e00c84106424581c010584400e440740c1483c40300305031201a42c200c403214103040c1c540a01082c540715a07412182010301402007611002c40100c1c68691034804215000d910041c0703e0119401060400040041e41c40c008003840e0503030403803680c92036003407509915a804901d007402c00c60500c100304180ca104804240224094003035120344180c19000c0c00420110200c21081c00024541e80e0040700d40701020446ea5019070b046004104081d13a203613005d000c0c07480e2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 532505350 1250 532504100 532504117
    0xc050c0703021201140c0405040b061603051317011b030903140304020a030b01180f052e0b040e090d0f090311010e15030403020c01080709140d051c03060803 69
    0x8100c0030061001d8109910000d034100e02e410000540210f80c0c00c10001508070a035218021182c0018042001d03151a0250800d4504100c41003850401142410b0081d00b0764504000e090201c041521203075034a40605800040c510002007601d06011185c000b40200f903d01e40c942420881040000d412034882d200b40040a5816143c61541040c00314546403160001002203a1150315a080400040d411441c542d0007014814818142c4041e1440c40c1d2082e01d031180e10741801189410100482d40b100c048012500c0c412503100111606180400555945604c3e0000b500e00070b1b0004000900302000e00041d8410040c3e00c0694500401a480032219041d0a981610000350f007448213201040e05aa44025050414103140c40d00a04042c0868151000148030400d0120084104014103070188243c0580e80001d2900302500d10f024000900308000300c0c051b046417680407007642812911820b12686005420104442d07943c200411075040310421a0342000000e03080c0300001400c010300100ba07031502c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 532506600 1250 532505350 532505353
    0x1104060e0112200d0e071203020601140a090b150f0c0c0a060519090f0b031e101503090b0901200301150f020c0a0e150a030803010308030408120709090c050c 69
    0x44449483d1641c035400013955140e48507a104072115040c0404c202d450002d000300910190480e00318103019080200582c08200e907a565523400741419a2032960b1901956211200066080b40301404121008010700700282400e000044080440f0b0030440030b4001000d80000300c80e0078030860740c1405104906442101c01148040c0188010b4960f0450345440080d217500c0e01d1000c6075074980c0d12407411a4030703611921816a000061042100d44501829884440c2030341c0a003444c1066601101700c101c181c40340080b1080800e42e0080858440c0d000400320607008004840b0504106600c140203090105819907102600742c109114002c1402c250781c102d5941c1a060102c081d20030720709540c84211140b1600031802485034503074032581c6803001d01024004600c80c2880600d803640080b0112140c07810780300d2107242c9500040000407042c80440381545c2c0c1c800780e050b03125100c034605038140307010b201c500400401d09a8104040d290340600c0640072108481420f0041622242081c0c0d841d02c640344005010317 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 532507850 1250 532506600 532506641
    0x20306040f02010c05030406050a0908061513140c0301080105070c0302150c0c010915050705040308030123030d03021801260c0d0c09050f030f0a0f05011104060e0112 73
    0x200e001e052241064a0042c148040d8210903a6582030655200d900034801240c404510050515801400c690242c01c8041c0145980d0030002981c0c40999000045207102d400800700341d000347d904a40000044021014541060303041c1805085120b400c01d0140048542c40c200c00569424824050940400e4258000d03001c500b045903841c00c11401c006104404003001040b0282c500c840900c104241280640d41c00c06a00d1100380741802035400c0981204d080100038031061001c00c2408040740e044455040c07020149240004041d12400c0b40c05442c1c641c50b010300201e0035901034040e0010018803601590025403609200f005480b000c0240151403410801040e1007a280410490b0103900f00710745512260611420001100540311070011100005002020400807824015403c020404007100500400c148085607d030355620380c028040c280c03901030300800d820f01500794000a030400d4207035406591517403070303c00c00362a800301032501e180052411201c4400d560110300c140555404a40c407010017 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 532509100 1250 532507850 532507853
    0x10906050304081615050a0b01110d030b03071205030301060e010306031505060301090501060f050a09050124030e0703060504150b10110327030f1501180f1109030705040902030604 79
    0x1080e001813040340c1801104900500c041019003142c400f03260204d40e4049020f240400010f01a038481c0e400003418071140c1040303609034031004240e514120102e883c0014000d070345080001e1800c41c3d16270094401c564280c00d1071041c03141c04402541614041d4441d041c05015200045084403800d10001e00014002c401d80c5d08429401d0704559006000100003240c0240e50707072100c90848032640c2c0f014021071003020080010b400c045251000804084e00104102d40c54854540380b04040001c1170745200a08004103800103009034031150312110364904551001b5203925000c0014a0700b070310140c03a00c004c082c003410014503190285011030b2a01402210000403c2c05d000e440000840c1140030240c0018444c850100902000d00284148550f40c040c00d10201c190505084c40007522041600e5044080b085c80414801700c2c4090444191901e0340509041e0200c1d00c03001880b400f00100d001030b00700742a00a600e4841d10207008031500803010307548225940d904020072140810b00094158100e07000150 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 532510350 1250 532509100 532509113
    0x230703030203060310050109060501031d1b030319090f0b180114090402070c030b070203040f05010f030615020c1e0102060604050c090907020d03390509040204180b010906050304 78
    0x143c0040b0090103d411300c40382c00c07180f00709460b0243c00c2000c072542d0701d00007003240d5a8103015041004050701002d00b002e0826185c0d080d100c100080c40500321480e0002286046d07241041103659081500e415007070400e9404c00000c000c40304a20402440340305901003c43c0c0f418400341202e2494209619131024038005c80015100100703140c400c1e800d000170034003100d40706461390300044c1130300b0b80300d00d124800103030451a00054400c2c0c0070340716030115130041c4014420700108805c54815584242010305480c040000210f0140c50250046910042058403503030300b0a40000b814000f500084404500090302914682c000284240740f540c01607122001144450410340d00458219082040c82490305040c90041240c18000b5950403005a000519032801d042d4544984480c0e800c180b40041c1f0f8000c8100420314034102050100020203c00307804484403540602d0841e245800c019009648480d62201d0602d401c07000306500b54500f07401c02010314402d40c400c525420a40341da0392261402c546035034880d02c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 532511600 1250 532510350 532510357
    0x301060c12030e030d0b03100209130504022b050d020d0e011107120c030b01080109030c020103180b090a021f0c150905070e0117010506010516031b080304032307030302 74
    0x20706041d51070403903210140092008005490300c4036400300d80c00f00d0345801e1601d0155035900c401122413040c02400c00c0c03562500203a816052001001156945513800060189a101c0f0444800340a402501c0040020b480300d90b110042e0240741602c0442c03000b180183c0c0c0740c80012001d40c00140280200c02a950b004210303607403591415204455a5640385c801d5108240c201460540c0d20600c4000f00f08200659510041e0250420304000d00c1650f025a80c0a13024482d81900241459191401183c2482404403c6280b550b04012404030b1424908100b0f519000301100c1a03001e1844e0400150341510615594001410581e0300c3e440d505070641c40e440c41ca034450b00d2800e400136854030780c0e03c400715608001d480060800c44c0b10800240d49001c1c40440c3c2c01050015800d40c41c1d06201c10049240e03008130503962020b1452140c66800303000d034a41203423076200390000650b01c80403044a040601c464000958401e91081d2160198213282800c5400d0300080810303090340360341e8204289800248a90042c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 532512850 1250 532511600 532511633
    0x30c122802030c04091e052d06010f030c090519090606080d090323030d050c090f0f09011a0c0a08180a030807230a1a010506130509100305030d06090507050301060c 72
    0x181d41d1543c0c60701e4000049041e00f21230540c00f280d4000c060140010040c0300c0c42d401841203c401482d85c0346142c0d560900a8550310071030501c65520000212a00030000300740d182d800c1070500801030b01c541407901c04010812401205000d1042a1000365014012040351054907040380000c1050502e40300c2804080362000c940e001c0500003400405c0b245052406040c0c001c1c0100b00034691580411b00074030507442202c03100340340314002c5214803140710340301c03d0182415a110038600940d0020440d038400d80a2007035000740c1030341d03115030002c0c0014801150090200d0a030b00c4000c0070040c24170b110802c080104c5600014200300010400f00000441c1980c424010090f4600603000b25411455580c0c10b02c2d00c0c144c015100c08880f001d071342014400c1407035504c0c054082100c03000d00306441c98807030307140c0152507008d514082e0505401140061a0384c8116800035130f40481100c0c0d440051a8106000e03084a200302c0480a0070701001c40c183c98050300540303040c0d070042c0d9142901d0301c1443d1030700f010707180340044c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 532514100 1250 532512850 532512853
    0x5011a031009020d1406010e0f160f0504120309170303060a06050310030b040b06040c11070b0702060d02040b0c01060501050f180a0b0301090c020f030306030c122802030c04091e05 79
    0x51031350000d440100701c0b0301c0e8210040050083c175031420440210f0007000500400180d1035680402090300085102500760390098904080324501c860415240c6204517084148103101021030030082550143c0c0d40026a4054140400a0103144203880d0781c030b01051b50007660110300680240a407601c14805150701c99216450030f001d103556030703d9003c20f201068030103a03403101ea0002041401d08150140294100d018940f58900c90310b0019943d880e00002d00811042d100c00086a00079076807221700384c49480d90140f108540d1940d65000300d51440c0c2c090300000c021942410340010f001c0d800b0f88203a4510f40c0d130400c030a51030061407690244910003c110130583c0481c8a039000304018108502070343c06851040d10000341c401c440075000e85043c1400720780d5890380d0300410801141ea200415290003c600554200e144608046c1c1c485081c100d4103800c8240340000c10000c04135151040d41c00344141c0e40207030191803100704640305000a40700e802c280981105046d1300107400b884600c9008042c0c6900940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 532515350 1250 532514100 532514119
    0x90a12030e0d08090418030e0d030c0b0702010207050f12042601050c0c0f0106050a0e180d050702040b010c0b040b1302090405030304110108010f03081305060c01050405011a03100902 80
    0x3002030340d54060b1840c207a80c4080003291601250a0600c00c903041c1a01407064400142c00d035036401031400c441c6401700ca00591020607070004143c0522440003049030303c00c0c02c8800502d06580000d0003500303d09000d96662240a01d01140400042000c545114140c4103a43c5082d0510350307031050a08407181d5664400e41803110a400b950700a00c01c0311b001d04541384080756140d240b1402289810607605c56108641d00d84101000141d40e030381024401c407100b596409523980c1d26402c1240641d44803200d0300c2c40c580220040080310a034400c00610003c2d02c00c0303508004050000c401100d0407404a0703001415206600082408035035070340c2c4101c1e03101850052040040e00e282c0d000c03c5401e141a20100d81c01c0d4000720a000800408140000000f02d081c0b0305038003250715100f804c0c41c001c06184009011404002002ca00c0c40b840480d50750054040a04516a1000304482e400d00800301110300343d40c03d5290003c5111141c5505260b00ca01480040040000e151501d0b4800000d042800c0201c0c0d207c0d450700c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 532516600 1250 532515350 532515377
    0x20c06091f020c15121b04050307031b06030c08040f1e060917030c0708180604180509010b0604091e11030403020706020109031d010c0213020c070902090a1203 70
    0x20307100400403690141511079110300a00a403282001001144e5401c20f00503c100b2000c40350300c0c56030015850350070b4804048080d0684075135126503000240c25005404002c41888015200010400544403070400c5550391224202d08517101d910203140052840c034046070200c0c4243c1c00400450f4042c4403040848c5c0355241c5000c0c2d0701408100b0440c2d0481d00c07a02100e00388083c046844881c18024520f1900e54901074006a00a104901004000c0e28011900b01c2e49008981c02000c06a94090f0415030f41c1d036111010a19416003c121003506c45040a00041c0f1885040c040c05400d4003018005074141418075840c18050610000402684103404003a960301d6031031800344c00c0e040c0f6001d0200030307581e08142c10000c0c2407400582110301507a05041111000079449000b202015004043d40a20b0040250040f03d540080840c040d500100d250f00018084038603a004054208280e4111540642d54415240c00d0b030142c034440c0f40c0d0010840804110080d038034201c82071001d101e0714190403c20003d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 532517850 1250 532516600 532516639
    0xd082211120f0a0507080115031407320301090b06040207110409030c03020615090f07020a0b040309050117060d0b13060219080604020310140301020c07030b070f050406020c0609 78
    0x940c00b002025404144030a00b4010140a0300014108460091044220301c89010550603040d10000b00000403400f80381103101400d0141001070030203440741180711030400100c0c41c02d80900d00c50880607942c0c1c1c4c8000d0906840c0500c07611100592020301100c2c41d94034141084000c0d0404042502c54180c060100410303961184158003520340b0a441c0c171240c0e5401414000c1ca0a20003c050044a064001030307220b0607542d4842e0f40c0c1d8095a0b081407036450b5600d40740d00300e0030400081001844041030105000c10190400720310750640c0c6082e0b91305509007030b01c981c49960640c1c003030300d001e5000294108a9070210340b41810316540000c0ca501c10000380c00e403554610080360301900d580c040e5030390764042d00c0b440da03603001021941141c000c0b181542542007034111079405070002e215443c0000d001440740700950f1000e4043e6609490780b0001c0d200a02d070340b410b1621070f125007210641d00045094030000200342c0500c060307170150b0380142d0042030042d070080b00303210140d0b10200f00150700412200001e10094403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 532519100 1250 532517850 532517863
    0xf090a03080601050c01061214070e1003060b0a0503060411090a09032c03060406020a1202040b090d11130603020a0b0f0307140d020a1d030c01020a020d0c05040204080d08221112 78
    0x41404a001c1012715038000c02d0030401d1030307000b10500b100c5100502110074051110b44d003c1c1c031b4115070001640d1001a0000d8604507040d8009038260043c0c2080000b4401d042101d407000b080186c418000c6ca58500210344211602e0103c0280410751110810154420342c03003846461194815800ca1070f00c0100b0002858030104680484a6980015403410030a5000c2d5131403c1560000c00150300f86030400d00340c2c40349800751084442c045c0e450f4941c00014800d01c41849006040043c001c2e038849c0b45c00756a944007800c035038001640a43c40011b40004c0b120703880d0045400441d14811110f017035446109040300c100e080902010f022007030501a901703400c055032008001c141c2c0182c64020020100301c81c44402e01802000302e610a03046003035021440c0c1d80101c1c0201070030303234110351030040e0102a2608440304d5a0b2078001a411510224020941c03800000d10304040511a03102c15a940e502d0074000804c0304444c101e02c3d458090070703400f00e070000740e54030f4010310300550300502211009140142e41450501c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 532520350 1250 532519100 532519103
    0xe030a0903110a1a0706150302130221070f0206091605100509060a0503160c152a020309031b0d0b130b0f181c050310090603050102030f090a03080601050c010612 71
    0x218000744060801c100c6d482030b2a0401e01880f005092686950001881c0d0613030901d0003072080750001081c0c2a04108401c1c0130544090002448542e0309100b0001003000d141544000003504c2400d008c203c1c440d800262410101100d03403c00a1864180414890038800044030795061000920050b41d2642d100406485110340640e24640c47c1e20340f5000d1070b020b052801d981d1200b03116001d03140304c020901140e02c10072019a118004242040111028030340c0c03522004450001c80c7c3e00700745881d1012342c00300081c0001001241101e075503681003681c41000c1406026819407054008580d4000a08516222580012003041d50360000300140c46074034000a0884281040d441c0f118104880c458041a101c904178280d080200050401c21100c20b401600c807a03064400e0000100004500704150490b0300050701030801d0a00119641c1c2c176010b800b0750810b0765054405443d05000540041d400a01100c450380c00da554400da9881381c4005640c00e0f03001c50000b42055403980408500e1104032100d512005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 532521600 1250 532520350 532520399
    0x7060c02150f160f020d1107180c0206010b0c150a0609050a05061e0306180703020d1406060f01021f021b0f1005040b040b06190e0a0e030a0903110a 65
    0x707150001c4825a4040640790400070b0000c0c03503403c0c40103d03500081405221000342007403007ca141982c0490f242034903540c00215800507102c9002c0c2408000c2c0c11082c04080d85030201e032020390b2188105881405241a40701465000013400f142c440c14100b2840c1d0050518900014826201d08401e0261042104e1460b0959101d1051001609203032014020303070080008410040321400000a8640c000a03000400c081608104405008001d0100000546d401040c0c503403c0e41c00c602c1c1c450107414500c030560070710340120000038122703040c0b5000010f522132059000d00080070b600d0403e03429030b03000c4d45079601d211507090041d1001c1d400104845038040c0c100e54010121076074003a480626201c40d075a00221590b040c0b03018480003450005400741c2242d4011441d48141d56048081180c90141c03949080da80300500000294113120003880900030a01e40000703100354120401d60329a81d1140ca600940020640f00042020a40003c40c0c00240000100300c008865a500302820b15014141c0c4400c22030b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 532522850 1250 532521600 532521631
    0x20f04080d0908120d1d150a0b0a0303050d200d0e16050904080a0e041d0c040504170f0913051f030314031509010315060803090607060c0215 62
    0x409400500702001441c0c040e00800801e05808501c0740540038103940b51a0070740c2c44030000b041080816418046e014500030403a140c04070029a05100c1a1094400e00c420610b468005003140c2044124003054a170141c8900d450b050410700180028908100d04016551140c09401c070448000001004410818440485c20002801082d4102141500a07680c00700c80300b8010001504d03040700c2d2552158200c0395480d1680e44101c816101849490740507640036140140c6400d2190300300e0b00406012500c50104e500019a1505000480e8130546001d03024004401c040031070802a003000740300c46610070311050b050440c0e12010800040c41401d260344030580301c00400001081c0202488810201a81208480c030700d1614040c01c620317000280780f031503004008001880e100f15070106074a80c1d0b42c00b03000b1903059031392408e05900f101090800804603506020000a0b40c02000060359041c1100510191424071142d0703600d40203015059029042d0700581403003400310700c40c180341c0b284920380c490700c0c1640 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 532524100 1250 532522850 532522873
    0x50a0c060306170c031207021311040905010b031e06120105010815130c03080d090f051b0d0c0e09070806070320030103080304020d022103070b0603010c02150a020f0408 74
    0x10791030710b80840380c000d03520040d03c400c0141e90000c0d83d4103401262241b0706590b4a101d001240c03405100340300319a2001d0400c1200184040180010800c84003a00307001c1150741d80301d805861181c48240c980300c3c040d08885864107600b00c4804045034004900801096040102c1d18400b800d40300268000200c903040403000a032291410007009910031000c1e080c0040e41c40c09981e4841c032030b99460101505062010641c101011802c2e44944003150704800c454049032600c0c68450b80d19841121101c28500d148000b4441c00d003800c10341ca8054980c00304c60412114204881070300d000c0c0005081c00710f5071040e0780c000a84d60740c060083c58056a580d41e00441e031001104020303107a42900113900101040c0820040010610301400d41c3c1d00030307a040b6501c0040640340d00003d10014007142d1180301018542280c810340290000062056070b121f00d80c03864103581d849003010300302c0f600030303400d0005078001c10400d005c90f00d40c03038401c40c1d800500c04a0043c20715003504000c4560350000d80140d05240e120b40312516 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 532525350 1250 532524100 532524119
    0xc030f09141b01050d0e010b041406040b041a040b03010b0405070801060e01080709120231050108060903030402090c0c0d0906110105160c05010209100801050a08010506011b050a0c060306 82
    0x149407140301101e40c00315054040000c00724811032480100d4695180490340b4211400c1d00f0400102238000c106000d8405c0342d012155000c10180c8900d031048c1e242c154507020a04042c020241280c58808012180041240602004c1d0000b001c585034155a070314413621290b0390f98419a40207440c5a0380d096000d60508101901d0184131300c01d90b5040c00554401c2003e0254809007480517100a40e281100c0381c0300910200344003000880c002107005810000803007040c11540c04030050303441481018012640d8540e4000e231107001c180c41c0c68121750801c000290140c1401c070b2182d60070015583c240c03490001401c4580c0d00b00201c1c22000c10000701c1480c010007046a003c01300035198a24031008100e581481005078002c6520f1102c0702042c4811200380006100c030a605880406a01400001080d001e542005044038000d0003000e01c9a0b00c041000f00d94031105100d2144a45010b0310307050710714100807043c000d40305070200c0d0444d21803240328450340004020911400080020f0b4801140d01400c000303051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 532526600 1250 532525350 532525363
    0xf0c020303070b1302120c0a030201110f060c0a120908090409020105220323061605040b0f041a120105060904090602180a06110a12030e030403050f0c0d02090a0c030f0914 75
    0x9401c07d5010089000c50b42d07444a20840440c1e0b82400c101c58038221460380242069a900b4841c0c260303000703041c10864407040c0c84000b002d6081c1a99a6800c203441920985011190100c5019120b00418401c480e40e40c10650301044819005051650500a030340c031085802580c80c0c14490000080340c50108104414041d00395001c054003000000285100c01c45a43d45080085c1807000c06d00d90001036111403400364007103038044c0040e41c0d209941d51035440c0d5400380540c024810701d0b09080c4080814030201d0002c0090f11040c018010344030203641d00c0c01c0200881c070342200911a40c0075036180740850020b5070714030062101029543d01712030302e070389800100b2050040c6540300700c05118081080c00307030540c004201101e140f80c3c045d0090650f0090168201c0050a10900109403484000341c08814041c1c0012000d100c001c4407821610035262600c10300000c980d11920003500803440c030000c16480d0200f5041200c00004510740083c0160501d020130042c0c52207c2030603540c0740c00003243c0050a00c000d0000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 532527850 1250 532526600 532526629
    0x1a190306050a150306061706010f0509040f06050a060f120e071212030e0309031914070605121e06010f0c020301181a0112030818120406020d0f0f0c020303070b1302 72
    0x301f8041c2d04a000c21218104000300210704001c0144070b08222103000364199046400e024000b0801c01d0240294900180110b000d680d22944211800041a41c07044a42d5501040d1550365803040045040d080709c060503d003000d030400360003488404181644c0c00d01ea0444028011480c0052480d80c0c07860150403500d501134204200e40040200ca082074900017a085002c46408000348940c6c4c6882c10005200c3c211003078458224051200d00040c21079001001d0004204d00454948444c0c58440b140001d8078440380c14090880c64080000310703158000c644061540581d420080c03104a62980024212094031034120751843e8280512000c0c00b14580554280248001a860682d4182034903042540203181c0020b00f0004081d0018000d0180d500c02c1a0420310100e007242c00e0303186200203a000c40e40281c002c40005100d8540c950320b00901c18014086640115281c10580c03003440403040791346a400c2d0809981602c42000f040c030008080c074040c584196020210990340403894410046401e034031840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 532529100 1250 532527850 532527857
    0x1608090120070605130509150117040b130609062405010201020304200316150f17061002011806060305061f0e1b0c010906061a190306050a15030606 65
    0x2051950801c00078400b01a0f4030079040c5141c42e48400700748022240d185802040d00038500030705020320070b040540d04140a8809886031849203101812104403980c088401800f100e2061001c2400c6468171f60165940e140964800f280d10001030b00c45005403400800c0d421005e0b2414489000711941c01c0700d441c405070200344000d5141d0708242d1110b024a540b128003501005c0303611407640c4184c0d981000b410b6031040d01e6010322a51542e44544034040381c09942c0c0c03203e0108291403101c82d00d084c80f400652030319281c0101e211b8081d481c0c030014440980c0d1010b0b032580543d0f5a9010039980310151200d01e82134140700d0140851914214a001e42c02c0c003c0c040c160b0b003d02c0401c10461b605c180d10b0320305048140d0311819001e400310342c1c60803e82ea50f400a000c1c140092500300141c580909001908400e8405005000610060b603880440303d080c043c22907450034223000d06011140d020b00740c1d04001c1e0a09542d500e00840d030680c0b10f100003040640750364081150f40b80007550113a0500e4041c003540c00200b48508 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 532530350 1250 532529100 532529147
    0x2030a0f0209130b0114040605100302090109170312060105390105070503070f0e0402030c0309150c2d04080715080c07122d0813050a1716080901 64
    0x281e03213050614040c082c4c04d4442c2204200780345503454990000004010050107101c01c494408405802513200c3c0440d203001030203101010443c0340c11942d83c1000426004025458109031900201811b00f0140c02d090411208100c04827440142d00031601c11180c2d001e80d100d01e11001e07503021a80c071114035250b44d06241d041030300704041c0607085000d580d03101e441c508044d803504645903401c0b40c3d0000c3c51142c05078002e1021040c0181d11422340c01852144c40c07000110f425000c00c000341a80180300440340c1c0f0980702e004220240ca084403001102c01b442d085544000d0204c01f401a50000c1c641050300820426448030310200150f80790281910a24511410003540074242940b00740824891004e000d0010320054001148003841210880e01c1d583c160004c02d80860303180e00509400c6606070104100242928010401c00e03c01ca83c4004c0056a22800038a2282c500750381c0c0342035000aa410f540e181080600011240340c0c150041d00c00264410224141e07600c00402c0090450140c001c0100004031016 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 532531600 1250 532530350 532530353
    0x30609030408150f07050c03070b0a050105040b0411090114040f0b071208010b0a110f060c0903070b090a0509040f060509160b0316032004030605100b1e030c0702030a0f020913 77
    0x8125154004886141c0b00346c7e83c000581c00381c0e01e1442100401440348010404014120303206034002e078141c801c100ca06011500881c0d082005442c010503100103201300c10000c8070b02c203601420084072404080c444d002d0a056403801c00203550001580681c0c40404d00082e58401c00c1540317185140b903080c1500b400c28881d418900318080a0082140010a00c2908081c00c1181c2d06c0030089842d40306049011248949000d6002955a800040c0c0c040d01038880c5460108815083c42c040c1c03030380c0240142c07601068618240410070003090103030081d40d00d80703848401040892711074002d4501c50444c0700d008111303105402180c5284440554031500c0490b03810b2052140e0920150011001041140385c046860710100d40c11b84003164036088021950400060000100030554220600c200803400ca2340150994801128005200702d4120800582e1000084c080001180000d9604110542c05590500c0d03400d40c040383c908522000706a560000010b01001140350800c0420f5100f141ea001591448965 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 532532850 1250 532531600 532531621
    0x90604020603070306030f0309180608211603090f0e06100f09120b01031101030903090b0726070b0105040b0d0201031e020a05040602010b0414010302060d0b03060903040815 76
    0x1800091281000201040a0b18801d0b0805006503420400d801030084003850007a1900d1464070030001c1c449146102000020064440c481c2111000d101802e0507009480d411301030a01128200d403180c0d1307030a0041250850360104a9036101d84a501d0f40e00095091041144d10301c03103240d0180f10400c1801c001c12580380c0300c000800c0a0152982482c00341400031520035521000c0c1034002441240100c41100c2c02c0c8042d203413145048034000c044503a10b0b00034040044041d2504050040c0104401c140c0c2006244100c000501d8203034000c401100a0594090700481d0341c01c8414410100c030a0086a114144202d084c2407038010301e0110f5042000d0003076417010034210201208040c0c107040c0c7e5030040c20310b28820110811014000c854007190717600d1510700081d1060304603018003070040d860704540c2d8005050a214400360441c081110040903032031682080035550200c00000d1415071114041c0d8842d8a04110150140101c0c1d805151103030b00300203100d8034103003030f101c02e02c107000000d0700c24070600c07015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 532534100 1250 532532850 532532863
    0xa26010e032a060112030c0507320307061b0501060e0106030902040b010914040b0112020d050711060402180901021308031822020c0a0b04061d061506090406091a01031409 75
    0x5060518501c403150700d00b00705003444082e501440380000e04901c0b60651080c1d4642510050120041044e01908007000382f5980d40c106000e90004200c0366513244081d9090320002c0084144138000109420b6210103424546240a0380440080b0f42c90311030301d50440c9090b000b2114106028688003110500d0070001e02155003500310258019035507030355000141d92041c512902c0110b010307041507546a880c42c0d244401003000f203900e080000c0421460740d4140101003102c0b03000e0b54004044040b09418407180c03000080010744821690b40d400c100103e241a5480ca901d4000c2a4410207503884100c400320b400103032540c200340f69100301c0044803a0808040d20882940110702d4003040141c0740c1d2001881180781c0004036801030249164a000c01041091a0308050840c00000c40d101928000188038a82e642b28140c4000f259440034580c8180c05043c6140a818000c0c0c0c01031000c9006541c0d10700e40700488003241c00010140c0001058000b555806006144ec0080f21103500c08203482e10264042c2c9802 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 532535350 1250 532534100 532534103
    0x15090a091104050306040f0512040b07030513080f0d0e041503110d0807061a0f0d110f101205090f0d0815090a1a0a26010e032a060112 59
    0x7030390381c01e00c0340030700c8441c1d810b4501901d0040c04545160803d82060851020300c0502202c3c90b100d03110078072885040b0703401a40c0884103104c541c1410720745285e03000d0711103412070300350707081081030803140040c5108041040329904941d02000c0e22001003100c0c0d0007006007800500650199082029403d1074bd03040790004011240c2244112660340300400008800d109060006032240d24082a0102407089542c0030f46400110405c60f540800c034468180315a2070403101507a58851613440c0040c0c0455801e017120480440014130708078107441d101d03000440b071402d0815603500113010300350074206900061143d03036041038840d8020300300348040f415900e641d443c0340302d00c500800425101007061140d400c000d0300c1810740010b0000003645800c1910740018003030305a0714000d07003140c107034014542c0c02d0507560482074650303070500b07408a00c881c414607010030303c0b0340c800d00c004665803142c003041054400d1000d019501c4504d10017481440e5104180f402c1d04c00035070094080b03500010010031805121803208035406 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 532536600 1250 532535350 532535369
    0x2040219050d290d170f0a0201050105030a020112020307031b0905010908211308030418050604050103080901030c0e09010e01050a06030c0504090c2106180204140f060705010e070515090a 82
    0x10907003443e00f40030b0458440c01c500217000c2e020504594034032a11001c0e10b80042e8a44c001c20040c0c3c0d845041503600c0101c00c00281c04036103000c51003440d01410380c0042d0b60145c1c00d800d0100d0f240068180c0c0890036910030492100062100800340040c0d0f030321921603002040000004e01062074402c070b114902d0340040040580c44c600c000303840948186e41c3c190000080026109407901d03165583c0d44e00daa180218107070480740518020011702c1e02c0c84c2601ca4035040e00c1d0071040075418020304400540c01400a25107910034440850440c10315030b510b01917524045d0504030300d00142d41d40341109200750340100780c200c901810300b4907000c42c08665201c0c0a0760300311511101c02040325a04034000f03a0360949100348070300c81d907040070800d441c02038a160800c808450001e480002c142802d00702d80700c2280501e0249142030414031004640d540f41c002c590560401e0010002d0745041803655400b800c40c1d0b40c1c00c1d0b45040a40012908001903d04070800703841c40031100120501e0b0000c000005083c80c821030041c3c0c00760 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 532537850 1250 532536600 532536619
    0x1b05040b043b0a1a010503011503110d0b04060c0305090d08132103060e01050609030a15060b1206030c010306060e0d0c21022103040303030902040219050d29 69
    0xa9240d072110507502030074007400f6109406081d0401c40800c41d10480b05204080300d400000805003014440c07a4800c1500c40700c0b00e08880e08580d02c0301d60440c0c0c564860359103e5921060400803480403c1b0b00d900451160700001050b07510791502405a43e8000e1900e815030f0468041d0040d0b45030006600e6501c02c4400740c00268008103841d0540135034604440040100c003802041442d0f01e80c0542c0710700b09030f4019001240050f07a8603c1004070910907600225050740003e05400005400e640e510401c0703105515001c10000c3c1c0359088441c3c240c0201c5c03491102000c1120600c8001d003030a00808410304000c0c89c0a00c421410090041c1c018010034030740b41e000d0921a0020f9040c882c2c0144144083c04520b0703040b021100310032110a201c0801803100b41c1c800c8004822442d19110f200300e9003440200010017841c1406d1a5850a50061101c140c00f0390f080380e020800032400c055881100240c025498858589410b101c103254000c035108089481009003a4640c09810b07542540e40b103100040c811070390241c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 532539100 1250 532537850 532537931
    0x2060105211504050c0108090c0a030b060a0b2b060f14041401090b010e0613060507080403080f04031e051c05040509070509030607021f181b05040b04 66
    0xe0300c221002d0003100304903803405000401c44049058044810240e03141c142075280c0510751500c80b441c2e50010f07680030800040c04c10016924000c2c095115074020019540140d4800c4c103801c09500900e0031720303d411580960f05150059943c5201244e01058a007003080c1800c00000803a804890300800988440d440700c134500669440e04104606201581502482e5070344840c8030b80541140c3e283d803030110344012a048990306011003603d0b452030400c5c0c030540f00a45040400d42c0c00e03070300aa80903942c4550410010002c0741c0d401e0001c01d40381780703a052125512499401d0400008030700c011000b65401c860080b00011540009038034841d01e050f8015a803032080d2807001500ca070704c12540150340102d4598100420103030480060400c10340180e00780e64071590703500c00c01c0b03071604d0020348a25200e004c0544a011421810760004205a000d0642d031592003c0c20f8881c82250400c1c1c00a0603034648603440103114508241c0118101d4101c10340d410301030441d2603d681c00c5003000741840c404c40b00d105402c0508 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 532540350 1250 532539100 532539103
    0x280f0b041d0112080c030d0f0f06061107030b04020a0e07050306010816020a06020a03060801060e04060c02030322030507061803020d0e03060a05040c0e010305030901030c2d031b021b010206010521 86
    0x40d6586545c0808008c0c0c1000c0040990150400e641e84400c0507180c5503000840c64010348001c120044540003801c1928103540d118a02040c0241c420ba030040791111000c168100300d91844d5010304126107802e601d1303181880004103a03000c003e01e01355422100c81d02c40c40540c0d80009070440480c0d404440580c448040e00b20481c000c0030a540142410341c00c004000400040241c2942e0003540961018400e18100e00000d980da4801944c40403c40e40e0389404030310160600d00c040124140c800d10380350f4034010726602c901041c0e554807404e00141301003811400c401c0680411101e01d6841080c2804600c0315981000a9140c0c02c0040c48402c9640c0c81f81c00040820402031404030103020b540d25498602d50b12410b08960743d805c0300d18018042490810310b580c0311402010700d064001405100760004010050002003e04450024602032580724200320920800c001e039171480d502403690003443c850301d0040c2420b0502c04981d0300d032419500110014020f54030b541c016082d2400981102c10121501118581e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 532541600 1250 532540350 532540357
    0x406020a141c0e040f0603020a030303050613020a1d030706020706030e160f06111b0f0f100f122a0c0804030308090c0906280f0b041d0112080c03 64
    0x840c0d40c991035460300607401d03401420300c1c42c8403e01542c003002150b1842011800700d4080c5d00000c1c1d40680f0080040001a1082e0001940000058081e0788010b52544421041c0e80184a244d00840c0c261080240005030080f210024604120014482c2c58686000691070300743d10b0041e44101900d03107649100203003042000c1d140302840c1d05210b001d66940c1f00d01340c52185c82240500d40c0041c246541c2e02142910001d0308042203d4107014441e18011404100f2108950340300c00c1a0b04001918052036032030303440b06251056880c0c00d0715030410b9034000303010080117588003413005403c203850304001800c10600043d811441280d079101e803107400c01da4090107403907a1042c0c480003000c02c0000600030080503031004860b4003801044d0304484c07102142c5c40420130581d10898500e0b810604110489d030702005a0b0f01001c40c09411070200c010300e1f507160518041c45ea642500030000784e000004042000403c1007100040303040350300784119a154104500c0c2008546110300c0a0321a10020510982c840e40074000c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 532542850 1250 532541600 532541623
    0x114030c0a0603021b0307030905100c12030f0e01050405062e06020d0f02150c0318030d05040209091b06030415150614040b090d050f1906050c0406020a14 68
    0xaa40c4010b0362904014069844862070850300c1c212900e08120075803000080e509490741c5a200d282640e41003a09100c0e940c0d0070750354640700b003021190742c0034045420b07004c03c07000c125129500420002c0c41c42030071800344c07100000c848000b40c0c541010040400c1c000300d5519004502d0125800814024018600c00d5104a002444803c1d680c000d00194880d0006214914403800361a600048045100181c0c0c64882c041c60200710750003003400090721a880d03070004540c004800301910400c0c1802240203803440d08030980d0b42e0780c0e25944038103100651412080d0580e115206030000c00c1c041c1041c1604c18140b0084891039070160902001140400181d410320040b40c448094007006280b400070b4035220050180e10504d00420b01c843e4111003000d1004080f10152907000291038a0654000c1c280885515004000e03070392801004c501c50640c4000f800081202041500000f0030f00c090380c2070400c221500a0600c5095203400c101c204030321600891600030301a0401021b036031506040e89202d041101c0000b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 532544100 1250 532542850 532542859
    0x30605060f100c02150f0a0c050f0a0318140307030b060a120f06050708060105250206130f05010c030813031107060c0b160e130f1b080703140114030c 66
    0x740c82d8507050307101985201c0ca41c0201d861719800d40d4001e50104481c0709007090040c00020030845140924082d000340401281300c0c2c801c9921407044480940e0a001d40304c14110005042d1980a182d68031010450700e000d080311840b000c07041c000e20400241e84040b030344001040c18411b1030000d812965555940c10040c060540500340c40401841e06141800c1c0101c001c45000340303800003150040e8411169180325000c1038580524108000a0182c909e03158058003000c004401b04c8400c005031640750207056000b14013648400041d0518410810360401c3e900f00a041140c02600803011030f038001c55254001248411100c0c5500c010300701200c400e500350042d000e00d4401d2950005520b51f00001c00ca20090003003100313004a407141848800380f05942c8820500080e4181442d090b107103080312620902ca4201ea5000030074040003844841502e11080c17a0f2011081c42c0074000714501d822190381c50b841840c502d41002070044c1000d22180e1010180600300d00e8030040949610103480411110544400052 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 532545350 1250 532544100 532544119
    0x20403062304051f09060e070f08010507050405010c020d050a0b06040612052e0501080703031b032a1a16051303110604030f0b010509011e030605060f 66
    0xc1640c041d00c1c0081c0c006078a000d85030301d6a03040e2145035001034041c1d54048041e000700301d80c04100700342c1d09004405100d07103e55282c4509000560601c90708111050490151000c40e01c3d1451286070301002e07600500c0c0302e904001c2080845544101254152102401c0103001140c4600100755030040500c0010241e200e459002428850a86481e6200381c2d000c440a106207070304c80c440401007180f0722000400c1940010700d84280346444054007110070307142804070300d0b002811708409801c1d82c0742079001c081c5680010301c060060640c4035840205401007038401180001d005d070b0b00284401026a82e0070085200300d07450301c203550384400b0b494501e42d800070007003505e204070315002c1c4280c1201510740e00000440c0c0204280254082c01c1545c052080254940849a02d140c84100340100c4180c000e5070300950800000c0006541e250075280c000740544044044c96040009110030000e042c2c1119540140c140c0304d41c030011002110b0030050340da2217900031039a625580041040700144a61090740500a40e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 532546600 1250 532545350 532545353
    0x3050706050a06050f03150c0a030221010f06080c0a0e01122409060b180a0b030c0d0b040e0a1b030803011707050114041e09020327010b0102071e0504020403 69
    0x19000f103815200704451103890340140d8020180c4c0d820310122460707501c003c0e200000e182d00300c01c1006043c01015500300585803140382800b0380c0103c42030006403072000f0b4040005204d008002d0082c0400b0f85110308111507242400b012081007402450962030400c00002001243d90b4407800c0e0054010440400c00e00040121409049100350b00c0104a45520680c3d08005406040c50040c141194242a403003840c00c2e06844042400d40071075003d1a800c0303030400100140750301030000110310951003405080c1c0c80c3c242c2d220440098031030944005201c0d81c10400a82c40000001c50014101c0d54060500e50966400c117004115102c000d074406043d012000c0000213403203030203443d1000365803030202c20758917070f0b503141c00065807180c080c44141186040e00780404c0c0142441c0c103036600c03010890004c0303c0c940d0075620301c2e050341aa80100e420340500c1c0c440400e540d00003041150402418000721000b400182071041c0002d5460450b446140c0c23084d085c42c0310b0b020014040a4620020b41409041503607070300d0701d9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 532547850 1250 532546600 532546621
    0x80103141002040f03021e0105041a09031f0f060812130b0d150803040b0f030901142a04030f1e050a121209050d030f140421080411010c0305070605 65
    0x1ca00c0f06031f01510f01011104a1214035030154292910145c4034503081504000364550410708181c01c0101044041100300f240341e40030081d045034006034604400105c05e0034235001c0e080e00e401d030112440943c14030005200d46203011402c241150420282d0030345442c0c02e07002c00020b021255100302030884000903038903000502c1d50800e6031514220001e10302c019642d1403250790782c2e119620a80c3d6202a05002c1c140c8042000740c021600241d04100214440c000440310030821076054030b460f151702018122600500708028244008042d03258549401c00707140d5100c10112095015005044012844d0302c4a0861b10b28501003040c66040021200100894500902840d0148071294003051681405040300c0006004541455034480c0180c100402d088c075090f4042c00d40415403c070910388078015096195400d4035040e1103903002e24000f40c030702c1600400d2a501c206100200608100c2107808100c0440c81595105841da0340038a0481000d851074141102c20b8005c03000b0007000d4904010610214464 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 532549100 1250 532547850 532547879
    0x20f1c0b0a06061b0f020f04051e060a0e06060a20030c060a020a050909070909090602030117030c190c05040f020d0b10020a0602031314060f06040c08010314100204 72
    0x1401c5008114a030707103402c070950710700c0042046802100c106a9400b40000e0740b6480d0013540f00e1000e0130115040c0800e000150603500216502c00444002c10f981081c009521184250454400c1c0c5e504003000382400403041810400030200c0d4051940054a413410230300c41c00469021245040c40003101d4201000919100c2d8001d05140950744142d8020071042070041c0700710344601a0079102e585c6441c18000a0101d8410010900d0091081000000460300d00502a00c90364070311840005940f50f05080710301c0620004111115003903130080c4060103104000050325505103040c0805003010b0b408a15003001c85a000d50410358010b41030029030391201c07010384c010741a2290940742c1402030107004010310180400c10074500c1c006900c41d400d00000300e200303a4021a08401c400c0424007001483e0f807206240200d000c0030800d0b117688001d08004070405140c070025002002182d060002d0b41a0060080078001d0600020b40001441c1003012003901c8208940d185100380a6030a6450b02c0c1c0d00e035040038082c0d0b03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 532550350 1250 532549100 532549111
    0x4053112020a060509150712200702091303080c07080f0a05040e06010f0207150201060302100507020a0b03010b18011101060311120718050c0c06090601030309140a03020f1c0b 77
    0x1400e04011503001800400c43c05880c0140d110301b10015603600000300c03814016105000100d40c0e0300d0140903900981d040d13103103003e11003032041e013a5100340c103206010029200500c110701101240c040c0c0400240e1120f400b940182c1c0e0340050030348030f00c0c107414865494410801e495482d82c40024a1400d81034000b8040d20840e00540024040c41c0d13148001910840001010303440107030010b1509200c041c0c03c0c150100400c10f440c1c0f0001079805d480f503012490b1001c02c20212000305201140390002c41c94240c408c00d026014150b601402d40d40740400078001c1c0d00403160a1404450b010010780c1c8164425428080d02e40f04004c02406140e90340c0c1006400701084080d032601911442486040c011000110002141c168484080410b0040444030b4014080900703440e0380d13200704000c82501d40d9005c02c0300c1c9001d04900c41c05001694036629018102c41e00980c020320320764060a0907002e031030b91000c40110441e034066a2134200e03130080c000001d40100743d0500c0c07081524040c1f0381d40404d00c801001d03d144100e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 532551600 1250 532550350 532550363
    0xc03030f1e160b07170a0e12030c0316110d0c060f050a0b031c2a080408030405091e0402010e040e01020414090a0207020901180906050a0b0f04053112020a 68
    0x80e103c808017103e400f05103c900401440d844004600c2054140c0c0c80350300a0721147e42034800e800c50328000304031503038401c0d140d513410f414000c4140105482e00c0c50540c28400c505042200801e540080241d88a480307140c0800c040c005409690401d000c05600071000310141c0e40000c014038502003e0b080000c0c43c000d030005000f8820803003410b41c0700703170180b16030b03802d14070319840f054864400d40305c1c03040300007001d0307003100e480239003480f021400141c10000980007800c0050059911142801d0500c0081c1800401c0b11404204071907443e01194116500303107410540a103426050210304001080107000315802020582d0320004000903244420441c401a4000403540000c00e5143c00526506074000d485029500101c10001045560b4590301d985030364070341c04000400c0074034198a0f61800c980c0e04803004c1346400d40356184001c4501d4403003050750444104840800c102d0030310000c140d0360502c01c18240950b0300c400410f10703038801c8401c9910300c100d035a01c2011241310328129400203466a0048504a400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 532552850 1250 532551600 532551623
    0x17030403020f0d2a080f0a0c051612060e011d0f011406030c0d03140403030e030c0a0b0f09222a050d090305091504080d020c03030f1e16 60
    0x443c03103030025480022644034001d4030134140d09034141c1070101584007144c907910208400407a07465141d0150407c0c00c1180c80b01c054500d03690502a0920002101c2e10401c5603007030300240100b500c9500c8500d00660021030008480302d41c001a2801414228034141500e101000300820340078000910f1003201c00c6c18002132200000040c000302c030000040c0c0e035051345504811610005030078000701d1101c1082c040d1410200d1761000c3c01c0400d000743c1c0160015000141c2a102c2d107101070500700309200085c50240e80d5403825514026224000d4050300b9080860100c0019460056903602e0391a0b041850514921001030301184a03000d00414640304188a6078002001360401c1d180754100ba0f0500701c4454817010314003001c0310200001864801c000320240402484080c060742c0f80c0b2000d4000340e5860b03031041580c950910604520380400003107071004540c40721404140b191000710a6070b00c2035908100301925003d10041c402c910404402005041044c0031801700c00a40d4180070340b240c40c0b8058400c0c00310 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 532553956 1106 532552850 532552873
    0x100e0a0f0c030606082a010c0c1415040609050f0a03050f01051803040602070e04020a080d050315090906063a02030f0607020a0b0417030403020f 64
    0x60070508168180300b0460705104440c00350621304018100035070704400501607844c8000b160340b02c010740e0ba0341c0a44a42d010b035004407442a4480300c4170a00e1358443d4200c21124116001a42c842d80700203107080c010380149000c46060b91155a585500b4500300400c6c040441401d505e0b294201d5503808001010800074003590361031030b803101c0001c0740a00300f800f8091181001d000007103401d44c1080104011a580000e4000115111803664403069943c60001658140d01d9a209400c1c3c0d004d10540b400e4125882001148521200300071441c1c440007000134401c141804641406596204a0104032245081445181100d03200840a0b4105007041640d1000490029031720f03a62014801e056000c524050007258002e030900d20080c40c440c580328600030742d254170000000e4401c0f00c0c1100418144a1001c041d034004040000721140d507402d083c41d00070742d141d0350501d10390f107540a0f00c000e039071 = true := by decide +kernel

theorem cover : BRFrame.Cov 532374100 532553956 := by
  have h0 := BRFrame.cov_init 532374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 532374100 ≤ n) (h2 : n < 532553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
