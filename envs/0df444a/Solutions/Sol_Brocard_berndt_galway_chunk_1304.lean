-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1304
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:16:38.2267+00:00
-- url     : https://prove2.me/submissions/f5192e16-4ad8-4155-9e8d-c457b3e1b6d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 234352517 ≤ n < 234532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 234353767 1250 234352517 234352519
    0xa031401260a0503040e0a05010503010209090a0f09050708030c01050106020d120b0607060e101803170c1b030309060a0204050f0103050a0608070f05090a05010312121d1c051c1a 78
    0x1d417641da54800d210038100003030390070124803824070001103290b090520956110707000040200170a520b5280c0c000005001c80c40c08450b185407500342e0140881e80030403446004158000082d41d8130001a60314908503041a0480030441d04581040c02216034015034480c2c0701800020005020400c0c030300050303110b10942c0001003e881c10000500b44800d0042088031640c2e0a484060203226015001d00021841b00d600090206c2c1d481d41602e03501080328446641d008034800c0480b0b2600c00c1c182445040d0042c0744440560550001082250f404414003901d0707005060380c50203605090500c00080c60310300304210b0341e03410580d03500002850b203641034001c14000c0c07111405507020f8a1b19020701d030121500714000d040c000d19901c0d0100780c88243d540b140c14101e94100c550380c010b266068108990f984548101c41191544400c90303219800c40c3d8881c0e1110501d1400001e24150700a20a42c5401388040954013040c02030501010385140088900503200b5000c56000003003002c8002c01ca04071107450705800e5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 234355017 1250 234353767 234353773
    0x8040602131a0a0305150117101a041e0e150406090e010e01150f031e05160302010f0305041e0501150902121b0405010c061407050a031401260a05 64
    0x302e00c02d04800390050240c3c100d1075805211996540b007640702001c50b8404041d0003d84407840d5800100501d004440c2c0043c01c1210010a407980c60981d0004148410380f003450110001504006410558103040c20f604c0c85403440010051600801c0041140000c0140f82501850340c00ca40e0b0503500c079407149c0c0140c0100c81040000901c0c0c1d0440318000d00984012808a41c41c0081c03441c114443c000c403003030495000144140d0ba131030440e071b00e55500f12104020400421691081e4000165041c08095910741f400150340e8000e61541c0001013035060110812403e040c40e100c02d01c404600b207099841c0014102d07031a079030629040d900d03185004159144800c074565600040105100c2116001461035001c1d20305c0b49070a80d110b0807030340700c0c2540303424031804c201074030801c401c01055001c3d520010327009009032030019442d0000d81c10202440c00c1140c880001a000182d001c0c1c20f82d03054840e07002c01a004088010785503043c81c1044401c22101c00100c00c0c0308010180840d000304c820020425155809003e07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 234356267 1250 234355017 234355049
    0x30c12030d060b0301030f1209032a14091f0b07050102030a0b270705040308070c060219170c1606080402041a1c0203030f18120c010804060213 63
    0x220030303240c0c0c0240c8009440142000c100040001c660820b50303059a411070100441c9032155603c00d819080050b03600790074001c8400e00000400d1800001307141d0362410005a41161032800342c00100e00f26a0f41042a4040c104800050541c840003401540000707a0255811038600d640700c000031a29095020320058440002c0c50002c216040d0041d41c0561482102030044c10750325010051200c82d0021701040d1000c050b4181040820580780c02e035042513003824118505900d0b92114156075103c0c0d07a05407401c0300740d40410031403140d0400411041c100000714640c034981a41d91403103410914620300c08100680032402c44100141031060708481845125455402941d4410183c0120403c6405174400c07490100b120501d44401350303d501e0a010018041c0300004000c03440340040c03084141c1c2c241d805100c14800d103180200804010910110426030417400424407604100521042c42c003400c81c0c0d9007000c2210091a6040040c10350030503480300e400341c0c445520885611820a40d0790014100c2050001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 234357517 1250 234356267 234356299
    0xb060604080d020a05150103050607030b010e040e010509101104051201020903010221060406032a090e0a0b0603070305030f030c0702090c031807060f20070603020c0d0306060203090103050402030c 86
    0xd222058144105c040c0c5203201d42d0030761800c806010912000d8030301d4104a0000da4524407c1d03210400268050605103d900e00d6440403408981001c60b80c020707186c4d0342d00705004484804000c1480361090414083c41000d1324003812142e04c2c01217200f018000d2038040182030241da02034041c3c0d06400005402103480d406002e41c0240c4115000c01c0d00d50340404110081030352070619000304000c0d240c12810410603071b5008204154100c0c1030090902121403020004603424846014903841e00740c80c60001c10032007120342007000d0702c441c2c094a0548254070903942040096004800d403244100c100040549030f0b940c0041040545c412010000c1d8090782120030003102001010145000356041c40381a807a145402583c16a18401402040701240c0f420b1700f801c2c0228800c5070031808956400090f146110304228503035190010790381019011a0f004281c00c1d0f90701c0d0301000010751510fa00c0c6814090740346004c5002e5180c2c800c0040075410140c46d4030000e402c2d900c0401240043c0c1c5000341451a071100284 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 234358767 1250 234357517 234357523
    0x12020d020d0506130b1f110706020319020316030807090902070c18020c0a1b080714030d0f05121302030a0b060a090b06030610020c060d020901090f120b060604080d02 73
    0x845880c0b1582800c1c4080d00c07480304c1441a10410f40c0040c0c21001c141c541840302a0880c100307150034a04014a07800308034218602804204010250748d00203645540e00040e040b00700b85800e6005504651051081500c11070110b20b4190b213481d0903040c41405a1681c0d41e0031545080280c0041003c14000180c00c020040d03080d144100b00c803641849a65420000b0000d88140d216481c09405141e1000d4100c1010481c08000307400210841122600b4a503620401c0c241003140a50100e1000810032440070358a080a02903400124220319000400558100c0d000e0124003c040c112004441e030840000c41401105220300401034008044403804001450a6140040c080714250b00500d06e0840000c0c00318141e00491040f00d000920712411981ca0009115030b050061000c003007180b140d2802c4244c15100d840080c2a01a044500540c1c3c900d1581c00240070080c49a0114060304420003007040150100425a410b0f60b50082c0e20200d0b40e2500d1000890a001e9500154214003c0e0821003d82c55000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 234360017 1250 234358767 234358771
    0xa030207060905040504150507021006061106060103090c15020106120b1009020301050a141c08120c1333030e100b300304120510061512020d020d05 65
    0xc2e90310446041e46800601c425110140e030001c02039122200258030003140c03a04444c3d4072443c40d1044810300380c4800226801d80d500e551041011072003038074142e0b4000c002032200c540d00c10b8007800c090202844941c0e6050002c040c43c4a10595a1203c044000466101703400000c018004240e018402a4950400607410b03501580c1c00c21202d001044001074080713550091740d049820041c05480e115207007080c9038203482d846080e45c552182841031142c5256910b852a00841c0b80220049600c8a2543e500145488400f5000f0118600280b1540c60076014800340242585c101e030a40c0d04d030102c0601043c2c4600b161040d001c000110740c1140002e501e07641a88502030240c101c4c0b0466070454080b800100442c4c02c1458440d8002001c094005c0820070000c94401d07415841c000e443c0781503100e1401080c01c42d00a9007001c0b0703a60880d080a902888030401040c3c0c40ca103610b18040150910b00315100220303069141c00c44083c020091005000c0796442d44c15503d06042d2020b0556440e1070b500c6411000f4281 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 234361267 1250 234360017 234360029
    0x204060305070810060905210a0b0105031207050c12030c10290a05010804081c090605390c060412020114010e01052b050703060b06070b0c0c0a050a030207 68
    0x200380020003540320201020112082c0b500da80e540790b400c00c0e02340724099241d808050035801c2c202a03080303000031040040d00b001602440080e40d05505010030103040c000003410b01c0c0070b45d80302408014041140800d044650710340c2158400362585084600d14214007502000e00600d002d007404070244840682c0180a03103a00d000c8141a01c0362120a01202c9a80c180902c0340d00820700d504244002c2d40603000c4a504240100251410f010740c00c4d0881009030140d4505c5190b40b070311010b00320204622406a290440d141d610000d040a843c500d00c10301c505800d48400402d0b030014010381151100c3c5e50103c6192400400594005191a003070580080a582052130010740c60211080341001480f44103c0c1a134464240303082d0341380d19000400915402d280b42d039800c000c096003010303034254051804078841c942c45000680206d500d18100b502c1254414005203018003010000e820006110b0742c04035038402c0270407546a03110f950640c500b6240500001700200a80b042403524014160000341d00350441d50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 234362517 1250 234361267 234361277
    0x30c030e0129060715090302010603050a080703090509010e150609030727050609011a16030818030306030a020603040c0314030d05012405090f06041203020601050d050d110a06020406030507 83
    0x1000744103100d05480b0b006030241280a0f1707024000c1c440b00c110380100c1c0c0d40c54003a100100c0c2c2c01d612503c51604113189194121800803001440070708158009400500914003250416120342c5041c0c000c80903004014400c41c0110300d0204284426611001617580403100541190707405d544401203004444c0c28031880c248415254000d40000c1d0680d401043c0c03141c0350103440710710264648188425044035502c445161202c0900041c031019590810303030b02205010396035181b094100341b844650301070710921507401d15410070800c01c0741c25100020400c1101e541030304c0080c1c1d60399642c10880e440041541000b420800458450340c8038050020140100c0320a652041200c0c1e680d460449142c44800030021280d013810341d00401c680b1b0302810203481d0b0f42d032010700084448010000002c0c4554800d40105138038003880488a030a040d41009164094402550882d03806040c41d12550360302c80700100c0c1c42c4104044440742c8240f1030014407031180d00c660701020a5441e10385814018001d030404a40e440300041c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 234363767 1250 234362517 234362591
    0x4150e01020a110313030311010e030f1810020607050c0703060f090c1e18150b040f060804080906070201110609150c120a0c0309050a3f030c030e01 65
    0x56010040b5000200b0950390407090307900d50b80d001d41e8088400c1d07003623200713070b550b01c50003441c00100520082a0071030081480c01ea454541004000c20104040c10590203100c0050011040980006016800643d00e060041d11840000c20b224074254a5030401440c80e410500c40002a448903000034030100e2103041900212610313030f105504449410650210410400c00080002000c1c1c00e900809415800c680410348001000c1d80048080d06540f2004041000250800582484403122009014a4500307090780c1c1c1002d845140080c01000203091140c24002015401c685c01030152800304000141540d542d86407841c109030301ca04a00005642ea0070884001501840a00007103032984071341400c07440500e45640785510010020a0003039028150740c0d21403900071542c01c00034082100e01c200c241203400310940e034003103544c1c030341040400d40600581c500c0000e19400b6001c2c2e00c00055058500081d40340b298076400c5003d07000480010005500e0590307403040e440024020080ca003040304c02180703010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 234365017 1250 234363767 234363797
    0xb2a060609220803060117070c02100201020405010504031103071206060e060603130b0414030f030a0f02091f2a030207051914030304031a09060702210304150e01020a 73
    0x504451110001400b46400070002220358020356040030061401c5043e600b01040b5007280520142c540c5808603001040000c00c512300b48541351124031043c402942054035080018146006501000b89100310b410307184100758034100104d5000b094550341e2488080740500b805001403605001e148980c042c5900040c0460400c1e5040f87d0017010400c0b482202072400c0c0e12204183c1c1c0b4041c00171907140ea440299120071810402c042c002000b800060181e49041141068007121800e8034400a050b00510a0042990b0345410b610345680070f04c80310401009103400f0484034001c0f200243c51215800002051181d240d40445071042c0c1d1090f02210240d907100c00030000444118080c0c0a0054003180c1306208200d6540a0003c20100280c2240d041a0b202e07981c10f030192400025a01c1c256828004002c00d50000b0020b00d5001070060005e80000c540c0c00f508400a0038019050380f518190000c0810b00b00086418210f4984410640401100c144003c009001c1d40c000d001e640c0c00583c44282036210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 234366267 1250 234365017 234365041
    0x30e0102030a2a060515090108010c0e091905010b09010e090606031303030209060d050403080c070f030f020c2107050103051303080916060906270b2a060609 69
    0x660220344038040e005200d40a1880343e150a11640040c1c10f42c200d002c480001c1103170080c140201e4440c0351040152a05a0a120403510160b2200305180c1c1000b6014100f00d8010001032012501a00d905500f96614140c0d0500340748003074100c0d00c0780c6160400000d03900704050094112140240ea45151801c0c030a42000250401984d525902c440100b01164690017002d5140a203140310342070150030110100300054081e0480684000c1c5551984104020103510038002a441091031011500f0003035240c030744d50b601e02d10b9550f006052000340b900c0c02461030b00802c016551014000d10b07503030003815a819003410902c100f540340c040511601c0c0022600e50b000780207161003070310060a01d0002c5030707294500300d44480c0003905c0907400c0e00952810070011000742e6400009007280343c50301e084403441c09000502e014540307130404030340c041c1c403a10b181c0055511190003021520a10310558544200301144d030240ca4100c4030f07260542e8910f4000c00b10010f03021424a02c90780003241c00c82e1031940c1d44605021 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 234367517 1250 234366267 234366277
    0x4030324060519020c01021b1302071a0c070b070f27030b0a0c02030d0b04060308040803031015020d140904020d060e130203190606050a08010b030105071d0f1f0c030e010203 76
    0x301580002001c40b403810010202e101807079234010440c290500400c0c00e61402ca900400c0260f640c604801001801028002000394009001c0401c8a20b081010f40381c5c4900540040c205800b00708030040b500b401c1e00d1007940c1d280c902902e1202c80c50700c12154034a0654030401d2621007221f100b170061000a00c0c1a105100d110102000b64014500e010000c1300307107000408210b41c25aa0095036a00c000c408602c9203c00f0b8000741c41d00c00300450b07581c140709404540410301c0740d00032041200340212101045902080c5582d0503207103400d0854254907980205055030145102090f00035101080f8100d50360300300d402c60b500302c4a2401c1032441340d446000c000c040c3c1d031902c0c0b00b0183d0140c0c8030200a4140e030b1041103554003814040ea45c0006c0c40d584a10003c0c00400082c1d2020350780d42c1d1110300341a80303441c0138441d603500700b4114146a01c0c10307a0030451000040601c00c0c91035205000c0354840c04c070507880c3c0310003030741c02030501c4206100d0348041c2010182214111000907030000d0044042c0c4003540d400081103070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 234368767 1250 234367517 234367519
    0x509011503060504320715051204260d0b0303030106022e02070c061d03060c0a030f02120403020f1605100c0c0b03060112021204030324060519020c 65
    0xc1041811500c54002500000d4001c13141030403c2602910302c1d540100c810500c03007003603410040c1d46101c0e02c090940713403109580100040042c2c4000c2180001c0c1c104003100e241100d41c00d8684926503403070403c03013090218810310300c1041d40100083c155042500000304107454100d4400c00000144405140c0c1d28002400703a000544c0c8699600715008008080c003042c040781c3e82c500c020391140300c20554400da81107080f00300c070f0035420402c041c0400d030f402c42d4690091007002d140c1c2e40401002103000030792391000031b00720781c90000e40018040c01051007078000412442d240c034010b40d664030f002c10591700f00c640101e9081d0014014001c01c1e012054011039500c0207104a0300104503076a0419041040d108800984c850500140210002c009541038103a030005121001107952246065400076116010440c4c0740c1040364410409903d41a080c0b034a0260410b4052800041c8040034841c0702c80848c40314007043c40c10004410300010041e501c1001012040105003500000072100e400581c1e4510100d01c0c45 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 234370017 1250 234368767 234368801
    0x80c010c111902120304080307030e010c11040c0e09010f09050105090903030718180c0305060a05061e07150207050d0507051b030124090c02030304050d050d020f0418050901 76
    0xa03030701e000700d04010010781400180401c030f1203c41c4c0d1030703107501d941d00c9175100c01c580783c2020403050241600700c250381e584028203003405888043c440d61800c0003144286245403050b0765461f0b07151030042c415030000c0c000c4070340508003551a50319141030038003a8009228003a412810038002003102e00b0601c0d2114050070300c41f002141141c0b1000b1041d1505905503c0d054124513030490005001d109028212001c20f0b42680005150088400c008054850007400c00d8001c80f5000e000301b003183c44400c2100c815401018254028024050112031984990380000c0e2411150300440b20300d0003495801402103a200e1400c8941400841000359218020f000307002d000d07130b08070480b9408a100c0181c15051100170003800010750310640540700000c2d480c24020096034107550101401550200d1140321514102c9000540c01c510303042d40e5541d6a01c0481251204000c00482c10000030000380d0190b606800c2040086078545840c1c00d2000c1e082440c2c14402d50f03c40d801d10000c1001038606104d80a401000c00c0300c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 234371267 1250 234370017 234370033
    0xb040f031202031c05090606060c0d0e0406031407080115050604030209070c080313020901080a0803010b0705070f1202090a050f01121a1807060513170109020d080c010c11 75
    0x54403110800700d9844400e5000400090501d071020703554051000907100b5001660b400c0c1a442030b494000c3c02440c150240508003c0c025014400103a0804104060314210340459804004035002d814140d000402c0211200d140d691207031400f04051003a502d01e00002c00c145410f110084008103814400c030b942001c0100414009420b12500742c642c0000c95050405104501e6a12031089600445000f5441c0c00b00c0d5180e04110314141c001c4600400415004003420340840d1100811072006104080c544540090301d01c003040401d00442004142080d08900e146a40c1d20301d803260524202c4080f846011004002421150f15103e910302a0829034940c0401360b00302801d01400d410603400c260754000088201c000c4030458100854400d441410302d44036030341400c0884500c2d0a2140e080390041c00303014002180001009600c0701c00319450390025800c000700e64241c150041c070840d403020b9004800003d541c004d00c104040280040240c2d00020400031601040071107299041000a2036607422581c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 234372517 1250 234371267 234371273
    0x501030b071d041a09041211121614030a080f01060c0c050103050c07170406030c0503070c1502190e030706020a050a081e0403030f0815010c1205090301090501090c0b040f03 76
    0x32100c0107a03444419280e078039040301d20000d80503102c106c804690414110346240302245d4802841014210084004c040c9100c1d80407000b019809100c0e0b4900c03568007400c0e041c10038462000184001c1d80c0b0080c0070b999403404800c80040111000701c0314600041000000024140d01c1046c01520180c0c03c0b10390918018207240044000c0d10001d4509905044240200d80114441c2810f90b24282200180650f546140040c00307000d9070b00600c84c400510409208002c001c1ea0410000014a5440303045498030a001a07541802805403894110f40320b0300d00d100044880b42c210303c040e00401e20403411291074030344d25078040b1703030391003071381c540240720f074029215800010755454007070010860303607080032064141754500030181d030340041e0300c20740004511000307240d08150043d01068215040481409032014450300207448400c0c4e80e58020300c19034819400c584258072940944d40c0084000700284400c0c00c0508140b4007030b010448080c0c541500c4000c0000c0c0b20300010007210f0031901016411000c0f540783d51 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 234373767 1250 234372517 234372521
    0x3070c03120e030a05220b03040b040f0b090c01091527050607080703030e2b02070f181406151608120a0506030703110f010309150501030b071d04 64
    0x2000e400034040e2620b1408801d44020700203400b500c8240c4d901e040d1100015402c40c0324030410a0102103292520300d4003840500503500c206c81e441030304500b0007000c1e07441d98503084c030143c0d030b41c02000307070003c43c0880a0090300c144c04914032002d610241d035000f014944582c50010300350303228090000030404441c840200403142130040803d01c0d0f500780101051a665a0201d0b080380e014020807169003a002418004064140c0b0444c810060140010089190316151101c1000c40c80c9504e45140240d5070a054a214400c00061018041d04601c1d005081c0c0da43c0545140842a441016580d03400d04a031646081d40480850340f05500c0101a6030028241100b1505298051080b14076101c0004181c0000710707c0520003000d90505c0342c5440b94841c0743c0f4154210032078001a02c5940710b81c01034802040402c01400c14040142411104414401003100041e401004211001410755107110121a080f0441364851030403280201c0c6c030030520f43e0f2020411289214565801c002d224840d00300c480c1e0314105a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 234375017 1250 234373767 234373787
    0xc09070801050d020a0b0408070611010603030210020304081c0605010e0f0f060325050a1209020d0201030b0607060501080a020a0816060c060609150311010c02130c050918010f060503070c03 83
    0x140002c0c8003c4d4803506c501881c0d900a400c0300c22194015041003041c0e41e40804c5090131140300a00811201c0c0c15658029102c203d402c4407088100c0e0048045002d004502c0308440609051600c130f00031494050070044081c0010740708190200b003c4d072079040d00300e0400c0241d89209040003058136403001501000c01c0346a030000382948940b00c500d010401d81241e1503030388040c880e0641e5141c041d12000000802002c10020348040c6c07500605007183c2d000140c80e21144403004540c2420041034492249001c91210302624038050111424a400050004000f140000c91540240d4104090310b8441000c80e603181e00b1511903d560042d28882000701c688540300d2201618840d81c0c000c03034150750b43c1e132030103080c0d48604010041c891207101082080100b50404400c0103442820500404c1440d5000100030340f00c0380404000e001d442d402c0b40740c0200d200b10210303181c4503c020701343c4808014005405501c4103090203003101441c61003c01150301401078040d07900c955441d607240459060f00340d40c112000d10300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 234376267 1250 234375017 234375019
    0x50306060d03030e1009020906010c0b0708061c150b030303091b04061d06030105072f01060305030310170109230f060a0c03060506030103030c170d090f02030c09070801050d02 77
    0x240d640324a0351801c040c001c0d9480b00580c0f05e07020410200c10700400a441502a12090622000c840c4580c001850b1482441d8444840d04002010b9a9454042001e5000c011a03d10184a040c1c10500801c0200b0390403898840842c02e0400c0602c8a80d4185940c1c1c0c4001d07103c198442e4414165000c8034000d0015a0030482c40160001c42d6082d42d0303078003114117400f80c4010b40340695251410040d0a0409200d640d5100482d40740c6407090410441018440303582030380001003091500c082c0027507084400d400907c015a48041107036500d181c10b040c50f200c02d4159001e203000c242c1104480ea0510030f07050060211507500404115580c0c05000c208442c480308003490503455000d58815800301c02c1040c06094841c40001c2004240000a40001000c503080da8000a04c200014401440482e602c4a088070b00c8687c0707c0e06030901a8110701c000d01ca24028010311034481402c204c00d601c10002a180700e01102032003a82102d0140a40c2c0c0b00b0410364400c2210204002240310004008a02e00702e4401143e03240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 234377517 1250 234376267 234376271
    0xc03090d06090c0b1209070302090c0a0c0b0f040218091203060f03070602160503160603110d0203010f061b030e060f0405030f010c1106090706140408031204060c09050306060d0303 79
    0x81c0b2503841d050207103800d6110034500003011840c2145003240560980d4072854a001618810b0700b5580010004407002c3c050756203201010600c401694042d490040c030080d004004000b10b4604401207018030744044a01300c1c0505041980001d5034001040c0d0a40202680c0c805071000c012034400d078007030a82005040301c1d8000000c1d04480c505880900c82000980f1b41d540c05001d513505550050601500da542c04140a41d008090520041c6290f500c20f400b52582403034041074a640806828519018801c6000d034058400000095100c200032900012103042d5164060303044079100703c19400ea080764038050081114544291064a060001407001114000d01c0c1814191a10082483c02c891440050403030782d03680030302030500c94000c480c00403e01101d000401941ca02041e5039920b03900f03140300d60014404000c4148243c000300c1001e44004d40340e180104c0f900d41501305c111003000c0400340d5044c4c0e500391410450074565071080003880e00f5501c2c00346c01070007a9264501401610f9455030000d804040d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 234378767 1250 234377517 234377531
    0xd08150103050a020d090606030c15090e04031107241704061d0d080405060c030910020903190503130b090f0f03011107050601061101090b0105010f0e0a06120f020c03090d06 76
    0x180e0510586c1c4400c1c1c0500d13800100d0506503d0038805429854100b41d218900082c1c01c090501ea101c40d41c94207035450a031844185072100c0c40c003070b034100445200e10300344c0b806480c1e00850600400712101800b00000007442c0e003000d185071810384003c02d01003079100400313101c200020003140b82900020175600c1004079044000c00321040e00f60814174000581c0700028140d200303000c180201000000d400c041c0c42c58030039140d402d0001c0b64560b2010130032861414103030045511030503682c041c48180072502079000e5822007030070341e46040d03500d903401050000360b41543e058010030742c1000902680c845c240040c0c814000020308030104982188d07031300501581992225451480c07140201c004c2c0517a548294014082d0b0750408501401e0340002e000c440000f40c0c580000f10010a82c843d00e000d0443d5000c4c00c0c01c00c07002403154800c8410300c910039095900032030b455100090213a4418044030204000900801c5581989600d150591244008082d4254014414800c2e40d00d0260341822000344547c1c070000d100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 234380017 1250 234378767 234378787
    0x31401120510060f08010f0507090302090405010207050d030509190228050303070c050109061403010e06010507120807140306151b070605040f0b1306140d020301080706020d08150103050a02 83
    0x1d83d00e5038204200c030500500701046080024000c80014040c40301c4240810701e00207000130950883c038400684211440e00214041c401c0a5044034038903034111050f90400307610310402901400080e1030840152141d8140b0413411650104030820081c1d0040c42035007c050815030300021080100c11074564610000300029295a0410007081e02070b00c2250b0200d241c516000000d0324010540e4000010b10840c86940c0d524440c402088a0640300c0302d40e2000300c01d072541d00040741c06000c0e800008002115640003d900da640107903070244185030503950304e03584801c0d09010342442e01003038440b113030014226110080000d50000180008005450710301005100c01c0b8107503850030496500000106000080c2403024152100b5400007a003036103984689489405d042602085050b48601004c00c6039595a000340000840101c901d0754000c0b207001e540301e58440f1480342d19100580310f030001502c12070000c4040d25004656040c4035410940c0400d50491703061005401030800184140140740d4204101e20603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 234381267 1250 234380017 234380021
    0x3190b0a0b04090c1d010b04121110030506031b01020a1118040b0f06010302030919150905030c0706141b0c060307020d0338041404050d030c031401120510 68
    0x1c400d000f1000210450720708680640c020049204074034407100c05e240140404802c2004a400700d6440000381225818507090011118801c840c502c2c1d07011f12001510460640d140c1c100a0203482d0441c141d40c000904600664820f0301401c40842c05608050143d401140b00d0f03c21003443d2020242821a00720030200c0c00006144080320116032441c245010312031140007900941d5804042030030b04500d5400d260400c1ea646103205c0c03070203000724141c003020301c1d003009a0043d02201d0210000028052803445141a030740300d401c0012a1042885180d03400202c451050f202200005203d119492400b4460860180203842100002155201c5e540000b03865840f8a00110705c03030141503000c1c180c1d40d0802d1b500282a42d07920703018140d010100c2343c0800842c3c680742c1c84240c00001c2036503014900100c0760340400c001d00308440662449050080400003403100101e02c40740303d040169810481c851001206404649080c10b5111151510600620111443e040641c50b900c2c041c20131201000b8240440c001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 234382517 1250 234381267 234381281
    0x204080d080f100302131a030d0c03020f010204030f0b13120903060c021501091a100203040e0c250807120306060f020a151805010204120c0503190b0a0b04 68
    0x192900104000e202e94114019089009550744111041c40c42d00007a000003d50550213400c00e43d82c103d05491180c2c0c001c411030303080c2d40240996500808608004d08803144405080d0b004d4001c504038032001c04410b108076020f0b6a4010740d01d0021024039212107401d540002c0c600b49045900ca02000c011612a5051540c0e102481d40c800c101c050452400005803031305c10f00c0315415540411800c55a044540080030705480300d0b000006001a140191514a02041c04000b81c205484107110300d40164040010070a4540942c001c000350f8a9a1000604a02c2161000c4104903141d08800c01c50a56804484e42c1c501d000d21001c80c208860f030f0325080b000a503480c1003d004655101810481c454021041202220990000d089400f4190f06c4032600e1a0078180310308841503590f402d0403446424074072400c40560700980215100e5441c3e413184000401e6000017034400f0041008002071610380001d00a0618240040c00b03224800c880e40c4601d112100501071106458842103219440e8485105101e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 234383767 1250 234382517 234382543
    0xb03090a081b0312161106040204020a02070321030e0f250b0d1e02121302030708060115020c0609280503030c01060e0703090b01030809040207081602010f0e1302070204020408 77
    0x1380481c1410328240c160001c0d10084402841883c84084000001c080340c010740c03140d0107880c09030b9582c0049404a081451350380000305404920540e500d582d0481401c4044000da0549041000c41d090321000c0e43e661140743c50b0b02038a03610650380304101000c0c5400b50b4101c0702c4800c800e030701815140c0e80800c149800650b841c16030f5a41d6880c14041103036110804510a0340c000300c0445ca03044144486101c0d03844000c11120941c0107100341c0310110340b000c000a0340108548030a90345956107400d4544c07617070040d96402d82d0041c400c0c0c0e45140c0301482c16500300c802040c001410340c40311450806080407600401c2c41200e103811402c101c0096262800c2c0000c280c0032038650000280b00f410701c500c0b1f4048000c05400c1d102050f107007a070071400290301000c0042c1036a4001c82005e03190a880310014000c1d100340c1000800003003010580c444407010b42600000014401d0301e0b00c08000c04002011100a801084982d038420f100b600002e42280a43c0d0090048a001030000b528081e21020f0301c0380303001403008900e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 234385017 1250 234383767 234383797
    0x109081c0201021c0b031b0105040b0906040839090f090c031236090411101d030115300b061c08030106030e011b02030a0201060b03090a081b03 63
    0x35070545005d101310300c60588890401f412401d040000244240614018907201003400200407a10342e82e81c0703007914000c1c05807004803164141e0380ca100401c01c0d00c4241008000040560300d041d110b02101412051005000e40009104c1d501c1d0032a82048610151180c541c41c000c4908205541c2c4040c0101c09803416806813181e030380c0d041100c4c0000010f04c0c685207641503401d498030502502200762102001034a044500455a49441c1401e4042044444d98194031402c00d84c500c0a40b030741c105014080e106074501e40340590002e0300c004c0c5800d0314003100c03128101d080421010311003c0c04402600c8030450748070144400e0700f8005000c111300c000006d00151010036060080150510f002a01805039400241c40c41c40014019603071541d8600041c05244149500c40d400c03601ea08200354443c0040c3e0030b1025148210340200900a5240e9120301907910040d42481c0300400c0c503041c5102100e00968131040106800c2000340c42d0221150010640c284142040c0320005003c0c80c401c2002d44901441c641603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 234386267 1250 234385017 234385031
    0xb040803070e0904020f0405040c0e0a091101020303070906080c070203010203041b360e240a0608070e06060408060c030105040b0d0206030f040206040b0a0e0a050109081c0201021c 79
    0x70103003204070360400862080c9001c1d420400161503400f900720b40901d0654010036107441c2c41c03407d00c0d1910802d402900b924031000081145103c516000601c01c00d00400303d120081e03002e4801262680b108a0b0307081d0200348a070108202c0d0340d1003468000c3d48042821183c5080c6038041d0b0009081e80d00954013600c0190703003120503504c43c140120380c1c00003e01c0030301401c5002000500e9041e80000b584c9110715281c0511510000500d01c164002503022040300080d1240348104a91940400041c40380c807407084004031001034000c500c14825035042e0f5031408d009004503850a041080b41e0000288000e400042c2844005050a010410320f409500c0c034203091507d0758141024001260070500ca040d200741d24000244015807151411030b50030103107000030044603540da4000b04030b003845941e000c1c2041c0007000407403444550303005500d0031444c44122090a0003c0c0d4880044462111074005d110990b00581c0c1c1c2c2031680c80c4010040340f40441540000741c10316081d030154213220003e4102003d2103544400d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 234387517 1250 234386267 234386281
    0x9230c0c0d0c0c0f03030c1e06140f060639010606080f060607031b02180a060f080c0a1214060c0406030c020114010911090a030f05070605090108130f0b040803 70
    0x1800e00301420704d0440c81403505203982c5004002c0c2d08044000744c01500c003034401000a03080c030031203d1103840e0406c03400e0101c0c020312480c0b09141c01040b24a6004440da10021840c146000e00448d4403218148a1038802c00981ca01440c0103815910070109900f2194450000d00c0c940c203018503002440ca64994054510f400d00121007491001054940300c0c40302084030b01d0000340c0015226000d02c10309400d52951903000e201080141441e0071081c111444000d00300036900980343c208905440e2500502102039565410721952441c0d072465030365002008642c01d01860b1203811801c0005d60080c2414820b20f882c151f0f245003407401c162619884010002010310903190940500c0c1c4043c0000d01c02000785050300400110f6801060140c0145180c07102007080170140ba003000c1d5500418020815070a4036900c0c03030400c005034a510707000c0f0b60318000e1500c0040c00034011815a02c0008041c1c480070340980c0e0b80003c01c088000d426038100c80c503200243d0051b010901d0400403d2240d80f040c040b007030b981c0c20081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 234388767 1250 234387517 234387533
    0xe0301090b0a1d0c010807030506031f1a0117010915090e0703120e100f021e0c040c11070302190e04030c140106121502091504060909230c0c0d0c 64
    0xc800043c2c954400c2242c88403990b0b010303103500c3e40b0008074940016161504000241804e4041640d0145280344010740c91120741694042e81a414032036148003503c00c0001d005403490040c03902803148100741300d8010460307100c803900861007480c2440c01100710fa5480725117a404454420000b0000c1e640041402e00c200043c00c2e18601c00046507050020340698128009443ca000d034005640800407441000700409000300020320844403100d02650045040005580c8d881016501031351040782000e071514909402050901c125801400141c9010381c00e41e002e1100e115540741d0300901c100c0c00c2540000318040d4241d03425014911036511380310543d440741404445220a0602d0b003e460b4500001000490044c24140403115888030401c10600c1176100390308003d004200c003540d00400310060701d100b4001d0100c0280241c034203c0d2142054582c55810b29000c4038260202984500d420040c0c40404602c03a0703074001d912a4101d9803491514040414141c1855000726108010941c2c058040741000710b44 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 234390017 1250 234388767 234388811
    0x7050c040c05181513060e0907090b0a030c05040e01060f1419080603010e010e100f111b011b0e040605150909090a0c0b03041505060109060e0301090b0a 67
    0x1a00d04207040c8140c1c04203c2242d036940c0300320b5502c144004107096000002d610199015142c050350b00141c00c03582e80202a0a0404503401c99101d0310340b01d0300103118039010719400010307a242d082800d814038150031002d50042000741001c000740001480002180b5494400f5070340131780107a035520340301d00600740b0004c1c00d00421242d01034001d43d01031200d0140c0c03e17151030550348825507516108175152a61000309004061480003100d0070350030400b46100d441c200084241d21081044010080101c000751820700321091280c1d9000316640c200000071400045141803e10b502d0498000101d514078481e0200c8071551807c2e0304004190f4101000740c2d20300d4079124ac0c40c005e10044e0b07043e40c0210341c41e95041144e40720b041c0300c40b446201d400020031900b5104114410700c01b03510004011202e9200d142d608030303680080750100e0b070341c60400b980c0c20801419401918043c20f41078681040c024148282038030501c0c1125a03464040d0350340c4616001061455901500502e15904009450741064843c2010307c000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 234391267 1250 234390017 234390041
    0xa0b011101140a0f020408070e1608040201020d050a180801051009050603121303050709051501021f0e03090904060b010810030b0c0703050c030d0b0f030d020601030602090402090607050c04 83
    0x501a010108480e0040c1074550242e40f4070341c0010f09440c803035028802400780d600711784518820100d010036809082459540901600c0400640c101e4038508219442001128024010303007182904104043c0107034041c1000060900b410070302810041100001483d032680050f02687d11102403002c9085206061000ba08840d0024410741c501600802d03a6406140503901c0c20010028028a0b00000680110051907100c4190b450240c0d07a820308a000d07100a81e591001c4078250400d0000d1513000017070794800010140c420a001e040c0d0300e50044020003101008075014001000905001e907501c2510b075110b944a1840060300d401e22200050840384004c0c2582100c025200e0f06001040b01e04070841e40c800c4561141c40e9684610b45030449281c0120020848640300108401c4001810743c0c014a0f050038040c0c61a00781903040108144da1082c01aa41d080584c000340c00501c003180f9a50024900048060000744c507241044010030060742c0008016a0703243c1154074820b84500d400d006071450581 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 234392517 1250 234391267 234391271
    0x30b060117130c0506070503040311180403030507020106090e0718150b070206040b1b100b0d020d0203070f03030809010c0201021e030403140f0a080a020a05030103290a0b011101 78
    0x620700a2074103040002d0184942c20012400450030000d002080701d0107420702400341901c45105280c01e655a42050108540807241c03690302002c0341c00d001a5100c840394803210005007584450300c3c00d40090030054821f10865480d400f0105d4500d030301d4014103e0f500704041c0103000c11340c81d01070b03c9210070020500324000c26060150103100c4601802d41641550580b0510036610720b51407002031281c0c4195849000c14040220b49d40d854103c0702041030210790280002d80300c2c824101504c100c100d5003001071452303011a82c0e16440c005402d00607c81c9040314400390454a010392280340120301c11009a0040b00000c400c0010440502400c0c000c59403a140280029400c28008406021860070001c44412070070a0100004040c1841244c0d4001040410b02c41c942d590009141e004040d603000c2c1e100c190100d6417800c00f107644041180302700d400b0201241d880320700356400c42d9140011101401101000700e0204100e5045190341d030341a5038011110018001341101a00c0000b52207401c591403030005a0b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 234393767 1250 234392517 234392537
    0x1017090c01020726061302040f050415110d0f0522050a20040609020a021203010e0f090307060f0b0f06071212020c0a0b0108150103110103021606050907030b0601 71
    0x70741c0003d241c50640d82c2d003501c50310b541007801c0da907810014410b0000400900c00c0317030f0901005015580743d0001d594003e03102403088000200441c019500c064a0080046a0400708504485004d84c0f142102081142509281c026100002015a05900e0b22944640e640b941031042000390001c1c3c0b2055021814200d0300d044419440b442c0d141c50703e8a070050300c90300340c030109600d800c80e05183c082028100100b04104141d01d5900c01d10094120128402c0588100b40034901c416070b085082c2c2c2d0403130f800310034011450f54030075000000c107c1d00500f02d4056484140804400140140210014803404c10030000d43c0c000ca000030400d00c040202121802802c0802554000c90040c1780080c1036026241486000034a00c2040c000007441002ca0011907409003c441004220110780000e04a40d10315044a684a10340390481e00c403040c2c284070081124103080100c40b042d50184d00035041d10f240480b00ca0214180e280c9494069030b404807000c4e0415005218140b042004080d62160080800e181c1003240c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 234395017 1250 234393767 234393769
    0x106050a08060601350403030e0609061605181e030303040b0a05070906020d0e010912050a0c060305060105190e040e01020c1b24040302062a0a080415030b1017090c 72
    0x810104100840800f5031000021b00b413501070f820264561158100b21109803070540c0150740c44402c1561034015042d003840100180a01c92029180c142c05074400a01a00b5000c0341040b65a0250039804912010b42c1540c1d03080b075076030a1025603c40d900640e0075102c24603103d0361020840b6401000314081c040306e08000d00c16158001804115095181005030f0b040140200681d8403110541c0700980340c1442c140b05404100f80811400000c41c07040c00126851529808241d003a02c104031400da000540502010a00032940d400701000141c1c641440c0c02192001408603090700c0312400c4000150790001040e11203a50108031031241184110101d90210300084005042c48000480303003248118001e01214800900b00211001194000e00096136000049442000c0c10420303030b00801221040c0794000c2c0c1c100000710f044072040b41d01c0702078107150504003102110004455952441050742c0c8a1a030055a201c2401e00030356500a903c4030080c84096031813184128800910503250b40d00160380070199 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 234396267 1250 234395017 234395087
    0x50a080106110f06090d03050a06060807051c09030507120c150209040624080106090303020604060e0a0510020409150e040609030c0602030109050612010207051e0106050a08060601 79
    0x1990124500a24204060052a40f0300b44040c420101c00f402601c2c107110000c03a0019802c1650b00807a2800c0c8180d5440d10000c1c01110703858403600f00469002c40c00154081e00c035000a1075140d0340410003031901e0080890013400c9941080c01140494000254041849090121048160290700d8804200c01840e510798503628504013105002c04e0700031034002050f80c0c607a04203001a050105c00321046000020030205200301014066003c2031911002003283c07845034042c9030070f480d050307002030120ba140e6035140360051080213004010340c0210711350000022001d2041c440c02ca1010b201c007580715410443c2d07070000c613002c540e8460b001000c0c00500b004200d51482455038440e80040703002a50303075603900b0b050380d042603459001010244000000b0949000d80c3c1d00007030041d40709403078001d0111090110340e03081b403240840240480d400401c25040350140300e0032868030304e4548000414060baa48010800f0449103802440c65034200703404111042d68080c096104003600074540000540c40d904140318 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 234397517 1250 234396267 234396269
    0xf0b010915051009030510090b07080c03040f03091809140a1e030c020604090608010b1519180e01051216030f080f040b07061a0a051c050f03071101050a0801 69
    0x10040290400043d040c60050000000464115080d1500a00c044590100400c840b034070031113108111001081515120b203541c1d511400d1400b016501c0c0da1101d031115030907207050040c100c08009503100089a90101c4218810803002c10540120b0780340040d10304180c500c0860310514805500500301400030030032000c03540240a841d0342c46170618036a82d06003240e603120801030183d000f2a00250015440d15254818012035802200070412481070000b0003040101207580350000c0380e0144040c03c4d00e1180a0441c4095402904251000c000d40400e007401c8102a903111954140220004001038100600b45680744010200500075140d42c00c0d2510504000a00000c1c0c54a0001007440080003030300e8044404440a562603107880e5603076401c10003216800151304642050a14a844480f202c1d4800140034042005240203141400d00d420322a4000400741480420765080c1c11440109200b4014045c2c403482c804003441d59140b90382000e903003d54841017664100001048090103103640700d5113842c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 234398767 1250 234397517 234397519
    0x20c0604050d060e1e06090102071a100512030702030c030304050603180307020a0e1e040809010302090f041802120d05030601141905030a0608010203010e0105190806040f0b01091505 80
    0xd03190042c02c3c040e005110031315400c0b980e480f41d0711551541884601e02d03100b1001c0e07180121030180d500c03004850300381d014141c0c0050003600c07101e2041c00044610503100b0f5111034210301407102240c0d9075001681c4104000542e03070305504002951400d40c103041c0060748244c1801c2d0002d500e800e140c072001c601c0d9440000d000744400b480c078104604aa45e0280f04031031034503400900404186817966918854060240e03141019110040001c0040d291050b005910650300b08442500300007100b001034010703620428890b94885440458101d065840d07118102007480542c809000e00000391061080c0c0c3c04020410b062194841c14211303441e194801d0403281d1251081c82d01001060300605c00003000d0042c04801441c59954250300c011656110024620840040344140146a640c003001c9080f0320080c05542020b05850300140881c0c1021148000c5003802e00111144480c1c1d10901c690030400d054904030340916101755003006001d201034444c1d024040800302040072205011500b500e04015100d61 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 234400017 1250 234398767 234398779
    0x280506041518080f1315020303010f082406033f0304050a020114071a0a0c03020f0f03100305060406020307020c1c1713090608070605070b0708040f170d0c020c060405 73
    0x2031440d005c3c00b4010350007000072140c5202d080144900181d140d4000f4041d17200c1c0391018890006035240e000401003044c05101c0400700c800324902d00b402c84002402001d05030988904444194100382d100454500140e01268003c11500403c8080340c84403040c078002e42c2908018420b000200f0804980740c81c84c513609090640e4071042d51207072850f140c041d0b5640a062601c00070134580c80c911800c9145840751990440400c56400d8450701903040b8003400c2111a2030304018005c240c030140302c040c000c5070891607030036450112039500d6445500d40042102c0450b203068011007030041d81030b01081703003165954040700c2d09a07051146854141d0a40c2824102400c0d803045007111295030802a82120b02d00e405c0200400091505d400c01580504103034440c4500030f00c100440010703103e1142080e03c400907809034900889885110049402849c00391060321a52103001b0078100150450315044c103402d0704021441e860f450000840710464074002c0c002815900306030303020003040d5201e45c11507050710811202 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 234401267 1250 234400017 234400027
    0x609150307030602030702010903111c080907080109050f0106090501051e010314010609080f0102031e090102040f03060603060b09090c1e04090c050a080708280506041518080f 77
    0x901c0c081c915440602264400400c1c030000f554190000500240261511400742c0b91400b980ca0740c0d034a100c08031404402e00c030302c0e07c200094400d824154000c4554003c5400352919034060a08488044008807160385c044885040c060030b086c081d2000400c4003200801c4290306d0000401c0980e45444d8186e0505218070316448804d0f03000380e03c80300602c18084540f00b1300350f85070300005e080902d05001d115110b1207200b40102c00c10805000716441880100b00d00c1001095030b0250300c4a080000c0c180c900c1654013440042005055140704500a50203a07a010a486e49075061000403a5080112103000341c44a80c00c102c00e058001503054000344050b50030078200500960440000c01190022692107824140d80388107204035a402c51050301e400302c901a42c00c50b510b41c0c0c3d0b90f649078070034170034540160084140144100c042252003000c0d40424010405180b602c0d540b0f85040100c2250125600300490402082900441c400d01d25201c0c1780321380200c05c10035251208001801000c840b07410f1030f400020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 234402517 1250 234401267 234401269
    0xb03010f05090105092a010c241d03120606030a09020409080c120301030c12060207050102120421080402060d0e0303010b0703030b0d020616050c1003020d0b010206060915 75
    0x10001103022200101003101e03040088605028280550754030090b8840e08640c0c01a410741a805181c0741e10298244110000c0c50300c00546a0681c030000c1a190703000d4040405c1c24409005030140c41800d00003c2c006190340d001c5080b40c0d00c00505003292502d551007800013409811407110000d07000403003280e60329200da03180760110b000b501c2c1c0e505c1c0c000c0d040b50400c207100b0f0800051001400036510382d80c040c4c80c00c000444101e22141c1c082448003604000c4c900314100601c0c401880042405402001c000d0311740250f54555501ba40e110030100340b6030480034400c00c014419050395880d0361980f45001c8040c45d801044000b0034414002c0c102034030440001404140f03410460341306000e025151000c1e6505da60b0742d1180b4060341c0d00180000ea011a04002920f8220726000c0c80d440b81c6c1c140e000f41045d0405260100c42210320016440c00c07034a0b84203030407000b00f95541d2000540f003405042e94026a0741e40c414840082581c1180c08024155804030b020f1104550b200140307d540150828040507e41c40060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 234403767 1250 234402517 234402521
    0x8190509030d1d01050f04020a14191e060305010602030a0302030c0c010e0717030f0a0315051513150206010302060f0f0301260c0f011b0b0108060f100f06030b0301 72
    0x1203641030b007103262110540c80741d501041c00712000f00c1034400030480d076079560049140d02102290001e510141054043c801a200c1451600200d00050008440c01103640714502840c191030f04482019454502043c0380c44510561180107031940b844e0a00295150000c00380d924000c0d42c00c0403090540110004284c8807040003500d03030060011000b0312035a22041a603d4541119009039060000665440100550000101c540e40c001c000c03002482c00070800c5041300100f08200302c1c010030b070440010002e540c0da40c07001210181c0307104c0a10340b030751095105110031060400ba070181c52540c01e1800040d55080e0003140050440c1e070191100c40c2e0740e10300d840c00300145104001906210700c80101c008a100000c2a8241010040c0c110401140125040c00c00c0d035070b00300c001c21040e4440e004030606c07000c4d54410902c40e06012044035100c013000ca216a90031080c842e00340c1007001590701820400581100cc5c444a0740c002c90f10034070061109081c4203020905603c40d0090384281902c40e00d81c451691130075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 234405017 1250 234403767 234403777
    0x50c10050702041104170c06190c0b040507090e0105040507030b07210603120509030a080d0902060c06040201031d0c2403041104060918060914031204050d0819050903 73
    0x20001c000c0c0410700c1030700c0c41e11354009004110202031480c9000005480004106418000c020b114600300014840c48816100c0c84140b0881005070172044000018240707001240143c0c815000703030a44038140030030801191003215064035560f0503c07060002052000c0780c014186c0303070001e11207540da41d24203809a488100c0c00b030b41404414103258403d50b03506504d03400300040c0c9200f03640c0c480950301021030807501805074035601c030f50503041074400000140442e001444c0607001042d02248030601900040d249800001900300941c00c21801c0200f1983c0c944221800050841c400c0a03201c1d0a04040aa8804100000d18050f0b107045003074506104003880c1c1c5103151040507507030603502d2415240460000000c10481405a410100d000c5a0300d013407405260f4901000c1e1101403002c01083c3c4a00780070301141c5100f078420200f02c506072018214240010403c0095601c5542d060b410140340440c07030040c05119810811582c40c040c88507000c0b006c021002406031000010440b0345901502500310701c90 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 234406267 1250 234405017 234405019
    0x20c0601080105090c090106050318010b12010b18010605030114011b030e24071b0e04030c050d081504090c050a15080603210a0309080304080316020a050c10050702 72
    0x848000040a1805422407482502110181c0d04203465613024030010000070b004900c0410020b1002990705842d201041d0000d030b52404c001304034401c0e60303004914400c080e02c044007940d9442d01a000e41c14104814001d03aa80512208a0351542c13408100601900040c01100f5000c00c1c40e119109003071b8410400c12030450b07004040d040e0503040a01d400b920070b0000500442c02907404003801442118421070640da0011162480e52800e0030a644981c40080300180c14031040305002da010944084218403280b00e94801d4842c282070740540d051a5181020310b507a1401046280340410101600c3c0701c160141500041da4085207011042c5454403410049411241d00b241900b02c0005840318a00140780400c03a0039101c1034200d442c1d07201030640740c15aa40e42c009640340c08140b040c000000460050418801510f0006808190b035900c0c9030040e070065030103607090306010050240d6140304602c1c20201c0040740c0010035440d07030a0399a1548440030300d614a031044040801c1040e0103030061048072151a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 234407517 1250 234406267 234406273
    0xc030d18080706030b0f09060918030714070305120a120207150f0c0306090908030103030c15050406020405011202030709030b0a060512010905070b070c210f1202060601090b0906090301020c 83
    0x3e114031005004040780d000081c480e00e40b07074882d045541400d00b080380c011030b40681110110f544005890b50750354100382c6c1da020541300401c400c20104001e140240041a444d8004c1c0594074079604105241c2600e11140c446810020040503030004c0d005600b0594190690310090385a035a0742c100b0038040c1200301440b42c10b4034201614413100311116404154400800c9d1070400c145034941c0813460446450030b2000303180350700804c01030020038050f06500c5c1c041031107014a000c80d81742a912000503940140ca0844070140c0104091255617013011a4200614400790114211301e8061001040f81d44030703110243c003074400c82001c603200e41d0058201c0380103442d015020604482011026600800c038035501992240a10f04021a43c0700b46401110a541c1e00304240e13030302003810103103c0c050902c4100001d1885104d40806000000c8281c1140003225001d03418121000f041200c0103410302000a103802e0401441e2101070094900c000140c2d40ca040098817001e4681c00e080001c00e00a10030301a02040b544 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 234408767 1250 234407517 234407519
    0x1080d120204080a150e031201090207020613062c0306131401020f0309100506100806041407050720030a0f050a0c0f031205120402101413170c030d180807 68
    0x110b1714407090307004030410340410040a0015200b080c1c1384e0040c1041003800071081c000401511405070003405080340000e11452902c5900c03c00388428604652000b03003c1010310020454031394815110080080308000401101007001c0002607e880c001411070442c4038000c5c001c403051001c41c2090744124180e181c02190b0f02c40403040d90b0380740d6800440e1458021720400c000030740450040c0c058680141d10250480f20340305081c1e1b0f03060307604460003403c10390885c4d82c0d50301c0b10311019409509240200c0960b1586a0b0718085030804039844076860404c1030440e2010681c00342651000900e80c00c4a030f0304030035104088412881c0080c200303250000082c1c000c0710251004521800011501c0e0100d92241c00d0b4682101da180406075500d0058452000c60700513003034000390140c14855501c6e680c01d29903141a900d521b1040d10090101c0e00f109040b400902c6000109110203003910103c148505a100024450400914002695916041460410400a15812154001001c2c03501014140782c206959040d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 234410017 1250 234408767 234408773
    0x706080c03130c060e1c02060324030a08030a0b12061812030703020901082406030603010b040f0e0d1b080a0513300c060809030c03040f1401050301080d120204080a 72
    0x40c0181218081c0700f4001044807112103503561b60b203190029400b4050324215564805280c00c00c21600c0d0310f0881d1245109025201e541d8213101d956500c80c8902186900d83c14282c80d07031812203104900b918081d641401903511041c0c0005103469100c000107080301011010b455429040900d2010b80907405100070051006894041d00900318805007a60794060582c1c03043e00385041100205003c0c5c503908500c1c1c1e102c11042c14410011a400f42d07000d0004a80103407180081800c48800e0580081420780e56880d910021806010000845040b0300d03100f011004070b03080c24880300307100e070301c0c010055600095000e02c454041c0c41551844403102f100c030700e00317255209117041c0e40041c030030b810060302c00b4050f8203007641c22500001180026044003954481c0303403d100702502c144001a0190b0b00c11b02c020300101c10313881010002000a80300c90801501054a13244060300408899040d06061080a0006103d0088002202094441d02c0d2130324400e040c10300c00e2103000138030640e0025400390007885041c10038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 234411267 1250 234410017 234410027
    0x1090b06120313060c08190e1c0213050703091221090807020d080f0f0d0f0e03030f07170403020f06060f0d030507172a0706080c03130c06 61
    0x419031040d10495031526220039100d80782d11510040004101050800b4000c56211304211004a4820b02c0100e151061803035075144d621641c0a00140000c0c61403200032a213040c014003141010040006a5841c51400c0c0c0c00910800e20014810000c20341ea40d000811180c80398105120710b58115400b04100300c0251001000c003800e81400700c0300441d030002c00e82e0f203907c1c03644200106c0c02d4000403030074106412070b42000700c04901da200550308504140102d900c999001c40003040e5041d0f50300040e5903201b45150941c41a9104420010001840c2280d20903c01d5030210840703900a0384114590f115585280042e140d07052100d40078403034901e80108100800d0380000d40107038400404811602c003641d40408020241945040903a00501c0042d24240020b0084020b00f100601c01c040f41c400c03401e4800e2140d54190490300c83c00c1c412480c0b018015151039aa41c0c3d000300b20350303c3c007030152010f1414070f240074000c0c55010b81600c0c106600040003900319031010011408a540c8044003400e9565903d1000b4a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 234412517 1250 234411267 234411271
    0x80303040309140d020d031101020d0b15040f050d03020f0105070c03300e0f0102070507030b0f0f060609030a05160f0e0f0c030601050f03040308010609080a02031c05040801090b 78
    0x10124654581c046100c5401d0b181111440f6070003040c0035111111a820f00c1621018841b00300d06004a902072015051420300141a8071107030010700191040c015010800d00010f001070066406900b00000e1005682004400301500c80036161103286440c01d150032454040740310b042005a5203841c00f4402c4451307015002050a9000e9034031001040364200a907820381c0001c1d000b00e5005d01d1305c4010301d10600000c2e040009254440025a11441b1100e409030b800da90040c54100c80d60741002c0028000c002c4a1401c103600300c1840000c00d01c451074031f01e121048400014121321310889012418441e10b40e010465800a1607002042da0f003440c440120035502c589450103402c291500e82180400e0200303000180d01e00c00c1d010740818a4854445441e4000254000b41030141007107010003880501e5074110004501841c4241c8d00e0758203542c94081c0080c11002d403500000203940140d250b64026a03000a41d4882c1c00403d140c8007018203103210703815643c0740304540c00703a00b01c3c1d424114100d06004041c24124 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 234413767 1250 234412517 234412523
    0x5010b03060f18061201061a04080610030f020d020609060c152805060109030b04050601050306010b0406020a110112090f02030105070201020a14030703020d060824190216060608030304 81
    0x2c02e10105002c1044200702c48010895003c0034910005541403404d003500c24036454113100000303101521100b4401c0c04ca1041c0384901040b0b51300180030000c1c3d20b420845281d1289a4070020b400090a40c1c2c0c4000701c1c11004c0d88040e00c507490f512450000e5550700812243c603210020481d950f140c440816030740c1c4410902d4041c2000d2070010340020242440800e10504202080c02020007400c8269030039002420051301d038a040014010f00030001070361858806000d20301a1005194542c5000105440c00c0f005030400544000300788001c00510fa000521141703416401415031012014103030040f92a0181c65005108071824010100140051200455a00360003a0002e106680c4c2d8404103034280d10030f41310300c1000140c00d0007501240b1030b8044003550300100e00d40382c0075207403040b240d12030b0f81660412742040b211900050100d0380288107a610b880c01c1c80c038464601c0100383c90045c807203145131303e06a80841d4030980c0018a90074a080300d0303810440c1442c0d000c40100800c42d00e038101c042d0340343c004070f44c21 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 234415017 1250 234413767 234413779
    0x20a0309081f050408070f030c050d05070804172a1c021f050c07030b0708060306010f06030b0a0302030d050a081b0301140607122106050609041e05010b0306 69
    0x2046500010030303201d00b000610302c44140e40034500c03000640181002081075684060900c107105c00100390741006503100703010fa42c4005810b482410b2660070078205250000501c0010000440040c2c1e048060300d08541d482d402000c8202601d411190800c00600b15800000007282d80000c00c1d0b20b0454a954002141651040c683d240c50140304024002d0040000e54044c42c160b2041004210f003100074580c10003a0b1615608000c910303400d45160960b203404c1150310348554001c01c019181c0c01040d10b42c1c0440201d00030103803545052810302100110f40100070030180c581c10385800d281c8aa00c0311400640e406800c03121020304004004165801c29011040002d0120f004039842e82a00c1c000c0f0904024040c0c007062441c1d203850408210030700a004580c0c1c000500340030140c08180d4180d195110307070940b0340b202070517081d6240c150610340301c07100310070400246400b5042c006a1180d40c141c44020500b9100054819100504218660312a4002070300d02820a00042219070340368010b18015041500d00e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 234416267 1250 234415017 234415019
    0x280c0305100b04020405030c2403040c0614071101030507020f12030609100308040506090409060e01050702120a0207050d02010309081303060b0603090a060b0f040603110a051002030301090903050910020a0309 91
    0xc001c16403150380f05603030345603111074452102490040b04c2e54a28103a4418510850507125082e40300d581c008032401d80f0400c263303000070025640c12010507808030650401140c601141961344100400300ca0301028101545d620014220900800804001003003410488460718502c0c01380c003200354822140c8900804028010400c22981d80c1c03189020f59603c00704481c2014140f100307008964210000352540262180d40d014003040d40c600c50754588010800c0003050b00c0ca800140039160501141820f503524130100002051a41d0200b04003090300d50407141605404454001203001c0c20343c420010349110f10009a00c48200e022140e00405c0783e209681c140010f00c00f4030b007007060a00040310035150382d41118130500001000c80e40a2409103c000f094080141c80c46030109003254107580045403800d200c94816031a030300d0103100980060a003241d60f0402140c03d420300070345a000610844105580720906102054012402d41d500100041c08410000b000c0642c029174500310100c0a03801b003540008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 234417517 1250 234416267 234416269
    0x51e090d060207061d0709021812010c090f0503030909060303070602030708070e03011b0f02070b04060207050406050603061008251e080c0319091514010b030108280c0305100b 77
    0x20b210b040160705d1005420701c1c83c5840035280182d441052812181406410b16071500d5582030050b5a8051a010000a0144148001500302605500702c51b0303050b00b00800401c0079641c0002280d50f0f1400079510080c480e110071001c240745000342040288607a002000300120654000c3d9810301ca11026603070510000c00301c0c401d05080792407012107807401e02e2001000180c0395020740350090100b8802d104448400366500c0c00f10500e034105400443c0140c0008070304001c503103440c2c011440a4101111050700d14141400092031105c0424008014040d01d000018081e00d039040341d108a0000000c180d400070307600320310010485d01e8222111620514201c803444002e038800c428aa20a01e9504409441c644034511101c19594034800c082352160f449950600000d10703030348860508003000780f01c0030401605c00011080d11100507041151042c00600041008140c0020b01462003410b000b038003881b01007802500e02c4250000300c1d0181c0b0903149000c00008200d0001a22054080c0c110030802410704540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 234418767 1250 234417517 234417551
    0x70b070318031b05060a0e0f0318091e01030b0f0f070c0308100812090a050102030a020709021c020a02100612030905100201150807090609050106051e090d06020706 72
    0x78004100348030000c00101c0002c1c0c041c0b0041c404005940a1090389403ea139030304e1070302e84401103890100031921041d01704240c1d1010001d602c190320200002d941030500084040c2d4000b903000c000c0310f2180d0590008100824800f50344482d0700b0855000900f025a1a8181410200301c00d43d1884040c01040000465a09000c10300314000e040711790700d050141e01c464400715903949002e802c600150840c0b00c0005002c01003001000c80c04040049001d4943e0000703c1005604852540518159042041611822907001c01c0b040165070a202005032500441c070b00f20381440d8100d414210513940700145150105400094510250760016030a0104c10341b100384826030784c4e20281c0300501189c5942401e1059207484d11000d40d00c00d0342403000080042442c05420400d0f9896030243c81c0c55080803106022004490003440040c20281c5070600039945846002082d5120b81c20303100c100f41f07075010302d80080c0e040d10a0856040140c0142031208a0f541c0d403c0400080d0f1004804951040c5051200d95242c0840d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 234420017 1250 234418767 234418781
    0x2100902030a020f0402310807030312051005040614090a0e100b0d2109090209060a0e01020c061c15030320010b090403031418070b090105041a070b0703 67
    0x107000360403114296424400e0202d003c2e285254040e40a202c2c905110205401d0111000310195240c019501c07500150200390800e500001d40d40c0e0000302c024400b00707810500703009200083c4071001a561340d580c00d0010750948a60000d42d4050b04207400003503592803d41c818507902004981420710b41c1c4801017128100c6142c4d2404469507000324800d00840e13101c07175000c48001000034241e81c407039281594070924640001d202c0300b090a44484a2800503c1c3c2c01404003002c0c0000500840ca03100d09070f4005a03a030701401d0300307140400040402c00c0e00b159100317002c00c800c041c40113401c858550215002000f890031014040d858414541705050034010048050302c8226605511940c2c2100e080045003480486004014403d0f5900d0303014510355500d464800038420381c00f0340d60005520014013490000c04034041c2151440381e100d2000100c1d80040840c03010100c580c0241d46035940c464800050341c030360080781d101c24038102e1000440d540950000c401013030164880d001c0e526607952024030a408031000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 234421267 1250 234420017 234420019
    0x30f0a14060103020a05070c0609060f030213030803060301021b0601090b04060f06080c0c0d021c031b0f020c0405010b040f060819020702040e01050403020d030c091a0325020d02100902 81
    0x80203001c100203500990003007120707220300e01e4800d10f0b00041f6100d85040c3d07060b40d84000300084405108102d03144c0d00056031071f407042041c5815441c0c00300c240250862400c5a00014006d4907000001c0790059600758119411445001c8019040355031012800751204401d202d40c1190707a0070304c10200c0701450684121001e4662031700300c240e6401e0401c401151031650080a0b140104810001120400d10411400c0c25002e4554010035503241800e100c0002106081204014181840441c1c1d814420000c02a02c20801c03514101c48100800306049280500b20710800790014981780c00407800b40e00000040007039400720b54011121566500e401c0b9551007044800780d101c01e6100ba84085140d0b170b140c0060400f44d000910114071002c0026501d800c5441c1034030300b200943d1184100205194150180b201c1900c80c604011618a141c4002802850a584915000b440000000400982000c080043d4001441489124084483d10003035529080b00d0307c1d401c051b100b10114510315610600a181c0b100c0d80c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 234422517 1250 234421267 234421301
    0x909030c060a0b0a03020904060902040b180a0f0222031403090303030106030207020a0b0406030212010f0b12091c0801031a070903020904030e0919050f041e080915030f0a 75
    0x190b04584000100184031031264400c07120200000541c2e158101d031402240640000240c4107140d10400c021100c20480e0700380500c010322a00380c810304411281079800703580101c010411480c0045044002d1060341c80341444102c824000da070725100e12591003801c0c0da104120414203901c082540654074000c044002d98103500800040c003807180b09030050400c071031000c2c000b5506c09480d00c880022a801c29004200002e40c0410000104460f5031021801484420150302d2420305040c640c230454481d05e030707000c001d1143c40004184003400400c80040c5015249210200845141d00010700c2082c0a220030390700981c2814003000c01164003040d641c0241c0194841c1004185543d00380004601c0050040e07042c0a5007640006250700c0340440a48501000c4a0840c801803c1901c035070b0449601401d40710311a000340040000159000d00c449505642661b1800c010340c006240000326440303580e44003500b111084414820030481c1c2c2018500a41094180c004e02d07036200e03203035802101c00300c2d466003150702 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 234423767 1250 234422517 234422521
    0x5161b05010206100332011b0e0d02010912020a0e04030e011709100c020c0312040612052403030d02070b0f070c0f080a0c081209010507080c09100c050609060103020909030c06 77
    0x10040100b444e00c0c0e0306d4442c0139072190300002e106400c50b140ca20285d194840700c04441081a13901c12a994003864044941000c240c0d03c40c7c00003400140280901180c040f0940311580a542d64202d41000520800100e100c0e03074a8240790041145c1d004040703841c00300d10304101400340300d10320703e041c02d200f800080000c10b002100402c0c0c0c3e4019091070b00201c0250302036502502c41d6030b20b0500150000040349005180c0e10340c50704070010401c0401158122034580741c601809418070404080f500c81070b4070060703400400340c01000001d05511440c0b2100009910005988040100c1d01c01c026124505030402c004c442d80d55407000355091a00c0500c000d00000a0654880c00070384000080d083c4140c0601e00141700c4440c1c2c4d84c6050250744990b0002d12403010744400c08c00030050900945500540501e031020740f9080c840a1b600b864001c3e00100d510a003d958051804640314905440aa541100444d455810311300c00081e1180004e00042c2c0c000c10640c80003800e0040008101d40c040d0b00703800002d05240d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 234425017 1250 234423767 234423803
    0x1403030304031d01030605030d11100218041d060403030605030c01080903090910050604171c0f081b0d05040c05040506060a0c1707080d0f0b0901050105161b050102061003 75
    0x3011400d03c03203418190380303410104035034a04001e00b2021541c25111108440045040341d4038019105840c5030407140100118075044000d601d410410002c140d5010981560035004031858000304041c030b02991040c102003206043d456002402111300540603581419542c0c5c0044440b0b050071110090103600400005145040c081d2020707034410052180c10712415110400a00680d00640c450280031035042c11000d4510000c0c0101814071140d00c9580010080340580038040d680c80c51801c906200c10140081c800c05107541a80d0070071041c182c1295924015859164021714003520141c54820300c950001c01c07541000e2051a001e481e008190310300b49a6403180c12680001c03401411214150320407031049900851070080d150304c80c450001c0e039413142803181e04a4221424001d0400035282440c80159907a04c84a241c42d05441c020310f042969410308021081030100b0800e0000d28035420f01d1080380b0344a00a00300801030ba0000d030300342c64444d180d01c01e1000c1d64400313500029281110f40c0d000030b029 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 234426267 1250 234425017 234425057
    0x5010e060d05010e0d0c110a05030619060503060420010f230f0304030903260301032d2609100c1a010e010f060c032003130b04140303030403 62
    0x207202d11030400450150189070000741071422040d14071300800c4480300d040702003000102004030454010341e030f2440f145141c07000107941c9140103041c428460f09520030a040e001030941240010b001c02600722070b21801c0610b409042d4000e41c0c1e1042c410b45139003840814031580b080b40104000c0b0503907920418600c03d040b03042c030525050107440420226082054031300c010407403800342d0b00c218042d85821031004c0c83d60824428071005464000981c085406038003908404d1941a80c0c1501d400c1041d030880b0820601c0c2400c105070611409001000c10020b42c81c08120703442003814070201c2e1003100f00701114440c0319100400d005440106034080701d50712104c50094810000405d00502890040b82190800102118010803e07040080e040171700f88014014259035100c0324005180900d40802066240e403401489030304d8a1030310310522400e511701420395400400548200c0038200d400464825610f1220031a0380e0301c148140e00481c003d0640e561503910700403003620706c50394042e2110050303600c4c25200300803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 234427517 1250 234426267 234426289
    0xd0515010f051c050a0b0306010f0608070f0908060a05100f0b07060906140901020316050304021008041103030a05040510030b010c06090201051314040b04020a0e0f0301020d050f04030e0405010e06 86
    0x1450100364481030010f92514001d00d4020101c4c0310740002c10090641c141401c000d0140c01185c200d900a540c06c0000b00d40c40001d060380140ca03850540c5030306041400c2220991600c0c1e0100300c10344078080501c100d45c88141d220340d0240d60900c00001d20155110035130341d02c24409208544c1142024007071000401c03000d80156280a01c540c00010750148290411480c481c020303120450969408800c1007a0100c4181d03151400101e10f0414030700311314099000440e5181303100c4012003000304d41c5001c0750400c08405c0342d0441c12032004080e01d440302070002c0018001d0300701744a01441606041c41c4000327068081c2c4a082584130069449249088050b15260040c00382c00d8003c03410801b00308603400034200c03010181d0010381144040520001c01000402c801e41e0b0300f0901c20340c880e40c4100b0a07800d05980000045000240c103480800b42d0650400000b802405640d1101111074140001c00220301d8031410981d200302d1182e280d401e442440c98050000b03c541c240250282070010300007094141c907010302901 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 234428767 1250 234427517 234427537
    0x905150c030903010c020d031410050607050c1201021305120303012610050402010314160e0310050f0610030e0601181b05091201050c0415020a0c08030d0515010f05 72
    0x346020b80550100342124030080c0000010382040381410070040d80f5016050580b82403e00a45040c00c20254540640e041482014820500090301c0010040103000000714400010842209100f15200050103035201080c15011b0328042e640204851411001d42654191444c00441c210380c03c6c142e00080c00b441d00764510181880343d26000000d440100070b182c500240d00721001c101c1d801d0500c005000d0303070b444680f19001409072000704440e003c004659541d0030020ba1030070510040740070003c00e007464003da507500750b058186010000040c00c102da000340500b00941e2510010451210101d080301c207404c40100e65500414010011840b164598203402c041488001640203803045455140099955105010540203d0860518079040004841c0050814003d001d6407600710500c040c01d01c0f640c021458071040b00c989941d41c25100300903140380300f54052094240c0c80c1d118103a881c0e80360010b641c0003001c1c6090078009008211504904040031406864039851001000429078598110190320 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 234430017 1250 234428767 234428773
    0x1803031e1303120c1505060d030e0f0d050c01110f030409050c16030201060e0c091c030e120a061803020d080714270406080a1407090504050c040b010905150c 69
    0x102c04100709001601d582c2c245511200c540340e0346481c015000d071441030702041034540752034100210368440900108035a50306141c00d08101c120000028503081c0c030f0540c0c9030f402c1500400524108000010189807108098803008120461560700341d81d81c562040249050b504140003c005c2815503400050300071440072074981c00c001c048504000b907503100702800d50050b074440c0790410203104840701940d008004e02501d50301e49002800403c2d0658005100441038040030f00402060510030344100c29510740003040e082c03100002d140416a5103881c0070043c0ca5440ca09841481c066450680c08150a03915401504151010110989016500902c50014042103046441100c3c3d81c0c0e1006140407404400340e031502502005a04c10024004a801c0d03008034949803050001c002c00107043c461140e80070303d8800842ca5220b60b05400c2044503841441064144401d02041020129041c4001081982c040090540b08401110711008070b10805400c0072000ea007400020b003940000340b580003066411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 234431267 1250 234430017 234430019
    0xc16030f0b040503190804020a05060c070b130504060602070e0106030216021e061603180f0e130b0103080714070b041503141312080606030a0b011106010b1803031e13 73
    0x40c40315402d68001c17603140041c02d01000c00086161101090b00a840141c2d88142498505600e00e9500d480a00445100c0321000c10a400c0703000602018001501018005006160ba20314001e555411a4001c81c0b0701201e03404008119103101e442529600b0319010340101c0c51002507000d100c6440701400d0b130030310704114000481c40c81d920780c84001c015102805058042840c05810010700309582c10b203a120725020302e90f02c200054400c640c84001958412221172390261a900036402c450800c00380001c1041090364000401d01c21b02c10060701c55940a0994105c0c1800a604480d845841c28000c40c40d042405005c240172218018451420092050400003011005078020741202c10048580d02c0b00c265400d207000042020460400032a40c0441c28098001e0410304001890b030301000740402422a5111000c55440e03100f4140640254041e901751422561101d403840b120b680031182c21040181d06a03081e88a6040000480390140c07010586800d050a0100400145500800054180c848110f00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 234432517 1250 234431267 234431287
    0x902031005040507080d110d030509030c07030501150b1c180f080306040b100e090c04030b07020703140a02010504050910032102062401080a021e0c16030f0b040503 72
    0x2055a0150f802900189982803802e08414034020400ca2020104400b8201840c00e2850004e020705c2d040565080228150b507c441c4290310b503018030100c8110034402c41c9400002c0c004103510801028110001f4480f03000e8a5861000c1e06201e000d0303807074010000c8007014041c40503850348a010032400b01c900705140c40100e40c840d6100c0388900042600c400f040001031103000d05d001e205e1500c0f0020142c41c82d1410301202c100103001000039032a01c5005d2003d0000040e421a43c900c00c0303d0103035038803000c44c09660402d64002551460300c0d003c2243c1d040e8035071036200818034002426100041d4140d4034146030a060030144082420080c200203204011628040002039519551890310801c442c9010300c4118190b800910704107001d454640440496481e80c112307a0b0205404419521003804c18034025110040070380000c0c40303181650043c0c04041460303200c0c014000f00040020100310cc4c00c48001e05001078002d07407019210b2100030400c90000c2c00f214002542d00000990240c040c00079281803e06a138 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 234433767 1250 234432517 234432521
    0xc0e03010e0325020303070303020a1808011e0e03160501060b16030e0901051c0f0b01061106010b04151103070c03030e2e050d0603020a1212020a030c0609020310 71
    0x300c0715081d400104a00d900d00c5030090fa10034941c88640d41d02c000d0a681900481e450f481400006820503400003554055103011300c5840700034250108000200c1c4e41c1d1805050b008041c41480060303090350010111100020500030042c7c2802c00e00c0186240011040b228001500c00100840e065521440300260300046030300078109006094000385240c0009150080c07910061000c540d1003101008010300075912036a1485501c0700c850002a515402e003030400c06040031a0318001019881168008910164002108a085c1000e4412030f112030f600c0b84a0650035010368000e07130307540c82c2c806071800d0140c40c40385a100c00000c8054050301c0c900303040c5856000d04400140c02c146c01050564542d0781d92404e041e070b01d0700d60040301c0390404410f5401e1982807410380798130a00e00c082080008260307400004015404040155070081c0700f414841c0ea0740742030860080345c005040d80c0c803040b20350110b0b406600100301170182c9070303040d660303180b03203411a41c0ca20004004200d02640c051142042c0800307031403103038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 234435017 1250 234433767 234433781
    0x30e010e03032e3804030b180106060e100c320f0d14070203060f09100504060504020a0e010b30150a080a0b01120609080a0507020f090106120c0e0301 66
    0xb00400b1a0158200d00a04011000540b8440190b81601802d802c03a0180344045c0c900352030307000380c4002894a0741c100b00c0070f2661051810090a501e002000107580750401003041c3c101d13005843da207890403c02001500c13402070f2503101810f0301c440004142c01e007074a040000001c040c1100c2d00d0354140914550200d02e0140210001c40d0681e10002501c02c0d0076030007100b801807200c10504c0051a2030410750120380c4980340500203a40c611080d401050001c0000c1c000c3d10382d200103c00c0f0030001032519051042c00703482e06413020b07405160200c501040c1d4403545c9503400c0c1a90b46413400185040590010101f07503018819400c031410703a1002c1c16a012980c9c0861440c015400c40800b144102c0002d0200710303800040d5030003280d00340c2c4142c52000000f42400030ba5030444103600c00c00b1003604024105200904028a0700800c0420300040c4084400e8110002d000b0342802541d421040c000740106100d81204e080c01008081108603c1200a00c2250f800c241c52030350640c80d1440d030520758803021900f5030341300b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 234436267 1250 234435017 234435029
    0x60f010c0507120302120301060f031d010c021b0a0324090c0305100608030301121e020303040b0d050f0f06041d060a090302250e0c0708070f0201030e010e03032e 71
    0x1804043c501403681c104140010014505040340c51549890806001c60090683c0b5900381620b0744100f1502441c01200010680200c3c03009001d102a4540000d480c0e10710410b41040b6590004000c0646080054ac007900303403030703110321425403a021071003071407803030740013a503040c100d40c544030040342000900c1e00f98010300a62050008050508080d0000d0080e107050703405c05007071036001303000410a082c080d16500301c01c1d0760040584071201000700d40300d119400414102a4043c440000e0005948086100616a91002030020442d40d29049082400400c045d18011201e420142c045407480c0b40c1a400131503800303050058a40c012400c00f540f80c0c24100112000c90049035101c0d80041490340600c845415844054000316802c91400814810034107240146500130f010034000170000340c003007002c4441705a00b100241c0e40301c040e2807800c809003074203070101240002d00b000b00000e011401402407002d07541d0104040c40c29a51000007218030381e4100c4000000d80c001c0074410800c02250708400d5005010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 234437517 1250 234436267 234436289
    0x60915060711010305090105091b0103060902030114011805060f16141f0536100204050418110609010309060207060b040c02060705040303050a030905160f051206060f010c0507 77
    0xc0c4420016049801c01005541b00d039041108102c3c541c4004100d0070000b108806184003109100e0004800902d83d81c0c001e191a03601c00000441c0c0113001054640005009a0b5611824008013600c60401c410038410103400c001c0621101c10004003100180c40100004800c0c04402c03103003070311081000c49030441d458080760031262000d00311140d410081040c92100b81020300603800c0c040b131111183e121584c80700c11301c1515800580f4000022182034000049844202c850950600308440029440741c4aa40c0c844c902e010791110000320400b02c01c1d0455038000543c2c88942140c00c5c18083c50740e211229640c1010343d0303070303a190000642034409004036a004003000200044901c0a1108540341c00d01140b055502c048104004c140d07109049030f0a60b903151415688400d003001c410760151003900c00c010010f001e4000c01001400c2d818000f80119500300d800d0048480e92082440400800e46400b0030701034104400084503420140c5000c4aa900185403100f0dc10103141c80e002c0c20001da60304040840c030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 234438767 1250 234437517 234437543
    0xf021207030608150c0d0204120c050306010611030a0e01090f0b0705010b0a0513021e0c01140c090d1b0902040b07051b09130f08180a090c05030609150607 68
    0x640e15102c1c08000d003090a0042103c0d03012000f0365188910010055001c00e0030006040e5002c0c031164041d00c0040211402c2200c64507400d14041d07010300b000c2c2c020b1030300912555000240c1d1070711441081c001d41441074051450003c8060084501d18400c4590505010307400f2000288a0903141c484801000c11551841d11594540350071800c2d0b49034492a00e00c505a0004144059a2080c0f00c00c98650305190005940704c503083e04180362854810002c3e000f403000800c460340f141006401c840c2420280c80704000c0641d840300c40302d0860b400345200052b040342880350114000b074010b404200080000501d080c0081da0b841d43c0d03440c01c0c4e030300640080c2e4442402003240810002c041210715002141a0200095020001c002c5088203000504640400b20384d04080c9050182d208070303542c11190440c1e255030b5640e021f81d6242202012034000f0a000d0310041d0720001c1c1030040b5203c2c0c004901510358440d45036450b0700701046003400c030185c045da41940c6411241480c95880d0300091070103a200d44103c00d110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 234440017 1250 234438767 234438781
    0x9010314120c101109030c01110f010203040f021011120c010612030f090e0402011e0e15031e01050a0e1b12010e010512100e101425020606010c02040f0212 68
    0x203582041d0402440b902c2c14046817550780ea000c40c403961048001e18100d804401c40c850828030b05584a400004036510000900003888142c501d040340d02030003030715201002048a501240c00b0100c80898083c6070300301440344030300e80c52181b00404030507403c1300002c54403603100e0301e003c0755004401900b01c001c40c2c040400c081601c3e03080018000109480c26000300d2900c0c107500003074543c1307030b224001c800040c0c08143c3d040104e90043c4402e8103d14000307015041da2600a24490072294010342ea005418110200c44c001d080000b00c400e40e050303803406000c0000340c91a1020039802d5803c0a49512907203450000083c03054080a03000d40884524170280c00031035454003801030950301061b0081c85c024a208805c12400040000b01710090010804002507845000d0103064105107400d403c908166017004d05c140c0c0d100c8042464140265068299444c250044158030407250b000c00324140056080b160000d6110b40c0601a10688180040c0001c200b82858202c040102e034803100c3e801c415498150148845 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 234441267 1250 234440017 234440021
    0x10f03050d110606102a060501050607050c0603070c02030f01051e091b060409060905040b07050c0a12020316030818120f0711060301030c090b0108010509010314120c10 74
    0x4070819041a112094a070840c8980f6081c0040c4100e004800b03031101201c215100d40c106031480000207909007000b440040c1c020500314807101003135030b00b50b0406002058910301141220006680b00c0e000340440341c6407009000c2240c0004107070500b40496041d400c00981c805000c40020b00300e03000000115460410390010125500d00765000314460060308001c40c1540c002040072031509945441d10700c09010000246040c0708980006110600341280040d507a0402d030021405180f0941043c00140d6400390304403aa405404510341099019410348404a13070340000080d0b92460b6407064170303d0400d01c0d9002c1c0009000340b0780b007100010301ca41c040000c0403026079503540403401c6402c05010b00711860040d01c0420300407514101c1e0313420710014810040100b1640864050040034051b181c8035a52410481c4c414080c0344103500480303090421880d06917118503c224161140105004820b07425a11031020406500c42c100e410391140ca03003000c1c100145c000103062413035804002012002421034194013 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 234442517 1250 234441267 234441283
    0x8030319060b0d05150a08030d06140a030803130f0f0203150103020108150406030c060201021c110307030911120607120603210c0b040303151d0402040b01050d05010f0305 75
    0x40440d00d040e6081c00030b60304941c22907100c2c0f1004000442c40e611160501c00061810340d03441640682107a000044603c80400644185d19902008105035980d680b509600000002c41080d4804000f00051000501c100086c5800000c0384001c0d0b09500425602e0030741e01c2c0ca8805040e1a408000c50fa198118a030030042903011072610b640c207001d507524541c0060300700740c00903005a00b035121000600784540c5a5511060055030412007220845a031360308003900035032040d001051440641c0100c07109c2031003d0b01070340074200c400404130b070b1440e61080d03c218000d05620f40b088508480007200c60301c2c1e65582c03c007500d210340c904401800f80c50809010103402d0000e1003e40c0d90300c2c541000800c10214581426941c40044081c442103840001100300311400d800c0303003000070506407103802484189641030740030b61200100060312000442e2203d0b29050185010709104500c010043d0000d001420190071460800714181083ca042003903002d00902910f600b41c012501d01e0080807010424044d0810103aa = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 234443767 1250 234442517 234442561
    0xc1509051003020a140c01110d0f1b0c060b0105090d0605010602010c0e06070f0c050a03110a120f060c110f0105091203070c0803070903080a1112030c04050103180b01080303 76
    0x1498000301c4c0f140078142e05524170322486085d0740455061310514083d0072031400b500040d10800c1c2da035220501c4010040c0440381682514130300d80104400e4003100038101001c828010707165080f201083d55600d002915040a4550401405000140381d90303c540c40441d6290344039040c08540b542c1001030090854400e009808100110210600345d103403542c0c0304940c04d55400c04040303103003c440b506000c8001c4d04581e0060380c22022540d00081400701f80c1c008248000c0c2c0495a40c130794580d6507a007145c401a50142c000d003062140442c4200042c80c26841801c5c4269281407031041d08000394561f50030190f1007200d456040e51600200140030303000740031034602c405c0301396201402d50601441c003c1c500c100c00074008200b55400004260300328010b0f0500d0000315031010203d40d65010386140104003003081d011003407041c03007000c045200301e040d0031066a01c521062003095050030b1404004402a20040070140b410341c0d12002d42c1808500d5000f41c4c2ca0190500c180210f5890400c0304006c018454911008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 234445017 1250 234443767 234443771
    0x11e0e0c04020a090b160f0c08010c050418020a03110406090303120908031602160906031103150604020a050c030a030617030309150a0b030607020601180203010b160c1509051003 78
    0x4070940da0b0300141311500342c40886440945884180070041400080d8043c081c0501981d10319550030230440304501c105460406000b8018141c450a0030784007405580158000e002041080e00d80f800c3c05503000d0961035415242c0800d42141c0c1c60300315815a401034002e01c0c000f950400c3c051040c160810350707944900320403140070058003800743c8420045010140a03807060035071040055288a04c03c0102c4e40f14440c0700844000050754501510008016910089440c8250080f03040d40f5840c020450141400301070b500310361140c0d0b608040000035070050300840309110f02403000500e01c003003c00c040c101d03d0603a5100001c0701418030a000c12040c4030200c1c901050389c0300704100101d0340c5010898104c442c050040c180555102c07007200710080d1440000d0290180314200070030190b9540080d000d812a4250b01c2d401c50005003020084052384024010b4055140c02080111042c500110b9201d20340b82c000c800f0380c088651034201c50003250b0800c1000d24001641010300b400180303050040e08622140c94202 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 234446267 1250 234445017 234445027
    0x7030c05040b070b06180f151002250e1006024c050a050403180305070510050f0a0201051501081611010608030a050c010f2705011e0e0c0402 62
    0x40c0302d11441000c500800615030880880e65035150644011040090360284180d14508004c510b00d01901c00c8400c40203421940c401e044c030ba0300342841c02c0d1031010319a6004c0e140c3d020300362070000c18405065496104256a20400042c1502e190101c140110658000f51203250701d0148002d15205900007072042e883c0494030345654810500c1031000c034051018089040c02c8685001c05450541801e22115083e0304120400080d0309540d0f1296205070710a40301ca03d0100ca03000e6030445448801c1c00700411a510440b028400c40c03524006032101c1440e185892454035100118001c800c0e0000800c483c00750303464400f442144c07071b210168030954480a280c0058035250064000a43da001196094180443c90b00d00c800059400e4100314040e1502c0300480c1e54880c5100c4c001045a0301602e40007a0651814a1401c2c200e189400349240c1000e140000405525690b050715001e140d207a1b504840542d6550200d600b02040d0400801402e9070000c00014907840b00a442c0d0306000c0c049002d98455441042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 234447517 1250 234446267 234446279
    0x605011806030b0d020d060f1409070303111c080f010e040b0703020a11030a0e150726130308070605071e051602040f06081209090708040219060807030c0504 69
    0xa030490071150305160218060384060f0201e20341540140000e5084078030a10307110180320030340d04482c2815064400c1044011410b0a075480c1c5010142c840ca5030940000208001003807245402008444041003a0b410622409414802c141c1e81142c0300e901103680c0104000c504110001001c0c01805900d102604c0e1349410344d900c07059540002c00070018140e005c5606c0901134480d43c0c40102141c285001c072a503402009074064183c140b140c2c2c100344101038001c1c20781e0020361580c2c19a032049511801440c4860300b1030341c0250b0000b4481c13540c024003001c00d002c0404050810b241d080011740c0034880195a40c1d0043c00c2c80d00545500426100910065160000791075402c4030303e02000740964603015450f103c00ea00160400c8080b80c4001e0740c000d00f001415826003900383c0c40002261160b50131548035220448100b030107801010269a40f21604a00042c905402590282d612a2000302a08203002054400d848119000c0d00000000742c001820491029018822103c0620311810901c1c100b44c43e00c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 234448767 1250 234447517 234447557
    0x6020303150907182301030b0d0b06130f06090b030d02060106051308150106170903030609061302160c090612080c070b031e2805040305090409030203030109060501 72
    0x30001034091600c03071000800d0988030300143e03443d204001110200c2d00b50b0b01c12082150500403c200245c501040186a4056009102c0e007156090701500d090643c078810f8503140600000185178941003030503070101410fa21402d2003519070745540100002181c0307007010002c0040b070310a4002c0038041e07800000054040750300010f0f940d0446540303141040d91500750b42b20390026400a079100004da817041c0d40001c0701404824001a060b00c038199030700c04014000c105c0705140701c8c406644030360840e0420400311300c1c41d080a01410380d000310044c0190518801d07140d10f25040368441c0807003100e81d00c1c11072030501c00c2100c070000e000000d05691030244083c50500f030f240c0c01c18501c02c02c00200b4072240001e0280e40c6410900100c4010802180c4180e202d1401900e4503091101e003803100010785e0b5040000400c82c400c6000100d60703080340314a000e8591034949035440e0040030054819010b00c1000d03c40350882c3d81e0b90303016411b0110302c26800b40d80c9a515000c0d05c1c43c1985c025820003410300030300120010000c80382c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 234450017 1250 234448767 234448801
    0x308040c09111b03160501200a17150a090203040204050a0605010212072108040303050901150308090a080d0c0b0a0504050607080a1103010608010e130503040506130e01030c050a06020303 82
    0x4582c14400f51804490031500c3d41c840c00c00d42200c1d05010a01070014410198882101d00614240740c540045030110b205440d0300c074500c0c0010200d411b0840c5000410019012113074040502103800703040c112030100051b030581181c0d2100c00c929400008210440c1800d008040d00f103407503004280180d03402d2000103520b40c2c031070526026500c1c0d408907100d03081c0408000c0d00c1004841149040141ca0340d17811009140000071101039000c80d0400001c504e9429052160b03100303030100b0341c10b1090031504694560900c0d0740400113190340b0505204000c07815110030701240207000074948400b00c0300005840d04852440b0002e05071407145103050104004504081401a801203035813a02d250b06175a030504a20040403080440030040710702000200b40b00d504403450b80d05840407940710b42d40590362041c0203051074038090f00c0102181c00c284130411160604c0f0000c0c0c061340390303014101860241c0b41c2c1c448110408007688140c070104c500090401c0b0b141042003140001d8440c502c0a1455481c2080c0080094600d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 234451267 1250 234450017 234450037
    0xe03011514010e040510082406120f010e010b030c0306100603150b07030e04180515100e101401020a200111060f070212070312050601050c0a0308040c0911 68
    0x11541c01807020740c1c810340342d469510320010001c00c104d00341612003d41003500b0f802441d10500c502d9598650b000c9a0814148078984100c600c046181da0f5a8140030307250a00d6084d042c0c1620410b0481030b120b03982070140c000c4004155000159041c3d00c90105441c01a41f884030314001c3d0002000d00c212641c0d00303006032040e140c1c18100400c10180000f8200d40d812441c0d8441b40d4640404108072003050784c807a8441d15188030032541417000485040708001e072141d05d468020415031003c82403080104220281e1075001e0740d121650700c890303582c07240ea49611407030488076410001d403000c01c14040c0019024041448101c280300070841945a6603c102c01107158900d000841d580d00028081c5680c451901541480008416944207041c403c01000841009803880c1001d805141c042603010a081002c4e03c2d007250305035461444107030302d60351080010800032f446541007120403c11087c1c0d41e2810407450310b0080c440d55032044603190604150915001030741041c12000d0420000002c43c48204050b03466403c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 234452517 1250 234451267 234451289
    0x5120705030f09030c0a030605100f050d1103010e0a0302060907060503010608040f02040b06281e05031e01150f0206010311060306040b190501080c0a200309130204060e030115 77
    0x420300000385c80c1040d461903143d030020304040301100b0002d140d00090300420700050400c81207034071000b00ea50740302e03210b000d86600609002510f9002c80e41c0c0c0d42d181c40c1e20310f2000d000000e000b1441100681404880b140550160784868207018000c902008000c00400c5180349c1242113505040c401400544007a002400740408030030f40d4805e558441d407103601011340041c40341d41c0d2021504604800c22050704189131002a800d01e4180e0614090600601c0010484e001003069001c0040c05450940000e8800c900e000444295031020344049801c840c040e090034031040640040311035008000300852900b000071900329400400c00034805409243c0000c8040b80c0712030701d95480e0360110b001005440c2445510108885c01c5828042800001005807482039035104c0056071400d0b40d00701070b840341c20b08082c0056044240010645c80f03429401d00603101210603249464020400200c044500703080b01c0416507070014080101541080074200560f4066000384038030400d040b0001e00000c0c4504c80e18503441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 234453767 1250 234452517 234452527
    0x207060807050d02030709090b0a06050301170307020a0806100f1202010804110406060f0e0109030b040618320a0b0708060604030501060b030f010611030423040507030905120705030f 80
    0x90140c0c2c152101070b4070010f030454a91420007001441002c1c00d11032100e016103408000b415138100003698100742c988a80f1317440e18503481d190800000c2d000b1901d160341680418045000103030349410203140100920002003400d410500040e04120700e00c3da100c241000d81820f0200515500300440222554090a06d074107266074a0078101c101c035031140440ea0b80585031407004614950000012080d0b040b16664500520400e4001500c2240e01400064010364851000400142603504220044040d01408c0400d58000f5514180481509274a14410040c1c1c4000035940c641c034144142805143c000092249010640320302010071000b402e80c5081001140002ea010384070002100c0003140e1250007000499501c03108a5a5500295a0501c9040c07220b030000070018400d1281820701e40032840554505071414508d203a000407400c0b4160050340b50010415072960340c130b100300391040b0016100810070141301d2500c613042c0700340382d03841400d008000d00c84100820307400420303030f82c602c48241d0006641c1c1d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 234455017 1250 234453767 234453781
    0x60603020f03031306050d02210a0f020c03030112030e061204060c031a0405091603050f0c030313090b010e1e040506031f1104050d080a09050d12180b0406030b0f0603010602070608 79
    0x10b0f00c0b41d801d254110600064a541282401c9c4100c90f204040c0d01004014002404041c1020b0348107100341d2401a901c2400103105e021900c1c00041500c0c0d2103030a100810b000c0308800306905400c10b90000e00f02c16064000c010a104150180c858103a4440c5400c0148a00480c8600300c1c20301120740031401540e82d000040c071654800c0000f0190f505680700001c00a81c6d880c50703c2d5540ea4080d1003040d1f81d6000717030340c00510281400403e84a00d12242c030007419080d03084c038900d03100030f000d401141c078100140002e426002d07845412600d41c1740c0c0c0500b178500860984145c02e00055803800750019020354080b41d100b407900340030941010f40c1642c460b81d000c50645941341c4581164011600000e0380409103001c0b6000308003d440040c400c107882c40e101c01900e240d5801c108000600602000f034400c10000030904a01442028503510307401c01d00c041009116262086010135030007c1d0030543c0401c0c0e882d02003455034500821905200a03044514038915810454001c0d2100d1491040906000c03040c000703d504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 234456267 1250 234455017 234455021
    0x40b040807061d0a1b06020c0904050c040203150913020f0d020102010608010e03070506090a0b0133030c020705040204180507052101050a1212081003020904060603020f03031306050d 80
    0x100009141c83c00424041516607203812070a94211409401001025032650341000c900c400c0350099009490a801520140030681c4402001280c080c051440400c80f5541c0310720146018030351902803105000b0040c802d201c44503402419a041e201440c420303103801a40c4010002c2e14443d0103807000d050309482440103034098441604001c2c0154240324506002460000280c075246010ba411580582c6691110741c1d1102008540038011500c21001840315003540140142011201034a184a007488040111061408540b0b040002030701e45a04241c07042d07041003541d01910b01150304501d400d00d446004201c090010404800050b1603c00041c6110f010b0380641e01543c100b500e141c480d8000d100c0e540c81c0008000d006281c03088040711008200c514000c1c1d4812100760340040110000d2541c0303001030b107210030014503d800c80034894102000584503012000e016134810301d8081000c0f419071040104d95132040150034000d910078003482541003620280702046420038140559503061034960740c80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 234457517 1250 234456267 234456281
    0x20a2301120b0303030c03040614041a1b0c0604200d060b0402040f0315050c160b150a030503090f04020a0507150f051311010207050f0f060706150f060206040b04080706 74
    0x83c0c503000100800608072038180c0290b00c5a07110b90360812030500000018061002c0a40d400b03004840b0504450003108500740940740c102d008640c0e00c4906e050480a1201140c0c0104c0c032100c4907800540501c41005480b28038081c0d86004807440041802c0081c001c242a0790401038041d00040c3c58200d603c846443d030b641294040c0042e490448400c544a040000700101c280340e041c0c80b841c0c54403001038841c00d182c074282c500c0d00d0b0f44414104080f01054450360b10300fa0018140d0160880c0c005910409941e0f02d0310542c000718850005140c590b40c888080200140380c0a1543e80030394010030080c0d0059500c00d007151840380d40403045501c2c100020303804c0c60003450140168042c9600c3c02e000c0c480d00d0129960348010701c92290840d168141d40b110300498554a507445280d4004499041c0d00d805c5240140440a2010f4068031380c0b41031103071f6500e4140c01c0d070714440342e48600c000f09141e00740080421160a00003a04503070006020604041e5910800c2c0500184054500c00c03001c81c0340010814a1381001c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 234458767 1250 234457517 234457519
    0x8160e0103150504020f19080f0103110a050603240607020303031f080d0e09071d01031d1905060a05070f05030a0207020306090705121c03090503160f020a2301120b 72
    0x5444140c51188461035600044024502d64881c003c1011f54911551045110313a01d1040e040300c0c2640b86944010010413150b44041d0322150b61400801c0c1074580d100614410301c05010030044c0c00303030202089544055030f9100c3d10300641040041c0c0c000760320004100d076044034255000f00c0c0c403001543d100502c10000d41d0400703201c50051aa440e2501a07100020142e4171408a511104a45030a0002c6d10103c200c080d955044070342401a00640f50301135171051344480c114031030854408480400c03481c00c00b000b000f00441d940c045010164103100c010000d03a030740841c5801c0d04000b1070a107690007501815101c58041d003006000000144049031030b0b0191044194054115611810240c103001d8962005011f60f07800350901d000e4403131140500051001c188500681801d03807509020a080340a0048058155072a10003006907462000c0165030740c490700c500a0309850540c00c1c2500c100f00e0303060500c1d4801000041400c03003602d45004c650403c2c032210391007403c08140b8080e034031b00c88801411043c040c075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 234460017 1250 234458767 234458771
    0xb070308060a0e0702061e070c0206030c04031a04210210180210030f0c0203040501141602130c120204211b08010b1201060305060a0f0204050904080a08160e0103150504 74
    0xf1113400c6400003003181c001c04440c580d140307040e80c4007960480711010454007000000d507110503040150030280021508050100d803a6843e00361a0b40341c1c9100f0991000b14450308a04620402041c400240e0400036028034039901e02c00c1e206500c900c000d607605030402101c5d4059903250303844461603034100320040d00b16602070f01c01d45074000e0214002e0002c1108a0548403041e0070000751509043c4003004a0702a075405842d075035080103401d01110301c2900400039514512038092144409079803520310f600c0318800403032004500d00a001c1c000610702d00e4a4001f944820b401404184200e642141070900102891103481040d00c0150500c0c41c8048035240301c80c110440c0ca00b10100e05c25030b0642080b2071103441642c042110f200514140741c200d40b502d210142c5a600000b0124507128035039041000c2c80102400090304140d100d40c00629482000d8074225400280001d9080318103412021496120402c0d00000200b01547c0c003014041e050140802810550b84030509030062014041d1788000e060b0251003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 234461267 1250 234460017 234460021
    0xa0f0603150504050c150d0e0309120303010305011413080304020103090c0f080606030a08040b0f0d1a010e040507120e242403070b0715111e040b070308060a0e 70
    0x7401d00105000c0c2c8080d100c500450114002c0c03810102110403c1952040407545410000c001e028018014007600e440d46001c20070644e529544c2c4c28082849032000c203009103540e540340d0720302503003114441004401030080901c00c00082c010a401c507954085d0b0010701081d96a40d80303200490080120f1a40103110400f001008510002c414481724159101c40c021039200340c0341c42040560700c9041140081a42c2000c00062208004080c0903221a44543c0c41c42c50404588410361303401c1c4c5039101c0f554501c1c010030740c12840c603a40c3e000b1010003201009270340411150034400c0380106450014802d1642d19921984242d01920741000035030301d9412220000328016000041c2800b10880c20f40b8403040361084103011000055041c141c030b0004010040007000001d240c1180c0349059001b40d4402d58080c0903050803450404846d000c1c0c00c0203600010030080c1d82d41d000e102402c1c0c00813840f01c1034145c8510180018030070800c2c480125509281c040c01c00a0b0107554442c00948900c045401c15020110b0500c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 234462517 1250 234461267 234461303
    0x1e0210060f06020f0c030627010603120813030e0f010c08030906070e030712170c01020d090203070602070308070b04060b0a060513142409061b010c0c08030a0f0603 72
    0x1c06440703040d829a2280340c540002107a0b10b04800704a19455006100031601209420150702e65040800000300b01030610110700c182141c07a113074415504508072074481d11002d40d0180740e040d400b2100394131040c40d04c10381d40c600810006481c901c3c1c500550b4070100c03181b040d1303010f412036001c4c0c00d0780000069940d10b8078400041e20341c0001d0350500b006c00c1c01000e00080c507180200e514002e03600d90610201c44400395880e402003c0c60f04800320554003e00b0030242010f00c01c00e000070110903c81841c003040e500420b04c149440e001c0c07503510070790448d00300d07140c144001041c1c030b0700b21240a074000c0440f4149465904041005000d40500c4036407000341d0000000301030b500a00078200b14052802c6075100c0c15540d01c4a44120700182d13102039400710303020b86603521208400c004586040e0205140c24100b14115011034ac0310b0303024048141c0d103075620001a424844c001d00030600c0044062a004000d4180d95890401d6808081c0400110320380b114181c0d208010340303611005c011070300102c045400b030107004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 234463767 1250 234462517 234462539
    0x10090201021e1b060415120b011106040809041b0e130e0c0103090c051903060f09030f0c110301060b0405040515102d11011a09061003091704180c1e021006 68
    0xb0b1fa03880ea0641c00c10410704400d6000b403c1c40d050807062080541041e640321317030395001c10758040e041ca55441640d4200b10b014500c09441006040d2403591503802d04281d00c1d6041000f03180b24904c1c5506a0390901c02c07518445000401d007015058000c0c00c0100350121076152416501056402244c0c000c220701c40c803038411605250051045078020b100c00c1003507819801c4030350306075035100c6005404180c0c880c04980d40c041c400d10b00f00180700d0040d10721074400c4842200090075240c2c290f200034540e8801040c00c1c80320703143c40e00c00ea40e0018000e0280224200070100071401507136500d2110814080800e030580e001c100081da2603203615440054107900c5000b21707500580040382c5d01000031607542ca402c07060f02c0360052280c0780c0035000030020040700c2c0c41d41c0c43c4010010b01c50302c8103d5500415485105e00000110124070101c100e040380d014881c0c6850511401c02c080307505110070392031510304014443c014a900180d900000080190010f410344980c0202a4a0041d064006001c200e203401000250307002c5e42 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 234465017 1250 234463767 234463787
    0xa02061207110f03030f07030e1506040b0a0f030b09070b043b011701021308010e0f12040306020a03020405120a1103120405060a1110090201021e1b060415 68
    0x1d84030b089a00c1c10144000c0c0c1d540480d104500d44690080000c2140c0101c5904060f83c4048246004642241c0300351003203081c070a44942e00007554a204081c04500e24180c050034201000030b40b5110112441c1c61000000303504144000307030101d281c4002042e031704602400440003404441040644e83c5079141d00018844210f00e034500700d60b50b040445101040301128082010804003e9042c04507404d118584011500d0310668803460f660801c000d4000c0803003030b4030100003030159070000100680c1e1520850305080400000e401f90360002d1801400e140d20820650f0241d0b608170b000140c850001c014103030000c0c800e0342c01c12a801002c050300c56103003541c0022107000461082003103002c10080c00c000e2607036600f00c00781380c419050070920043c8440d080a10140205503c80d243c1881583d961410007428000c1c2c2031181c210b142d03202e80541c8199601001004c0e15400118003040d110300c410b032881c503142d41899200302c0d00c80503d907402582554030b4030103a6000d024040082c8120743c0c0e50a00c040c00c1d42001c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 234466267 1250 234465017 234465031
    0x13140102070e070f030507021c0207140a0312050f070f150c08010f140f04050f01030b061503181e01020a0212090d1202011418060901110d09050a020612 67
    0x35040040b80007045607030b8a0b030051030240c0b00c0120009400e11300707070050b081c014842e200b144104c492042070f84a42600e030600c0c011f103540203030101790705180f41c481d004e640d404040e90248840e000204002020994210b0294200b403a003640c450191a8a4011520a00038040c0914642c40d03031801c00e1240d69620500841450030041100c041d00c000140e90102091040700150800c4180401c02d102244806517540c04001b0902540b04d49503070001011a84255107158078641107000610030001241080ca0b0028811583d075000a600c101c0b5002e00703417200030104030002c01c100001180c0e6240070088a9a030114004000d205071400c041407900030341000d01c5440c01407060903642070030041e9600880324070540140c28480381301c031140c40c5c0c1122610301c400410708640d80c80c1041118461800c000e18020b030b0804295140100f0f002107464036151000c3c107101100e034504010003141c401c6038401c82d290300b0382001c80450103100303500f001810042200c5019400600020b500812402010402486825 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 234467517 1250 234466267 234466273
    0x8041e14030114131506170714030709180f0b101a0304120207080f0a060606031a04050604020f0c0304050307060203070b040308060406030f050c09070e1e0613140102 73
    0x1034801c05003603034003084068850740381e03460104810a031864940d140c031900961040303120080415080084032203d6200b070f041884410100941e6131028004500100004403d10784644030010000c0e4840328144a4180c4103030360307035645261280816039001c600c0380c0c01000c9050302028030306081c80342c20401c4440c0104400d04034030204013800060480030008100d86031981c02d5a0380ea43c0d58150003202e05603400c003548100140011143e100b00034140c1074a03a89405070144c01d40524051080e1500c60b04414249410035121161248001c03010b5100c0c502d08403004181a10ba41c404240284910340c045586942c0002c2c503038418110000c010801c607002038044030249076455600301e849028070140180210021008a03000c03910072101e03140c10000051002501c03560341e603281c910003407550f001200c0d250001001000d0914060884075807110309801c7c00004260700310300286402015102c111203451240880790603684558043d2102158013681094049443e00d00d100c079005000040680144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 234468767 1250 234467517 234467549
    0x20a0201140603030a050403080d2a1d060304020d03030b03011401081506010210090201030b09090f1219030519110c060a0b0609090718140102071203080105090408041e 74
    0xf003000000c840c00c06516982c2c680c10141141c1d55841d55a010610b50f03901661520758030326170500c1044c40f001000c030740c3e0710211745814904039000c1c044018a0b100500c401c91641c080c50843d46035841280da01590440e140310000c08185000c1d0005c00340a0b0700180c041d0301c0c0080345010402e90528441c143e4a98000302d841c01400e805111045c00c104403041e034016008011540c0d0301510503007094030b049105040118104405002040c2180e01c00c0750035400b81d602c08240307542c1010307003400340d4145111514502c13854660301e1034000d800c03058000d555008041e40c500c00941c1803011140c400d9003179a44004103000144091b601805107410070403080c00e40d8051407010800382c160911845000c080040c210506040c0c0c079000700301301204018000c80a0001e412094400a01c4035000180a070041c1e1070b0156401d43d085000902d0300c01150440c10344200e10042c07400101c0c0c1c001d00090304540c2c084900c0032559440e803800b4230300d41c021a40000e1040100942d1212418207000148090360f07000b9034401c3c40c3c0f03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 234470017 1250 234468767 234468769
    0xf090117040c030b1b0d09030f0306050a05011115090a03120c0e040e030c10150b070b011e090e0d2c0439080f0c030c1c020a02011406 59
    0x810040d0341c01000c00340c0800040002401084045902c01c196000e10809a440e0300002e0708658880b03031042c105c903546d0f55500010950000c01441c00d40c9854582089210309103000301d0702c4590306024584c10722880e02c41a002c40041005000884404480326206505013130840f140d82c1c041c2c620045000c03590f440d558086d00040c2c0e100781000341751030b81e9401c2103c0c2140300921008110400d0607500c1c60008102401c0c5060f002c0245c40b07915440300e00c00060101c00507071445000b40b069082070810040030080c40c00444c01c2042c00606542c0900260030289507a001d60201c140d1260307016203100c80c00e002c21100c1c42400414080501c0c015a02c40742d00003a102441b0464150921414030708041400070340300185d0409500001c00080481300d0801c101e000207011040940e000c1004500c10304212980044003a17000100e0703504000035503000c001c2424440038000c1c1d00d0100400c4c00e6901310700800c48001e0900f841c40d0812071006806000c5588541584000b4064415800d0751480480600045501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 234471267 1250 234470017 234470057
    0x518280b190311120708090111090105031801060f060816030207122102040f050a0801090201020618030d0203090f07050a06120203060402130b0d1a010f050318030f0901 74
    0x40d070340103441200a404400070003580203052000c10a41c0e40c0000b4041e0000102503011014050003041d00c0e00380c21440c01802c105d00355883c508000c00400c0090010503c603980001c181ca40210100d9502c0180360115410280140015480a91810481d09000643d0f5400480442c000c0c010113440380124000c4d5101139046c0d108880b0010445122410340c581e259100314200605000d03030040003407990b18040d001b40140d8100d83c10040007150b441604104514014200030010700c0d41000a011960f030a400207034481000070801a016140c040c2d00e400f6180007401210ba8250811804544034100500c41540c0d410303880c510705080d841507401c0428175141803004034048443d56a10a0070965a94104070040e400190401da0016000d00510241001d0640c444000e00a00714400d51140450190181502d190418444c0340008520a544850b40d004400c03401c00c01c01418095665113480c00029401c00680b44803410034000070401c2e02078012030f200103004c0020240e842c014000e85030304100c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 234472517 1250 234471267 234471277
    0x3150916030b04020112061503020d0509060606031303020a050624090c0a0f122d150302010507020316150e090121050a06021c050a0504120518280b 65
    0x24882c48a001030300540c807484c9000d20076000303072201081d4030390f680c0c11407a0710f40440780040c3c7c0804e8005c9003d031280c01003481415449018500204050b003001c002058042c0301c040d00b041c507030220042401e802c0c540200244070310303242d00000f11a0f0b41d1520307520314000c030b03500b140f900e041e0140c00e01412201440c054018502503052424141d15148000100307942941000300e8207000d2200312441e51000b04058411071800c1c2105031400c0e000a0a13002910790b07003110492012140624201d01e41030010410030284082e41d40c203091550f03a1740282d0001030b2410440103801852441c00a0700072441090b00f00602000e8034260700c0d00380c10019060100031009030309001d440c403c01081c1034204003e0344181c01610308907000303405035580d20080361942016039204410b0300c030014210b240301c0c4865070340311712900e030307002010700701c01c001e01d0516a4550720b8181c00b00904030100103001c12107401d650201b0240300f241d080c0090404001190800180e94220402007070300e242503031159070000b24400b400c02256 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 234473767 1250 234472517 234472523
    0x1205010e0421020c030f01050403090501050f040b0a090b030a0c030b01171303050c07060837090305040b041d0604180f0302150711010606021b010e0d020315091603 72
    0x5000445200381506000078090b610011440390090a4120f40c400b40400d225210069002064030318007403c0141288001e0f0340000e040000802404c0c41c000e00364016038080c2c4049200c0075640e030202c890211034406058005000a64002080c0920241580c6c8503160351340183c0c07401d020b0890b0351401516001020180c410711911021b000070111218044100f0007288242855801c06180c80304462410701140c006d0808210114180a41c4412100010a84001c25020304064080c00d446482d6507909154004042c141c1312140841014011b10550700a06a03102c00213031515a124890151030401020154003005040049011420180910480c9103121b8012059110503595014002c00d0915815411400340f5000490348800e03106c800f81c0a0030b200c0c3c1d0341d00d105241c903c600e0350848000754006d80966000c6500300349582a0598980d29049007400c04000001810b40460001109140c000350315010303142004000e90f500201940c06841c2180c202d81441c4119a03104507141032a000107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 234475017 1250 234473767 234473783
    0x1906090b0d110f0d0e060c0f03070905030d050405040f090b040807060902040204030b01080f0f0705190909030203030708091209100e030f060108150c0d1112071205010e04 75
    0x24080c84850303000034580300109a40005a41c00724152468036900309440c6440181d0001a02120b2004c4c03600403400390b010080050120341c03c20340500103070752007400c0117182c082001100103004640204005c0c0010200502603500226104a0041550340580220b0348218039000300c00800880764484c004590340c2c04041c0c01c0050702c82e03840315025900070345404c07520b02d6207641c0c1c0400142ca46001800007580700b0041c03000c036075040c84c4036182000d4410a07080007960103502585d001c2c000000b101c030704603901aa500c0709102d90049040144400c2501301518072400e0601d02000c050f4000000c622400065032080e060740c5800c54880c2d110043c0200403c44044280b00e0036a043c580850381742c07030f00021414035041c0c2c240c001011a040c900711829180d03590300701d04010041c04c5810702c4000602d40340008104194a031804900c0040e0080c443c5030074019030703075101c0b007a20140040222449900c031740700d40550615203114014641640d88199a4a841c03c0c1400003e16090828095000d99800024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 234476267 1250 234475017 234475019
    0x7030c140304080d05060607080c0303010510031e0507020a08030c090108181506040207120806010e03030a3204090e0114090c0111010b040f0504020906120a061112010b09190609 78
    0x21280103420098601b0754050010425000003036103100051401d000300c0009541c40390300d468100b10450084e40103030710a043c1015003c0801c000444005160001d10310380000d842d4682c81c00c102c2c40c10b15801c0c1c000b40304003400070511048013201030190442120907a0f80d180076680b842d0b8011001c80c6205404042984403010028091100c10800f42e44040060b02c010f09040b941c2c0c40341d0010119203d85400480c103000c0900002d035a2040d00c2d0042003c090700158602100b0100080c000c00d8061746818503441c4c904000840c408078141c00c901c01c024021505174585485840000c000d1900c180c102e500c035803034525102001c440b04080c1500c01c0000e0005002c52440c090011340e80d1151a0714045004d5686000541c502c1e5924801e010904005550004044c17500e8414440c0420300682807038800e6110718003240800d0400115100001d41c04103021070650b400303658403000c9004d00c1100c00002c0c02000300215080040c080940781d4401e0490f40080d03190034080e001070095009002d03900010383c1c201d40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 234477517 1250 234476267 234476287
    0x90b060918091204030812010902190503090a052407030c050f0306010c060c02010605120102030115050703050c19050d08010803220801060f051306140103090609050607030c14030408 80
    0x51003039002500c0e03003c1d40c0003189004180030080c0c1c800e4108070340c2d509020540b044400820103440b400741400d1842140b40000420b0801d081700c0e0018104801c00c000040000c0c40301c0d02c180602464194460304a55001412485040c2b000d000d9004150003c080c802c000340c492446800ac00080068540f10903141200c801c07007981966000130502d07818045810368020000c0c07658420340382c40c4a525400010720074140400c0125940c1d0308981560306038010300041c400402e42d0030320b00031640110705050380e480d500c91605640e1405142c032141c482e030043c4030481c495508056926485240700d0030690390780c0943c81c1e5050754248802e004418480d8010300a01d400c1024104009a01405942e40d030203c480d43c96580b103007510265080001010700d070580400190070800e00d121000c1c0d1114009014140c1407189a1684040c0e0f148014101b585401034402448030399804008400d800c28103484c034a25280f440900580640e41e90000006c5082400143d9403e161040e240910fa000701040d247c00c105103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 234478767 1250 234477517 234477559
    0x108040305071506050a08150601180b0d020304020f12070b03060316140f010504030807150605090403020a020109050d0804030803100f1203230331060204090b0609 72
    0x10812800e0150410050010900d14080c0701c40c1d406034030740049071060a19062100c072080b240d111002c25841848061301c0344816240c515800142880c1540b10794500c050070300e034180e10039840b00c20b4503000047c804084017201d400852040703000780c40c1d0300100c2c05040140041d032074054000100c680c0044c070b0203001d02254ac60003190804001006c84100702e9084070030310f4094400381c0c8100c41080c104c00d880c00c654144034181c03c0101d10242800c07424039240d5111809648213100005000031964881e002c603140c803940c000c001820380507010804a00d003503e030296440408210503400b00b402000000b03424a4600c03c04a0000d50080d112400c00b451541c4148054102608040840c6804034011480500b0506e1043c01407103046c80c0443e1030381303041c02d0117020350031043c80c100c00d001c603200c1103a042a81c1c080c00303d942262241660180604c2c10500c42c00b07072400c0400e00070401070031946998041c0961500039000799881300c9810410310020608128040c0702c0c861145030000000075009078101400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 234480017 1250 234478767 234478771
    0x30105090612100e01050f06040903020706030c02210a030e03030606040b03180a1217360706090e010e07080412020703050d0c260f0a0e060c070e0916050108 69
    0x2c10444401403c0c900264090794050031211885039518000c000a5000e01890310760000015113042100702039644009454520602a203020316803108101072185200b040b40052001a09094030183d1034901e03070464041d40b011001c040001d040480f0030103122800b20842340642001010b19103000d1420104503d160001042188610502800700305010020b200c0144540d109201d007120310f0744076260141403140300d06031581098480c0c20402282007100080c1c03000300c5256000c000c0315010030091038840f0f40c000b40c21680c2e2501846800180361500074119209440f5031241031042681c841c1881c2512060464660f800506a407000c607012030380c85060032119119510588403119201c0c0c80341031800d66103480c20000511352030414030500c500001d080c0b1000d0582c440c88070001e110011880003500502504c2003081e03100240002c100c03406049c65582d07049000e49000e4485e201c02145039140c0f1600e1040f800075401480006802403000b240a00040320141050354440b400c10780115010540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 234481267 1250 234480017 234480049
    0x2120321070f090f1a0f030702031215030d141306020105090f0136080313120807020c0402030a0b0913061410090504060b030303041b08121e04030f15060b0301050906 73
    0x2005240300406c1040020352080362150003c5507510800750540380041d01c000d08405850700b24a20034242d943c1d006c0352011183c074403460a0b038040b0118107032130000c81c402c0840c400c2210350000d00004070300b0b4040d0407151140708800c042e90001c442c0382a40d40e00f41c614040c911640d94420800e980011803090001c1182c1e800700418049100040f583e030941c0300d80c8241c4440240e003030981c5d4920100706114900e03044400c007518042c0d515040c403910183d500c179505070291b44629000300009103426010391180303410600040000045091810a0f00456000c2c00c105664040c144519012030f02001c0d038000380039201441c0c2083c103403898501e1250082c0006070046901684a841d99210395800b00051802603028880c0038420314030400000b00c2c2e50041d507100d040d0380e400c20340d02c0f400b84031350103030580d240c0e80480c100010b0162890345107041c440c841e0303810043ca13100d442d00502c801e100d03400f400300d0382200581000300f06154456050030000e001c24814264020b4009001038624107140401e9081780c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 234482517 1250 234481267 234481319
    0x801230a020c0f0102040302150711090601020f01090b1014010804080a09030f060506210318120703030c030807050301030c061d04060b0901082202120321070f090f 72
    0x40c140c20b03a6041540c0502007403102da4002c5070a2081d454103910080e8414a00718401d45008080d6441c000c4641003803c07070342d216521500000b00e0a034020b1003560384000011008004003149480c0201203e082951710024200b9190303404100400304e00715845869105841d50036081c0d42d6551840072a9111545460400c40145400800122000c000318030700d6100b03400200741c620785002840328450100814401104c00120006000c4070040b040307a14501490030003081c200c4421022802c030085184c0d03410b0f614030030500c0010074180d0100741080202c1c4659501c9003107456071034007100c860000707000185c202d55409208002c0d175809100c4055100341100300030060780e8031100005049403200d03489a05405000204131150303680c00031500c1d40c00015194800b0683d02e0340b0085030350234201d100e0300034000d040100811840400c10810340d00c0b003804469462280120700e440c0009141825198140403030b40100782d403034580740102c00d02416548042c042000c02031800c8034500da00b031700d072500c0082024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 234483767 1250 234482517 234482527
    0x8102603040f140f030109020924031c1107050108010603052214010b0604030b0103060c090308071505090d021b0f19030308010501110a0f02180709030c0801230a02 72
    0x107500442c444000700154003080302c0c46040d440c280040880010724a034440d91400440c0070042c3e8400c04029041407070140343d603d01030962580140c00304009866254144103403e5212283c4881c5000e00c00014a50340e6200c2e1040c0421981e1903844400d806090f0108200600500145d407080c2d10495120600c244002c1c02280001c010803002a2624420b41c0c5254404035126582d81c401d001c0c41260309001d07164103140c80c0c5140c540c805507031018000100150f0f200d90031009405c0c03040209101864001a009503100da1918020010f00c03414085041c030607041000251545a000c10361041c02c000d65000741400002101c41108103c665007131450b4000c0c14202101103984940042c20014031001030305014260135414050002c4205a10403030400809a2105010b4180841c10491069004d200035940d880760b840090200c0d0400d14114a0740b50702c0204001e2181c0c0e02c21011070460b03014801a031241c40d159001c49083c4c46404170400c0103030401c11004820001a5103c0b542c2c0b0002c0324000600384 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 234485017 1250 234483767 234483779
    0x41508062d0403020c19121103010902090c0405150c0a0204152c0c0405150d060e0a05070908030c19020d06050f070905010905090105090a110a0f0810260304 69
    0x4074015902500140e211008603695402d02d000300c001d0700024000f00460041c0b130681e6912010310040c00040c00c805503480307a00c0040d2000d40114216990040290407d807400d0300001c005500075124851240b05420025030011900408940c40090800090320040b1442c3d02480302070256075402c91511405c1200c0001d5941184e030b0180c00c1c1c8401034030500450b042d200818401000054007141d41c1e40d00802080005071b49148000d000d00c0b030800b10380ca480310382e0340002e540144515030050002c40f0701e20017042400d5480b640315a120703207020f858144001c1d40712002d0581d80d000380c09071a00164814909070000491114840705641e10092580807040025a0303034106440e03040d00c5c00d0080d000c0700070034008003d4100151401074102860105c400790316200000f004094103210303036800350f101d0301d000c01c02c0754109400c245c00401251900079501c0081503802860381120551000001b08984080750f01c2c00c0030001c4031400c0318290046142d1914128071a4034001c02c51000d02040c40c40100b10010304 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 234486267 1250 234485017 234485101
    0x90f06010b0904150b0a140c07030f0318050918100906020702091510030513050106060504090c0503090a030f0203070b0405060114060319020d0f06080a0204150806 72
    0x78041001e0166100c1e80704a0500040e0307003046203801c003840a0140b00703020050240d403c5d01d01e0486d02e03180004401703986110741c0d5594800c020440d07580c0d02034200003000b806444011441c0440c030036541c104000020101e010540800780c002c02d6400070094020581003804110510300b1159458141ca0700d0310008110802190543c403400c84060360080394480c03d5207417402c0307a1a0b200c000621989200101c8400040908241065001c10b240d9500702080400e40c03400300d0340602703651000080022a44030200a0010782151140142927414004000d03226031050b42902e01404510f00184001500c076030b000e440442010a0b010300710300c024000500400d03203d0b034001303005034024000b0300259414061102ca20461f0b200b003c80c0a44020001c5c4003c084c203513040d201c2071081c10000141c4400d1410551000f81001418000b1101d0400da40030400000100e039018000d84200c4080101402c0d2040410385041648640400d40e04400005212038440c204180b4440031540da103070390003582201200d20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 234487517 1250 234486267 234486269
    0x190504180209090105060a12091103010b10080a33030605010f0302060f0c030708040f0f0b0903030a0e010504090f0e0105060d0203060c090604180c020f0f0703031101060b03010e04031b08030f090f0601 88
    0x41d0542c2820025255040378070641c0000042502c680d0a6a42c4101016111940285c88101043e81e189400015403440c40c0700080b01c021818a503040203060603082c9840303640d9600060b116146004000070790022910b0030401101c0d030180001d0708103c03040502040a81101d2000c18107404100081c00006900000800c0600462055001e0707290a0018a0f002d0764055049443c010f10100000c071070540e00042a43c10020880c40c255408414090040340c2a00459029030401030804003040c8000507940c01c1031200c040264000c00540e607400d020804110460040a90142c000b00f000c07507040c0400f88020038503c0e030302034034803031820b50313510000c3c4504601111a14040d82c0e9035204800f8070b44e4140040c040b04003900000300010144007005603214900c501c0018180400c401005202c0c250a401c200020818a0411900c1e507948450180001c001141c1c2140003d083c40c01c05202c9d40218000b03402040e400c10521402c660300c40c400018020409400302410b07104610340300da01c3d00c0c410000f047c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 234488767 1250 234487517 234487523
    0x8091923070311040204050d0209070c0b161701062a051204081b030601060c0623070908030a02060c0706090b0406021c021806070305190504180209090105060a1209 72
    0x12401d2032a505008004203502896548903a004100c00c00c00750756110140030415030100d80014040e15550f03800d0b1940c1405081c02011540284204030b200c5154481c4036683c03a00300e84488141d1001403001105150f800d02030600402c02c412044061081030449104035101150000401031105885c0d042c03402c1c2c22002280c03245400000c080c0114a801d0051003010704003290b00303240710200702002a032540710501840341009a04e015000500445030800000544c0c848420100c03460600007010b400d980c115074480211b50244000620001c0c000304503010940c00d6800703001c2d5034480c016150320943c010b081c10b0714030303e844005000200c1c84450550340118803410f00140d980c0151400c1e5920f81050500c00e9034458410300c5400100d00013403000c2418020100e80660341c88100d490184d0b190b001c0e811480741580051948001040c0d0854010300030348215001d043c04c07000100f5041426841501551500159907034010001c9040100150101c1c480a0405940c500d540000c080d040f10a000416 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 234490017 1250 234488767 234488773
    0x60c1602370905100302060d14010311040c0c05070312050f03090d0809030a0c230703060b0906040614010c1515030c0503060c181c0308090d08091923 66
    0x1440110014910751002407401050a1100e0302c0d1604441416692502c03000e805084006050030a826069000c01a0b40c0d04020040c09a540c42e41000302c1807490350402c2d5030259183c0395180c484a40a84401c002403907218005083d0181035942e08050440d00004020500200348100f01070b0700041c5000d1481031071400c0041c4050242c002008003145030190030034103d500b0400070b440b51603038000074884145400900a0383d44803d500c1010300c1508603880030102500482c80080304103d46600045140f540850b00c00c0200e0319090104400c5a125204911058007084840794040d40544e04640c015801402030b010055055540c40c800c1d121f0658082203540c1001c1c0061082044840b40c0d2405400142d00801c150320709081500f4084c4210400080d580034040d8001d1a20343d01c0d50440561100d2030b4128820641103032501030150041600c4510307040c012130894442d518400e021841c424142d280081c58000d003100c2c0d180020307219948080cac503010307000070070151110400c800c0d03040524913103001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 234491267 1250 234490017 234490099
    0xf150c0302031f0501120218031c0e0604050d021e0307270e0c3a0b180d0e03011808090a061d01030e010b03010c030b030d02060c1602 59
    0x48007402064520003c40103242c0c0609100b10b0743e0148000c0d0b8001c440003401039845011007c1501041d2828003460340c18801c4008150308030b0344078516410030201d661a041d2480c2c885404025481c0501c0c011150000d4601d00050094600f4600c41c0401c0888001c40200c581107070300200381048215040180404602c000011182003510104500035802c40020001c0300c2c0214522900d504441c030413584141034000501c5800d145450400c0c0e02011540c0202400301c20b651866601c8001d40704054a416904e080011580001060425502c2d09103002801802c59a2107068410b1100304903269059941d0304081c64580008180900b512405010a9a03c0301d0018041140000b880d81005041020500007030a18941c0141d4500e00d141090a011808010501c94180100000c1040603415801c0c0440c0c5c401058240d03010954920060702510900030006405a039185425543d084800b80104100350b18440e8003001c20f40c80031b00c01012262802d0b440b42ca00c40f030b441500e01d44820b00654200e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 234492517 1250 234491267 234491281
    0x60c251506080c0303070206030402010309020310020310061b05060402190b03040b01050316080a0305070212010228230306030a0b04030203090117040305070f110406090230040f150c030203 83
    0x401100c074250110b006600c3c0030341b580d0100d600d81c000688000d044c103458100100c110740e03050048090b901d02280d0115241d1a000601c401d034240c41d031060a0111315600301c160005640311150030681500500240540c0d00c0c0c550a0040c0f1040c400d00e03101000146000100c1c0036014030300218000c40c01280d0480495041c481054204600c180b0a0000315a91640421003240003103501d691064041c240540c4580080c00405c0c10504000c683d085a0b5100155000311099030004065030403c00c020308100070700c1088015500b00703001c090000c586e00c01c4400281001e43e41c8400440d402000541a10720381c41d013a0782c2d405031050090700d04401580000ca010304040d42c5c803003141030b152003155000002c68141518040e001f031242820140400326840840790074880d84028243e4104c03800b40c030420907165200303043c000940110003c194803032004901c1008420340d000040d40e282210f5501004181c136607569408110b0145001260328100d1541d420400c0c100b140b2400f900e0802d90748015a0341e240c203070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 234493767 1250 234492517 234492523
    0x31209070807090207060c05120a23070c12111504050106050907080a0b0613050103050709050907090305011b0e130f020406110c04050f0606070309050307060201020705070602060c25150608 83
    0x121f036010800500f44078022580d04151484da40281080300000f8080b00ca240070340e5078000c8003200b84c8403200302c0001401812a400321222003010701804d800241c2e450311070000c0350804a5200f0142043c0d00c2000c1c4602d010300074145a41c2c02501c64030001331020754410201f981c0520446058004c207090703104000480c440b600412140d010112581403034084a42e400c0c640305c403418010a8100359491001643c11405122101301602d0000c0c0102c81d14034115070010420307162400b048546508100c60900156820003500d031000300309803038000d04441c40034203201d1804a50180c10008a46480b1006041e1240d440184068240c1c3d903030f800202649160080c0c0707007205089002d8003c9151800300000e5100c40500c2d81d811031030071560f0a580b08501e06040307a40300001c1e00a0f65040c01800000a1a290158001d09240c0d02c03a0055415581c1d4400080e600d80d07004607540b002c0c0d1541004086040c95044051240d01c3c807100d2080b0120342c6454480310807080d042c509103090659100ca050205200070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 234495017 1250 234493767 234493781
    0xf0923150a0203030a1d0714120105060f19090c021c02061611070503010203090d030605150d0207032129130f020405180103020a050105040803120907080709020706 72
    0x340c20803071800ca800240250b5903c0010400c1c48540da50b101010040b203404000780c504105042c0843d10003946440240803821001c1c03041074441c861f1580c56280441c0c1c10b00555201e044014840341800c030b0902c00f030090103800740000178020009024007040706c920a01c034142003842c1c1c9900a20f50700042d1129804410948448181594081010400d280580c00f81400303401200b450601610102e2030500c5250960541003181c0c594000300c00c2018842c4c00007110320820310340361b500303205450340d9409110801c4490071004011000c00c1015840da01e641d40c0050807014880c0c0340c903030604840c154801c80c080d004480710800742c584601801444001d043c682e1a10205070100d2609038120301d50024220f00102c1403003d4402d1f8a072030700c5055030b10743e80c0e05035001401c01800701a43d007040006038001c1d030802400102e03c140c002c00d8003c82d041d48a141520165052440258a080c0380204007203d8010014818481d0703205205010400040901000e00204200907001d1703195200c910b8582c0c182c40007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 234496267 1250 234495017 234495049
    0xe1c02061501170a090212010c0c060b04020405010503040b04020a03120809060c04080c130213060c0c060c11040509070314100617070b0706181a13120f0923 69
    0x8656000c002d580701da54103c40c0c200820b1100000c04000b1072002c50b16401e69040004c0b032a500e03121035480076030782100042102da445644c0030448e41f0403800400003240280d00405d400a041440042c0000b416401c000380c1160008052812503503482d95070b81501110702031147d0000d100c06051045107070041001c00c0d040b10822070f400f420319044c0450281e43e1044000028824100d40d40403000006180e4101ca40060360301c42e4400100e500e0749006010242e1241d821107440081783c200003503a51003000b901000c80c0d4030007000d501d048038030410800a050040c094a0790741c001c00e480000003440100c0802d86400d0071034058031941400c1e042040848003160f00c1070034a421f880b2030803140c4940110b010340c00d84d81040e404903100c00d07a44c107015000f8402110303042c544000302040e13035040c05140d444030212241031070309242155580000b00403508100c40c20040c681c528501000c441d05001c0c05c0c2c04050311a0919009601c1540e40c0e034602411021455103544441e141000c0040900382021080d202501f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 234497517 1250 234496267 234496277
    0x1b030402010c060e010524010c240212090109050f0609120c030c0f0f0d080609040206071b030602120a15230d0f05010506100c06112101090f09020906040e1c02061501 73
    0x3612030051440f0b4503c12b1595803a2600101c11600e402070741a11810300b081d0034404030900c2c01c0d2030028000c0038800c84c181e42c2c0d40300d20365401e501643d0001d07d05200d0700300280503100034000801d0080c41c0c2e4110040c0b1301c003d030000b40008800140700300007004d04440001c0007442c60b64404c2c42c04c10300348014000401d007000307105420045070340c488482e4182c01c03680c162002c55807540135040940d03002c1d4011542c55000000031000005000145c4c010b010200740d20000c0327450355185c01084d40c0c2250014090400e0040d0314200401450f203985641c1103224039146c4c0445c50445c0924001030b41940350f09001c4801b1402081d9a4051140c01d01c140c40d07000c2400d41e102003020741c544502404442c200c0100070107160329007002c0b8146485034002d86106008504d00b4692003c030010b8400031085d801d0051041c00c910b020303800c07540700c00540107143c44a0b0b00074160b8201c603150340382403202521114a41c81d101c1d109641e45460701c1d601581c0100821340352540a4410350030100c000d6548158540120341c1080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 234498767 1250 234497517 234497537
    0x20a0504080d0806120109030203030103120c050d020c13060e060d020616060e0709020a051b0705090103050a110f0609010c02063f0402011b0c030b0c0c061b030402010c060e01052401 80
    0x249c0000851341506d130811040c10042007481021604e24800650080c02c90084900034200f9036000218400b070f118048601d40080421071601c14100d424a20030305020000d248081003141c24041c09204c011400901240e191941d4050102d105c02040e60003100d19070b964071080b0300c0300315043c030080001e002401c0055140c40119000105103000c0e00c10050781c403942c0e036000d0954059042203010000d05000e00315504540e5a420000d445080c90001918940300d89421103041c0d2900d1b546903080070030014210390800d0740a4004440c048003812040f07801120822803030400c814170b4405603801d148106a4617810007012101c0850a000c0d0311800309c1038454090031300c1f00503030f00b0900821803480b071102541d0380d0700841d0a001c00d06441d00c1d070001d04911804014002d1000c40400104862603a40003144c07503a40740c82810140b101c8080c0c124440c3ca44041c00418010340c40b40c00701c82c0b0818000c881c0480c1c640080c0d5115030031154186c450801061040e4042400040407012880c0541000d00304600d0030303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 234500017 1250 234498767 234498773
    0xf090203100506030901060513050402090609091915050114030d020106050a030809030a020d0b070e01051903020307021f05010e0a1b030c050c0312040b010e01031203020a0504080d0806120109 84
    0x301c500d00900c0e101d003c0110000c0c4c02d50b1002d6001d480144001444c5000c1c066215881500520043d5800e07402440380a0015845043c041001d50150250030002c06104104054080740107840e042c0480d2800359680415240340942d0180034042e084c884681c07160b001c000000c040c41c208001444c4019079042c00010400c1359295041130f8222074109074046c2d610555200000d00700307000008020741c40700c0244030302002c0c8011a0961f034460a000e40341e00c6503400c107020042d5914020450107070f40c7c2ca40701c00c80610110b4802c0e0040e6800664900403030740520810140d40c004003e210031107104540d036030310042090041a914a81d00441e407158100700c14400c90266000b0350035910b11640605803241d0701c1c154854401d404070b54800c0b20207016030340c60342c114480d018852501540e0944147c9803010010999003480000c09040345c1d0720942101900d115a4015006034208621001c18080c05100002c0e0442080c060210340840b103558407042c4d460310808011100843d80d0b41160141c1c135091140e000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 234501267 1250 234500017 234500041
    0x303011e181505030313080d0c0506060d0611030a0903030501380f04090501090c0e0109170304050604140306070e010f03022a0312060f091810060b040f090203 70
    0x109540c1c9804100e00c0303007803600034200010a80c4030300c0d013500c000500c80504462a81c4d02209960114090310000d508401003100c5010b400c070340140103500700b0b2000c1405803a001000000062055501140b03007101d02d540d209058000b01d070b1400030740c0c1d03d80d5264010150f151080034050030f40c59400381100f10440303103001580c041c0448041e00315010104006425035100003903400c010310000c40c140d41c403500d400381200602400e22030849a141811599003145000b850301c0b007a05001a0344044105103000c0d0395403079a0a10601d0f84445000410004c10b168807100d000704044c3c00c0c01d9410080311030401c4141454104002c0c184000c020044460110581c1e2002c40340c04009554a0090384817070f001c51440301a80c10f8019a8030344601e9001030890300c80d201201070141441c06003065615980d42d80b0038405503c0850070030a5024480e440020200150301401004072146001111a144410307044a000c40e5a10b4001004541d001b04003005401401c4400c14050001100c044d0306600389403011004c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 234502517 1250 234501267 234501299
    0xe0f0601030507030e06090f300304060e01050f070806030a2127030302070f03050c04020318010507021c1706010e13091506050d02030606120109140303011e 69
    0x410980c0380c0b80480c0d1001d110303401c0300200b00d01003c143d40c01402c0007200c1076a501da80720700400d0603000780450000203242c100d800790a0880d04800b03480d2200320706102c50205500040003151403c0d0381d29410001030409114035849505e04060107105428451000341582c180200300303e10a500c801045da00042c550014001441c0c0100c001d412401a0321308140d980c2c110301c4020002c14000f6401410f4115038029020044a00079025a001c290304e40c0b01180d01d4208600003d04203500550394200d0714103040c0e0003103901079481c0462200c03c40f81080312609450040e40e9101c0160302a100d4091094481c2c4d8210610315900d081c00714803060a030b4a0000c4c032150040a1f24140851604100e42a0f103640305007454946d02c0c0310040004198500c0d0401071000d8906190100a141910129003820689442680580c0042c0108010b0f41ea01081060100c100b8100c400155201c540c1c0a002544007608050100c912001440d103960600c842e09151804000060021840c80a020018101c000345410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 234503767 1250 234502517 234502519
    0xc0c0c01080a0e0f062a07020d03030902130e0f0d020c0d1b0603061a070818060904090b040506060a0303090311010512010b070212060603121303020306040312060e0f06 74
    0x264a03694042002006000f039400152013805500501100c070080801c5551189800414051280f01a030881100c414843c281c41c9111031410042070f005807500c02a810300589c424a0041040d18035030b400b054001004500b624501c80c0c403050480380e408001d00c100c09040c02c40034020903105900703408c0255140322142000c0d000d100901008800e0088200c1c0300e1a0242030b078041c07143c9a0340e550100800406841c4140515102c2070a00d401c11103084074202c0d129160003600c9142003c03660a81d104441c0b02d80444030707a122504004071100354640d4060207011900400002c0e4851030705040075403d20300000d0140d40b2600c0080000d10011303030050380c3d0500707498114a952182030b440070016501446040a01c1c1d003000035440c000143d6104070b20081c0420392080d00c042e800881221051303980c6d254207544c401c0d0303d0f410400c5040c0c916501c02014080d4150f000c0c43c21040542e81c3e401290802d00e065400760700181c00300d4442030300c09010340500d40c0181040107043c085031070482c04190f40c044001d0603039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 234505017 1250 234503767 234503777
    0x60f040902060906030c0d0501060203040f030308130210020c091f2904090c17070504090c0212041203110a0201020a0210030b100807020706110a081e160b0c0c0c01 72
    0xc259140e44056515120014020f9980c3c0e0404903942d00042d0040341c001e00840381018000724166101000b42c90449001c012034400d0541180e40644100d40014550f80391284100121000341c1d03203c1c900103880303000300d40107000c410f0b00030300a210b100e02d4014400c805c2c10f2180000304400107030b40800308045a003220342c800102c0d05401c00102c00d10510850a4030710400114000c600140c5a07882180c20103480d03100d0500161100b440f09800b201e044034007802161052100700106141a00103140c00801441620b18074040000d1002c01500b00350003c4400100180c800400c160b00318502e4120800904002e0144030340d180c5c0005d50380c0c407840700028000d10352820f1180c2541d02940282101041c014002409a074007050024800d034011243c40005200c2d420700000d029000d0407514004c005804003810203058951a07401203607200e260440d0602072034603001d401d414400c502a008491446407200e000c3d001604041100c200c010703215001064040000240c01500052400b07c40a801c1c200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 234506267 1250 234505017 234505031
    0x2104061b1805060c070e0a05220c06030c020708120a091703070f0f02041a030c010302040806011203110d0c0606090b011704050c0303040e04060501080a0f031112041e050108060f04 79
    0x32981c1001700c140d00000031980e4030320502488000341e4119901c1181e100baa00c690142e4485000034081c103140d400175040010514061010a200e5002269107402600443e8842665821024680100801c2c81031407944c000c02c0c140308559110802100900c08440c0c01004401150301154482c410381c8001040b40480040c3c4000708407942da40140081d400400070013000c1301d241201048082003d08880c845e016941805409600070310985d400c4c0c91441d00200100da080121142c4404a44e981c00c0c0c05014159040301452101000030065000b0180c0d13541094000a10b0000180e540d1504840c00c0c00c0c0c00d000300040d169034801c0d40b80c003c9101ea4803051036542c0302e50a203181850340040707209405006c00100800c0e00400c04c420389004522800b02005141e0340d40e072403507859200211008140c030081401402c0468443c59001854a28039020398030345a03400c5422044c070f03500503484034490541c00d2045203aa50380215407070004090a0030304400c2131801d500058910020050307440c0c03141f17580b41c00c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 234507517 1250 234506267 234506287
    0x80603010513021503150a140a0b160624030c03030e0301091509020a03080406050417010606080c0705100c090302010206160f1d0a0902070c1212052104061b180506 72
    0xb44840c4d240c6ca007d03100383e03945511003801c2034445054401284c0544040180081d0040822044a1080c800059005410003543e0b03507800c0500402100e0480c00c6107a200c541d039101d442e0181e454011441100e8505000345585005000682c6070300c4058840d9140c2444400416100e80d00700c20301c6100c0d940c0c001945251131002507140020b5420103820b0807008180841c070360790090001d0064400d10308402c1c20741b1546544840c01c0c3e0b200e900a210005001c98085581002c90034094480148610180c445410780b424a41003181c652120660005204044c100300790350301805980d400135030380301d40b00e12006030b0140c000d484034162101010400c40310a4400c01d4100041d4103440c500b02d070091040c0a40340d80e031034151003c1c1d00010f00c02e8903502500100000c5504003044180401c662103568075001c5d010110007035842d900031f51400c80040880c001c00f000c03180b40f80c0210521561283c04d00140d081c1c007034440c00d103100754500c044209100312000300802d5a12202039110480e60201c81c0140d807220b0880d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 234508767 1250 234507517 234507541
    0x30c0203100f0b0406090b0a0501032003090105180303040f0b0c280912050c010503130210031d0f03030c0c070b210a0b21010e030a080603010513021503 67
    0x50301c607914601c0e0054000c400300d1a50415000701100b110140800758541c030050081b00c40181020380c0c4200500360401665000f03820040c02c00301c028480c1c0c00a0203103c088010b2aa004407400030040c0d541d03c08200c0e0b0341040c1028007210400d00300007507055191a5440c10b150b04610240034120280310000500d900b560002124480203126001c0464001640000703800100d101910901080c2c440001142d9040d180205514990300031009200721076800d4019940343e440503141c0c04082400e0f0001c0740150712046080703c014602a6800248500c0302104c4c8076441c20140000701c02c5400c08605000015000419a07801900380b205041e80c8290264290745002d1441d8016205e0032004600280b090841040c8604c4c1c1c01d034120900385180d501c101200781220303088c14046600c015401251451020290080700d03515922000000d40b14851514491841d0454221b00b03000174043c00030405141000c0c09460303005190305030925501c070020740c0003ea0a2900300401031141002200045090b0001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 234510017 1250 234508767 234508783
    0xa091109060418031107080607170402030a020d080d050f100e0901020c0f0d03110301050a1502010e03040909020312120f0403090e0c030a0e0a1e0c0306020f030f0c03070507030c0203 80
    0x400e641c5480701d10b04e0060171030169450906184c1c0501000025882008202c90788618003c1d03507078982003603009030302c0c0b840c90700c010f8016030301807040482080050f150841c0804045019401c0542c0303941c140b861302020303128001c0c0649540f901c0751081c0003289503280440340039145843c400300d1003551000000c6008ac012100340b5881845040c00c01c2034803000109542c1d111010503541406621a40102c0f00304a01c0284116504503c0e1448104100b540c1c1104809401640f44004507017400400c01c11481d581207a00194031241d40c88000703008501c1e041181c000c0b09e07a021010035040960081140304150300081001c100d16032010300207020540725008020180c0818056028281406c030340d00368441d003007112042c0314176280c00030204040100007200c803030031a4080040c80315020b0b07005904031040b41c00750084070720804007400840000c000d4005840e03900c2c0341010307480c0c0f01e1918141c103414481f000380c01420360a40401c203202415910030704641140f901400c103a8400300003840440c2c601008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 234511267 1250 234510017 234510041
    0xd030b0105091908060f0103020d0b0603031b0c010921032105040506071101050609010b0d020904091b0b07031409060918070305061210180c06170a0911090604 70
    0x82d0454003480f1608400c0b5034000e694409040700c80310380e0b410058241e42c0e502030002030350054200e0b04000001d250345c480c1c01e80c0040b01606a070700b420365131500070031405110800d08015030080704649103a542c1c0f1200240042400140320000c01c8060310703552907018200140134081000004180010580c942d0350b211281d4a410801c011038136181c00d00c0c03600c8450a882d42400a681c007052400f518505020b1907004000040180301c159203080b07107800082d44080312441e40960284020f01c51035032a407180c0442d407800f030761001c00910480d283e40340d10f440b16070304042d100c00e800380002d501290b880141c00d0f184501d0034a00c0d503a40c646040004400c0d010f6a03080b180d00c4888000308241c1402800c0c00c046c050300c601c6e201403106480788007c102c00d900e15491403220342e60084408203905125900708030820480390010100c2030040c1d4590400c000352075040040031031708460305040d07460301049000364080000340d020040b06699544042c42447d0445070144117008400c04034040c0e41e40c41e0301035100303044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 234512517 1250 234511267 234511279
    0x20307050c1c0305060a080309040b0a0503070803040312020d0801090222241b0f020a080f0604030801060e0d0b0a1103010f141203250807061a03010b030d030b010509 73
    0x245000d4081030844000c042c074002401c10003c1545402c1115005c002c0d103542c200550f00b403042030340034800145040b1050380d60107500d9403800681a103050000344041c04050b03020b144c2e00d03411814044890040c501c030a0045500000568210690090f510307810354840c06405079450055581509131240030603003e10543d0051040020b0f0704070a14500190a03144189211480f29004010707910f005180c7c120300b00700d1740070001510014100702d140b07079103040c0700a207440320141c2c41364401860900c00b07082c43e000c90b0b0300240c144020301d0b0304081c030786004001d1850002c5450482d400407454000400e00000e0150b4000c001003091020303ea00461a424004206c56860303603074a80d0081c00b10040c51144084101c12412500840c0c00e01c0f00c00001b070304e000b0100540c540b1081d01d07041c0443c00400b900340c1340c1c0651181100000180c0250081505c0c60040f000032580742d50302d8007000f000100c0210410312981c58120800700648001c80c140c094204182000982d010f008001038440c1d00c113408005602c85 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 234513767 1250 234512517 234512533
    0x3031308031f060c031806020606040b04020c030a0503071d06090907051e040513061d100801050702060709082d0a0812070305070503010807030b06010516050601050f03070b0d020307050c 82
    0x9540320500f1413a00e4065540c12a5400c40b803007031440e1107610360040382c0c0160880d000044040c00c0c42d03008525284006440146808501c0e0102400c60308145003d1000403000014459800d5000e4442032030252140c40e1207072800c2611000822034401d404016010710440d8000880301d80c0200156500880780d00c50b0207030703605404604110158000e00070648a02c8079406d1510080c0f0b01031184209a03580085007401002c0d0030030f940000c15100420608002d10010b60100d4149828040d06000c0d46180c0c000300b25509040700b0113400e0504a411245440e84021056815060087d400541540c9002c481c42504d07158108090b00341446e41b4805040150005190b08440c0d80072070406107d901c070f95908015070740304c548046071584028469040a1740c0300352024804981c6002c0e8280d00440141802450044081c00c090030583c1e00020984161f006070300100114180a0000700d0365071400c4000d051910b042414180e110b01030510380280a40e03003c00001d0455004c0d400700d800e03a55084044400071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 234515017 1250 234513767 234513779
    0x604030206090f010b09370609110306060a0807030b0d0507171c052208010903080603030a05490c0221071a0a0e0f03031308031f 57
    0x120700036038455845114071100c40b044410b0611400098140c000c005c8082070312400c2c0001d034a440c0e11020000f0039190300494000b0548000c1c00c00e036201c11040000318600c0d107018515000c50705401c4590550360000c004100f0903640350703401c82d00c0410060800d08170310f48401c0f204400030701d080d030200d6401032100c00c0518180040000d1802c1110307071f0b03c803945050441036042181c0304c4c0b502404200405c81d405504d80b40c043e00400140c468902030802244409180003c0340740c142e85c06910090490b55661903072001d0662100d03515901c003606600851030072449207030003889881084400300c000c1003d10030004079a020098040c1689043d000c04440300c1244c4d002d44603d9801c0320f88038016292400500b41081e0b800451030200c2e5808952101c20900600020301d00b103944402001c03220704580140041441c0c40d0700540794010300c400a0002500c512103001c26181003240c281c10b510f02c0d0300c02c0c010825007214815544034410780c04031844d0b4480d100c80c60401011604582090300c41c0d2039100022070740b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 234516267 1250 234515017 234515023
    0x204050d26040b0c0714090105240f090117010e0a0c03060905090114010e090d031e062c0f010302120a0501020d0b0a05010507110f012d08060901080303010915030506040302 76
    0x9400c50f070020390340d19950320b02c5100740b41c10003800c0c12904181f000703004014600e01160007403450004410201042201d48584100a82c010241702c000c2c0c11000c21803524559015810036800040711142102075410100714041040c0014080c004090b00c1c6d4020501603803103a0003883c010222a08144030a091084501e4040c2c0041002e0320307040240b281c00040c1c92070500382c8090051820f00041d221764900040b04602800c10513143c9180b6007038055244e01c0100e2544250001000100c81c1030a02c004170884032084031141640681d2150f00600a1140103041034000604480c0d048407252100c1c2c51024415041941c0c100000c0c140d944085038000310710341c00340c010480300352040b202c44141a0701e6000549030741c0210791028142141055002c81d180c04c0003113001880030014103220f0805d1148070301580012081d28a02c400841020f008091500d41200d0103036007140c01240c07410440c0d810107140170741c0c0e808144282002036455a1104010410f0051204083e58001017900c40625180c06c010351307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 234517517 1250 234516267 234516277
    0x329040b04140604033516080603120f0c120d05090c010323060310020c071505071a040f0602032e060e0f12070602060412030204050d26040b 62
    0x8140c0002c001e0010b00380b0010651610507036154076a01c142c503010314000c102180700f9038039181c81c610510820380c154120b0410300c54440d100c0040702009500b440b05008080c401c015103414040d5000c509200b0344200d8203420380b48404002a10700e074890500c0c488171440d01403070158100018200080420701104690005031080802e601201d415101c01c2d40114201d4101c41412085040740407603100c4814122190340e50008801000c403003a10000b91003e404036032082c080161554801c0c0c0b810860302101c8211081149041d04009007402030360b45516807161b101d031400c40c41d041300407000202005131040c9030407a01500400215201d140c448803d02e26400319501c050b1044002188000b10506a11054400e4803440e9507091034404070101401880c0c1b88001019a00c501d80d501b800d140d820041007640002d0410b5402007480c0d00309030414900c05480d444650081600400050103075485451001c100e0642c0512615040304107410140039010711031040114003171000a0001c1c20340340d4900544 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 234518767 1250 234517517 234517523
    0x12090304030c051519030603120314090604020105030121080403080a030b0a051e0f090a09020a0806240616060209181b0c0f0a0510050c0a090329040b04 67
    0x80400ba0300c0b41c0c1040f016500000d43d11a940400300300d0584440d1080d214245028581d00300880c00503125a540c070b855080c8011500002640d40e1500a823030b0300d0385c940158211200360054403841c10a80c0009000388414000c9c1c2c0907103101010841c180d01c1820840a50701604082c1076a00c0d10344900d046191680b0130440000003a0508000e1002441c11502003001c443c0010203c000340880b1a058030440c0101190040d0b00c91104c3c210b07000b0907180c00041e00c0c407800703140400260011b05441007014009660308181d01561140013003141c003c001d040030051000360840801c01040600002403040d11a0b1403400e4080010071086204000ca01d40180454400864150308854904081c00b0a40c01c0203c5e400510401454040913400e05d405008101000c00101900d64100c45d403048589080031a40701119030358403150720414440454400d540d08102070044440c5001b4608200400d600caa40c080a00010004601040d020b83c030880c0580020300020310303d00d00362415081408100400716015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 234520017 1250 234518767 234518783
    0x3090f12030e0102030a121a090906091e250b0c0714030c0d0f020607020607080301091104053d08090c0406060c03030504020d170d0b1f0c05031209030403 68
    0x500c68030f60010060782c203406601d0b95644041d10130402004058021003040c040440c42d400c0007204141c070341c46241f42c880c180d1320380200000c0c18003a0542d07180210340850a110509514004c2c9010000810441e081800583e0414025000c80010200140765948016007802001510090000c0003003424002c40340c100c8941046c4040c1320090503110a20f2030b07031283c2e00030060350094000030000502c0040542c00980441d04040b140da0101c0c1196021920079180498003100400c003040182c05a86489031015101d00e040c940f4010218544207c4402c2c2c08040035920313203801c0f05103200e0750392112260881009440b0310266030f020140ca00f0303009444440082c0204201c0c40c0f4207050500407a0111446640c0300d221005c6103032000c60041601603c1283e1201c1805400c00c041894822280e00c50140c0d211469551034840c0500740c11200c8001c0700c01d000d0060080101d0701481c0c0003000642c100c0540c240307085100f80502c0c165085120390442c07600f010401c1340900c18560710020250080d01d05c18280 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 234521267 1250 234520017 234520037
    0x30a020a022a0a17030717040f0e0a0f060506070807150c110f070311090a11030a0632010f02030c0105010807030515130f030302120106050d1503050d05030403090f1203 74
    0x154240031600030303040740005e610030040e1500141c0419080300a901c0e410020301d003025207a40d51484d400c400c580c4156008401c041c20700221544510440410030342d40002001305902d0304000c100d6a009400002c2c05107140880c4000078805910380f112001c40c44c1300c600f0400c11740b0b1524003038000c0c9070000030200b191143c4403400e0400c00d00010540103490b080240c8070301c9058400c0400c04500c0004181a00745030303d807140e001e08800000041d5008520440000c10010300304200302ca15020f4107030036101c0c0300303840300380010003d84040c0030009103040a10f81240c403c407500009a1846c4034821403402d2540c0380500020700d0102c08150081624030510070b43e13041d1810341d100c80d03035100b1064407400703261101d0260301300004548000d040e1036079200e420054101031076200c00524a10090781302e003000c02c10004801c810103400c0d2289001011440f403104c4807542c11600c2d2541c0d00d0440700ca240d424001e00001040c10b1501030b6644000411180803a400c0481d2541940c2c0100c071824107044000c44c010f111 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 234522517 1250 234521267 234521279
    0x1e0301091404020f04110706020c010617030a080a0b040b0a12060c020d1b020d05010510080d030204060c0b060303090909030a020105070806010c0605070e04020403030c020901080105040305030a020a022a0a 90
    0x352650040c0c1c3c0007008159404448020000100202409800c0c0d0350420003004001440c00c1c00030300b420320301d0b010000450900c0c100c5401020741c84520f8035045a00204603440f40c080d0411071043c0c011a40c9500042d0041c01e06010034010954803409550100303552030000f0761818600248005244160420b022102040c403042e0b07580e10100d8082c41c04a1040300940700c0000158024028a82c001000d00f8025052034039003d084074020b40f40c0c0c000295441c1c070103010025040010f44101c22440c9000c41ca407915008006010b800b07031210062907001148040341040c2d80c204165480150300600d0f0201c5411f100c855a5a40d5211034000005542002c0c002180305000b080c10a12486040c1c550030044403207640c4001c01000001c000d0414080c045000c1c040c0c2c0d4480d4806007010f10301c80d0311000d50000d07185c0100000320a05a10941041e81080100000030703a006043e06c0e00031aa0000158550000100903030a05400071140941840076180c02d0303141c3c82550245030554203083e01c45801e0180c07149 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 234523767 1250 234522517 234522551
    0x30e1204050a1e060e01020a1a160207060203040b1305030102040e0106110604030e0103020c0a05010606090602100c050a0f02070e1e0a05010501050306060904140a0e0615030d03050402061e030109 86
    0x907801c1280c100ca4040410415009003a031170b82005051044d104100c2150351042c030008907900d09090300b51003040c1000242c03049a24440c41940d210300040c00344501e4603500968074402d034002c0030500500031810070500c1000c040010080e00004000307540b078603107440c0581940e920900c41c01d4002010540c1d0040041404078090b0b0080d0b4140ea6901c80c0300103600c005401a45c0601c00c004030f079128040c00500880c40038481c1c10060074080d558980c0d40da2800500038503101c1070000e02c0200518207007221801c19001ba04850781d000c2c5609202c8050400c00100f68140a0568441c040b055031020030030403810171024040c0d90420741d0a261400319254213a0b80000c40d40c0900070356000c184200701250007450244040e00800c8401030010424000b2502c400020b00000d5400d000000d84880f4031100c29001441280c1d80501700c80041a40549114000f0365581c0c900c4801e442031699410204081d9110302085031809107007800301c030325070346642d5415940680c030900c078410402d403520024400b140c4e115 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 234525017 1250 234523767 234523799
    0xf010b13181e060608101508060f070203040807090f0f0207030e04020d110705010c032a050f0f07050703111e100215070306030c05060406021507030e1204050a 70
    0x401c12480302030780241d8034100481494a500309082d00c0500010000414501400b406003003000d000c3c02110511501c2101543c0b00b044158600081c43c100a00c800040043c80650001c054101c024403600d07481c8040e400d6102d241c1010046000d005000308040005400030903040042070000c0015044030b0070860700301e01403080b000b8000b03150720808000d945090307006006140c03054100001d8403001403003041c6a940c400384007201c1c0c50751225401c92089805202c0c03420481c0300308509613311444001d1412400b0590f8910a061200c046404000c41c1140019a01031845a8100540d54500707800d10560341c1c00e9031710003140c070001c41c028038018500b070080c80356401c1e0490380780ba000c1c452200380800c92400c0c01201e680b4214071810f0030714080e081c0c8094500d070040c282a200000c0c0c203410350070030425003440703500054084d0000300700412080b940003070503042c291400c2018117003139180d6482c2100544001c002624040c420130320b5450200c01801c1c0240f048640891b8111841c954550f10510b189841d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 234526267 1250 234525017 234525041
    0xf091103070f050d0c020a1a01150c060f0624050a0210090f0b010f090e011107060504110a090f05100803091203040b0301120320100902120f010b13 65
    0x34004240141d0007a640420070111a003003841c2400c102d0f0725842e0494141082c00fa005074007503101d8100b0b00ca00c444600c0360803030703207644109015030520120800032420502440108902200c0030f100784140f503800420301404c800010b2210964803030a03107011200846a200036598010411400b080c094011100900965000b0303042d24070b000c031501401400440e030140d48032400264030310001100341c66840d01030407020320301c02681c40c1820707000310880c0e12505580c0066031515914451071480ea005841035107038000e001207003030b940e00d14200162071824868540c01c9004120082a000010b402291103440000f004010701d0341c55001d6130301c4e440842e106050860308100102d4010382007506150580b04d010008482c03800356111010105a4426401408810400304a00c020140c0c0244040840804408441000c4181100164032101e0b01c4100302c054a0741c820280c01151504081815940c00990a9480b034414110059000e1310b90204010301c5905101d01505402074148501020088 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 234527517 1250 234526267 234526301
    0x9140d051902060c120a02100b01020c1c021e12010504020a091d0a050c18040c05041a0303030f01090605030f060703050c070807050a0309090e03160609021206010f09 73
    0x1071000004056820004140e8001da0200b100301d40541003040421030100a0110160399010300c10002810400340420860b4200c2c1090078902c0180c0e40020765400c2c09000b1640841c1010350b0313541c488510040c184009401a011500c81940c9005401402001102c142d8500716404011f440d0700d401c0742c0044a0080d400f100445040c0502c01e8140c0c00510100301d0724507044402c8081c80c207443d285c1a091002200e581c0d02900d540c00303041c00d00004070002c03c803c81c3c48200790f6080c00e6840c4e104034800ca004850080f41d40d0040400e038490020311056180c600a819260f1706d041035154031541d580c09000d008076103401c12000040e60b080c0092003000310403141e030103003501c0e840340d16040f0003030200079044a402840038400c03000805d40303c0d001403207840c0c0f060000701089107030b528000d007141c14144e00000d40380d842d21100070404000031048681050a184044130401c105241110080c448a540690025201041038240d220b0000312a4103032400447c404400a959001840c2551082c1540c5c0404903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 234528767 1250 234527517 234527533
    0x1051b0c120304120822080a021806100e0105040f092307020a08030601181503050603060115031113030b04210e040507020f06070216120b0103030507031e09140d05 72
    0x10000c90250010741c0106c01c616a0b880210030a0000300d2159030403509180d081184030108500d0700000102c04200783d9003000d04c181c84d1800000b000142040007200078080c10b1641044660b124000b00c4006d03240445488140a4031103000700700500302480f170310b83d01f10066a560903601211125035440398546500070304004981d650350440039040948640e050110100862040942d0018042d001d8800910311031b900d0384c4036490040a4880291150340290031000040c40030903410011140d403103215040104140c1d00003d8241500d100b48041b20340c019814100100411a00551036070103103000d0480562401804200b40110201d0b07070401b03402141441030540d10a040c01c0e0400c982c011543d00665912304220908a030804074100c82040058208513124003a1500c10002070300905103007007444441e25040d90b03a8a00001041c0005414040d0106980080521404845c5000103070f11252000036064480c014040d0768072401140c40d030500400700c1600c0c0e03042c140d44c203204440c5c00000404e450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 234530017 1250 234528767 234528773
    0x9050604050a0b0c1507050715050702030412140307050a1703010506030612010f0c020106050a0b03060d03080c040b0c010c030c0516140312011e0621050601051b0c12030412 76
    0x15a0213040a007029015070440f62140940340d40b000c17841242c00f0b0310b8403a40d0340c0b080d2900c8131040141d06000e14044d442d08003801411a4000240d80070b440d108144100c2e04009030521075050100300040710418400002c0e08400c008000c1070740301d4003511942030510046070030103c203074a5001c00d006140d0811414030006145180c191402c1c000d03030000100001d440c130b80d40307801c03141900c101c000c2800240c0c0d1200c3c000c2086080c5104c40c180108107100509085040910025588100250024007004000000b11781075a044004440041c21154200c0d95034285418409010b041c41c810b100d8042850301c0e141860107400b80742201c1d00c0e000f004a44508104031691aa0407106002e8940441d520090003840703180d40800c1d504502030a400007410350015409081c1c000e6010540d0800e03020400410303502c11503e0080300b440000101c549202040313640d1064012249401825203424840c00c0d922020007941c04041007248461400b6181807104001c98040d81d50359100758410803011440a03e090408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 234531267 1250 234530017 234530039
    0xf07080d1b0c0302030102030414210d020a0e0619021522112706030d0210180b0f1602070602250308030c0a08090c0120010e010e030a09050604050a 65
    0x10901c40c40a40260b540c03070f600402d089803c200c1e000c403180114001c83c0062160b0800204081a0742002e8042500340d200f98004c00f82d016040c0e28a100e03036000300e0b42d1101e030b502902e5030f03040300003010b072400780c0f903503c0501e0b8580c000900c009040058016101800c0301240c40c02d00c1e040c840d03031000301c01c5e488400e2008100c08210540c4c11064801078090f54040301660b45000542544484800d0707104500880b01c100d460f203040024010b50300c030398061903800382c400350003003018007042903c0007001551000c8400c038881d00b654010302c001c25080303069040100c0c01f06624000b07030140c1030343c0036030605041000302c083e44d4541c00d0f40200c0015a1014600b07401c2d5940c0340441010603900810881005580d03950f8007001900240c82e05140d4400200f0505005517010740c4d076a6014000a005105820000c0d002810240d50009075403d03100a4010100400d80c003504030a4415060314001c020f02640842c03140e072070748c1004c154100001c03690f40780003c1d103103001d1060310203440340100b1600ca0303035203003040380e45d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 234532374 1107 234531267 234531317
    0x1110106050907120b190b1c0c080106030e060403271701020c12160201050702030f0f07080c0613120215040605040303091d0a0e07080f0f07080d 64
    0x101240c0320040006c1118404071001c0e941d1003041c0c000d96450a13035060510055030034081d141342400d42c00410641250110341d01006900c00040c230003902d9003000d0381c010f000a01c0b119607624080c0e41590403481e040c6526444a810203907107503100801c00400302407201c0c65960100380c9075801d101c2400b074242840341050815241440c40c0940310610004200c02074100180842c5203011034504104d060f0307102c1000421909040005d544883c0e4815580c00f410105000700f110142c0c00d4204038003912038110001000078030742e03801c10004600703070010b141e0b046ea8082059011400c3c66401040280045e01c02961481d03510b604605000d003110066034071106404110b00d1401011410001c1503a4005009244c00700303c000c0000045032810103680c01c40d84031801001c841c01070754a00080c410320101c61410541d15a50b688030f1030191520254030031400490001940c400f89415001c0340f003a = true := by decide +kernel

theorem cover : BRFrame.Cov 234352517 234532374 := by
  have h0 := BRFrame.cov_init 234352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 234352517 ≤ n) (h2 : n < 234532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
