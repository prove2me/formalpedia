-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0807
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:54:55.892265+00:00
-- url     : https://prove2.me/submissions/68fc8e3a-d15b-465b-aaa7-7de9cb96b0f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 144964028 ≤ n < 145143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 144965278 1250 144964028 144964033
    0x30306050301141e04050705060a02010f0b060f0717040f030f060f0203060f010e030f060c040f05030c01080a09020d0203120702120106060816030908160203010f0c1202070212070305030a11 83
    0x2e040e212001c0f002c410780030400d140c04044c80003800b806018003a4074005c01c4007900c00d03542c03a040c0f104000e0003800e449605c03126a81c43c280c648038483c00e080c402e680b64840c4807441c080c034041494480308111a9490b10a40e0005000c0102181c00700c20742400f14010362140d850411581007619104056980204607003603a244184100308039942ca240c0b88160740703042820440f001010082c0841d09120401116030b0700c3d88580c1c028003041030301031802841142e40d020b8180609944910405031286900300f030306400200c003180452414a21036105100c243e10080038081d100751542d011030300b4400e82083c00002040c000c1501c0b001d50038022804110201d40c28020003103141000c40282c550340000c0c202c45410100c078903401c01c0c0a4000d40c400c081d031030b80100c000350721034840c0103035064801c01a0000b03c0c080d50811160320210040b9000d50103103072001c2e48404003095620340c8500029002100c040e41d022a9000302170aa9410600c8210059409040034540e47e080502c0040d10311500c0c18000700300e42c2d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 144966528 1250 144965278 144965281
    0x9030e120604110d060603080f0702190815130204090c081005041e0201020a0c031b05010203070b012d0b2110050f0604170a020907020118020d030201061203030605030114 75
    0x1d0b100a00c0040d80074041300d01d04625030ba2810300000030f04890300020305880340045c5142c40c1d03164003005810460700c215040b1540c0080784090344100300c6644503a00641d8820b11a860b404000210f89580c4035101100f40741c1c22105a4000400380c5d4407482c000e4660b4001528188141681031201c00140c6c058000188840e05240d6a0605842c110760281d81c500d0700603480c0c10701168400c1c0101e040d015000755030391580d140c880c20715515403003c0d25521020890b68000000d155400401501d103025000b0614400e26880d00b80c2d444900f0840800403000d6108020900b140e02010030303070b18805440b1903410340d9100d084110986071005500d84080c40004028800c001304082e008614030252501510b030702e0038030798030503011500d40d009a4001c801800560026407103981e40010701c0301034690080300d1045864841c09010b070b0032035035420801c030300ca50134440443c0054200b803034001031070a200e8800020300984c3d480031020314917444101140026281d0808105a01d404d025070f1541804000700c1d890b0a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 144967778 1250 144966528 144966533
    0xc0c0303040e0f0601030b190e070c150c091a0408330c04050a06030209030f070b070312060e0c0a02100b0102070b0f121305070906140d0c0509150306010f03080f1b0109030e120604 79
    0xc0030b1203401c1403039240d840c0d5104000c01c620554001c0c0040013508040740740d0000fc1c00c030030310640e00280145609031040b134440301114000340360702e50f120b611407034420200174814a414a0352035000034182440d42c40c0c100400100e0362114642003008261b01e580050321080c1103010181810400d1020b107815900c81d04c1d00f88a03240451048441c415454106144030010045800001d40000d41c001c0010181c541c0803c02c00d207a1a80040000f11501d6081d5191101c1440b406011030705642c0ad80d60040c1e015107814807103001c0c09001001d079103949503101030510b02c003541081036403402185d01554070064240c00c90104403080105502a1448031018850682848588091a1030080038648a225505411010b00501240d14000340c40003903c11a2685003082030496454800700c1694000d121304000002c2d620b1a44e01b00c8001e0780d034400410340c50902000712040c00c076080011035400300702400b00d007141101400d10489008500c6500d40c00345a00f2200200140c2195214103000180c1121041000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 144969028 1250 144967778 144967793
    0x9010b09030d1803150b01020c19140d080d090b0c180103020703031e150503010608030a0503040507080610091b090623040b0c0c0303040e0f0601030b190e070c 70
    0x70b02030035141a000320507445011284003200c903400640020342194003410903046079003151408140030303000c4a2000380c007081030050784140c0400030341c08144172a0b010b002c1412504880e00b8074402c000c3c000301c0010f505489507806940402e0818801d071b6912503c1c40f003040007d000781c6600601000b44075040425081d080810a034100700303030f03c3c101a80001c2c102c0801d4040d510203443e0050300803c0044040f10010080001e00d9000c560f1141180e0020000030140350500030301040d51000805507040c0b401240040e41c0c190000b078011100c50041140120340c0306010084d040c443e80065100b072560764a40800e4604980e0a0003050100040241e004031019402a4080301118031601c3c00855004012005c07860344004880031080f204070002e00016034228180c05444207840303d00031380707055104400800d9540d2055109104911180c000080c004502c2c0d01403180e80050b06040100d10314190000207100d0b80880070941c07404002c4002c0038000c0110078450f081d8004018240404800c0d115126004d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 144970278 1250 144969028 144969043
    0xb1806012301260405100506190504050a0209030a0b04030f050307021e010e0f03071b05180c040b0d050f010918021203040504061d1e15151809010b0903 67
    0x20b060050040301d007070040010b0070302407040c2e0071421500007007420a4648141c94a0a40d41000c00a50400d80811010301c0c112042c555002014101d080880340360100344006464000d003100d107401c0d4240300b8a80c0b280c500f40280301000c0d1041006124500d40740c074000d09003180754100d0b0301c00c0040074001c000704550000b41c1c800c480c4040c580004100680ca05c8403d0250401d0003441001d809092039041602d40000041d201c4580b040c40c580c00071707054441c5400b01d5030205d4070540c0d600000015034280043d0501c11542d405c9081420400d01d0161503544110580e4030940a03094203a94407001c12900d0304801c0d01c40da002d414071080c24002c2003000700180101060100d40030740b1484e11180d00c00d100030010402c6600501c0058414003000d0359030141250258280c1200c0b036030320011000000e428040c0380c19058404541151440c0c0c40352030349881400c100c904000115002898507200a09513520b00000c1c06c02c2c0c084a4204136400c90804c024400404011303030021901900c00d0050003c0c0c0ea4022410a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 144971528 1250 144970278 144970349
    0x301020f040833150301021b2b0f0509030703030504030308090c010905010e0d060504030804050d0201060503030d020906130b0306030f120d0209011b0506100b0a17070207030b180601 80
    0x3c2d101500e030101000300a04103052005c2e40b640c4000781080d580c1c114040c0c0080c0780e940c084213841c46d0508035050f5803880e0b24008240070310700382400414540030b0300646010000c0d075850302d4401d0610201c0b1002c42d103401e00e03680007500072540105003042010780c03084000350700c10121800790103a10b90410028040200380c1c001c3c0f60502400c03000b80c48860b00c6082449125a81148091101d0300709030402800d42007040e58252003500956000c0100d150050050700d007118000b44c0114904103a284588000750031090815900c00c3d81004030700c100500000e0184090034100b40956038a0404c0c104151801e805150b030b40b042130304074500d03584000b64144141c81c8070850007203016079136451034001207900d01c64281c0e06004154051903070070180000003c0051044c440c410540c08816118500d616150090701814400621450350748082e07040b001c0c0c0011b800c05c400c1c0c0112145146c507036032200b80c0703007034210b0b2940300480e0510380700b0709801400c000403030040800c1d10a0132903c030380900300c0507041c00c0c1c1108031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 144972778 1250 144971528 144971623
    0x30b0d03140c0105131a0f010302060706020f1803070f06080a09020409020904050606010306050d0b16022d0118262107030509071203030e0a020301020f0408 69
    0x703610103101d200381160b40703030307074416008011504e459014001d04501ca0300f000c0c1c880444c28014031040710305200c1002c2c0581805405d11510340c0c0303036908001f0940d03c558000c44559030248070b003548110101010b000900003c4a10104186019080c03514041e01070780854403603102e0000030418a500700701c50320303040858031102042c110501e00124014007508400250414030b040c1c100310900802050140c0500400d0341c2c00c0c0a4038cd59001040301c00c900800024086c80001c80200c1c541c5150f40c41c03140481059030050700c02494142d500380742d580c162500003010070400c0e41200e101080c000e1040c83c60b10300c0c04d00914090036281d1f46a541ca007807080c10b850104600400075a01406c2204020784030f900c02c855002c50348428544201e2108400f042d1441d0001c2030414020800240c004100c00b01030720f0707a4140510560300c060303d00314003500300603447d150781c1d0180140d240051307102030006091a40e030705070040d6038452078200464a41200480f05108079450321000b290071030440c1302000d0040220062 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 144974028 1250 144972778 144972797
    0x12030519050a1b08180a02101805030607120f1401360b180c09100c02060712020d0206090a1101030b0a09050a0b040207020f19030602030a1b030b0d03 66
    0x15928010300c0280c440303d00041a1545003010990300030b01940c4101d184904405900003001e0300700b941c480414034025071199411413080c00036442420707061082400044a42c1c3d400c0d80e1003020906103001038440200191805900108074017403130003200203107480000d080014032900c1b640500c2d4040c06000d400810b0003c0c1e4500c01312588540c0b50315000c0141d903815813814420002a4100030116407000a000701030f54541c01c4035108201c00300c1441a142c07505082d260019000420011200c0006003c041c0910006c100000da1258800380032800c1c41805043c3c4141c4130104080e00c1c000c01c0303280c140115841041004288180480d42e0403102d580200360440602c0342c0360040c0e0141460660840d00320361200d00009058005030071850090314842401c00c50300003400d06000c01d070301c501c1c0c001a40000303c1040304156401d1241d207500b54564502d800c050103e403259a182d00360f0b40203440b42d0b400952141443d0b54214140c10000d041d078485420100582e10720a408500c00041100c80501800fa4021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 144975278 1250 144974028 144974041
    0x105210a2306100f050402120712091e02011e120504140a0c03030e0105070206040b03090118080c2b0e01020709110c060106080c031b0904181203051905 67
    0x55404049040040c10360b4070500c0c00c1c0c1c80c1031114a19074464071031080c002c402d0009003804d040c422115000b040d40d54403121a504c5100c00d031f1324500d00d541681d2940e552a8150300c081340382950065180c100d034414250701e0620301e000040500d8417846040b00707031410010800207819007010100c14680c0000501081d40d50f914200b81c0042c51000f414009640541a42e030702c100800040c1d4441a40d10a03101c0c0d1034411150b0f00119105d0040050080d0051001c00c000d00c1710307040c044059580300e0350100011548100000b2140340000d80440d0440f910080814810090380e400d00038814401d8910b1106c941d124645040b14034043e0b840d40340e100030701488100181c0264400d0080340064407500005111541542031300550903404900441c41c81d0081c58000b281c01849106054003484050600781d096031180c00300e101d420780722201c80d039054140801c850030094449010319450780401080210029140d4106420344003d048510030030585460200a400003448200b10b6a8107101e1000044030366444 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 144976528 1250 144975278 144975323
    0xc0e0415090e06090601060e0f0a0b0a0f0302030606070f0c09140a05060409020d1104060e18010b040605012102130f09050901090201230c011109100903081611040e060105210a 77
    0x1c451141c1c100b41c0010700490f00090bd04014020030015a54407405600c0850f0110120b002c01da409a0b440081041140d0102e54446a250007141c094010744550329502ca545070f0403108210b000c205a0750381c0108103c99903480f0301c40e01d503004509a5081c00920060740c0013900350398000e20010560003195100300314130744480d800b03c1c1c040c0111020300e40300e90805580844905c042001c42403942c2d0b013030804000c61400d02c2e0044a00701c0744180c4803031038800c010340c07244010810400c11700f10006a0078003e0502800a00b40080010031941c092074040c503081105020642d180140300c1801c0347c1c1060038000c0146d9000b4a81d03141da2115454100c3d50031151881080103200d80e503010355181d803d0440001a41d0b00132401081584002c4401c07100c1690020402e031050a01c51202801e00c28041c002200c2d90a0280a0001e03c40e2040310740c1c0e01d40c800344000050489014181010440d07004c82c1c014003240c2010052110540b409101900744401c2141c191640c5080200b80200000c050043c0a00380785080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 144977778 1250 144976528 144976549
    0xa05070f0209090f010b0f130509031917070e0904082b020306182e03050f0f010b010903050304090c020102120103030804030e120c01030c0e0415090e06090601060e 72
    0xa200c800e0b1030514941c000e40d82c2d05660360b490700c154a0000c10f40c0c01031074000c04010385058040d0248052601d088520700c003d010007070121103180001c0050715038403100440f08114108064641c0001c003440310007411800480202400305124406044522079903c240c0d03132a602551150180d907850208101c640c0c401f00d0700c42c103206031510300c010320018440007030b801640c456241900e50714002205582071604c110000e4841a2403690701010f03450109c2110102d411140450000700c0c2401070b40ca03038640d8903120f0b2040d0010710039085042000710004081c0035003c0e070502c01b440c2a100f000e04580b10283c992080c1c1c032400001d03640e81e243c1c0407840d43c000e406480020403503a802c05c641d5a0359043c0a000414100d404030000f0302813003191400c510381440d6142c602284070380200888a681c80054000700305000300c4070306000703c0070045e00e050742d15409481141c1d02c0070321028a50500d814048000c0e84e680a900e0801500711404000301c2103000190a4115806460441100d0100038007082c0464038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 144979028 1250 144977778 144977783
    0x902040902031e040f060216080c0307050c0f0105090f030109020d0b0a05090d08070c0312050705090102120406020a030c08070606170d0309030e130f051f08060106050a05070f 77
    0x115000034429500d5000d540715001c5408a880000000c1c030503252038410480b00284042500000b00d008103006a020f03010b22460b40c00200041c0d103a6844216040c0c100003a40c040c554030009000c3c0c20040240810000a582030701d1080414405c100060028001c1102c014003411051840c0a00e665003504091285500076107800c0e024031b02418502a400800c89a82c000c540c185000315280ca100010b21101d004d5056890340c1f00e07901c0d16182141c40100500040d402c11804c6442c690060030b440c820380740580340c2600d43c07940e201c50010001e0700f0020300400301d04020b40180b0040040c03d40201c0c13051005949407400c680242103030f25000c8064080ca10029110529141010401c070303001032086c80402c01064201c60540415507802c4043d0f9181000080c009825200b0801050803c42005085448070325004180b1740319810210007260401c84482403001440750580440e17403115510100680704081c003170301c001c1d03050807170103826803003103003040d84c01c2050000d0020180644a06501040c0d3b6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 144980278 1250 144979028 144979031
    0xf01120b040f0b100e0a1208120906100b04030b15010908010906020d1d070e060303070501050423071a090a050306070e010306051909020a050408070608040c090b0d020f060409 77
    0x544154504005040401c0071600824001201c139130700a00903100302c03054103002007043c0021801c01d01038021142c2c011104a0712900280001c002e15009034001902c1020f8480040205107808100504041c0e40c1780d100c4540d1040821090001c591000c01095010b528811311050b03507003802004969468950b4401c0620354a442c1d0501c0405c02c083d0003d1500c240500b9050009402c16071102c0900440b07146503e0b0607a01c0000e04210800020b003070580e11070801400d6900f000d00700d403562401d603041101d0441701941d2000c1704044405100450740420a90390300101b16150078417407010001651030b01d03001d0b40b200700414422029078030300b00704002615019058071801e052160000d00305ca10b03000d1081c0d002c41d0500300049101d00f800601d000d00240e0030b4299121003840d1010324802580102c0c003110400a08110220f4943c40420ee0380c0003c24032035643c980b1038506418442e02e808402d800c4011118280301320301c81c0c01d9803844101c28031103804507488480100c21100003486445107030b015001d4035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 144981528 1250 144980278 144980291
    0xa05090a080301150810080a020405040201230712050c0d0c0213020408060f1f0e0604060302030a0b0a0e0a0c051c0c0801021803060103050d140d060e06010e030c0f01120b04 76
    0x98000660240b040842038841098640300c0401a1b12291401d008002d0f40c1d9005000f0b4401500d011f42091b5000750041c10140d0310800d1800215920b9465549800c07004100010000c0421400000003031200880740380c0780c1e0404144000c02c503158a019200a410455082861415980c5841168081c021000350843d603850351926103644410341280c11150880c0807100052004a80d604100c51100301450600d42c9903080610f902c0c02d2600142406401590740d903400320040c2c0f030421a000760300d4041c0501c10010b180c000e002205a80d44015511000d4204400080c00a04038a45150030380c1d804032020310f415207101c540e240c4d500400e441e015180c0050802d0003d201c01040d4001d200940820900da1260700e83c2c90f00785507550741300703100040c0380c0c0d072003d602d80340d890f4800c154800f0101020a28203150400035a8014159034094100e4142c0c843e100041c0501c941e00400000d082c0380c0b042e0003901108002e2030000300320144840155051007500ca2038400c4c0c01d101a40888030704040100200a038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 144982778 1250 144981528 144981539
    0x122d041e0501030c0207030c170c3a0b0403050702060c07030303050726010603022b020901120903021c0c060e1509120301031b0e0708040b070c0b0a05090a080301 71
    0x310498403039980401e1504210403003d6102050510960750001d00b140016850070b000d40c00a000d0305900740c22580034030781062041c1d5a4601c54088980d07081c103614040070b0140707180040c03c01c0c07031100140c01e07592820681100044000404a0b40940c05d03003072103a2911418004180c8034461071065405c54017881201000305909540300f1401851a959401c0c545040c040e060390b00c62810011110428001034010400203103e03800900602d088086504003910321000d015207100d510b809411140c1d500841c00f50181e580c851039035108403140a00c1488020030f1510042c4d00d92350640c0366074400d0000480ba41400900408281c003a1035071110081100e0703010003410300c0d100c01418440800c079141100c082803c0d41c0d400071703008001c200c0c4c030820705246910710380e9241008417070000000028031070001c0000d03031100c4854015204080d0b03912942c0c802e20b0180740c40114110300800b01c07403d0113060001c010200714034100c03a03640b00203100d400084c1070321141c07566480c01c43c00780e00080000318000000f045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 144984028 1250 144982778 144982829
    0x403031107051005011508060405040201020a0c0e160c110d032303090c03070302011b020109031203090201031103090c0402090f0d1b06211a060c070503122d04 70
    0x3070160f4034041090341d88500402000c4003500d0512000900300701d0105800b8585a40310507000b03032050040750540c0400b03542e0301414a4640d03100350301c503849000400484484040c100b000300d250710b152085241d20382d982c9070400c3c0410234400500038122a84445d04250007407814605540c0d40c0b10221000c2582d4440a0a440c0d00c112000364903405204020251070030002200d01c151b80c0d050711941c03408035075640000d07261004c075841a0f0400a142c500040440c0c41130317803000c00124442e5004031720303400e483c000034080d03e0045d800012003600410400c94440710204503800200412980581c1d203045480000c0d414060540100d54004045106a020441090200402010a80c0318800002e546d54425509507107840c10b400000441c0e028559076803403c07640310a4004580382c03200841032000741c02280298121038201c5000340d00c000018011864108000c801112013011020303e01000310072880c40d1071815000201c145200400c204400c00d00403000e81d80503001e1150f5071007060800c1c02d01c000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 144985278 1250 144984028 144984043
    0x7030e0a060f09020a090e0703021c080703030b0f01080108030a050c011407080105090c0f0703030906090f12090b0f07020607030207030b04030309060b0102030306151e07080706061205070e040303110705 89
    0x34400e110170340c80065610380b54001d101444030044041c0c4036062541e000d04c004045250a030361410098001c440002400e10300c06460b4041c06a6000509041040140820b05e001505d0490600915800401180c080041103464451403031030125200c0e40341590f4a800340c0b010591000340c00d80f4a008108540e81d0081c280750480e0000c481d201e1140c0c6079801e0032600f52094641845200c14200081e41c0424001e170054180b0754801c00700040e104503182c0b22007a20340c1124008903981c100b407902a80c5025407102d002406001c00ca03011a14260415802e0411482103160080c0101004a140d20515009014201c01141c00c403444a8592a00745001401007000d5081280c10720305e40f950046140d403002003030b603100e50b40103001c0c0c80703d03911621a208100e80180005510140d0501d0002d22001d802202030511984607094580e00e403019840c002d4250b500350342110a0354000c0d98020004030704001140c07001c40d10801d40e03801103a00c46084c120701502c01a0a20b401c00403000400380c08100c0e0000307090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 144986528 1250 144985278 144985283
    0x714060603061b07060513020306040303091b051c06022221050a020d061d0a02040506030105070807080901060b071101020f0303010b180609090702030a111507030e0a060f09 76
    0x480059032143d040a69064895016000041c0284800800250280d200b02d4010b281c4015401c44441c131980003a01e02202220124002a01ca041352003c004408070142c41120404014130f90240c201000300300c041d058000e80030070484d42c110501e13052065560480314005841041c08803d004581559040f0925622a4a00d012410140315890380c810100040b07246610001826020585400f00002040100d1040d0784069481d5640b07140c410424080c1503e0340c1c07194010b08000580c0340100001c41d0001004140240d04003020011082d42c03104000394051150304180920340c44403130310f0500610442e002489140c00c00503008091041c3d0a02048511500f40c2c01c880b40140b0b40081d2940380e0000784540f210002047c08151032071094044c50400954020b4050750030206100d00141c1020002c0c1d0b480c0001d6080000d580301002d070700601007608a0f400d000204070048c50780040242d0b10714000c140c0c4042660b40c00e5100c3c1e94420521411400a400141c24445a07003180d1042d4000d04030003404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 144987778 1250 144986528 144986533
    0x1809151f11010c1b06060e1f090608030f0705070905150405100609140102010e070905180606060a030b1c03110106080601080706050a12060902040306060501021f110714060603 77
    0x40044414140106122040c1c0c40d0740b13901e0400140c21014a06030701d52141200c895842d070707001082a81904000c2c0b031013000e45500c0141c2000c801030201040781c4403508004c001c0e0b0304060052211074000030032241c0c481240000c03550303600e4850a01c0c0f400c00c0c3ca40c0d006540a9800c080034008555000d6190441170b40e030448080080b9200c4c101050f05400b5079116140c0800c80d8400104121584c02e03010450429040c00081200c03400081054200049074110482032551007051002091079014540c09000300c2100030031280c1841b0700055500d008440c0350808058480404da003d0703407110300d10082c926801640e11112440341745000b901b041040941d4440b41c1d0301e0b01000280003400040c00c1070403207035004007801c10ba50801008580b554050041c0805206443c40b1039240c800151180500401117007000680f1103040d450000280d91407544a03a04560026009000c041c0d03071b2102c0c0c4403288001745c90020380701c82c4a13218140d11f4007484101512000001c00c0030300c00f860020482c1803141004405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 144989028 1250 144987778 144987797
    0x150902150309070b0c01020f040807061b0c03110402040308190e0a03032f030309010207150506060d050601090b0c0705100f1706030703060c0f080703021809151f 71
    0x10625414041120041050740c000d96040126002d044c004001c8140783e034002626180c840b200d05c03400755000d0380c4074248540c0002401c00c52070f580803804e29048105080d040384c0005c02500d80400c40320050002906460000078245c9541c1d5803a03041f140119841860140c0f0f8264100c1000300c4d913040d800036400400e954068441d01c40c5007038003440c0244c1b68140c8540381c3e0004031184c0c003c075601c1d0361418558501c40d4981000c2071100c0070009944580c1c144400903a030cc15061a001000782c828220116044d824a414040155074980544e500c0010140340021070b035448200403142c01c012030740311300c9038003000007210ba0384001c01180200960300150fa0041d4510251013040301c402c64102d0043d0000f49012a0107400c2404041006802000c01000c4412a54503a01d4110841e42d440710440041050301c6040b1400e070b60000c075880e5014000f810114104404a84c0d00c064208049000500c41e203a014005020301c0880d20400c44a403c015000249100b08640000c43e40303072511030a000414960071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 144990278 1250 144989028 144989059
    0x603070905041a09060105011b140a0c080f060f060d1a0a06031b0621111c0510180e03070803011e090b0f040911041419020f040605090a03150902 64
    0x624203041f0364041c0e444824040564440c2d200c0c00350703958411140c81201c0c1c0090b81707844008001000040707004072100e00d58946081c80da2450100310315000109500408100700184404141c1e481d803150303054a86207684a464a0041c010012050301e1000141141003800384a400960298054030702c158840d0300074060f40007441d1006100da01c02c00b000501400d1400500100e184412190019a5240843d44848065440c0c2041d04610070800708140b08110707011024560303018858100c42201c8522820908012000c0c4a642680400307900164a40e25480205001001100d2505801c0400b0b40c0d00c03561200c604104030702c2540036101c00241d0129011440380450310455010140080c40d600004090400344000345c040408143d80e000c0d000c0741540d4064030f5030300490750b120740240c0f2002102d240010703000c4202140c1b580031a24040c41803014002c42c2030004100d605403485400c0c159100c00740200040c850b0b0100d9040108402c00032140c00250100c40e40007641c40c2407007155107120194281 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 144991528 1250 144990278 144990283
    0x31b05030903040b0708042103030b090f06061305061303030201061a09130b040207050a020a06090501050301090b030f0f0a030806010507050d0f030209100c0c050105190302030603070905041a09 85
    0x3074829008076002040100014030741c00005000c000c1c032581d030540c1890703a10910300c00c0780c840c8240660384680c60403152400701366041c803940402120449400600d403c00b1003049a07515001015175010b01d0000468401c1c0131324a4a07800020b080042805a40e044089032581c0c224082c2c2c40114050342c2405d07000b00e003640c10040c80e9805000c2d0311038458202111641046240c1120304802d01d5015901d0700e8240994450740010081b060050008004008151040c004c1c20581c82d4003201c100542c0303000c2480b5603a80241243e04455884e46c01003003c40301480001d0070103c003400c035261796101c1c91013001c43c41400030070b00f0340c9400c0c000e0310b40c044265160001034403e4890000000c24580040000c0315030180510140007030404249001400c0c5070307140000c00d1541c00c11407460408070301b05049140c1004401c0b01e01c440078110a10f8050f0400c0440310f100715040c0b401200740000e16030040700003105e0340c0782004440010300c6c03890018030a07414107041c040c550310203041c025280010480c00047c03550000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 144992778 1250 144991528 144991531
    0x2203051c0804030e0a090c05031b0307050a0c30030b010906200a060f0b030601050415060804080d0914101401090209010306030602120108061008060c0a0c05010c031b0503 75
    0xd4840581c503a88954084858206031840740b03a001042c138601141003140c510440407035031001c1d118a940c904007000c42d4102003040c01030b842c24007038007002000304c242e80c44400d450226065082280000c003441c41c265503c1d0f410b2036801d51429030040c000c440c00703a443c020001c6d110100c903102000501010303001110013112034000c030b9022135482034480c0c2c02d0300300c0800c8070700d02e030310040c01a2103450800d43e540c00c09803144440c6803804680c5894401440f0301d03090080c1401403008aa04222200c0d80707100d00040713100144540d0060012201c001014030158804940680c02640e0f030030040d01000d441c010340d400341100e244c105140f0034611108121001d0344505001e450351080350000d00c1e86401220702c0a0f5001461090401d07448000c00030024640e80050011440d034600715000320340c109000e5900d45500107014610b9a05252010403601034041a03c42d044060030b2030b01651202c9100094521101c014002845076180520310210150701d0b60051146506407406550410340403481112140030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 144994028 1250 144992778 144992833
    0x9120206060a1208090d06020a0e03031309151814070c0209040b1b1204020f01091208070230330405010e06010b030109060b0708070303050903220305 66
    0x31034590600c600e1403a10360b1800380a12034503807079117031a4850000c1420f00944007400c803016900494035420650b0059140144580298000d5080800b85000340c5403000044c41166196030703030354410851240e00ea031034603030142c0212210101d07118a608070560081212884400344520800040b5008a202d241b1071b0022b5600180502d18503180e0f03403501900b8000c041c12072490b9001c0445d80003005032800c00500300030300045051958518090042c40b1807000100b24030f904101c2641028800c0001050510403c5504000c2c0740740c0364001c61002c16036050709411500e00107440440d41c1d000c0510140034002c03a12603204140c4052090022040e40650700420a005011a0020700404054000218154498018800410308000340048103041a50030380209401210000046c40a01d2042c001c0741c005024001c3c01a00c0d041c000d8640628500400c00300400300b684400118101c15000c006880b0130b5003208604d440040c6038054081d0a440ca548401c0710607004008840c000021007404100b128807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 144995278 1250 144994028 144994039
    0x12040b0d0f0e06161107080f060702060402010903060f090b0903091206060102151b030408030109050c09090604090309030c09020d050c0909060120030d060305101b0c080903030a02010912020606 85
    0x44854880610b2541d0b07003c210f5003000b02c440d45e250740188081240c50b00510080c0007409039010481081810198000e14900a6601800c20b010041c1d03030081c050800c0b07980141300042e000c19442c000801410003001e01070300300e084a600f0300c502c41001000034191035800f11754070100c0081e801710300ba445007011948140540c1040464200340f007038080c1810340c80360100401111340e0807621600b9460390025101641d80c017a000c40180800441d5200700b980200c800c2d0840f500303008851000944002c002060540030717640b203005000405025540910117168419186071110b500c030046200250440c0c89620422810000403413011160901155036400000e0420402d90f0340d220700542c0c8000e084001c01c3c4400714400c1e0f003078400140c2480505046511124042401461400c101c1d10f001500428515101e1801c080d003994800e4140700c0901c44140d90074002c074450a64100040c240c0100d41030076816000000742a0a12541907204140c2e5910a00c84180c1c40b106568007240e07104011034440d80c020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 144996528 1250 144995278 144995281
    0x50304210504090e1b1207120303020c120f390606030d0e06030604020f070804293c070605010501081003050a030507020d1a0f1b0f070512040b0d0f0e06 67
    0x2d05020000d200a401042e0850347c05942d07e4500013500714071300b40168002a40400d6a8550070b0040c0904006004e254410904042c1d10510380d01e0244120740b200440c0702d0329801c41da4409000307290030005404902c00c00d4000c800c2c0d0201a503464003003c80741680b19004060b45402420b001782d0013001400c0000c1c1c103040c110360b2400184402540407141001c0700340c03418400640003907507190060002d4030812043e400e05e2200c0c00c4032111840c01e10503080d140010107100d012500c01c80701d0716040310600e4802d9800011400a403010f1104541035000002034040042c044050103000d410480c1202c0c020380c0c40c50129030f44c2d221100f0218800d0f0100514940150b0300410200e4424800303400e000f1300040251445025507903441c058903002c0c03c0003c8540c1c00880800002040d8803080c650301640340004a034440000012040c06849420801c4840c0400891074406103d4104519441c40c19010f20b4550b45507158404e10704aa00309d044502101e07410007011186e41802ca016161002015000400c0e85 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 144997778 1250 144996528 144996583
    0xf0602120417070506070f021c02032d0124090b0303030412211b020105100303050d090507060503010f06050a0903060b1224060a08070303050304210504090e 69
    0x4030140200215491080030008104c66171031000604c8958824100c1c142e0460a0740305006040c882aa10135010006070403002d405a00c0115201400c5d500720040c5003202d00d1036003040c407e20821881c40c00e40329841d2010a54a21028401c402038018441c844030041603940c99490040c1c40c041c0035201d4150b0418408107001415a6001d40160310346401d155a809e4000e061900c01c81071100789140300540c41e0b402c840601681c408040c210780600d84001d204a00e004040000c445140b840000d0406c0030014140700540d4261f40000341c0e50380c0c001d06565086507a4040181150400c0c09100d0015105400020320361780104c04803020003850383c440e030300e40c11b1441d15010010f185141c40242c11406038200004240b8045c000c00c003540c03a003821048400700981c2201050101d0007420640609107014060024540004114080303a0b03041c13070601d40e0f80d40d8610b03281d501401422179109081c2e015200900145400001500a0712055281008007040204441c0c0c0c1d42d850347c01480c19291010f0700100710 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 144999028 1250 144997778 144997799
    0x1f1410050d0603050102072a0f2306030a09020108010b04030b0109020715050a020a09050607080910120908030103031d010e01030b04020f030a0f0501080a320d090f06021204 76
    0x405124051001404556a481310381c2661300c00c03602240c14429403000c42c0d5000382503800c411901000f01a09941190500041c182002c0d02401a10a0031741107025090000b110410405022031000e000583c40f41082140b0b00040e110711041280030503800380001c10704640320340a03241145c2d048011440e00342d1030303d0405030080d84428001c0d40e09401c803241c642c40d15000d90007014000c1c0c400c14030041e551146444000d02001640d00031601c01e05017040920045070440054030140c0c107044508c04450401c0100640318203141c000f000b041e00b81480c100c3c20920808030b0195040383d0007500c41e0042c0c8031705640701c800c00c080c04c14000e038080781080c2c400c03040d994420380c060001254040c02c01460000710060300382c0c0503001110000402c84e201c031441d8801502c14003903a801051043c0091440681c00e40d43d41101c04500042c43c01c09201d038250f000b0940c00a4201c00512515220540e1407286c480000100003401a024101d0101c2c00d6910000f011880040c41100c1da80490045a0615040018080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 145000278 1250 144999028 144999037
    0x70f0806010e030a0b010602071a09090604020403051504120305040308040f0305130801020c010c02010501050a060302090406050604030b0f10120605090304090e07080f06010e0112050f061f141005 86
    0xa0402c0103142422896440801c18114294028140b41c11551f1510038001d00c0c0507104e401000340048010b220010905014040d64603a50040394100002e80d5020040f40082c09a6030010f821445410f05404440c0030622980380541d0040021103560110344d001501610001d66005000642500026000c41c1980c80d038495024400d05c0c089107410758441120003040400d4101c145a039500040c564800c0d0824421507080180a000911096140000042c108100783c45200107242d00090f0305403042d82c85601200140030018400ca4039941ca0741411003500400701c980100c1c8903a500040364184076404180300c02c40d600740c403207054059600e680f610041d1401a08400203031100b8480171608098130300522103803030801001048031902e8218210f140000f00c10942c1c505401260046c000c15008009142c1943e102120408054565141c8546400300c0d1003040c8d0503500803541801141c54a90000c985c440318a1040141070725100e885c5c07404500d441c40c510702e5000b00b0740c40700392940900480140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 145001528 1250 145000278 145000291
    0x609090501140103390908060411090c070f0f02090a05330406120203070603020406090b0a0e03060f09150c120601140d0207030809031603050306030115030f0c0e070f08 74
    0x40c282c03001945440c0c03030900000781c22517486826404035000003a030300a91113001052608000e0880d810107407078003004420300a60581c060b0700e801000407190490f5108840316590310000340e100601007420500c82d0021403500407407203010340c2d4004c5540b0300c10740d005031030081a100c003007540160030071002602c04401482012080b500c0307805a4425035038442c80b81e18014500d1768000503100400e4810142817184a070894410b1500c1840301f401150340c0880003c0588440c007503101c1d07881c400440207a031402600000d1b0340e8144507480c00c001800306440035480c05a01d8100444824102c0c3c0e04850402e640300f1900c080d0003200c00d01040c10b0110079640340c1c540188060408003003d58091061a002d98020001400d926400089090816074030480060740403800710301460400e10b00048210001103481400350070010048045031150303400b907008a0340c2e040650b02c02c1107416607c0c0741681c460001c01e4001e903102081000009180d8509403940c501c81c0382265140a80c0320f0303102005a074400809000c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 145002778 1250 145001528 145001561
    0x30b040b030106090207120903050c100c150b040f0902092a0c010b18010e040f060e010204080106090b06030402061912020f071101110307060e0a0c0e010609090501140103 75
    0x2010032510203104183c094600c9080c0580d440b02c15050414035a8048403515042201c1144c6c2000403501c08246500c02100840fa85a00103080300c6007224091a40000038000030540c10410919030b0440d4004840a40300392414084000c03400501c3c0115010040080d4202c4200300015000c0707001c07001514462050341c8090302885104c0000c0c905260040c58408030140e55a1760651140d150030301140d0022250001007030385640c18060106113404019100a06032424481b80a00700266500295104e02d4860001c649480c4c2c0d07190314501078034851180e901085e00c2c00c150140c880c280340f400c49110b560080c1c81d082c81e205040e040c4448407440403a20204118000032170b0b16110300d890008120b95a40c40c00b801b42c85000c01c0c20300114041c04410024148050b850940c283ca5101200b80c420b41a040303000040c010414100301800d0140110005085040386500070a01e450115505030580341280c3e280c0c074010361a1644441100c400f8040c3c1c082840180722b070800e146d03200e50400d099044940c1c04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 145004028 1250 145002778 145002791
    0xf081209060d050f0109060b090a0b0a030b041e0e01021306050a0e060a1d0a0305061303170106020102030f0a0605030c1516080a0e010c08040306200304030806130905070501030b04 79
    0x101d00c4100d901c00d4808002d0b41c0e000c000100580c40c001d0007210050f0104094049c989220000000c0d86510144030b54444184040349001000740030794000ca61407030002c0d00c140b204a10b84030b5945c1c241c02d028500c0c01c2d0810320702a00c00e614801c05201703171406031004508000c2d445040c001c00380d48581050401504010a009030608940c81d51000741c26201c42d99181c0d0080301340c00300c425034201c40c080300da602d0140c0c0c1e0000741080440c1c000078210360071a410003c04010254030741000c40e030b40128410030081203164000000340303141e07055000398420403100211785200d0703c3d2041c01a054840510a0580c1544844121540c1d4a4240c034000240035202040602d0301c4004080b20700012144003041d00c440300040340704010190802407130714103171000b480c1006c4120060340d00e40c2294041da020145c06280d4625641030703100c1101c1001880740d03202500c45074503031500e07190050018404580700c81c02454034801c4070405a07a18010002843e40c0000038042190508004400518035039102c1a4065141c0c00d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 145005278 1250 145004028 145004047
    0x6090705071b09020a03110304030e060d0609050c0c06160f2d020708010b0a03021f030e0a080c28060506030304120b041a130602071113050601090f08120906 69
    0x2d8418010700e000a40583c1303881280d4005070071074a04604050030708804000304000603500010940161a0403179925468082c01500351004000d144c218403070041c42c10040c0900c1d0309144000e481211011421621107940c1c5000f00200301c0c07440c80d141c00100d1440c40c10200341c24020040d00111102c0c0441c2840003041140c000280d081c104480c200158101c03100604c070101c800c1c0140c070240da00940b0b00303c140518507030100304000388440040d008403458900440381c0912a1300040080ca0031401141c01995a0f814502050381c40f44a01241f90f100d400105500382ea03040080c1200786e088003110004101003030710b07444090400104065031500003000089840c080e50005010070501940c030560003885c251512c040398141c00d106010049443c641040050f680b200f130384580055101c90096240c140601e809035180700d002e00d510354006105071844074411b90329800240b040009982e00720b00310750358030140b0a80d80c1903070049400c030742c0105020b98048a00e1a00910214038060842840d208412 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 145006528 1250 145005278 145005323
    0x90b040308060a0f0501120b0d061d070518180a120f09080102070f030f121109040f0b03190c0503060403020c010908030c0309210d02030405180609070507 68
    0x4440440100790001c0900505040c4080148050041002c42c00c084501309400030344070b86e92903c00c0d002d0301d0b604e407400589183c81302800c0511184d4814420310485d6111283c50000c4078000103c40d000e40700e014000181c0e4603200d40326011042103441200710030b8803101c42100e0720b2500b860a42409200300d82031140024210040604005025500c131800c03041804001000c0403900da021600681c01800040042900040360082d0903a0504040c50421100c20085d10f03411000402d1070141480c00c65510480350b0b096006041e0300c03100f103d0030800605801075940c11620305016450b0150b0145803038140e03c5900c00b2007032510300e008a4402448036900c0700028505401241d00b01c00581000e4554400b1b1b507001424000542030f200095030400340368000f0a03a4034040c0d0061184210842e0300e1511843c800407c10031a090409404d40c0d10144280d04041d680ba40144581c9025a9148000c0800402c0d00d900035806200024014480c41d16510b03c200c50a4001000a94146040240c26000550030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 145007778 1250 145006528 145006531
    0x414030c1003020307030e0606030d081909120f17270102030907060e06030c0d020a090506070308070210150b0304030e1e100503010e0612030904141902090a18090b 72
    0xc42d600036035a840c0c5504c0060070380e03141c1d24212805034008030601c0040e41c0c0c0803480c6c4001c00e480345407103843e41d62400352043e00b015524800307070b1245242401c6d030414041c1e0800800251800381d11909020102c61104032200b000e00004108102003900c04600e0340428402c414414000810840400300e103580e403c1401ca82c401e540c071004a9119100c20030180342c1100c001615014112105030841c9489115500c1d18814030140020703040e4005103203000e05014034058800b800001d0a06910b410b4070317207405004444140d54400162040170403a00c40c02040740204c01e1250001d2030340c10845454038040c2402a00081c00450074050011610081078495200c03600d005000200c5040c01c41c42920244400e224150040350208581000180030b11b40124500c2ca410084c150382444614441c00e805508500400362071590203801d0215510b80d592070b050900e80035601d4986000102403445803070700c0803441100f20890304020614000c0141d200240115020050030710000300d0300f40e8030f0f944d031508815070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 145009028 1250 145007778 145007809
    0x10b0a0e040605010b070201050d020a09030804090f0f020301051309080409140411010503040308061002071701020405030f0708070303050703030902130212060109050a1502070b1602030d02120414030c 88
    0x2050401c020301409015050051400744507540c03400405400007081b520a40401050158000a80343c072064468400c0701c0007160402000c2c3c2d00c2c0c82e1100d4044c405481d81c801400407160074911282590707403051088904840004004c104001c1c4518041c0c005441d0001007a100f0030003e201c00128802e190250740c1080403103c1000d0094039081ca00036074900c15841a0314100442032040000081e0026a900d0304840119002c440700c0520142c201e00d440402c2d00308a038480280640360801600540280c03090b240304606441c00c400700010708658480451048425035440075000b0004280039000a0110602919004c103244441e038021030000005600046102a40024140741c80c2200c4d501943c0c10240903c3c0212145180c01c0c000703140c03051580a0f00507100414402220307000c0c002c01910004244034158151555600c0204103075010b00001d0990090142c135090080d030750320110b5241160404900440e00f03003070400f14000c1054900001243e05403161280748451941c401c1a031500410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 145010278 1250 145009028 145009049
    0x303020a0507090b0105040b030c160c050a050906100e031c02030315060306030c010807030b09040b09150907060f0903060e011d07050303070204050705070c0605031b121602010b0a 79
    0x102441c01602c1c1c1107065000300002c501e07007019101e00e41e034400100c4046440401c4600c0d2030b6164240310a0742e61040450003140c042d0f0102140080100041785281110011503200c3c965035034407014018207080c2100c0d4030f82e02c005004644c54038180600c3d0483d03403010020b0101d540803014202505074984240c01710b8405a4004000c00801d8425441c54140c20141030701c8880c11424004042541c03007003011012030520080c1b1000a0ac0c0510903444640410300081c0549440d051904150355541d0b41519030b0181c0e40900488403e03080c0041c04018040d280c2e00c001420410b10348030041390055003048400041044050001002c1261342c0103001802045400000340c22004404480c2c02c00f0300c2c40c0c2c6010454019040400150350007200395000944c050301c1c044ac0598448504030303041d101d041c00081204005000205160794081d000e94804d0244514100c0350400c0c2c4480c052850143d000000410040030340010000a20401944e0a074400e40c00041031a80400c00000c50700f9501c0e40009110b034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 145011528 1250 145010278 145010293
    0x90f030f0c0b0a0c0b04020112090c050307140307090c020c090a2a0f1409060a05030117010212010308071b0b0703020715050919030203010501030f03020c03060705091315030302 78
    0x5404603a600100b0310500d01614128111001400758000250041c00d1501c50301c0002d425640205107002078a80050f5041101d00c001d0700d0300704e141200c1c1d03004660191080050118401d04142c01c000581107000f401080d410307241101c0b482c080c02e0071364000c07011401070146054041e00c0d6460001d0140041e40c001140020241c22a51a031180c807080c0b0000040c4cc0d402d04903002c036001901500d10803124940082c502d0441d080040482c800c58030120340115002a405001d140e000000c0c41c1a90052280411413140c441c13205400d03801803141c2c005042c911500104005030200e0010268948120f0555042030b240341c0182c1100c0c0600d41c0b1a4100b200c0000c0c074101095418040e00c8081e0405a03207034401645840360080843c0200b0540c94001c10050b036003400740e11400781300a40103550090083c0017035038591038401d9080001c101c046015100d03144845a203445c1c040740e107620403e200c0d50382c1410906100c00b04040034a00071502084555280014400352050860b840040d40c0a60001c0100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 145012778 1250 145011528 145011533
    0x30905010b0916050a0c0203030a020325021c03020c0301090507050a060306080d0309051203102417070c1b0e011a030402040c03020d020711030c030309031507090f030f 74
    0x2075800c0404002c0c4203034141c0c4104054990708400c00380086a10340743c8540c0b0785d490404103903550044940007035818032005c00c842c805070b507000008110740c80301003041e5040d001114514040c0310600c40c400a501c4540740340400c3c404100c1107d64202d582c002d104548803400044040f900f154103034030b400da48a400c429003d0065060000c1040000c110b186004c1180c68981406941c48552103840d410401d901c9001c070340d0521404200340480c41c641c04490031f41c2c0342410008a00b44886510800d1000b1030f80503150781180c88210b101114801103a19811555003010f201004c125400078010801d004080d40c0e2080410702c2d2041c440d0b821009a000400b8050800742040030280d016402144407000050300d80300d6994244042d20341107581075402013031070098414280e02074000d400f500a101072004c1107d005102c0140f500c005880303016000d5071859042c44060644920440092a4140e484990180509070181801c3c0341c0c0400340380f91003640f554440c200c0400c01c6003194402d99600110320300e024103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 145014028 1250 145012778 145012781
    0x510051c030318080306120a021203040609090e0d080a1b26010f1505070b070302030a0b010f0507080c010f0507051c050103030c030c051002030c070b0a090c0b030c0706050703090501 80
    0x10710a28010f10f0100c0181c3d54588180340300007460703a03014460000f440c01c0104800c003d42107200e40d0003054841c26031001403095030fa0782c029200e00300000d9914000010860410720032010b203a04e9101c017a107600800702d10b082da40308401400000025039240e40d440b00100040803a004000314030342c0d913600c4400b20003d941e02194003211401e2144038084c8010400052020030039401c50788000d12065000c100908140c0e800e02a000000e00400303910000c00803050346c190300461141458600812107600c40c00011a0140c08503000c07030300458420000702d40481e10385406000790303c800c1e4002003507543e00803d512094036004c0d1030420110320045200400781070204600411507e10b070804105a40c17458400814550b500d59014051000745403152040c01000d100791241c5880000080d50b40382004903520109601400c4c0561b24200b04a0102d4280711301ea0217001c125680007400310340c3c82400c00400d02c160b640701510b105415802040f4504c0040c02038014241300d240151000100b914a90034402d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 145015278 1250 145014028 145014041
    0x90513120513090204050a03030f03020c07090914010c08010506070606030c060801180b100f2c0102012316051c09060501050f010c03030b0103061a18010c0c030201030510051c0303 79
    0x50341d43d4010700050001e0f845115240003202e0705884c040c10000c002c5541a00244511601c168075030140103008150b2056680001004902c12061164180b5484a000703003203c0000100707400044117400104811f2504c1000303407242c54040e190005000d580c1e951103500221056000d003000c25a00801044a0706d000341503142c0c1c48206c0b080502c001040040000e1082c000000700301c0600034410b00d0b15080b140304501c014046080903c1614a00a0483c03090a40d02c40b0031200d00d006600f0001d0407040302142d95980c0d11070098005150f1000e4507034074019510031100f00e004004014040c440c1c03001d891342650a440ca1460880b40005841c42c1c54140320307040d03540c1608442e004116044645174240d81c803403800b02c0d6141d014a030025002201074012405080194000801400030041840c4080350480040a20800c0045441c03840b02c9120015030707503541e200001034005450350a0800155009421103944910281400001c07142c843c00007420b601c8039001000d80c601001a0b1000400d6007500c03d24 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 145016528 1250 145015278 145015289
    0x60105040b071203090501020304030903172104030c0b0f1603050105010804060b120f1606020a0c090c051903140f1003110301060b03070807031103040c090513120513 73
    0x186041d050401c110a6407040c440000c0280424000b104070043c07182d80a91031959001c80290f50307034102424000c2c080300c40c1d40810340b02c25481c104820b40e148e090001b1100080105280001b00144882c411220200003c1007502480050528000002c900c810414401d075903204080009080c07443d11021010303a464180c038141854400140050703070700003020b44c1d0700551051000c104441d00c080492165203102603908141e01c610b0391070f0014000301080b403445140c022341034203081ea41d451904aa590740c02d0b0300302030b12040e1000390038089880380741c1242e44030340901d040c105d191100d0310349807241d650740050042700061b5603443d00002007095058503641000c030419140003075040100c240000c06810b44001014402fa40c2c000c102a078501390803030002003804400e55610703072511940180c0307008000c030b038004000782c0b0700708000d404c8000001c162402581c0019414401302c0c1030642440040c0400b500c0c1c070b058501000b0543e00000c485061000424510350f450a40f40d6000d402c0c02503640310b09e074010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 145017778 1250 145016528 145016537
    0x10f060203120115021f0f0506040b0a05130615050c0f0715031503080304080309060a091a04020d1202101802030c04021c02040305070612020a3e010e060601 69
    0x80700600b904940c0c00505545280d03480c2c000d601c41c1a001645000c2c100b1158542001e40502c10b100c068080d98480c4143c036849441c144a65640e07201004202c55240040d1584170f0440e0909100c98100120b088000c42d0b541840000c0d11900e072040842c04a404031400d40c005480081c01c90300403582400786001c404046001400c005003407030341e85010021408085410140c0d80d610040181003120b140f14001c1d900070028070b81d00d04060828420607481160207907840e01c5100301150301c504d404c4c072940d80c031141c02111400110100174075100342c81c9400741013030303900007801803000e070228a00f00944078259059030000c05d6500306081d4000d050b40d04076041d00c450300107100030900c05a100441c0107420300d04101c40050341d4022100041e8410100e45208426241c404a000310806c03000041c1d520594025458007101ca001e03002860040c3d20a030044680011044850445100483c109100b0480b00c054a00f080e41a0050104c401c0c1083d00c07242c20f1611380d150707407140c0394413981882140e400200c00c0c0380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 145019028 1250 145017778 145017787
    0x506040201030c05191b1509061b080a050a091509020a09090b061207120303020a14090105160201050405030111030103020f100f081504060b0703080a051303030e1207030206010f060203 81
    0x170401d8008044003041018403102d15000441c0f00c0308a070800a489601441d01031401c42182c40140052104c0c80742110316620b0004045d15040a01d0008118526103036180c035542c0c0d503581c840101400c1e01a04211000e910340080000080151440c0c0440348072041001612034143d004014a0842c10760103145c1c41c2d45401d44a40c0800c61900003d58050000c4d900c0080081d8a070000e00d180010070b40c49114914080001c41d8201503250b00201400031050341e64008200440b521304005120741800385010510800ca10791641e003071511851149401410800e0820350346002103070079981280303213080b40c04900200500843c54400100c0c0e044640503a203a0030100c10000003d001c01e08400c42c402c0900c0440c41c0081c2514030b441c1d06a0140f000d001c2c01c01c2c001e21fa9150340c00005908106c2e8101c0100c3d512034000b80b40000c0303d101e8248103071158070485808401c5520281c000b0a10054494010f001740501d14050002c494000c001d810b00c030303500421140d0316056001c50700284580140b01103400410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 145020278 1250 145019028 145019047
    0xf031104140628021f05060f1003060b03130614040b06060c0f070b030a0b040903020c0d020301090f080a08070809030d0b0d12080106030605061303111c0506040201030c05 75
    0x206045864002e072030b620383c1d03821201c520307101c500402c6084440380350192500d03040c61680440e000c00464a9045040601e0f24280501c000781c51045818581081c0544a442c0492078001c1c0410086030042c1800100300303483e00d4aa42469204840c0301400c241c0e00441d800030415580b094005a00340760204100c00c0c01d103940c3d440c0e4070f600d02400b41072080d075012071760341c2c1002010302c0800c0c0726110040855260507a070701c1202801c1e804c110b407045016881d2584006e614101400342541c6250b0503800340c9030191190040104681c8002c1d000c1e40c0641d42ca194410004035004002d0500034003e2021645890881c2002820888010300c0b9101b0420040240701619600006441841c00880070100c0ca5560b880c002c1200b0704d040c008050070103442c242030703088402d8204840e181a80c0300707a90180407150329042405030b18031075041450000e0340c0d20481000454a606d018075003045c030041c4501110503402e142c90140c505400c0d0f040e980c903003000003400110340e054400c500801103107007482400c04291a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 145021528 1250 145020278 145020299
    0xc030c0f04020705100e010902040513050a06050c040e0a020c06070c1109041109101514071b080304090506010807080103050c090a0213030506010e0c0c071202010e0a03030f031104 79
    0x408000c1e029a0300800c3c08010007905001004803035080d900c0410a007180c3c003a44902800780240161b0250745050003060303900c84212254100d0903084401850350340d01960710080100743c014000b9894250621010032010b400d260801e025040c0e0030000740e220021102c10382d0505101030a0401404040f801030400908481b07212b00548008580859070303175031181000d000c001441541d050340840100304014080785450300f10000d41313000c0c6840c6542031401070003d480f01d900701034102441000c10320410b00000c8400300d80c403c403840344890710b400c0300f641c61005518642141d003100052544500c2000095640702d48a550300c10700500d071112003940345455031500d0380340fa628018080c05010b0000349028066030129040d440c0c0d034100300c6c050b0542d41d040243e00c5150a00402100000c0040811413500b040070940704a0507500c0003800d4810714049500450881c6220100e0501407042c000c1280c650318105040d0046010352145525140c03220700080803210b0a40e4044164101400140001c1080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 145022778 1250 145021528 145021549
    0x1f060b0406081f050d141b0303090d0f02030a080d0506040b010f050307031d0c03120c0303010e090c060f04090c0906021b18040c1508010806040b04060212070f020c030c 74
    0x401600340c5554030950f0398485007050300a5904640701d6141801040b45d45240b0544110b0038405940c2d06e50700385203101011a1010010607455802404154071a107005808450340c5446031480d601c09220304c1e800f190900365149015945417070003290a0301d2540490068940c8040200d400700103419030360b00041e144c2c414881100c0304100b008000203800c98040e03807240c007030a520000ca01e0a18107a0304240303036481d044540b50301d01134010032500d0504401c00e6000d40d0044118800078500303581c20074814040c2410000d005c8074003032260070003140d215100c1c81d008205072000c110b800c5a4848c180240ca0041d10703d0244d200040000d465001c10001380c1c049400940d0740c01c5100d01d00d0300b800003500020540c51402040451022124080c0b00407c0700e054490360032500540c070400049200500103a0b10310f1001d206180c1070390845000600060304440c2104d80c010322a160041c1003500211003d01e6410040f2000c1004c14001c00c2e11b0750050b601004503d04200049009002240590020035a0000b2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 145024028 1250 145022778 145022791
    0x30709050705030414010e2e0204031e050a06090602030601090e0702120a21020301030201032307050a141602030c030d1e270501031d0a020d141f060b040608 69
    0x1124200c1740ca40c4000c1d080400c2c0004140304a422070180b80080d0520444144d82c030587ca1680c0c486024442a5140240e4040300e401c01c120124000c01011100708001404c0c0080380e035400703108032010005403c2d10813030b001280170390b07001a01e07894000005000c1101680204401c09064810800d43d140e0016800000300c1c44041460f40f6080201001c0c0c07262807219100c121141040c590105540e8030560107141268000d980c00d0280703107030140b024580221205000d0040c003114130300040c1c0c564018001015550300074540796407210700300309010100c1d4202c40a80041d41001e00c60303030015413500b00000321a041d81100602011640369101514202405659140181100c070a9124035070180441503c105500001401a08180e400380f000c080c04d580030b0383d404246041146200105d50354414010410703150001c0c003c1d443c4c10303001c000350300080d140201c07101c00c00c51103c0b041d44030080c00b440f05040c4002209805a035140d044042c00d540d960341000030460b0040c00b00304070090303204401c0ca80004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 145025278 1250 145024028 145024043
    0x70801141f0c1704060c050c0901120b0403020c040905060f0912040509150406060801060212071104150b0a020307050f0a0b040210110706050c0d080106080a020c01090f0602090307090507050304 85
    0x1180d920f81981c441050f0f8040e124202e0b00420000366060b0848002c0724241e119034107a030746151005003004010f66080c040d004502d0b000c844200006885030b4a403e4101d4024012240302d842501e00040980340d503c2002c03a43c0d504800d082c01244a94550380c0d94100860f40c010b800542032143c15841d02c8d000d60322680344103a002801007003c8a00d00030065001c070710040c10a0110f240ca442014041c08070030305c903900051003415004000d40c5481e805031620710b58003030150354601688000700801340083c02e51060507540f03c1803000641c420300303500402a1880c40e0300515200e00c410b0816a003002d148081000311500030b082ca4074002088c440d031541e070082d4121400c00d041d01c0c0251007101d440804440d801c0c40c511600700c0120f2900d4002c405400b401c402c82045400782d800b03598048444010030301c1041c022684640100b078151800340c014010441100000003164400340d114442c040c0c213544c0c026101258001030030080380c14140180005000800010300c4141449400105644402400075000c1ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 145026528 1250 145025278 145025297
    0x7110a14060901030605150a020d020d051b010f140709090504020609040207210c02270106080901020c0303010e0105040b0306040503041a162418020f030312070801141f 74
    0x1607000703a010320041c20700901041003600d0314502100c596030010350000050b100c0c8032b003500780144c400180c3c00c5010025039152400e19102001c4c0300c0419030000690a115500c500c42921450707910b10540103929144045c42e520380c200740070040d0030103480f078000f40407047c100410040585c03541400c87d20b0070801a180140d96049505088001500380d92242c40c444036500c10113900346a0241d410030210b03000b02c84001194422900780085a0000d6002d03800c0201344200422082d07029221255000700480c0002d8500036103018502d0450b8000d8200415801071440140510306007031161600203207003a8002c0c1380e036007490f03200c040d981d00851080e0000c2c00e110040c881d110144c41c4082d20072001e291007886101c5a41d600d00f000d2803c4004140c0203401d10041840144403480d40101141a61505101c4901e00759036001d12408a0301c26030415003500c801c000c4042c11034000000148070b00702964861500c1c0d418000c226411048092048d8801d100c56520554065010760310b0806420140c00c207211032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 145027778 1250 145026528 145026547
    0xb01050708032d01150e030d0804141203010e010803090102070b1e0304030302090102010e0304060905060919060206090f1621060c11070909030509060c030d0204090207110a1406 78
    0xb40307182c2080d00343e06a00508042140900441c111416103440880c01d41048070904011a80d0042d11240c05516a010300e0340c0140d030501400307000c0d42143c0600f40c2000d507190b810280601c1c0c4513581480e5401d6200001c0100200080c150f4035602402100024610300341800700000d42d6405140250b0b14010f0300003407403c101d40340d071000881a45418010740d5840380340034240030b002500315500c440d001d0b500381845000c0f2a200401250140c07115529040305190410f03041c05030769003040288907081140801107448031001c02d02c10b60001c20b61079006060038a0030403000da00300741841000380708a42c032901f41258103c0001005105070380c401c01140b0801100710b00164a40b41d43c0240242c0402d29204081d40e20540c442c1c020200320500e03100f1a00025a01c08900b8101c07042a070b805070000744c007070190091510344440107042070b46a5004aa0a0502981ca01412a401648080ba0b482d6000460404001001140101d00c91041325100e084a142c0035071000514442210302c0d105600c000b404101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 145029028 1250 145027778 145027801
    0x71115010617090c0a060c02030d0e0307060f05070b090c030f03070b07030b0f0a0801020d4a06010806070314060a030206090a0b130519060c15090807050715030b0105070803 76
    0x113071160000c02e1016002c0c0d0b506006030090019400070380c00b0340104c0308040c080078040d000b4044001c2000d0010a611850210215035201d0050b590340204082082000003003419400d02a0003140c451024055210348001058078000703643d06070041070b8105000700e1000c43c524192440e841840360802140496203540007075280ca540c2e00403d40d020188010200e41c200055025041c1c074041c1e40301c108600b441d0a44088041189a0504410516001c954424106607518030182d00e1020741022003076101e4401c080c50512000740c2007205564440e00403c0401541801840c05200b0900c03500800380c200540841d00000d181c0c00080c2c000ea2002500e030724181c807950a041d0081c084d10740455121901c1040580318160103205440c4500060042c0d100100c6000c5c4c208411201daa131101271010615a803210440d80c0f290f540c0a2035959549100d00109210200410030a4480c86c040c02d0520304017444110b40041c100c42d88403c1525080610342245d030894103c581c4190420781e81c41d120341d50314040e5038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 145030278 1250 145029028 145029043
    0x1006020a12031a03030d1506030e19111002011a01030b0102060f18100902040c02012c07030c18060e0108030d0e032203060c02060403211407111501061709 68
    0x680510002402d184440c6c2c050b4403c2288402c98031411281640e40c4004500f922148185100e1642158050040207400c618072556040e11600e00c2c101d180031001e0000303442c3e105c1c20050b007002d40d44405c0300d2000311078504250b800030002401e003000900040d1000039661a001040307600c1c4141c2d1807012842c0000c4002030a041d0500120444021112810004c0c000c0d1201c468224011402e2003031f014030880c010f0096018003072450344004625070380b0744040e2100000c980700701c2582d80110800070010405000b550b101808144c00300100d90b0300d52525a90442e400c81c0e021400080b011001406006000300884070200c603642e501003400d89090003813038110b04c00d002100c12207000104d82030070030201d00e09580045a0040b202001080f0030080242c0c1c440c02e0444008000911000f88126010342000040340b000e042d00310002070006002c1c00c10715002c10150369440128044510040418500708003441c40304481285a1b2076952411002924170880308480101c2c1040600025212100800104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 145031528 1250 145030278 145030331
    0xa0b01020f0d0306061101050702060c0f040806070512100501050405040207030e042408010b010c0206220303030f230402060901140d0219030c09050103050903040f0b031006020a1203 80
    0x720b02c81000708501800600c0184a800c000c01c04a4500252000041c8111072254419801a0881d581d80700c0181860303a01c26402e50211036401c0c003000c19105002c004203032290009480d82c0b035071081d0440e81c12a003600c008105485040c400c04040c40f8a0740c2c440c0a036002c5072803d980150b200c0c0c000780740546020083c44506500603107002441541c4a003010722149201c028616008189a06c501c20b19099031000320020740840c071403031041c0700141004d100811290b45034003030101e84010642041c0504454550003500002c0d101e0182038000f06c541c1c4102c1003046c849a50f2000140d0b804142c03480100c100410181c0700d84004110104140d000e4503500b0325540c03220034426503e26004401c20000e40204850380340d040004119440301900911400c44582065203801003c0c518040c01103001c0e110043c082c04c0301c1c0c00300340f0000031440c01c1c1001e540081e003410540580c49142c424920321602e15507a20240840d0311034130340381c008a00681c88017501030885180105a007034800040c02015250758681 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 145032778 1250 145031528 145031533
    0x210d0216060903030c050310150306090513031803110409020d0203120703030b0a0506071506230405060a030f08030c070f030215061203310303021006050d0b0a0b01020f 74
    0x4410400d441d4002c40380503100c1c1d00d0800c81040080400c4500d8001214000800d071321025003406500180761503201c06036100e00e07004c00e039a030303d840c100d83c02c0d00c000340d40e8070700c984003045092010141c00012000e48006209082c11020749182c0310450110500c08480d0301032591000c0250540d203d10048001c03064000e01114072003517140400c803001d83d116100960001c3c1c80c1840140091601400b0381046480c014001130900c2162344595a0030715150b10640103140e076400c40094031003150380c3e02107002c60010300d042c8041e40f52a014041980c600802c100e00c21107101e00140001240da107440c2280d1900802081e490ba9a140503518980c440e0820140245510011860401d503000a0892211009004500c0162907520078030228510300214851150024841a0b886041e4aa100740691903002a1240d00d01e50030b00b80842122690740082c0c0058203c02d0404140f55018000d1400419040d10388881101c00c617196030014210141c000c4140c0c039280c02d00001940e100b0048581080200401e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 145034028 1250 145032778 145032817
    0x21e0f04030503160b011208090126010b040302040e01060807031205040302090a0501090b0a0806060d020a0e071106011a0d09020d020a0f080c03191e080a091403210d02 74
    0x59030000142c21508842c1c09010038008121804000e0040c01000c8d40005084d0801513148010365540c00d1020b120126040c0f0041c00d001e5039884600d80310b000b46012182c007a507884c298018041660b000c050200d89582c10600304103c4090001030903c100c0e908414000a01c0903100000c0f150b0b4851540061340c041e45940c1070103036600035580064120384418800b00007680b0f0040a1200c5801035214aa040760010400600701c1e08100b4080e613038042c13004060144450b100e0f1222100800c0035101d41000590078030254600c0002000002d024203540240d030741c1c84100c111901005403240c2e104404006485500b54821500c41c2c030f4034080d501ea8018014000540c44d40c43d040c01c924a10b12406409119010003030025040200380c5503036151a540120b00c00421a407034500794071080451407051194010584004a501100038081549407550b0309000e0b2858001a21903070506100349500c0394010044082c00342c04aa0080e08841c0b01b0055056142c8000f042c84070002e004000e9900700d201000385 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 145035278 1250 145034028 145034047
    0x3040503070606080d1209020102061504020c241806060409030e030f010b100e0105032403030d0c1808030a0e030f07031505100513020904091208060a0603021e0f04030503 75
    0x594000740d041a84d11071b2600303811511034a0a4500403c0003034050b82220340414114034640d1070762980c101c406807026203403d200700c0060789403801061801122008a02a444004050700c800c0ca410800781082c0e981450284071800b0740301c0d02c002d01034902c0355544614210825000342c0c1c50b01d04e4010000d060301d50346442d03c02d0040c040c3c00101c014512400c1d081c0c800648050041a00345454901a59160b05642e107200c040c81d42004c8040c0d001d21030081082410401e40d0b410070003802160000c11010a40c001e0742e00000d0320140c4049000303400c00100c14814046080c0000c10b070b87c0034400324a0440110300d41c0001013810080c0c034802900e11405182004802c0c4800c41502c0c40c207400c0080b50030850fa40d02d00840a0306002d81e40512030303006e4418940401003100540252154480092002445401559840070b800c0311507466400400c040300c0c100000c80c54143c1c4140c2c005c207440d040a51501e101100c902c510029034142500c29440081001d981c0c2000d107509440103180e20400b120b41c0e425200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 145036528 1250 145035278 145035283
    0x2030109020909060405121306030207020a0e011e09020307050a05070c0e07020f0601051f050a0315170114070905041a041a030d0f080106081302100e0f01110d050304050307060608 79
    0x125410343d43d500c600c58171b990301500c1c07500c21688c9a08a80e2005483c1e6428144210040d610004d41030342e11200b0007101003800c00020314510700804038821200345a012510303600802040603408009070318810300401c0301031500101140c40d40280351030031560702c40652800008040e05a0403880c0d0200803a0104110b850300003840c2003008104c9811502c41c0d81c0c0c2c0700100300504048034000c5112041c5801907405890007030010302110b58a5040104540240406064401c50309c3c0d8000c032049000c10800c001e040c6000e104000d4042642a03001e0082d2800c03420144c85c000c10f91192602441c1d4400c40510051804403101c891802e00a0013400481c030b04038440c003000906400174601c2405900e06a48056002d00303004c0034a40d10903110900684e10307280003900c100e0001498100d5058240c40d9050060303440c102c0f15111003400b5107440301c54924240034802003000384c000d4241030140c03003450070140c94000105441c1e41021460481e642e40c2c4c8a00d0058110b000d1071000a140d41d00b8a1008540700002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 145037778 1250 145036528 145036531
    0x131509020901030b121023100e150f09060d0501051302010314070c030302090a0513090507060c050703020906041107060912140901031a0604080106051908070e040203010902090906 79
    0xf40e07001d0203e80d82c01410803658508519120860f60311001c4001b114074096000455030b21007000341d00c1c0140101c0005001248422a100307014a0300240c4203006021241a02d030f40c2114400103004003030202070010415040625038680e106442c40780000e0740c2030703603860302d00c0724403030380c454003d000f0346c01d1001c171416011000e40c07001c9000c68241120350020644501c00148244603d0303403000007000072600c1c264000e600185401e504110031705401301d00ea0301d85080391201c88410503000100341d0190304005042501c181c01032000c0000310f12106000c20400a544802e40c3e4048682d0b81c060307180c200c001030041094a2003019401d034003048650600055510420075507015440316860001190000c42c0da05410190401c80c580c4103104a01940d403181d07022401440c6035841c46218002c0620001750142c00c160301400316603440d0f032020f011905090040c01101c846c044143c401c2c00303050410168549400e8026080c1d83d1001400040039568250441c14401da0050280883e0f824140e03106500c5000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 145039028 1250 145037778 145037797
    0x20120010c03020d0b0904080d0b190b070b07030219030b032503030806220504030c051e070f0b09060711060d02030105100c02031f0f0c050705070605040503070513150902 75
    0x280c410302c45d1030b5080a41149101ea0744c0031304040d10380380104040c00c9c001c0c5100301280da00310004006081104220204880150492203a22600d40c00c00386071141c81072070014046420035005010121807501d10702911480a0f11900f4041602c030300e894042880e000d0f00d0300c14181c2d440100a04446034201c903601d010180ca0080e83c410307200e0380e02c600a020500003100700e540c10500803951915651900c03070b444190811b20901c0c0421001000fa141d803442c014140c40c4501c00030a24610302d5110403c01c015507002000b1b1101080403051800481070b1841c05080a041d001d44000550034080004070210100501d00c0180119100c1001040f400001c3d0400d0140340d000b1070240c0d842601007070280001c43c071003950040040007002c01c041e44101c0116a00e96103003082030307110b0b48802d00c070b200b240c003403610246103a40c1c90a44488003424100d1820701c07240c0c00b0406001c020071040c02552000304075074041c0c030380c103450410b00c00015005034801002e803031440100c00300c42c40c4c6000c00c0c4000640c0003403003041c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 145040278 1250 145039028 145039031
    0x6150415110303130507060f0801120f051b040c0c0b01030314072f01030b0a0902220915060c3201020715050c040e040605100305070308030124020307020120010c03020d 74
    0x207448110640348448e0220110000c2070f5444010400740b500d0202d10038007140f20341445003810003143e540502c0d01044041030b03070071850180100000c3e401c00b4441c1c003045280c0c42c130f008803901406803689844000103020103810051407207400d03400c042003101110030b010341c0800070552107a08461001d205101011225034948042d00c2c00f03480c1580309000f00141000010100b071042803420102c80020b6203c0c410700e20313040000502d0540a8030070911903400030603001c0790104a107400c80c01d82044200181e0414014020500c81440128030a000c5000304c09820642c1001c0c3c0d0b4011a00c01d245000240e1802c5001350b0000460070104421074000c0280556951800c0c0f100d46c5400da01c100c0940200d0085a800010034400180854203d8000d6600201540844604961240ca900f0b08040b581d170410341399810000010000d100980c111b49050b5402d52105d0025480c140e84000e44074450ba24000c0c0c10000c040a152011807034260101c1e074880e000400030840e842100d580134001e07400c42001e1110a0303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 145041528 1250 145040278 145040293
    0x40506010609032a0504020d15091b0c03020309060c16051e010c1103120717031b1b0f0f0c030a05060106080c040305030d05090105061504151103031305 67
    0x15401a400030b81a0380e801501d405140d442c0c00ba0b0240e5001584003122110780c00e0807000038240d19248003c1280b07002c03400d03020640110194081c50380300d19603801002020310304a19241c0828074528000314416891420700d80501f602d0508900c0c41c0582090958404800107401c101d0340400680580d1044092000c68900b82d82c13401008800c501004840303d24820f032420901d000c2d0b10600c0303240030030b900c1b8154030440d6880700c40c08285031024100024044205c0055080b05100074400000f02d94555603960360b14503c0c110001849591241e00401c10034180814415400801080450501c9a803002100c6c003106200e00d03400d943c0e60b0a01c005007483d006d0b0700264049420003003068100300da001401001e071a40781180c12211400000c0900c03811010510022000500910090034104100a408102070030001075450840c0e401426580c80ba100500040300300382072040c1910101c40c2039001898000042900c180d403a0000003050201c82c3c000003080180710055400352048440c09a011101c3c3c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 145042778 1250 145041528 145041539
    0x40303020d08070f0e010203040906171b0a0b07060216210302040308091909060f0509060f1003050a02090a290406050403150b030607170705040b12150a03060504050601 74
    0x2140c1501d02400050003540b131580040d01880551154900620440707140966506150088901c2508a010546400ca4407410140420000c004c00404900a400000c09040300041c01d800140d10952100107008504074007800382d00d9040d205240d40748107010b0007860300340c030301f02554507810046803244928011003060f03a24402e100342d60689920589003481c10b0440000c201030141049245003420201d0f03680401d080c040303801200d00404d0390260180d03d03642040f08001d88044014020b6003d030001d1901401c0b84d0b0f0b81c903014030f0001031083c00c00080d01d403154065803011380300d403620726a005800d2840c000342c6c150707402c04207a007080d019940c3c10100c080c2a1060000e0b83c402c901c03541001a01c24001070010421100348a850400c070994002b443c0715901002c0303420a0030448490000c1a081028452a412941c410640c4600b56240861034942004082640303805080c5a001d01400c074440024080c40c0c1c003141800c1e1a05004004040356541c038a801005440111011101c501501000180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 145044028 1250 145042778 145042787
    0x50603090708070b0c0c0904050a0807030f0801061b0f23060a0b030303060120010f05070c020f0a060207140310020c06070215060d02011d060a0905040e0607050304120e060d02040303020d 82
    0x14007030b1241003d440701c0146c404c100880e40c04094004e85e098010740b51240002030041c1e0003840a140309440f040715450948102404003c4140d00440a01007c0282000412198501080c4656002502030160307111410700c45104001000c2072445210340c10041d800d0304200066092040080c03201c10f00100c5000014103490313003c10740da941c0c04952820710b11828940300f44c1600041c55800000003541283c1400c4050941d0350a0340d4030000301300003418210650078012103081480100b81d4030500034918000d0001c2d5651030314400c0301101800c0d06050f155907a02800740c4000740d16600b4065444500d540300c99074a802003914050050b100d010b41424a0380501d91017603104100080801c3c4031000d46d41c00546403880d03200440b07220000440c1c41042590744120151201d10315998a1203651818001400111904281c0c03801c09175000c0007c114000d07a01c9001c8a62065000240107048010480d00391201001c07682c00310f50056000c82e02181e603a0241e4041c00c200d0340a0350866500c4d40c0591010384 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 145045278 1250 145044028 145044037
    0x1206381309020d081804050403110606151806270a0e060120010b0405090606040e030315121f1a010e0916020a080c011a030706021015050603090708070b 67
    0xd41007511803d48601084114014049480704061103213015060000060100d402c110b908801141c0b5003030000c00c0211040040a0780000c00340d603070f110341c01060301d04288079000f88803a80e5040c80f510039014513107854060556a00820b0f40190000603032126408030840d00c041072030a80586d402c5100024848210200701d4090310040e1a40034085038414030f000300e1320240c0e040e1203015649481c1c0d01e03182500d440c41054415001900a00786600b0000e0422095449480300c3c010035038018424407040b1203c500c180603041d0070803100f61283c20100d044481c1010160840005001003035011440842c0703036600b02d1100000215541701920005000544140540303540064212400c840011780d855414450010070211b1401240c200024569408202d0b82c4001c1c43c030b102d01d0751207485d07103040c804050b401c02c00e0790f07082100507103507003424000d00941d02e09a02c8070001500346c0701d00704684202ca50718601d101034800a0300300c031399901c1c003065401d64607001c1d48140d801a00c158100010501d580c1810f48 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 145046528 1250 145045278 145045283
    0xd0606081303050406030207080412110102010b0a030c0b030603160609080c0a0e07080c091e0406080a02060a0f2a02010e04180807290906060105041206381309 70
    0x1913090a0909604034001d410120084410300c000b0000820074044101c03075482400e10920504400d0341e4070500084c00d40d00303c260181d000301030140c000d00010b060085040d0940f48050909501c0c0c0d5150000a480d00c54408110104201c1468010541551066a2000f030347c5203401141c0007010741e401032082c501054410040d00e9a405008555003501c0b9070001030300300060032103c40c02e0a0a4000140480e92410700c403040404504459a01c1410070380030300002000d040014204000b4180c0104406200e0204c010003048820196694058020b40002042c101030a107514603240003000c006c2c50000a01d031007680403840f06144299140b810b03010340e07034048080c0381c100110040140c0e80d040079a0447c0e0b10888100220320900031240350080c000212100c802c01c03805a06040c036510b1542040b0303003d40954100041000300307001d004020b801c44034105500c550000b03041e120052191040d5081c605c50301502044003401c603032512500c1944e41d2090b040403140e00030000d030b2140d1810221454034100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 145047778 1250 145046528 145046537
    0x31006061e0f0e0d0c08010f1e0e1c030608120909181009030c050604111503040203030318210d0b01020316020d0305040e0a05040b010e06180c0d020d0606081303 71
    0x1040d03030f42001c01a420b1070071700c219010700015840e07801d85400d40d4080006403601729038600d808001d03500c1b070000d10b600040c072440302045596600200d40c1d441d02d1480c86a90b1003204840ca5012609110354400b00040000c03400703031840e401ba4510f0350f000580c403600d1907a00c90442c17100407500000200c02035001d41251000204407141c00c01040d1000b8001521044d4144000c0d80c80311408103105010f5684240c0c441d8080f007521100010030084004c424000390f400302c000c1071082000588000003100d40051540c802140c0e5015100c2c0080d107010030802c982a140d0104441ca0300b5600c60045c042c6c4103220300001c082c4920011080120b0b62400b82c184c4030050b410701440d0f00d0700035090980310400d001d0300030310304685042d0325081003000008058580390600c40d95841040240300c6501020750140400c0110601da606100f0009030181006031440403054661401098521004204031016041013980030354a03125100d61203001012a031082d1000f2a00d0321001a044e03000e829154612154140c54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 145049028 1250 145047778 145047797
    0x70e06060c0d08090709060f0f06053903070506060108090a020a150e03190c06080403120f2405030706080603030d180212010c1205060609060702031006061e0f 70
    0x9045498000240139004a4000c0304030100d000b41041c09200c0c081c0440d10091942c1e249040c0b41e841c4940c10550050041010600500d0210003031008445441000b0114003600c0180782c6884900038104c2d41c0c000d000a2100082070b804003c400b00f2924071418090f05d65060a0351449402c075100c407802e500096008880d04024005900e4100c0089190225440e16144030080c1034042031410a0140c600e210f030015410504e410090b102c44a00050141c83c03428110701d0600c0c3e500540f09140b2190301c1c0c1401500e400001d0f0200100d41e2040d00b0b00700300e90070010f0020104002075124810f16000d141d01a000d000c1d00410a14043c00001c1c1c0070310f42c050021450501d00c20641d030000c0840d80c0700c84000d87d03c007440307070b0015035510048202c1b201e20800c00041e0142c03060780c002d01004400030003049005d0804003002600d540f180c2c195008e8240c00c2e15240d6841102d880040e04103d03450422901d03c6250840108841d9803120031a0a050104c2895600e4019461019905030602c51501d500040742e010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 145050278 1250 145049028 145049053
    0xf060604060e01031109040e03040e010f06050d0e0c030d0302070209010506070f140a0203102301050319080708031609060c020d1403131710090209150d08040602070e06060c 76
    0x18085d200040151040300e0500d21000002001e8800444188503d5480403605100800c030341c40180780100440415560b82d070b480c1c90f401400c24080c0c1e070040c1044596580c0d0309040b80201b4010540145401020740b40741ca810078101400941000303205034041d1038031200104050401d4402c442417a9080200b00444800315680c16000d413944050000e01070041c0c50701c000050714100703c240b000c8080000c1c0800e99000103c1c0900940c0e55521034012404403000c010030041e1000f242800010074030079924440305000d824226001c2c4902c110040c0001000010442c1c0f040c42c00c691120203443c41d5807048100d84d541c0e44115103218907001e0203980004444104000a9030050164403500400c0041c0d070f042c00c840031403807a420f42696010b8416001c07034103180d00550f54284800c403a030189001c0c0410080c0543d4012680d001d1000b0000340c42c20385040d9083c000e550322503201c00d00b100e07840500e20385d460f51154002901e42d41c552280d80030389420500800c4581c1382c807500b525128248540100010090701 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 145051528 1250 145050278 145050281
    0xe04020d020a08030a031e0b0a06110c060f070302070b07110609010314090a0308180619061205010906200703080402190909050601080d050d0b0102011409060f060604060e0103 77
    0x844003242c0c4003484440000d1012400e001510758603681ba10001440c040c1c240c00918450b0317094a80c40c04c0d441c60003041032250b91350508040250740a51070510360303030380d2030030f0b500e901e17000180a826030710110200700d00070710040c2d0600800d2100d00c80d909035501255a00341c2d0403e0b0b4020a00300030712508504648074000d0800c01c010f41100401450042030240403035008803040c0c07000381d8030769445401c002002d409042d01700010640180192032810b0800c40d5290030b260f210074014051101c0c0d10140b032015100c078042038100c000030700584460042842a1362038501c0c000c0c64602c0381101d0160411001d0b084a41030704100440c2c07100c86040130307840c00982da84c040b41c0b04d29000700200d90119211040c001c2091140c04000040d00006100042c1060700f420090315001c4140c1c00080150310260090240a600c041a07130105190f041010a1403801e00340181c1c09030042010341303030040108500304200208000351807070003445180b00190007034690900788410b0703210b40e000301e20115680508098007035109 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 145052778 1250 145051528 145051549
    0x21b0105040306060e0a0525030506041b051b03040506220f09150902090f24030412030c0306050603072003040e04030210020301081207141c180e0402 66
    0x51421510301070b102e980c2c2108581454018003000040b950411850098512400343c00c4013600307500c0c80321401111209400c0c0321130190b9034810551110080b03130381500c071134204061402c0e11400340090321085400052041d080f5101e810ba0452402ea1240c258160100c01c40c1e043e0350300505680d14100c82c2c1000d5007103107041604010b140346242c4500051041c016408040505041100070541804507410b00c2d24100d01a0000c070b0a030341c41003010f1103581c1d8801c20b1001d03040200351803070848420304070080710030b0f031000c03c0384050440c0c000020081040510811303d4510030058908110070072491508070b0850383c1c1401515040358041000c02e400500840c810380303000c10000b02c02c1c031900184080b890b05580199000c4074a030f202550501040540521141c0070b2035400c000114190361410003890b42c4c0d082400c69019844400040417018000d0602900c0e0302034081c0001c44560202e00c41d12001880d0b19046014001030916208404407200c8500141c22565150300b00c0700b00d038a8035000c12130b01c0140c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 145054028 1250 145052778 145052833
    0x1d0d091503091104060303091d1e07050c030708120c0316050d0204170105060301112511100c05060a0c0e1225050108010b0a05031902130b03010302030709050702 71
    0x103031111040c0c10f981d120702465024503c250b5030031a4140c5484000b10075014120302c206440f07142e1034100110341c0021003c0107880359a840310b07461941c54001c41a5005e20840b44038064a00000551600740302c0e2150041001d40c034828113000035650f0340b20b800d450900060ba04200c01080c04070440c45118401d40280104001070070b00180350030340d11600145080d407401c00307080190351200104001841d0a10800d00843d01481c0364a1505805103203000d5160b0501d04071101e0788200e00303111000e0005c0382c4858510f0038400781081a1a811004000d0301e80c02000b0740449807403051200141c1800c0301806480241e1703c03581c465004803002b00c805c10114102c02c02007800d083c0310b004200c1174041a2049604501d003042602e200d80a03082c24001849060141c000c4200340740200080d02120740d00c9011681d100034840e540440c500c0803044090b000e4031811142c000201408271003c01e0788550100194101c1c2d100310203e80c41240d0f0351042e03000f95242141c902c4056044041c0003000c0705411070302c040d00d03581d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 145055278 1250 145054028 145054043
    0x2060708150d0515060d15090303020409050a020c1b010905010c020d120807081e010302041a09150405150307120302161212021204060e03010209041d0d09150309 71
    0x524070004102807550304841a41c00c3e5018401c02c0e0314007180809a03e82001c000d550000074800b2513200e81220321200034000740d4903030f9500c00d00805d01d8132a40c140c80241274a800184601d04108441c5400303900005018440d038020802a90001809840352161842040e1640f0140c5031030301c1c0055038895629981641c009045107108800589101d8441c9059205511050321034204079200800c0d1401c001c00c1300f0341010100204240c0003c0c5024640d0440e5411035003c2980b2840404681c00405241e2526810000c084148460b482c2100d00d8151000419201048039907662104c400c0c81d0740f201161a0340540021340148491005041d400f40028002d004407060441084c02c6180c0f0070601e0741c481c01c1c009201d0800d010800411260703c5283c10110f1000b040115041855010346200764401c4505114070044486c0b00ea807000c1d0144d034069403004004100040744400d00c690b10b1820394040ea412401506034403140b65015043360800d4591748400300d100c40b09a68010780040c003442e6019500b01c0f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 145056528 1250 145055278 145055311
    0x9020c01110f2128090609080c010b010302030105091303020f1501060f0507120f020f060c09180702060a09060f0c021f020c0c060a1115040507051002060708 69
    0x280480d006200400c07400b602e882c2d0700c000c5600141c1d09058900f103001281d41c10001800040984048002220750f4030540d52001e140041041c480103008003a0b004043d0390600392484240580d410140c81c0c18a40d490007444200034080c011000c0384003d0144d40e92000d01320000c2606000d284070302960303d41c440d00480301c500707504050552901d2240a2044003462a1000500585a00c800908030550030703810500c0c20f110155950782500f0341a820384104000c0c40209240441d1700c2040544034018104055820b5801c3c41c0d0b00740083c951040300c141e402a1840742080b61800c41540d411031242070345602a04140d100c1c08407081c098181c02da001c2d1481902c1d1345030004620564802d06000d0041da800802c0300c01c0d04c00200f5038018040403804a041340c03050140c0c0f4040d1030046016100b0400856200c0c1d80c4202c0000280c50b007038640b40400c1c0d041c1c460b16060440c05070882d4416405240a00e044650150f41c800800c801c448201040b840142c1001740403584003409000e0264101c1c07001502003815 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 145057778 1250 145056528 145056551
    0xf0d0f020d0c090903030b06071109070e060a030204050f2b030c1205030a050f01060e120703060c1d0a0f0b03060d02040f0f1d0c190b031003060f06050a09020c01 71
    0x2d40703110390041c2440540d5500b0001c10580c1600c1098030510064500909042c100d894000250141880d05401a4032810015241c0b500c1402640b409190080031a6103501d40f03010024001c2d0028010280aa1800c0e0300c1c011961800c2449001d20001003201004890310202c0340070b907a110169011018007039585441c03000101d800038584083d044541e00e07a5283c0c0303007200b9800142e4101902c0002c4903500c981c01405440d51051000c0600d550071341d0000b040c100c036400f100746041d08950001d0300041c03401d4640380044d41e1150803460710072030001c1c0f26682c01070900104040100948102420958103101c10860400d41901860344148010400c440c21103103500440c1c140c0f0030b843d1042f00c8090f640c42142d91521641d10841580d06045409104205c6410701400d0341c550741c40c1d039074a2240001c4540c03081e05c002c00350350314405001c010140f0b549a08080004c60b0040b41103001c101d0701c5500700701c685510300c003540c495007044420007002d28048038038000c4620b0081d0701102d0213080c60b5407030f031220804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 145059028 1250 145057778 145057793
    0x3040b0a030f060e070e240f070f0b1806010602030301090b010c0215251e020303040801240e1003030e01181205060106050f0a2d090f050f0d0f020d 65
    0x5002a0104191071719008100608170345041c0c0d00301c1e01c52181d41081100301418411110351441010300103507580e01500014048601400c007008084003075034002c007820803208031070b80342c024a104c40c10f1410040c0e110300c1d5240c031264240226030041c0e1080c40101b240140d19000718501a0041c10b1840e00a074040d00031808591001c1a03c9940b0400001c41c2031003890380b600baa4144c00403406240c1340c4080c0690300c014002c42142c8d01c981191801941804c1559014000c88008000b40c60003040040302e02c484c000c00f40304840f9460070448804001c0042e1540303404650a01c207042c600600360800d07003180d40c1a11001e5a41c52040d04200d07100004100c80c00340da29160340604084250071400404030f05d00319203010f10580061040100500c07058140d10a107005490b545c00360750401d601c2c494000d8140d106100d0700580d4141c40411329030042c1d44c42c2c503001005641950307900e4141c82006519141841280d91080701501d0300040815038003004035440c2e03507c0c090158402043c404101c407040d1079120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 145060278 1250 145059028 145059041
    0x6150a0e0307060201020a02030f0307200105042102060610020f0f06090d090303080103080705031c0b040f0b030c0d11060301031a01090618020a090e070210060506090303040b0a030f 80
    0x100032a168442145292500700700b030500910301c600c000d40c500075240400039124010048854400040800850500d80c010200c28800c04410700580e50700348090031405000e8041600d0503212a94a5a0000c0500c13910080600040c02c80350005d15298a40c80140300c60b10740c20002603011030080c0002400903500c1884080d00d1500084002d2050341048500345045c008540c42d40c0c003d12410340c008000107500640c169045a03006423005460307c1e69420050306610842c81d600c0c031040040e2540005480c4150300c41002c035101520f0400441001503242d0b012285e0320105590f0581c4401da0023001468078a0501c2e24551049107400150501e840c08500300d42c000380c2044914802e14086040446e84814000b4014080c2501c107105a52412200b40a442404c00701c4190103600080e000408500507807041c40207000b4a801070040b460141030094444a100413010700c180c2c10050300080502d13152046e900c10310300060255107040d180450784007681d8000a454400c0c15258803114488001038452030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 145061528 1250 145060278 145060297
    0x2109120313051504120503070201090804121a0c0f0a031808030106021204060c110103021303061532120a0510050a091713050a0906031e0302060403080615 68
    0x110040c2446140c101c1c280f0b101c0d100c21404061400341000080f03800000c0403800c6105600340720b43d40e5100c40400300e024105403107001d0410303400000d001540362110f0705141030b0f0601421450704111054408080d403002d064074034110000050200111a9810000901c0040450b040c0002c2c03907120079800e00c4a02d441000c040d14000c50110041084640510603103c0b1034044107240351525007803600140c124a21400c000d88a50400484071784c41c1c3c0d010368102d9507035021006285400c190b40389001c001070000e07800c2800d60016450000101409001c503107002c040000031b0668000320800b0780c04048003c002180c02d0b03201c07003040c0035074a481009011a2900074007403005030050814541902d8142c500c090420320300186007210090108450b5004502c8500c11000e03d41c1d82c0d0044529400f0a0510303d800c6140c3c0184446000036080307140f070303201408a9100d144100307801050031782c5050744130803403110107009070b0070030400100002d20440c00d855202200400000010144400c0c0c1243d540041144 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 145062778 1250 145061528 145061551
    0x3020c060d090b1329070c1a090c120705010203031506070b0405030703031b050d09080c100207050d0531030f06020c010605030c03070603050613150e010b21091203 72
    0x1040c280003d400b0000d10000c000d9039007407400000c417480c03c500154014140780400203e100c540042001090350341140d0070703200345c5c905514189601c003070342c481014080306071203071200e45422500344602242c6001199016000b860555440c500a00054080d0500503903118a04002440010304403203110740c0102d0081e4015030b1984214640901140d001c0301c40244c8030b02d859060105543d074005e048580e14060078102003140c0300c2a01c1d0104060080e040301403c540200030f0002060000341d40a020802d01944c11110716421005054a25100302d81440c03d1592294000d224000f41165005a100020201c0781144642ea43c07118030001584c4042203502a400044202800a0034002c04c0e02a1038110003400c6940c1c1c0d0784c1e0000c0d5079900148518000d15469500040c0c4951703c869001c1d051094908080c414254441183c805407071882c0200c0d110324884000104407d291082941c0e80780316141004464407000300700c0d4910380d800c000d100c9000b5200d0000804400c01000000d50f0140205001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 145064028 1250 145062778 145062811
    0x9091c05180405010e070c020406150507050601140105032e0b0306030d0801060206070c020f0d03051306050301030206390c010201140609010519090501030305091002030703020c060d090b 82
    0x38440d00c08001410070501c0385003000014001c080d241042c150300420142405807000131540f010401a082c04c7d4000c008a61101003d900490f4005000300134851240301659026a03d40703245989210142c11901d00240c000e1000504075041500340d10300d010700700c201e00c03102051701e20b44e0106030a00e950030140d4440c201005105090508102007018102c040c10080315940c14600001d40d80c2000030180300030000d400c84584d087d51a2882e038841c4d100760191400d04c0c1200e59040240c0302e60710010001305021280e400008032240f19800792410380b5401010149050880c02c42d49010101c121041500700c1040050f043c4c0d0003034611050380010001c0006403088811200000e401c40e21201015190304001d403081140e1640e8400900e41502c8040f107400a1012100f0100e5903950700c1c940000700110326000000c007e15410901400c4024001c40300e2a600d6014030720201d8030303402009401005030303110746843d500c2c510303000c00581038018443c1070010302005070362502124640103580c3c030038018501d0300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 145065278 1250 145064028 145064047
    0x501030608060f040b1506040806041e0512031b130806070207030201200102091c02030d0504052116030606030521030711031c05070905010201061409091c05 69
    0x590380c000d00031070001d442607280c00204500c0c1003100800c002c0c074504900d0300084c402d1108282c1e0071301004010f0081515076403070b2400a07955041c2a101a60b004402c0050752101c00580c152112000f07a1040243c1281c0b01d0109840c03140e42c0000c1c14040010380380f00300c60280e0142400203005800c80c0d143da035000580ca4009000e04006014110000b15009800c0c207001613600881a40b414540e860120f9201c4250409c0d058028010542c0651388412481c7d14484a2500081d8005141e13002f241511008900c011007560248a940300341b60308403102803c0980041c0c0c03000e4239820094801c0c401d49106c1d401051501c090701d480c41c0c008035900c135607508090041c000300700701011111400700702c0b0100207414a6907034015800014003610400c22505185e940c480418403d4070b4100c41c0d20001c4011102c0000d00010150104840120025901c0f4000052561050044030229210f807082d40c0082038034901032011003400144091410701c1145500b0103200405d2034901681c2c401aa030311a00d904880 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 145066528 1250 145065278 145065281
    0x605120307060c0201151802090d030c0c08010203011a0304170a051b120702060706092004050714030106110f1203070810080606131404060b1804051903020307060608010204050103 79
    0x4102e601310380c58070080c0c50074007040c100751005a410703504c4140c0c0032a54010f481d9001c2d201d8002c3d40f80d00092a1303101101016007141008256a2017180140140c07034445207000c1c00c0740401d00ca00302403d480c054529036600116802190041d014105448040d803401e41404955070210702114005040010081c2c0c026030f18131542010211014090600c600c074803290803000e0700410310043d12a000000d40d075810020703e030780300c40c000d16440790603500614590b1002c05844008038410501072814400041c50b001c2c440c1c401d0303d48c641d00c100031586c00c50b401c1c00f0302120090b880003100407540c85600c04a240000d010410007030103c0c005007400b60349250854000f000e21402510704658205e08400511103646d0124415500010968090a40c4031040d0310708400b400d000000e00340929545002e003c10300481307405c0001d0181090728511500c21085901444034101160080d1580c1c114080078a100c542c90860790083c20701a104890501805895070000c0341c509d0340c0040441d81d40060200001d5030507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 145067778 1250 145066528 145066541
    0x509031e2505070b0c07080109150507020118061a191511060406020307090306020c06040209011208030a1d1515090f060108040212070305060609010b030603030406050706060512030706 81
    0x500711601c0e00800715922196100300a006081124201042d050085901004610024a104002400702000c41d0400c0f10720f005407030010300045401c0c5000107400700c0c014001c8102c405203110b03001312004020b8540d54000c04000212001da1419903610304d48036621603111018529074132080322a040d03c1c0500005041d4000c0010505101594201d070240b2100821469800358020801503500d59507203a0443d4501455000100310310300c00b00f4080c13281503002074901e00c55842a510101641d8031681c061f0f46022030b4010040c5011820000200d007080660461031051380c400c9100c0c1122030003200c05605050050414000c1c003621300b0704100d85141070006e01103c1e100c0a4845c04d49078104101c80c92121003004016078144500c1030080f903b10744403020714902c6000020141c0e04615200d20700716881d000c1c250390301c2d88140103010010031120150000c4070f0281500800540c50289000000d44141c0c010710070035550385548583c00613158039091003c0000f0b40c407400c0a5582c601382da2034408104d841 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 145069028 1250 145067778 145067827
    0x40f0204080606032e060308030109020c01050106032d060b040e0712020f031f080111040f05061305090a020f03010b030414060f2715010305070b03070c02040509031e 73
    0x17124540356000300c26040038103040102d0900c520400c0080ea4004405819107903c01014040c00000009048200394003800602600f50000c0c01036907a9441c040f02920301101c0f410400000500e070420107201ca41e100b4100c14030010340007003079082c1d0714010031301980c04c1944030030203000840040003280c0c2e42c0701000e40751204940c2021400c1550040019045000003480c0000e440c2c0c0d1414070000140120b1800001010610003d0000c03c04c40504844180c11510503140281c08499000c03e41c0e140c000242ca5030f5002203005494114581002c01130380742c1001e002d080d400c0f9400c024026000d0302d0100154003a14415216076943d04003468003400f24100d03c90362080b5900032405020311040d00461041c0c000c1c00c0d010a44281601021044081c440036030f03040011445055450700041c0c0b69104128101e900031415106065a504c3c0a1492888201c603004001441000c0701c3d001481c0ca58442a040041c1c4000c480c140307000045440030344140400d601c6040440800c400490f040e041054103103046 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 145070278 1250 145069028 145069033
    0x108010207080301030f06090b07020c030f071815080d050702210c040c030b060c0c100207030b0a0903050906070c0e0903120103060e010e1507020615060901110705040f020408060603 80
    0x20545481c02d6502041c000140702c5652485010b003817005c00d402ca081e1b003c1e00140c43c8611800c202c0000303580ea010740c4003143c0c045d0203283e809298800010030840c040f54640c06114540440b40e0000000801c4014040c1c0107065451801050b1050704120311f40c2c1000071501c03402d503105160b0041000c00c03015100c5080d0b2042d40030200c11024000411400d5021303d007030701c02140b0001481010303000743c08038802c00c0381c0000010403540001c0c0f80008500200460030303182d0306045450307860200d848000c42c0c00080c011140c04404642c5240890780704006050103450300034109000d81d80042c0305507200032425035410402d5070003800000f131003030700d540c3d04004140011407030320803100c00c0700d10001e20500c80034180d507540d0502d50811440c01e4202e04a2038415074203407800f070700c12071811000c0e469003500e03080d005129200000e42c5812010590b4080084014a00c80c20804a0801111203010359441241e0500940c00c0c00105a100c900400200caa6040d001503103039820b144400707203410401000c052003035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 145071528 1250 145070278 145070287
    0x120a120306050a12030c05011e0f0c050c0304140109030f03020607120605010c03050915030f090613030819060b030c04080f01110304030503040606180504060b04140c0c010615021501080102 83
    0x5104c3c00404050640e03140c00c01d21880706803410070380c8c01001c1301c009403141005159142a20326442d41e200500d140c612000400c40d5041014040394076005445905071a94001c020a0110300f90303480140c800d0900c1407419141503a241d90b60200741030108070301200035900500c14400f20035009030803038074000d89c3c0550822180b8078040009226060001029043c08400101b4000c00d4540011524030507a41421490381c904094500550407001100d0a2441e40211408076045100c00d05040751482e405a903074105a449800c500b44006d00e405440000c4203513501c1e40060f0a41c40d0f080030310f00ca006142d2078151500d1502c418070f07003440b42100d42140700340d140c012000902500b5100745c2e50404d8052601136180d50760792420a000341415000389215200f441c1046240c2d0601c2d4011903c02c030f110340414003458140f0000e205c199100000148444a80d1200080e83e5411100103400351000040000c92696070390000c00346c001c1c050042c01001a0030180c2e4060242e100302103c41e00504c504030003186007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 145072778 1250 145071528 145071539
    0xd0516020a0c06120b0d0c0302190b0301050103020d15170d050c19050f060f011d0f0105120c0414040501060609060c020d060e0d12060503030408100b120a120306050a 73
    0x812154003c50701072100c0c40300b00076240c48240d80b2101c00c44801a02c00303018040203080c000085d18191004031b2042414000c0741441e1500c0d014181c045074440003405046900f010015000b0790441d0740040300304ca80c0c4a0310b0b1800d01e081424480c00502c00f072140d02540746488a031030b42c28159900d00540500500b000a1002c04800141a00303001c1c113080350440321001c40307140c254103040504141950601c16082488a4010103031140c1c3d040300da013041c1c91400103100c02c000c032040d0003044030707110340b500d11b0b4400400c418102010258014043c01c0c0c2914508503403403000904503005044036018126440040008101d000d100d500080c0c10181811030310549007600040c882d81d00400028024400090401e0410001ea0007a4044881140580d41400c1c42804010908403500b5242c2d020941403d01c002403a0074040111429204440c3c080c01203040c40000c80009001c9280040350801c080509075044400203204444846100320420455075804110040640c0d099800c128815002503804108 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 145074028 1250 145072778 145072793
    0xb04090f1103100213030b0603160609061d031b220f050c03010e0103123b01050405060a0305090703020301110307080106020613060c02010f020d09020a0f030b060d0f080d0516020a 79
    0x103c0f40d01016003481e035562a0080303800d080c0742d0303412b005512103080720106950f50030107203000581d90569100505040c0841020a80d800e006803459010b400a580d400400c018107501900034800207805040c060b40301030300e540d5402c401d444203105215038600149540c0229800b0f041d812808281000c0c0c00c1d075042800c20241c00c40d0601c802014000426040c1001c280201c3c50540c060710a403c030207003204e1860445014102c28210112502d00c4c01200194030b543c050005e0b60259003024180500303001507030324150014400640100041e1060200010040e6000d0050301e11705c1440d250155101d0504c000068010301e01038000501303641148003004400150382c80031070720064001d14003040d6195000b50603801090081600d500c3c480c000100000248202e4101d03040041c401d80c2c61000031640c0d5034980d01d00c0101da010041c500540c07040032030281e2521420024240340140c00310fa8185031a540c480005500c845440c41401c0e80300c1b010000b0f6100f654503c940f070141140041c24075003010360303108032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 145075278 1250 145074028 145074067
    0x2040605120613030e04060306050106020c0301060f06030c050c07061701080f1b0d300207050f040b030316061a030f100c1b060203041419060b04090f11031002 70
    0x80c0e01c20001c14008040c5441088040b0151101070820420a48c40742082e0014003000d0198201500c11600c07007022a04052195004842c203013241a1107050505070b0450250500c0c41a003020040244140a0200020310042e00200110340b034240400c11860350f0140c0e41c81c8140d0103034101c0c0e000001f04c02c8040b41c0c0840c51050400000388440c0500d49190005132500c43c603018007500000ba0a544150741c02510808540d8a0611039000d1020071a01c107401c982d00c0180340100e58102e0b090100360020b07818107400c4100101801400d43c1e0070440300041c10070303101d1010002038511680340d4a20007210300c044071210321104030681c094904c2e10300740c8400c00c0c1e842c000300340115000d81c0d84502c1c22480034882c81e00b200c003800e071a52400f2039030341c0b0b142441c00c042c0d04240c0702901e10060b00b0642d4143c2a8000969040c00c404000108082c000d45481d50001005500a8141c115460300c448900060390340195031103240c81364614000b148503032002d0519120514520843c5203204001c4404816031014460 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 145076528 1250 145075278 145075291
    0x60408010b091008030a18090e0706020c060c0a022e020705101403040b190207140c01180306090614190b150412080903030f0c01050721020a09081009020406051206 72
    0x20b0064003085501100c1c1261f640c0400c12543c40c0c40c1c003900141c040400d4403400c8a419900b02c0d0a17a400020800486200d1780e041040680d00189501c401400e00d000d4420040d411200c03080d0409103034a041c0c4081507120b503038a000580254509114074600840511001c02c564903055054004c4004070302194800a0400b0380500c2421000440703d412080016110b04103c89082d0b49030101494013400141070f01c44200d43d180594044a04607511038514240107261100001d10300a245440c0c1750001c03e08584240d6000d600d400503020307956401c1003140d0040c0c0c04002c05c1d4002c0c0c250484640d00b00c0b6181c1c12624420200120791142200c6540140c8080c0c0e4145446903143d24117910f002e2a40b0300c210f040ca19050301022842c44140001900900009041c1000a0007550340f80081115400c80409003040d048011503c401e0100c003140c0e01503d094002030602e11507094848556510700208900355141c0c4540322510348085042034010720006160594804d030322a42d824a8907602c502d4001c010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 145077778 1250 145076528 145076537
    0x8070c060b040f02040906120803010611030403020a030c0501020f01060b0f0a0e0a0618080114131a0a020d0b010201020f09060705030706050906041a090a030e010e060408010b091008030a 82
    0x240003803280c107900c841c01c4140014010481c0300c040301e4014029400c9480350b40c520034501340d00059100d44020b8810321181e40041840e18581c01e043c42603410b511202c2240500340b0042c0004401038682d6440140690b004518942ca0319141a000914055429000700c0c40ba90500000704200450001610611005c0070351984e1180c070000c074119440348141180b00d46c0030903203000000d001c541007201e110345103403035900c50b0300744503214142107080c2d03903031006c808584c414a40001214540341c83e03803c882e010310881c00b23026408140303210852080811f4803480c00d000d03030004146851000301d20803604107610a000039814a058424120400e0185088503402401c0016550080100a0046170009a88150200464100444020307514001182d085507856605040b05a0120001002d144100c00020003094030b0002980c1c126500c00499640c54184180050f080d2401c2d0b030740c2c01c0500050303d8146c0001507008149401c002da85080036000c07101c1009880c006001c4e91001208460254229017007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 145079028 1250 145077778 145077797
    0x90d020609040f1505030f0a05070501030b06090303190801090b15030a02040803210c181207090c08060f06030f070305060a09060303080405120c0309010e040e0d02070305060f0103030807 82
    0x810082c0445001d000ca1544c80c14a207041900720710b6219030240d520560031501000b28010311650b0360800454054a594040f41007040303158480d8000406008014110600f0943c03542c003c00d2942e0805944c0d1080c0910758145404210b0380200c00c01d00400c50f5002c28000310340300300b0104a064032610324286052400100058104c100758040790002c003000000c80780e0b5410040100040e0151100070038410403e0400800c03491440301c01070307841c00700e00c00035407180b0b02c0780c107501300130700101185080b000034003685d08005000c25181c400c0a1481c1c10700d4a524409140140412460007002c041c3c40740314100610900498131100d01c0c2565102c845400c00041c01c0c0c460301c0c00130300c0703923405644040910707410000b011041561040300e481c0141d1080086814410500074440c50902a103008141c0590080c80040d01d40c0d842a51038a44c0e502c406032001480c400305030900b6042c03412012418016902450003001040780402050340d0004944a04402d554190766004082030409003024041080411 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 145080278 1250 145079028 145079047
    0x1b0402092e0906031a010c050f0118150204120308070201090f08041e24032a080c0a0206070e06190305012c041b0305070e0f090102090d0206 62
    0x2070244507031041c21441280d200442101d00c4031009000000e14002510201c00140343d034000e00511001d8041203004000d252001030044980c40405441680e05100701001400c1e040700a100b002018a10a005801c00080e2801e203102480450480c0c3c50750544100800c2140d1070941c01000b20300b682c9460301c1c0a840d10f82101c224050011104040c240200c0748900002704515800100100c42c4603500801100c680c102d0094100442c1b0b1040084102400c00380c811694481410407021030110309002402543d0402d04035601c0244001c2c0c0c601d0b0129408016102c43c1d0004805940040b1380302140b8a000300d034001c000c1d100c10004d0112810301c00c0c00050940c0c00e82d551b00c04d803070203020995120422080c444000401a007001c1c42124403481c0f10b8050300000b500c9024000f000642d030f0240f80c0050761502d5030745d4080c440c3d007540c00d0704c0c0711900540b0100000708180154402024845003801840c10720540d0095808409007600728a2b038410414240c858032403079a01440c0c2d0390101d65450303c034100d52 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 145081528 1250 145080278 145080289
    0x4090e031b0a020a091509050c040b030c0405181e070e090a061509030512030702010e030d051b0711090a02130306090515010810020f07060207150506031b040209 71
    0x1500031201d549100c041c03000d0414000036640c40030034000c691400d04030355109140000c94405982c1c0e01e900c02e01988041c040c00d080d942040b90042400c00e50503241907520b080d0442c480d001581d14007a0b4020000c0e04001524005c850a10081d000610382095410b00d40f088440348429020714006143d12040000c101c0b5015101007008981d018040d21f4003803030480b050b040281554000c041c40d800b150b107071035084980320740c0380c0e00c050380d030f1040c0101480c40e8161009095500700410f00800c543d03c4143c40e0b4409001030010b010940c0a00c00082000d0610700304407852010b101800324031181c0140b0a10300030856401030801911816141c42c5500d865980c402006840b64a04a078810030044038000108141540642c0783c0c280a0415106444162440b08008460038413601090f94002501c280104c4819402040c461034a0710b105071802000b951a44241d8011a00a48002c10600c05940f10f175503031405015031104d812406413003582040c0c08030b14408a41039191270300440c1d01040310300041d01c45 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 145082778 1250 145081528 145081537
    0xf12020d02031503060702010614010e0a0b0f04060801051906050706091e02032505150d0c0806010806030a0b0a02090f0307090e1506030c0121050106030501091104050604090e03 78
    0x1410425542c0b464410303005812841800c0902d80a4803034000042c1d43d5034410b1040c43d0a458207032080841030302e50080115002c0c1e40d40485268005807107800080c0c01c0b03104000410910717201d40340980c0c8440c076151000d007403410141d00c1103000c1c00702080002d0120743e0401c07403034042d0382050074007944840722801c00000401a58800403d44002c1a6602e031800303460142a4189510031411031b00c1c90000740213a604046094031410b9008482c181c02404a440d042d071907001c1c50500d21881604140256949809454840c00b081010502100604c10556801071000c1da1004040d8014103003000903503150080410010305521170598040383c00003040d07131840c15004214400030112001c890320703600031100a00140c50050124031071715031310b50401d800740d40849100384001000b0300425014040196030081066144130141d1030700c400200303c02c1d19540f0170903010f0302266500080d20760500c68183c0c05c0b510484040700c0c0c00c01c028041000983c0e40c0750201c90550b4801203011524100e4518058510b004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 145084028 1250 145082778 145082797
    0x70e07030207050f1209101704111311090a080606090406020c011508010606200601030b04080715050601080c0705190c0e0426040e040615080a0f021e010f1202 70
    0xc0c002208004c41d0707688042d140c5800110707010701c0d10301401f200a40741c08401e0500c000c0d0b290811000135000c65406e42201c4103058001d0240703c804c100d8400c0b8481256028a25006400800720b0b5002d01d41c103240c900600648121801400079081080025440304002400105016000683c02540c0035081d0401e030584411000c003852881e881d540810702a04250003200300190341d1040310014015140c8203c2e43c2c40b0409130241040c0d90031501c0741c1d420801e0040081c1c0d86058204a00c0b0000f416041c0c688110020710036000a039420081c000504c4000c000e402c00044c07100c103005c108089200482c00e1004210082d588208615117407903c0c4081000680c02650300d03401c074500300802c0c46041e031a842040f0021100c01d51481310982c10071209401680183e80f0440400400100059200d0b409502580110600b0144403551345480700c1c500011040c0884140803072403000c03000c604001c04440c404042090f0101c0317a580e81c8400080000d15060f0700d103020842005d8030340302540000c6e41168000782 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 145085278 1250 145084028 145084033
    0x609101a040312031107080a03090c03060207262b05011d1014040b0111010c02010e0f060906040228060825050409090c151e02070e07030207050f 64
    0x20281868249a41c21901c0103641e02c0b46540144440d81303120b48520710030060800030280c01c02c00180c482800d240c01c0300243c0002c0c942e5800d01c16010499802440c802903218500c050303520380c081d00e0408c040184203c580709211b12140c04d0108000003210039144900380300741c20b11000001403900c6100d40885100090800c900c0c100020400c00844080701201d918020700d14402521049880c842c40e12844c0705046104810a81210300c0d8034007a00719010b5032005140c0f030b519689248644031300f102d0043c030901001d82e541d40289002413105002101d10b15a480001d801c1900d40751418580310900108028868085540c00c00751144041c50484607088000d0b039010155a210103010345060000c0d201910750400e80d1030341819003003c051160010b000c2560b1502e0415140030580750103421140c03012603425203001c102048483e200b9448000c0d0448036920321001207200c04040481d040420288005c641080c00180000f460000b1f41a07006103e80c54016941ca11500b4501c1c28450020601480e90 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 145086528 1250 145085278 145085309
    0x2010e06070b0402150702090a020903010f1103100b07150203040510060806010509011211010311070b0a06090e0a0c0e0c0d09050c010305090706080406020c3a080c03060910 76
    0x115541400b0300c5a4030944a920b0751101d29032940c45d0314001c40b400250301a4030400055900100d40e00541610000a4008200720801032158001e50b12408240512420048201f003140b11384102c04000030310700c0341401840e00007036460b154408400504104d81d50b94000011a003042000c0000140d0111b804004114a60b00c401415440d014280318a0748200c08100000c035042c2102074180c418194031110342001c0c440050b005502400300001159000c140a11010000c26811a00c551051000d4800080c55500b1301c41c002e4216046906206010b070300248125000030810f034440000c0c2d40c850f500020040d0766282c0c50517117511a2040e0405a242400c0d00d020400a0000e10005491000d890030b200540c0c80504040c1d456845100c2c000c0000c178164040f034003044c0107134000d003044041802540c0003401800c3e1071034428618401c428140d150710000e04a9204885203419482d01c240745804000da041c4110301c481d407804060003e920075060340c40441d140d08801c0000d0001000284210041c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 145087778 1250 145086528 145086533
    0xc0807020d0f0b0108010c050901080f0c0d0915150501020d03200f030a0b0105031003240606020a030201060911030103022e0215060405042f0a03110102011a01080a020702010e0607 79
    0x100b1711615145600341510948140c1c000d4044c1d07143d11406a66800f6681d443c1110014003000c003500c01d11380d00000f04601140f4007128010448124040c0c24801030004040003600220f4442d1100c031600c1d9850848240503681c0d000c40c4105001801d8500801c80080c10781140c070500320b1250000a519800250490608110708055880b482d58441c0400200c2034400c01522035102c1201d035900c51911007642800021510b1030b850340380a440300f0022070052080310310705048664039000346000d43c0c82866182c0425509000d078501405d600341c1d06000c0d004031038110000601040c08000d20404076210124182c9072606118130142c040024100340d50005800c0107500e503c0c135007105802c1c00340f80c280040c415040034090745005940c000723040103400348480c8202c400701c0a10f0410040c030801001900409640314050310020314080e81c690309045032803a0001e8211104940e43d4444007088000e02403580e038001c45101e510101d08440540e80701601d00c01240c0c1c0d0194000741c194448030101d07e690030b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 145089028 1250 145087778 145087793
    0x9170708061825121101121401170c0604030507030c060302040602120a050d050411010e030703020306010509090304090c0216150207060e0414010311030d09080606011206080d03050412030b010c0807020d0f 90
    0x100031007a00e51100c80c1901031590b4003034420301d44d10f4075231b0315407284010040c480b50490b214805811020035914102a00000101c107648554401d8840f64401e410500c00c2c422600f100500070100c60504500c1c0620304040a515000300d0403d60580340310214075407071140d005608940100200c2e120802280c42c10f8034040d68aa01003035401c0c1d00003140036a809005050008114080d2500100107045582c45e00d030400c40c1500c0000d10b005510700060000141d0070b0001c1c012524a9015600681191030a060b181e154501095101040c01803c1070821307a441900401c948060f070fa524582800b0040780f0340c0c00325006d043c0b5425201c2e596032031031000000b0b0201c401d403e643c107001d00301c0645100300068401160840d409014202c00c9800030346c0450389642c018400300c8112040c40d80f01107803884c1d44030751903414411046d00e02008a0340b64030130401002014038003140b045c986810104905070305800002c10301c01c03003164000c000880000b4268295a034040081d01d59650120b009850150140f41070f91 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 145090278 1250 145089028 145089053
    0x1150c02040c031d0d0507080703090503030324011d121f0902040b0a031a22030302071a0106090501030518060106050414030a020616030917070806182512 68
    0x50b104d20f1038404000124041810031031440c03d81d46141c04d1070303500d8503030f5203456201004c1242480010719000815440c04c0c00507500c181541c0d032041d400c25040b83c4542c442d0300c040ba100c0703a040080070700040c00c8400c2d160b51003502d95841902d121109002d8444160700d04224803035580003c4140a00d8560580d807580c00155519109940507c80c0307140c0c203c00e1029004513408010400c04164800601c60300c14454101e40c403400b1001c4041c0f403003039880318031180e242a045041c0c0010340c0014424090003120f20203d011604005000b48040d03241510003404101d8030700600307040648a001180500920000c3c0c664224485c074144ca58550b5200400b5107158090320485849081c42c0c114200245404690307581c110740c001d41802d01c3d0119020850003150311010040f41800309900c00880c48001b100022059051f82c000103000d400d00f0500200c1c94a40001c1c0070320014001615802d089160100b441440d00d24a00010095444000030040300e200064000c2c0440c1c041c911404000c6c00500354581 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 145091528 1250 145090278 145090301
    0xf0705010e1c09150824130203060f0901030804060302130509090607170105060304020d053c061b072a0306050f07090303081306140601110a050601150c02040c03 71
    0x224481395107000300030b280741d0110382c0c070300c0440c5000b8000340c510200701c8480c00e5a4110075000c50f40503980704c0300150144220064090b1200e81c080200906410302507540c081d914000c035030380022580341d42d8030900c15104a00810013099000310301c81000031030005101018210003440c50b11030f4070300758031100da0300d0b102212000d0004921100c002c000c004540d010906030b0314041c01032480c580d00c94003400081d80f401c800803281489000d039080c22035a01035000c2001c2582c0b0483e5528410484900c1e18426144410140c600d42c01c40018401100c0000401560b9612101040303512502c2c3d6090100208914850400d052000946685500f02040c3c20200030f46c4c1c4580b000304895102c6100c01c8105d944115611400b080c0b140f60b060010078081d80e0603592000e80d030800fa42c1492800e039038080540350306050b030b0301c100402c0405000003984c002c090580d40c02c40c0000205801403032611102e80d00c10041c401c1884020342110f400320590b110b00340000442c4d0300508107100c40344403040000c006100c6030b00306 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 145092778 1250 145091528 145091537
    0xe1c08190807091e0305060a050103020f0102010b01020c040e010914010c081008060718080a030c110f090c09010c0602070f0b0106091802090303040f060909060909080f0705010e1c 79
    0x900354180501180c034000e50456076034003100d03420010651030041c4c500440d03000d00030300d2900c0040001c0b8204403182c41000c82503000301e120f500d9481844982442c202c0300d00c1c10f5906028584610b41da0019040c0100c03c1c04603070209100c0b944040140c0140f850b104007600d1940d0000c820484482d054024100781c411607501c4280c1543c5880d40c4c14211030503401440c0e03080d0081e001050300c3d28032a080040183c0e000300d0307443d40182e80d2422468584810210101c1c08500e2040f1032200780000f0072014004004180c40c92603145140c1d02c0000ca081d030004010300300d2030742d011500342e08603407240d04400c0c41594007440441d51000310f400e01c00680703802c42404840c0c40c5003a0300085101c3d44200c801400300c0c2d21540140d4001c003e0f040c1084047d4100c842e410342c0500c130901001403d00314110041c0028409034444521203410140c0c1d11041e12103e411461503141405421000a183d00d01160004684050050f4990a00b86081405000080310b100041e224007540c4404551000d080d0340305d5a64940c9a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 145094028 1250 145092778 145092817
    0x40801051314070b040521061008060f060105030115050c07030b010510020c091314030304030504061106090309010819050a0f0b0d0b150303130b090f040216030e1c08 73
    0x144141e0f1102540188151250184401c0006092036000400d401c01c0d842214140580c14141e87c615003c01142d0b07030b44a00c001d00c442009414400c0c4071041d00030b80c540441506500d800ca001802ca44018450407040380c1c1031410046d000391042007520100c1d41d00d1401d5903805c07a645d040031a04042c082c013034184510451644000b00301d000145020121001400c1c12070207039034042c0d8820362065803150950310366102d0820140b4504051005512039442904d580e620386003848001041d19032000c00c031001590051003800040000001940c40210091a0070a600d94030540301c0440780110001081c4118180014808000b445070020990005040001c01c0302c01c4443c010441c1c02c00701c081e00581241c2004000c9015402081d002125903030780581120f25100380d00300021100d0303e0582c000c00300000e020230714040034034142003450f82c4020102c03429400c228183c65020b820441c92040101801490700d40e804541d03c441140400031009440e03144c8014481d4140550594402e4003624400303103a460 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 145095278 1250 145094028 145094063
    0x91810180905070b180d060507090e0106050f0703031d070602100b060306090c0403080c0703022103030a0c200601031502040807090207020402070c080a030f050f1602060408010513 79
    0x440c4800301500000100383c0d80340f420035a0100780c2c0c0621846104458406800022500c1c2e2407410301225114080000d024906688000c0600c80e50360043c030900102d14004005242d80714003520a085406113803a40c0e00c20491400307070018680340c05c81c1c6001d030001c2c0365003800036480469100222070040c1c0a556069200030480b004031200106885e92000092020a51f00d0034a00c240642c401c070020042440e0035141e8036400181d400c280b51129090b40302400c240110309060308841d9960758000e1001d6000100c90301c015849006c004c000b0111a540c820300810440e104e00c1300d0043c0740010314040210079039060f04180e1214024081543e016405814044400d4418400ca5040710502e0740135145542c140700c1b218020b0340c04040143e81c825001d10800c0e002c82c1e2440c83d0480105003003c0100244c1740b01d4540a0007003840c0380e6145044c01418421000c1449652049402c500900380c01076021034007520010f4118042d60304082c0d0550720701002c1104084101c0354200c40240101582c21110360300c0f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 145096528 1250 145095278 145095281
    0xe0402180105060706020c010e0a14150403080402040506190b040617010b04030201050706090204050c0904050615030a0b03030c0a03050913090f020d030e040908040911040e070509181018 82
    0xc1c410a43c00003010403d08000ca45960302803d04422050004a0594140d20b1005c1c50190075020a841101d003102c0e2580c9030b070804202120540c038601440b0300e22850070b42c0700604044001000640541e4880700002c150344e481c800e4051541c0180034150310101d4403030407500000d030070034098000889d4a01da0850040c90500c01481d04841c400b224091815045500444a68101100c00c9545075265035841e00141d441e4090315100d401c0918460f901c85031036208200545078003816060040c602c44400c04601c14421742181c1d444079101501141c00a45040880c2c0703940f141142c106c03264011000c00c1810198044014525800704683c204000301044040c3c104913900110018019001c841320000141040f40d60004242e00905016940038940002304040c1c4e600b040d805c46601074002001c0c04418003174420080c48a8210798654101801c08118800011000c0d02c08800d010001c00d55407415503501c00c1465003480d15090010300d50070101b2900c0c5030b10455005258000d01482a0007200303085a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 145097778 1250 145096528 145096531
    0x6150f020f0a020123070302010902040b040506090105040e0705190302180f01150507020303210a0908071106090a1502060a0509030a0807021c0206040c050609101d09010e040218 78
    0x10001400b20030380c40b40e0042d1285540c81e0500383c2104010100c80e0405003850000d40162070207600040b0303484015204001c211580c1d000f01911440c40c20080c0001500c4030030441c3e0665a040c2d03000102c100c1089501440d04403039510156000084541560030540e420340f4042c1108d01c00c0d03c800c00040d00242032840031a0040f15260040d40355030004000509865800b44c0046080382841e44c0350840c19004203040d640081d40f040c84403401c8580c03c881507100000515480040303000f00b040340811a0b550381005100741c620241942118010900255581504846019500810071891580d64658a02d00700e486820000094041d803000a4130010244c054075102d02d801501852815041e240151422080641020f003148940041e800d5a45036400810076444c06c40c0c3c0080c1014640b5280c52620712501d500b03c1c9001e04070511110f0007640350740124948a81440c1441921500c0c010780c1c24107400701030386d512644003101070700020703116004a000744d005900039202d271130240c0106203920209480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 145099028 1250 145097778 145097803
    0x1c060602030f2d0c0f1b01080a0b041d010606050702060301150c0204060807080106050307060e090a020d060b0307030b0a2601090501050f010f0e040b04020f030307020406150f02 78
    0x30400004240e0b03074000d001445241c6040340801e40001d4241a100c00040100c0c800e072181c0440022881d640c203808010404213010b050004100e000380f028002100101e0541a807810b0155040104089000580040055640c09007003004039500340c103519181c0300f040410f40308070340d407034080c01060a0340700300220f4440580141a041c55a40b900f101d40194485481e0203000f04550108910010380c0d5a018410081100000074803013541411852421514a40c0c0403d12035448440700f0007043c1d401807180d50140f07400b1a412055903a8018048005c1c0c440c001403045424542040030032100b1618000d180a0040c55a04209030810181440321002841c0254040e101d03840e100032a00031004c14110841403012400400e464110781d0340c9609450054030040504030308200140300d075901c000b00d204028400c4901511403801d1549a000c07112074051301c06800783c500303805606959101003044903045640030300100a1140c1e114201c42e035943c0f184004100050104040003081d034400500d01a290a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 145100278 1250 145099028 145099033
    0x1c020f0705010227150a0c060c080108010e060105090c03131209060909020705070e070507051501030b09070f050904020a03020607030e01030e07030c0e09150403080601080a180311120d021c060602 86
    0x900b170b420700510a80000300071700200b01c40b0031140000161240a49003002480d91221380c0c443d414002c5803400e5800300d9490061942c41200100455940c0942158205040040030303507032901c4109181d0301d183e00030200070b003801d0140160402e145910450001c122075450707a03a00b10407522a115181603104894015141d580180c0742417120400412a064111a541c2449450513000b961203604040049013070f12001c0b144007004009009a82020741d03440384864002e48001c0c0e0a261401d8403141c0180500d034000da8148000a0440d22500f0001020310740061245840d02c1d0b4510300101114589041c080c0064140382113450001d00014542d000d507580003180f0700c0e4060418540300310180300140314181510070684298820704204107c42e00503402642c035140d0505d0903000141c00390f940030304208096441d1070180c4600009158a0b5070040e941864690018203803544080c1ca005554420a46065800a030752128101d0650041c8041445180b100c8418910303859070078101d84007449480c001d80c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 145101528 1250 145100278 145100299
    0x5010b0408030a0f030b210d0e0a060c02030304170606330706090b10032d08070303090b1807080606060912100519050a0b03031c020f0705010227 64
    0x80d805070788010305a400c541740000c0c0a080f00b4000403103030700591030030142102c01c5407650030903a0410320100000b807a040c10702e420650b481c0c001168201c0e080b44201020003900683c0501150360500880d8000c042e03d030703030318405154011605a100c03c02074070041e03c074549000103030720300c0e1442e452040c100d0701030803807094a008503039881c0d51410f5228200495841d40d451280e01c0005252500b01801a22300c543d5240c4200e0561901c41c1d40040707010458a410084d6000c0410100a541003805c0001d80c414801901e40c01ca91506602800030880300800161082e408c100001c1e00505030381c608c020040049901d010350b59690140ca811041c1c80151700501e041100021a09003040414001880681140c1c0600c10340c958480c2100c000b958183c100103030400920413030031400d018481e007048246100300f0015003044002603480c8034002e008400000d0070394a00400307401c0c076815601440e01441805960768018070300305000350f20081813138032588203442c00c050184501c1410900c10300000352405124 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 145102778 1250 145101528 145101547
    0x90604020a0902130302040207060203010e0c04050f01030b040905060f190615110a05150601030e01050708010302090a020936070207091a1012050106050a0c0b18060408030103030305010b040803 85
    0x1031341c08103210b2070900901840000058950f03100901c0403e0086c00b0060716541818041c0303c9081e0060f00e0040c010109210038841c0e955840c500502014003400c0010f80901e808000c180075015003280500280038400c00c111000c1d09a0000703134425000903001501e060b01e03071010b1404569250240d0801492815003040c1c56600a64080d071140c92400c2c102c0345840901e681d07052410f07180503006e000c823150b040f0600020756014001c0340c0440500f5002481b0030302e09000000e01c0e082051101a206140030000f140707490106504841c450000039001c00117000300d01c1c1d00c42e403c01a002c07070f551752043c00704a2030750a00c4649240d0b25020744010350242880d14640200e900c00341030750080d2442450340300d6200f244659902c038100c0b5110781058981171003124610f1030003c202c81c4d05a0164052140801c000c00c2c00070740c44201c0c914401d80c05038100c506a280d54800c0148220b126144012a100710310502041c09240400b65048a1007070340c052100340e88543c0c41009031700551090b0340055005020300b207503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 145104028 1250 145102778 145102781
    0x1807030c0f0c063306082d0402150403030905120106061706031608010b030f07060c02010302070804031703090d03060509040b1b040b0403050105011a0702061b01020f0a08090604020a09 81
    0x1072201203003c0120154901d54070034150444e04a07200440d101c07030b01d00f00400e58010350415030210322003944603404554400c0424540e5299900309000d40c3c11540080c0c00c642e11100c4500340d0402443c10b841e02c41c3d2b10b900d000f07881b51803503001d13541c0b01c1c0007000c0c0c0005900308140160415036007980d54007103024088a414102c1035002030100c0d50306001e051041c022051002400500609441d0000b194944065051609240e1041c2ca40c00c0d980d0403004080c080c40e5000b580710800640d0a2034016910013207420910154003c0b41c00c020b01c42101c1c408075800c450700b50005107010320648400d44600464100c03042d0100c2d8400d206058010355002e000a000c80d401d50784103640442418003010082540600c8040e1660080e0060502204049418820b20900f4460540503012000c440c80303415161002e51b0110b4011520001e110383c0c1e00040f14100d4250861103461a40342d00c0c4000d5446422100c60b5034129040301d06500700040b84840016840c1c800040c03024001e60f009840f611255003400811360 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 145105278 1250 145104028 145104041
    0x4021807030e16051309030509120c09072001060305070509060402090909070807061d041104080303070e1203090108040303020d18050d09150e0103050601030b1807030c0f0c06 77
    0x40501d6981c0c0494110540140004012074200c901e1541c1118100010001e0b8a450440401101031030141c002c000260010100da60340c2000300d45010100d01c401c044549454010a040b0341c000041c0340900c8200307500401c90202d50003410110b1a110648520124200e96440c40041c00a034401c5a040100342000d08105401410141c40945403042001c0420410b190036070381c1c00e9066105440030403034001c003804044050030203480e1040c001009074221b03c4643d16103501c098426652981d01c1542038484200701d42c01411024240c0e1744030314102601500000b80b080e902c500074680030030040000c0da004402c076200c0580503151058151110f8900b20020b4002121080c05540d40e82e0b4051102e20303084c60070240d5903120740c0042012510343ca40091803003d080d4031012400b50341d1011130103081d030440c8541c3c4048100b80f078000344542d01c240040b00500116606240c0000c2484c1650000100844c175682c4100c804d501c0031b1164030782008080703500401241d21040040c1c181c08024000680c1c80d008070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 145106528 1250 145105278 145105291
    0x803060d0602070b0601080a092a030506130c060503010b220504020d1e05091905011d010b010807050405010903260309031e0403020a06050c011508031809040218 71
    0x2008100326640d205002c03030b0700a800c280e40d115074900400105603071151590380d0140d0b02c01000d209051490381d4004180c10f050301e80a25410520050304088400101c4441c01541c000c404ca440506200c007103080f605c208150152001c0c0109074010030350754001c10441c1e04803010003403001c1c9003800808010021600c41680100034059044001a0360707030305d500103040000200032340092200802a44445035201d0280480040d9003400b0030030a5061000c03905190340000e83d87c515501841c646002c40c0104481001034611080c0c20074480c03070884c41548034410611089c2c03208081380d11816000e980c1c9002e00d224417030018003001d078140001030514248000c00ea80e40c038070120f00c1103a00c03070840d8583c0c0c004484014882c0e001207a150400701da800c000030681080e00c605545014291b401083d0821420b00514061001c005220302c142c2009600c1a0111100f03200c046c0300f0640c0b102c1c01c1c1340c0c807179000c030100005125104514009900d407214034240200d43c0200038013501800408282052100107010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 145107778 1250 145106528 145106539
    0xf050c0916120f060f0e011403030708030a150f081b1e13020f07021306030807030305060d02030706020601141c0210050d050103050c12060610080c1605060f07020a0f080306 76
    0x200151030450082201400c0c0b040c0c052581d5504043c120504586c050744552800066524661140d0b1408400c950721590402c0c1105d5581d602c0380e0419028006882203a10600e00d20840019125072601a038416681800300781c034010300083c040d5442810400141940c8401819100068076025980c407007290140680402c008001c2801400c08903000070007000c0c852080000c0903000c503e070482401c40c003007505803410030402d07003541c80349031540c01212402420300d662407002c40c2e500c1e9503060410b2106c03a0f00a0441d5101922240c000752105420312561080000c0415054024604506500b03c9200801c1c5425621340c0b0940800c41c510900603c10014810100591000c030718243c0074040c065400b980052090503000800c2c020a20300100c0b00c2e003500d801c064240090765803601032003c001a030030b1801030b2854582c28401c0900d4451807903903489008401e1100010003102140c0e141c4180078402125080f582c480c0c409980782e04160000603e40c940032921100012a00c4d800b0750b0f0040d00182a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 145109028 1250 145107778 145107791
    0x15140c0c01060914010312020303040f0f020a12061406010f051e0c070609140108130b06120f012003040b0403051602060714010b150a080604090f0f050c091612 70
    0x281c0d8802c6070001548111300320540c40040c030501c02c400601c01d0b40988030b480150b1842c5019203c14158110600c002088a080940403e0035503031800b890706c0161140c1060242c031395696240c1040108a41000003480d070f036030b15000503090360141030340400c1e0305c040d9120289131201500c0342d400421600f0500e07455100086c0400414403000b00040d05c081c1c10700341c40d102000760511203668021008014014104044a41088504e5000c020f030805410360010301441c0940f660f100040189204901102e0305101e2182d40c00b000d000150820144401085a850154542c11400c20303c3c500c401c99021b410591150302107000248140024115a045503c82514108050380012582d600c101d100b5507000c4060340070f41e02502d00a11039041e40c0441203902c01017007421400004a43c0c01103445000601c170f10080007581589803038110310b200039403084c15800091128540320742c0c41421607405545a00c1004071400301410721074581801800c8000b8142c003a982802000c951035400026040c1045407070b070a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 145110278 1250 145109028 145109039
    0x90925150318140f07140d030f12050c0912010c020a0f1b03200409030f0c020102010b04060801150e220f14061812162105030415140c0c0106 62
    0x8860f801ca600503201501d819000c2460300351400070f19400c03208110305103082c80360903550742d5091124155031500740260009180c0605440c1868000d006070600c84c1410100141070301d803000240a0b4901c02c850701103030246000812400c8641c036200b000050b9200c100f544000c20043c540c3c900c8190f01c601c80c0300c41c14002c0407003031004400150b40111241070b44841c0d5122140300708890100100800d40382000402c403991001480208145296404c0c008004168030969200f1341000030101c3d4041c0061000f81d6030f600300c031802020394100390a921001c0030000f040400d1043d0354280201d01c2650040c8d2450314948014401c1d400000c8101ca03084551600c80002440f21202d52040040d420003918003032400c01001200401c98804401d402c3d005a0144c011000d01e84040c0c951006556461820365149840e100c10120712611a80115842000790303118585c1c2e20030002c521882c419540204000b0003048400d00380d0340480415014201064005902c2004030400b5081600303105001181d8141c2d0344 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 145111528 1250 145110278 145110293
    0x40209071e11122a0a08071208010501080f0604150803130905070c1a15042408031309020c010b0a03110a0902071e0813140a060207080601090504030e090925150318 72
    0x7400c00300c0302246c90401348d00038160465141c90040c4820308043d0090701c2c00f000c0034a04a80d0003070030b9610840d56130010010086c048020403010b0122142100e50b61103040074040c840c40224800c0351100c81c10700000030780181c0b00700c805c81c104a52007800301409242d07000c0b0410740c19034010a4041403100b001c00c0d03245959501d003d150b0700800f450803040700003030011000c4031618035540c00c94031090b402081495500b072900300c0d20700c0460340110001622500228240c2d03024155038030019a0083e510341001c003e00800780d0442d65080c00803140819081d03640c1c01c40d10107038000c01c60050103102c40845251048400c002c41001c585101e03011842c604001044201d1902826030090071000f000d500d001545030915014590240030140001c0c460b007860440c0d03603543d80c1da050081851039074a88020808060090500004050004091108500c4c0000300d45a0f15001c150084409042460719032183c0c2d80a64428026120b004d052075000224004043e0094500d992040c94000500e403154400300d1402d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 145112778 1250 145111528 145111537
    0x1203140a0320042d03020a170609011a100207050405010b040603060b0c1903020c03100519060b031314060a0915020c06040209071e11122a0a08 63
    0x76240010741504400401c555114420711001d0401d4040006201d4080841c10300c2000400c0c481403814480c2c82505070409840c03c40e840290031191102000c03483c0b01418420000ea009440308950980d07864000060980c4c2080c0003042d0b030ac200c0d002100541d401c2c4440c40307404000150049415166440000c0341c2151000d90007140184c401050520000e68140104002020b07080303090390500c40c282203896218000c007146586840803a01803102058024400f0100307000008083d500310383d00c81001c3c000688000c0b10380c0380b440e091507010301031400c1c8c05110387d50a0780c1c411110ba5007160740d02e071391446400a01010aa818858403c10b40001e00c00810803d03118400900b004a0100039601c5c00603241199541440030440c010b12800c40030040000b40580d0260b011140821140c40b001400c0c0e9408034041415030403e00c034280c034640703150340100c5198401c0c40e0100450319410150340184080e409009004107840610410080000080d00701c152100749005081d01c0762540303c0c0e03a800815500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 145114028 1250 145112778 145112797
    0x70318030c05030c0103020301180228020a02040501171b010c050111090a0501140703120207020613140402040305030d0b010e0a060201050105091501051603020c040e100f0e0601120314 81
    0x19107401030050381010300c104c40311000300b030030150700755414203d210000150202254140940c0403590820206402c44680e2240c05d1150409200c0c1e0b5240c8002901da020b4803200b640280c1c1031a0000800d0404401c00d0b082d107410560203041c80c14142079000e010080044003290401115102035000705900717201d00800032502d00402c50381c90203000c0600410710801e520a6041c48542d0085450b038555190480d8031569141c0342c103440412171592040001e000c0d6060180d041140420045428000943c1030b5041d100b120700c0c1002017074541010841684141d01004140750402d101d8066090030903000300c10301c01014100607264282600c0400c41c0c00440d640300f000107079143c034010461403c02c080c001d60052070341984141c0a100e5074001810900c140300500303044179403a02821051510911000e0104440200240174002d0380d42c0807142c4d10382c61012880d407010310f4030465180000d1144590f4809110004c00750000d82e1030f04100000c0000038000560901803400d410000c14540303071008080312a07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 145115278 1250 145114028 145114043
    0x7050a0f030e060f0c0d030209010f1404210201080603060903070227241f05031b030703020d0e03030906041403130b0c0f12040b090d0f03020114070f0503010b07031803 74
    0x341c000300380c0d1b01e002d4148800d10103041c4100502d6049903440418142c15819a003084600c201d80c40e2800801c07440780c3e0388400031001c481700c404801148049540c0300d03082d000341d8400d4904d8031036600700341c3c8500003942c4030196548100000401814041c02001e14240340f03150750305041d0361200303020203624800c5030710743e900001520005407a03009840c01240040300968007000710305d00c04403480c0d582170780d001901d006100b4080300007004050300b50819042d254082207455100d0400c0e08002d001394000c04244924a4240003200c480441c0000a0340d00c1842064010034075030312507454600b0a8540950b090031140001c110f148400140042c07004018a0500003c9a4490004070300314141081010b2000603500141502102560b901060303c003a151185091039483c0024400601d203082404002001d61140c040c800c0241034040d800b41800b55038841d07480725680d079110411150411086580008980e080c001400220300103006019528442d0030000d01e036132074040310404010015401102d550 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 145116528 1250 145115278 145115287
    0x5150a05100c051507081f0e1305010603030504091d030a0807020f03030123180c090d02090a020405090c0408100c090e0f011e0f03020d0203070308120108010c0507050a0f030e060f 79
    0x176a0005965500c4a920314240b03629109907110450740b00070320b00c2600341444100c0045414510b04180d0540c4d000e5100000301700c010751760300d0040d020b500144220800c0c00c0c50172200d03450802d1480c04048009585002942c90901c04030317000d640781c05024201d1800c501c685000c45244030800c0005502a11b84140c0703000a0744c1c0c4440b005034200851500c0c03e8024046210003003400000c0700c11340e9400000f000c0c0741c5911035102c1310201f2280d402c10380019600407100c00900600b040c56500400c2a22410b0762202c4040d6514001c5040500c164402c0d0784a0b50b005404000e6a070350302c0c1d4070045007594140b13040032800d0703522200412480001c0d41c4503800307680e0010040103a948088000704c031103051508013125840c0b405a5203c03030400c00348406402041c1c50300e10501151341c2442408007070743c3c1c0010f0003074851100c00c501c8501c08a0034015450150b1811110400701c0c0d00510641d003030310b40e2220040060300503e9a80021441c940e00040b41485141c1c103020104d03584240c00792200141020700b0381e464 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 145117778 1250 145116528 145116541
    0x3040302060c070e0c19270311100c05060106030906021b062410080c040b0a05131a0901030207020301060905010b09042403030c110301060603020c0105150a05100c0515 74
    0x2941c0e000d030840d4036030705e010000302c01c3c140540b25005502d19500e04000000003092000c0c1c003003c5807411840d1441c1c3c00399007008000c00440411809120364250760604904514100982c1c4115001070b01510030307400340c401048524032981010710340c43c0c801e40340541000c11088050340010641c810418080d000002000690080070800201000c582d0b0a40360340c00300b00c0d00c08266101c51b503d5490041000540000344410141d00072140203110382800181e44041d061001000c4d42c01c1510704000380604000d00090f1b81d01d8801003100c10a1041811070b240004100041d402548100360480c1c155498220010300001030b07211b020f000303241c4070240320380e10105201004200d4000c40001207c1035034150204620700050484c030300940ba032505001c1092111801d01d02400c1c000c0f220440c5e4190708010380410081e9064001d882d00e0500c0d50000d000649500c40b0b44c80e21041c19100113900301c002d40204101c0c03842e201c500d40f1070020150030942042107140e1101402c180000c490f4030f040c40b0401007403100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 145119028 1250 145117778 145117799
    0x92805011406060f07050c0a0617070822110a031101030f02130302010503100f030f03140a021b0105090904060504050607020a0f020f180a0603030806040204052103040302060c07 78
    0x40309505418146007071401c00d00240f0b541c000c0d1540f49a41403004219030003044010808000d05034030040106d80d800fa5030303240c0100415555503481c0301c000444030100d0100e900510150780285828000302c03a1890601520840017004c002d015118100102c0721030310251148940031001d11b004070f82c00780d1808852070004d81501c00420308182d091f07204005148140070383d0781100c0145d960928001e5565120b03042c10a8900c40319812411500c5c004860010400143d200b0101140e4072a07201e0340b01003240030524107203d00500d0044005a04445682d911500140309407990350041410443e091540d0b1802040080100311030449980f0f0347e0324207120500c6420000b4980c4600148000e100e68020b980d01d03000c4480048500130b004001c104d864a207155620000d0503c551243c0e48140103d00e0902c408074043c10031071000786c002c100d0600120341682803500840701a16009000801e000b8a0f4003a10ba020115900c0508081d010030301002c001a078848005004c6029040000c00074182407802400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 145120278 1250 145119028 145119041
    0x51005010803090f0d0c0f08010f15120b0403031d0304050f06030402061e0706020a18090501050114030a2d0c0201090b0402040e0703240501080604020603010e09280501 74
    0x511950052040e240580e441c4240130000700c8080d20380c0b401030314551034400f2007800a500189490440480f0110b17140304158400380c0c101c92051428004602d40302020080c10310540140b089000f45145210041410310205a410a03c44e00d80041c2c81410002040300565000151200c5034000060030401031408070385000c60384404586d9035195007020740c0050302d684104003000280703184c039200a0403009a070809460f482d5800c203070b05540da011407040081604207422041280c05c6070399100402c60b42d81c240306080c1a1601a107c166402104103d095026040102000001d50300c40da00141003020100c1291600807410048103c0d8441c113205403c142d40100d07185e081161300d880018808151400c281d140c009406803000200c81c20500040b6003441c000f030300050a0608911941c503020614100709108401d10311104005507625030032020345488098402940c451420701c0184884056200c1064100c0c45290407a42d502682d8490000f2008502e500305089028070018601440020300452 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 145121528 1250 145120278 145120289
    0x405090a03170f010e25050a031503050304050d1103010606080105011115040204020c15010605091528020718090b060405040314090402070c09091110020c010311120405100501 77
    0x2c916600d0100d8000c50100d00500c0fa0448207210300c00410320101c1e0100300d18079a0303496594078130302c0c8070540b000240071584107034185c500003032402d03d940c40800c0800403030b0b8055992040186107410b103414100844000b0020098543c0c40d0023248105140d903003481903230010409511071548540c50b200c005040011406e0b600c0c41190000c80c003d46007403840850303880d0311640c1220016107558909100c50324201018400f00c4032000c0680c004036096800002520043c80c040303980140440d00e607400448140a61181e06103a03002030060f034103c1d91012529a61200301c0e6104441405a40c0e0048920803890715412405560b075822503402881021a0309030b0b800f8605039400d101c582015580280f802e0881443c821245001103152082c40d80e5a030115030b01150410242903a194a40c01c4602c0280740b0302c2c00440310103840c01007542d114107146405006102d0150003504055540500541c042c00340101680141d0004000308505005581c4000d40aa8041c2004140f680415406042140d6068000c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 145122778 1250 145121528 145121567
    0x90c01080f190f020c0c100504080709110f04120606090c0203030a0c09171501090b0603040b0601020a0b160207060e0607170405030307050a0302060f040b04060e0c0405090a03 77
    0x204851181d400000e80d401c0001c05445036160303180006007600030041c2c201202429400011110360fa0307600002c100003200e00417180c903000941c2400301a2000d204501c102d041c0c90700101800c0128410980c0f051040e81101800f82d85040e01e5102c1030005640180c2125145049030345140041c400a403150101078481d44104000078003c010f0040d50b02c2c00002c20107c5501d4071090f0300c200700d078030a000c0c4a00500594000030001e60300d40c107605407128000300c194041c941042000164140050041790300410014100c1440d41c2c1302ca031651000104000d15041c1035100e8042414001284543e02078031541c82400c6d0f6a200070100a8000c0c1400220740c840d504001d00300606068a075180d82c22030300e40560049000d5000d2882c010801030b14059503021940c140008643c81007485004035003c82c40d01d1280d4260760b000d0f40c07003154503160400141c801405089503240010005419903011000516044040744d040c00b00707940004c1e00703840045815032010f8111000360340401d07070070045191050707403241704 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 145124028 1250 145122778 145122781
    0x7091a041202090a240603050c0301211b0308070204050a0603031e090803040e0106090605032a1201031253040c0509012702090402040b0c06090c0108 66
    0x309100d042168030041e20031000000481e1500e60f41d075014001d94008074174011040c0c181d0704c054601c0c4030280d01c54a00484d08000000d2003101c03848085a06948038030307803080740690001412490107101e845045540b032a504845400034460034a21000a51103034040a60b91000e070300c10701042d01d90160502aa03141400381c2440000d0b00008010b4400040c20717030351030001c0d000d000215800300d00e950004040d03002c000b4021581003203610b00141078520355159900c025560b040202c8261000700c50307504003030702c00421055207030503061401d0000c0307207032030751410705214032007000e07031074501e420307401140c3c0d000300500c04040180e0000e006c00182d100354280521122049036020202c020024005481d00d00150340c0f0000303252404008101401000082c1210b42c030b8249049c00c51211a40100d5202e0403400e0b000088002c02c40c20007110300c90040440144010403070022401070f4000280c0c10f54010b800744800701d2840201e00c042e090120300c80700107180138213040c00c0c2281004212943d50341040030120 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 145125278 1250 145124028 145124039
    0x816050105072303070b090618070b16032d0e06120402060a05071403071e080d0b0310140609150312030601021005010323061b03060a0305010507091a04 67
    0x46101100a540f41e00e1a0000c85402c0300c0b8118421014020906041582031051440000841e90b11459803d10860300c80300c1908201903460030184204c0d0000754040004910310781e44440c0d2240e000d48a0706002c458000440446c07c0c1c8001c218650400401e2400c003116001d5503c00c50900c020302090324158070b03007000c0540b100030710980200b020740240d400040d03c070801c0344200110f03a01160005e4a901511070140141a101c0e40490740550310203d80c902c135055017604000b803100745950b001e201581350035103c140300c0028010a4900300d504d4002e034180e4901160b101d000d01d0381103040d22001403041d4070705032041100310301000d080c1d81074115a03841c05148540f0000f0303244489224407446503450b940e0700f0004030310300010031154181c61404c1000010805c10001c0344201000b8121a20001501003d9141e960f10350301150140c007001040c0e080980301c0030100c80115000720000d080086569100d89503a829148242c1700c840000c1e02c0b00d0701c200004a944804401000c4c481c450140c40c080c40c11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 145126528 1250 145125278 145125293
    0xc280605191b0c03140d05011206060501030b211c02030a080a0501270204030213021b0f0303070c020d02030d091502030c030403060f020721110102091503041407081605010507 77
    0xc0300400380212164204090805c40c42950130000e07407014244219030b1035589000a045e80e0100c12910a810034001080d150f02a011305030841802a1981c1b2400380d00c0342408411201d2001191a07600682c0111044004d1007400f0302d10417100c9030000c60741c4158103c030040c0b030044020b0030103510600d080018805514804a03041c0d92556021040601c5c003d0010420300a118550000350b010300c0d4644000050740700380d0060b0030703030355001240c01030304000b0071086070389605100e603c40304107400c1000007a140c14014031040c202140007900074800401d096000c00e2400c0385c215490380100e031014108000040c1c1119261410b10390502c040d50500f9010040d0907aa8001c0d800020722080d114882000380e041c2d6581500c0400e504503803c0c19041240c234051924003040c2ca6500c1002035103804031043d0041d414000c07110390703c0d0301800090700f403410000d003c1c0c05034101400480d94800703000006003142c1c4c0100400c00180002c40d0141191980e200c0100036408440d9002c14103000c1c0c00d011060102d0280d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 145127778 1250 145126528 145126547
    0x50a0921080703020330070804030c170412060b03011107030804080d0b0d03030b010219050a0605041a070305100f06020c0103150b070b0a050901020c280605191b 71
    0x44600c6889180030f242c00d80c1180514543c010003581903c8584400420b01400307481740e0b803200840b011442d241c0718402c0325040d40868018020561038425030001581c50000e80c0903d00511010a0078540c44482008040302194000c0c2e030540c0e203400000c0340c18030742803180c068500c3d1141d01d8a40340030103e0794003a1082400030301c050080600405c44004008203500545017401004000e0100303900c407864060010101d041c0030718018405c1034120b5940e402248600b18059400034010481c0d108580e40c1c003005420002c100b103d102203000030001c00f06609042e00c50140b07007a07460100b003900d4118031000c010700d50740d44149042c40341c40400b0440c00ea004100c08038200801c1c6000300e040560900100c0707125410380c0c44400d94074400071304035050000c0f100c443c502800840340180001e88030460507509030f0044984048072504000041c01c0d011000c0b42116146207400301100c958841651200c0040b00c02c1103c1c04082107440324400c0703405a480e841402609d09110509a4114450080040a0644 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 145129028 1250 145127778 145127783
    0x11070515030a060510021207020301060e010626090a08030402040906060b03010806060d03050909090a05030408101104030309211a010611060702190c23011202040602030319140403050a0921 83
    0x3c7c0082c1a03410764400b90800d5016201e0100c10403c6949c2d40c900c010200910400032aa004031120545140c502e00c910303265010b8004000140300c490095120f0a14a034000340c401c070307030260780c0e010a030300000c02c0f40c00780800074480d14045685a40c9009000c604119001b80040e10030060303c0d441c80c0002e074000080c0e03017400a0554a040c02c5a403055110742c54050704100c042c09130b10000c60300041030301c00000d000710003100b01402030144000001b01000c2d140160b000050100b541c1c3c3c081031191690018501b19062640404400d03198050307126111022000000d0400c60400c4900500c802303600b00118003201d006000c0106070a142c1000029101e000040700401c95204015106043c0100342c00100054980c041c52020030b41083d1160386401e03108818040d0208030914417500c90340f00035200b0307502107902c0c50b000303107240d0f0303544841a03108440d9000c0c4600d45580d0381c1c03400c0c204015080400c140300343e1080d150036544c2c1c000050302406200c00795000d40c980c0300c040101c12164104002d800c9a5050303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 145130278 1250 145129028 145129063
    0x8011d0a0b01022a040605030303010e04080f1909060e06032a07020405160e0102060f0601030c1403100e3106020c160513020c0d11070515030a06051002 67
    0x30341c0100100e05024518400e4854a044d10250060b1001010700d0020b9240c8101c4040040a64030401d045d04c0b0301091086c28400383d02540000c0108415000400b065032407241d5492421402480844a4a0710000748400040508006000b1150085c542c44080d1004560140c2585480c03a018290790b18044240c1561400c034000a8440403800c07000e8817000e40e030042c8240700e580350491804c4500b008400e100c0000800c60049001554008200700e4002c0c04010320b9100141d0b0390000542c050820b8020034010004681d008100c0300d81108c020b10f00459001202406082ca0aa40a501840b0140900407451201100300040b4044c0c0c42c1890203841004404210210719810504000d01070021602464025050a00b800c4801d150705103090f60404c440310070000d025200400b0890090540c5030307060354007201c4103401240c0521552401c403410b0004445040e5251800b09070301261b401412490200c0100c1402035551740390055001910055810240500c2100c00017503a444103c1c01c540b2428 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 145131528 1250 145130278 145130291
    0x4050c0d05100b1903060e070e06011d0105090607080d0b010302090315042102060a050a090b070c140f01020c0c04020903060408030a020909010b0c0d0f0f0f0e0307031208011d0a 78
    0x281c86480700c131007889410715040000981d490800c800580038410309901c2c03074080c0040116261094040143c011070040e0f54105005074204c505c10010307454010700d00c2c1404000d000700501640d4900050820707038810200551924415042030741a02c0d0152a0f190600d80180803005103030b140091002c0054072183d1140110b600c2c0c0c2d0402405444000300c40002d4051010004164140c0003d40c050050740d440208201c10360b10220042e04940b8540001020340308908040740c80240305e90340e01c2c01c403540124081c640c2d0200701d84c6030624004242440c101c0d10b9402090340c0700300b01002d1009083c0d80e00141d40070b61526a500e000251100700082006140c20740c0400410309080d01da0307050756140f8170b02038070040305961203951201050704004284d18031481a81d01111046109184d030000004c1c240e1178125500310100020340f5034001914090702045004144611342c0e41d01045514010b5014042c000040c00400300e00410707402058020312103110000c20354108150220040d0b962140c1c070710300d001814 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 145132778 1250 145131528 145131551
    0x20f0d0e0604080102041403060708010b0405120f0f281214070c0f030b011401090506090103020903011e1b05030a090c0e101e030b0a09050a0f080304050c0d0510 71
    0x6a0195030021003c9620105010911000d9001007080b8103d00f2000c90300180e036907400454545509008100c1c41e001d080c4800c020900f4040c1d46801c89806500a65a681804e11012441e04034600040c180030340c0034511600079100c0984e02404205551303004e120320301442d80c4851080100c2d6040c2d01080280f10890400140600001d40300020313480040c021000d0f60b1610140d0301c025081c0001c0c2c0329001c041000140010203801c204442030010786230000c0c3c0c20700d420200601c903040030841c01d040c540c0030080001155400e02c2684450518030b121250720f549902d100d50119288030240d024034121020124021a4000090382da00100400020ad09500580b6150207401d00950080544d02d4000080c0041e8105046100099030310f075000441c450300500400b260314040a20000e007668941d840411a03541d0340d6002050042d0242c000c40b04003558030f50703d180300b100c0c1c03510064071020800300500003000024011400035403011106080e18007403648440d500c60031413070801c41a490355000c900b8032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 145134028 1250 145132778 145132789
    0x1150e040f05070b0405010801050d021003050a06080304080102070b0a02040503061302060f0d09060e010218010c06090203030a0203131a03160e060a0e0135070c0f0f02090601020f0d0e 81
    0x101d45501200b607555180d43d8001100f00d40d001030140b030f804995030000200c2c4a0030a422a0315580390002c1c010701e009094540160300a140160212084507242c0c070b000309982c0b00c20070082000301011800145c0c3c500480c2000104810058648803015004100c10001e41c2d0b00002c03542e400ca91428549900302449200040652140a149601c00c0e013002c43d4030540340c00030360b00c039400c41405114284600120700c000745080341b14009001001c10004501a410741d441405103082d0544603440000d400390890b000a840c5800181030000140d02c0003400c60804541d002890000b40701a0026405c6070300c80192004d50b50100030440084015181c489001c120711900821042030409404940d80b10000400141640920b4049501040c0709086443d954401c00c0c130a5001d18181801980c0002c0d030b01009901c005001604080810003000d00380d001040c4407a80309882c05104801c9845c07030b03c04620502109000c0148814107640014081001520740414032940400c0c0303a00d07003446080c0303000740041c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 145135278 1250 145134028 145134053
    0x61109090f040210050d021c0e0c010f09140102070b0c030a170402031c12050408041508060a0b0f0d1104090e012c0a0c0902030906010b0a0e100302070204050a0504060e01150e04 78
    0x80352381904144110945200d030310407010808046d0179102ea42d100300c0010340e02c3d12030b040400000070f40d20b0a010000c4096403c0300803a0088148165500240d0b52200030350940c01c140c1c5d0401884d040001d4a06040381c1219640c2400c98040c84044a20328060700003d0b210014650410482038003e4001c000081c410000215410210102088213040c0f0342414106a0441d004140700852050110007a0b14025040740344076090040c11040c0513814040f0140c00c03904649d0001c0c00d0110207200b104203905040c041c1034500f240c00c0d40f100786c8031844c180440d000d95403515100c6010364034141c480d03403a590200301c01494001c80d4070000000300850004091030034515140207082d4601031440491210a1038004500030402d080880e01c280c0d880d00400c040c4c40c4202d400744800b10382403024880d21400c1441181441c0c0d50f0a04005081000c83c2d004171f07043d104229110390303003141c2c0c0d5010003003004098851030702a00d1a9200805c100c4800c102c80d0004094540115201134070048002001c2002158640c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 145136528 1250 145135278 145135297
    0xd02090607210806060c0a080702030f030d23160e030c03010c0305090c090709270f0c03060e01061407020409140601030c050319060e0a061109090f040210050d02 71
    0x40b0525545034030b4012000019814041c005030801c00414560300d40302d003e442101b00204098104c0d6a4681c2c2c40310504d5100ca001207030140160305c5034000100050028060a5003208000b05012455442540c141070582d100c0b0400302c00050705001c000c0d64030b100711006054180c240801c6054110000030715002c0d0740c2c84441d43c15820841c95283c03e0b945900110300a80c43c0008848801d80404200582c500b01151424000340c04400e041104454140d01404100f2200500b0481c65080400e0501174851040038112210340fa030902041d0503900d40b0400009019803040b0881a50601000030710154030b0f21000941510003040300740944d9503aa0181407031562000c00c0c20700d200d031002012501e84070300b44000d8540d031561040c0003500d41008a540f20748243c0707004270503011a01507502c010003004040c01c221802d1140b04030150009402e0321464400024103081039407104204010012641d40042c16403010359408070074000180c9900749090000010ba05006847d0304103109020003e019283c401d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 145137778 1250 145136528 145136543
    0xb0a02030a060509070201090c0506090603060904030509090421020105060f010c030311070c030b07020114060418050d081f05030a02041e110d050718140105040302090117070501140d02090607 84
    0xc0c402034071b40550200d070850740700d00c18001800d070340c404c200078a07030145240403034011000700009489031910150441d4400d210b820910b04090960700441c5522070100d070100c4080c4814072104066142d00b408000c105450742c4000c2c081441c0070000f05903040f036a88405418032045880080030075000360412085000c0003aa1592520202c0c201010b04044a2105596030b501030300204800a1040c015405601c001680003120358a5007024000140507600303d208170000450424000954280850068200e641e030b075001ca18107029401403000c0000c1c1070b81082c03024031603c0c00c215645000c5201002c1c4c45d0100d90008103022031420f20b00c2c10384e149405100754940740c1440d0390f1403007481401400d015500b060040004d0380e030b800401c0d02d038120506201405807100c00400c101d100202440c59245000624125040030b030b40c0e86c0882c0c0800742c00e070410703140304412403030303040e00c1c141e041000740010f00d024038128819050040540580b8442e004402c0751840e000901c0ca0129216201162481c6501012 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 145139028 1250 145137778 145137781
    0x507150324260f030d0b0d05030a0507060b06160203010c0c030206010b0d1803030e100c080f090106080f0c09160f08280b090a0b0a12061d06070e0d0b0a02030a060509 73
    0x4031942c982c2d2080150241a1b071900100c11418181034011f80e210b140d00800451034146212419103581c1c211242c21a105030f11000c881c0241d0712901c2c0904500c1801c4d08180300701e81d106204040c2943d8494241d02c0400c1a8000c030f80011990020f902c41c11903000f0181c1c150f852603403c034210050030044000b00104494402040101035155000c9903451824006444900303e19500540c00d1b658050780d03020019820070041280c110070f0072462034016080c0000001c0d242c2ea640c8156080c000d00583d00c000c03d800034141d030200c0e07080ca01c01c0725a01c8140000d4180755110040c3c0e0203819040031210380070800c141d03140002d80700d01691f40c22500c4113030030000d46440c6003a52003110015141c810140da0080d031410001c00d00319003c03400383d4220050010040368240b41010001451500c000d441510342585030203000520722000c100c1ca01140d8050400b4010344d10b0032a0380900520003000c805800f0710943c4002e603000c51007035101d060b0001951180582d41c2d403900410503002c3e19042e00101e0303202c20200c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 145140278 1250 145139028 145139053
    0x40302030a1b0b030105010c060b0d05100b0f031c0c0c050303070f03031a01050412020117090a0506280c020a02030106060302040f05040204030b04080a0c050715032426 74
    0x204428904540e0b0030282c40d068960343c540d41c1d940020b20980340401c3c1a40381100000f0001d41210f001140080c0152082c1000350b20703031074500032403024401d03089a0b6900c1c01d60658202042c0340c5100c088260001d0039010041000201013401c0c5030729410070404401901d00820603131840650003402c0040c1180e803618900e00f8840ca014416030000c801103440c01202a6060000f403034040801c0720140c45260505140c030701c0300d04e04071102070822810402c00a1200c106003452a021600503114803008120039a964039110345403040c081d00d041810049650100168021010342c011480d01e0003602103010b90051009030b00d440d54a0400940c95400d109020031700590550140c02150309101400c010695500e0900007244030b203000180c00c0340d07034080004020604400c028400b11f2130903d440081c80840c0e480d010b041806a0b0000c600000d40800c141400540c14020303640600385000301f07410804010581e0f41521002e0384a5501184403403150b10f242051070030b02700040c0c041c4520990302c0180001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 145141528 1250 145140278 145140293
    0x602030f0f07020a020307051009170a14061b1c0218030c010f14090609060f07020f010302040b03070e040209030712050d0809030a12020f0a0f121802090c040302030a 73
    0x444070503816000315400544034510000d1109807250b0003a000d000300f1820a03080c006209040c080320303410301c802810b0000310b045041c1c1c100c0c03042c04c2c0e01c40041e10032101103142000c0c1950040c00201003980c0104148034100079100d101d0300e1281d010041c61552501e4100110041218021001d8031041c4081a0f8844511310407600840c00901141a950701849820054034260400c07034169001412860404040c044200e00400540a0042c070640c24402e43c0c0002826550044003407820070000410040110300307121042c4803c1c0315003401c0c150b09007820720b0400300c92070200504034001c010282c16448041d0b200d69044031000304015068035843c0342c541c1c4488058a0810404468900c04d060b4006443da10410384076005085220146117482005103048552008030389070090201d50070416500300c0c030303c0031005140e00706081c0c4901008030800200609501032103203141010174203200c1c05a00342c05040741c0c81601d003541200c2088550720380409400c140e0065420084d01449012000b8007480802c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 145142778 1250 145141528 145141531
    0xa050f1c0606050304060f0c1413210605100506070222020408011514032d010501090507110c100f030b06030109020903060a0605010f050906070c091506020a0f0b090a0602030f 77
    0x8000c00c7c802c80c132455075a641101d280031400703000594005242d03004030141c0340040c840c444101404c690360980ba0318110b08141d150070003a007211220908a501002240d004841e4441500041c1c14540352074540412500c1c415084000d11620f041c003050400d45036000f4200c0d15000341504110b444548030350b0307450700a28001d0ba0b03041c1443e07170219000801000340e04454007051000340c00343c050070718091440c0341e04070035403075606501c03c3e49052b41c9200c600c002d01c665802403041c0c8030041940d0505a9002d0680400d10200341c410b604441c9503000b6a0b10303403510b02140c841c2d0a1401140403880198114004d003a90600301d948240d00100000752004150040d19105000328151002a1203014142c4211805c0e442a80e011558a540c3c04030031600800103045014405032142e8501043d44d90360301c0d41c45590340c024080c03c1d40c0d6a08000d040c43c0088140d076000e0031441c0001c000c2c50383c5545400c00c0c24030900b8002820300183d00c0029652420a2140c403004543c070000035905ca042455150f40003120 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 145143884 1106 145142778 145142783
    0x7090305010c02010906240303050d06031e060b0108330d06140a090510020304030504120b0f15090403030b01051e09040608030a050f1c0606050304 65
    0xc0c041d0404100d02d40c3d000003405034036494602d0481d1095000c62445255660010844031900f00c10039050b00d402d070606a407108482c4910001921007600010000c2c6040c42c01a400700700c01e20340d05c008952140f04140318400a0400449003440200e40c5a4030030041c0c5110044a43e520707a0041c1855100b848228428061150102d03481d1164039408035455a504c001e0400c500f4a4984001e41248a040f410700550032030b0344034240d442510501980e1301e60350000118041501442c200c800a0086000c00d8a8843e0031b82442450710030225980700d64003a002d4001030640426846414040100506064a0303448d0380d10214000d00c000c0c50000e0602c03408000c03003050b0000c0120040182c030095040d8680c1e640750681400143c0380254401c042690007800a11502904407003039404100b0400078640d280c205e00c258a03828004004070885100349402030215606a201d80154810790 = true := by decide +kernel

theorem cover : BRFrame.Cov 144964028 145143884 := by
  have h0 := BRFrame.cov_init 144964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 144964028 ≤ n) (h2 : n < 145143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
