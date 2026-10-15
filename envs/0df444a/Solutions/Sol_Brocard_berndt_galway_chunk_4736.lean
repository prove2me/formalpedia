-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4736
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:34:02.650571+00:00
-- url     : https://prove2.me/submissions/4d5640af-7b7f-4bbc-abd6-0c6e4386df09

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 851618705 ≤ n < 851798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 851619955 1250 851618705 851618717
    0x1113050906010f1d0406090c0810050601081b1c06080a080309010b0a0e011512050c030613020f0f0705150408130e0c030622050907030b01080d0801050d030207030b07 73
    0xd4103040500341c0d011a84002d00c4c0c60031035034450010788941c03802c0c55001500400017140203500c50401030203040d400d500c0403c041c418150071190b00700312604818071680c0709803107810440da2642d54842849021104480a07050b01704100d2000044a5184c2c0c0c000724250b40000541a44400c98146059241070042d69808004020041d48441c240140c6140c10410b4a100b90603500e010f4500d40e02200601440a20a44082000c10058458885c0c110100b01c9081c040c0110f08200030480803a5000392886070040d8401d0044090360541ea00032952503070b02d2074844510f45a84100c2d07000185d003002804945c0c9000b00c921700c03940d1890043c1514015030103240c2d440d554162003020741c941100598010342403080150708004104121805880d4010020350b6600c86500d01e0b020b01c0002c1c00e040d0786410300c455203040180a01d196000605506603031140e402d40311940d0322001e07035a594041e4401e00000040309480144004e0519240103140284240102d03448607890340e03074002c0c0307a01089408200080c0c0e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 851621205 1250 851619955 851619959
    0x3020403050601050a0e010b07050f1902090f010e150a0503121c0c020d0806030c102601050607030e1c0605040606051e060a1b061d0d0c111305090601 66
    0x72050002c140108030444026862034907101d04103101802c1403046090803e80400c400c6d003800424010003443d02012800c0d100d602e030800d4500e01d076811005500360b0243d40b084000441c035072040d0306003a060320450b030f02685040d40d5004004203a1555000540d401414145000459841c1008540800a04c443d034281d201d42246007420f480c90020000c42c6110740c1000d00c0c0089150700072600c1d0340440800c0c5042d83d070a5580300301181c80c0290300740c081034001b00d070a0f03002030045074441d04009950080400741065419043c484190382c420a0140640c003030810000d201c0000e0013280c185100702da0142c000381141000368601230181c0038400301516003503101d000f040200405407003000040d0808031040c0c43d00944401c405402c54031817195441c018600014809400c45c080c60202418174401070703c0241d255094600398026001140d103200000c4049245e0400030f200103e40c0c3c5c4513180c3c556071110724198003925054100e0b06007440c1c058001e210600d16082e210414040c451090030b2072001810b03694 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 851622455 1250 851621205 851621213
    0x803010905071806050702190e0907030b070525020a0305030a031a12030702130605040218041505010807270305210307050f07050f03160614060a0b031503010c03020403 74
    0x50b00c0c038500c4443d104000c406114040d0888250340d03016405807546c20f210694821100c08003190340d00304490480000003000f04034400040d922080d40c2c415591801180c45244003a82c1e070740a41815002510171103030b8152140d400841640e104580000c0807800c290380d4a40301c40c0e04541c048407100e000203884080d911803402d005140300c058000e00b81c070200d4601c0d0105400039200c0c0100c12000b0301c1840f10000344096000c42d50031060207060000c004646e500c98422070b99140c0b54501c107210380614200a03807510400e0502141004840043c3c40f101c0c807560b500182250100b0342c4050b2f6280d0803001d03003039036003250042041110195210703500030705800d0000010380c941c0000005110003180010020011f00c1340e40a4240c0e280e1010030300d4800e4450525180907424800d0280c4a10350b180710109420300b402814542241c1201c0c040c1008104450483c1c00c1c030f051030f06040707603e0380d04141e03031040400101014000942e401041900510207810b008400642540d1401c802e07079000a801060a1041c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 851623705 1250 851622455 851622467
    0x80d0f02131401230a0c020406061206050604030201050301030305030a0e0d09172109040f02031f0b040e1303110f030307030c05090f0405040507030b0906041509020d0b1003080301090507 82
    0x182c1c001d00380a0b0482202c09551034100d4181c2c0d588282940c2d0100e0102d003454010281a900140e004105100d0a03454503001040320420b5610800d01500f0004001000e003011422101541d406139201c900c0d50f801c50300c01b40c819510240c004002c071581c2d920a03005955041c005404074035280d030b4984052601d001064031440d015024446800d4002c4030119940e05407070225007000c041310700b000320345403110000010020f088a000320283c0600010030082030a4640c1c585001101c01d03180000c00300303912150301081500950091700d0b030a400c400017040300c1300b142c2c000d03d00c4060720901c0d01c5192404100c0b445404e100301942c412845030710202c180035100340c15002c0c8020303031043c0f072034205d0030811080d0024502460300c50300704d40200d56a802090503c0700a005070400f940d08510342c0b01c1d0b030381450040a940e0fa00c0440d41540c610b0002c00300081e05032007a00030150b84540003803078061110031944501500380c0b40034110b03c003200c0800c80000001480b0b038028600a1043c4500000d5034030300148040c00d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 851624955 1250 851623705 851623739
    0x30c0e07080a0c022104091406100810030201030f02160f0203060a0902010827070305030405090a020f09301b06030603030f03100513020a020721080d0f0213 69
    0xc103d041c040142c1200740d00080900d00719446440c1c0c60000081006202ea05205907001040880c1c20405109681e40b4280080346c001c000985201c5507000a0000c200c03140e03201a10618007140e4403000400240d07100e030708002d0b031303480e00c054006260400c510b41199142c1c07940d66049842c91420040a01585001e000246e44140b94650521100c1d4503540000c1c80b41038010010340c4607070f0014031031110b00c4950f0290401303440c4404040710075443c6c0301e003000d6a403074101d4800c851180c090342e0700061018046009071001000090101401c08540c401045842c0342400030007104000007007901808081c240b0b0b542140e8005400140480840d0b1400716004605120121406000204240803450b24000115100821001c8010761661501041365000c3c054130b91050781d0160401c8071007108407a0990082210400503022a401305942d0542d80c513039103c1446036010481100741c10307000130824100050916203082c45d07000410001c541c1c0c00300308903049007115a01d901d950f25814848000c1404002c2c00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 851626205 1250 851624955 851624971
    0xa0602150c070c0e070c1109070c0219050405100911041427012306072307050303070b09060709030c140a0b0f130e0610260a0e0c01030b0307030f020604030c0e0708 72
    0x1200340b274542400b81c4207401300705000340501c4401c05078540450a4500340b9028000080041c059403e2050301d4200112141c05801c084928241000c0c061308c031100100d5003200c003410320b50000001950100045580206080d1804018041c502c0131011b12500201d8081c1c017040a036007103280c42c2d070300404001c0903000e0000c50107254100941e50120394862003000b9030300da040c214071101603020741101d030034503045a000f542c040c0f101003429410003174910314081c40380c00d6442c22140fa40da00d100c41203c0108103440082e007901410780f400e100c0304030b045201003000b41c00580094401d6985802c9009607a005c0703c01d100c0c0c4140040b030f00321100d01152840c43d00034004071030204c01500780b080c0024140c50b40c14411805004407100308100702d5507510075a554101c24600020354500c1c141000401805603003010000714015400025007d40c000c0c89130041d01200a801410a1401e5135a0900c25280c8850140c1c0c2c00f041c288400400907001504600142507003188000c400d05195802400b9a81d020b40350780 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 851627455 1250 851626205 851626219
    0x150e16020a020d110607050109050a0b150108011a0903070902070c1d0a0f09061a01081b04290a020f070b040b0712050f0a0e0a0602150c070c0e070c11 66
    0x201c05a5110640c0840c100c1e00030001103454542d5000051040c030030070400808a5003408080028800c0226100d500ca50084020000a6640e03280001913001080d04250110b0503e40041c4500046000b8802034401c401510f01d01c2c0c905c8907000285498090303032010484980001c2e00908126448407514010082c405100c280c00021310041e02103080014208031810340c2e50420703603030382c1c15190300565546a00700c40100190134510b0500d102c0900c404a019000c28150004600a9000e80e44111264000c1d001d11074106030414141c041c030580c01c41c480c0100300d45000071070280c84003c90000c10440e07402d900202500300e00040c01c2c500780ba200e80d000c4048403000380010848008504100c5490561041001403450524030059501e03000e001202c011518021071484030058010581903020707a000c9850b06410b9540789003c0780d4400c0310390745290380c40d070549011030880710482000c1c2803954400c4119a8083e1344803920740c07614900032141400001c28107840030b405d0103000302c01c03401144010f0741c00c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 851628705 1250 851627455 851627473
    0x80708120a0f0c0201030908030f040501050709120f140d050a110304051032091f0504030222020706050f0709063501090509060901060e07050706150e1602 68
    0x19264803800100380b4103000b40001e0000031a8403c2e801044c10f540d00044a544a040205a10018000894084030720b0761801011a14841c000c035081001c5034540c0d10b582c00f40c42015500d00c1301901d1191001c85040301150951612114140b202400011084d598030b500c0d00c4202000a00141c8984400e040540003000300380155141c40e401412a0300807401d086080e2440312111241c192514045031010300b51034040c90040700380060007400c03500d000b01c1c0c0d507913440020042c4040105a0244030303140821801c000070001800d00000d8030102110400c8018094400404017100f607a002100495000340c0c2c0e50108014441801070550300440c161514021003410550050400390191040300e0a068030b15640f6088071030090804043c503007103901c1c0214156034800c0804090501a0f9121820f4003034a030002c0c0e00250140314180c12076825082807000ca490340d8400f56003540c4229815030b940e540343d11a1140031421801c2840080c544c568a4100e42d26191888580004140340c4240c1150040c00354 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 851629955 1250 851628705 851628707
    0x106180e060f01050f0c010e0d020c030705092811040e0115020709020f09060d0912080f0412031b1d040e1c0c050a0c180605091504060f080708120a 65
    0x7902001540a0070503a6170703903138208002d14140c0100c8141e440c440d03003485280602d02c000490407005a003411340850f00000650000c041c0c1b42c44582c016250411800000961404124100760b07116030314200022107142c2a140c40c0200784d803507080510310016000101000540b00350007009004002080d108011b41000b450002c0d2640312900c1480310080e00868406601000481215952a801007115036182da201f0782c54800303040c1d460010b58158000b02c0c14a607010340201c040f60b1040d0316150010b14140d80359070f1040b50a1505050350400c1507501d130011640545080e12480d51100940c450841d600d00300c1c044200d101d030b4000c101c98081c41c18851500b4030890f0004d0450030001d48040c1c209103c180780b0104488a21903414090000e200d0b40d41c2da001401760040c0c03040180c40302c0e00b90510380b041e19110700a041c1c940612415402c01c060f140080c0806045240300704003060020000708803079650f940f140b4540701c22a04002080d4200b0b100400c16450f0801c00303455419148240755040c4118820 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 851631205 1250 851629955 851629969
    0x3010302012115030311010614010c0314070812160201110a11030f070b010e150f040c030912171014060c10020307032c031c11030106180e06 62
    0x220070010003a41510300b5003100a181c1010b420024018155805107640382001065132001c0042002076521303003540402c0206c05400e9085491406854004031404a940c0c100d603001b0001d0701c2d8007030780c1009001040010702a140144210700d03006190b641c00c0e051090305850a5500030304a86c0540e031400064081d003034000c03020380e0342d0055281802038070041d500034024114803529a001d00440c0c00041d0200801c0701842d0110305076625084038200582d00c0f10f95403195185000708207a8402468800c4031000c2c9407a4110300c0702d8044929010503004045e550300030098032025248000301c1c488550240c4000100b203107240d40132804203d840d00440c602107020303a20712031013031026008420014142c0c0c4601c804002e6641c0201c0906421507492400c2500203004003009452003400030030f00781d91401013041c00c904103142c40184001075450034105400390b8a0700d461155070301034155142d50180c684101c02102840c000e10107170301c5082300100e000307520b441c0c0d005a0b80c01110f407a01500040c0805078403800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 851632455 1250 851631205 851631227
    0x3040c0303032f0a020c030312090613080304081c061401020c01180b034302030c0c01030203061206041a13080d0510030f0f12021203040206160f0b0910020301030201 73
    0x100b003055413503911160490034041c41c8a142d6400d440001498007075002d40740620391062480c00c042c0c402d6604d50f40850008454507100141041c0401d00219001c01d680000030916600064900b07150403a600c4104800d031000d13940002d140542e0341410780050b50f010700c081d5003166001d1820000d0b104c07580130000d80e16200380c01410f140e0704002c0000740c580c403d000107401425901c001e01e4442c02c120320844c0c1e40355076a0400140d1040300d0820440c9062400001518252a820740181581310510b400440c0207410041c0720030342c000441a82d040000303405010442c010390044021040c2190549080c510611010301011090f100d00345c030290214080c2c009842070404007113804a000d495281411340d000c525604080c1a030091199180c2c100301d40306840400031442800b04c01c600c000b0546061f030300c80202d00400c0e410a0b00c2040058018a0468010182007401e40711496242105850300c02185d082030500b103d80c0800c0a041c040e156008020610300002010000d43c0303103604503030000b0800081c0c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 851633705 1250 851632455 851632541
    0xe0d0903080403110a03150501030c1406160516230a0806040605070e150a080a0209031207060609050c031503072d0803220e150111010e0303040c030303 67
    0x40744e0046a00d5441c000030200840e080300170015030030781c0e26440304000c00c0c0a100440d40e43c9141d64002840003090308090300301072002882e13641003600f50003100c0c140c0d41c0455001c8071a0301960601309241c4000402040140480400042a1204039410058084600d00c500703031040c180c0030000c00644500142040d8069802640401e0b10345601c00b0513a811060a241a50701a00c0c8208048000b04c5800250182000954420b00c0544500d030180089214480090360160802e07940501d01c036400d0801041c2e902d2044000241542ea00e00c00d0400b1520f080d5140d000010700001417100c41641141d041590718021005042d03803d2400c10100801c0200a5007031180004030b04440c5110240ba004120041200300f0540381da41c2c00603203007001d10608004401421181c0c03a10302168410380c0c441c0b1248902420343d180c220b0311340050019950728081c1c110b01c5603a50340368403460040440c1032001e140a00e12800705c040d0740c10b040d842c02030141c1e00102c17000b02c0d40e200c45039418600800500004681d8002c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 851634955 1250 851633705 851633723
    0x806010e162d230d02161407030302061008100507120c0201051801050108030315130c08040c150206010b130801020304080409290108070e03100e0d0903080403 70
    0x501002580c00c0d181c04022158808802920010303040c0e45500c46500c0e02c010340e51030701d800003a0416000301c0c1d441e0320141c107500e0010a0101c0c03c0c105140b81c0c001c04480a96035511920244243c0d1130010306d00903501c8280f41e0b500044410020180c040200581192002424003030709820300808903668610303c82100c05003a00d03140030a40c024010300030040041801081800400300c01d130720190190105466100d144181002184401d01c0188103240c140c41c003001c0518695228950f07000c0c1c201003002d025503800144954004a000700700d2189c419000b038951601c0015103070a040c90001d10103658032450754041c0b94200c031506203602040e0310f03041d29952000c140e1145190b014054810001380c02200b990340c80041400144a01c03074006e0001c44010740001c0c060080f48901c05100748602c1281e28840110790034000b503ca60080a07035a6000c0810b18142d14000c046c1000245030120308010b107803040da42c0340d41205100106100c214403502c00350400000e52071859582040510492101503e4111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 851636205 1250 851634955 851634991
    0x60f09040b0d081602011707021509031c020d06081507080a021206133c0606020d0309151404030201061e3302071809080d090c080d020a0b010806010e 66
    0x2c0581e10351144050992400c0c00707e4503041c00040c0d81d031a0041003038950700300340a00140381c6480000441c2e00c01c82010410f00c07400c2c0055642e21010707410061485003080d031030350780214100c2d90030081c40003111600628aa400c2c05c00500180000310b002d032608041500400c94011050750380b0680c560440f43c10f0300e4928001000d882c2d0240148080084c403998000c0c0f40e500441015459450202c44450103500c02000e4805107203807070304540c0140319400240e040307000e0440c40b040c002da01000d0840d0080e00c1c550700300440010b41c00d003103c0400c60740101c4079404030706000505070f0911031103010b001507c8400e0030710440504544444500c074428000301f0042e843d07000901c0010310442d04402c030406e8424009a004050b030294031050b4501a2031744c11440c10091450440882c0500200e1580140450349820001d00f07000d00030302490346d030a03a2803404103100012090340c2004187c0b280c04045e4080c00ca50080da150881f00c5400c183c1c4011503e6012074010b022030f0f0310501da56a0424040b04c08502000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 851637455 1250 851636205 851636207
    0x15090b0901110c04050a0e07080f070e040f060903080106030b0925181202090f01061d01030e100605101722050d091406070f1103070302060f09040b0d08160201 70
    0x180301d140f8494000c3c1c10034040c08420542500085401002c540030380300301c26180e45482e6038400c407000402d009540514030411000d081c100038030350014003038415684215520340700d46050f90b07071a6500b140000d4410004000c250380c035100b59454801b04480300d0640e400d049062171419109022203050240d940e00c91244850f010b0f02403200c0000a2072080118142d940d04044c04008003128107034080d614413000a003941042d0202c80d41681c200740c0300e8072130f180351004419502c1c40300007c83d24181944ca030a404c092400c100005200c0d5a045900454000d04040c1448032122481c501602804001820410b0040036140d6850748040044805071f109134200c0d4406400a0110401130002c0c01050f0107600815440500003007a1950300950442d100507260a200280c0b16040d800b80400141e4440d180c0000d900d07000710780015800804440c6040c0d22600056081d500850340760300c2c4008006080362060900e4042c1500c09001155010215081901c03500c10328890148050780900030004180216 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 851638705 1250 851637455 851637463
    0x406090e06031641191a07031101050a050702190b04080306040209061611010c050312072c030d1b06020313150b0316050a090f0b0d0c15090b090111 65
    0x9036200c0c20348a505141307904100d4030540801441c0741c0640050002040c3c440c0b1081d0122040f201d440794040d00140f0b50100050941d00040d0046040181d002c0ba91b40103c2400d0041500034044900300203003600b00340002030f203001c1444520700440080b04a5141c04a40e00c00d00040e4004d03000000c540d540d64500002400034480d0301231302c0358046000700342e61002c0d00401c454924a82d00c110000c0009405450042d580780c0c0c01010300424903403003040703984402e085002090350080040c1c01d02d00d5000807043e00c20001d80b0a00c806001594182494204251600700000c002450050815081c03035220501401e503460742c03500001e001c2540001c042203c1f0000b8403900201150410b052601040f5509510005842e600101074400d01c91007000c000c080006840c0001103581c0100720399030031441d080506020701401b042030344005640d0011689542c641d002c00543ca18464202e4852840c00c04c1034001c00c082d55142907904003c1ca110060002c1c00803107040b41c0e00315409081c07465036030315442084d92170 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 851639955 1250 851638705 851638769
    0x70e19110d1103040c1d0105121518120c03031605070c06031b020607050313050a0b0a020c060f041e0204021605010b01030b09160e1201020406090e060316 68
    0x2445240c0780d81d002c0100341280255001e64422403410800c0c80d9a1552180e0821160381d9940c01140d0304030040009181801000d48062800e4040d00e849000c2c00d41e20103c0518211913044001e01072a1030000905022301c03003000103842803040c0d14208580301ca8080c0d501c3c0801000050000d4803681c00d8a0150b01990664520030f41c40740e02c6083e1aa151080100500083d40c000e1b8440010310842d04101800441d0107803080459944040c10340e5207071111005501c0c03801100b940c0741d006280f5048042607820700c00e1481400c0502001d030b5544640704031a0b1034400d004000c0d07042103913050305001c00181030854a00c1890a10312600451407160700002d0024418450f50400d14105901070504018040d08842c046440907281040445070760780c14008a11011203200108018901814048502903006d90b03525000140c083e04080c9032030700c24103089a00a400080106000e1070041009000c3c20200903030210f07050f40030703021060406803010300d00c2c07466015040d07400a039142901d182010b00950022 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 851641205 1250 851639955 851639977
    0x15191809110901030c05070f030e0d1703060f01081902030c0c1c03061d0c0307020c0312070b0106050a050d0b01110109150b0901080d0309030e12010e070e1911 70
    0x250240784060001c40e5118458490109040144000205020304165110309030807207641040c00510342c2e01103900180440450350322011090504021440440d01c020704030303d9525104c1e81d40d090100c10880c1c1170864281c103a04100040b001c1000003407107485580503000c2c0d5600c2c0540c40392241c81001c07036640107042004605104110250f0840380141da00354940a019440411a01e81c5800c841c0d1105108019101040d005034008902e480c2d200342d00440c0d1100c201d10542d4107424002000138103200440311110b65071000418244288030b0841451401401e46003011440c0544200028240b07005245104607010740c0c42040020f01d901810386181840d05d800000c1085500919025001103117468030100250716042d00e480081c1007503120641a0b402803c014010115014800c4014207803001c001c90030003510701c03102e00168482c100055035807000c0a0012030b9074080c03a802185012040d078044004075044501b84214404c6504031800680041ca1011a4410800038498040c1c41107020003c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 851642455 1250 851641205 851641211
    0xa05030313031527140c060913110708191e1d030717010513020102070506130905011d0a0902010f2a0c08060714030721050a0b15191809 60
    0x4070030495003443c0040703030f40d1040340800800c01c40c0c2170f000c0340d841c80055050b64000700308016680740e034545003544141420030542e000c1800341c01d400502c0f0090300001d4084440341c0c0007040d40d00a092002c0082c44032803045140620500d044882282c9000000110403014400000ba010700040e56400b41086400d90250403140d9460b51000a20403024072a8040c041039481d010104641071805104030b486690140d000f030104600704003c04c44540d0040702d4000c0d2401d5282c2e000118075900d4040c19000300140e1000d020710300032985000da0b45840041400c040c4600e001d211a0050703030006901039409002c0e14000d00c20f00340c641800807000030341c664001c050141c4240200d0030440c0320048501a10030800c103880085e15a444207540d803080034511804404030500000768030900c603400985010300004c0c55200e040c2c440b00e00c40e00448100390b813541c00782c0c0d490300054000d5003030640a90303014499a144035880c01c0e03081031684400c6640004904104420302d4000c2c2c9206080c0308500b405040c0b889410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 851643705 1250 851642455 851642501
    0x12090606080f0d02070806011a040801050a0f05090313030b09010e0616140a09030605102720090d02010507200117041e080f04140a050303130315 64
    0x8103545101c800000002c5100c0c085080f02c00620100c1d030901103d200000820307290742400c0d0041c41903541079029040b4101c0a200002d640e1500b405800d00442d880c0c0e80004a8040308024002a108020034400b12580100b201120103c141e60410f01280c0e0003d1101c01c02d61600c607082405840ca81c00380600c0c5205100a02c06140312040003a1840e111907241e0000005e0130500380701150140407450804690100c0c020408508240c000d103500c0201c0045802080d5115041a60bc0356a07910300b4003212102e0440140c1c40d411544188052555800081500100e00d00134500b494481c0e164200e0080d0001d0401c80d045900800555048a60045d5041d56252a01c481044074026a01415000407040b000c2e20800c582c00c01c080724062030308624481d8144024201003008107005030012251b02000b040f0b9001e2b03410303101c800341c009031080d0000c0840c0500080d0402425020a4004900c40c0e001080f40c2606c0d001d40b403010004807540107042549a011540300000281403540a60518040e4a103003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 851644955 1250 851643705 851643719
    0x7090617010510050904110d022e020c030a0f0512070b04050d050708030411010c080a0315090204050604151806050702010305090a03020c1333090b1012090606 70
    0xc91400c40415002005207aa400d0f801064000c0e40f0302c5242c5d00310078584003050101e500c2400424007014003030a0710500e900c2079408542c04c41d00c01610003400c2401101c2e0b035010244c1110710400b980b131030344c8020029002070400198481d614442c0c020400702003400010100041809660200e200e1f0701d81468403000e06092190452104807412200c83c0100c181030030515010300c05031030525800510032070030360742ca55403035400926008d24800e05009100e03140703a000401100003041103020540e40490820416154141e0101c01c5410944880340103010902580c0c9070841928211411036030255403040760080c050740c08051007c0320891181c100900890010b4006000700750081c0300fa6401c1105030b4509a10580f1456982c5000b00181c000b41c1c01d0700710742e280c04a03041d00303170850601c0d002480703080e03c8542095502d001803001381d45001040041034800c0d00810480d00910703880c50148a0100803800003100a4a5100101c09009913600c41e004800e0013544003243c0b41c1e5012400300280c5842d40307a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 851646205 1250 851644955 851644979
    0x15040c02070f03030203121e0f130b040302010617030301031208071e03050103020f06030405060447100e0601210c0206012c152409011d0d14070906 65
    0x110251a07054011f0115074030b07203885040300048491120f814120354031001b0b20500c0d002c40290440350b000365031048540200c0c0103d0708060241d403080e0000140c480c60042948500000c2c80d0520000d500306000420204100d49240600703502c8915042c1a10f40e6003a4096038199000b16180440c04040c0700101021078141c0d01c1181030300e0085039002481a080400c128080c0700c101c4d00146141c0000000c02c00061003440d00c86507003140642d02d24000c05042c48502c10381c03e40098032000c14100c0d018102e408801c0d1011458014840c42c00c10a019400c2c0341001c1c3e13038032401601c4141003104a42c001400c404040720300000040400d20280008211400c000399a01003c0c01480c000ea050300fa210115441246100f901412042c040c0d815565034445e6580780032100b040c40d182e04112880d144408110002c1c84803040201044403050b10340e001e07080010300c424030026004c01d4541400020800130b50364000f866401503840020005e071402a00e071254100740c01d55120109440c1406004038a84480071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 851647455 1250 851646205 851646217
    0x7030b01030515060409030e040e0111130321023712020d050415030504080705011503031214041203110408010c020f03180904080405180601020d0815040c02070f03030203 75
    0x310f03c20b00c903a220b220400040340c3c00b0300b0000b80421401402c2405c1c40c2000c2c9c200308119480c070400081d0024211801c200c4591000404145a88220b0000e20400c404221001885a007074101c6200309101000c010390303030750310308050854010b106207003010a00c1c40c004003284c400e201802d48180411414070344604a501b6144450f07026003e40740c9800d0520344500251802c03509524540c002c43c803510817065001709000b400507190080204a03a0b00400c40c00d010300400c0064403a4189030342c0d442c6007801001d0f4201c8411100c0441c0c00c4c44010a272240130045200d070401e170844041102000038103000d138001d101006080181180c0441d0000350341034198884d48491401d60213a940e80b051480c00030340c1300e220705009450302404158040714a41050b000c01031340705129455a0b443c0c15101c0000800785040280c01194501d00c84040050b25607051007000000c49041c03c0504582c00c0c800780b2001020414400036000315517551080078803e1003003003064001d001c0301d030b44008040d0302c0c2d040007907d07036000c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 851648705 1250 851647455 851647483
    0x3211209011e0c17040203121e04030b1906030503040b030c090a0608060a0b07050d0c0c170303190b090109112802011104060806043614010c1d010207030b010305 71
    0x181e504c880300c9280c0f40d10f001d20580e8001d002d000b00003010250440d0301d4208110601010346032458088001c1f010000900107140100d1a2000c0e6242c209012400c1580c0c0178079141407907040c80f9080001030000000c0d642614080e40c800e6440b540d40403024103480c05a000341c2c40d400a5a40c40004100d500894124010132058510400068075003200d40824805c035103006049034004102201c00341d1056940d03003949803160702c4e1007082c155130b1640d9040511399a04441c019400000500219080c0b9900c41d4281e529400402e20080640380c0004407240c005119210341c0796110101000304402c84411280030008141d00d00c05103070801002c046440000d4801d031000b640c80c02200050180b03034081031b03800b1112203941701c032020395078107050001030200c000581c00644101c81600c0f00c4a036185e0000d118000c3c4003607010b800c07940c0d00d09160400340702401c1c0792001a45010b0034400d10a5220000f05010401c8540342d03040b104201c80101e2803c500d80d400a403c2da150b090010007041b034042480310340c074205 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 851649955 1250 851648705 851648717
    0xf0a08160f06140c2106010e060d0605010305070c050c0f1207060903060e06010e010b09010309060606050306030c060301060c030806030a02040c0527010c020d1a1503211209011e0c 79
    0x201d9813041c00a04c1030400058a0700c03941d500d5004004484c040e0964400018544074034030503105c03004609250481010603820a45072001800b035541c0c14450141d0004051804441c21403154985607121034a10408030f0007003158185ca000345450f6045001c84500344001150641d17541d0b02e2006202c0010b81c08104c81180c1000801504407000040e103034142d90b00350144c0c0c0156403810300c8d582c100303901080519040c5a1a200c00f5004158113103e010000c2c2a16110940e071303494804205810034402c540074070b00c00c8405000500541e80e00149102c02c4c40d5150a001c81540c07195000640303090f2020000a52243c2002a21603031194040040c001007648441607113a5005000ba1101ca807018503165980002d079810301d2000075240c0881041c1c101070050130b07240c0d1104204045030121b40300498241944000c0b04100c5400c9003000c10020620428203150000c1a19208000d032000e0b204030030107007020f5000317070300818035160b030a51200074a41036141381095001042c10050003d0000e40790040c1c08038070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 851651205 1250 851649955 851649961
    0x50a0815100e0a09050408160f0f060b0f0904030203040909050a05010c0c140705010503070c1a040c060f0908190305040902030a0603020907021c110a0b0123030f0a08160f0614 77
    0x8135134041e940c01941d0200e40d41d41401030500b400760306881c543e181601d00c8102c200107500072862005500c131215014000c0482d05075002c0d810310440b0400506040d0181006c8000c22000c2036002c420348003942d0020601059910490600e186007601320f440180c0594648882c1d00f41481c0c00040c085c14280c030410b00c401908888078405511005284922030200390b0420018248521601d00c812006100d945080900741d906002c1c0c2018010890302120304800341103052041d40d401c9514070340d0009080c980b02c400e0300e040c00030385603c071807126107000000d0010036107980c201405101600e000c0d088201086480345024110900940910b10059009000c0a030226110f01e101003101144140c3e90690101e0b0f0400c404000c80702c80e40d41c40e060350780900911304010005900311140e41d009010081c101d03415116848403040c1441d070400996803003a409030100c88000b800124650010503004041e55841e05540070842d0341c420f80c6100024190764092010604200155100d100c3c0d042d04090700103440d40d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 851652455 1250 851651205 851651219
    0xf01140d20120d050406030203060a0905040c170c0102120901111204030c24080a06090e0f1009050607080a0b04091a0a020f16060e0105090a03030c0c0201050a0815100e0a 75
    0x6918003211001a40410086c00406c1c029001950020800303803145007410354480044c1301712041136400b03e484000e038900400c9410b8030b840440141d0103640003d020500308180c0081d42d1200103a120001064010070542d003182e0064520036212680744c800d41c0c49a0a1a0102440d19402800200c914090f01074000c6000400610313403070b504240c0b5600501c01e4451281d000e4808450060003d0602ca858480110f00207245002d1f00c100e042c5c1d01d000509225024108a5007008030940b0b40c400c030980303814031400104600146d5181c01507010300788207500e51141c45501000e401e0001100c0d41140c1003030444020049a100303540443c803848008050b690300d1b54410181a84030f811190000782c007091018082a0803450032a0260b03a105030400503c803d00b000c0c0c06400e40d80211002c217101c3e04010f50450602d0f801d4024039421612034039121014008650020b022401081da0603000c10140b5070000d2036070310741d40113660b007000c02c010492103004d62240303001801d01074200e0006014100d5040009051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 851653705 1250 851652455 851652463
    0x40821030c0a08060301060b2d0f070b070908060403050309011d0c040b0301181113050609071124090d092102031011031803030f01140d2012 62
    0x9084403428081c900b1220040403648600090300b0544d041d540c50b100040d990030b10f04028181c03404139580c13030288002c00d1550030407094140307040c3c40e0100074200080421180031a0480d02016403007002d95200c3d8541003c100d50340c0c1c486e50000710051044400380000c3c1030700300014600c1100700c04002c0c0702c90200e04610002c2e010f10703400c02c40352a51001207404154a442d822004007440080c0c00018080c0314241840d112200011060324070301541a294013150400300400e55150304000400c0c0310f01e040c0742020950181c0d00800b03c000b001381c0d950038000c4009051101110806125110b400745055021480c1d404100680c4c40300c189206007540380c035440d80504002ca0460f030340e0141c0000e81800344d1009a44020310f2207000c9030b06000711000800c44c0d0040d445088102010000044d40fa49000316081a04144d01a980c1166038001d008101d001042101d075581555040380300c01c9003c00e8088003003250000c442a00400a079442c24495840b815028036520202000301d8403601d26400c107030045070315 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 851654955 1250 851653705 851653711
    0x203070203280e240301180e070b1608090d2301060302090c070302030f0a180509131202072117040e010308030c090411130509061311090604082103 65
    0x22500143d8054241e00e4042c44074018004002000f640c00b410b40d800003c03075948240c0107041c0f90880b1404682c89038005100e1120000811f01c01400c1c2c0741c0c100544a04c0c03d00800b81c810507040031000c0440f04000075241983d01400300030b480030f0659201807504c1c0c45480490035803080324000c0745010904042050141004032174000d8401d005607200c11401d0000f03a40801d10039000c0d4401003002c2400000342400030460350115540d4480070b48804003100320021865070000340b01c2e420400500c107404001c003c405000d80c0d0300c10b0302015400f0b0104416410a103c6620003281212025442c01ca00fa5015002d0026144982610005824000c031458914003c900600d40b0362490b030070042c00016070382c034000c680140e081d010a608000412001038255400c0908660b148103010581c84901401032450b00c4c003030141100c1c2c5550b1340c0752030004a580758441d400900085c2d030f103800416960f80c4200040362003d2001500c03403650340d91580201561682900c640003000320750202c02e02c184544a000ba00c1c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 851656205 1250 851654955 851654957
    0x5181605010509031c020a061b050409020901121a030f060403020c0d17040f0e07030915020a0302070605040602030f0a050c0a0f0e030604030807020f0703050c0402070804030501020307020328 84
    0x246800d04004480302e0704000861a0584102d200c1e95800c0802c0e042100744100e49903000b4140a803e5107003074030071340d0840545107900d03031009000007448641260a542c15030340c9009006886209210040b0346084c080700c1805a030b43c0c902600000004443c81585407100e0b0142d007251415034500030004d982c2c22003100c0140068001004000e070524040d800c508100340698605031412454007100c04030383d80f041d0300c1000a41d00510042194032006c0b400242d112016040170002c2c0f031666200d154200781a02d540f45a000d9000030b207015254081d50640d00183d411100810252500d032909000940c0159944442484040000780340c10b105405803a01c06e500b0200a5801e0200340c4006603121442402001c2c02c1c4180307070490221544040100364400d40c041e80d681e043c2070800040c00703401c05050720001412900110400e10100b48000f0342c083c9860010b80c3c0050b522002401c0401413800f8a0b000145154000002d100c41a540000601145480070f0450400400f1082c1504040e07406100014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 851657455 1250 851656205 851656243
    0x8010213170d0c170a0206151c03051309051008010506101e030e0a0302060103060606050403050717160f0f050a0e070e04150906081204081c0519030518 67
    0x75421038410f00501c3d90451044a8680385003800090040c0140c110388289801a4080c5003080608501842e124221100948400700303001c500c408940202c907801c11025061000c006050102c0c0c094000341607008201128042009080941c0c2008900b0b405224401056091a01203405403a240c0207181481c09903417503490300e00d40a0501031140711500d0780303e03600703041d035a0a1820284c0c00034401c4407070180c03207940940b07955070451500170222040764014204228040c401400024000542c2c201540c0071100c00030381480c0001c800038500782c01805401000382078400001441d5203035100040540d00f4a1030304040003500d45086c82003612091003406081904800814807960080591300c0c00c914002c0c001140d290240304044001c00b0b141d82c0300300c0c50321366680000c00003a0005e014000204d101746400781e1405141c410b2955403210243e8072444002042c400c4240158040e01c11039004081a410010000d0510031300900201003c80780d111540228081d05d55011401150610220815042176 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 851658705 1250 851657455 851657473
    0xc0318031a010819060f1803030e1516080a060b220e0408070f05010906060b07150c09051e13020d0b01020a02060a0e040e01020c0a03271202190801021317 68
    0x4a0142c1b0480c645a01c080340d0320303556203c1450801001580282c026200866601d03441080249090340314882d8807a2078a47d00203000520310250146030300d0740f81c00c0c0703050300b141e45030035030f10f000100b2869018405003a40020074204043c1141c0424845280061140028513529944446025021039009003580e104105500000d10001c46098202d8010700001a00d003180341c2d2104111686a000380404040100f0020204106540c05595102c1707000001e109200c100f440150010b80c075405007501c1440e4590300c00281e40606071000e000600000c00085240840c004107100a500502d4000c0c090380c1001c800d000c0303d500008071382e01000c1e03000e0131a900d0002080400c42d01d820b031404104d90701584900d007000c4608024000741a80c4c8030080081c0100d20268500945176614070f007070400b5031480f031500759107100142114500442e95102507202406185200080700300c40c001801c500102c58071400272802140540c01351182c000c05225070020a0344801440015840d816a2010182d00480b06 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 851659955 1250 851658705 851658713
    0x605031510061427040f06170a0206030a050c0d1406010e01020a120e0d0c031b06080c0412031b1103190c180902090108010b0910080c010c0318031a010819 68
    0x3c6607a1a000e804101013030f01500040541d4882c02142c0342d5640c607030005010b504030380c2000810b041d01c0d01c0014080c00c0c14560208546010040000c0d04055640d00040c400003112804c4818010702607a00b00609001c0100c0003207908419a811400512410550801940001000402c080d003050095034100c00e141c8086848548504086401c402580030760400601c82000c1c0501a51080440510141d103180300d4000320704c1650700450801006205000d01038a0010480e0143c03444405140c0c6c2184a50501383c8204944a090a0b041c91140302150203201008486038075160003201078a403280700400107507241100c006809000b0754003da4003044209a18100146c00404150002c90100d08940009803044d009910916461751964100c00d07035442d000c070169900c120040e01e4400024109103800d80c0d42c0c01540c403030030305009581405006041c000e030403441036010003a844000082c1ca9103003000c460340308c2e100d4650f2030800c1c540001c215410081a11120700d10324494205240400d074035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 851661205 1250 851659955 851659987
    0x3062805010b120a110a0504031b0b040603020f0f0304150c020d1706120703150b03031921051603050603030306011e0c08030f061905100c020406050315100614 70
    0x40004e0740d68054004448034024050a448151512541e84407407845c10041c54031103c260700624a256411010b00000b10b1280c1920182d40c100c0c500181c4030101c1d40c2c0140c416104400c1d1041d400d40d0040100402c011901e058806080b1125a013071000706134211081e0b0b91801e00b5074844012644840c90071800c1d200d86040280d105030000c0c5402e4107416490a12030610b0f4043d081a2110785d01003c004c114003c03103000e054121203050b0011440c11124004070624540400340140c10000c450380c1c4002480140c864628401e00c043d03c00b00300e181010302c2d5480c002e160728498100407900b0301e00006d0760345c900801540c0c802ca6040e16001443d01d400060405400d0b02e551011050003c10b0480102281c074401c041d512441842000c0c0f88141000d500b0418440c02030301c0754034a044031650050109031110000720000d5112410103c25130300041c4002000740903d908401d8040c455000d00b003194001500d074050042ca00c0b40c1030a810341e078448404458000c0c0f049000034035014100016001c40982c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 851662455 1250 851661205 851661211
    0xd11180c0322080a030b0108100812090d060c110106120b07050c1e0619020c10320105040506030303040b011203050c0610030c06020c010e04090201020c03062805010b12 74
    0x1c0100c41102c072040d40d4028103904003c6141e07001070b035245001e00300380d43c000000c19081040701d290724a0301131804600656030426407240d074410b10b10210703080c0350316100c2e444407a80440e846182404040d003085801400a811103d0100c820f40c2080c0000031546040004a410b41c0c0e00050b04c070f1407035a280314055035a90b1115400da4810f2041a0f8a9244401007059103c481528000502003a0414081c00c02d002c5180d1f80c503080c640d5204000540161400140d40c8041008800011924a2400a00700360181400d554111b428006c41ea00001c40144651914161041154108600c0c0c0701c0034285650782c08116001001c080b080701c014851954203d00440c00301d48246030140c40c110503801404d061250076680400c041d90000700c03e00c100003a800055001d4041132008000074450040000c0403030b00402d00550059680d00002419179100f44000c100c4a04c1c0942200c103e420513103200714407800400500200312400c041c140781c0c07148442c0078107412202800c00140c100710407901040e114100103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 851663705 1250 851662455 851662501
    0x4020d170d3804090c03021f02070614090f0604090f1413080f030a0f090503030f060303180f130219121a0f0f040f0b091807030f030e0d11180c03 64
    0x103031780300000603558210002245104950801d0040680d10006407605005070840000d101c21719950409a940302ca050310b203c00e00403102045200740c600080780f028484e541106107001c1c10030f072841d400d490040e00310302051141d00c02e001075540d4400c26890344040401c0c0c802802544100144540184042c02454200804280010f5000c500004044c21204440c4048136103800100030440181c41c00c404c02d6030300140540155140030a0420380c0b2000c0950b4030103143c032074140940c8842d243d4841c3c1002001c01060143c00f1517413456007151200b402c034041d910a1002640b190034024800c0e513a401010b140030320b000d041c4d100f107254500402003260700324507843da001415092258101d0f40c60f40175510210703c40c03083c00198403100509001d407009004091141c1d102070010444d0344070000044620480390804a0401c285503640b800315810070a800119030700580d84070010040c01409580203420400450f4280d6402655180c0080c48401c200c4a5082c10360081c0001980c0c981064000c0f0150062 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 851664955 1250 851663705 851663723
    0x80702030f0a080901051e13060b060703020c09011d181603031d0625080712051b061510090e010b03010807051804020d170d380409 58
    0x800c49451140d000401d09000098161080c81100d15080c824150080a49081c50128411781f41140721040340161011001190103000300f828401e06600c46149031500a200130b5803003d40d410000d58840b1181e00251203844400c0000840f801000c10001c90020302c10b20410103560b9905002c0082c54030f044c580c1d0b625001c0c80c0040d003840c1241c0242070340a18481e803a500741400182d110f21608004558055008550400a041001160100030710901c0460000c103d1107503280c2c600404035004141005140411141c1000e68494000c005000482400e000c68624059442d50316035440700240c0f04a4150340e847c1c00f121101d42004a1498681c2d1182d041501345d4035903580e039038070360200240e0000c0b40a0002000600100c0d50900c00000207100844443c1c40e0325008001d020909071000e0170007072185864603400390422541242c404654901c0b100c6241e110880c031001b6001901381c00e80c02034106068425429010f00c00003051424000301d008110280000e094180402854580020b8460700c1c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 851666205 1250 851664955 851664967
    0xc0b0703090c0510080a1805030f300405010506010e0f240a121d060a020c07050d03020f070602060c1204110913031701060e041508033402010f08070203 67
    0x40d96503400800e1485541e440c603280c07404113805012100c1c0c0f0003080107c08115080d0401284002095030881c0036134219031503555070b02107031588480c0b038161402041030304404405004020b01c842c07020721640c099002403143c3da441000440380e0514807140c041d803290504030945454140346810714910b034402045c4411581c041d403e900000e8000e0346a44000490002c48004a0907140c042c00c22140d0440d00070304a041d01107540c46032110002441c0360841d0740d000c60b24220070b038020881c03800100710280450403032140605000f9150f0340b800c100d00c64184190320f00002d403240700042a13813040c0b04520f5800e06003040c11502c040c04800240c81a00c825580e40b001300502c1e036811054500520b031804400090008a140c06010303c42000b8200c0c00b649a08401000115045402040000000c840004041c9014201c031142540b064010344010b00c40031031a4601c440011070a524004040384081140030100d5410701d84052864500a00190960380c03040001d902841031290041803600581341829 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 851667455 1250 851666205 851666209
    0x240f0601020127050c0a03081b0307120903110a0608060f121902090708071b0501020d06060e041805031209070b0a05040f0519050f030325050106060c0b0703090c05 72
    0x401c0d182c00f2032100441c01103c804200080002c500030301800d880c007055091643d00e0710030813401144031100e6604013009807042c10010078411200c4559100100e065010100781d0000c200c0542400221940000d1151798000380c070304440c0b86000c0342d410303030303960010b655411051005190b07404280540140c4030405051080b44180f00ca4034a1241400e80100407400074010002200b0f4090194414000800207001906030f10503410100308126032091080207006207000c600a101d0800c0500980d49003d001107480780e40305951400c1007204980501054030100404984d40545071001001603004200b68034001e02102465a40b0104c030806030745009607180d400004940c001c0700000001200003405008140c220803041c1c0c09004183d8a0f401d503c110303604054150009801481d21a290980300038107283d404000302e402814100c80705885c20301c03004141049200b4a0720f02240c1075400c0c4080400c4481c80750001e000c407107030030402d54401500c950340203400411503003009840010000c1c802040c15 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 851668705 1250 851667455 851667491
    0x50c0c100909140a05060a14241b0111040803250f050a0203101b110f031303140d090902070201120218010917070b09060d060806040302240f06010201 66
    0x103003070100c0f0001403820034424030032290000c24191145428190500a80380c8c0019a2061040140c84250b00d140c082c4080081040c01014580708802001450300c50341c80e0a5a40c4d542e16904042c002e00616041002c04c210740d010700d01a00b03a03942d00c00e20100c241500c42c100b000078110913808032602081110f444510b0a0150440103a405070300c461021002c60904101046490450705410003001080d0085681000000346206080028503c401000c440c801d02c0041c10000e008000c0b20750b6071808140c040d100c400140b2040d503c08181e10207180300c0786004502c0380c05280385656418000b86c10030300c04000075000400140e04118007003000000303142e250f03c01854040044010100c081d002a40018440449500880b0602c1c20510b540f4081308800074484040d0740125041c40e440c0e0b0500d9010403000d0280784200c1207101c0c140040080c003241d010584500450080d0f0a48000041140403e8000d0340c41c505c4081c603096400d00002c40c05024100107a0b00400140300100d04050b6030b090302c50070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 851669955 1250 851668705 851668721
    0x180409060501120c0504050402013516110102040e04033509061302010203030c0d090206030708100b0c1915090c05041802031e3a050c0c100909 63
    0x16030a0b00f1107004040c070030060503103401404120b4040c4160715059000030091a8110450851200c600c104004540503510000d2406201c07d000301c505454011024114544400082e0003c51507010500070b002d1810300844c3c0907201d41c50588105038540341c5d011122640c41e91440e0840c48034903400715480807940f46910003140134114815050741400580c0604041025044500086190001400603600801a40d601000d4a60626100ca80343c100c1c000c060114150025880400082080074654100f50081c1c01000c034480d0060f850b5032240b14640c290310801743c0c5e4130169401441c4180b1000011002d902040348240da0b404518411840000c05480461804642c200180c4c00240703d00c0c10184140101d00f00302c1c2c01d2159290200d90040303a1078040617421a00410138841d1035a181040421140814454081340d5a40a0056110509142c0300300c150012402401041154910384503c0550761840b012070041e0a41219040c1004140303180c40282d40c0030302120041c00a000034542c441c00389 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 851671205 1250 851669955 851669969
    0x3040c0b07080c1c1d031f0e01020d020a0e1009030204050411030109150e2407020c1201020403020108151003051f060201020c0606040e060408031906140112060803180409060501 78
    0x10740741e807940c5809401d0390250100041070101a090106080e6000102000b0080c1500b0001a400c07447c2c030701480142034825001080c03907000203500c100415aa1b402415040703225900c03c500318000320300b003203c0c407942c80c07100900207202020280054586603010541040c400c40b110400d8090100c042800e540c102070041c3c907040d01965509182810724007854040c4484c000103412082011099401e240c4100f50101c50515170302c1001401c594003c024161844c00c0082203565441e034003c444038040d42c00350008034000362040020601e01d2564100c190695030740141a240f00c5909510200c0c01400014110200790301103d042c1c80811014400290180020743c2c009607444035580c2c900c51804a0140101d400307240b905c10111291100481c0003034015901064440c2c0c1e986651801e40710200e0320f40c0d481c2641c0c51801400103a100040c90034441807520a0b220004010f8170182000c04032082813240d115240c02c00c108843c102e4001e4268144203110040c4009884900340d102c00c4101c40302600140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 851672455 1250 851671205 851671243
    0x180c1e02070515070209010b0a0c0303020714070f03060b04060e1f0512070609120f151e060314010c020d0c030c08031609081b04090212060a05160503040c0b07080c 72
    0x1005e50500c0205103002d4000740b90103c1c40d180c01144000c1c1a101e002901908056012038002e04000710040c2c04490310054100704c45141f07031101000b000c1205684011038140e0310348150030a1900b0140100e904840e074251103000c40d070b0b540c401001701d070038848180700403000100d000c00b040e0740c0d44e0010b0251032240c4060040540c5230400401825064254020288200010441d680054952640d0300b030655880400745007a008600482400760412116074548000d4806a01c50b120042da409041101c0c01040000c0800d19440c003207a080b2040300e82d8401c01a001075800d1041c1500615031070b031f00240309141a48101065481d0340e0820f80058602c0c0c50340f0381c034401514943c1d661051049014040d13050191401c00022001e49a40c0f00205e000341d8003441d141e61011065603103031002c1041c00301403c41614698034281c074070300e070060200b00c9031004590500704020207050f2180c1d0580f44030360f51060b06400c0312420045d58002c5034105400485510004100d400c0c0ea80701e042c01085c001c902650405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 851673705 1250 851672455 851672467
    0x50109030806270105010c0510020f07060506011b06020c0304180507030608070b030f060d050f010b01180302090a0506120d09030c30032007180c1e02070515 69
    0x80008410758200d52002c03603c6141c107101c3c2c04000705046044070b0742400e00c82c94082c010b14006090040d0304c0d14001c5039620110300a02c440390401d00406000384506010005696008015119985000030f4602000a40010381c000a50198005e22480540c6d204032806c041c0c0c2d0b07203070864101000420508129440340c05000714150907001c7c800180000002500c0a0307070601002201a000040149481d10000e402003822074070350300700480300603402209071809000c681d0a15406040c05540301800144490000700c140c00d107816012041e640e00420020361515220304200c09410007504a59000108a50a4055441c00c02c8100c0e42000a03465001d8a540f55080907c00100d4651103004107c0b04100740d0182050450032142034050315042001002100c0c0c1800c4810352011a11140c8000d400e041c88140128005a107808403a40c080150f08008412402c050640741102c146002064201c181800c0d007110050206442d041588111103a40760b40f00001340c0054460304051060b1a80015a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 851674955 1250 851673705 851673709
    0x60506160b0105010f0c11010e0d030804031d0312250b0a0501120807030809070306020a0e091e07050307171e0a150611160e01050316060c060216050109030806 70
    0x200c03401807000b42017001039840081c00107001d40031079010080007200c68204103407a5a02803599241c1010000e02255004a0342e854043c01d10301c0309480a401281c04140c200c0e118510351010700d0a404006400b03000e00b60740c1b070b07403110016411070390612404c0040c0454590b1180e2000041c0264113016811041c2c0c01c2c20b024244504840060700500b5400c1e071034240000101d40d4141c202c861155045c50441015500c0b090b0303160410b110b5400050030341d03000054000c661076004d6111020418121001c6000d6129014200903e400c041804c03244040004001803000340160003a650140a50a02c1100f5691407892522004000c4807903000240e00c507044903070b9210560307228a5201101902c1081460403001d0b400110607a18400c002c1008a070703460611038100f060117414141c0ca4a0708281072038076128580c010050409000d09030003445a004a44c14240078043c040c002c1710059110480d01c1022519007034003961100c644070ba681601000740e0000101c0901c25444070300e000380d42c0c1b18030703604003041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 851676205 1250 851674955 851674973
    0xc0901090807060e061b0f072c15060c0718180f0b0a0f02071103060603070308030f0403030207200906180f040c051f1403131506050616 60
    0x101e203001d540000d00900034a5085543c841c0840805c4030003544802a02400d6240b418980c1295201c9000315070b02410103030300c00600d80e4207a42c1419034080c070070400e980c1035480d00c2c00c45040b0300380c040f490071021034514155030b4030300d054014029242038600501e569080d403030488a90700c50080d2005680b1512003020461140b40341891040217503890f140e06603110144505e03101000079000043c0c042c0400c1c0c610034641c4c420b950f0f01c04143d500b9903d4200d681084c54003e8400c8241d1802405050000b84e02c910b004a000302c10740340d200c0c04413403c68844010717112106600810440038075501b0030406020075a81260000032080007007040c860107540000380654581e0252003113020352501c082d54804121166a1242e1120205403603460542d00e074206102c009045511150700201005080405e55050003811400d40f02d41e41c0b0b42c41085d504485d008005480220360030269003294420010008500c80b41030300300040f14000101e45603888600180466010403103c09035131492400704010045529 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 851677455 1250 851676205 851676209
    0x50106051807082d0a021303140d14030106080603150a050a0b01030606020a060f06030c0305100e0d090b1b01020a050a090e090a15020c0601090b040e16090c0e06030c090109 76
    0x1c8103c1d5100108000d000010310019aa005100194001580c5d28105034107540100c80101e07144c0c1c1c9080c0d82c07400c20036804110116881224000d10208071035072800348030701e16070010300d5070321017440e5a113030420869170094064160350385030051304410510204100340b070754050020000f000a450406d2041c0c48200c82c040402c803410b040c00c2c0802000420380201d050314400340c000d07001054400d10706030703e0390080c0099040104888440c038008001d00c840000c0095030322141e10410001503400080782c42d5521034407280340c40040c3702440c082c0420307148000508180210881003080c4040b880c1401400d80e0441940c1000044000c01c210444d154807000c14030003000404001001810b00941044d10362410040140a14401c001c03000c04080c1d0760f40c1120f005281c003400355401355031181a0034010700106080c246c456410950203511110780480c184e46c2c0c0c41c0204c05200c00c880d2410104802409440b00e04030709000c048014086143c8441d0015440b6002c115501c3e81c0c0c6a0b9010005000c0221036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 851678705 1250 851677455 851677471
    0xd05010e060d02101116031202070b04140f01031b0e2d010c0201120504080315061603120b04151d011401141603030b090a090305090d05010605180708 66
    0x10b1488401507280c10b1040d0f41207080740d2070141002c881c1c00201d01c2c9001c0a41e00c04038210191043d00101380201d45c580d140c3d24078001d6080d1801d1039980c0341105194002e03406a04a400e00c4940d10210743d1804200d034081c004010305001c140e03003004d4854208120418624003003c80d001c004a00e56901c1e00c02c0ca000c06201d0111003040e0707860f440c2d028983c0d091518042440c1408001d442840c00d41e805035030481e002101c0140240103034030303140c41c00c0714480d00150f42c0c0c1d404200e0698814003052500c041a2030051500c0d107404a0080301c0c9880440b01d1840414103140c1080d40d0700301506868613540141031002603081d43c005859440c288148110400040b5036031003004c00303c00103020000d000b8054941050b02440c10b00a0f000388018174600c10300c968007440310010072032550700041503015045450a100b0840c2c2c441030070b0b40c542400b0000c0e1048a800103000400800440e6450728259521503400c1d0b000340c0000400ba032300c500c08191090019501c5401ca51040010003501960001e4899030103095 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 851679955 1250 851678705 851678719
    0xb04020f0411120c0c0303090c041a1f03020c0102070507170109200a0e1305100c1b0501180503130501031e020c01110d0b0f090601090e0a110d05010e06 67
    0x148040e402050f02801d80d03c20042c406200c04108482028001d44a14401e4581940d03583c0c2094200c041e960050b032001107000d2410311200003001040014550070007000a024890703070402c44170301b51010b000c1148881082c10707428020282400030920240c0502482200103021142c01c00382c141140380154500c450580c0c0c10200c010001650070b108040062043c3e101c207064054011700007400c403d10766041454042614400c0007000c1c100c0900c2c50200d02d020b031041e55103c0000308204010784080e000c07040c01049151903603040981001400f01c55003401303403000041540041402c03410000942006071800e600209007c030381502e103d41d10350300400e17003424204440c6039076024041780c82079040342440c0310315808120000109800c1d00145a0380d00d440b940165079400800420005004c0c0445d12401064180c03683c0720036040034420140203e5050b124071110a180c503a104005080040449800540300e01d020007003000b42801400d001e0381c264401040329070501c1c449a4a6102c000c0c411441002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 851681205 1250 851679955 851679971
    0x1030b040b030a020909010f0f1e140105060f190806010801080a0209060d0501020702030a030521010f030807020613181a0108070f091809050616020705040b15070b04020f04 76
    0x140008021440d643d06403248003086c1d544100c00750040001c081d10441d240e0a081c000c100c40c40a680c400210a441030740c11406004454681004440000d0400034170400320500510581c41c001016140540b54840168908400c1110081118680401344000301c3c803600d092104079a00f00c1210341c050101c1400400c41e60126800180c210346010342441e0140404050381000d104003034044072604d0760080e003124041500303450000c0c5641e00c000b0702d03580c00071039a0401c8410340b2003054036a4104d400304103e2a019a00711745400d166648425800ca034051070410448801c940f81d800d60400800000400c50b4290320009070440c2628001450320541c0d400e800d402072400c1c0e8000041c01d4000b401c5280201e051104034000b503904480c20f0b044100c4610b44205d588101024a801c086160343c4541c00340d0b02e0035203c02030501d1030b000ca40340c1c8070009604202c109224074280b5a00c035036100c41006060000003900c810380280e507940100c030309840c07101b2410204421340c00d04440b1600451015a0b040003c0300d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 851682455 1250 851681205 851681209
    0x100e0d1e05030d200f040e0a02270f18041118070f09090606170405031b03070203010b030a020a1a09040509010c0e030303130b0c07051204090621032f07030201030b040b 74
    0x1c81a4003c442000f169a0003042c460031003981620b4149074480900c07c00031201c2da240803a448560500188110950bc2c587c54003824000c400c0c1c111071001180031045503c40d582c0f19030300700c500c001e440b58001c00b542018030150724030b40b48114010581901d80d050b000302842001411400d060300088185803e0010400083d0380c000b00300c003520030510783d41c000c1c2c545a03450200c0c114440c0c1d41000c01c22102c8980321801408001c00186940d9100307c0080006001c00f00a040e1203c0d0b002502940c0200764030fa00b0009c1c02c41c1c0d08003520380170701c10b8148d4500d0001d0603000242110f10607a1302000b903030b664441d16440d09801000c0b8000c0754000314000d40c20b40c5495010f19805000d102c038010516001070b40803e22805606065411483c0d0000030b840c0244503840c1c0c88112900144a26084541040c40c0000e82c2e2100c242814001c0b907070b00c0c45211003440e8035201a0780c0406107490aa00c0c9801610100340d82509a042c0900403a95400107444140c0c503600004040d82c0c42004a54442c034608060b8200ba9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 851683705 1250 851682455 851682457
    0x12080a091505060409050f03090a080d0e01050d06081209040e070e07030b0105211b04180b0f130c03060b03010f03060509150405030405100e0d1e05030d200f 69
    0x10001c04007002c1500e9030b40c000494060310101e03100825078891402120741503040807014140005003607803c00c12083d03450040c1c0755500c01900040c40451212a20045e0b954400c00003401400f4510001141240d0344070020761810348103900440c80650b0200e000e0343c2500c0d090089040c0051404000e120b4103050071b9058851400151010090655504a582d001c0c3d00510070f4410756400602035220300031604141c40c0169400f141c1e100421095401045035200c0500c0076203042e240780803103e00230115400060340003000c44540965002e040c1100c0700881d655450322026018010140105414441d0034000d41500c006070802c11100000b400148400f00442c1a14005c498000501090302c1d115203a00e28103050800d8032214612406a082100f4490000020b104540080c0d509501c8005210b034103d80950124007459404000000d89402154400c00940c92a8500602e08204200c21380d494501d5948003c4031840c44648441048944c10307a8500c20040d003640d42c0a0070b070300e440003015601301c031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 851684955 1250 851683705 851683733
    0x302040e250f171003020f0d05030319020d0c18050d052d0a1202071d0f06061b0106031a0702030f0d1803210e0d0c110a0312080a09 58
    0x20018900482e15100b0b2003401d020031040d200410442c214200941490001295030006a000d01c01e4190303040351600384003000007005c540080140d800d64030382e003d5440380c02c07040c45256014540c09208403103103001c49204006201c401d58032000300211032281c010080040907400140709040b59a2180085100818104158454400c00c1c0c1d00484c00c024005600c0ba44c0e4080c100c030144606c3c500f410803c80107040710b0b4800001c0f90215a0010355400c584081c06000711904903002d458900417070711204d9103405071900302e42d00400d204e0511200300040e160282c80000240040d80d150003080060103a1101180000f0136207050002d607910b48180301954a10070f849c0d649400c520700103407852200b43c050344401404031a203940384180e0002070a000707041034a1559803940721101a01c0348129080107120b49812524100f01800750888014030a5a8102c8807540a07200314071441c15044580d07884031816005940300750000f6000e8120341c84000c050441c014034140b5050314004010020813502004005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 851686205 1250 851684955 851684957
    0x8010b030a08090d0b070c1703010b160c180f0509061e0a0e0727091203020903190c081b030a0605070509030601032402091503060d120302040e25 64
    0x250310f03010301021548030011400301034020801041071002040c2c1c013118160819010701a40c44c650209440d125078584400e02c84d0b403584541c100a061802101280049a02401880d0100b00559100c2040510032880c0c0300c03c66000e61303035071044488284a40714041c1c22501c040300820b0305182101030a14440c42e004240e440c2c216080ac00581000e02d143c100c4070549601209171015903903100010400089420f403265242d0405c0c1090382030841031403241a417002e8000034011108035203854160000d5100c12050783d0140034090880e1140b400000380c00000070304c1107000704a4545002e00030790030700070341d000d490341c0507004841c221103c0e607000140c040c2c045070045400211501d640c0e2040d00d1911440365040c0e003500414000005200005050082100200901c3c90020f2104210301d822840345500c05a840005124100906c24400e009950b201a001c2c03c04102144070303480d1152050b480d00381020009030002000c0c0694040d08a075103400504c41402c3d0184105540750031024426040003c6c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 851687455 1250 851686205 851686207
    0x60305120724050601110a0201080115030b0a080714030304030c180b100c06060501022b0201150b04090b0d020f10020c060438030a0504030c060e0303070908010b030a08 74
    0x180030701400c0d5410403904002c00d060001480d2528620300094070b000c0361042d000c581c000075502200b80700440c044410580c140d503505116803e0043e1214608004030030300b0704140daa01a040480d40b16004004050140c11004014942c68070b07403010881c26010413140e0094006010810000740d0b01c000040c11790b14000c8000c2000404050000010302c810301620368030000003807021000c1070300085410b54941c05410140025901d03040160313591201c402d0803420400348411100e00c0c4221510000d02c41051910000c9200904469000c03280540c940004103c030000040810284c2c1c0984100100d0b06819a4003c00100a540000e000c1d200507c8400e4002c9030424100b1101620a125100c141302000701569140c0e83c035000184003400e00125043c81c403210610300c1000c2a0443c0340f020800000000c07004d80703076a5891a54034050710002d03000302c062040002600000603858002c1d45031500ba43c074003e41d02c928084400900c4003045c1c0c1d0103441c241c0d24200d0301c2c00183d01c001c1440c0282d150421001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 851688705 1250 851687455 851687467
    0x2708070305160b0f0901021c021305210606030607450905010b09060712180905270d050708040b0a0203040503060f0f0103170715020a030c0306030512 66
    0x140c41a02ca01c042100c0c075640c0001c040402c01c82d2080406020309080950301c000c45c1da074030400394200c0c401d107580008a91fa0750100c03103244000f1600100016201d405205100030f03501c1c400b0035a80e0321040d1a40d04d0302d000d10010aa0021802c22205038030030310487c0109100e0501c02c601400200301d0400c50f98201c444800a58100701150039406119017403e0081c0038030403898a0200e0a1010501903400c030681003000008084813590180c400e03141009090900c0c00020759510300c85000104c110303009004003006041544003001d903030381000f401d6040004c01d080c45c102100b0141608858502da003c041600c000718100c51000030f0f00028000541001e41c1da9105030300f0036080314002e0713a0002d0070000340001c1c43c280c80c0758080084d1086a00940445490351601414026820401c80d10304206e802c42400420100d00710b4440c0320010040141034a1404000d038640340d0104490502003030890f90009400c031002d0b41d06100300080c2a945180800c5844c1c15961a540c5403ea0702000c010311000200e48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 851689955 1250 851688705 851688707
    0xd0f050712021f021306030504110405270a030f050a0c030f0207030c090c030c0c0f02060a0e040f0c0905040e0705060306010e0d1b0e041a0405010f0c080a27080703 72
    0x507000b00c940f49580703408460268030a026001e5400541e128070000805500011554081e019090280307a0050350086912503c02c10b02c0002d1a00514000d4140c407400401d40b4141865a0010138517a03420000d0000301040f403e0141c0340100d91100203003041300800c040309a850f40603004418890340340c070345000c0d0b07100244001c0745419802d401c060800d4001c0100006c080744d1940c056140220141c40c103100c6c00c0348859003600e03400c01d4480c02410070000b2000c03c6d40149004001040c0080143c20711641f40303034182e80442c00b140c0001d200031403026038aa03111080260481a2907008190441e0140030301c0711122840c030b40b5849a8400c0d680104404800f18501d03a008a00e071310200d183c00b420212003d141410003081e005560070740c0510000181c0300100c2d50480c5541103a100d150007000d04055804c040e01c2c0c06414800c02801920349559412600c0300316103c40c022592640380b15500c18030b182c10803650303200445103004851000c10040300004000103070414401c590305604000c1c5d942e122016030034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 851691205 1250 851689955 851689963
    0x20d030c0c0b0c030310080102030714030405120403054e1e04090b0105120610230409140103020f0d030309050601240e09060f03120409020c0d0f05071202 68
    0xb9844500403d50000c400d2001003d0344c801e00d42c0440383c40c9070640d548165401c070302c02070b01c7c0c080025001903000000343c2c0072940190340081c42142158218044c200d030141903078109800071641c0313800400a80480582d644442e003a0800c5511991950018200e1121000e844008550504210101c0d0080c000320ba4403052f580c0052407140c1c582d00c00c2020036145d65a45d030140c0140f924281c940021102154441c4040d56003100b540307010900162100420400901d12940d594420000c41c03d00382c20810800d500c1a800040b14140d0281d2907c1c2086c0c0a81e0661f0b145d180c3c0c01100d100e0303903001000541c0e42c80007035800e008010381d4081c0c0d5001050174203e01801c03e0380d802524a1140100010300d00c0003034a105400503125080d448082ca0188074212840e951010025500402d03110119840d460000b6154480c001c004049032802c01c00c19441c0710b42c0b40c001c0d61101c24900d0b404203280800c81401e02080f903100b5003924000c86800112100071b8a58002d021014011420440c4001c0e40180200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 851692455 1250 851691205 851691209
    0x512071d040b1212132c06030f07030809032107060b0117090a120f0801060302030c040302151b0a0305040608220b04140c15090d0c030b1b07020d030c0c 67
    0x501075074030a0301c4600c840002039000c25a01525110a090002245d070999114071503c04a41c07950304006d800000c003044000d22001d0909541f5000b1804844e048410422400c0c000358855081c2c99100c41401d0205030600034406c02c0e001c0390310311030613030380d04426150030454580b5030b440a000070f0b0445101004950f050003040780e9000c4803080f0030074002e400c040001d446004034420b00c99512201a0803108480034407031800c006c008a01c1440041c40350901030f0300910351100e007088250342810b03501e400103988403464400c880500d000005140350201661911001c45000c0e00d0010000c44ea281c5e60014114440c1d0710a070020050060040788001b0800c00c00721046904400521100706518207064105030341c203440032912405017502c104001c1a010601c240300c1340e0b00420301c2a0170751400ca9402c28680c0040001c070303400340170329044030005212001440c000d1070141070051164a80580e6800740784d0315409000120220510070700f40165a11001c4002d40c503411b14000f150b544840c07a08150582c069 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 851693705 1250 851692455 851692489
    0x118110f0c1f060e0a021204030f1209030504090e070803030f0a0b04050411010f0e01021209030106150c03090614070201120f020a0c0506010e010303050403080304140304060512071d040b 82
    0xe494010211903800c1a410350350701d40848142e513201c0d9401d050884c801c492280d085040047c3c00100400c0c025201603041044600b44014148a0440194119458103008801294020034244007020380d0344200494205030741c00400ca15424071000594030f0000074070320549120b9800014441180b150405c0d90041000341082c00141054a03240c00003541c021131185c000f031400e0384010701042c4200100c03548008180c0103071650720013542e480e070360903404940c915403d0b640769000004c0700314600e00d039020107004076900d11002c2c0c400703490002c000300020380c403034010401607000820840c01d10100710381c00141d0908141d00c0002c0044582800361114031110100d952010890302d5040380c2141c00c2c0d802c010702c21001c1d0b41c52a83c03211000301040340280030140000700284410f1002a041c00b0045400c9070040030f8800b80408850380d202d1865015030030010000f01c0104250303502084510340c07190086482e061408502914295004249a0402c4203a02c1691a4109994a919200d034004550350203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 851694955 1250 851693705 851693743
    0x31a040f0b100803070c0e1b03060112090209070201060e1305030a0f17190617103303020a0602010c0f3b03070b040b0906070c050603040b0118110f0c 66
    0x70340c00c1400c8806c1b110706c110f2403850203041c001045640345c000e211a8107001001c0e007900350740350800110f034022402403600e41c40d2551484803201590350400030501c41c01d800e50020038142d042c0100080c1051020303280b400d06500c40c804d0300c0e001410220a842c040300d402c1c50701582c072000420049803017241990740030315071043c00010301500c0300d01c800c1062a8140398580030710105550720311805039a0251400302d44c2a802600c924008070081d90440050340041000c00d22508070703a555a540f118002c004003103100418405c00700b0450402198540c02801c2500003041b40da055041c01500700c0d04d601e40b0150030001c2030508043c03807402e410a4418094901c040c102006940303001520108075529500360b00c203200e04100000c2e40c0d92240100e03000c1e0b03004441001c1c248040030f0140300300340d000482c0849900303010300000b09654840c1d0b0044c51180d03005c0c8980b68000d500d8030000315020306820702626981c50801040d01f94041d41d4204a68100720b02d42100c07030769920891b484908240c040320701d028803100c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 851696205 1250 851694955 851694967
    0x503070906031e051008011503020f10050f030f07021218010825050c250608060f12010c0f031116060b120a060b030c09010510111006031a040f0b100803 67
    0x40110100000d81b5603070802040106080d0100e403204510510009511901c440e400c0d100c42d080c14074060110403020f04020381440e811070101a2a500125030744403100205504110406504000040700280c0d210b20341d5140c80c0517403c0002c4030740d0b01a0b5442d41030282040c0402c0350085400c450a1020200b03003201504017403000c0c0010025400041c0c18441c1e842004990341c15a418804c03029210b0f5040c03c3c402c031388180341035020f0350b4182c00280081e03031001203004054500d80312140d480c8010303d260800014026101d0001404e001110012541014980000603882d54040001c40748000748034407070a46c40820502d420740203000c0601103d500403104205201d800c0c40d0000f0155042803103240305100d001070303030340c01e056481d03410200481d4000b101000401440c108512003005420980c5030800740303503054035030fa90708c1c04507400c100c1c3c4d88159507640c0401c14803481c001c0d244414030101800f0501c9040c1074444803040c10410a024107105002004142c51803065403888004000c05410b69031159 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 851697455 1250 851696205 851696221
    0x90f07110f0a03090503030c0606150f0d052e050f121504031d030606040f090506010618052e0c05070602061b070c0e060418060509010b010503070906031e05 69
    0x15107882e0850100d020f5503004201c1d0324001c01511350030403400c0d0040c2200e9480608100d01b1088a40c0c03406404071307042250b500c005150100400743e0500c820404201403c1c030030203e40640c101c41d440352000c041c40d40d004000e90003018001380219601143c01301c01c281a04d400044928510301e484400500c111200e0050205180ca20f05108a0103925882d956040c00e19950030382c0c42ea0300d144150315821150009a191030070394018580050303524400a00f00700c0c10394409103000000c0e04a900812120708907120b101000500314405014207484503e2028181414800645401d4100d468855200c05081d88030070f2055421600c00d40c0c1240464a5032581c580000c1c2d02e482c01070700c40207013140d02c05154070034400d895403c44134442c0d481080e42e603410349002000c012125000d00410361154607100c84102d140f81990100c0b2495005060000e0039080c040c265038210782c01490301506102080c81080513442c0c002050400311140360502142c07070138881000003603a40036009140c0090786840f00340300c810 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 851698705 1250 851697455 851697463
    0x90f0d03020a170c1c180e0430030b040605011d04020313020a060512010905060916031d03220605181507030e15030c041e0306091a070e090f07110f 65
    0x154400e0b41ba8990012060f00750300e00910458040c40d10b844014101160020780c030001e01c1603407082d2240d5000c0c00ca06002c10f0201c0780350361110400c00025200d009880c86446c01d80706d1070009007001d0901405c0199000101c1d500652200e0000303210703030b501000040c00350f0003503a08a2001940100100185a150f0101801030303080390110403850b19594001050b40740d8241f203090b004902c01061115583e035008244e51203c5c0300c1280203400c0640390b01030440c1e0603411805c0009501e0040000c1d589a800e500480319101c2d0b9070b26a07060001c80004020040c540d0080f0403500c440844102002c004150b90001c9605044140a01c40c040700300001c26005150341320010041020781240e802124a52078084a0500c2c042030700c0c1f082c800442080100070302c40310001c1440c0004200360503210181d07034981390581160101d001c2950810303000e980d00c6100e0800111004d07031082c1103041607400d262541010070401c0307000a010041c45046600482d02541c042d0481c0ca100960040403a00c012000c140e1064603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 851699955 1250 851698705 851698753
    0x52b1e0b0f0f0c040e1f080304051801050a05062d0c1006060509040903020705180f09060c1e0706060f05100c080d091e0503090f0d03020a170c 63
    0x840907200010440200340c100003036020b070a09030140e60030203007044000c2412080240c00c41629003e1440d10b1000d0250344a0540000c0038600040d68440313203000f00f44004640c250300950003040e05070005224503a00d19403100160340e01a15800e454200e015020302d000110350300b009207180000c80000800e410312070001d16071000020107845020000f0050b103c01e444060141002051051000ca80181840d5010300c0503680644111074005a844011610001504010034140001300342009428017040b120503810281000040006280030241a005c60050340c800306a201204200010a03d60074004d07a28001d81155040042540e038521181d000c280d81c1c840c85016500007140e10603018041d4968014841d00501568504002c80c07001c6001020080002c613080040d041c5211585c034020f0a090404610401c001c554641045080041914400c4012485100c14184140c0040e6021501140e010751210240e4003a40070328020b0350b26402681030042d458410a280080a12280004854 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 851701205 1250 851699955 851699971
    0x4080706110306040e030a080a0f06030215030601080f09100207032a060605010203160b04020d080a050d0605060702100320160c0501050f0a0c0219060201090c052b1e0b 74
    0x80701c9104200280c6d01c90280b450b554001c224143c00085c0d0102054110f81540b8219180000b8183d8590f40002e003070000060803640102c4010081000558100f940c0070b0b04a0720b2108412034620704003000c1c41c0e03205040260500c0144e0042041030805000c1c861144004032002c140380d07401c144c1600045a00420006c050782c109042c02c0c40040d9950001c4120781c1a008000c00c40a001246502d40d00003141003d08102e130030072050450003000c5803030100940070040740c1c0e41d9030340e030f1340c8128400340c00940f140c1c3e410461050800700400c0303005076038102110300c0300b5069060105189103d50101180140001c10071414203030b000170000d82c0f182c00f5807241040c0d80e100c1c006508045171203c0c0111000d006000038240c01c03441c10000f40d081c042c0a06614210030340b00401b80d94841d5191070343c1c280c1080055003c3c070090b030744030700d81403041000208011000d000d054a04401002491001c440d5113403a00d10001d01e40c41965014505102c103140100140001c108100400da22491800010511007154514 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 851702455 1250 851701205 851701211
    0x120902100807120608070b0c15010e1006020106060c150902060c0f01060911160606091103061c2a0902191101020901080606030601120f05090d08040506010b030408070611030604 78
    0x85004244a84c10685010000504045041c20050001984050354100300d0f07100b11100890b0fa56501c4400fa80a4001e48140004070300b08008034007080c4080c0c0e003041c005c4d64184042484429800b10710030b41358a80165030a030460b001e01d10034100900c000702008e5007004000400c160084130000d1070b01103504108008000c90360356000f07448100c600401c00240d210904001b460342c141c4101c282c4a15040c065040010742c1643c40003001d04850b0802c00390b200880021040048915010000d040030380d61a0501d100c1c1784410780d80b8030203035055204a60030800070120054032044070112083e40a003c1e611001c5503240f580d0441088440c190007884000240c01d1001c0008040041c02a10300d41001030711540542e4550800300806a000100b000d07040201003041c03454079000d03500031000d01b0aa040b030000f51070f0070080041c1d410121038007910000d002c06001400f000810028290f07044034840c0a6040e126201d038541142280b04110001d4001c1c4d00703210500c404140d0000c025070050744111010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 851703705 1250 851702455 851702477
    0x7030c0207060815090705040b04030c0906120309090f0f0e0a060c05130b1e07030903020306061c020d1b0609080705010c03080f0628030b0c03010e07120902100807 72
    0x101c89141c02111200c4c2c12010b450014010b500b0518282c9400c4410350500178140741c0c54a5110000ea08150300582d1a1600c116080000e944140b05e240c003c0d107140c0003e00136034450740d107010701881c40520403805034a030b69040d07098801410343d205001d4415110300c28841c840c5496180742c0d0fa40000f0000303441e01898841080b040f24083c00c101c941c00b25084800c1c91445150a401511680245c4d003100c0c9110100100114042a060000c0080078480d4807103808050a40c011300d03207130080041003940211110300c161040000b2094504036190b0341101e90b082200030503d05160b090514001a02c000000795001190b140d800045040c01d443d1601c00b00d403401d40c2d1760001114003100030500030b0085901c1201145641d03003d00c2c41240d00c0f4001518500940822048044000e4600c0b10005100320b4405010b0003003080700110300e9007254500340c0580c15541031020102c1e10001c05482d203424001ca8a003008400d014941001d00d0560300240005000003c4207005000c4c002c0484245d0001218046030f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 851704955 1250 851703705 851703707
    0x1407050706140105093411070501080735040312050115120b030307320c090103020f030f160609090225150213030b10080705130608060a0e0d0206070219020d050607030c020706 77
    0x202f140b103040d0076944ca072039080600440d82840d030000480105401d5600c3c043d061b035500885040d0340618402d41d581409905800e10b440700710b030760607007000c10181c0d80d00c0340380348549070300038105280012030701c6002418643d0480081e00d184030302d04008003800d0954490820b0030b03d030808070200b00c0801c0e041c170314060360381c49405030b4031351503c0b050300380d0b100c00740f40014005820000c440244071030010741202c08241d540075000b4580340800c600300c1401c0c5401c440603c11240d001c0028001403400070000d60400290a010300d0208a00180168002d40c2d88130003c1e09001c010094001c141c880103400310742e200c40c13a8491801000640c042a55405c0f201c0b00452120503c40303040301c2c201c07a008005003903103a00306400c001850f0301611039a420300340c5444001c60703041801d000c490b0240c082110300003906020a140c0a0078041c0340e01c060002c0d500034108004655402146140c0c908110f00f03410304486406100142d03402a54500103030040c8182c030100320195030181e002c507d410390140c084480e00c2da5507400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 851706205 1250 851704955 851704967
    0x2010207260708030c070b04080306010905030a0b040809130f0209090f040c091d060f15090f01060c0c0b0a081f0501020c060304061407050706140105093411070501 72
    0x490010740c0030042c0c1070109007007402a607000030b84000428604105600c03100da10308400d8905a4100390000140001c5681042c02100101800c0e0060226490b03245c4078100001350060002c2c06102c4005151001d942c1c5070000380d04c440040c2101005004a91213141c0008c0d005000e016008031003240108036420640504107215075482078000d1002800c00d0f44100c080c0c4180844a0955000344200d00810b02050128503c11110320000c50300b40c0c501401650a02260304040d18000c581d030b50140401100f80c000001d064409a05242d5929440e515080c2d0210f48242d10850801c107001c21075120313069200603860b00034140c10151a2010304006400c00140d0f620340704040c050b90021090682a0418001465002c1d000d808001184011002015000e2804880c68000100c002403c003081203c68881c3e4400303400303c1c0071071245941c10200800c103540c402400030034034004404d686810304495408542c0c091510240c03c0b524103001760350040c0080e503c0b002241d40034082c0c05001300710382d40300358 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 851707455 1250 851706205 851706263
    0x6050a05100f05041710050a0510090b03070e1f0f05060a080a0f020c15070c2013020f0a0311070b130f0c0b0a1106040c05151902010207 60
    0x304110703240d00c000801034904240011084007444024040020079004401c80281500c04003070140003601500c242c110200c0f0002469440218030700414007400b009581003130005d443c40c03680001840c41d0180006440d00001e644810303401e00c0f2200c00c1001c40d4001c4a850302c2c022918001c04681d06880d02181001d540b91400303a250000300c14003860810a1007144816040b00e802c00c000261501141142c4c0c0581e880401c4140d80c5a0003030040c9203440403040e411507448562440d10708131890302c2e503503044262090f504003d0424101c4c2d00c03448049544140303181e16600103010045644801e086030030005500041c0f44600424a0801544001180002262400799100c5010609540d4800d103403034400c1c400d100140e40303c0800c020f0400010709221410400b4010462560b0744070902c08a0007030003855800c1c0b02ca11250410402c0c000020141d90b1120141c5004480b00f0b03501c1c9038101922032160003280780c129542e031003610002c4070042d010f41c001c144080c007818800c0095600040c482c0000c1f0010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 851708705 1250 851707455 851707459
    0x5011e0b010c081e07020d0620040503120c0102090406141003050f3709020405091b010e1207240f0c0609030507020303030f01050a0f03020d0b0403031806020d06050a05 74
    0x404c50380282403403c60b84c40c00e8040403450000e0030400c0c03940216508a1103241c048921650315203000c0465030528151072032400d00008003d280c01d0a110100c5c0c0c032000506c8000c149200f01141001d5404400e40544034400000b0304100f04035030380c9249030b080400010140301e000381541c50781c00c2400361084c0926071092411040b200d4060b19880e0440307482da1191801c0c050342c245540c3c0410080d0680c0c04101250000b071550100d4248a50300400c011200b018000e00602d90000083d0000e070020481c211340c080a09003048c0598880d2100490aa0000b100300340c0443c1c020300d6000324040a84d41c6111074501c9840d040741c107018044640644013802c801d00340d580400c2c0803510000000710103802c005005446441c0040c10000150702207441d5420560b103424450782c003400180b05034185600800024070301120780218692858001c5842d0f0043c110020742080203420008003031602039003001c400c404542c0c0442d00b0600060a08400a405c800e180440c401c1c10040e0015640c908641d0840c152440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 851709955 1250 851708705 851708707
    0x612070509040f05070308040e1825050a091407030e1f09060612050c010f0f12060506030103050303150118121713050102010f020304030c0b1305011e0b010c08 70
    0x5140401141d0040108101d036480b000c00d4121000034014000d5070000e40c8111030341c5881d2030601130100b207a09401846800364455940282d40070780d100107086c40c031544002000d002d03449041d03003c0c40b40c02200d540286030850045500000c41c22945da01c00f4102c20359440c00200d054440c03120881c150f03040404400043d60101404400c1500c1c01804280d800c0c0100310005408040355440c441503035241d9200740102415114140240f040600c0080303280b62091915502c1d8004074880030b021125440c94030410815500c2e80c02060500d29030003640900700090031240c80c0c1d03a40c0d1520599075403040760310380300024158150882c0c5501034500c7d00c03208140f1800c890801c9040120300c00d075100c4c01c0041590b4120050500c4200c00c0c10f9000100103000c00c19002c080a02d007080e0000e1300f074034905c1900401f45403041040001096000b8224010541d0082d40d0301c05036260600880000c01d0103035005880e039480c012481080c0120720512001130642c021041c0108403000c80151803c1c0081c05000c4c100b000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 851711205 1250 851709955 851709959
    0x10b040b21030d06120209100e01060c0f0b091f02130302040c030b04090b060103060f080c0103151e030605060102060f06040b220f140c071704090216020405061207 72
    0x90068205441071001c0031242040c00b0184680144c0b40140e0049050302c070012041015070901960850340600800015040c40d4a4103031880d040d444e051003094100320444d100103003040044c00c0c3c0c80407015007241500f030441c28484002610790402d01032441c5110f00e5a903540c0c4410a40d40250303140e569020700d0000c1c2051642e000e000250819a003000201583da42d1413202ca56540d202e08015280140e8005125203001d03c0003404030364454000c0e0302d40d200c01c10010802e1140000300150510401e18000c250b015402800601062654008003512100c2464052404000ca01c4c004201d80c010001031020340c4450005a8a580c0156030708191b541c0320300b0005481d4103083d040b900345524040c20040300e0040c0b01c01c00360700c035400c01c00200c1607941d03d80d03001d403038519009d00490c4403a1000846049040c100950032811500c07440030000c01d42043d540c100070307690f4040310962300200400d04065613034000c500e08003400c1c40c8809c40102e1103989400040303811400c0440c04140b41030b1020008002080c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 851712455 1250 851711205 851711239
    0x20c1e0a0210121b14070c0b070305040e01080f0106051012112a0106050906010f030903030b04020c0109060609110f0d06082b260a061a0c010b040b 65
    0x801441510b405209002e035401086001c01c3c85100c005221500d050102041201c10003000011001c0210304a042e0501c5084040380c44426514200c81001c88210341e103903514a001c2d1083d014691003e541c89054800014074801301154402007030442c140200001c40e2174034100260a010a2600e50001d5038035a00d240c1e4103101076014030015580d08403040e04040c0895002c0c40309500108100505e1407001002403c904000d018070005040212103030f020754605440020640103581401004164498240c80c0a00d8040e80c0500c650300b2019005541d4ae620120040e8040c00d4004000c440c0540307850000210540325105070903500316840e48241c6070800300807041060350040540d95158a540b8bc10018544108120008051a856903180e62000d5400e20480c03a000601e03031041d09200058141440340700c1c8030f07000c090000000c00140456521031811a03001410250860050401c402004c032015044041c0608104610040203004940d51001888251028903002903081501024602881 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 851713705 1250 851712455 851712469
    0x60f03020a0908190b0a180f03230403050f0d0509060d11070308090f0f03030a020d0e0a200a030c05043c06060f080105100c0213020c1e0a02 62
    0x25032540380c68042c068541840c01d06000c015641041603224010080081240000784990700c1402c020701041006a09101d08040c02a201c400400f94242000f9500030140202805007031681000c41c0c5c1640d03840c3c03d480000c02030b4007070302080c0ca0f10320401005100300c0100140d0b80800c0b011503520141000c88003030510a168005c200d25854403500c3d40810f021100c540300140407034a0190b03035443d403242400c525407400c0ca500003c3c2d0b4480e68126005d242c0555400201300d98000ca655035006a03100700000f4200010202c1054590346801600da5207001d1006c1180340f0a03800b40d1400c1d110004005080811400400603c00103004039190441003225290a41c4076a10314441400f600c0308643c0010b1201104204103a0303c9445000c0d030007824004014a403040c580030f4a05402c1c404801e05480d4805444103205100311391041a002800c5041e007441201400300081e4007900403d000071601800901079048070f040c0b03007024416505440d0490140d40000c1070040390700d1001d014214a544c00303100e24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 851714955 1250 851713705 851713717
    0x10170c0d0212120f09041808030402130e030706140a0e0a0b07020118051b0607150c030609150806100303170a110d020a080609011406031b0c0a0b10060f0302 69
    0x82c0d0248528140c01074003848000d1070004010402e4554400100081004507880c0b540e42c01c4250555040034070014083c642201d8016030122041d844c41c4003081c03050005440381e81d01b1911180401b01d04c060401c031a54005044a8980d01e14044240c1c0e80c580161003190380c0450764a243d80c2c000004140031500406885400401c01e100106d13840c01001c5c021105e4a8039801c0890b1560300203001142c102c803c000d10240d640c8030071600c1c0b40c640a06505c0d201d14881401680451a40d541e0488a003900e000c0d0303018100400840000340310036030354440d0360382c0c03000081e100303616041c05100000343c1501d11910b0900140d9901d5107483c10341d000c0c51092040c2e600001002030039401e944640c0800315540b4035010700650518143c025a1320f007115140144403400203440280100101401070250000403402000d802805032600364032640c0d03000fa00e0202940035000e114260300000340003003801c50040740e80d010503030154620380e2654964140510f4126130750b228002c0001e6807160200030040c82900100a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 851716205 1250 851714955 851714989
    0x50708030408120c1e09010504032307120b1602061306060e131a01061b0c05040504050c010813050c0405040201231b1209061c0510170c0d02 62
    0x7003816500e2404290b1004284e41d800405032010400003001100c1c1c04494489003580b400791818021000006000b034041c500009019405c500c3d18421064841c150864800d00400201d41c1c04903030700c064002042e16005e000b55140001800040c109503407110200d201000c10341d0040065aa4400d464609140c403040c0c100c5602d03464540c0040d00e400c00031855400b0b40c04050141c10940e1a41c6031440c5103d12803030344198905910801001441e070007a0341c10055140074a0003030104034283c506080e1078100c035040150700a03e00f50601c0300b484000290062603210030b8803066020b4444c5d59820b4905001c120300100340741d004410072070890506411950b00284181002c14070342c015034000220700d0041c038081d00081c04000c908a851104a07800320000132882c003000d40107900303500ca10500e0300c0c800c42c0c8115024500000c0c400524a00310f600e620003041543c0c5080050781000182840a0211803183c1c059168003c400104640e40c045901060130a004100420b4003400703500f071094840003000b00c58 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 851717455 1250 851716205 851716207
    0xd050915040303030c030b18310c0602070608010f121109040f0203011104060c060b0a030f03020a03080a02090303030610020313030317090601061209050102073e01050708030408 78
    0x264000c1021005080914400d48000c6403030344010500400321010200c10610918080d00c6041c00c1741c1d032404a5903001a4181001d0b6031101c0322042064030300d100441c20001013052020094144200146848142c604036070a48160036560041120450300a0240600040203454200806017500540201c40c9200d01902d4004003002d000040c12500115000e487c0c0f4190809014218030f401e204000300640d41c010711906060a2202c010040c038840807004244503500c0d0070220b40c6590300001c1900075944404010024066031500035140e50280c80c00b2404030700f4040200d41d500b00580203655030301101400840c156a1903104210b510b0209080110a600041045917040990400350101031030081d11035603010600429055400389005041d032080f60000340040c0308441d400528103901c00c1988001085603030207814403d0080c410640001c1c03040b11020b00c10700044502d680070741645140b0b1501c81e80032005020101d10910201c841c443d0000d40708014090014640a000d50f4125000b04405 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 851718705 1250 851717455 851717479
    0x201030b0907200105011d1005030a050d030506090c0a0f03060f0902040311030d0c0f030e1807031d03040621020706020912011a060c2406031e0d0509 66
    0x800c0760900700b0354a0710001152401c510000d1814903544511000c00071008000c250300d0802800125202d0407400c4443c058a41e0120f02c1104901c852640600b02c01800d564400040f444c1440e1b4901000940703c004c24100000144280341055415100b811781441c03041c07416404c00000c50b07038407406e04105000d143d40c0e00e00210f030b420165103059000d0302e02c0090040c0d0300c0341181080c6e40503003005c10305140f2a0f4080f00803109500c0d07001a0322202541c0c802890b81c2100070514050307030191a40c500c0c080d0080f00c0e01450038140d41e00d00e800180148242d0310700308250ba4800704a1250700300c0d41c4076412240d510420040205520a001440303c2c150200d12500c0d00881350740c506800c1c3d0b441040203880c603e401040a02d11482c120b100c0d519110b40c20780007004900c500d031203032900c00682c00380407904c503850101d00800091014002c1000141d45154450030101c1500b4071044002030544400b070192043c890710090507420380b119854242d0340d440c01440301c4030510070b040703c00350f00544010342c000c2140240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 851719955 1250 851718705 851718709
    0x2c151c0f0311010212090708010609020f04141302030c0a080f06030d05130308040b031f08120714100515010507080d02030c090306090c0f1c0212070f0f1e06090603090201030b 77
    0x215001d6100a1b01a1854620700070381c160030344807150022006180304004110a44156504541c11500d504850f04884400400086d02181304045030040860001082100305201d840040104d25855101d540007a200d2203506501184100c44075901503202040550b0302c10302940c060714060004c01c2da281d00d81d07900d0755141861904144c6c0052596500403042c40100004100071000d4003900f0034964100390720b8000a2599203480c00d001801e03560740002c990b014444000311183d48000c1500444515500319407000e0300901d01254039000c20400c0c111071003020340c41581120700f81600b01c00d82c9814086904041c100035400036080001000c020414540f40d030f00c0602c802d91082042d1005001101c050005001e80070361110400c5110300264414500c900c0c0d00b03006a4007145030155031911000141c140384a1402220360003001031004191000961529001080b4090b15140e10100d0801d4450451019904a1078090304010070303030081d0207000d0039100f84d210110305030051502049509071030300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 851721205 1250 851719955 851719987
    0xe130f0b060a0c060c02030a1407030c080f0a1710061416080a03060602030f0415090302041a0102011512020d0602040b03070c02282c151c0f03110102 66
    0x104040890701c000580350a0004e00d1240c217440c100d642c0084c0d4508501c8a074020140b8013180703004c0c40d00000205183d000e040c4a803c01c600541c7c0d00040c0d81d655180b502911207100c0d0010480b8100048210021030710700440d4200c0c0380e020f6417111119400c000e0604100352404803608e003038611000801d03c039442911001d0001401440e010380500c03039840421207001010366a4640200c400d55200f001000c8914500101b140c1c01c80741c2c2c003601c035090345003055800c8404441a90000c2d40c083d040c0061f0303507402d800e0380380440da00e501c00b60002c001080114240c904618520303c502c13034040d8040c1d826407001d41000c165545030b8a109031001860552291554071482d00242e400d0800100209800e200b1800c09004910001600644480d0503184081c1c928034011154003070390806050042c4600719480754000020303000804105400f00c0c501c2c1100078a5405e02d000702c043c51203070034650401001c0c4041c1d184841c5095400187c555100040341e142a102601d40b12042e4202c1d6600304041c24840390191 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 851722455 1250 851721205 851721217
    0x140a050705161707150e0f0301060b03160e0d0303090317040b180105151c0203060a090c1e060e0609100c05060702010b1c020402040b031f060e130f0b06 67
    0xc40000c1420308001120161918000c0f481019902090041c0084e8907003079981c000c0128503180c1956921409004100c44055000c0e030719030158203101002c561845000003541c81060b010103008000702e40302004490100f05211040e400c4041c0b0503070040403038425048801001e0181c03d09400e803840158650303624030421201070300c40f041c1a50910103810765400e00c06802c2007014009000c5402c000140440c8a0310036091188a83d00c080c001e110408180f0a90b0325080350010150341107071412078410300c0a000c407990229403403594201e01141d40301c521241c000c9081307002009405180c0c02c1c4103055810105420079694001c009011014099992118031050b00c146683c0e2025000c80c03903c0c0181c50144050140c90035a4104556082c042c2caa804c1c000c10584a1140c040d48900e07a10300124009108d2500300c041101d0f0008100814580319005c144190311082030745c04400c5076500011511a0440c1d00c14650001d260450307041107480740c0d0000c0c2c902c81068070001856280000c00906594004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 851723705 1250 851722455 851722483
    0x904022104031709060f0702121c0b040204030503031b070204050901020a020105160c03050d060b03011212020115140f060a020109020109140108070804050c090c1c0606140a050705 79
    0xd64200010542e01100c8000305100042e1010b906080c10f201142d100c0030000c04030810200c2400000b0201d40c030030001d0002c0204c0c0c6245103a96907881c40511032800ca0407a0b403080c2c075107003032203040d42c80b0381418801c803422640c0090182d42551510003a100c1540e4100340958441c07001444020090b070b036140300381c9000f403004500040e510b00001c03d0180c2980c1d8003c0c00031020b001201c00750100a40c00c035034a07402c082e0341840c00300d503a9070119248100401c4540c000e10440000880003091000c4107951400c0d40314040c4070384e8003000159503000c900344c40d00395840119204406100304011280c0c0800646504401400424803071000c1002c2001d90704212800d40040c0e440b13180c51815541c2004001c00501a1450090440e808000000c0e00c02900503100c0310070040c58400141c207002040c0103112503110000c2041c461420144200d0803290046a0120307000300c01101c02c0c410160701c62103490101c0d2070b5a00c4091441008034a00621038225141072002c3c00030801c03522000402c1480480489456 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 851724955 1250 851723705 851723767
    0x1009030201020c01030b0604051201020d091214071a04020d020d030302031803030f0c030c070f0b0103020a090e0607050f090406091a061e0706110a03060303020f21090402 75
    0x9140002481c04030b070303140464180340c90302c19801015100c500460341600c80c1503407448815800400340d40c0c024821350303a400e000d8500c1d2003804010003880c0c3c58201c0c0c101d8100d503910b55242600481c103088074442c01800400403000c10310a020501102d9128980c0180020702400100700c40d6004034410540c0601d003180081e5000040101d00d490201d204910100401c00640c21403a040c8c0340b95622000c00f424003400c260300440000c03241501d201c00c0710715a5501c411098121030f101e18120100d1b80d003e00040703100340d031801004614050144141c9035100440002044207440703503038082e0b800d640000c1a14010201c104020b200c1504d9500500008108090000601007a52200d61558102440745140308060800140b8a00c0c204404011f80c407a4121065690700c058030315003030000700300d04400441e03071440c081134090131260035600c070108590185d003c1d80c1100044e0499191608000301c0c075240e519000449448020340c120015103140b07200a03000500d400035080115404c0290740380b80b020803241d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 851726205 1250 851724955 851724959
    0x90503031908150603060904080f07080915070506071101020c12071401020408071a041706070f030b1c050c15041a040506030f040309051012230c03151009 68
    0x80e1242d0060351221034034102c2180da15030f4100150321440041c00b00da11800d2010081810310070180204d03407020798004841c5584101c03501c0d043d05103402c88014244142c40440700307003500300200c20480e03c0c000e510001078101c0d42d54403a0160740c01c006c1c4983c074010340c0d07500344049124214104850070021900d5403c0300c2c0c880d402868150401080c42c2d40c5402c0b50790041c8020000c00000190910030f03140380f0721442141c0001100f4004460145034400050410307100b8003080d00d284085000c034000e0250381e8492040040741c00094040d81c01a151094100e111034019402c40b403130000c4e505400e248140c00703841c1004e6007000003882c0c07540c04107002104454006010031103a5407000801c840c0115002060703051030b01d440001400e500004101d00c005c1460800040e0406105d4138500340502001031210765040c440d1800200101d2001c0c4031245d00d5031400f042c0d1600d00030550300349690381191100c507035800e0743c42d248241d41541001c0c1c505641c000c404405a051580c4a0f080700e00a000c00350b0325a0071940c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 851727455 1250 851726205 851726207
    0x3090c04060f05030c1206070f051e090f091012050c0d080405190f090921051b0a0f021c05030406021b0105211005180a0e0f1c0905030319 61
    0x20700c1740110600c11841170866009090012800c1603103e07041c0e08207026004495001942c1038480c60148401515066807214a1078002101800c1800301c181c419501030309244091010307000c403c0c0e4842a034070b01411800c000700701c500494003418500c00d20503141e04655540c08034040141000007210301c01000b003001d01890400c0103207082d480e505082203140c40c500d40944598400703983e01800c51000e4480c8840800c0c0001041c10164002c000c16010707100c8254914000d003d50800100800b1a00614015458920001903241d00103600074004d4500300a8035800c0059840d00042e071804030364141c021180100740244064001000ea80e009800e070002d1518401907003403c0050f025052040a103c41c0e00c10801252268154032003130400403245484201d840696403819a000d01c0d800600c154540d000b540c40004a24040d100c40003003031000b41058440e031912107a10001541a0350f021150070141c030b04450000c24120b10450504c10310b500e4032503000c281103601a88105903c1000e0340c8200d07003a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 851728705 1250 851727455 851727463
    0x5160c05010f0503150d2a050406080c0114090f090406141612050912041206060909030c30170c030c0f0315030a14010f06050906040203090c04060f0503 67
    0x1001882c07030240e145103401e0300c2c05401c146418110300d0080c02c545c80d4600030814010315406803030400d540c0c0e1000c880d0f414000443e100c00d1238020540281e0030208006103e04002030203107258803050b12442d4081642c0541d42c5c056800102c0020f80c001c048a05142c69500c0e1100118015406460040b820b4054842030590100d40923224055007000c1c90014084980e201c1049503408189140c0403505031280c41c40c0d6807a1280c03100c1c00000f111000580002c201030743c807100080051040340140314041c3d94580d01e01c00c84922803000b0b8041070b0709800041c00200311041780c8120000108840c08a540c40d90f810100000060510001069450216103602944961800d9111302200103a5155141c03070301d4840030a010b619101cac2401040400415802c45414100100c07592000c3c00300c44c02070b071250034012601e000e01e24130403849511344800344040e0b1085d4041e14044c0c4501a00d031222030744a08003480000c0d80020b16042d45409440c040c031000d641c841c080c7d0030080280e003ea01c0760391801d1408050034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 851729955 1250 851728705 851728727
    0x1a152217030717030a0b03011a0405010f05031c12060e01051c050319020f0303090a030801061d220509030903070603020c1e070b0304150f1808030705160c0501 70
    0x41988203200300c03000030702070407003d5581c034020114071600c035241d079034010003c0c14802048503455403c04052004804192500e0712030304030300311000d004d03690344e4110b014042030300b03402290f40640000c2c061395120001400c0300200304a0f40c0c40c0151144c4d401c3c2c250314045401a8100d455164505070041000f0300d400b11649030401c216281091107a0702e50790300c003592481740800b91070440b00004103281d0254002e20482c40c0340c0c0784020503070703940303140030030605845403a42d41c811400700c0d10304400416040e00c648540d14000500028440c209985007003000314090030000032840e07405000500b10503c0155015940c084c21206005640301c1007031004160078515150010b038101071041c00418800300001075505141c4403c2250540340200002d001803d103043c0750055581904000b05000c03c01905051165901c80c0e40c100400070203060241010607500015599107000450f01c0e86100070603201802550030ad101da060130381c6040c0301c0d55091200d2900b99041a100340341065000c015550b00a891009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 851731205 1250 851729955 851729999
    0x507031d0d170c0409020c010c02070f080304050103020d112b09020a031103240f16020a0332031b0301050a12060b0603281a1522 57
    0x12072195030500042c58440d410b4090852107803030342c0209400c920b00b02d08032005012410810355440c0880c0486074041c00e0240c2203400148074680e000111205111841c2040c0c561540c0038500c5c0500e840300440194204c1c0c042603030400d55030441d9040562440700140307094400040443e1501030300480c5000c0080890f1185021241020301d102c0040e51090754040070340c0d40c000c8000c0701406101c00071a00d030607250003004010341300d41d00c00800e40d51070f154542880b504003052694842e0342d9001000c2164900c0906441c0540d00001405000a0003038000204660240385090b4141205a40b041d20080d4449041241e00c0c20010500c41d500407000d101c25850b5441030b24261641d4500408140b4200300340c811944009035080c180300c1082a143c2041e801c03050001c003190f40728101880065843c840f00c1490041e044828201c6406a90b864060b03200790344205192240500003a10500800e00c160280030010320360300f004004190700c0b1660701e088038841d042505030946030500441507030f02200c10710208 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 851732455 1250 851731205 851731213
    0x91a04050702030c07090908090d03080f062403130203061f0806010303020309060d0f1415030d08070e0126190b1f0c14011b11060c0901020a060507031d 67
    0x19043d000081ca01080711804480000c10120034180368415018600c09c441d4401741d80b054450601d5840403082e8003032080c030913000a4076140c00d01003088042c010f400f00c060584070031110004181b1440065036101d030000540c02d80407030195001a08000c2c040780c4064040d6541081d056030300c200301e480580030708020002024154110780b030295503809030342c541d40c4c41b030140060031003070101241e00152880ca081c10410f0040c0211017a00c620300000c02c03202080c0c0507041d20400a81468001003088540c6069111803905485d400402c03102412035416a6052109201040e28404511150340b181d0b4004075900701c8140c00c0c44501621098801400305031071609200f1140001d544a80011013414010600c516034110761507001d4031070300c5a07814040c00d5040e26140c2c0002080c01074208680010881400122003003022506075440d03081d14480a81551128000070300f040c0c001e90040506d1501401114000c44a656801054560403120400040d4076a5130303850007640f41e0500c214403600a10054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 851733705 1250 851732455 851732467
    0x506090102031812040e1b0d06060e0121020a02030c0303040f0512190807111507140f03150114031e0708010b0306010305060112022704020918060109091a0405070203 73
    0xc4c0d10240500d0003521581822400400c0441250321200e01d88100340144803920381c0d4482d6099401004248105c0c0041a42c5942c03000082d0702c50403c0014491422410a2110305095080402034010740c00940c29807004003c4c0c844400070400285101c1c503c100b0150b1200046858160705000c0b000302c01001e0107030300f03224221030700b680d554035280250340514100c00c0b981e03210602290360804030030151740d41d8042c060368164502c518070180c1d849100d054542503001c071400d032100145407040c580d5100400134144003040d000103608411030320801051510400c030700500081208135500c15034580000545405d20340740d1402506024a5205049080645056261640c29801444010405410540e9a0000540f01c1c1e01989044944000e05c180c11515112141c01904001076074212040c03000e0745281403424986428000c4131380307111024203011039689040d00d00504522020744894144043c2c03480100d0744099911038003886820102c6500c0360400e1410900003100c1c03014051030210f40080200c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 851734955 1250 851733705 851733733
    0x60e0c01022a190617060f011d04020f04150306080d0c14150a060e0907080d181806050f0a3c0801050105100206010807061b05060901020318 62
    0x4080c814442611081001240100000310005031240c00d08030010b20f00c0c0f1000c0b80450f48240681011061160312064039242c5070100015083c821086a0000b81020381c08610150b640d660f8250004c40a44007608101501d041140c41781c10039088014800c000e1100c546000e641030003441c0c02000800c1c0030301184100480018408240c8402c06030a200c01d84d041180c42c840e040049800741181403841300304030b0801c9000d1001404081c42038410402115010412200001c2124811101c10000901d29541405000c0e1040302444401c0300c0c50b484004400a008948000007841520101e000081c0b52802c0c0b00401909045004545000b00c003010801d00c4820442d03540c00036184c4040e4500001c1c0c010f058186288407a044541e0b080300e4220703e00000f24000d0541003181650000c49001d603c017016940c04983e0344409100d442080d03400402c04000b00c1c3c2c094078080c0030414060000310380d01d012a80714245010b07410b980005007a0340c000200007146171012108403a608121014120921406070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 851736205 1250 851734955 851734993
    0x30212130b040b07020c030a06020d0b0604351c030f090f081c1803080106050309030a0c031106130b101404020a0302070f030512010b0a120f1107060e0c0102 69
    0x801030072846480042184c0c2c9008100d082101c070401000c441a45810303150820203500301d04180f0b0045801e0401c0c1c000396240c5032050300c056940081c003d0304c1d10102c00080e007512a0031501c08440401d005d000001142c13000340032a03004014110040c29590000703100084c200c503c3d207030154407610f2030072900d0000101c25001100a040d000803a1a44547d480100c2e921200c041020502103185419000110703420214402e03810715020751146280b580c0c0e80c0760245c0300c0d803100300c035219401d8108009281605001300040c18000b4040d142c11320039085061082c0707140010a0300c900c0c014025031866101000b810380c010940c02000703011a080801c2c41c14512001c040c1d0881d00075032040e500412203801681c07103541920120b40d0080c0b001c02d0060424103010300190f200c0244124220581d00002ca400340d100c204503130a022695441031119440e90303900ae0002c009610302100d00ca601c50442c91808078996019098490188100007012001d5a050301d2910014014041c19134002d19024a418403401d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 851737455 1250 851736205 851736211
    0x507030f0905040e01050a0e0a08071212020301080c0f010e01090b03190c2a031e091e0f080c1c06020d0c03270506070c050705030a03030212130b 64
    0x305021903103014500060320030741e000350880782d00145481c14010003440150001e034020080c1134000c1141415601880740c0300c00318a030024000034020880400011040c62041203e4100e030300d8160617000a00000c10240c0c1e1087e0311000300c507030104220352540e00c2d2401a40c0303031a18090070001d401501c01c1d80040e2800d00984030301101381d800880060903036003221100580030846168200200700c00c0030409444100c800039402c620080111380840b0000112802096058141e01d4082d586403484817000d9981c4c090b1002c500801190030780000b484900b5405940c121b08001e8140c00c0114148088400c48014643c0158016840302c40200402d0312504e81d0b2016072030503178204a00e009100d040090107403080380c440f056200d01d0700c8000744249a156001c0e0342544495542c0c0d451501c2107070103c5c500c00c01d4160025003190014808120351a02800720110018400c1e81951030160f0740b1000072381820042041640070039000a800f0030684600b114a585c080c0410440100400e000d8513a140390321002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 851738705 1250 851737455 851737457
    0x180102090d12032a0f05071a071803050304090c050c1e0c04051b07231018032015181c09050f0105041e0306060501090b0d02180303122401050703 64
    0x90f021011a41b09034215048070f0740107980300f200a000e500581404500071903610000801c030000381400b9070303400f680b40000c07660007400442c102400c0402040c000c0107141009014840200084a100b107002d018107003010b040c103410030001c3c04002038030608010340800524429450030042003200029202001c0c3d03040c083c4001c41d07032103003a51716100c40b1911034101120f18480e00074000e2108128000703140d001d400b2940c0c109109001c5640e801002413042caa2004010646542c800160303000c9110701d101000700010112017801021000b03103900002c042e9140d081e0f41803514089410980100090706003a40c0d03185400d03006c00e41c2c1140040c410328040c0203240c411801080041490381c418410b80e03029021400009021914842d954480d1500d43e03c022298141801c0c40000c4540c060b50407070f4110380e02c501d5401d182030701c8002d40780000c1d4040b100c0403902094800420000c1c0d10100301038082e024500144240d2400c10001c0c1814900800704488800c90f25500031203000e9034071030199100c0c1981 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 851739955 1250 851738705 851738717
    0x60908120d0b0f0603090304081b180709121109090f191703090d0306050f031005040f0b0408030406060509060d0f050c030d2d08180102090d12032a 65
    0x60103001403242030f0380460107a030180010050001d0628044001d00844041d4070032a07216541c82d8284101b41084041c0c0f0542c4000380c920b1b056032030040c00400315808041890700c10710713150705c4500c0400c50302c0b802c0000f9a0f83c01d0400200a0060909035a11078001c10100000d2016241d001e803100e545811000c0c1c2c19850140c440003000401c50b100130f8120200341304d09202d035103a250000085a8449040107080006400c0c0280000c40b030400b8072107000000d501a0103804a54160b24020002c0d0901070803c4a419402c04446000308002210850091744110307201550717800c15041c0103040d600035400c4184203c0221081c030034150b881e0b5100c40501640580c11400d1103d06007041c50800304203221301038050046807032007124260301000640d500341c4c0d02d032695140000c842240e400b030380100d9100400440c54900201d903008503459401c2c0e00c111450301c00580b601c01c00001040e40d04110610848482e000c030070040391003c0d058020400c0c00d0b1600460702d07000c0071100071104680c600f040d0114084c400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 851741205 1250 851739955 851739971
    0x180606011209020303040321080c091c0204182a150309050105040308100801021e070f080f0912010b0f04020a0e0a0b03070305180a03030231060908120d 67
    0xc25070b0400c2c1c4032290020142c0341c480d55241444a0440646125039542080c5050145c120a0140134824015070340040c00d41d041500c020240290101034012504001c0d104a80041c0169618011034010000301010342500e280d40e450300305035150b42e0030100301d01600b0b0500141003211200c2031010403210802c06020440343e400005400404007031780003415650a100400050640241205003c0e469002000b40156555140b95080740100c00d01c4686000381c440181d000192aa07015101e0503010340604030000d18259100840d9500800040042400c0801c02e040ca41c60b290301c0514000c18208000d00c0350700d48682c0081c4681210001c000d216960120342058610712079400d010120f50042d03c05001e40d5201c468101c030542088801800207410000003e00010b104010791881e405000020142070016a81c03d4001c2c1d0080303810b00310000c85400c001d00300c01000180d04c954890750b89005080315070621200500c42030594004101c2a803000f60101c0e1040c03039820444050460080d00012000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 851742455 1250 851741205 851741237
    0x8061c080426280b1824010e04051c0807030b12030706050405070f08060a050601180303080411060301031a093c1c0e22020306040f180b18060601 64
    0x2040c00c84000d050a009103040050843d40d001070b4001a003440022500103c03022172401b12441c0f03014001e500f0007200701004101e2881044500343e006841202034030b0303403074101c0d880321900b0401503a03071980007031101e005102080e03806205100c0e00050030f076000c180f1700c100460341d56030344e10070740318010500c40e50350700050300303003c4180700e0b02011303248028003495130310f80c0d9000290f0b42c2c5400781c60380c5041500d4000400c000b503000c6d07055021100204c100b041313101859900c0940e034a810041c800c0e81c44910400f00084503641d10002507000e5446610070b00356450301001030f801c0b0000d0052150040e503000c540840301c1c0010380c580780100500f01e00c50500665026082c0d002c1c04407241d10400341c4907c6201010300d035207801d0000e084a26039440d607403135008114010411881d0254103c6030030105c1072106079007008880316002568040d502520205000400d1b8104404a403c8140304112074000400003004110f0b0480307100d5004000c0600c3c0d902d0340311140b440c980d115000545420b040c0f020b0901c000075a6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 851743705 1250 851742455 851742523
    0x7290a0c0c090c0507140a020913060e1f0e0106080712020301061a0712050406050f0d0b0d2d0510020310030b100f05100c020108061c080426 62
    0x2d840104403c0c0000c6051200c06001a04a10400c44810a00711060950208001204221181c0040000e141a2905404203d032440c81403815500c460722085c080d0280c444c200000042c0c02e04800124401c9035123120308404552000329103000c980d05040301046064400540e007011b484005c07942142c2600c49100190060174030b075000038101401c4001e2443c41c6041d000282c0141030241c0c006034848034050104032098400e600441c400b1035403d10500c110303541640b000e083d11803482d21000958240003000180280c9048401312940c200325542c945d03034a0480d04041d10310782c1c4401c116a61410300760b91581e0310388564044000c03025a01000080404e04c2061400c0019501709213030101504107510b20f4030b101c1d115409a00056a4580400201810304115154040d030b001d40d03078614201203079401181e44c84000b402e455800740c4062450510000d81c5103032248114854690f2603a541d20b01481c000110000004001078008c2d40950882052004600ea80c0361200b0124425200090342c0880320700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 851744955 1250 851743705 851743709
    0x30a03181a04140a03050a0809060403050a050d02100b09040b10050604090b0a3204060b0f07020a0f030b0a0e2109090c0c0c010c060f0e07290a0c0c 65
    0x140860748508440404010020070030342d600c8481c0e06030410f0481060180b65001480010710310382c080070501d804030329001c000c0d20384103500500700752a1664a8a4141ca8109070440540b042d82200704c03080324443d010070504807215120141407010748005400140d080b0300042c009800c2951042c00100e010642c0100f10011f024000d11540d161a20b42401c030000308002c2c0c4090740607031080900412a80301860311115465903960150349990004000d000c1c03810500018182c00540f925004a10b16102c00301501445251a00f000d0320f40c011401041a110050340c4604000443c980052000c42d6031b902c107032075100c050340c02d0204a8501140c0b10f02c5c81d00c4040300c0b580318039000d0605034540403644000108174090040302d040109441d44a4003113035501c1000a038643c103900030340c40c040b40355010742c3c1d20740011f0380600c01c006504200c0040300c1003034075100341d00b182090708801000d1011903000140c81c804040304102c1045914841015601180b240800610920600000386001c00810b0050040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 851746205 1250 851744955 851744969
    0x1c02180a0f092a0906030614100c21030905010b0603040b061c02130906050604050c0a030e0a02130902010f050c0d0c0203100c02030406030c0512060108060109080601060c140606030a0318 82
    0x200103200f080d00140b1940b55405410300090514900054030f032100d5290790892a40102034110300c1c1140003058800050701801141d03800c10000c22644540c082c1001042040382c03945000c1290075181c80c195007103a40360180780748501720070f009102c0410a82d90760b080d409001502c0d040c001000408038410101d0031140300a5102c07805944111481c03400350080c1940500c140418440780d1120b00c01c10099135412a42c00040d80d070280108050107109400034409d240d503010030343e544907009802181c550501440f00007055130b25800c51308119640411244030341001d5141290500104040c0140c032a4445c0040c441002050500c550965406102c01480c000e07540742c0800c01301e2114031000e5100c2e000303846408046032904141c40300940c0a0021640300900c3c00c0d0042c0840d582d0b000040d20422009082c00d03040040d40180440c401e00c0c02c101c920302800c0c160300c40200c01c0b107062405080303405520101182d00d802c02c03c03d100141d100020300504655150401c09041c040d03180d03102e00201800d0780401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 851747455 1250 851746205 851746271
    0x9030f030a0b0a06110d03020d06170a14070f030f152306060c060c0d02130906140a0e04060c1412040b09060405030a030509031c02180a0f09 62
    0x4081c1e0304165010302034a24055a00f038040a80d2094103071000600c40c0c05284164000400b0b14001502c45d6008280d40d442d400400540a925202160b81800140d80d9a03041d0b0390208003450305002400c610403641100201c01080c1003420302c0401060642c2c01d10000303114101104050007000392144442203106003040042020703480880c40e80f0b170a0595801c2201d513206121011070001e00f0701c0c0d41100d01040c0f41c0401015240c40d01080314103a0341c040891340c0032403036082c400b00000c0b00300031003002e000327140341c15011400c5400d1820300150071480d0b10f085032285034101800c1190340c00f8003036030325800b64100c1000540c01044d400c09552090303401d081d16001c080700050890fa01800c0260303680c0941e002c0c410b107214039602c103c0700703554420050710041c00742d038418450420650301c02e40000f0b07405a00301c1c0559040806516182d004075000150038030043d600895180e2000c080c88040c038494540448a0111091400344001d040c0d5000d40030b0040000d0b00c4006400324034501011440414205000c0b003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 851748705 1250 851747455 851747461
    0xc031206120807020a090e03122203091503090c0501030504030306030b10081c02190c030204050106030c03051f30080406021002030603060f0717070801050a060903050a02060309030f03 81
    0x142d050762050000300c1c0300b0380301a0b801203100c1045d8031812030040d41c860000c43c9000214036480c07841c01c0d0001c05100071241c03851060440725955210071580c40c0e1181d1030300c24005003482e400e141c0030403805001c0b80405280071044000f06061080c0304040f12001c1c200001c1d992140c3c142203001c0d05040c0c00c0170344000312480030300c1901e03400a03a442c2c086840d2a070544440c1010000c210701c8048071250f01342c0040e0310210200325803542040a030701c1c0c481d100340001c180e002e94075408a130948800360300003000b203076076558894400c0d9094020b140d40106074416103621000f0b9203030300b00106180740c0500a1165444078401c030072a4070255000c25842c3e100002c144c4451054070381800c540e40140580b8005005e008a01c40d034140710342c000c0d6401104000d01815059461402d66401604014102c0080101c444402c0c4903182e00702c80103901441d03080da106291581040e090041100c10f6034001c800b0045440020030125201141c0b4112896040f03d000f6030300c1d2981e20f007040ca10b025030030056504a4000044c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 851749955 1250 851748705 851748713
    0x3090c100f141812100905060105120d020a030e0103020903030403060f150b0409110f0d05010e0601050406020705150702120a1a070219061815110a0c03120612 70
    0x400240d09a841000064072107000d00024000c1c001d00d041c8100078041d03d4066441e040c0500382a118500003110040ca0102c41000d00744c600405042c0e41c2600240b0042c0110305010030000b40318040703000109840101e0410003903441e01ea550001d0700b0070654052032040d980c4aa0100c07142824000c040340c0c1c4a03520717410a44010030403008019103662410404030341d11842204104115a0050741c0b080c2002d1a00d24003201904020740c200704429000c0001000e0030031028040c0c04180f00c180d0000561b5030505007991b149203c040c20144c14490140020002c0c50b1b40050f2440035604292090320415182c512130846c117000d06c5200035030051000c0030000d6207420008001030b00c94014651740d5009c001e00307d40c1c0c0039800e000b03441040060f001218207052104140c40042011445280001041d040e003022100b501c45001c1811a6042c00c0054554842c10241c040d0070501110002400d292184a00000d0b00d441a0050001c090180d140d1a40320a41101d500810044c00160210701c0307407507014a4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 851751205 1250 851749955 851749967
    0x1715030f0319080103021807090302040509031206042f0f0307050a030f2313020306071d0301020310050904050a21022104090209040b0604080d0909090302100203090c10 74
    0x60200300100c1018551200e9030301c51070030301381200e8003d00104000c4103c42c1288100301c100a10000034030001c007400000688603032248a11448010000c2c644400203d924494011b001031b000911803820450206a2600b103940000c80c910281c00c0d140d20780d0759a00700900868092050640c0c00040040108165540c0000040000b0398280c0c2d41000180c489114100442e1601d4121501c402d10b42c085903038a4411a6507400c0d000426034000317856168040c2e0009107004012120140000e181c1410407a02c2c1d14203042001e8070b95001c0b4004d41c11860b0040111402c60781c580318540c40340c2a600f020405008091041d515071641000403181c24545198920040000c1c000c5088014401c08110a10050a1440d1042c0c0702240101c0c40c0d14144c500507007540030350440c02c000b0342d1107079a840000c14a556584002d00050001c44c003d028440074002020f0407140d282d034020381a050414134a580065408201480c2c45c1e6200400141c417038444a01d41850b10001180f03040d002a484480002e100b60019 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 851752455 1250 851751205 851751217
    0x1060501120216080d020a0924050d091205040f050a0b0d020304020d06060f1d0709090b0a080a0c0e09030a0203070201120b120c030d0f09180b1e03010b101715030f03 73
    0x1b8075000c0340182e40c0e900140e2a240c2c04410195404500b50300080c2d2140f1800042c00841d081c112f000c558104d10f40c5440340f2203480c40c0040703004590001010002100c00c4843c401c0200000c032202d61220f460302c0e08100c40c504c150740303194030110750000020741190b958000003404141c03c40004c002c01629880310000300b80c882c1c054807118000318cc41084a2491a441c007501c02e0407542d03034a9900e50305e0541d02c4d07405000340c5194680e1080405a021814410412842100900030107804020707a261502e50101c943d03000c2c1c40b9000a030010050407800e00c0d00001200d02140d030a28000e00b44100080100008000d04a807040c0d20240d48502003900420000b048802200100d003038680e8592000c1090316122035840600f000303e11410340400510025031800c0c088011a0040800d10032440ba000400035040c0702d44100c06515500e0540d502070400b4441d00d4408a0b00f80c908080c8900d00084c0031f0402c40c001d101d14800380c1c2198002801c43c0d190b0000d2041d080001904403003041084986054a0350044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 851753705 1250 851752455 851752457
    0x40b130f08011a040c0f080c09100305150301020a091a0409050a0c02010c0503070c0b090a0503030c0c010e0705091f0b0c150a0c1e17130209060301060501120216080d020a 75
    0x15006648191909200d9100300c0a169102c4605540b2030900607560f41200608d86520b00405005000711030b12011a0100c2c0f800c400d035000a8240f03003106020300b9031204c1549407802603106122001031280c01c4810802070755030030819800b821500d2010404d6901c2541c010f401100d0030701042c040495040d4208000402460300240140340e0756407000c03aa207003c21140703540010329500ca20740c08181d000c203110303800c008000c040d1340e94003201e030722090b2a69100b40c0321012040c00004189221400a204007a00c081804028104440c640000910340d550003a011403901441c103400700c9101d920910f400300c002d04454002d1f90f1900c00401c0856240d1680e806101d5224600e40c0002c1c0b849030040c4200008401e0f00e4881c081103c814413180d8000c00c1480c00a201405401d24820080011100045100d0411400007084400f01d42c414400f40070000350080e402030b81170031014000790382c11181c151803c0c3c126240058980c40094028840500da01101406507440000e84030711880880c2c004100c10308103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 851754955 1250 851753705 851753741
    0x48021e090f0a092f040b06031902072a121a060102011e0506011403060303042c090a0629040b0a1d040b0f01240e09190b011103040b130f0801 62
    0x6010f0910054816032500a03602c181c04100040300607100ca498807108894081c1c0c018103040950f40c0b44443310900460021002544164000342c0e04038004541003e405c2c8443e0360890b40446540c0c481078984005041c12005040000044480c0d2007580a80514288904c900b10f01507028100c0c6001400300b660202c1c00204100f03000c840c0e000c114401c480c0035a0700900110b150a190080d80d106550b22030b00300d080000e405403454045040450b81e064040c1c101d50014142200181c50500c1c21600007100a00b90155940300c0a0b031010800d00b40400e458405440c0410b035440b0034400a151034105400c04104000c03807072071105c02c261a03058150b100703511031400c1924503141e2000c1008282030900c104110b2406010b00c40541075440c021040d01a002410281c91310214100000e040140480d002075a19103088030b0740c1981c907800d000d01070300540282001c1d4486099140516124421405640115000099060412484900448000c01243c0350514040d40c41d000d00c54040c0c20303584000c00800311 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 851756205 1250 851754955 851755043
    0x6070905090c070201020703200a090c182d2102030d0c050a08070602131205060123010804050708011b020d020c0148021e090f0a09 58
    0x3001e1088900081c4c0580041505074695565400e070124000001911a240c0384030745281b5071a5507030b51002801a070b43c0d02049100306114014001c030703514280c001001132045003c1100c04c0072a1000f118981c841034004032242c107400d806004940f020b62002c40760400000112062100c00004005174070310172001d0700c812003142d50702121034108200c406009a0000903480f400902048001e003a11882254054100524000290061440c0368400e9070b61000c2d46642508101082c80316601501d616035600e0000b0301054488083e080c8001d1015052024200220b0207010007082031400514201c0024000b45901e90030980301d0a4500222101504c50594400481400420311144030181a55890702442400c012140d0481c001c940c02d0352000c881180581844035480180070803a01c511080380004ca03154418000b128950000d40310740d00388000001007007640ca1910050700000017810380802d54482c040000300034403811600500303000b2007400c1e820072080c0c1c10300d5240c244e80340c0c4102140846 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 851757455 1250 851756205 851756221
    0x1081503241006080f15130501140d030e04020a05040305060106090807060807020d050912060c031e040209060d1b151101022b06120602130b131211030607090509 71
    0x40001e000f403402064641c800240000c450031001540411001050311003000c044c2c02044400c09070302c40820629449800600070228200103c40704140282d64104009000c1d0310000c0c444403235055018401d83d00001c4001000344500141d602658021060341e02031b581d1158042c10344651445080450301a1410008000340600c0c4403030700c1380c05150080d000b030600c403050442d0719034003a00c25a680a0303091400200c00c0141002150b2040d00690f600c2036582c10f04014032070300351203010145142d00100804000058445064854000506035152074038800585407240c0a50700b4085404085071550b200040c104000304840c07200d940c01da407910008003807140c4004e0700340c1c4180c004a03420035001c41c0031020007042141510300400c503000000550300340ca0f100b520324418816002036447d00d4010a0310610b11000b08041001000c2000341603182504945181a030320400340304c0c002088140c84003540512a04e07840166500d40c00505503080d916182c90050319900c0e0500466029085820000e800c0d2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 851758705 1250 851757455 851757481
    0x3150603130339020d20120a05120c03040e0c0d050a110a120213090b040c081b0c012a140c030403140309030a03020a0b0f150108150324 60
    0x426081000000b648039000b45121480400c100d08070f0300700140103955804141c41a4205140340520b4090300d0001c0d85410030400c40101d07d80350107816400034400d0000183d000a142101c0841c513100540d03e581112032414210b008950002035105086010400300f050203400814004070100d404000e1526070b001a403084800c5000b03401c0c91601c080000c041000d000b4130304ae42d054540c1c83c4c0054948500120b81c1c00a80c5200e9001e0f0344240e45620103071050346810300071401010500e107040403480c030308130151980e0500c0403a24a4140312000803c541d03151007e401c60b1503c2300d00010f401089112860281c601c0304082240100052510544d00c903040381d1800845035200e07500c4000b541440c3c2107032078401000040100070282840100710020803510180652840e42c1e010707070042c003448003107814012550003004041d02d056090120401c000c641400740120341c2c0c248286465500359554094103c0d80940c2d48282e1980340c841c09403907034800840029800d04820f2190314803405612540c5c45442c2d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 851759955 1250 851758705 851758757
    0x41a041d010315240602030405040f0c0801031b05041103040b0a06050f040f09051002040e090c011b0305130e160c080904050c190201060f06020f12031506031303 71
    0x3d002e4803805207000716440760440d281c15519101203110b0f2019102424851000d0b5038004c001603000454100144e182c00e205228a82e44d08113000e0050900940c4001c01c48801400010440d6071042d0013210710703e416644620191001600400c0344940380c940688454004990407a80540310000064401e07440d400f400044890107400c604020520004200141c0110216810136950f102c8105012920401045000900807140140c0c0c135030030408a42d11641707009140c40025400300c034607040143da0090340007200c44000c19110700c0d1440c29103421116031241d00034402000100c00b20100b40810b4038666a801003041c090104681e0b0720b003500c150340c1070281c42c20103881d512003401090350700d04194200c0341d400303d20300050b0752415807404c6100030700494a00c15031006070755644040c050b04000e9140d41d0b003d042d10b40001d00924500e5410035659901c1d055032903220300710100204580080d55520a1001880103059a850f4a0f0100c80110000107000e030580010303a074200c803442e80310642c81038504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 851761205 1250 851759955 851759963
    0x270105070c091109030a080c2e02030a111b010612020a090f1b05120c070f110f03030c161d0406110721090b03100e0c041a041d0103 58
    0x81d100e803800400400800701c1d21140808040b041044d80c005035024044103880c18401d1081d6a00d90b2000d022117407800c1e0b0300481042c203003070722180406102120340c89a0400c0c01021800581d8964411500a001d0016482213403480903008c5282c2040c000750082c0401107210700f0008004607607540c20185038003051141c01075004015401e0900100d0a1500100ea9102400d400801c0300110b03000c22440380089036102100040380400d1705414207070705075444c03a0850981c07000c007400c015144d103400000080100340201014507055541815440704410042d27070f0607008080d41d0f142e24408802e1601d403c0d980810281d241a800000704042d020b040034852440700845490045540340e0b50313071800600340030440040090082c042c800010340d501035041e2840031042d030495844450340d100980300d924180c10a501d465400d200f0001b9666811101c142120400801801c40b0345402079415a0345c4502e411501c0f038207148030603c50768a880e1313a0050040750581440004240c001d4be92800e40e40d0000c1c08018 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 851762455 1250 851761205 851761223
    0x1080903181e0303040b071115030c2a0a14010624121506020105070f0807180308030c03010512070602070504110d060f14030304030b040210110327010507 68
    0x21103a402c140103014200c42c41c2c0c01c00094000b841100091444e0055440800c0d44600081c20b0300070840c03041500d64604005a446184c00b0b82d910101100b1404010112451840301140007019072102081d003040f01c80c05002e40c0040c2c0d400710300c8041d8071200f035120155a0140e8201c14940511014459501220400b440b45103030304005600700b20040c518104a0420861000740ca0414590325100d1462080c01075189030050500d0900c01909541e80140300c5420300ca03000fa81d2141d0749401110f5244d1010941c9080c000c15180c070491550369003099003000c0c0800201100700b050b1107224500642c141c80e011142030911141262069079208214001c02e40140c10418081000d42419000382104402c1220700c24249a400c0c184041264100d034401100030494040410919030b50120700a81c500041d40914500350039a121240040000703400207004000d0b006907030302c5040c4541e84894072040504142c940e14030707840360003d50144108480391840000300108130701c15800f990840d4080c1d684081c0386 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 851763705 1250 851762455 851762497
    0x809011d091b040b0a020a03080a051e10080a0f111f0513171c03020f0304020603131406070801060915140904020705010212061519030b0d050c01080903 67
    0x44480d0b02c03041c454400c80c88051001090000001d400303841c24500540c0200301003109810000c003078030b0340a400c0c1094645403000381b2141400c1443e40044400c0594000c81c050303101c640c408050800d5503805003005000702980003080005510507610018000c9282089105040c0f0801001c02c05040814a92400361074030321100500403c050020350715010244030225994141c503514805004040c0d1045400030505035031003184481903810390380010724045041c400f007128040f440d448060b0006c0c0c81103074040002542c0c50103178400511019448610314500a245030030103079845009903070316800700b01500008075259204d0a02c240031101c28101c5041d0080c1412020340c0c0d20001d000380d00d00300320400c104a070116100c500041540c2c5205200051340c0782402001c0030000d04000c2c0589101d40400b54000041c0c07918842654508070704c0840d482c8400801500c207800401100001d19044804081918180700d0003196072201c882c400e0321005050356130004447d44a1040c202003802031f200c0042d036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 851764955 1250 851763705 851763721
    0x1217121b0d020a0305150a080d0c0302010b150a0807030b0f06090d21030f140a1532030307120813060c0306090510050a0b071a1f080a03080105010309060212040809011d09 75
    0x68030342802f80c000040c10340020000702d9550246180001041940000e94001c20b55200300c529520016903d0100710f000c16240000d86100042c0f820b02e489008040381a50320350352032900030350304d10b544190b11403c2d05007181d01000341c1c4007900c0b41000201c1c2c601428a6402e4580d80101021100e2591400e0000d03a100044600203145038001e111206100c008080368007041c9502a84102108849940c1204c85076640300ca0091490380d4110b001e0740003406440d0010380110300c6400010003030b00f4203070200c0d903810301e004210740c48110b4050314541c01d0211121016405602040a03030b4014003051256580f901c42000f8040441e120b1950059800703201008840302110107050280e20450902c020310384050221120640f0690300d4140d03035026039043c9c0c00f18180c0005040010038080300640340b807074800e0720f024100450510499040c16100e96440040180030f0b81141c100311071007001d00001e4185801c3c42c2c002c0790454918a800b061424520141b14180e10701d0380c40508030003c0071240d0554a61076 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 851766205 1250 851764955 851764967
    0xa051c14041215050906220503071e0f110405010909052a09040605180d05121902070c030b060a14040908131217121b0d020a0305150a080d 61
    0xc240c0c1c0340c400f2415280205801c07070007010b02a81c030503002450b060415004070725180185020550501c013428034008002200402a9401d00381c000c040040e004d003400014216940202c0e1008003007111a680329001c00c9403c500b0a0ba2f814829201000542c3c1c84100040403034914100151035a8069502983d80446002080c04030600c0d400b480c3c071064441001283c0c440750141c0f0110f80064030340b01000103120060000008516200c001844151150100070f4240e11589c1d507041c1003203120304005000410b40c1d203480240c0c01ca140104542d07520701070410a103542154001125072660a00103e000e51800c03099220070380320307640071401c1800103000401000f0054180200c41400b020700072100ca4107480a5078000501d180581117100143d5813503c0c003400c070208001582a14400d0299101410000c68000da0004090b0300041e510302041042d04a02e0103028000380e006800020043e00299050308a54024020003142c1c4c0030f47c015042c104030f54030721079005000c031a0b8440e0043c010342c00e104035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 851767455 1250 851766205 851766239
    0x10219050102090a0801140c070305040e0919050f010509160509180d08042108041e0803150103060b3a022802010606020303011509080a051c1404 64
    0x10005180003d150b0102d00c01c1c00c2590f110040700c2c1d558001740201500d04512041d0b000c0e000e100824030303103500e645e8083d045014600601230640070b0a8001050003104110200070107180e0702c3c4d00d006e80c0110340b401558443e110722022100c0c1d401c12000ca85c501c034000a208105c455445803016245080c0820301c04101401401c9044041d00c944400b4410101031086200714a030941c0c03103e030305150a01b00340403042e440d98000a500005c000035000708660001110b030b04590700c4410400352061804082040014050010303125500000c11300c10103006003101c2e443d40a400382c03814804603583c1c0c0f80748402409802880d02c001e061640030103418441d1000341c02080c80c40b4880924041e450b070002e0b40100d030045d001c40010603080c0001400038044440c031030f8209004500c000c0c8201c50070040000e40b03c1c0818410701820840860001c0c2c04030740070b9100300000e401050102c46060303c940c03e20b6a030b0307805400d03000308405210140e802d05292191400c69640340e0f1034010079241c41d107014840e00000d6144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 851768705 1250 851767455 851767463
    0x306180609070e04020708041502070f05130c0509031c0e091005040c0207120c0303030b040209031209010c050615040e0d0207050f010e091008010608010c0c1b0b0c061e0402010219 79
    0xc00c0b8070000150320324080c0000e02149e81d40e4803500c20342c00c84060310b44aa20b0304070b003c0d0791090040400940e550b0615540e0030ac0d609801c082110741c101d00303040e80c0d24081c0403000c030341c1402070003d03e00009402c2964080003031800d9a8012036170240e041480300851055503d00380050094600380036604042c0c010004640d041d1045514007560b0b0041081380140101044512400403801002410341c54014485401001c4808514003083c00340000e80c1c5601c20010b07407200880200e48100380e68015445e00c40480d80090545016150001754000c0000e203500c0b0703c070311039460711a810800d01d030001400d000c0b00506400500190b0b05103070030480c1c000c95510b4001e0401c01c0c0040306c01c1840e150803619900892141e031003401c41c28104200c960035542c0d582c108040c02d038908071020500b968480f1940b503500d60071500003581c01000610382071050b0302c1e0380c001032080c03040014104801000011034074420340002c4902c052100e642c4444954820068030042c3c010381c030030340b9015101d9135496a00000d103031203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 851769955 1250 851768705 851768707
    0xf040201120e0a020f0105160317160804020d061808120703051b13030804061e2c061b0604030e0306010b03270d120605060313350306180609070e0402 66
    0x32520b2010741148c0901c108030001903549608030b8040c1c090304020303900840d86c0751030b1120000c01100c005118140060000e40b04051500c425803e1100d40d2780180340c0200c00c0404400d50a81505000c51140c0c0301122082c2c0120890000414292092068078003c40c140000c50600c1c82c0b04030036280103a00b180c80c03441140c1d10381940000024483e0401040100a40d491702c0c18000101501d006d12886c6c001078800c103108900046152564642c08454400300040700e00c4c528210104010419601400550001201040c4034228a141001548501c110720030f54601c2d07601001c420a0545401c2c080c8980001c008003400401c1040400108a144140c841e1450101c0e07410080015882e04140e20719030070100c1c61041c90501c038400c960049401074007059611901d542804084008180f00490001d492340d214503200102e44000282801040110b03003040349448410043c10021540c4291884ca110f5088115501c085009a079070701071281030000d0440c10f0756a52002d084d079110301c007880c2682d40198 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 851771205 1250 851769955 851769967
    0x190203150a1503060911030d090603091a0705070b2503050405030c0106030c050a0603150510020a0f03030614010309051e0c060f19211e050f040201120e0a020f0105 72
    0x1c01440c030b10011805460007040407041400c160350828080104203020383c0108501d0720102c0d4100452408940b16460006079207004c6041c58000d00e60100c1800380c80600250a12010a5212001e41000c42c05100007500315110807000b904160388040000c60011182040e400049009034003807a441030160303050728030301404c1184440c02c40e84560000c4603680e0002006208a0500c00072050151201e03040c01c0021840c5042168075194803032090511855170b032040442e88920074403050322003540c0603210805032510743c500580a800755025533a4550400120510340e50303ca80211450346401c0710181c05202d01e0402d450034105980c0b940741003103225845030215641c599000030710b10743c06942c0c0d059417941d5a07980d0120341c03080918944d00c104141d000b00c42e104d0300d20280710142e00c4c145480c0b0000f000f04000b002108007a0101220f41d804d40e1910382046250700305010a144100e1003680d4160740d905031409440700320b45242c2907986442c0d10141c5800300508100216400c254414104181040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 851772455 1250 851771205 851771231
    0x3040c030206070507140109030309050d050307170a020d051213050c030d08060414090706030c141902010b150f1b0303130b0705090904060c21090203190203150a 71
    0x3c1d01c0440100e40650283c0030070000403d480c0f01301c2e07000900910340b0106162564070020114007842c0503442c491603100d040c0b0404c0240410460f6059640000c91010207500040ca840007604440641c0340503010300d440d500d4640b8450000c81e08900403041c0b0010458880348010783c2880c0750b45a049400788503501d4006c0b5595010850484000300079600e00d002c5181040c14002907070700c40c000e01500c1320948028082090808a001802c0e5086071900144c2d00100e540101c4460011341d10ba180c44880004044410310502c641e810140c504d41d80007401451240c000b444030f0307101e0810080140c902c1c2445801c800d250304000408501e00c040300b0000c400075820070780e81d083d41e109540c1ca06640d40c0c880c01e24010460303110103203544440346003401070400710003002185820ba40104001d00311544c0d1020481894003e242001c40f00040740380b007600328548104844014807082000383c0c0f0900c07480d0400c0f40400c0c2054641008950b024000d0b00041140b91000e54000a025141d07503610703901e0f05000e02e500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 851773705 1250 851772455 851772457
    0x6030602030907051e0a030816020d030c120e060d1d1501080607020d083423040f0b1c020d0614010c020a0501180e2707140603040c030206 61
    0x8010500103002c80310710700010401da80107501d110005c180300301d40d422a004e64071001040c0480381c101e5a03003690340c115004645050003504a00a600403103a06040c401c2c542d01424151445104000510306248070070801d445420303801c0c150303075801a820003c03054500745035080342d200d045085668699070307101ba102450403c04251740d12050320440c40e0040180050810045410080398005402e4110301c0c244c0052154100508500040150100c0300364000424500019a00b180d003002403081c5a400c440103210b45000080108280c120548151229886c00c08403000c8421165503480c515150004180d01500031240c405d07080d03406030340b501d80f400516000801c01070182d03990010380d00e400c1c03036502c0b002d0500c4001941d04024002c80d00c0001a1502d01c5043c040e1796090030100c148481094944d81e80e103000750000c3e688100c0303000501001484100c07841c0e0300120140345010100802d00c02c0b0341d44d0307020580700b6550441c4640c600400300d030400074001c1d90490b0140100b010111348075004070300300d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 851774955 1250 851773705 851773711
    0xa03060513020a0605030705270301091a07110705300a021804021c0804120803151507030806010207031a060102061008030d0b0301090204090308010314030406080c0a02010603060203 80
    0x21007000241c0d8046151049108010304260b05002c1e0460500f0768005040e03008001029079298590180c0c03851004041039085a8120b00034020b01c10354186180207a10348081ca0f00310000c5100920200d0151801001c104c03400c00b40700c90042540790702c7c003402c00229002102d0042d0000c074401c2c1441000700d01179070180b03100c213403520024510003441e84180711101301016009003290141800784801030ba00e85d01c0710451041144543d8070140c06c80c2c01c0c070340c54a06c11503210101e82d0307050505010810503100051449004980b120b40b0520766000103000d81c2d141c003210380f4000701104002080c002406002c0c255001031040c8100c0d0340490b00c80c2d8401e8491409946013542150f00c4808204c1a0340c0c2c100481c80c2d220419050001e1810301c2c0c4004180e807400313000e80714000d803500d542c00d009898409600010000780c00074024000101d083c11b01901e00c0d6403c0c0400d445200c5041c0c1c98a00b040b44c0007040307408983d15661030700d466548040e030000c1304e0b07000501d680c030840d526480c0c00008200e490008d940 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 851776205 1250 851774955 851774971
    0x2304080d0c090e07080f1f0509010f1802030405060402130e030f03090631030509041d060f1303200a05010608100e0d08060d050a15050601030b09060f0a030605 70
    0x50a83d06080c0c0810240030018203240400c0029000c00003181007000c4590341000081490002c4031000340c0d40c1c02010302c000d400a9400c41d8079140005420194140204201d0b03203003840005c0c1180c0451340304426403004950151580d48000081401420044a80300500d6650240040d00305061500f450a45c2e015840c030b55001e0342c011051180440d014007a45422000022084904208103c10a003007609941e80950341c0200307240c8100705060184080310000c4000910410010624008825040904e01c454000c070303120702c01c00110080e103407500880c092061452403000c40308007a80d0440d5041921450784140440028440208000401c4058041b0b03110710300200b076603414103858500c0d1040c091075405240c2c1c10124841c04442c0d02040c0d150301d50a40b13103003850032a1b4a170804a03525420f5464020070500c111401001031010b1030f0100ca0117402144014006512030f4070046058070840115180d00100c8100814203034903003000400039aa2002d4194a55a1703501d072942c07811101c013118810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 851777455 1250 851776205 851776217
    0x1030f0b06031c08040210180b03100807080a03020d0f0503160c02090a090501150f03060f0b030a05010b041406030316020316030f020906150d0203040f0c0b0d0e012304080d0c 77
    0x88118500082e20200ca481c440c0f411003202d542d0000b40d0700009500e8400c1662704040040030601905560703642d10043d1802001f01d50309690395403903040c0c0e9401040302c141e0050040c01c058502a40c403480e051100c5250b542d48036400c1d610f446120300c80b0810784c49103c0c01444081411039006031903e010303040c0300f1010f140c800102041141401402e5030144035400c0707081d00c05024240b280480815010b403d0700d400c400001766900454400c0c0300141320941c00c2c030398148103105088080000c1500f0030307048464280d40c00e200b010808061b5650014040d5040c6a00d5002480400302c0c002580c0e600042c3c2e03500041c00c48201c00c42031081040440d6450300107a44400f03072003000342c0070750909010f42904103000790b0701c10441042042010b00d4500036080020151500000844c043c42130380381d0602e4405400130704402c0560341d00c41458016600468400c4a01d6060441c0b1118109040c4103070510350081141ca00e8040e450001134070041c2800034400c4030802024081c3c203040b11141d02c07801e9116a0301d07465203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 851778705 1250 851777455 851777461
    0x3110a0b070e030c121b030114040b0403030608060c0406080702120301090e010b03061510020c1f0315030b070e011b0f021504031115070b07052101030f0b06031c08 72
    0x12504013116258510702450b4440580f660025000541101000c801402d0321489000e400010380500844a0403c185c1c411200600003405003441040740100d103e43c400b00051583c40c0c001c142c68140444141103292800d11007081042d0040781d010340c0c8a01c00e4170507210240c2a0302c09480280d0400c1e0060b04489075208545080e90409104440c80400200c006045501d002c040708560b00d4094024507000d001982d201d910301d10700030800000190401072a11908113540b90218103ccc14100411400103070601c0040710b01480d01111319000c1c7c0340c00c00088082ea9868030f2060b607542459250f807504010908411505000c40c540d68428130910402036521455200d0040100310030304060102c0b101001000108001003600302500e9481c50f041c1c4140f80f6030080f824445000b80141400a002070b07104504000c01564410010080014038030f4800c401c29110707444420305c159013400024488601c8a01c0c01010807001c110302d80c0e000500604466050001e01e04824030000280f1011012030060380074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 851779955 1250 851778705 851778709
    0x60f0f0509100b0f0d14070f051204030503060d0203030706020a140f030402040b0f03010e0706090b04080304050910050d0501020a0e0603160804020102013b0309030a03110a0b070e 79
    0x624009000c112010800c0e82081c00034150841100d100d0241c107010002060302400403658140d6540191070003040100f155160403064100004658600025070044021072a16000360b003034401c4e080d4910300018617941ca9950950b080ea0029100700d902ca040c3c0720200c1d006076410802481b10511406000d61155440c2d0700c085c6c4a248030405860150f0410310400c80950302c00c20031780754442d80480d0041a845000d80228000c03c40b010032460b059401d003110780c07840304000948101140d480b60b0b01d80d0585a600c20b4000b000d40500d014045190300100020080c0d4a440190150086554580c0c680e8440ea03c0300050740341088082c040f19265008200401041d0f0421a04425a1000d0b29900d2441c074108040341c1064807040c40000038018070201041c00c0da4802d6000e00640c0300c0c0c0c08030b20000c2800300d10215200b80291142070142007100d035031800c1c04000220a032688800c015000340490b603a29030b001c2c1c0d1108611070034084a449031a0821020641c150700f0700f40141d110b511030003c01d80302042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 851781205 1250 851779955 851779979
    0x6121e0609030702060d0f0f02030f09120a0905010e150c0f060112021f110706020c0f0a1410022e0c0306030506010513090f0b0709150c060903050d060f 67
    0x101c0000b50000e2003a000075032298412900380f011300c1c41c000140c10440745030303240041100a03960b1114510204c20031008015561045024890170403c503120300c0f080216120451280000450008087c50340801079075025650000ca14080101a02e07689010a000311501c2e820460801ca201d900162011442100c240a4580503010346040c28001604075004141e080c100401c420302c0316000381d00ca07403070000d00c507203903003090303040c180b41658001942d0b150020350300c05504003d64861a40c000c5042d0080c50a0560041241d10069869000c0801501080741c841c42404108055009030702124a04403103d903218403c48107102100002c003000c1c102c40004449202409000380361130200180003150740010030b00c0c1198021180c036643e07141e410b050030000d802d200000070445101c22480004000c0460109407240c08290388104032240e54040506130341c2040104000442d21104102e4003060440d00942c600b24002c0c2401c0b458400c6804800084a200303074884c0c109103442003000d05c29a12862 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 851782455 1250 851781205 851781211
    0x2030f0303270c100516120207081b090a20040609030b010602060415020306060d02030c0904141e2d100f0b180103060312030e011805100506121e06 65
    0x2c00a014010051001c11000a220004101403145c0450b013283c13840304a45081d02d60680c040c0303000c0382e42442107501a40d940c0c9903010342c3c0c0c65800342d0b0040401480c50490011240d0170010080c608a0311113541800c014154488080e28101c0020447c1c0c0241d0302d4100240300624a9139075402a02d031460402040512040e0410011074000005100102d0307030b81000c40321581e805003001650f03034403140006402446003a2003550464004010449401d40460217818200e0042d0740501101c029101941ea40e070b041110308448190106509010009880c0c040f0f5034401501108079001c1d030364000c0301034840c03511420101d150000803010801c40180d59040301e0000c2150722591424142000c0c030340d407a54004c95402c0302c4454807005030303116507a100b40c00c42001103400507403c10505403c074400030003400ca68400c80700650f0030b2000750203034007400b001d10030345441e0450301400100d20f401070504094100a062642d2041d084030301307101240300900420103c081c0c01d82d64250b20614401c040c60510f5401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 851783705 1250 851782455 851782531
    0x405060609040b0f180a21020111190c0602030c19090515130e190b100e0622170f06041211150a0c17061c02030f0303 52
    0x14000002c1900054580180d10000300740c104d030b6200c142080780000e260020350400e10a040c0100c06000b0045251902010030038041c0c40a004080d105070b082e1800361612048640040040c030300758000c00b03035120a01071100d10380304985603201c0d101c28050380c1042c0d4442c5680f03000000c1c45c2c966180c40c1c0c0303145175500085040c023021143c58000003510600c00800c0010301200005180487d01a10020b2a0b003d00550400040079082001004190303c1c810708402c0d07103862070048844814503114076103001c5450103030340340c080704c8100405000d01c9803c80d0040c07802200350401084000702c0408210405480400752418060404072546072a0000e405007008154114006200100f0160a12030b0700c08c200341c2c104040c04107665a01c007813a100c42d955003090010030360030a1000c2000c80d40c0154400500507500c0030003d4954029506080700280c0e01640d01c40c101001c2c0301441c8401c1f802146205000400b0344188000070f032042401d6610456800000040031040d11080401b41c80d204000380c000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 851784955 1250 851783705 851783719
    0x91401080c010f0c1505040302190c1701020d0903180f050f06030c04030f08120702060610030f020c0a06020c01051602060a1a10021e0309060708090103150e04050606 73
    0x14100140d0348410180311a0350410205501207048680600351007603403640d11071544d0004105c0f1880684c014402620110014001c4d0140100013994003248200c1958009100d0400f992419114200c840086441c240c1c480d5000d0108020301a032701e104190240e4060b071148050311641a0307514895a203c2d400055043e03e100009010030340321548100c540c03d41c00e490990f6251540840031110b8022a80700501104c0c40c00c94420400c80c40501400e03501c03181c11180a0240c0f541d9100741d88440c0100c607a650050380080e8062040d500c2074100c29468040c0040051421030100d1000b800c00071409025a0507a8000880c607001c91024820070703500c00200e45100b000003100c100002c0d210076010300404442900d411070603060780030240c8040500320005080c0d42c00300c1801c0e203000c0d4a40190300d201e15110500491070040306000403044901e003200003402103140c040b59549603041ca402900b003d40c100341da41c8059028003980001d1040c05090044107101241c035062600300d20f400e6008090070b0103088 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 851786205 1250 851784955 851784959
    0x30a08010e0601170105040b040e0717060a0c0f0e06041502060612012f090604122003030702090a06080a26090a030b060f09070909060f0b030417040b0f0301091401 72
    0x18104c0315064400c1124045444a40000000c0142100c600c5001c40e9011f03900b40003071200708100b1100d80d0810b404080d54000da40301859401207900300c0310a6400b01c2c030404040c17240b442c41480740d02032034640104042d051075115080d907040255001034050160b070221061040074540380d00100c580300003883c001d101170002c0d9034014907810900404403160851244400f90010b80b0742c070039102d40d128050070554035a0740d200210024110340c20000c2c0e034161844100043d00041502224400310006401185040c2c5640d0034000030000050005142c01e03aa40c0c0c000c5105c25040c000d4072415400b1361515003022114489086400c40b8022514000500800561000b621600040b00c1225000340e02c0100c0c5659030300219043d0000b210145034840a4101005900f50f0010741000666601c504100b044948410101c02101c1490240ccc8055420074800140062035000e25144c9202ca030001d07a80c00e050b940c140e00c07146a0001a034001c0d070b034800880140303c60f401c50302c902d405414410040c0e1040f54 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 851787455 1250 851786205 851786237
    0xc06050718090c1715031209040b1203190c02030d020606281205150103141005040213051f0b0d0509010506130b0424090e03070804091d030a08010e0601 67
    0x8113501ca406114140e1800c001401901c42d2910400e100c80f01030141c81000011100000513a406030070000d1040e45000054a1181007007880e80000c8480b45005514000b03807444090031404507003e51700200840700070f01c900161014007800d1840510380d0010400b81c00c0860800c820700401020141e03520b01100780d03044104070300403806d004450445c1c00080007008507041c103d00b404602d00d20721603c98001000002082100c404009403904c0900684504030480e0781c0c240c081c1c0f20141c0e0040d6019824021810f40c9408541c0700c00c1d0004001d88000d01e1a1010a051103c804050703400210707030b50004140398408403018058180e104c24100c000b00a1860310304002000b401c2e20b06484441d144d940c0d2100381070f5468a44c81880b4444640411401e4084040490050051a8001c142140303080000d42003070003800000b96207056900c0201c06091074103290481c4d004191002006c010000310303c4c1d00040c6004140001c090901b001d9584460540c108014541d11810280c2403904201c4000b070614501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 851788705 1250 851787455 851787467
    0x30b09040b04020f1f09060e0109081e0c0a08010c030c0f020d0c0c0f1707060306030f0b070507140a0b01170307060e211801030b06040e070c06050718090c 68
    0x36504a40c81502d041468000c1000304005450405c401c0c21100c12045050b5000f44601e4100da04990312522140d40103001141c01d8000e62250031400d510510303c2006856400c1c000c8501d00c40060100e44e00d0701c48032400036081d80303c550303c9200701ea50342d82021190654140600b4012600f04e041a2001805440c0000d42c2d500c16204680b080001805202c400c0001100702d960091001d4440c000345e807134031503503841000c4070400303e070040600c0b4031240015480d001c1c1c06401e040b01c2c0c0110001d8003401c41d40d00c5003a20080010714000c1000700400988000a00f080d03900360010880f03030000c010100b054507104000400680204541c06003600840c03c00321800801c486840d80d00010105e980581c0c0041c1d20302e8030424181c00603150b60640c407059442c030400400740c00b0100440c004c514101c2c0d4040015030407615100405504040204010f20016640707070304d00c5400042070b14180016800540758001260000d17075101000414103111031092886201140000d40b0b0b9001041001c2030880c2c03009800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 851789955 1250 851788705 851788711
    0x10b1c061401030e012c0f150c0705030c06040606090b010e03032203080706140c1908041a162312061c030f0306140a090209120f03040501030b09040b 66
    0x10181c42d080704004c6080300790010b40385da80a00c240314030300103004102210b41889200b8040258498048403408002000519170300031003d24048000980f1007240b0020a40e10540055503070388401c110701140c19001f00080c82c41240110300020301c6a0401c01600c0a482440303918074100100a43c2440541e83c0100484032900144201e409a0003400c4c5400c0030800390070342c00580f480c4801f050440900c5119009000d00398080c1e4401c3d44139035601c0c0c0700e41da054007400c40d01c080d54001060990081c00d02070041c0e079170400e005801020b5040340f6802c030103880380c4045030b000e070b158104840700d01c3c00542c001080381c0c6a0303060f00740a10340c404c42d17200040c0c040340180084034440300c01442c0403400d25210403d81c90902c90309101014144a02410081c1c030b02080e070945c00000038a45680024000004600c4228030500285045c5d030032423500d2115006500807041503030740a21310001e03030042d00c13402300441280c0803440c601440d2240d00d0f080024017120f800251031070081d00c21008100003d1840040742d54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 851791205 1250 851789955 851789957
    0x3070c170607050c07030507090b0907080f01030803041e11030c011409090a020c100902010e0a0509070f02010b0402040e0f0609061302030901090231110405120c030105010b1c061401 80
    0xa00e86120707000c0c4da440c20000d61300191041c000e213075021403051402c0d0040807a8410648000540da1104003040301c1544088410304100d0002800510000d240c6034011504030f070107480031b000154000341c9090283c250102c02200d1f2207050700310710a07480c10300348040d03180c0201c2400c004071000385424072010703d0704c2980d0b10700b07200e500d44000080038101c090341130f0785400070810102c403072010f1015015030043c012800700364041591143d0710525482d00748000b1060362405003800070661506042076686540080f460015552500d0441070591958400342c4020000181081034a0070880c0918658000c050071003801900c0e00d0041103078948450811858108500380016070f25611404c441e8010850094003c1d4041280c00c0c8003400c241c00c0c4503502c000340343c2524018068681807041d8208880402e60100e45414040c8800c01081c942840400b001c01c4854054412084107000060700310340b001d80201c1c00c0039102040c070258a03102031001c00307154200c002d0100a41800d04911001d5400d031400594 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 851792455 1250 851791205 851791207
    0x6050907120f140102070803010f050616020d0f171305030f030f0c07030b0112060f0b1e130f140a1404060518010501030302030406110a0c0b072303070c17060705 71
    0x802030060f1942c00450040c1000319221001031402d00e82c103601c02c2c40b51104442003031002181130300e0100304a40310104050b03401101400141d0901100381b0300c200060311540b600c8845a00800c40c1101544102401d034450641c0d00d80b840302070a0034165568008030b0080d0b0060b84001052203000044403040c1640501c05504c4292014815140a443d0341004000d1082d0100004004941d40220f107861482400140a0333401c610500d581110b40207460380358000715528801c0b581e481109402e14401c00e02408460400c40300e0030552055514010401507843d644514441d084c109628080303800001100003030110440c00c072615600e28001800140c40569242e01040212006102c1404246203040090000e5a500e0030081c3d102d411074800c40c00425200e5411000144010440c9e881c010351012090302080c1c20042410350380d401560045a009800c500841660108804845603000340b1070010340d51900300d17251607008241c65600c44030080546011040d00f0760004141140e20003070a180c21 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 851793705 1250 851792455 851792483
    0x2406030807170d06060915050a1205130203061312050c1b041e0e0d1818021b010504021305162312010e060907093f0605090712 56
    0x840c242c401c49005403c298a44240000c1840d002202d0780308680d40d5402648401a07540019070381417065000c46400100110201c1c89020388550101c6c0c2c120700103d04c0c404015003982e000c030b45030001c140c608981050210408804106148180d0754601c0110b20309a8200420f00b11441ea6a8507504094141e400540346480701c1d03070702c803948160301c0f030704000c0c05c0c4203801d50031044004001e06820022120714010072100140c02070140700c2c1048207035401e00d509071710700e4034080c1000a00020500100d02540e000c0244e80c1044d0700c0144101904d0140c4000010310382060310408c00a0380c4041b0348108901d04000400ca82040b140240801c1007010741400c0b004010700c400e8181c40c0140480001000c40d0b0003050b43c0700b4280101e0002030507140b40441d00341440d02c3d0041000701504003203135098009102c1e0344041c80051180d10400c40e20f10080c09003190542e0b180094046180800d0441c01004400361200350144400c0c1d000e07060b0096441405840315605050a140d5002c40440000c2e00c1c00a40c4205 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 851794955 1250 851793705 851793743
    0x6020309010b1003050f060103060503030f09030c060c1c0810060c02031e010b040f0902090115030608030703030c02100603020f10090305030301060206011503060501020c041a0405042406030807 85
    0x2d0b441c00c0c000200400001d01d071034900680141401d17203100c0d00e4050105d0005103c2c0d40a81300301c0c016500c00500450078000c40c50380c8004a58451341d4100d425008582490101d40c072000003415107061040064070203c0207851120f401107030784c08004010007030504203114084000114100c15220f10f4602030301c034040c481c00421b20300308440000c000041e0b0f1401c25036080613070640c40404440d078200c90a108110700c1e081d0a43c1602c030303803e40195102041d200100091869124441c4890355507040108042c2ea4400c145410742d0009802503001c00c0e2190317158400990306001d07280c20703c49045001c104007402c40e004201445d000d0814240a0607254000e9038050307000300b108100955200701165600e603120752009403520130a00c50800c504264030441115917000303020741d000381d40040e0300501c40314100c02c08200140603403405490245c01c14010350b00c1c00f07488038060144110f02030501c5010212203c0c40e68100350b07080c0c0724541141c5217001b60520000744010100c4880720341042d010340300e00c295800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 851796205 1250 851794955 851794961
    0x2130903020c0d0b06030706180b0c120705150f040f020402093c01050c100c0912050a14031c09060612050607020d0e03030d2406170717040602030901 66
    0x20a0780d0b10480e0380494104000080340070500c5000250247c414241c0d80d10001e4541d0b5045d5015010099100e02007800045a400c2c05040c00c0b070b072070f0000c41c1ea030f400a003009005507078420701c0b041c1c070581c011420034911050310100311034000e1042402c01015103040c0c3c4504c9202421f170320f00240310311f80000c0d480da00b03940e8148813005030348042600904900c01854611070380c4684224900040c8120300c900320b0503580201c2c16a000020b00d00d004d44601c40c501c0380b0000081521402040c14415200d1011902070900c500c401c80355031080008007100c2d400c1d41440b11010002811403006a4420803000f0098000011742010744210f1001c045200d46040c54036101802141d0001d403148012841d204040c4100000d1160003292150250364026502c09411a40240e15141a0b60103502c104002e41004036554080464540d4149048031514a00d00341c016000d04180d00036000503804a151600784102070721800c0e00708107035082c640d0181401480c06107010200400c060200c6501100040d00c1e900290 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 851797455 1250 851796205 851796223
    0xd02040b010306170705040b1219021302030702030a0206011406040e0c040801050702061e1006050313050d111b0d08070503160b0406200904020c03090409060b011103070213090302 79
    0xe0240c0d2212110601d044e40c0e176007214030a05204908080d04d182c05424a800342c10012200b1001500c0c10510311171400800851407001203810501e442002d0071001c2140c4041d50240d0029405103035500340120009251180c180c00c1010b8004002d98400c0c0140c1d02c10007245d045543c590360b890302aa840b03102a440d60b0055600c0040315500740420080f403283e000c190030b407041c8810b044011620220108891a40c0000c40302080c0548001000b407107440d0054000e140c0c003a09148010031710300c0e070f965905030030201c4004421000c10480032108070400c0051024031024100d40401d92051010400000d072000780840c0b010340107040010741001031100034000c64008083c683e00c2803091a105180980704030394222070a89400346401b00300c60380804070000f055406800c40c540d00c3c1c03d2102d4042080001c2d8440350b401149031000304008021600c8a000d032210060213070301d00082c1061030030300140c400c040d81841c18209401c20040c01c00141e4419281c011030000f500c400003500e80719498142c1c50b0406607 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 851798561 1106 851797455 851797469
    0x90b010603050103020a35160e041a04141b27040b0603010609061502061b0d0b0d0b0a0f110c03121f0f080111030103020d02040b010306 60
    0x5101c000c60034448440e81b47e0a070303049582c01c448240315148240c0c1d81142000000e001c4946929000502081c4000582c0b072406a854010001030003461000c1c007140d00010505101c040001c0c102130302031a400315403455078800c03411039255025600041c4140181908400c0c44d002d000440c9041c400d850350710b04000d071240d541d1114900c1e00240982e40540d84c030b4000142c0031031280144130040a0102441d404411996402410501e00802e074900a0407802c50170388030f528540302140c0303480e545a8000618400c0c0500002c41d0468403000c06810742103004240402258181d0241d40600c24404040050203002d0340c2c800c0c8640103a00d07923042c1c150014405c0c070980c40c1c034031003007180d1040d06052450010995024642d0258105800c070034003030201104144900c80007441203400c612480300d41c85086602d140d0014100104a107002405107032910500c140d0350b402a00f0040183c018 = true := by decide +kernel

theorem cover : BRFrame.Cov 851618705 851798561 := by
  have h0 := BRFrame.cov_init 851618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 851618705 ≤ n) (h2 : n < 851798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
