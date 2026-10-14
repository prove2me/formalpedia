-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2342
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:25:08.143096+00:00
-- url     : https://prove2.me/submissions/9518f816-3765-4e0b-8b92-00e5142520e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 421043165 ≤ n < 421223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 421044415 1250 421043165 421043177
    0x3011116060b0603042001140a1b050f0f0c0402120112030504031b090c020a020109050f03070f090203070f0504060f141e270a0b0c0f010c0203070c090519050601 71
    0x200b2a240e92006500843c055010b03035418403024103403400c166600030310250400034640152014000041c0564907041c625003001e01d000c00205848441ca10132045e40038089103d00000c140d4540e2000c21041d044100c41340940300c0d66524030040c80241e1080640300a2001000001004040110410786540e00e1182c9886490540d40e91924010700c020a941c0c80003110741c02900300580c00d80361140100e100c441d40054092505a41c001906855042c480c46000300e078038100329000c0e90740034424000501281c1b02c1d04040143c6412448000b9042180c581000c52080040c0c500740c1800380043d42c0403513259694260166440c0c071800c55100101e00c04031546001c1c18407071f22813003d90040420b00c482c040c0c00180c40d00d130000c01c07150305001140c9100c21840211f02200500540d1100c1c441130059405031b0320700303690318240301290f00c0c03510020107a00304095117021a1443e460368080300800300640980008603c09031a04425004c45500381d83c00c0c1082c110207504e903103078000903030003890b40b2101c141010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 421045665 1250 421044415 421044431
    0x1a0904080307120e0c041d12091306030614070c05030f0904090b0a0b0a05060a1e0504030507031104110301050102030306130b13060f0605191805120a110301111606 72
    0xf00143c91009400b0076054111080c0342d903c1d410140700308007580010440f8a005d40502d43d0009442e011444200d03003103e800001c0d0401e03540c0710705515070b50b41d10503442e04014540d40d034240400100303070f00000c40703402c103a52101007007007144901c1700212940d80113000303540b400040b00d0b2080c00f2584a00c80d013540090301c031032800000c9442006014851400114081140034a04042041c2d044454000fa4454003051000002c1c41d03900038100344210600c40803090041820090540d00c50145520082c9603101e40e42000c41080b2017480d070b095038070b0015070b030034090807146049808180c042405068010303842840001c4035464141c0500055091007400050114110030100e15062032010806072003e4440f031082080c0391300c104a0000911591610b6402e044070340418418128007044010300300600c1d00d51030150540007003034003001004018410440c00d2010720b800c507204c1303102d1070042e904241981440300a07410180103801070480b00c215914035103414803d08410308054110103581481e036400138 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 421046915 1250 421045665 421045697
    0xb030a06060b0c010501091a0906131805010507020703330608010608190503120903090604180e011a01030e030c0111070c08070e01120303180303020306041a0904080307 74
    0x70302030141007010040355460221001603070950300f069000c2e0f6449841c1c031aa022000342000c4e400c1c8441801202c91102c02c1e1940b01c001400d40200c0400100703507904c2c01041e030002c075144a4121282e140320f08000d01c42503507544010382c1c80380038500c8041e1901d040e4201032420700700f280c46c8101b03035080c2080c51954004032039807044080b1581c5030022102e0340c0d0341d0382e0b06001600040000b801c500c00400754444091400f0395410341c59000320341d002050202c0500104004840a02c141e603500a0050100c0340c44550740c44280d0344c0c5110052151646901e0300207140c9500c5418080c1440640c0046558400c1e440c0781401100101001d41e01082c00f80014007804003401d600b07001d07c031180c40f0310b500314546590450605006102403a80650310301c0e401204100080e5231500c03480c86c11148040c840300d940b5010781c10164007404200c03a152400008404442c8100340d0903502840c010802070b0340800004000081c4403241000056085030301070502c40c0043c0004240e8801142d0040451400c0300440048120b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 421048165 1250 421046915 421046921
    0x14010905060708010f0b0304051c02071701050a0f020c0a080c0109020312090306160f0e0607050d0c2006030a0c0207050607060207120305130204050403051c0204080601080a150b030a06 81
    0x2a018000f5851100421400340c00b03a0300341001d01b4002d5a000c1c9075050559a043d665a0408a1405900744080051201c00d000340038200040c44407000a050710304403014001d0081c0001c0301c61482003840d0030302504048141d407094030b04414a000003001e21000326140c0c6521a0403501c00b4035a82c1d92203520b0540103850902402d1010004201c03401c2d122500001058100500203202c010064041001103040d194001c8640480c3d6030035041600405144202044451140800240c903500c210070460030981e6000203d81410f601611004501a0080390f040c4c0704e0880e420b40d19a030084007400071a0f0074041550005000300d807280115207400b80e4810208100b608154025107500b40d010580c2c2c400e000d00d40c010448107003050f2508120502d0700d401540c0100441400181c01641d4907800a010140520300310385481c0f041070804c107100e14803445407002950260007503407000c0c000c100c000515994005a50b0f0b4886a01085040204400c040c010000f40b0303940d541650f1611420f09030f900440c02e144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 421049415 1250 421048165 421048171
    0x9040903030501031e0c06050706090b09030910110309120106030c030b04050609070513050703060b0c010603060b10051c062102010f0801230f041503020108010f0f031401090506 78
    0x78601056541c90b60030104882c00500790210040340090354141e0028001c405140240c5a550030034070344a4040b400d00e41c00400104800612080b011001e1100c000c0002018110301d02003202d041140c41d45000c821652002c1c00c1d031140d802541300340400711852804a400301c0690040c600000707041562500d800f0a20300c1281d1060b18040f801600707000500405120751580709025000500e0070034a0000814481d2408404511055030307038101041071684a0b80100008100403800d00e5250790305048403900038211803004540d43d07407600c00b40381810f041016440c11030200c5900c501c1e06003003420080028095806d00110520340e0b40300b03004103907080c2c2418505009000040f0003d409102440050403010001c6449000d1005001c010802d05680d82840c1900f04401807641607120405800f094a21103030300302d21a400303401d080318103920700d508070a20001c49000341d031a80000e990f2094004008680e5015841c3d40941a1038188081800b010560100680303000c00020040d0032900d0340d0342003030340039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 421050665 1250 421049415 421049417
    0x20c150403171e070309020103090b0114030724140c0a0c09060905250e0d08030f060604030c0902131d0103050f010b0d11150a0503010e160c06050c09040903 69
    0x19002c4042034145214119440203281c20400c070f03d41d640c14450400014003c0041d400c06460342069411a4401c1d0810641d55501000d0440c00e96124140603281000e0070206030300a110f240780000d60381c2049000900320700e00c6400644c1c1c44404840d0300302c171103044010050b10105010072010218000c10070455080e9801030240d2950300741054903d1061b030305954032030480b0b54208001d208030203a608048000078011041052443c40c1188019500401410211640280302d00d01020038000c006004501c03c22030311102182580e81c030300402401d4080c03400041c00c28990398000b03212004e12031b801420725042c0081003020899940c502c03825444001c110034901d0341c5808004008105007000031010400d2024000e11214074a200440e0200d80000009800112005441200c580b5480c0c0f81107410501c03040220b5444000782e4010707242d580b083c850344056203050740000d210314586a50140700041959100704c00c0142c507860303441c05407e0180c540c0242580c108440c99095031a841102001846 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 421051915 1250 421050665 421050677
    0x403030e0f0d141b04050f0a0f0b03121201091103070c0507090f0c02070f27110307020a0c0b16111504080a050709111605030d2903070f09020c150403 66
    0x44210404c00140019a4240038174188010710401415801e01c0c00d900c0b140707501000510a0745003242101500d56040d07000d070180216241c1c41184a41600203240f090441810160240d81e524554011111002c120000810003070020a0880f81f1030132146101502610444001c035844410724403c540b81d11600e20003056444001900e2207405100d0300c030080c15907460382814585001c14401e9518040d048040301011600c4881014829a41c00b4000c2030000d4410345e0385928000034065a103010401c810b456440c915840041c0b41410041250b001c0c0e041000b4078110010b5690798400c5c02480c0b5198903603c15032a50000c02c65096460280000f080c1440013000c04000314140a030411120b6000300381094100150310f890060048102c60451700d64141c900300034150b031b0508500f14094810f20341a854140103002500c8400d8080482103085c1150030000541c0110b000c041d03490700380748107600500d0064270040001100e940d01500218480c038003660314500142e01d00e4a24400111000c4000c0741d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 421053165 1250 421051915 421051933
    0x20c010614101805040c02100606030b15040b07031b0f060c03061a0909071403010e04061d0c0f0f040e03041a0c0c10050706021308120403030e0f0d14 66
    0x107030a10082c842d108003401d20100105240c40c1c00420410640181c5005684841c0a454003620800201240c00170b1940100001307601c0700c0e0024060001c40b01414482d401c030340149101c10310b905003180c080303c2c40c100d801448d00c1402e54054802c000c0a1486180c4480124402c0d130100e1208080415094480c13000092070264084024080300c415822090315092803508107146c1c2400b4500300c5040103011241c002007683c0c0c412044841c0029100440c045003004400012501165007095010741d05c902403e00407040d1285031140c0721841e800d0903540503070082c080e243c0a810100101081c966010384101c00d01c8842c400070405441d001000c80d540740d480040c00300054103040c0024210b0101c40b6007294036265541c0041969170030a807050910400c04065658503003401007040301c0c1d24645c0300e8819900da00241d104034590003a0380c842d90089000c0c0388101d80d104c00b1041c04a038152549500c5034000d15002400384914590900b4005070040001c54071140411044502206040002d4000301643d0b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 421054415 1250 421053165 421053169
    0x3120402010219052d07080106060801120b060f01021e03030a0e030702010c06020c1e0c030d110703200a170d030501030809010507020a0306020c0304090516080c0d020c010614 77
    0x203c58a1040140120b81e0484000010f5011400b0182490000d80c101c600818aa8000e40c540500741c94440c03040c450707040009015001074201c1004c4904548650076643e913100784809481d81030210060400f04403500098861420b015200108041881154180d001004040512501440f40054035500200c01c0220500943c054070f60f051030300c0707800341d403d003170040e07001800855064100500c4030380c011610260703d80c001c12801006a400c19402c6484c05e01d0101595110002400c2440c003e0066a603a00c0c4d00b14040c000c0081300c2d90201c40107000c0280b81d0386980c2144c1d41c0305042d6240c400e4030b20009500c01e0755600074240142c43c1008140c80000c3c601104503142045203161541418144001000404c150209441d0266020300303109985111610009840702c045420007061a40701040e544003a80000000c0c0041c0c0d00018020081620f03410a8803883c0c082ca0b280800c009051007000948205900e40604a9090180780240c03c00c07a6050103242543e0440c0c120b048601001c28030703080c0c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 421055665 1250 421054415 421054423
    0x6130b0603012d031a1e010e070305100609060302090a0e090102040e16021b1809010506120f0c010c02010c1e0209450f010504050c01020d0c0308060a08031204020102 73
    0x883c0c50f804202d07420038555520391101030b4044000c010034001101c0000d0380401c0031701580c0c002544403000c2c4403003503844120f08020840309075400000a89000006000c22000c008900182d880e0741c2c880c2c0420520b070600c110042d520840c4910703004800d000b40024800441c4075100d0056a0581c0096140d50174952007100903c40240841c100709000070a40d0406600884d090090b0340301c41e60074100740d81a010101d281c0500540280c898203504c0010011042410750025001c0c840803119000041440790482d07a4030004000f81c8400e80d0411b1603200415130082400380051407060600200d900416112001e1707995600b83c10741d000040c51100c0e4801c41c0751034400240c1c0890150006800340c580d0490088186800c400d01c0d5419040030641f203944245ea60550300d0b03104e2001c908403041138011134400c902030175046d40c0c01ca42ca40b0440b01c55550643c00403a840080f89529562070342c285170152011246e200b000303041d858004100c21004503541409200422510314266031800c1d84c0c0c10035100082c0b130 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 421056915 1250 421055665 421055729
    0x7020318040513050f010e07080a02030303010b030702010b030a030201050a15080606040504030e031b030d03020a050f1e070b06010806040204060c06151205070f0e06010806130b060301 81
    0x1150010442503500302598624803a9900007664000380076503410314404406040501c0241440c481c0c401082009081508000c0f422a1410150b40107181c1d10003400b551a030700c7c100000c0d8590400c1c0018030a0140080c05560f1040c0d0505c00414030040401c0400d0034466599030940050b5160820454400b8080c0100c240c0400300105000c0014030708a1010344481c00940414031881e00c0e540811b090502c10303c0c0010034044002c0c19500b00340f0512150b030342014256482c1c3d5010f8000e00e244070060601074400d6690719441078603034601d4100002000d1a1a074809404462140422800100c3d1620f818001d80f02140c42010f04e0902814098000740c01e101c4002d00312441640108414000e00d64800312408a00d0703402003000c942c24a681d207a22841c2030035a0030000480030b800c104807041c003000003459000c13500b070b2000d001c403010703150007202c104000200c5016020400410100e80340e030610800c4591071560303000000070b070101030034000307000c5520a038011442d442000500015400130108802c04c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 421058165 1250 421056915 421056917
    0x61803120506060f1611090c1305030102030705041203090e0f27120f090306090c1207031a072001060617040c060c05070810050f0601030504050a080d061806050907 72
    0x105001d920300400656210340c280b0542043c040800d01d201b00402001290040c0c20010600c00c5a0b280c00140782c2100e400084c081d60142a52100006090034107201700c3c1c0c003424070795682a00d01400c042102c1e58078141040110204890704100240c01107205d0041e43c000d07071500490340e040d030070544101c201000c840300d4107200c90003000c1071031240c0710800242150341400c4c03800166128161031071106001d00502ea5401c0c0c050040704200001c0c00b101181102d428002107403041d04880000640c15a00d040600005281e025605800150070080500c102e91003803882c07622103046030f4092070784d210f407016503d0070707007500e07911004103200180c0c1100450100248a00380c02040b40b4154440481c0840244070b21824400004030030f000303101091014402800c0d144040310340c401410f460b5903004200c1103503121207034800980495203940c420300070030380516040001050b50303040032b468600055100500600d803e0351b44104c000b4003500024500e810001c55071000185032840d00c0705005110400401c040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 421059415 1250 421058165 421058167
    0x50901120f150246020c06070c05010f080c070303022a01050105011407110f030a0c08060106030506180604050a020904090b0a05010806010e0c0a2a051006060203070f06180312050606 80
    0xb1600c0110044081080744c00466680071401c001d0003c0e810b002000d080250040d070002111820f200b18440c90f0313000c84e0000e80c0c801501d00c0798900e0450380d041c410388184034040010040d050101c1d10076000340c88078040d41584030005004050440d9013507010092510302caa511480100701542e00a0300030341032440c7c211131a5203408a80e9844220700441c200020b072040004400828090b10108103c200d100d0348a5804040b454031240f0350350750b0303a00900c07402c070001342014001144c1e17040c201c1c114001d17200c6020754200d03180c80304410403002e840001c11005101d1350a00c002000c40e5101e0250640c02d6000c0e40c03441c0503d042c012a48810307210141c00200040e880203004004181a8448040d84205503041c201c1e00c505141d081203d0445003100c440d81c1e04051200131a1140100b01065044141300340c04580c02c011000309030034103452461103910096042403140c4404510200ba0151b48140708100010b16518039a141e0181c01c1c0419001707038002200d442da88040080b15108040d04a9400c5900c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 421060665 1250 421059415 421059487
    0x90601090303110307060504030203031b04180c030921021009170f07060515100c02090604021b070603020c06010801091101120b09070f120501050901120f1502 70
    0x18040d0802884020100200b032100d81c4103080080c020f5424640e03200c1c074184400d06003818001e46d1b98100350380c000707010410400703500101044101110102c070070403d40d1401814103946040002e01c40052543d060680b031705a442c000481d80f544c0c03180002028480c0601083ca4610000d2070b00b06020110903110349084001d2001c202850400d00101c040780b07440503620303460070144441500600100800d0141020300748441440038501e0005088001c2c2d811422101e8500c40441e803a00316006e0194010000401090003410a90003c3c04800d120054010b03c0182d0a003d4a1408540e0f131300c6180043d602190714040036000b03120751401001480b0080c480004141c86080321400c00a404c03d05000707101004240c800b416070001842010700030803400361894100d101410562048a4076400074081d14a03001002d800d610030035050329009040b02000d40c0c205484016030800204060324565030308241d501c0001c0c0d149a40080c48401e0400150319072034504840c5104001404d044916401d4038054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 421061915 1250 421060665 421060667
    0x20d0f050c0415140307030501030b1f1505120c090f0307080c0f010e100c0b070215180c1005130f0303121515021c0201110a110c040f1a090601 63
    0x251401d4075503201d11401082c0310f0207400c0e02d0b410503203804410032030008010011440e40540c86076049174018042104155111070305803071842c620015100e0480d0403c042070000080c66030f820108051035080c172615119503201110802d0034205c458072507502c000100040e03241800400c800100d90140c0060140d0f81c02c000c0c0d0b07a0b4030741d8180768205002d2600182c060106a10448101c0041013026040402e0019465001002129174101c00d0341c249020030302242100d4400503005e003040510501040441c2c58244961062290f104003c50381d52003500e4000910740c1d10050a500b40304110b03201c041c0e03280c2900c00c2c40d0f040d500c2c582d80085204440d800081012039000b5541100c0641c6040b000034100449103a60030401500c0d070000100e22001c0400848207640002c1d40892080e17180c09510300d0600c1c090310807402da400720045600f4415042c440141e0190041c10914500c04200041e60940000080803400b150081002c200c00240c9540c1810700c0844801d001404110043e0340002c3c0f03d10b030001c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 421063165 1250 421061915 421061917
    0xa05060a060b090109030b1f081c020c10110f03030c07060b0a1d0402030f1b0108090a020d20030102270108060109231504230d0b06060715020d0f050c 66
    0x310247c140000c08000410b6110741e210070002c0003140c2c46021407641d0716a8080f69680d41100e00540242c101c1c00010801c1074000182c10741c014000420500c600710320700800b158140c2080e03211000300d125000c0e00f1161800240007546c03081142c440c00da6210a41130501800340c454000c80d0600071409a003042c058507145c0d13403001c0e5400d1950341e1035640703544441c80031034504044400d413040c66006074030303070300c450783e00411141e4440c64001d90381d901007501c2f507400d490344a920320305009610417000d550510000b10080030492104001105a80310490010042800e80e8403000e580482ca004050304d01d51010f40184004003035079070030f2900140b1490403900103000d550715800780303001a210f901c0482e4002c40c102c0300341b500311600140c403050050851036103441c100c0d003250081c0a02c01450a0356016071b0390540801c030751f0012008001c1e1078106403030740380c03030707980e42c03001381110360000d00c20000e400104a9070464102a010382c2040141d40352164021f140c103e94070103152031251070401d0b00340000414107074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 421064415 1250 421063165 421063169
    0x1404060509010309020f0904030201020d15140103050915040f0b0108210d02040906301a04030c020315011503020408030f131a280c110a080a05060a060b090109 70
    0x3c00c000403c04074600000d5400070450520702c3e44a2400c0082008160b41900a8100400c03110000e110440d07510390b402600a001d030040c00710100d828003100341950310940203240c004c80320200761030f038801c0c840304c00b070303d00f900100d4054484074015200b070410090b03803110890041c14088003401200091140d2040c00c010405200001c110000c5816515107074141e0441c1c00500356241d082040e030703940320234a440f080c0f040f20403d40700016400d000907001c02ca4070700003c5110792101e0086c4400301180c0c840b04040801a101fa806c10100a55083c0180c804001d1b16030800c07620b10709054950f00d808107000d124400300c2600350805005000400c10020008103581c2a80d6050b00b07c1a2a1111a403405510b045a035101044404c01343c014056803e008c8801010000c00b6209905601c0081100000c0501c851000490010398220741d40008a00904a490001d85005010154650740c821409140c001d840606403042d40121051085010441c0f0502d070040100c612144c1c284040c950000c2c3c2604414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 421065665 1250 421064415 421064417
    0x1021204051e010201020f1305030709050606220f0e10091a01051803160906080304030f0204050a0b04020d06080c1903081804020d1a09010b0d0c26040201140406050901 74
    0x20b41248010368002e4050710017007850280b1030790311003039248200040490f40780700300d40c001c2c06101c3c80481e07030044c1c43c080c0f5440b581c5c01404a41c5041c50802d803807000c3c94846101c8805511301c035140810071080d5002450001c0c228a0300e201c6860800b0aa07800d1140b4461f07004d022043c0c5041c1402842840d5600f189030180000d08105440389000c14074640e80e440d40b000b1a550601507000d039000c024805a40c0c500a03104c405504010b01c03502c69411071795030f100703600010b480b01c0c0031500c0365401403070140c105a912008051001c5001501e01c00400d0598120114490300281c4489051103203200820a450103520b086800030380303c03501441200502541c6000103030103681d001580494008240300510300e0781002600441d540e081800a94006080c000c45543c0c1207284030901080c81d14101c11498160b5440107942c41c03404018940c114010a070103150b04050000410040d0007030a032003034030640c5024503032880c03c40b2881c02d40300040420360300d20076a160880d020700060000c2544181a1099450300f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 421066915 1250 421065665 421065709
    0x1031b0206130303060e04080c0607020c010905060d0b03010903120c03063c120b07110c042c07050406080a0b061c120215010602030a02150a0e06090604020102120405 73
    0x42410f08034040c20054000e6444180313400306010401045c03000421201442d01c2c103480701c944501e08126100c44014078000c0c00100c4141d0140b140c0d01c0c10200804000d00b5040d4005115100307400860700b5240f200c5d07001c2d80402c010005402c01407802d070052609154841c5002c00a00e810101000158428907614138490038107140f0315001e0001c815008445100b408881101c0740e035959036400703a42d07642c5540072070b034080c4448007081c030301400340300c645090341c0d01040078200e16010320381440001c0c0f140d0031140c0d805070030013191750003102503154041d0750710b0ac0c092001d001703e5401d040900040c2c40641d401103461741d12106140003c104602c011075000401151000380b1441510580d50a813421a030001c0c100c50070301810f19001c41e4000400c0b88114480681c2c1c009a6030381e0303030000d136203a0040500c0c400250b000081c41e010707081008042d035030307000410203000560f40e002c0900c00d41c68141c04544109880d480f48050206641c1c040091f200250042446a450707d401c00020400100b10244511680c4034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 421068165 1250 421066915 421066951
    0x1208071b0309170a170a122705070909030512090a02150c031c0f0b010207050607171b0318090c0f0d0e01230f0405031c0e060c0901031b0206 62
    0x502204d8003143e0052070f0341032602c0c00f0341080112640710408020208200304d049540b11002801882c0900c404000f5014081d5240c082e510f104200b40141200e160045200100d0004003074410006254083e940300d03a110005401e034820507540142802045500c001c4504005a542c440300340580980a40544c0d2101000d9449a1850045000307055070711110300c424a50001142d80403030210481c21005005130000c010041e62540120b000301c0e6000b000805c00c2001145c0002c2004c005028802256490003d02280f04200518482c010f010307150000942010100e85610300450714103400c44a0901605002440b01d00a20890280d0051110049940081807080758401c02c52140c0c0c51009003c0c0c408a50041b0711095182c000c00b03c40c8000302008202124681800d207440b9951140055142021070b140110710b100c00b028030700402030307183c0310881440902030140074040c801180c0d505440c1c3c0010b500140607a204440c041414940e81001042615800100700c1c0d0031080040b44021196 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 421069415 1250 421068165 421068209
    0xf02030409020a17060d05030a0e01090b0a030e0706020105061f020312010e01080d08040c0311030f01020406030c110307050c01030b040204050a0e010602010b06040f061b1208071b0309 81
    0x401a81e10000072a0300c0414490b01d078507040303c0003440281003594914455a01c100800c02c0310008520b01401692040c883c0d007421038080c42030705c0c8803940305060645403c1e9540c000c80e02070b17502054103e07000070307280c000711002180200720b0782c0302a0070640028402841d211001c104140c450104c03244400c10b21000f020801802801107404d910740c20915820340d0344e11854005c46400c2c0038403030080b40b80705030200780007050301c11001c02e4000e81c1d1000c000042e00b8515100c09a1001c000319070079902d8004c6a00a445010007480140000c1c01c2c80c0e10042448a108032015010890241c0e1080c0325820802c5004005000441c5042c110002420300169160340e0801040007409950041904140302250100d08440b070000840d048a205034028055115a0000d12817580a00c5c07003000e48a000c001014400d00780075004002d00b603036180322824090201707525011345c0d07420400103050210380003405101032242e1041c441c1180c01406409100c820845540040c5003481034400c0025581c025407a0171456 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 421070665 1250 421069415 421069417
    0x703020c01050915070203090607230a050a1205070206030f0a1e0623100f050f070b18032110080a080d06050406030803060418020301110c07091b0f0203 67
    0xe51880008114901d8114800c1c3d55580100a001012511400002d00300e070744000201d503120f080141606090101c560380d20f203440c070105d90b224207041d4450f43c400da0940408000c00d00034030740a0740040c404841e1905206000c5007001c10400d041000030042800940c85540460f80c01c0180001c0c1c1224541d15080b031a402090f42c601c01c0351280208044402d0203441d25003225096800e540200d540ca01003440c0c0c0e00354006103017100309030401b650090809881e80103e000d0724001141d410300c1450642c000e10107090a5005420448401010340148840c00d0442d0a84410300055500214070b0000354807002d00c100d00740d10b00e07049070210803100081c5540c0203884403040100641c108403003c0711090300d400c040c0e6412240c0550311043c50a00300060078913090080310708803900720a0080c0383d0345580e01840050304440b28802007100c1c000131100d0040c2c4092094021041103503411680712080d050405003401519441034034111f0400d045a01441c5040c1e580c1e13030300040241007071000348285038426425 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 421071915 1250 421070665 421070677
    0x7140328181d010906050a05060703020703211205070203030a2403080318031e0d1b050306100c05121e0409020306100c030206060114070b0901020c191703070302 71
    0x401c4011500016a4410080c5100c0303082504020700740181e07221030f0301000310388542c86110b03401b9080000070011070414500800d0018001e105440c411a16500c460011a2002c8940c4d09a602c1d200703401ca000913800303410070706080c0140c0c1f4140f1480c10701c0f010095a900018008035030742d0740d55880076044084402c0d08000070a004034280c3c00b42d16a2400c10380915007044945c5501610001ca41c04400b01c0007008644000c018054001d9100b4520106c0401d1500143c40c518200d035500c00d4082c3d6512020f044500100d9055078400d42c0e0307440c00c50140404c0000355401344050290011074040003035400701d0402c0855442800d0641c94034181c41c035107130050102030440326544800040c0443d02006640045104840a95801d980c070800500100c40c058850413019005800400c0400c0301903204e482000748032604a4002070410f615921502562003040d00c1d0310a00d6036002820300916031043c4041e0104000d50164040404401c2d16854400d020303031505000008000400202c505010340c0c10313500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 421073165 1250 421071915 421071947
    0x806040c1703041a0301030501061e03060b01031e0501080d0e031005070309020a08070e061002030d050a110a02011a040b030307030f1e270b0702013207140328 70
    0x180340c01888101c100e04c1c2c0d20038003040c0c2d407550170002d000c10300a540c106060758412074481240c1007035146403100801480c0201c0041e04251300d070518403403000323404084020f4149a02d1000506035240c40c641ea460443c1007051a810300c060503090541c11340d8041488a08030524900c08034556035211001c8008010507200254400180107001c14075050005180040d10301d0003025035036030341b610780400500e0164100544010780c81081817003403105041d00b206811035484140071070300701c10030b41c2c0390f08244d0000c081000c0180c1d91010001104082684c2d010b5020700c0035102009101d0880c80883c0d128855824040c007030140e82c01d5000246403285500c00c45106000d004a240b0b00701c0005c0c01004009000012404408203040c942c252581310b00000c0d049440303800032613241c4202503006580c0040c41d81c41c10742d0780d502007441d03940c2c20405944210303080b00b50706a15141c5da4041480e01c0600d19000504624090340113000205a00c0340e4166034082c9a0000e03401e11a40c0303004002c00f283c1c00100101400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 421074415 1250 421073165 421073189
    0x2206090e132a091a0f031f0c031b0f0c1103010612110a0609180212070302210f010608090c03120a03140606030601050f040b0304080406090806040c170304 68
    0x203015103102c0003000c44076400342c40d80c12a40d10f5031000140152841001524110395a038151818149420142c0106914000c1e0a4a6801a910712041d40d10000790051040c0705450740340300b00c0a10340c1481412a42d4154407640a814164040300810b90340015464070144402c102d041c005011160441c00404200140207001e0380d6101c81c080c21020b00e610208680d02030304054140258509048884280da81c903940b2907840c0f9180c40701b0071078030081002d07401c0740300c650801ca406202c984580c04548a00007989025a5544d90744580d504a040c1a6040010401c0140d050285d0003242c446101e046031258507040640303440306d901c0182070010070142d80d43d0610a055411051b840700c04040c04092900d518201301140d41c8040c813091540084403020b51140307042000070030a40c040d001410040916600c11806c143d01d52502d442158000d640c241e0306914082410091607074400070740400303048514040c1605003050382e10484090824021901c08001542070101000d40c101f040d6401420b26100354 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 421075665 1250 421074415 421074443
    0x1003060b03031603090918120509130501030c060806090411010c020f060a090f09091e0c030b090a2d02330c1009080a12090f0501022206090e13 63
    0x45e000c07082501c604542a814603c41c400c030795680d280d00c1c01004e50000c5003144008040350044513941c0c00030458030381c800343e0588a4a00c103025440350764060341c42441100b1304107003080d0001e020914010b210621460381041000b0002da01e0040c0b40c01c041b0820301b01004911480d20018080d038000040305508400e0215503a1700302035100581100321400a401e980704107440b5035062041d6500704c2800b0b0f000360402e00c503504840107000708038040180a0b0304515401d585940d540520341c413058860044590003240f48905202c00c4d074160041c070a0405009400e001244080c2c8985940881c01c040e200d4001c4a0b03a9607560b4440040041c2c0c810031403810440c00c001407080d0000150810f121b002054440c203807182005000d9445018803107608102500c0c104441c03c0c9013120040c400c00445040561910924400500301d4061104980d100e0740026840d0901c002c0070000391a06243d43c010b80c0c1d21101c104001260300201310000782c405070a058251650b80320102d030040495440018050a942145 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 421076915 1250 421075665 421075667
    0x20105070b060d0f0b060f03010e0c060715020f040e070c0b01030212151603150e0609090c030604030f02010c0f0504120606080604030c02011b03051c0905101a0105031003060b03031603 81
    0x207114886d920480c0c1d1031001c070f502c0e130041c10f00320703110030070301c0302c03580d0b2000c820702255140c001c0107030507140d118445084030080c20b06541c8060360446190003880d24400f0400f44111011211191751000c0c071442c0840e020b034101c0e112441c1002040c4000380c0180c00f841e81154040005003c0c541656091001442d010b041c140101b00014200084450002c0c0c501144400032511803c90103048414910409078940c0740d210400440740c1025144080c1c2d0700c601c100500d511346091100c140b080d4020348908121085954010b4203540c64685840d00700301c4000c1a03642041d0300901554150743e2041802070020001d0f10f0694000c00403138214800602c03c94042100b01075204030170801d90380c800c0c1d07501e0505040000442d1102e50114000501068047c07203120071906c8a101d0301405000700d0400400e00800c992582c50034003400440040740242c030340940300e004920800340c11104031428a805480c514000304440c0c2294441c0c04010a10f540b520079420f110f035010000d0f40c5c2814404200c0b0b524404251038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 421078165 1250 421076915 421076933
    0xb0403091401170a05060d050109030504140405040c031209030f05061602071a18040212040605130302060a0903031e0203040c0f080c10020106090603080d0b0d020105070b060d0f 78
    0x1c2100d8800d040107198140c1d55203d002070001c9000c000200a03419183c03540060080c1c0001011950080e28007404040420800d004440b4600d0181c0c603210750350780c2015100c1e584907500344030003405181880c003400001000000c144003100c4c0c10529254101030f40e000221000f00d2158005811088400340c585c00380314010a0380350003000040b1403224121494241030b80c45a40d00c0c4030380c2d0000d5100100300c900401d1104001c2030440841e481600e4403401c518001800c903000b2105144601c0d1003038042204000c007900c109a04068074500300c03150f90303015a400039521000140201f06140e00e5a42070307401c05000e0f8100414007190082110580034003c89a18000e40040f1000d81d402d420b100c0b8000380c1c0500704000310098900c003e02078080c600902c0184943c0d44058241c034000c40d0341e6014002554440c0744200c501840c8191846e550fa0540701120074151400140da5038030902c0b891a140005030380110441d4a02035001c0d14921659581200185000d101408060030701c15003000c0030020800ca8803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 421079415 1250 421078165 421078169
    0x120303020c0114010302031902040f1a0f2b1b0314011406010e040504032309091b03010e18010c0507050f0601230a030618021003020f0d020f070b040309 67
    0x8000c10803d201c25112602c440020320001c0d405030440300345000c1078043c20802d100094000351001c0b07192620114200b00310f850203800702d1540d03280311801c0305881c58030040c10242c01c0011900011810b40b075500c5910102d40b4200c45e24403031007039004050100000e581c92034044080040400b0503541d680d06002c0340c0913400c042040b400d54a0041060083c2c0403011403140115010380d11201c08043d6042400000c0501500a030306012024076800d0500c03000c80030400e4407a42c4840c51036290030100c3d090004915003c2c1800304641d20210154014980d86002d40b81180e10741d03460140c160b12152007444018061890b5401d4950034001c4400b4003603002401044810721407011605142c4036400d205442d03280a00a100441d01c80f0b0b40146810998000c40c0401000000d04c0d9501450342c0ba5180001c0f10010f4511030300440300c502e440c1f000e6180c0800f0000100d81181425450a041c21410280c14410201d500c3c120550104034203c90072900c00903644215440701150303525080900340903200503054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 421080665 1250 421079415 421079437
    0xe0604050607140f0f090f0301060b0915030c070602130b0a0302040e06040209091f1d0906090a080f0a0c0204021c06090c080a0504050c1915030c0507061512030302 72
    0x74140c402110f40d2401c00f11000181d032001800e017040900a0070300c0d42135001440d01c82e80420400b015851030342c1c0c2031048200800c10546995541c00e4144103010180e03507101554510703010b080c410040650010403c40c1e0926901034401070350380c1c0c1d410f288130001950342e40140010b2000030508000f40b03070b019030007041078590104040c0a0350b60b51000704401c0e841810081c07900848204003040c8160800800c041101c0c0c1050f814212582d00d0751348811424855020520341c10503134800b03100101d01e0500040c2e4101c200c0324058000130380c0e1529102c144e03229921a03004044000600070b0040d501c502c0d00072901c6503005100759940c8420110200802ea039414001c8105460700c1400552040030344100c0ca04480651507162103079495440141c01000e00030015a903602444020101c5561038101d07000004103103044407564242440320b0805400100004481071601d049600350440790444162484540d022901103410f502da803440142001c42e5a1000c038140d24100007810425030181c019001150700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 421081915 1250 421080665 421080677
    0x9120d0501141c17040b070602090f0909030a05031005060d090b060906180406020706141e011a0d0b120a05060f0c121e180c010306140103020705010e0604050607 71
    0x314010041c4900c1c50202140307602c025840ba00c0e000400b84c00c50840f040c405a0102c6041a94400c0c821314540d2114004407141c681c0041c07a01c065142c1304200d448528002e9640c000c49260002540b03980c2c0c03091040d000103010010000450b45061110400087c01002e8902600c031280c00d540100500b0015804850240d6850300063321420b00301d41b5280720755801096021151020b451103162000050004e548051b02004a41c001c01d29a005031540c001c1c02d042a0791051402c0e190341d124103948188116039103904400100302c1c03000c41303a00d1801d1860003801c0050740d87d00200c5c40480100b8400c0c41031a041a281d9221202000d008a5000142809a005e40340c42d40d43e11884c1142d215001c41d104440007900707000c2c001c50340070301000080d4030030b5054003030341010450046079403001e640843e55403100e048030a11a100d5a2400d0040984001080c2000c1c40741da4100150124a500c0c003500d41030405502042c0001408825000b0400e4a600001514400d04050801d20348844080304c2038008201 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 421083165 1250 421081915 421081949
    0x3060509120901050a050d05010617180d0324170d020313121506080d090e040320070504060e0718030506071407151a0d1a09120d0501 59
    0xe80030481c0094410141c501c140307440000001910280c00540500c41000401d0100d0941aa940d00c141c0d4042c00883e250303034035400d2000c000380d4081e1000030f002002e0210803120501c00a040052074400f052018100410400c1d080b030b00c1418546942c03c80200c04d0341000c80c00240c080252000c403c2e1007840c1c0d40540c2e20000342e0100607130f6240b1480c0d039180e481840c040020800a9031044c044d41e64984100c04400c440306010704c0080c162907144d045030903e50001850f002109402c80b40b04801020310003181d548a1030981c0300a0040ca40000c00b03051001c5180b9000608410300384588000740500503c03c003c00c607114a28805841f000721042004101008501140e90131000702d200e08590740b0000803d025940d980c42103e102c441102d40451524041c40320400184000140d44003074280314100040d00716411031010150b40b034110a0600035408850280040307501c3d0281d0000819126001c4100e035202e01268510f0329500d00400c8074200340100341c0b078664540170740100741200d03031350a00300003248 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 421084415 1250 421083165 421083181
    0x30c06150803030a09051903050c01050a0908030412023301061704060209010c0c090c14130e040206090907090f0501140a0f020703080a02010f0f0203091213050307030c030605 77
    0x301a006140d2140d0060000031071403107464200c519914031450554602c05166141603540c0d0301702a0f4100c001c180c001c161301c42d14150922903e503005089100030310211261780c07103411403440041d00103402c02c40c4a010142000d8000c0104652020340360100c040c6181e506c07884504965450800400e082081c400005a101d10034451103a690010381d04050309074840e651303004025070205081d035062000211240002c2030b22402280014102480e003c21040500b50740145003026014031f007080d880c4140202c000c8195608101015200c000101405946882c000a5601d01840080c1680401d0700e03410450081ea11001c03400894450380d01052029460300010766038440d50101c44e010106050103820040b40c42590600b041d8140b03030041c0d0f020f075620398682c807032503521100381f0300c0140c0c4d1100700c0144e0440f2f031449a1a01120a88000c50030741c101000555181c03100c0003a86090060007007103a8a00c40440c83c1600700605005085880701950707440e0050720f101c000d11050300c2d064034100c00500c0e06 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 421085665 1250 421084415 421084451
    0x1209030215043206030a05010311040903020d0f050d180b3412050702030c1902030714060c03030403170c0a140307031e0f0b03030717030c16030c06 65
    0x69406150407044600c002a40d00c541c0662400f01d41043c00f46181081c41603881c0c100c0214000d103080700010595604500f030008403001c3c840e0460380100d142940640200fa8040b8468083c46024500050b10711b000400440b41c1d070043d80b0103514071524064a20820316030900104024a00c2403101c0d840d00e0392546000001e40b0b5448007090141d2040c09441c4241840102349191221060300b4090701e00314000f140d071320481d482202d0000150744005402e48601c401042140583c204001b030034134110300e15a000c07075100c07081c601c11000c0041134004c0c0550301e5901e00094130000841e10f4101d0b6141c0c9001d0030024100701c03200040c0d40140803802d000c900e0501040c0120b805040382a22a6196082403014604444c0d0009000c24201a07031020401e1800b1079843e000c43d030350907202c070b00407488050f004075000480f159500840c1c8070381d004200308d40c00070703224040c182c0e41c0315000d51400d9281c0c0c1c0d0311003003800c4510901c69030840c1710800700e02c403004142d00a00055504e034082c20041140a032024040310700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 421086915 1250 421085665 421085669
    0x6210311031c0b0a08060a0501290f0a0e030a11040f0603020f0f01051303060b030601171513080307050a030f02030c04170a05070303120c170105011b120903021504 72
    0x7880c20b0511600d035210455811a03004058050005071241755214005800c1210940b210403100762940010400c0070300780c043c164041801c1c1c02c0d07445007959200b80301e08c0b568840c01c03442c41c4075507402150000350280035602c2c59054036006400c1e00c00d07191240c83c1000200003a110981d11842c6411902d8402c4034492203000141c96005d0425403c1c00900340400020180070303290641040300420490440e100d0f8802c0310001544250004640ba00d0310900701404c04a05800c1080e065213480d4202d80f40000c0040c1c0c11002c2c5e4007150010000d9207404a0700042d10080441c081c0000d0740c00820b2080240d88000180899a9650b8080140e6000c01e00f510f000c3c1c2c07200340d6001541d4a4244070610800d540b000d0031035080c17a0440101d07000307010160f071010704103056a1320981c081003d1f56048580c2d0b100c01d0094002c090704502e07000c6100c03984284111881c0c10b0600a031070411048240c591103c0b41036035510403030b04d50091042d0317000c0c2d80243c41c01403455000b40012406146102000c04c0e40079010419202 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 421088165 1250 421086915 421086937
    0x20313120f0602030402041d0f100203060303160c0302030307081b070303230403021c021509091315050f01080c04060e18070e040b04030806010c0b04060f0621031103 73
    0x700306840d501d44001a400141081e80d00c60740d245c01c0b0f0180703006080d244164481c00000944600b1208805060030f0550340d440d074020780350041040114a69011040307071041070054210030981c0c9160700b4001050214cc1d08001c2d01072000103100c1c000d1240c030902801c841e00c409440300c1103104c3d140100c0c030780741c80c402d20004010420500c1405a001744c54080528100345900308142015074031340004900300d181c5400070101d0b60404e2000402d600303000840c07512004c80e042500b072800e204580032400c0d9800040060040100075484241084255100c0382c000c00e00250f410310190034141401d0090500a1140ca2a20f200720120b5588600f000e01690301294003c0e0500b454a80e101600c5045141003100307488410300900801103846c03030000c400c1d14012401040458020320b0186000f824001c400b8006d41e0601ca00da200348070024400aa22580c0194001c40104082c000341e202c840281c851900070301c1c09040000401c2e180009600a480b03070440c02566125001d188180410780c0703034130900401403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 421089415 1250 421088165 421088183
    0x504050106020f282103050601050c030301030f21170106020109050c1011060a0903201009060b0406080f060f060901090e0c100305090d0207060c02010c1e0302031312 73
    0xc40305624914102a1004048400d09410242d917a130038000c41d01c0021107450f460701542c1ca0414940c2c14410558007803000c0c2071091810480c03102c015600e0105100003800b0780c1d03220200504202d08070540c420801507006c041c602e1082c801001410602c020701c00380801907109030001421520500411200a40200c0900b484003c0c003020310800700149800c000a02c6007107282201d242c0300401134140300300e00c03008000a00200b030745002016030450682202100c00340c2c2c403507504802008140c00311103400780c1d07800165804051400d800034003125625076600070b14240001940c2003011030a50356085654069840039500c4820741c0c0c01c0882c080d910181c20161240051119000685c0030010b001c1c003403001c5446424500000503046040842c0300c2c000261a0b03002d02030300b100f08004d45843e00416002801c94942030000c020600d40302c2010182c100b203103081c0d50b001440007100180c3c00ca5611003640e928800c03c9810f0203540c0381d01520508101c940601c000040c419140700401e051260310035518 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 421090665 1250 421089415 421089433
    0x9060c020120040527090d021b180403090305030a091a071e060f0218030d030902010509040f0e191208040c09050a021201030c0f0509040c122603010504050106020f 72
    0x3012880350584100d00841c40304503a500070034000342120358421b451482c0184a032103104040281064090150f10000702c0c944203045d0520ba4a003c00c09180300c03400140c810f038965481c1004c030307041c821070341c0b000d829808005140404a82d10030840415585025518000e0460008501d50781d80700d18000913009182d20031a0040d82c450b6404100c000302e00030360004c40d00a4202c841e60089a0055085644440140341c0e5a40c0c541010310802e40c56159505003040241030350f80002c1c19030700c00e0b00041391081d03136110f105038094002e6a2000c010b00e8400e03c100c50801c07107001003011070100d0f00c4505403020620b500a4a015600c19248030303100702d0b84170049910b014a4003080300040d04010b845106116001c0c0403004014041c01c215500960103040102101841c0c10081d41c50006181c115a025950ba4001c01c000b04040901d058200c440c041c1c800590801c03582480030040090400c0b08400310040c2d61604e1508555801450688404490402c466641e44c00180e940e01003044030044107402c0b070500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 421091915 1250 421090665 421090669
    0x61707060c050705060901021e061006260a020c0109080a03060e0405031204080d0504030909050108010b09060f04020f04180528090201111504061103011d0406060909060c0201200405 80
    0x286c450200c0600488500b18181a200f201c948940d0f4203200659201c00200b102c8000040c189800400190070045407254290103401001aa17100c9060840c100c42c41c00b1940d60301080d030440c0c071a910b06a0013000030809519104074268400c8400c500042d003015404580000031410041c0200c0d07202c0021803901e4032454144401d500000e1068516079414480c00f100c480490043c1803060f4230030b59450b0221070504100d1400c035001a040712625a1400c20f43c00c00781d45a1922864012004840095090265a00090181c410820070806880d004940001c0c07005c40130303410b41c0380d041207404140300f15a540d10003051502c0924003410320030203a09074006040e0900d944454035141c0185031182143e40040c0c82c480c54010080242d20804440304c00b00b00c14070800d4403800c58111041803e991030344d40340c22030710700c03070300200303650b115199280200810104221035001800410f0a820f0034400e002c028184900148204200032025500703200c0020f0000307a101560030718143e007826440e4285420482 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 421093165 1250 421091915 421091917
    0x418020406170703111b12041d182d1603020103090f0209070f090512060103080f1314120601061b0f0b310309030b060102010906061707060c05070506 66
    0x51641850f07600c05540350800039181c0113207643e0340010b415000b0111b03400b0805240100e030300c0b039546c1c0c2c0c0e6106000501c0207446581044541584422104419484400d001c180703032000000131616038480c000141c1d415800ea01902c01038031040c00ca464064403400000d450f101c09086c40c0c1c2004258902c0c00a000660180d80000d034150f00411040c41c083c012540450102c0c50b003031b54910042800030320038649017a800300404001d00826101c0001500b0a5450581d40d00e0040c000103140480205000041c844114213582d00304d507050441c807140640e10038140a101d02e00c00c0c403050269840c2401842d0512000500c00e04840711382c1e9508002100300824405070007000d0004852950391030958001007200507a200380591100103542d0b02980074410000b08015401d0705e450703800400201d404000c6500050f20341c040b41e07000f290082480d070700c0e440101d0040000c1d20300100703182d01d00b83c00428180c0703045107603c01094060f4125030b41192110000c1d6080850364000070800d0340041024010ba041c000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 421094415 1250 421093165 421093171
    0x3020708070e24090705300f09160b1b0d1d01020f1005060a0501020f0307020409110303070f0302010506030a0f0206070201021203090102090406060816030504080d0908041802040617 80
    0x3030f1142d805207503e002500b029000d4400c00d0002e40c003c19041c152181b90714070400c00061011b01e0b090380c00070403034520401001c010020310340e0312410000035048080600041184404c2c8030740f030185440c2c880140b218a078015042c810b0402101c1c0c5d084103617004000803070610352602034407200c408035452b081440f21f100203091058110701038020520050413040100c3c41c1c00e8102c84101144501d08401401040c640a510080c1107501c02d101006040d100441100c0c1000d4041c2d4020a80d0251420700308509201407041a4051000062500c284002c0c0f0441e4503509109600922080e00d401040641c2c40401e8107000d08140e003d40107a00041c609040180602c030320600564042040e03c030704851240d0030031985101c4d540d40005d009401c4c1e03d401d2040c4006402c0c02c0c20f010115040441c00300182071803d101420526a80744082070500c5002c809807608900c10440c20300030803d182c64600803d400601c11414040e0718000b9080031081c55000f40c0d8292a080e0756074545003820102d078010405005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 421095665 1250 421094415 421094461
    0x9090106080d0e041a09040803270d0315210c170f010f1509090c03060c0c0203010509070302010c0b070507170a1b0b0606070321050403020708070e 65
    0x150000200507105100089550740c0c079803103101103840c0d03d5007400241d03214010082c00c2c3d10220f01c0400160750301c205066410641145955460307507529100f51600544014442e00c05048185811100c4000003074018000e4089035070921005004104001c401c440324058501d00107507810000719050110702c4503001e8107004400040090340e4400c501c0501035103600c840c0d8825004074901002c00c4d40c007409480004034140400700550340040f220030311021203600a003600140c4460b01c410900000b16900300245402c00000c20034400c1444014001c1d19903400101c0c060750802d4002480c035000480c118003240d4041c2c4070040b84d8203603581c40d03502d403520052140c410700c0000c1c059800403e92900031b28900d1001d20407402d9462800c0a00035085a5100302c3e00003181030361710760240004a0041101d50084801d42c2c9032510741029217010b40d0030031045451200b90201c40c07200c031440019507401190040b4000d07001d585406440d220403584074200f41c01455008500800811204240e484130440d11142e2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 421096915 1250 421095665 421095671
    0xf101115040c0305150f16020f10020c1212040f21050301060e0f0a060e0d060510140d080304110d050a0b01080706020f070b0703030209190e07030e0c090901 69
    0x25440d0348080e1000c0da0180c82c40d11401000348200702c4104403194840c1d4084084883c1450011403019440c0d1005280154550740001740c45002e40c000c01410321086040b100350360107500c02c645407000070740040041149030310403d8200c2070068a5001101c00308600382c1d40c4803900351317100c1d2030341d2400342c0e26980116803070360260090304c0e68001c0b00d1201d5140f1809540e6281d42d294500440103010314040703644180719440348640c400140e82c8103422441290b8260130a241003460300c8001a1660440c0d00e0050080ca04040800c4443d801840a010a80380080c000030058404034060100415503030000418a820800118002c04d010160010702c03440000d041f18030240c0d440c2c1e126804d11162080458084170160010700a5502c2400281c0c040e041c5840200700074510510038a650f0700440c4030301241c0030000100703001494400d4040b1400c506005c0c01c418074900c413240c09403000311402e115882c960f01c1c2c1003000c070392403620a00800f266040b07010010001c40d8201d0f000c0000913078000e841c142e01e9640e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 421098165 1250 421096915 421096933
    0x3030702130f141314010b0312041802040b040905040c15020a0302060105061c0209030a0c1508070c020907050c011515090806090d050c070815150f1011 67
    0x1c0d400004120701448080045071003078144440750255a101c48401002c201c400c000c001d003a0007000c8031055600e0300800c65000d240344200402e8010136444000c4d98241c01100e00c029071000c0d60354001c004407400c13640c2259142031422803450072805180503901c09400104404c000428154014581203405403054601c0710341e0315800c3c038140d88000d030803170400b60704009602ca050540601c14240104420b8820700c0c900f4504c0903000310081c614090352026a54003040421443c2ca04026003440c4660000311607030444d48598042e046842e00c01e50420000705200e00140c440c030704c11078854070702c3e0f5805400d009464480e40c000380c40c65041521080c4c0650b40c2da252802c100d120001d500d10003040c0b503001c0240c01c4501d0542c020000d0190390040401c1394400400c2c44803e40b000900c0c454926105e28280f910383c28140d003003d042c611640c1c0041182e12950b40061b02d41611020391324080d120682d450990200c1c04405c5c0071042400b41030b401d0b4420400302c8070004071b41c01100b1211072038040d00151400b5036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 421099415 1250 421098165 421098169
    0x703110c0607290c030604020a020c0907170a0209010c0803061c230105060609090606040801140a0e012a030f0501030f1403041422020d200703140903030702 69
    0x1400c411401e0b24002d5041001c4050f0440300940000030304010f81d515405494584c440a840703200c003900c66402603500040f4483e68510a000c00403110a0042040000e030030070410080c035a28050200403081e002103000b0911440891003107400400c1e0607101c0095090242d00c40c810b13036801c000e040b030750844d071002c40d0300c0355140310410722404052107451040045015150310941d0f4848168112001d83c1c50401449407607991081551801a0100c0c0e0340300c0d0541d035040200301d0501866010b480c0541c242850f4640c112507000c10700b8421210340798104400080348140d98281c8401e440c0751144284052014040d815681d807140035a0707c828140401ca0100e03180340e03c0103e800903441034421092000c928801c1050040c1240200c1000500031801c090402c0704480d41c0102c070074011480f8407908151481c51038000000601c1c002126030045444030b00f0950040e02401051410b4039803c0120741c0f00070860802c11042c0e8051035010f640d4155041340401c8a01c0c02580140e0b86140d051000b4003503a0016 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 421100665 1250 421099415 421099417
    0x5092821030917130b03130b040507080c09010b0a1206051203030f0106031b08071b0b090f03030123030304030606180605040204030b041203140106270503030703110c06 74
    0x26045554000030b000d00b00c1c0c2800c007004115048500442002004803800c42d200141610080d83c0c0079001440c0c2d00e4a03603560b001d1060541080081a482ca04403c00060040102c0c0c8072040740c00301c6040e40e4290318140308100d0500424020710203409010301000045601c074411140c840e001c034540005849072108001105d0740c0380b44070302c2e100c1355000000700000c0703141081701207005012500341401200b941c410600d4542c0d05010b060410800068001101c1c0b40c07188080130f48039500c0700b50b1328802c0345017420030310702d014005c480c00c910603c070342c40c01d030003520200004032030494000c440d0303c0d441035a600031401400d0740ca64059030740c1880b041c0300100114040c1c0c4200e0008107806109105800110800700040d500b031a0b20a622852041c082080480e110743c0b003a55010741d000c406181c002d00b582506600400703807040400f203140f0f0a40c00204905802c00640003008040d5500c14024240d10350400c1606a0a80036080d00b50b0814480c91001074003030409101a152098280c40003022610f01050003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 421101915 1250 421100665 421100723
    0x4150510061d12160f090b150d02090a09020304030e150a03090c0305030309010501080d020c06090409080d05040804090b040525051207020c040605030309031e0115090c03050928 78
    0x4a800404204120040d8401702402082e2071502840407000000005046e104155084144014005148400107290741d04564020344024968000c45403203201040094004945c101c010400c1200442e9440c40e1500c601091101c100b454140b80000400089014104007a402c40f90202158008400108240080c41c0700d1045900001600e43c0b40039912072400180c00c0b01c000564009003884144c0340c480c80100c0d0002074040c0d60100d44e8880e6482c0861300d900c225284003c0c0c1c81c2c58031041c40200030b541c10091040780e001560602c055145c1d1410401192000d440e1084240c1003403101c5244e121034406080c80302d96160800d541030030000d41c1503a0001b04100ea2a00c01a001801044c60b28075051003484082c02041d4015820003070880080380d0f45112240e40d010f0f60105103c075040c040a800d410041755030b50703d10305801c2a00e549091082c060500728901601090816001070068000021400402d008501c100c1c030600c03403441c0c0d00520341101c0d8002500e10f0061280074101020f8a20829a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 421103165 1250 421101915 421101943
    0x16050604030818030a05030606040902130905010b0c1f0b03030c0f060c0414010c050c100e0906060703080a09020a03020411270f040e010b040504150510061d12 70
    0x201a20302441c1c01000d80d8401460428a035030b030181c0060500d400001a0340008109050003030f0351352240000624140103e600140e60341d8000141c510345030303850110b00c1e0100c03107010106100998851418242c24001d071062011503500408160303c20780c0d090f2030400b020f03004031100080c02c804200042030440e80000b020041642c4047d128030f02081003080b4450b440701c00c1414050410341400d40d520040c0c003140034118100080245108288030052081d85a2400000c0c020444410b0883d00540780c61341a02005109091400005660f4103140f0201d40b0742540c955500c0c540c030390707451001034010803009006a0700701e0343c2610b0220050b00c451064405d01c0310140d40c01d030f40720356050200c0c141600c25072440b004034a60250540e244da403654a00c005004008a45c0410b0118040c5640d9006000c80700219510500b450240700c1401000d9030700003604002c8180070700c815618080e01110820f180d10071400000c0602c28a160420b48010008030300c000010440071000d410340c220305161000c0340301c1c412 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 421104415 1250 421103165 421103173
    0x150b0403030e0301021305042a0306050118050d020108180304060503150a06091205030c0706050301050a06030515150721020c1f030e16080109171204171605 69
    0x200915400190b0b410b01100218025468031a102400301151036080c41000c1c0a941c0f1003100314050501060710815003210505103900d2041070755401009000107125103404150f0340300605001e07800200c0b0b200c054440c00f9203911284010796004589621000b485404500380e010400304036024207000030802004c81da60390646a0500c496541440d0b48041e01d420700c1903c2044c001c05c40b05410640c400125881d1039458900601d2908015095201e8010100034901600402050031038020b0302441c140c1d6030544030b4403c802d80301c0c501542154000c0c1d803e10018010055031642c0e61900802070001081585004ca0804040346d4421003520300100340c0c00215401080e5003c040340d810407404059800c00c481021246240c08440c0c1424405030760404105500c401c43d1100c802010814070189a01c40c1c8a0001700035030781c0200078001d10b4500000ca846044052800080f00ca120003070300c0c50080324040d246815103503945c820405c413041d00ca001500c1602882041d250035a01d440894440e4010340240c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 421105665 1250 421104415 421104419
    0x70f0506040b070e0d08030a0e07080a0b0907230f06030f071103040608040210110a03080a14010b0d1d030d09060b03060c030a05090703080a0c050d1d040f150b04 71
    0x42c2180040100040100440014040f48503910740700250000c0380c10881c100d603a9290802c61101502000c1d8140200e80309508002451050028501500f5070203901c0003074654540702d80040d25006c031341c8184190400406054007901c0401c0d103940f810040010101d0610b43c01380804200182c208480c4800c035102d00c00200700300d80750003041c00b907090700c1e560b005940b8003400c288019101c108054000390044102c440c01000f4940641d801100c0800b0320400c45100700941d00c3c000782060000c48080e0015820001075400a007007086016040e5080c03076108601704005585420014200c00c0c48424101f00f045201750416081480180b906441d504030224140c000350901030306a801c1c8101040c025840081001445089101a20703002204018085132588a800c01a81303031a0341c1381c1014164071000500401003a800c03400d01c644440c13080c42642c205154548003a201150748902c5010720140c0582e0030030140c940355000104144081400181003484071450a02c00520340e00320700d490380d00000d42 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 421106915 1250 421105665 421105673
    0xc0a1b321504391e1e0306111b0307110a030c120312050108030c010b090403080f19020d0c0813020907110709020703050c100902011b03031b03060501090608040b010e0c070f050604 79
    0x4003d0103170207612010410802c2035003042e466003655100142000365102d980303540050410b0200c6641c2a42800c0000c001d08058251a8680d88001811900200c85024900440c100429810308a94104280f03010040c504405a1b4040c07900c02001c9007001100d5541411b2040d0501ca00d5001e03140100043d40c590646418041c00c45400880b0b25200c0c000c102c00f08000070754400103080c0d010064468404054542e41261804500b21001620b912400450f40c28041d00d007540c880303403050350315039503001c1180c0f180d24047e030081d030075030b04003a400410603400030b2499409818424003040742c0c03008889035665603450340030880e0044171080f00002c3c8006540495003000308205611840456000c200f54095540040c02c0340820003a5071214040d000003d00900d40690b000c602944255160343d02c0b80c0302c80100043c021b01c2c6501440713011030034010002c07d41c1031140c012f00d4801c0b03612005200d03e523400c040307603082500c4000700300803201c0a0400c0201c00040c1c01524551070203108000910031800c0c2850 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 421108165 1250 421106915 421106969
    0x51c02032d0709090b061009080102031513090201020c06090f04090506012c1302040e01050411030106140105271003090b0c0a1b32150439 61
    0xb0010440d0b0703080ca04000041540522001c6e0054000c5418120320030307a102c0c013a194034420364088281544041304103e024403020810215591044401c14044490081a00100c5804100190040c0d200d5844503020342070500081280d00d0005103000240221100011f042c0c07008000c00700d0f21604140c00422203007084004140c4040401c000c2e034100b25003101407900f10113000501c4181c00c02c078504401025912a688868180b06010009000700c2c43c082c01c15032551002c4280244c00380d884c103000001d04100940318515079000c1690f6240c40c00810079007040e0000c004080403102c2c200e80000290803942d03a1a0480e108110544021403071503600d0601c121000001000008080000c000781c41850b680b240b00700303100003d414424080702e4840c0c02c1060803d0b0780c928103c01380d075021071060881c4410710a00f01602c41c00701011600c00350381e51030340c05c549642c0644008010030f10940c1d40114080b85c0e0558407020001c006a540304d4809499103c203180f01840e4000399a64074544441b030209441d0f11 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 421109415 1250 421108165 421108169
    0x120a060b01030902030d0503103606120b0910050124020d05040501050a0908070f2103081b0904050403081e0603030d0c02010e0304060f090609051c02032d07 69
    0x10030208043c880300d0300401d4441c603d0421600800c00e000000136003280c0790000c0c01c0c0140280302d0100100c90b00011700009200c001c0d010901550007440d40e0b14000048a0188e035081e0b03a44840e00140c0d503402540c03500a0701c038004c0d02c100d0090084802c0d003203142040d44545070003890921880c52201d5010114245940f000714582021900542c80035070140d0b13085812102114020300e80195200300d00d903000c40d120543c0d0707002143e2a0107810380c0015042e81c0c1c681e2170000c2d18890032480c0e658002000c640720301207a080380014046400d060001e200400f0302c00c091076480780d500340d4681c6411480000682107407030454084020804035410b021044582c0c40b001801c411900d04d43d2029410007100103656400740c20661000c0ca034403117076000c070558803c0d004820280c05510840e604c56894802c0500040c00300c8003c1c000050810700c00040b80b030700c18442001111005040480c0901380b40d0b01075210302269400c140c0c1c040c41270b12074044032151030900c035000071205000741d0b409004110501d00d09098a035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 421110665 1250 421109415 421109417
    0xe10090e0906240303040605030408090d2f0d020126010b040f060305070c060510030b010b180621060d020d12110309030712030c020a080f190b06100e120a060b01 71
    0x400c0079043c80740c40010468054580e41d04180d501c0e40e940d46411540c91040d40c10303540d0040c2140030f6090030070040302401c030b021703411464003e142c1a0094007a40e040c0d204144806a0000048100c0340140d4044c6a48106030300f4095940c0c040c0312914480a00026000c0e030200800c8400024100500501c451170000074050900e0282320714200500000e149800000e000f602166a5101090a00c0941100540115400318180d400d035a52802002003581103865002e104001210807aa001d1038904104d41840c07800070b0010b012030f41004114151504018580d07034100d99844020401350b640c060f100c4440328070444400f100c10b520124001d000449460201409070710508c903c5203140d5001c01d03402c040e51801100608150820708007142d11103000e91000c0d403c1140d00102080045020400d0030700c90000318221207c0c8050800d800001c03007000f03c40586041c1c00c2c070010410a18018501c98010109031602212618841000074448580018000615400f9034031843c1000b42c140a44485105e007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 421111915 1250 421110665 421110721
    0x70f031b06050711041b11070e13242901090506041202060d02030c030a0b030c1f020f0d031e02031302101101020a2d0e10090e0906 58
    0x60500701034814081d5000090208540c401081c019841d1a44034104002640c682c12050010001c030140580c4215240100d50340240d500101c0c21861034031116010f40c1145c011b42c3d4543c3e041e80c80d1248480076180d6465001d044c14081386002010602480e04150345444559003601200124019010710b18a01710f8103200e41c510341000541c0c1c0e16015101120b2075507100c01000191840014403030302c66100c0c51642288003200340031b00108000040c0d44201440c1c0300812032440b11900701a034414801c88034a9000859403810300f04002c1d010031041032540c050044070201e8401813211030404040216880000e641c0e856900130000c05d40000e5810f154950300114594208a07001c5422068500d9000c0c0c011240001104207181c802d0202c001052105ca00854580d90000350040003101c104541c00c4543c1081140710081e1950300d907000750301320030645450700b5510049080c0a00601030b407592a080c04003200c00003810f0004038034031074403e483e044090302d4075140070080d4812825a0702504800c204c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 421113165 1250 421111915 421111919
    0x41011406010c0c05150d0c02011a060d02160c05211e010b0a03051f050105360903130b03070815010e060d0c02120a0e040f060b070f1104090215030a020705070f031b 72
    0x1442ca0081032b42001c080e52080d640b90394261544000c0d10030703020041190740031484480706104035400a0003d40c0d00840c0c980d80e0322400f007400804030142502220f62503400100307158605049108600801580001c0003050070420200069081000d96000742d41c2c0ea0841c1e03049190004840002d00c0d020b00314418104420350421010822440920018251039a0300c103005240702c1e5458049900140e040410345180c0785032200c4880c0e01e80e00306541000d0b122960035030104401c2c5141068a10032071056491a80c0340c1c1e208405001507405400851781406802d064410f010f03145d040040c0800c003050200442d810643c182c00a1a01c0e0f2102009840340e4400e20600700425440507000112140455000c909d28a6036649840181540d0307100c074100300c0000034243c003001185903503442041e0240c0856034014404606220984ea203a260083d030141c59814050440d0031154041c50300241007240c01400c004045c3d03505483c043d41508542e02080700b944c000c0080110b1401000305c0fa14040400d00b5084d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 421114415 1250 421113165 421113191
    0x903090603060b0d09240e0d03050f04201903050c0303040f14010212070326060f2707081506041a0741011406010c0c05150d0c0201 58
    0xc0908030213000040e80f03c0403501c061091407244041548120110f40700600e030389201d80070091184140103d2a805004082c2c80d05501a00c02da51040c1810908002d1941e216561510810116a01107003111800140d0b5100d58481e40d03c0c5003400c0c0020883e91312124118100645000c240c0e940062190388100014403101c45001c810004643c440b103203125040b2200ba00503428442507110005030b10f44086280d9080c5503120f10f41c45e0700d110003114030100b040c10a00c4003021a0400311b8815400c40c114043c82c4810341003801c9915040c0c920f00540e401001d01d401c800e071603500000da501d4000954518240081c4d605018600e07030354824204c1d4854501403400003001080b50811842d1142940045001011320281c0008803646806284400482022400100d81688a0b4001400c0b07044455222520244814421902d0481c0c8085400c0490794410004542000c0c03120000c40e020300d01e503480000c1a03111198503501034190021481d444404240c4650b04960720000d00204681c10031415001c42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 421115665 1250 421114415 421114417
    0x2d020309120c070503030708040312230702061b06010602152205031e0307030606050708220b040603090201110a021e01050708040902030a0b0d030801060e0a03060f0903090603060b 79
    0x841881080c103074484025500443c10250b150740b0450b014000061000200540d100c002e000340e0f80b0560824840480014007150001040002079016454480b03039600a8004000500f0440e44028a1680791002d460031f0038103400701c8111030310000d0303005500500000750184010182c00116801e21032442c0741c024044203031481200c488050b20044048140b0603c24144111b410303a11040740380e080342c0d600c11500000c1c258000c83d001e43c0001e241090120f101d0f0321490032142d032160042c0c052410401c99040c182506100c0c502da5640b8441c100c9000100ea2171440013420043c031180e2000150081180005040034441101d1a84203800000c96200169588108401407944039030481046407280781c010f07125803090030000390503024040340000d5002400e0300118420300400c0000c1c807060005200b4000121240b800c010042040100140400e034419110401c00703050040c0f1361107046a81b600c501c81240d27000c02c444100c803522072035030b0018180c00c0808800200442e01e4100151842c01e0703d11111 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 421116915 1250 421115665 421115683
    0x9031b03010e1b0609041407080603010b0a0b0712030b030a0c031b0819030e0a03050610060f120902030127061505010207050607060608010606050403050d051c1d012d020309 76
    0x100c4e01c0c0c003181310b80040c0c03581c0d40105200c03840303205442d443e410181c0c8081c01c007282c112901d03803282d03003000b6100c003007030405242c8a01200c43d030703007409410100e40f035036a490150410344001d4109556604040010740d0300308200c4000c907001c2c60594124506508194600050840100407201145041080349500006140c50b811002c0030082411907071910313049440ca1a1039402a0780490465404400e00a01148440c02403c00c6c2d5036110207540d03101802d491604940b4158070200380b400010034075000050300101c151074401000010a0b658254400141110310420f6061030140450020200402071203008510b443c907c2100c00e0040c54400001d40d100c2840c0103c81c0075400119070001086000d4204070007a1900380d00a010082e19040000c155800c00d200585080c415a00040d0195000340115110380c2e40d940c072016500208199000c0c054a41c20030815100425080f032403042c08401e2140c3d510551807000e0f40e150320543d035001e8105541c010701a000004d84108148081540000f0702504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 421118165 1250 421116915 421116919
    0x4050109060e1908070905130f0f03050d0f0605040c0207050603061c0807030314070c170307020a06050a0b1201110901030e03041d040c150f080c09031b03010e1b 71
    0xc10003002d80070039040a006810f515070b689000c107000c2100400401c00e1816995400350820042e40c8a0801ca11071502807400582012130b40303020380010a1000d032800d9580e902034180140381a003000c048000725280d0b915500c403029070700c400c00e10061800f80038040520400d48000c00485003443c0000e019407002504651161748651441400702c843c80c990300c2c100c950488411921480c3d0390034050007038200c030350308802044800700c0083c070101c1c0038229850072540c202c009445c0c00802000e504000f64005482d00041d84240b034060000148203005143c400c105603080842c1420590052100100d00741042d241242d0400317611003980fa60381e50607910488030929002c0380e1b400220300c025081d803007030303410503040d984a0dc101c0c240070759141450680914031403c040e000380c84d0b0355030101c006844c4100c1160001001c80030304d2100e5520402c0d0181c5c0104011650929102e10ba04c0024a080350464100365110444101204189428412400c807030b096030020f00355481100120500d018605a2024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 421119415 1250 421118165 421118177
    0x718150806091b0d060e0304050102070509040c05010c020f1003060302031011030c09060c0706021f0203060102190204020409060e0609010b09010203040b0706140f0f0c0a0f03020318030a050406140405010906 91
    0x80107680e03480f03810203451741141c020404600f090a607603840c2d03480b50144070301505c101c0703800044500340306407098400c0343c20040504015040c84011502c0c040740000c16603020001a8210409554103241d40320340c5102500c000804900e1481458144440c06007582006031401c42c50100e021080002c807640500c00c03642c0326580f4070320b00c80000c140d809814801c042d244128000440c009400003003240c142000c1d0740805001400740740064003a1b1100300e030340303d0040e0072041003a05070f005031520456806d440280050300b000e4559030904219080c44c1d0040e0324a13101d41c0184005801d04580e00c0d03003d04440c43d4031038604002200040d50f644100d101d9190b01c90000103201c028085140e00c8444211204036104c640b50070450702d080c15030302003511403d46005104005c1041c86040a040715a0b1414030340300d85480703010359041507000790402880c420100006031310004100790f041c0028582c40403540c540c02d0300c480c10303e1001410300c042841c40c85c103901000c11007132015030b030002c10342c50803100c207481c00c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 421120665 1250 421119415 421119463
    0x1b012706050910021332010507060603151d0106050a1203170a09031e0206010506070609050703050607080a050405120723010c0f05090d02040b03071815080609 70
    0x60f00d0300020304601d03150340e440424420b981c80c0c2c0280503072080316001c0792540d041078400f01145006059a10308400b80b000f04002c1007000c2c0d4042c4000c0c242ca14040c00001031020307943e4584603104102e40021650071552042c1402e0200d0580c0035280300520b09000811001d4104004154490403038012030381790041103061041018401c0e491b076081241c0c2c00000d54000d08140f003089029000000c4204c02103500040c10754403466252070035103100102980182410b900c2c4c041480000d43c400384003944d915840354104030200d076080000740d0046101d50000e215038a01010b00502505016000803411410300083c8004108000b85c41c1e0482807141d0b028550715003417032515503120300c0b200c0900b40210702d40365401020000c066008140f80c40d50342c2c56482d4100d80044084034103200b040034440e407001c13050b00c0100150601e41d1003500e402c400a01203880146e100d030102c40d268a4000840c1d1403994956151340c0c149074900700c0050082c4040c00c02807586040003e56680c40e2102401b039000d03081c0c540303d45 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 421121915 1250 421120665 421120681
    0x10c2c060c010905060601080606030f010504020d0204080a08311a07020918060a0c0203161b0b0301080c010f0806091b0f03010e06150706050901060b1b01270605 71
    0x8590744030308040000c10121020340b030590784a80040701c407a4089148500010554203000341168498549604404142e80c2088101f00080d008402c990819036401c0c070011840d0002013005050380c40c0140d03046901c5900e08440c441504944a8001a04406423182038510700350040320038003540d000140c40d01c0d200b03100348102c90841c001c0c958065072086460b4180103080e0000c0510a01890315442964840c2c0c0d07a0400b00c10985642d02c20280050b4010080c1000512040c0e0010700035501c12041c840a00407400240901000c03550004102800000010450b07290b0411003040010313020708000b02c0c1401c2c002e9000e04035070740080c0803a0040d0300b28000140381c0015004610010880c0c0754269071a03000c0c010b0020181e030002d0092003100118517010a0719071610451000440316500480c0b860010035542d40c0740a8200a04400c1c015900e40c1c4001c0354903801c5c840036007240d0340340ca40068405002102c41c2801e60b2102003156581e04890134001d103010880042010b2415002000803d01c1d0700d500b91 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 421123165 1250 421121915 421121917
    0x207021c03120204170138040204031a01080706020606090402040b040603050f03180307080712030302130621050f0c0f0903030a320a0e03010b0a09020c010c2c06 71
    0x4060641c4501c00100400c2d00381426007a417a003070300300307100170807150900d080e0790f80050b0b2801c60726a03c006000744000340f030a401110a130203401e0000e840036081640e641d46441007550048440c070440302c10b4800522015008010180040500c0d1000b81090309000b00414a02e10740036002030300031030311071807200c0542d156608804019580041180c4981c40108040b80e100e4000c0003d2448200408100181030b242c009160425605a00e01505030a271030300e0b030106a50b100c4130703408605042d024442d0f164503a440c461031070b0003068140c9481e140c809042c0311654501d4600703600413400d030345840e0030300c081c5604000803a0307406481084c105e40d40e1215820b5184040c0601c4140e160b2600c000500400c8003a48003010f624140d8013151405001140100949120381d03400e603441d040b60800f4000c100250744110003400090f00060000141c8040d401c011400d0485250040c0b4405500001d000c1d030380310000d2043c9516a00387c0d00d02a404101d5140c01c101058121013681d840404600c00c0c010025a180c3d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 421124415 1250 421123165 421123187
    0x4020a03090f050106140a080607081e07020c010f030203132915090603150a021b0307030f0e01030c02120a09051c020102010b010509030a030305040503270f03010207021c03 76
    0x8040700b07034804150315215020300081d0241028450078000c9036a2941030484c00304080d40c0401004e055240c1d110385c1c007201c05100003400c03820300b88000001c03480c05d900380710340060103488030354007030011003044c2c3c0d0014040c240035840340c4003014070400420918410340058644010b6001c00d256080c6100704019040b070040e281d5501081d800c83c41e051007481031b10071440402000041e5502c02c0b09aa400c2e00700342d1191010000f0000c1450241e0004001d1030803980200b5002608142030215103140180491554000d0001200464140304441210b079402808804210a00746018449010040c0c0000e407110411103040c01201c80c08a50452054064500140070b428068200f401010a041c0800c100240e611010b90165107404040c14081d40f00307030304842c48407102400405909e01c0c195000c80003080c00810030b0b82d0a000910640601d820620786061520080503107050103004241c040015003040c03582c1d401c0c881e0b0300c10480000103803103004403640c01d0504c01d558503000c001d82d81802d0b0764900d140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 421125665 1250 421124415 421124423
    0x60607050a02091b1314030a1a1e07020a03030f0507051c0f0e0d030c0f0e1207031b140603010305150c09060703081f05060301210606030c060809071404020a0309 71
    0xc41d0705150350100017801801c031001c10742049142003011080c15252800c0a6024080b40e00880d050081180c04110301500050925660101784002c02030140049a080d0f5003440141c00400724036050540c140030700c2e001900881400c02407424612800f40c041c2c4103d494042c04803020584d202c025040960121001600112040c0030003a83c2140c070580f50b41c8001d015101282ca00740c9031b80700b1140304121003038202e40c0c0b0382c03100e0204191140801c6004003500c110302c005442a40800b000148050303071004200b40050b4a0f9509080c203048095038401c00000c01039029280900040000c01e41c0020000012060500c01c0c1c400c98403480c903d0042c0e0702c506880141c21010015425040551010f50a4410410807400240c4140442c80c05004031100d40300f0254412001c2c00140b048982d51502d203a4041e640000c00aa0175040340d4480c4203803010340d401a102c80b000018104480c60708503184a40c0607852901800c44035052001c428843c0d110b521500d40203660120354101c10030f000790b104040481d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 421126915 1250 421125665 421125667
    0xd0b01031808030f0f0105030d030b0325080c030a021309050a051915050411010e130509010608060f0c030a11090d0c05010905010c050a02091509010902070209060607050a02091b 78
    0x80c1c2c18110841d80c401c1ea05201c401c6041c00020341c542d00001d07900c605950000f0090603490081410441c00740401c0780c1215894040c20407202001c5c450035050307035204030003000c1c800c0c201d626000709503041c004100015070180e04040003607401030ba692044801c030174406440c0014040c6080c2842881c1c81000c0d10000c203148a844000142030400c3c0c00c5500e4801e01c01c640394944550018045415200103a60040005c807203090780100d60340c01401007524046010b004082c0c0b4032401620f4030181c82055075500e1041e5500c0e2400d01200340306004540d0311030500d00f01107065003001c40482c00340b4480100754003d03660703640b003002c40101e0300002111644000100901007041030b504003000c141c03145100b103d010074210a0300040d07035405407600750388072034010703015150040003030b001d000403243c00030883e000703140001200715441ea44002145e400381c4400440140c40303d1651041c03040300701c0050821841103105022020008200103080c141c1c1c5a4152194035a42c0c8a0741c010101d1210042088480000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 421128165 1250 421126915 421126961
    0x100308070803090d140a120227040f020306060d020c010b0d0524130b0907050d080304060f0510090b01110f0d020c060c0d050f0f03010e18060702030d0b0103 69
    0x2a20710265006280d1041502c8800000c441e050700e401c1c0c52084003910060013448400c0840b4058501a00c0302020040301525000c0e11000d1071104040340b88514260840f032451b0600e2a0801e8403860004040310001145035041c030308000761036401408014941c06400188882043c502900040000a400751a07490301032014589262030306481007050030381d01c1000303110780e80c400b614002050084014224400552050341c42d8012905030040c8082401c0c80b40e00e4000580c0e4459441140d20070f03005404103600c83c02c2514044007940e8076000d1035001541000180850082141600800c80d10103060014201c50704500603101842c40c40405420b9010300300c1403400904020807080607102450303003690301c00094881004158042c815004900e640000340c0f000303003940584020b06110b022554031508290a580d00c00c0202d074002d8014a1122000c18103016a92001051034640c10b4001e0001e080d0502e40020000d549021300e820080503e5103c507400047da90180d4000f42e08102d40004a0000c44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 421129415 1250 421128165 421128173
    0x30c0b1603110909240907120e0705100f0e090a0203160504030302070b090301150806060f1e01080603030c0313061101020c0c09060a080106230907020a080d140906070306091406040510030807 84
    0x1483d400b078401c0a007400a448400d849c003042100030344900a0140d0b803a1084894129541110104004240018104502c44594501200c4c0d071241c918000d01590303a19041030110441c1d82c010b07500c0c0090040500c01400000c3e00410b00106950171a00601d071030b90511700000b400742540c8480d4401001000c10003046001001c605d00d8402d10081c1ca47d45c040c104a5428407410071049001804c2c50203451440f0700c03103903120341d00e081c0d040100141140d050024a4482a06580c040308000e0440740090310b0800a1303c0d085044030148070503040c000c600340320b07440825503120a0000084d5101e05020300010702103550f90b0302060003504004e80200451130710344000710711030f00c59000080a4099407a104082d2846d00c80307070481c03007907503070b54054110180c00b0303074406000360041401c01da1144d2b00c80b0164000c1c4610b060001c0e00c2148120b000301381754109444054212074007600440c07522810090011001c9813016a002e80124059a00007210360721020000710201a0340c100401c0b8090000e080c1e004c1c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 421130665 1250 421129415 421129427
    0xb04230904140f070509060d03022a0a0e0124050d140f010b070816050a06090f02010e030f0d0c0f0503030403120509060f070507030c0b1603110909240907 68
    0x2c0c0c400300700c03040310780d5103200d4940e681c2c02c0f072090b554403d0b80000041d0b9903040803079406030700c103100c0d0044035994880e80010f00740d002c2c1e0007992182c1004c1501302c0c403812403810b4401c01c1d009241800d0710710440c0d41814800341c1e07000030f044140341c5070803070f151982c002e800e10407000c94140c402080003c1001c401c1d40040c01007074002c144c8901401c0500b60001091880a4001b2659110b80c4281030a00e4178141c0084421074240950064406006600721000400c000380076061980340314500c0d11844501c5440007403c445909039859000754015003600070142c10000740b0b01c0d415121820700d0820001c0520b03100e182191000f800816501012050104044d000040120400e071200c0d4280402da40780300006940f94400c803500080c1030400404254124081c50007480c03464041d03d415045940d04c1c2c0c0b140ac0c03032000306446000340d00c40e00d65002c1c03803195403520810410000040e40030789880e9001c03001401c0715001511000c64481c04280e0004101286d2075006c02c6c1107400f80141c030143ca06440003404d9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 421131915 1250 421130665 421130693
    0x210207080f0c0d0209100b0d060e09062202060c1219050708070305030c0d110c0f16150918050414010504170f0705060c07020103150b04230904 63
    0x20911400d44100700384007000c10080701c4400c001c0c14003c5244000d40810144c460060701c1091004403180e000310350700681c0c04c01003150b00303071000010410a251080300751142000500030782c581d07003244042c003c1540034944c18405079002074503058441802c1e4000210303a44900c028640c800d104101014610000900150504010601c0f04284051700030200391390902c540c4130700800c084e00c00c101010000e40200040c42c0c002051484107410301504490f0b00088031004042d220340b1007000b10b1000b0030b14104000d00604000d04402510442802000c900407001041c05841140d410300c2e0b0162903464030804048008004030301d0304c2a44007156036403004c018581036030107507410210510325982d103000c140a0349014941c844142c81c61103030029a070b203000e50010301c0c10344452001005800c0100e54100700c1540507500d42c0724181e0717550700c551001400729120403142132890b5043c40000c020703156802050724211410a0202507091850000d103d6554100100710369002c001c02d0280028444c200082d071071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 421133165 1250 421131915 421131929
    0x70f050706140304031d130f06060c05100b030c0306160e0904030f141b01141006050706020702041503050c030d03021e0c07050301140a0506040216030309210207 71
    0x1402900d03001e0803104450010301c2c0540c101070403c00b00740000d10403040b000100c1003c00e0280121090030000030100454000403124690312001c2405020034248520341c000c01c40e81c2002d807039000c1c5a03595140c4800d4036040d15500e20703076120210000341d28148140340f04004003e040e038503207103804499400108400d43d54040041c1c00005d2080c814107005218a0085406490322150040d070710004461407001100300700000e81d0244000380c0944190b02b40709204a88070350001c118000b882001084040340240000d02122981908122554104089070030042e000800965509414004078003c0c0100c1402c030412540c0d078440c000140032010842c0c1000704412010348049030743c2d143c812000c0e4000c003414510019403484401d480d1070049801440c0c19100f0000351104240d907640000c1c21218004c0522125070030001c200b04205025220301c640c0144100c4d400c50906200c1d0300300007040c44810b00020285940c0307542035000c1c09803041c2e41d05240f0588082a032150000e100d002511078045109142e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 421134415 1250 421133165 421133173
    0x90804050a0e0a0f020a0504090e0a050d09080f0109030e0d0c050604090902040c02010c0818151017030313020d050f060412121404060519050a020a0e030c090412090506070f05 77
    0x220030300c65001b215000c031099034549040c40e0420900e000102083c66100070a0710484c1070b030b00c000540a0051896000c6151a0707010940d14202425041c5a030883c4003200030b9140c00c1009002070303084020800e807481c0a84a04817020140d190080300c801032078024a0b40f00354049000039210f1b040760440e003042031003034606101071213401c00268240c4000480400104405800003440781ea5207c8849842ea1070650403a10140c40c0c8014018a0303008c1501d060385d0120381c120082c081001810a04400c640404004618515054034150100c91010200a10401c0d4080c00078090000800100c1100390560040c0e80407818145040514521300c04850004540b509061189515040c407440c924011b0618003003010380e56031750392480104001030680311003c0902e501513521070340b1486a50b02c1281c002c0c10050f5518510540500021011424244aa805001400c007581c0310300c85100c1c0c01035400301c50420190502c02c01607580880c01c0d00040c0e040503000c1380003000c0c40107032100c0e82801e6009600395 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 421135665 1250 421134415 421134431
    0xb0f13051b01201b1804060506010806151210090f06030b010f05030705060c070f0e0901060b0307020a120e030d08011d07390f060b0a18090804050a0e0a 67
    0xc0030285819020098250408055040e0b5100c0c00c10002000e203000610b4404d0500c490928481d1174001581c080d038005030b40d80204110b958105410316000341c0101ca10506041d060b0140109510511004150781d400c0a40800c0101d004840c558003d4124010248105030710f0560040c000e113201d00c030a840000b802400020220200e115400a54401030094030740b43c3e08010500001e50700c010b11002c45449111000200d00c500c20000d0302c0074140d016440d140d5800d00074070060a40c1c5094001000c110410000d021110780c0000e0000c50329a402030000346d045c1c035060810746800c55500c40c01ca030076002d161100814942e01c81030032030699078409400e0002004d0039141d00b441030b0b809c48d155000b18044d0340c540425201080b1104e04101e00c085000b071210001e0b04c3d401d1100305a814012940080c21032404130070000c503401180c01c110020349460300700c2e600c0c081c0341c2c01020910b03000c101d0000340c1d10a50541400b10400c00c650103400e003e03112065040d5240003210311500c088404408035480e16910b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 421136915 1250 421135665 421135697
    0x100e040614030709021308060708160e18060a08030a1101140403140d0b210c030c0f010c03140309030406090b09060d0f02160c06020106080a0b0f13051b01 68
    0xc0c258684005001080f030b16081600401c004e600c80612004040300050001800040800541e81b103240603540d03100039403d084212203501d600d016000811710502283c10035082d22610311000d070b480200c1504070050345440e00031030b0301c0341d845812001d43c5000c0054901003840e00641556032903603009008000a0800c41c5200d915110b0946000f4006201c40f0b00001016603518003800702d00141d40400614000400700007000c2d0000d043c4401da40131a18031810000b06018031594000c0709080e00605445a103580c0002c910348481021141800030359280002450700c94203e100000c081900201e60b00c0c14011a1a6660f4020780315850006900c81d002050400490040e05c0074110054900c2e414848584643e50180ca007403102c42c204d00e83d003401150714410101802032031050080e5010350207036040460082c251401c0d9040104164015808030001655403003815521241328120030181d034540c410b0b030030104c40c100c1c0c90181042c0710382446500041c031807208510000130f003600d81032584000520 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 421138165 1250 421136915 421136939
    0xf091209120b010b03040c153b04050c0903160512070b0904090f0206030a090611040b0904020c0a050d0201060806060a0b09100306170604020301050a090b0114010c02100e0406 77
    0x50020b005510302c0004205070300e4a00041d5400c1440780c0c07140f001580c1c460703840c1c0065041900d21540020b0781c1410303c1401481c0c04c02c247d10072420044013260503942000a82190350040004d150080380d646c00001c1e690703800703407040c3d4421000c01800e0710f82082010100c003000340302c5405a940f14610034803001700d22440c0060f4010803904100301c4242400c42090030000100180d00c0300341c524950014440300184e803150021842921450700000340c0300c3c0581892401ca4041741c4440d166158100406e100c03507141c98099642d0400103d80140c0e8440550f15609d04015580314002c099104c0d00031015043c41d010f40080040e2031010303040701c03696982d0004000840300d0610070246004401c010314566400e2030b05071100d40d22600e040201304190745084040a8101c1c100c20601c458104009100443c542809655080b0515441c2170002c03200d43e4590003280f88040c8240200003501d2100300825034018a120001150005c0041100c03550408000c1c1410003403400c0c561103585041c4000c148044021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 421139415 1250 421138165 421138199
    0x301090b0a0e04302f032d0408030304060c0f05033d24050301050d0302070b030a0905011b02060c181f020706080f06090601030f091209 60
    0x1c00c948003c0d1602d40301d0000e1903000040030002542000c1d4071401c030b41801000101c021a0651364a040700300190032031001240002008842d814150340780f0f00740203200105652410b24588401038060020002003008848000100b1184840c00f01e00041c44000106c0503600c079901446091240d0020500304440e00132500440d04c0105a0a01c00701e00c10b6000c00005170380440e914010b0313601001c14008121074408130410040c4000301d04800c00c0c0080048410341140c490b25031a841c04c128490448003401d240414011306024119200804051510070005540148080e500c519500d040c03e25151000d0030710724000350741c590b0900103103103518911480b8080c909127540e2301618040d11408002c45241c1d00682d01d151340784038a03036200320780c9036252032010942141c0011200c501819010000e400c085080c3e1000080c4203666041041001c0b00403102c591000040361404031a9842d800181c0082c413098610300c18007441c0031640c0e8100441c0b0f449048905141d0384450206030b176240810840e00c1076074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 421140665 1250 421139415 421139429
    0x80f060a09020906070c1517061c0f0f11100e180601030b131b08070c031202040b1603030612021f02031b1f0605011b0303110409020301090b0a 63
    0x3110007004298200d6014045100c0020107003885d0400f03d0b221481039205640108222025014803080c145402803d0244000c0703042003482d0745441c0100c001422548000c8030803806e00548069035080200052260240e10380c00701005c5141c0596052200303e45a000c2d400d076010b414040c1c400342e10b142c0142600f42400200801107501074000d0403c41110b801c02501480c18951211450320031982c640300c88132810f0061200c00103900e042c40c84000e8010041075401b10500c9000c90902c401e282d4031000000344990182080b000c1c10b0411911a0028411940084d082c0340020902120416250407011300e0a0700030f580501140c0c1c0c44400301c1c80d0301501c0b454000d40c840c0c030281101403114140b0203004000c00c2030b80103032810051072a0200b01c0031503803003414a4182d000300d4a1464103141184e40008044222001008a11b0804001825001256940c0c110301e0080c0d03c0c02004051203a0003e003403100c0039404031a11655505440c0c03010390421702980d043c4a0400410f4a07880c103044200c2001c440700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 421141915 1250 421140665 421140679
    0xe04080307200d0c0605100803030a022803020912030f09040513050d09030606080703020d140109150b0a05040e06011701140106090e13150c02030909040c0501080f06 73
    0x140c51000e0300c1200034002d14580c2a1814080010244814031212550f03040c40e840e88400032100345400800c03543c3c024804c61a88841c1c610501c070810b800420f90342d0001d20302c1c60040e83c2d070b01204002400f032402c1001c0c8032405a41090075081030759041d0041c04060005582000d03000f071880c0d920f0342d1203015041480ea0081e0301030284004615041d005150080145180074200310000e4442c141054103140154012030740a02c000c2040001300e2041c00001c101d04c101815525096a002981516003110050111f02003031140901c0400294402480194815299510880c0703001d51f04011703148030320642e0300c40c01e01e00c1d200282c0c5d824140140c504030400e1a0140000760b08151740218050a0035205082d1503594041160f030740b1801c002007902074001030b1540c1c0d90b02441c08038000c1004500038003107080d0600c882c20042c006404075402c1146401e4440c0c0224034007146e0f9004074690f02030300e0302e40d030750002100041c1b009200c1d10990140941d02c003a40c8107480303952402c84207250380a040c3d0f0042d0300080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 421143165 1250 421141915 421141921
    0xc05030601050d021c02070506090102070b0c0304110a030308090f0c281707031509020a050f4c0c03050304060906020c250305062703030a0b01090e040803 68
    0x2108070003c105000c034039040181000c00c100200700404401c080c58988107a800a0341c3d0051010030003840d40d10074a1080298a403d60565407090345810107061301e5407080380400803800300000c02244104142d406449000c00540d81d082c01810030350161031110070703401400740b41a90038002090140909038090b00c03440400744200d40140c507202c4002004100c8200d02403000c122034002410100d20a29050024003076a401d42c2442c8901010001c1e014084601e44480c100050311000e6000003194822103000611403034440c00b00e07018003002c20307000c0e18131002041001b02e013401c0740da0385210503451600020030100c60008070345100c0030060880390201d01a000c1020020384540021503100e441040040340c0180d0030350b034510507070700300c4044101d042c3c000303106c10702c8204c00880031203507948221040071610a00e036488050300c3d01c0c0045c2441e21070700410035440c059179029990403c1c000028a007101d60f03902e4041c038101d004155420900c2d0000c0c105020005e400c440e881e1016000341d40040d41a461a1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 421144415 1250 421143165 421143167
    0x90114090a1a0a020f07140706080f04060c0e03030c030436020d150e040b070513031112031308070e01030c0e0912030a0204051519050a0e0306180609010c05030601 72
    0x10b40000c0240f60420b070208009880700c0007034809407814620402e42000300448940c7c48038106445034203c0410000440c7c20080c40414041e6825045a040700000540e200c0c02c000442d41c1c0044001440e400d80302c0020590025100000208100c4000c03603024400c1d1b8440c054403188400444c050388080c04595001c0d0902c1001980c0240841d6941c164001841d043d01c502d007400d1202ca9500c41a40c440c04c043c200000e0000c00c803410741e801441450510b03c2e0544942812000c00d039103000160000d04420855000303601c480002c1044207002004903500c940071240001030040b5079025444c1c1a00807400005030001c01791042ca4142c99002c0d076400c0b02c0307505110303068010b05402800a001c0d80300d05c0c4041c00000e1810002180540c143c0c03c070150f5103e0800e010b2000d082c41d05408840200020070007468003041c1032044405109036460219500c07102c50400301c40c903c45110601d030341130080100303201e00286060040040b034510402501d1165441c00030007800c0714101405100420300810000d60a5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 421145665 1250 421144415 421144463
    0x18040512030711060c0d0f090c06050904060306020309030a09090902010c021e12010b040e0f03040510050d05330d03200f010504021906020c0103090614090114090a 72
    0x480924103401c00d0f420228545180c0401910301361301c070040c0019280d0103d046402610b0714882a414244441010b640c2c0703102e0300c4046889410208480811002c0d2269a103801010040d40c03c04000e41d164145540c0458580d88100800300206800d000b002980c1e1006004c3c84101d150140c40d200d5000015400b4451040014481c142d412000daa0602c2c219a817464280400903035400c00000c0c40c00028814081100c1681d031500d940b03540904522840240000308403010360b41d041d1012808030b000b010059803113002d00365403088503c1c24142048a854503200140040700004e903018000301801e0410311408100c40300706160410101d00502c000b29000340d210b0500d90000307000201c0c07111080401c040c00c00071a4451280d13282d4452050100303500d0025071409a104440c00d21642a82c68540042d54a5200103146414180c0b01e080d02c3e014801950f006200740080811044003629001030032600801203540500710050788100840d0448070001031411300c0c00c0d80700c0d07110907441e41d07050064414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 421146915 1250 421145665 421145671
    0x9030302070204021801023a050c0304140a06090810240305010b0909070e070c02030705090903030609090c0303070615090c050705060f1003141513021804051203 71
    0x18190200301a0006032968402420000000203400b2540d400c41d00c0020305045254441c580d00c00c2c001d0f003c4e02203842130689400c5001d601d0f241805a16010b14009035594013400500c84480d00011a0019060904a07c6c83d0341000c0215010449903403030300340545588c41c5070700a81015621110540c0070302c0e90240d2001042c14144400b10312034038805030307501890255a8204880994444ca030051681c108008643d400001c40000781004900f001c00b11258200010301f00e41c104103518040ea4190340b01400300c14007405010300700f065a45040e46a20750307260300c1030f0f4503103004034848e1000448071071012942a00c17039070008001c1e41c500400c6032118805003071460a03501010301c4120000a0301e50540c0f058884001d100e45600e80c8400141c24030070700740403005025802840d4040c3c00c000c02070008030046002c0d241d00c00d0000c138040340702400301480c2c412400204070342c04280314140440103060801401145108030341d00c4005c0350005040004c80c21042d94000c2007070b408200d40300d0b81c8a100d90f001d594 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 421148165 1250 421146915 421146917
    0x40603021309020d06030b010b1810053006010903081801051b0d02160503190f1a060f040908040e06120303070e0108060405190e0c0301053111040903 66
    0x4100e07180c0c400d94003280d104c00c0a2201040c2e0702c80c41001003021141c1950b00500c001d15849040100e0442a98820b041c400001403103401442c00c24100c1e18000d07002da504c1b0a6882482000e0340e60f00305d4841044114070400301c050350030a400000d50540c0709907002400c3c0d030b50080e60319081c0094140205840d40e41c8031085e9041c0030042c00207a49181410f0080303a0300c86801c10040104405455019041901100c4140c48003405a0401d11003074034009014050131500702002d58403001c0718207025039140c00b04c10004100407400d0350f60000c0e0740c1140385140d0040d80c04030360510034004c0b42c604002c200c5c1c82e41c0c1030090184e601404104001c828400140c0d034801d4024002510385803416070710a00350f610807645c01010510904440e80a541e01c0680250b20850598040040341001407220186080c8841c111080540302e101744220340c2c40910140f9454040900203011509101c0c408505c54051401c101e510080e20990740318601c4016100c40c2851908040f440940742c00100c18000903103c0700c48103070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 421149415 1250 421148165 421148197
    0x161502010906110d0605010c050604020607110d0506073903020a0503070302391e120606040c030b0a0b070501020702210d090803090112150f06030608060c04060302 72
    0x4400708405004841031038810501c41650b50388201e1345038003242c0c1d058116504014444401c140044e900091150f002038040b20150f40381c006a20301844114000240f03141c101c2400340217a81004400164103000f01e000d600c4e4420000031503021030312a0980840040f0a0041c030003006041814600b01d45000c25005e8070544034660302985501c0d00e150b216460460044c0e01003100403070340d00d11881a54400c110492612110b4030f081403642825504d01240407840344215062522900e20f429048003480d40c800707000c41601640781398509454001c115003150149007070030540300d0700c03a103e4407a142c013410005004100480c01d03e0148226a04401801c5030159800c001c403002594400c410020200f080103c800100041c03800403c0c10b040241c841030003440000001840160004810360308140c40030f1030701928400710550b140018010519040e103902041100c00b0980c4415071035010240c0300b8903101030055640c0c448c542da95a96048500300d8940c50309100600c0628413070b40041500a41d020020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 421150665 1250 421149415 421149431
    0x1a040e0405121c05010b04060e01121b02010e060603060f070f09030c1401020f0a08030a020f040f0b09180103050706080406140106030c0f0e0a050616050d0207050108060316150201 79
    0x1000260f0140844000f40b050082140d5a90102801081d001d80000846241402e2500700701400c031841c400c0c40300d414014074840e0964100c141d90701500142c41070814644085070350328006130082014643c114117600a030400181c0343c0c01d001683d503001301610400e8450350b41c0c541c4001c84072000814002400c200004000001080f250690180980401000c84003895400790000e49001c0c81050940300a4000a4091001c61a09026250b00000610f8003585c1d0f00322140b445a4603108981080d00941480c05010458807032540c040c001c0020165a18821303180251115245644240700041866005000030321105200b084100d4200740b00d2003003c01d14440c102d40d01035090100760400340001343e542d12400d000c1d550000e001030401815013003620001c1505004110382c0300890107400c1c013070000040e1007012006003244c00c01c0d005400c001554507405910360000c1d00c0e44500d10a480c0085c0c4400045000d0b89800f040002c1d0714241001001000c52501806100c5048015000d6056550b1a60741d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 421151915 1250 421150665 421150693
    0xb070f02011103160b010e18301207090e040c0303030b0a2706090209031b0102120304140c04060503190606080f01050907060201150918080714071a040e0405 69
    0x125013490b803151a8080080d81405140036011000601c0b080d00d003019200008004807000c100300c07010071170781044882d49840d5540041031248045130500c8682070000340c0c0544440c0000c0e40d040c0070711416501d209100b583c0d5142242515130541c0c021b0802607003d10100f0020307000303601c0b0055094001c0e01c50b040a50b605c8080c04804d5407204d0450340d0910f10f00385400c0340c031466071090402401d0707090000c5040620b400c012036507950b41c00b200c3e020300c14560419801e184e0f000300720300c0d01c8108140c92000d60300d18151418921382a00014248014801c5044e42181490306024120903211702038010075140c2c402106050039500c0480081d40c1c1c1c1c5640c0c51380421101424880e0901d48107945002250508042e8422444c1100341e6200000310f91420b004601d000e039558001c4000c42da0080307008174070000340c001412080310b0401c000400120b0001010340170400000700c01c0c6c01291042081c0e601c5c042d92880400030110142c5908403800d80100014002c01d02e400e10721680140c084e4049036504100c00c02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 421153165 1250 421151915 421151947
    0x708100e04030818010e0d080402060705061008010f0603030e1c0210020c090f0903030414010b041b02061605190302090405041407080d0203030711010b030111030a060b070f02011103 80
    0x50306034005403a10040104d01c000d594a003200c3e5018140080200401c0b85802d25228400135a01200f00a055030100c0c05640e1803100ba1034035150041e003903541e04c0c1802580a00d14440612645156500382900581d0040640c4250000c072a010703100c6003104240ca05c02c02403194026400303044004140c020480c0581c130350f40c00c0044001203c0d001004001044020080c0800000b41072810000000d0301f000480728020003503903003140e406055104019002c0807842d005d40040095190800e144c910500c1c1c40783c484855160084581d602614007584500501c548640442c900c83c3c07022410410400000d4103030043c0a115200e018a80181454542030000c0c081d07940680d41900c000000303081c0e48501c4403090000f880100001d0b0b004110207402d00402075268000100035000f40003900020010080702900030040f2075800a000304801c038050050005e0355002541caa100d45841c018002c00c4120100e0708a4494a4000c0781c0e95072001c0d815401150b00401c500039000d818081485401c0c46011061 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 421154415 1250 421153165 421153171
    0x1e052b0305130f14061b010c050a090b130614120a02070b092e09050d0906030b03070b0708070f0b161d090f040c0f06030f1d060708100e 60
    0x9920036503290804124042c8194454001c044280c182150820406458450b000460107090705c01030b0301c0e50400b4040080304002c00601080319400c100c04d000d6600c0e4401c1c01000e0718002c0351104140c05840d01c02000e003030702842c800305401c4680f840040c420706004150410303540b0b00b00e405003450445054202e9140b0f01058901c002c2298004c1141c00420000406042e80282c90000500b0b00058147d00401c0403040f0b0800c03003d48509203048408184900e4209020945d00101107403140903800000601c82c9005105090009242c8456000c9914000c0b45480c101c40c2454800c0e403e04869840d0001c0c954088071049034404000c0f005000090080014203104510480d10028120717401c40f00035200b40d04004031400d481109100c403092698582500d1504031003003000704010355481c2d10703050089401c1600002c080240d0050b00007490f40d40f5420003030007d00c80700014032404a0b282d08005c3c42100c01003c1c0507098000c4400203412904c40d80300b44e03030704c1400d40220700d21142e42e441e030f824820740c415 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 421155665 1250 421154415 421154417
    0x91d0c0d15080f0a031731020405160909020f040503070b0d0b19090f0b0303031501030b120304060f0905100915080c030703020a03110d050403091e052b03 68
    0x4000200b0202c0002e000440800c5090740140c4101400c80d07800074100b2040011102d0700101e8a030109014480101d2801180038250703444410083c40b51151000c0240000b504904ca103042c00000b07440c00740c2c50365124805080c6030300d070700c05950b003001c0c5060060b42001003000d0100f14240710000e003680e41001840010b141800d029591010080c07601d00c10364010a40305406100701601e0103600510381006041140c0030034500013410401c49031800e01808250003025072600c0084180103550002a1a0300d1510b04240c80400400c01c800b001c0c4881d00a4820101459802c04e1004110303250003001040d45030809403524072201b80c1ca5800081c1c216484c031214600080b010402440640c40d424005d486a0510f824000304901d009241401c0d2844002c1a0004254011034000f2003180a60040709619800130707402e035181c241206c2028010001100c0980026001020001c6d4007a20a012030006c0307682081d107600d80c07505160a00c450748400114030075603405500401c0310034000106410304100c3c42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 421156915 1250 421155665 421155701
    0x1802070f260405030a02061b0d03050627060d020a030c08030d0507080402031e0106030803040b06030d110319110a03020c0f180109090c15120c091d0c0d 67
    0xa952501e007054442200c80d81c9107203420002806030383e07000207000714090350445013540ea0308400c4100c0060001d1540820602e07116035000d1541c81c40e090340215114032020707a059281c2e00c2c2445e4540e121400c051190003601146240890014100041c0e048030301d038000b5101c01e07945507990b0b6541c07004100540c0720240a400c0440c1c52072100109010b8282c02221500c5c08018904050300026240c000e00c1d030b400d10520024810101c0c00700c07800c0d040800110740025076203849160508221100107003c0b5942d512034001c0c1c0458044e041e0040c111030a20304035130340086041203a100c066800e0321900540b0755061054200140c2c0010707201300304404400384070350b01800300070841005008a90f40d0303000003a8400e00464620001c40b070703008110141122881c00e80403c54400e80e0a00006076906908181d0103041036100c220507960300111036140c850680002009519420441200c1600e03035805044084051004406d008015011240fa001040741c03200a1078a402c4401030350841e50380102c505030100d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 421158165 1250 421156915 421156943
    0x30f0201020601060804050d08100b0a210207030c060b06090d03021b030f3c06011409061c110a14030f070e18031314190f1802070f 58
    0x1070305021032401000642840030013410182e581503114150002008200001007001030306000b4002c00c400d0041602c5000255903c0300c0c204001c00f402d140e0491006d80425000d800c0c3d0940f002071007104e0325903825980381c1c014004a55144006410200d1030280e1101e030a0140d11010b40d18207007402005071007a0010f10f0700380b03000040a91026101410a07110383c0265000300c202c6500030640e01107244055070130020140318910412000e13039011f0750303030402d441c607003000d0b0a03131460000744140c181c81c10b0340000c5800601c90410004400070880e08130350030070402c0c82802c031810000c030042001f440c8280b2201003014601008500e80c2d03000355120800c038a01d05140f06d40c0704e041c02d0100e00c040c0d2200d8005001040d0500742e043e001e924024041c0081d180b50b00790f158410240a00541d091b0440480c0c1a01c00e6503642c0041c5109160b1000f0072134440d0100343c0d40208014030512082003142c1854210b0300660f89072503503007028803110010280713149800704070250004601009020301c8030303c2000b4442c8240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 421159415 1250 421158165 421158167
    0x621030a0503150406050907053403080f13060902041e051005040902030604020f180c030a0e010b01091a090909010204031e0c2c190b04140c070507050a030f0201 71
    0x48015100f64000c40c50240c0902450311050354035503100030303541003403580c800300001d014015500c0c0010303032244c1c083e9058800c285000f40500c440e84c080d000340d4944156868116108240c46030613a0b60384101c1c09021401000902c0b950001c10580340010030001d10380c2080380c0a080d0038103040c0c89118103d540d55041140c00c00d04070300b84001401c015201007001c105d46074003003540d0341d80140000e48135140529008106680e644c107103000c035540c0041c841e6014107014010056640041c0e031034516160400d1110f40301d541c0144251041150140d6812240d18502603600700d20003840910904c3c109410454111607840340c40b03000d4041c0001c1400103075241e2460800c1204210400700121a21490200c0c0388007250182150784180e444030084c036980307400c1140341342040780581c4541c070005c0361004081280c9074864044e4441080000d4500340000c0800c041081f08035649042442d0b00e48030b00c100418003080c244409000d40e00d22802c02c6850311600d41001648286107544101c803040c0314000400119 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 421160665 1250 421159415 421159441
    0x5040f0b10030206030f0c0f0c0304030605060619110313080c031501050d060b010c06090605040203060601140d0207022e03061505031503101e060e0601080621030a0503 74
    0x10016188070011014110b07800581e480c48003403c40d182c0748220101054075a40d04100b12050b0514981c4142d0f079550142c182d25440c1d810030702c0140d8140b071901c40001e48900b40032044803154185070005c006480203040741510b000a40d440c9c100342c2e40c0b0007800107040c0c03001d00390500302c00f81030303007600900035a15000101440d144a10200c0407002d02001c8c01005591100030001c464158490004100b82c0703050f6004a8018102d494082d105030b040c503444a0500040d03a00203400740d40280c0c29a9007a9035800019a510b1445114461020200300220514084103038040d182481c802420305114680960b044903d100d9a81182d888400041c004c10009940511840e401802c0154800302082e01e03611016065002c01001041c0545d8002581001c540e01800b401900c03071280e031780810400d003681c0c00c02c00d48600c032070984490441c5089030109004100c009030901c5014140d40700200c82c2e81304400d0100201a146569048600070000840014020710240c94401d08a0f52042d40b02d1810341c2802e034070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 421161915 1250 421160665 421160671
    0xa0504080c06190f0314011202040b010e0303090d050304030506010b04061b120e040b1906030b090906040f0219090b010905190e060303091804060b03060c07061d0105040f0b 76
    0x1194104016100022007490340c03d010a07002801e0040c0d070100c0d2502c080c2c01030039090480b000c4200d40350b00042008030f105580845418020707a0104542001100151072103542e00c801c1c0d070362592061051800f11315001180314140c0c2d105d041941d040c00c0d82d0741d07681da00d062401c0c2c0000e50406004038082c8000c0c0da00c50700415141c02540c2106c80c070041f1646070007500d05445e00100082081d450a02d0300d0341d44030382d0043c040c081000b40c004207102052140156000241b1b000301c0e0002820417140078898900551010301910b80000030340099169561414615650024120b0b041074104c0800c200e41240800d01c1d6005020100f00869880090400102030701c1d80398020754456190f4030818a02e800c0303000209070507205182241d0885c0d450b0000000d14500420011942c80300582c40781d8940c030b078614180d0b54081c0340700d520309114070201c2c4801c01d5200e16084910b030270403107002d015000102e403458110b13040341c001c5c40b28600301e40007080e800e003403d58400301c82c2540c1014841d03d6460410043c0800e06034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 421163165 1250 421161915 421161919
    0x20306150301030f080a0e060705161205060109050403140c0601030201080708190e0106091505120721060f0606020d02160b0703110c04230a1107140109080a0504080c 73
    0x407666045130381c1c2c4202c0290181020341407a0000c18101482c034003410901403a1003004062586880301d614007603030b17500c0c00c1c038020141207204207a0029880c00c1c15907504000d940c1c0302d0060f0140b6070a29401c2801020300400135420441540d529140d00740d03145004008051000d0094102c546c11400090151103003e8800010803e212003000384500c407002c59a1481801c417007021400361020f068032409003209410003040b05103029840340100d24140349440445000380c031030f000580718075118151503404070f110b80e12003ca61040e1075040100d00613840036400344100c03400500c04480d14440001c4030711301e170810809a80440c2c1203500194040000d40406840003409d01070303290411003c02c07100e0249800042c01d001640551f1207243e83d051103068140c2402800c1002031003004014203030001001d0340380c0030b203a10200c4082940030380c0b58051443d03031510198005280010640c0c4880b40c0b5045020412043c1d507950500e0800147d18000500b90310805075036141c0c480d402c0c00c0c042e81c01c0a4550701064 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 421164415 1250 421163165 421163167
    0x120f0309080303040b0115020703020a0801020c2401051c0816110a060e010e01120513143904060e10093b0a0303060f0803090a17070b070602030615 65
    0xc030018819500c0141515800500c021fa104803100060307103818090b42000f0b50004c031407031000c03c0d5000c0540c083d0141c51901d0b401c5608510844480c0c03d041c8040340541e0380d281401d01c005201500b020001c409482c00000105500c02c205620f425500380c001d40035481c41ca803c0b4180780420301c90f040328641c112006c1110620740c01c91500c64054152210000c22505005071041c007200280e00440711007010100010083c0020b1410b440c00160303105802404440d842c1c1c4680ba15a0300b1180003a44000100c801c000e00860703500200b0060002c035404041c500d0181c0084115001a44c0b01e9000e1900203216a41118415041600304c2603c0c0e903505410003505280360582c40326200b546105e18844d4003101201864510755441e02034500ca520190aa014611070f0300560b004240d4103502541c12229003540314051551181e81c0300b51240305905c0560f038040b2290f00103014920892403002e10b110b4001e0104c402d0983e440c1a14189500002801e44006601004100e1541442045440c280b00c0f44030b055 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 421165665 1250 421164415 421164421
    0x906061a0c0721050a0c050312030c0412020f03030c07030b06100c0b0a06120f030f0908030901270905060f0604080d050903160801091502091302090a120f0309080303 73
    0x642c1c2c810440c42940f810100450103038048012814a54001607040703c01d6072030004080c20510716055603441542d0081c45000541c540790440da0342075a001e5080213070240c0c645480c1c4848140600806c03002039a026601a0341c0d0740c001d690400050501c40c3d1184060000b07035241d414050311240b4001c00b0b99005110014410400c950701030380070300c030003a0f002e44506803075141c0a404000401083e00980d04500d00d0b03540078018000002e4103425024800e40c0c5040100201c020210b80386441e0b44604801640f003400510600c0d80184a01c1c45284440f9000d41c0180e1280c20704080d5a4559600c00c02c101a41c0d2014814035041c03009881400040a4070913510b400c2c542902da230769031026844c1c4201000008100b81c5200d81e410700c40200d1903d080f00c03580c050303aa220b0f07154074002c0061000031900c080e01c2c00e503c41100e23103543c001d07180da0003401401c04c6002003100361503a010b540900025503002181c1300c4045100d40380303000142086405440c51302032610141c42d020b40395050b1500034261036070040c410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 421166915 1250 421165665 421165687
    0xb2e110c090f190e030f0d06030b071e0203041a0703170c0408160e0718080105010314010b0102010504080a03020705120403110a06020705060301050d0f14370308090307060906061a 79
    0x44801b44540040c5060303840103080a004002c01c0c1a8000605035841e080c148841194850004c51000c001d009554807104490340081c1c0c2d50744a01d00c81e186e03e042e00d500d10750030800306220141c0421b40c000d0500341c0e140e4031200f40b0081000b20866205410250104003880981010441032215802c0c51030314903040e41c2400b101090101008200b80f0401480c4001001e280300400d00ca40000d00c2c15200a104c0d079616803a001c0e140350035900407080151303c2d0442c0104158414080c00d0301503904060024600700d000103044020b0751103000d041d0b51074440c0030f12103890450020001c0000794001c0c1508000782c040d800c01c00003030000c580d2142045602c0000c0611a80c0e0f241001c490441c6c000f110740031150511890990200358101e080680700d40490808100a2100441da5100007030044da06003400180610040c20060315201d0f5480221202184000029024119584d00300c400c00d411242041e20070b9440d01306582002ea0120340c8643c0313503001080710710011500180140704a12081d41402e1403514 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 421168165 1250 421166915 421166917
    0xa0e070803041d060d080d020406080606072102030c0618120c070504020d06030f060605090105030a1a1f030303060e0a0902030a030f05040504020c010b2e110c090f190e03 75
    0x1c1e00f008225540200b41340d640c17448203e54203183d2089a0a48825048044400079041481100081803100d00000c81501e4607000316140598402070348a540c050911030b0900c07410a00392800305504c0200822110640c00700006446244081c0102030703080384c07a8544c1e03400d00750035105002c10700ca800e01803e5201c0b84d01042081c141c50003900e006840c0c000c51030210000c0c0070381780e0000cac0c449041941900c0c2806403640120069600c2034a481c591643d030740c0203140d42c2d242d031150081c0105180641141950340c450761115045001c00c1521041804000078541480d5495403044003c00d0f0b6401c1d04021214200c1c034000d6103c0c0888200708003c032181d8001c251a4140c914004040151100e500658140210306a070041c0501500c21511855240445402030100303440042c8162000b13040c520070749034008444124031490400408510a01c04404e9402024140000c1203034010640e40d201561030b00b84109204140380c812554603800c0002d04600700c8070b02242044c84d03260602c1c4c1d2404803000004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 421169415 1250 421168165 421168199
    0x3011a04150c02010c0812160801051008100f17101401030b270c030c030102030615160206120a0506010804050706050c010617010615080412030509010905060a0e07080304 75
    0x205129010b001e00348012182106a900020318030540070412174000d0345551140c41c414107880707070540c000c062140015039100c0d000748201ca6000310402c140c80112440303443c085400500c04400e59214507115025004105420f410010f100400e07000341072040042040002c04043d002d1038200704155445200c1000900140405480307044420045840c0418128106180060402d07174840c10045403410342d9180c03000300a50728030030701c00d05000c5883c1345018400c0381c0c082c900c002c040c1e007a80120401901036580202c000d152242c80a5502400940c496000411403510701c2a120b8140e031401034030301000c903800a002141004451410040001da00080070b030155105410100e4031040d03200001405030105410010300c1d0500084000803c0205401220681e02c012a41d5842c00042c4901211389410448028103111402911186443d000b5441640c21440c8480041100c25250b185c0a15151090f42c0520340c0560300c00d00d083d154841440040f000d09101e0340038506c1e1910304140d420f0000c941c2d03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 421170665 1250 421169415 421169417
    0xc0c0309090c0d1103010f060e060412020a09060620010216020f0409020a030b100e090327060c160801020f07061107140327130f15090203011a0415 65
    0xd10041410b4103034407000d03640a030421040c04c0c084a962102c11240b581c10a210f11800854144008640c90f40200380f8105040000b5184504040c50500c0304060380c0b980781c1003680c10461015010a294009018403000340c559501c5003822640c942e4800b5246c0140503120440e9a441404980c404250580c1d020011680480324115000c1514000800404403104020f602c130025403000010001760034506482060700340140c0c0d00f4031f43c0d600c80b1030201550480c0d81d150540c004020309aa003102200c4841000c03c0301c4062094002d001d00d0118102c1d91003414031340c5a95000b044105d6800002162000140c40e020000790301b0081c110300c07185454062003100030103c903200c001100c5414584019100401c2c0c122001f05070402072218040d440b507101503101924114101c0382c0d812141c486221601c2c9482000d0401003940031030031070400040813040001c400140c2c0300c03005010543c04941402c4082d103070751280140c0d02c3d45444100410300c42288a9480a140184000c1040300c030f0a0080c401c0484039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 421171915 1250 421170665 421170679
    0x10e03030c0118050609010c0c1515031109060103021602060306030307020409151a0604060e21010209040501050a0807030210050f280201050c0406030b060705150402090c0c0309 78
    0x141001a0035801500d80610580d840e00300c0c08828203031000c00c0c80390080e024200350360407910343c5007803182a2001552a100482c00c0100090002a000c400c03024800c0609000003c11402280400701c00d85103a42c015542d50848805041e501c0c582494026044102400c0c11442c1c04803502041c0f41c030240c2034002900c10840403000070700310340b4140300f151039056008000300500d0507245041c000c100200e10001c0090392030550482c0388030705501040507035010014a1039050616120003203601544040c542070b045086098041c940c07211145032601e000090304000360315006880c00b8042100c20592210b44101d242c400100b100c0c1c400407444000f502d0301500c041240d51a2200195503d1080011814054000182040120034104d40140c2108607650000340001c5d080b941c128282c4030203450000c04a40c5c104020001d4038042d50005640070005080301e828481661911030038a6900152040046015010041180742000e105079120100b131054508000d1501c0e1800c0d5240901c030072060103109 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 421173165 1250 421171915 421171937
    0x10e0f01050f0409020334090c020303130317090105011514070b0601021612030e06031006030c1b0528050c0607020d02130b010e010302311d04050d081501 68
    0x103050101c010302e0800e1f50700745101b00500350301451000894942c2507200d10001c41011540e405079009040c01303106d50390700640c1580c84100742084140c458030000c4003800220144803030304c1d00d042104944140301040000405615240f07000314140134002d801401c100151943c072024644503001e42d01c095401c016294100ea0b10b410050307143c81040e040509140e203070300b10000b0302142415000c90035144266140405c4400f004240801c500055942e0100510800c1c01405594401d80c03041d184c1408903e001d19240c03020440688183c0f421104c2914a078002d0141804480000f0ba0911103640020210541c00c81c101c0d21100d072288602e4403550301c50314001036032905555030503400b4a50716030010241b200d014049280c0130b00600c03541210030301040c811510301e0a00d41c028400d80d02c2c00500c40c0009602101003503c19000c90383c41401040d0b00454030803021442c13400c00e241007917401902c0640501542424140725140c0115160030400b00141441002104118900c0e90800c8190a0900d803000c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 421174415 1250 421173165 421173169
    0x3010b0d020c1e07060504120b0702120d06050a0b0c062e06030218010513140d05010504230303010609050108040314031006080a0513121115010e0f01050f040902 71
    0x210a414000080340320f8184403003c01c01c00034040740b0b583e80c15503045810841d40da42064540d4000c0c0c0c0300384503241c41c200e800f070004250090280c41d44132800748141d840d00b10070310344880615004692586441943c805052140781003a10404d070141098012130360424068004a031740d40c100050005205c0c3d0003840740300d01e000c41042c515100c03103104145034005070b03038407040300030000d400140010013000090b000b00d0301594040c404803102a244001092626424541070030b15000c90800030a82041071a803584012900078898540500d11a181412400e000714204c01444543d40c000d40e5101c0c4c00401c01040415002461641141d80a0802c104541d0300e5090a0b510f405840141c511500000001c011810900140000030b540540c0c54800441d00c803170042c58225001214042d200700160f000d8800481d000340c0c0700020a101a00e004405100e400c3c8400b4101690820076100075140785005105a4800c1658a0740c416a446d01d81c02441d85080b000600e40a0032000c268043c0390355030f42c1c1d2810f40d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 421175665 1250 421174415 421174417
    0xb0a03050c060a030e0703210e0f1210090c05090109020a0801030605040302250602070f0305100207020a08070b0403060b010e010801050105031b0c0319050a020c010806130f09050609070501020303010b0d02 90
    0x2041100564101b40d5503818142544103401460340c070b91740b51030b00c042407580b070080300411f041180160202e011220107900340980700c1480040c0140034411050f200d80e01281034010802e0701481142060703e8a480c2809100c503001040e00000d0b2554014004906601d500c95180d904690700840080b80341d440d1400c0c26030600ad01e814010421100050742000301102c43c2c580c640032103c880c5d0031201d0031a501c070070080190006000c0100300740c000004911080400707402910803540002d21001ca0540c1d030b00d10940c0342240c01e81c07120036540c42c0440d04100740305040c801c0301c01c028020708208013118030b0080000d046000501074141071203c0800401c1034800b02c0d1240081d210000e260196444480c40b070b20a542e90408020070858600440c8540d0791548200103540c1c8580135500100045081c0e500151000b00c00186902e0b0001030141c2100007105c40d83c0102d441c205a281c4000400407110705105013092002052a41141d00c248010011643c1c00011a41152080001d503916422010b140ca0f000e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 421176915 1250 421175665 421175681
    0xa0e01140d020a0504090f02100e130c050903031b0d1b060c050912010e0c01020a0b16030906020711041406060d020309071e06121404020f011701120203010b0a03050c060a03 76
    0x4a4601b0b46140100410b04220245090003100c00741004810305000b180d00700c04020880781c020f03407603400c000740d00d030740541050307400148605043d410004030101007840c54129050050010280c400302801c480402d2144481102c01d0b460000060482503d104101c050f06070801851640e03203281c1c405440d8814000d40700704400081c01042d804260107011400380584440100d25802000030030441d075800003076198003e9501003141e100c0b903650021400120050038801c40c0c10b2603201c0c00e1660000303569100400314030384541020070006056000380400c5582c00c52283c0000314200c1c091003543da4801060f5140794800d484003503600e40c1c40b0701d0154140051a8052045010021541070000031002200b000f41e03106aa42d242840e640c141c2d9060903141036450000455803040f012a01500b050f80c500d18600d201814541c0540000011002c0300c00000d034801868001401c1f0b42804610b820701030903202400840744041305500b035845864649000b0501075108035000284228040d0107a040040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 421178165 1250 421176915 421176919
    0xd020f0102070e0c1c09030207060819020406050c0d0e0a121b06030203010510020c0904080d1b110f0102090f04151809020f030f0c0103020c01061703090a0e01140d020a05 75
    0x16003021400d2510f580c001700040300d810441e0030200c141d0559280b10310fa046a8059005202c6180741100551314a800a45030000080e041d82e2001d518007c00e00040c030081030140d942503510700089900e076040000884100c010481c00344c06408503561161140d070107803410803290010400e0240b8240c0c4902d42c920070302c1d44203256100c0f00022240d030140c1c0a98101e40c03050321654080d88444004903113075148000010b0744070005e100480d002c60b0b07030400900136500751044005044000c142e10b0341148124444a600001d850010305040c4c0e00d02403104001c030703d88410003582407004a0000581007101d0b20041070117182d45c0c0d2540100c1d5050408104000d150b41201c50030700300003001041c1c010f0480c41c10b09a00461882d2503000e01810001003005e000301c20603020f03140300c03850007004502070f62104d1211501da40d2500c10200300b01610025541c43d100440d00115640d139a05414000050001d038080010800940d0040105202404110400303101c1161361341545100d42c8001000c0307014507040300d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 421179415 1250 421178165 421178189
    0xc03030b010e190609050604120b180105040c060e0a0609290d0b0f0f0d02150d15050922080a12050109020c1002250c0509070203030a0b04020403020d020f010207 71
    0x30468210f004101000d4480710741d00c030089071703807600141301c0580725600c59500b030504449001c10115003402040e41d08400e00d00115408541804403e80c01d54200b510160380d544900c0604110290b001031226002f004161081c804a40c6440009405880540305015510b000344011940b240d4032409007481c0000c02c0d0b1903641d16040c0000ca208010400344244d6401511940e5a0040500e050042d05200b1040104400f442080030340c00d0200c80c816128001c19100410302001e8103442c2c0300c0c068036141e0b0000c0907400100c20301d0402008a800030141000c5d20b011254005120303030b0550328a484d0036031f0707070440c00440d034407460403c040380d801040c3e4041285c100d203810000704d203e4055030000c00c00c60030b4500895411185440d0070808900c06c0010310040ca05d49008900341c0a0340fa4602d140459004040c3d6005503603840703021540c00c5104540781ca0043e040081085032885203031080c1030f04010180e074210700340350440d0f010032210080360704003902c40d07540700c80100c0c1c01da803082001c1c0340600718440781c0d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 421180665 1250 421179415 421179439
    0x1315090c0906020111090d0201030209121207061407080402011407050d080a0c02010506031902030f01180312050108123108010e150f0402010c12021005160c03030b010e 74
    0x408000701c501a2000650a104541080c00448000c1d6041000c0040c040754226000f41d0065000754041d4910507080143c0c180c4010300004180001181000000f480b2035031403100b86488403c031401e485c1200425180302081c09002607025001581c002d50a08240ca20005258402d120394002d40c0c4000703003c0d101e0030300c0714400da03940701100501a410802040c840404480030a90a85000311482034041e440840c44603024100c00c0f4a90b40d295002a098414020240c0d100e00d00b0359424000c84500c0641c0641048105548618100440742c1000c1c010800c55043c15a8541c892070007100e42015030340081808003103003140700a0303801c1c1c044091400d0700c0f0318800340f1005800c4103080d20901d0515440d280c0b58066140c0c001c230b009104400301c0b507a1507400d9501c10114196241d000340c010790422040c04001d400140411640340100b60582d001440e069101c903a400c0103039040106100d43d54441700c1010300502da0408022540d040c3c1c1414080b803200c1c0500d0040f9401c100000c5610b90201001c440c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 421181915 1250 421180665 421180667
    0xb040e09100501240c05100513050a05070f1d060d030512070801030506070315090f06180f0c0903030804030809010b0616060509060417090406050a091e05061315090c 73
    0x20041281301325442c980c900e1001000155000b020b40c4c4009040360300051a8040c1021b1f0a40c003d0f944550011803001811380039071100391822040c1d00085400ea403145005210001d10903085074000c002504036001025011250500018400780a242c005c3c0c01d00491310f0b04040c0100e0541d0303884260344d4480344143c40d140e0030080409a083c030082d900c0340200004150128400e02844084000303404090003041d1403c1d100f140100000030748056016a200d0700400d4411040c00d10445078002c1450100c2c4500807481000221260b201340d41c0240501c0d61020000203070030151243c1d0154040c2042c0009a445d1b2410f14090301d800203a06502c044001074042203001081000301c1d10a024120401c4030f1750f20709901c643e44803000da5001e40401c10f415082400079960784020680200054404240306035901c0115003600059041144503648a417469056008030040005020300c683c1400d104030308011010130450694100c8451100d5110681881100300c1200c940c80100302000f804c114414a1000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 421183165 1250 421181915 421181939
    0x17061c03020a02210c01050702030f060c040807090203102c070302130e1003080a03020c030d0605120a0209010b0a0509030a0506070f05030f070f1b050303090c0a0b040e09100501 78
    0x40c12403081d12003814031342441c0124250914501100e500414103030080070010b4906810804d070890b070500c81c02d0070200046900b4040c66005242c0d0b04400c1f500d40742001c400c1405d2114a0f002410030300d1040c010480d400414071000001c580300d115803407110b01400c0441800180707982c41445c1c2c1d50076501d010300c0149039050340180b44885200090221032a02c4031010b0350380d01d40c00d8032001000702031441c041c40424000300c002d18000c2d446d420014a06005000326504581144145140d190798828040015040941100c8080b80c00382e809414022501d45c0020410390060003011281200401c0d0074516901401c2161000c01c1300034219a0070304258500f050342c0d814100c580c040003d2003564a502841e00901c1039902402111200a940340e803031980803100030720074110140400004100b0f84500805420a554416005201469070b92030304900c40f0703240c1010380301e001c2e000340c440d03040410100c400c03102034605903071101d8501c80780e64444882d850701e4060b02c2103036036440394900030000414640c0c5103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 421184415 1250 421183165 421183183
    0x18060c03012112120b120d1115070c14010203070804080a0207050301020f040f0510080a0c1e08070305010b161b18020d0b0105031306090311120903071517061c0302 72
    0x14080c481706460005020113142107690b050400e50000f1100000c0d02d004101c005094007a19045602a8949020b160f10310041501c0000119440100d60001e001d810035004045003051002586141071080d4014402d0a0051010300030590120b0101600d03442407029100070840180259210b00e100340070078040740d0051203800908281d020740010707a424440c08455142c0c98175200c0e000c1a41e41ca0303c09901030030a038101c2c40c080210349003510f50700e0540b241020781024101e641e191624a40b400015040781e5041e04485600e45d01880641100c40400c446014074960200c0300e100c1c052450a01d0501c000401c0e00824014802060040c1e004842a0f0141aa040a40e48180000500e145c01521f4921098800c07d103000725204199002c03a01c40d4001e10709440c460300e0945501416482074034107040010034903481808002600d684c4600d0100503100141c88240000442c0c101405005041c80b103a0986000c40c0000c0180001c4899440d426803000703440c007000755000d094865240081d1104420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 421185665 1250 421184415 421184447
    0xa14030114070e0d470601020a03080408070209010b030901050603010e03091311161a0402090406020702030c0405090709061d010317040b0d0e060708060f060d0b130518060c03012112 80
    0x14a034842c440700e040c075005c10300841c41070300507111140301c546040755005001401030b01c5403030040180302c0058541142d10381c001c2000a05260b16402c00104032829554050701051103603043c903010741a050b001100300e4490303010468030303070719801e100741c00040242c840b1242c01160b0041c045450140c031450b0030780c41e000c214032a2200d02681d41044100a06102099601139001644c0c04000340008800b40e0087c4806400203048800f541407000008069640c00c40f80f400c8203030003181c001c211201450040381302915401c141c0030a4460f140380700c0c1544c0d82c01484080d0030880030900c12080701402c802168080d1400d00711840d500c0800b641c8203005803c409200d955a846541e00250740240b003101000d00a510041010301510041020003900b134018000400329203545148961007503642c0c0341070041c442c280e0a0b020a0700e140810044411403c140215205500800200805400320600300c2c0d0544403003682c2aa1603050021424039418800c0000500b40c40f100c0840300c81c040c0e00500c40b04042412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 421186915 1250 421185665 421185773
    0x6020a020108071b030c031e0e1813030302070201270f050111120c031309090b01050607120c170a11071202060405060f07020a14030114070e0d 63
    0xc11104030b540d20081903070031312070911071100380340000e100d4858154454020320744034030180c02c103500c41d10034060031450782d101207120714220301080d091260905045920306403078950760303142025122040d0150004004c0806600088002c216805180216100408200d103120300c00a00c0800542150319406007008600b101c0c08002034542c4120350030b142ca141c064003d00805007003044600c100b900200c0c0381004e503000a1002d07030075883d5038240400007010f141c000880e4148041c202791100b00c1040e04014003645007008078901040c4450310301800f44d8601c1c508030f51000002e090400c240b030300036070a00c0900311001840c103192541c4007511104080814003076030000780e50352804400c091910301d0001d410440900041009180000c00f070201c6900b09909207142c1001c60340050f106401e01e800070031500400c0d600107025820300744103003203400012144501041c01c02c13640142100c6842c0440d20b1107015040c1449042212050300c4200c203ca0141441140d0001c0d4040b411070300031101260740300c6540d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 421188165 1250 421186915 421186921
    0x309030315040608300706060f050a030b0c0c03040b07030203090406050f0112050a0f060e0f1003110d1103102316081509070905041401081009051606020a020108 71
    0x10745880f55400f1241180010a0300b051100b0040041690000e412103400a00c0540e2450b800398607001801d100744100d030300203480c3e81010b26003182403200b40c005a0240010440c10300c00108845111600214101009078031413600d0f070308403072442c8500e81041d01000400b0562204068000000c3c1195250446050028944032014040384011160040d80081c00c500c12185403a0f100c0e501480c0c00c518201c001142c0c46402d055185c050304c4041e1300003010100604204000b54440001154001c0341c03000002d0000c41c5107484011411a0b0b401030144103840304211300c020404103c00385000100040d00743c1d0310400b51006c07480c008044e481d03003425032490151201000241c0d0204201e2141201e000d076180410744000c0c003160440c60040403440701c051000b208800c0c5a60f00e030001031040550790b13503541d8201d080509000035280c0c0b00054540d0784070b01a0040c403164038042182140b1100c1050300180c0d003002c0d41003403803074a10180c5500142c0c5c1d030811808110760764082140d507483c5000b80c0302e0b0328a80e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 421189415 1250 421188165 421188169
    0x10c1713052418010e1206070f09180e010207170a030b060f18010c080c070f120f0611040306060e040b0f130b0414010219091a16170309030315 63
    0x8810018180c6020340300f0403180881e44011449416205018586103e0484200d400310700c12003c00000c905003a4072600820040950080e8802100100c91410341420f61400c400741c0c80c40c116002014441e2502c458032080c6028003517050f07070030742ca4000324961b0842c40e05005068056008101d140006030600320058000d04089c07040396030000d20111014502013041402000f1440c08a000a040142c161410004071354480041e0040200001c043c0141d00c6c580700a0700196141c99004030b64078440000000049206d4130440072040f90850404610046084040643c1d48a5604001e0159150031000715100c400c5070001442980300d01004052502d440541c1c042e000030480e4107186032500110349500080120130b0580e001881000840103c1c40b9500328942a80c200116841100d0b041401c4110f000340c1c84103012008080365040418819058100c01036240304661181041c400c040691104005040182d840c00091418050f5100e04044170075645990003070f14640001690610003a0040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 421190665 1250 421189415 421189459
    0x60e010605041d04020102010608060c0a09141f020313030302100c030b0603040f02060d0504260a0e04020f0d022d030709050111010905010c0f03050c0315010c171305 73
    0x51543c00b00c030401c6120407040054600c0364010030481c1155210400001d842500304a014000c4c0c4514100c15203c020b03044008041d00c459610503070440d080031001b01d109441d00c08481c4184241401d4103482c526102000360303c2d610682403148400c02d40c40000100349035001c20699600b40601d83d044c00082d14040c402c400360749550f0042d031750001703081000c40c0004a59000e06103c8a1016081d1801d0050b500b03203000c12100100c80c250b41d00d100d00003d40e0300e2200c1443d60b0040b8cc2e0301d1095540e0500221950041c0403441c2424a6401580d00152505590840030159968100303150015580c8200780c20a11491a241c001002800022a001c0209101c1c0302425a8810400c0741d8511407006d2a100044883c6c00e024800c02c442ea540c0c580e2007101044013800f0b030b403601080a840381c0009880101000f422a00014180d0200c028240244000d5030340780d80c00d0f0304140c0c0c0c091809440924a030b041486100425100104074902c0000d0b04c00e22401304245044122402100e0b06845900c00075607031451 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 421191915 1250 421190665 421190669
    0x60b0309071512090807031205071b141b12030a1418090f06010f050306091302060408010204090902010908010c080105060c030d050108060a0b010c1101080c090301020706060e01060504 81
    0x1a08060820300040c102d0400c0c240c0203481c2454400c000c2400c3c9400ca408642c1c20390402e86081c040041d0070414180c01200140d40d480c102c8000700402e1508100007090110121400295808818902e03810b0216911f40b4900c40c8040364141d8100d40040008030071000342d0140d036940288000011101c02802c00302c10794084003015111103407103440544d00c03da12a8400222041c50602d02490303500b00d03856402149100304c1400d07074480d2850410400150070345c881d0025100c00c22a080082200d43d03203a903900c942d00b194000c00c010105044910014401d80295080503001d0341c40403c000962840316040844c0f403500170380358071201c583c407001c00501b40d4400d42d00c8003000c45d40302c00040226040c00300003040074008000aa07810100c5070750429080c0d4000303903c8503c0c65444035050103030400d2240b180404400742400c00d00ca500c1300c0e5580700d440d90b0340382c95040d0307040c0110b200005900c50700381000ca0f41c4002005000310350350289844d0a10050829001c0c40043c0e524080000c11800d005030100d0741 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 421193165 1250 421191915 421191931
    0x5090703080a0e01270305120f04030b06120d031b0504031208090c10020a0b0907260307062a1d04090203010905030708071502030f040206090301090b1603060b03 71
    0x4035011090b0802e4031030889042d4400d0410041c01e4030080d080b42c2a1950100354154005141c041a103507040903498040d00c0c0040101d044400c1015568000403103088600b2230303503c4410b0800035520600002c0044090344001e80990196048495105515600c403c0540071002a9101941c10040701114103009601000f4042c21008071901c040038007032044142d0240301481100c005010840201e000042c000c0d551802580c4a85511010008803a030410341c08041c002c010140b1342c1c90312146180304840d109159108240452140004040034400c880350f80b500003e051000c5c00306042d0300c51881d1003c0840010108010951340020361148600744489061382c004d1208151204040200801c0c2c0316900302d074599a201007440002e50288098840140581e024603110251800c01904100f021071b403125900307204008010000c003c01d901160020b8043d2500da0322010700901080c010640c91002034010701c5004200840719940c00051509030034031760b4040c0400d50382c07002014081d01003501c03245 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 421194415 1250 421193165 421193167
    0x108060c0702011b140d02010c0210150608070302070506130b0f0601081b0c0607111e0a0b04020409050703210903080409050c1b0a02040c050711130f05190509070308 73
    0x126a00500180c01c006960194001750340564040401501d8003801c1e40300700e0b01503515094110882a01488104d41c940035240c4288603a85040340c142140c00340350300441003841090404240454480d9046e12443c580c0f003403c403211414040c83c0002d000705110307411592141340e280014145900420982e000302d0041e122036085031079412940703d88041c1c0b410420300181050040c0103071000100301d100c0c018080c03074540c01c1051551100c9503040411100c040d440e29182c111441c541808000303600b1060035002601500d585d01c2d144009005080d002401400b580b094000102c1400a03450000807410b003103080c0004160b0a4103400d0b04e503c2401e20014119801c240030030404440e42c0d0f0081944020704e503a046140c5003600500304640440d40c4205405640039880503011401e05200786081594241811070600d15543e444030320000300306122600074a0705c4009060322401e640c03c000c4668071303140820710041c40c04400344a1118250102081351500f01004a00044e00104030340303042c1d0350409105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 421195665 1250 421194415 421194437
    0xf0e120307020a05030d0501210507290a0e1e030a0b100f0303050408160e18010b04110d0c0507020904030c03090f0b030406060609140114071a0108060c070201 70
    0x805054100402000941c024010020005801840101850350400c000000c0c00d50405104414540481d20441041038803200c4d240d0204000280d46402c07600b03040d40c003001c4240915100070ba02d000042480c00c643c000410904144c40d0080801005050140e9038007400048118041d03074102506000c094158012444940c041803580503d16807085030700f54002d03030307066440e800c0b040076180507030064000039404581030002c1e42c0f040c03007060f040c240000d0007403a0850800d04203001c5003a001d80328500710b10052100c1d0101d00f00a40240c0010040200f04004030200d00c6010529544030204102d07102d40b40822401c03506001e08282c0710000d4001c0e02c0c44d40c141d92155400d03104140c64103015418000c405400140b80180c1e8482c41c1c0c0070b0207110108036101d081501c4e001050f64110b0300700ba000d012101006004008400d40c1a05a8030390918000d0b43d0f401015169003064800c0c40c802a2403045070000c445404095a06030300c1c101c0b07421000b1030749265510340030309640b801100f1000303000854501c08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 421196915 1250 421195665 421195693
    0x30020d021c0c0f0b0403080f0f0601140306010909020c0109110607030203070b0408121303030b01140904090804180603030f020d050409020334090f0503060a110c07060905040f0e 78
    0x2480031840341c0d0480d1a0043d0507182d007840441e04842c1100011507600410136410915401d1a07000808011164060b0604900203085001101070303c444100000c4000303001d40c0c1c0b180421800400030201c0c11940c40744c143d40300354040c01d03680c801035604940d0003100b0000f07402e080d0104c40100c0e4040d03000c1c42c20001152713101070039080041c4c02036420740424030440d104201c02400303043c083c4d10f01480303100035003000745000f0307050b16030381c101142c103008c0700c1700c900070306501100d0850718485011a07000a00d0700140c0b400114a000f150054802140d8070341281c030705412a0351001050300d00036114052000300b803100480c3e507030903080c2c00c4d10300140051204004c0744101d40c02854201d5550800f4411f06101c06c96088141442e0980e29a11045170f0b405941003290030108850141004445003095107042801281d43c0b00005801c00002c3c40d5a405140945030a10f41600c0b80d40c000d03101034407901c03541c4610080c02001c0c0b40c01003070f00c02c5181040d000c02c0c4407414440d5208014240c0040c1c102c420f04d03280 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 421198165 1250 421196915 421196927
    0xf03031819031407030b091f0b060717120f40210323040c051201150b0c0c0d020301060506130f0501260430020d021c 52
    0x32010001a5074040001803601d00504880b40616005000d40c51a6013807600d050b403030242c80c0600c10740080910100d820810384030410103032061400403e0881c660401b0901520885601800207028400c2258400784036100500d44075040201a00091702d4416260042980076503640002c000e64101003245810003030711448201500c04050112840c07c00321075565401020700032900f1400c00354484c5d020841900c1c03500c1003e5143c0c80c0400c100b0b1444264101c0700101c0d0380e40c2c00d00160507a00040c0420105c0c2111402402010b4061010341d1b22061019010b04850241d0446220002070082100c01042c0709888070283d048004210316002c41003485000103012000341c0e0155200e68000c0741c2e5403680c0d401448080c0304008000056454211076102c081c40c1030b004181000b0300300328900c1c0880d54207049000c514252440c1500700e61694036100c01002101e418800010000c1c007405007818883d1041049444510b400341d48100b00c09240890710381800104001540c68409040100715100d12 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 421199415 1250 421198165 421198189
    0x1e09070c02131103041203060b0a0e1507050321040201090b18060316020f0a03170c07050a0b01031a07020d1202071704050a0b07050c040f1805010b0f030318 69
    0x380c0382031075460035801000b080e144080c05010303c0c50400018001040101c1e03480c5a2610303a01e140c00c120703540c00c000204004d440f80011380020495510310741602030b5200d401d0140b192410b480310995841051810a469402485083c1060300c1d040008941c170020180d151441554142c0d90409561f080007001074080d0000c00501d010111512401602a201c4600650281c014001c0e100c0c050f604400000f403074041204039608854002e60300340e0000a40003910052000c0030301480c0961541c54a2500006005252014203540320701e000040c01e000c01d051b41181a03074019241c6d020400740d504200400c030b035029925030006078405c1e6080e140302440b980c0f548a8880d0020310141c074203a441c0e00c50b4225a509444800e51401d0001010040c0b40703054100e0b0070040c2400405c460070301190b5219940c8503090a019140203d842e40501032000b08540e03c145200311741c0d0949d1040d041103038103000d8000c1c9030b90700e1091301492819444e80c00d103250000545290111100e00259407200002c244440c6040079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 421200665 1250 421199415 421199419
    0x10f14150d150e061e0f0d050a0501150e01080303060915040e030415030b01080c0702010c031b1104050c180409020612010305031201050109050108060f0a09060803091e09070c02 78
    0x114005601d40900b140349200619000c100400300e41001c0702040172000c5144a030305241400682ca9101c55141d01c0d14089202c482251601010042814079604000314904014429442c3c014140c818440c49003100b000d480d1002c40d8100f0710b82e21030745101e540307220070b0700c02a0781b00d036420b000507900210b141017018404030003900100d4800f105400d11480d43c1c2183d0490101c2c0038920040c42e5402da403510480d030003140d09181080c02c900301442110414444c5d044d010b410880c03600701800505014940e44007000ca0003100000c4040003030705240e0301c0842c4018040b4070407070500020801c5200c940003600c28040c1c0c20500c1c0c440002d480c10030000100000c0e80200e0304280e0034404450100040b030105070003903000c1c0b006140e0300c01c0d980702c0c0c045c020700c1c050700310a040c07002d00c110030f00c1140d91040e0f10aa0122094034945000c404410005010714004e500c904001401e020010401500200c06042040b40607518104c2082120312080c0110500c0c2e600b4540100403480042e030b5192003034244407811800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 421201915 1250 421200665 421200671
    0x15020303190e01092d0f170912031b121b0a050303190b030a0c0603050a0608031603020705090903120a090813050306060102011b0c02061908010f14150d 67
    0x30040b050303425129100d00685590701c0402d170981044036080c1000400b162050f040741d00740d40440d0383e00c070840e0198070406032009290358444030107a01d12004031041c041c1c00078001c400280c030803c6181d660354011140b00c03170903488405002d000c000c0c6c0050480542e040d41698203041910264182d03101c0d02c900c00400102b80b1454102c05c000c50300620007980100724041c124000c1c107042850380e07429121380d0300040d406a0700c948822004030344544000b6081e521246404611520741c00345003c083c01050b0080b01c254000001d55604440980c02003440d502d1003a001d96520550b190100407a014080f1004181c54004200b89020031008200c0c0b50b500104040c40003413030400c0760b261484035030000a407400100039030001c01d2005250070444941e008200740300a2220f10740d01c288404000c2c0360311a0100501004c40e80074411507840806640c144125807030461840c0443c3d103002401da00e020701c92202c0c80070702418040b9021140c00b48030501280041c044069450802c0303642d0320b0300e0380311452050480c0e80e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 421203165 1250 421201915 421201931
    0xb0a0b09030a151d06090c041d120301080c09090d08060d080301030b0a11090a1412060c0307080601261306090b090d0c1a0a060b0307090f1502030319 66
    0xc0050b940b400345403c0d00800080008850070690744044a1081240256000f202008083c070700001c0d5003d02140c0540340030030024464070702004401c1812001c01c5a80c0605ca0911040043c1103001d036041350120030440c2c0d602340f0388105000c60f0b0300b415103180016800c258459042c01c2c0c0510640c0c1d420600c058460344200010f40c90700d0038660801e0b0011070f003c0c000c0c801400780015150051b00e090003801200b00b440d0020041c00a14101034074031134800800c075680d154400c10741d1081100d400007902181030751000d180c840900321480d8021a00440820f6104003c25101d5224403500d113200000d41510140202c1c43c111064074441c001440b00c1103505040b503c0d0030018403140540003901c0c0c0b055800a8450038034140b40b9003004010807110082003a6000e940021030300c80c90358102140051001100283c030381c0f04c03010010388916000214114800400e22103030030b40c00040a4111078030a110103070880d498808040f040342e140c05400c0c005900134404962401804d10751400090040040012200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 421204415 1250 421203165 421203173
    0x60412140d0c091406070f0201020705132a0c0303020d180609052811030f0d08090f070303080c0a121a130212040305030405101506020d02010b0a0b09030a 68
    0x81d11201503110816180c0744695a500e401c0300d5610094002640450040603200c40440d0b1030f400741200c040d00c401c0748107a0702e4065900a00c000c04c06080c0250520010050290888000e4018040c0110f041100550b428108000302c6619504103070540e074516840c4051074a0440c061b400402d9650229039a48018005181203022000070346c512030714012403592500e0900e242002120100180031a0541200e19046500e14052081490b441020451600d65900c042890300808801c905114401c3d40d10407502a900720a0543c82406a04d0840c0d180d161180a455241c000e6844028007040d00d200100702a0381080303015080340840c9107480b15030310155035100300641740513030520300c3e2407070500e094034003a800c102040300840740005500750300e0050400c244602d4008010406001c015020012400308403040c4a440e0008105c45001c1c42000306010144c0c400301c00034440c81000d48501484090350a0060007044c1035540000c140310130192622131900445e502002030f05071300d4060200110001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 421205665 1250 421204415 421204417
    0x91506120403030e0c150a1403010e2a070f05030c0d0807260604050402010c0f0602040905180d052214030c0a0807090f060b19030b01030e06041214 65
    0x519103040004500d030800707040180444060366004180758014025021980d15041c0101030512012140707280d031083d85004c101d41d80e0f29000e0500c61746900001c00000c002d4910302829000c0d0040c0b0285840394115081c0c1202c0480e402c040c0f03030010040902c100f00203e0307548100e42d4102170154040d6803800d13522943c1d035410001d04050010100c1e0910341030220156200228258001c0e10144048144501c01c0891481440040c0007d115a44500020307046911804075280044d42c011160100c10b500b03460550040e4001e801010b0b404c9180100103000b2048021001e081c2c1c034064006170481e50f40c0207070100ca0690004101e01e40000b0b0400d081403150383d50020040090894080c0c02040003007000801d802c2c660b129046500c521001e0406110f4500041503400c2218000000004c407449042201409440282e0014102e00c00204580d00703211074200300e00b105451603030ba0030402d400c01880154100c80e102c0f803100e40c40c4c0c1d02400c000341c000351211680e04040c21342410587e44401981d4500d181c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 421206915 1250 421205665 421205677
    0x513110705150601170f0c07081204021c0803040201030b06130f14060f120601020705371202010507020a0801050705070c06170a090c0302090126030301060509091506 73
    0xc82c0e00c45010640c040d4111455550410401d1030566a400480d0102c001d110001801110300c507040600070601d041e42140c1220a204d9224041544540c3e04084249200404483c181d01038031141140103e4940e0f142d00222010358458411411600da035001100105028a00c050300528204000d080c030f840385c000a68000e00303040713200345115410141000100740c00f642002d030107000240a90100d00695106403940250404141c200a95a50300104d01d8000f26500c555042982e0000c50100500c01311031300c02d80140002400714800941078030090702d490143c442c0c212500c02580790361005600c40c1005107082d60004258626698550701e03420b085650550f503e40106400152007003c015441d40100000c142d24103015169203005044410f8400300201010101507441c0c1d1a00300700001481241c0103507802030500c400640c0c44509083c03030b41c0c8803080140424155114001000c21001040300d040e548540e98080c203102c4001d0921110340c0c00a040f005698405580d034540e103480e1400a00030f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 421208165 1250 421206915 421206923
    0x6070f030c1b06021506010903031107030b040804091b0219030908160512070806040b0604150608100b19030228180618060f02070905090307030e10080105131107 71
    0x4802440e00f08007924051060700038102c14020700c000c024880c3c0c2c01c01011011a501824582102000821201d041c441d4035000180188641c1c014801800711150203002602d200708020071910b143c841043c2659030441d80030740c0041c0d01c000c5466104507419007804180714444d08000e0001521008503034204480030900f0440c6440141d0200180c0c9410311184841c2c5404601500038203051250b0a034485000800181c00c140840c000f0800396222548190742540880060229039611040010b01c075440c180c5400c41501004c46011410040d030304221880102c080d00304003000300071100290041d412402c0d8204022400006107007280d8950500340208000540d200e4003050f08207960a030142500d40c0201c000c00a100303200e4540701101c2e000705801c0d2100c1e400c21101401e0803100480c501101e40d00b10824032030030b1038180000f03000000054185a4480d4407002000b4500a0034841d006406e601381e60001a68480104801d04040d440340002c0c4441540c0400da1142980510700c00e03a000c807404613 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 421209415 1250 421208165 421208213
    0x51803070b22021c0614040c0e070e040c0e032a090a15030803060114030106050a0e130c081902090328081c050c040b090405090c0901030f03020609060606070f030c 72
    0x100701702c20341c072a12440d410300d800d40c0390250400d62038565070044240031703000c7d410100d607010076005801001c64051040000384248041c3d121040b00a00d20209803140703a00900c580b04c5400310400c00140703014900041044183c9511000a04000e16000d000c0c2c40140065a245d0344584402c2014404201560003091816aa828040d000528040c5400d003080514541800140031881c1e001e4120303414000149001040c46000a000800c00401040e050140919042d21034160940100b1b40314490308003030b1011440d022150a030003003603104110900307a00d40c210107805105101030b891081803480440100b4190070ba0280e541c85c2c0e6aa214000b0444102001020300071880010b0041a900c0003540c00d4190806141c03c003107070320754007814400030b01c900c1e101d2000506a10080000d03e243c181c0c0200b4464040d607490610790705001c01080203400502503100052003540700042d1907409120f000d0005868950382e511200d1201e90350300000c80400007855000340202c4c2c0340d040304001c0b0520300d81201e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 421210665 1250 421209415 421209469
    0xe0a05031c0f0306060804020f21011e020c120a0207080d03020c0d020c01090b090d17120a05060a03030c050309030a0302071e0308070b0405190501051803070b2202 72
    0x34090360141001da508042c03d21005200c03086c2d01155a6400690580d0016003a4081178000703074042c405c08840c10040050920040305640b015042205148155901e04404041c0c5141000903480380e0035a601741540000d40c0040e00342001300c01090803040b00d20603144041c0d29801990300702070a00350403100003034003c12914443d00c02440303274950491850000300300b824085000a0106001031082101c0030078041501407580c1c0700c0c85807003c101c60380310341d00c076241500c40007121881d900405000c10042038040c0008454225520400e802020001c29080100b407030b5a45c02c41c3c010540f91821a26030006204501c4141c40810071034448034440d40281500c5400c140100031051000c03440d2540610808108002061104c0211181242c1101100760749a640e420030303900e40003045002e0041d00b0040800c005c203008040d80701ca40186810045c4c40740c82c1c42d207090315680d00c0c0a403440103054000303031501003088620281c41e80034003420103100311440d101c52a000101c01d500780702c0d8040b424009801c41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 421211915 1250 421210665 421210667
    0x120f06020c0c13020a17060d140706030509060f04060507031b0801090e0304060e04020f0f040e15010f1e1103070c03050c06030c0d0c0e0d050c0306010608160e0a05031c 74
    0x81c28504a111004c506100603024020030440e034a4444000800c0d00c1e8005c15156250022a055150341091020081000003412a40e88181c98403403840000e1501022800881010034498018403d907000f01540f81c5680e10b4080c005c05001d0602c1d4141941c40f403044000e01c14418180d45030f5501a2180c003413942c50010045c05070b0301c03190707043c401e950000c2000740702c8c9075000300c000e8090105c159001600c40300307000c222200e10300c1554a13a030101100031400048817101d400760a481401010a105810060040150381120040c1c2c1503001050b03180d850780000c00d800e0410848400040c1c034040340c4407074062021900316880404182c1d2640c0c401c82050040c01800c10680360605c1d0b060b03c03194514031308080344581d036000f0390700d0080e03105403951500090345204030800b0800032401401c4051107020352410316a140344030310b081d0b40240118400085c2950258001070310400e045640c1c4000400f40090844d0426034001401d503010303190a4022034191400c110a401c2d8980090b404040701100c044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 421213165 1250 421211915 421211929
    0x201020606240715180606090207120503040615080f010515010e060c0f01060906150206060a0b0d06090e030304170a050d1a04090507090f05010f120f06020c0c 70
    0x105890103000da9080c0e0304a09429141c480c1001c2144002c010784844a51908044151480034201091418400d508150403020b120b00d008081c8280b10030011a40d580c8060313401d80c002e00c4030140c41c03108020f1403415458020401980e0043c0300d24000280c10b1220f000c100700e04e0200790070880c09503102103441e02840d0803d04c14241c1111542240ca8050007640000800e440e420340143e038050000814072140001c000c0041d142080d08041c0240240c6840d0040300004014901c50103070080f40d1100252603072400410003078040d0002401c0f0b400d00303d0a00c0c1c00064990302c14461b202000340c3e5a41c0c00600000d0521400b40c02c0b0711507901540d0b0b282003500300b501c420580e0892824404804020341072159401c0b00803140c51030741c06c890109881c032008521980350500d2240d85a0840d05000301c150400034041005020347e07140d01800c00943d40c0e041203010031642c00340110021500d45a0040c04510081101440d100303214850030081e4140ca039a8400583c0c00c01124204250701600c410ac01d14501a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 421214415 1250 421213165 421213171
    0x20d0b0303040b0d021c05040b06010f081003110a030c090e060705041215060e07031e060303020c040f180b0f0a09081204290121051f0f1802010206 65
    0x40c01141800c1c00c1014003002881200040b05883c3d600254000c00405a20071141c0c491125180800080c6070034140201034034004c80300a4001030b00046140c0d9041e0241c00098003070310454000e80b40c00c0303007113644401200481c47c91b41a400000000d0010000701c10004502c00741001440c04107606500507041454660050500b2003800401e00c400c2c058036001519007034880307030840c15407091105140008070040210750402c00341003204004200c845a0103403c03002000501550384c0940e809440e00c00c1c3e041f940c0c43c0c040240160400903082015241c19000100040c0c0740810010308440c2c048009015107464100c2254001c26040c01c0bc81d1500941c03584a6210108510a02808000d43d541d910b0501c6210a0018100c6841c0003180504c414008040c4a0000158141c043e08805450040c2e08000910450581c00a0200200c40001d2409480c0c0d01899100c0c00801c58061004c503110307c40003020030318048a581e121a0f6160054580c02480b0a009004401c100490803500009040400c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 421215665 1250 421214415 421214419
    0x601082a0d0606080615070609200102070609120305030a140403090e0a02070803010312020705030303070923150d020d060e07030518190809040c030605090a06060e09040201050702040609020d0b 85
    0x44001c221791a200c04e031a01601105510800f039940b007492606000900f107446024102811600040450b5400d00c1807122003c8000d808442445580c2d010445607110300d0f01031542151240410b0000007406100919000b82e034517000410f200b11441c0a80300c1401d01101e087d0009195507034100841040b000d1410740110110b0f02c15450810ae9844000300c912043c40000c00401510684c956024403d01c0000060800281640c4e503904000300b0060619049010300d00c034407007040c0300d0005a10f995100f0b804a480020b000205140030b0340e07655003015000b0100100c0600d03020000081e035883c45d0720030320019241240c43e04800d130400550040844500600c410119003d10601e0725440d240000e1301210000e00c010450441800c0d0703d015003030b500958070030581050405441203c65501608100d040c0c400685507079145a8a09004000741c803958418a0302192114405003c0c0e42030030114554018010f040541c0790001d15408101124001c2d4400c101d050390101c0ca00342c044040d03018104240c401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 421216915 1250 421215665 421215677
    0x3c020402040911120a02160312090210030f0b0303090d02040b1504060306180b010e1207090504050a060506090408090f01090806090709060b0a080a0c0903141b010503040b0601082a0d0606 82
    0xe200c4242e030640b1841c0405400d0040620927100889c41c2d070b8016000c400d502070050040d0740d50050300a00640100c91b43d03544038070309000b041079540c10000241c0b50818030040c1103411a030f440d40c0074171009100c22031000750003040c403050315500780201c01d0041c40104201d59001500c145030280100e21088071100c40301c2c0300390420030007024980c1e22850964001008440b011100c50a82d40c596103440380b0344c1d226104050518040205000c004620718240078007072034040c4140c2d9101c800f04610b4400461f4020280c003400d20240c001313030030944624150400c060511000d801e4a44689a20701001100c3e06503d940c0b00800130b110a185a000c0e40e00103280130340505040c020105005030071401c0080100e0392441c3c0c8c42c403030030340264403030200040290741210300654808035042c100e40c0c513064485400010412600d07214074480d4481c1c8100c038030850f0400f0300301038141c403400d0044400f480054621042d242030300c1413411444030407508000c1c62122102440e81e69049080d808002c1c0c0c1c220b82e00c04424084 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 421218165 1250 421216915 421216927
    0x10810060e091f03081201050306040c1202031005040807050d090b040e09011104230f06030403050c1c02010902240a0c050708070e043c020402040911120a02 69
    0x18014164038100c1204440704841543c42440521460320090b00c41d100c020070401d000814000c0d034600401c8400d40c0313070100d100e8503070b280c1041c140e65003400e80d401400562070fa041044000c40c03d142d1110110b01c001c083e40e0750354008000600a542083d601640e21800000c3d1400070032004100303403801c19040e814003c45680c07a1030f10a010a014500c2001c80c5840d142c40001d449030400c1d4003050b4040541031000303860f10340302c8001c2080e040d0a44540200700300e036215546124030f0425803040000d50b005200501d55a01c07698102c030960419081c240d6a40301e2060114602021102c44001440591f400003404100314010480241c2d226a01c458181d00581a4000c1c0003112008031880c0102c1790034048030020041c0351042c50001e2076030000c46240945040414504035000080340951700520941102c160340030740030610b8103209281415152803640110201850f42c1ca01680070600041005044c6503440505009449002c00919680300c80012054080c2030700b03907200d58002255400071401e00c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 421219415 1250 421218165 421218167
    0xb030f0607031a060a0c0b09030708070807020d0c140a05090621030f03040c050a0b0901090510050d020301170d0f0c15020408010e0615030a0308060405060402070f080901081006 78
    0x291001d000d01d001c040e00d4075001e80b060305442d8604000e202c006025142d9540c4c441d40000c1802c2426001181c0201080380420104440003080e1006aa00f11120500e04001a960040240e001a0040ba081b000010318503021a200300c0b41d00005102c11030030b14903100000420005005120b4000d58403500303000e400d00c000350700c0d203609087d11088a4200a40d800000c3c4442c0c40c41d500520781004d075032220010802003004981c502c03650032104141c40303440d412620303038801d4261402640083c80c0051300c0003808103c5450005194071100e0704504020b46460000d212136020f9a10036007140100c01c1c4007058030703000c2c410704000441101109190603910051218001003c54410840141050702402c01d0810f070101d02e581240c008001440c005c003d100e80c02030344039803625812103218140800840020403141804520951241c3e410703560301c0e441c0e076510003c00c0000e00d0081c0642c1e800503402c0c0100c20000340340c440c1001e00e4038022038006460740d40150004094a04c000d000d03010180204004220342d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 421220665 1250 421219415 421219423
    0xb04030c050906030a1209150507030816111e0c01110304091e051812040f05190902130e061e0402032a0a110d141b150a0b030f 56
    0xc1c580031100d58845858520009250a00485003d000c4040c441c42070840281c00c45090030841e091006071840b01032402c0c9041e00d0a0181c50700240202e20114006200f00028656031103020f11503043caa90514550711007685000d012400c51030305044541d0003090782c0300e010001511f90a9007440c01c1e11115400c890600c0d204d0081e03104160381652581b02906a1108203111140c0e1b00d01245420411b80c64441c1440106949201d29a003550082c0240d08040c240008115815600301180c070780c0ba0945010706200320304901e050f600300795034030050700814909001c1c0002e105840d041c4590b01c10b1141012000c2186d80409800301e0300c200b8110001c0d8844450344401c00301d412004032030040e01c2c0e43ea6010118280801d4000318506800902e400c01c40c00d094000145c07000b514150380380301030704101000b0b0980c1c4020300d1382d001c8046003a4403040b06030100164001c03c59440582c100381c40d104142d1281500e4010f00c2c80b10107011405000810000101a115154220b20102c0052a010322801806511 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 421221915 1250 421220665 421220669
    0x52b0e1c02120c090411130b1c110402070c061e02060f070513080d0f030207020901030212120c030315040c0804020411040b0c010b01020f0d140a14160203070b04030c 73
    0x51550702c00303400c0481c0042c0001060354a0260000105143c00d2910318a032071402403215200d082074800d0000c4480755441001001074001d01080254500d031702c010312018460b01c50440d404951392850b10178036200c0d030018215103445140288505800c007030340a0a81001d441c0307815429910b911140c0d444550018400340c2042b14000500d0f05902c5e2007400f01d803640300e8615640090000c0103000211010002000d040403102e50b80c071901d865450340812001c2c1e101d20500030f940300104000500141c50824000000c690040d400c40d0162040c0c411101060f40103070b200c040b4103410110410a5060400f4501903124004550030000780444d040080c104440160010380106e41c0c802070f03081018510421600a41071078844030b6241c01c50b081d903444c0a0304046038107900600990002508021001031070001c0d0f5031054440d210300200800c40c03100c1e240c1003103620702c0404c030324035a00390f00d10441440185005031028080511841c0d05006140c0380800da41d20002d811481040208041200d803100d90342 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 421223021 1106 421221915 421221919
    0x306050604090f110105120a0501060e0103110a0c020411070501150f05031203040219122003190c050414090c030c0d030c052b0e1c02 59
    0x58a40b00540140301c907001c034045400040071071021401d207042c185060303418035a000350b1041d8a4982620300703003c034560703400c0148425940007901200341d60f420300f41030002c0c0b00c1e0319414a900d4400c00325001d0400c408125000219036035600b080c5058002d8903000384e12504641012402001d00d035010091900403403200080000009078030700111503004028100041c403d10710030354907904c000d1089034814610303040c00c00e461440d04d120710f0151607800c1c408c00f0302800d5850704074031280c07407440c2016040c134928101010598000510440621144554804034280c43c981000d25214035081203500500308014004442740140300e05101e4884002110b0b010100c40c018162284028035417581c024010a100c000840e004188200a140c4100112900a4014501e050f1030881420038648012007841c40c40346070548c00304026400701d10031500805400050088403010701c60840b0001c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 421043165 421223021 := by
  have h0 := BRFrame.cov_init 421043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 421043165 ≤ n) (h2 : n < 421223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
