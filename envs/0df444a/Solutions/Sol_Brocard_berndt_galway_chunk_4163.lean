-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4163
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:45:10.765268+00:00
-- url     : https://prove2.me/submissions/1ace92b6-5a22-4519-8054-f6001dc567a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 748561151 ≤ n < 748741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 748562401 1250 748561151 748561169
    0xf060927160e0f131409010e01090b0417040902070803010905091b0114040306052a0f030105130212180708011518110d0204060f03090305030f091207060f06 69
    0x1c40c1c02415032400400b1244610314200100c0c400d5101c448898100c04c1100f4801e121052a11421010040081d101d80d21503618015200003c0001032080c009901d900c4092500992159100e0b022822241016981828820800003a110130700d880104405ca116600c8162a9850400014100d8400408d04101d0750464280c032031082108009082a81409080a03580d503184100880d001e400345400042020f403030032040c00300321080300040c840150303082040c42c5c1c0d210300300240a6002b030180681030210380c00d0a10046c00180340002e1503103105200f004d001400e090f05072080c540010300a4400d20920141e0744440c0c85100000c1c0700c028090002d01000b03004402d00c4410107602d088103131040507110b244a50f000c0a00c2c0100713811031541e9510080440c0d0f1070b0380c20601d22030021b502a00c9068040b49001d07040c403000c607000e801030140031034158584078250343d1400115400c2500007040c01000b40994020041c60705000030203420030301e0140300e00080c811410f10610007200c074580c00c82c0804d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 748563651 1250 748562401 748562431
    0x60b04060503070311040c05090d031d030f0f3703050f12070815131d010e070603150e0a150b0307090e0c31030b010306050421020c0f060927 62
    0x294a43d1354000422319070bd4a8400b2807400242c001c54412501c4d0360307403180d02d03016119034801c09841c001350006980c80d0342400d40b1109100a4580000401070040c0b002c1008004460454020b11140d8561003460107814068a400e407040e40c0c0903101c3e0700109046002505040a000b402e590141006174081c4021582d503c00301c9481c0c000800c1601c01002a600f465140d01103050312386048640312203015030080c02401002c1e01403081a8840c03025010324000240342c0142540d07006030051400c8215a042010754006403100c10f0b80002a000e148e445401c050b004200004442e400440150f105940b0b603540d00d820f0605000690516100181840840c944140401100b10382c10780040391400d4140040c03203074600300c2c0c0010030b00d1411082e8400b030015480b520000050003000e400c40d07072169100e030b40c8a01d5165240d21048850b1080d404003040113902640b01d6001c6410100e040400400c0c2c002c01d0b050400841d54000744e0500b05070303280b88074109c0c1e1401c0008075090501d41c241d500044c1410510f40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 748564901 1250 748563651 748563667
    0xa05150409050606130e030a02150703052202060715021306140a21050903030a0e1f050c130312031104031a07090b03100e0105030f0a060b04060503070311040c05 71
    0x290301c210240c6520700c54105c105422011083c107600c0250101d001205490b1200c040090103900d410100405c880788a1081c000501c100d032280c0325151048140036882621684441100b07000c4481c1c9200498006400300480e42c04200c94503180002c0c1008080e003d42e03500e43c10201c20030802c40c5503002100380481a102032280004000a0380c620305601e19102c0c2d800e03662044089109901d048903d41c0041c074200501003068001310046211300300f403102c00e001880d04140710300d03503416008400c40d0407004081c00c1e540b200e400315002250005440da503520300700442819104441001a03004544000681c49880100c60f014050410040b01c158800c0b82403600d5603e0301000c030641c449044c0c500c1816080001d81341307401029918042d10359049040c1e11707460007c6110f00e000788540501d450f0070000c42c00007c0c0500c6c000a169601c54a010091320502c042641d07981c01402c3d42c2c0c07800300d074015100c3c000856107441c1003000c0001180901500c85200c00c41c0000c0c401103901002d400400c0020401a000d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 748566151 1250 748564901 748564903
    0x30804050405090c090405030304110a060806130f0606081009290301020d020d0e12031e10080a03050a0e030606010c150f020c01060609050f010f1b0b0a0515040905 72
    0x140454400740c90226442e0b83e40101d884c1403101158505901422000910040c00000005584124440c500c6840e961f1003403020082e214901d88100c900290b100c40000741c0a0408031000d400e600c41144000c075102c2c00e030302032400c15518550004000078469808203c942c01c0b4a50030000104101d01c41008040011015424142d0b075074a00249000f95030710340105191002d41c105c40c5015070302c0d0703000c40d164143c20180c0000703050466074a0900c1d216050010800d042007804403406000d541c80e1140880414500c821081e1000803e88001407010b1840080c1100b0103102d2200c04034801d984540d80c480000c036001d8600071641544ca80641e00c42003c1184913600248200d2040341c000c40056142104c3e044090041d1201d00c44920400707001241221a0040c1504118181c45040e03c1c2c480741c01d0707150030034032918202860080d40041c8820500b0010f60303014080c03032400c00c074031094902075424003900c582d001d601003038030240100b030707541c2c004c00c01010055845603050040480702030166400b203441d41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 748567401 1250 748566151 748566157
    0x1080a090308130512031611120d1107061b0f090e07080a1b2a0f1b030b0403091a0c100b01021e010c02010b010c05072303010f0b190308 60
    0x70202a60806254400c2c130200300004c0c007001c542005c01e90751740d01d0100101c04152440b15642800b155040030706540d0342d04040b40c120141e00c0400c01d1141801403040890b80900075040c203a00c4141400c020500c0400c3d01405800c0c89a001540724030122110404001c2013021946c3c8942d0400c0301c0b000051100862885080360000750901e04240c0079240c01c4081c50040201280900c1d088500141a0809a400c5480480c10420900501c4101c44108503441100340c02c00d5402015281141048000035103001d50806580f40d011091440103034480e03940008000040d0b4054001c00c40c81e60003044940160413503d840000c1520510f803c1000c20f9041c5a034607820a0030000b59142c41d001c0051450f442001486040070039000e0b0042029050741146008080004407040194200002c5122a50082c21001c9540f43c0c808020149035180800003010740d040e90007202a0f01400101c00c18a80c0d500b4003c0074403000244a00040b60f901e10800c0111181c45210712030304000500d041000828020415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 748568651 1250 748567401 748567411
    0x20d090b25051c0c0c05070f0602120a1809020403060501050109080307140f071d0703020f190c02150a0f0e0d0b0411090405061503070f1509030204021801080a090308 73
    0xc2d103440c448401c4007000a84090320907010380c50510311130b06084c2c1c8407280c001914000d0082e00c00807603c0f070450a040c0f05141c040d420259000c20381da0035080a1010007009410154a000b282e03c41c00e04840c0c51441d805540180b41c8150003103400e00a021007072098600421003420700703244862600c0c03100f9481e0b0190f09000f90519000d040c2d1460902d106020100200454005607042a6102c102da00694900143c502540e0301181c000038040e64041d100312140382e07140c000018280f0565a000b42480140800ca0b40100801070b00081c006031160b01c000400070741c00c1ca104507150b2120041c010403544048010404100f8480c142e00ca144e1505029039842c80c0d000103041000d40d5990900e05104011003035525007007d158010082400800709030540103566900c05140030b00000800c00da550139a0340103601c5403600b946c0b002c00980a02018240210440e0704103000c42c180d8035000a001ca0b00040d4861110324010722403901f40e981e12a0a2551150990a0070010500c01d500e00403c2242d00500c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 748569901 1250 748568651 748568657
    0xc090601030513150c031a0105040302120c030102030114090f0708180f120405150723010e0a0b01141f3006031103060426040504020d090b25 62
    0x10200303030080a0100c0d07203072006030042d101c044003000d0210301c0c4c4000c0ca074001c0b1080c0000d10b07010001048a01242140400c6001656000d08050840e004c0009410b01040f8200d03461207400d141e8800c1c2e440a0001d9402442d03120b84505004407004180840c0d60801003031018211840c40400c80c000380c10005140d04030400300c0700f503902e00c070b200d60165180c650300710b500c034030307076204650340c4032248410b68008206903070341a10800c0302000d0189402119001d0390304003d18501c01d0f1818088400030350000c00b1b6030008134400100c3c0d00120103440b1400d00c2501902503d80301c14081c014031291043c0c800c40e08683d4420f81d518030b082403001e83e044c0040761540404c80104588040403013002801d440240d0994052042c0529004003842083c000808103440222034505204180d003030940f50100d2564030450304001090b1800e0116000201e480c12070305151040720405020100d5940c03074510250407413203010a00082d01d140c03507091103000b00e42c0050041e180724a281002c82c104080c03603209080d45203e40e007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 748571151 1250 748569901 748569911
    0x30e010e0601300c050406050a030f02060313150c110d02030f0901091a0309072709080f0c0105010e0c091003020315100e0103110a021906060b0c0706110c09060103 72
    0x50300f848040e100b060b0721a600064041d8210b001d00203a8000e1100b1030310100c60410989a4030b000340581ea140ba40f2000c1c10700b5100035800b00140c200003006552000d80c1c14405001c0e1a02c0c0d0b80c9194110a8070380e139200c070407551103c82030080c980040700f08030a9104040100690495103000035501c0c401c9800d0480084e001150040d01c1e80d000391160005000c00c2034810000541e0400020607641044407400224820114005511001e020240d40f84000c0c01504010507150582c4120240401040c1290065420041102459044005440000c208400100c0c3c0c40d4900b501c0100307211070203004543c00709070805c45135a17681d40d4001d50141e060924200941c503542e40e0a007030001000d0280007030307800101003c0301c4c0b80c42c07907440303460300030204400d0701e0401140f00c102490b49010f00034a504040503038420203085c0c08500d1071481e0440c99a2040c1800702c1c540c0e45885419005d600302c004100070992042e0411311500d034100c42400c2e50740e5010740080003000d100200056107804082c0c10507050560314 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 748572401 1250 748571151 748571189
    0x9030806011103161703180d030207020a03112b1a09060115030f0c03330b0f0903070303110d03050907050f181504110301081b06071a0601030e010e0601 67
    0x5e58460321450290040c060722446d10b00c209280000340843d5640650041c6100124400e00034826101d070075401030b00302d040313440c21a911030600b140780e0304805030700011454140994035410030500c11200c10158100c0c4c0002c0c4949020b07007207520301c103039812295041e050401c081070070002002811201c0e05500c018030011154400d50041907401c2091055030704008902c0d904c1c80c5c040d0000179501c071141c0780789070b50500806c3c0e6684020840845c3c0100103c502e000402c01000058090304103d01d040c00d0f610720f03008203000000d1818035298800c40100b0007440805020920500c40900310508608061006240c0a041251180f0f80c0d40070325031041102e0300140250f5100e0340400154003250350f06081560a1100e008114a0207008000d481036003440c2c1c107440350700000d5040e04d0498070000002e203c05401c52180d01e4024070065801c5401c0b06041c4002408a400f447d17524400c000071461a1106080c1344c000102a100000c00310f80b00b580c1882001e40b481c400c0019500d0440360704103508207008001e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 748573651 1250 748572401 748572413
    0xa03033903030b0109081615021902011227060605031b0409080d091a090d090e130510020306041820010201110c01022104050a030c0503040f08010903080601110316 72
    0x2ca400146d2288103641c0c0043c80f91081c80d604205035003400c031841700b24030aa41d00c100d950b5182100f0400c140d03001020103000650151b504189525090749002c074014406006205204c0c5081c00180040c022540000b01444114401c18002e8035040e005012107581c00010781c40e02c403d000c0f000030700485d0756059207400c4c02442819116000e11442062100c0502d604005c424540c60417480c10b003003100031006c11004d20b000035214500311802d0b101d562000d460541084c0404100810608554184404a000044003130004003c940072140c1c00503128203010050000b110080c00000b0360240301044c0704030110310301510050300144041c01405500810302c00403405400e00c58445198008080f65240c010703401900a1f0909003065080c00710001c01e0b0031180c00015030140d9018149070015080040800c1c444d900c0500e0390780c01641240d2600c2d50345c1031000c0c804000d0740d003e050140d548845440c20158042e034942d410090074601403000c2c1c902160b0361034403403184490030b4100700c1520041030700700a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 748574901 1250 748573651 748573667
    0x6040f080a1e110d0801080d14040b070305030a05010f230301110d061406122a0d020301030b0a060506030a0902030f15010501111501150302090a03033903030b01 71
    0x400155000c807859442c0348080c0c80b407100c0d95100b441a008a400c00040140304d42482d5049508000003400800d49500c02941c407046058090220820b0811010440704841d01c01020914860b07a01d83d55680b0b481403041b412180c042c3c004040c103019034401017100303884040c40349038850101c00014000400c01d100080c0101400c1251030355048000c21501c08221099000e081190b0504130400a01100e074002c11106114446051820441540102c1d0800c00d6840620310803409507000d00402c459440c22010700307908a102c00c1d0001d19000001402000150303000d554000b00a00402d00000703017401e00240050100900e08400507684802c12401c5d59030400c4585042c070b1218050711f91940c5c1910007107480c81001d0040c0750100e070354001058803440b80002c0d25028180400d001c1d0364182d080c205002c00045e000d400b0780c1c041603024400000d0700d03528800a500194440d407610419001c04068900411010500380810b52074980d1078891a80980003048008681c5403600142c400c0b070f042c006842c3c40f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 748576151 1250 748574901 748574927
    0x230a02101e0206091027140c04021c180c0b0307110307020d080a030f1104060f0906020d0c1a0907030c0902040e1305160b1c09020f1e220605010206040f080a 69
    0x11031000c0381600340f02c10407c000d0340701e0300d40806840d04840075234144405c0c2d11446001076441070011300342c100d1141a03540440850300071014000810101c40e1075100a41e02c2542107920303030200010522424942040e8000c3c07822903550051418400ca0340c000601c2c3c003185c2d0802030320752480003070324404841c4264400000c4010003a401c01c084480d1003006280f5402a0140c2004200c4800c202124580120303102002c6400316802422078503507000d0229580c403a0b10034200d49904050f020701d4108d16a102078188541c3e443c1c401024001d1035414208414105c0364820300780303113104100a01c1088040d10b075840c4e0048c3d0150000841d012140741103450030100b0504441d14004a2201084011a030401010a40e08010b0800f0407040c000441604842d6400c2000b0f51240401450103103908003070400e040199034001906065114800202c2d40030106541c040341640b5140110982401891048101400c4284014035441c54107589200514060715005841c145c00452115049845900000090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 748577401 1250 748576151 748576211
    0x140a1d0c0f0703020c040b04140403110a0c0801050712110d020f040b040f0603050c031312020c04050106021e0c0f0d050a02040903030225230a02101e02060910 70
    0x41e201070400944401210859600c511f00301a507100d85d91801c1e0086441c00b0688800c201c00507110791750161200c041c500c00010140c0a0842070700046081481060001d02d0400d00114480c58221001401c2440c090045982a4540720100c100348460406840c001b0038812401030380e0f04044003a41080f40502c1c0e1215000c0d46002401054030f12454402c10111200c81c1c0b4207000c01e40741c2c41e0701c64100d40021200c1d84151402016204089101104d038000400c005005481b0301200c0d000100c1c0c00e480c002d80011000d80d110340d00386d03a0065502040c90320a041c50002a040081c4091b001401910702460494172400c1001c03030031000d000c0c09014110b1085c0e0b008004001030701280c90094080d401000c0c01d01c10007480e14210254408201041115140d030004e01e01070311b0003000c590000c100c410721102d200144540201e083c01078032003151a61079404640c6801202c00d0300c1c0300e0450902601d03600000d0442d0001818410002000113041c0e51040040001141001e003d460303441200300d20b09551404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 748578651 1250 748577401 748577407
    0xc030304080c010801080a080d0914010f0c0215160c1a0106021f09172226150a020a1130040302010518010c02090405010204140a1d0c0f 60
    0xa03010004202c05510b000380c0b40c51181ea80c0c0c804a107602d0b0160128040c04080d410400921031a803180d00007113080f4032840351a110614098034890846094061101000d0b5440d04032001407501040501e0381071200707000085492401e95001086480d00030184414170465000c0802040590108800f0600c4800031058070396960300402035607007000074100c1581802009281520000b00e008900a240d0448041d0101f284004d541d40c840344d116106600d58030b01e001c200c80c941159082c51000051202c1c034902c141c50071302c80402c1288082590543c0600313501401030b0043c09000400265484031400c00010f032a00e114807401d0359007000038100e26005002d041480403014890f001800d05828070703c203a01400312440314825031148240e01029010a0050064148000380744154030b00500f41071500307203c078031425800f01d2600c60341602d086130a650045030500c005116245101510f850072103240c07280380d01d04001070040945480c20b55014038140302c00183d0304800b9408449107258680146a9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 748579901 1250 748578651 748578659
    0xb090d11130504110a060512091f0914060609040828080901061401020c150403122a0b040206070302010e031b01060b0a0f050c0a020402040b04050405070810060c03020c030304 77
    0x3401c0483c0d044a4a4080318002401d9003800c820302d2007a0703a01a01d0312803900c850000c50201c0c90030000c29010962085002134030f164444a40f14030360400d01076801088000e000c1c038100c6240c052507280d4201c194800010081690b6940c680c90b0303001900304071280e68821550364840e103c80c031080405c01020b4122005052202c1d440600c0701c1c80f83e40c010340208441a02c49103001648400707410581c1c01a4044101c1400d20300d404d454090100c1c004449207882c1540c4c90351040585110103883d140400e10760b00000034a803a200030380e50340c421030460092620340c810365200c1486600142c4041c0c0911404a10b000c2014001d61100e011101c1e484110303a1109906018044800b2030b200341c1c02541d5080100000b81b000e018020b449003d02c490b100d2028140302800110303442e0f04078443d1071030b45118440c2248090f17219840184080c0030020445030740d9034100002d0000303441c0c015008004100d1110b040102444101c020740341038800e146004000030686040491600030084a203d60600000400007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 748581151 1250 748579901 748579939
    0x70f050c1b01110105101707081603030f020708100203040f05250914060103051b03010f140913080306180f060a050108190c0309050a0501050103030212040b090d11 72
    0x71032206090b0307240142c0205018401d400c0c0d0b542a03459401d1036825030380c01c0c0b103101001c1142c400303d040342e130040302c50b10765807100700605c1e004942141001001d459501401415403110308440b81c40c1e464001002d03a035107040c4405564548142c0c038101440d81c0880400c04005280e101520341c590018100d81c2072030402d02060102180d050b03031403076492035100ca00040c03000c940c1c00303440440514110217031305070340e00e010040d805071000815501c0c04244064407800d807143d55101940c01b8120100c2c0c00d04141d404c0200d52406803401246e841e01c02c950a1003000034600c0710804215600740d024015507180c1d22000e001c03484150180c1c280c42c482e6000e070401c04c464818440c88031071064900700d07455a0f000d640d900040d00d80c0c0d40199400000c0b80c0000e10350291040b842c2c3c12021440c00c0303900d00081c01ca000c549031582003400e020000c46441e5101c2004105043c0d040041450f88140d41c1c0321113140624150910940c0c2c881c07420b105000301705841c005030a109820005044200c0c0140042c500c60030030400070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 748582401 1250 748581151 748581193
    0x1030218100305180f250e070804020907030605330d020306040b04090314071e0b04050105091f0504080717120c03060d03030e0c1020010e06070f050c 66
    0x35409000180b030301030201c0d0000a05280d00e14003405c040e10a804200d055026625030034800d030300c09005441c200148203072203200482e100d808240d803480c0d0b250900c1d104120440c0c1000e00080b003003608010051100e9a5403030b508003150442c031142d400c2c3c0304000038000c40141052907440e2480c41c502282c01c001da42d0b400e4000314414901103c2c02c204805d4035000300000c94011800c06000100d0880030242411043c1000b00405c0d40107017140801035020300e008c01040e01021030102c421030318510034081002000d0040d180c002c50864043d1154042090003000260b41000550199944410205050024087c2207401c207039040789502400d0300c0c100c250f07140503902c22b1a151030301004800c000341c10b400c1c0902c10f03030b4000c1600404400070204140c070210003502c440000c10344140a00200c00c00d29540da070003040610a0140c46140c04000011326944002c900080d0003251641400e40400c0c0d00b141c0450000d1b4030a4071403d120b540310480d0725040700d4502810b041007000e0311903084009100e40a1001c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 748583651 1250 748582401 748582411
    0xe01020106091104120f0807150f050c0f13090603030c0b0a02130e04050309040f05090c010908060a051b04090212011d040839160b0901030218100305 66
    0x28030600d5a2682e0040454030815151a440e540900c030070700502140c0e8410300f480e00c1c050a210031404d14070383c46e01400765010540448030708202e64290001d000d0030f405036101c906001ca00402040c9040c5107143d109200348000707801d400c980014040c55044040d01104064028044100507064880c50017505134820704000b610507075122800601242c0f202e00882d410003d0a00c2904c1540d46808400d81441c1400b601c11916400107010500407922684155580d1800a103c081801e01f0401c09070750800c1440103425040220052041c0402440007034a02d800a203c400009a2540c41681510341e025400c800488603c4001400003941e04031380c0c001e840c03010858100d4180f141d9131980044518242e40c01d20311340502c0840002800b194455018141d1400c0703c0e0301890400c65141840c8002811506418840c00030014801c24584020090500801c0354079204062407814559020564000d130242e2078101a0001810390080f10602540303a2a180080c0002000c50740d1801e001d4007614085031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 748584901 1250 748583651 748583653
    0x306171501080318221802040506040902031902010c0c08010f0609020301210624031a07021c0e100e090a200d0b0307080d080606090108010b0a1e0e0102 67
    0x204540b04003000320303407244019044041800324040140250380d8400361007180d0480e81c1200342084c2085a00403c80d000c0c036040959805940103104100c100c1c0d0000c4d0245000d503282000400c01a01d000800091900c080030444007005602e1004039410407545800418550500c540000e00b190305410403228009240014029141c0741c022400807404248100d861841203110a4405070b52500c05491340756000355008155010250080b2103084011301c0ca1398516104880f0400a01c001c0ea100780d80c1ea40303050b0716007100034209140001c0d513800070780345008816105c0100001d500c600891000080b264060702d80b113100d00c034040e809000c0e406101c084030300428081c0e001a41d05412403040100703049103d610b0b02050341c98103801c0d0320250024851540c103540c2c1c5207210301455030108902c0380100280801486c8000e0329031801080480060406409410b003070081411503a000b06980341034417500c492045c4ca8558030030044621424100d013140c0e2903400b62080000745039200d0041c00c410102a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 748586151 1250 748584901 748584943
    0x60906070c020607020108040c091d0f0102040b190c06110307080f04021f05090d060e150c0307141324140a1b051603030905060903100c030617 63
    0x5182a0740002000e00002d6104004004a9005601521000347c20034060342441c00010380712070800c000c503200600d041480c2010380c3c8025070388640800a01900310070344ca0007582418900600c0c1d240340d014101d0f00703e2040500e80b928040f024403030a0700398009a0801ca0034444080c5255280c280c03544140e42000001c2c00b1030000400804031090514082c40d0b02600040c0c100b2220103407040e5400440710603130100003080012012941d2000b081c2054180185800a0241444824649080024420010b9031500c050400603031906030015268080500c0c20001281d07981ca041c2654944110b80784181200f88803a00401c3c0c12803400e07941c0304104e49070fa02c144409180340805461081d040036041a081000300001c0100740d226aa2035810001c1000d980800c0100c0e075501c550070b2082c26210b220340d081114500b0810b02d80d100403064018841500c44c0d80c03411142c000802c0d02d0b518a2440c04456035114580702d50ba8a00c00d6011000030f00d18036003030a88035007141192a840d80811030080d1a0301c0f00f00307 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 748587401 1250 748586151 748586161
    0xc0e090601050c060c090301150b0307020f0d1b030c02061c0b030109050a11062814120411060412051e0f06191b030504021e060d0f0b060c060906 64
    0x2c0c070807201c100c20018014403a0b9501c5114240e4550300c071060710b58140d52200d22901c4c00c0c4070b92a80c610043c01d00504c025407a4644100c000337180c0805c174025441d150380408210654a6040318942150f81a903d450240384151401c099684000101c8001d400c1400040d0151040321008051044174101d00010b22a52445400f010309880b070841000d032441c0c00061040c40001c5000c8484881c41e10081c05803405d045045201d2200c3c101d41a40118181010491442080b0340c0308038080140c060308150181040740c80c0b00991101c043c0104001c0c803108800c2c00d915242d903508401c0c0c4004200c03081c6000006070a41c41e10310b44841e00c036000c00f41141c60152051089420201d401000449208020300c03003036035052402081d00f4004c421089071107540d41d0090300d240c4980c10138100640c2d00742d00c0c0130409083c42d02c1406410304403078000c40b01030102a2000252a510303001204c04805407082d003c205800314a2824000307005803491141d00002c0060000b40c40240490014400c0941805407040c1e0b55070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 748588651 1250 748587401 748587407
    0x14010602010605130e0c041e060f0605040e06130e0102041a03011401270f060f0f120b06160c2103020703030302070503070b01064805100c0e090601 65
    0xb00c1e002d5154080030714444619042d0343e0b9801080b019030400704555400a40802103401ca40403640c00c0c45002c01c0d820400c1802901c0307070040b20b005100b4400e080d1609890401d00410b28041ca028101c5901c45001c00b24651b503030b408502490b48001494108460b915441d1032038002e5000e4450180109240c00032070310700e6529030013503e04071031a007a09081c058201400450744801030956240207405114420300c035801038001c60074033078403503c440c4a00c0c2d242071050152445181100340400c01030b00113040f0101d1540410350602d0b641070f1070004175460032900c0c00120305000c2c081c101c42d084180c41d40d0140a001c1c01074210130440d01c0f0b41d0b0b080d809901c50407285a07140300c0c1700000030380980c2c0107050400000c3d1080d401443c100d405002640d0400049a480a00c242c1082e44100002110b2008440406140402060890042c1400c1d524951028002070300c4251a102c1d1212052004444e4042840002d1000b09590700e14284100714141550001070f03c12030101204601030520040015540c0d40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 748589901 1250 748588651 748588661
    0x14031308070b04060c020307030605090604021f0c03030506011b050601170703081206040f0504050d02060c07050703020d08070b010b03040309090902062d0406020c03190f1b05090108011401060201 86
    0x294601c4058074284c1800703000e88400b040c08004a80610900000001003501449070f68011150b0201518540c203180c01000342c010045000d4003141500828000c0750f540d0016800041503a060801260760b90355440180d0300101412211940340c0303103030103481080240209070760741a00d5861004075581c035a08403a031a6030300c556020041404604000b8060811201c00c1605d03440400104080307140310b0741d8807a0009030b94094404031041c1c0e12035440c12203140e4040c0103a6501c00340350b2075031a060404540b640c03076960300c10380b00c0030b802505000e4504081c0a151001c03603c07181d4000301075041d156540d501d04001c5034001c0303d0550014074003100c0403400050a000e5101840d0300100001e0500754007882c5242c4459201c60124814041103500c20303084011380e405400102900c0e009456040c14107c28103040041880b010b00c000001c000080c0c0000307846041201d181c13a04010700110549040800c3d08011400b6084107620504800000900a0f4150400312105200700301c1c400c03603a42d07100c030b0030fa0a85e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 748591151 1250 748589901 748589909
    0x110a0803040b041404020f0d0e060c0322111801060e03030a08181618050a02030903160312050423120d020d020909010902070203060c07080d050601020a1403130807 72
    0x21082108200c01c0c480c0301002c4029800c000e00c0140303891f038034106026030303688400c0001442584504240300040000e121b0319600107800c4070924a94174003c40340041031070355a88410310481001e1198424001012100c498080000e44028031210502c0c1c0c04245903682440b0b840c001511800340e082d8681404025262450b0007901d485101391144624070a942c00c640140c0c84c0944a0750911284142582100780c0040488504001c944002004071009031070004203550040c1d4010010702c10302d440004101c039142c803003d07290700609035850328088910b80501d5800040440c288010301041c07001c0310703d0301320403503032150401120001083d1100ba00d69081d141c06202540051100880340b140c4c40d0000d014281c06450700500d4198403a00041035130f0400e070042c0b001c0540c0032a0002c11420f003003041503041800d04a8040c2400c4181d82c1c0d03481e0511401404524040d01d41c0c2c08103105034020400b55130402d50040c1c01a801e44084102c090385da8101c64180d6185001c40c1d400054050404100e220650f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 748592401 1250 748591151 748591169
    0xc123a031416020309031b100306032a0906091e0504030c022115090114010311010e06190e0424091d030c0a0512032203030e0a110a080304 61
    0x2940e6102c0159840001442e55070096010410607040c49680602000c501c0c04174410f0742540c4503c50b1400d01120f815070203c040305051800c0c0d018008518841c02e101c0301121181440498009820960040901c4070b03401034a80c1c60070b01c0800b0034404000c0d0011500803400020004120035004041300c280c0740c0545003c2d0118042d0444000541050941e039a078102d811420b180390454800e140f10315040e42d01c65208014401c40082c441518001c4c0203980c11000c109015200f81d5040d6150a4040010751b000d490612441c43c000c0e10351a15440113540d144410121540c03410403000034040c2031000c0a480b2188501d00d80341d83c0e456203401d080f13007044082d402340a15050700303070030318950900520300512194a01048448043c248501c2000148401d10301d040180103001c059151035850b081120909459810301802040350380c1200c030003c040c0403110181c00c1200c1030100c0c1001e40040c4901081040c0c5409100c01b080244550140020944001a1b441040e02551444000c0d100d0040e0701401c010b07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 748593651 1250 748592401 748592441
    0x1606021b04061824081c080f010603090606151d061602010c02040209040c050a03050108072403060b040611070e0121060b0925020f0c123a03 62
    0x14001c0c036131185242c0a900011541003e81c0303032008800307071601580310f0f00040e80003400c0f541107504c88054103c101d80c8a0f091003410750501c401c0140411505010302000c05954582c000203200c01a04840000c000300300c10001070004440005010140324025407100c0358507441501c816007041780444020304019040410143e10507801144c240d01c0084040c0d038442c0c0c09200500030350b07945104194910005d9110103035a142d5011010b010f6410590080060f5040f003c01008a40c054048403050b81154030a850002128004107800a2503542c21450050001003400315443d070708000c040882480c100c0466203120b43e00c0040845411090080305c1c1030441b030960704500c0030b25044e03030690b05911960010400c3c5500ea000714405c01c0c0c00b00e541c8040e03407521403c902c2d50f0b0882000303030101c0740b00f05101500f130183c01c401c0d00039580c2c4000d241ca540aa41c80b00050100c64809005840c801c2a4112030041449950504c2c480c038058401c5491491044000c0160100f030300a00c60300740300b07040c103440c2c80350307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 748594901 1250 748593651 748593689
    0x2150105010c0609080310030b0c071e050322080114010f170f0a08031009050f0613021608120c03150409140f010509011508060f091606021b0406 64
    0x3884118070034045501d0f0780c40348032040c00038000001451041d80d40003801003416146061402309500050104410010308002510100c0c142e6950041c2c500b000103c24150b42081d441c00c1451803060200c2c40001c001617011411851076050a40f01c00c9501520080c0240840504003d103000f100784540048040841002c1080805082204404042200c20740791004410f81c001030405602e500100d0b040d0354000200404120304404540c054040000c003040140f0b4154992901d12a029154030f110b041000b0520900308203a4045170344850204040d03e00c1e00740340780750504d5260006088180c03000c070a40c00003140e0f141c004091740e00c90042081c0540048442a05100c01070601000c155500100e40c840d00500e14410001781a950b04044000203d925080c14420b0031038100320f445a400b01c15000c010080c5007000075100343c01c40d02c009210340145e1076040c000c07407070004104001401c1440e180c600294294010231042c40700a05955082c2c001d8a070201000122081402148190301c030b8a40361032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 748596151 1250 748594901 748594907
    0x512030c1c02030910081e061c02030c031615080601050a1d1c0c060302042709120207090501090513030c05011104151d010206130804230906010215010501 68
    0x74590600750042d60314080050300450180d404030880310700452042014411100b0366040e20198641c0080441c0341c490412400040040724595441c001c086e0320040f40c04295a818002c0c0414000001e044805015030710b611641d000d0854030429100351081e4510303021b2640105800d511440c416950f0602e4581c5692090b140c1d41045019650003a01d008140c240a40b5030314140c0351011015002d40380151000c0c03403e500b4448454001d8400c00d4014003081140303041c0b800f50050307084000d4020108e00c0da110580c01c5c004110004005c0e2902d0702d00b41241c552141c0104014058845079401400540e03203c1c84200141e502c1a9414000001c0d2095102e0120744100d62451515204000220301c080a603009440c1c1c503001a0401e031382840d00046142509a01302c412a96803440703014030808a550000000713501d0f0350000305107500790582500050100003a54080350054a4030301d0b02c3c0c0100200019010700c8101010700081c0c002c2d282803000c030711658000101e0304882450b482041000d07a00b000011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 748597401 1250 748596151 748596193
    0xb010c0b0a14010609030501150305031806130b03041a01030510020d0e160815040c050402030c070803101502210a1206230a0803040506031302040e070512030c 70
    0x41005642e0740b14008240c4502541541c001d00d29a1307a000c80742d030b04604001e800c4443c440703c1c00c6055004010f04000240c00402a00c000c0d540c01c55107803900e01050004a134841c401c0190f811030840440d000480d00e15001070242d0700a50190004031040251144021511130342800050617036030100190311010a0b80390001c10140d141ba40d4089a40c11100340311a113441e07407518400c48280b401c000240000c0c002088201303085080c4546074080b0381004e442da9600f4507107500425004d6500040021800100801100e6003da8801001c03641c03803800007003c00742301203280100c56080c0d0500310001b420710f00c001200107049401154048014111070001c0020381c2c801c0d0140c0e000e0110000030343c401b01d07103107200d928018000c015140d41d030400e0700114076444034a14500d85208441c1c038007080c00740030000426101a601c040d100307141c3d01e88648865000084000c075000f0b500a003403115801100c01d004c200c50046990648014002681400c0166240d006a0010076102e610215030503054800c00340325 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 748598651 1250 748597401 748597411
    0xf0b0a0c1b0e190e1911040e0303130c0608090309010c0303110a050c0d0f140702150403050d03200901140c010c0203031006020111070303090309091a03100b010c0b 72
    0x4070340d00c4560b503448222501107088030001e007144401820b25a55071100d00500031a04591405441c40d1904444241d8051302c400380080c103150361420700c0080c2038840741d110303440c404d1070030044907100d00d011100007103140741602d03086908081c903400000d0154011604075009040e041c0141d414070900000444102c2c00f0b15901341c041580b11901d00c103501d0083c0d402003a54107500e41c0d0301c0b540c41440c205518500745520084104004002203003c00c8039034403811540f07407076a5030016956545040e0000900d980e800c40c1c654900fa100009001040040008001c9540f00250310280000d80c0343d1410900105082240b250b43d00c2e400308038184c100c0d032017040c89000380028000c83c1d038101040800c419084400c04400000540c0c0004240500c0c0b46215000d040188051f10090100e00c0c040c00320304240340503243c030090071b0586808540c1c04050041c01941d02074900303004c0820070349421404001030441c01044083c00b9010b2411410460119409001035080c07044c0c44442c4c0500c400d545030f40305114010300c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 748599901 1250 748598651 748598693
    0x1030204092d0c17030306090c0d020f0910020706050d020d0e01020d060609120807120521011a13031212020a180e1005060c1005100f0b0a0c 62
    0x405250002c1814060b11410003003548441140642841c0c0030034001c0498000c0303240b442c1d00502e48580007400004995001c0e0003515215a10f85070720074480024010b00403503030300841c0007013015021200d444000d85103145080b11858103c060011050b82c0324134150103070000007001004140044920f54008180340e4194540c0001e03003403010f110060890300050000350788281c50300020402c03164481c0003030010708040d48010f005140103030745107001440341810040c07007003880e8441a150f49001d442940c2080c06041c0709001e0500c03c00c06075142c00c4909004080c1c0181080e0300d8030307100b17102110546058400300100e6080c1c05003951101a242052113254404000e22602400303a6089030f400549202d100d2520341000703005030320303480a6640090b070700141c4212140d90704102c0b020310b0400041049400c15594140e49003400e441e2542041c940c801e154402c02c1c2810305004056481c907008204650303444c403210300060344450010105100c2d09040c2000100301c004010f0105081010072080e01c00030745 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 748601151 1250 748599901 748599923
    0x1c0c020c0a09020d0506120c09040606030b0a050703050106030603054207020d080712050630011b08190b0a0305060a050919080c100501230103140103020409 69
    0x18000800c9040315401c04030382c9940102c0c1c1c0010400040c0112600003604407803280030300070301500e032560303a19803c41070750b200b20b80c1680030400703101e196032203d005107802c20341c0f64040d0702d01412000081c0ca815a80380340001e28090000403400c3c07281c4140c5082e2903100000e0039611103a2000d90304d01c1e0600d60320088150341030100d05d1074401c2400c1c0005484c0600031100782e00914000401030304003043c0b0145142806030410070085000e52020380360500e0005140002015107814001c10030038180456651680302c039014a0521080c0c4046842a01c00b07520002884030904580154a22403c0c000020b4041901ca101050b240d070503401100c001521a820000f66a211500c0090300e800c0303035030340155080c1e0001014001100d0160040944c8502c20100034039451400f0003510502ca000301c031300030b00250f8010031005403401051003400c1d401c0c0e00b01803040c40300756160300c40e01600100c03225038152200c0300c614180c80305500a02a203e59012144ea019005030320b1074003404080d00840340102c0b800b180103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 748602401 1250 748601151 748601173
    0x3151207030303150503030a090608010504141303170a0b0301060b0c120a0309080d0c0e040b0a090921020c2d09040206070606030503090a0801110405060f1902031c021c0c02 76
    0x308040c08c041705c0300d5503c4c800800c0c941a80500707106810b13000280140d04000e000441c0300f11030421320740c2081e07400c4042da5800d02103060488241c01c6e05040381d42c01c92006010700c1154001038000c406240d5040b8020001c0680c2d420750703010b840c03003004030b000c0081e00440ca14036030682c994400341c00038203c10f05001c20b104070140d0341e10319203901010b0041040c0f47d441e0112a070269100c0d403c0c0480d4035040e034081101c0804d00000502005031403007010f10f107685946546007004500036104280c2d0b15441801880c454400d02c004e0b44903140e40c1d05a500500c0d91606a004131002c00f03e645501c0020b02010102040d112000d021003424000e0041ea088441002140300003045e034031030a0000c600400140d42c48651079420401901300da0342c0315901582c1008000303801445011b040303400b2241c048a60b00d03030754030341d86d507003e001030084020701240b2051100744002110b0300480100402c443c1020b14035240e00c040500702c0c0032801040088040700c6421002d2000b1208280d024a245a10381d0044031804800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 748603651 1250 748602401 748602403
    0x18100b040902070606052e0e090a0903030c0c0b0106030510030b0f09010c020304080c06130b0c010204090506010912020d03030e0102131a0403050303150d020d0803151207030303150503 81
    0x1640141c0340a40d0001c0c0a6060191621030080508411200d048600351035032001d0100960802c6044c0b0400c40b0803000c1030403c1d0180d00130316050b41d80502806030510341020000d00030001140c0680c0402e042080b19441c051045052114a80e0712068120315a405c020040700103005c02806185512010000440418401e288007446001c5482038401d130fa2801494580c20345900004030025584103020a2102c7c0c0000301c0d905160030000d9507556100d0240c8003440b1403616556000c081000300004a203501c065040d0010300581d0050541403000d034607010011544d91489215842120700c8540f142030051070200c8220164a0203031802060048415241c2c070b08990102d01005521400315504020b941c000700d01440343c003590440464181440c1d0b484003a141d100007428251000078021320b264240d80d40305400e5103501d40150808028401d07515114505502c207462100f00040d40c085550350a01c0d15002e54120f091060005d8890f0340c0c50340d03a0a070b01a141d02c1c102c10030101c1401c1e10118817510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 748604901 1250 748603651 748603657
    0x1707150e1f0509150c040e090304050a060504030b13021e150d09110d1101080702030c3403020f130e15160503010b0f09040b0919060b0918100b 63
    0x141c1d500064141402e041180c900120742d0316a0a00b10403040802035803070616002e40d400c8803104451003905039102a140e81c290301c12600115400a14500c002ca81f00d540b00000d4010340b0f01c20011f180d003503250300701e819200700003122000b544840c111010035110522030345003d481d802c001d0801540c5083d071810200c8260001342c0030500c415030760b00ba05070911524103912207503050306941d07101c0c41d02140d45071203255003000381c922414403c0220101f1000ca02c20801c0300c51800202094480480149080745204e1048108681518061100794088104802480e20459a009062000c070042550500607101c980c00205a40b0640d2064580605c48080c404600f02ca1f2411050440300c3c1f40400409844511600d042020094103100500650000c401159100c210001c0e17000e03250640c640010300a413490f209500e810030201c4080c0624042c0b4000903440d803d000701d00920006031206d55a0226005207400c4541c0809030f60b4445211342c0026880325004940403154400a40e04c1e011b4182c05c0364 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 748606151 1250 748604901 748604953
    0x12070203100f0914060a0c0806030a02040926040e060f010215060a05180603190b0730061a090d2d03020d020106050a15030c03180c031707150e 63
    0x1d002042001252a034074455487e010f5500e042c068903904108003c03a03910b48001e40c0007070289659070381c01400e101c0822488100703d440001040c000155142d080c41c1035420074410494420300e880042421407030aa4078981c41d020041e4003c02030ba00d00b040410f041000f015107000e411210240c8080382c01e8a5281d080106407118416401c4a814250b0030b05107099110200090840103404042002038218410a0740002c1107290040c40d20380122501c0700342c1c0780c0c42c80045040c41040302d900f034158103158214504032010140c0c101e41c4010840d41e6413a451261011480d4414021001d0320001490703a85c4000c1c071841d8518002ca01e03045035041030310201010303140503800b6a000c40d102940040d03090050501503c0280c80028040d4079128424015142c40640081030540322604001c5207482030b8030070320003294400c41c04440d44170141000d440c105024002900d08a0300300c0a2601840380300381c00c0f0b8411913405070fa2041048051003100c030040ca1402032714100d80c000c40c6295401032641c150708140207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 748607401 1250 748606151 748606153
    0xf030609090b0603060106180311010311030f060f150f0708040902040e1008150a0914060c090a08060105011416050a060f050603010b03060a020703090b0309030c12070203100f0914 79
    0x181002e204051a05170164001010080110350441c0100602c0c00010700b101c0d03120069103140352051300141c01510a01000e00c04060740441001500800229020700803141036860112964551040c4040264080e110780707150348081051510b005c401100508200707001c2c0f180e150078992603901c0101a84d0007035214881128024050000c04041201c0c10300041c82c101c40140396080146902032075845000b03011000d1325559051510500084819800d2240d00e5031050354654a011210b4180c01c1c2c011880381d900400802da8049151500020924141c0b80c0c161181c0d00c15070014088a14154031060b55144c00404020b6881300041080141258542c4507000100d41c45094980388800c0301d00003815030344241c1c10510300060070f0714041400c41d0060340d1507c001da03440b20395003170540b07000d1103941c00a007040e000081080b00a50012001d41075010128064172171041c61a07070807038028041c0240182d41a0041512407140c4001d030303480092030071802c2001244513052602c0d050414030501e0100116 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 748608651 1250 748607401 748607423
    0x50d0f0b0a0e1b01081302190f06120e070e06030a12080a0f09020d0206090a1d04060e0706020d050a0311030a060312090f052b0f06060617070f03060909 67
    0x540704040c0103100c07041210703c0c2400003250201c0c000034211840506204201000040745100395104d88200c011321605609140b15100d5480b00210b21040c030501c906000616110100001a001400b4651a00c50080001c002c0b0b2418104408580c3c8400382880b0381c180300e0100b040000070308140c0c540301c000c822070b00d031440945030240049003640d440d03801c0d00c6500d510308ad1403000140c0d90030340081c404071340665410341c445091001042900d140754001d01c40c0104024040b645d100d0b501000a44524421b59081c001c40e03008550055031168580102da001d60040c4002114062285024040312020b91402107121911000c412240354002c0c1c900c0300040351104807c2c018041550800a2101902d182c101d040520300804120407140e940503032481180e04001e034000305407091001c940f40003658842000e00d08074628100c500d075a5560ba00711001404c201001490a000c1c00c444201403c44201081c420b43d00c107041180c80161488402c0103140c1d403514081f40486103413090703003806840707039220b0b4007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 748609901 1250 748608651 748608671
    0x901020c1215161e020106080a06020d060e01260a142b140f0c03031017010911010e0d08040f0311040203090a0b090c0d060b010e19050d0f0b0a 63
    0x520b00020f0002c8607590061828000c400c1e4400042c1000741c81420962280d0412141c01700e0150215601c889520322515010f04107128090340201007109043c102040000d54a659080c086902442a0081c07084c05503140d6888400110040d0b07040c0c4040c40079201220015039030a5071203592000303c584540d001d0400d49031150007a0403119840126007454080600c0b00c034500500840350303982181e4440d8004034050401020110940e81c54a85000c15a52246400d03140e50a03250ba03203100d00e00d42b810740c0c50006c0c608000c041c811288240c6e04090b0b0300982107444001961607606040342550020240c620f1100490a0240074001808815003418041c80c40d50410340d4504a8850510744510b104000b80001e0340000a0710f007410340c5d030000c80480b00755501c081071800c2202d158105600043c01107460020003425901c1450201003d0322a00b601e81c1d110002d004007240440c1a402400041e05801d200354508004550402c0e4451011518031380003a58540c0080001903801d40c0205803505070241d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 748611151 1250 748609901 748609933
    0xc05040305010c09080712140d030e120c0c1c0203060f060103060f121b0f03030207050a1401320c06070206090a08070308060f030307050c0a21080901020c12 69
    0x83c100308450324040700d025062120050710780216128041c43c1c0740c4616030071010030104406c58603001c45064240d0303003030b1450840d01801801c0f03010701d4549e03980a0b198400da0003000354415074880f0321844009041d1041c0f58030a0045468178101c2c80300904200c1848240160b90070802c01c1d10a080840c1c03c41c4076402c22030005000c0d20460340040c0e46109040200307001c22807010b0030000010b03800142c1c83c0d0103465854240e660030845c03070701310400b0745010702004001d01d40c000440c20304803407064840600312595940619030440300d10203c40c6c00034021038010000c00401d6503100060190030040c074000000384d00c144107415031080404180c03075040107040184158052200383e50210031440600545125075482e0031180c841c004004003400720080120b10992a005145e02c0140c4000c2c040302d0759100e40742080c40d61554502d0880d4401d01d403914010034103803058000445002c1044440700c007a80c0d115901d683c0b0300d0f023100190a04600c1801c0520150b607641402095a07150000c0280911405904200e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 748612401 1250 748611151 748611161
    0x80d0210050402040b0904061d03360909071e050f13110406031d060c34300203040501030f111204050d050a08012711121311090c0403060c0504030501 66
    0x210480e0b001032023081d42d142c0e6881d0200000d000004000c084403641086002f100450304034403260840184e00c10013011407800108213050b5074090400340c401418000e9003801c10041402015008102c07041d0710f040d117003041c1d6180c90000d1800c000120310441c1d255010985078000f6408000044d44505614003030024541001403203091490103404030340f030041000452446402d40401c908d0004a45e10003950210414014030f0250700391022000c2c1540d800d08112071218958184000070300e403015094001d640c0100320b0800c2a003034000d1801c00e0b01e420010340c01440b5034141c40ea00c0d292111100261041007500600c024503040c42e242c281802d007802e20038a02510484040f041c041c08000540a0030b40080c601811102b60a03508811900248005a031001240740803074605800c0411107940300e081600548182018002c0f0b0b084150b0342c0c0c443d09643c66040c1c0e0344c00780c141d03084800341044904055502651040343d00c511546000d541741d5a07042103c0491075624002a004501441001000c1c025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 748613651 1250 748612401 748612451
    0xc0711061c18022e12020717070318031e050c060a1e021603021221091e10050a090815070f0e1302160602160c080d0210050402040b090406 61
    0x24211300c954820f83e40f0740c8460500ca40312418094030b8030340b111001c41190111106681e2050950b20f4071421000c042105403c270420882c00305480c150014108640c090095084a07008218011314000c5a1320040100f001c14205840601480603140c0715078841ea4010110600660758172107120130b41c1a02d00c0c4041080c2d000c10001c40d002504440c0640075940404819650110f55118040000d40c484a00d000d0040c56244141ca0011185190b80600c100181200400903200000819500d965050505002d0710350301307901c55850b13007080d160b4900c20342c00350a1840440c1040ba0200f512500c0e9189880899203510b48448a240c00300103d05500c1402c00032003600c1d600300f01240400101c0012000008601d622080a50100d00756181d00d480454461120740c000104550b82c90060b181c04000c1800311a094035180c00f04800001c0101e400605902400040d40c090483c141c5440c140c080a860064410f0341c0c0a82c85064102d2a641c680030007501507803182c13500180c00c0078508180c0d0584864003203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 748614901 1250 748613651 748613689
    0x9120f06010614040302030d09050f0607150b0d05030c0d0318200406180e0601120c0306050c0409020a1107141003180506010e040b0c0711061c1802 65
    0x5148018000014501d040d42c1040c1003035a03920412070301e91080e902850344045e41c180310300c003000d103119600080c90a0603500d042d140214134282074010702a141c410b240c030081851a0481039191540316030f80c003208244e4001040407202450b04c1d01d40c546903400000c810f0341103810011460f5565030b010f01c1040b02000c101d0380c0d04003124100e900d030b036241f0706a100d07030100840b484155070001558440e80140064400316030100200c09903c030050000f81004950244280325480011441e606848404008103602c107401d04840c90070740c1c3c0c40c40094140a000c00351345c06000d01c80821250102d0020303215080c04e0356510365404081d0002289800c103268010495000c40310007040c031540356003c0e081c1110b11903044c0030941c44004100882c8c00c072080d09024107a8015000007040c044800811503000d075014a000883c1c0317842d40300c072a032032034071881200a006e030400002c81c107410304207007025200484a14000e260007542c074603900030a40c2c2c9041c92400c680b49001ca0074204502c1d018504604102d0b05007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 748616151 1250 748614901 748614913
    0xf0813022e081e090c120106030b1e01050d082104031b080a0e120f060412081003020d0203100c08190e06010608190608060414240702030c0708030912 66
    0x220075980e800c40000c000d5003680f02440000c0c030109010072030300342140b40140c15140e180808441c00ca0003412240000c40300188050041001d16180030000c4002da0146030030411139034030f043c0030001c120030000c1045030102c0303080c0b0546411000c0c243e440341c04404080c08106141c50301345001843e04c603022008410054241401d1408070fa1003a00751503201901d81022007400d0b02c040c001a60b0205e501d0b003800341e64860800c0c800e50402e80801c4035030043d807080c89098040070401c08151410401102c6201344040b01c1c810403c090700e001a03400020500190035240d0450080c40d0200a1700c2240c0300204c041900b15040c84441c0040008c1c000c8075154041d000c1105113103a03200103840e0303001841540c08121060011442c1000110003146071141e0040080040c5660b841d035242e1121803c440c10f481c048490310256000603008039000c2400d03100183e101d4007014841904014140024000f402184800e006000b5029410070550000e8803003071000359201c0007440100702c4100c50b88206820142c20403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 748617401 1250 748616151 748616161
    0xb010902120604020c0a0b01150f051c1e050f010e0106030207020d02100e0d12080c041202041d010c02250501021906091505090c030303070f0813022e08 67
    0x203800070a030041001c03100940d45040654256103424980000a002102400300011344a5122aa041b0865450b611000c00d41514140c042e11036000ba004040e07540c01d01c0021620210381140d00c5002803844504040d14a80701c903d0503441110b07011501c120399459a0030061044204bc50b0400303005001e1031505610307003d62a80411206c1c164640020b000b01c0610081044460040ea421440418003a2407285048494280002d4152a4003120800b242ca00340205940b0f01120044070140c400886200e107408070315500344401444014494412074400f2003440301010001c3c000d909066031258000c20b6a5020190602c8502c040551101c001903c1e8603810085640c011079580c0d4610b0051000035042a85824081d0181240100080441c000002e28a105068951142e07010306d40766003c880401c1d110401707241e6030748029288000030901206103150307a103100300344041d82309030801004250b05400c5e41c08101d0030100c40d010f01d40c47e00c3d03032107000c0391074449075490154180c01d0f1441c00200d00d0800b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 748618651 1250 748617401 748617427
    0x5071814010b071127090f0105090601061106060a14030c060a0c020a09140601050a0e1306180c0e0609030c090408090112060605040b2203080918060906040903021510030b010902 78
    0x3200d81084a40004603001819000051251f80301d641e0800009102e42d2500d0f43d0015204d107024019034010903840c00c2c1c180302e115400210784d4441c10002d840c0c0702c042d40c01c114813200d0039544c0d017443d1503252140c0c041d0040c403612440042c143d0303000c943e1a1010700710420310400a40200541001b1030040c40c1014502025030b80907141034003c2e030203082a503078490f00908201e4100300c025414a800000420f06c081e01620715074461000c03150310144020700020041581810b56110319500310004400742c3e4040f2080c90f1040c01480c5215006044903100c080300b102189202c08110380c00e6a80c00301c046905665542c101003e401410a40c090801000d410240040d020340124069940c48200114158105a101d44041d0705d54954240c60081c0781640ea107452400c561020306201c6c011100024649244086152098010103005044409580e14001480010082c92030203500b10301c0f0b610028440702c401041c0850140746040020102039065050080c807014042e48201c200d03e01c1040b00c2409034070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 748619901 1250 748618651 748618699
    0x120f1b06070b09030d14041101180915080109060506010323070327050a032c0f030102130602070816060813080408070b0318070305071814010b0711 65
    0x1902251000c101d07140c1400e410720f1401205108400c0c00d00d0301c0141d20706c240a180046100324443c0c4540100740c030200004403068490340d0703403e0007468000e1038244002c010a400140480034180034a280150f91800e01c1c03800e40d0341e40202618680d99032000d0000380e5a150085020001c100203c190641080010350750700008000d0148041503980c07180c0465404001400e12826441e402c1c00110003245814415210802c004048012034662544c1c0c601201814501c181c089461011004a40705285c06100e078419200818982c95542000101d403a6100000d00e1300c09088580d005044150030145a42e00e085500d640741446810110b508000060f07000e072510364003c04610507006070241070305c0c0400260040c2d800240160080c60000f141000465000e98030880b50041d0007810030390b03003640d495110000c0c0d001c0a4031581043d10180140640d100180000c0301c04010700080305492032402c688604001e81124001f07400001d001d4003449035480d4180810301085540940100c0c10702c525081c030300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 748621151 1250 748619901 748619903
    0x10801061407141c11100f3305010201090b06010c060b04050a02210708070c05070306051608100803030610030906021602100f050708031302120f1b0607 67
    0x2000d101a602014240d00603920140e501040b00b4010b00640005161038201c0340211084c8602e0b04045000103521851080145040d00c4010746010b400c40030141020f401180c2644c1c907103076255481c510001146c1d400301c60701103502000000c0350410b441c3c030441b40000380d030388050304681c1001d002c1004104080503140c1c00103001d091114a1117505d14140d0050700d03228040f11340c000d103003508100384140e0ae030f0018080c4a1f82c401815141d60403503210100100e100350380c8480000c84d10400580300c24024801d60119500840482e0321199403a0740f0207007910402ca51058050720402c40c0c2c502602e401000141d0812400510141c00390304100100c0c1d92800010701aa00c40d42c0c40482c034680a5010340d000c0803c10303400c40010740d580d84003c4a02c501000031401c0c2280507001d41c000c16001c841c4500c0543c405404150766162a00040307448100c6203810207005420f000c0e040201620040c0d035200402d105420403000030f8010366880405042c203040701c016030100c0030415012a900c45580c1c61085880103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 748622401 1250 748621151 748621157
    0x9010207120c15091511190e0a080703030302040303120903080f0703090611090f060c150a1e0507081e062427010504140f1f120e0c01080106 62
    0x401160410303003003101a001004090f07a1400486109008603046103440e03100210405002c1101d90885d00d01c1c40384a4040005204c200003601c45c8450b134856203600401006c010074040300141c0300c64a4505124441d442140030a23030001e030070000c041d081401540018503480d4104a94102514041c16044d801480c011030a01c1d8400010f0480d80a80c1c041c0e580356400c0721041282046030080345000e5402004618800c80d440844408140341020481d00b41005c001c0c00b81070310b1000704c00100f8590501901d45120251299500c41c0740341c50740c15141c0c105041c4068085918100b911001d461b12074040c010503030141d40d98682500d00b80ea11160940c1055017030b101d101900e000c144521118910b11085280c40030300001d1a0068089020711102d24150741c0c0a8582c0c60020000056604c1c3c80b03980304085c0d40340074010740744440346401c202480c8903040140882c00110320120b5114186820710f9200404145020900705100d0140e10544a214449000a00050301032a0000e000018140316007420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 748623651 1250 748622401 748622417
    0x6050105010e030d0e19060315080f100c030b0d080703140c03070b0a06080a030507060510120809010e0415170c0108041e0203030a030e01050a05071e020304120602120901020712 78
    0x240c0c1c9481b100c4403900000080441e8045031200d5004000d45400b014118001e129200b010920900c046052405585481c0042c1201c8011054003406014405407802c00c0c15500e50820510381c9070f02e5540d0306041e22482c05a1355039a09031a02520380c1c0001d2200e082c0f0000c0602c9050000b0300000226581c640e000b012192580d40d4500d05000038011903008000c4c0c5000d029098810190070001908200c1c2c8178940c107011079581c800c054000c24099100d40802c01841b45441d20108040c003000b8541d1107c180740080700b40b001c020125059821152032400c9036840000b0401c0b10308000851407001c0e0004801410040503040d00080130084040d2011b0070950307004a2148480c261420b200c085542c2c0541039a441c0c10340800003900800382e1000d090000d500300f900150b04952540301e5244251050740720a5001e0684030041110b40c2790744404601980300820000c298400010100c2c2203083c400c44e400f507524491420203403408200507140300c003142c1c0113000104c001441007014141b00d080324030309560 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 748624901 1250 748623651 748623677
    0x1b07080c0607080c030a020304080d08060a05010521250c1a060604031e021804050a080a050903071814010b120606040b0a030608010b190b09030304080709060306050105010e030d 78
    0x3c95124406071061180b01c0020485a0150084044d000300c0342001c00790380200000ca04140d503c2e000c110350710340d4041c1c001441400b19602a401034040d50300c00154413210055422014400800c0645040d111000f4107040c000c140c424029413141c0c500030524003c1c07001c3c072081d51104400705141444040807050b210019800752290416030340115044001d0b140d2030380092458146407501484264080c4522a00c1030b418250140003d500403a44000148007030001500c50307200980014544a04014041003a500309540801c480f1002e001c4a4900c2d00402201c4011001159441e1030300c22070203c0c061004026071080101540c0941000c181c10a030315658610000b42c02d4491600040105400030610f00c6600c1d40c954030420a85101030000c0048040d014200100c4008015004414024540081c80301d030341418043e001303403080507044a04240d2200c03242c50411461344c00c040c000b40c0c0d1f92002001403240c240629801041c1c2801e112404a0844001c20707219400d64401005214007103203214 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 748626151 1250 748624901 748624913
    0x10f120b011a0c0601060f200d0e1908070f080f122b0b0906010201060506070809040902060c03030f0a0c0509010302180604091401090c0804200409081b07080c0607 72
    0x903500c21400040c0c40640d0b841b1503014000c41c400c20345140004802880f244403850151005014507402a40140615401d105080340e07038913100e120b600d03000100c190110282c00701380d11000b8040c000000141265508140c004040ca81969000d40b4417035100440e10103000e44041180a000341705501816690090f6200c44044400c2a400805030040558258090002154480003144600311503000302621400012400c0ea111800340d954002020800c9000144100004201700f0340003500c045002202a00000c810360004801c1c103115030400001c00c00c10515071515107610a80e0841c040080d0034840030b0003049401520822030605500260526010052010301090f2040042c102940c60b034a034400480604200040c02100b4156480040ba8654560281c92a01e4801d0350b44c0900f26612900c800d01e1000c0301e09940480f0b100113050f5240d460321140900d0760f1150048020035940c0c181000945840004421401c1d00d1f5002408284a0650045407211000708225100c50311021103081071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 748627401 1250 748626151 748626157
    0x140106050a02120d060305010b012f0a050a030f0809061e07031e0204061d0f040203040312110a08280e0f030d0e01060e1303030c140d05010f120b011a 66
    0x6030600d0040813030345040c90a0a0b8001a064900c150300a000c03403106034006441c1c3c4071400165201c25818036544010700d02203540aa60302c007001000303d41104010f40c0351503040440c0c0440c107a0000c1c08100d601005141c2107071030703d50400c0b44003006114920786807030785030b11401620002629407042280800c1116200380c000d203901c0340303074030707030f00c40d0440440c0e00c501c90080d8824403c000c007040082c1d04612a801003d1800380004a001d0101000c2c0012131082000950000b04200c0030f03c42058441004810603118198001d00b10350021135a511b80d4400241c4882002050401640c91450080c49203840c070f6142842c0c03a00c281c02c400304036480041d440ca0300300750007100250150700c03010030500700d01807007600304088120848000300002500c5107410041c0540444403a40345e000503e48101c0024880d0b40700e1b00c0107000b030f860b11520322000902c2c00d20360b9a101030801c5c100c051719600184602011603034010010148440107a8001085a03a07610b800746051080c00c444031004e4044041d0b030010a422 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 748628651 1250 748627401 748627423
    0x80a020d060e0f0f1c0509040b0126010f0b030c2727010e090d0807020a0c03060b0f0f010c06090c050405010609080106060212090409140f03040810140106050a02 71
    0x55460115509551036600d80800d000c4c40b01c2c0e4031840248809107032090b0075555882074503540d00d914090702c2e0000e12010382031008446042162101c0035003050080480c1c160013151045107099000d51402040c06481c50f86074004801a0000304280060396044108403281809400340b001400c00388554200d1204410880705600144103000340d2981d1003003018540d803000070303900cc0f4082d243d8072a00641104030741120741c006240c7c040105420814000d030403031684581644110f030401a0983d403000d0039901d450780111080741d00d03065102c131645001c803044a03202d1010380d444917211800d040000e12900b0504000303807602e56a611031200f40550b00d0030000180001038420b00107540d440e00b0003801e08550f803051801d207504e05500800e90901c0460b107580c0c140c2614284506081c5070000704001404070324012a1419a030070b05840e03080206210346031000701030710060345e00c0ea403500640301d04081682070170075142483c001d90f21030076880100f461b0b41900c80c18034040341c540c2c116a1060b4944854258 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 748629901 1250 748628651 748628653
    0xf09050a0908371b050c030703141c0909090f0b0f061c02011d04020c0111220b181503040f29070503070306030f110a080601080a020d060e 61
    0x1038503040c0c10400c100145065070740e019404481c030b504a504104100d881c4030864002041c0000514459144420101322240640c0a540d400781d0300000003450305089900c100e58005c0420380303800f101503003031160000c4030120070503000b100010b0303810003001d80d8018042d100c42c071940c480018003441041c04003040226840058040d00741400c0b022909070300001c07100c0d1403041d05075444a0005080510300407070002d506840d6400c0b001a41820740403002c2c003910039030360080c3d8244141e43d21114240600c3c11004900100c090341c0340500c40e034401018074410700ca441441e241000401040c0c80a0080310555410030030455402e112450000760301c200c00e0f590000030040c011050006010848420580f00c0344100709825080100c5400707141008030002c0307181e81c011441000680c416020b40b00556201c0458580000c010f503c0e42d031140040000400f0a4854044000f02c10006051101c0b151004d004850001c0c4115803611000341d6a803904000c0c000d00441a082c2c0c0102042416000800c0b00c0780300384 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 748631151 1250 748629901 748629907
    0xe160f211d150405070f03170d2409050a15030818060711010818030a0e120d0513090e03160c0b0c0a0204050c0918180d020a1403040f09050a0908 64
    0xe0768412003030b081501c040e186070149040006000481c0c415603400c69600c04400d010f44411a824a1500c5c2c01c072084c003404407515203181c450380c4041e6140c44000c14407a000094005030410313140c8030441e0030042405c40d0851401903051381e1718841081000881e5801000c07240d903114860060142c2c1031480d0720703080d00000003088040c100008800c05d00201c100030303a039211041d510a00384541c6103205180604943e00100305000c4a43e201c0c2030018462000588821070230205401c19030318091024280c41c0c00580301207504000c60b4100141e15008103500c00c014040340b01c07510840b43c0c503881100181210340c20300c00500004c10182d0540e1100030589090400e0f11416804003844d225031303089104a104034609000146c0132441c0c041070b503a00c0b50000c0c2c001c1c110001c0c1c02104504c1c2c0680602040316507500c6280c5001c080400300a00c40010b1099805003102840e9441c1203920009480c1c00200c140d0030a11040c0080030713440d4a030360211041540041a941c456101110041010000140c1050400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 748632401 1250 748631151 748631173
    0xf041109060f1903060614070212030a0e090c13181b03050103050c09041e080d0501080f0f0d0806010503060d0c0905072c10090e160f211d 61
    0x214002d028402e440100648403030fa1040d004034201c0b265805600003244d010521090702521450282410038400b80092060640903500149190040e000c401e0000355001d03543d00d0541000c18890350084409600b060800d00544a25082040c0c00d000396103100240b0b1001040e20021600b000c05050480d482c0b042c1056030700180200500000d010681d100e2084040e011042d0500000041c440d0345c02110007600701c0d200b074640542038800d400003513900e000140012460f0707600d04d03c644d45c001d00000005142e0910781010490905004400c0e603029500302c002d014039100d0708020b02130340c010307000d280c1507a40b640c071800019101c2c4940c01740946222440c00e80400c8201241e8011400f87c083c5894000b0401214003408061602451b01c2002c402006000c41c613860500c081c00141e48029410680300603501d40160440d1804100c55500003801d9003800c80300c9541d007010300705110f47d109182020790b40158110403000201d03001e20404d05640e4500b81040e007101505000d14104002e40d082e11005601 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 748633651 1250 748632401 748632427
    0xb0d0209130f1217090a030c11010c060f02040311031c03090f050604050f010b0a03050a060f090b101401030b010f230408010b030f06040c06111002040915050406050f04110906 77
    0x3d1091940c0b814200b4400300d80b0240c400941da4004950550307800c200d50782c0315a9644c41003141c1181503414014000bc0301c0c8001542030080000000035901c00585403461070810402c0441c4140702039010380c22500c14210600c01911009a00c9082400c0c04181140b01d460894401c000c4110050528081c2000b800108100480e00c1c28a10300c00038001e100f8800c07038030300b042130310034440c40000c0080c0d1203884100006403c88d0020081920f40040000b9081126243c040392054100c40008030340c00c4400d001e20116442c035841d20301c0c0c1d80c4203107020051074110b0030020b030203407980041c94001e00c860241201004200d44030340e481510038022009882d40d50345c103403180c082c01d41c0c00f000510030700900e2000c1c43ca0f5840001c07072900c00d0360400d0040940500d44201039555010342c008003845802140000060f81500b400200000d00e120700c000141400400c2850300b0f52039254100b148110f080c030000300010343e40c4015410384030b0300841d00003070090072003c075002c418030902d4951508410046607441607060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 748634901 1250 748633651 748633667
    0xd09113f070504240b040503150a0209060708070c0e1b0306150c07050307090c3606120b0d08031504020d0c080f010b0a021b1206010e0a0b0d0209130f12 67
    0x8400d0358460390540c0c5900c1d4480c5d82d8080c50040d42c0e0150b01190342c001b94441405105600306201410042c901000c100100303841d54000361003611010790005e4600b080184058095004040d842521111400c100c4002d0f000e4510901440c00d00d000c000c4085001d0342c4e10354034051111340c0c0c01305801e643c071011194403a40720f001500c5801d10070b0042c04000200800280a140c0500406589844031030038050006160403100303081105003041c05030000003400061201c1d80c800b900954592680904009001c00c041e03842c69285940a6480c000400d00050b0502c026a03030131100c49480170210b40c0807040810000d0196640300780055003000017602c0c00a4000044500402c2d122131403a80d80d03078850304205010b10456540c1070050384040b06010421aa0881c058100c080040024003840c04220b01c25240190a8014110b4070003200c05001d20500680b00e950002041900c50000103d215000102d1011004000500081d0404103100401a45612143c0c0b0035902c464642e1001c60600ea000302408 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 748636151 1250 748634901 748634951
    0x1804060b10140a140c030c070905090d0914180406271a0a020d02030907180e0309120a050f0a0605010f081c050d09113f070504 56
    0xc540d01242400501c1a5020100c0c02d50702c1404a14010f200d1104540d07050310208950603503071007809161071640c800d100910150301141d0040c204181006510782c2100d001402c00b8096921000140006d00d401c0030221044803800c002001110140e0800f2400710036003002c002480a061800708000c02825500404212000740380072041c84c081002c8032403400c03210130400381400d0a8070b0410704040301c41d2126640d04c8820401c025080446412000041c3c0e002902d025010790842d1070240311140d207800071170480003070b0060207011206040001795201c1c030444003d80d000301e85030600300c030001d40100140348202d40e01c20704861820440ea5101a20382031401d5003160320382c0c02c00000103202c108560f081c60a841e800d102038007010104980e40c007004600c40c1d800c8030030f010303060002000410651080d050140e000c2c88202050071401d00400030307401484101c41448201011b12850710001c40c4000c403001007200d011a2803801c4016050034600489640055031041c03d0140400b81c40c00e80444105c444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 748637401 1250 748636151 748636159
    0xb13020a090807210b0408120a09020102060a020301260f0a0f11090f010504150302090108030a18080307030c06151d060f010e040b0a030803010e01030c06031a010c021804060b 77
    0x368030360007a01c115084d8400d10005122800045401203065505029045442820050301d44070320841075481c0307040708980b9a0050366640034110250358040c001c8580c4207010642c1186158140802091000c451031140104034420070341003800250208145002500304004456802070140b5103944900142c0030201c415203241c01e041d014904010040130300540d4801c40c21912030b030034801403000820500399000120481800c0010258891505890103002140003035542c42815034800f5040c2415240c03490030039005500100310826001c000d0f01d40d1980c1c50314100130f00c00c010b8240200545407a41c0704c000034401c81e18001480140074502c0c003041c00020503a0b0b1107076913520010080044100e01040340410313501c50b110f001a1600764890f00c03614600074490a5120b440b5251096036400036000340c190b14004400500602044820000003001e5a03d414031000c1074441e010941c075246455007506000a80200204650352070b41c00c000d0045002c1c0c0d03915120310309420070301c020304105480b01d405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 748638651 1250 748637401 748637413
    0xd0b0610090608010605090d0b0a050106030b18060111120c16170c010503100b0408010c180b041520100c020c06040e0601110d11070501051c0b13020a0908 68
    0x459800751550404854143e180e030101a0320f0a1030a461590000d01d080d5440020000464002443e00020384d000e44ea00b420001415810400003400715561042d16900c146070b103a0b1074126500000600691005003840e04241503604510703100d150107485525542010800b0442c41c508500c0042c4000d40c008414402c1d40f2142e0b03980e40c1048410a519441c21003a4014402c42c0205500a000070b50b001180c1c0a00c4a02c100c0da41c4405194a0300320341c010310f01503511b52820809495105810240740846107440c0c000c030518041d1580240d10070303480307160034545000c0b045901c100e014080c201d00940040e458007084140000d030791511401d0165105204a01c2c0051362a115840000d940e40804e030081e0101740743c5418514004264840181000e042090b640f010481401050050f1640c00145441d0400300911891802d401c0c1401034000700c3c10441c060100d04800c02c4095180006000c1010300000d06000d42c001083c151715119608600703d5000003211030030700b0740c015030580c1191a4130040d588 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 748639901 1250 748638651 748638679
    0x40311122b0e090421050903070909170a050a0318020405180d020313120204200d1406060d2f180915090a090204110a02370c03020d0b06 60
    0x2004044e10f02078500440e5000420000d4040c08010824040c2800c01e141000e88010006e490080c2c0e030781000100380e0300d4549140810810300d40c81b01c000c80100c10749a050241849004140b40201e00c0741008050b01c43c0c07001c00a41468500b15458541c02410500251521603124802c102c0035030584440d501c07030f02d80d00c0b2802510200a031403101c0030350b01c0904a4180f500c1c10071041c1901e005d03004d0764019910303100c07400050804e00840401090060342603445201104a80084a048464007110300c0d91403010851166074410450344858903217400062502040901e124825088040940350f204501c04000405070022000c1c110130300d0847c01100d4a0036015081c40007200003a12190640380d1000415007a91a00c440441e40c0450035100001d103000300c80c0c00141c00d0707074080f04030544160000a60084000e50501101600e818442078400d100a9080003070040002015402c0c01c1075030040000c0000c00030214003c3d03004580040003851000100e007030004103840e0990340340784100103041c0b82c1e007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 748641151 1250 748639901 748639909
    0xe0c010801051e04020f03090601051801050d060908070c030506150a0e010603050403021f0605010306380d1401060807080c0304080f090409110f06040311122b0e 71
    0xe410303540040c100d2803203805400180b024041e80e1440c00e961042d0207000080c4a8031785400958401c54001c4001e100d2940b411091058802081c10b40c0240424990010301c034648a000012550030fa00c0b00000484032580c4c1080c1c04240550301c00206030181803e40007080c400300152450051340760a40301803c10a00e20301300411010b41c0e1240c603c00103d071600401022340660301c001d611074020f0043d038103003c018942c442e802c40b4600340300c007480782c0d52401c0078811964144120f40c040c21640c120102c20841010100451003280e00d000d015030418007200950254806007903415a09401c0b40520105d4012019507583e600d003401100b00180c030410004203c10310444815016090354101146103454540b240d1503294454003a80c0f10b0180304000748455a00c80e4864401c800c0d0090301c920300100181000c01c0f443da0f0307400001520600041c0006d102044d40c48442c610004802c8034002c8403d40e10604490601c3c3c1454200c3c1d1240804c1c00b40107032000d88008220700d04085a540b540c1c0034904100c100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 748642401 1250 748641151 748641167
    0x501050f01020606041a03060415050c1c090c150804140a0f030f0c021c03080105010504050a090e01060906080307030807050a050a0810031202010c0e030f0303040818090a0e0c01 78
    0x980180d00420120b042170601d680710103071a0600a2152244003a07800c040392506d40c00303480454048050386909500c5201c14460590021201ea400d149042903021721b1303d20031a49441a41e22030355503003200768104468901100c3c020280200310b200422a4044064541003080350f0507602c0620306940c1c1e207250000411401e240c140d01c104140c1c694842030300e08550480209500350180320b4844240e030090303038a003202c9200840642d00c054503001003614000742130700c0701079100c1c505115041c031091249544120080c0203403086440c0024070001118216809001103500c00100180303000380202e2103440120081c03501c1070007074075000c00503280c80740215614411000545c000403070078003280c0000d5106030b40c12600b0058040a242e000303501e81e10342e61604c2040080b8600947e65070715111440503004021803030100c00440241c200c4100911006d07480380f00007400184550000190907104d160515020b10b400580501188003524080210320010200032402c0c40702403007880326081c0700d5840340c81d84c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 748643651 1250 748642401 748642429
    0x12060b0403170d020c0102040b090f03010e03030c0a0e04150f06090b04120602191101110c030708131a090f2d040e0a0c050f240703141804050105 64
    0x581d2110b0080c100400d412074010202c445000d40e02002a903510000c240003410250007060302c4240e44960700010841c003401101c000782d000342d050049011101002005076507014002c2060140d44009151040303408800c05150316074014640180701801d52014001c046c19549903943d03c00c122a01d400054030303169541c2c03140042c2220108020310140400d445401c40c0c20784242e40140c10210b599200306007040b03c4c40e1510b80014210056109010f00074042c006840940040c641d24007000010440c0d2a849001c2001d0a07079180001c4030181d10901114082c010051901e403071101000c005445a11030b40300300300e280d00c20380755815030256900c3c200c800f03111061143c819150407410400510760545108840c240e50091380d9000103060094140502410035210303c2a0801c00c606207010010340b45c50b003524540c0035001241d00c0c5072111002c10f03400c506542a03000c82a482c4e14080c035046408601e0740c0300031313403600d1004944901100301c0940b200410040c100d0b010300c4103a8858003807200359004208 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 748644901 1250 748643651 748643663
    0x100302090117101a27070309080706200a180e0105010c02151c0902030709020703090e09030418150602010e0c010302031509100303020d0314071b0c0612060b0403 71
    0x1c4103c0c1c20800540c08440705024103104503c020b4a078200007149900300300c51030101c1c2165200020f4841c0200d14040364400c450741020085900c0036102e29200380a0b03484020015550340d0590200008042d0b89200e100000c6030000c1da40700703500d0341c00a00c03440080070070013469410180042140c1c080d55038928189c440682d55030701c0408464080008450b030204000842d031100300201d25140b00d5041300d18590088040740410080c1003441414030f0420031f030307104500e230354414060040000da0100f888070442c0d00441089103c1d8603105c904904501c15644040d04100407444141c000c03002c182c00a410030424a407401c40d18a64918041c1d00b0307500c0a12210360150044003860243d0340c001c2c0e015681051407450001040c07200b00780803543c080415108006184030140c0d04008265040110355001903841c43d041c00300312100807000107610b80180558050150b4803030303010300004101003002c8826400080c04110107a4481c0301500bc0c10f00b12411002c0320303082240106407801018201c40460394880 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 748646151 1250 748644901 748644913
    0x315060b0c030703111506132a17010501050304170d0519050601020a030f03020a050717070b0a090218040201051611010f0c05030d090206040e0c09041d06160c0506100302090117 78
    0xc019005c188c1200a00d00340d41d075425401400103200d0041911281c000602003030200e420b440c0a02540000291801c0c03071403c141c01403000383d902109890700305510808010000000b513070308044602030b0010030100c0914020130001c2460041d00c15183d0841d00000800164840500490301c8008406001d004150750200403002c5910950052044400d1460f2050802c1426540c103032540b030010f03103207c0c09140081682c2c0c040c0b00118800c01d82000e2640c02c1000141010b60104038a1181c66a021030702021920015081d0f9005200f1a801c4030030410a80050104031300c0e2005181c10354440681c00500c0d1070031703a50304060040a06403007503900400214200503ca60580b0090201088226040f9505020015906404079000da024a0703140d981183c41d010008144021110100303812054519942441541c0c84400305055810940c4808203456030b000d0150309580c1400100c10040c490700c41d000c2049030b040c80c0c8000340c3c402d80344200c682c1d6003a03903640c01d44a0030f00d400c4030560720701c190080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 748647401 1250 748646151 748646161
    0x40c090e030c06182506030506120a0201030b0a0902070507060801080a05071401090b04080102030f071e0806060903070e0a0e0606280e0c1b03040b040315060b0c0307031115 76
    0x440055132949403800103d812201c0b03141d08091804409032107920303450080110910005805000e400e0380518181c84403d8403a9480328910365584c004217010b814503a071803000b0119a198482c0c0500940342925095655030300300c4c81c06030790303600c2c1d1440340d9400509a10004a40e80078081220401740f03400c000204a81810480315084500c0d0055555052215021000a40041040c0500010b0650f00001610b925051350101e0101400804250802041c04031040f2101103001d00070140280031324002c41c0c19175070100881e0f0145308102c0d10540c148200080040c00034a5901107502c20a05a1418020010301e154504e0756100c043e1025a8065951030f0191103908102030320017890740e036500d209136a4650343d940d07401107035406560410074101c0000b025102c048060f0700ba2086403c0382d10085103014540902c0460501481c0401071580604015000c214596a0041c0300075004092180742c1d02c00d0540c00d183e6030380c0c0c4081821400700d0449210040d01e007202045d0350800c2c030110001c0302d06903524 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 748648651 1250 748647401 748647421
    0x8011a030c1b070906050102060402091504060b04152c010507030513030f02030c0306040c0522050a0605090c040e060913050a120324170a0506040c090e030c06 70
    0x8010000e049101041c80b4248031051051010344402c9030326006404201c0c1031110401c00e641c40d5402190540d80920b09000040c0c403141c05141d4000b24032000c94525600907800600500a241d100410b5158040b8011510700c0c078a4800720204422511600706820108602c0c41514461131303491300b040009900c0d4000d055004078000c0c03620f50300c280b80a0707161803001e00c40d0b921124420f40082c0c80c00e162080c1240114201001070b5146154128000c00c040d1a042d83c03500302ca480d8901406006262005e0700014240200503141e40003030302240240503600c1c2603240c11008100a2049138410382c404c0000c25005500d45c41202c1c04d4982180001c0115905c0000b40b00d07010340b01070105c108080b00144082c012030300920044050610400c0e0400028040c900000c1c01c2c0e680080c10010f40f01c0710403100c007207000c0c25000b6036802c483d0420844001c925498512504011040310058030501031321041000304069140c1d5401030390b00c100c100b001844050f454540e1703030f801030260400c107030b60114011072a1024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 748649901 1250 748648651 748648657
    0x2160504021c0e0c011b11040c020a05060c1206010504060c06091104290f1c050a08040803071703010510031e0c02010218011b080a0905090c071208011a 67
    0x70301108110740c0050b5101c054012103e00d0f81c0b0902c1e06410000da50081c640e8080500d000c00c041c00241c0e0f418200084d125000f01d6100101c1c1144611b03681d80c0b40c201c01a0013440410710540e0031000391907840c5000c000341001903000340c0340f04100c4411400000c0b19036001f07100756415100240e542c0560300c04550341e514000c1c45519016500601c0304010341d544d50351079004006151402e03031402d080d88101940b595101c031540a004500c20710206030002c0c61070321280c840a11304141d4010200403400142070136400c24131205c002400a4400180100780351800000034034103e889501190340c4c10131103840b10152400203008042c0c0c011003038210f030791445100c0e0704008142607518081d1030b002c08c030359100c1d2001c413045441c9030030240c2d402042c48440582e0548500c10040420300f0151a460301c06543d00b07850940c40d0100420501000c0383c10a2054464410100030382070140065842d805c1c0980400c1380c513000454200c82c8440d2070704480c8001f61046802904a4443e0702c40d8a812040d007941560780c1d50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 748651151 1250 748649901 748649917
    0x507030210051312020f1011181c03020601140a06081501030f0f09110d0c0b030408074404050d020414010e09060c0c06041515240216050402 62
    0x40d000d21000760114150801050100303100e03400070684540040d05880c1404540342d001d4064615003c20b0380601d231081401c4640203203243c0c2170600000780c0c07000003030724031a0f08940e182042c038070080240781010703000580707241660400007440c0d09046910341005452901401000b00003180d5902050310b01c440c03030110344000b0005041c082003998003448205e0484400d00c0a40c180c00b41c480950b030048c000341c11200c0d800104169480d01c0210b0749602d403504285507030704c41d01d074007160f00000003410b009030802035481056002240ba1000215040c00741d006488200c01105240c0480c01c8140b1900c450540301c0b40381458070300c0c00c142407038940420401003002c1f8040c1a6041a01c450036203008006ea0140c1c40e0180c88442d1004910303040003d2103502e007040003845d221404904100750041e0314000142c141c0e019034030030443c1c04003c034040141c001401c1c84d140c89021400d11102e000c80c054a402c1400030320b0f45500d880c03000c207554030400b01f00d0342d42e2044400321600c0c00d0320050512182c24650001c061075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 748652401 1250 748651151 748651171
    0x3100507050702120319140f071a07031a0d03020703110303041d040615060c0807080c010c0804030e01020c09160e0d0c1d460912050703021005 63
    0x3051440e000705240403540c140115250f000010364120045440d40c0c086c2e000502441c003001c010004000204080c81600e54014860001040c1032040011f4002d2420000c1e080c800800c0060400c80c20141c00341c090f010741068201d14402c6c49080c0f41c1840c40e03079141d8541e019070061144520755202d0074081c1403007601c040e41600007003101140e202d0000000e01c6015045e00310324041440d00341411400c4445000da080d156400c4614108903007035010348800d0420340c02c1201076584000768039141204c0d100300c40c1000c0c015401c00e14101107254100c205644124029101d2100c0704558400481e140d01501f095186e11030040ca002c40c05c62400d4411609400940d820b285502d80361440010311056000d11044400c3d41403000b09101c0f90000c03010002d0310626200340c104040c2404030300c0814911404e41444100c500c42c8550040c500c41040000025080320980c02c10451000801c240141041d42070507114010034135400c107141880b4900325a0500c0e0964040c00d41c010780c46003101d000d0040a8051160 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 748653651 1250 748652401 748652407
    0x1418010c02010e03150f100f1a0d050405061f08031b0309030a08450d171b03040302090402011d15030f07090b04090e0312090a0201110c0310050705 65
    0x203c0d40741000f0490f0703d210f008000710b15034074010355610700040004200700c00d030400341d401c1005500d05112001003501c0c0710300f52100c07418404044400060150140024115003008240010301a011a40c9400384c0c5d940c4c2004003200b40c1c81180c047c0e404000303105d4ac1070b842c1d0042080d815800c01c58051641130742c1c590380503a0725103405180002d1501c12030f04019180c031000041c5040d201748443e250030960b90b05c030017542d643c0b0042c3e250b0f01410921185100280d03a410f50340e02512699103600036464025071100c00b01e444840020411803c0b40c20501143d065001c45444541da02200001660104e0350700404da4811a511030f401169451b1039210202c524202d0301c441c4506a03030715541620f90302040788243c65203034549050f80c40d0311100c01401034401d20070101001e010540182c0304960035581840c001007115070040801a103140704502040300b0203804003052200501020805d5001035000342d9034100740d0700304400b0203529580c45182030381d0306074845512070b440c0d2042500f0090f0700c01c52605020341 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 748654901 1250 748653651 748653677
    0xf090908090307030c17060106020a080a0c051f0c080613020903070b0409050601030f090b011e0e04050109030f0f0e0f04020403050a0f05010c3009020612071418010c0201 75
    0x2c0703054040d810443c0d03140170124040c8902c000a989090004040000400b0307103514002e0080c2d01c8240303400010306100c0001078500882401031445410365640403040b101c0b0000030801c90b5268509060300510907074201813002d800e00f881507500c5c03401a00700070b100600c09852520410000e510603005107030180601c0c50002400900d020140c0010503a4a401044034684a000101120442c10000042034589403550340454461091541501c10950076080311200030301c5040d510310070035804a004090404100800c02c981074000d29103c51283c2c441c802500c0f03000c0c2c1e05480c01c4150400d540c0020f8082c0d0700f21a00e0340b0b0700d002903042502018000526054498640c141003100004003640c151904038015002c00100b44140510301b451450150008040b4101c4110078a910315041c000d8080d408404009201c01035001c04950741d4018107403541e8480c0c4916403071503140126400c002044061684100700d0f031150007103c020030708804140c0350b074803c888015289451544e4040e070420041525081e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 748656151 1250 748654901 748654903
    0x304121a04080310050a03050c1003060906170f0c010203031f12030c140d050d09020f03070314012009240c03130b09180903120114090603070f0909080903 68
    0x41c0c011030055118565034a0070000302d5907000a958000c0d03028076101b4030b00b000440c078046070285003241c08031040c0103c1041c82c24100c0c094074058001c461020301d8000b0000b44140400078114601506500b40d5604504002e0401d40303592035808210f001d85c000300b0014107540b0140300340c0040c054012980c1802c00c1c1d11510032041c903a90400c01200425075035502d5800b40300c50450400041110302004049111010400514502500602c81c540035161236070b56045640703040300c185440310041c04032000c966890a05000c0441502c02c68900e9500e0b046202c451804c1903199034880c4005d00e0580d900e80441e040c28407020030114482c040ea05000c07241520700c2900307064020075285503084000c4d5120f445403550380441d004590b010200c80ca000300302e502d29a8644c08003051040c5244c0f81d243c4d08540c2c4c0c02641030300310311030031400400f441240b07400464145051728580311580303819030302d680c0c25582c2d1101b0305950340c205002d220540b1525000030003140c0d40c40d402c0b241c1c1072440307540c4560034608040080307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 748657401 1250 748656151 748656203
    0x20041512020c011401080f0606011d130509160f060c230703060209040f090209011a04030b04080307090608091e1f0906142809080c070f0801020c030412 67
    0x424144e4a50000400c1148070400045583c54038000107003450f4148000041c0440c001c03004007000802e104e4989004a0380c84e080500c0419294007001c0c040d40c41c2801c0c0c010785903050b100c0300c0b042c00c030392050020803680d400544490503201e1580300c001c0642081d448890301b680194a004060b00c1541e8290b02c090042406800c00842c0314100158070340c0c46039010002650102060b500d5482e1038401c1480159503400340641c11110091041030442560641c41c1e003e5204541015000320002c400703000c00c0042502c000e600c9040a40e465405040d2203400446982e001500d43ca41c02d5030181544081c1c5204000026000412110407251703400e80920350010f031000c4403a4030600e65580c3c0d40c806000d20245000b60680c01c004000524120b1070900c00c24030010042e002e0480420b01d0098011005d84416400f10203403540100840c0d44400c000e0b01c8140c0d0b00d803114041c6212050200c1c0b07001460f0303032050094803915092003001c0c50905046c01095016041044402d442c10040c203c905454200392104c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 748658651 1250 748657401 748657421
    0x291c05181f06080c0112020c1c050d0b0409031e090807030b0405060714070b0402040b060f07021f1205060d06020c0d0801060905060301090203060f120120041512020c01 74
    0x800e45140589140450b9400c0e4800c0401e90040924040184c0e40840d403406d05506580b00140c60b04001041c3c9450b0110145080480302008003103d10300e103800c480a0849a81441c001340710059811060209941a00800a0200b000c0c800313983d080041c42c8010000000031440d000b41c500303070386205282ca0b0003116030003038580c0107040b000c0c00140001800807a0f03004480b820708000030541c0740c046031f20f90b200e10f280c040c0040400c40c0c04603007155502c0d04600350070070000305a02d40365a40000412103076444507400b00d12030220a0842c5100c590400c00407100d09042d5200c6007107004007030b10340d0b1002d020000d04459001900c40c07503802c0011124405082c0c000e191400420580d00d03100c501802c1e042060f0824010700c0b140340020006540c0b40000c41b81941c990380e1015860740c4030800412810f0224201e001e03840382401e0707207020420b541544039502c60750010018921075584440d44041d68400e5000d1513191956030031071419454081d00700100a0011000300601e400318000c20303642110071004c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 748659901 1250 748658651 748658683
    0x150e030a02041d0c0904051c120c120c0c0819020307020411040305121623100f0b0904080712050d05070905011e171f291c0518 56
    0x140c3e003080f0070002c0046140300c10f400e84000d50541469100da9542d4904014030107c034480c0041c914000e603128110700305500e900004140b110903148600501440c00959195500f64a490f503e142407034410041c0f110000c3c2c000c541d003072400c00a107650001c00320315000c0307035030a600c010810500142c94500c40d09984602c2d00800c5502d40e03007140380881c00c10b00e0552030b040075804280010800d9400d800360901030658482c2e102d10050451007540041c5580c0380c8a4a58607000e0304004560711012500700e04400f90414a0402a02c0d80d08002c010400e03206413000351640009225a400150800512100c00b60741401d103242071500070700194055803400c9a840c0c0000c2c0c61f0340c0080049507000801c000e40c0c0300d50000c51806009100300c004200804801c10340b08072480900114911140c110740328400c0100404c0b054800a850b8510b000d110a07500320f0030380442d8032891400e00c0d0b10700c0000942d00d021b41002c0c40a01c642d084111140060a40a0000724600042140300079011800704540c1c1381c2010145 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 748661151 1250 748659901 748659941
    0x1109360a051e1507020c040506010e0d03080a0e2d12071209050402030c030f1005122503021003020307031b1d10020c06070620031609150e030a0204 65
    0x440c20700c1c00d103e2409100c20030f441040c400c1c042031680104407a86901e40a540c001078603601e680040380c1d0b48412010b41c0340c10280815121051580c480101886a421008180042440701503a01d58030700f80c581500130050750041d8840c03000104084600c00300c0707003a1401c440400e1122087e0726178542c44808100c2703d000c10703181c2aa207003e400085000007071034200e8046065140034080d880580c8801400c2c901b06088560014030009000ca1545000d4200501101c405405a0202690300c014401d0800340d02d48442d005091255900305100781641e6011b8120a21035006010079006508040d00782000c0c151113a4130034200c5141030802c00c09002541d40c42420920346080c8059040c1c12180c09140141c046850003110b0507000124450205000c0d01c046945448608050f0300801102800340603140002004500200b8000e01460080450b41c0012800c1d0341c1c1c41da13003030300d02c15180d210b450f45a64070164031801c01c60040f04040c42405026040d2080128281d0000d800c6920005400300b00346c03440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 748662401 1250 748661151 748661203
    0x1b01050a140d020c0a171c1e0c090906080316150902031f0c14090114090316050907030e070e060f0901030308071101020f0403060c05040806041109360a05 68
    0x2082d01401000580003a242892509080d6001508024945041503c8214581e600c100304420b03807230a2444200200150740761350740c3c020100d070020301c5500d0b0380d28100707000441c007010040103c400300818507108583c0d1a8a030790354054191201d1104010b010f565107048400b503201030111140b0032560341d4044070300c0042903943d4400c403021862208100143d044030100b415200504554840c402400e0a101d28601581d41406c540719143e05990540900c0707003040c440000c01d100702415584129072036400340da50480c040313044400045d800740c0a50b0188108104400d0080c2265070042c00180c483c01c6064407901c00710340c07110003e80c4110b00180c0302e0410080c141e54003034441d00c003003081030300294a40501c0f00104d00043c019800041c2ca020350303829254bc000e6010b007046400514843c0251052880c0a08008006041200d0228011a00e1400290442c200c1c0e0003440e5000d113080d1200f1104001d0000706030000c81c2e9858116070107108003c03040e00407400403c100c079180203100400017400740340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 748663651 1250 748662401 748662413
    0x5030403031116050f0402040512060109110f03040b0403120c110606040b030a06111611030c12150402010203040b0d1b02010b01020a08030402041415031b01050a140d020c0a 76
    0x1451031040d0a90441d03c480680007800307402d501c0869000703c404102c0c8440440004009200b10b620095000e0300700700340d41700520404141103040741c221040c1040b443c940b00e464090140f280340d41e1005050020800540004c00038102c40e50824080d00c1c00c03515040e0340c84000800c40b0f450100c0f480201d190203129001c1c17503c080007035650004050b00d0601240e01480046561400031580c000c000a488040500c9402103101c01e543d06030520050f411a02450360404100f01a00418058080e019201c4030f001e25060114035004824580030091040549204004103542006041207046010804c0001003442c03d000245c0f51a000d45400000c4001c0094080c80704400250071200559060440c4010240e802140b540a03d940008502d9583e1b41ca074400540104020203100b40075420f40014064100c64181c000030540c03000360200e5603141d040d04000c01c0d443e409941710303600160080000614591142100190701104442610b0408184803106020313038003d68103584046d40b00e10035a41c14800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 748664901 1250 748663651 748663667
    0x306110f0304080721020d031a0a0f030c060905150304030c0204020a0e0a120320010b13021209060c03060613080f060613112710121a090604051806040503040303 71
    0x2171105803103695a580e214040d460758180703a190820300d41d50b209130042c0c18001d0110000e841034000c00121500c2e8031541070816440702c074003040d100c00c0c09080c2c02189441c041c010f0841661801812031180101081e00070529070701c0240b084041003039060800c00182c441c0d0016106040d80340c1c4510005041d1102444520205503007c021506081708420000c650441d072480c14008180404100440c640c001c140c0c090030b01c940d020f9402164108a048c0080c080d0340c0546403441c8882d049c00c0068640402c140e82c1d401c015242d852040c801080803c800c1d18015005000c11f050f82e030111044d242d96100030505115400e6184280c2d0b422480400120b403420085080014401e48806c20200c03191400951042c000c203102c24040021400300c5c440c031000403078615201d607100200400415500340d10000d1140c42d08071100d4540c00d0a00001c100c043c0020b400c56041c1c6880038011007100c0e6915010407002c2c00e40a0300e811300159800030015020b49003801464446c40c010750042d541c8916510300208410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 748666151 1250 748664901 748664933
    0xc161a040809120c0f010e0123040504180b0c091201110c01050610140904020403051b030f0a08070b0c12090303040506060406030308070c15060f0f060906090306110f03040807 77
    0x40c04c164413001441e6510801070314540820700e8400a101134200c01612080107501034280030703c5200c45040f02a054441c001e1041d600143c8041c048031030884e104042203d08401c0040c400f24000000074140084800a4440254000d0025401c251042e200c14219144d9468016601800103242c00040500b405115081241500c41030100d040d403140061003160030803070b5203000f050001141c803200c1e03a60740c068801441d004801d44200055000c0d0005850120400180c000e0080710310b07140032030b0030220340c0120349a00030140903d0041a50303140440144010311503694202d051110303900b0716040000c440c1c0700c2c00d140b500a65880c1854203240c2c2c64950020302c0c1620a6042003011300000754003500311074010889003065005250702d840c1094410f4103400b8050308030780c80c0c01e000103040500c07805168111000069603d0071661110001c0359004624080c10001c6441030408100141e2998001d6081d01c400b1040182001c101000700d000c0c030761080d40c0c107070740141000c01c01d80140b02020071800108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 748667401 1250 748666151 748666153
    0x606050405030a0f15141b0309030a03150b030106020a030e03061510111f1a150d02070512180301060509180a050d08040b0c030c161a04080912 63
    0x20618010000b5a5410380307a0b0020220303061400f002e4100b05814404030080e0803125000c6c40103e5040c0b20891414804454000006a40000440c00000b07000c04a074003403103044024500d0111406400d9015024141c10384440307000c5840c0001e04140c01e40040c5018240300c1d409441e440c001810000c010412140503580303ea0001018003001d2500c3c41c404084c00101074612441c00b54113000c040c1d54802141101c20254000c0c41e505403141080b09052980c2100012000c10040400281c644512900103100c40c0c1c000c0740c03000030b04001c0240407002e040300500b40701d400b5150000c207544460510703032a42c282c40381d10304000c21803400ca080006010201000154020003040785420b0014040c0c51025194240341f0b40d021454420b6004144200e181d500e40000490754207200180d00201a550100d5080e1900079a110100da80700042d4000c690040c101198054201000d0702903000e81d0308940301041b81e00ba185a04081204035088034102d22590281001c5a210040107081c483c500e41c01c2450341180b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 748668651 1250 748667401 748667407
    0x30c030414011206060807170103021809030d060b0409060b12061e0d051612030c03050d06050d050c030f07030209010b0f070f08040311010801030503220b0a02030c01060605 76
    0x15010004103450844038031604100700511900c0050358440c51440c0480d5125040000101c0c000c0d4000001038040e44a99403440c4c0c141c2d440003079641c00c4507004c0c000258402450064144036032008042560002030240650b0f1611402021040480c1d98035448500054000700d0108901a442d105500041907441015850301d0074071100f044407100d0040c21107210310407507a215419a11000d40c010040d92020f0081c55001c4203a0415503980c40c41081000420720303448201041000c076242d220000182d05442c1c0f02081c100556065415801c406003081100e42c2d14000005d00d5074a1104014030a0301800c00740030407094004c2807600b003010f809090f0799158000b24007000145c40b2048010304640780300484545507024103400012a00c0b610402030010130039880e0540c02e01010000a104807132003031481c0d00410f82424015545000c0900c000f41c03580d0400d00c800d41410004c403248482030413054015141b07050725124460055042111507a00680c8041031040c01402c0900c1303924007800b500c1c10001c3c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 748669901 1250 748668651 748668667
    0x10e010315020c2a03010f06030209100b0f070201030b0a0311010207271d01091a0906061003091704081018110114070b160f08090304120c030b070f02070803 69
    0x1640750042a1165040303262181d000c960b40444003010110020018002e10050041602d03447c060a244d000c1644100000008501c0c040140369501046481e0440d66a00700034a076041c0c40c05940010000b0780c145911215200c01c0350b5907a408141c0550302c036070800d104ca07e001000081c6800c0b01d0760080799000d601a90700441d181800140c1504012984001180d140305507491500d5030303001118220640c1d82032501520820001209000503c8400280b034580c560b2a914219520b21060303400d643c120031010f140418042c400d070001103091303004403c3c1561902080c1d2105482c0ea000360b000c0e40f80e5820040030f07001080c1c0c49010742d1000940628044c0c00f4003060384c803040d0030382210440c040d042c0301c2e9405480075200c070300800b82c4101c150805803400f160725100c041200b211203450f030f03030741c0c00a01410b940030345207030080700c5650246055000441c1032505107405101001ca0b08501610f0b80d001011001000498204810348548055514034415201c042c00107031814a603034110500540040c00011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 748671151 1250 748669901 748669903
    0x30a0c170105150a02070308041203020f0303070c060203042f100c0b1807090c0c0c080118120c021c0204060509092104050d05010615050c150a0b0603010e010315020c 73
    0x20300209441d10410f98900104806911b44001da07032000f001000c004c00c0001c0c2d2807006201c00345205e406502510030580100c80340e40d80380c0c8011920307000454248864007022035031580c080d581c818402c0594060706901c0e100e203039541e010012045035401c021401500303040d080ca41d6010b0322031641e50074000c2c000b1001303640300c41e0440030061100c99004428012000884003c0000500a03c040310040081d504e82c0e500042c00b90102d62401e444140010b04001161001403081140380500020405009400ea5448001b0303242d107000d0600030072098011500140c1d5602800003c8110f41344030350986020284140700039201c159011a00c1004078034104158075101045010341e120034240c40c650b40c1c1da1030711803038441070003140c0101c4d81003540c28210b14100101580f0510030b0f20f14500c40c410300382d0038205d02200e9034890440300d09141e40000c02d01040c900b0326065519003052a80501190060b803a2000c1001a0000d0380400750245a440040081c481320941d032404c60888950158a4048075175105 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 748672401 1250 748671151 748671169
    0x1202120f0c2d0d0f02101722030f020102130b0301050a050906180a11030f0a11031003020613031a070912080a0e030a050106091e020c0a02091902030a0c170105 70
    0x1030740c056120601070344200000c058030103083e076900500348001d042008000030000c00084030b011810b1a8440c1c0808d00103d414150030070412a0210600030a1441c0e82c1c003110590070440036481550b400f84620742c400c010300305040e0080c0480c00100380d202d625000070400c00b18640c0d070081d0b0241e81c0f69070500295840d080060140500c9000c500c007165114013010000902c4288483c1012903030100074410310741140550f007800380d112400c0512151030120001a0705100a9940070541e8101d540200014104071001d0040360b600103414034506a40c913200c00340003601d50800845891070301020001e50b103400400c0180030b0210031043e103c114000b59140322a510403002e0000c140310400c141c02c0700c555010003801c2d400c1036001c4000d003c8075030b4a81c0d2120183c0000600701009500303100901f411a81ca5200b6a00349941c407600030000341e80c1c070743c00340049800007910b0161140d094003109440c13a20140015402000403100c000f817000001030000b02881008095603183c460b0400040140f41d6900d040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 748673651 1250 748672401 748672489
    0x15030614030303180a0b0103030809060f0f06010c030201140106030e1c0905040207151a010e12071a2115060304020901050103050a180c0f0602030403050303011202120f0c 75
    0x440213140c02e0070390410785003000030600107065481c0039002204069125091034060808801210304540362030700010319005044a0080c000403208c80069015846010400310fa213002c1d0000040044a000304506041401d800060109450304010308021070100071407a03000e060145404181c01074140001d20100d0188204e43c452900814110240202110900354200c55120100b09180a2004100c000001ca007069804a5044680220320741450408042040e00c0d03200904002824006d10349900302c0e0a0f442421900c0003403118007440010010b5181c0c1c0d01521142c014143d140801240060940c648000c0d80259030074000d100044e210000d0050550b002402c000c01e05a580d00400b200608940d841c40211810301100081484a8681610b0070754449004611031a0b803030746400c0c0c1c0d03a0300c61440000d003154010401009400014500d100000b44000c10140c40c41413042d808518103071103860381400b0390f003000050a420b8a07128080c4030038a0300450800032a05182c152a20b043e0070001c903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 748674901 1250 748673651 748673671
    0x509040f020405061b162709020a0608040b070e0d2607151107050304061124091c050904050604090803161404140d03090f15030614030303 61
    0x20840c6544155901a10007410016064549503116085d000f0076000b42200440414020600020588039041c0310200540c2c18820240c5061101c1e0111110003100240743c080389035907243c10720300c0180d5404d1100303001440c203692807445038102410084055003010301860103000b1002403c075680c2d1124045d81003e81d8020010107003483c3e01441d28540e44d02e4807604d071448641d001074558108402c0305034640c0315103604441000000480150a000d074400c4090203005c690082c041000f00c0e07482034008446480040099505102c03c0e13072600c1146c86480c454100044c0761141c10072440307160400000e0b48040e611001c9111070000d0042c0038041d4030858140301e001d241c403180000e03801d8589402c42a0190740c44000950340740b07007034620900e020b0020041d9000048a070010405080380f11801d58080d036214012507024540000c081102c80200c5a00440612203220070010b04440305980080003000c20f5084000032448104e00141100d20310b4016013030300c07001ca0001c601c090f1000000e807980200400c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 748676151 1250 748674901 748674911
    0x2040c2007120209040c17012702180c2205030f1f111c1b080402090f040213050906091e03030f0702070e0702010212010b03040201140901030f0504080a170106050904 73
    0x20030010b218483d0f5400000010f0310aa200c01f0054005512464900c00024250340ea410410000041b07068180200030350301c155200100f42c08036407480e95041c5c000200c80c501c140b904440f1038540c41e05101400103144040620001041a410309026807174052003100060501c2c01c1fa0008002103c0406d000928005540c41c401007030064810421544104c894101426610045515040103402000d00c0841100800a8102d0216001c0d54489024550090501009540e403440d9401000c8008000303a82c0003500c0c003912882d42e0094400d09001d50084009080f131450000182c030b140000c3c0d5003402210314152030821980e80740c040182c0f50058902507a541090301c626108a161038004d41110742c5025407c810b0101c2c85405600a1903a03e080c00100301c181e0780c1c1c810005020340000ca0f40a4086245803004d008041e2541b0010183e0303100c1410009140020003402e403044560854003100c802000040485641c1e0f0059030708070007081208200c011560400c100142540a202d00c0369000795216 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 748677401 1250 748676151 748676153
    0x70909081b060f1801060308070606031406190515090405010c03050717011712120a0501050409020d020120030a020303010515040f0b03090a12020102034f02040c200712020904 77
    0x86d040140155000040307240c030b603003260070310ba00105428482200c808081004900320075402181407031044048494030307240c0003135000e045406480c0081056440044240c02e0a8070759980c00c0780d00c0e014901420000500d00d403a0200135040329006000030091204000481d8800d018480c0d0700c40c10346012404d03100c44500304581d4185044603074003c16401c4500450b81c18040c0d008965020320440b1440c0301400166030351410300c012108a0340003e908801d411b00d0020265000b440e1007169240d03044058449070045100d414103580081c410b0f0300043c5c10000041140749007000d540f0544603140c4403802d140601d0040c080071007401500c203450b41d0410120004100010501800000540203c9018280d00501500038000d50040703a4810f10110150303a1526001280c00c0311424401e0360710048141d25201d1445c0b004003c854130000340350030030b49285200c01a1070398081c0306494180c40c5c03550340140740340007034440f2404001d20020310f1941c045902048220800d044a00b0250340541d60040d01b0340b61 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 748678651 1250 748677401 748677403
    0x13050f03120a0f030506060703050301260f0a0303060906150c03020c040c17070305160c0c0503010e0304180e030f09040902030106080708011514040b03070909081b060f18 75
    0x76070801c0c0490750049a040350040e08019940810300f010f5074204410350b251410043e50303000b96080a80000c0003800180030f80d00e642916400841c0e0840da28448510785c1d40280b625144c15101702000c3d03a04450802e908050301802502c01600310312600340946800c04100708441544900c6040820482d601e164080c10700070b21245441e907001400c14002041c45103405405121780d0350f030315108040914005500103100f441414040c3c246000a00d024605203881202c83c221020000e0b243e0b8000c200001a01e55800d1082e1060840407a01441e1201d14104003040080817244200403800d0a041e00482548004001c4502d0707503e01200305d60b191048400400d0084c20f88260007500340d0700e80038021031200c0000492104581c8490700912007004c460000c403550800621419840110010040c1000e14180c0c0140d132580502404480940d0b40c1c920306c80707043d91418001038411b2400060101031201d80441c250100ca90040010129030501c440b60302420400100301c161000d460543c01d1807400c0c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 748679901 1250 748678651 748678663
    0x7050f0f160b041503021c02040f14040e070e07021603060c0806060a08010b0d0b06070c170c0d11180705090a050114090112061d0f0a05010308040b0c0316060c0206090313050f03 78
    0x1f0b039000c000c544854682d804412166681d000c3c038800d004480c0b54441042c5424080c1d01d059003061000b82c2141464203105c00040071001e0541019401015841c82140d0444c1141100071800346a01003205090782c10701501c4428050000c2d80500000c00001c01540c1c0c121002c0ba044624112030310703980b02c0a050288000704000401103a00c00000500c0400780700340409244103030740303400b00191070386100d8190050b43d07416054034031604148210070800c003050002d55410340000c006801000c43c644d8000c0520341c8050119012004601c001c24840c2c41410070b01c085002801e0282040440110f4051209003e4051404020b0411409042e9900c8981140d004500245241c1d044841d03440300c6110243c141032004c03911525103800c8440000c00d41109801400e04132134104007a5441c0c5810001c031240e01d94015445011070b031104000e004003010558810701c0186009500c001110060707603200a0500c20040d100341d0441d030042c001c1074070704c640e40c1403444100d40e0700b1075058034080080004039040c02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 748681151 1250 748679901 748679947
    0x80418020d091203061e170109050601030c030317010b1903060302130906050a02120f09030c0d050904140c09130b09012402031e07050f0f160b04150302 67
    0x140c10602c581d4108001961400c01c0e250003034409000c20b50300c480748503800541503103c2c20071010b59410f0804c5088104e141c054041920603001040c0711080380c4405107050030a07031044440502d1003600f0414143e1000c81400178107440309a4501c40e502d86503040c00280548140702c0714080d140115032400034044c2d40b0a400443d8058020090305081c00107a200400594800341d0b001e034100030004866051780c0c803c442c3d822390b4204c44200180c07506c426449517821300500d400c12500c4204881c1c401520104100000390100e41c0e2120340d80d030700c1c0d0424401900c40405412051481c45014003281400440541d83d02c40c0d401d03101088054103550006025042e0303100c005801c41850320001c031780c81548a440380c08654850305d154443c55030007002241e41c2d21641d1501036401c0041d0f03031524011100c880007899681d0041c01103401200000540702e007000e1001150200a50000c6165032403180707010400310090454003c2582401e02d402c504d01400340701c18038a8004c150780025200f80005510b400d80c8902 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 748682401 1250 748681151 748681177
    0x140706050c1c0b0301060812030135010207290412170c0a23030105090a0e15040308070e0123160f0b0c040b1c0e0d1e0c08041802 57
    0x5000e4440a88010000c0f01080381c069401d040700410040e41c00603045c00381c04902000b142ca907070310b080110008082c40000da0321414202d4803501c81c1d190322006400c45108105e000059803422030786072031002171001149000000d03a040309055a48450000034075441074204802045000820208841c0410202403070308826811105000c48110410082d05041406440d64446100003503011030a80c96140c0c001260700c00c0400042c410b5051001165030404500e18000ca41c42a07204403044c140000403444261641c0e855003044145940a03d8040c0c000489090441520700d03140c4c0020444014006c0c682c00c01944800d420600c2840c2d40b08444410b0804003008a0400041c50040c0704003107102810368248444202040e402040c10089508450022a0f108d10700860240c1c148405401c600d014dd80565603281c40e18445074040c88000701808131a074070b0355009134401e6141e01c0362034403241520082003108426100001c80c100215401c4d100c0440e144402ca0400c40050700103485102000503070307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 748683651 1250 748682401 748682437
    0x3030504020f0612100803070b160903080c0c0a05060301060516050f0f0a1b0b0a2d090306051006020a081312031d0f03070909031202040b0c0607140706050c 69
    0x1c2080c002030130718000c0a5008000b081d1700c0c2c0d2134040320358034017410101600c05000c10f00420101d050400286540140e1030070f2110000d0360b02e84940c880d50b00a04540d0046400c0200030700e1840c6004082d0301d01410381101d06600f154108880203107940501212000080c2402e0005020700c801007003c40301c401c60000869904032000000c043e169440c3d1101190b15036440c940c070390b00c1c404104007080c040c1c0d5950090b050600b1201c8408640000c420350720840180360f030b81c00203500c6000d0101c02007020003403512140d42c450f00d14a4501e085840007031039502041c02d8800103100e015070100300c6180080e00903420315102c100b040050540c107501079108040d41040003108100701134000d000361005030009124600122070700710038090031009003a0003e44c1a001907600f400301c01070a6008140e00382c0645001400c1c0f081a4110100b04c0e0b00a400008801c200419108070b04c1008003d002e60084591030429210030003d150f00103140100c5400034401c940b91000280c07000444003d030740d0814030311074403510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 748684901 1250 748683651 748683667
    0x9042609040e0a350d091509120f051207030515010309020a030f0213020c1014060d080c031b1b2b02060d05040609051207020a03140106050618010f080108060403030504020f06 77
    0xb000b002c266401326424900160f01b900107c1903881041c107d950440850021080801021200340b0151100181484003d01c9182030300c0000b2042d0612401c0784d51000034450400d402143e0490b89460b110a040505151100c00181c40310241d80b0112a84800e80d80c8103080c861001400022004017030b031000901c0841c0406000f01e00040c8000b41c188064001c200040258854140038101120344c581c005d2a0281440009552036000b4a481000c8005803800e0040c2c401d20049015900c40d000c0711a80e21090f10b0301c9441d0380c1910000390b0300d0300403601d20b031204004151089040d1302090341c903031607210090107600c01d42d143c950072910039248a40703081000d403131716141c15001018101d205907104e00c241f01241252000f0a0100d86400c9c0d0010920341016241d0341e42d0100c000882a0710100355502e8070300c000790316100d18001d010190b141c440115101000d0b840014255840020403c04100e604001001424004603590350095007601d004211966603001042e07802000001d604c2c0c200c000021124 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 748686151 1250 748684901 748684927
    0x304050705090c09180c04050406030b180102270102011103010e0412050901021518060f07120603080d050714041205062409042609040e0a35 62
    0x4400d40700100d9159042e078a505403086000e00465841039002800a1003982001080c802c98079030107040c800405240a0321400818280c0300e4680c001c95600c1296030511a440310100d9007501c4489160008608003009050800c8890f59007240c0c589a40388040102d10103a4402e42028424400c000105030f52543d4401c940001030780e00722400c2c1e56801010b030800070503a100c0c0c0201c031510503050f801024007030329002e0350b01404000036008503015522440710036031180081c89080d03c07904840c030500304a0700d40a48003030140b42942c00020001c504d04401803000481c0b50007a00c1c030107e403040000850741d5a0b4041038520504140b05880696804200080c20103080c500c0d51000c0c40c4200299600d58444034421b0312020034400e101c02800c0c081c00c801c01d0f044c2c2006046c1c154840e001e0050507004400101c004110020717007030500c610960001030995003a0500740551410103d150006140030340d2141c681106000740855605500c4000b018406424020402685110440d03241c0300c95548c0c041007414 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 748687401 1250 748686151 748686163
    0xc130608010501030e1f020c0f010e010b1e0a030609080c0a0c14010311070f0305041d06010305060603090d0503100b0d06030506100806040803060d200a080708100917030405 76
    0x2e40041d00b0522850040c15000c1028050b15450101502000d91580b0390003001c0d4010004440442c4144032001015640034082c04014000441c00000d403413440c03c05010025a104401c1510440500c1c0000d80701c1c0c0703031300708040101c981000300014034008034079004081d80300e02101c140880c414914164207003d8a49003190480721100c4603416011114801542507130040070030040492024800c21003c50740c11890603909a02c43d2038141d10b400e0711961244030480c40e81d41186041e040c0344040001c40d5030140b04060304a1002c40d01c250031031070490810b42e83e038108131507440c0401a010010030810040810b104014041c0d120015440d1903d100d41c80c0020002c0344000e90301841602e0101f010f4440582c0440306035407494019202c00d58403522600320079803010b020b0b181c0001e0a918030b1790102c0c2c0b244402030003090742c24038200b000560103010403c4605480c3c11048007500451000c0144040c0040c080f02c180d41a00004612050389041c00316070f080000c0180c6140c0c3c0400001c01003041808540c4c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 748688651 1250 748687401 748687409
    0x34030f05101d100f02040302060406091d0f04021003110a02010207150e0a030f050f16020901140102100b0303040e04052817070f150c110609070b030c13060801 70
    0x4004800d00040d000102d000260010344580e00003201800303901d80e6641080205138101c0e030015241c590380364045070f60f96105505c004c0c0000c000c0c10081c4907100c09020344504051044418000b1401c106009046034040540024421070b00c05078a4100113029401401d081c610a40140361649503007680a4040c0d40000401ca5860000b4a0841200e100c2c910030342c050b8207607200c000d01d8045017580e02565244c5050744070b6800d21205000210307804041d0f8008044a40056001507221201841404108081a04171a24181c0e88070705044159900280419141034038490100e0b4002440001c03d00b140700c0c90b0402010300704a88108418080000303a00384c0c5412020341e8284030082d4001350301c502050305010061450b1404c00b02d0006440c0090b004c1d24050b0f0040d10101c00ea010b06984445051044160544820341c807980c030300c0d541903004403848400121707940241021380b80204405840b040c003801650500c07040800801d20044841060701d40e44000c810481012644410002d0581102446 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 748689901 1250 748688651 748688683
    0x60e120d020c0102060907080d1202040b03190f0614040b0a03150e12030402091810090605070212090a2702040807150c0b0109110f040f03020a050334030f05 69
    0x306d00240400514a0111510140038004078803007441d04507101201024aa4100b580900c00410980c1c25200214025042c0d250b03c484020801d0038800140c40100c409005031501c3c0203002c1103a1000300f620010b00600c1290000b4400510800003000c01c642030300081c11542c80d8400440c26070650364810030a040f500c0d002c50360301c150a0400405e141c4412070f0000d4015600a02150011030300c5070400c100c4010040940d080f4648000001084070403001007541e461b170f00c4100b405031b00d5406000d80361400c2030003241d003450402c4250119240c0b0f170700b512800f04040c8500b41d0241e41e04c0c05c003920384440394800700c405558a5a0f500c01080da0365009d80107a0301541c00c4440a0507416004402e2408525807205c4442c01580c41d01c0c494100802840713900090300d402c100411180c040b40d00c0018406000c1180250341e07480d007107005101078299140c100c1c40c0260b000e080400003e00c00c0101c4120030026028601805468004034009007002c50b520081007095424181d13000c018022810a2051007805 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 748691151 1250 748689901 748689913
    0xb0a090e040b04111c08071a13060b010504030302150619080607080604050708180705030d03020d0b03010e070b160212031806040f050105070c0f0b0307030b0415060e120d020c0102 79
    0x1c00c00890b42c10008170b1500010610000d0740000c0c100c040641a002e005608030000900044926000d9480c01c072800b000c50040003070742000b0000e641c810241e050200780780c00c3e8141420b43d80e0103940c0d408810681c2e50254680c10004007240d4070070301b15520104c2c40c03030404200c0c00c1c6c0e00ca100a5545400b0781e562004607240d800011000d052505c01c0a100324035075a224040390729a036000301240c14448040451074040e541c00490b59480400c94900010705e50364005990300c44c0383c2d140c03d0840d42c110181d580b2176410648800070100000802000b5921503045490390740408100004081041c1c1500940100500c0904201e55102102074009880c1d401d020a06104c04c41c0100f12580c82140911060700503000d8050049512810241c80c44500c16482401241c2c2c40d02d80c085a14070f04c550040c0c3d0341c1d004c008100407075542d050180950100c03040c0c400b4070104220f000158880310081c007800c0300700050300b08004155034078608070b90600c40b500c9045e40c2c0c8402039100020344407903035901039a015110700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 748692401 1250 748691151 748691183
    0x18050601080a0b04060506030a1e1103060106090b181809010515130b0d06050f06010210020c03401403071203030213080d0801060f0e0108010b0a090e040b04 69
    0x2060501489038000b03803d00191341c032030751078000905000e0000b0750588100b0781c42c080055041401c181c8072042c01c03808203502a1080c98104200e80a07e000607009800c4400100b018541210440043d13030741c40b2114548980410503007054151200305800d40c0300401344c0d50002205184401c0714092020310009020503640d00c85425142d1448a200e170750000159025101568515801119601001080c440003648140c49880650b0b0f4103481140e079a007010002c1c040c02c0e41c3c040200901c1d84040b40f0b029400e150000040a13200d001d03c6e58204c0c1d0500c00904482e0648070180d10304401c02e11211444062030b0800c0c984174546003114080c51083c0c5040055424107450300007682c004990320960391440b001050b5504801035000303010a450440e1441c640800c1200051109482c038681e80d544181103580b400f20010a441c8104c503555050090202d41191142da1281c000c90545008034074030340d50340300401800c968a040c651304c0303a5041c0300c0b41010701c4200209085264051030184c02c002000c9804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 748693651 1250 748692401 748692403
    0x1103090402030619121e0203070911040e040b0f010608131e0f0b1501090b0304020d0206120117100204060e09091011031006030608071a0909090c21030f0c07091805060108 75
    0x30700b800039506078801c820800c000a866040088029504005207040c650b41d24a0f0f81cdc04880240c2e011503074203044408006d01c04416409060040025103011949410840442da50446582d84050501506000240c041500441d012143d155101c103000d20940c100e4240115450402d44500803940b404008480b032039031003140d500042d9122600d181c1c3c991f84a81d401c1109001042d0004c030f070440360505c070841c1d4030500d24440b01c0c0240170f0040f6400300160b02d03070320450a0111028000c0802071051000b0722001744d100d1a0300e0100c00e4146c0c2d01c044580c0307614900702d142c04c0d00c0d4503440112509144034410b00801c0b840145010b03148240d003468500d03848a4080d01515100c0c001c1000c0c99000280401030710b003c0402c260043c4001904951800c102c51002c9080510f08440700b1031954041c2001e01918100f40e440340c805142071004000541c0c08007440710b5164440da404020414074003240c0b0b6100120240105c40003441540c100b044041600b40d5102501c04a24400741c0703c0d0700076800000740c07841c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 748694901 1250 748693651 748693703
    0x10f020c13050603010e030f2101180905010b09010f050306060a1a0313050d0503040b13030504051003020c0d0e0a090c05040b0a050d0603150c110309040203061912 72
    0x10007840080541d1035414400010400201103035071540d25150390031002401403001313140094004102d03540d1100030a004140716501d0f880308203251005000104401180c4103012050441811300120301307403107182050b07800360030070300c0006a00162141c00080c9181840d0790120845400f5002e86c3c0342540c5da1010001c015282c0c1c410088a60300f1a1813041c0307d01c4580d00190750002d03901042c2d0714401999100c2d9881c0016101d008008500e00200788424448038860b66580f10102d004107441200d05541c1c002c055028510645001c2d00102c3d1072009c0c42406034043d1158045481c04445100c86401002815889601060f5002c2c80b8200c5010640720400d0142284418035610749518103071410132110003540c01840c03c0740800009200b48403942d41c60380244002107029071640c0c010f0300303010400700701215403951511003840381400320742000d03d070048281c2c0d000d054225030058890b500d94010410302510114501d800402140340807444148009140c01034034043e841806607010303080740c1c421541c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 748696151 1250 748694901 748694923
    0x30605090f061512040b010e0a1b05090109170a120503070e0114040801020c0a050f0a020a0323060406021c0e030706050403020712030203090f090f010311210c010f02 73
    0x103103207075001841c02c2c10215600e84400f80c0101c601481d000b00803e203540b034030f0300550b801c0351008051381c010016104d0000f031050308040308000400c00c9130704894a0450031440c00c040642030003c040b5020350280e000d1440341c0c0c020304529205981c0b408091071800d4840c01142400c6564440d0032100243c2140718a040d20302c03d1256854015501207820019a45801c540300c51f107007418020130001c00d803484280003900c0890001c40003440744c112580340541c100014403610302c1807540300d400c1001c050713505c9103480c03400c071783d04003520781c0002a10a260b0102c08160b40c200140c140300b01020f10003040055402058040c41c0e10008035201d02118a02c002510200b605060044d40103020071400302c0d0050307101030f81142c402c0c012a04010b59030030140101740a0264141c0260704042160310450405802030000035100301d510300051310b0040d02000e003070350046c040500b240361606c48150454032490741a1070303100c1071845003c26410080050359036440380310305642d000500300c42144501030f000080d003103009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 748697401 1250 748696151 748696171
    0x5100c030603080a0509150403050114070203130509180a080403030801051e011d040e031201090e0a03111609061e21020a0e09030705060708010b09090c120f0703060509 74
    0x21903203039011142c40e0001d2807003e922880d43c44400d00407d500300e000f03100640c8142e0020a95000510082261840050191040d90801c00c9114245021691000d0030f54504a45100598441880720030780d0011801d400d4806105840082e400d000030840640300f00c0348070755104007440e03803140f09001c0e1260020191180c0d2101d02d81c0304000c6d543c000c83c0402824000300c20050742444401e400541500c20354001e0016940001072151003000e00707051801e0240007010703001d02201d8100c010b00ca5841030880006801c101d08550300080440b002c2c804400c042c5d98518a51900c0d640b1100290010802c0388128000d645249003550050800380107075000302e40038980052080c00000c00e5402c10440c1c007000c102d07031004208001083c50310211480700e00030201840119240d00c1c0900d05a860000007170040402d000019004001d5805d14108680e0030315030503604100e0a4940941d40c1c0383c10301a90451083d104607020400000074101d209061056130280e6003844410741e21014081445003d80d411609 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 748698651 1250 748697401 748697407
    0x4170d18090207060905100b0310020702030a080a0908073f02041e020301090203040b1f1511030a0c0c0b090a090c0c080708070302060726060a1205100c03060308 71
    0x310242580070342401c84c0102c90100d141d1050380d488906111140700c90352420395403004501164107080110391000498030344114a410001e400203582d491140000504842c000204000313043d21541e29030004144401c111407519031104041c841c640400000440a4030006d20141c50340050b0000c00038250320314140b800703890700d2250244030107000c00c0f54892491141c0401c0741c0600083e1403004500030311840b400161242000e1500c030400903c0a02420909258160340303d00c1c01d40c1c21000701085130082ca8804040e140850300c1a920340c840503511080c0c0d80004100002c2c900d81102c80303400c040340304155006103581c50780031801c807a004134850107800040317642c0c3c140000c0400ea841034058414906003081030019903520106a54405581150074503004199201010f0301040301a420084600b002e50880c00d804c904440c0014140103c1401d00250601103000c0c0d84803030a01401030107400b14010303203011803818042c0e65000042c1089150385d2605a9040c6120b02c60310031036064961203042946 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 748699901 1250 748698651 748698659
    0x303050906070903032f030423040606020303070309030903021203191b02010e0d02090c040312021b01030b01090503061602060a0209060a0810120f0302010e010b0901091d0304170d18 80
    0x6c00c40c000011a540318880c41c0300b040c1100f00c0300300040c000a01458140a00c0f5244e0700111a500c00164090759008504203141400201c0d000300603664040c9062a001408000354142240d020150784d002940143c407502620018010100007085121b8025460044c20110510b048803940d020510034102040384080c160010b6120340d0085507445c0e07006060200302100794001030281503007610504a41900041d0400c104820911501100c0003240050711824104c0318001c1c085610b1314240710304059440ca00c1c5691a03000300c2901c40074000182c00c030b407007615000350044004c030826070b440710240c031030000002c0030f80601d03008407013030300b040940528205400400192022000030f000c550008548410104544d281030144000150051000350001c0c42203090180c2144c6200c2d04a01c240c1c0d05040d406003a42c0c031035014441c11114152800560f0002206e0089070070556400503811074000000c00052002c50a86445e00084200082e079040403d407140236a040c0002212650b00a581072800300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 748701151 1250 748699901 748699937
    0x8091b0d050a060c110f060603033405031b070b2d0307020718051509060307320a0303021506130c11010f060b070f0618030305090607090303 62
    0x3035929071060044034045150b582e5104103882c094060700b800107150101d400710b83c0c04100000c1000041d40300241805040c1800400d45a20a9064803070002000c036580d1110903055030390f942160360300c40071031400f18412840e080b0707140da010f40c0b04000c440c991f9110101c9c0c0303001c000c0751034001c032080d9500c40c40c540340c4400440003440441044804c1d40384040c0c035010420600c11b0780218881c03402c99015261190070189869142c44d0089000c800c8a480e01b0100885d034500e00a20b840c2094003110102c00a98503000000e2809145400c5004040741400c0800001c07103100c0e00c1007080380340400c84c00701a800d01100740a2030707920341e1001600582c0412000d000440c0084c2d4201c1c3c020340b000d000d005056080003412410740f1025507141c000100104901041c040c020f1140fa821905c030f5080501c441361a00441500071f001e821005411001d0749068041000b4840c0d10810240003403898507444906603040140c01441c04640f07091660040c03c0025407000e110b801e881d0240d913495261260f8094503590340c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 748702401 1250 748701151 748701169
    0x240d172b1401120c261203130311011118030106080a05030a030b0103060506030408120705040506120916120b07170f0612340e011215090609020108091b 67
    0x903200704804541c0030802d036080040b9480c100d0000001d142c0d104010203240c2c6e161000d0300346010b4002c0018030034095025981c0d520780b10050f4152918400041c02400c2c4103004152600c0c000002c1000060310f8030b2407054101c0300d185400c1084000304150341e61480020703200c00f040800100250810400000d0b29401f0754428140c808040c0b400044031601c0d01c004c914180d2041d43c041d00d4020010607142902e096800120f46d0004d021324125090a2030800410041c4c0151000d06801c14200400038102104c100b04125545800320300f00491140d0300c4640504140f030780c0c4001d558a0900d41c00107000c0b98021018804180c050145000300c55440c18091050703848050041030340300d50304a400181410f030070044d02102c801d400c52950240c8148126101803024000e910040c2c4a21160080012049034002c443c1120b104541d1a400183c06140080e130041800507050303600c03481c1202280c00d0080350350040030594402e03240d0b00d101e41c54140c2d0040e0f43d15440c450320103c10710308074805c0d0400e08203101d070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 748703651 1250 748702401 748702403
    0x30309030f0309070b03010e0f090703030504300606061202092d040510090b240f0706141009020711120f010608060f240d172b140112 59
    0x43d10b5034161145d040164550003a48604440312484040c0b05100006070402c0d0781020410340144222440c542c2c0107000c5009520802610492076650710f2040001c812a8121200d41d1240036180ca2417107103080801002d0070300451700010b0b01190400c2d0502d100d84211070324041c005161400d10061804500511006035035003490303595003d009030035907895034091903014850180d4244e174034034142a1804112103080d4090b912900184551181c180c0034202c180c01d070310b8030700c680e034590b00e21502d880c01c5828480c048008240518180740c542e40542d0f0b14001501400070304900c443c281c0e1351040c2d000141d00440310040d1440070917004148151a100b040206c000c2034040c160b900c4e02c50200945400c488980e8840300c81c60300a0401c02010364003950045074480c080409000c0c507140c1c220030044010f08020741c0300d40140d0f141c103110401d000180b600390b08003c285946c810794540c1e407803141c080da0107041802c04003600310302d494105810546004260355928a0303500d50352240c0c40c200b040380c504885400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 748704901 1250 748703651 748703653
    0x11250924150c151410030f020904050a05060702100f0615082a04030c1212110a080706021903060605070206070204060305120c0c0105030112020910170708010e030309030f0309 77
    0x108840003c0e50350042004900030f080320000c0c0404281d40050001ca00040115070594144c1400707000040190020710355242e01951559420b98030380c5059490002100002b401a00c60a01005074442c0d00152129001e0f80444e0184203021001d03c640c01a1000c0c0e000da002041200c0444c6000d1030f04ca12040d603800f000300d480076a1240c42c0446081c00f44110103a901d2148840010207000380000009504001c1001088942c0540c04540340c24070700001c40004007040000d801001042240204040d020b01600701d032459a030740744107140a41c000e40c40f9450041d000d94042a504021a01a02c101c0048501a484840c81c0c801a0360801c405a800064101c0c2d00540d21040800070a104010000c9200f801094980e91800c0381014a4900307604031840c00e0410030200018801c0c5e0341c44541044005038159140c0641d5214a00403a208902641120b602c00040814505041c034000480c1b60860f00b11200030000c841075500c03015141d2204850545507648104008400e041041c0020b50303000c10070070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 748706151 1250 748704901 748704917
    0xb0d11130b1011010605090f062e0f1d030706050a021f0501050102063303010b040c2003041d0702070810140609161125092415 56
    0xc400a0b10419900a2010000c0d50084402c0400d25007446250040c020403601c02210703103001c01411010311401000d050060003040000408100c1b40c0f100c0540c880103005104400d000c103494014224804d030761064000a180d80300c90178500c1c80740c400c6109142d174050040d00700f486c01e01809039030652104035400118840c041c100d504519002075042410340719081c000c1065403502c4002032070140060103815901d110304401c0100c08144060300e09140c10f007542002d80a40398480040e005204800c80e0982003800c00003840741c0140c3c0715241100000c00a50042c00c1c5040c0c00c0ca4440e902d000350b003c0e141c0b1091000c0500020780c2c00b10400107a000b504c40c4100c0b8440d80e1a12030050030401c08454012180e03840c1c0c0c1d601c1c0300140015104a5000c4016107000215150205400b038003041d1544501050021a1100d08201d08060122005040c19a041042e42c20411a4175041d1119180701e444d44991505040b810f14041c40c800780c40000d82d140c0704811910b41440c00d04545c0103100ba0014050200314 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 748707401 1250 748706151 748706171
    0x82403070b0301080f0d1416060621020a090b01021506190305210a120903030f0905030306040e0d02150606120a0506040605010e10050714010516030b0d1113 69
    0x20740000d40c040c00d007040182800c00c40485450703190142585184042c030400100c1ea0021b01c4c5800180c802405e07004608245007455800c102006110316002007061184000b07500740d01180d0750540600b80345c4240c407100007256440e000e480c212100c4519060040e00184810100c08003d48041600030800404840c1034245000c50800103440d50360003140d240d000300414014092011640e41c0c00d40043c00c191600c2c00d1030850000300042c540d19207121040340d4070801102030600c217500a101d002022101000440403900700750f07949410032070b401ca00c00ea00700341402e2130a4801003802d4a4101058005000d1042079200f141e402140c01032203d90402c1c010700248014629900541d8003401d120900068103043c048284000e40f0b07c0c1c0e401242c18001c87d0751100001e526014940581410700f40790041c0c55040a00c0c0080c88600d40340075104603903003040284025407092940030200582961000c019107a021400d01c41441e0503140003504400c00f400400034542850f90a00320440091707600010301e0044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 748708651 1250 748707401 748707419
    0xa0905091e180106140904201009031e0f08030903130f260d05090f040903020601230105090f0d060603031110061a0c160e0f010608240307 61
    0x108480c040700b14490407056101000c000c0c880c20001d01038920414003100c003180f01040b6080d41c0903100070300700280406039030042c205426401c50303400c40041000000d04420440200720003101d01041c0d46091840d0044504104e04070076000c00d10303602030914842242c040d241c2d800c1c0358200074030301c5006000070810354040241000040c4007510140c055000c4043c144144140c1152084000040000808002d04286000041e1842c04443c0a142040d600c170400b00229000120380340c456900641044518010980c0101d0000e042c1c41468004a402002d50280c1c540280c041c0c8005a0100c0c4040020180d6401c1000c46804554400b40503c58920081c2da01e0302c0c111810366105800040c5580200204040140308030900b4501c51003040c401c642c14000502c0f44031b0011840000903a800181c80c07049900288044003d01c407590b200160095902c070311103841510121001000650008000b1030700034040e11850740224400e495440c80815825003e001103030421a4283d45446415400111586 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 748709901 1250 748708651 748708711
    0x5130801020301031a041a06031203090c0f010c0b01060309020103020702130b1504061d0a0b0a030b0f090f1314190c0542030a0912050a090509 63
    0x610000040c0c2e25031450400c921090010241c0d00c80c0c8421500078040130502d0021400c0c50320f05070310b0610b50740da01d510b00001d14080c5c81c601030b00d02c060b5002c1f0030040000000308840d102c032001a500c000701181c070300340116007030700e80d28100800f00c20f03598006000e26882948204507043c130604005140c0407540c0c0008019801452000c17641c107888070150007241c10141d8240700241310000010781041c5c20b0420241440c0c10b01a0717500c0441300009200c4c01c0765540d80d05504001c00c00740301050354803421003400030302a0001c461124007400c0100c0d040d11243c104000c8291054a40d00000d1203e616003c080c12000590a2000e8072248948080c10800d00000d02c100d4811030000c1002942519440c0f401209014003580704e07612980f10b11240d01c4406009600c0ca14010b0b601c03100345149000c1c03071004052842603688102460107400b00c10440c2c0d04001d0380c800c0d402117004080d010050b41c03140c0822181032080007000c00002d80c02c0503040006081410f4aa0380260650342c4c0000e5008054104802600d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 748711151 1250 748709901 748709909
    0x70f120e0f100e190f060207050601061e0801121110020d270506030a06090c09170607022503021c0b0a0605011407030201230712020309070302100513 66
    0x2810441e03000c05200c0003003005a8120509034020b0110f040101042511015400011610701c204d0240e410300308210f005e940340456900c00800c5444a00f81d08040f03680b0300c8240640c2021070412070071800c107071840388007014421503aa0303180095a801c0030302c0a0791407072000d102207e0032404240070030382c1035480c4039001c03810b05491350041c91002c0300140014603c070866204003101c0c0309010a500341442d605035559042d50801d0307503c3c81d13482d1940e00050006142e260700103480f45161039001009035911070b6440303084440c404060841c07500f000c1540d0b9248d04081d11601f02690094000c0680708002c80040790282901031980c1e50151360300c2c0c010445011100e0a8070f251800b01006400400c045108a10340003a0040c0080280300e090200180c82aa0b48a01c00f213404540800e2003000c06200750840050070304410383d150042d403081d04449003400d40540d41d100c08592803c04500701003040b4406c0d039104611200003012001d14540a00144c0c0c2481304048007044020414802e02a800c40180303c020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 748712401 1250 748711151 748711153
    0xd11120f0c0f03060f130b0408031504021206460f081513050a14010b03150f0a0212040f031b0305030a0e0f1510061106070f120e 57
    0x19000e440c0469007400708580805208089450030020b05407030001e83e581d48a92203007240d0540707480c0c101c51160540c0161000414000c040000c00080010302409140510b20000034442d043c8400b01c01c020903801110b10600300c1013031110021b61079142100820600c070700000081d00c000c0c0602004c540040d5440c00a4980350003260407010300e21030780c83c1d000310000c00810040ca10303101d0502082c1501d03242c1c4140804400302c24a000314094616007010340d804290300c101118004842490b00180010801d0000181540b03000480101801c012404031046a00005501c015607995188049943c00142c144c5260781c1d130a11004035003c7d12040703902e000764010400d4003105044c500c4d00924240360000b09581d04200b0326618000207412a003a21340041c28504003040d40c010a030a024035254089540b45064416404941140b1b003c1e0402d07136001d000454907500c8910b4a50109545110803180c4c8514180c0c04400003030001d9204e001c4c6030010500520386118a80f038210380c284181c030f4264441441c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 748713651 1250 748712401 748712413
    0xd06050103020a08030705071a0405040c0c15052e0504090c1a090907030e0c040c09140604350a0c0e07081009020d1e021c0e0a020d1112 60
    0x354506550f222000302000c000942c07030441d4035540c3c0b40c0c40d10b042d2711841c4440300040a006030500300500554000c0c0601820400c880c02c83c0200c020650f0900c1001550003c0050b04003084c2082c60380a290301c56204021700c4490801d08a000c00c141c1c0b0390301ca030004245020b08034041103a9840340105401e184c0500306034207401d8246420300341c842003840640070685000300300d0003c060700c95651075070307200c900d505001a42030074800b22181400f4000c0d00080e4428036190707141a6031608041048180c0da45000340a640541d8070050011610603406200c111001416130010b80340d101d608906844001d0340d0f4406180703440d24120511f0055204411034402c60b00c520240141612a156a0b03402842c500e404c5035a0f08140b041c5030500c0e82d19002d0748000d9600081c5000c1e20003c0c5801c01e40118140c1c1040100e940103694458000f50407644080b8040c0c400c070f038800d21000e499400303001c2100c1c0c0300c0c00103016003540b07aa003005010955010b048035024035000070a0543d9031520904075010180c03030f001d080307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 748714901 1250 748713651 748713653
    0x140d060204080d1106060f060306130608060109180506010b220308030f0a09120f09050307080c0406270207170a0c0201090b0a17070302130f080d030b061905090d06050103 75
    0xb11180d02d000d130b101400d0703101000b04501c5036194480700a5408065880907a2a2200004030322200d04001000c060507081c0000054804000030344a4120740003140100801031030f6011848211843c600041c0084c0c1c004401406140000c0000b0045401e2810003140740c242851803191500c003059100391107281c004020003070a084252070866224002000400029203950b4a40d0b0460004081d032404202e528009002c9460013410903501602c00101140c0100c1c1e9142034133607440c80c01506641c001c034203000c00092440040410340168010398078122941010b04000327407000f5001005e040c1d1364403c9010310041c40501c62002014141a18dc0d5002030888944c0009401c58081e60b0014401c04810400764549543c40180d008030112640d07000381071520354110840280c010440454020741c001e140018030069140b0200003201e04140582d071032036101500035400c40d0071513910f8680061013000840320400084000c540c6150490400710305101941c40450602c4800d02000c5911710781d1640148 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 748716151 1250 748714901 748714907
    0x5130f1505102904050d080705011b0207060e15030f04021212070b0916290304030504030201110a060f020d1b020304120c0b0a1205160801140d060204080d 68
    0x159009a0b1000411455803034518001414044060380d0401d0301442040742601d814a002100c00400c070040030a00500082d041c110322a61010760101da8541ca0000306090402008260a4600340d0640140c54040e2a01d00280c500b424410403913603000004410030818240001c0141d40140032000c0d825200d03150920500110002c14014184540d001192525204d008542202c006030340c80010650341c0d0701d449810f00e01d0304603d5608a21050039049001c181c024044401d0703042071751448180c0314020b046d00c1105a0601c0b040d038004d40080e030200420b00144d401245d81816440100c001c8407003440040c1c8501c01191141000043d8941e00041d98a525003840e010b807018400381c600c51010500410400030b962441340c0c0c41031004070180c0300b5802e010f00c003801144600800e2400ba07030070340d00c2210002c020300c01a0105241e147c3c0f1490440415100301d254101c4002c445065210306555034241405520501032080c41154003041e801002c50024180740050001030810500038600c003442c0c50805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 748717401 1250 748716151 748716161
    0x30e0a2307081e10050c09010e0a0f08010b130605060702150910021b01080c071101050c0a110406061e0315031b05010201060e0f01030b070c1b060f030c050d05130f15 73
    0x1240c01030f0130320042c426402c5002e4100d49440c442403c007445840e0700d076800f150600360184d1040402f04450400000c9000f030641020b40006400c9640d031445c04098014401103540300c2c0520f0b07411500a00003800141070600454099034860400e450a15807880c0001d0b40c1d060740400340e1801608514600490900540c8641c1c5003103000342030400c0c1514291301d1103c018080d801c1e01908110342d081c0f82e016246d0160045606680e042810349510014a00745540904041d4882c1e6009034502200040d0b100e105400044840030611b500081890703080108030701030001e103600c01740f4040300d0423800000600c0c1d402040d0b00d40040d00d4100310b034070b43ca400006800c40d256940440b08403a074203030801411400984206e815250b0041c04107000e900c0e072480c2100e4291440c1380080000c1000d800421070042010505000c88807186d071280e03400d0005410440944110811000101e4028800c890000b00d940d000140d001100c00081d42032800f15445d6501c01c0b04a40b20269190816118444140e85080c084c0e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 748718651 1250 748717401 748717423
    0xa110f1e0d060605041d3a11030304080c0607080402100305180a0303141612020703030209151201081c0819020f1e0a0e1c170901030e0a2307081e 64
    0x4203140d264034800412000d0000c3d50022240070a240f00122507e50140f0360b5100d0001c2100c0441e51a8070302454981c81560104022043da0300c9418001811030f440f07008024811940070341354070220011514241c01600015151b0700034064945c4c000c0300241f10030040444054000e69010078000e1224541c60003940c800303001141009035800c03107400000d0304810080d0850b28100001a6104040d0038201c000b07014580c0c115034010400d9565400b40182c0902038030140d0b582100c01c070500e90381c4220490b82c0d14851102c2d03080f0701d0301101d0000115405991866400f05c0401d040c0322840e103e40700302c0e4081340e001c80701040c1740480100311310b021317405100414501361440d00541840c104c3c45000240400c1843c1c2507062241d011540b0300c0041c0b5003071082c085000d9900400029130398000e800003211640100c5e8038180000e00e003032142080e05400080c17800109800010001400448030581110a0000825015244545013001a000740b00300041d1194014050350071811460010b4920305100e0303802e031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 748719901 1250 748718651 748718683
    0x31509081809010915030201051b0a1103060a0515040b0a1203091d0709091a120303090c04021c0207021f080105090601110607050a0c050a110f1e0d060605041d 70
    0x20100d10815140e0456016a902403c2c255101c4c811420310440c02c2b0303040341d4250800e0180e8151001001159010311506110413404d481003962200c9046045a400f140e2240781004100c22601144c00c282d0300140d481d0b0b001402020380240c8819010102041014044000586a400422061504203a041e0320000e00c503038006100c0c100094001d003002c0b224014a00ca20790b50703181450743c81c1c0e031070000210602c0000d4030425035441015061612a00201c0701620b441c02800d1800b1458038042c03003241e0719010740300d058410840c0c003416800001c4d0460700049800c500e40460104404d03812040481c2c065019683d174010f25030510f0140480190090a80c80c14000d4101215129040100b543c03540520075140503515803021030030869003000305020240080c02116940b10a0000410a01e00000c40644001d8000c00d030940c00d004040102d107003070040c4d4001d9070450010519180d250300001a0084001140c255101c8000600f21048040004032075102400702c00b8a00a062002e0050918000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 748721151 1250 748719901 748719911
    0x501020d211407021f02040810090204090b01030506040c050d051c05210a0b0102030408060f0c04030b070e04052a092103070c0e07090315090818090109 67
    0x400c000e01403228030640c01ea09200880e600054081150b0b01018281c080c21050309103a0520600180d21084404030710b480000d01c01d582080b241e1818000c48040325103c000608020a0200802c801030600d81e00499001d519a210200890030070b120f00f80c003a5004002034491410300d481c100454100039072120b4012034400101d10081074010134081060300d6456000c1003400750744401240c4c18490480001d0303100c4003001da0701e01814134150740640305090700380e0204003900c1d00b0001643d503402144550071b03503a405040001c3c481c0c9501305015810090104480341003d8596030b4211805904803840000961030190410085c50f1601425400507840251a82540c03465100b000744144960301d00716940b8400240011203031038800e4030004d454048405003000b1881c07620b00a44a81c001c000a543c499004803000c240c00c60410144c0f4050312842e01c130501c01c2480c6070f07207100c0e2000380b68488090560742c407144c4101003a21440249141d44804400781c080c80307404020410b1070001030b041440342d60702d42 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 748722401 1250 748721151 748721173
    0x213082b03060506180a090203070f030b03070b03180111040306090210031a0f12030a090509070f09181e020405012303070503061c0305120f0709150c0503030408040f050102 76
    0x50100c99000c001c07150001450169030000c01e1b0001060360041072000d00c00010402116070000c1c0d071001c2e44030326a85c144141500c40c0201070382c40b0003d01034034081083c00c0002c03c80408038002c18000444244001191030040340c02c1118a54000f9401a0b0741c10361200c40e40c45c114640f06c8148042c0d42c419050402488010b610303140c126514103141140034108034400001304e582c0301409116003002003c201c0b0b54900c1d03060702c010440d00c6980b1806024411003000b29410a010350042c55600c8030a43d615020740d4a0300400d0100c0064041d01f20101d44d03940e035054004182d20f001c00101c0344882d4407015a4031403406000620a511100c0f050f40c0c82c070768520610720700e0f103140e804598001d2003600c0c00716107079118440060600396082c0740e091104200c0101d40e0302010341140203032507a00000e2050107180d40c3e5035014581500c601f05d0700007000401c1005c05000090f000b104041c001403c0703103803074542140c09541e40e030718503401590142c45844012404100741c0c1d41c1d802c4000094282032025102080301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 748723651 1250 748722401 748722409
    0x9060f05090a060b0105040b03090d090b12060f0105071a07120e0a0f110d05060718031a1b040b07020307140105040905060d120f0e1f030213082b030605 67
    0xb2000010300c2c0c0340e00d8255852840e81310700e00341c4000c0c002c0c56200039540c0c101241080d59911202903604040340e001700000540c0350848060340c0030241020200055690303210100580c05020b007001c541072040511240c000710300001d0100c9040180707070f4100103260070300030300c0640350a5140c44e0106034a414901249040a4082005000198410300344600d511a5103000c180041001c0000c1d500003c501550f802406030014405000f82c10945031141c10062041900503507200e10300003c5d000080146503982d04100f0540c0940d80804190625180d524009100000c0c55000703030b0240100c10703000700c0d5980540c81d050262030010300640b0701c903500380d894410018180c4c0c0618402c02500c25912000074015464040c1c0e040303800c540c8800c220503810700301c520185c0900d5900c806c0f500040d0701c402450300719081c001013448480d11a40c11000307030200c1c401d40841c040d5020030500342c840d43e16007d0000f8115800c02c541c3c112041c003070b81d00200c1ea04001c940c4518000c007140e0a4020181814420045612 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 748724901 1250 748723651 748723663
    0x90f060c040b12060d06150303030606050712110f06011401080105030303150d030507170d140408190302090907020a15020a0c0f020d02210c01020106030809011107030f03020109060f0509 82
    0xd04540c20109644c0e40034001130405100b660080c1c11541041400300d6081381510700c22082d0303840b0782c42c03c0055903101c0a04071064020803100802c40c00440f001c445400d03005103406a00d45ea5118115084443c40301e039a1801e150007030340440d0741d005414402e50030070b41e00081c11743d0152500343c00450951804c811100300c50000041c00500401d000d07421542418800d6041b80c03529504050380424801c10556000d40c3c680c85a000718000c6468901703510601c030f80408441d0b0280c3e8100002d1414100d01100c2383c11001401000e08050540c2040301008980740e28038041d10400c4c9030b40140c91a000103090264880c0781d80051500703c0361040022081c01500310701e10f544903e4002000d0740405009201096010460900c040e5103c40301c0f1404100c6441200b421a440d81071030415143c0080c51500160300782d4802e0300000700310200030b0081e00c03900e5209458000d080181c44045492050f601d031104080300b803c0500980040c0d45a0851a0600145010b0301c00441c1c407122041005203000c0840c2501d440c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 748726151 1250 748724901 748724917
    0xf020304200111060103080910020102160204050a02040302040e0105090d022a0402121302030d0c200a1802030a15050d0b04050c03070b0408071d010e060d0803090f060c040b 76
    0x401251180c0380e181d01c01d103c1d1081c41d100300301c200c0c4d04035610784c203102081d80c00c000700346071042103128500c50743d03980f042c029a00b00e0034904c107810441c4e00b410b500704400b80c48004c2c2880d805541c28403001001da41ca40c0203070004c00d07081c4400004e240c00d0054801e402d02c80809106003d56108609640181d800d5020780010062a090040020340c0400c000502a1041c0d41e041d21440c10314409022401c0c0d801c1d0615111148200c04642e149402d4400585240c255400b01420b80c0b481440c2c9207070003030f00800030590071840051600f140d017612880c00c6202079000c610880d200b6175000c401c0200203006807007000b882c1c08040d5500754030740f407070800094001c10500d00d0042081c9448070116007045400c0028500351b083c02000d40c1c0148ae00d07812104495045403280f1012441a0b920000f010740c0404100001e0700392440900c0a983e0034031a214a0220000d4500b03a000340c0704440300c20205014102a5011b001007902030b14036644241207551425038094441910b4150800c0100312030004a0102c4c0c2d80300d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 748727401 1250 748726151 748726193
    0x3f10060305061c0318081c050c010b030a050d080f041226130c33091d01090c0915031805060406092001050f03090a0c09020406030f020304 61
    0x15030b141c101180c0009560501d01c03403103061034507103c0b04150b0041c5503030014100c1414007070000769441e413009075905080003000302d00d80b500c00360344c22090380300300010704540b821030300041040054040400e203042c0d05084141c0b425000502c407580ea003544205203640102030201c140c00f9a042030f80319910720000030200b40d81442903515503401c00d884481c2050652039030010b101c503050701c0e01c80304d00304c0b1580d241b0300101e502860160000c0381e400c1020b140790300107803810a140858040580740e090603c0340000c100f4418442c0240c0c000440c1400a01d001ea00300b0b07041c2c41c292040f545011507050a40d00c00055920901c00580b6060005010210203407840311140c0c500890424503880d90070480209410300580300380101010003043c40619040f520880e0700c00c00b000609801e400740c06c15180c5e0300864081d03000070420040f0100711070482c406103400940c080e090307403104181a620f42001b14103551005018640218080101c40e4240c4a50380303485140c80d405600d9440c042d5240d02c0d030003e04424090321 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 748728651 1250 748727401 748727411
    0x20f040b161703220b060f0a0f0f0f05030d0e19030807120f020f03070305030c09030a0c032d02060a0306030b190c09030201050d113f100603 62
    0x510702001101c450351504044001d440c90240030b007a0707810307500845140c18060b41c1c540240302d42d4000d40d460902c0c0700741c00c0007400c510382d2112001c000e40d00e908146480d602c00c01041c00850b00502d0440b21100130961425030310354452814140b40001d154992059119030401e101c5141c0c00c98000c510754081e5201142c81d1404a0284400380c0c11074107c40c1c1014001c0c4034085207820403c50600b8902000855548440b803080110860483c0d80302852058100c06810500c00d0000003030140c0e028640040003010010304000c0d03c0e201081c6498010102643e131107400e40300810034403901503a4142608200b0b5000f080101840c48113000030b5450b890004d00070f070800241110002d209038403010265a2004005070582080c5007000401252216a61092464840b421017424001c1e101201102d506031950b50034800034844200042c07118560035201018100811306030419070a050654aa0a110090351940c0c0f50250518903610802651605503400f0401d01c0355200d0f03c2d00ca100d04940a034500898 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 748729901 1250 748728651 748728667
    0x504030806010e120f060604110c030d0b01051b0c01030f0b01021207050114071e090513020d0608060903070b0105030607021e12030c070204051b0a0c020f0a0305010b010f03020f040b 80
    0x1360700340e240030003800c5014122000154100c003140c5240038001c00c43e014800c16605981824051003045981c15003980100b16004204d5000d40180720f10a00506050341010308950062169010307901b200c510642100b4400091583c061185101403c00c1c80404c2004004e4180040d40daa0100d0303d5181403840046042001c000003500100080240020300020038100f100c2e02400340d403070102502291800c2c0503850080b8501ca11001d40c01c130b42c4000c2c4611802103100803060700951202410040003501c4000101d0659410880a0b016002c1c51004541e10300c41030824650100068200c81d100b40c00c0b41d01131200490f8000b58510310110504510592030580c08941071400048244d50207040e1808020040e904109071301428501c4d0007500c0c01c3c86650380d400c200700a5258100040c0811003414007135040040d00c24003803641003a1018101400811001c000500814656070040740d05a4444041c0085541d10003448466000f05003000d41c03c0c546546c4540c00d290181b40907016282c100071132420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 748731151 1250 748729901 748729909
    0x7031b0b0a1e0f0806361006030513030324140406050f030604060c200709050703090308160e031605030118081231110a0e0a0f1b020c0a05040504030806010e 69
    0xb55205286c3c00d04121580304600802c4040c10202c5901128405680002450038003138081e09100c2e896003488036804052540e000d4005200328104051280c0d10417400d51040c1d212603a41c0d60140c181d024402612414030400c001c00d075000703034015500502e0100c110014a41300000c50079041940650041807142c0740d80740445001c10310240c40344030140c2c540c0c0d2080d503660003c100e0209131180010300340000c0e80c4410702a815103800c490300900048507040040c640001d02c00701d08501090a1900349207040b00900040c0c5000240d0002c0c482c200c45817034042000c1d150904c104065428101e200c14078010980c0c0741c07400705001e011098013140008000040c440782c0d0f40d1460510a10780648c245a8914070344600840589040c2d0080360000503403c4060f0b21460110240303804c440c10126500d1b0380d59100380c00b0780068084101c05104194440c6001c0c003010001c04d454000c8442d042d0700401441c0c9400c001c10113a21501c0c0d1107140901e1030001031101082d0710084040e400700f800e0800528411000c0302217 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 748732401 1250 748731151 748731199
    0x6090a0209130906091a010603051501020a020d05070b1813090b0c070f080c06040c14030d03110f16050d0f05090415030503040b04140a050307031b0b0a1e0f0806 71
    0x600d00c5500d0440c401c0c2c1c030140910b06c05e0507a00c981d901005150f45001550a41003403c0d0410382c05640201d006c0740040c0340108d149180c66101c1c00c01e80f0309c8107a4600311000c0ca50072494650500070301e038511000c2e4a0030103240009550103031503010b0150380016280e52015440c040e101c0d078400d01c000268030f0284000985840c00031603000300026a140c0b01000b98079221002610200e0f4521000c200c0050201d40c1d2a00c000145a0020007410480c1200d80058006200590014a8080061185207144500003002e4880c24118400d07198102e0003d192950900c5208190740b420321081184891943d5404800e541213000c3c107480004584400342501040740c071a0740d1000300588400200840d02d042a807001e0000c580001403120b0324190301c0c000708941c00c6058099540c056001d0760040011a6280400624a0f058004070114413030300c2d11441c80f80c41e480b140440001c80c912502c41c0d864040500d8142070109201c0c507050f8810400070303000611030388014100d14402e403105105a20442075140b0343c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 748733651 1250 748732401 748732403
    0xd031410031527110a060503010b0a020c100f0f021609021b0115060e090613150b070309060f0302090306160302130905070e030714040f1803020606090a020913090609 73
    0x25840b55240c00c81e40440050b900f00c111904444a41c40401500b05408480240c032201e4580030f003503a00380800b40070540c01c400c41060443c406d01c1d040d0403032919940c5007800b0b0781c111036032101c07116201c0320405419003001640d2841198040070444100e50704001d41c1d6005e80b03080300c0d80541e0740c680a8a08003146854801c482d06203502e40145000c00c40000b040c0b04080390301640300ca1202e00c0c0000c2c20052210800c8403910740203816490004086940c1e0392217103185d0241d8a001d10001a110b8141d8031407034003d104220302180c10440b083c402c25030800300345800e03407101d0b1805500d85055400030940f509005004800144066815099854040c0e016140411003d20200000c1070f03a603180d4034042c060554020021411010b0b540006040100b004429108428004500c4540c12418840181001015100090740d2403074210741a60390380b03500d90f021a000358003c3c42d95040c660104112160702410845d0160310400120850341c9402541104800780d24800003250415801d00101a10341150 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 748734901 1250 748733651 748733681
    0x30909050f0901050601030209060304060c090315020d050a2306010203041e170303060109060c0f230606060a3002032404090f020f0109080f0d0314100315 68
    0x208000d58000007030750240c481d20008000b803042e92506001502284546442d1940000c01000000e021807103c2d000480d01400c0341c64040384290ba641c40700c044001c0b03200c00021050350000340c0da91112020b4002c140e044510204200000f18041c0c00666890b9030103c1c1c68820580d88100249251307000b401964020020114002100d81494800001c0b002581c020301400511140a850784020f000055030701c5414107131546107002d414403600ba2615412040708540110881101b2000101010300415842c0d111240e881c13089030342415541d0509c0001000300340248414040f4004695000c03a111440d800445960f2070040c0c44030a640080b07140c00b82c480003020740008107100c0300044081c151521359a2280d190b0a050689004010a03079500e1680581129604590200903241c5110040b89000c014181856031503695800c16080149894003003416800c00700c0c034850343c103401d030082040541c14684d10a4242c40c0109464001d050703940409009000120440c50041701c2c9580b081c000c81a1403a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 748736151 1250 748734901 748734911
    0xa030c0215072304030c1a0f1b1506010914040b030f0a0312090203060115050918070906480f060e340e0405030915120c07030909 57
    0xb5001038802d5901c516462441042100c0000007803111000759420303241d00103030544075189031040c0000881301d0b00d500d054102c0c4003000490303241c6803100001c200c071049082c161550410003250f000d08007103060070071142d280648002c004a9a83c080f020000717407100850452840150040410002d10301c0034626034251068418a40007400001741a62a140c86951101070034510b5140c810160307602014000d406512810051111118807403803c015a821032404074109150b03880003075840481059084603500c420428005903d80c040d8003030001d0240c0e418101d580130100c016101c0781008416202220070b00840c00701ba5140341c1c007100c540261820021310400680c130307400c0c6140e121841d000111600351903c1040d880c22030001c64040c0350040004012000e03801e8449091094102210004c0c5d1901040c01d80030608a036030350221402180108025511a001981888805800c3c03401c5800b1040d003e11a44544020004015a01024008110391a0040b62030140c2d4414115004036580508103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 748737401 1250 748736151 748736161
    0x30e0717070506160201030b060702270127050405030c030d06050307050117040201080411030106180b0d0c170a0b010803130b041427130b010509010501050a030c0215 73
    0x344803080c400a6209803891141d0391000c0080c00c2c400c0c22001401541900e1100f40036601a500c4480711160151041c1d02e813421550014946c1d0051840311141034500722981544600a48c3c031440c05410f014588104012003c24424040e0703d0fa101500035442e2a20f00080c2005000e006070303000d41444200f16504d03051405000030180031070303004e07850203480ba4000c00542c0d50712503805860014006192000c0d180c4494004554415000b44103070b03200681012481056202482400002c20303280c82c6090202920041d507000396443c403080e49104004401f04807000c03584c681100c070100c9803446d040e002d004406040240c00c043d039500c400f41420786600b00008500e400030004140070b000c2d000030800d559031104021130307c9001e107010b004884203001e80c0c91a00d60802c02d2844203079a5119000c84201ca00b803101e90000300c0d4049401124044150b80c0c48010018400c1005001d02411a03141c84d481d030405000030403038050300d000b210405844031a1b6621581c0248807003089100200807003905444c04d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 748738651 1250 748737401 748737419
    0x607020f0409081315021c030b010201150605120a0b03030a0c03020f1e160308040501030b060f130f0e13030c0602131712030603030306040209220f060b0715020a030e07 74
    0x103031184c020071043c011400c0e00d8581c80407e801c003040c3c038500390b0040d00b405103244c11002040c0c0f01000e03a040d996507801e40204007510150040c001c11095403415610b030a54092903000120207844540000e06268001c00c8581d40401518041506072178036003560b000764202249004880007801c40e0318020340107407685003203c072850465080545021112100c0500c0d18590802c1d86510000c1e00b80c0c003082c0020b106c0c541c030a822440740800010841802c01d141300c0e9100b50998041c0c606840010b070921000c01c048180c040d071507001841c1080802c2018075084210741c040325200f020042c1045a946140404c22010303a044c0c407101e1030000316070b842d82c0740c980d05850b080c41c8800e045088030b80300360401514180310f200c04980c410480a0040d50460315031801348800780d0024810580c0c00130060003200090f058208110341460402d40300824401c008144002c2200d4254100c0c5414401c200400800304440600c0a402c6400303c040050f5a504030407003c030000c260140a1400900510b400015040c0b8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 748739901 1250 748738651 748738687
    0x40b07110a06020a0317090304080304080622110d0303020f0d0501060813020a0b0a0309080c030a12061d100b1803010b190e19050108030a0315050607020f040908 71
    0x603059464078003080d01d40300140d0b80c1d009a804028005071411044460700c6002c5000c00d5048800740e0304503424641c81720402415500316801c1007140ba0300400c100804024842c00070030b003032210321407100d00017042e541340c0940100c0c800b22668020f07100021401c0c2014840d5040b11a208801c1d0850f5442e1118840904040c01c42886407800250a00011070ba10380908d80c40c4d4032850358001d0180302d02c0362400d07000c0606e0303400c50260003041c560781d6642040442c4003c0010004840740380061a03581c040440c01510704114006907084591401005103c44a00c80c1c0329501191040b06456000e9521036511400060440d00010400b180100e9420583e00c0c0144050340d44000440082c071a00f4404410300601a80054007045010010030080003003290108149400080c980036091300c6180003214082a140280d0203002d41d13920000341c90b040c540d45031052104403e010b00c085c0d07e409140800051240c0a4204041d10402d64482980c0150381c0342d500c0751045c103a1204005440e03001e030001800c8041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 748741007 1106 748739901 748739933
    0x250b0705090616020312130f270902030a0501180b0108010902090c07031e0c05010e120405100203040e010e01030506090105070203070b090a2109050109080a17040b07 73
    0x51b180d100411540000d005003442c982d180901d070884482031a4068442c50802d29005112452107020490b020841c42201084000c428000a824000b03000c00080c465880c140f2224145400c8211081c1824040c01340890320b60703030311107a182c00d840d44020000c5d4410b10721380c0064102c4980d14050a80305000b8a0192020048454540d4110314400ca101c40070442c07000c40102041801d0060081d42c10b610000740083c1429006041081e001e1400381501c640d81a80011901603c01c109490091103010180d4806503901c0c2c0e640c202185082c0803c0d54036000e0340d4002490800d050080ae80285040c1d4021841d000729500c41440301c9402408881d0503005030304405022035129500d91210300f200740c2c14408460b03010354024100922540c00503060004076402000185c901040040203690801c1d804284810000c0780000944076039004008405004180780341480008204180c03a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 748561151 748741007 := by
  have h0 := BRFrame.cov_init 748561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 748561151 ≤ n) (h2 : n < 748741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
