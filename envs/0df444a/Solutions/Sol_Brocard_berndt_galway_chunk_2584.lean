-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2584
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:08:38.23534+00:00
-- url     : https://prove2.me/submissions/f87399c3-ac4a-4cae-876f-ca4d93796761

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 464568345 ≤ n < 464748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 464569595 1250 464568345 464568359
    0x80c071203090201080a111209070e040b1e0709061d0303031003020a05121525030203040b06100e010302180a0e07020f012304140d03020a0306080a050307030e06070c 73
    0x100c040b0f8000d80b60326120342d552980d481c1c190f03094540102c100001c2070240c05007030714203842c056030070540f240d00350b400c019101c410a041002c000c42c0c081d1000e41d900b1003481650550403400e426040c250040010083c40c0c4440040c101c040d10b4810308017084281c6201e80060b0003030b88180500b0780c1008060326503d09048200d420712180501099100d034103e6240060180340800324000f0400c0c2203005081d080c2c030000858a103543c4020301131b08800300800410016000e964550101e11580e46e2401601d9080904212a44000c01445d2601073f241800c4a444010340107988440c5030007007481c000d641c400441003a4400c21101d05100c40d0007a00322030020414140008003d0b03c100080e1b401c590006548280c01400c1c2d8110000790700a00d01e1207110a03003c810101002e80e40305015682800080500440362817400f440b20071520000703a40425488001d0758540a41c00003480713242c0061001409a45609459120f116001020301480a05120040c0c4401c001e4502d01c1b07402511010140b85d035000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 464570845 1250 464569595 464569601
    0xa180905121803070e0a09080c0a03030c0f020a02130c1101050903070302010b030d0c0215040b28050909160c0218010e2401030f0e030711030d0203040312080c071203 73
    0xc0e451510485030b0301d600d185401c0000d0303c0d00441c0c030100c0c0c0c6640c13142c40c0d003240c0c0300c001c0261440580d0a030500304100d4146081c2001142c58052190b900010181c5100d5402415000126203800c210b410950604015036107038203040142c80821580000c600c40041000e8803040300c03407800d8100399402c250070000c0c200d0001c000b42001ca4001d03002800f13541e16210130140c9076021406c40740c1c08500d50020000c050b0910302d162580346601d101c089441c0584a0030312540c1a002f0f08101c0c0c0c070080707581071207a0580501d041d035040c1c0e40c0000c1c1402c505002100f000600c0b04900200340c6040009850140318049104018001085030041c110b0a8000e0303154036140d4191409000d50400c500078880841d540060240d402e41c50658000494840f00b21203200450161141e0000c0412190322036545000202080c402040110302c43c0f284407900030401d9044c0b40c01d10110004610a5400070301c02000851820500103080c0c58040c504201750340c2c1d420301980094020140058001c01c1030113540044c560701a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 464572095 1250 464570845 464570857
    0x603080705060912070809031006090914030a020c0d050a020d0b04060c090308040b1e031003020307051806013212150307060c021201050f061c020a18090512 69
    0x741a00c0281e03445221041d6130302c280e07401c4003c091340c041022002103200c0d4009880b00900040584002c21103040d003907000c0d105a0b0704190f40351a6030310002c90420090303c01611022125101642c140310800c1d4002c2d490b44c4101c0603203030042100d0404402001000d006000180342d0040c60141d4000c1c01c3e040648007000100e0f0308698031458010b29211f140d004100110031254405101e610301414802c208206401621040c04843e2814084075240746071390b8040c611449900c055542070a20358010180740007440d5201302d00944c0c401c03040169603051603006560101b020708022605080c003011702c40c00f101c1c5054610358004900900700705000c000e00c000345040f18580002c01959200c040b54400d80c1c83d405011507916074001c07441003260070700070800c08100c2c81c0010a003c7c40313040c1039400c2d0303800d590084500920300201c07601001224070300028040f82a1032400c050036079001d050381c080b9161428500884000702d00e110265114410f0039001040c0f01070b4014240c407814460810348050a42203a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 464573345 1250 464572095 464572103
    0x303090622020a05210d0e0a0902030c03160c050607030b01090b0903070314070810060806010f1406090402090414091905100515090c0307080f160809010b030106030807 74
    0x7114441500041d1514050041c1d0001d1040e820a40b916080054440c100b0030716604c1d120400e4000b00c200e06044c407440b403900a6030346411182e0f18041c8204424001f19400086040380b0620a000700481941c0650b948003244842123011010102420b840907850084024020b02c1020100107400b540750300281e5540c0001e03202c90900544605008080b8041e54510741d0f0940d000c48802c2000c200018450310040c00071b80c0944150303644441080e410b1842e04101001d185484600801280604002c02401442815880b22a0302d080c6142480500580784120348580404950700c2e66a541b9541160809a801401044075005407040c48402000403191a400c0303009031076500303122403180c0028058250b4001c0190440c648030b902403400a0078060140e24800f86003c0900400c1d0f140c047c0c2c401d0003880c001000f0394030303482c0000000b000c0000040051101042603000e0020400d034040e1041b01034981070402804603038806403e10b0050211140f607640c1076003051030020074402040c00401c900d5000f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 464574595 1250 464573345 464573371
    0x302090a020919051c031b0b100f0501050d0209040605041e0b0301151a040302041113080102070809040b01120609020403060b100905011101090c23010e0a050d0f0503030906 76
    0x4109440300107054510826800001d010103148142e560171100c03d00040c40307030a00307003120342207070303507061081c0102403411100d1f640707802c0074440304003d94110740c0001e08101c0303491701d07000f400c040009081c4e002d000b6400c07105a07000310b990304c10340da640c2d0020400f4020181c0100442e4048408035200541a900c2c455526031400c52640c041e81018011400c442100b0f0354040d1409240c031a007a05203c000b8040048c000304140f00100050b0303039a01420121110441801e5120480f1089921480816510000d8075030310401c40710001510a90070750700403110881d40090f00140c8000141c50240e041003906006074a00440454840000d501520540e80982c0b010000e2100c604180038190004803000c030049940620200b02d5503102e98603491000d48a1300021469862590b22460700319902d0300095004080301400d040b4940040602d00c0070200b013440c0081c820a414000700b8180241801943c0c0140090048401482105202282e42da40d010742200c1d50391410002c0c0540300d800940b250403140d52 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 464575845 1250 464574595 464574619
    0x70210020a0f180e1801020405040e01050718031716051e1b1813060240090c020106080a110a050909120a03060302031b1921030203040302090a0209 65
    0x843e5028100079a0040c0c84168a80d40b1307501180c180d1807161041001c45590200400305030354540f401800c50b4000a0000800d90341410100540340710842e080110911075024010008161450340902c160204401110f87e16017000b007040c11500340506010b0700764842c40e0103520400b43c1c0728907422013100074101610441c41003012a12890000c01c24040d5010800740a03040d05c55031850038041c2c100840856000c0003000c503988400c1130343c0002001e1140031295403034038480c20040195840c21211507410070040c403a108080401992454011848126a01c14000d019a4001d5100324090140801110019800f614103030b0070345103441000c1c9004840d429000a01420101400e9004032006000340c03a203000503a03402e0401d6004000008101500d550300080507880070b020228802c501ca40b0600c541e09140c02c28464007084000705040441d1000000b0858407041d0082401c0503004803510b408840828203040345107001340c3d003000e584a050b150074030507201078a078000c05e00e40209072000040342d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 464577095 1250 464575845 464575877
    0x90a05030f160f062109020904060204030b0112021008100f03060608010b0402190f0309120807171e060402130f0609060206010605041e09060611010501080c03070608070210020a0f 79
    0x295882a400810742501e84010a17007201034880030307800d0a0200c006019483c035000190100d009036402c1e02c50941c005018001d00201c0d00302640900251301d06000e00684a40c0460300b140ca81c081c07680700300030212012412410a0003100ba00402c42d41e04800780e2107417a07050550027405c0d5403107600859881c1107048a0b180c10103000741d5190802812078240401d8042c501642e002031102000c80c1010750381c88200001070303903501d8040322a00055640542c40e103015240600812001018840ca9481042c2007052104007000d140164001c000001d842a0b111500820040e0095403480e062842141802083c40204c69480501b180c981d03940e0041c0e19551814141e0321110207014480000e40200001e000415069100000c004a20b46450001c070f41e8905605080303d015810010000d14140040414040b00340a010302400c0c858015101c1401c401c1e00103070351034031580311780c82c24040701500003050503000340142c4410f41408002595034400c010001040340d00c0303e0310b105000c1030420b16960005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 464578345 1250 464577095 464577119
    0x30c0c011503170c0705030d050901030c03090b011415030906040209010b03100509150d05010f0e120a201506040501060f08190207150b09060105120606090a05030f16 73
    0x101d4000d8000404000300c08030b0021182d001e00008049403054005c0012643c408002000409803191b4a860f2180e040300001410389450b200884105401d0004041c0481c0f5400030850459028101c0c022801c000480410070b0841c2a401a0003070310790102c100044141d000c01c8661042d0701c2215803461503a00e40540000600080c1d42002c020f260b60f00e4180064208074035141d41002001c040140d60010600020716810140c0c801101d03030340d4603803101181840e01030140d909030600e468041e1090200813203107619070740560303043d5100f00b01207881c4402e442d121810001c0b01100215050791250714102c42a5001c006007034030354034050f518103000000c007640f082c512111009416982d103c02d03915110204d01c07440300c055400c1c0b8440c0c4c0d400c1125100042c55a2801c070603031130f00c20b800030403060030b03071800c005446000400690600100308804003611448a07142c0350f020104070f41584d22041210040b52249020b03410043d01485450751000c4140e100080351808940e1a699807004503440f12441822 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 464579595 1250 464578345 464578349
    0xc1203020604170702045a110c010203010e0703050114010f09170c031203010501050d11040f06030e06090106060e040e120f040609090915021806030c0c0115 69
    0x180c201c1c00c0820005401e2607021801c04900b910b696081543e10b40002d0102c41d6a81c2100000340051006c1400340c0d0003c40c900141541c107440c6074000040c00344074001c0360445104d8070074500c03090b41c491444041c031542c5c0840b081d03088a856068803041041300c001e000354020300845000d075100100081210b4400c0c081c3e141611200030305841e0912080d001034030303100c0c1c00502c07a80620a00d40000700740010301c07404801c0030000c0d0070000c0c6000720801e001e05050600344001450040303002c10060100b030360000c003101e0110320740d540001400d200488919055004030341185e5a580c4520900058895264101c400526081010784000c1c0c1c07649198a4200c0d0614482e00d00407031228101c02107070b8034042d4010030652180500740d030f5090301100c00250241c0c0c0302c1c400d040e15030000454140900d0b58000582d41c060310410b481003200e00126210b01c01940520340040f82d913150000780d84004c404444851004400020b44680c0d00da0a001c00d000303840b03800220050b1a10340ca441d8507485084c20794560314013 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 464580845 1250 464579595 464579597
    0x3030417040312121d0109030e040504121202190305071106040209060103020d1503030f080106050309031605033705070f031803050a060903030c021b010305090c1203070c1203 77
    0x5200000c2551390140040c0c40d450b2107aa1190045640c813040c001e242c00d084e40c01d03000003420300d410785806802c2c407c148140c14052441c00c001c11000800b6000102d4102c1c4603400d086c803175145090794280181c403690024002c0f042881845005003a0190012800360340281c5484000c0b004019810b56102411200698005080804984ca83d4000e80c02411180300180c0042101008007001004108140d0300440c0001c1c0c0140e5006855503021142034054400d900e0300a03c0d601741551b41075500c0c0980c20f0900032400f2200229820040f040003124040806c110180300500800c41881c102c40c409030941910000d0f00c0e48400e10220b00c40c80032540c500e0b40c00f14815413070780400c0e1000c54150144400fa405030003030210001c0301042e0100009405944505030104daa0326003460003c0c11b94904483e41030a5501130b89020241c400c456441d088074910a00c0c00081a68a0300e240915118000c0070f569008022400c03805c1a09a000c0014100c003401820130340100c1d07a81d09400d20014102c1e0001030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 464582095 1250 464580845 464580863
    0x406120b0310180506010807030501150f03030819050a050709080a03021509150c0a02070509040f12120216140c0901090207062d11040b0703080604110408030304170403 74
    0x401c2c0d048a9000210810702106a078282070099038640c1d1410b034003a0010400f80e80b20391030400c00c21000b405005144441c4c0c5640060851074080b02e0b091400349804001c0034080c0a5000408801c4642500c9801c405055400d20803420960040c1e001810240c61110000d20101004038090200240700081564190300400114529080112172803102401c500414064400d800912502c0c80303170040e000d01010043c060740c800c180c0c0c6000e0728bc000705a0101d13004c1d1050408200105400761202503105410410711130382c8102c6c4070000c80c0c81508100804620340e10103e0125034405044100e022002d1003140200d910401490b0400c3d84c03800d142e0f0301f0a074007c40c058010300140d00341ba000342c15094414100404c0d03040700031200210554001d00e0201c001c0036170302e02d0444da115150055116920703802e1005071030f15082c09a03000c460300c520312029060080000100c0c0e42500c6641c005503102c640013194a40380e079200c0e4001c6499070700590301625140c0181180c8101c007a0300d04121801c60340e01c01210 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 464583345 1250 464582095 464582113
    0xa0510020c060304050106120b0106031803080a1e050705130e0105090c0f07051005060301181101031a031501061101022104080d090b0601030e03090a0311061309020406120b03 77
    0x403281d07070300041c400c0f90507540b945400945616005805800f227841410500100d40c18980d0080880e0310650200900e10a0b602c0d034100400c0e0010f40305030f0071240a40d008101e4035500d13104020780e01c110b010b000d039a00703103403404008580d9800405000b0f04034070036222803200c5640e010504000b44080c056168042005008507040300d0541008001c2c10740700c1e50106040041c0e42e25000d00f4512044100310107142c0f54020410186400c1c86400b40842c03481460303140025498039017082056811a4440c14140d0380c204481642114070095000044003c0844900342c030300821031103580c8801e12824010440100b458810044103000b80c0c0c144040b402e60390740941d441072030310380210400036005941d01c0a0420100c0c24901880c0219100f00c1e000d603d20001500b0403100040455151581d410401d42041c019810f051345c45101c1c61040301d0b04040002e46034241c1400044031071140303040881a42200000c0090341d0405034000d03008981c0140c030740d00721180787c0100700310644070008685580364000d2100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 464584595 1250 464583345 464583349
    0x20306100c02010207090203012c0f07030b032e150311100e040f0e0c01180306020307020c0d0f05061b19050408030a170121030309080f07110a0510020c 67
    0x1400d41c00ca40148100c0300c40c1e603580c5800c4403c99201303030030200380b0480c0542d5000741c4428130f0354044081e5444010030b014502d40045884682c180160401c03080544400401e0010b42d8200120001c20400d40001ca80a00d80c01803002c09192559045c1ca103ca81402613003019000b2050b003a000320303500300d81084001c0d00701d00200711904100c444240180013aa891112031511340b48100c5112460b103100005600141c400c406140c1030303446807020b040208034020440b10100c49a5141d04880d8084005a00c0f9141c19a0a90800d10400b040759008032891019a05000d220003e1901480c012416120b542c1c44890507182300500081410210150401c0390f20030340c60004086900c00b82a81c9881410191500d91190555201c0c120031700004021284600c00010740c00f84150042a11211185106a04460140c3d03080c036429001707014580d03212509000c0c0511001190100458840c2d0b140d07403070000345016404030101d40f00c0c0600840304400301164034140440c90802e50f10301500140794450f44102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 464585845 1250 464584595 464584607
    0x2060c030709030c0b07150c0207140604030f03120501052d010e03070b28020a140a020a1503050708060901153e0d050f0f070b0f0610020102030610 65
    0x260301c10000207900000100c0d41d141d4241000d010f10350360960342c030305890a08480400b003459450803880e01e802030111880b40c000540d0412038040003818810341d52a00002103880c0a10360001c0c048851031207500040661114901501c0001d2400c10032042c1d80300c4051100e9a01e840e150150103c2540104400c0b0a140d00303003605402d40d0501d480706d15030320440e01007820115150722220054070042565400d4901c40d01d4030300c80040701d42000c001503465500c0001e5480c803690714041e040420f01036820101070341c1800354440e0250080c2110706441c0e91104000c885e54181018000020716140100d681180326100c2a80900c0c1c0040072a14583d00703100714451103c2d004090305040c45031003a1003510b43d89503100f10b1540300c20240c00c050809104c07401044941e101c850942e00300fa0300008400c03a440c6800c2010344055000000391681c585c0a100b0301101240b1800c2405846000c0300e80811110a106d0703030044c1c0c0b24034070554001030308105a0000380d00340d0000fa43c0c05644090784404103030035144906 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 464587095 1250 464585845 464585851
    0x60105031b07320609030429071506061701030b0a180b060913080f0915070f020103060b04030503090d02010e0a030c03031704051b0a050a06020102090405150102060c03 74
    0x4039801c1d14080050b603420340036140e400042c0800c004440d003186510500340c1e03030200d803801840c40500040d191034420651648218010042c201c1c2001e84501c180d1611122072003002d5141e082c051b0341c1c031402c2e07040c2200441c0c03e8006120016040820101d001d44c803c115041031410402e1800401ea400c5035100b440b010300051440900e03d03600d0000e40f20341c0381542d45425903d03005107108900380c1418800d000300303007030b009111311181c035218002d5000154510f011034040c1030070468442d496002d41000540710b0402440c80c0207031100f0114041050000c0180c21030030003403007624200f00035591444201454044d900c0003410a03001401460710a0521f0441c0001c62441490a05c1844064a001a0132244190800e94a1916005042c0201908413620854110442c3d2883c2080d15040d51130070b0f501c004103800b400201312410a000e00d16280d07503401c50041c01000b80725210203074807410024000d42003803110714030035420107004c901c4400d000e050f4001038040603405050343c0d0340c88840c031020550001d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 464588345 1250 464587095 464587141
    0x6140f0d050327120f06130606030f080d0e0601120305090604031e0b06010203090607020f0109080607050c12090607030807090e0106030c0f030e1b010903120e030d0806010503 77
    0x10070901d04101a00d440784181c0e590101414016143c0b18000e001c0140c0240d10030309000c2c1d014005c1c481c00a41d0000f00b01d0b03031102480785220b81e45880e03840c1c02000341006500050100c3c49481e1100100000100903000c0c05007a14002c1000781045c3c50600e5403210288108005018250740180110348210018550054060b11300e5180c02e580340d4404511081030054942e48010000500b010400b200c12440e801c5902440214108100700b00040c58902c10040002d100e5000320145070100d9018107016001445a00180c428514184074054142e0f4808a40c0113030500440c42030b0540903200ca4260b441d601c1000c0c00d0b039030401c0203a83e0700380d82c0c0722006081c0d00140444d1450005c1e6424a0311401c1e406803c140d07038003181600035254080c114824200c03a2505050034030801c01400c1c0c10000c0c1803891000058844020315101c0f10050320180e03503942003e0300601c0c0d00040502226080020a419020250220317010a0084041210101000d449150008030704001003120b1003103156401c1a25000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 464589595 1250 464588345 464588347
    0xe0405010b0d0b0a0906181b120209010e09101b0f08010807090b0a03060903020709050105060702220902090f0f07050a090608071103031f0506040b0412032a0606140f0d0503 76
    0x41c050680c150f040307001a0440f00041101c0700d10039115230600c5000c004003411006c0c403d41c03442c0399000800142050041403415481103000032000b410400c080303413403088240002c0110b40b010043d4910700e4800c0e040088041000a003000c00100d20440b030b118106c0300070318050308001d800c0c2140d203805450b040f441c05030712113412600840490028440c1ca8166880303038004021103407600210905540d8140e21a0b441030710305100c0341d00940ca602d1006881c00c06900081261451042c4140008104400020303400c440c603902088080c030451100d00d030007114803044003101981d404004964521551300f50000103035500300100652406100c8085e0400d4075030a00001941440e03101920b5a0000c540c840340d0103c08150b20104000804445000350006844040ca81130601207642c4580c41184078810a140c040c450405c01d0520440608070781014a8001101e58401440c4207446161400300666046281007c006104220404d29400228001d00099004007141d410082555920401a9001c0c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 464590845 1250 464589595 464589611
    0x30c0a05010503221a0a18030c02042d061403010b01020706034115030c011d09090604060e0c0f0f0118080304030c080102070309120f0b010e0405010b0d0b0a0906 71
    0x2158034440c030f80c1080e4035807003441280340c401c088000382c6036103803507c54030240d456030703108080703644010414407450f01550045000252459041d00b400700350512060904039030b080c0185c2011031900800215860004009180c5c0b0042003018200c4d0890444180940d0044104006142c042d4211010b00c100607814228105c0042280700c1c8810707440070460302240d0901c003544512140f0008016000740d08445c2040801d109240426034441c44ca0202505010501c5a800c112a60049060020031000352a00a880c10000b03c0c0a5031104141c41c2124207504040c140c1c1e2070002c00180f4a803841100500d2100301141020901c80210f0010400301d04108500d8a40011071ba0310105040007090400000c56940c2c2c80c40c14040203141c0300750084500c0f44d00400c00280880e138484468025210145e501980c000080d1408011003d0501801001d1020000000450b81c04c00e0035600e22803070040f80284811104902000100106c4031030050081055501040d00c801060b4050178006211701c200140c040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 464592095 1250 464590845 464590853
    0x922060e01090f060e0703033207050a02090703050c0a0e011134080601060e010207031205130e060127083004080309010f030207060218030c0a0501050322 68
    0x500c0c404020390304a1003456000f000c0150740c5c0b180e400c1c08092240a420094210750f4004c007100c98248882440c0010620740c012800300f6104080300d46480c101585540703082e00e10f011900e800380500c0580c030842c0008000f5106c01d020303003d00c62240d01c440d8460307880c00c40480c900b0785443e008201c0d95410040d0207508210006010804140d400440980c0d04147c40c10181c80e40d0004e0030460880c0381c0301ca00b68801004890000a43c041c1529141e05101c0780d10105400100c4c60101c10b580041c00440c0da83c4c117203c50060b0820000c203107002c00e003a11806055194410025017a000340c40c46030005805079200445442d142002c0e074002c10205131030440785603a4810305860106c10003004d070030715011a031406020180702101e80d44c1402c2451a08ea08182c03401c1c132160744038003464080c5810302c0713141245c200320300384640c3c1291030a0354415811522078803903142600c0c0b07021880b0b24541c02442244020560f51920040003421100305954407840c580ea1695a643d18040c40c41741403a80301c2c15504410300003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 464593345 1250 464592095 464592101
    0x21f051e090c030d020115121e061a0f0d020907030e030706050f070306120f030c0c23040e0712020f03030c0303100f03030e0d1a01080312060922060e01 67
    0x107000d4950003404014018000c05041c00c40382002003055a01d0b211070b01d804000811100c10440301c600e40c03130f060085282c4c02c04503079120703003101c401034040b03081101c1d1000c0001c1a41305c0010304400903200061840c002046c41180d007040f6a01070b52003800c00d914003005142c40c0ca925540b00569181c00b0440c005962213152464010780811a400c030f0300c5da0200000170010741e000b554010311614080c0003c40c98034640701d68a034200c400c00792014000c8884881894020011000d955034800042c40d104c0783d44280c1c02940100d980c200b010b034003494820240d06440d0a02a00e030508446202806559141c5940d003001c6060003603040760001102c055018140d64140041d244407050100515a20701e400e01000f4007500c0aa00504104000014244003103540f00004040d00070055401c00548030795420007411500f4071055a1000c1d135500c500110f90140080b002d021210001c281c140640c0d240d0740c040103280d00c02102c22903400e400c003e0411207043c511503000c051385409200c00189210ba120b05041c29 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 464594595 1250 464593345 464593351
    0x140a05070626061804050307020a060906021e030a20060f0103151b03020703121d12160f0311071e050402120a020a11190b07021f051e 59
    0x1c40c140c44414401100240182c004500542101842d0380c41c0c6030000801940c1140000401821042e00042c00c2000030412140341a40081c0440046591900b00030443e0510b0702458006000b4030081c02c01003090f0340b0364078060b124000c025509103102d000c0101c460030003008601c01400a010754a00102030180f00280c024410000d07001465810b40c04c28081d503401d04080c01d10702c5843d00300841c0c155095298202806403003894056914441800e08680401110f005c1d550024608400c02401520900100320710400e0001030b510441d425a410354414011801d0382d6072082c40c030000c0d00c00000c050005103c000d910030305209038405000704851749084055042002072122000400024002c020365220082000326030a602d40004004080c00c2d44202501074000d180d008a0040c0119002c1c1038410202c1d001c0c02c0440d41401d00c182d000a0f21124031680c203540c0820640c0110ba031880c4081003c0d00b14461440008910620110810004210092060808a802841e1b01b840800e07900c1c0c400b40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 464595845 1250 464594595 464594597
    0x1014040905061f02100903030207050610080d0f021c03090506150a0506190309020a09020c0303220803010303052101080d030b01182106020a020303180a02090103140a050706 76
    0x1655140000074026801504242904101000c804501c4a144d0014806a00403000c05021600340403500d41903029004444000b00540200b504214070340c10700013803075003c64801d0130490303100d41c070402d200b034406c12403907594070b130068000d20903012500401c10301c01d0451100e94540007440044648034103007002000c0d40c101e07050804000f0313405d815290410030080074000444a1900d0041c400c2c1d043c00207861011000c005040d2541000d00a5689408a4000808a02d001590303624007807409103480350b200310780000d00f1841410740141543c00754440b503d21680d102c030b44203285900359101541c254019000c200d402c014820031b4004900f1250b00d1090080200e000280b1480d40c2c4001e010382652084040d681c1080781608208440e0700c4049040c00407544020002c50360305c441230300b10783c280104c40780c00500f5060001460002c3c0c103500000846c17282c54255400320356490140c003c0350700c0b0040660081c1d4040721080c0140b0100b40341900d00d164a4003010304841ca40d1086584850408140e640000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 464597095 1250 464595845 464595851
    0x60d0804170c04020a0503010608040f050105090c011205040309300807050105180606010e0402040807060806100318110102011803030e1e0312130c0305031b0f0c10140409 75
    0x9042070010001648814001c0b0f4056003480b18002005169003c1445803808012503400881c040c052810180b11310315402100a210501e00728110640c4c1d901d00307200b990b001602686c048401c0b2460b0b4810f041c00f880d81661401c28103481c0c2011440b06400450600100256270b403818030507a0705111030a1070300c512490070070b40c55003210f040850845500510200701103101e90010464400d0101d0302d01c0d400582400d01108582c0d0410100300203001c4d81d00091228400d542011480ca904000c4a0780308500850320200380c213402080440958084a82011603482c00d9641c0380c0002d01c05404d040c0315190103200000c3d4240300c14928a00343c0100d41c0081d00440ea5030304a92202100900c008081450300d01c4005c541044000d8005079644101a03000880380c10003c080703601000d501c47e8a101d034903007001e0031707000d07290326420905d440342c0c0a21040312018a0002900c6500000070401c8500d14001d80090f040784840310301804a1402c0100301d0904010b03582102440145004024101420f0815800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 464598345 1250 464597095 464597129
    0x1902070506070f1b031d033c010f0e07050613060311090d0b0a0c0e09060907020c0904061a01030603150e10140603070b030f0c09040b04060305010e0c06040f030b060d0804 75
    0x306d01982403400b03854001e0f003014450014800c4075049100d10449142d10100c13a841c0c0c0c80b034154081c0d14000d1400742a55082c0724102a510000c0d8001e10b00b1805004161140140d032481040700a01c58420340031400c00030309504001c0107010f588a40c4095080d486460329051200c8005600003112100071901e038405801440380d480300038403502032500341c282440b408a420b1880001d802160040440348500c440e8070000345014420f22414070700c108082c0201c10681807a25044c0050065003041140c501500e80324600382c0c0d072090180d0411660041b05400c001040021311074042d000c000140741d200d100d840644101c00c411407003250807407180401c0b128800d080803002c140c18002280c0c8a4407164109200f4480c010800141c041e80041e00c401249a03104080307404100913200320138402d60320070f25003c0300005020b01034220a81d100900405c0d80d180c07811000070441140950301840300e8090b48803106000203002c0c500000c0d0007080050850b40176581c2e941d036100301a48540c10001c81042440c7c0d030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 464599595 1250 464598345 464598377
    0x41a19030c0614040b0307050d050c03060f120a06052e0501050d020904091b0302130b01020316030306030c030b1801050103051b1c110a090203070804021c050d05031902070506070f1b03 81
    0xb0325401c507550700be1329803075400e1440020f00b04444007052507204020301088460811420408402c00b40d6000c14148213500d000070886146580b506c50002100190780040c0c000d2407291003003401660016141d41c1d0805003080758180080d0004e4942c9504265580c001c0c40105045c4035401140d034411201c03a200881c1184184400c150f800c0610003900d50400c084106d450782c001c020b03a02000d00021000040501030308088020304400d900c05001c611703480d900071080c41102d010079441110341f0445e48070701503843d0b01041d08940003413001800039006407041c10743c40e200310155085d00400080400100c0401e0001c042c03088a0316110407680c8440001c1a410b480c00d0000000005040712141181103181c130b1040076000b0000207100a120b02d1308820704060940c603002401910907080011258650030158002e450b562080d034450100070f403012409000c49138a03000712213203103900c04043d01303498440480942e800c031f42c0032280c102401a10350607504c80a02582a0306145d03070007955090704900d183e0903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 464600845 1250 464599595 464599601
    0x3120a05010f0e011428080d0e1e01050c0717010606020f070b0d05040c0b03100524040b0901020307080703051207030e0a20041a19030c0614040b0307050d 68
    0x80300f480c400c810440100b203815481590310b40741c51810340d160074010903145076014181144000b5688030a0780d18001080746140003e2400d076040b0b043c2c45981016204400f00400030080c0d62628141e46000798001c4400d502c06cbd07000c0c0440d6003214044805158a400b2031011307100c503200311400360340e5480d0810001254100b040010803104070001d007078418103206140d01540b107883c3d5001c1419445070042410440c0140d001c2d0020f0510501c000c1e104d08114404014004c803078410b4611a003940d072692070398080f80c0f8170030710803040f5921060f41c50a45000c02075046500091601c0b81580014050300b000f04e920f1a00801039903200340d840c00e55414460031941d5542d20003408090400d45001c80701c860004000a003000703c2038100e44100742c0401c0804120300c454807030103142d58010341403510700c0043d24050000403880c00f1040342c0078560031840410300c088036142440080c003041a070581c2009914001c0b10190441c000104d03100b407500340c0710742007074415030310955242c0002070700050312000003d9184 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 464602095 1250 464600845 464600849
    0x60b160f0309150206042306040f0c15110105070518041a060309070f060203310f12020123070b0c0403020607230d1413090e030a1103030103051c0203120a05010f 71
    0x21019203601d103e9102980d5410300520082c032b4070186650070b500b408000b40c0f0b1607000b0701203c0840154004000002003008041c03840703003940f40d802c10b00401c0700030f80504240c4da83d07100c019003101003803140c1c2c80820006d441504d62100c080e1552400211480c6c40e40ba00a62049402900905a1500d800401e40b050001540000f08641040c00180c0300c01c0c501110b600d1058076106411000300140b9812f012600302d141d40055110402d010001800e501d9151918280713500076200d031418a0f512001001401401c40013140a44004015600000340141c3c951900040080100b40c1480d84a07404200c7c19404140f00b03075002c111940360034a91b4480140c0307c0c007044c60f000010b8941219000c0014142c0c40301c40720225803a000204d00040c402d08074000380c0005020301c0c0f0080c00050f15241d00c0640300d9200350004000640034101e0128903c00020442c1c0c1200d50002c01449924402c2c1c040903161a03d94120004501003080048161840c05203424001d0349107600001d41075140c15520b02c09000c0503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 464603345 1250 464602095 464602133
    0x1090c0e090403080c0f1309320f04111306050102190c030803070207210b011502060c030703020c0a0c0f0518060d030c02040903080106110a081911060a0c03060b160f030915020604 79
    0x43c9d904000f504003503080700342c0c02400b03205043d0045d803900c1c54901740200018401641002c0030061030341d090304507a040141207031801c4e0282c07034440175001c0c49059205130805002e4003800000d074081000640260066a0040c3c0520540d4066a11445400d0300407003000001544141d22513040402e01c000c405001d03005042d1103221101c42c045040000e0740702ea800a108004c2903c0220001d26018004d030125141441000300703490040015103400105884140101000d80702c240c0381c04601401e0640d403494501d0400403441d40f10781d03210302c04c004015805c510110100b0151480e014016140c0d4000c80d48120310986039040d01e5810010014002c03111040d070441182d0148880802181c80f0301d045900c0c21001803c035501c0b900d0625070546103590100c0c5001800d1050074200099108039921001040f0359aa609100b0079940d088840c4d850700030701c02e0100d4040421401440040c1c2c0080001068600c070f41440e030115540c4604421642442d4200311015800c034034100000c001070242c400140c1002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 464604595 1250 464603345 464603411
    0x30106050603093408030c0105090d140705070b120609330a0806040c09050a0c1d040b0a06031a040e070b1b0601090c0e090403080c0f1309 61
    0x254043c5580d10140181801038841291036500504041000c00403402030320208840340c1c03503550300c01a03942c1d41700d40d0203100749519060104070400404210214540a2540e840f10701010b8030701c01c00d8441d844000f0440342813098210000700703030241d00050f103e1aa8440401c41e800d103001e00c01d10441032030041660350f0b19000703849420030101020146111010080174058983c41981c40030503500b100d02e2300045e61510504c000c000c2000504d403200030540e21562401e02c41900e811621030180e640041c001e40110b282e00082c00c0d20802164bc0c5480302d00d0009202180015828000c1014154103401410010341c4401595808070041d050680118905079010081d480d080400f20740c07680b000b03001d103922500e80011162121810348081c040b901c00c407501507802c1c0756507904101e002000304070318141c0030840c10340c40d80c1850f03c0e182505a1203a40c0544400761180d4410303030760f0120380e072005410755407140c018058001e0007200d03544084094143c0d040005601c05000071000200307180e69100241c2054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 464605845 1250 464604595 464604601
    0xf151d06030a020702030c060f130b07021305191b020d0801051c05030c06090714062718090a1e03120504060e19060c0e061e1201060905030106050603 66
    0x22804112503101884120058450340f1302d00c002818400c42070348599001c503010440500c10301002e0000c100890310400090303d400e41d64040c280d26401500006580407130480c03020000d1450f05e421842d400340c0c000441c0381104e40310012403c12112804840b0696010000e00000c00940400c0071442c0d200307036424442199032410000450100040306c1c2c0e52003195079041c0da80704000b000c005440c500042c1c881507400d00d00c0c0407010580e490740c80d4402d891710304000748518503241c10701c04200c40b41038041203c507000303650701240791030b900b80c00031100700d030300301000c84401c80703e4051107002d0900031135140700039040300c0b40c0c0c038145030b202d900c440308030040b03806038901007900020f42000e03080b4481081c03090017040c29996030619000601c200e0748550900d02034240301000c81c0240703003803c40f181d6106c0d003001c200d5017611040448411041b5414190440002c209400000d020101030740e82d0140d5040740706150207068501091120b20230307804180440c0950409004a1800b070088401131314003070301c000381585 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 464607095 1250 464605845 464605849
    0x30b07181a0f070303020717071e0b060409020307050d0605060406080705011b060f020a0507060e031303170d0204081e120d02071407080a0506060409020102030703050f040f151d 78
    0xb1140400c42e00c5000700020b00c510400d8007035010754510070341003016400584140c810f102c03040d038080e032402c44484003048031030b204800000c9642d81182ea00540e01000c01c1c0c1d034030030510005102c014810ba0b13040c031507801c0020302c90340c840f1000c0c2c00b00c91043d41c02281030f0508400344801d4802035040010150454001800f5590340f0030382041d0828038804440c035244800c2c0c24481c00910300310751041065400000c0d40400346401400418034280b06480c104424810035541c1501c1340610300d0603048442c00786070200045100084444e07942450010303003a140c010341e034090390100d90040c0d0010905030031030b8050310200c01080048641c8280150301034030441c00c80d5800c4907400d21030303c0380c00080f01b6404a111000d221aa42841d0f002440c120101c8482d1a1515011030795000034001c01c81e1207110751000190941801e0260b200d1040e0306800550400d0515641030b90700307800c0b41c0f1400b101c600d01070000240341003510424030b00034a1801c8201d00907090900000301042ca403921024824418005100615 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 464608345 1250 464607095 464607097
    0xc0c0609060112082b0b180907060c17161e030e060f13030606051c0c05010c03020307060603080d0e1911040902130209040b0a0e1906030b07181a 64
    0x1513211008075a2001402029042100e58411004800598400b480302410407503100000e0114210b40300441d2000e1049403071000c0700101c440a07090f0308000002c0009034001c00440c0c0520f4400c04070380d000801c110362100700c41d4022101010040e000e0811040500aa868030051030030350455441600159645018090303498445046004505c0021200c0980704810240d4400040301b18120441030307524207001c400303800b00d4040d55204000820281c0905881c0810074003806622542d032250a520348001518107180500d401c0c1d0a50108200710030014141e0300c104c201452040c0c016586401c19400c10408684520308800c442e98070000c100c01d40708280700c4044800541c40784507410102402c501140c0604243e00e0001c0d0484940141002d8180841e0080c143c0d0344010b440410031801c2d54020804969120300c106440010b010020414040c0b0000340106400381500020411550300d0b0340d1615006001c40742540000c054419004201d03125480c14802050012010450b04441c02401051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 464609595 1250 464608345 464608379
    0xe030f0c01181205060703050a021219020903030a02070311010309021c02060f16060c0c08030a0b0402090603040609060b01111e1e070603050702011a06031b030c0c06090601 76
    0x521407050200d180380030380ca16002c005800b0501520f542281185452640e4020603621000424289400a040d810291003596000404400c980c11281c403100e0030800352901140c0c84010300c0e5020401e041403a10104001c00d090451540200740342840c40c04c0c0000058a0b078000c06040600300721200006d070365040059840c3c0740141001c810103072500d1001603c50721414944001d0400f01040c070000158210300031895641c050710043c88600603e840c200c611400b0380b00d00408280c41800400c0103140c0c560301440014402420061420001030b0005403a50005c950485150741c031a1108400c001c000c5c001c83c80085030030300700004110400031502c0c2d01c940c4081006a0804080e0302500d41d1990304103c10ad2610716040d0300c042d201000182c007a91680d5041c007a60307001c81d05010120303003031074030521400176101c50000f40c12800312056410403426500203066501003c0e0b404101800c0d58040400441c0181d41030704080342c0e01d50f41c0b605c1050070004000d003981590f420100042080340e0000440c0c100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 464610845 1250 464609595 464609597
    0x1a240405090f0d180f1d100503070f090b041103070c020105041e06081008060c07031715040b01140f160b040503130b1c050a060e0c030103030e030f0c01 67
    0x1080d5844585851070580c40654210b00e61088501c1a8000ca07001142d15000f102c245005200305529860701c4c0d40c0040b90742c41070744004c21248a03002d5204001c90034007600010741500c0401420781d207000003480c2001d59040741d00060f4416400300041c0c502e40c0300e8852044001c2e5024008200e40b011400c070700740001000c480501003c280990304580c82a000c841c007608c00c0000000d40101c1888420181c4211401010045100d031408100c00488000225007260752410041103559030304c0c4044011900142d10490074410030b14540c060003840c80900c07070300c103445500005004004d0f20b010002a640543c2c085418003440c8151080c144200c0d000300d4040070325100031540d0751080e119a040c841c3d21940310241c0046004000c0c44100000440200000c0e15040150078000c0d031605102082441a146e00d000b0f8000e880c849110001701035000f07281c1c8404a808009441d581c1c64002000c0900125407694060800200610070190482c2d0b242171010402e0b8010010004941025580e600b98085194 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 464612095 1250 464610845 464610851
    0xb01030c0c2d08040f08010509190201051e031504110903060a05062b03181809030905040c02011d030a0c0605090c1503040203060f06031e1204031a2404 67
    0x30298074425104915482d5120f085240c0e01d135540d401001e884482c1d401815155402c040124061910014071b00c1004075014000ea83c40a615a0040d81c00358407a00443c0605058000c0c0d44420829100c01f070741c403440000c1104072281c5040703010001261004401c1009410003407050b00829240000e00540c0100403044c002907a8403950300003880c040001ca00c0900070041c5030030f070cc41c41c00248604a21f8083c400d40f101460780b01c81541100c2648210301400782342104419420303d40e00c9a0b5008900940d0082c00c1022090341c550340840d040d200300c8a070000140c2e4458214103504110b1480b07130002260720300e01031030402c2c04c10030005050b1805007a01901c00c80c0c0350f4012801210042c80440f03520100101000c0418040f040000a1070300100c078242d2007030040000250380440462159841140300401900c0707040e00145c0c801d1240c14a80034660fa5070301c608110340754a4030b4000018805580034008070744904210059200c124500104030412108003a85260210103400005038403240c0122804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 464613345 1250 464612095 464612153
    0x60309021504320303030403050a09080304031502070c170304030314090d20040c090e06370308030c070b07050f070f080909011404061409070c020a0e09010b01030c0c 73
    0x411065103e842419490300002043c00201a04000142020182a110034641c19514203c964481c011480050010000c0c1d941c01c00810743c06a0041100d144200007100b0b4680d02d80d05903c01c80780001c042100c0300d03440064144240f5410900c03500c1c4840c20710001d180ba020300d003008a18048907615005140400100500020028001d84007000707441c09401002110955100240850b0b404d10414495080110219500e0f090980201c800000d07502820741c0c0c0c8400244080141039082c410078666541c3e00d220100018031020003d601603144402035603101c04040c105291000c0300a40003200b070150030000780503016560025038607616005000203803050307100d0412048511801d00e505034030000d21000810030f40c6c02200021301498081e030b4200810b9884100701d07090036185010b8541c3c02000c940010b100c1d58032524a080c80c042c406421081e03825594000030050910a071030041141c0d4481114082030f50f4103100700d020881d59032500c80880e400513214a2110042601b09090804850550b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 464614595 1250 464613345 464613419
    0x5030a080c1c18050607030c140a060906090c050a0f051011030c0f070605070305030412030e030705070608160f080703180803190939060309021504 65
    0x60b030b4010a00d4021402c20301c9003108401054805600200301c1e9442445402003041e04111081d0781e00981c2c16110001e4a035615140c171404198580402ea070140302d1705203440001482030103000842c40c414200800c5161403450040f07a40501908001c1c018985084100140c0311403140d07900c11a842034071100354821106c04200c901c01c4800e000030256100c00265041c1003640052141d43c0c010012003503500c1c25455060444d40383c4036815010300041d100f0f2001c81d0114600300c43c034402c01c00c0b403130400280c0061400c9195082d500101410798464001c40c80400409422440d0380d51b02c2640712080c0c1d10110390303605001cac02140c46240a41c040045413030015800c0d6003e5030056141000c1c05240714044200c61401d1803907903000b1696545140d505d207a103003014002c11c0c040c1c000da5a92000300999a41c0d01151038691034110248484070221801b2000c802c04405401c0f403201404e6203a40c0410400d80c64014401c0d45c0465070f03441c24042808001c200145840071044042140019151102003070003805 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 464615845 1250 464614595 464614603
    0x90e010812181915020f0d140c03090405010f091103040f03120e1606090506030106390f0b13081e21060102060a021201030b06061b0f150105030a080c 66
    0x109501242c8540c460114940111030180c10301030311190300302c4442c050b48148664903606147c06903c04100405104007103c48420080c0c140842000c00712270034421448001401e59000382c0c401c8070b400d400c2c1d51061018426a02038a4a1030038039159131840c50030640e661440d221082540601044040c40055803403540c2a08000e052182107000c440c001424900c00d60003801003407080f280810740380c883c00101c1c1c0c10f240d0141d9048809035211840003109204030903c6141c10508404507007103821851213810f05d01c1c2160300580718042e4150741c22981180c6840d4125001c05407102c2084d5001240d034000041c0202c08a0b0748107222510080f84102600b48100c81d6401214010103c0000444c00400d0740c9092040351881003000f40d00b11015500c454100c10200c0c891080307c000f841000c400144081406090b40707542084019145c6440c00700e8802d5491350004541c11050680c0d000800000502c0301e003003202110411b85142550015450f040004c0d584416004d00105042c0c004a045411084180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 464617095 1250 464615845 464615869
    0x11407271a13080c01030605030705030706030e0319050703080f060f13060e0a0f050106080906071b060e06040c05120c10021c1e052502041803090e01081218 69
    0x341c50001c1e8070b529062501d407100d440c030006038002031911f4000034079450002406802c5940c0034002c3d00f215424240100c1c05003404907500c2145110400101e100441c13076040d49201015140e83d00c580b220545e00c0e009007419005809178002c0b140001c2030120030364414296036540e48040b1186982c0d0581405e040000d070009500181c61613020a00300402da080b0303500301044907441c822080015a0f01c2d080c0664481400b0b8a54135805d13800300300000c8045008804001142c0e110f40018003400b4215503c0078183c0700d5038005011590425000e11082000e82c5500e500644000c5400e01e03911240130039072642d69505c000c00075104807030030340308403140038028841440400d020780c001a0b0f4500340d5490180603031741404031010315403081e8503115010030310030000d40b82c080301208001000d4040f0580c44050200f0001400e9a20694542c80012900502161040428800c0d115180d00314076200c00e80a0b5084160310444135900450007281c2800070450444081e04669182683c05140d40f50100d10010141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 464618345 1250 464617095 464617117
    0xf110708010617010b040207050316110604030311060a0e032b020304080324061602010212031005040b0402040503070618030b0a020910022109040e011407271a 70
    0x1055000c902080400c244244148281d002170080340c0b1210103001c120f10510402912603001880400c0c0040da01d450341a1040c1d0044030f81000c4240042c0000f006903115500403400b0900c1c044451080c03045c1440103651150089000f0410745020002c0f1a8807403003144050681e0344600354032442d0b05044c4242c3d09032400c1c00344008641302d141c40e181055043d84262448008110200140403910681140d5280118009410b203400c0c100e40804040a81002c103000f24154000c1c1c50708901c403002844055482a0060100e111040d0300c5d0006200468001d070410a004138010441031019032000600700c002c4507524030b05010310a82c40b095103110390703030309800c0200411030480c02e21111640d85c0d0050300e4441400c4440c0e010641d60750350107981c0c03108241303104c008031001442d215a88074000d401501000b440070b0b00104103070007446440d508480c0581d12400c0400c0905051105036503101580c840542c0c1d41e0000746130704410125103000c1240040c0b06242c00c8098580f15000c80d0000398064540d0300510b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 464619595 1250 464618345 464618351
    0x50a1203050c30040f0b070201020c120d030b0105120103080c0a0501020a0e04111911151303090e04050601120201050702100905040b0d0213050408040305150708010b0301060f11070801 81
    0x1c2c290411a407801800d0b031107a00c40300104035160f504091000300c40880b000441101256850022020040d0b044040140d0660046d07841c030329420784406050a00702510b140240121460041001c3c040795800640c00303041103000c2c0110310180c0281080d180c19660802001e5403500302d0103200341d2070400e2001c0010a03650001c5100c2155070341189003491101012181031100d0401840c030031207140140390514000200c03041101100b41d0081d40380040e9070390743e002580c0610799444a841c1d103100090300ca0702d500343d02115149042c03550024085001e4180d4021428082c02e098072080d48c3c515041c01044e8062101c0070710302045a000c1d00880d00750030350203013443d1204080300d900901864840c0c85040e000301e040a8070035549241694005c10110fa000302404101d403002e00501d001042c0051049a0241c8200408000b04004015107003c0302c42e44082c60056150110b802004124103a010414030b00c401c0c001480b6040d0080002418000145044072920304640c1041c4c4c54503105034040f13040c40d40303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 464620845 1250 464619595 464619613
    0x1704020f0604030b04110108191a061206030f0c0306220c0b0c06060a061704081b070303030f050f0112020114160c050303030c04031e02031f0e07050a1203050c 70
    0x4e024840c0c01d2003039002d58901400d544100006643e013007011503070145003011101e000b041c400751130761121110b2409460844004022080402c40550241001c007900000f041c00300701c3d041c607081141d6240c010460001c1e2988010320402b1999442d000342c6030002562940c0c003038600c0450800103000880303401c00d8210303401c6942c4850005640d0702c02c45158030745000e48000102282400c40c040c6080f9110380e40d40d5540c000755681e510126840242080750807610030490346090419000f5070161b80c50043c2d010b021224a1031801400b00d034010b98003c2e100714246401c0000c1005e000200741c0c1120060302c0e0300301e000402440121414500758100203c201c0c004500d00c083c0304d40c4000c8280710280b00e0307004018080c2d22001010b980b400300300d4010340307940410041480064649a140100d080300c0c00d08983c03a00c88268002420b109828418440c4c4480040c5840401001070050400020702d040142c1000b5040102082d0f030944540a9001841107a003446001c051041d401c40d55265462015121403039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 464622095 1250 464620845 464620853
    0x703020c031005090d11100b011806030b011d0321071406011401032a020f0613150903120c05070b0f0405070f060507030e28080601060f1704020f060403 67
    0x200540b0200114802c684182d940705000d9180500511042001001c0c2e00c05502100d00140c10443c25a032704010080c03000d40d24400b00c8401610190205480c0810104d0040e00010700140c403403051000040c060031094901d584000c00d020380116001820b5000130b860004501c2543d200e9080010003009107105201c082c0f5401103801d0341a91005081c108080301200300440c1a54140c100403800f14440003c5500c1600d0a000101d8189487d8015a5052010003001c18103100c0111042e103207104c6000308070800c000041e4008400c4404400040040c80425180100140118100c40015036034038041c180031039001c2d00c29a608503603c0303150b914540c58200003040300c11034103603000c640501c51000c02080d403e0410f0755440a45021383c2d00d560601e041a1401c4070148403110050740c0000b844008072415290030001642c84023803c040e141e14040c03418412070f1810405078807200c01c0017451060340009550010001c0c42540380f81216410b01c1d00e176030000603c201c503004d16071540028001f40c000200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 464623345 1250 464622095 464622101
    0x40f3c170c090f180a03030614120303040b0a1d1c050705061519090b01110309030a03050705030c0d080703050105240a11010507020a060612020f060703020c0310 71
    0x20300d0358280d0020398400048081a514145452070a82c80742d090b9001541072120114015403100b01d200c0c00c10405a08082c80a0a1042001003900020745580040c4202140070075120901c01e020380d411440320200c0300c0813039228000680024102c1107840082030101410b6040b201c9010149802e00607000885500c0ca0382c1c071300740080f070f5a50424039003816600c1c0501440c00d0351125030b0800040c10903960780d62150a0a03100002006500502e100c645081c0e02060850f0300000d084104000100e00c480340f400509440b6503030350f00450035442005841216180843d0407200e0b00d505090241e11a1001d140c483d045020700c2241c28810f2189084151a0350f40c03010406004654985040180e0303602c0e035041c05040038106640d48803001a07481c03c02c0c00135040e8001016911814601602800c0494004500356001500c89100582c440720804040c8a55445150001e05080d10380d003100300b1160b07010807003540203600902e11a501c04146030013410300074400f000707206034000c0940d031107401099984001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 464624595 1250 464623345 464623349
    0x6020a0c050d1101050c03010b07030c140312090f0d05160201120e060414030c0c060c160e0a0e0316080a020f06010e25020a06020a0c0c080d020d05040f3c 68
    0x40340d0708000115a001c1b1400d0304980c141c80500e0001880e1884584090390139000b5038504031100381c5d0b2031214050941090000c1c191508980b4040c0d01e00c0d0500081407440c0c40d0185100344110b404c240f280c80da40c10341040c11a11010204904405045503038001610742a007641280b480b034031f0920b5040300340c070765001c07031140e124030f103c0e000300780358010a8481140e8a009200b00c0b01c3c1c00d54003c5001e20b48518024000d00500821038003210388000c001c5400030b4061196074800b0703c00b00858800e001200d41039009907004030400100540c203141641070b209005078100300016044120029075040000e20a0000840c0b00100fa0300701c0b01a942e54007030742682c0780c40882e40b561142d00540f00340040d21607100d84600f400200f650003131002840c2901c940b402580000480010310080c070941100092a96807450018807491700a09030545845501034200040c1078610401c11400300401d00440e00741e0384e02c65040d00d4040810303000c2c004e04206c1002030381107081c0050001ca0000f0000b0042d0822000038807003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 464625845 1250 464624595 464624627
    0x301060305100311090402060c011401180e15091e0d0216050618030705040c1107080a05030d0e0721030207050901050f091b0f071209050a0306020a0c050d 68
    0x46256224821062241d1440c00f0080079520255403802c450300d403400300c090b005800100020310741000440c080c2e08440b03100004c0c0c0b00c008061401041800100c00c5085101c01015406201814100e040662102c4480500c40c0d0103038000004201034800400683c041d440e8a50004910030369980c0a0669038003489410364014421146540030280c803030180c0c40d0485501400c141d007881c0e8806014681507162600c910b815204480000665039218000c1030003055040c0c030b443d03100d11109085541080d41d25008081c580c0c0c02035025500042c0000205c403100f000f003200c005040703802c000b0390600b032915030f50141110fa003101c10303210603c03d924015125140d2013502250038950b03131441800f58503e42442611b511000352a000034250422134000d80d808a03a40420f002110a1b040526041c3d070042002c2010303401c00401d414082000d0028441060a03060401c00f0f0075a103044001041080c03d40001400346401084000d140d501408a510841398403800b61422150183d100401491400034155 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 464627095 1250 464625845 464625851
    0x8060a030602341b140d14010c0e04050f0c030c0703020a02101106090c1003020a0903020a060c05061305030a0c0321051906050a0902070503120a1d240c090405090303010603 76
    0x61484e04070f800c40714203c6100016546408071400d040000c000d100c103070243c840c02c220714000d440c841c0d070a00c11046150030549407001030011100a220441d00005d220700609040241486401450320007039a902002c000d440507580c500c24503049007000c01110009401105492680d02030030740103002400c14000300d4049030721580ea0070140d1030b0f48003120400a0340001d80d584520a03010f2082d00200010807050428212440e0ba9038007140101d80355501550020300c011010400b0080180101d9410070303070f440030701d100410781911010784030b1052000e40014070401c400150f0406004030700d05a1107a40c8403486150440c1040c1000c03000e40402c6540e8401241c103600c4429228003580300f690140e41d0090f010584040c10903100d0002907009190554441c130060028031207240f8400442480340c5c0801c10042000aa05507006001a80c6840e0f015010740103100315a0200000c0380d00504400010300740c001b10360b00d400200c50b809115000015070054140700420a203010b00100440c12514940d07010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 464628345 1250 464627095 464627123
    0xc03030c0909220b0603011d01050702210f0315031b04060602010c1e030e030307120b09221712090c010c08030a15120f0201030c08060a03060234 64
    0x641108104a01c003000c00f24a0201a030001c200c41c503440c503600020142c00060541c12088141f4400702c0d2000000b1910380d1100e082100d00c56042c00741965903410200801c501c28403260700c00c00c01d80550a0040405440400003854103251100e070300100386009800d8800d0001088103503055041040003ca009a043c40c4c00007420a105100341076444440740c1d00d81c07200180c1d01d010103103007039001008030042607140c0d1190000ca680a0008501074040e42d22036254001040c514081a1403403500b0035485021403108102d0b11051150b1425031444145072144903840032860960042009050703043e00c00c0c1404105030205264020302140900490421608030328007140045451000c0c0443c01030081c0c80c107101090340e00405410454070400600f060102c9503484000c188021510b001c026a208102414548155605032144614120151030075003468038201c4049403440c40c26200083c10036600262078000c2006000d80f04842071907002100d10038041096540910807440d8500341c48400c1c01600d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 464629595 1250 464628345 464628361
    0x106021e0c0d390513140f040302011a010e010509040603080a172202120705090403050a031a01200c06030c0301051309030e2b0308070f1803080f0c03030c0909 70
    0x8203103001440c402081568103010a203c0f000e04c2a02c0980c07112529410f1901e81d4044c45c0111b40d00c01c407001d00a0143c146814103009095840c626268070241d000030750444401d981c4400c10800c010000e090041d6100c81110100d0020611940060507000000c2000347e442507200002c3d04021079503800c01000340c0c4400c500b005000780b914004106140e80d001c0301d40014200641e19406185100c0260391120b56580086400740000f00c1d001c4000034000221008050b800d84541c03032000c110b00c0440d85112416900281c900c0050b00820400c4005a6a02c06012030041015100d0324002409082d101c3c14400c007480701c01d4000f800340c00d104030201c103086e00d0060054415800c6858061384da99034103200c140e052100c903000b4240054184030450740d500d807080744a81c0e491400c05200b40e840c0c8500c2e240c075480c0240321040041480d010800304400700c030800541d100841066035041024107540305000340040f841d42c461843c20704624000841040010000c40c000f806822409aa42541c00c2e920b0b218 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 464630845 1250 464629595 464629673
    0x40314130b130b03013006110a110a1104050a0b0409060c0f021906050c0714100e03130b0901020c100f0f030203040503070b0406230910050106021e0c0d 67
    0x1503c3e446c400702c041400110055408000340780280c3c83c8440c4002085601d030392050300d061660505220f031000030601c0b40c147e4401e421160040c2c9420180154203982c4e600c101102c00305c0c10b07165100710b45400220310080400e900a028103800240100714402d90342c80c2050207080103005c1c4602041400d00d51000050012500390031103042c0c41c581c010200055500d40c0300800c00a0040c0442010600c40c550000740b401140e001d142007000004c0151007512404038060300c13a9002c0200e501d800a0103000311008000e0900800e6514040c3e50790380351251800100c3ca41119100b1007580000311800228015420600d5021785203251340da0440c60f001071304400d81c00c1c1d1109580042013a403040101801244c252004c0706d812a100b0320b0042601c02c01ca0f40344411280425480086030a1180305001419804000c8001c0ca44000c04050180798541030300030f5101d0f0503030702c9500c15500d4040300b22861120180840d44100c0320080c02500c0610450034100f5102044011a82c1e0320203801001680300c40282d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 464632095 1250 464630845 464630849
    0x3050d03060b03070c060b04050f100b09100521040c0602010e010506010c030c0213020d0e0f0a080316271401030b0a0603020d060321170708040314130b130b0301 71
    0xc070080c80c603140c1d1340c400c88034170140201c242c5174542d46e01c100d84070a503614041c02d800781540040d40030803802d00703060904040106501c010000310040111215035140d2102c00e81d614041403c0c42502c581d201202050a00c130b41c206603045d5900c005041000b00200c0040724001da070142e90007002540d030940741ca14200d40041da4964003003010440c482000900c40c4401140f140d00c0985005d02808030030103007000341c1e002560400801c039210103650058007020846082500c5108004203486141074451808030321026101d440c00908140c0020200340c0185117840e820426005c43c03181140c40c1c150b17582150300e003e001d4400c4d000841c08110300c040d80b00f80140d03d00441c0003061020348600c0d0080c150025444a0981600d241c2c030303000000003266046004086072072151690b0011100b180c40c00400c07001e9201c0b500b03005001200c00b4015120392000b942ca500543c981480300d03c102000f42403405170b0251500c840440e1920310008074008503071501070a41c0f018810071415110362108040c1150703002c24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 464633345 1250 464632095 464632109
    0xf0302100c0c0204090311060c25020a09090807200109080a151a0a030c03060c0512010302060a17090c030609070b0f070606050a0902040e0a11070308191503050d0306 73
    0x120b294400b501d0154461001c040c03007818000038282110701401c0c00d2903001c65495207500008100001d500c14070221107503034510013154503002181d5517030011b0810641401010100341c1d13aa0700c09810400751000f250351268002d40000001c3c582620355803640745500e03400b41e00003101510300040c0050b0000d1100099a40500d01c6103507650140d010800915100000e01c0d50050a641030288540320402240040c40c0604120f8104a0940c02c210060701c1c1d04c0d22840080040c208842d0344181c0123070a140341540e5040b0354160b5a464aa9400c4800c0100c1400d0352142d0900c103c00d02c001c600c1c0005149030f4440056003952480e0391145490f07600e03038440c1c0c41081d071400401c0240410118505000f031540030300c42d40e00081ca40e5100c00104c0c000d034000b07801040b09030340d000800740b21454002e03400d2035114849a02c1400510b1181c5c03141344460054150041c248881c3e000482c1030140403d1003840d03003c007285010048015040400744448619101c1590380307000c3e010101c01e82d0b61103401604d040c1d8400c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 464634595 1250 464633345 464633357
    0x2090a0308091011190606121a130804090207020d140d02120f0406030b060d05070f080105030319030b0d02120109150c230705060a0605030d0201092301020c0105040f0302100c 77
    0xc40c4400b590b0340c04e8585c130032580946e4400d008a5042114241d0b5201140a10f4000200400c13107101003040c000701524001d4209401c1c2070820002d1244411101903550051001d130701e520440c800b165501050002c010080d400d0030400c1049400b00040388035940d4215822034640c0305e40c0500d940080d01c40c001c3c800c2504107040000f07010301400780d04002c0b03030000050441da2800003000001e904485061b107440002424900e16840601e5012000c44d0142c50100c026501d4408211030400c00c00001c042044241522403694800c19644c1303145506015401030000c555000800c1c10302402440081070407500d808840750713003041a000c907100e154031082140d143c52030306862054000904a02004134a01540b80030001080000c20600c1114059845400d0229086041401b01400e0449045800c408c40e898800644045032441c000d1400d0040034090b045801300040b991a4003900c9001c40100c5150300380002d00c420000c100c503a42811a0081c1d0980f005444d500380ca40c0d05a80c1516a8400040c803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 464635845 1250 464634595 464634613
    0x1107021e01051801020304080303041a090c0a0311040f0e0105090d0c05121e0d1b02010e0718061a0a140c070e07090806070903030f052a0102090a0308091011 69
    0x30060020352503c02c05004982c1456078880a06103598011075040300c2c40d484601c81d1f24200c05520980d20f07007003d44500501000d415403008541c01e0161840041d05407804103801e1501c80d201d5a0121501c0c3c1c0c50700c0424000355004049242c0602415504d420713003441541111f00314079104006075400664041d02429910034203c440c0c0c810741e0040d000100d9003503064075030074021841c000000d110800b0b85a10225005400d00180120000f640d80c501094ae414681e00f12480c08003c80c02c01c05071182c0310316850520140c0c100b45c10041c4074941220940710480c5041c062405410006044580030681e90360307003c02901400444540104010080c4a6004038021701c581c50099242c16840b8001f032401603505691090070900d01203050382c00802084880b0b40500615900580081d407501d032070f0422502e0020b0b20b03c0c400003081c200c00081004401130a03050005501c0039012140320740340041c8100402c0e622820701040769400424980e11a182c040a080d00117030188941c0400c4000c00070141c11040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 464637095 1250 464635845 464635867
    0x1050702060903120304060b131109040504030203090a0803030f07090509010603050c191211090a030807020406030501110409150605030703091b15080f0c031b04091107021e0105 78
    0x41c02c001c061607414040c940d044050400c4400145214902440010454500e01c1d0b00740007400310b9450003503a00d42d04000e503405818940703500302e580300c000540340010f0694990404a0442c028069416842209010001a055030000c050341c0a8030350401e0310341190312850010ba840c000c441c410030b9002500c0f280101301030741c001e52090354020b04c100c02c0c00b071030507904104804a1001e14030020300030404660820704400340a02c180c4000c00201a40d21389000715180001e038400000b440000c5c5940c000003220780c215200e1f50480d42c01150312070003e110b481c44000038061140c01c24018ce060452405099102c0b05001251840880f4400d4840c02c0c81c0d41c0f54000210090f03d82d030314040d03503010f80d2440e2031600401100395407002020800c0d05007002e4400a140145449006442034416842050912890003008000c4039004881040811649030801100c0c40c0540141d80c032100c1c615141454800014880b10000c01e1150320803940c1d045400d01085001d000302844040240c00501d041c00310513110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 464638345 1250 464637095 464637097
    0x70515010609291b062a2209060e0a050c03011223010f06090204230a1211012601170106080a0f02040c0525020d1506060e030c0105070206 61
    0x1002e086070042c101c994140c1003205075501c41c45004c0c0002c40040115111100c003440010342002030400c1c0e1004040840d400400203075000c100c41540003000081003100002101c0e18120034030400809010400e544000c54001000c1c0c611811101c5a181c000080c00207465209051081f00d5030300781182540d0030603502c0780c0724405014080302d0700451043d8501040400c0003007504210703406400458001c1100b04600c003034031200e078807801049005020a005000501420b10341d1321450070042c2456044c0e00d4005042115a0750008625000610f64076003440b950080803011600207032035043c40902080018090058001460f810f0b0640c2c0c1d4005000a42c122041007902a41c4200049405901d80a965080c46112a400c481c0301c1c00b016945000c500741070048584008807410310350304164031a03508071941e02000944841c04c5000092902c115030301c0c41040b074040d0350480030001e882e502444002009250300d00841c400325a960f01d20711414640028000303070809041c0c0d01c5509204081d405d000b05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 464639595 1250 464638345 464638379
    0xc160303150b0706050919020102060a23040302060717060d11030f0d03060510030b01020d030905070b041409090f0c060d0e0a080d0b04050f040803040303090512070515010609 77
    0x41c1c01114076000808091440c040c049440c02030030000350754140341641c5c61402c00d24410b2076800301c0d506204000540e03000b0841c0c7d680142404400328814402c00300816080300e140030905810000c0b1000c1c0014954005041845912135444500016100c0040d221030310100f00c601d1035012070084124400100003103000c1c0c0c050b10b0f0180c00c0301d600c070103100c0400317040426540b2000300203581d0b071100b00400c0c0740050112100d4007160030100109800703400000d4950044c0100d04080c99140c018150403c80d003017100c100140031106046031101d440d842ca8140303219400d0055841f0300c290b400031800c0b000b00480c000b15003c1411004040704030b145401e001c016008040882c20340d580d1100110240b91040c0b008000c207074890a621503940c00002600c0007164000c40003580605d1500040040e2105281101d58100d0381080200c0d0712640c0b2840c0c110098080e0a000400f00c1c01804423b511043d0f800703002d82940380c8540140c5960300c1003003101801550092040d00c0c0014000d190400030010102c40203c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 464640845 1250 464639595 464639621
    0x1a07060b0d02062d070b01060507031103030712050a1505040e030c0f0307050714030604080c01023f040b0c0304051c050301030b06040516030e10150e0c160303 70
    0x1800c41d4240e00041d4058012040b010960304400300030008061400c2d8802d6042e4200d665801c0c100700c11074480745000d86d0f05003d03200501000240e19001e150244a04082048003c411079a80c0d10746008024240c100d4200441c0540b414800840c0104c5094013581040f00b10088041091034038200030000984820002119180400c21211800c003505001003d0480d1100005507500e0820313160241c074000c190341c07021169602404500c4502c2c2c1c1c1c0810340715009034101c16081d8450624505042c02441035a03000d00c400b80c2e5075140d017803045c1da00e001032034070400500c01c0e41112112404003e44034100100c40003003d13050080002030000c20312201560b003090185044a07481c1b212499600784409001c2c0c0e2800208a000c8010400c2141055078641d001c84251800d021a0402c206c45010340030b4400750172418035803110b42ca40a01c100810207610581c0c450709090045589000024850514500440311a024880000f03a1030306100070407581d40003080701e000d85100901e601c04500400340d12080da030b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 464642095 1250 464640845 464640859
    0x603010b091b0408032a240a0e010c120c030207030e041a0909060406050109061413020910181a070b04060609050405031908061003050a0b030106060f091a07060b 71
    0x120750904200003901c01041001e140e002240301214030b001b441041c40c010083c983c1d2041d203072580050103030982c242140701d1004403812a0307220b43c900070001d80356803051006503600c1d00980802c01c1e540f04400046d0380080e94070400c910384101d80118141d100300a4054045080015270b1012400c09501021001e90002158180300704090700051079100180c543d0401d562011041c00144030443c40303420b00500100c801081600d00e0180400d01c01c00c0381900c054454404050900c04d10340342a01290b10340980100015005181804040c000c0d880180c2d420450603225103001c503240020090841c580c01c403850500c2d0400030a950740501d0075034024821100140c6842000a40450398061345002d04d102d0f201458031003801c094512804032200048204110a480c24821251030f035042c5144004a640340100740c50741c0d00140200130b418030006941d095868080002006d980c004c400c4204801559208031003199245202d4110a03440660a0740e401c0040141c900050b50300d500818440320007074141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 464643345 1250 464642095 464642099
    0x108030f03100909050a03030b06091804020a03021c06060914010b0c010f11040503160303050d0b041d010519020408100207030e040501030b061002060c0a1119030e04050603010b091b04 81
    0x30f0070039204000d00844580e030108410708105a014002c11111100c00e441190411442c0d05c001014041100c60310100c585004001c5000d548401100802441c0c024280c2040618048c800d80306500b1100800c3d07801a15180d00440c0da641603004180411400c10039600c2d40380d0031710302d04406c04e500a50303000501e0340da0781d03031404158620b40c00707203100d0794101280060f111450081414240341c0c400307a031b044030280100c2c003d00009800c80140c4d10960a52034000600e1901840400c0042a1240d405540c221011801c0da50b4420705420503807286e03801e0894109482e45a040c0e45060780a10b01a0a01d00e810001701118102c5142c1c0c0900f4519000345484034146128001203021200203820913111a500501000440d00348606100034a04003407000b0902460b0408400d1001d024044001040181e29410400c00e00010040c0003404051844203c68521082c41c0260604030406405030196043c440000c01518041c0300348440c1180c041c00c0760410750742c0d80740305680b841d289800441f400c205c107100c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 464644595 1250 464643345 464643359
    0x309160801020702010f03050f0106120e0717010615020a061122090b0105040f140a08030309030301030b01050a1d06060c07090501051305010f060e0402070807050a030908060108030f0310 82
    0x14a80203044a0300016918200c03800010301c00500145030300d051600b01018400da01e50070540060444490b0702c0c2100b0f48103030f29090f20019014181c1c3c901b406201e80900440c030039105541c0a20040c030603900030485256568003401000c40451003141c09070b01f101c001d51000c9030032600591200240251441e01e000c01503103010003028008440030401180010050260355864440c50401d1710f000d0030254140340c68864810ac1180d501e000345100034810010802e5071740c9401c100c00020b408607600f03494580c82e00c1c511003603030f070780007403100b51600311052000192508060100c40280d900826034510020814800300030451750141c5119023014007007201c105030031408d01024015007000c0e41c011940b03524000400c030000864280e85940716141c10010407800903010702e10b108a90090801c0358071a112100083d009019000020b0004c81000840302c04101e000310f1781051443c0700303468500c60140c8503819603560b10000d01071004541e004000006c0700c07015107000b841e44160340e07a588622180c0ca07002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 464645845 1250 464644595 464644633
    0x170402011701061701060503060a091805151b04241806020d0207080706053c03010302090a090804052103040605040e13030203090108070e090405030409111206060309 73
    0x4031820010319141d00e41000c488021348440c4c01001640303841401c50030440005071019420f441050002a5a07100078400c120721110401c4110380c20009854040103c00d400060f4048112800e6000d401007500d500e98100a00060301d052b82c3c410072031210326500c022020741100c400c0701000400d2000d00a040c0c0e00c09074a80035901c01404596000e03041603603035100040d00c0d01003280c010090300d1308030001c1400015801b10946440f0101014107140822070002c4c90a5007100800c03001c1054800310b104801070301148030045040302d1003595010201e944c1c00307043d81c1c101c4680d408004d2500404001c1002607107495400e505034001c900001240c0b41564080c6240b82d944241e02000100d0401304040200f1a02452035a90020020141e0305262140ba03900a40ba03210b800c0e41035042c03180800100f003aa40c450000381002000c003400e00c040e20704050030195a02c0c0c01511400760400d08000020600b0b40c140c0d000d95800c50312002401c121600c03400c1c01c00242d03802c01051006280304e4906032122102c0c1c244 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 464647095 1250 464645845 464645849
    0xb090409020d050c0126060114120403020705010e01020604030c020609040b0d050d020c0607051f06150305010f050f15180a030c03021302040303081305011b020c13050601170402011701 81
    0x2428484c2c0fa420015101101490604085202c2c0c4090000e01404503580603600c84024a45a101c081c60030b00744090b5401440090305082b1802d0741000201500007500c1030680e0000d880d0b101b04d006d111001241d54100403940280094009a40700b0010706000c800f038001800700900120f0382c1005a030100d406000801800d464540c00148201042e035010300c01031240810a8506c03924009558651315510004c0c0441e00d0540d12544007400c46502c001c0c0d01800150004400c03850300c0c406c111000401512081c01070f4032482032401400241890944031407107034490003a22039594244810188041600040c032405d8141914800f5901a542d940f900704000c2c1d4466454030340d1141c10b500500500306051540c40300214810002030000c290403040f00340d07000707040b402900481030080c58640c3c0588801400144030404181c084078403280c0204800641040650b0507001c007620007a040802d641d015203555010070105030b001109540340e546101d6005006040280039030300006001d5108000903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 464648345 1250 464647095 464647103
    0x110a0801020a03060f050306061c1b0b0d050903210406091e05060615040302041565041802070b180c01051b01020c0303040c0e100b090409020d 63
    0x51300c01840a50f143c000c0300070260006600030000c525048010804c241405154002d82c900c00a95101c00c02c100c0c101c0124083d43c0000251700080e5540100d69000e8100180d01d945160404001600f01c07200002507407202c11a03a04071351603000c1c03180c80156a03100060010b0b641151500008408030341a00c803910b08511040e00d0b44280b0100c60b00301682850780290110b413003113a0814500112921020580b410f4940403280040d03007074125482c03444035000b15440600c9034a94903a480351b0140d480b440000c54103440083e245213944805060440a1020741094030f6990540c00d10780d10310900d02e40082c0303c1c400e0703030105592910b5102c01000d40d46121b61b11641410940009409040007140c002030b0707400071102a8480c001009640c0e24949030540302d0703001d904000c0d0100c1c00089692079131910b003411003108802150b9881c0714010340750701e03580112804c0d500c1d010100e01c00900c0824480715203118030f11041d10760003418141000c03042c0c00c1d8025034905911607290070410002d6520107090580803885 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 464649595 1250 464648345 464648351
    0x1101060503030c1c0203040e1501030f0e010e0139050f04030b10060507050d050c010b0406080a02180405030a030c032714030406081321020d120e0a110a0801020a03 72
    0x511200c180f00f0340b503003804c00c0300715002032104008100c2c0c0002c8031038014100410036030590050800490081c102c20301d0850429040c0070000402c3d083c10340c0680d01d2030303104800a1100243c81900c60900c103a1000d070494060307a54400303911085400b4250807001c2850344c40c04920702040d0000d011074580150f00166040f006900600c6580c5842d040242c0050042d810614100703c1079031a001d88900084401d1014014005000203401c0400c1d03100140440008104016007030b00d078002c2c01d40e254a00707e400c074011501e40980d20000054032902030b2186501c44001d524146c01980220302600d841a046824161900d1542408040c240b0301c1c003041c0304042c0c0d0764148903001c5042801040f802010740c1d880c182c20400017403000942c001c40403a4040700b6940c083c030380701d4051715200c3d1540d2a01c11002d01c128060694240450340d012030044851702d1785544d0340404500100c405401c4411514082242d60f22000c3c40030002111400708514880740280030320080d943d10500c8509903800000042c0020b030b5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 464650845 1250 464649595 464649613
    0x20303011805010617072304080d08040c33110d050c1921090305013c0f0f021b010b060f07060204050402070809041a101101060503030c 60
    0x945200c1d100381d4038888280c20710182d494441e001e001d200340554032101104406001442840c0286051a18001d058900030059900e40501e220660031074010b60000340039a445403010700e449100d1043c043e0b03400c86c0d4004012442e140100c01c200a814101d01080d03800804c1b8441c000040b0800080c2d820251b44908660b02400d9017030604080062480000380501403007961443c81001548030180401400490b60b254410f0a1102040d055580317085800d0f0a11105400781c1580480c00408582c4124000d000e0b241e25203800c2030640020302d00320764842d20850190310b444061420003035114440100009800d114480b10701d01588c0d25650302d02095074000502c0d4103c0e56a000d1024282c1007100d00070096280500b000607900c0c03094000700103681c0008215442400030303a50440f00180b2006004555507a00b51030001d03440c0d007100746c400c3c0c070070b0345840c1e480c0205070080d07115903580100041c0602024071304500c0c181c40740c030401104400342d59a130b21004070322602c00f00010700040402d40300405a5039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 464652095 1250 464650845 464650859
    0x7050c0609070303050a21020a0315090207080a030506040b0d0507060f030501081b0114270306060109031e0516030620040501030914030a03140601050a0c060507031b02030301 77
    0x1d0050007207640290300410102c3e5209041e00c22031075641c54207540702c4022012060021120b100d0103040c2c1880081c10051544e05030740800b42e201c10350140c00154a952341e51600490144000191500300c0410140c07a0707d6110b54403041c2d11840041001801d100711a0118807200c1d683c1000725220307800343c20184800d07031300500c0e130104030f01e81807409005660501d0700c142d40b5880001780d65100f082440e0444441a1b00420100f2140010654203a07251a6026460344660342e0200c0c4a6004886c2450020064100030a52078459101030b1200c4034658a10350703628228440d5000c203400200070751044400098010b00200da001c280410f00840800d003182031171021100d042036400304000021880100040306072040d01c0458100342400507404001d41002c90b0000c3c103901202140740400285092466010781c04040000c124058404540e0f43d00d000640f160300ca0803e101c400b1608000d615000074403d5003080b9807201c3c3c5482c011880000d550704014000040e00c40c2d100251304040014401c1e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 464653345 1250 464652095 464652103
    0x100510050d02160b09100615050d090807050a080921030327010c17160815011719060f141309120503040516030b0c03090c0901090b0a0f0302010503160201110307050c 73
    0x107000723600756090021b101d4a0700a042e611400c841044030684a1000405009164040c5c8503078a400c50300b5200d03c4442072401c003100703902c170f0841d803442400701e1030103049500030030b80d000b03090440c22000852541d10362010010f14030790003c200540013003103010362085480081c001c04403007152945030348001600c030118000f08408028005214a000803c0d41c80305503900144d40d44c1c00c00403880d4150901c03081480101d8191101c5c1c07180f0f8154409410500401d00081041c50380c0030040f0890810240f40c9502005a42c0d040e2031165015201001c0e16101c0c0c1ca00c0c007007821601d02c54580f0303400036803d00d080e5290b04425050322010004194003004010611000307110318100701d41c692030f0b40112682107507031307100c000b41010b03280b01306030b02d40800010245174081180303540c0203600620441e070035a0350350080d4011348945051240185488880090104558140700041da9416125982180d5070400f03440c40610710310f581c2001f159203a41d54200760308c2400c0015401a07100b80d940541d1400e000306803034a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 464654595 1250 464653345 464653349
    0xd0b031e030c07141c080d18020f0a030b1609090f020702130c08010303030b030313080f0f030913090804150801030209090c03150703060815100510050d02160b091006 73
    0x2020380350320210125a905170440303140e60810301940301c014141e4241044640164803a0011007071070012300c0c0284d090701c01228454070344202d80058136441941d0501540a025100081c20345c0307100000b064884044c4240100d9400f16850013614850b900c4130b684c0c081e10380300440c40100c541c2c002404801d42c10107a0303034075401d000810014030501c10390480c010302c409014071000e13080503600d99511001c0d580c240304943d8041100441e450300140c07207080c07036604d4560042900d0142e20131922045070100d8040242d03114400010411034036803c5081e280805031580703030001c0316040c004220225001c005592803404000321990390007855811417041c815810b401804002e0207038051485c3e5102a500005ca01a0115920522030020f442e0f0220640251003140c21840860240151003607495400d880c800d4426008020300c565010b590b00c0c00d00c003400c89105081000181c0400000cac0c2c1c40380c3c542d0014802e166545400c0030109805454108400c0303001c0d511003440e0f80028461503203806080c000c80b00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 464655845 1250 464654595 464654609
    0x604050c070818040221090c040b0108040b0405010908121608060906130b060f09100305060a09020c0c0d030c030906050f070b0405120307180b0403080d0b031e030c07 73
    0x450400d242c0c60700c42c2c0d54090b002800300c2440c40895040001e45558055a141c50380814003101c03660500c01c03988070310341c0b011a000101c03440740402003101854280a0300f803094006031510941506e03103880700e0101140060045e51150340700d00a0900245d54040281040c40006010800d107081c01090f0104030f800c8840900200001c0d1800e0012950301c81e03040d02d130010300c205c420318501e2802c91104030142111640782948240d01040440c8500ea000d801031180d15800c03600100c0c0e9070100941070b0308483e03040e500940c112034691820b10a01441ea4020314054201c54200c801c0300c20200c0c0054980c0480200480014041c0380048041503046196030004e400641009403c000c001c4007a03030b0b11400303a5100070b05000003003c045401d0000510000d4110584180074956030710386044041c100a002c0b0300341a804a004003c00200702a29005650690b036000142d10321f80070820650b18060000d0a50140e414010042002e003400d002804030003040e4011005980c8a090f04ca41d1a81004242d40c410b030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 464657095 1250 464655845 464655847
    0x30a080411180a0902041508070e06040204120308070e030706210e031c1803030209030607020a05100b120708011b0903050c060f1b0604020f060a021c0e0d0b0604050c 73
    0x20b8803101088001d60f6110307010345000034000c0003500002d800b0b0a4031070640480f07a4800e42012a051101050260994400c0c5031402456181d50041c40b040b440fa62245140240c4064109170000b48181146070f007004d000d00e01808200542c80010341081c03078650119000c0b58540190311070803060b201045561038030103102000003c4e13903000625142c1c0304600400c01c02000314880110320044590000102942a02000c0c040c05c940d450040d00030f500580d0401c2c403a1295000050f41c036440042c0d07411341c0c95400030240440000d8840c000c4083e105d03860265074409014401903a50769800c000d41401003007034200201c0c007100f041400c130f800e001c0e403411007100f0040300403403e04c0441c0c0c0002c3c6641c000c86047d00c00ca070341d80201200582041c010031002044807103c2400c04648403500140c154082c60088420f5204071040c1c00400c5039034400c0e82c3d110000350300600c0c4090440d517000781e00000d45640d941003883d80044108005500d440c00d03a070045881000301014044d413030402c0c0c0700344e0350b210014440103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 464658345 1250 464657095 464657119
    0xd06060f0c050d30050106020115080714040f02030403080402091e04021912110301050c160210050409110403050d020a0b0a020327031903112505030a080411 69
    0x20383c66440801d162070500040076446a0000b0040801c42004140707003100304c1080019441e0340d03001e00001e12a0600640c00c0c1501e5511156540340300808031480701c00140200c5142c041c00504920740b16031000d038015510140c0085101c810300007944100c0c4030780c0c2c483c1c445181910401001010291461603107050701c0c089040d054440c010860f4001790102c40086e90600c0f621400481e104c8280c1010a0f00c112142d1400d04000c483c1c0850002500101c00910042d035030000030750f00314020743c2c180501100a6610982c00b500702802c041c400f003580d6281051609484190b5079040c0c0703092503019401080d001604000f44207050004007801074052000d8070440d04942c403071a68038200a452030114030747c000302203200c0d2441c40400555076603940b040061100a629110341e100c0e0003a030402c4050703503034003400911b40a00c05d1082d00512807644540d00c0c2054005032680c01c1204080f501603035454602119400410340802c094030100380c00303a907813600c58949172900b65880c40d02d551096010750801105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 464659595 1250 464658345 464658353
    0x72901080d050304060207050106030f06050c03160f0e04050c1c020a02030a0f0c02090c18010809070603020d1116051b0306150d021327050c01081b0d06060f0c 70
    0x6000024600c1e4a000780c0c80c0d0301e41e13090a100138420800010300d80e41c078103030002081010100c1901001801104200082c0e5100050b01010348000c030780031001980d00c4184e42c5940c1d8010a4001c2181003a8a080d0030314014800100e402c941050391110f00007003000c9068016264030040890300011000d00550410303104110103541ea01400d480c401c1400f91f074000705011140309155040c185500103140450a0528001c60421940030800c0c20315580d080c074007202e0440d400740c103a00d8011400c400040c06081d16101044000f50407500705004010744840c2a100700700007030740150040708403110111403025040e1030120300d482c00c03440c500740d801164044087c829075000b08070b450b4402d0420b20a0410460384100040c0714013a9044025482025140364110080581c1c0c0311030810f20708118200711080c0c0707180760720b03000c0c86020800501c01d500a0300c0d01c00700c5500c24004190000d400c80d803009000c21046825a109406c52444a104113a80303000070030805d0351205180740390000b1800d040c40081d03680c1d22 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 464660845 1250 464659595 464659603
    0x14040b031902120a0b0106031b02010c08060103020f0f071a06090c0d330816050d1b0b04080d08070318022206030b0117070f0608070504030807290108 66
    0x30081e00c10060780018152001c014003940b8542584170b83d0302034483d030f10b4100160051503a1221151301c0310b500850040040d0051040304e00642d42c580340e0394030540d95100114041e520000d80b107104043c0c203108042c2034101c0c10700034005640c03043c1030815600e003036a0111003030410010684c1d44078021140c01c0c49841d030f60b508121004480d4051001c510710703a1015604c0d1079010a05081a014541408500068034420010400b6183c1e80d4064071506908900c2000742003c80303010710340d40075645000141c000342c05200d40031150000682a44807059a0341001d290341e07040780d441401e0542150314803685c0380d64451030b070b81c0e888051070404010242490b44000003051500300020b000c0c9007154601c500b8181018010540a04514014805207490b4a0480200c070001c0c4242c0740c0d40e0402e070f0a00c0030300e0035000c00d0820627246040c0d41680118940f01084070700c000054030b100306100003040080f0100d45008018441540250746c00860103128221310440041c100d00132032038900307001005001e1a00081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 464662095 1250 464660845 464660893
    0x90d0309051816110309130221060612060f030f07091103041208090a020603130c1401080f0408040f030809032a0409030e0301050907030b13050d05030a140114040b03 73
    0x894100e40302c108107413055145214124030141d101e40307020104454840035800030251070450a140d4100e03034404c030305d103025190025034105070b0000d001d100c0503406c030074030307140307260f48040000c1030300c8001460840400d04206641c400f01045030030841c4103001d11607081c028107529032410350700701d4514903194460ba0303520981036454004010401c008a03541c0c034000c00411243c0d540062803113980b400c117010040c0c89403d4440040b1403c1006060000e00001170040c1c8a55111040e15668420342c0c1e6148014540d560041c421240510140800700c0c00c41e1043c034006010314440c10815a076a55041d0070185803651040300300c40c801c4200d02c01e035004518500c00180d003088042d07402041e10341c0700346000d851100240a20980661900303081102082000034182e045a000d1090000f06854103020b0042c10f0320001005025a4803502180760150b210b00029540244044c0c40054105108a0b00300d0000720f003030f4408903402405464000c824645440360941d80c10084000b04141c00700c02c08a448148404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 464663345 1250 464662095 464662097
    0xc051c020d1209140105090112140c04090606080c09040e07120b06151606020f1b061f120209040f02131401050105130b0c010e0a0c03030e06040503190305090d0309051816 75
    0x202589d00901c240b241c11202c1d101c200d4800e00031040c07401d07100fa40700580280c401d1008490500c0c000041160052980741c2c06170550245491902c07810741d041c48081c00c151051105144105440000c80c0300141e8030341c480c4c00d8455802c4540c1420640c2c01c11110b8107030501c5203210b25404111102d000c40030100c140d2040c40d8400d01c00f60b2518040e01840b12180030740c4162030f400c0704007100f900041c03001c080348a510541210b080d6658000d00043e40c81200d192074040e46081c03030307144181c080240c5032082c00e40750301521030500d02d91000007580c0030a01566405002c030b200340d911880700080381c8426451040c090300702883d080741428417039115110403003114031500481c000001111226100203401c0b800a80c4a241c00300c0304044914540b1240c0207520f488158009034900700311500c42d20700281103400b2180001d00a0020302c10800307900b00801e45890f021424041c04020300486030b1511219024114000d0700c0300310b04641382005000c9200c1c2071103a00240e06031601e003085018150041010070300d01d19 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 464664595 1250 464663345 464663357
    0x2601060f08090c1002070f0b040324020d06080d0801050319060902060708030702160923060a0e0114090f1006051308031b010b01020a0c051c020d12091401050901 71
    0x501c04100e051080c0101415000f29600844c0c521303081d0002a030300c04807002d1050f04484195a0b0300082120302a0f0b002c02071128061034070240801001d6820625440c0412000501d004828203180e411598030f603000080c5508602c4c1619031064000d0501c03401400b054001c0c0810039182e40181c0d0a81281c49001040303d23980b206820305640f224003d542c1d080303900080940c1d0768140b0620103580c45408030916025100d0001d00420254100d014a07401c20301051136200e80c1686100c6004425040108680e03048204071a002030b40f003101082c5c1341d009001001296864003540400c0c00002440100f10700505000c600c00c4c03224030308010390304608444891038001c0e21058600c01c0901c1c80c00069001c58158440031590346c280102c020b042031007411210000b00940702e03030440166103444079100064050324035020100400d05265405041182011022000d80011540060205681000252203074000740590134041504032001304054060454494007825031180024003a2092a00090402038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 464665845 1250 464664595 464664601
    0xc031204261005060a1e090b030307301d040902180a140112110105090d020d0f030e06030f0105040213090c0e0102010c030621021903032601060f08 65
    0x469803080441c0d5411426a8920019101904003418040c1ca4161140004010000c2c801c18070412250003480806044d0b03d4191a01c060741e001043e41d00c004a41500042148400140400709104242c0c0001481e207840d0b0150544071000d0110415000700900403203060111a410340700303408000c5480c1c2240e012800030741500c04555452035450620703440c203d4200500180000942048449024000382064903a903161020074510dc14000007514000040f42d0408040d442040201502c0300080d00e82203072802190301080e082403003400161000f005094490007095448003031300c080b01d2011615542103091886404a140c0700600c56144100d070700041c0c00d840d034640176055500030b014a44041200340884031002d03101502000ca058015440d100c030310032a0900a02c103140030780c0c038590324918080c00394200c2c030251101c9001090b684400d0555030045d000300076014207806540310303695000c4d00d00c50076070449031901e8250308104200c031a03020042c080d19034030007003541a141c02854031842e04e032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 464667095 1250 464665845 464665889
    0x100203121315020706110f030703090c15020601050f030304050102060f04020d080f0d0c0305130809060c0102030711010e010605010c0b100801020d0b0102100605031e0c040f0b030c031204 82
    0x200120001803441980b40c80140140403158054801c00b401342d14144410090040036032810300c034403404a041007a09001161005100ba03000b80078443c07140341c2c00a4034130340f01c481c190550031524081500592040d00140b000c1e003881c00000078101c406400460500e41403000107521040f00070445203847d0b5080d07000ad4155520307800e00014247c2c0040140356215070307082d0718006a0340f10000c0003582500704405014424401d00c541803081070100030382d4484994964070311900f9403181c0e030070b0f550118040c00544596042071004501821023500c5070040004241541d42c01d4400c00791191401c3e0f407401c070003000780742d8200c50000c2c0700c00c0c2d00402c1a240c95072070601080403e00a60004240387d840402d0400050447d82d0140750003803026006c032012803102800c070000759807840c0038503a0035030010030302881c4600e2440d049448500080090300e0400012001103402c680c0361100c0b4105c1c1c41d0712006000c4660409000d8001c0342176040e0040e00360030380030440c0c4074081d10491049012840b00c8000c07207a440303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 464668345 1250 464667095 464667121
    0x3030e0f060c031317040e0f09100e030f0c061b0a0509091305060a05060a080606100e18100e0c16020609060d0f051006050c0d05072d1110020312 64
    0xc0f0340c01005000c0c0c9090208075514a134003c0d0007030606116090010921000040c500342707116032400390003081c8442084155001800100341c0030b8440344800e000b500f0a008820000c1d103102d8a64070010b050a2815205040145241c8403004181181c100100da4007180d2000445240c1801581e0a04098843c2d202c03450501d007a0000c00313400c83c007a040a1000500264000310301964048500b44086500c40c10602e0b192601a100207a00c100b8009111a01c9030007016000240103000341651190788910030b43c00f00741c900c2114145840c0c045601c3c2030048a507050a01ca811000480010f0f0905110782e0340488c0c507480b07120010b4424a00800c1c50f5131156615001c50300c034403014075020b004140c1c11781401070280c40242c4148582019034200422014401e0b0f0a544195a1a900800b012510608292540d920120080d5107100c2e007140f0b1004a110300564082440101e003810306980e0210382000d806000321141c4151051080c41c2a140c8490f40c0001915105071000b5415074a0341c0310b040000100b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 464669595 1250 464668345 464668381
    0x4e01060807050c030c010c0305011706011206140406050402010824010e041e05041416030312020904020a02030702010f022d10061503060b07020105040b0703020c12070303030e0f060c03 81
    0x910000481c8005d0300019001500c910403a51400d10942e40c940d00d4019000d8007482c80b4204c1cad0303806034004001d1080c45040c0c1c410360b140164400142d0301e40301c10401d07054890448055925036182d17400c0c0001c55078000c107441d522140c4110603100d100c03121749500507501b10140440d0b04202e000c1440310038641d616401035410816402040308413148042c00b00024142c2103a05580510320002d000000d60b402107881e500c1000e20b03c0710042c209096650a440e0490490090800a542400000f03819140c0d880101070114198004503180c940d00d200060000781400703c000c0454020304039008034115045032003201e108000c0f400c441c049020346e40640c6405940c0d18500c000d5801e00700c000a043ca078122030303009040560b0b60280003054440301200c4091184c404001d0006000300010080b201110000d0711070b41e4071904c107850042c2400d0000420b10840288100c16a4200c444100f00f0150180b28603031040c40e40f00c01405c500680b440c484c4e511341c9001041614140000400108200603035009485 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 464670845 1250 464669595 464669617
    0xf051e041104260a21090906062a110105160606061817031603110703080310050904150e16180507022b054e0106080705 53
    0x40c03603590340c20383e00700d81041c48a40701144101d00d16048900390b00205103011110307000034020803025000204215010080d141d14010001e041c01c0c04142c085441c05258020103c1e9543c1fa00d0a10b040a00c1d41105810155041102009403c004001032a1a4050303224060300b4200580c50b400850781d01041e051051078010f044500d01500894a96040034005102e0940c2c94002480a40c490840104c800c090150402c001e80c018489a100c400e6511000c50f2900d00c01c2c075040c003031080b40d200d100d4a0081c0380e0300200c40401c000b00801c410300020551301d40051804907400000c0e41001d4544519541041c0c2c2c16a021549850410074107841c00c0159154031001100da00300d98541e40c08420120113040c07400320b42c242d03081c440450f17255403000a01c80501400e03008120521840e60321300c1440b4a100042540c01d1100a101c2000007500d0100188045a02c0203c1c240054003898607248888074922021007035032410000c2c0c02071001042c01c1c55030540f1001e00746070b41c054442c00341c01d6030b5900550b90008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 464672095 1250 464670845 464670847
    0x20310090f0203041211070b160b0a050a0c09030c0b09180a0506031615202407020d1b02180a0902041d152a040e010f051e0411 56
    0x120702407120b80c0294407641c0507002d041c4820300700c4181145c0c2011407000030740c5142e101700c0041c480b0640c01c80080500c00c48a046080c00b0005d50f07582c5440d640c8003103d1440001d81d9940c100a000b82090103901082180f07403611748512821a65014040121801034000300c00020540c0c00b51500d4403d000300346060603d0300301c15180b600a440e01c001d044200e4555000f80142e034800b03a0300d00340d4108410f05603140070340c0100642ca00500c003150b418454104d03144103000743c4c001c009070152050040030540c4401000302158100da00c86a00d00e0010040c00d884115072103a0074122000e030380320040c00040780b0784030141d1304504000d000013a48802c1007000b03058000258024080005034590100414078802d80d014851804951010300250801607090202500248401d07502c030301019a4195000d040b90140403110118400c00f88a6041e55084442d084580050140623070458020058018034151038041c520300d04200118920002003d000040c0480d03500440c68640e8694000700300a01050b4506 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 464673345 1250 464672095 464672111
    0xf031606060305150a240b0a02150106020c01180e011a0c1e0606120c040b1915090b0903030d020a0318080405010f0e0a15120c0512060d030e0402031009 67
    0x82c0481300016191240c0075032070040141036001c0f0001801b4010014800701c050784a02d0b12041080030b0740444030185c02c600030704010065481007583c056028002543c01450405a00c00c005060100e0803080c80d0402070301000e04204a079403040b16030f4155461021703d00c1da42c546c01c000088041c0501c01d40120f417405140e201080e40001d47c009501305c0c405841c21501d041d25000140204100704400e520700c580c01886600d12030303040a4003c180f04110241c00907100241c51102c1c000071301c0e82d58010401c0c815003004400e240c00d070310032104006440c407140c0c52407a10b075001340040e03924850301d0581c102864000c11031070740c124002e80c8035039140e407074192402d40900d01e01c0ca48500c90358032501441c0d0101c1c0a004c000e501c46032103505001440d04001d0700d40c43c0b1403814000ca1806170302911425400308142441d402001a0342d034040d003881c141283c0c64143e01c2e1003050356451404040200414001c02d90281800c020a501c03810405612500ba01c0041c1e07261210b85c41c3c10b049010740c1d0008440a4141460 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 464674595 1250 464673345 464673373
    0x90317090109140d030810030b04060e06010806010e0f1e09100e010603020f041d0d0908120702010c030305060406050a08060109050a0203240310050a15080f031606060305 75
    0x900038410266603041e0090f0b143c0c0421440140b00c1c41020f600400809110310000c1d000e484025040701406000b1251540c0da541e40746084c0d10f007210200c0d14244c50340301c1031440304400c104440c00341410001401c0c180d0704201403021100c3c40180500d01a13840030f004940141e40e10b082807440b500904003014120714184050a81d103c59440c40d001c11070307180c40320f15410142d041c03007200240c0e80d0080013000f0014081d02044090070034148401c45e0360b00c94011085000f80100b011a50492007030705e400d000c0b9403034405468140031404804084d00c0b03008105120040c0e81c81a410300040c0d5250a0002c4c10b1f464440104e80200440c2c0c100b20381183c00c40c90084bc682c0000a20241280e0740c1080030301c83e5075985101c00041c0d000c141d80043c501c112291107003080e103022084030414a280a42120108a80386590806a800550301c3c5c44d602030360340700c0d003910401c540b1694002404010b401802103541d42c1d180c440c1d582c410300340d40c07101c44495000369100300030480c0c00501c02940c0000c03c8821000c1c90940b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 464675845 1250 464674595 464674597
    0x80f1b040f090f02150307050a0e03160f0305010e0a0f03051b0f07230102190501090204020d020c011d06071b06020c060708070c08090409020111061005031213030206070201090317 79
    0xc0c0d128070303000481039a44145500486e0311407480c0d581c5860500c10035017001d0b90345011580005a04d4060705441d0f040d0800107905a500401402c5030080169155052180c00c4426210490256030040860740c008202c07400c4400034003d60620b00310b40d880c10344c0091840620205030107071115010f600c0001c01c20f000002110b00c26180c2840c2000550b030020041000d000007901607a5015800c03038102c40c1d14004c900b40e283c0000b14069000841c0141719940054105d81c85a500b40104035404240590400307404d1145d90a048010b0019400c2c10301802500d9540381401440c030410070070504031440d01707210800390045050354044019501c460b114405243c41e803004541c1d810010391038a000400540c890911174007455000500180390441107420f000161044031410b9041c8580b416813044091820810b0f0740c45010148a040d00c0c43e42401c04050500300e0a20000b02600014040780d541041c42c000c003681182d6040711056600c40c00e070310050f1101016548007a142c0100004440307038100c11301e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 464677095 1250 464675845 464675873
    0xe040e010c210b0d0201080c0c03070c03060b01020c0f10050d05040c060f091206050c040b1201090b010302090609040902010c0b070e0a090504150c0201150803040906080f1b040f09 79
    0x820540003400400b150b5004848400800c60380c09001d841e00c050140d4041d020454201d0302a500301850320800c1503032185568440c40c02100e000c1500d00c0708205010301441034200307031042407000d4075941c00444c0000744c020100c02080c521070a80001f4100d0300b94080c800300e4400080c602020720031480c0500745030125030701d80d11844000c50600954900d4030f5208441d2981998200b0b030b921a1a8030300c0f0344400d4010040107042d600780703120400020034030100700d8010384502e604494075003080f58148680041070b50f4440c00910b0504d80107002c5180e055562000355102c21301c0941d0001607481c0705000484960382500e0002d0214482d5000b800041544041410340c2144240c4e100e81556648030202400c54408560140020440c9100750301008510b4202c113030705032001d00c008610300c1c42c071044241c00300701d05a11242e015032001508000401c424060b48008106078000352440700016101d003501c0303041254100207040c9500c0403200041d0f070b650b404460100034400081111030481c3c589010519500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 464678345 1250 464677095 464677127
    0x30a021306080d08041505090a14071206050709090501050607020f150f070c081b2e0f180b0405090406060915030203011a0f0d080c062d15010e040e010c 67
    0x421817418041c0c2c91b60240501641d100c60080c031096280e901d4001140302c1203010031565006440002440199481100b030040303000780d80002e060304001401400505059103c41c441c1400c08004004035510181911815901590131101c200030b6030000445008030446a00c025000106020252600e032078041c14003241b088011138681c13034035241400e5032402c042d1501003807111404170030103030383c00d080407600b90182c4600804400300b12003d40a07145450a0962a0001105d18406010050340320740390500c03800c1800c00071307040b0506100788410244110700515004240640c040790400c4100d40c4400d00034003918208226880c2c0391091001108440c0c84103910960030301c4000d10010040680511100d00010300b806401c070040c409000f01d51130071140c1514a0341c42804200c0c082c040510203988501d06000305024420701e240322804c2320904083c084030500008008006030301b4688002031003511030900b48a042c0340c52a10005000d0082c140084000b5400e00c40102407058009603006200ba00e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 464679595 1250 464678345 464678363
    0xf03090a050d02190f0f0f030206070914090c0a02030c010905030a0e180610020a021c050d17070315090207121e0905040f0204170303091506030a021306080d0804 71
    0x2050003284c0da0401e40c10b0810904107540000e1307000421410541c0307250b511a0001c1c0c00701c0c4900762204900401c1b4480141c0158000c1c0c002c1103646039007c0303001c6000c1c0480500e2010b550070004045200000010a104141d00e00003404140241c000c0041d2801034030300c3c40007400341400c64540315842341c021452003030210b05007402a1405141403580c0000042084456103110fa80d038004020140c0c00b010340481c00d50160011500c050307100d140c1040300145803842142082140ca1130060314108070401810100000001c029001d9105440041d421070140e00d80890440038000c21340d80c60705442d41c4050038081c07001030f584040000100181d00070780c000d602c542c218004c0002100f200b04080c0d0010200086080200384a81d00c0c060f030002180081d0182c005091588401d909141c0a9140208207a00da001108008550008100f0400c0070144c04040c8030f1607060010209988400c54240244107004040740855500d03101d51101c001080d1640444a0b1000d40507005414810240c6040c0d4440328 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 464680845 1250 464679595 464679613
    0x6060f0d021203180901050310240815011202090a0507140319110c0304060302030a020714030c0f15070e0409150b01030b06070c030b0415051510020d050a050f0f03090a05 75
    0x2d80041a5412148064040c0c0f00800780103030034400034050301180441d40c8004a120f801d001550000d0740b0090408007005042400e00c410102520000c141d100301c07240d0300ec8a08000050f166180c0d466003100030048040b44d03680f66000f0580700c00c50501c1030304140c540d010082110000c415441070442c40a048010001121038088169446c0700f50002d006540d401004100803071403107039004603844000c40c0c6005040000c0e50341e4048514084145200c0c03a94400300e680810010700b44040000300c04108024901c01d501040a5015a44001d2950003440302043c8120150740716038000200d4194007e45c1140801d1a01c036030f48006168000149000918040d520f0310a4281081110407054002c0001c00c0a103203155640300c03804070001c1c01140c55240e101000d24146d0b6040c01458042c15074048116400312145091001074818415504215032000c486543c40325000300441d038480603a1303e04680d42c0e0440c43c0c011601441502c0c400304a42200004204500c0780100c1c143c6030243c4941300b5500c1d0750b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 464682095 1250 464680845 464680849
    0x4030309271a011e05180102070b0c060912030402032d0a0308011a071703040c091e05060303090901090507110a140d050a12020d0e031605060c0a0206060f0d02120318 73
    0x100c0f604c140002ca80d080140c11800d070040c030700c442102001407044900715511075041e900140c010440e1528285d00800034440c14880900990b1011503841ea040360951030705030006030b50b80c02c8242020742d00303000641c61a1001d107108080040b0400f076007812030f44c10b01030a00e001030554200740709002c10502035111a0414031040c0040b111069004041c50010900344038145484e60f1002c1d2080394100c016100c0010541518095110394200070382e0081c0c28061012041004e4903001405584a9002000764408a541c1c50544a06492000c907000411b641c41000681e02480c1a08009803988112103965040014589480c4120100d13403095a00040caa5103050f9800d00420510034045808403402c134000d5913032540500070790102564003281c0e1005411030306086a0003414101c009103980c0800c2d909000b0200015078110058001444c5025a810002522203a019020900c00d009104000e4410364807000c008070030a40081401c0345501e054241d05649611200000103524802c0c000001c440c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 464683345 1250 464682095 464682137
    0x1e1a040c140607031d061608030601030c210c3b0405060a0312120c05070201020c0102120711060403050111030a0c02010b010c0b0a0f0507050702130204030309271a01 73
    0x31913415128106540840c416041c01c94440140c40c0b074020400740061100c090344800001c8134603004008480d42d03420104c00040684401100e5501803044400d0301144c40096031206070032440940c01d000031003115002e4100c812180c20440382c0303001244117202d01c034031412036909060403040b848007000c040b101030014041900c004a0b010b9911030b40e040810008519000e000003e10342082c980703940da07000091381090403a0003e22207a00042d1002c9525811543c04216410f0740c0102400142400c0003001c000b80000c0c401d6200040084d803070400c2058143d201e06007aa405154800000d1040c50313001c0c01d811413a40c2048803800c1145082c1005907100ca4010320401c0751040040e554070306462200c3d241e44281d04009458001c82e0340d6140341d0106021281d11503280188299610580d42c0c84203401080200b41014901e084214410001040086e800c50010011100600c910342c9403066041a00702808524150048507641040b91058a13846201c0c140c42c0c0d0722100740c0364050b00041100064000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 464684595 1250 464683345 464683357
    0x20a050901032306010804050c0d0b010509180d030e01020415020124030b1b070f0309090e0f1e030409020a0504050925030f240303030c0503041e1a040c1406 69
    0x82e88040004c0f1300c0c41c0d4401c07543e465105004004840c903132000031012030410700180800b5070390100c03040e0051003507250004003070390481c183c6215520b0031102260702070389451038031106005150b5154421402c448080d010381e0024082c0c01c503460407102c10060080d028014034004400c2104c3c803d8948003040c00c1409480c0b0030b50f074000e0010700c815912011a81a0413500d031100342d02e0810140408400181c0085841460f984281c0e44c1c150724510300b180305403e85030210040d0080780c0040c201000c42e070340c0010700003000c011890b0341419080c1c40e002a090440c4201e17008034200500004402800340d410038010300480c0e81c1621501c8896880041c1c80354150203090406440341c1a451411489a220760044001c46825000014260f25565074065072403030f801c1042000c4803a62a0100103058152203000c801c05a142089465407900d581c07151407220101c401406c021505910350003d210020941d024a4010030822030307020304050a04041442d464466401c00303c0700c0100c40400380c28003038141c42c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 464685845 1250 464684595 464684651
    0xb0f030a17030a090b0702010c020f0a0f08030c13080714121b04020409060305010b041808041806050a060507050601080304060c0f11101101060e0106050d0f0f020a05090103 76
    0x4141c40701e001420090380c4007034018801152204089008070740b0342010b150140b442c9800000c1c4011400e20040c2c281842000d1040045c0c1041e45401d005c5201d10002d1020035601885443c0c0d00e039281c11650b000d03401810006001c0403e81c400116241c1400900101034a00703081101e038001c400142041070f941088840d60b10190480a075441d20303103a241d8040b8811500040c405824981c66140d00d404899460307100f61902ea4540507036240e1400c0c03a104107207141e01d20428441b49601c47c0c2e201c040092240f4800c0d01686c4041d000c5880081d0010780c0050050301c8002c0a103021a6600d120003000c0c0d0f0410b4205603090300984e4000198048000122400c55445848141c443e4030940c48a44406801542c15540c0c001c540c1e983c0c10040d03441541001070100c0c16245c08030961640e100e0700d03084400942141400c90040b070014840030783c2003000c4e00c5c082030001c48017051420000b03c110b0003034503d954504201a00229000e240c86422001804001c08203a80c01c10800346409e0401001002810001d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 464687095 1250 464685845 464685863
    0x1201031505220203010e0d030c080f010305030a0f02190311010e21070201051e03090f1906020702040e07091a01021609020a091d0a18120e030709020408010b0f030a 72
    0x1244140c0e160004402d141e000078000128080580000741c10407000d803003a0b100203a501d80c41d9030109030b00110041e07080703803d01065034229030555559694070711600c01d101082c85608400c10304080d1080003021401e100ca8600941d40301000c2c41d01801a031070203100c5005035403c00d40c49504100c800501048024200301400c200d03160251400c0050b64448a0264100b100402c0a4650fa11104080c54003800003c248240c0c0c91801032055402c00113a50b620090741d410040ba03e0030500784c0c0d000544441500200010707910035081c40040c004105c01c071502c0c0c00031b0040500005503101c66500c0101d0071070b04406400000a40e080049845240c100005810301001c1441032141e000154080d140d080e0040c10800d6043e03441d8044000880c0b803003040080d460880f1020460125403d021348000501d8509411040e400d056075280c0e2442000e842d80800c00062040011013030b3380821a0000800c1d44480855649844201c20390190031104c0d111400768480401c40e080c81c1c100000d0320684250081007030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 464688345 1250 464687095 464687131
    0x60f0e0f0916090902030115030c08070509060d1e05060405060307030f08070302070f09021306030203060f041e180b22080d020403121d011110020f0c031201031505 72
    0x50031070320300b51201078070421004000200303501e000c0780300860181c07402d5040000f0b00e440d1101c00406640c0c01c4481841040018002d000301e140c6c1100507620b1620742101c0c1c1da9111501945070708000c0c0035060b41d0035520124030008202411096200714002d24066805010780d03a200e800307050362828548001454070304c00444180205044002810080d44070344151804695260004400c5031003a4000315004c43d80000c5000000500c111850000c080d1410150300717614026001908501108090340c1c05a030322000c404c1115202825900d480d02c0411000f0000804026440040d1200c26403040b81d00688560205801060701154506601407441014600c800700703030740c2c503d01c90700211003103403102c2e40074030021002940310343c4001e08868076941d4071300c0a00303180350001e00c03480344a500d024140700c0c090030041c03000c2e00b005c9408031829104e00409a034441400344440c040c5c0c030a1400400042c007001c9461000321240c1040141200c4c0180e4030344013a50031300e0502070100d880540c0d08520242c000c40071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 464689595 1250 464688345 464688361
    0xc0b031e06130902060d140a06080115061b060c0e2407021e0904060212070807050f21040c0e0106030b0d02010f020c030f100e0109020d0b040f0507060f0e0f09 70
    0x4500c00f0380d8405072003207052440491260040c4c0d84d0134078810003034038407801c00c01c4210754061103850b00501e04503009102c0743e80034021503512030361140502c0307003002040c05c040e10320200000342019115034821410080388079010002803514610b89100d500c01da03000110062034035076003403040301e04000300300c0c00c64039210145c2e00308481940300284c41344c02c07101c0030921662a6941c800180d4402d07405400302680c7c9400f590b0b584150270710002c00c00420300418100340700f00103a100080d03c518000c02d402640e81c034400e200681b0018100d2001030302000b43c030a030401017001140c0d802c1c0d5040b103501240122a913600c5030810b40c00d88200081d41600b045000310340c240507600c00c1440d0034040010380140e86400b5041000301e421700c07000003564902a40000b010b000032006521450342040108d80c02007000c0101075000640403500c140000d021941440d0114081c403603002d07940844d01da8408200d80c03c00380e4821024111880a100340d202040800010f0080c500f816480301c00440b60041030440702d0380d24154 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 464690845 1250 464689595 464689601
    0x312040308251809050c040e130b01060e09070f020a08180d080a0e010207240306080102130f150801091a0307120219120201031d0109060902030607050c0303130f0c0b031e0613 77
    0x44271140450202c00c000c5449030300da6034040c2c00385070b0b50300001800ba13005000c00341a010304007004000502c01e003c0704203940420707642c0c0100d501c003080b0783c1d45181021500517500d92161442e98081c522924210812049500600c01400c060312a0b4440c000c2c00001a40c40d506c0b248941021355082d0781c0b880d410704554980c0491180307504d00b80080c06946800c1c420f422038100c00c00e040c4449040c3e040c244400b0b510818618014403827401c40320030344030700140010324801040c03140d00075031a114040b80140642010200d42d0104015040310744203550f8244101e040071407898182d0103081c06030f4803d0305003039540c01325000781c400d00707041e505001030f00c0d070f0044001f030849540e152400700d10440303020820102030103000380c9280a075001183d0461203004240c00e01402070510003d0060400c83c1e459109800b0040d00d5206113029a0854a4520380c2040d2040c94111040281118204800810941d4086c4040e40c003818044884409004030340700314003500c5000f980c00e20b0b40320300c2082059180c217000c0c0e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 464692095 1250 464690845 464690851
    0x31b1e0e151c0204060809010f060b0f0310170303041a060609011b021e12010c020604140f0d1101180b2701050708010501110312040308251809050c040e 67
    0x402110031460360120b118049801a411110009242030107020410600740502000408a10000c1010b1072a00c4000036251043c3c3c200010b0011303007c8002034500c0303120070b5040b0080c91146001e52156070043c1c100340d140d51044500303c510403411801c210440e607a0310385030b502c2450064682460120007034015124504103140e0800b003800b40011710f90058031504e4202c1600c0800341c034511102d55a16081048800c5009918200c503850075100c0310a50307a00007078058000c0d400007018004d02200c44240c1c0d040c071603107080ca44043c2c400c0d103120742031103980030a03d8103030b08010000811240303005810388a15100c162501500600d841e402150710854a24180c0b900b0f41807907201001d04001d8100720609640040350840003081d80200104103039608128100502540080a540b500445a101c9004110301800160400c001074001583c101c9580440e43c00003070744070000007400d2505840081001e00d142c00e40f09040700075088001410035582c010790340a540c609888c00d06160500303040220f940002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 464693345 1250 464692095 464692117
    0x160b0a051c06091b0c15050613090f0b13030c030513180902181608190213050f0613090507020309090406020409320403031b1e0e15 58
    0x14884400060624807403080242503020021440c1c0441c15070880d00d0750060013458091101900c04400020b5212200044858240c407001640d0340781c210203d4940320405074010401403400344c05074280a40300c0c0c404240644124510640b44c0c2d5000745c020f0b1071694125005021500c51400100001d02840161500c0b02228031401a5681e403020f440c06000300f0304000c149800d5403040c0210039410320011080543d95141d4600c440d0b414400305900f2100b2042100004001c100f8000c100c0040707041c01d1100d40502c8458003036481e04441c030341310f10281c0c42610900340f00b550404680d450a08001003030302d00c1c40c512419030084042c40c10030050701410b0000d00c100d0440c08104401190342d80c801ca24a030103580102070042c0c503a814914101b04450781c0c0d2903071710345600310215080040000d5417152442070554101d1620952554075095015201c00d0b0700311640c0803d001c5155010540c4500c44203642001001c1c00c00d000c01910b001502d4031100d401182c0e0300850041d45003c840c4600300c0040661810b1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 464694595 1250 464693345 464693377
    0xc0809040f15032303030105010909020c0723011e0906030b0307050a0b040806101410030e030f070605060603060306070f12050703050702251a09040204030605040203160b0a05 77
    0x450042c0000701c015608102c0e5a03022941c02c260100080c681e041840d035041d0002903155504010021b40b01030001e1140c0050780c0c3e0009aa001d5068041c4603d0005042d0388240103260500001c0d00e032103c03003000c1d00b52800506d025a010700501d400c41e07610104048980c4406001a08000e000c40141458200b2140c041c45495000a1107171a000c0c4100010f0a0303240d540c40e00d0b6401c11030400d00b0180094049403038141705440a002055540c40b01e0b02c0203410444280002034802107043d0003074406031480300c007d404040341b4058807084010041540c1272041c0000c0103d66a05800c0102c240000c2d0b6806415038407410025046901031505180c0c80388441c2001c4c411550b040c03001009880301140c1c540d00081d220414802425010014014a001c8020914250796410101108032584500c21140329480341918110901c1c80c49080b41e4800c04090000e5641d01c1d101d060420140c1801e40f0124064451420803400c181d00c2d0524001c00c0d102c000322040e1078a502c0c03080444136600701403011045212 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 464695845 1250 464694595 464694611
    0x1b0903010e0d020a0b0903070503310305060618011805041a09071a0a0e091012060911030303090a030513090c020706030c0f08130c23040b010c0809040f 67
    0x100400c81c0010b2400560b0040480c0d22a605c1e210081d00380181c00c003061a4414032040d0001600070081d580c04c016191100b84d1048409007690540040e211507018083c8100300d40802403050210302c0611900301607840c0c0000700d018100200c50380c4400d01c2600600701c01142e200c0d1054100f0b410a0f50481d004000e13503409401004000e230b50300801074610440591110380d0400508202c0c003030044010314600d8100e41024070a84010f000e21503414039a07403080e021800028001c9102411180c090300c40c2e10041a80d12540d45403035402408250400d40380f2600c0400304503040d01d000421280300702c1e6080090003204002c0d5a050791035800502001c054507c20060101d50300c09a4030400c180890240d00411150740340450150880c0c00540d400c90820486211861496801000c12504848001180380304e40b00e03282040200c82c0001c3d000b1840d180041404a0b00490185840b0103000720200c404211204091005441140c10100300408a103030620055840385010342c4030841e0090050000316805e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 464697095 1250 464695845 464695871
    0x4240c020c151603051c0e0601090c020303060f0a23090c0a0203070b0a020904050a0b01030e0c03070e100f06020a15150b03130203030c240103050307021302090a090f0e061b090301 79
    0x9212224907054460340c400d551f1206e0003007005a1070041241402c1002040320b20709009483c1e1000170a8a1701400781c440c90a00c031500e9030003040004010003410718071030780e0103204149140b100034a8001d100b403203e4030100e42c040001404035903030401c150300150b1602504e030350307402e1984200800078500282c1c03c0c0000d80c616140c50042a10481e03400c00c000480000e10000501141c0c601039200390b180e0b0002020606c55100040c405040c0d846020001c41a580d41404880c2c101030f4a80120440c0d011010000610a4000480000d594442e030079054694842c0c2000d10102c2e03068550310703803126105810400841240c20015030b00002c09085910700703c501600440d14540c806042c40309c0315802403214a0034142000c3c0000141c05039240d41040319450358681c1c076624001d070030f00640720700e0342c20398100d48984580c0d048828080010b44140401d83d51020b11200400c46100c01e91441e07410b000407800142c1020a5071841100701c00e148210480c8190381d07070009504201906030b0150341e0307116444051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 464698345 1250 464697095 464697127
    0x2010906020d0501050414040203060a0b0d080406020c010206010e1014030114010609170f0715170411010908030a090b0a021617070b1c020304240c020c15160305 71
    0x442c100e0203000c00c6951500040c40b04850fa9151001a2900f480301440300690380403030940e801003040c1c03c021801280e08000a0300c099542c1d180240607180c0011b0002d46150045114188107000360240c8066a81e40e4204a480c580c0442c0c001e42c42c0c0ba101041844922181c3d4031064130468081c00008840d01044036228045500b030304041d000c55180c5c0c00400043d0702c41c40c10801c1152000014081d48400d04200703903903612807800341d0a410708440c002d001440b8030581200038400100c2d83c14040c18140307070801030310021401e080180042e0880310041002c1100000f11030b004c02c020350310009154940503445030183c01c070121002c2180940c410726010311890045c424041c20100d100c0120303000d803514140d880d202d2158002e4031044c0c01030001c2d00c201500181c003101d0030784d000d20025a407503883d07103030048160000300e1001040100305500c01c00c0d01c58071584405008005c580032145d00c203462808124200c002c00e0304500c2984020001038860a01d004400c0018602c039050090804280480c0c007c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 464699595 1250 464698345 464698357
    0x20a1b050306040311061806010308030a0b0303160302011413240e030c0706030b060a0810031a040b06010305011404020d271a04021507170c07060e03030a020a120201090602 76
    0x85c101080b10f48a000d0300b40030280d0040c05820390895658402074030030740c450300c05100280000402200056241c04640c002c1c0036009401002e0300c1e07650010340025109014582001d8005600e41040e002103110780c100c409000d5040c00d04c880d824030b112130340c032406040014240054180c0c0b500600d100600e03003a004251034070f07001d54051604d4900c17003c6480d240c402180e0001d801c0504210320008a5155070742201c50048a524040816a44265811854041c1e55100512460540400410f0080c06003400d9000d103100707624422a544a440044041d61000c0c0600f100d903017446e07941c10000f0b01d031a90040c100e403c156100452000304e1801da9004211213442c00e55550301001210b5810052803a59145031420303048034503607550415401064030281c1644400000710b00004020342407103140e800020501a00082e040c1c0e48003140d09500d51101000d02c11380f000f041040e4014540d6140201c15240c2800c01340d40100200005911035040f420310105580040d9540c494081c0041201da00081207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 464700845 1250 464699595 464699597
    0x5010b0a08010e0c031c082e050f030703080301050d0c0e101701140105060f12071107060201143d060e03060702150a0609050a0509010605060a020a1b0503060403 71
    0x3000890400d50a084c9041c00c5000c903c642c00c20f015084240c5d202d29000c1c0206031343d6182840c0b0596800000090000b021000c049800380a41c1d018107601c05110701080590344141d45082a00700c1798030a155907102640801404030070244010300040c1055840103520a0140301580b40d60b40d079424140b10a09400e452162107065104414000800c1c2c01d010008414200c00080103048070140c00d50401203070600810f4451304002494007001840c07602035940c00b041e040321094030390409020103030641c544c40e40d40c402c00d07000308480003d000740180b04044200c01002025603290707840f9162080b40082050158090102030501d0045030085007003107491820740b04d8203004032103044c10350141000000f01c080c5031290b0301803030401c28481d6000c01e00c0c20f00c0310211280709a040e100c80c00e4910141216800c100c0d8510303d003404014450786183c10480c000c000c0c00000300a6940c9500901c2036070300c42ca81c400b00240e8040c0c074081c000201c12021002202d00380442c01c01e17001d40c460000030b040c00c0b010795040d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 464702095 1250 464700845 464700851
    0x120d080a0b0f060f281b0326060406060509030a080f0c0601080c0a14210106051e0405150a0b0703030219030c020c060406120f2004060206130f080705010b0a0801 71
    0x2001d403802460101c0207000030707078000141710310880b00c01800354081c04e48024002c0d551a207100b0805004000c07140c415060f1110612070040700743d1102c030b541c820440e0080c0c821030600380b0002d4014069070032156444005805001c2c0c242c029183c01005d603003d033108800a0710104402e15036064180083d5018100e808050080b00c80c441c010814942115000340c1e03501d0102008041745556204012050041f8105600c00308841140d50f032401040e2540c0300e1a005a4081211403d03201c40a41e6211070380e104a40400c1f45488030004212081c0b40f03071804c1600002090024040054000d016151302e500c245409031170441d20900f40c3c1f403205840e00c4084040790b250303075050800c540c043c401c0103841402900c503a428039143c00c40050417858240b000c0500580c0c0c44840d10268040c503000f2001040c100071400d00e18048484101490ba4854812030b40103008030004149044040d0505d4001c1a8110040031143d51064860b51986e80c0410f00c111140e65035558504515110041802c000b40303010340c000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 464703345 1250 464702095 464702107
    0x2030c0d050609060a050f010e1011010609020a050919080d030906051602060a0f090b10081c120e03130806060102010e01051e0601050c030d020306120d080a0b0f060f 73
    0xc80280c81c4003a107182d120f08032810070000140c40724411002181e00407104603005040000042c0c0c0d8110285160b6a04525461048003009400c010054102c030200b500030003030b5950361001c00049000f0403006da4002001000130701207a10300307003540007400008145802c440d03a40d40c21104d480c2010344009400400d031266801c0007442014880d413a444022089074554480b01440004c0d110000100962400380d520341d0404d0707002c0400d6000002580c0d01071100100303070407d40c035806001c001d41d00c501a000d21070303041814499490800300342c0b0201d00f1600c03000c1100742418040006043c400400040621091100d4107080c2c2c8605014002040140e001e044642041d03c0024290382c0010340001090b03041109008802c800f102c40041d003a04242c00202c0287c8408004a52078070400103098106c0c0301c04200c0c1d0340c84035100d60065006c0d5004035104000c601d504444140c07240034164003400855009000501c003451542c014503c1040010903c100d10a1800c1c0081c2d80754000c60740903154800c0205103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 464704595 1250 464703345 464703367
    0x150a0806010f0f090501051b060c0d0e0a0f12031e0603030f030908030609040320030d05061f080a0615020714120706050c01150602010506100311041e050402030c 71
    0xa0582c0900841c0340ca40f44246003a00d000d0090300b018030440d410020006601d1a40d0043d80710558150480f03041500d0f058240b034140c0c0c0600fa04601507044940e490002e2031a4201d80004e213040c81e41c0e6201d05c2d00341c071300d0690307440e6011181203454010040c503403103000006020301121020f50481d40044800941e10303096040040c01c540100845005140c50301c0511004600076070141c07540900100c1e80eaa1155a451038101c4102d0504400ba014002111807540b42000b004400b070701d0402088403040080380e80d11000c2000e00442858003402001d1442d26107a902446440d26551002051002040450360f59020a1031f80c0081000080183c00502d014040e80920000c0002210001c0b10703103c6d80c0d101c5440341e00e80c03111454814007081c4031000030380e5200950f081d042504490310303540040c0844c2d942c0e2071020707020b01000c4072001e11552070700d01d1102040d070213446a6290446281d00c02800e081c10804001d01c9544614100e44c0022007002000030300e55035900046100b50340c69141203841d4000c18030303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 464705845 1250 464704595 464704607
    0x60f07110304120602090603010b041a0a050306010804020a0314010e010b0d1703070201090b0112111516420b0102060a050613050103031d0a120b06150a080601 70
    0x44001042980e28034011541000015101521210811420848000d00c3c1c0040240301da010690b802c0803011000080400d42080580101d43e140c1c0c118041d0307488607030101120b0344512000b6030301103141030011501c294464500c05500c0b0340b0103003e80d90060f440751502c80049800caa0707900007da4483c0c2c004200b8030400c0c00781e1103803154103860544404186940e41d011001c00700720601054500440000d04083c800d412107040319400c5180c056076540c407a0703800c1d10001401c500c1961101800c18104e40b0742d0800750078020045034942e41c0b05040070610321440a2041481805540c80444c2080c00c2020b0008000c00520305480f070050100e1500c6503010310003880995000e82c061140c038121640c030080e40c010035180d5110314104400a0103a982c03000040000410f003a003030000914010005c002c040d08441000301014001030200c3c05403200c84200005000d04d80281c49811065280c1100024060000b10307800003402030880c114000302c4100c122103500100210030001c5d14280c00d102403542c00207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 464707095 1250 464705845 464705851
    0x6010e060315013b062205070504140904020a140303040801140f0c0304330f0b0913050705040902270106090e070206160203040f0e04151b0c020a0512060f 68
    0x2030074004031001300c0d03c0e0040341c680c0051182e0700410030200c0c01440450300100042d01942c440e0800c01050905641c0104160013900034031051182c201e00001c02071601c1c0300e071148110b500070000c50045061400403185807687d0b0561540621080c0000b00da02882801800303182c548410548002c4d1508407090f044042c0050094248254100240004182c95004102c49403400880e046032004c00c071911040c00102d03640141010f9443c0c0030005103a2800ca4015580350141143c8018954552075021030746040c1d02d500003400c40e40455020016810280c000c038901600003404142c00240380a0305201d41480c00c00001d00f04000480103000c0d4a401ca142540580505101c1403440d00c0e00340c40c06540c40700c0251290071462058003417603903240c0c4200120740c00303400c0000440030601c5c1ea030061500c0c902800c0d1012a01d041280700f100055130382c5031061644c84c81c0d241c041d00000c000503140075254809000c0c02079030009240710000ca01500e40c44030007a0b120f060341c0000c06182c03509000a02100c203000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 464708345 1250 464707095 464707169
    0xa0b04050103050a03111f0509060105030d0e121009080406020609010203270f011a0a080102071a07050403020405010f06020d09060e0621010b0703090803090306010e06031501 77
    0x1001030001c0f0724000f03038034810941c0c1410500d81c414808075040345804000d0b05549071491110010308404070702ca4121a01076141001102c00c5a40c0f11004c05403aa00a003040c0d900160002107450a60301c3c10b039442000103003120341134500d940d40303e080b9081070702c940708000d4405004c0090204074055042003403540c03082161000b1400c1d401c1040c49500190310840940311400c0c12283e13264a501c90920492007034002c050000c120a003840309002c103020501d00c101c14414031800e6000280c044040c000c40313120750362140c221807500c05843c0b040c160b0b0b0705015018404000050001100680340c034421103020381080341c100c900c1c15192040091516000040050030000309a4040080c01d030400364800245004546440e140c90505880310300d84461030140c99001802d050001520a80100040103410300031f544d09510075485030521a900d01c41d1062a68065000c400104800d91079184a9508443d000b0113840d90080d140e1844484c40c202030300002d13244265000914820920707201c0d00300c0f018080d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 464709595 1250 464708345 464708351
    0x1202011206060e0d03050c0109050c12070503070603321009020702090a05130b040c050108090304300807052d0312090f0a05070914091f0615080a0b04 66
    0x10800b008100b1071501d0400b50280040042e0182014014016618100c00b007100800900c407a80c1011a030741c00c6962800c50081300342d000140324000003c948602a03c2c1c0c0075008000c82864203504600130000003c03141c0061813140d40b0440009040d101c000c1c03038800300d120410107605183d40d5030611058a40c4c8911401813041044100580383c0c0103429600c6024020b000415584c2e1310410303070307201c4010b140c001c021b21199803c000420210306207031000c0d1802070740c0d402031039600d020b800d9030307244224010011061080102c02000703455000c074500c0216174645c040b504c0001190382d00304441d04180c404852581080403544c40181c140106506021003640034244c440402000643d04c1348100b442c19916012100002842008100308501540540504443e884603250600c0b0352250103a0040300c44281c00d000141d0781403064402c046001d4000600a40740301c0b400301114440d049030503e031050307080c3c5e2581070008881d00380120401d800803a1351a090031318544402d071300044a4080312404d204da0302d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 464710845 1250 464709595 464709599
    0x21030e060606070f1410020c030c0708010e07030f03050f0d1b0f0c1502040506280503100e070c12030b0a05030f03070f14010207030c11030c010e06070c0504061202011206 75
    0x5400301444da00190014401250f0a0040512900340200c3c0110820240e00024502019140000003000d46c41c1c5108141e401040c1c44107609402c3e2030380e800c1c1c6000310b0b40c808182880412040c44900105912034100383d4680703803000d10900c2494215400c0c0c054820b90b40c3d1104448011007039001c40440445141600081c512244050210440e2100c040c100401c0b03685140440c0b03c0c01d80c1110b0103030000030101c5840b20032081d0407214001d000810303000204041140c51003030724081c400380c074050184064a844c2041c2010b51003850500010880000c010800e0070359004035815406204403070100740d030f01064400c48a0305002c074440e84c0d0340c0f081d4041e902c034482c2c0f08080e00f4080181e9407001e0348400c0c152004882c5040101c07541c040d0345a90091544005180c108042e00545400c03101c1c0e100d5107842000c0c8041e64101134890340000c0c00e2501168141c1e940c40c01c9490840018589140310b26a0100ac9030785940115085900542120030060210444030080d580c0018800a68030201d4009001045c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 464712095 1250 464710845 464710853
    0xb0307210515030a151505060d0b03150c0a08041e030914011d0105030603120a0201060e0604050f0a020d0f110a080903040609270903081f05010203120421030e06060607 74
    0x1188603017658510341c0d8080c030107070700314041207060014400100659243c5402d20140310041410102c02440391240c18085000a10164080b5110311160308502e03041c10005903094550640041003140d4910302075003225243c400590381031288a00070741c0c80400240c100200005650391903600503060155141204590ba0400028501aa842860302c152a51201d0300070a01d082d120120a00002d00046900d5201541c150300100071500009070649040d11690705003c02c4510903034008024070b16850001c0c1c01540710782c0041203125003c2e403001a1300302c0d220516800310b8543e0107020401201c00103a106c0b4040e8041080d9421072441400303540f80910301003028182901c944107611600c05501c0c41a8034a0218000741c0300b071059104000d008a5000303160050502c442105d104500307d08440c07020070013107140400501a60b4042c0c0055181c80d05822a48005660040c42140e0b41c04420350040d0309881102c0040d14107500949000c610703c1100c00009081035030080c203650144d14107001100200b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 464713345 1250 464712095 464712113
    0x2090901150c0b04050d1218060c090b070f0b06010509010801060c050114070c050f06010b0403020108181c08011e051e09070507030201050c03010e010b0307210515030a 74
    0x4605201d01c0049010101006881c2c1800582002d04654540e0040105100e008554001d005a01da0b81e000b2500c403181c8007410071981110301e440020f0a2503038503400003030b07601e5100312805070f00c41c10101c80c515070740c2c021a41070350300c4880100c6035041c85c0500341c2c1c1000681101f0765000682420700c0380c14110700c0c80008004100500c00c0b0010094605158003d02100790300007102c1c62404080e8009620b0119000f80900c2191001200c442c46020b603041521200030a40c1c9040c4c4101e140a1450a444c1d0f4004407802d03030002e040b000c814581d9103000343c00e9800800540e01100104201035609400c1608090a0000c050b8480b20a405c1050311104c40c00000b1002c0005a03141252425000b8900021160300142c125036501e4002c120b003000c3c801100c0e00f100260100501c280d00900903075540c2d160100f9240000c1c03060840d41603460300180010070f800c6014640c0f002041c41c0c400b040d5400c4100001c5200c0d5160008100184e9910030f200301040d800400118811058000b01f4a40149079200c1000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 464714595 1250 464713345 464713349
    0xf011a030417040608070e1f120f0504033c03020c030d0e060907091e0b1801090510060206090d0e210303090723061606090c0f050402090901 62
    0x126000100203000c002c10818141181d400c100d6049846980f04c03039000d41340b0345081d929440403c00d098003c1c07100785048941201a92800210811984919001664100806692012030b207888c0c00040400c4852445070f148964000d980b8408941b150a0340d04508900d24a030008184592150420403007042c00d10341c0880500c03528005a07540703424000281103000c0d0051400c0b0032401d02d0b0403040405000111940580307110002e85c2c200980c0d4124402c1101c100d0900c00c0c41d94091011348444161301507000750f40559010308200320225400440407042c84090700150100c0c0d80d25414402c882e10342c00d0444010708030f140001e082d94140306100315030b10303842050903000b082181000c0d030085854141129014038081202d20300842441c82450b0385075042110b08540a01c103803040000c2c0b100480020103000c008080400c505c07201514284003040d8400151041c2505030740d200315002400611444514501030340c840303401c0e030f810186810548005a4049403280c2c1c0103003c000b005503244c010304c81c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 464715845 1250 464714595 464714639
    0xc070602070516060513060e01050910020c120c01170601090806010f030303140601020c0d08090307090509160521120307030b0310020901120504020409020d03320d020307020a140a0203060f01 84
    0x10b00c107007025004030780c142f01e007041c0150407001266507400c3c05900014444201002100c204005404108000e540c60004484403400140180a058035001200c1c0c034103a0402c0d41850300c41640781c0c8980300030345011001c2e1f02164403500c0000d020400e06900d4800d0b584800b10071107000c480741c101a80000d40d10049000c500707210304081d001140401542004640e6010000f4060341e41c4941c0e03951520004003002c0390014a030b401002441c0c0300c0c0090345503d000c1070320002400c3ca8078090300c2407003040b500140818042e4a92180c0c60341250045050400355126016a950200d00840200c2c2494101f45084e0322810120b401401214400d07a0071902c2d400300b070402141c0002d0316a44034000680a41465000603420800a0b552481407692040d8901c1220981d040c002d0b40c100480d0f241044010b24500c9a01c5109005115012000407250000c6030071000034070486407564004d03180c0c0d040440c0381c83c0309061030b58011410882141818050180c2c0444441401c1ca80340d854905803400c02c0011483d15a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 464717095 1250 464715845 464715857
    0x81e0c032502010b0a050306010806180709050103080c1e0318030102071e17030705070303090609020a080d020c0f0a030b07050706050907141f080c07060207051606051306 75
    0x41c1d44640a451000c00300086040e03066154180800c0607008281c0490035500400c2205004192400c0c00140307541259149402002c4950780c128040088003500300c00c074100c07400350400000c0c42c02034a00615001e503000d02c02c070300da66901d102d108074586080304240340c40350f4521409401010340084150f80b8880c105649401400c5000d4001030300904c14030600408054440710b00c050190110510313060030030700c95034003905800756010321501c032800129000e600040d410090440041e10035004106c10b14490140070811a00d1a400070b40d030a100358001281e582d00602d10380c2c03822a4104042c12202001781c41c62451000e09002140e010802400081c114a6040020840310303031080044418130b41c0c00000c10084c6003404621607440f0038a502c909001c03907103850082c00081c0f40540c4086c4940341140789014400c600c1207010f0301c2d0a04010310a030031700f4806101c480049105800205902e40c030400113013020440e400325681c01d114040c1c000d9410001c0c28030480801c0c1c81407107105c8042e298282005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 464718345 1250 464717095 464717101
    0x1b020d0807080c07170c010b0d200f040516030518060117120c03070c15050909101e050a06140403030518041a0109090e030f0d090b090607081e0c03 65
    0xd1101441404c03130040000d505409642c09420f5004c01a00c00c6411840003480b042d242001003106c950360300e8001420f40e00d4910443d0707410024001e00341100d0302c0040e11712510340c46450002003c1340c41c06c454110003603940780610741c0c65980c10304c540c5a004990744032640c880103907900100d541e0401401075a442080f40700308480b240f1410482840c0c81d07030f03481402c10f6451413042c0c45940c13070b80c01032482120008001ea1010951001096201d50244d03502d540305400d040341c0d10104000040302910780b21900030740d0700022500c940341034054035002074150100b041c40c0307203007006004408800d41e121a00700b0800190001da5203507144111403c0720307003500e01141c841b000a03451050040e0454045540203191846d043c441c040c40142808016500340c0b03942e407a16a0321049a03003900c48040c500100e40e00204000e441c01e8a0000c042c01d89100900c41c006480401039a5407a010341083c3d4817018564001c0080041045d84100c1c0c066001403403500c140e0740300003039100e480313aa40e40c00750610302c000c007002c000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 464719595 1250 464718345 464718361
    0xb030106050a030f0302060c04060f0e19091409030702011b05011401090e010c020c0a1206110c01020c061302010f030b060d050c030a1104030b0a1d0304091b020d080708 74
    0x403800280200410040d0704503540d1400c41444030207184100c002d4005c00000480c618008c400b0f8a0485ea0552505811829140300496220301404900d40c0e100c0c402060112801da94180e0200203041003800002d011a40220000711060b0700410108440d42704010241c0141d0f07020607050611599010600311803007040c0b4190303000d49165102d00e02d102041400000d554441900034030b500081c0f140080100250040040740c072000d8001c41290410b240100c20030642c10902807442c940d500406c030002e241c007421080030007268800305001c40b0a0b90040b43c1100344d41800c1c000360707800501d004080a0045990f5001a0000003014091014959140d1032504691941c4080b41c5044442e40303402c10080c81c0c102d10b0712000c1c0e0401e0381c540070000d282000c4801d200b0103020486040e03907080300013103085649100700440640b2099105104d544800490150302420400c040d1015100d0418041088818031800401085034207420342c08540c07001ca800c1d1103070742d04480050380102c00d1f407600308641da98100c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 464720845 1250 464719595 464719601
    0x30c09040f061a090106021902091e0405010204060905031513080c06090706030e03040503121303020a140f0d082d0d09050f0102120f04060912021005010b0c030403060b0301 76
    0x1030312071800c00803035442101800c0d0f0010401601112445407990300d0b14030403a503071107408406401d00d88080200002600d4135a0030207900807140080c0015546401c50071200041d01aa03088406a402003410301410390000d100c00090312059000b030000000c00242e110f94140050320310004e0509a42c94039050280300310480c2c0384004c030b4030300311500d50810161b4903648651b248103910020389009004058000c010045800300e62000b00140010811400d80c980c0759444015031242011103401c0000050715050400002007024460405c2013041e02c03001e0261401115004611607a0840c08400c00100c0180590b04c000300040380d4000e52044101c2c081e060300841203d6401c45440200350340445110300c1d00300d8500c0b039101d01c06071148615000801e900380c1c041c44002c9020318190b080000c62721403286080035400f81c001c10012840002c15113038210500004500100160426441412003185074001d0500401e200c940840c42c0944800c08103031139010301c0c00014030180d2240c1b014121607070250 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 464722095 1250 464720845 464720873
    0x403060e0a0204110c060109020313022b0305120601020102071218090203010f03031b0c150507061a120708070b071b17060a02120403051b100518010b030c0904 70
    0x54004c000c0c0341c80c55018003c0f15000303550a2085071003004000f10b80d50019000f540d02810031950307014881c0581c0e42c00c01c00341103c100c99118889411200b680c0300c00c40040c0010017010700a071280e6a440810014850710b0a900a004c24107580c0104a90030000740008940d40c182100c40ca01617102d650b00d031500c82e4503407209502000c1030385c1c0084000304000e130554035680100e070302c00e84034541c000102c0c0c0e1344000607400020016107210345180301000780c5692115011740c150a50310b8050f00c1c0c0840b0b41d454608036054000c80c5840b214040c00107074032034205039070000002c1d80c013100102505450300c1d0100c1d42d5480980103d80d100c400c00704080080151320508041d40001079060710719440e031141c1510808050440842d03229205440c0820b100d440c480c400c4940c49610003095410039a62600c0558865000a070854101860224007d903030740030a00102d0040c500f0b00e100841c0f02c2c1400c0c91b1085c070328000d1000c1c10251740d14020103204503a60000780c0b65501c0c441a0b4041c40300f07036124200198451800303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 464723345 1250 464722095 464722099
    0x10209091009060e0c03041106250201030e030313060b010318060c031103091209120d0914100504090c030612050606041a09131110050301030501110f0403060e0a02 72
    0x6500384000caa1024a841c019650180b8003002401d95803684a5007a240c1544c1a01c0c0c040420800310f4045418540c01c21b0410401801c05482c200391448040740d07000f5140040505480c81819400840da03050060b100203240050045083d801c01070720b14aa5000301d08002041207589400b04034651740240c102d00b03c0319000c00d4a8601d0010781e424200c0181082d00c1c4021700007031512501c1c072603044040c8252030107000e00c0700c000c0008084904101c007c0e039002d401c2840d40300a1881c1c4c044030301d920403c009040207005a4030818032510b09454004240350b048820340c480d010a10544824a50000c00c0e9030032101c03042c0c0003140c2501961410380040c042c03034010240b51a80401d001045c4180054007600903d0196402c201d0840311016030090020f1000140d64407038032000129113101c0034103403e402058040d942c00c50a500f102000200004107102c40e6001083c000700041051200a1140010510b4942c04c6103140140c803050040312481180002030031241e454101215441003000801105940 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 464724595 1250 464723345 464723359
    0xf190902041505040807030b07031503060207060f05090c3706092903100b0406090503120304110d060e011505040b100203090f1206160f09030302060612010209 70
    0xa560600000e5403007801041020000c84141c4610148510101c5007103c4103040504480e80c107558608074130107000ba2011080580781c009001c0c40218080d80c3c040254401c0c000103964420915002082d1074880e125207020070b2500e0100054204042059002c4800807030300c0344000c00782203900d400c010000641c1024040540030760031118400e003130510010340790903454110311941e40d2200003a090b00303c1d803000102c0030a00e44030b14991800c504090760708000c280f100e48030015112100707203519402a0740103800041052030204041d040038000780d040f014040c2c0b1514034618081c0c680404000b1b0460800c3c5c040c0d06444590814000c0c16030001300301c03025070700092001400d5940c500196078490f0103060720891078540b61011901d80360504640750744060b009141004d004204005003440340c1c1407403541241c41a0025030748400c003444298404e1130081403001e000c605000000786040703d803e14104c04d01c00f00030014000320f07030001442c0b03602c14001c60b1034a1466018000300c9000e405441d0445400043c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 464725845 1250 464724595 464724599
    0x7020103180f02030714010c03080a020702030a08130b0f1b1005090705010f0507121214130b0121060c121803020d020106050f0409021924030c0206060f19 68
    0xb82495401c0c001c80440b0301c0c042e118440c0c5500405c1c491402c902042241991100084c024950349a01240406006050a5241c2c005c00d0030b2450908044512010010b0314045004400114a014000d003041050409016500b00003103403250700074124012003001c50b6541203a0f001c00882100307100f01d000a000908003034820b02e82d00c4155000f414040f44030454100e089610910a640c03149412940760802030322400b506481a422512500d025107481c2c00b41000941c100300c0c079850045c0e02981482d004007906090030303000d001d81a0001007169003030303004c0c2800c0300c1000c85403818100d4020710001a4a03911a00c10f4a00380f042d44006034a140c1040740b8400700005a40c3d00141541c040d07003d44508580f2900301f2030899000f402400d51010000d410184030341095802011054400340c06c12030001030345840540392040940c0100c0800300d41e90f003604800c00c86040c5031010030110342002d100c54612501c1c065103582c4002e089c1400b032055810085071503544c045202c401e1085102c0821101e83d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 464727095 1250 464725845 464725853
    0x1c0804030c0f090c0f120e2a030d0c050a110a0f030f060506040c020717011112070201060902071703060a0902030a020a0201060515071205090910170607140702010318 73
    0x5039039480f40ca02d045281001e140e400c240580407046606480b5512095080f641004d00e00042041c0c400411082c031a1205155880c2d0240c010110107414640000c843d019100d0105860005194250410000c1180c40000001c0c800501d85010540c011004101c3c1400e12003c10380e07502c1c1035448917201d120110700c00030900480c4000a04003c2c040d50081c800d07661400305200c1035901c560542401a8001c8904000542d030f07407130742030603403510900000c203200e81c2d482040c1c0c1850300500c215903e0165024140201032b5024813840b401482084d0b001c4d401c003040d40e2110060030b18008080e028640300040000c0e82079460403d62030240188400464071b0781440c8102d5002500b0910100d0003542c43c150700844c0b68500b001c00404d500c0b0102d5080c0340342c601680d40e1a07650448103803445062040604c8800c2c540e03903c800915100e000c0c3d00c442195000e107048a03000301a040a1507500a6030003500500c03d0480d0300c0010a02c000740641d05040e0b550285100490040412a9070201c04030764240490b0100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 464728345 1250 464727095 464727119
    0xc120d0204180908040b160203061005010801060801260a060903020c040b03030f030121060501062d0e121002130302040b0a1404091712010906141c0804030c 69
    0xc0c4042100740c10b00109140c0c2c6034011140c400c0300103040240207000401102254200074040040f0104c1d82240424041e80468900700c41910030401c400200c0a06000070750f44100c5d8940113080d40d207040c85441d49030004641207210030f01d20360083d4440305029a6031440c020031445103010b41c01030003040144c0860500039210302000c10191710441c04c00c6c00640f5640b0f00001a19122030319000d0311440d503441c1401801caa03401ca89061411080c1400444010407c580b00d502e000305520b03150f0102024007154554114102c40c01072000c0620414040300c9030341d5008403841801001624074812501c0345800151030100e48541c0156540d00008089480a500417001011240300713440a00000e4000c0342001480d10090140d19840d42005c50000145d25154000d49800c5018620b039000421047c80b1091716580064485200e01044c0d40040018140c14810300c401441103c8080c000d40f00c030000000c040ea501132a00307905000001d1640ca003840a460f04070380056a00514030010640c0d286091108 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 464729595 1250 464728345 464728349
    0x3011407050414010512041a010b120f04020d1707020f10081302010504080f030705070503060103030f0509180c09100201150306050411060304030f09080c0d240c09030b01080c0a0303050c120d0204 86
    0x50354200e100000301100b0420582f84000440d0140d07a02035030300e240c0000c0c40d03200001d0040e68008801081a0b010914004004008480d410364050b0707501b030240140b080001348200c0b81400380c1e6405a00c1c0c0780e4540d020a1980c0c2004011810075260411070004031240d0080b5040b25400d40540b6851034400783c0000014507080f88100c0951b54450740d103904054982000f4400500460701036601a4003607880740c0020f2084003002419002000c40101000505100031552031803600c00c0040c241c00c5170710740940d0000c0c04000b107100a000d040c000c259041d001700351a203c000c20090b15800810b0420400c40d14900b445580a0642510303445c040c28003c1c1820f844014507000304c4d00016000c42c05203001704000100303420151807610040515074802265400f1540b000c402e020920036443c11076400c90103aa41c1e0039801e030341c1c1c800e00c0d6419410041100c80c41a44003003101e43c03107a0b0a110301e50322001486022690182003c85e01d075850890840e04060025100010b00c9000240f22030090000c7e90292007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 464730845 1250 464729595 464729633
    0x10c05060a150f030c1a0d02191725030603050f060f0a1506120f05040305041406190507020102070f060215010806040f0204110906030c04050301140705041401051204 73
    0x2000030764880e141c0700d01c60036901019104c05c034440760a010075146800030081526102c0252890509801001c204a80100c840d0700c5040d6640140c00748020f5000442130034465903e04070364294184031019006602c903000312480c10700c803800141c4210038000e0340440c00858015080d01c001c00c0d40305206030b0301d03100300300d800d07214089012011803000f104511035a80d110068620240010341481015100007000c2a03650101c10303190191095440b0b01409494052071082c1c03103040e03c2c3c50616000d02440d80340103c6a80c06000240500ba0501c1c0301c101c0240080c581c030341403085c1d17907102d80e000403420108282c10461034a00d861600107a800e034001200c0c907d43c20701c00702a00d21039807100515a101d0703405850142000c01586015070261406a120401d200c81d16010689890110030118170607410840d0100001d15010908200794102801040011010360141102500d000e1402825034060f80c054500f041076100a03040c2142d000740106c444611401da040c00c142d00e01441e00c00081e18402d804a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 464732095 1250 464730845 464730881
    0x806030c1039030f091a030c0403140705040f290a0e0c0309060a1a09270a140c06030a0b040b060705060405010b010203090120010906020a08010f0e011a09010c05060a 73
    0x111a039119584680680740a411314410044117000c00e410355030400381019100d030398104000000a0301cbea00c104241d0b0f00300d103070180500768500b10420045552601700303507081c40d00b4041004050421a020501c0c00640c280d1103040e107007c00c0b00421103181103034108400024100d800e102c100000030700618403c400400440c0c40595a5905190507a4190301c0c1d00d150748100002114942d14045a0303107a4011500501a05012000c10510450607180b44201c81250003001200040c007240f90b00d1008845800001450340000c0b0b00d0100e101440010400c0001e00d0341c81e800c17802e131035940c0d03045040b084200501c090348032076540c20510307141d810580e0700b16107542c40c00c01844019400032050310220b18050f15140008030700702100340c10445070051000310556880a500b4001445807010f00411f0806941d40c11181d0b040c40b085012005598200c100102200e40c01001690310221403124414458140191190003110058441001401005125025003c1009801e40e540c0d40100c0f14200485591 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 464733345 1250 464732095 464732117
    0x308030a060b04060e0d05010b1c0318050a03140102120c040e0a1a040e0c030a060603150e03090f0d020a0e0604140405070501030e0322060806030c103903 68
    0x490503103d03e219034070101d140506900c150785002452103690500450010840f179101c90000b40c0c001c07a003081c1907a03420b9880103500302410b600034810071040e10692811140503042000052503280070717110040c9404c1c5145503102c8600002c0d01a5107034400c080f80503075802d04214a220100340c0050081c001c4100360840000c0003203500340034440d00502c00050000f0b0b4645440140b001500012250034050b00c600703c40d060040d1010000b4004d2640900e5000891034150308d480c42e201110b8140111103a0308280c160124030b0b42c003108a442c1c90100b00c1e6101c0c56800c102020902081401502a51092041800203061100319011522981044034200f054a80707c0624032000d240645000d0b0041d413004030705028650280c0d200c0500d000280c0d003142c0c100980c1da0f016508803610131070100d900c0500f40d40d00f00b202603080f280564100303000718080d240700c140210101e141c1c4010724429404000d0034441c00e040c110f0404041420000c450240036101c004401c401400b0100c0407a07085002408200039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 464734595 1250 464733345 464733359
    0x31a01151b08030a06050612060f01080f010603090c08010c030c030506030a080313020604051c02041104030b070e0616060b0f040b0d03081f120201090b1e03040804030503040308030a06 81
    0x245281034111403841e5298000c0d40ca4050154000402c1441d140745d076440041b403c1da540301c000c1d008d68401200c17407040c0d52a2000c1441450341e040395590303052141c04810700c240d00081000580c1903c003986000a030301c412504002d42c2c0c04480e92b0111105501e402c49102a1701e034103400404030305c14551818052500c0d04000e2603039800b540d05002d400d0030401c0c4042a5012054481400d1003800102070b9410592250300054103d0302c880a002500011240904214203160041c1c81e210f4803544842d41c1041e10b1a15017610b0320100070070707076410480510607202459840b4010359400a20b101d99800504400d0f01e054001000e0041140307106500d03980d00b070701c0c2c0780c9424010742c00221310241541c1501421658240d6104101600c912404c45807911900141320803c0010001402d00300860820444240001740c4140f000c0c2d007084040803002c00068152542c0d94860701841180000c1055403035445040600c0e0701e00481d040100341d030100281c0042402004009940500840c0c3e9040100701d542e010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 464735845 1250 464734595 464734607
    0xe0a02030f1b0111030d1104031115070201050c070e1008120a050a050706062c18060115020708060c1309150504020304060e0a061a0f0a0b030907031a0115 68
    0x90b00c0c000c0400600800c5049500c40c480c02c9015008000842c1d08004420115a041c1d508120030101e0b00000402c04005002d40e6402c2d101c00c903d0241c07145000019044540c0c007140c07082d0140641070007000901c807154110208100b00040100c5a1100d0281c2010000141c50031280d10402d0524890580c4014905030008200d41c2c500b07103151101e138a0a56882410b941c20b402c10542a80c21603510f000010301e454000000e0a0100c000e40840c0000742049204080003100240c51403404604840038030802c40360014000e81075074250041184001c68810040703141290507006000da03402924103201b580f50b994806081c03004c0300b28000c151816210160502154107001c0d0a001c014454141080386081980c010342d0024010302e00400d42c040c4980030130b454444aa141203840950ba01c0c0b02507001c6028003d001101c6c2d000702c809041c0d00302030000041509105001d40c0001c42c4000000c00c603c01020094072000f1503016440019400c1d041c61a809503100c00d10582000c10006a00311150302d00c111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 464737095 1250 464735845 464735863
    0xd170613050714040b0703120b0d0809040612080a030b010215150616030e0109050a0b0702131506180f0305060708070207081501031109191104090e0a02030f 69
    0x600010080c00c4140860005080058500801e02c152015864092400800104080d2404005080d9100040d14009081c1c05404503243d80e2136180c0f0fa10407549541d0062808500703a08204c00f281c82d40b00840004000300300c00d51201540c80d680700302050400018101a01c4065550b8408010103030081c001a600c403441c05604403007485000c0000b800c3e050b0320062000711b001e4003a0a00b4204041a6039001c5031082c20310f42030780400e11003a15001c1c550f900004000c007500d41610119120ba1a00c24506018082d4000082c81800000f040d289144010303440b80010b0481d000c0803c82c0d1340d58070302c00a498040885007100c0c5080d07885002040780244c1201a400300ca511a0051425555812040320519805030261007140074607440042c03aa501040f5600504c02c4060228242e5407441c078102110301a0034030b089000f8004030040201c004070000a80704038416958005c141c00e00c000550843e01e02c250342080603900c1c50700d240040040700000301e0421603403082d01120304c4001014101c565800d104c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 464738345 1250 464737095 464737099
    0x40612020114161707050105150d0308091002040e07030b0d0c030210090503010213170c060703080c0705030a050910020105060f06070c0305100c1d06040e1e04050d1706 74
    0x5030b0011030701d0480b07402c001c00c0307120503038000021500b10580e01c0340d5507014800695100c0b20340129030507080c070800b842540e03042820f0108c0300c0901070a48000c25010038250300301606001901d4002550b005040c07011480b0502e204400311350381c903100c403000740844a0640d1f207040003d00c0c044408456090001d03580340c2c020341020401b400b01e8070350b6082080003c03003148108100004020005201d44090001d0700c0944141d4903580070340c034242100b201e0080350884a440c1554880820030b5016101c82d403c542c0c0c80d982520f02880c40742e490003400b0585110b61040148548800a02010400d03880b102030a1801002c5481c41d0301d545808504074203803241621450361001e0800220141c510300340f4020088540700d10700700001c4039565210541050041e50240301c0c1140c94162910b01181d00188200301d03010303045a040f06d81550740000c920765020754040d00060881034404902543c3c40d03072944060a00e0400011242c500d0980380203074580c1d024400030404190301c03244603002c2c030342c61011480c812040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 464739595 1250 464738345 464738357
    0x111c0903050702040e15040c1403030906030705090109031a041a10060503150315100f0e0c030411030f010c091a3c0309120405130c03290406120201 65
    0x10f408020050142004841142c0300300c0307403800e040b0b1028165191085010788030700b58916142141729003001d0035808181d4400d8004100c000c413503550f88415a6001011454826156181c8100503620038203d900b000d03010082c61017640d01c5a08070383d1001031250744200302c4400c0800d2700000c0c120303101c0170555095000707050300b090074010140308a0185901c4100400b075001c5d590b2014000c642080c004105400c604601401005007004006100c00c00900300d004a07804480d10b40545880c0c0004007410030a0300801c0000418144144122402c00054006084e0351414600303521090007014045044c40204525110000b01d028000b800560401762000b2a6840d19840240040d41c1c400781c0204103003d0030b8504400a4419406003d01ca40e6829042019a481c241014510710f400c903841c66000030040c1c01c000134132182d182c0003901c0403851003c56022851a4102e54254080c2441d032809034900b480355551904018030380c0c07282100400d01900e0410400382c40b0719014000100340c0e0700183c04160 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 464740845 1250 464739595 464739607
    0x1104061511011503060f05160203030424140f0a0213060c060e070b040603050f060a060c0f0803090d0908010606080402010507060908040909020306060d1106070c0504111c090305 78
    0x10250028840c98041c0c4000002c0c1001e4001c4007055a03d02604240d0341c45e82c3c3c50100b410390b07100520502d5000681318440c09800341090714000c1d680c0c400144000e00409503644205100b44c0c2441440040b015901014042540c0f15403000458000c11210342e4411010719010600c2d104151088401401c2400030010203c0e0910740180d80c1c5001e000805c9a050707903242115020745400340700d400c020b00074190025680360301e058070060507100042c05032030b40d02c00154203001ca65510615100122070707480c100480700140604150180c00c40e18580030300342000c00401c1014030007002c82e000500081e6030301d81c1c0c1301a94032480010308a9115008100105851202080c00b5601450241030711512584001c80c02c40303229502c10015070415440f091407661116001821841c1c2070101c40da01a50503140100070110079100c800c01031200da41440c1c0140e5000642e002840124054040500301c0074000f40414450b084414000d503100101c007644c030080010203100800028000c0d035028a030540d40d0642408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 464742095 1250 464740845 464740847
    0x110303011406070512042607180e0105041b0801091e0c030f0602090909030a090311040f150806091f0f020403120e1507080706051305061311040615 65
    0x300d81c5060031944080c040c0210b500040c401c003c8403403a40040c1070002d071141d14200c1c00254011030420440001d06480030104c101000015684040380e2045129407002d80c54102000010440072407030058550804040105100e00c6c10746920009103160f0090030388940e0350007660b080350039000004041c40c05482c00900940909240140c81d180906085c600240d036a5644544d407142e001011941560017055021385071030072480441e80400c00c50b01445c03038510200300080c4880c0ca18003009248142191f0380c03a480d61070307503808081c06001688080280300c03004540000710781001d114000c807910130b103000540b11440206010544604800c5001c40003c0c0c1a00e100700584415807030006825400e0200101080805c5808040c800b62070321400f200e48402c40c10700c2207400c403041e65225145e4003000342c0400580c0b0070013103406682e0054400192521241c802e0f8109042000380600b0610440081c445c1d28a0701c01c3d004150940704401003000c0d094843c081c4810740744944615008000c840b40421130746 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 464743345 1250 464742095 464742119
    0x130302010f05070b06101e09080c0d0308070804110d05030705010c03021e1c020d020304030e0406060f050c0307050f0f1507140c010609020406121410231c1211030301 73
    0x440c007402c0c4417020007c5e400e0403689120000d409440082e91100c0e042080d043c050040c010710500c04e6460052400320754034054042500640785000704020350f000182404040e0300c6100c103c01e40144001d1140c2c0c01030801542e280c000e008240e4940d480c00944072a020300074800c03295001050000d02030040001c1c1d0305886190044080c02d44905c2e03290040b00c14001e144e10061580384c0e4220001612070409080081c0407100301c9d0840ca014500d0010280002c03508031b21b018601c1001858030039541d607428001c0c03508501891400600031300c01c540d400320786103001094202912034902c003183e41d09801030031900e503480c0c0c060303c004010a601c05040c0e5105102c200c01404040b40c01000840d07001e030307600b03c524120390150380000001089a0030542849225020b104410000d840c82d148850030f211030000d005403024130509024070241c3d0104414002c61043e80803100030000c110700e0b040c810f405200b144d8010041400ca40a03c440402404250f000f00070280140c271a0500a6003160b003090760214407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 464744595 1250 464743345 464743369
    0x5100c0f1b030b180304120c0506030f04140303040b0402060702040207120e0a0905060f010e01090e2d070e0f030c0a03081b060114040b011202130302010f05070b06 72
    0x40c0d00451254100440d210300c2072901d085218240c000d41e15480c50030401c58550000e0201e8400118002210500d064000240c80a849401240f00c1c01284989008400c5004541c4055000007000c800c0045d03d4a100c0038451017039000d0400762108424540c80e5a88a1100300e0b001803241d51200049009400c20700b0140c03d03510301c0500014604002e5480d100c02d05c00e40505820000340c0038105000e607a0606417640001462009030610140c240000018644a200622305040280095008a4030707071060030a2401809501010111801c0c1801d480e0002c400300c90025411060207082c0403c00d101403840c07035200391f40643d01c0322000c0f0210000c0001c01d44103414101c0c0c0c988180f08a940c038580d03480c80000000d5107e04006a03642510111000458150580460b150703008003004100500b5400d150400b640b900302c4001a94113692001a00c2040c0c02c6400303411b0302840401c0500300c60000c44c801a05880c000d8a030940f80b07951a80b021500d0780302e910001000c1d0080c40c1d0206031a810a0140405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 464745845 1250 464744595 464744603
    0x1e0708060c130504052802091f050f0406030c02070b0a0f0309080c010617060601030b100305370b0a060c0609060603140d0e0604050a060e1f02010b091005100c 70
    0x20390190f40d140001e0607940d06840240302200004a400503000d0410415065112080340079411700b1407000024000e10140e40d10100c000030140418101584214202e07480c48002907112a12280c82e10030080041c010002100c000d841000808039282d0319500030380b0b4141100d69101d508941d607416044014040d0404203c031000f0040c462201030080030f000e42d4020b818055454404180140c24151509034043d00060500d0700c0c00021505989400d1103880301c100c0e20741401b1801d07032140c01065000d038061f00040d120502c004e03440000a0411300705d0220751090441024804284158100140c158042c0319140c0801c0e00b00c2e100034000b9506401c108040c5005074000600540c2d40d803501700120381d02600480481c0c0000501c19009908001c00444818042c1c4213241458200404035100190500400341441450011040907550f5018034918400d4005101500c0e010000c2d0b000c1c0c040d01d640d804040c4211b5080000491340c800501e400070443d03200400390420124024030035a805000c2c0c81081c0d07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 464747095 1250 464745845 464745877
    0xe061c0b0406210215041409040f0501091104050a0606230d0204030803010f0b1e1615051005010c0c051005040e011d01062609030d0e1e0708060c 64
    0x1504081c3c1860460001c81010080110070b0041c0c810050208550309807000540d10512041c801c105000d03005003c105c005030f42c111060340b035604080d0068494030384000c2c82c1d5820085030004101d41002c0d001c1c9a44810755090009450f0020040c05580e140c0c02803400040c5644002d000095003401d10580b09585180c00603d401c8150003400c09030b9002d90030a45212a001004010460020b0324030401000050901b90400da643c06e0316082446140c200c1c2040440e02140a07405140d120011002142e8030218158004250100200c0a0a0120341058660350107420010f000c1d4050a505203203a1b17844000709480c642800c0400140c0040b22250340e003080000d001c040341450001d11070034081e110498051203100e8090344003042005058009130200001d52028410019040c14181e0705c501c03030260036401c0783d40c5001003a440d50290f40d1079114607908150f40100c01d614042803427a2980c40201c90014039044d52940181e4510241c494018254860000142640c1100019000d50340c0401011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 464748201 1106 464747095 464747099
    0x10308030f280c0801151707021204080a0b0618161e08040b090307030c080a090b04060e01080f061e060702030106060207060e061c0b0406 61
    0x548160607000c52014855104503981c19542c11500004003a401400c141c081e001e854a103a0200d5951000818032428100690039442441c1c0c40301ca44d4008070741d0340031620190041481c0114021030f407841c01c1103c5070300010401019194000c01454040c0e0801078156a0044c00080c81b68000cc131000314104403090907135900c900801907001d03030125084401d450083c1c03085042e0007507891010211300b04607009003010b40101c4c050b4651300007560302c45400302d50781d01c00c180014000c1a58000407000240814000340340350101450101c1d0207076a501c82d2500a50043e40045000c110310b201c4801e82564420803450340800e0090702030042d41403550103d0459501d04946442008410002c42021b4403440200d8203510b502034001c00c41181e4541c0001d4848115000d4100068038480e5592078a02d490419180b0040560044058042410311904001e01880c8000c54001d5114030300 = true := by decide +kernel

theorem cover : BRFrame.Cov 464568345 464748201 := by
  have h0 := BRFrame.cov_init 464568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 464568345 ≤ n) (h2 : n < 464748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
