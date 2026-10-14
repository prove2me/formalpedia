-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0125
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:58:11.71838+00:00
-- url     : https://prove2.me/submissions/762a38e8-f697-4903-b14f-28e6135bd9c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 22302164 ≤ n < 22482020 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 22303414 1250 22302164 22302167
    0x60b070c0308030703090602040f05010e0d03020709090305160303020405010f090609120812090601050f0406051e130c02031b0a0f03030506180901020a03140403090315180c0302010305010501020c01 87
    0x30820721010702504008800329410340d109400c04100329070003503820741d26141c03500d12080c101480c500c112404500b107a01d14120a09010440706e12854141d000b9041c9a407900d40608064003800a084040140401c00c1c0c000b074400080140050600070f5a0040e22075080800141c2940030309031000303040c8846004200702e1130740c0c002e4004054031411840080500020f150950060141c0b0312080702c000e05c10030421a109400140b010704940e07003160f0740c08144c401301c0e05100460b0307804d000c1c0079040070302542003d81200305004104003d0700e0240903d58a9010b00302080c080380c2e484914040160000a03510003064401104d4540c0035194a015059142c040d94451b8540b0382410703001002e140d220400100300e0307668070049501c06540681c00a07050314020303903058002d6000f00c0300580464a0507101c00200b10304d0541c0b05114981c943c0302c11500c0d0381552215034560000310700204c44542c54003002d140101801d80b000c80441c1c442e0b034011480906620014080d6101600640c0c1190700c40c5440720070b180e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 22304664 1250 22303414 22303433
    0x3010b03010b0f07060212220203100c020c130902010e010f081602070801020d0203011e0308070311190b0a0e060c0703030905010e0118050c0603011508100f0f0306060b07 75
    0x115000d0041030b5030362a500d403c4044a00481001614091021400328051810142e10038429a0307141009045080e4080c003205141c100b2100203134143e0301018504113111213640c010b520721207082c0110398460041030009010b020112451810031900c0b812454215600040e4948500c0400d003415809902c0030000245025401071500454040f2003004c5a18503000b88511b0003d44042402555100082814200030790300c00c1c40b0760340c0a814060b03111000802e804440f0303000e881d40051064902266520202c4200c84c40d030b0741411440c028032862810680070228440340082c404c0310b40c10101d203492450502284c107003030000a0103030410020070030b001001d04111241c2c60b515040010b020591800c0850042c881c040c01707541c1561034158090100200e203000520102d1250080f03421580c1c01a09218460001b0701c220600385080c4100302030240d0189034482d500007906000300095955500307001c6511a80c41d440122200e81c074180610a0010700e00840340604208400f5030b1130216955a4801c59 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 22305914 1250 22304664 22304669
    0x702030f0a031a060408030c06010902070302121308010912020c0a0509011203051306052218020d2009030106080c0f06030714040602100c0201050708040219050d0b060a050603010b0301 81
    0x109039440c0079401c1e618458080c0f80c00c580c4400390010740c0b550744900e911a0f407640090020400761088000004100c5124000c54016aa1681c050003583c0224410f81c003042d002a070605110446254002c10f65010912030441114001c00040340102d15185010382000100601680901400072050145446441d8080e044880c089081c416036001d03401d0480700ea0143d2441055108240d0f14005030090b4080003074090841600c1e4407007140003031801102000c075010720a0501c1c8045060201c01500c0c000ea000d4180745c0d041c0180410075219200d050804903080e9000a003400e04041410a13250609110300d030050f003280802000d0980740840002d580407110791b901e0303209500c00400591803910420008800d1440b800d0119151602c419000c4c4d02c881e0310045140f03071035141c8051140071500c140a124000c0e820b940750b410740c03030301d540e02070042c1e18840003c4000c4400c140100015140c41300704400041078010720140b001c0303040c80f008100c9101c1d6a82d00c41d503c15038060005018160110342106e04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 22307164 1250 22305914 22305917
    0x50603060c03071403010e06010f020313120c0e042609011e180b04091a0904030f0e0307030c0f0e04021305060a050d06050901060603060605040b030411090405030703080702030f0a 79
    0x21030f90703601c100071140003500442c8090301150200000841111440f0ba2500030b02090701d80c07820410304603104a03641d009403000c150464610210402086038400c4a52154500458070010b043d40c0b070711040d4000c0b10049d80c00300e81c07081e02c0c01003200304900c562001c4121402c50240c1c01c8d2404540e07500090400688806d03441d01c214044003000c0640c3e0081001c103485010310100700f034026039581102c6420307800a2055000c014100340c0180002101c030780000d20350480040860156031501d0b01d08032400d0301c06441340303818042c03c0c406000150b0340411200d4000c510403594003150b2070411401d03c15207000e42c0c0c0101034035a40602031000595460102001d1405028000200c80c0c1d503e40005201104039406950420740c1c12000805101060700082d2261072803c0092108039600d120403030844007144103000000f07500f480203112160002c0000c43e0441c2c040c180800722a4900f200040001c1c4003501e040b80c0b079500000e000000c1507000310106601861500203981090302c6440d000400b0700c2040302000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 22308414 1250 22307164 22307167
    0x70e04082d12151f03110403020a0b03040c0906080a0302010b09040515100b0f070201030b01020d091502010f020c01140a0c05030109050c0c0a0b0105010201060f0b07080a02030403050d0504090f050603060c 90
    0x401c0195144038480f424100200400c05081030001d5090300e5280b0303900c41d0030001e0308000c1841441803400c001c4030222580900000ca206240c003528403c660030141003120003c0350000300248610503402464068030284c006484c14103000d240c0030382100c2c1d10325241f0340a8840b00b0100300c00302d01c0c0400c10203400303d41000104150394402074100101d50058009500324200403925440f0350300d210780a4a4000e200384c80401c418804c0300c00699a03200603201c6071b80040c1c0368803024000e0007288250340c1024041400085425010b4003c808180d0700300200d506020f139076840c4404040030b6998021a0000d42169040204d02801c2ca8000e0461005000d8500310540341d001041c030040d1480200c1d0741403e0090140c0350101114584521a800203203c0c050066082400c042101d9001940a00c21908681889468180341d0341c0c95000c513030800307150f601c1035000521000000c07401c02d2106801042555968a595034140640c5d40b00700c0300012180030400746000200141600d0004103950081808407560707 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 22309664 1250 22308414 22308421
    0x30f04020a030c1202041406030705040f020d11120c040b030402041d1504020306100503030715090203030d09060501090501030302030706050a0f09050f190507030b0702070e04082d12 80
    0x1c41c644255440100450b01d0498000b5007a841900e4000078244200c5003403007525603040c07041d00846000d43e14164584c200c144100207614203540482c10180d0340c3c0703d0141c107000d82510018129018070b1035011048100090943c0c40301c507a9101da50780f0125507038400c0d0074981010401a028040140300a0080e5540c10004581c090014144103410364000c0489080c1c2c54003c074841005007003030710101e00a01c10301d0045410110f440303183c05c046d500003400a500b0801c541d1a545204d0003070340c48100c030322903482140c03a025071030a20091000020003480801c40d0513403450074004440059000100b03403440c00c030041c000207501000700c40710640c05c40008036007525441070300402081c0f81c04489660503d003003c044c00300800403034203815020110041c0c27001e43e0204070b0f904c158040c3c1544000e0983c0c00560080c4001600039198541013003261040b104400d80300c0c40e05080032842550140d90b48180424900c10640c005003091203078a101c0c410540b0040b4400700002e8080c040d480410503000500d1002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 22310914 1250 22309664 22309669
    0x60408060726011203110102090607030507022128020f060724060303020712030509150405040207060204031101090e0c0d0b040906022511040504140d02010e0705010311030f0402 78
    0x10b21180100400c04402c1c55691020b420b2404120780c001140071a091400b104060841842614190303040600313250714040a81c2d070110344c5540045c0e02264003110841100070189414940398542c0c000d002c004000c0d4802c0c1007028040c100c8054038020007074014031200d400503116110035000079042035440b00d4075400b8910304280500c0341403401419400f12059a4900070201d41c1141080307a00075001d45600c1c0780c841000310701c43d42d0300e100b01a001c00e60401ca00c03081410413030b502242050072407607514102921100050166801504241e03511900410203105000d413411400c1d5181109081030f8102502d80440e150300d6040080070714900940102c0c0a9200c0280380d009079140d100020170400004480d450171a009400003c07404c500b43c440d0036000406455290200c02d20142c028a044d4150704081d01044040c0c040108210f400440402e00200e01180c10006140c201040d5000450b4140306120228a840f5041d48000e0406003400070011282c0d070341c241129048140700034100410b40d901d002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 22312164 1250 22310914 22310957
    0xf060c05010912020d030c021605060906070503030403050d0c0e01020c040f090206070b09070e040f020f01140c0a03030e01140103110102071d240f040f180f02030c0604080607 77
    0x1c068030528100031401d840d00da01046617a0440c003562801c000030030900b5403c03a07881090000890389092080814403261914101805030040b005200f280361600540c0c0399411a00141c6003180031034004915000b90031180d0182c1903510b012440e10408071921480000d581f004039000240c05540e68006e1441650040c0c3c100811458002e080542d84032064903081400010442d0780c81484d000f4140302080020800400b2405540c05c0384c036086001d1103940030850381103001215241480b205501407070304284440058450101503071b0240c9000315440c1809020b4079040300119000781d1501e0500d808a40d03503003050301c3c1980e400020144800e4812070040c0c0c5888201d401c80d2100e010034509484041c6031031010706228041030013490009544071104141910044801c80394032007041c0408000700d00706680049243e001485010480c0e98060b4100c1c3d0140880c1001a2000c1240c229071000b0340c1000c1040303844094040c0e8105252619010b45507450b210042c0444003003200c590002040e80c50543d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 22313414 1250 22312164 22312181
    0x30f01090f0c09091511040e010603090b09011509020c030403020402030f0108010b0307030f03180f080102090a05120a0308040305070c0617060a180e03070501060602010501061205010f060c0501 85
    0x14000c2040d0300941c01c0044008619200449a80110800216180003240106101503920101150361140a00d080c0310141007508045255502d040c0700020320051b42c502203500800b00b41c2c4000a040403a81428103001c000103007941900ea042003d103405400d4001202c0c1704480d83c1890058982c554580d44606502c141d030f0010b540302e4004400d0003500aa00003000b070480d25510003c01c4800000002e00d42c407644a44406484c0700000040d00d400300b80642207403241d200c08007980c6030381240c4604a80464003100d070810405a1f501145004c0d603802e001c01b4140203000216281c41c0c400018801607aa00c0d80c0000c0300400708a001c00110b000c040c002c0007070380d126590201050b000320b502c4c0d40300100b13000c0d510750500ca4026941c2001c25654240a15224107582c014100382a4031008101164080d028840c0c4003c4980700c01c1255001142d403c0c41644041c05150340041690351410301d008260f00000383c196142d6501c0c0100401c0328000b0b1190660448581d4100001c0d410f0f01030404a00405140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 22314664 1250 22313414 22313443
    0x501020c041a030322080609060403050702011b050d0201140108070303050f0f0d0b09070e03060720100c03051b0702011d06030f0601080903040f03080903031b0109020102010b0609010503130203 85
    0x3050f401542c00d0007006003542004082d00003000c5c60307610148540c0d0b0300001c1d2005c080d550404408200803911901c000e00b4014010b0404040c50700b48111400d880d2200e10b0015101908028024a06154203010b4070700c2c00c1c03c000d060b01d0680d50600d82170a8440104d0310004041c4000001c1d000305818481090300c180d800100c900c1b684504c5400031050107482140f103000d00ca4001c03440013032915400748103c031541c50005030041c5850343d0f400b201900c50944075040d450407400304c80c10300c90740c81c1c1d0100011b2002c0c000412001c1041004210050706030746000d084240940c2d6800b12940c00118000240d40405070246000b802c1122400b081464a9803c4056560802b500004103d0f1650010390200d0158000f0703601d0f410036541e409c200c2c40e106d0149014000490300c1904003000484c48513005810202c5005066a01d025913403600b045541c04034800d00c000f680d4446400d8000e40d031b0203200704181000c5c141c4209246c21500c40000340759110042100b04018915078083c003d5440c01c02947d81d11190305c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 22315914 1250 22314664 22314667
    0x7140304030302010608070e0106052205040c020a050606012c01050f040303020f0c010305100e0a020c0706020607080702030307140d0b0307090609050108030f0f070305090901180f060501020c041a0303 88
    0x307a04000340070b8039281c0162901d40c07082d01800200381691010043c101d41030f985d146400c00c3e182d480b144c582c9018207400640303101f0940f000450f440d07586215190003007020381c0042000103090300e04241814401041c070703070511010b02d0160380325400401c80000e40002c1880750301130340110705c40140c0706401140180001800c0c0410040308040d00000c42c8800080010700302c2e0704406614004605895046444201d480c041100410120a60300300164126400d00c0000d400c0c22a0302c807885140000691109006038040790078488829080300030503402c04054405940382d0703d440034001d00255420540c2d050710000024111500e2585540120311b801001070a4580386a900c0701800003508403401040402850071000003081000002101c5d940d88908900c2812b1820641c08100d040d003000d8410760510000300080390b19982c0e200341060280021070002289012140500b40031100c04c198032080403407601c3e80c240700d240e030002401c01d8000d504581c08200250340f0a400440048a01d19454040c4030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 22317164 1250 22315914 22315919
    0xc050a0b07050705010f05040816080904020d050105100206040f0f050c0405010906080d0507050601030809150a02060a050a09020a050f03010905030c0106030201110d050304060216021c0b1005060d0207140304 91
    0x24440b0080640342e008100030f011000108090310104d80d03081d100181004010401145840740d00030701c0380880d500421905081c104c40e040410140da01c809003250038560790307800501036450104000c1b44408424401131005242aa55600314a1011308025041c104150403620400008101c0c41050209c00381040c452565142c150b000900020f00070111280151403120403014404c0055482094001d0020402070b443c40e11065440e5009600f5150000300516102040a640f44010300d512050b070b80c01001180703010344488044403000340000c0141d43c2003100520260f91003500750030a6400403941e21099003000c0700020b0052052407030040060001141840a6100660119003100d000303807a851303c000002c0c0584c0f80c0b1400b801041c0b401007039092012801003a0540c0c041e00140c200c2441070a060003180d0005102c1144409c2881c2001d03a00242c41d4003000012820b060300902c800c8112600320341414002401400788812000b1615030200e03c1d0000c0c010040000084549200207680d66542c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 22318414 1250 22317164 22317167
    0x20105010f0618090c050c030c0304030201030c0311092b0302010914061b0c0109020d0b04170309070303081005090103030507140607120f0b060406030b09090304060f0c050a0b07 78
    0xd1080481d0752040d4240064228018000c3c14045044251031600e034a00f4820000c0042c5407002688040103801e11070551401d03820002821280b10315401103842c0d40c80d44c4001800d4800c5040304504040c20120a0b10001010005546418804440d941921005101d50205030346698071814250515011040c05054041d84042a002e000b440d44840300e0b40b145090a5079540180e80102c840f6400d403c40e034a0803d00c400c080c0444c0c01e503520010075101400e800086003a11200815100503405c2400e100801400004008aa0ba4954140750651400e000170302d45620052201605100003000050080150b2541c50005401c00400707407100c65031217043c001e2240e0404c0604a0b800600c8090380c12014a0010f00c80d845000300e590b0302480804407540c104003030314a900001c0c4c401d075120400c0040607030f00d510141c406413000f60740014085003036030304007d000340001e0041501c0790410002840500da000c80c0010300c00d20f0a0800d08a0a1414034185190403803802c405880da0142100348544913 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 22319664 1250 22318414 22318421
    0x6010201090b2a0306030309010c080705061005030105070c08090d020a12050f060907050f060d0e0601061e03110f0f04090507080403031407020d120e0307120f020a03080103020d080403050d0201 85
    0x283d0761141801180039003050600b0309200c103407521581036105200410040d841011160b201600c01c88605081201c00d58855190440c00c1d20650720b9082804024042410240301d4103034402c0e202e10303005400b1012a12142c5e014403802a05034041c400355102c5800303540310b1100781c00081c0f030550240f40b080503450810646452001d40ea04a0500502c40800d41480c80042c41e182900d9004001021030b050341d008001c00b41d03200da90a100090b81750f00c0181050702e0309102a038020300c080d0b1101000d000c2c1d621800c0f0203039403034550a6000c1c185040784885003c1c00310002e5900c1d118064030115039a000100380100a402150300032801941000d0411954950181816014620a0b00c05009141c00481b0802d000b2100301e54000060b80004110110b480c80780e9001c030340303a90a444001950f038050f44e210340e0441d481144180c43c007400101c00034504640c840b0342c80055a41e50310150010b8078180c2c0e00202600c00c10312000c2d00c25080d9011807020f00266030301b203400455001c0c4c00c941e01d0b11184107029018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 22320914 1250 22319664 22319701
    0x6010501080f010e060d02010c0605040308060a0506070809060304030c021c0213020c1525080108100509060109021c020d1514060706020c070305070602030c0f0c0a0b0306010201090b 80
    0x5080c680030525491440b0300d0300381030320785070650001141c0d26002400720100da1160306a0400c0030110415010800c10b1141501a5005e6540c103183c614082040c040510741c42e41c08603001c1c0500300b0058011505140580305428000c40312150707251110b0070203c504494006020b0750103515050844544600d031a9072484c0148240e450310ba00034020001181240100d46401000e81c200314000300301420410340300d951000040b0005d8880307003c50000710712010112082032010503000c0e801800b4281c3d0421110303c9190141c1d44c140854039201d0329481d1191818412030f0301003500850340b500641d001000303c07a042d246c1d450307045456501c001306400c090490f680802d52080d01c201408a5401556035589200110203480300f07141c02c0060355020020b500030181c00d1858022802d01100042042c1324060040250703174010340d02c848818040500f0509550b000007450391110071f4209507621a00c03801c6c011201c009040c3c50301c954a0100503070140c0464070005026000385000c00503060b01c0b14090b40325 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 22322164 1250 22320914 22320917
    0x3090f0204110d150e06010e04090501050106030f05060303041d04031101020f041d04020a06200d020102070209070201050601120905010b0a080d03060b09060403080307110d0309031103090d0b0601140c06010501 92
    0x54480d0004920744d95544030300590111030b003500e001401a50190058004405003c1d10000700102c00740c48090858000303030080ca00098540c40c000350f2001403030041540107081203014520b014a1302056158503180c808100b45a044140b001406050040c02511142c1191900130341d580c1c640224000c03000d40c060700400c00500c0500302090310b0700c16100403070b500c0f81c0c3e409030441d814142000c0043d9400d945060107078400c1d1580100d40c403541d09041c1328500c4a40196000961141c4440c0304001c1610001031090085a2401c0200119a81d026090701009800ca40000a0400760707070400354050018080f6182c2c1013102204001200b03c0c0c00906041d0b1402650350821256464940660242c442e43c0303841c2d50300040a100c10700c0030819820056401c02e5084c200b510002c1803503006030b4107281c203040312000130a9031503403000c0c285500308001403455a03124001d14940a4a03100160742c0514007100600091964000102c4990041040c3d140c3c0c0940303055060b0710b51280959580d5101e40c240a140d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 22323414 1250 22322164 22322171
    0x6060108090a0506060402030603030d0e010501141206040213020d09030905090a0c0914030708060103060902040609050402011b020a05030f0102040f05010503070203040915030c1d090303130303090f0204110d 91
    0x110340741004590042880e078440042c000da9102c0c1001c003c040c1d00302500855060004210106480c91240711300302e9450304180000c560383d894021900d0400c2210f1911b0f034020120394209402032900032030074581c400d80c119110355100c0e885102480090207006280d081c218982043d00342815005140102250307001c4504107800ea43c0d03800500c088d00d09480540d000310746c842c1418840340c2c51900008003501d07409070448460a69454415241c03010a0b4400eaa100350303a00034010550030300d40a408041c01e2040c805002d42e040030b0340001e08080d5070407114203000c00c603421840f046544010004000302802002ca404e00d03042c11300c4c518000e50242c40341c1c2c03114440c1d0680014040d401a01a079120b80c1c4036401039400d00c0e250540e4a005804400c5403001300f940c100b800880026601d5401360007416149802032403210201c00d1110615a0282c00d40c00707194014400c021805500d044d820075841d40c1840d000c145143c05e45401480ca00020304020342c4541800c040113a002581005840007034480031092 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 22324664 1250 22323414 22323421
    0x20f04020a020a0b040501111309240e06030c06180f040b0d02060a02010b100504140108150f01021903050a0216050a030303020c0a02040906020a030f14040b0910020c06060108 77
    0x2040340310750000c2030096041048140301050f040080c96038050300800001c41e800161904000441c1d1080603c041107900c00360051012404d03e2181c510400b0300d2840040c60180103413588424920f43e8414292034030000c1c0005492510140001000b04401070034060715440c214501c41540d845180b50103006808100076030407685410701640c032140034081d00b10300c410402502400b00c0c0c0c0c2c7c480c3e245517040d0b40d241c0381c50164070345540b03d4409052070246e485a8480b82040403444020300c07092081c03410001c48400380081f800400360150810131085031100c01d185498401170b81000164030020701019200781c401401e00d50440001d24400c503c903801d545c141d01548002c1c076400c543d1801959040040c0134070910009000b98001c010b07184c039000460704003500640c00101641e92260041f12a160040b504400d05a00340c010550114920f55062000c075444080c0710794106030042018102e0240c2a001c9400c0140c20b0003848028a54150290360f01c29030a140603a4520003503a100740044c8100000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 22325914 1250 22324664 22324669
    0x3070b150118030b040f0203071208032502100209030c03060112060b06030f06040534090b0913021303020901030f0209060402270a150905040b0103110304030302070602070b0c07020f 80
    0x2400a59901c0340150a0710b817225242d0305422070702040c08a82500c07400d840130401038032074450303000e0f260306c15000e40743d59140410302c00400c0342c10280c240e14a003014000754544c0f80e401142e001c003c0c0044550042e240d50b62207000901e031a11038101144c140c01810000b1403d540c0c800286a07003907004103c1030125107110300501080e03200445040c0c162400b41d02c00b00b9994a0f2030b801c101c0e00110b00c07e03168206070384000b9400d6100d0001c881d0040042004159420740160443c00107002054140c41e0355042121540200314000f6001703030200d028550001d4052a80c03550005c0e15009160007600115540d0303100d28003200000118030040e44102c00d60800500369103024000c0365a0208090454007940002204451441c410301d03858070b5026051503804116902482c0d46081c210043d59035a01c03202c0d2509003440f040700c89075440981014100003146d01c80d0440101140d40007985880c005a903281c907410104000d0040303400007000c48120405002d0041c150901810130766000f220740d800181085400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 22327164 1250 22325914 22325957
    0x40e0603070b13030602030a020409020316020709050606040b13080d0504091b1407020a050907120e030c030a0f0c060f0509010f06080606060a0309080310060f05040308160503070b1501 81
    0x403d090b2a40b110394140001103183d005141c00040c07004c070140c2050b40b41c0280301c060b81c1085460249040040c0348a001c0140d04003c5403000b00841d00c0e040080d42030240210300b851050707014103840c0290008034002080c024403140b00090010030103032a461000200003c0195102d4400c100304682060b9110042841c0c4182e51035038002c15841d4002c184541e40007205180d00001d10aa0703100444100010f01034540703003512031041030141d03a8040d220407036070700080c00c443e00750300400401e920030300602000740d5001080b40c888181609020081d941860b00c102c070408102c00004000340d0501900e080c01c81a181c10071401031504800a0210f01d80e2110300c002180c241d4810005541d01c1a00400c115052400003814a12020b140100c0c0f914640c0e181e0f40c80e2540155004405000c88031010440e03194400050b0360403a0207031400c28506451a210201d960062016800307244050358100c4040003420411914415440a464041b0b464a14400c40d02d0b800c1a103d0540410711201040a41c2c559190 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 22328414 1250 22327164 22327177
    0x30f02100e030a060b0f1011011109061b120406051201080a17090102011508070603060e0c0702010f0c0f060b01030b0105040b040902070309080a2d03080402150f040e0603070b 77
    0x24003c00348900c058403800040d00d03821400642010080c1e80c3c0f040c8581716508035001d698881d40380c802d1411304013000a800c59140f15905522644180b040c0c01283d84c480003160380a10389046c841c240c40302901911402e01182c0100303120403031030016000a56507042800f42c14000c10b404000d80540c0c0e65006601c0e1102c0e03070718030014010302c030f00d51603829191403c0d0b000e4004072006100009417400b0407c0d002c05500d40c160800180f0754400030081118651502811000e40742c418810300c0070341000c5c2c0b03180f0428042c0d0400241405a40400c142c1c42d10300c500101d0100c69041003200c0c0401c072050800100500300e0b01300c1c45002070b043c0083d0704c180d540940107c4040750a442d00c9940707000c1ca0400c03094000c1d04610011030030454002c2e00028050760400072460118000c0843c604400429039584803003010001800d24055038408207040841d8120400c1da80c020340640b03420443c0034060540541a1241d17041c08140000003103404074000e4140105a441031a0580841e01c0003074903666800b1080c0101e1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 22329664 1250 22328414 22328419
    0x150f030302030306150f040311030c0604050d060b04020f0304080d051501020706030f060317040e0601030b0a060804031202031f0e0103050c0d06140c09040b1008070c020f0307030f02100e 82
    0xf040403503000e08121411001c0c030403015003d141802c0c40c0184803a060f42c400d0b40b09440080324940751200614080c46060802d8004551091409142c03901040b003030845014050030312503840814000075188e0780c040390034078101c103582c8959a1400d454580555003004070001b44c41882d00300042c65a0385003555a0700c3e03c500c160010401c841c9408011005880d0101c800b841007a200d40c4000000307403608580d007610f21802c0c0b4040392154144200c9811030700008000904143c20603055481030b4940b62070300429076003185080c515070341d294102900d250740142041400c15100008002040340120f030400103c801d024500b60750b44e40e4501c9411030b080710030b000150442e001728a00c04010b18045503000f02e20f40c401e10010400d682a491b00440c0325804851000c0180300c0042d00c1d500600d424415810b425404644003407103080d1402004050403801407484003400315050500055640d40141110341040c01800c9540b100d07141e140c01340c4001d2401074102d00621502e001e0b0b6444c20f0007103503000c03c2500b02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 22330914 1250 22329664 22329667
    0x90105010e0c090a0e0c1209010b010e1512010e070905010c021c03140a0e0a0b07030207090b010c05120c061003050606060901110607020c0a060903030507060b040e06010306150f03030203 82
    0x442c001e402042d03020455803680030241c113000180040c07020807894807403e411540f00381c64107101030401d07944040050026100303900d01403010a06a0300300c8540344501109540201c100004520015a0344c0324010b00070030f1984001c0000a000c5e040030032050701c0b0310b846035a0450003d60b100019142d1040e80100294400d850f450400800c40711036095141050103031500085861424544259550110510320000380680c891102e071030810401c084000c1c1050111145021342c00e03280207444c1c00007401100500c0e521160700c0240c5a104419600d402e07900300381030b0f40c0d5491010306900113943c40100c424030107000d00c000081c214010312240104903038205000e1f03c00c0303698210400420f50301203070701c6605020409420f40000c070000c10070140b00702115001480c030801d90108100342002aa40600100800510284002381e401401d4842c0940d0042d40410b00b840800000f40241091407008070b4180304400000044c4015030f0010072600341e80d8858001c4140c1c49181d03141c1d00441e0b0b40000780250780f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 22332164 1250 22330914 22330921
    0x60b070f0f02130c02011805100b030c04020a050408071707030809010210050a09170a0905040915091a0f010e01030f030201060302030717150135070603090506090105010e 75
    0x400c1441500103449588145800070039507000031000910500c0400d801c07980c813401e0b00619902486403044ea00501c1d250040500f4042c0c5e669541c1d840749110b60340b000c0340c94000354007040d20100201600d4900040c01591249054400204148c115100c0c1031070520a0308030010301d007002c100038000507031040d20140c001c00d030464480b03910b075505c860101811480f510f0583c5540d10079a01c80c240c001e22403c080841c90700f001c0c2c280008050203458647c8500441045110600c0d074000d035104040b54820380b00403500d2400c5081c40000303003000f0001070180b2410900c0349010048169001c0032004540c80315000c140e200c10303c04180d801000d0060181403002540140003040d02648a045442d1080c80085500341c2c890f030200c1c2c2804a40c0d4440401c484c0e140340c4c1110030034414456400031040c05a0030b96034035850900301111244ac150920402903600c1400e01101c1d885d44d4040a080b00034840c2100d00c0b003030f81e940c40140209150074060314a4003590002c5818104180030700390403140001c5c0312120544 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 22333414 1250 22332164 22332173
    0x60a020a1b0f08070b040201030b090f072007080303060a17030706020d0b1504091a100c05030d05090601060f020303090a1502071a09010b0306010f030602030c0405091305010c03060b07 81
    0xa0718001d89425608582070b42c0010340c003100812010384640c201000701e04240c40098103803100400a64400c1c0090340401103c1d29030540016070144640c40e1101c107a0045609000059039070402e44020b5005141c00815251310000007076005420035210124001c0d903601d110021b180b03510400c1501c40c0c0003003001d040455101c0d0040d02d03c54195410008101418500181c00c0c00c07840c014290003041d000c9420040300102c1e20a5850802c5215101a452703441400003d686900000a031414880010079801c00c0c080f007002070700d20000030118101b000f4107101840076a200310900c80d100002c3c205c1c40312185882c0c80070044c0e81c000c00c288001040609410703910a50640c00c088221420710380e090013101c000c507101c0d500443c6050010399140c1c10300c5c2090225942075950342c4e02c1c1107020790300420040006010000841080f6074104100603142e44070401c2d20042d40c071403079100c0c6511003110420b0259612035002c0c03183c0f5161051000f008861300900b015400d961061090000c4020280062008903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 22334664 1250 22333414 22333457
    0xc012003030721090302070608070c0b0112061103040b010e010b040803120601051303060b21071802090a06020609010507031104260a030918021905071b080d02060a020a 74
    0x80c03400d0100c034083d240020a243c00c542c5500401d4005178054a000c01c001d0780c108040380d170030200324a04491815841d417142e031b24500b010721030a250040d04401c000300340070541d0703c08a160203440f03c409039281402d041100c10b0100038060040880007100000407941e1405e13040700c08590b038640196003052000d032590400180010140c0b07041c8042001080c0b89450b0b90380d9040044c600ca4040081c005500f1000d0000580018a0f07604801d0030302e00c1d10004208000079604100c4c0c41c8109602780d079650300b07203049003e07020305010b01c0c0d0030001e500e00c08111550007040c5d092040c04400300070401503580103011001c5c0c1d540b4425000c00280104002d00445036a007034a50080050200401c2c035582d06250310500e05210707800203900160501c0c00510190000d1280b1200300460500254101038041482d0210301070440c141d002400030000d00c510401829003100c0443c0c03510314800d01d0881e9600c81c60581c85071082c208000c018081d460020350101618400d81b9a0781d0745690340e0302d0208031030002000c0340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 22335914 1250 22334664 22334687
    0x201060b0702130504030e0a0807081c05072603070903120c020108070e0a031205030603070f030503040509150a0602160608010e0f071107030c1a0304030c0b15030109050c0120030307 80
    0x4010101820010b1908c0b40340d0044010440d00e00200404e500c0c110205003010421510203c1c8151112003a03540d5540c4882640d54503a0441c42800003d04000a00706031080700034460320341c40e90302100300182c1641004519080b43e0003072450101d2a8280103044507155040d90340280400c0005c400316420300d1040c000102c54120150030100c4881d1682c840100c0da02540c0c45060020348000300b08140d6040501000c0c000744600002d5281c00d6046580e459100e0045004082c043c0c0d5100300011103e20981c042028982d4014000009443d141e14000392102038048103000702a080c034038002109885007031040c1c12144e046038400c04e507480e4000240c4c2101e0028044004025000d0310890340360000784840e8000b9031140e00035003001807414091695019402c4c070501c580d00070a204000c007182d003060911040300e41c0018803d00705c0d52010300409800407460741050300b641c1313800c5840c001c100c2d0000d05004042d6090b21448410a0000c4241885100d01542c00c1034680003070000c288544d010b868840310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 22337164 1250 22335914 22335917
    0x10e030307034706280903051005070e090a0b040e0706080c0f09120303091002121801020d020412020a081c030b15030702150606030105030703020910050612070201060b070213050403 80
    0x41c5a41c060000404542221003e0600111105c01322602c0700c20702c16509400c0091414807407517441c5180c81d080e4480d003989141c6d041843c3c59000080c1035510480305010300b200d005020388864108055210024480701c50554040d82c07a1100440031a00005110b070201c1e5942d41d00c124059484c0e96402c415500500205030030340c1d0040c0b011085a40d280c10700c0b2240480244019a224903105510301d1500b49440d0380c2102c0e462040022007100d09480e0b0859a0060303991a502080500c0c0310801802031013011071802101e0b02c0401c001c00c517070f902c0d80e0804100e98000c40314003640c81d40340e040c41a124140914200c602e0f140b4040f100c0c00d540d000b42c01030303082a400100704070058112070002c80c02c40d41c002c40d002c500681060741e541c14940610884c180c2c01201c00e072080c506540c10100441e680e0340860201a1151000d040060056414a20404081d20000e0130b115100d1a00a07602d5003a4801540c00002550130540c0100d100c110200550b998540c0040102e0302410790401000f0060101400940 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 22338414 1250 22337164 22337291
    0x311040306020c030d0f020703201005090a030e03070501091a07060501090b04050702010615050f0d02040f03020a0e0c09061b010c050903120c0703060c02030705010e03030703 77
    0x804201d4920250410201c140003459031031106008140484490003106600700d4410710564010a130b00080d0100da07403117481449440c112042c100a840d24489489841403282072404100c2015800b00380400100e100351280201a181102050b40365846d40c001d0304e00049a03080c0802042003403070050100d01d03e00304800d03840c041490b25400181c450980140608607100c19810b0045d051030b215080d44450301c2c3c402088a0b42c184080507002c008090f80d40c03800c00902090b8045129520340440f4540030721141d044bd40c40d42d8441c80c088042e030f105d02c000d0344285400c200004498020309001031045030000c2482c0d2404460340e04024054028140c4070810090020346056010424030400d00130301c180f40c44a03074545030501c2c1050300e0801c685411a81080d001c2c801004840000540002a0380c0d10010124100021035000c1385980030300040030708a5030030710070203014024002c4011400b41c40d02d55010300450794045020b034080020032103060000d14001e40340c15096a5100f824149035299944e928 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 22339664 1250 22338414 22338419
    0x309030c140303010303080105040b030c060a0513030c05090906010602030301120c030221010e010911060306040902030d050301060f0801081e031c060503010b0f0108040f020102030906030f0601020601080c0f01031104 95
    0x1420312940ca4218040140c2c4000014018160480d04c105c0c0140401c4a0500100403c100802d4482000000540c015400031425182c1c00b40164181c5816191014541e40441d42d642006441c840042c41090301a549007000700b80e5600010500d2816150036800452442e443c000780880c0101100c9000e0340c0703132004100c0100050b51582540050002d10b1000502c80d41c00101c0720908440700c24000d964141c0c9003486c0b400005800c04280c1d0b20410301100e030980c803a501e52010a020340840280298103008100303407030f0a00b0340c000d00a54117a50181c3d03101020020440001d94408100b80140b00c00c0f540040e0503030b85a12005251240c1d41400003007620b00b0b202c07140d1045071142d03410845108182e40c0724030301030080e070070244521201d840080f1580302000d0000f00001c0c0c00c0e00ba001d0170180c10513408060400c2564004c2080f01c2d4070081c0600b0b40b41e0b0b03d180850f48003a10ba40280c1c0d080340113000d54400058540800a0b0b141c48242d00189101d82d120111001034004024034000c0d1800d030807062000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 22340914 1250 22339664 22339673
    0x6040902041e06020105011a0313120804030207060305040816140d03020d0b0a030201050913061d012c07030213030c09051e0906010902070204090b010f0f060512070309030c 76
    0x40c00c010501c4001e8814a5010081502d520700b0b00c64100104680c50040104a40b016044413500701c0c540502c1c6890b5203484030070b030305142e542d80030001800013500c0f0005114041d50100e4083c0c8101c0c000d03400d84081c00d440340c50890030b8070b10580b400307444108103008039109941c0141c0c60f001c40324401c5900ea01c2503120710350030509124040403450f000c00c0e40841d0003603d8048034042c4e0b41e4000b80c00c8a80d400303c0e6085500181c045e0241c5010a4000c0b55a541007101c7c11010394001d5026008401ca80419221502e00c08131005609001c0d034014003803040025203403941d0203070401d8001080c140004100703a41c1d807001107009410030382802404504040c400000301e801c04c1040d0000c0d01102401040902d0100700820394031040c012514212240c10041054500c0d02290040c1915090700001d0b03074521039400010060001110003428000e0a0000000c100500c680c10780100da00c01d4611031505030f0340e0801070790f541c01030a0b1801c3c920f404800010300000d04c65840007007070b60b2180c10404c416a585449 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 22342164 1250 22340914 22340917
    0x80f0702010e16060212040e0a0b13090609110405040b06100e0a0305061e01030503160f02040203091006080c0d020906060f1813060312080703110c06190605031b06040902 75
    0x18065501c001c3c1c00041c00b055030705006009020750001d600515240c40c00b0100c1081d07900003414414065039450340343c0c40740e61760300e03103a49a51500e020090100d5015402e00900508034880c0032207454040800c00c84890415008052086401262070b81da1a59031900b07002d0703101c485a04070000c0050342c2400c03440c0340d43c42c1020b11001d140078100a040d140f5003800f01410401c00000d0040c21a152040100f000034000400c071144030712928900da03041030042c64078840c0804180300007503000d4000720401c07e42c03c10007d010302c030915505c8005c1c0401d0360340d00b08a035103d4091000c1c03140c10a500c1e08100f00581041110380da04241c0180c42c1514110280002c00ca4541264000da1004405003006110070700d4260101d00d600301801c0d00c01c204140c555621260f0107510641188144160300001625550088c0e02500c4050b21010f069640c59a414400644a200485003500c0340540d200c15400d6115491141c481a5100039004246541041280c4088072410311fa01c282c0c040c00400022801d90040d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 22343414 1250 22342164 22342183
    0x7020f0a08120d0c0813061104090903030b0108100f05040e03090d15050105030610060e0f060a12050112050c01111207030906121506050703030b0405040503130806040201080f0702010e 81
    0xb5001625001d03d504400309031803200058008003c114001d01c40d642c1010103080c1072107944500001008142c80c40481a103004030fa2028245510742503040c0b0a05805400180810200342e88110481d5999080600c10a16900440602050342d62003401241000d40c17110f0f03014110201202c7c00c0c170800f100041c0081058950480e070300300f1480c010001ca28964003a45015020440241240b8500307010102d80180f458410700d8100300d5800000c4005440c0c8184540890f1700140255a40f25541034015000c02520108031042e5464400000b07580040d84580888450303006000c1c2c800024003400442c0c1c40c41461031414014011a89600b0300d043d141d400424400c0c0c880c0e2500d141c01751a02c41c0241008100100c0100e6950030004811020b0140c082e404082c0c0c2c1450914945403c1ca50070110000c0803203e40854100e032410041c4024000c00001801c0044081458501c0c2070351107034069511910140e80007400b14484c00041010f0484003690564045850b200009910b004040e0040c0b5102860703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 22344664 1250 22343414 22343443
    0x403030603120305040b0708150a0902031006030e030417280201120207020102060412090909150b060406090504091106070f020f030c090606160b0f010f06030e0307020f0a08 76
    0x106010020046a00d00111482d01903042c10000c614064a03203100941c002000395081001d05000104500303685100701d0403559002e801c1140f80340c1c4030300c6048000e41c030640d00702c41d030b042c200d81300010b01a01c00d0003110b2039408100081c50920f07251040180d007a0501b641079207001d001e54040400707031502c440f40b0700da00382c00510041403007450940009481086250300c190703041401040381c00e000d40d80005013160002e0b488154085e8622a07500200c40303004540c2c001c80344030b90030008900b091101800c12400344140394902005681640410000c143c429440781d4400314502d104200041e140030381c490300745c1c9805444001903078002d80c000035800303a21400040300c00c80d400c4031840086d410580e05030135000c1c0e010340042c4070250705c000024000110082000307204400001e010301c0700007a01c2613a002c0c07980d4004241403540c1002d94081c600d08009004100f4545144200003844512a00407071078080300d580c0141d86003504540a002d54026040d04464000705004800a4402e404100001c401d035001c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 22345914 1250 22344664 22344671
    0xd03020c0907031a2d130e07081204030b0403050904020f0a0c0308010e13171209070e06090c03060111120a03090311010605060405010f0314070905090f012301030b09040303 76
    0x4a107602c1c0b1460119854680c01151703a09120112401041da400f48801d0b180411101c000103004c0004550014000e52410810300b40300c0b105401e00c100040c3d5900b60b0704803400f554891441c07a8403c1952f4092844041e049200400c00b003030100740606d00810040101600c054500f4802d0380b00d00075258082d0a40384c00044041400a040c1940304040384e01400c94045161b03d642040b00b045c014600702c13100c02604219005490034031070300041c411660036000d2822000460f1414a043c0703134491006204000c00e0590f4080020103500e8100007507442040004021070954451000440d02c058820000001611034403080600c2001d204000d004091110ba401042c2d403c0c0c5841d008101e212413120a90407a030400c60141328565072402500c09490382032074603061217402d0707580c12005440300316551690465030000b1300100a0b80444140245c4d030040e1505260354803544840070146200344140522056075032050301d80d241106020810684c01490003140416074000018541d0006a80460210b9039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 22347164 1250 22345914 22345931
    0x5190c0c030b0a0e06010501140d0b04061d0c030408030103060b0d0f110406050a030203030405061e030112030305060603070207060e04090515040215070308061c0602122a090d03020c090703 83
    0x11034000c0c813444550036000382145516101c0064080801c88141210420012909640315070340d5603c00c805400340200107015140c0d513007410310510700c900034030714a1444100700001c40304148203040300d000700d034003042040c81c0d40c1c80e60300c4d000001c06d042c800c0941c0c800c1d040d002a201007096131a0ba1003036107014280c40e00046c9c42800800040701e02d950710241c0500e5101c007003007026035400310a83e0100d8900303540140c2d0f106440c1000c5121100b03e008603c40040c400f00020610041c00c4000351050b0b842503d082199403681802c1001c00c1c0011a03c040050380100814809103101d441004011140508041610307070f401c2c0d40729403c10b200d036680415004a00030401c404d61070075050494401007080c000c0ca21740b5a181e03c000301480e000800c158003500251043c032426240740b01148250781e8115100b151581c001e001e41d48100041959414681031075602c0c900d5050101503480150907400c1c460903483c0859401c14003000103c0c0e04801c0c0c065006900500e005a107800c00d03040d00c00c01803954002440031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 22348414 1250 22347164 22347181
    0xa11031b06011203020a120306030516030506060103020702030c0d03020309040221070c0305040b03130c06020a02040b030105060105121306090312060603050f0a1805010c0903020a08010b0105190c0c030b 89
    0x200e05901c403081901c1e498103d100429000714001d2181c0340c010704551030400980c1c00c141c002c3c1c030040d4402030140c030405495145c495079071170080e401c0c3c074820070643d9002c3e25090300440a901078000b010350f254007c002c0e0340103145001c4440034000761180c0152400c20802c40d001030100e81058241522982c140e041003400380300c015122a034440c089040c59000d29095803170007421030281c0d008040380490004045404d2864091101c54060741c840700c852032407611000000e40314403031110100d00035814003400140d20302c1c040c06454410001030b5121807d0241c003040a15152070080c00c030b140b04180544803140841d03468011048014084c1e1151090500070040d410203c401c2da038002c1e010580303040f0910280d40d802c61011070300f290741c007000802c00c00c0318120359402c0b41003101e10041282d0320702072010b88440e8100030944200d034000c40308515407503610f81c6100c1c2a1401c0400c032500065003004886c130200c0140e010038100080310303d02207811140d6680c1e001d0b003034001c035001611b51f50300d107104000185 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 22349664 1250 22348414 22348423
    0x5120f07020a09150302010c080405030105040602180a03032f030703080103021309020a060c05030c1006210c030204110409050108010207022e0518090c09030712170a11031b 76
    0x900d00f06104101c46661814400084802030000904100383d244082d41400b040b10140c2e405014010300800040c1070600d0100e000f0740c071275000c84401c0100083c55254618180c41014201c84d05030b00c907446540922034a04c5055800403074026000720001c8449100f000302003018100961007a201d50b1899419801040f11038000020451104c90801407a41c0040e1110703c071450456000b801c2000070b030b080620f4118114040c282c0b00c0310003440b42d00341035242007020f50080000c5508007144203002d40300103150140cc401020300042d0035504070110800050401340d0201924019a0303c2140c1825210302160040c0d810030390215085a4000c1094ae042d8a064070600c017070050300340c0c6070036003800040c03604070100c0c60701000c44c80c14000040b07503000301c4504810307e144050341c006019010364644030050105581000883e10b0081c030540e940891200c0304003401c0e015a941000c4441e40d50303061200c4034003081c0d100140b9401080f8000020414600041010340409042010300c90b2020f81e00241c0240360 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 22350914 1250 22349664 22349669
    0x40302070f03171804020d061a04080c1201021201090501061e08070c03030e0f0f0609010608100b060702090a0e0606011e03020304020f03070e090606040903051605120f07020a 77
    0x80e00c540e040000441c5102c400b2102c03280c03440b0594640b01004144d400d054094140d03d0381003800050800458100c2e5032110056071045e12100c118400182149005405140180c00084e401f008000509140200108881800c681d0015107001c01c0300750800d603101820781c401000e0302e440e24014401d03e0342061140c10f402c40d0300c6072251009008800c00800040c8050901230a1050404000c400e0502c01d402030107400c11540704070340c01130601c0c030030503a914001002d4440083c003920000c502c2844060144c04100c601000007410040020195040100016500e4075400308041045100580b5910744040c41085804400150042d030404128100903005181c00e0402800c421261135115903000c010300700d241d45190040e1243c0d51480801c0030840030003205540744c8a071100005010401200162040035000141d4260b601c40c001840144c1e280044002e001c2003060041d0300c100811103a000400c10700034003c0700d0840d00340c54541e045952000a04000d0300b03000240303000540c1440c8522400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 22352164 1250 22350914 22350929
    0x10b010315030605191d2407050307090801050114030c0103050f010909060e0102030c0306130c0c030c05150106050d06080303040c0312050d020c01020406030b06130e071b0b04030207 80
    0x2400400710344800301e000601000302110354940114403018140741000951072451101001050065101804406d021100e40c414030300c500ba060b0501d811440b01000000020141c840a81d502c40c01c0b000e40c7c1e10b81008001c6d4040200203440092140d41c240a214000c20070450420000f881c0358051604102180340018145803d15003409500301d611600d2a0442c1c2038644009400b460070b00e00007000c0d08401d00120705660002c4140089030106200950143d101101c844030440c443e8071400040c0c444108402c000310f000c0e1204500071070302070304910048a1040c000d036012401000700d90002d9250a80200300069404184c0c40407040c1c1c280f0074007016101d024011800c5241a95440c0010300d1103000c02012500c070b8214040300e0341d0258007601d1541800f003800703549035410a10748034005d400a01c248070000b4208600b00e41a41808012240c0c5441d0300104c00012500301241007004201c0505042d080141d841405550310000003989103000740714050013142802c00d0b0900a14101c0d0540002d030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 22353414 1250 22352164 22352171
    0x10f020a03170601020f0601090f0e0d050405010f050903060f04030206150d0204020702010c0c090209030606041b08090c0d05010e0606010203160f0c0f030501050402100f050d0b03070f0e0702010b0103 88
    0xd01080c0c100007450042620305030200c4669540400407420004030095000540c0b18980000c983d01c00c19030803410140050040401101455009243d5a80c0881e200d2001080d0104000c2c8255441814460079081d2903081c11850107001c4000b00c3c4c0f80c507104440e110806803000003071104050741403001607000800c1c40d074040c100c0a801800200c01951659009214a600113041811a4020000744400035007241d40303c08026a0380e1040740296001d190350a00c20b0043e5030000c0c00502c0c0078072815120074481c0340058446181040192036607007002e460306580e881613400c80944c45e91001300c8102418880c00c000f0401c071120140040c41d040780506401c3c1950014801c0701c20114100410145031074004004000711111820902e24405103504410324505d50100301000340481504036034041e500c247c0340d013110042d103c1c01c111000d03150034100c039002500821003420000c2a942004141210040545650594030200d011816a00ea0b10030700040300023604121903030790288a4440040d1302801c060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 22354664 1250 22353414 22353433
    0x1020c030c0a170f0708060702010b04021608161e0b0f010b0307051c2c0705010801091a03060403020105041e12030c020c04090606080705010302040b0d0b120706030b010f02 76
    0x60411061801202120b1803c03040300480c0d01d03800c110560b40400030f40d054641040d04c48030310a880b090121f96220240d800e026180446013400c2c402c480e518112409600186020395443c41d0b0554400e004003009c83c4058080c40011501461102d0b158103003a00c500131000340382c0c2c0340c85842c02000409510700501148010048000d0279401ca940c051140c0c44c00541e10080c50285c038a00c111468242403801e031030000d0140300041c502500e5007108940040b40c034000090549450742e100264040c85001502c410010010314000740c01540e120303880f0114040340d90820b000070901d000b030101d070160010b0791a0000d22050144c0e29241144240c1c060300a04003096135a1075941c3c05404c01c8c024041015500c0c000100b007544240500040d130a0f00030000c1c0480c0446007040c0014201c079004101d858060040001111b600078802c032401c0310301e1412260f04203440800010014022807c005803c00c010f44209500c0841c01d00080000d883c0984000502c90306800c001003ca1192113800c4007503600c00c4580 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 22355914 1250 22354664 22354669
    0xe03010c030c170c0301030204020906040f080c01120b01020a080c07030501050c1210151b0503070c080106090c020c090403210507140306010e1212040308031902040501080109020f070206120601020c030c 89
    0x4403811f6940686000d40d80c0c08079032003c940e0a204c4e650046c00c6140301108013181480380412111a4000c00340d0380c180c981d0701500d2961084440030300742240036074050325404c00052055000380122010312029611002d03a29282e40b82560b10481d940b100c20603000921001c071315142000c842c0c010100310000d110940c2030803ea1039400009848840510001d04285a842a000e20f0a100025400b809503078541d21507140892180c040d034020112654202440815503215510030310103840140e6000308180302e410000c0c4120498003400640170400301e10f4100e10451840f10f0b07181c2581c00c0d410360000c0c2c1440e00f5000106503891070820842124403c01c188481680d00010004119004032403a440c030400e2034029514114000019030b00352000032900105200c8074034080c4d803041040c01161740080c0501c0354000e01300c0c811030007603501040c00c490040c407100c1c101d41d001d40303a851040c501052074800a6000586250005205480d840404004100d1607580c11705c500c0070040c605800906800c001c4400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 22357164 1250 22355914 22355917
    0x120702040c0f02100f060b070506061315050d06110415020c0306040807081815070506060a06021507030f290409080d020c0a1a0103031b0b010603020a0e03010c030c170c 74
    0x1a03e4440e84501817404210b075554416801000000c03a0165510710526005440b08011120980b00b4050319860070491801800388000b044d001c0744100c100c60382090700304204c42c0d01240092724416501d0460500d04007003034000784090320b8648180000440d00100c001c3c5001c21410003207010307400c41b40500c00019a641d080d0360a46d50702000303260311500c002c10b0384128200910021603012003044005008500c60000a000b40d0f4064401e44901d075130f131076040c443c00d5015449040c3c0182e000b81d155540c0d5031821241940c1244c2140b4020810025000410701030718104070030b485031410207403010240d92107446002e8008150984060115181c2500c40345818060860ba840c120303500000d0f81082c1d807006200c0d4160702030340403031042500d0712801c10949450364240000c50218003d10165840781003030700406070f1f0700750780843c0c0c40407580e00702041240690443c88a440601aa8035020380c01039034280a40041c02006640004000741110070041c5a40c141c40000c803034902405c4144001030180d0340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 22358414 1250 22357164 22357183
    0x403060b040207020a090501050a090e0d0302070f0503030103120305010503010902030c120a06051906081c0c081c05070801151710030f0302010e0c0108010806060d0204020c120702040c0f02 83
    0x120005940034000010a002c1d114036038000b0b41c860702c41030001c15042c4a81c0e010a041e20fa041c1d07010106c407a1030301c1450080318881c42c40300e5440e501280132000312034843c0d0024100c26204060b400030b4108a5650740e8078540086c0c104813028040c1c0e00d40c803001180e2610400d4010302c001c03002402040190380110740c80f0b4403818006c501490003124070590b4003804000c1d420303a99034040d030108405e18004000005c3d101c2c0700143c4421550418030001449000000e0f81c107010044031080c030700c04030060901503680c138210034001c0701c00070018004044c00841075040e1828039160361601103814900540018004d00050b004484da1490300c010200c031041d841112020307412022031428541c6c0d25811803440500c001c5501c01040301e25801f074a00704140d419004030100d00c811204441031440c4550065507560000d014448069105000042c554680714201c180b0f00e0b8000f5100514028110850b1400c0030004a807040d100d09001460a003182064403c0e42c03ea0341e9140f400b81260191104025200c5d041701 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 22359664 1250 22358414 22358423
    0x15070f030504230304080c0402030402060409090c1d0601030606020f100f0e25050d1208061504060c0203150906070c11090106090617040b01050607050106050405040b06150f0403 78
    0x42000408011000710140003403240400d1510b41c2e0b00d41c00c4a284e03983d521501518000f4021200c443d0307001e04080c020390703006035030080825042ca414425148010090341e8003d03940c80b410418001146680390741c0e102d4841a1800c9205035a1610700e00150540f00150701c15003c42d4070107115400784160100d068604413400300404541205850f03615000b03094441c40d012594002c091420400884d0800034040c0003030385107603280d0341d1540e940400c040c8401606000d019200b0b06034143e201e0510403002d00394041002131000c921201c003408404540d40064100350041910140c448096190800c601c1d4400702c0d00ea8001e209904c9c050200d103850703c501030400401d1003410410b803810040300f00001e2010010140a58081d0744e920040140340c2c402d58400ea001113458461034840b03000b520600c86114640200720404d040e4a80028400e855100e00b9081c2c540b07541e225008100d07a07446005075805203000b0002d070076940c01c01a0401808a20220002c0e880701800c1281c0351200402400fa141280d802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 22360914 1250 22359664 22359671
    0x50702070b09010509010c050f01140f061509061210062c0d0201020f03031e070f0f080601050904140403020606010203040321050c01020a0917030909040215090307090209010215070f03 81
    0x4805c0182e60044682038000d155000d06a401d1488030015800050b043c0b07d02c0c6500c80940d19002d04202c2e14030000c0e16240c0d005290175031002079a25520009240a40c40500402d10707018040c588414000402e540048030210b0000e01003091640c01045190316400c01540d4070120b40c1c65602101644509204050040002044940035680244840c0e44c10500306015699213140c0400500e5042038045800700c0007203e04000300e011188550b041c41d4404031035440b030300c0c07801a40c1802035500d0f48000f444541005000c00140305103480350b015600d030601c0d08107246502c606041c0380103810302c80014140c50440d4414030042022425028030710001a295a2481800c848006411039491142000c00f1178550300029030307060010350002c0c1c030501703c07003503003503000c40003410400c003151684a0b02e8400c640c0440d102c00418090b00c0d04046001000c0f5483c2607140c6050082000b00c1d00385002c0f40e000d5409513034045040a500d580500032000852002ea4131100d5078580820041e05505d03288803d1002c1594 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 22362164 1250 22360914 22360927
    0x1204020f0d02180709060e03150a06090f020903010b01080f011205030d090b070809030a02030a0e06070c121b03030503041104090506091608010501050f0d06020708070602030a050702070b090105 85
    0x101c440c40e5040c03094001d0492054801c0c142c111031030341c0703000ba02c8460000d244110b00148085c8680044422010010003511003608450001505000c1c0075044081c1150b88076400110504207101d124090f4200140240c2c8801121007050308540841050b1818406804c2c100401c008004c1d040343c0c10f407490500302194903400c0f81030052541c02000b502024a0785400038000a02082000040c811103456540c500c0658500840300c1d01d90203543d0305c010250703105012a40d090340c0201d0301069503020281c106810704000e1303101c41d980d86600e41d00070b0741d090012900c86410701ca410341d0b064200c401c480c940901180e28640d401005848020700241403001c0f000d0308205d259865800506103d608903045403268100031034081e031509081243c00c8030000741c0490000c1c940c00f0600410381280c500814902c2c1034100a800d1240e18200d107202128511790800230100060002c0002d0010207004d0b160050310391400c00d14000407a200038240405650000348108420150602103a590900038600146c5804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 22363414 1250 22362164 22362169
    0x1b0302100207080301140d03051603020c0a060e130204080a0f02130504081909030b01060f051b03030106110f0718020904020d090501051b04050405040c05060705010b04111204020f 79
    0x3242034159290365000003078210611143c2c402840c142c449000c410b1440850007010803000310381542c001404914184604070100d81c055128860003806401601d0040d004e002c00140700000c55007260000c01c84070340c0c94165034146900e00c641450101c0c041189407506296066a665200500c01007a409600140300c0031502c400103505006070070302000b0300117800c051a140855420529203820424209216146810301c0b4540c51000c80e9003006c01c500c056402c2960031a85100702c4c00782e1b1010300c00100402c1000c11000c080b4003c0c040c031603101079501e07941030a100405800707039050000c1c0b42d54400b04415200c0200450340f1400c49040c0001d9030790000051200308040e0280c6135010380e01c14801b107440d0510703894a400c507403c0c540c4284000c00c00e40ea100d0101c00402c1d111003030301034200030060205004a042580c4400e400c24060021014426a12800240e01d68810310080b2a41e0b51550740c1e0724000e0800e800b946000c0b01c041d80d0401d04180c03c2070000d50340740030002c10192081300403403101030998 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 22364664 1250 22363414 22363423
    0x60b0a0504090311010c1704110103020c06150306060907020d0815060c15090102070309060e032b08010f0501020d050d02040b03070503100f06120917031906050405071b0302 76
    0x1400c01910038002c2e06442c0c00c0c0900031104150b00390001d5400c01e0500203220303120721070110325044138590840c00740d255078842c0c1000700c5001d00401e040c503900300a20b0f21411010050184950016035220052241d20b40a00d41090b2025106600410700f1030103124000303802146000b548100342c9084a43e075628003603c0d2808610a840940e048031001401e150801d402142e440c2480305c404030703044440d40700c0c40340c4076080740704200c0f0240001d90f078240c080c0000352140500c6180028010101c64001001c032400e8454070400340b00180360740341b07a410305003032352604282c4040c0101840e184550034a40340c500040d4480c44e41c02003003401c00c10000760304124014280d0585000e08000a1510f49900c0c0c2400701415550041c2d540b880d850141c0c90001030100b400401d9441035074501c0d0788040e600010442008080d00348008201c1d401c0c401c60700384c440c903800c164020314443e1001d078038840e1038607065441e80422079046801c414041c0c0d08000401c00e01640088140b0400c06403450002034610850a04a091 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 22365914 1250 22364664 22364669
    0x60409020a050a06110f03070210120b060406030c08060a03030e0f0a030c08030417010203060f210105160e01080108060c0a0216030809010f0509090103080d06030209131b080307060b0a 81
    0xc83d112210108046902c03064541c0c01c507400700101e56841880621031603603409914002540501d0340e40c3c020030303058402c44c10303c01081007095004c20f10485100c001070032504141c0245002a039142c12404883c0d80c40302000f80c2143c0151511207034217040d0b1310010301a00ba211850b5010707a92031001e60a02d51600078100d00190b4224003c1d0381810b45079551282c40e5405441184104c40f010580040420018030840740103000013031003004e05a5102d010300c62240c4104460552032000e11000c1c100d406000e0040d2440750511f1500c405000048000140c90388402c0c00c4403604000b060b40061281410010300160403113007041e2000c0d2200a150000c0f480c02600100341d5082481d500c00c004100030b10a0017522000000342c89010000c02ca4550403105401480820346d07015891400400120325403500405074000400404a00341e6201d8002c41c182200a031f81e02000c1003106d001402c00d01c003861801c80d8001c0c1600e682141360a2511400c0c5aaa00600300013800050f41c030000c402541d902c90800600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 22367164 1250 22365914 22365919
    0x50c09060705060f09070e010504050613090308040b01080114011e030c0e0402090a020a080604110d1505040b01030c0503040605070c0c0602030a0206070f020a080309010f0203010b250803060409020a05 88
    0x2035512051401540360581070b40c0c0040c0c0741411390041188080003007603100c252401c8400451a982ca80010800900001342c41e254210640e840c2c4036010502902502644a0080e10707141c015040a1400d07800060051780002140c3c1d2600c1346d1040541601c5580b681141c042c0601280000b400704514865030b8000da2005004a00021000070001d426041413481130740201d488004550790032242c60140e20034102c1003000a00214002103d520381030340700100300c0c070300700c100207081c40e0001a04e901212048a01c2c0040441c41000c100040c2ca01400340540e069420319060040018140018080b400094801001c058a8100180040d031140341c56080080d0001c220300c4059590b01d07006034503540107603140d10040c0a44000180c60600402c034001c0302c41c116034000c000300089501c40b03c1300c0e5000036004284e6035498080071a200740e118006036020b00305002c034080d42c50b010b0416140c0540c413020f50241c00c4d100842089004114034030162580000166000b02e0001c40394070014451914580005c2d6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 22368414 1250 22367164 22367167
    0x6030907090e06040f0b090f06180f0109020f09090a080f07050d020d022a030607020f0d180905090a02031f060e040c1703130608060906060306090604050c0906 70
    0x10491800040c0c0e202100e00c501800c0107502c40c2d26807003076190042124043c111400700f089000004094101c41a0301040400641f0b006c20440c0e00190f0070120252408030560780f0100e0f5103800c0304030600406038041a000c0007080707220403c0d800305202007001c10055105041d0240000c0511b4020310052004c5948000c203241e441108071806181604071a4055030319100d0f580701d508840d4000100000b80c1c4401d80c00400b0142c2e03000101008040c42c44010082800110300c0481094404100507801100b498001e4213170704c40c84905041ca4405e02d11500003c10141100e41510700d84c0701c1c03a2170825aa01010081065035603070007443c0c0392a0b10000c0081d09841144880f020000700900c3c01816110285000c0c00f03030903920601500d80440c16240a419002c1d511030030418100c8071031401c1c03103181c000c0c800e8a0914006039842e15428a80d0b83c0210040360007003080001c00d1401100f0503511102c01c951882c00c44c20114040b4040c6440203200318012599400130402c040c07071140030b66044180052640307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 22369664 1250 22368414 22368421
    0x150e1b07030c0b0702011e0207050c0909010605040e030a030c0203030f041112100f060603091106030a0605060309010204060210020705030a030f0b0a1403060601080708040308060112060308091504120f0c050603 92
    0x9000b098811501d0800c0d6002c03c500787c8145402c1d000316041c0d6500035008254400640c0104442200e001c4c0440070290340e107200010f480e4446010b00742c2c44411110180da11103d6040300641900c640c1e08084045420400c00c00801201d0b03a122140c1264001e203a4206070104900841c849408445040920b4820501c0d9903c0f2015030740c20103030031030310080e10034816207503129010303802c0c1c0e164940001c0c1082c1c05d0058918060501201541d40480c01c55004030314196140007107001507000ba1000e0805035000241400501d4040242410803c1d690700114600030175511119200d00804403400c00701900d1300080420206140c1041121800c010105c40225580390081c10a00010383d610902030302801000680710f41c0100c0390244a86d849844d80c5038169a0b07a03a0403983e0300b0000b8100c034180003e06c2d860724400c26403032040b04081c520490728142c1d501d19003000c21103244000c1c1d20410711490204814419410740c2003003d403400e607101c8002d0503a81803529150302c1241c49070300015082500030081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 22370914 1250 22369664 22369667
    0xc072a0f090203060111030301060c0314070221060f070c020d0309090e010605040e0111030c03071209060914070303021b030102090d050703020109090209030d0807030e060109150e1b07030c0b07 85
    0x550044e0f2098880d400404110b082d80c1781c407400244100c0340400e503821000c0b00424055107817801400404080141742c10501d81c00105211041500440c446060080046454008000c5c40c2e410081c0800214024170700540020400808030070004d001d10b405900e0002010f003e901c0d64000f03800c0c1d004080c800c0307403422281140204118482c0358415800c00e100070751040010702c2100030b035845a9861500d52354801c04080702c241c0c0003414200030030101a03210b80c00c200403403184850700c80c0b03e101c012401c0ea81a042a0341005202c0c1d08941e0300b81c00c0703c00b0401c0002d800123005079189004036005001510300d070000074020300512642d43e07040b0200c2800340b004c0100100d00101540d100341c03181c41174070303440e092100c040f40100340f0581d415501948030000d201c1d00440600d9072281007881d000c10b000308000c515605044007079114002661312040a11403100b6120444005040040291001071a00600c441c00d050340360b900000403100002010341c00d1620504101005a030401c108584c1801c18140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 22372164 1250 22370914 22370917
    0x509040b1e100306050310020702060c010c050d1109090a0b01091a030103050723010c02040b0d0f020306150102060115021e06010602010b010e0f04050a0605040911090c072a0f0902 79
    0x652512440c1c1c9001d80d0710b1810300130710884003520000f50041c00e100f0f40d407900400095014040c1030341e00000070300102081480c00d000340a240c0d00c15541c0c5940310000f030140f41c0180c1e18051035030210240c040c882060241c44451203d0343c001e2b0390b550007060040321040103803075403007035900321103807c1c05d003240584d007081c108400441c100c6c0d21890448054070f030340d110344072200d66400b0a005045114a42546901e61103003c1840e4a41c1c001040040d0451400c1d00050941030345407011260002c1080410701545000e00000d40d1150103a680c09140c0104100001e4883c8414001c44c21180c07940602214040d108116048140c40864201c0040c000848901640d0320b800f485201d00540c2454448030701940b1034814955000e00c041c04031780c45401104200300c05054010401442603039107240018880c0c2d43c3e8003940c0451030107006021b4040ea55034050140b030300c10003000030030344040400801c0c0004410506120303240c4071115240c1c8c015520b80c00d80683c514140e603c0200403064004012131505441d50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 22373414 1250 22372164 22372219
    0x30302070b0108011e0509011103070215010501030501050a090e0304030503070305030109050c1306050c0109050d0e030106090b030a0b070c08040e01050f0117070507050111030708010f0b04080a02010509040b 91
    0x20900d402da90b603110060a0b261103c040700e2400c0c0e0350340300300340340402107400903604240d800b4008204002103030301c2403015400c00c442c03420043e4404509400e0300c60000300007138090142860180659810140490b103a503c0d03e01c94000707040da40c1d003082001c0d9076040c0141c8024583c054142e030b95403291420b0081584d002805200c180ca4600000f01e103042480008a0740d0601c00c1c45c0c030200c4070918001068800c0e8210380c0d21480103540782d0580800140b8280600041844a5110355074040542424182140c04903000407140b00d180c0f0a07680916640001da611926a005002d02d01e995034400045454070000c00004081800104004c0b91100d007440d4228140e4070251441e0714170b40308240044a100d154240c103841040d061a02007813007144034000070300348140130384004030740c0c09140c89040e40d06600485400c800600c04a0040c40b118a00c03110710002030181c8041c59040c1410002d0064070751503000402418042c0c0014515650380712a0040c05034928024404204100b90407084e45a014200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 22374664 1250 22373414 22373423
    0xc050c070902090d020d0501150b030a0b0306100308030402010c0f0c1703030420061303050304050307050307081b0d02030109030305060103111602060906070b07020304050a060c1a06061603030207 86
    0xc04001c142149a0720035564040e034001c241c1450740c902a0248440b2004c030140a954a5499140c008110304002250300b0080014031005a42c0b0f20b00703852000700701c5100c1e4480c64440d070444402c2c0108650410400740a994100d50002e9070382d1100e00c010785050041c0d00c001441d9090940201040c006060315100481c0c58414042c062221070440f029120f20003150000d2103e003000c01900c1d10580020160a20090040d12886c03802c046210321210503500d96000b25080d03071002a050001d030030140241c44c0240b0094005088090610920513100c681002c11165600d00340414040c4550f98003551700030301500071380200858615410000e018120480f06a40880d08100041080c902d501003150700f00d41d8415200d51101d09181c4c2008003d80c805044980c3c004c5041c000a004a80d45807984d500a810540040d0740d200d1030700061100b10f02180d480391f000e2103403161401e00400c0310020308151200c1c1c200000000c039034a110005100d0300504440c126140440d00e001420990554018410f043c0038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 22375914 1250 22374664 22374673
    0x7030507050a0302011e03200415020303010602070915090c031a120d03090f05030c0604030f0503011a0915040803040501090906120b1003050a1a070206090304060f0c060c050c 77
    0x7908107000b110000c502c802400503100c280c0001ca1003c0e24540844000498940815a003984007810901c1c44143c2c10300c0d007500c070300000b01040f003009002c01005540c142c0740013450131589881c0c8040d44403072892040c94280c0343c0b15845a200c1300940b01400e070262400305002c20031200064401001404951906078030b008008010042034030744120f00703010700b2081500900d444a80300c0310880c05020981300449002c207480754074500059061000c3d00300041135070014030082c6000c0c02d0050456041040440c2803090800041c81034420381201001c044041c40c20407a07541d203003400030640039481c00c1c80b04180150003140c0415507a1000c030044c011a9001d0380c0d0480019120124001290058451a03075650355100c0d058000400348071025500c40d001c01c4005501d00d699840b00b03410310010503811601c0392804102c0c90403aa043c25107090300501188000c0c42c1900c3c4c050307c041c2d0303244194003589060041e500c10005c0d0f1340e4403451032000800c0c0c3c0700700140f01214075040d024006400c4651800d501d40107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 22377164 1250 22375914 22375919
    0xa0c0618030c200f240c06090d080402061801020c090106030203010524030601030b240301060f0206070c0803090f01110c0f160306180210111606050405040203070318030207030507 79
    0x38007004801c4054802400c0c01d00024591041140c00d6030041c1c0c60300342d00040709040300c45c494443d0b000f60480b0108580a01480c0c581076055a041001ca2003600703061101c01010301002d070f2905000c1e80c0c5944160003000880d81c05000040c2e19101c03403c22007030f0707020035010008600d070707527041c1c015604840c0c007520702c145407050ba0104824502d091610694580c4000d10000c1e0301036101380c00228001038043c0c42941000b44d07680034010ba1102d00c0d150701034603600003c010001c00f60700002015a491183c4060b0005003821040201640c2812802510b0188003101003600c3c0c0009100c0986003242c604020040d070140c62110b0250b41d00110001134041c000c017075050b0b0010038085140c10401e602d0075160303203003141140d4841c2c0c0100100c401801c040394681c0400f9005841d1a41c05841c13030440c64a980054cc403100d14501d1610080c0d42c9c4842c20510402c0040000e10307002002d403419511304890150300c0c0c2c0d6422004134000c011200d4046c070140c40300d000d680300703154002c200141070b00d004005441100c1d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 22378414 1250 22377164 22377203
    0xa031406030d0203030c0d06030f06050403080705180907030209040603200a06080106110312070e1905010c02040203151c0507080105010f09021b06010f0e0604110a0c0618030c 77
    0x1e104129200544c100700005a14882100d0003840100c041c5100000c5854032a240d060003800310ba00202ca0841d5504248000d01d40c210028590058103032400614021907d4243d60100810a400c075005825881c0400d0b90745000350107540341010089c00410100d0360320b00740500c20a00c8400140b05100d00c10060000300e003000b06109084d02e659484007605a46000000c4411100d02c100d5003407a80400d0101c03140b40810314040740d0041c0199601d080e010b00c2d40c00c0c00c100c0002c254144480d84603000900c00c10060360050703012291160121001616603891101646200064402c3c6590100006210903012880c40365103ca580c2c0c09142141c0a154841140608a41081c0121610801031101c10400402c054004000003291800050200c0e040d0b890300300c0ca482c0c401c1c1c200b8140140d6004091013404590580107a0100f01103805000c0c2600a48161080b0304c0b40d94400810420111000d0381880004c1c2c02920010b1903003100800035865600300205428104402210b048445800e00d20008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 22379664 1250 22378414 22378423
    0x1c02010306051e0d0512071109150306060f0402070602070c060f02010c091502010e150a0b01020a020906151224030606090106050318030c070e010518150103060b0a03140603 76
    0x441c201004410b08105070020132020180000d000c503454480c0740d84170000881c1d480060b01c0c0c150300c81c283d400e41c0c01c0c8240042007026a0024030341401040180d52841050744c0005101d41c206a00366980c1d062010000702140281c07103640e1010740060300000e40ea1003040701c83c041d66401c5440c3e03942c414600c000c00003030480c244c400390300000700018003582003403103800260024204114114000000c035005005503803800c01004451042d008043c1c001003203500401c80c081c0119101092000e849043ca10340d0000b504958050b103074030300400d0644c0800700400b42c05001c64100c444422801410f83c03070140c1010340c2c000021143d9848003402d0f54100002c500b00020523900030302009100034203070380c00c00d82c04a415404c003d0038040556035001c5070302e11036502440200b0380c0b06007400141c20340600b03000e000c1001041c103038042400342c0c103007107101f82158100c09040d0f900480c030800080142c0c05041c004034090031680e08507251610340003441c1407115400d45e22480180c4c440042d00241c5548440070907484 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 22380914 1250 22379664 22379689
    0x4021801030512030c3007020d021f02070c0306020301180c050a0c080904140103050111090d140312180f010203090a020f04060b030103030c0311030307140a0306051c0201030605 78
    0x140c3c0030142c1c100907030036028055030340107560956450400e81d100710690400c01c01c4144242c04070310555100c80c404500c6a004951102040c0001c10a100070030070003d558180307085a00010351680c51410602d1000c82d01110708240d00328100d02c022603103034200f10000358401e04c03804801c0070300c440e5004c1d111580c0e8042c42d0b207007032965150b5078140007031404203480403082428220f4418508000c1070383d83e541e940c4110341d190314040421204035030640c03420600f1507400d07040d03000003400103010030207050340c440c41c110100607801900e5000f40c80c1c0c81d500c0e60b4610f000d960104035485d40b901e0104900c0e040e200c005140000340c4a000c580040724518034080c00c0380301c160b0321b080d015040742e40f08101606048070085500710010b13000182e403954802c0130780c203d508282c01c1100010703481c0c407956043c1a486009130018102c00381c0550b19601300f011020b82192444214040c10300070105041131640c3c000c0e80044010726014181c1c0301d290440d010060b0300c800908200b240480c0c60000e000c10301e0308215458858 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 22382164 1250 22380914 22380923
    0x50412180b040608071107090f0e0f071206020d110307020c01090501090b090604080102030408090a080606010f110c040504030f02070b0304020906090c0d09030203030f01060c0506010905070504030c0e0402180103 93
    0x20b4030341400001c0701d00640c000c4c100300c1406807161440010200c100329640c0105691980010340c5060314030f500c0c003550380e0840001c0607a409101d502c1800e890205070181101c49041c0082c041c403103a4601840a0301902c1a4144460702c0c107000076546c40c0300d03400151700c20710040e400d8522650a00005550182c0c89010b1980010458101480000c0640004241d500e0001380f4884c2025036626500d401e99004540c101c070030003408192400a8240342c180d0f50b028180c0c3e003014110078989080021b103480910490706d0200b00814480c00701200707040c401013241600103001171045140601300a00407480c060360020041c803c2000000c2d14015800c01e880c059039005140342a25203807a81042108c207406003100c056900e0030028000c07001303220700c60810003602c40d03005107840c0e15140888450b0506c05030312074014082e911040c90006000458424191608801d00050507107a00b40c04640c40e0050b600010801d0f003000f0340c007240600043c04400c0c4240c1c42102d0b91021202c240312408c2090710b003031000a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 22383414 1250 22382164 22382167
    0xc1101080912030a020403060e07050103060e0f0609040609120f080106091202060a021213030b01050a030807031d060a05071b0506160203010f02030a02070606080105060307031b09050412180b 84
    0x20900742c0244011504400c2103500075040645030707142d0f081104d1324845d501071140e021070000c00c02541c244c010000244250b1045602500d414014400c008000901036031040c0140e900040801c03056034000c02901d500328401074000075500b100540555030b030f60403080100d0755041c00040c00b04d00c078003007210940b01e04240403a140c50705603007030110640000c10143c2c03d41c0541d4400c21501c0540d50f01401c404480d000405030300501d0340c204a212268181c1105018508001c420b2010031b48440898484c00d9040c80d04020038513450705000c428107600d220303c40d8000700c0007d072030508540c072070040d048050041018804101c09082d45000221143c41421382000091080d00d1500c0c2c0c084507101d071054005800400c107800c0c4145042c0480c0d0088640c8071b10a43c1c04244117050210520480000c0c1c01e084008214500381100003c0c2e0314080c034480201010b40d0004994100001c040701b000040c40b614a00703010a0405240425003401042d10000c00100e082a440202000b03040a0808071482409410f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 22384664 1250 22383414 22383433
    0x3022802091003061401062303071b0c12060b0a05030c010f020111040303030c08160905100905030f0102030f07090b030a0b0d02030703110103140c0412050f0105070c11010809 77
    0x20030381c003000401420301c5140c1c010001000c0ba00c18014803443c1524807842c0c45056040401c06042c0942c0c0f620401100400316400c5003451145404590f0132000a007002c1c1498490301d80d40f81c580310b210ba040104003c020480000d007003012090041e030014451082440200701400601c4075501151080030341c03552040989004039400703400101c40000c7d051001140203103c4100c0c110b2140d110303030f05c202c00080d62a42e2001e500c41e03001600c0c1d80c001040031140280141c0d480802000745e6190300a062181400350b040791100c0340100101c00082c107026080c0c4051800081106000b500200c0d24414250710380c1c00018100c030b204142e580c1c26110144003080c01c507181c5402600081807543c5103242c01414018242001da5400c0000000540c0714906c2007003184800710005040e035082d80c5c4c91a910728149070034030041144400c01d40b410f48080201c1e0321000701007418110f14064140300c21601d1546090f040c0400c8652140410071400e000f017454000e070101a074011201c5220848d80007a4540010802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 22385914 1250 22384664 22384669
    0x6150c030415050403120e04060e0f0103080a020f10060e01050108040b04030302090d0b0414010f020c070905060103110f040603060b070b06040e1c020c0a09020405090f0408040308040e0403022802 86
    0x6542e400059140c4181403070303142c1e43e5001c45090031104d480007084540515a07454502405641d000d42003c0d007845000782441c2503a0a40c120040c00003c3c502000442c10400301031003008039a00e4a100c40c0210360b2410305a9103440020403050140380c610003502d1001288550041360058045d550100c4103c0d039582da43c0c0c800310001c1d0001e619041e4802c3d00102104041075182111714017481c01400c0042410000380002d6003160038050308503800318018407061a101c0e00218081c400c48810200105290703460f503004900502544d804801d010304003203054003068000201510960b601900e0400c8013035160842160b6a01900c0402800107040d100022050300701038201108600c015011074101403010460720644107272160fa4500140d000e09000742261030240d000b0002060200c00031031509061001081c004940240703803801046c021004601000000c4088800458200803c0c989844c0ca92240d0461500c043d1030030f03001441840354882010b41c4143d5003183c0905070013869445c0c411039900303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 22387164 1250 22385914 22385939
    0x803040b040e040c150216090c02210c0a081309060e0c0a120e03070605010b090d2301020d020d050604050609060d020d0501050a060303091a0901030b21030306150c0304 74
    0x3113400c0310030400009008102203a9100c41c00007546c014201e4807020788220792001000b5030100030640d0901544103c480d8010402c01d03982c44407031585081007c01c10303c3c1440b640c4a03d194111700c501c0707001a000700788a010405003407068002c00303c210b02d45039034412100959600d03000e02d400c02e42c10f0802040b15605014000e241481c22400c02102e5911600714800485402503002c5802d600700003120020080180300d00383c050803840765030a04010350800424814020400c0042c00c1c4012121024070380d4030481c49000c480c60348403000750341da030908941d000041d401078100d807034040c0d04080104000c1e18003806240e10611000d4101080e41c0d9900c41006024600c00c4000d9030464081d9800d003011402c00c0c0500c40c410511030303102007541031031807400500142007680704401880c4441c2492180001d0002141c1c0818004d1801150544081000030060f04001d05c80305000810603200000800000c4060340c800d00048600c0110900c58030f030104d2583c4212404400c1541080006125a60a024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 22388414 1250 22387164 22387171
    0xc03120f0402040e0c010f030b180702030406021c052a011d10020f07030503101203122f0306040204090603140c03150402040c050c030d050907050102010e12070314160203060a0e0a0b2a030603070803040b040e 91
    0xa004102c07148007911581d084840171080800c04903402c4542802882c0c1c00c002d08108080111011032506961070f5001c42c98c0d00900b0401410048001302040415541480c40740c054001c440101031800d5092402800600038003902d0908a0705122500740c500030184a50415500c045c02c0b4071350090003020313039a5142c0d40001c1c400759002d50300307110110f00b04809204040286104220003850403840e1841d135442e060f007440540344030b980007082024406403001da2071608903505135004030300c45610304401e84003030042038800140c40c400480c0c804c421520a8019a000b12021000c0da5125070704d03100124282c4a000e01e0f4041140e00210905018140c0c00c00144400f80c040c2c40c001c010303141c5a007000307580d50788482444501414003414280540c80c003402015044403082c0d00401c002e401c00c0503403c3e1140c0b54010007804c03859407940001c121a450f02c06020010500381d05804801da94031807007033b400b80c1080d00c00d280030b071044100119002000000702c60580b55150a401d0400c0c3c40c00500900c07182c5d006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 22389664 1250 22388414 22388467
    0x80c030a090602041505040509090304050d0f17070317010b0a0203070308061513150503040f03030e01090210030e0f03130b0c03120f0402040e0c010f030b180702030406021c05 77
    0x822001a031005c01c461010b0346041c883d900c0740c1e95940f5210400c4654900500074100c0741e0810041007003195071384001d401d05160301c140031314500506824400b61608c0c08000302001503400140301000c0640c00204948020030320109001c060740c0b1943c040d090b5026020812002d80d00420007440417a0040000c2948000d0060411528407020115044507400c440c07004401310903017880501c00c085140c411449011060304d0500d0a6207030a4544229040c600c1a0107002e160342c031241c40487c80c500303401c00e50b1010b4014156014100300138200030000d044800382145140102000b01c1d16404c404000c950b410a02440001242410300307d03840c0f90b0790310262041540b07102c100310407031010300c000d40b6941c46412094040c2d10949014014042620710800744849140c000907040711060b0b030030541205172005203140014031100c0b00800b003194010100900c1d12411040c100b0010116400001030040d1141c2c0e41c00d842d0905001c00441d19194030f4081800040340051000d0b4070304440003100d20a00c6502e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 22390914 1250 22389664 22389667
    0x1050108060f0a2d09020a02030703050a020a020901030813050303030c03041101050c0d050a120b030d1202090301020714011103071d0d06050a0903180b030105040902030a0506010909050d080c030a090602 89
    0x100d0031040e5008011140031307041d4040b103222080c2c080c400018064002d1103c80e0055250144030440251240700e400342c0103003030010104000d034a9078030070000c0c40340d583e0340604041e100c3c2d41c40f420111802c0e0032090f6500c40b41201d140c404180c1e800c011090b039001d491402485800c40d15599183c03020a85d4010303520307041150901c004022942c0030031282c01030104a0301c5056440c0c3c000b440081c401541006400c815900300450203034907480004480103513546500d031450400440c185c0002c00b902c24140c101c1d92660010408901348540da02d003903100f143e00700008101090b2100c45140b400e0008503003040c00303d1841c010303000142c1403410458010150042c00700c20740301c1040e5101e10440d01c003907c1c013610480d40c0d031900200705600200d046161320450301c0507240072440d000007000e03544014003c00b8000c5894400207811910100580e00c6401d600c40b003075a20030342e10750070a00002c00c2c0c1c0701c2d001c0d180c500c981a081a102c0d40a0000b1074002c45542501c18519076801402e000505070702c01c0c0c00c840c2c1550 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 22392164 1250 22390914 22390919
    0x204020f09060304060903030515060d0e0106050d0605090d08040b07051602090403020105191506030207060b09041203150b0405040b0109090606050c060f0f13080904060b190801050108060f0a 84
    0x85800040d0310413840303885c00250301c0740749013001800c48000418050b01b0102d24603030041d15039a05020380c0c0c079950641c40040313140014000e010b8090549580490b0b0070100d5140c080c0c08000f85904110f01c96041c8800305d4103400c2c02d03044100d03450101607501500d8240a0000315480030b2080d001861034415864060b40c012559601181240804440590040c1d6452041c045250507204401c81540c15040c2d051110200e4002c400818007118425281419400507002d010440d00303400a03811101e004203c1000c0b4900f5081483d0041070307500005000070301d045c0071880e413079251880d0300e001d07071340c000302c01034242408d01003404024030305422801d050184001000940110038000c040260050755512610350700b030104a2840c000e00a403648510200100802091804000d10941d0100c01c001030b410008032507041c13401d024401d6080308c03600182002d02c00704140010380004c0c402c940d080310100d404440490030456007807800780500e600050804003c1850791500400300020740b0001004514010ba = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 22393414 1250 22392164 22392169
    0x30314070c150807110715020f0f07060809070b03042a0306021c0605030d080402190e0103110301050f070809030d14071107030309030b0c0c011a09010602190204020f09 74
    0x72000d40c08003441d00b450300800e002d001e511070100c030f8000149051002103082000720b455103900c5980261110205558000c461a034401c0200e51040d030705401c182c1e102c441c401c00726142c0318a000c1c090003012400701000300d42e130507900152220407500c4122425046440301e9035445a901c001c25008994a071a000c4100043c14002ca007410044d80715610059494600000444601035488000b44116142240400a5403000f0840072100302081c904000c03255a03a2002503400300b012045008144007488002c00c060006001490689000b40a105413410a010805080e12811101d0ba4400404039001c035040c140940312864200b864641580c0c100652100c512086480152500354290b54080030721410a8020300780c224001c11100c041c180d847d00b1511301034440c1c44140700040403007450900240504010005468809020f80001c0c021070903007040580a0f444d00104482c4134000100000038a68000203002ca8082d241e40c84009052099400301700003500145010318840104108115990f0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 22394664 1250 22393414 22393433
    0x9010b0301152a0507050406030f1203021c0e06011a16020109080102070318090203060901030803071704140708030903070501120207020d210504060c0609050a15061809020a03031407 80
    0x502c1035419260100f026814042c0c90981d0b01d0307000c03500a0346025021f00114540c0c480144003d070b0003200c00d100d03041c0031181c1200240b00d20f4802e10025101b00025011041c4241c000c6207545444008940b881e0b41c076155503c1d90507040e40b00e01e103ca140c0400c190030402c50410f4112200b1030050400c00c1500741e48141541c203983c0003840480005a00c002c01000300c1e0040c000c40800341004100442c11490300e0750226903511010701000d807180c800800001e50103849629031482001440d41456102e00b01882c003a101740302540d41c03060040c0a8010301061400d00042600d0075800004d00030441c891030100150b80190141a020f02c039581c00300070301d80160b05c0f040247c0c25258400c0d1804c0a202030080d01156010030003044400801c07104001c06c01070158410b012000b66508594005522200c0b441c141d890400d201c64020260130480840d200e00f12555808501107540403880e0319003a5400d8000e2008880d1148002544a12088010b001107440b584000c550640320104070352500d2015260640c09 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 22395914 1250 22394664 22394717
    0x3030e180109020a02120703020a08030a02090a0902030411030d0e0d030903080c0619090b07031d0d050901030e06010e010e0903160501020d061508010308090301020418050603070509010b030115 85
    0x9181c0c00003020200705904001800c4880080c40082e4107040c2152342c029281c15102d803000e4925135001c40402c4614076150304540c404a8000e140514140c0c1d900c074400c01a4101321004e45804000061580f054100814440c0182c415a5952104140034000708070031162102c006604002140c4000310008241c14002c00a80035000300402c4030746003500310314140d80c203945000c504a609222440c03000840c0d06038600e41040b1a41404164807055803403945070166240085540ea206506840490940003c02410104001c1c2d9050090382d00381d80e407035a500c140070310400240550210040040716041605103400c1400c81040c2d03480c0c00c2c40b407100c0301c6120384500000e5440b079600140d82c4a0480540c4542ca000748403071191204040569217019002d50f1052001610001c00000c80039040e69081d41100c01a0201c0f01c0c0051610030f206070701d075000744022500340d4042c0c400c0300c0740400d1303902c2d01d900c0e100e0407690102c00f0249980e0074009060031428104040809025903080c01103602080c21070750491303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 22397164 1250 22395914 22395929
    0x131203020f04030b0411060a0207050607030c290a060308030a09060b150c071a0306040b0a0b0a030603050106050414150a180504050705040e031b0c0402031008061f03030e1801 77
    0x2005e0910b828017505034981d56501512803402041084030658010843d0070071100101c80103502ca049070308059401449082000308044c0c012080d10307480304840d0012840c588281c0034100c585984076808801114041d000c0601821000d0000500654540e0004015548100b4003c6031211514001c20b54041241508200e803010109000313016080800c1110002c0c409900600400041c0c03d5507000144006040c0c14042c0385c880491400741d48501035030314000c00702001d80540d120043e040050040941d070004a46950034883c0014180c5010b0155031000c885c81003003440d02c1c1c2c41d501d03108510301c1140401c03e500300056500000700b00218081c403a41814000e14081924a080e240003030400840750040c0703108620b0088a640304400001c15a440c941c40414640c1c912101070386400e160046130040503602500000c100312402414003500001ca64002084a5035500ca1004001c4000c15038250364031840b071800b60410210b4405d05d42c412100002405600c05104001c0120f0f664400c03d030403105 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 22398414 1250 22397164 22397183
    0x1b0b0307050408060f060a030807020d050304090b03010f06050f01050c0a02060403060e060702010c02062706010306090b010803040b2a060705030106020d020703020907030509030c010603150b0108131203020f0403 93
    0x45409014044a0345c041c2e03458070345c810755240610000c2d0640406000142c000d0700042a6181151a45541da124240c0c014080307a40f80e40d80d400100c4040d03c50403050a000354201264181d42100a021301010794100a0012070100169401110340e50855080100140305081c02100561604001040070b14040c00000c03910090f40c410390b52400c030016040b0011a0314000000b041c155001c5401030b08501d507081d402d01030358094010900390280e01c01d14595103020f540c00000401207a82d11000310b00d4803035192010350740e03a540080d42c0c90b8025840340781c0100104000806500368107403060701d44101400080c6c5915103100d403c5a00d0302400b100c04201080001006010541c0c040040b40c01e002c04601c014488241940d0108054a801038884401d0580364000300303800e000240151500b000a40000300640303503403401c19117480742d0322400c2001c41c90303d0440d02480035442101400d1081820f500c40e103951240399941c120301d80d40d01801d41010940c1c20b2040040e05001200180010f40c003683d84c44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 22399664 1250 22398414 22398419
    0x120606030902011e0c020907260f01061706010516050109030e130c0c020603060301060510020325031b0c090f0204090506030d020709090f020603010b0d0b0402090105071b0b03070504 80
    0x2401c0c840125070800325a014036004d843c0c801d03622401112240b641030b40e10300561b40740c0b1103081c1c1e200f0b070100c150254810508604107580c6001648168800c42c0d40f42c89000585e40c0c3c6540c140c0e1a0a40d100461072034a10040001e070142d400b4400400c084d03280301d0400140124079483d050b00710b0310312a0003100026205840a115890704950188807902200001c110f40107030031034042d000ca1240319000b03016000201c001465641c1c203602600040001a04107100524001c000070f4030380d40000c8400e50740038075840d400214004c0c28181c28421540c16261180018024520008171441c034840407181081c905801181410150045c02c040700c8503101c2c0580c4490a009500042c1c803001803846002c1c1d4850300c2d0208130300c2d900089a04c0ac0303070900140020320010500f0314410b05e01500030065000203001000284074800c500041c11580c004070400c00100316220100000d82c810099501e002410038410303000420300c00c1d03a582c11500c803440b0408000aa4a00e0503403034030780080b1070240c0070a2000c00c08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 22400914 1250 22399664 22399667
    0xc0203010605010503090a030309080705060108030d050a06030201050a050c011d03070b060607030804021912030c051501030c170309130c080703050105030709020901030902030f01061401020f030405040c12060603090201 96
    0x200340242c1400d00f0203604624142003215540d4400420107010180c035a007060041c41042030031a01426040000e9809940e147e0040030b580c3d03071000844030142d920b0b000014410408a200d8401a40d5050b550145004048031040360386c0d401c600d50403242d5550b0303070b01c040084a48004194880155007005981c445240d82801115504000d02050152004000200c0001d6100c0c0100e6072155045079a100e81904008550601a1254202e50301220a99a448040c0740c9c028004020842c072600031102c0081c0100c104408080f0284001410f101251900b071040d640c590021060001d07907141102c0c04d101240c0001280011940e00e55403030f00323a540c2c10385451281d03c400082e40c80030f40c0c2d040138001c1c2d503d403001081d902d001d01e102d403060b40d40d40444c90340d140342c3c865008020032a400a0454007025036155000e4003d01d2580f203070080122011442c068035500220b01024014062005182400e29050500c405040002c000f28100075241281240c01d032405d01c1070b08046d00041e5800a0382600c140700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 22402164 1250 22400914 22400921
    0x409050406180318270e071211101d120114040602070512030103080405100e0415050907030e0303010314120a030b040510140f0103020c0f0307110a061403040317070c020301 76
    0xc0c1c5c40301040000b0603540d540030000300c01025107008a00040c000e29004c00b290601c15250032484807802801c45c0401800b00c1c4800390501000100c95500d00035030700078020746c0c40c20203410540e02507402581d804640e52070720410140c064030007000086407001d2507071100480da050481e0112081ca9003c112403040c02010000a41e14940307540601d4519411030711210080d02551103028420300c0b8113514080810f10131690800c41d40b101401c00d0001c1204102c4c4441468414064140034011007400540080c1c80f90058250b605802400340d455a421070322400c100b03144004200485114003143c6000c801d035168018082d4a24645d400501c0700c00107010802035441c045c01c00c1103e060031a10a0025002d03054903050b602078119481059100c2c40c5006a000c0d000c1c003804000603006000d40703101c00c0d41020005149891046084542c0d42c0d1280013044807000030350003807500145005540305100c0d1004401107402601900b4030302020f042e0030101e25039036401210504001600307012505c045003401d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 22403414 1250 22402164 22402169
    0xc082a0909030301031410061403010c030203070905040510050d0c06030501050a060807030e011104180b0603270c03030d060e06030105070203030619080f010b091303050409050406180318 82
    0x21000e4103242861014075075a030006010251501d80542c90407001075500308181d60754421a00c90510015aa6081c0d091f81f01c50000c18140c020350910b0141103c1c0b81c0701c1d02c2140e1103182c142d283c100c0142c0c18082403000805000300841c80e000b81c800c4000c0b40350b5807111070303550b24988940181c1142501b060b00007002d844041c3c0c0114011082c0340418028039401850440e4800c2d003500d400a4281d2849940501400d1007201341c903440c800008010600b040c015409113500c85000c0380038009110ba070b40902c0168801211804103042c0e2141106403040c503020003041c00806d48408446017401c8550000341903a200e1b45c000081325680742800c10942d011211002c1d400402200204610300c0c0c02100a0b44038440105514480d40410088139500d12600c40b5444c00340c40080220f0303007800d05580300b00b0f00814545410601c81c2d010303100040e05c008417907120340301c1d556419603d07207040c14680980a00039080c041e2045440c181c40c0c001c01600340710403811003241035000742d84105006940c1da0403819480110b8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 22404664 1250 22403414 22403419
    0x310060806062701080d020c0312120c0d060b04091404020a1e0306060e0108010525080a020c060a0603200f090606040305030301060c060605060903060703090c082a 72
    0x1820421a40c600810200c0e4420703400e80e51000840056410b88001116002c6651038542021002080d1204c0c0000c2a500340030a54003111110003024040554448103078000c0c0c20f40450401154218584e162a0b071600404101141d504060511401c5070684809410510502d40042803c0001c0803c070701402c0100600140700310820f04144d000326091036054007414032b0030700014640c00d141080290001000310b8224000b001b800e03031515117031100361a00b80700e51400c2d582010089040800c0a80c143c140360350314038410400c00c0d012940c040d5400d03030000700809012a404d018268616605001d070038410b80e07409000240b1141180342c00948c00e01c03403401f144903074000c0c0e141c00115515140b0181001c020b045901c072500f9910000099650f00c1260001001400080000106207810030b10042c2003a10504043c44259142c1040c0240d0340110b1701c4656140d072244000c51809402988049200740c0a905a9030311251a001c10500e801c8641044004000002c0304546601400200b50320080208 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 22405914 1250 22404664 22404671
    0x60c05040308030a050c0415020615031203010e09010908070602030717011202090a1b02070806070c080306010305040312060825050102070302010513051e03010e0105061c080403080d02090310 84
    0x11902c420519000c02044808115680c03c0400d10305030780782069400914020005a8910070002c100030b40fa80301c00c2d150103c5070480b03800039003c2d0740380114a02e24101c40d1080800d05581c030b071a510403d0340d1006424118555681c81c0001d0108036034000a00750f0701d016600151703403030500800040903070032113020004041450340c00501115500e2141c4010b500e4040303d8a02c0c04e0388070661003000a080700000b103004940560400c0104036008030740a411550038400341d410a40e95240240d9018400c207100400b0f54100b000010b44942c0a075109035005130291034002528800300f48107004550040e0000b101c20740c40b01c0103040503083c00c0451803068601030002e40382400e00d007400213592500345002c024144040810030a102d120f0007004240108801401c41c2465040304824440c04c0e50891106802075082c801912280e038014003074140100c401400302c11200d05101d950044007461f500d005c4940c50000c1000002080c485405407030a080c13031003401a0344100d06002c0602e0503040c0550103203160704 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 22407164 1250 22405914 22405919
    0x130b010b07050606193c0806070201050601020a030f050d05240102010603120305180d2a02010c020f01051308010c0306051009030303050a0b03010e0d080109060b09060a0905030f0109060c0504 84
    0x1043c90005d4121400b00c2c0452403001d410440c0300401002a19070074064441c2c02c088004400b61081804007159030000981c8c50b00c0c1c442038422400d80e40b046070082e0240e80009000d40c00607100388030030b0100160610300b9074102050b07407003c2801d50b8029035212603201c0d03d06e458910448039030101286001c000740000c00c071445c0703140d80e600c3c0404101100d40c401c0c140c0e1080041d60641c0781107200032003000300c07405036540704204110240291009210789414040c480012060140347c0010300d4450071f4050b10707030091582d080d40c204054003081d19502da040040a108110040001b4460034020341601800400c070810802c4004044901607806680b0450390780407107140a0342c1140090003665014900032510382c0e030b03031100d0300003510032604016015864840724801035000880c807489003011f00d0f50b5582c07082c0d90310621207040c1c074918003600c05212400c0041e0903080c500080107101400746800c1c0300c5c00702581c1b03c000030b00b0080402d802d409a65103540c85242046041c1c41140ca00c40c95a00b4140e04260 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 22408414 1250 22407164 22407199
    0x506011b120306050303070302030712090b09100315030c03050d080118020706021c1410050f0f03070312050301060201061a0304120909020d06051e0303070308130b010b07050606 78
    0x10103844081d02120120307404032580362180e04900c000e0000a0b0407617944620f140b800030343c0c1c0e0f800340030140c3d10070714440042c03464280b0a09090342210b412002c2e403800c000001c420800312640d91083d00050540c0c0d180030000343d01c0c1d0300c1402c2c00211b02620a1115441ca1403d1040c00c3c4144c28010300d00708590100140503210a05070300b041e10710034401d00141c0b41c6a484c94031100920400c0028280e0720113034504400000030a40040c3c1225011604281030341d190303000803064603c007901555611051600d0042c400e030400700ca00d84038105004040301d0146030349813140300ca482000b5100c440001e0300080180841d58090140400400080d02c03100700390318009802c80e50070b02015200812142c0d4401c46507103030620845422024000c0c24000719920f21550310107000415540c070a243c0924180340f01141e413400c070303948480000d10020f8040c40c9030040a6030200c2341c1e4034004003982007801d120602c101c0410100380205000c0c240007017415030364603607d0030403501e0114000c10742403051b60864580741c00034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 22409664 1250 22408414 22408457
    0x42d0923070915050702030a06050105011d0102060c160212030703020d02030703080402011b0606060503060a0e0108060106050705030408030304031206091b030c14130e090d050f07060b04020309010504020103050601 94
    0xa4501e141e0950180c2200f0804a46a22411001940c140704000d0090207010b407952106040b2542600c41c904030100d001c0c040c882c2d00c10203c20942c05a00003100044400306d034000201822010400710036119185503000440081020340000d54541c008a2803800301901089880240629070006506200c05a5002003d500f402032009041040340e0b0f0445003000f0401a00341231f4241c0c00402406070780c1d10382000500c16002201c000b403246000030703000240350682500c803070f040c2c503800780151030580e0800b00203070751551040d0021201c0b0b210812000940c040144044d501640c802d80d1003000302a01044a0419940c194104c420054a01440c1084010070114100920311203410b0106002a482106980e000544400745c241c1100c0021401109001c000111040d00e04001c0c80482c2d940b00c1503065580e440d10308260308081041040b80c091101031913006000340501c1075401003001025400468280c1c0c0040c0c0709140300740e441d0000e100131076805004a9601103020f10f09000ea844411070308010700d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 22410914 1250 22409664 22409669
    0x15040b0105060711030616020705060408061303021903080f0f1303030e010204080a03080105030d0305060a060302090a0b040321021c0309140708030301030303051b042d09230709 78
    0x54100010b01d0804c00480c0c020401110348002c041c2c4d11640f0b044401e0940303502c0d071500b400e8010302801202180601c0c1207402d0707405440c223000080000c0e0755034040c1412400304001040d006c0d4403c3c640c1c4410194410b8540d03983c3d0300d00c40d40d81d003101070620940e1414181e01c040c00c1c1c00b180f0403440b4100301104a40c40f186642c15a014540440c60f40c89007421240244035a402135007050240b84c11080516800000b80c1e412110244c08071500080602d00482c00c9903020b968856111078901000c014591081d0040e0103401401813802d44510764491129600d544583e000320340610080124490800d40c520100c44002094006800c07022000101844113104041040080c50303621145507081c05a8203910966240c01075003141d0007540c99100e03035680e94000740310440010f82882c0000e1070031888902d0b0001d03540e07070075207005080504011002245210696210b00032202846104514000b80f0020100405501c03a0001e0710034241c900800440221501c500000c411403005d008015034004007a208 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 22412164 1250 22410914 22410919
    0x20108070903080a0e0f040207020306010b0f040b040609060e09090303071206090207050c27040303050403021906020a0906170a0e070902030903030a05010501020d0206010e070e15030915040b0105 86
    0x4040d80c0305103060321034815079040980218004201d028507150040c200e04030300b0a0131a0050110a015401c1101340c2c131503880029016042079004005246101d40509034000303070340140909180e19403c0d400d6264205038041c00000d038001c00204841608100201c907020b40569551425280202d0456074920010b0080c13410070101c41d071890301841c21a032100307010300700d0807105541c2c2d00200c0c100241d40e850401e9156100e911498459903880207950300000000c0a040c2c80041b15560307944041d0700500303001348280e040d030080e0206031403020940301c103002d11140b0035800180c43d14003140e00201508100e80080e401e0090700c030107460014803007840090380005110030120324405002011030400203650b110140e00e5001100f4070412002c044091407042d040e408040246a9075203004a075a188080c103002e0150300090010f101860040a44980c00a0725041801e00190840040340e00701d00800c40b0f5042c1e03102c0c0070080c00b4542c041409030900d5803100229001980c2400d855418030100c041c4034051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 22413414 1250 22412164 22412177
    0x403140d06080a0f020f0a080703020411070605090a030810080307080705030f0a110c01050f03041520030f090a0203031207090905010902070b22110a03020603040320070308070201 79
    0x15440e0001e41040300503110480c1a66018900362804424240c44014224800c00d0b07859042e20031420000302007812100c0d0303040100001442c1d902848000c00c043c2d0841c070303e181810000c1c08003240c15801072502400602c002007095400d00d0074010080d05020b45030840d00c0510050402503d0000400d6405680e0080c0300f15035074409602e021490340c0f0900d03108219940307000c41c2c1038880e99007104030024101040300a44448007040f0004450718801d099240b80c1020060001c207010a15032051014900111000026003400354081031a048500300c1c00c1401191001080200068070880840c1d0007520942c018448000ca80d40000c1e200c0c02049103190b11030b0b440e1400240d940d40710722002001484110310411807941c50b582480040d40c0002c40644020100c40003149094561269100d91806140c000d01c5581c180d42d034404110002c2000d01c2d6034411880e410100150b512036000b50300a0340301c0c2d100d110ba03004095401c0c2c0b02e005104841840c190f049100c080001c40c4408027202d007170580c2480d140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 22414664 1250 22413414 22413427
    0x120a0b0429061b0307060f0203040b180c0603090102090a05090705120a061e080d020c0105041707091a010801080307150f021c0b040b0d0f1410090c050a0e040314 71
    0x31a140602d180f081c001c03052951040e4100000800100b50b5540101424021403040810080a030300c4141d600414030082c610004004141780b5000718040c2e041c020550388c4d010481030010b80140c0040c0c4032a04103035800644d5000c249455601000140410350f0905494901000c0c090403e0040713003600c0f000084910000344005806034400c1003d00003402188002d2100d00c00d500000c644503010302034141c480c0d4429186164000101c0300b999180580d90945030a0078140d88102024256501c441c1d50700c01c0b0040482d035000303203004600841041c5003126440407040e400040c0580410383c0075001e40e40003040982c01003000c954081c860311603d550081007202c083c00c5000c000788a5032070500306980c0c100c0308005d4031060b140c1101c550140c0860b01813101800b0201000b203030100d1054024010500700211100140401203044410341c00501900c02000000c0c105e80240c400324a02100c4603d5a990188158030305012000701074022101540f8013440c140d580030f0710071211b5041d0f59a0202c000f1800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 22415914 1250 22414664 22414669
    0x5090a0b04081902070603060e0906060f010207050301060b030a271209030b070c030207050a0503100c18140907110a0b150d05010614010302270409020402120a0b0429 73
    0x84800c04602c0c00c070441c400f070b807607400c0003034403150180078070f1000034203040c8000b641900040406005c1c09110b400741c210358580004000041c02c0c21402c3d94158004c8860004040e907003840341a006003200985141c2e079107080c00d4444212000641004440d08a03c1101c90f03452121856803845154000c544110b20800d80100b034404c5080c0307610042003189140c1c1000714171a4030001c0d201050b0305c00e8080711001e5403a04200000f6148a005107134140e8442440c008081034641c00c4218001d40c1410407802d4131041e10042070081a80381c015880d034100c00111502e850030300201c520b40c09038091500c018164280300307002c2e8803001900c00107401d140c2090003040240300041402075071150001c100354250207580c034100d4044c0c4528820007104190310500154594000d000301d46414554070459404505200c00450050150501558006a0769104640141c990b8070007000002c4c54400034400e42d14195034000190703031038006003a00581c14480b1300800000742c0e09941403d03002c0c0101d51807056601c0c501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 22417164 1250 22415914 22415917
    0xd030902030102090901060e09240d0c050a0303050a020606030303010e06060304020a081009020306061f0810030204020a03050103060b041119020a0f0605060a0905010b090103020306010509030601030506150405090a0b0408 97
    0x1142d40c0c0041700100000e1030a030030a144011400013601d0345a0155120f0f114032a00038140058031026a12000b62500d061516000344442d403032103100e03075452040c0c81b640031407514102508110089000001d120880e00d0701041510f92160b0210011442c42d03040012020101c0d801410050160001001250440da954504a00603000038411514400880605036002e000e000d034080e0300902609020403040e081110070840301348414100c105020300c0784a411070300b85000503c050088a40440084016a10f43c00103014040c401c3d6004501c550441c10014101c6002003c120b12942c42c2040708066811003c050383c00c500311468000a0800080c0030607030034001c0982c4d0040c150310b558500c0204010300c940c4503c0c01000103607008030b03420b0785600030324088441c28015000c20301c2c2e00b031122503034942c0300340c0007194070941c10701d03055080c60b4000000c40c1c40c12030280c0044a81d60008404c114003010344458858811400726030a10407070510188480d200c4006c50740c0a00100c0d041c10000d814085040e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 22418414 1250 22417164 22417177
    0x9090207210302130501050f0304120903050f070609090b03070303050f07080301030c150f17040c030b041101080a0209090604020304060603080a031e0b010e0d1419051e0d030902030102 81
    0x100c0030a0a0700101400600075800981400007030404514040f8155105106551840c2c403044003161654603151079191950190028002c10407040000100008070180942c3c0410841c900040400b141418009000149039401c031614591074020790b035903a99000943c10f41126054184682d031034569000030344e82c0f8441e10304e01030b003012400000041017200102100046680740841c02da0884056072045540348000b610902c0090760345d410044258402018084d001485036010b490000c0c0d40355907106507030004480a5445a80000c0c8803242540c1291030303a5401600c800c1c046207080944000103010160140c007040c0580c0d1b010000404001140d40001c1c061900502c1ea151500c00551000380900400c04800380c6001450f10b00030040a42d41c09090700d44c2c80161a00d864200b404018030520b407180341c0094444640d011842c00101c1000d0203180510200300c2500051124681021b17403070b2034a4000054040c05183e100f031a90040c5c0407880c92200300c5203160115036070505000003806401180b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 22419664 1250 22418414 22418453
    0x50f03040305030405240715140a0203061008010b0a08090a0c1e060302040b0403020402091504140a0f03030806060705070302090f010303030b04050402011b140f03041a090109090207 80
    0x5010082c004004080c00455100b201c1414200b24242541c0d0752102e614160f059011405022000c0082c040f0203545040e16180e00001031031807516040d618800300280c940501840c0c0c004103004003030600d2180c9800c4148541800007080d40b60595601c00783c0301d155101c20030030017003002240481c1024803150101c680c211900c4400d058840800d042c4400c0c0064211800d02014140000c1c02c3c0e001e4000c2c2c80071a9101e800b41c6003007901e0754080c0006984685200c0c0d5124422542032840484004007410281c03a5400340c0d00d031218800e206000114a441d084000c40700f400d0213041001036803103c034056002ca015600141c8601d5549042071a0015640000b51b202034800100302102c1440c1020038100ca0180d903080c0050b003681018081282c0e02920042d00181c0ba1a000c440700c2411181c1c0c0b6000e59200c1c00d05602041c08021042d824850541c602c02219080040c0800c1842018006124080c40c00080e45141c8042240064034003100c908c00d5075034031a004252441407141c1000118801c1521 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 22420914 1250 22419664 22419667
    0x30213051002010212070804020f0105070303021b0d110c090402040b01090308071a01050103090c0506090105070b0c0405040e0303090a020906060f0c0f0f0a0503181c03020303070801120201020c0904050f03 90
    0x4074401034080c0d00410380140000c030404c4002100c06100c1c00302a405250080c141c82d40b6180c407000115111f40c080481581416020005001100c50902c812011054160050a0151034448000303005050001002a02c0c0e0302241009640707a40d400c20013500558101c4002400600c0e070760050b00d070038016900281007440c01003000030034418030714003c00b220300c1d8160402d846030b03032214015000c44200c00005011614140300c14001c6040140007040b089070705040c42810410705984a4140b003030121030300005000e004c24100240d05081c011446100c0340800507500318035107005481d9560750f00010103885602000080307510303612641f04452400a501003090b80c2c41080300d11450740c0765a0303184501c03800e100300310005c2d9801d8008909a0032007503100c0090f5282000c040d042c0003d03112041c06003580440b040080b4200321401d0300a65000c42d11a030080d603264607103420050803024059010240081d01c0d4a60302005031703070200c1c9201c3e000d401221003400c4da03100c4d801e00601d0080091040c4020340310 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 22422164 1250 22420914 22420939
    0xe030a030f09060309170a0e03030f070204110408030d110c16030b0a02040305030a0804060209040c180506270f0405131109010509010306090f02030610090518190303021606021b060403020c0103021305 88
    0x1115009040b01400ee44003070004d860360342c2044081c1c0c0310f207126429264005206440d40c1208175084596100c8400c40c80c0c500700340101e001e40b82003211250181e1005005807a08008000700108455407003890b0320700460415107103444480e240d1040a601c84200032020300040c04020f125419103020000c094801c22072034690030320281c11420002414601c1324104c03480000c0c28901503085921041032980d25082002d0007a21201444014031300250b8407031808120050f1a440d0740c4207191140c507244812401580b55410102034030306036206000c1c0112042401400301c2e8449841090440790700000014a0031a00e05160240610528009605024400c1845130a4504030f44500c1543c5959000704001d44030060400544a559410354a04d6049000040a1641100b11603207460b4003e0801620b8409441404034111031540b80071a1390355030100f50310f840e541d1030807a0b207414505281d0040c9400c2c00e20307490287d0f448000340c0f001410190002140e4030100d1369900d012006180180a1142d41c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 22423414 1250 22422164 22422187
    0x60f22030b130312091101030b06040e0403051312170a05070c090f0c0203090d0f0302070f0b0a030e010203130602030c16080901020c030604080a050a0e030a030f09060309170a0e0303 80
    0x7024035000d40000d1030f41071801000d03141c180301d05c1840a6104c000700e00b0000c2c1c003000541c09070103107148442d84640700b8080000c0034040706882d544a24880e594840d56114916403207146400540c10814003440a845410300103261f100c0c440412001c0c1100c1d940e22920500000c9589105039035000f07151804018001424401940144100a02210381440000d00b030150890341e03801664111640003e420114001190569a180025500a2050341e200648407640c0c032040d6110396100402c020400255846101d50504c5841c411f070140c1c0c0020340c40c500305030102840c44d00c81003802511060340040844c0c02c58450104440c281c0440140394003420710b160402d0322080d00100c0100703001d0701444148400c3c51501003100791055038072200d414141070708407400715403030b8101c5000c050130300204100c1b0042135a0100406064144260380300b840d08100360303034020301540c2c8960102003418201540d200018200350140174949411184840e141e00e541d40c8102c80650b01444010b8150200061605001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 22424664 1250 22423414 22423441
    0xa06180b0901090908070b060f0603011e1715150409060605040605060901050a0509010302040f030b160906090b0c07050d0803010905070e0d0209040609080412060b060f22030b 77
    0x3000c0780c82114582e6600711400503140140d43c010001c501c2041403000040207400c1d0b00b40c0100d8050104090000d00300c000c01c42a500a812040740510803d221101c10881c210480700640b242d407030750b400d50011054841d60b03640303880281d4031607900741070002031005200300d030100021100083c42445801244d09080380200030a00809000e0780c00c080011440f0b0038004101c45102c007044c0d44962410881541c00c840c507812404041d41016020040000c1244090341108042c501a4200030220300303210444512100204102105104a990080040715041000c01c0e04603115011142c0c1c0d10b40d5030595403410b2603041d0b001039620142100382e1070b0074011182c028505071801ca07001003255071076071041a618064003003402c0e98443c2120140e00014200707000345903041486000b0103e0240e41980d9400394035080751b040903c0180209804800b802982d020720310208000b6200c0d1850005c4c07a00381c0384410720540705041407100c034040000441c0070140b02510000d542141d040115801c0205000141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 22425914 1250 22424664 22424681
    0xc05120a080c0405100f03060801060311041a0f06070302030c0609031e0c0316050109020909010b100903050606040504051c0c02010f0302120103060c17040507061b0c030b0a0618 78
    0x1e81c1d03640000715000002411a8281d0300020079850b850042500f0455a41408410b0b450405488500c00203440400f40500b0300514415a2030000660361a4240000c0750325200d00d019002c200740740c4001590707e900180b40c400c94000c1e00e60360b81d1000e030350400382c0c518401c0000320169071084c00c00f080301c2050040054010142c414068000310743c440380001c5090b00a001200306250070801503503d000010040e6019820f105030004100c0b9411a00000c1241d0303c2180c100030142d440348180001c2d0f18003485052884c090742c0c10015481811034603255940d4030000c01031805607580f035000c5024440b0800003285072850b500a120b900601185005080102c172503000c0780801e245908d04480070740a40290b0f170400c803495002400d40c0c0e1854550201500511620800340702503103001011440090801c58801e9001e0b500820000d0b2a008000b081c1901280320b0310f000c0102c1c004000b00145105c00d40c1d2085a1300190030358215100c0400c0c0000415456008080101c52209440401c01c0f150700078081c0f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 22427164 1250 22425914 22425917
    0x302060c0f0d0b040617010b010e030a031202031509070504050a091107120908010c0801080601090203040b040312060e1602060c09010c06050a02120108030c37030c05120a 75
    0x1115180d40c00010028041d4a0390099004024030a465041d078003a4010300c40c0140060001c01c1d240d603902c20b030b10185100005002d140307035100c03001200103503002120150398000c15001002c24050a0700e0090088059000001c0303c1c607000008140c2a165074002d182c3e42c2e00c8010101402800e00b0400600b40390300903c00d040c00740e40d20f5800082e002001c3e01c541d0394481c0c0d01d03030786d02e46c80c00760282c0d078030404084c18040e03c0d01440001da60104481300b0034828105100581e07120480e155061602052500005a00c68500c0398010010000003a05800d042e9403c1641820242b4103168400062009080c1c55041400c0e524009020401e64082d0202402c00741c00280d005d860b07254031101c082d50701170b00c600441c440c0840d103031320307aaa0b00048030f80c0d10580d4881c1d4178500041c02c2070301130403a1861110003039005010360750000c10580c030201c00601188020420b01003100c52002100094240c4c01074000d02c0d0540c1c0b02e00202844020306004c2c64103c0356103640705064400820900c07801050035040f1282010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 22428414 1250 22427164 22427173
    0x20a0501180c052404060c0c0504090804030201260a0b010806010903170f090607032a020d02060c0f10060609050303040f0905060a0909030903030e010305060d030813080304050a0302 80
    0x480d20440101d0004a06400501900d0418109400d004130011003c010462080440240242c0c2068000190014060a0781c036180004001c0c00d00c400c440c42a60001403045182c00c01d014002043c0b0b500300c0f0100e950a00700b03001c02413a0988028034a40025200c4002600080700300b280404c0d00d40c1c488402c0035001d8807007281c1515408011100c01c551400002c0c80e10003072844481c19210302c040078010700003012a025103811080c502081458001d81c4003100428826044180b81440820141c0000c09516110201122494000a94044400802030f02480000071000c203044d03403e000e0140954000c034211071000c882c2c01d4403103000340542c1c45000002211100d010a1a02d0f0202c105e50440d00c102801105280c1444521401481d01801050748440701150008480c100c600503604403070f02940380d44a200f451405d0203031417a110910080c3c101886d190411440f0365034500803a41c0c0783c0d0185041c48856441c61105a00090b0200c0054140784003c0100800c100c800036852a00310300c66420349 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 22429664 1250 22428414 22428431
    0x11010608030a110d080106080c041a072d11040f02070f060513030804060b27010e01120503070b09031b030301050406060e0303030a0507020309210c01020d0c06090f0b07020a0501 78
    0x11502c0716040700750742d400240a0300041101234421500250030651213000503142c075a89080034010520940d150004c910340200c1c15070280403400c0b03400308003508000b01d111382c0900502d0b5280c00c82c0c0185900108015044c45407202c0e50b071207681c456040e002e10702c10b04547c1d91460382000d00686410f0b40c0100c1d022810b160018940c207100e0742c04164020382c0f5803140b09060301c480e0781d0f26010301005030442d600a03516400c1101901d108101039466088000d00c070085a5041c100c4a07102c4e042d050b00403142c180034480d40d400c009180003049840494001601e40e50a1b200d18480340d040d40304401c00c019000e81c02c0b881c045000b40c00131004504840003220200721650395072405031462480c0b0300240d9850b420900000d03142c001076802030741e403080e1070340305686c5400714100c0001c168501000c4e0000942413406140c10041604012400c0c5c80c0700240001d0401070000301e4010090308541c0f80080107030b5101d884041c2041001c184000d055907012491602030301d001400299aa174a1000641d450340c2040d402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 22430914 1250 22429664 22429697
    0x100c0201060807050402030a15170c040c080403030e1218010e03071a0706020d15080c0d02060a030209040209030106031a010f0e151903060b030d0203040e06040c11010608030a 77
    0x1c030800c48491101810a4524241c1048002d40000300008601515140d080b010013441d1003942d0083c00d06000e040e110941c040120f40d00c0c3c94156045140030700e10b0310280c090103640003810a40e01a52518001c1061202403071824105104000c3c1d485000c0c1c40426610405001d07420f0000c44e070f850a83e100b041d044004010541d1f100c11500c584540d0517081d02103400c2c10b0441c1c40040c651140030f80d002618108030b0004842c100c0c0c1c070900e91100c4000401c101400446001e0001610200040725500910720321500021003510401e035224040c50f40c00200c01942d51196019200e041c50300a00810a4682d80d0a054010343d002540b40c0e0304010306100082a00403030284034400b56100c1000d480350a84d030b21003001c40c0b00810024907a034080074950b8550354400507080100c0c050b520803400421055060000e0524080c04030480006540081c4414403050307030215091640b2a80441c1c0215a083c414801602c0e08071310150b65039265401c200d404900d110b0300100402c02e00840d640c3c2d4100703d9004858 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 22432164 1250 22430914 22430921
    0x509030601060e1008010b07080c030705030a080a0e030a02060601050904060e0406060e0c030907050d020103111303112b110303120601090f03020105090405041b080c030f03070309030f031e02100c0201 88
    0x20b01f900b015060050b00d000c2500e200140a0405141080b01e2034020316860310b40c6103400c011785100004101c603007000701320342a500881c258007d03000700035801c0c29010301000c0e40341d07040103101c141002404100880c5075a01c9800050080c0561021140603007024281000900850301402480850b4400410500d443d40403c6074421510100079022903030508007000310480d00c80100360f04050b12515528220790020300144108915513500140c40c600e0751906020307614080d1095880307001100c070040c0d580300385c071141c106180d03d5080420100303516518000240b940001030840e0075110110b40f032403204c0c3d4180302a03030041c0c200762140c80d94a9a950000c480303025140c04000d0001c1c2d01403104101d1401d00c0c3e000150403602c03440c0c00000020110910021145c1d203548400d00592040c01305a00900b420b01c0311401522a103405107140c80407940740a0f02d176800c1403000400400c4005440c1c1c0500d0301c11100c02d0154117002e00b52600c1c600260780000d40c0c83d1800c4200c01642450b00e000c040c0c03228014070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 22433414 1250 22432164 22432169
    0xb0423060d0201230f031801060501080106050409051312170f0601050a05030a091b050a0e060607030c0f060f050106020d030501060f0c02060d020f04030b09030c06010509070509030601060e100801 86
    0xc2d140000c00220303041c50210032942c0b5443c1c4e80a2581886151020b0b403405024521030740c0d4003402c18035100040c1030340d2401d6a6503540032506019640005221342907000302202c0c03d64504440100c0c540e01d5a5110040d052040c44020340041001c880d003010380f075401902c02508070842d0000181e2a281c00c0c44c1415080c400b82c407040c1c08900308100c0b103049940904055079002007800400030300c400031b41d12880483c07610806130b00e15401e0500000d00244c9408801407000e8050340c9204440303464403c0c0403595900c1429809001d01004140c4041001203504844080c581d1000050004800c81000b80003d40000e009810260251080c9400d60a101e445813030304880075603032081009c4410b050151580340510f40c003642c100c035040000c607030040a240001c2c1740002d4009662540e90b80f943c2440c5410282c0542120ba40390002c0109007141da10008a090544008a0341da1a158a81c1b5606545510564500135094021a8000501c203600f140e074000d1002000d5441414030040400c04446180090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 22434664 1250 22433414 22433417
    0x80708030405100e1b180103060204090f060308090103090203190c030606080307050601060e1801080c0108070f0f0503060604050d050a1707020307140604170d090e01031112010b0423060d0201 84
    0x1884010300e445000700c005e0580700d50241c400c5c04210216003002c11050000d804c10340e02181c0003c0c0030414446184500c58182242c2c8400b00401411682c1c0e0300c4a622480c2003003070400d600d03003d0a90656805010084003d00b0400c1041c0c0c10490b1071070b2028121005210540b201840c0c00400201c00c030001c411105041d6201003c0c00e1160300308842a900020781b2080c96410403090300d10041e2140f400c80f03009000c1d058030002400040c00e90000186000d500900b090704020380340300344282050300001403624151b580d0030103135182d59943d8082070050107254400d0390710a030302404200c18450f010546081d114003500c203c0070b94428841036585140b0a03800d0080d0107902c000000c0018001030282e4250130340740100041d1a0540c0c507044205c1c1daa0082e51a001030b60401038603410490303046006c040080c1040c0c10480b01c1589141c80e0710003688160810380e4002c03c0408180c02d1501e500b07501c800c4401200400401035003036a903000b0340c801035910403c1481d00c80000042041482c295800800540c0d05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 22435914 1250 22434664 22434673
    0x40504080706050727081b090103060c0507020604060c061d070b030414030a080907050406060509061b01060b12010806090606100c0507062c0f010c050a080708030405100e 75
    0x42d598840141001484442041041d6402c0070038500e4100c488800c540d25080c0002d6035505100301d031070a051034243e0b604d11800c1e034903002100544030862007604482d003042000401c0c101d40c2d0800d88662081020081d44001e0004010900030b8118a15903031150003402c042045c0580c0c0c1d00e551405002c0300020b14a10f078442ca204100304029500110383c081d210b01a50f820220804030040c3c51900704486000124603000200648010100f003020000d1100b100d00340a00e5180403406405c0c3e05c03500300103d000d900005841032482620044688840415800811043e80c1e1100b44c504c00343c03c011124829070480d800002807038200080c034580a5034081e03001c0d040d02c1c0c54110800c00441d501c04408010300044c07510200c003050040c0400b8000707180300d88549806158103000e5103503103109449000341c0c1c000440384404058652aa0f00c012024080c03d21032100f4040f07040c19072601c03a20040042c0b02c0d000002d81f05080081c1071001e0350149100b101140c010341c03d034441034000d80301040c1c070640f9558003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 22437164 1250 22435914 22435927
    0x1202100b01022e050406020a0f0f05031b090a031401060902041505031306050f0609060108040b060907270512070e0402060f07080d0e070f05180702030405090709090b04050408 77
    0xc01c41503d144501001c0140d5801c940090308242c00e403441210141c80d421360214803c464250440b140c1c000d0741d1103071701c0c01c0707020180b115201a1990101400c150013008441c1070712281c01c0860790489101f900b004100180c0c01c1d6072841c1c202c2c456409200320306140e5003800710016080c2c101d030003650f040e120101260f2480c0c0511400444484c4c00c0108640640304400d6607040101b540c6e80b04050151060320350401b024601901481061140904200d0402c12140f08102c040b1350100c07586500040c0880340d504564940c10b0040384c0714645202d196254000344401c0403070583c601b15a90048075400e40f1865005805017400c40c1e101e000c5c1d4814000c5d01a41c08000400610b41507006045101003120030500b041442c1c2c55051664022035003e03003026684080c05507141500b0042d100041014140e0076140b20b05103004a4080c00503610342103810794404000c203107600d000b4000d8070060403019140c030754240380134000145451325074491030440781e02d002d5403212242410b004561240f50090449880c008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 22438414 1250 22437164 22437193
    0x151a010804060b0a15020703030905010518150c0106060201060806070206010807090504051504060b01031506090e090a0609050a0b10060903030f02070308030c0405090a0203010302030a022b1202100b0102 89
    0x3030146805074046130075003000c10040310101c20094401c0c00c640c010180d2a0440c50080c01c040e00c250049418007200384101e130425040794103506e81c40541990341e00b481d01100195451180582c44d02200b05500f0702e0302c0840e003140d0562000b001c4415103000c49034161034600040c0e031102020702410f20142c004180c103001c28803550308030541187c8600c1c1210368080c80002c0906001c0c1c002e0310200d4070641c451074044d509680c035026030207001107044860f5500780e14000010b00420407520988002c0c0074101c00040c205001400600c1d01c640d00441c003030240015038030303026031103500402003104c240e1035900120740c0c28007070444260280d031100d481e4003101c141562803d98095842d9100402140300c0c1440210000da1a007002c1c42c000d40c0070b4100251503909020401503914401451440d01d03910500040026a03400038003481c0003078050340c03030240303200d551462000c2c4d030125084100a16822407841c070042040109280b880b0a41650a550701401e114080710140c3d803030f500f101c1d401607102021aa1501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 22439664 1250 22438414 22438421
    0x1050c0a0801030308041a0403090504150506041e0506030c07030f03060e19021323010305090c040209060708040b030f0106030c020a12110115050109060804200d05010207151a01080406 81
    0xf0740070f9141e20028280c2000607140f5011f0440c0c0071030004a801c881040a81481d01031400030148015842010b00c0c10500815190300442c41010342090200000c88848001c5002060240001402031a40c17454190900b141175844214110005480400440305881c80782c49030900b51004902410361986480340240c0759403452600e41c4039015801c101149481d40c1c4204000018540d071480c0201302d92540b40001e200c46a0103036064141810300007003002000c40440c0e0755010700c2c422100162144a00c2c000b0800d40d00442000500321100003034041072108950000c1c500ca04a5110004401e0303884402c02c400ba140c50603c4140540d002c2141d640010301c00c0817640102d14032900c0e001540300000d0840c103003502d8070442555141030b104041405031b035031710442c600090030480c1000c04140c1000d070788440c0c10007000c842c6483c1c00c55515580030718036a240200035080541100096440d100c45080101813203841000f0300300780e985040002042d040800503004050007058440d40c040fa0746544034540076 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 22440914 1250 22439664 22439671
    0x3040308210c3f271e010b1201090c090e030304060b04021306080a1b14070804050402041e08070602250503030310030308090303060d03030e0a060e01090501050c0a0801030308 77
    0x24400d40020f04001d54060110440320303401e05414039403d5003012821821020303441c581d44104070300c03260810b19000380c00103104005450340d611040e0940c2d1400c82002d004060202c07500354410b00300c00a1307568518054101544c01d034003600ca860389245c4c4d2102c02504403504100881c6068205000003408140142d1040003030316000b41c8054030f000310800c1d0540d0840300640201000c2020402270200c1107049125030350035106031300d401248580000c540508400500c0c0340e00c1081180c009000c00c1040444829500203003c0540b041d501d42e5100d1807071102c1e0380741056161002841d02000001d90303041c00101d1034121550ba4003d442e910710b10b100740d02403901a000e46003003c2c5102c080000380342e0700d0400056100d01842280542e910382140b800800c010740142070341d2789945c414800d000fa02c1d038886006082550b0306044c00103100030481c0065051461140000d00850301d0000342489501040d0005078841e44603000070042603554400301c41140c05511000b0740041d900e04c005000081c0680ca11580 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 22442164 1250 22440914 22440967
    0x5060a0905010e0d0210020109061a0f0909101b030b100518030c03060403020105040302160f05060c010b090702010209280302060903120d020403021c0201120f090503040308210c 78
    0x104d001264012501304c41e101c404034030040c1c1d5900000c0042c46104d200d039610410211120740410011a40010148600340b41c085115023020008254403020400c203907000c42400c00c80600c0081c0082015841d01c0700013190301c2d400329041040e05c007228a019a401c5503465041d0322202d00703001d44405441544100c10344001d4052042c814416041d58081000a100b01e04c26400800c1c24942441c00900f0001002c21462404200352401d0240922540440c4140c440580b211501c480301c0e1a00140580460303201d46401012410038080d0869043d00101401c2d0300640301d03290f103511075a9400320040c1e081c00d480b031844003100304180700518000c0b0041103002c0004003120500214081181d905c0d0f405403022000d804c0e4005410821030030301c6011035803822030b040d0007a544810b0680001c0c0003014102c90f48200184da80d08902500d09480d4480c61480e034010003100c0d10750381c491401c0740b010350101042034002d40303540000d40e90040b5032214844c4942c004030704190030800a0710714140c400c203086205d0710 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 22443414 1250 22442164 22442179
    0x305090718090203010e03070606050916030504022d0301050717060d0602131d010e0f04032a0308090105011401020304031e06181403160f0203070b030f0f0105060a0905010e 76
    0x202513542406044c01200280e40a1a5500b0781458810201c9805034005070040400d40101f201c40c04820200040c0d2090608000c503455980c0d2002400038404801c03507000361010f110a805030304500c01317942d014150b0150002c211a4880c0881581c90141c0b004500c2c82c1c4442c0301c00017400750b0500406242c40c0510640000d400c152658540d41c03210f125542044030455000410345030707540c0c410601c5500400d90300120001c24141101d510002c0e0304000c5c006401e102c0103107031300000c80e20303000541d841121035401130340071445052a00030f104200503604211f40f036007408008508100041c480c4011908144c0086141c1459940c0312802d841c50420044025500c5840301008541d0700d000780d0b00805410087d0707a005509a10300303d100280c82a594100e00ea0061180a9802c500e8580040740250080e907405a40d0741c281c40007920b45042d0342c1080380c8400000c4103001e0039440c1c150708940034940d1000800312981c2c90710184100ca010307095107040002c01040e4100104e50207101c030640103040181414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 22444664 1250 22443414 22443431
    0x904020705012a0807201501080f0105010e010b040510030608010603060209120d121503080a02070303110c0901061103070215040f120b0406050601050d06140f010305090718 76
    0x1800c4032003080000000522a0740100c0120000058000680f046800c050030182440c980050141448000c0c001c210000d00540012401c1c0030001146c004120048400741583c44696803511910000c8a2400d40e6013040c00104240c080001d110303040e42c000d18400742c209440c00c004c1000300e00e8111f0050341859a00c1d0340103d4894402c0c0214400345000710800341c1d81c0c5419178244600c402052082d03002c617410801450003619030214010454206128010590111060b0100d00d06107003907100400c0d62800048441202d40c001c9811021240240c45101c190b01c04e10300001e44078100701c44402e6011450344014413103107003c3c220140e10403843c0e408036810003c00c1d60100d044800345600d911002c8201003010801c2e200380601c0c08014058241d51100903814541d105404100c026100a2010b5182c00004445900c80e400303441d001c508425060000a1352095690a0313500c4c0c0380045406070800e2005282c0c5940240102d078082c604600003050110728110051750138032a01c0e003009001c42d1300c44003032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 22445914 1250 22444664 22444673
    0x70f080d0603080307090b09130b040e0a0f0506010b030712020307030e0a05070e0603030a0c02040e03090901090204050301050c0f0304060e0c0d03050d0e0f060a050a090803010305010506010e010201150b09040207 93
    0x10302010b075105104481ea41d08108001511005196104002c0d4400c100440c0f542903c44c054102040a00d03a10082603036485400054080c009c42d080c0312103188a0f44603480c0031701c2280b02070214481e0140d000d44000d45d80303561100e0428441102d07114080384101c0492030003040c080e070055a00c140940b40015821407280c1d03030b2505000100800703840d141d0000009100282c0003540f50750b04000201e00461030700b04109030281c100851260044d108565036132010400007070501c00c4500700000107259186a68496480d14004d40250141500a6107040002103075184c80004403045132103805406800e40e5100da4409010b400c086015070b500d40220100910b140e1101703da00c3c000385201e5260580c68039926000e10f400c440449007811840e0b446000d2191200c80c010500942040030504041a66a540c0d203101014000080008105003000000002804810f50020b40501d00990340c6174007131a8080c004900f61001542d403030805241151040020300a180001c07c45480e01610142c20150f007a00e6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 22447164 1250 22445914 22445921
    0x20312031e01140103060602071a0708090a0b04080c010302090a0e0603010e03031501080f04020a0323030403030c0317061e1203130503070909030207060804080706050a020904060b030408070f080d 86
    0x40340c80e0003e180c0c0c0d08643c1c3c541e0580254801b46c0002d00c001e14010385017000c0c0c0702903882614120a00c0c12800134840040c03180400442e07462440107000403098170364070702008206034420300c41d00b0700d6401540d00e02c10040d80b09000b11225a4401810511107504000c003850500002030109a411340d40d83d04075078031a04081c8040c501c2541c14030305001d9200441070001d040c44000628601c0c051040600300b000507a1010b0082003581e402c00700d031007100c0c01c0c0c20300a00070b0840c140c03850290501c40820000101a800510030110f80e21035501c0e082c0d440e0200c2185e0a02e40c50540c0c3e0076070701106100c011783ea05000030082c8011000d004200303071400f001921000f4115440f006000c0101c040c2c03403006103c0d0717041c01c1013030703100030481c041e010440f0f0300654400945841890040c102002280d038041814130040303001351001590800010052814544075141c0250311a44d06140500d09003900000c00d4818601620310a903041a0f03081c0c0b402c0c50030313a46e4003a520200301d002c440b40241401a05603901c80c030710 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 22448414 1250 22447164 22447169
    0x20a0b040606050a0503010501081207020109030c0306061d10090203070201150305060106110303040804031b0302060c1501060e03030301090518070e07020c09090d20010c0e0a060c020312031e01 85
    0x1d8001001c5041400348241490260001400381e81010010442d0740c07030000ba0130f074442c5801411161107030118030040300c02c500b4079840501002108440070091000d00c0d4481011944014503052003161081c4c070980305010202c903032404030710084c9010080c4080d141c0083d1b52081c0710b03100018980312a6031032950800581d40090f03030140d100d0401405800e8028903440028a481d0000b5815850035644081d041d21550000420658944180d4400000ca4000006c05107a0003410300d9164051072504036521200c507555500d848210200002d8603c0c06543c3c100703240800607029510390307805c1490110103400007925294603094407040380f0422060a020700c40107040103070442526420039184c020300d410254103001e031059030a1400d00c5008440000d25003042ca0701c42c10020310304920410103102c0c0009886403010f5175402c0003524003a8552015801090410860740145c01070b440e407000700c17002240f101d4000c0d01356000105146452006030081d5502c8120310740700290b03004481e00a00020082a03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 22449664 1250 22448414 22448423
    0x90406090f050c0403080f0705010209100201020702091501120b120d05070c0915060309060b03010f1e020f16050705030a1a090c091f03170306010917030a0e01020a0b04 74
    0x40045003111281c81c01103e03001440805400d09190030354031500710034030030181c00081b501800034130310080250070b4040d02d00c0c01200400c1361441c81842d0700c1c068083e500001d400c9200d810038800140341c240800840702c82c11101a512400014013494a80e4003e0401c3c83d9050340c0301d207611001c094002c0d804c0101c0b00324070219599003601c40100780b91400703180d21140c020324401410070b00329485911403042140c045410620780440c0c0e00609090004c010004407003055015400c20305401c070021a25002840c81402c403540700f80d1218400355103a022805502d98a240c0707641e00f00100c0070904803203c000e06a0038000c0c1e0130307a03001da0740e2080024a4120451411620f0314440620342c002803010300c0440303900c101070f03102030039000080c0000100044401001d81c4104c220004580c0d1400610070b00781e07805103512072803080c180e0b000c0100c41c11640e0412500c80d0300103501100c0c0841ca41071400349800d103104080303004600300b00c8241020340b581e0f0102e216403411445502d0f1002c002c101d0450a03980a03500a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 22450914 1250 22449664 22449671
    0x3020c0604150909050610120209090406061701090804031106221809050d030c030e10020301030203250b070609060c120e030c151b0c06090105060d0b0a0c020309040609 74
    0xd048000c0c10043c20356011301401c0c0d14090800200d901d81d800a40703034a45076450407540c1780103282a28030080c01110841034100120408210403c51380e58069400d03510044940c03003030803040180c921b090b542154401400e80c10140800c20000e440f800391541c055034000d107654201f8134030700421100d104d541c0300c0000c0e061740592010008110b04000d05070380c5c0e0505d102c01303211682040d2101595421400007034400c259590060002d82403280d8441590a404041501e404004210807900a03400a00042c0c0c440d0003045965001e448032402001544012030011502c0300d80383c40c0399400175030000901503231402d0703c2e080e4200c00600309114244120342642c0740c109030380280001060031a00700f80100e200c0341d030040006001c1c0e20000078031803101d414011785000070343c0c0c5d4010019001003683e407000c190003903010800006081c03000c40c0c0380d132140702e0600007001259500701c02c00001c401c2000c80500103028040c04030748012815004100300076110b004507403078207801c070011908a540c00d50208490310364 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 22452164 1250 22450914 22450949
    0x306030b07050a020318130c020a12031e0506060f04080f071505041a040f0620060c0405060c01090b090d03050109020405061603140a091503050103050303060d03020c0604 75
    0x20002003440c0c00c00340901e01581030540c03c1801a5a034859403099000c400d502c4042c1d01d10965400d1405560307060071550a00034085a4180a5a038080000040300c10540112999603100d00c0303403140941980728a00c0070112002076902040040c00090310841d0402c104100b15605219060000e10050174080000c1004d2803106160307a01340700c0c0f035400a003903500b003000040c508198050191401d907000b001c10a40c0002e100c80412040f889103038068020a0803002001336827a030001c00e60340151070b50941e01100f401ca00c1c5c0046481e00c20454042403410400d000c1403100c1d04014024101c040c1c1da0500000e02009903807103410360031100300c410316425405066014509503050142a0040070394000560501d42060b000490354000e8030b82c100c4440884071030110601d4403441456208400e55002503507551400c0b40d006003042e21078007449280c44a054101c0704400e1103441401e049039003240240d42162100c004020036041603003800d0f01148039601c0c0c040c0c001c0c0c0d14071004000910302403c00044080c4d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 22453414 1250 22452164 22452173
    0xc0f0803180c0405070801170304030b010f1703090102030403030c11040e011a0105030603070506030c0f180406140a03060b0a0b040801020702040e070303050703030203040c090509070305062413060312030603 91
    0x1610b031401c860245090500380180760382c202080606460280b0411002002548810342c40c5002d0340d4000b0b420a01c0c01c000028801e01a4100c0340152494003000e111114042c84901e552842190080e0307005034410041040440d110306007490341684103090b500c081d03140442c00038081d207411107209c682c582d65a4400c0e800751218002e0800818000b820018150326042c0c000030b44070b48452013540c0c041c0300000002160074000a00f1241d1400d1051121503d500d05401d40781c210502c001c0315540104c0c0741082c08100b00010200c0c3e500c4114004003000e000c2402c60f41c41030068891140d00c640c1120041602242043c0b240c805800a401c01c031000607124029401000246c90800d03030101130a81001c0300c14004254004100e40c255038150601690f42e031210f1070500408106a03214811141c81c1c40c00740b091005010a91004803030048040700c4460b142d03112201d030b0442e164036104880d00001206000b980c2025010030300c44003440d800024181d5620380325003500128280c5e0080019030303100010300411 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 22454664 1250 22453414 22453423
    0x2041406010e0a0b0409020a18030302060906010e160e01090512060402090f0c0d0c0c020a06080405010f050105030c19030501090b0a0c09050f0103020c0f0d021005010801020f0a0c0f080318 83
    0x1210440301440d20704e142c6405940b03103124a005442d0081d030005146240e4038000c5880303600b0b0701005882d1400307059484c14001e403211010346000b2150b0094030000070709105d0164049004040241c245000c4c550902401e4a0b082d4401c14500d05100280b4030024040d40c2d6950050001d2a021000d002641707032030700c108010920000c21144100700081e00b40010b440c07008043e200b0708960400c0c00122038106080c142c0e001212158000c1d07001c0043e4034041000c1e44d010752114000da00ca90002e01292014509a07410380e4801d0048030340641c440c810708a07131450031074500d4004a003030140c42a41e4030303260386a11b030a59214032025940300e002001403141c259907510902c0944040d03890200d40040c2000001800d41219042c0703a810560040381b841c11410007840402485800d90040300c900740d8148030b001c0e45035000000013030406841d0100003d48000103000b15a103154054000c0740c500a01018203444c1e15000c22000d0f06d04010f907850b500001030850340194090005d554030054840888003110385030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 22455914 1250 22454664 22454687
    0xf040e07170a03020604150b1f0305160e01050d020705010c030209010207060201050f01030308060f031b0a090618021c020301180f0c08010e060d0512090a080a0f060506010c0204140601 81
    0x503400450458003183e40031031a1500580c2c080401c03001e49407c00d00540292840c11440ca07440540304a0204251142258401c2c484255031024002d41e03403030003d00c041c0306060780801004240000700904040d0b221310020108079120f400b0050a003282c9444150848102c030401d400400d17800100542e040d038041100e10020b20845c4000c2c4128548074400840300c05040c44000d0034040c80c2400300e2005c2d030340c540e84403041550180441c2c800c0c13894001545c220f1780b04141009d020304030719200418029110b000d003005a4400c400804003200c05d181c2050025400121803c55144030001005140319131800154000c0c0601041002c0341c4030f941000c1b0302140c4034509051623a51a04000b0301d01c580d001102d403411245a030584a01c0f030340d42d030408110001c0c45104020040d00501700e03040d11340708118018003a40e210980300d181d030f910b0300d81e600142d482c0307205030000d8515444015400001078003034020581c030240600d84051031135141e60104d011740705d1007840d0b180c00c14820410800c0559210303116a18 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 22457164 1250 22455914 22455959
    0xf0901091b0f0b0a0918020909040303050103030e04150302060a020c030616121b031508030a0903050705010906080a090f082106040203010b070209040203010603020604030b011a03040c060e0f040e07 87
    0x3600030118406840b07180075104032046000c0c41c3c103203010180c1b00e503410359001e010090300130000351a040c50014002c1009010440101c0c0d0929403660081c201489250b40a0000d0031f01f042c4524111340801c210381c9c00028284045114030440b40400341c03001c4c00312602904400c02a21100b6a52140141c410804030085030300c185d1811003805400c14001c0400c0b40c181032542400a840114040c00c0c924003c080c0c2c108022601c800035200d2102c6522219410459014500f43d680c0541c0718001140c951078140710f0040042d80340800308403100d565034890403c86104a01c4103002c425030355101e8031250080b80440d82c0035010340e920008074602c910030315640060200c40440c915818001042401d0051000190103003000f030001070b00310340703007503200708040c40d0020010b039103c2d80e89140c04002d580090161038110f00c8843e1075200070090f00c1c0242c0303000d00d510110b400b45883c24442c1c1260803090100c10303542e200c85103c49900140c1c4651080101098852002d841c100e0f041840605521008100584 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 22458414 1250 22457164 22457167
    0x7080c0616080c0a12050705070302100207052109030106060c0212010b01121109060301080a02101701050f01020109021008090f060103020901030b06060408030a020c0f0105120f0901091b0f0b 84
    0x284582c060102544203041940c120b0b111300a0359000c90300301c42100c07400070515191005100701c4c1c6800002400b48144a60300b1260320800b1601d50070141c0c025510002c00c240d01c8a00901400c23014182421188812850380c40d05241c08080081d00351201d591025010074500420b241c01d41c00e00c90341044028011000910009044800007003a01d0140003014010940d90009c4802c0890040c0455140c03950040000d600c80d40c40308909501d400980d0801c903c666014121554024055001081c22401d0358800c02013a03880d080c1400003180c24160f42c2da0440d581c840c01040140d40d07070505030407c00c1c204da4550300c0b01e14141c00464a170601c42100f8190580c4074034010001a551385622a0540394014101c000307a48800f408a4214080e40e048a10f85000104018861942c00201608120011581000032303070540030054407140b2602c81c0c50b5848900c0e100c001080320180c8007046802010500000071000311580720085a0400303146079440c0400494801c121400070041071a02900302901306d81e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 22459664 1250 22458414 22458451
    0xa0501051906050f070204111b0d050d0f0f020a0c0506011403030316031401062a02060702090408160503030114040b090f040305040f03030e01030e010c140702130207080c06 76
    0x890360701c0203502c00c07501000380026561a40121003400c0d076040c00c4c0d01038010701040c2081400b841d92900320203803040c0d10812102c0d0300c2ca40b483c40064030b00c0b4140c056440700d41c9003001403158003025003441c0c04940c1e0500e45503210406c9941c0c1c7e80c4010169040c5c241c0d11a050302000707281c8203041020680c480d040b80d0b85c007821201440c1d0350200460350003081d45681907007090910352068014004a40c078441a003c05100001003a5800c400d404034500c0d29040034030405180d0342c0170800040e074240400f94100d8010320010b4010b050956856070814018401d0034103010000d014a51015050f14003100c040e08040010850158205070f2a18402001c450a0000620050125040c0300d40140040304110381080400c5c14540544101d801601100d0b208004040d100d040103021040750120f21800a407602c0f44204200c503043c80754071200741a90792240711000f00d10b210410650494402664031410a040580500305184000c7c01d1140c4100cd0084d181c58404035841d09009008003005025403200920 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 22460914 1250 22459664 22459699
    0x1805060405120a21020d17070f020c03030a17060405150607080717030402010806030604051c03020c030406030501030b0c03010810020c01090b0702010b0f06120105011b0501060306050a050105 84
    0x95509480042c2c550501c0d920040e400a440c002e20890003900000743d103c981c2440103044221550f901010b9000c0301d0a0010409003103580c0044c00f4010760311103200402050a1603ca0030302500e1800162044602c4084c0810000e42503600c0b5000391408542088540040b007015006100d901c60f600300d40410107440c00c031400f402141c81100c541449408001070100c1009010001e443e406600040991780061003124031021729413081c3c50503070201d402000000c1040c500000c001c1c5c41250b100b009880d8203008201451042c20010420001703254080c1701c540c40300b503820405080200f82c00e41d4042100e52440c200000004000b81420140c41010001405055000291002e46050075400140e031a032405199074014100010002e0000d00300600380300c0040d905411003410030500700d50200c1040c2c40c400c202b0082d80700d8466100404006000104455070140315800d00d02c0040030903500c02400150346031421030b825170704106c1e001980c58084c0b141a41c032034030503103000d0501920f4028040540c000c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 22462164 1250 22460914 22460917
    0x216060813030c030c0b0f040606080d120c110f06011403030f04061409120a020a06031406090402010c0203100501060909110d1505060406030603060b0303090117040201020319030507180506 83
    0x1c000d000c0c880100800002c040c0b1078000203031180e404c8072aa059070705040c500001910b2040c0c400351285c5d400e009000c51104008030340c2d20180803441d16004124004a4404000382491408440500c03000b807842d076031099014030175200d80000c2d0700d02800880d03040604413210850b0805119000c1d81c400e00c0307071501c402607000464041d91424101544020038683c030540e198400c0326512504801021009944810000f444c100510701c02c458911072586c03254401c038204d030baa4440c0745496000c88008980c0908010007595007060040c9801e80031485150082031511640c1407034600902e5403580100800c0380d1001d40b0704081d241d0700800b441194120090142207000b84000d1200c0c81c0d95a280000342c1c0060701c0728580062402810b0b0a8a0b581e91341c86c05001001c0314801641c14070b0402c02048014078001c0201c5d120100141c480b4011340350f0720b02c01050341410080080f810b5100810060307403000720107241a002c1d0b078090b80d408606403500a2000b0803d041c20305d0251049007221005001c141c0d10b890 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 22463414 1250 22462164 22462201
    0x3040c150c0303051504020a0509090106050a0e0d050f010504050d022e02031003150c021209090708090f030412031b050607140405040609020702180114040209030c0a0602160608 78
    0x15000c1031503240c170104845060554a00554014800201c14103269005000b900c2098402c5496400581e83c402c3d09845a1050030000c1001a650300c0040e0b8176440d00c00d13101c494060180c011181550031000e0b0107400c40740d05680c103a4840d0720050f0601841ca50400994254011419040d040713841c0e140e503a000920321150b03603172183d0307500480040e074095200da40f420b0086402c1348441900790380d0540c122006090201250006002d40c140300300d400f0b42104202c4008041c0a0803440e49503a0b98141111900310280c5908281d000d0300c1189150407400704041d0020700001010300e483d043d1640b5010300200214003180c142c1540c0300c061900400c2c00072a506078005081d0420f0705050b40c01c01c001125500c9250801c1c1d074003514000c004680304c2040e5003d41401d52098804c3c5006c41c80b10300c000f1071100404d211351a01003500c02c1e2152264245500a0081d002003c0c003100d0841c600200040c0302209980c02c04001030380710a10a0100d00e20032940303c0010121428040f0a50070001e5006590281c0344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 22464664 1250 22463414 22463417
    0x70302030a1401091a070e09041104090f0803010305010c080717161107031a0c1602040b0a03060516020d110a020904030203041a07210f030509010b03030403050303040c150c03 77
    0x10902000441029000505030f40c3d803004c00300920703144a1741c4030070060109865600008140145100c1d60303040c5900700f02e004580125400d0b80c07820b000b100b0000541500442180d8166207007801d000000e68000143d4080c1d0321840c0085400d9807184ad0080c0310380710081c040307010085410b8481038002000540d15800580000741010001c11032481511100030102c0400d100d407240300800804e100c0b01c80c420071a580c40703500700042c0544640040c00c0d00d40c0604a20080e200044002c03140c014a8203501c8900c143c0405041d01c807401e6641c1d00d0701d104444040340c00d040340c08600d845a440c0c8943c1440b602c441c02c1c0d5141090b84010450400e0350f0341d02d01c000d8000030f005604038408a0103040c001c0003910000d03c01001190140d4051020202d00c64005220464000e00e400d410100014200010b0801303400c07050340e4002007801c01c00c6088000c1c2002070001c032500d56949400302c0041d10144001c0c0045c600800085560341080d00e004110104982e106044041c10245a082c52070780c04a6a0ba0307000350117 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 22465914 1250 22464664 22464683
    0x50f03040b0c0f0706050105040c0905010504060810030606060806030601090203010b0405090c0d02030907030c080304270605060a0507140a0809090727030b0901050106020309010f03140c071202070302030a 90
    0x4031122600300d485415070036465a00b000c14280d0400c0401d801c047c0c16180103840c1488507004000094546102e1401403a011610620080c40200d01c00c40e41140d2042208000c001c6455036900c4000440e4003c2d00001c0004208804022081c21300f0886140103003140b00b0114959898104805400e000f81d0188030310402c120030205031050800e10994442c154198001c55490410720111039032100a4401160310b4040008001001031011080e901102d9040c0b0000c11481c58108228180d6044110040101c65485c1408203054403004040e240d02d10700d644503269900d04e00d040c0042142028a901c2140d540724002c16000140140c0c00c0d2950f000090340c1400b115102c4502c03d64011040000807545c4030950310284084031141c0303040e0750440b0701810380c040c11500d0740c203030030760a07224240110005603104000f440825485a01e00410001483c90b00060b16011040810303504c05040d1008516214049078038010310440e07600200d2009642e000078070354180745501207500c905140802805120703c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 22467164 1250 22465914 22465921
    0x3100f09060203010e09060f070804020f030a050111040501030b0406030f030f12050f04060b030102071709030703060203090d020106050d05061f080102070f1e02090f150a03050c040c050f03040b 85
    0x440d030000c122880e40044150340b20b6844540000c402c1000700c03400020b91003804003140540c4031000a140c0075401d95a03540440b070b40c5640074000000d5a18460a8040c820041904080740f42841450780240c0c0103c0700c240d41d01d250038001400d032040050107600c5a8548242000051183c0c207040301c80c81e5050900c42d00043c000d60b003d451460f610742003100d2039402c060410881d840845801351007a80310b43c400b0005903011900707144c00c070300410500515507800581d030000302010240180c20f56040041c01c0b0369105031642d41d010300b07070b82003900d091881d6480182040311107502070103082e003d0710b030941d1a0080d01c1e0b260b450b095620100680810321408201ea000800012440c0400001e400c1d202c0080d9170752226450b0040003080400000e071103025182c5950407203804c1411090948513001041810300352241c201016131480d01400c022861418040c0c11140740d00c4640000c00150b014101038210408a2003d110507a0720782e002440410504101080e041c0c507058058a030840d40004001155a4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 22468414 1250 22467164 22467191
    0x30f0307151506020d0201060b0304083f180111040b130302040e0a060b0405011d090102070c0f09061401050a05070f02090c0403110406050d0206070c0e0705071a060310 74
    0x91840d060a402c1d060780400800c085400260f07160008291741e008011081e0348080008040c003041d2030040c074028041003526201120035036400c80030a8034648640707901d200b0200080f12105100c041c06c0d200d608500c100000700150755810840c00c0241c2009000c9445035407120805482580507114204030b0204084010075001d00c00310b40a1940617004101c400100e1010315540c0e00000001c460030b40c10b09402d80e03101c4c1414001c141c12184880000280b00c021781605d80829a4020000b5410799424000388c0c020841943d0201f0044c401014500d14180c02c0c00c4102080d42e45030b0b08101000410740d11b1108203640d004088410b0b01c00c40381b400c9600d50460f8034100d81c200d520920065480703401901408030954400e0018030840780324800c0d003a03914610400b400250f4540b44a203c0d40304042d6242500076041150003801c5c003510800c0d00303800090300c1c0d0020b0407000405a1b505400100c1c0810503808010f0804680703024984203c44030a01c519200b000240d03640c0100c00d86500b001d403035042d01c01c90f00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 22469664 1250 22468414 22468421
    0x30c011d03060a050901050a06030201051602010c08040b030115081003150f0609020c15010f030b06060d0504060213060305040210030e030408070b090411030103110f0a03060e01090201030605030f030715 89
    0xa10300181540d08038100500e10304007400003643e180266518000203e4040b0290b03109407402c030f03503060315003a0500c5d4054000010444000c07500b60f050140e4041803070005100100203101400070414480c0d101d5061016041c8888408030540b8103121a00c0b05029680807450312403000c8a9005000c12070340221045a14050045403c81c4046242000d10201e007605658000d0018042010b00719120b040b072600d01907160503820701c5004a65aa4650300f81b01065400c1841540240c0140503149080130800702001220800c48040c4d40d02a400309010100c0101e010f0329500801891030140864101500024030a10300d1182c0f03802450342d146590140400d080c425240108440ca00751580341c1e03520b012511081c1d000300c000b1031055140800480001d10101c0c10f49045c4d03a00f00304901c0229488205000d09200307505141a44400c440e400000082e19a000f9013208081c03440c008140340403140b0024058a010307403c20340c42500001d802c028020030002c00e0b40c190b1900301108103031940307030811081d009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 22470914 1250 22469664 22469717
    0x40207060e0a050606012c040902030109081305010e0f0108070e12070311040509010509030304030f021603080c010b03031e03060f06070c0e0106031505040c09090609060e011202030c01 81
    0x1a0b005180e44682840004100309110300801c3e02d640603c04502c1e8003002000945134032404a0307042180c9205100e06184d88010300b1a84054000110b404080e2102c01c142d4100070744228000200080a2115580c082840310b104202591056607466581c800a00002c0006020100304070401c4d011308115511608001c410202d45c006461081e5281e0a000c2c21011440300f26501642c03c1802064090f81305108140c81481c494010318116103c1d607604031810440000c0020440c4103509c0c03080d041c0404074411070001e5101e88180b03036951400010303150a4600d0010302d03038403030340081c0000201e01004680c65512241e1094080b40e8903603440f00040c12011a0b079030344580180340400e8400410060606070703810341e01c0da9415a11036a0740e410003181581c1080301c01d030284240407001042030f030416800c00782d52001907003000c1848680b50060b9000b1a06aa8003403407074151104002c000040352041442c0c0036001c0c034410420145059004a41d0381c8240e102403504002c020b00c2d49050b441e0120300561503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 22472164 1250 22470914 22470941
    0xc0606030b190b030304060926010501060906030b030705010503070e03070305010c0f09120507090923011a010302032e080f060f0c03040f060b0a030c12060b0108040c0504020706 78
    0x14182858010351542c412104a5110741c581110301000c0d140010546040f80c00302c1d560307141500c0c208489144090300c5807089040b400c01005103100c0c880c00030300446010b40320300e90b01c030510380b45019001400e49410203520345c02504510703810310440c0d0740001226031040550401c02060190314002c60701c0c11203940c0c000f600d00d500e0000c00e41c80460b0f001c3e44001000c1c500760782c0e142c012740c0c603486110f0030301d010948010039550201d0700030445082c43d40c002080c054081c0c04d103403c1c400445004440c2825007114001600d0350745661140c807034042010344607003401003880c0c01c605520300305442c8007000b81d941d00c03080112000103d40da00d4a0b896600080080c1514030b0550f0310b00c126510039142e8404e029180720100c140d1410000c3e202001d414180d0b4800e80d00903a4000ca142601c3c1c0fa80c3d001031400982e081d40040040e400800801c0c0c0c52130401000300602c1002c60001c806904000c0200c92002c001281000020014040440d503803a10900c241c8008882c0142c0d6004c55150020003094440304161 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 22473414 1250 22472164 22472183
    0xf0d1a040b0c3c030903041d0c0d0b060405040903120609020a1b0206090d06050105040c08070503070f020c1c05010501060201050c1206040603060e03070c08010b2409060415090902040b07030c060603 87
    0x1011700380072014100700e5458120540401740e107500450144041203032010820081485030300500140381d0400241108060080b51030300d13840b400030406407001410305401150f03609001c01424007462040074020030079400e00310306181d03000303400130209c3e43e1645a205420150741a518195524001181c064000c000d064803d9540c441c5007101c083c080900c50144070341c2c40d100320140c81a00600d0030b02d1080407503a540700e28603500d099003507444400c00e1410600710310a2004440c5a40c94400c2e40c00003086000c0190442c1200074603003103003522016044202164100001d015404804c2c509442d00a600181030200c56507608004c203008040c0d9a00142203e0305000c001581c25030301000074070101c0d004001200701142c03191400c80c241d504090400383c1000100340c001168011001103440980031508840d4a03000c045000103071300d078001c5c1d04030241c05214a4030707100429401074660002000c80c0c1034158200b61030034011110f00e004915029040c4244034150b10304025031079000708003850b030118445 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 22474664 1250 22473414 22473421
    0x15150d0c09030507060e0a0902071a09030d0b0a080a1202030f070303020702120105190c030209040f0501050102191a150a0b04050f0103020c06060f0d1a040b0c3c03 72
    0x200703041c072640700c1a100c81c00fa0f0280402d281e8480d145041c0e03424400351990388607510b80a0002d0007980217920075640e0640441c1d8910051001c0b10381e40780a001418015602e44840307030b00c1074003210701801c0740c4e52141d18207070820001d011011440d0030b08070390409008025940c0b41c160590543c400c0b140841c0e05803c00288130000c01d905036000d02002402030b80e48000900025580f10700300c4070155550900041c4514120800340140d420001c60510589800760030000070f00013040032303101c0500c00500710948520050000d541c0c100401e80e4060038000030502d5042d13490b01d80c0e4284623120100c540d00d00d9206000034683d2203034181041d2003a58054104803515035200000a05030304140a10707442030710359082c005001d61090007a81c5c0c2030564540540080d4803184100507041c5444808550410700400200011405541c400510440301080e08a0280340500d002d100d000f8004100142c02407040c00319164114111001040035992521290111a0f107840d000c140d0f07080010800e424200c001040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 22475914 1250 22474664 22474667
    0x60b0301051005030c0408150406110915090406081002030109110412020d020103141006030b0301110d090f0209040602090a05011b020d020102030c030f0d060b0c0a0f0c0b0a0e0909030315150d0c 85
    0x800f07200d034ac00ac2030108100d0990340110030040c803034014501c0d07000300c01c07500440d0440e09070401085c2c0260001c200250311a59400d000e4144881c41820101503039000c0300400c030071090350003140004940350340a40d00d0076003003500c030300d02300c40c100305010b0b00684e140765418086900030784c042d410499400001c00820b140c0702d4003000300134440b4010240000e0404003802060b013014010b1a6a408400700c4550501e00080f070990014441c2010645041c6250000180542c41e00c080c82401035005100c09652804210244800d04103036512040c100014946000c0028403141130b41e0304030550496000444094500040345103001d101c0174855640030010342c20444d540300c00000e1107038200403030b0140103240c4d60341600042c0e070040981c1080540c0081440d14000740741500321132022440b802651403c280c0352110078085402c000782d00750105046644100d0f4914000c0401503214003d4401103141d4030f000c07000c81028082c0e038803c0d00d0003181d52185140c603080700f07002541c40001d841c4c8020007451442020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 22477164 1250 22475914 22475953
    0xc03050a0302010b010e060703080c0f0301032d030903150e03130509011703030c0a020703051209033703020c040e06060901060207030507180b100909060b0301051005030c0408 77
    0x811400b5600e800449003855014180d100d07909800149014107003500740d2800d4601b400c0042591030030b00e03006c00a0441020641f07004d1806140600152490300d0300308049499129030f25060580d21412816050b00006c3d0702489000690b9401411101c0740f104241003540039080c01d10412110740808520a1406120000700310102d46c002c840a16450340e071045100b0113107008555003ca40d030020400070750301030203420080440c08036500c111540c05039a522030302c0c1481100303881003a400c100000c00c0c100314030b0104080501114003a02841c901340c0000031040b1242c165104c1031810049542c1030710207043c02404920000c4202074401e00c00141081c08440e15a038084540301d10443c034600002c038100384000782100a41758450006c1c410b0505202442c0020705880384c0c5a400c0e10703159003a100003a00c449030145d19010460700e8481045050940c0741c0b0646216404c00c01030144103000400c0325580f03017828900f259041d401e10302d0362900e5070040c1d00114401d50f00301c00000d109000500b44441e00c14075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 22478414 1250 22477164 22477183
    0x5070506150a090203040506070c1a0103081806090d0215090604080a050d1107030611090612060102010501141503040204180b04020f0103051614040807060905030d0201060503030706020c07030c0305 87
    0x5920311903040d100d03507000b004c900064030050a01d9005100107600f440c003c0076940d40d094050354603501103070720800321444804000d0700100c900c030700c011031040f070501e00118140204003c04c9400c40d0038a14404080f4240c00410070340684034084000115400c500c000d000c5401100c80a0051a178564517071019943e100c04041007141c6038071642c0781e58660385200342c0d0300c1103401000d00c01803c04e0a00d16200c0c4005000300a81004010f07008100301c1100da901c4000911444411038000c131030a103014400a421a03070140e203c4000c1c852112008207a0340e58160002c40c0000c400c428442d103944890020070028240101c1078400001d4040303140051240d0140c801d803180703108540329a00c02d40c58034011402e6910598420b0348513403070503a0b442103850041c0041c010706141e80040c5810140c0d1004500e262000a9101d90040384590a0a0085013002c0c0044420503920f40000c4c06028039100200c1d50301c1c40b4046001d800036901040307480700480103010074401180c001e03c1c80d848940c3c407804d141e92103100c0030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 22479664 1250 22478414 22478419
    0x1905030a03050417070612020304171902070b09030a03080a0605040e030301090c05040509041202281505040308061e040c200105060901050111010204030606060e09010602010605030a0807030507050615 88
    0x1c41005113400010b2250181c90031546d9100c901070070507480001035000900308503190605115101e0380a00d03503c000d0300c00403040780b101d80d0079408210300c00307800c00e81030b504810315000e030801407103071076480025403011416031500d0280071550310360b80070f40000c1c8020b030007482e03200d42403c0902c00c13000c40000246050343c00e441e90400200540050580c0c02c2e10039482400d4100c150391000601140c2400b40941000070a030054400c0d00c07500b440c900e400810b201d46034400101007a00208244000341c00305500e1600722000402460506c0d0302c000e0803402d4001c1115119885c151516a9143c0910003815a4400c000d00180030000310310703001400e05480e164590300b100382241d0341070003c45014003e00e8040e16000e800c2d00c0c074070303400c0400440c1e099414a03050415903408100002c0010140d2040100801580c0c0e140190740410f88100080391406034800f8085a040c45014012940d0105184400f50703401040c0580d20081e51405443e14028030300050a05c1c052802007082010601500d0000c0304804c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 22480914 1250 22479664 22479689
    0x100201060611031801050705011503050d0207060201020c030403060e0a080c010212090a0201080c0906070b0c12060612070f0903050f0f070602030403050c0616080a020109050c010e0105091905030a030504 89
    0x100100c0943d24000c80601318580440c1d00d4000c04c4c154001e0004040550042c00003180200c9005148000c07080e503a4400c86550b404441007102182e418010000903005500c001c2d441e200002091960b24011400007504640d51610601e04903601008115070f025409481e4548844545c010742d4000d40290303119540c890078000c0000c10614020441d0b18299074140c4031020191a030500320301c00c603001201c00c41d800441c100030f1100841c01109240c1d12802520000d00da80780300d00c201003144d045010f0006801404180b0210303601001601c2c3c2143e0003801403902a4100c164450201c2d03421007039500c081c005008945641c100340350007152070702c1a541c030311040318400b40d070713861040340e480c8124840600705401500000300203240050040c402100359010703030384110501ea116038148da48400c0401c00941e5592a0102c1080820301c03c0b25802d9100342480368402000d600080c08070f1186d416003d201d80c842480c806a810340980c07202002e0700b00981260190300075894003418590160043c101c40d00034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 22482020 1106 22480914 22480937
    0xc21040513090c09020c0706051c0906050f091c05090a09060e040b01050603071b2303070308010915170a080d0209100801030b060d03020c1002010606 66
    0x40c00001450b6210782c41e200c4100e140030307840f8084090060000007118680829004229100340c18083d581e012070161804000c62240c10030803e5506e1720b43d051b07085c0034160380914450907e034055452281c031008045942c5a050038819406244041f8904110500c20006030030086c6000c2c0a211300c03241c840c6150303400e95a098005c4a45810321034200818000015000743c0180010b4a070545035040c40c25000700380060a0580071807000b02e256040c410000744000c00307400c01124a1100d5000741035800020b441b640300760700c19400242d0800010580900a00c40c1c900400710403c6003018107880d18074122061000d01f501185180145048200800d224400414202c004250010f03a1041804200011034444641401c10000306400600008034219111034000100310742c0e006104540389000c80c644032660342c802c0e4024240c1801075aa00e5015004081520010781740d4440006 = true := by decide +kernel

theorem cover : BRFrame.Cov 22302164 22482020 := by
  have h0 := BRFrame.cov_init 22302164
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22302164 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 22302164 ≤ n) (h2 : n < 22482020) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
