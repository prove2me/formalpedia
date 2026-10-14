-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1650
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:03:10.624078+00:00
-- url     : https://prove2.me/submissions/e214407a-4e37-4739-b0ec-bb5c8cf4d8db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 296582733 ≤ n < 296762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 296583983 1250 296582733 296582743
    0x2030106021504020a0b220905060a060509030a06050a090c150504061b1209062006010b07030e0d03260912031f060f03180803010302010c0206040b0414040501140102 73
    0x1102c59400102540ca0314804285803407500d07403162030a5000031949101180c0180d900354284161407030283c103851f8407000c40804403003007600c2d00c1e940152410b00410809010b000607100b1070038001d064691030596500d40c0300581d00125070101703800e66614620340810115101040142c00b503000034031180d808512020b802417055004020500c9400c003040c04070000649580408654408010582c0703410400c00585059070a0140300e0101c1c0c1901c01c000d007698007420040d003883d840503000304416480d00040c500c4c25400301000f5400c108410070402065150b40c0e60540320644240e0340c003c0550b0003200c141100000407860035424400346014009039601c0058050900d003440200326235207881360320082d501d44021148170500080304100008a40ba04411000c0c200d03011603d0900c02a080150500302040f02c0c4a001400845c00744014005944100d0b10882000d1028200a01e0700da2100d801d01e035290002d0f4031a484603038030000c04500c0c85c1094003070341e401042c0041f0024a0102c0c1040040e4481c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 296585233 1250 296583983 296584003
    0xa0b0f03010509060a0801110301051206090a0b130602040f050306070c0b01140f030604030906231204060b031009031e0c02040506010905040c020705041401050307060c0c0906060809060108010203010602 89
    0x20703c40050104185030782d41030680e002072018000070001d1071034900c1444c0d280c1e003091013003038841d03403500c00d19040200b00400c0f1a481046044054204512640d039aa480f45d0005441c0310020001900786000195080c402040541002102201510f240200701864180000e201c082001405886040080c0791107590b00c1c1174806052000703940101240c0400d4008004040c001c1d81403103640c3c148003e25810441c108141c0302b00d5030751980c111042044148000c4d003540c00031980d40504120075401d40c07032503844881d009271195001081307455801000a14061003480409141541c0e99031803410140c010328081e6458400c102c4401e2107401500c0094140040da0101070b02a6480b1030000304241c0c8200c0064000d4103000f08208104280a00002d5494120b400341c28021460400705070b841e800304040e01030482e00300900a00c401c1e410510704491120750460112018801c4260108815a00740641c401030051030340c0703544862418014852801c00182e100004a0b44108018406aa800300d100070031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 296586483 1250 296585233 296585239
    0x10507020a030c260f18040b010c0204050408040e041407140a060c1407080321010302090103080c24040614012616060f08090f3309010b0a0b0f030105 66
    0x2090200604030742c400b513021081e010200000d12490000d0014040d140c00c12018400d4041a0800ca080c0011a040c202c14540441c0c0080100c10061600760082075000307209203003950070300341c3d10110241510001d8138201c801106003181007a1803041001100018a03150440e01c420031181004111140b106001e44010000000305410a20481c52011140c0d11501000c540301295581c100540740d8004c0d40035030301c90301c03200707041c045c951110592118113a0350020708012444c0d181d0350355030000350b000c01560304060007416802118502111120799840f08940160b031a1440c0c00d207411012117000040e03520b13003001508014440400410131024000c02100d000c4640742c0f8010490b1f62600594420003003928541c42000b040e1568481640800f401054552400030380301d41001c0303500e925590b00c8611540d404804448144040700412259180f40a14070b40383c0030019640c001c062a1084650707200c169102d0094204608140140c10010304444600508259004100c0909803006114580c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 296587733 1250 296586483 296586503
    0x103110a030506010f05070b0a0509030c0d0801140901180c140705060118020c07060e130f09032604020103050c070f11030d0e03030d0e010b03060103061e0c0203030a050702010b0a0611010507020a030c 88
    0x2800e14bc02c0044070244a500800c5603040005104001d04800c0e00340600c19864240d90035040690400703a050034143c4184444610441107a49480c10007080000c5000041010001d90100d00701c54640081812900500107010a58146100f80b0030300941d803441041450b2040080383e0030f032200401c5650030b840003440d0005460752810001032a40119403035807001d0a00d0030080d05c00000031a402101c0c01ca109031039802021000010140324407100d6056418082115000500103600c20350200c0d038070011603000107081042d540c589103405000c82500701c1303000e075a1110444036031400f0400300484440b649041c01840b0010702c0440c0c2ca03401017404c105040ca0300c94801d12200c400070342080808dd54040c08448280d0b0b904e0401c0d401502c813410141151301120482030510a180c0c0c001c82d100d01c1001d0300150300c0c584601c411000100401840e09086540e01e40000030700d65a040301d40d40087c280da548080c56034091018850071190003134003800c159401101044000307608100301c0c8021035003116a103c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 296588983 1250 296587733 296587741
    0x6140606070f060509031b0105062e140f1b0f0607020c0906180903040f06051201050f030109060e011e0e0a030c15180614040201050f090103110a030506010f05070b0a05 74
    0x64694010340500b00600d403440c5010420805055202621840040f80c1110b5580259200c12404bd24040700c4034125481c11315901d034005015010b10801c0860100405180c40350888200125402080111142c41d842c4020656500e9041013002110002800905880c4c107100384043d54803c81040303400d0203030f510540050210380e60260b100c40b900310220706401d6603207420001983c890380b1a02406200c040741d8000401d02a1051041e604076415200b44481c56074200b400b004014180040084d03815074a070594100007642500500348401e4400c40041180da043c070f41e40c60400d11108002948541c605240c800c0115030009040807042d07014113051081440c2420092030110811022507010f9040c80348568916007a81d6a448106009500c00c00c02c0029502003100c074510203a40290000e242400508804071006c401000904414100042c01c800500d4441e403082c1c01400d0b9100c04295502c04202d0301d540c0000f900103420945140007880c0448640c1c580c0e180e000094030719440780395514006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 296590233 1250 296588983 296589001
    0x30f200318030f0604060608070905040b0a090503091005342d031e0503090a150906150503061b031f03020d14010b01050a0203040302090606090d06140606070f0605 72
    0x8110003c3e0400c0540d2100c0c40c2a090100280a07140314810312031003a1040018072008a120b054010b035030008100c1e0340c5844400d02e001c0501714050040d00c1c0d5010811100e54260303240c1540301c03060000c5840300340d244d0301d01c080c952142003d482c610b258040a070900421051175004994520a42d00c0700f01e4402440c0320307000403c00c0356401036811034240c9045440005064002c48101c00010140c901030b280c02203162011034045c001903911840c1b83e03020306000400034095070320454038105400360004001407240c640c40140e501000b0b00302c00c2d07440c0641d010312250805101855020911141d031b01021100e10304603200034480240f103581d00b444215180340d04103c14400e00c5d8015a002040c4001900715410180c00a0381e5611401480e9071803c00d48034103650042041c1c032401a2150051810300303203075800340040070034001c00b0160b000c1c00801c8045040e54604180502c0640200d0340003a2050f210b650106004d5409801107110341d00500041c000a00c60000c04c90445030f011901240645031400c80d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 296591483 1250 296590233 296590243
    0xf1d3705030a08130f0603050919120c1506060905030c030604050303040f0f0803010803031905132604120302010b0102070b0d1a0907020c090105090c070305031909030f20031803 78
    0x1c0001c07505c1500000889135815000070b8011303807004081d40c0768030885201c0c5020f11881100001c14841540040341d1010340588030120985028600c0601d04054a941060442c0c865401817004640300c83d40a016a080420000d1213404091f00100a5030030191181e03503070382c00000c00042c0190145502503041140582060b07030307015405040b60b5202d50b141c0040507201c0c0c00c21500302522070035069145003055400e0141c0b81c0680710612200ea4111050740383c5502041598040134690004002c50070b11610a4000410051506401110301039050b80350007130951f400580124110740c055441805844202011504909601c0c0030009500f06e43c00202440503c02260b59070303006101030704100d14140c02203426141110200c4894030075a8851080001904080c1c4040b0313000c0e078050000c2d00000303010740025504007940d074217000e4a00402210500c150303070382b00d40210700042c481d1006080303054018000807144a6900030f81e14894501c128035503603030b0090801c00c400c0000c42c0b0036001400d03141449 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 296592733 1250 296591483 296591489
    0x9170c03120307110c090a09110a080715020f0601140d05060705040f050a030f020d02031612060c030506031b011b11010f0206070f1d3705030a0813 65
    0x19120004420340c00c14240c1d8200f2583c540c0410300f00841280300711008140b090300381038001e000e0001c903215030104e40001e15008100300d072210b405442940c0346984a00043c0c000b0a50070005140c5142031036004c0140030b200c0c420503000d652207890101c410b400c010914505456100c4007030b030a4030707002c0c20015500e10b0b010400505640185018000059032050050041c0e030720003002c801195503500d0038451102c08520001e450407000300500310041c60205100c0600d2400101107440d0081c1d64114010f110449030b0003105040c04a00141042000f5030150201c00e40b0300381001c00c0b607445d10030b0101e0b40b900355103001c800040e0002611001aa030250b01c0340b25100c484034801c8503001e0b200b031400d01004402185043d011a20000000311060710000d00180f0410840d0381c4c3c40c102903880340080d540b43d0009203804590b0280c0f44c01c0c20b0207079115400b02d410f1803941d45600e038400760920a503400c0760ba911189418548800c0100500950720006900980300c0c1c0d10200c140d40c0d0340115451003480740c503150 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 296593983 1250 296592733 296592739
    0x307150e1f09090c050f030109050c0c07060c0302060703050402030d110f071d010905191e050c1306020613030518280509041a070c080d140c040609170c 67
    0x45054126264090610016910b01810410141c94030241c161107501404180d1110303406d0030001880b1001c55a004030303811402c50801e050500c498490014140700550b081040090286048102415410000c0f242c201e200c6e4241040f850400d5004243c070b175018001106c06200d500141c0424841c010405800001c16103426180d1860310b4100d8441c5859100c45d007903443d6100e00c000072030584890b04c20700e4056020498080c1401034081819805440d4030700805845c0e40803503904060042aa009451240b072600300c4440d03603114258801030a1300301c035800c4230b01154000c4082102c1c00401c4c44030703112100d8050034000c3c1c851180c0140d0040c1c05480d61001500b2035400d0795440c00d1045d103c00803102c10044116040d04c15511602400641001110090403000311500107800c0390b0040700a850300b042c1d480c9042c2410307411944603e1036651018048000c80c980c1caa040000d8481c0000400750054142102c8514142ca031000050066100340107101c0b0b0062a4030f04151801001c012540e140b00d00a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 296595233 1250 296593983 296594029
    0xc0307050c210c0f010b03190c080601030305030915070e011b0c0308040f0603020c190204020d1a0109060311031f090f1d030c0a17040302060f180307150e 68
    0x3512948803503800c0884044414803070fa1000d1800c1350010300400010400c0a8010940c20382c0c4001c428010080340c82054940342082000480c8006d401e0082c10302944c0640c030707150340ea410b140075070a25281303110001340088003461040c00712456000c14087c01700c58003440c3c407906000480c201d02400500c4003000812118030140008104031040700904111104c140303540c8201560703200140c042e440b0b05c02140c0c1c402c1d08001101d480190f6028010f49203280080d10040c2454041c501010880d1050300103182800b680c424960565a40320800e00051f210924090200100700400300c011400046c000c40e4484403462001c03554210043c081000801103610148110182e1290500c0200301c0b00c80e107500d611002c10035007070001200004030381c8031440c800010f1007041c20580702d0302c9401d5083c5481848410b820400000560f45142c042c10300714240c0441e00e5654021000141000000419294001d8100d01010000722100c0918045003045034141020128202c00010703240d1421031126031076071011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 296596483 1250 296595233 296595283
    0x110303160e06090402070f050705030d050d0515040515150a050f030405010207080304030c2001081501020709020409060503160e0103080708070609030c0209070302131a040902070b07080f0c0307050c 87
    0x6805440744238018800c6d00c0f0b990340c072041416180c040e4402540080341d41007000c040203205950040d42c4c40000002511055035400c4c00103416108180c8041c03000b84000c0240320254603002c3c58904850345280e0700b01d8509045107901515030b008a81b00c0d480010070100015080c00801e404442c822613015014030380d070780360501d009001b203d01c0c5001992400e5801d11415031510040543d01c04404050719400d24960b104280040386200c0380302c0560460041141c0024910b0213800500040c0680a00100d5114181000e261400352000d00f001007461110108005d440b05061515040d242c101284079038401490a04002170710450200a003034500c0e02840d002030680c01801c2d1b1809030310071100304c9102d842d003090440590040da003501d001e0710b03200c034001c001c0802032500c14031070f0341c0c4842003803410700d95144055001c82e0003001080d2403c503420402c201440d9800700030769070320603401214101a41042c00100500d40401803e010a01400180c22400e4800402054240400d101022400554 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 296597733 1250 296596483 296596493
    0x1150306112203110405060d061a09010602030a030b0f0d1202070b03010f0e07030507020d0c050703020a0b04170d020c09070e130b1e0d0305091206010b030403110303160e0609040207 80
    0xc061105403082e500b1032640101900e0140183c0c7c0c0110001000b10b00e01d031344d0b0354030303076400030105011052903030132000d4131001c0c5949401c1c030702034000d0001e50041c588500f80540042c007924411a8854454610900340130602c1e40c4442a11303007081d820410700c0f0703410104010140c3c60406d07140c02c13032841c42901200020f00240e65807403482c1500d1100d049081c1e1601c0e10b04c01a4181c4406542000c0940c10042c403108645114400040c000e40c052400c0302c405681d00d13000b142401a1580000c1499640003606005210404110095505e10440104200c030a8044000c2d02c4450042c0e07501e101e00c5040020a0905102d620a400a290001c0c4a003c0038281c501210300140b9841218030700030070b0f01401b6131800080c501d2130710b012044080d06980c80410a41d504072110b9210403d801d6014000e4980d425100208000310b031b01a103119201582e0b24105414041c182e8000303040a00069403003082004050300a2110440e2184c246040c8240e20000e44c400069040c00355031140d0b07400900c00310766102842 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 296598983 1250 296597733 296597797
    0x6091b0d1703100b073804020907020a211e0215190e0606031006050a0e04140f0a020f06041d0a020408030c0a0b010807080a110f120604140115030611 66
    0x5098402040708070b80b100d41b84a41c200701c415602803116404001009814074502d015809215481a6a0040f1240c1c2d04c0440d00d074000100b07140d413110703540c180703101e0180c01c46800b50030b01151a03000c40c02c16a01c6500290f0750092840c1005681d061030010602d07840f050318942400c0c54100001707000c4030030f1100c085a0340d4901142d0f007074030030b00c5038032a40c5121080303d101c0d4800741d80c1c0180510310347e80e0a00145d800d8246c000382048841007084001c60307410850a12000340c8409540c40513281404c0c40b801040b10421038100111301c80d070000c000400800c0c01c2c20b101d01781c4203450020000c2c0241e5648003084c0090045130b101009500000642c46840311020076034900c0213110b4410542c450341c0780c01880b0343d00c1066005984855001c8004e000110b44581000203070358038010041100034090301c0105600c01e540d243c0d5515581d2000d0144020000c031030003800030408481c00200105148428850302c51440c611025101c182c1d038070364201860740380c0012500180c1040c503400201d9000c1910440900c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 296600233 1250 296598983 296599013
    0x7020301110d0e0c041e09080f040308120702060f04200406090204060311040e0f0406060f0605040503010507030c0f0e19060c05100b09010603020c01020c06091b0d1703100b07 77
    0x54094001d11001c18689481440c03540400440145801451b05924100a040c1d07810103581d0450188601c500300704996004001441c402c000540c0c81e43e10302d1900310742418010304003801b035401500c10041c112006494565105030050080000a146080c441c252145241123081d0014104600880e003d81c650b0014011128260360411403031100010004c0140264000c1c110517800710700c04070f0151a80d070410603401c24001c000c009090340e501c1e01c0300d540090207640044041280410200320501e820b100340b07a401000c0b4202404454030301d08009016030700d0f40c1016801c0c40190036080c034254846444c0104803804000094841944030308018102ca0409002121584100da8808800384014001c26001581c05824221680d01b080c2c0d050700030350000c0515491a40d82845244042102000003500500400340a0468000706147d9003c90506e1480d41c0c074000c0ea03121443ca800a5103070194000160001c200c1c03181c036521281203011000c070055120034403140c00800c100c0e013800682c6000b5004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 296601483 1250 296600233 296600261
    0x21b06180c01022407091215050604090c03020603071407060b030f0d09090c05120a0f1107050a06180b0708010915080c010c06020904020a03061a03091207020301110d 73
    0x1151941d00d004980d502000900780d45225068001d4410202803e0032490308040c1c982040c1c0d84070391b1901c00d8440c81544460003550901c1c000d07035550b0000300d224807516821490980f01406503c00540300e804040506100c028044c00d4004005030340c0a12a5140500c4c0003045205569a05460b0038540080c1158002e180c2c82401121482c03c210319000814800407100307515088002d91601005900824038651301c01c040c0801000190300c02d034400410540f1400c40c424002440141038552101210b5003004d0011b2401010020b00c400328400295954813680d00071f102107807400690035008000d40744c03080002d0804139080d007480300d61500300d01828181d4010000030011502410030309441070b11288a03080090300100c11980080d44074080d0413002034006c0c800503241001c40c2e40820100e80c03003040820300090351002d051101c1c90404001441f000c4800000d00d00318140f900c105501c0301a90b00ca00d0302000000500d0b017045440039000300201d41d40d00c5140c1034417580d02c002883c0c06040a64880c030b074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 296602733 1250 296601483 296601493
    0xe0d06050a0b0607120e06120405030309121e0d0e0102190206060105070f0f170307020c0109120803010501080411030712021009060f0507032016090b0f04021b0618 72
    0x151505002d01074070301c1145c01c055941c844000c1181c00341c0302148564842c54000300c00700700c86407126061840040c041c62080d4010340d03480c64404540b904001c0100c4000c12039440c10400040d070480d41001130803071114000c480c5a50340312071064580051031184070414082d400031601c00d811180703030f1014000e02010364080d26540d50303400c001180c42e4460340d9002840c00007900ca030071010460300c240e08101c403449040404101c104604280d82207401c120f480d0300059000901c1034443d035038024a84801001da01010192031a500e0740d0380740f0b0300e0005001d41c9041050035800207040c8031108807459225007026007510000e80d2509041160a000d5000c16402451492104030344140324401d07000854100d0381d00c16074a40231603a0700b1030701640b10704405d0f07042000700455200c0803030305498240d900c80380d00001441103c858080300000400d181c4e00140c0320700c0c68182440401d07250241014114941141d00503a1030300620072840c113090324609104d141d481040100034111041920704480400c907403044071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 296603983 1250 296602733 296602751
    0xc0903050d05040513020307210c0e1e1903060908040603060b070b0417040509010803030912040e010302040906060902030a1e0903120216080c0a120801051f0e0d06050a 74
    0x74620b40300d11301c40d40340c01c400e462407001040302c1543e029642002c02458025100c00135035000c42203a0859040013030a5540d0384103040b01154104448880c08941074071021419089803c0403440e140175180124002c1120030014080b00500c1016040a03641c010001c0148070081c0c00c0821098200d40142e5020a02c3c015010030442c482d20140c0c0d44c02030388090340756201d075a665140d1610070040130380851120000e12002c54140d8516103203d0103813100a0003075407240b40c41000903207030401000881000402c10401801446445108a41034036010b1b203000c55011010715004000340101da200613401b41c03010051201382d2119070014001540c06191380b1504440d05096101100e4140324020081429100c031040454199005442c109060080c0a1030103000394462080f5507009410381c1c002904240c0702c0324100801442c21030b104840500c0c1000580d0304100200d07003a5000b0740001703204c1c540030801c0c440c0b10314440c02c03807a24603103400351400740280064903003000940400e81c0c5a51840381401164 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 296605233 1250 296603983 296603987
    0xf0b06010801061715010504090e06090d03022d12091e060105030c040b040902031f140f01090504230a051203060d021c0812040201030c08010825090c0903050d 70
    0x3002c56511301c00f01c4618a84490350303c400340d24100d5172014140582407000191441c181d01c01c40384560000005480d00d458070806072810003400451220030305105000380c1c1c0000e4084000c441c407008801c041c840ca50302c00340c00183e45d01e005003a49417151182c09410400d030042c010500c01160b00310840c14100aa41d404125a1240e409000740c0e40c16a0140350200d031685401c0d0860b03542190701410020303041082d600480d051600030810281409042202c1200c40141845902c086000e00c403d000e0f0380f030403c2485095070105c107204003088030b500c450100e030a0204180300c444841400c00d041581100360f0b0100140c0315003a41001360b40740e01500c5d1102160200c164112481042c0003444038255450030317403c02c0440d150600480c0040005810480c00083ca074400414441184140c50b21051800b480010151900c09a00c07400f0012407400410400c200040c40c82502c81c11051810000c020101c0c3c1c0c403212461541c07000001c80d050580c440e0380183c01c4200002a240100107641e61743c4001401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 296606483 1250 296605233 296605247
    0xc0a030e0310092112020c03070b0a05060a05090402030f0604150e03090906010c14010207030c02130e060a0f0b030303010e0103050708060c0d0c032309010c0e18060a030f0b0601080106 81
    0x10250858080481030f0411400703d0540e007113000003d00748200d19007900e039020710481e000001c5003001790307200080340c00070b12400c0c91803280d0140554500703120f0381c581680403910500c030360300c1400c1c01403c1d05000f260840d64240300311415042e20300100d500d0f40c54503003001400307900c0032022000c1103468080031522000b800300440e048004e001c0d14005482d15400300446200040b444140c840c1c10107052507080441c401e00040091300e010b655071030300e4440a4010400ca100e80c40ca0801c40d10f51034089125042c2c0c4010400355880703007103030800044900c5400c0a0802403c401d68166034580400000403548817050710304507050703a00030803c503601a03840e40301c1c0540d250003d03900e00114880c24000142c2c220850341040c00742d00d1151034041200700c010103000020800008200111400a03400c101c90b07090300b4850003840d840185441d4141246d140003282d1000f801d000400c1d02d1156507070000e0b486403501ea02c0c100003150300c40e001a401c0322803030a100d40924070903181c50b800201001c0001850500c80e001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 296607733 1250 296606483 296606501
    0x604092108090f1e011103010b04050103180b0a050606090307090e0f010b0a030f080d1a0f010807090b090d020315040b0705040e0109052701090203010b040e0619020c0a030e0310 78
    0x41c25840c080c05000400d41340c50700c1031a4504c4d922101084003d014240c080c6000f014100112500c0f14205000034090f503c1220711418a040e9482206000c01c1d0280041600312030124800211601c512010401512400c41050f80501c216803000640c240c0c144e08c501261000321003550045281420980c2c00da460f0300103400d5001010b9142880451b4003c136410b81d2081c0f14545051504401c4a00c0c07078103032518080c3e0440b28191207003003102d070760510041d2012403280074600b001880c54580405001c20401d8012215140d4020500d052107407112102c412055400508171102094078440f901d1924101f00c8040307960000f420040f07055a4003942c107403019144450148140c5030f007002021001010028075028494036440e814601c6e10780d0009051200313110310030002c110840d0324010325080d50441e03440a402545001c000034441d036404030311550820b00319001c81c000d107008109114042c3c051034040310214050102e40304201608104043c150620a0b41078130542d202a08040d0b0840f07841c0c003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 296608983 1250 296607733 296607763
    0x5010824010312050a0302041e23060a0309030c05010609091a0702030313051f050703061707030201030c020703080d021801030b030a0b130804080c09012309060409210809 75
    0x80190041d481c000c03005170491070201d14005040c190707a07441c1c1407083c40c80705203425124100790000380714081a05240c0e5001000040070004696000d00105007584030340c0600d1010140e03107998003c10140704480b41e4407800d40000c001c1c0311241d03d03426580b00606400790111405040084814280540d01e40d05500c14a07c0750051403c0d96680c5400340505038611004451f14010944034000c04a0540c07242c02c014000c40000080600e800000601107400741e0f00304e56102d24a8a1202c0c081038000509142a294203207400318400096840c142e140001c9600003c0c1074174004107140d1240c803007550182141050781e42c0c5208007090900015811500240b152503013503009040280082440d06800d9a08890100400c500080e015210149650855008030007243c00011700d5080521346517160f9800b4020803008000c0d440e903100698060404da001206002d55603a1000030010303641d613803004950300d03000080c503c030b12200101005071003000d0120782004540d0382c4000c07032520b1100040440480440d9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 296610233 1250 296608983 296609003
    0x6090f0602030901140408030705010b010207090e07120302160801140c03040228260708030301150f0306090c0503040203010c140f0706111b070501080c09091801050108240103 77
    0x71200445419200840205021908000c0003c2a020230801400094050800040c1c3c082d6004002400c1240592009401a0922000801c4c16001048071811503923461404031f02d21009160030703401c0014402602c0c10100300f41e140003e0702c42040d000894440502501d4012079500d41d00502c25901090310003170f40002c01c80e010070b200c001124044880010410203542003840d0394024901515130140d1040d140c2c002c10103001c80d0403660421107030020300490005141558142400100c60301064001c8404201b082d00b210504070f402640709501400d0702041c01e02405a038a04090310503401503600304e010b5840c121011640070311a65180340d210301c504151514241c0310040365840c41e080b907001a070301c01d40c1d05e65801e08400d844100038800c1c0e109101d280300f0450545d0b19803504107041540058140a015001c121452500303000720352800a0403507010306145c0b50184145000c08c4002040381c044d41c0390a002007050800052000c07604100000c00040c107014011250015031020b200050844000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 296611483 1250 296610233 296610247
    0x608100918060e0c03060114040b04050105010219060608060a02120f06100f1206030606420e0406030501020c0f0a0803131407060c120215041113110406090f060203 72
    0x7160300030314a403004101c2104d00ca48000030000341404002c0e0301c41000900c8034000d1041604050049900c0b500d022101000b480d0f15040010f901c804811512120f4241581782a40400015610032005461034004940f01403401c030001c1d134001e520030703804a80d8006c810000070b092001030702d28162103400e0160204400000c4000240c030610906913500060001c4101c3c15403001c1d02da88200002580105000b1420341d1802104a40341c0c48078040200d10500010541441611840b281181c0d910958580d48064011540c4c1220711441458060b540309041820000c00d10105401400c0e0030301840c800c0d245034040001d4100e90780c00314140010312940050000801c00f041180c1d0024502c0e0089414401c0c5006411855091045942002010481040070b40d0140903032640c01c2c40b81d035a00c2d80018094480c00038529a60001d0040000702521b9032010a444152070311039070842d000b0401c0100784520074110380c46060a0300903026080000e0281840099000200d1802c40e0031500070741c01452414030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 296612733 1250 296611483 296611493
    0x706060806180d0e0108220c03030e010203280504170c0a05030d020703060b01030902030f070e060105030903090f031009050f0d090b040905040c051018140109230a0608100918 77
    0x1b0014001204401c80c40c00440c2240030030000a40c24034402d4007101d2502d419494090300807100caa5400741158421f002c190000c40751860110306c001e04811400c04540031600c4102c1e0184503d801c00c400c2010f224212200c000b030b0008003209608000c41300b455545480300c003459595000081c9180050344a004208045415641b0000c0d40500c18900458808007540110386031030a48202c0c0002036116140400030a2503081c51241c0100092900a24604000300442c0c1d0324000c15a1044c4502000101c948459404202e410110718908400340040350107401c0098490006a2041200d8060340140388100c0b440b0720240003d40c0e40d00706041d170902d800c0c16a142d0041000030001c4881c2c2c50704010101c3c8039603444d05103072000d44e81e9985070340040c4003000012140c95059800031620070a4030b455150706030b0708054810255423070508880d09049200c100c241040e07900154498010004a6020900a5019103540e05c2048100c43e5030164640c0c0b280c5c0201122010f46820340c29445c54115000050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 296613983 1250 296612733 296612747
    0x507020309090912120703060605040f090e01063515130503070c14131e020708040f080303090f0610060806010c0b07080a0b010207290706060806180d0e01 68
    0x68100d00842e0011400c4d004440740c0c035440004c100f50364240c00003c100784c0540c14020400a015545052410079142410f0700101c46440e0080c01002501e58a000c00c8003082580f1a900404402d45e00340c28035030300319003d4401080c034100240c40b6480700da040b20400140026920500e00403001c4c02032801c0d0f580503001103200e0780d00c10381201c050000300f01e11000b00384051907020190070071132090416000707020200000c038a400c41c2c0007c251800c0c1000c0c420581e094180401d4072040c040c502681c4d0303401c07510b4180d1642c1b040e600324006450280740007081302c1400101951141a840c001c898034400c0c4481d90076075801080311320841d00710f052a001c3c051188112400c507002a0103041000742e041c1c4c0d0ba601c1c810030510450b95a40014003900401230300721042c3c0241e062910382030001d04440c85c205540a4458401c074400d81c80303004c1900500740400201039044800054015a007004015218003403141c851a0944007500e880050030107080d66880c02081d408051a01501c40d004000001c0b070064441c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 296615233 1250 296613983 296613991
    0x209031b09270a051005060d0b010608070e0415060206070507080724022712120708190509040b1804110f030d020703020a080d020a0327090f0c03050702030909 70
    0x340354204150000c1081c1000f0702e24101d8440c4000d000d0007240c1034462002c0715001000c4522405201c0e06d000081b8031315442e0141512101c1c603108400b42d80b00d01e4151100d078500948260050718180110f8904d0704c83c0140c807410740b601d55007030315071a48071080200c40500503404d0240c40101e04112072000112a03a01e109182c4d205106d41c00a40103000140f041283c201307035a0650303802c1c540002c01a004001006001d8007501c1100d441c0b103a06041004a07941e00101030f40320440c10030008040c824444040203640131003c492094010120b620f100c010b02c0c030b07005110fa0600172414804110302c03d10b001c0301e4441c0c400c0a00d010b0503480343da550310f54035400d00c001503405d42c002a59013040c50043d00c05220003030810a075500141852171861040c401841e0301ca504c540c01d1a08140410f030000c03680803454046142d05407628955051001400b2000c0041080107010b1004445600007540d104641004001920510041080b46590032040e000c2c2c410455296005803c1080442c582c0d141c52502d29801c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 296616483 1250 296615233 296615281
    0xa02031305190e0a1805010e0d140901180503011e0c05090108040f0f052d0c0a030206071b06030e0d110607030e01020c0a0b090d110d0507080d06090209031b09 70
    0x1c801c0c03140c0c0f2511401588030070740d1180d4640231030b07002c1180200003110b414100b85c6045816036440207888a0580507042e28a4100700554010118588840340c0b48000352000a00030403101c4615080c11a412804d4030500d0760f060b041018061840f40100142d4904030130684a8241c41e6035559540c0d501c094109004440082240e50420007003a010000070701400c1d5461803140b519008800c0c2d10001403001c0042c52002d0f40003200791000c5403104482c1c2000c8a60655481e034840c001450a07141c9041c0382c541c2c02000480751503001404030f6040e0400045188100c0c252140f0700b03500401141c0a100d441c0340d44110b40d100c1c00100d030b43c4a1095128001c2001c00d24001802c007122402107a04200d1605010381e15140c0e030b2402d200080c0300c1406003100019450512440c5c6040590492f40c45d40d4541440000b407003030109100003409161011038900394400d02d0204a81c40e00c441002009400445020b4003038030802102c0e400c5c0c00d00c107070180d00504000518200c0170b070f520000d40450a119007812684 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 296617733 1250 296616483 296616491
    0xc030f0203190201060810061206090206070605150a09140c03070203070b01230a0f03020105090a080109050a12050414060f0f03070806090c030610080703110a02031305190e0a 77
    0x102d480010140900080641d50001c6007451400003030928001fa4444403020003032400000300a444100074414400680c440d5000c00c0360302550000074114029400701800480c184400c102c100b2503040001c0355a644111003d5000ea40c94080f0802214181c109054a44120340042155a40c16501840c0e01005920480340f0b80303403180c2c5c3c6960301030f002079102681c040741e05050000d250189c80e08400341160240c0f505034803507142c40d507082c0ba118000e1001905101d00081c55145946442c1c8a50025000305ca0007800407242034940565540400070095400c02081d2888101d403507c035000b00c42c00c64519112104000301c55104014081d031140c041d1010a1104021494900320080d000d14407a41e16a10781d00914a0b01c10180102c41e00c006244d040840420010402c543d526202c1e1640300382e145141c0128158ad41040581c0148201030070021403203004140c5120169000000704900010080200710b0251740704280880c14901c1210444132500c002d0083c001004a2560316a1103d80b0020120f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 296618983 1250 296617733 296617747
    0x2121b0d0903020f0d230322050d030506030d090608060406090606080907090506060f0306030f030f071a01060c08071a040303060509160915020a170322030c030f0203 73
    0x121400d0001c11070158128003560403c5a60034170420134901c950b810003002c81030201d524140262240d01000d0003a22000c008101c1d40c00c0c4a4110300502c00c0d034001000060600313410082d580c2c8480f1710002000a00b00000214142008200c100c44465241c882c0b1080508021055401600080c106900240c0c0c400c0c000401d101513029800040040d07071101c0506007840c8c4a038500b000801d821500c0714904001c02e010182d154001220140040b0110168032901c614000a0915410070181103140c440400c1c281880716046000788101c911958000d82c00c401c4220b44d02c44664400d01c1a038011a84099000000c20711003001008400c0c41400388000d01441c00e50444540b0200f9103041e00080e40e201c00034000d90504d6a1010340040040084031080000000001c20407017103170140c4099521000810003002e40200006180980e01c030001210003003028030911101d41089401e07217514600d0290840200d400c4000301c00c3c0b1241c00d95508164011541ca041e02c290344140780c035808511081202c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 296620233 1250 296618983 296619007
    0x51c0204020d09150606020c0607151a040b0a0e2806180e06090a031b05060109050f011a0f0a1106130b1803090d1703040f1502121b 58
    0x426440362411000540c0403c03504000321036121222000240901d000300611071243c00041a020000d022241550b584415140c8503c0c3c544a000b02d1384606400c0c0041d48081104e002170b04500300c00c00f51002c0100320311030380c10000c18280703601c0748505040c013800108803500f031a803d829000b81c82c402c40030815011440c19010440d80750b50300c05490f000d10001c1030128070703416010301500354070b1800c0141110306124601d40d4540390304800c0141030001b07a980703c00001c80d2131180c035600650000280d4241d5030b0f6a2252402401084551440f08102180007007441c0e00004001c5026020f0664902c0c14004148010004c41d4041c00014040c407090182030000e820080108511504804030f580780114481d18142c406060b01800803070080d41002c00c2071662000020555010f040104e5502c00044840d06005980092002406546150000270442402841c040410609202c1d205081da1700800600d00c0089025a0300d00254201d041c2001c03ca200285085980c0340c0101030110034a4401d2201c14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 296621483 1250 296620233 296620237
    0x40c1503050103020906010c032010060f050f040212010b07080729061012051801090c18091a06030f030c0f1203090604140309040c030506130e07051c020402 69
    0x11440041c0d00d400042c011400d00f1010150824028200b021402d17016a070090034450544410001c1e11400c002c07840780d4050201b021760a01c80c40544204192500e46204149210260207102d0183c07a08c1c44442c00541018400c40c0d0000e074803020300c100a6420650310079019840801e0640c0c98010601210f13012580d41460814640a40c900c0303400c11614a1920ba0078543c0010810f502c42c03142010100416600546601c41701c00c040f0030005441d0f1f071081f0384941e0880401d0600c03d9190300e4480c0000c10000404a2a02510300001e2106c1c462803003901ca1313800391462503000605008488012102100681e0301d840c0d0001402019a030780034108500c0c0340d2840c1c00203507080103554007101084681000038032084c00400351100b2442d10710700c2c00303060349136841e040a00010b000b90714440d20021004000e0041c0c6000302801001030101403810301c40100a40380c00e542d03e602c6048170000b11400d50005120340072400502c8005469802c0c500b60403c410203a007000301040c180711a12031000103a0311440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 296622733 1250 296621483 296621519
    0xf0f1d1204210614040b130803070e01030e010509150c040f061419081509040b130f0f03030f0501050108060d0b071403040609060c0f02070909080c030304150506041104030605040c 79
    0x504c42203500e01802d004805100217400000300005203100400440d01130400c07250f12070954100710030b22114010048000b0103110001408551900b000d100f00040f0106603c4070402c7c0e4400a946aa100d109130500c1c02e101d98841c41c3c1c00554240001c10000b401080d0706c25480d03030484039650410811282203244154080c4a600004010000b04004050b03901d50200e00b10a05645241d41031405036a6000244070161120070251700c840020402c01c100c800440c92155401142c24040b05840e1a010b0041c00c10025074940d11b90400d40080380a5200e9250140b103880c2c0100202c500500c95202c0e500b00b842e014046204014a44040c82d4803c0004801140110701c80c0000190074500740c20201d0844030b040561004108640c445865041e134002410700035170740c180c0c10010318004a4070741481e1034070441e4044421360002008000a00013500c0c62002e00d141805c0080c030440d6994801c10040f1404d00c001e03412816400e20044c0b000c2101c680c002584070307116503007001403075840702100d42003c100d460f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 296623983 1250 296622733 296622761
    0xe011406010306120b13020f030703030e0405070c0308190e0313080705060403080d020309070512032206020a0303020f09030114041718130f0f1d12042106 68
    0x205116881d64544120b0000345030054074112055856964504060809065400d840480751106800d5540705a01700343c0d01f01009088410841d9a843c000e05000c4408100380d02c11844d00000815050244e034541100907459039640d941507840c04c0f54118210380100941598a94425043d001d2038400c0000702401e1180c4896031100c3c0d440d014880d80b174a40d45400260280d00280800c00000d0f0b044403d0f240d10442201000d41c1b20b545011000e03140007890b0344420b0f80410016000c007034080c000300050148410300c642641c1c0c2d140c0c0d041d00f14802c03a4130034441c0310016031100030640d010a10a40c00f8001600c00c0443e0705107000d2aa10009007035440d9102c0b0701100102010501042080ca1101000110907100e61b25041511024103074500004034a80341c2c3c0941440b06412402000c1d41d0b11001d00e0300b0b1155010020316a03050b54800050002a41010454036a5011414000e000048801c20a0180c0e01c0c110302d8181001c0038400140c0e110812000c501800d07510520004049010f1101840404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 296625233 1250 296623983 296624021
    0x1c05040f08030f1b03070501060f0e0601020609101a211903020d080408120c040807080a08070303270503090f10020601141206090307020405060603010f060f030e01 72
    0x4080011210303415032000c1e016900400164000407100c60507645040c0c1039000804030b00c04440c501c1421482660310091040d442c254011034181c16074200756041d01c540f444140d880d03550f0817005907600c5400762100c50481d8080d2106100c0041d451700001904070a045014590b41d0556004c07940c4040b903415080c1801405080d5481c4c10803003003000c62038030700380078800c0070301001c0d2074601a440726000e0300d220040040302000141031000c101c086603402000d0f55041d10003482e22030000030342c607005401001603034060014000b468810000301c4000054102d11810b02e00441690300303078014070030100d400700c17000b030030081807600b111101ca41003030f10500503005140c1d04d130b032024100000c0c20b01170240c41d840b4000c04000d05003070b99800204607040d91300354182c21100c40306070000075892001c5042010118400e00f020451480c00100182016600c2905c0034055500c80104000c41070100340141307168001d10700407c1102512031040000240500c0c103002a903003209080503420348040d03036080c018030a84 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 296626483 1250 296625233 296625239
    0x907260c0f06043c0e061e030d210212010e1308130501020705220c020f03070c0e010608090d050706090c06030e06011e09090501020d0e0a0b06030703031b051c0504 72
    0x11000c1081810002011404089030400700d80f40145d4034040d05040c058003c40a007510710102c42c0800c1ca07109030008048031184900000f0081c40c2c28031403050491440c14040441c00c03908903030300a031440b20100620111440e0b081050a04128200611262486100c10f1510010541010007404900e02c4020150b078450308001c00645002465801240264000d0400c00c1c1c18074154001060b00f400e40c040007081c4018080c008900d0f00b51410703c1c46a49020000c1c1e00c1c0d0800c81c04440030001c4940b240e81050f080ea0307861b0400d85280104980860251b001159134012240c8520020800544120400100618141c1b90f8a5050081b6000000404c0c0c1d10750700c008010f0800c2081c1401022409042c1e01104446442501c00919a21403080300c641c40d61141030030400c080d01039460460041700104a1400d81c100002c0c0d40b5800742c0c0c400c0c0d0b040484a80070070a076050114144041c0d03601511100f001009504594090501001040e40e8902401c06001c20380010781a035a421221039603030755521141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 296627733 1250 296626483 296626559
    0x21b0a090204030305180924010311130e010801060803190212030a020a03200904110913060501120b03120d1407050d0f02031e06010c0503030907260c0f0604 69
    0x540306c00144070f10760306003c001020708035040714004000010a58141c030200240140c01910b1503000e03125000b2004104950b842005105480c12034040110486080e6642d040441c02c031a42405481c0b41c1d90020400f4100c9806146078050b526240342c8120382c84825132050b041c4180c7c0041d01c403840400d4001076030f9200c566060007401300c103044850742c0185864000f0740300d81c039600ca500c80c914041c6444280c0f01c1b290b0a1203100f0782c4c03d0703200054056100305041c1000500284140c0c0507143c041a055808100031110500c9110100d0b0f4014004000c140c9004032a1141904002240321405894841c0918071015032a1040c0c0117070007030b1702d91940300e000751101041030310420440703e8600f070702c14401c00c035550220500340701046034007003000c0d4410f48440004030380321455071001614501c000020702c0203400001441c1e0080710720700620312107801030031240600c6a01220750110071030b1344446258115032074044d548852a59000700894903060b503600000f100d007440c00c80401a2504402e000f90042c003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 296628983 1250 296627733 296627767
    0x8070209010e190c1b0506060909060403091e05031006081e0303060d0201050c0a031e09080d03050910110d1802031c020106030c080a020a1401021b0a090204030305 72
    0x811442c140761180d1401d4641038100c070f21480211a046522107600a10b0180291040c000d40745065146200b2040c84c0c1c1086075448805680c0c240c0074031aa00009545c01034007280c00c5006d6a856030ba06079615240401450b02441809050b14214004000001c0d05607410480c1000200d5105d0020a00c42d1400d004c040c20700100e0b00307505580414404401b54030a00202c12607078015801c4a0f0b401c1d0030509400100c409001d081160885440348003092414550400000d1404a900c1800505410a110000c90700350119219849140e4024141064503900a41201d40d00204c01f07000c40398071000780d441040c10f5950508040200000c0000c03030710030038005400380c08031282942c00d8200052001d50f002c25554480e0f8050102c07004102e05203807801510039040000215040048d803010140c035904401e40714110721070f08920505251100041140c0c1c41c846400c0700c4d010507000b6100814441401c00082c510035600b0640c040c1c1d05102c0483c0300304d918030183c00954000d544058917003081401c006440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 296630233 1250 296628983 296628989
    0x9060306050f010507050a0b01261903030902010c05100b040f02130e0703020f0a090603050a05060901170a0804080f210a03230705030703060509040809061c02070807020901 76
    0x941025414041c40e2552580c03114002400e2070a95910304060420f2801e01880c000b00400002d01f03d400041d2072050070a13849c0000c5420740c0b0b488803a8034801103484d61082040340070901c6d004211070610200703000342d00c65074203d40103041130100100141d40c1c0c2810105100012800e0310740c0e601c100002410207108074004600310503002c525010200b9042140b0903407074891103841810100004806071b1107501910010710070401d11580310141414094122440760240c440028076120004400303100383c0c003c9070300450000c0c040030502d9080c01c0c8090f13001500c56024a0310351040c0039500e400600705500070f100400031403003d892440e01070500e9604040c01a40b035400044490134210030302e482d040342114000501420000388200400400900004c40000132200d54441c41d820841c015800c10000c40c4101000e940800031a52501c04024804e007007a58045c14551040c0704048007410311800818801c0610a404814013800700e0350350381aa4071501045a001a02042d80d90841c00c1c91740340c09001d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 296631483 1250 296630233 296630237
    0x11b05031806092d0d0c021806360a05010e07021506060a110f0a0303051003031403060a0f0f15090806070f0e0307030b04020a06030209090a0b0f1f0906 67
    0x40d6041c9503c01d140da404030810b61100004000e40c00d003a00344030f920f10010919071910143c0303101c80010880038161039108641030b4080e2102c10700506d41007078410701951003207000034401a00442c0d8030200b00c4080340580c10810120b0600c0390a520b0b01d065800c80b00313129500622000c1120741c1421104421900050002c2080d54000c11000c480001d01e03007821903010800b904c07071035180d00031072400721240504211042c11b0b0740601e4071003c04c00c59004c40d1145020303019440500c440c0d1502140b260000303000341702c0640090011941443c082c8100340c001e68005c140241000219a1038000c201000c500560002d40d950300051020048000b0350903990407012560305113004400d03d8420003940b51880207101c5000c010481d644120890f01a4068031b0450101408a4006540303900d0020312440d0156000c0c0c0c82a4041000051040d1180c02160140403000d0106541d5494106c1e00d1800341110b41804c0d0362003001d0f1030180b000c0d62144041c20380c11030b200b2400d20300e4140100202400004140d000102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 296632733 1250 296631483 296631493
    0x40212061201020f0a0c032607090f122301060f082b080a060b190909060f031403040306110307031a0102210412081902030a09090e011b050318 63
    0x201084004d003079030080d04a6050024141c001440d00311440321441040034000340700c3c0480503081001c0f4503025449a40c564448a864580f14400980b03025914840c1d000042101c012100004404200c022841601c00070f000c10519040c507130071425070345e841c1c21040e50307e4594202081214410041c440780c071400f500480b82d040402e00d00300007507454008030280600c0010000700c0c143c01081d62180c0b005010300060700d5128180c10030b1340c02040003c501c0c00700001c1c032100404103241d082441410100da5104500340e010602d107540d8602120003100340c444080c04140f00c0040482d000303002da0340100541d21600e503920303c7c01c010058101c8a8113008001d0100f944000030420780d030001030040c0402251010741443d0030004c0780c02c40181c8903c2c1c100d0b508650303001c8ac01d2401c1000f250042d09801c540c10411070305140d040c0404070780e00d0080604480000d600b80341d0401881a095005040d0f46030f1410001c200d002042d58812402001440ca04001a40c00002c1208003000101e01010424203900544 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 296633983 1250 296632733 296632747
    0x19020108010f0e0420040e06190203152e0807110307020a0501120f1505010201060e09030708070804031b032627090a09050c0609011d0f04021206120102 67
    0x5194103c004000a01d003000e00000741c2e44810180c00c10440b640b00040c014004a007c401d2915100d4006541094080c6143c103280d182c2604180203880c4954034403440070300e29810150801080e0700d1160807940e112a100780300812010400c80c603a0414601c0d0343ca400b151030a02840041c0400031000055139260400e0042d100113a40f01c03403540003102da0900c0c00c08070303182041c40c030307035004118281d172000c035603072600310a00c800b800c200d8004000c88409800030459540e507140c0303400e8a0035007150460801c3d0400c000381070001e00040e0240500c3c2d07000e4004c42d4181500c80d40c0d030503214849081d0381e991a010b407910800401103a520003a19034201e204038070111141c600084980f88c054184102c2e0780248031506a20802c40c290b4013503a80700da00609401441c18150400d80040c41450350a43d001d0040100d082030f1820170b50111000890181e450140c0b0302c4c0c880b5159220600d207504d0607944111b203001d44000959882c0060101044000e0039010682406020040b14210741c3c2203030f02150340140202 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 296635233 1250 296633983 296633999
    0xe0406080c01030f1116050c1009061211161203061206020309010b030102031f06170f07180612050108010c0903080a03020f0a0c12090b0f0d060819020108010f 70
    0x2070450004207003004100324080c00314010180c582001242d0300920042a41131050560404100311180550182d0f0302c00b4200c0e5060056460720f211100001c241c003e034080003031601c03c040020360b50315141c5001650900c1c081480c0c41641c080d04000c0c0030b042c039401202c0144801d030488103e011035541001c02c8801c0c6041d0510b603280c00042c80141001350701000285031407d00303401c6103160041c010002c540d20300d4000f8034001c03a01d06009051a80c84600b0801280d00d84c0602d04040010340030b503100810a0b503402241c40d0301e07540e004024400b0490344984448204002205607405800d160325603010b492402a1403008030b8005134845529a810101c4c204680d84d0082c01613000e40b81c00c500c0143d910b00c410324060b40039100d1100348031444900042c0d0088104d40c07003484130030242e110700031900c1c0c209402074003110451114000c8001c141020008070401d41c0c002c5000b402043c450407804500e1607550100780c0d0925141000c115076040b4a80c4c0007400310342e48204214050090001184503c81c141048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 296636483 1250 296635233 296635243
    0x5011403060702060c18060706050106110c060414280518100603090503071a01050f0607150b03010921020105010e10050103090c0509040f050c0402070503070b1b040e070e040608 78
    0x400c50105c04c0051360b01e81c90144c00035014541d00c4060505c603665210740c502000140b01c01d03c54074001600000d414550b20401142020461500070b003424101030a1164a40201c07904a25043e40066400800b1b070703600105000c8000420b581c54104140c080c40c2000b030250742a00d0342d69030740d00f15252030104102d0f0403103054110151400c43c500020016440c1c500f10385548a607000241400204003640700502d001d00c40180e068442c00d40c3d4600d1340701c04082c18810f0728020150004d081032140c000780c3e035050185030300c82004000000d00124440029840b00c0d811020301a0030085c0d10241d20322814051a0240603490042c100341c1d000c2d451310319000007a90544c0c03410b03000b450304150b290121041485190392007000070b0080109040d803d41003600d4001c002c00c082e11030440b40b60107660740719005894240300780c3e80c4143c0c003c40514a026142e0b070340c172081d240008100221201c1014540210614200302400c003818035003030340c9881e5086c80a4050407010340c0d9500203100300d00300107090140e0040458 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 296637733 1250 296636483 296636491
    0x120a09031b0c0e0901020717040503070504060e3c060a060903030c0f170301060201020a0807080106051806040905040f1103160303030b22090201080f010806070507110303030403030501140306070206 87
    0x1040d042607184d82c0c2c46240a032080810103003c6c62580e08030f405d0503840c040000c000316078003207040ba104a980c580500081d14070074421304030402d0074074000860182e140c000314130746078920b0010301c040c02030b00017994045c448000803001c1d01d403030700c2c00101306190a104100340c01803c010700780040070603c2c40e07400030700e56200c00f4401021280d40f00c0c403403810006103c03583d41c41070b81030106950322581c44010080c002d4109001450016500c0408626a180036181c11416260341c0d030344103443e104100001071070030840002008d41044c4100300c0040c20f05031610a0324090341c45010103541c01d0500d802c1c0413020303000f022100fa00c281c000f018144101402c0c141c030403049030f505042c08105c032800c180000382c0c450f80c8404000c020031101c142c494440401c036800b4890784c81c802d0b240c0709156216050b03000540e00b0b09004840c5164099800301e05041e000d40041d102644c03090744030074007100850002c20300310f03001550201d004c60349a000600400c0554445007000b40e0040d0000e02c41c51412440003595030902034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 296638983 1250 296637733 296637749
    0x90501080906101a090918010c0306050a1505040806042102013810180b04050f01050c100e0303100902070203250f030515011a03040215120a09031b0c 66
    0xc84d50341580c00140c02503405030316000300050395034645411110201c2d80340b140544129468403d0002415003e03100b800e055074000781801018500300047ea40c03c0c2280c0744c02c0f00044c00001c0c00000703802902040100c3c8114070501e41c1c0903404202e0990307004042d003e80ea03988150390501944142c1250400c1640c3e103c0000d2440661501480c410060181c0d418204101d82040a00c01541c0080b60000c0c05604140d1420359010346496403134903d9643c9000340d000302ea51160522900c00b061b9031045c4080d04000440200395160b090040700d90b00c1c02c0315100c2000302e2194002104018140350010b00503030042a11250941c9440340e150700007a121290200071402d4038001b007240c4150320b2401c80001e80a40990300b81e188500d0344a0412a64035003040344065620034003400081804106059404072203100317400301a0075901c0316801c014001d0781b6040301808110050094245440182c00805d014903d0614002002140350800402c0317400d51a18040c1c4101d1101c0216000480803008941100c1c044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 296640233 1250 296638983 296639009
    0xe07140706090f03030b1e090612031204150f05070e2211030604060501020c03100c050712030b01090f0b1602030c0a030b09060610120b190609050108090610 69
    0x9481e010006140c03841c0007600a00692808004042d00b44d8450a4480c5085a10200e00d00c0086240404044141000c50f013202c00000460b12605002d02251400c105080c2620b083c00351048850031200c2e801c94080d00c103900c16018240766101a807145100255901c04140b1082c030f41100040c021050707840d0406e01030203000300750f83c0500006520300c42d054048894144101c10640e50040301c2070708142d800070300c100d14000b0005031540c000681040c80b0031018019048023103501000c50020001303080ea102c28450100070500c001000e422001c40c0e00d080340d880c00241d03a41039400040850b2181d8000b5000790400c110280030001c0c5440640704075400c841d03280700341340c4414400310342003500302e115040e00070300b90342c00120400100c00d55480c072602005084620907581c8104200e1100b0000c9004030110319000d50000c4512426040034104007006040104409401c1040240c00700480d44420005182600144440d682c0401c035550005074800007084603040a020101c5003414034820301c8201101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 296641483 1250 296640233 296640247
    0x30103150b03030a030207020f092203031107120807141b010204050a03051e030901120c050c06010f17030f04050405041502030f0103120804050a030e0103060b180a0e0714 75
    0x1504500d03840880607080d2911095000001742c065041140120321443d000421405c0d2410190a10341c495903828085814285101c01c81035641c0a83d00300580c10540c484083c41d503502d0a29008090f203503c030300750f00201035054030401480008042c282804000c0a10081c01199800303100751070b0081e121514400e0040074101c0c010f40240f05079849141c00141d440b8002091180101300c200403840b042210150030418090000e40f207114500d01a80802c0c0d500c2107469032100b45038800503031411300341002c0b0303d005078440038240390447c2640300c401074190800051090024002a45e0103130407003c1c1c0210300b840180c84a00000740038a000d5180a6681e440000301130080d400424869584c1e211021544d074104041c002d40e034240240016a1000000b2a103102c00d14803800103148030300d40100c0038101da030300c403560110b9510078a03c05180c10107440f4200070a58100f40070003800f040503c10071403c0c440d007410b010b02c44040e840c0e030301200f031440404d003c001c0101e811400b101c01c0c4210340d920080e03950031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 296642733 1250 296641483 296641523
    0x13020405150a03050c010e060a1b0816060b030d0e01050316020a08070f1e02030604020d020f040c020714090f0a0519050f0601080115020705090414060408070b070311030103 76
    0x44206042e031095005400009010001c00c0c0c2c13a80200d403e998541ca2114500705018084c82150300e980002080d03016404101c2401106490380284200d0b886072800005180e5030136a1800e0240542d0440d5640166050350300d0300b00001105a0558101031100d403031040d0000e07010b404010041580402031805000b500d510074006650242e0f07001c404a0340f20750090510100480444404803428009000c0409819030780025802c085d55004008100719925070342444150812104126042081c03c0c007000655a0f85006282051855a0041c490107152004400e250401890314034055001507003401591143c0340b4070142e01501a0318007003840d0b05c1d1540d8030031900000852050905243c6401c0c00111550300380d082d40100001d80c0c600d403c13171742c071a0144c0034003d0a00f111800542d200b160208000e0806c515504d0303200740101600001140d03009005420400c040320100c03801000000c20030204030809070515000452498100320103255000180d850b8801804064850304c00200041c10303002d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 296643983 1250 296642733 296642761
    0x360608120706090c03031701050303040f0306090629090f09070608041407061706030705130b0118080601050915010e060f0c0d09080c09130602030c13032913020405 72
    0x15a00c2010300300d03c4d50b52424001c001050610a01462130086000003c2a180000036101500c92485101c00d84a1441d55910010a00d920003215580c0e100d100c0300004413032488540d00121010743c11400132071440d104003e9544d900070f0900c07400490300b1090080880001170340c1d40c06d840380c40c1000082c517201d6051031180011a4070b030b881c600e4440c0d40e10104025031720003840c18503540c114442c0e8246480e400201502c2d849603001d1150000d4800202042200c401e4004c00355441041c10017060b0444901044842098075401010160740004010803540c10144c886543c40030f0100584410101544c1c002030440c0303403688000384100c41c003294010000e00400d084034001c80c0900221482200c201c100503000700424860f80b141401000c0ba0800315080c1202290b10547d10020804150121030751864000c0d04081c042541c4450244143e00b0002640c0c15481c1c061809042408610401d2011486401c18030341c40b82e000182c0752605000400303100c3c9891422103a030450300401c01d56543c0d56414030007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 296645233 1250 296643983 296644001
    0xf1d0907091503090c0b030f041203090503040b09100504080c210307110f010908030904090c030b0f0f010f03020607030c0602090a0e1e0f04030f09360608120706 71
    0x408001c8020410380d905540b0404211707210b501e015850700d81e0b43c0440724150000701c6250404180810001e80092a99429511440c62508000400e41819115145560400c0c0c20031300c0d5400c6c002401840925241d00c2c100c0381c0309001e203409032070541000603164840303c0308004d55008901d603445440091a60004500d10900300320112502d0b04414149038880c40c510b1a25103000d0b0f48003080500081d481100e41c00203440c1100011072802c800c0354107000061001c0314064903418001d6401100003408540464000c0500040803a65424090701000c2e01e03c8043c1e0180d0340c09941d00f5007c10050b12010103a034881070b00342c10100c021400ca414a80080c1c800e1801007580000e00d41c9010504d4084600c2c41c0740100b280c01404038422000090350809040c0598120208082e11400100042d20078804008903002d1490310070541d40d504e07a500c0c0000c492502d101c243e08d100d0005201c2031000f0815074208207400e0144144001450301c0d00c000d480e1203020380c0c000364064000941d00c05102c9542c00400f09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 296646483 1250 296645233 296645249
    0x60f0b060a0e061c0203071103181905100906180509130204060e09150a2307020109080d0504020f031506150c060703020c0d090e1305010b030f030a0f1d090709 70
    0x81c0504d52140d80c00a510458914011a50307095042d40f10010000c255000c01e0b42e01c021880c0082540810031400309a2008100c910b00c000f00030108054403141e40700e118a481a4450000241c1080005400101001d10310040c100d0750724000c01c025030320303440e146401051000807106015194004503000c0d1409811512a0054940500108400000340a111044400b50a00003500c03412a1401680c080c81e42050403650110b40040ca13101c041500a40c00c40528000042c00d149190350340d4ad056005000244101c44c0e0350f80c00c01041d401d000302c1402c43d6450032000b074035008442e0418280424006811740d4054003200000c102804a4501241c0c4203510b0f0390122207484c0b400c030200401075440000b99440c140200004885c01a014035000c905680200300640c038150b07031344101401b02401c802c0042d20103640b00c50455803030381c80900040c404182101c02540e618a01490054200302007a8440410448070342d02c4111a0032084d6201e0798030b42000c4905c1d000542b500c140c01c8900171a66002042 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 296647733 1250 296646483 296646517
    0x7140103020c0a08042c010918050709060317190f05070b1005180c0702040c030b1804020907050a1d0604081207050105071b060b12030c0a060f0b060a0e06 68
    0x814800c94001400485100351b180000c034650b00c080308480028441080c180501c81e0800600c1a448140c00110070103a400d0340030b80703e58945459081c60701c2c6099002d000c541d543c550303051042c4032120050541041d21111042d03c1d0002e40d100101d040040f18003401c00300b0070415024002035104404403070fa10781d00700c0c115035001d0a140c0c6503101000880d1248501c0f82d040f4400c1d418101120112043c41410085030712818550fa640a04c400b900c6a04e118508141d03a40e404001c0c0b40d03442c66403034400340300c00b580140141d00e068810700405801c007624a0707003444828000780828541c410b000c0e940e181d03402000c603480c9451000226026024580100f8907071700402c50b041d202820800c010f446003501450080c0301c0341e01c8200703043c0c91840c00704200b2000b1100c00290b203000708031903400440c6405000b818159040da8446403081c00d50b0030a50041d080e03904030760101d03400e0100c207010382010f081503101c041124020010004215115802c0b1130028400c401d0b610b284c2a5032540c00b5100341d8449225416 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 296648983 1250 296647733 296647753
    0xc0503190926070b160804080c010f300e06090f0c06031005010804110306010b0a020c040e0d18051e040c0f090506070204020c0d08160c02010207140103020c 69
    0x5450201c0502403440400c80b40c0100781c00311420054600e19030301140001d410658141008415154000d103445409401501000c400168111008200922200d0058075102d5080d100040482d0307181d540d100104680181b0100005c02d8122070815001054660f04802095140320034001e03010b1203561a40b68002d000c20401307135a40100301d00c03001131903080584050142290403c46035020a980c2400080c0e145682403100b0750080800c00c0d00240290108010324440f840020302e00f060036040611411004921008000d40420002e20b521030111002d12a940103910015596645001c00c0d07010401c1c4000750280c0218a07145c00009410b000d061a283c1103020054541c038003107620f03021405649070900c02d4000340e21400c509501c035641655800c6c000c0c0d21b440c080044a401010041e03900513820405111148410002e1001c04101d07610b51000c585402072200c1c01c1c0c11050b05260050010003030900380142c0e804034042041d540b800c46025079078120303000101e00038012010306400d10310a0b00c2d004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 296650233 1250 296648983 296648987
    0xc010b04020a0c0510020a090e06030c0d12090902161205160b071101051603020c030412060e07050105041a0310082b030b0105070b04030c02180402030c06070807030c050319 76
    0x161943c03801007013120082c400391050b0604070310441c03140c0c0340019100e250038420103021101d8640c004800504843c50720400c4000646000d100315001c841d0740100240c040c000c0d80d0440c000b04001c00b0030340d1045090101c1c01050245134451404020002d0648044050f4410f000301d05440083c0c1101600d021072059a1070038407011181541e20700080341c2424080001903005004d043c1c0703d030310340c040203215402040d5401d9020390044166401d0600040c40042110759110441400b6903001e240041510312188410390f007854035940029041007030401080c071107000195070303803d00224400c910681d00d40c0c2c5e070790400300741200d10340141043e0f000c0c60701281540303d03041440d5000001d61a128440500050700d0030350854500b83c030340034007060003400040c0c0824002c0d00110740c807034040e0411210310100e550008541c01070054490024091041c00d200a50904203c500c40803d01a50701c10f00d40940e41e115205140180e00d0020f0410112412480800c4010301c00c0d103910340c03030303200164070503080a00300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 296651483 1250 296650233 296650247
    0x40903090e0c07060b0d052104080d0201090c0e2806050402030106030f05070e1302070c05191706070504030f0201030f1a041503020a0e090c0a0308030708060a030b0c0c010b04020a 79
    0x400d85585017401d42d800414038010200e603013090351000c0148000c9624080305524006100c2010320032180c14000000d0061003805138103001c140650001614801034a0503c95020713140c1c00058401c0c00317030020003001907a18000754485c4000410742919451110700e840003c0c01c0503401480d0824004000041d1883c0c240c1c102d0b20360301078044010300050303456150031100b040c1808111a401300680e11003110101d03580e070003018064000da041030b04032622907002c41c01242485004002c816018070003000400404201782d01b1408500010341103074140100c00501d5030086000242602908032000340440e80294844a024050150148592003074525145041040c0c2414580102d0804940e1071258444606407000c1d241d00401040300316003002c54180864800a00403c940d02c590801c01c1d00981e1098260f50007540306941c01640c078a00050700520003c40684464080d1032403150a00004000f0b680ca258044044010161603210003c41240907003051002e468000f480060f0340d125007540500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 296652733 1250 296651483 296651497
    0x90a0906050f040b01051803100903020d021605060405011b020301060b030a0e150a33090b06070c090e0a17040e0105060c060a092f13020a080105040903090e0c 70
    0x1c0c89000c0b104958288001d5031160031910b0300244041100d08010610b01c4401400c41c0300240c11212234400482c808801c1324806801500903030f0000029102c1d440c0d04000200600c815448417082c0d052500c40481d05038007a50092606000850310516039940d2841202e501c1a03400400074803540782d442c03800454591003501c0c661034060070720111891491000451803e00c2c1d911440300c255643c1d6100499000b025000e000341d5003207101d104200c104282c0c0c0e4480840054200c010324450500d031110a07012a40150142401400240321100c0410796000d00f40048480704100400c01811441482c1d0421242c4c4c0c0c001420b840038014581442c030514400780c01640c2038441282c000340d0b2540c082040500842656500e05d03403019000400010254200b040e4492007030b940180013030204410300d50859183e041f0002d41e00c0f0f9400c007040300d0f40307001e822101c6419108139085150041c214401042c40c0014091140141d840304166002c161040c18880c00520b8004944801418400d14006150740005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 296653983 1250 296652733 296652739
    0xf0a090f0609030b04141c02150f0402060a0810050604060c1b03080d230a021809010803071e020a03050303071413052404082404050c06030c090a090605 67
    0xc000400c4180c001c1c003840040e26080000300c0b03a160340d241c3d03610400403040d8020902e6401182c0700303403c0600c070401c00e0040509058000e400c20140303001d1795902c01d8a0040c0310307070301e29495003052001681790071007107810741c00c02032403c8010790352541c0c4e004804640a510580d007041000400244166100d244c0c450414400c80681c4441018141204410380c590701014048410030841d2080e55a050350210b411210000c140a21825540030001d40e5400221240107407640c000548244082c8220040a00c00f9000c541c41006075041100a5550303001e8401c0080c81c0303021326030300900817504021b010b81c01c5650007009840000d1b22031504070740b2600203890400101e40c0c8071091a11449007071069545c1e5030b064070107c2e01054038081c20032038a148240e9100901e09443e00101d0b001101c144001d0000d82454402406d20004404402c3c90700400e908840b86004511000d000014402140385d20001e081256440c2d140d40350344401e410940f1130358401d00e41c03011b6404c000190801d969004402102c80031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 296655233 1250 296653983 296654009
    0x90c0702040f02040f06051309050711010b0d12030c03060b070305040e0a110703051c060321030b03150408120405010507030606020a0c03060c05070b01090e0618070b030a020f0a09 79
    0x1018900d400da020b81e00480c04001100f001c28045144a0000f601d5031032401c08c5a600c655540d65a1801240c0060300c0c4100055000302c8140c081107001d00404840140580306010400155291141e0302250348990004040c4c954540403c25486904420090550483d105039034004528020303042d0760280c860408a50140b0002036001143c0784070f10754030803081022041c540b24844e98100c52650102e0410840c454444500e8105444203100348005948a281850f92090001c44804420380c0740700c400000700360070001883c0d41610049a004100d081031182c4003040e40716468602094020207180d42d404183e00c0b401c000500c401500701c1802100d013900c0411000e521801c0887e1540c014107400703000c01c81d4102c0108002691544294210300d001d01d032090401640b81d481c406100c40270313030085880705c1e100d0b20785a0350790806100c03154004441d0303920442540f4801507000d031205d40760300c40c15a80f10400700000d81c120030a90103c0e52105000f030100c690b2481c8000c0c01a01c1803425010707413401c850348 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 296656483 1250 296655233 296655251
    0x30a0e07050307030c050904170307020c0310060f03080307110a0302030d0c1719110406020609010b010314040b04021306030308090709061409130803070c1b260c090c070204 76
    0x4075103e415650020310400e42c0c507040a0902c52a00806807044613061f6150882e0041c19140354055401006507a02922290443c1410949405036007098510000c0c6030200030060903202c2d03401282101d40c8040010b4482c1c1d280036003a610200101e205103510b0062280c00010554040001c004840c4d10150410285203804411102d404130b4402c81d013002d070050000b1880113080032400100b89814608003055410f551600f41000d60032540c0301c200542d0010007481000c602c01e005101c2c00f65130030310701003101c1c501c00c0e80d1049003100080c0002c2c00540b2000c010a0a41d21410990b1441c501c0040f003d00c0403507500d01d002003c0c2d0b48101c448091500600320b01052100440c042c072011a20a0b004d000340c0d03290741c5030400504000c0507001d105010501c4040b1400207480c80c0c0607612a80300d5448a00100740e850610240ca81041d5510300a000c5094030140025401100303915840d01c805800641040d0403503000f140b0307141c0c3d2003c071241d01c000801e0401520036480002099014820782d000d11980795 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 296657733 1250 296656483 296656489
    0x180b030307081209070b090d061d0a0308010503160522061409130210030b0307050d0b0702060703090b0705030402010c020d0b06040b0d0507050f030a12090302040e0d32030a0e0705 79
    0x8001e006d2041441d10800c8003103501d00d002c184a040c0c090107a14006424010900c6a000c811000380c0c4559068022254550516410171405401050140c014201c06200c489840b0300d070303070b102d402207a01c00c0c04442032600d49000700781140200b40c3d0140724100606a102c83c03542005c0c0403118a00c034400c070700800c00502c1032100000210032255002d0200c19507070620500580c041d1220031244c070f815125684002034a45c0c2c1d00d4503018005170044400d0340040c24643d40090405400902240515080214040018a410f014035600000034030340303180c40791507034401200c0c04484c0c1c05010754485008a11017041c407151288082c000c0604031010811f411024090062a080a00c005001908120f10410460038287c0345014a61030003001d84182000a0f580c20300000b49081132000041c1c0c1810b81842142014422301c40324003030b8200104000c40d80c0c20b130010a0b04244500c4c038050001e4a0405c1284400740f000d05150307070380d00707141d1264807440d0100e051002054aa548412035206049001890b41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 296658983 1250 296657733 296657743
    0x7032c0a150c0605151c03080709030312020a030b041407030f060509061314041103070b03160e0a0807080102090a050a0614090a03020a061101060b090a180b030307081209 75
    0x10340ca81c4401401203a0750f01d4400c01848001c16070415800403400c01c1040b980d4405c060000c9140c2c2036043c0d8071510032428003c102c0500100140e00f400009131040c004a03800281c0c1d0700c4e465000c400007507919400b0070b81c00c50103880d151005503042401c2c11101c103013800c003d508948c0b203130f9450b076810884008003011182c140c40682c0704590b0400364050100310f050500b00c444203420b000700301010a524104108001505070121020f0b81d01514621902e86c0a213070078803481000780210100d007401c0d41042c452801c0d410040031700318414802c0c0c40d80342d01d50584981c5680760042144030141d03003559640741c0c5103902070b600c4007940038450704a1402c0030846141000c0c516065484564424820784c0c1c000290615550105c01e0487e4054100200003005039626070000d009003000341c1c0d4100c20402600103503820340b2000d822000d86080d0a0024540513168601e414045a0311012641d0b0300300415100d007402070110080d805d0301400001010010320a03100001c0203c031200d865201a159a03500b040f913150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 296660233 1250 296658983 296659019
    0x451002041406160b04050d0905010804020f0108090a1407180e0307021003090f080a0807090302010f050a1707080405070902160b0c090d050c010e09010b030106030207032c0a 76
    0x190251401120240c24540b01030485500c0d000403404049090f6240c64204180481301256035501c40c0c426500c44035800041100100400e00384483d1500301750780020000c0010700b03070150400c0845000502c440c03400f0054007000582054004210500c041c000f81e03100c0090f8058a0030803038502190b1030903101103100d80b404851391900a10300300301c410790811841e03242d004031403010592210600e07000704407104002011988140d00d05a0b072142c203d0030141004100a008a042c0b1005070020400760f600800143c0d407035440c0d85000e617903070011200705682c9585200d040d10103540c0c3e044200007001f0b820107010f9000e81c2c080c01c219800f00b6600c50202c400d0f1b128400444c031003c40c45c1d511080010305a01030281d0420050600c803418001d030301020611600c421203007038945900640001226581040407066000010b03070f45e039850b540c10284500290710061140004140e400115141410b1060b0001101c102c0305034041c403c003030030b04031600d500c004410921034481c501c4500300007884103040c0c4e80a070174 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 296661483 1250 296660233 296660249
    0x90f11041d0601030b09070f061706010309150b030111030f011d010819020d20120309010c020f041803090602010c0302030f1506040f090501030605060d030845100204 73
    0x540e0940c5d42d40002e98002814180c0c940c03148441c042050301b03a0392011406080e40d44d0f907a545002c5480e0540503e01c501510b42414545080c00f1030003c2401240f0320b00d4000c1c0c090300017003450000d0b40701190040076100b4661035640004000c0c4807139020702a64003412034504991030700000810740c1c0c1c000c80004003031040c07000c82d40c40384d128545e03d00c074918480550980010406980e2000603105d220b542040a4448005d98a24005452103032500b04080c0611049801c000e500342944400003a02c82c440040001e071040c030701c1149501440c1d44940144107226802811100c540c4400e14028003092624003902d8090f500f00203060800c244248241ca01c074a40f03441c40000141c640001ca4900c55103070300260b40c0c01280812011421b4102a00105c0c0100040c3c10700040c55851814180100d8401828007841000c00501820201f035001901d160040380074466041040322070743c5000131451700c10511b41c800700140200414122004c6402211810103d01914400f03101443d0f004c080348618003400783c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 296662733 1250 296661483 296661493
    0x60f1403030318030904050408030a0c020c10051b0109120e010314010b07060e01020c28030215090304030f120e040501030b28051006090f1a0d090f11041d 68
    0x40c0e010f916028000740e141c801000e42e454041e500703002c1410b489084400342c0d22404004107000d144481445a071070b4140c01c61000c0d0001060300360001d0080e100745500c070710030080041058100c00340c0c1d40205443c2e80280300000c0003007824030310780010840800c504ca100400e4200903410080e502900500302e6650310300658000681c2403822403402c1c2d800407170040e0303161a81d41d0f4081c0302581092005210009250005000c40100100009948040801800511407a60303000c2400250009084880921101101180d650320452610305d035004503400035001d6440e6103081000c1c40b004001e100c0c64500d4650300c480340c09008000344000c0e41c07400c1c440182043c9071803000601500861212880040003090048060700b812400b040a440003030341c1780c600c003d84211007000381a401ca90404000c7c5a44203500c00ca80d0b1410b201c00820f102c44040701050038200007014030030040540d2000850303035030103c04103000ca13246042511852110320803240c0141d15040e021200ca40141800a5141c41c0310b100902c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 296663983 1250 296662733 296662741
    0x7091505180708180606040f090b011403160e0a020a11012301150e0103050c0d11032a030a09030c0b0f060312070209160e100305160507260904090501060f14030303 72
    0x801081c40e0500d10702c0c0c02742e64103241c40001e03d10503402030080c100300701c3c21145021508c00705030528152851000104c0b05080c020007440c10202c0003075510071080781e00184c440c4c505140940340e0003146107060a9a500c3d25a1403c103800c5040c0c6040c064894801c03480482d60b0300d4021080400f4174550742000880c0250003d0b0b50258400d4105c40c0c0d01c00c1080d0302081c100010440070b4015a040100c0d404601203000c400c00150040b4002030141c15280c110b04881c0d910b103e0241c4190700c0c400540040f406030340350201381c003d0602841c00150115404804072440c2d00d05880000511003041c0c400610034003400c4042464144a0419a60801c0e0000c2c00e40c1500c2d10380c0740320309004c08502c01038041800354025560002d9501d6034410340000090352008140e030300e000c0605402c405141c42d15075060040c1800760001090014100f040401408480700219250134403641d20300d406111715031030b4800e0038501660100481074101c2421251a40e80404040c2c0d240c51030a20301d17125a40307850350958801c2c0009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 296665233 1250 296663983 296663989
    0x6080d1407110a0f14040e0d0c0311150109020705010c03020921120a0c031106070e09040501110301180e0a080304170405061201031b060207091505180708180606 71
    0x307910b5260000341400b030a250390b004142c898010950140380e014a1031540310b4401e0a060080c200390707070001703005403081d2203410340080c0c0001104400581002075056002d001e2001c02c0115110640303541d078220590f984d4411406020354020403040b0360650a007a42d10040034068020b840081d00300600320100540144030401244200c100b10001c24400d840c50700c0600180da1008180e0305807140d541e070a03821480d0030041d2119100746940c003002c1d40132404004156910010301041118200c0324610740e505d85003011400351000c4804041070f20000000007909000d89808050f0346040355400740482c2e02000380707054680c40218005401400308000040000e0707140c5000f0840c0340003038000641800d4035070700415400d030800500a04c041c21188018028490030207403a103084146841c10301c007854101031000351220494403c01c00081d8650308030045907100b0102000c00f41c00301501d43c0010150324a4000300702041501c1420100781c1441c082051028000c1640f0f40e0309040e44000c1c411500c0b40824 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 296666483 1250 296665233 296665253
    0x105040b0105130806040c150e0103020a0c060c02030306030d031a04021b10090606080624010c020303030a05070f0503090c091512010b010306080307150e0a1506080d1407 75
    0xd180e0410204210710440200c45800c00405801030500901036131410303140040544100340c10107140ca09606400340400c2d640208981a010f03028640942c540307040801c140c4400580e030a005050508000668210550020185105800450445414011000050b0221740c082796100c40202072040040c409400c06130000c0010040d0503c2040d04240030365402401c1051035030318100440c1e200c0d505042841880d0103481c0147c00c4281c050081c0e0300340040804901c002e0029444141201551079400c1d6a00400004030080d0b00035003669503d1030000007050080504a43c8031001c14404c80e083c2281c0740c4101c090f04d12170f00e1143c3c010039007898008108002c0c100001c003071441c607042e407081c840c980f525400025160940018000b141c1c5000040024040e982c86030440e1960b90b0050190b02c000c5002620180c0d80449045d5001400d40c8280031f0042c20070500d6030b0003810703000704150141124503072540f1030f0084610710f034141c0340f4034869404102c1c1c092807402c2d010591000140400d00c040f403840c0311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 296667733 1250 296666483 296666501
    0x10302060f040f0b090310060e0708150d140d020a050312270d0801080d0c06090809060708041409060105030a0f0e070b0c06010902070206030c1806190e03010e06010504 74
    0x41802e2590b5903251480102c900d4009801858000c20182200d0800304008a600c807100e00040c0866420008211100b4100034086820040d85c01c000c92250080d180300e9007403010f40603180200c090324500b844c0010000c1440101ca0b0352017100c55030200a0700c0414202400f50748800614503041c2c1d412010780c100c00c0054199412141790880195000c4604160240314a44680c042d024400d0002400b42c14000160b00190301031f0861403001580c5588100c0f4250b1041d80400002086a440d061841607802101442a0006000100541480f160601402c02c07281c030b10340d0f0051f45155480c240011014140d03500ca020500c1400462b581d0810358110302c0c0c01c0f00059800150108640d207a1a10341691a03101034036420000481004450b41800824003400c000d40055103800b65a030b020405520005101543e0300101140e5500c04044003d4880a5003a00a1440361160303280da021240b01d0400102e1200414550080d104080c1018010400460001c0d0050842603281000b03010260610761 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 296668983 1250 296667733 296667757
    0x50a14010e011503050105090f071806150905120f0c01050c1c03050907060801030f0201030c02120d050a060510080a1d0105040c050a0f0e1f091b02010b0d0b01030206 73
    0x25a081c0c100d010921424040200440e0072003c55499410071908440c0c0181156400e0713004804142038010002490030103c40f40c9400580000840c0460803008051640241058542e444203455503503900038101c41c10381d08100e9020b4000450350700a25a2001540380612080d004400f412002e58020000740c1801e02d985c0d019a814103030500c1040e481d200014000c040400d40d50014840520380411403500a4031003070a0040032941151103035100f10032603420007030401d912200c1e0b2010f170350f20a00000c0c031f8410080d540c4a480f003404400000243c43c00b11070b07010203240340107800525440c2409040c980701c0c18a4071074031102c0d12515203190140944209c482c5c203850744000419040c000c00d1290300d00c00c5020f000319a00715401d10040110543e641e074800040044800000d1145202e415816908030316020f1811030030818600702240e0521580d840703503584a240c00307000c050b070750798a03a41c41e503482c80c45130300820a8851007000c03c030b4110407140024004103461f100610050400300300402c50b0010300303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 296670233 1250 296668983 296668991
    0x303070c0209180105091b03010605090a1d0304030609060c03062103020f0d0206040b0c0f1903181b0e010b0a05070819020d020712080a0e1f1d060403050a1401 70
    0x59441c0e40c0c2583c1058581040311f034003010044100071401d00800d02d510034120020f2041a217084006140d46a002d08441c0c0d60a42d01c105c0c0807204020140c04010b50321005003529141c41d81d03070074100003d00b030076002510218145200d00104a120707100d09005d54104110b01840148001900c2c0400e140d0114203c1c15803051400384284801c0800040b0b0003104560f009040501e82407600301103035807000d401e104503841d00313100c03100348401c41d2401d442d2400803603541d8410059400c1c0d0708030098210710101e42000d0301805032410138054400d40b400c00e5a40511001c000441c0c2e540d0300c48150341801d10911170039050600c400d401081c89070000780401c50107031044604104844080303c1c43d603401058000096881892901000c3d40c0510006005214055000311500708948034a400d900c50404c4410170004860707089450b5030f80b140c1c6c0b20a407600b60040142d52418402a010b800c03100784170030449900319400d030403428514101c01243c0a40740d006016001019240e65801c40c1b01c01200c91507081c030f540b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 296671483 1250 296670233 296670271
    0xd03050c0f07050d1b0801180c0503120a05070f0c030c08060907080c060c01060f08010615110d08250207180b06040509070c08130929060f0408060c0306120303070c0209 74
    0xd000d20420005a429046508c4400307142032903c0703800c568000e80c0079400400289a1015402058804102c03c1c0e0814994903201ca1605242c0b00541e010014101c1c8074966011040c41403140240042d60f00d1034044038041e444121074542d070f40a5a10440d8403541c000c05409286050080242c07405441010010403c141c460307082c2c0c2c0f1001d24581240304540e46d03564041000142441081007800014140702e1070030340c481c0704020745884a02c15120300340556040824001203504540d580b55a010000e15065000d600c0002921890684600041c07149103d00300501124984070b0141114030082080c4c0ca0030b40380c2404d009002c070004001c10148011858480081a4510020400865200c48200545061030000e10448a100801d200302c1c0c0513411258140c190b151060200b103080403582d1580362011080c43c03844a1140390004031031802044280311181c681c1c0c0f405903005100443e00007001e41d8092000359521b01089881400107055440d08002500f4001c000c103800c41b404642401002107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 296672733 1250 296671483 296671499
    0x15020c030303041a1e061e0d0606090c0e0109030b060a05060403030926030d0b1215010305060109051e0702011b0f110303060d060f09020d03050c0f07050d1b 69
    0x4103c070140c0718209282840030070510f041c19110f51124403580e00304101c0c20031000030143c0e0207006080500840381c0c5140740c940d034000c1d01d8061514440c014442542d200281c9030001c043c0500307200e4489464113004c1800107a13400b81d1940340c60544d0680d11660000e00c4d42d00e621344444e030043c00709038204104103804039942d120000184055030081d2a40da4000c1d01d8082d00c0200300c2002080148580010281c0641480b00842107440060b40148081003410980c1e0000d07050704810f001c490700c0b9205081e00f481020911b8001030741200e008400760b03038044e82c1c0c550741507080c0c50003155020f1441d44210858854000040d0038190442c50b50701c000652004a200c044200036100101e100120301e1002c00003440c00e611604610094906001650450070100003103000b400c02c0c00320040c051a2281801d200d1034481360300c6509001e030000e200d010700351001e040103003855110001d2072110b401841e81c030100800e000101d10089590103091880109800d4541500901c409403031403a139030740c8415002400c5a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 296673983 1250 296672733 296672737
    0xb071412040219031a0c0304110d021503150a05090903121305030703050c0d03061a0a140417060901050417091801080c01030c090305030306190b03130b01051915020c0303 75
    0x13622403c0f019045124032551031001c550002c1400c11001010020400000c2d44840000040082550360780882a2180f0000e089d038a41c0f10040f100507200072042011150817140e0206800c402a20502d40d49511b078818482ca101c0201c0b11280c4551040224202030880c1c2280351f54071030180260300e0025401d0b81da9443c1564842c0c0c0d4107400043c0c0200c2d84011151082c0181d240c03000d02d80c02c0c1003040398600708141051202c6004801068038011482c401154010b1100003402d200e02010179a0f02c0ea12030302503003002d524a8503004020710a040014119080501c04e40d4000c5130085200c011450f070040c41c6004c071754003588015400c003040e40e020810f617411300c0e0951030103001c1010241000d6021740000404a403404200c203806c0200342c440800c04076002004a9400c0305040c0d584d0f07592740e060603505007c0481e60380e1001c03692038030020400207011244179050543c01d124003506156640d940c4100990003104191008644075607280c20407150410b416210003031803c50040d07070041150540024156 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 296675233 1250 296673983 296673989
    0xc0b040809040e0c090a3306091e0506090d06090b040308091f020c010b0d060504030305010f03120f0915020f0708210d1404030c0b071412040219 64
    0xa0440403440326194500b0740030708803099959400508909802500250000d0405481649040c0c2e5650b54401481d1759102c49420426419101640821052048881c880306610034100028101003001c1004804e0a000304c4070320040403149040c01e0708000802602da48414106544511a120742c2e00c0029070398000d24000e0b0340030f607103245a6490700b420060f040d2003000340a4907481e04614003044403400c000701855070750070f07500e00c0050700c861030b4088075401404007400c2180c1c06144001420204440c82d0051707480380d03203e0f94041c045660380394110311b0380e05894080244800c540c00000040b952051604c480c0d040030310701e4441d02d2195030703135403641d48000e41051030030050b00803150900391908104000310042107114024002e00c3e408031780000300d084072420b424041c0040000c0c40a2070503259003003484500c60403021802c45007024500034080e4030490600b105c21113098000a0085402280302d54040c0003400c3c552441c000707204d607021070291801031003280d00090744070f580d21011002e44824000303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 296676483 1250 296675233 296675243
    0x9040b0a0b030a1b02071412011d011109060a050315060c0703050c06041508090a0b070801050f03010b030c130f02040b031806091c0509091f050102060f010b09010c0b04 74
    0x41c034209488076800b031300e0642e0f00a000d025907a62280c52903903800254142242e40c8044002440d8940344001340000300e520305090038030760030000d07131100170803034240c0d42004e204003038001f0841641303440d11200c1e041c0149180546d120505208203211603008070010350b4000d51440300410300c20a507070001103076038014070303c0d0a00c1e079442a501801008410000440401011074040b800e00d81b030201d421482a40d003001c404200864080891620b0310b08004182c0e880f0f40c42119000341e440c213450000c100c00404d105d40ca00c9000e4040100c141c6003018131850610000c05005003620700d0050007032020700c0b40e00419440320981d598046021292061002e03101130710807048500c5e92800c0805480440c1c8854440d01c0748550040c0061003c05000010f01c0c13448410030f14848041c2a1a90700165424016034040a4000101c40b08104449441d05002826411a5031249500c0e64880004aa40b10021554101643c800c00014040051003d001e8604103105140c803240012042d503580a4540c1d0039502258 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 296677733 1250 296676483 296676487
    0x3020607060b0303211b3c030f060a061e050a02070302040203010824010623190c15060b030c0f04120305030105030c0f060912070f08061f080307030509040b0a0b 71
    0x94603038803d01d4000c9042c61484600c50a0500030003d401c2c2d03100c40b07d0618500285201281e0000141010400d403101c10b0801445407a864102d440c20f01d240c0044031224814039040c8030204400b0f000d5500300e24200f88408400340e100070401c00a9840b9402005034070198800c1c284000010f0340c86000540c0a012020042e02d0311a8a00c50b800c9291645102452010a55070006200207a07010751081c00f4403034290f1030701c0d01076030f052007110445204014074012522400d046500381c85400070543c880c0035203d84a071032081c041010003102103421500980c42c607c8410001308520b84042030180c810b20084d0707454580340c183da4405907001002d10035400c401080002c0010005403800b44191002c000c01502e1400d280342200000800034883e00300c000d4441e01e540328681e0a00c14081054501500700c07141c0780601c81d03072100c030f040d99250400c0700c59510102c04443c00101100c042070981c4200c0704000c008604100e0a0f96003a55980c00086030305030042d60b5031540d041c0c02e95406103008010500325607466 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 296678983 1250 296677733 296677741
    0xc020106050405010b07200123031819030e12010e0a030e03030a1704050a05010c0512060d02010c030c05010b090408040e280e0307050102030a02130f03020607060b030321 75
    0x160f880581c03020404200c240007103008246501c252003600c40d401f01c004032030041d844006a60104000ca2824107240004512010312883d1000641c0100c4e06880e00b11500c4400d004040d589802c00381d5203910361260b04c90b6047c0003a0054507040791450004105d20359590207103032014211509889000032942c0a1207000003499040144865400f005901542c580400b0981c06810104cd8001e01e5590314a03090016040c03043c103002520000c4d034060020b005c1440c0303104000f8100e40100e45800d00040002010844a1800c0e003600f0000a41c180c4075404c1d5125a81c5060702c2030310340a00d003541c485d501c41c04c55100f41c0d611429804d11580c4148001900c6030b0400c24451086000200228400b03000c1a07091038070100010006030960b03014100108468074003040c5030b4194000c5400c004c000b0360010042c0088180b503a0003500c4543d401171503141c0e400d035650308951030704081b912019400507010010807001c50f013031f40c00400c0d206001800700e0b850302c2c980d4410034800100c425480c41c034000704e4030148 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 296680233 1250 296678983 296678989
    0x10e011b0909020a0f0c1103151f0f1e090509060a1406030c100302070c1d06010801120b040c0b0a120c11030d020322080307030f05070c14100c02010605 67
    0x1c80240c190860304609154941001070500c0c614140c0c0e020601080c0044001084107540c030400002002405494000480c414003c40181c4195100910704d039561501c1581015010410310880c2c008650340c00c0c4940c0303010701140320703522151310303907440f020b40c2a201041c14000350003a540250b03c04401000103103444042813007180d00c0d41c00302c0407407080414280b160b0365800040709201210215015074030201c0c0410198000c1c40307001d42c0180f05844c00d0314005640c460448940c4541e03c0340602040c41070f0749480044400403001d003d40303400d0391034000007000070038020254180d01c948108001c218550703c40b0b0301082150445140000026240c1f800b8540d007040b540540b0169512506094482d50b018200e550780320301403c020340d000d84e6801300019904812000c154174500050411112a002c1d00c0d08108485502c11034010380428204540780130151018450701344203c005a441c0351800c03059540f8600c8120030748400000740d00c00d0524030182e80100703204200c244401d68000240c40c03840c03d014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 296681483 1250 296680233 296680247
    0xf030403050a0e040605180603240a0605010f0c080f070209091f151215060315050601180308180603100602011508030406051b1207050628020a02010e011b 68
    0x2030030b400303142022000c00460b04c54111f0f104000104014001c002d0783c4480c04245802d010380703100d0045424802024091b02c200c1c0706404d000d00090f5034103008054840005460702010754664000207410082c010000c250050050219260100c100c0d6203011016000103000400640c0da9424503040a40e10201200384032032441d403926500601400300d9100d51270307002c0c012142c5102e1503141102036051034040280c1c100a4141d4080582e0b02044155120304118814a40d486008030b881850034001c50119030280c00c905403141c403407040180040741141d9a80c905a00120b1540340d0400340c000c0c6400d1f16a44010241d8896000c0800020405241040003820f4401e80a19585680c99100b0f0500c1541c5000c02181d044d82c0c11030800c6540c0390402803203002d0360072880c599045035024100c56008800840e000030101140144102e42c00e580f20400f048117462603500d20f10b1110402022405804006500a881070181900000a150754074244641c00c0da40d8999403a5030921082803228615074001b50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 296682733 1250 296681483 296681507
    0x302030105180601020d0509010306050409050304030212071404091b0e0910060e0720030d0c0f020d0c0201031802091e0f10030308060d060906060603052212050f030403050a 76
    0x5002ca00300100043d442d140c06141000070071800289242040e4000d8008a004180140040040281030304042d40c507a0010300080380708601c4108102d09441b800182001520300d003205500400f1440d5003007000800815404070341c001d040c2498491140700080e0310b41d0040c01c0d1841e040d5450720740000c800303040034084842d00000624101e428040200d50321400790703209101d03042c11401580d5960950342080c980c0420f44106100003e0380350310694290b0448090900281c4410040c2038044500341e84074110351070000005401181c1038005580300341c0040c010b05d1031403442c1d103020020316008500e030500c04542030700810b250085582002c5142c4034986900449100c409841c0e8240303851400d01505641c440501005000c40109490f80c0d03514564155aa40c000c008100518080c602038011740400e114200100b4580400a00b59040021501e44201102406500003400c80d03a030760104000d4414010080140030300c42d200c1c40060200003140200d0107501c032941c4510b0201002015012611 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 296683983 1250 296682733 296682769
    0x4020102070911030f1b03090a0309090b062704020c07080d0c020d0f020103180f020301050c130605130f0602030c010506060f03070e040b03031902071e23030d0302030105 75
    0x85588603d034581e100c00d80f50000d00386451560b40791a44510b00d20450301d1a09210b540110002c1413000130340000541454061181d203450840907600c005040c02c03103910345400340c3c00c00d2081009903005041d01c0b58040d110300ca01c95454044524810105089030815540c030f0413130b64000c02040c84509030401021281411618112803c00c030240d000c03401b9108060740c002c110280070404c49085a0182c0c05c445230480b01a8030300c41c4003030700c02c2c21300e00100302611805074041c3d480c0c003010403101813004085036110400d015000180514100b01181c15520140610341030428412004c82c0d01c100c0f160800d0300400c500d078019510f690039222542e0850303a0141c526842448100b00d2803d0002c5000c080c0d035403103411414071240000b45c6e00b020030094840c58203115414000000c0d000c0380007040e2904038180041b0740d821111696180d4035441512602a0341c20351241c050001c00300150980005018101e000011038800155207002c00700380f50810250584010940100c01032000d4140703400020398200c966 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 296685233 1250 296683983 296683991
    0x6151202010801150e060c030d02130311010309030e060c0f0304030506042001120e0109020a0f061101090b131401020c0616170f070306080712141516170708040201020709 75
    0x20200161045840d81807950040e00e012170300ca102400c7c2801926a0061215029580d41026110343e207c8000580001c96890007410480340315948a8401c610300d4580c182c80b0100d0400d60242008040d400420202504d440380f503510f20381c000801d0000e4002184a44014401d6082616204503015a1100843e07051582020004050780e8407e40742d031181c03907408030700059161a5180c120301401c1c0301080a50071901050303001842904c06901001161070582d034103054a40c0740c0c04614207031350800001410082c0e41c01d000c0f440102d03000c0d00818070f29201d2007200700e0b0744a8907078800342642c0001600340c1094004c0010000400588032848001c01041d01c0d22221010800c82000001c042c0904000c101046c007030001664240684d001e41d0242006104031010141c0d228000072852258600495503a80d10221407020030100051044400c1c109110341ca005550324107841d980e480591b0800f10421a44200015464484440c0ca600a0784a580c4500d1685132034000a0b207881c11541c070101c042d0b4a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 296686483 1250 296685233 296685269
    0x7060f0503060409080408010c0c0c05031917120c03010f0b1c0b19030f02030c1f03090f02120a02100206010b09010311280809060402090a02030406151202010801 71
    0x100c002207940c008012500010484000d09141e0200e014030b8100503007035071034120105502c1e6041048542401e1040d40c081551b00d80350001c0c152a8207012941d032403103100d2001010002801c0317100c1405240141f01044d4100b107050f0340101c1680400761600e003c131020001c0140700801c0c1c1e444459014140720f0b2480c902d40b56008a172034002601ca0481512041e58401044002e980c2d11200c1d81214000100207040e070319206e00340301c10102c40b640d0049200e8482c0881c0652a402d24040a044400c841b1030302c00c040b80e507020410b0340a04242d81c4201c1b400140302c4d01960059441d40e14103120501300d100148410a05841030160b9280b0346400c0d101903602000c0100030300c040c01411a00c03021001e28012426030140c84d80d03003006005220300403c840403010700c00350f401051407030400013440072030340e900b81151240044280c484600ba10043d401048000016041070000c1d00110b401078401e510000712080b14800e15080c8510319080890078080c568034034000d540e0f10204480c007403c1000955050000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 296687733 1250 296686483 296686487
    0x30a1404150e0109120203040609050d0201021c02011116060f09080a0318020604150210020702090103030e0612090f0c0301021204020108040c080303250203120a050a0908070f0507060f 81
    0x110314507000180c1a110781002010403000e401c018011940b18400e258894131030040a9141d41080c05000b00080714024005802d2921600c850140c1390103030060711550f0340304950141172042d66609401075648031203000c0f07100d1200e07000508482a0040414480314080d280c16015241c3c031104136401241401000d1000c034042004940c040b032840e0034005080c1d502122116542c0e500083c01079030083d0081400607900744624400304101049031709407140c00540d02f0000d422401640e002031740051032100180006801118180a8000000e24650500c0d07100c007800c0300210030848003880203410441100344100c00400c003014012030201c00035400c00c000302c09000001c00c0020400303410000b58501041c280f0400040e40400f0740801382c2601e540b440c01e00205242087c0342180303003120002c41038000001c00e2000c13080d0350007001648420201a182c1041c074101030030300a040314402c2907a5030031105c002811000280221072140c8400d524005a5043c040d0a0101d50752160090111086521140075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 296688983 1250 296687733 296687753
    0x1e0b09043f0e1807200703060f14070c21050d0207050a0210210c0e03071d0f01060203191209060f0e070e0103030c0f0b0903070b0c09030c0d06140705030a1404 70
    0x80440d541c0d01040c120700030075003440e081e6142d1018165a00c5c22042c18540e80b0690404601c072440d800f01d0b80859140c2c04c2f02114030b9081440e001d401c42503060078041c488403041d405006489100c0c600b00342850f4800c0303a2003040ba88002c4044805521a40c40c220442c203108414406009490412040d824500c511f0902c0c89600340f142130f0310007a501c031054000203000e007100c42c21030040030b021103000c903851344403110f078011410030784c00155a011400a00f010150200c078a068070360b994090360030406030000020038807004200550510002040b00c500c040e810340b01c0c7c5440c15003e12404200d803298030303540d4000c40c0e5001e5002c440340e400c14101844280031200e24581142d5161424a90214003400c22008007a1001d4009100045003c18454006000000781028a00410b001500d98030350f101a01c030540315030396030036030103400601c100d1205280c0090b68280a034010000410054038584000e15200300c00c44d261800b20314040203010b204074040c454280407051280010155061688030700b0204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 296690233 1250 296688983 296689007
    0x306060d0b030703080c0a05060609160e030a06111305030309062b0504030804020f0102070f05060c0a080f0a090807030209040b06060d1e0b09043f0e1807 68
    0x603115580c1c0030007910200700b5040215003154119440740683c05d255921500f403810203907a92706c20300d40421600e00d8121180e9000f140340044080182c88400410f4070310f40340c0c4440c0240e06018001071100401c609003e000003811014560640c0c81182c5202071540707180a80046000740e205005952a0791100d02c2207039a0107460160507900390381102004840c41c0054034000306c17400d0a0106020030190007103452801a442140d10840c0030340d9003801240d03601c00b948120340c174040400340d080007541044070090000d1003e1009940d02c800064641d001c03282d01c503a500c0352a51000003079104001d540403140c503026141000c05442c0044c40c6800090085101600140008203030901088041e6511300450305e072100d40b1b82042c04010040d0500d58180c219042900e8012810107409510031716200401310712a9600010002050404501e082c041c03991090292100000300030340c40c5401d2010345820309880c13140c0e40d600300610700c030b80b81400485a40b0420301c4030280100c3c070030300040d2508880d407540c03d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 296691483 1250 296690233 296690257
    0x40b031c02240c1315080a0c03140121080c060f06060a02030307120f05090106030303060b07031209020f0306090d260601030b040209060f030405191203052a07060c0203030606 77
    0x1d9000395680c110b00c1c4e00c000d9110b20442c948040150107a542c0002d1142d2203541c24980400c802e05582e901a0309036103c0c50244140008000014000107102d140c41e0607603000300a070042d007440045c0c0e030b83c503100340e001d20007031091a4400010881d03000707120740b01607502c0081a01d40e0741c1070982c0020081d64a00002c1e2a030004c1c07050f203e2049150303048581c070100701c801075904280f1072420001070759402407081c0d020a5000130308020f004114402010121014154540d8650203500d0086410308001c01d1208000c07a40400080d4487c0c469a4003048158007a5030705d4006850500c0203c0b8002d080c80c50284e28458801490b41904c052040b96000e480741c0c00030307080c2800304100d112000050002d10488544581c4034502184400c80d1480c0070002c1c602c00c51146040314000780c10320032701c0c21240c006008024596a29072390304064540c880c0d04040c1d00300c00a1070710256080c0d01d51300400d419458907041035107901c5012035401309011840c00382603403540c1079001540c81c500b01903010880ca84501044400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 296692733 1250 296691483 296691487
    0xb04081005010b0a02031801120504150b010e0d11040204030c0f09050601020a020f06090d0503030a0209030c0316030813080d080f0708070e0d03050c06011415180906040b031c02240c 80
    0x21230340600080886410038030420080e620b02480d2080c40800660b1610704040e2070b1090460b0254001c075140034612038020018141156555a4403800718104610140c000da001d000000001c0c84414455010300f00361701d99074012030f052801040850304c0c000e110604552200c40e0500250321103030341c814140300060381c44640d1101c05002140d801481d444008100f4400082003150507045a805001003802c110196410324552408140e95014150b03050785540760341280400004680701e000304004e503891b01e481d01200d9a190403081c1000d413801d0704040459540010089401140c21001d5400401e0b820682c0e61420b06c104028040b50b401110140515140c4078107174140744c014401c0c0c4562000303103007c4481641c4c444e885120203510344030b00075020b00c0c020010484081c2152083c0c800d4023100a02103039800c0403000c2048008000944842d800503603940c1404025141408211200541c4056080014060740700007442d20454400740104150503024079902c4c201c0c000c03200c6400c8840140165 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 296693983 1250 296692733 296692777
    0xa141302040b09150102120c1b1503010e07120c0c0206030a0b0d0f061119030f111b0d020d0c0b04020102121204030e040203010b0910090b04081005010b0a0203 70
    0x24002c00a10800390380c0b0a540d00c00304020050344101c141104207007a800d071500001140300300700503402030f9041c00c810380d0000f2a40200c841f105d81031300e03840c100008082192080c11008484042d9100380c009031922945007080211198001030000404c683c034140810054202080040c503220551000034821900000421500400c5400074082d0b81401480c105444502d40b401c2d1402c50410601103601e0b81c01d00046a54020b01002512111841c444441800405d000d008400400134000c01041440c1c0d940e40403481407000402810040d1802104c2401d80c0310207607001842c3c1206148000119400000c0c1960001c0d0b101c05d10f0808a40e010041d494181c03103034030060f820500016400c1c0202c88001c501c030f03035164031800d80c44d901a40c026100c81d07140c201148288404d07807000b40a8600000e804010980355400c20794089080b5a40354030380319142c0e680b90040402c90b83c1c0705500c0b82e40300350712018070080d5040080c45103600400c0c42d0b03629940fa2650384c0c1e9001e510b90194a0542800da081d20f1030346 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 296695233 1250 296693983 296693989
    0x30305120709061704260c010e060103050613060f0203130203010608120409050a02040e0f0415090308180c040204080313080d090510031e02190c0803160c021206040b0a141302 77
    0x5009200381c1d441002e040586d040042000c150040382c6884059800c14035105801280414214162500311340648150760303075904c40b580e40c4202c12200300e50559851040e01d080c03082c544040c43c0280d51405460302040c00500406080d606590400801d541046070703440d099136001411501201c43e10080482c890f1f5440300c41c94001d000317035405842c90b17911200c1084413841d0348206170b5104601c61303a814211101028030302805c07030341c41e0040103001c90410001318032020480d030362415482c1c8480c0c0450380303000c071964003043c20b0b40c1090b400450035a1002c156040740c5880c654071340d0040c042c441d00401c0441d4400100510300b032050b1003a2805080e0a03103100259506c250880c2030581084000c03d0b11084240505000075440141140e170340c0d4110115109149102d0340e4090742c0c185e04182e80078110744500d41000948020001050240701108110b080140c650304d80089403810b04d140940014a4907081c031603840b5500900003c1c0305890f24450601629100d240a5080300060b02c0304103070f40c040c038404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 296696483 1250 296695233 296695253
    0x109020d030302280203040303051c09030806040f1b0309050a060c08152d01020f0f0a030207050306070903060906110c0f102307050f04030305120709061704 69
    0x1019412040441000040c1905600142900d104618100312515941140f1402960b0042e1341c0c0c0c80140c10030001000441d1003400604601c61004011151490806010301c1c2242c0607070341c0886c0815010f6080014919240c4202503142c502c03801c081c480b00c2c51444a24009a219404407000e040d91040d801060000800c0070343c6400341d0150b000c109034031140102404100d021509000505003041c100c10980c1041120b4480034404904000380300020200303d00380640302c0e00d16250440c403610900d03080024040143c5030305924014050306585400341002800d1075410340005010341d00440c00e200007954800750324403c07203400a10020302032509141640c054450b00840031641000481e1005c2d0541e800b1595026609000e01290034602405015400b5560391070766a140c0100072032420841002c10780c04546e40101d091400514020100004500642042e04290009400031130a001001c00c0f200800c1d0300005c00342070000b00c075898075000500d01c0c1081444c450003180c840e008039080002d1408 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 296697733 1250 296696483 296696501
    0x1f030213110c03090f0109050306040201031d07091b0e03061305070509070210050f19020306030111030c1e0f1c0f020a05091504050f060f070501020307081905010e160201 75
    0x10405070b03151021030126030360313404c280061845142d090407480c41941c06282c0300b0040391000f4001c1e150300e40e203070380055000340800c3d1000841889004500c1008803c144802030117800c000b88005055554a0198086141002c0b420024450b55000440d21550002401ca500c240d00321081c15046c85a880c0080c2484010f51040d900880d0384800e0084060300070810440711025200c0402c05907903014120740b00c105050398400307901c0d0150705061070030340b00075002540e0025002d0001b0541a03200e282000283d8012903011200e00740c04070b010484400c40e4400c1b041030400f031000d502c0c10065001c6070030300f443c410020940300340d5603075452650840080c1e80001c824a248000300b15114040018080c0441d441020054851044001c2c0c11009020800030345050340c00140c115070111800307400f40400383d400303800311211441090001500040c1c00b40002c1d4842c0220b651101a60b04040c1e000440d94a504414111107a04180040c03001c03040c40d6080070781c002c0c0080501c42501c1c2000b1801c6c0d0062070100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 296698983 1250 296697733 296697761
    0x50d1704050d0c08010e060606040513090812060a09231e040b0106230405090705070c030f1a0402010c0605061507260a0c080706060503160e1f030213 66
    0x4140e65050140303250fa90012554114020b1100804c50040e80d40c86102c1107031202ea001c401030000780154100240d80c9000031050010000b0b40b110325448050150304007040910601920204100703160030a19981c030300130182103a09004400304117030082000180c074040c0300000c48814000644d1749034088000340c58142190b0b0510a50f081606219550080900826000ca10481180701c2d8040c10f1003450340380d1070b0a40c2a21070806061108101c21040b02415034010401d0074050703200070910b0045410300462281d108001c120741a4a0425030400701403030385000c030410000410001d42d8100484100242e4060f60001c2d0f190b03140800144070302c18100c0c01c21801c03440840d442041041011203480c46145c810548407007038928440099451180000c1b81001540f03048100d800114100c010305007007881104007041c13854881010928001da40303004a00703070214401040000744400100c0741e40004000351700403c0c120030002e00f40540300e140d110080c09a500f54504000510040d4000d01e6204030364 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 296700233 1250 296698983 296698999
    0x515120702060a0605150405091b161509080d0b03030d0c02030408061305100b031002070b150f0a0314030f03100e0106090e0f04030c1704031506050d170405 69
    0x1684000d6454004481c0f1000c0c032440c1c0503001c1020b14125640c442441c4013a4255407401c0e0030074080c00501c08018124415044016184840a42d426000b41801409011910044926606103800d410221110304200207184c0b4003402d011803c10001c4944051402a01058500544002c2444c600c070b0201440011440c02c900d440b12194003000500454007800304558064441520f010a401103685005059900038400f0b01281035164000c9008107500600362030461000b40c1142c0e040c0e0b804a4422203000400c00100030711a04800905520103206940100501030300350041084542640000380411001000080c80e00300100b080703500d540c00003901c4e0380d102e0400d01300750a800c80300b5004411620312014004540c0c144900000d40450380608540d09280e180d455160102c804041e00690400c014407a01c203004c40c80c43d000c0341ca680840002040c0e50b4a20314208221019801c2d1103142429007020010401039580b580c11025807a01300303110b000c81401162004029205a6200540001c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 296701483 1250 296700233 296700241
    0x190f0e0310090605010503010203060603041e1e060e0c030c010e1c05010207050708030c03040311011b1506060c11060f0c060709030204050919030f03020c0609010608070608070207051512 82
    0xd2038200b8400184544418451640c070b41007018282d0004861081e003068003800041c011441000d1090f0300d220303202c1d100106800040c1c84080000b000b461003044030041034002c1c003080114900c20184290300c080090010740e0781d601c0020f0340b501e03c00d401003810800034041c0850583c0c0e580780402e50b21b07121924484007455081c40e01e603010703400c52001a1080d00520300000769404000c07085400601e941000745240a0440e43e60500341c4610304041410030100e440ea4100140f0001c0d8140380183c0075070030302056214564060380c140c610076000041007040c1d44a07204001840c90b2903280c407940080f41d01d00d44505220b1801415400344140c040058405d54050001840c1c000300e10500f92802603d080c409552003075802c03a07680c1c4dc130009410001c54900e0301400400d1143d40c03c5560302502e4030b800352901c00d6003040c0340c2c507010b001c0c0d48100c41655201030400081c1803c100100c014442401d001c4420329201a019403194003520a580c003401441281000780b41441c000c8071424900102e801c105814 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 296702733 1250 296701483 296701513
    0x3070f020f150a180c09050f01030f02060310181d0f0303010e06032812030605130903053109051603050c16350703030b030109061407090b190f0e03 65
    0x4017901ca141001c9181c440415074078030301c1241c424103880e00915441101400fa900b80070b81c65200070300c0000340b42c42c040e80100b4140b5054010b9850f4410341c40006c5203900b0b04108112041d01d04220000c0e99a00051040e00d2141000c400e6904440b000c01e05c49101e030b945c040100b401d000180e1030910501009980d0302c655042c40441840400740515888061044081c3c0e054044500034003842d46e00035840f880480007402948c000702e060700d2103403605604249120721010942d03070f00101034207024000f400030a6030f40004443d007840282103071041403003079017000c803034456882c08a13846840030580c6a2001a07050044207085540150400b02104424900f80c140300391881c1c0c140d8405188fc00440c8060b807200e202460440300b40d08008100c0e5480c08501d0369055008094400242d03800d552079142d09808101c25100b2802011180411903046142110340244085d0003504446110003040c84840340c0309000205500010144c3d062007080c2c3c6030300003015145405070000c0384e40c1c035108007050196200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 296703983 1250 296702733 296702753
    0xd0b0915100e0709050112050603210a020c09100302150c07150806032118040f0203040209100312051c060609081e0309041509050a0203070f020f150a18 67
    0xc500450b60003031900d8140007100c2400b0640f05440c0080d00f074401040002c00076902c0940c100500804940030015107400d0310b00030141e00181d05642000100301c020180344c0500c240f112844040b22811401d00d014a114081c07085140006401040034204850843d01304071b0407240b01c10348000485203055603030141130b080740f881458103400084048010400324280002c0d40713a94041140d014103038941c00c1d000e5400b2070790410b03000050343d10644d00080d0f01d95203442c0b00b0710650f5140080d015039a4a000e0040c40f104c01405040c0d174071480350340707202000031440010046132009c0440c40d02a17034406070000300c90b803100c00a002c44040c051070000009119030308500c200e021038200505640c20003e00c5107a90486400c64480351915070420050b500c40c500e0140d12001302a211039115010b51610f5010760821680200d80c06281c066000040c030040680206139103c1800c80740c4010710501840c039586a45903054080208070500141000c50700142494200030310099034100d0714287e082250a00251107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 296705233 1250 296703983 296703989
    0xe21031c2306150d0204050411041e12110609100e1201110d020310030f030f140c0a14030405181e0705070f08070b0406050a1a0d0b091510 61
    0x80c00700a15459801e201140809100d100000c100c180048054002e00000d5807040c085505220750130000407459aa0b82c1c8542d528451004051300c1e140c80c1403442076406100b01e0441d40e507401003000700c00c01c20300c0c4c803c0c40740050f090760060346a103220414002060041c01200c5034254007000019201121b26484841e00300140400c8030141c070340500b031300c140782c3c220f070000542d01e08207020070800c04000010f540c00454009040b15151032140790381c1c1d10b4442182070b90003002c80014100a0169004650210725400003240214820b880c0442c1c80070304541c4e45040440c02000d40110102e8105800c2050041c1c400507c80a006a41560322858462149010845039005003540340780d070040f1010001d4070507034405c0c0d1035915030610300a900c0e180d448000d811420220359951003045508000f40550000b64010303440f0300c4011525040a20480342a5018601007816000f06005408415a94034071107a14090708030340b11802c00c0e1600c401a40c00c0080443c0a041200403000c140200212408010011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 296706483 1250 296705233 296705261
    0x705010b131e18060c02030d0b040c09050108060d0203010f020901020f03090a1206111b010b0904110d06110703020607091202010512070e0a0f060905010e21031c 71
    0x195101c040380100840d02450710320a41a94031189622030206158060300e000c82542c0e091040050103a5070314001d5032000c410f0500141c1001c00c08282d1b40700e050007400c04046c400c45003070090744950307400204400241d118960401240c800030039a170b5200c02c05076411280d00500284204040d018909010b0350110351518018852640691200c1a0210968131740c500006d115500c03e603e0401c96103401c6516100c1565025500d07800700190746440030081a0824445c1d070451903142c0070078042400c44510108181c0030f448040200710004121034480c0c000c40f9800c4518601106250034600000d0004c040c1000c6010341c00140d4800307064000440314844d00003581c60754441f50716400b003403260070b0010300000e01040090002d0356950341d51410841e8080704524004015090100c00500e92400700da00504024100100610205900c0070040d4003604003800c240303800c01d0f81c01c0081040c030090b80c038442e160035652508a0740b80702c40600072201c940d500d0b01489050703070304481c6222004040803000c0301d403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 296707733 1250 296706483 296706499
    0x408031801110408070e040c03020d0203030f0706051b07110907181e05060a080a0c1b0308010f0b0406120903020f060f06091e130c051504030606170319050d020705010b 74
    0x44401b0301e0034031144585e52004100109900d907074240703c00c004810b00d00b20b925000030b111030b880c0003014101409906015a0001c07035181005801030802446802c0c01e5000c10388108034400200d58010001200217100780c503403038120f540d015070840d1078030842c00060017249e100c81000120007250b1084149180ca400e5061100d056442c0300b007202d00d108500003c000310305420002018440207502407024204141020403800c4410071f1030310302d185010f0f10100c0c003203040440140f00f00d075a01d4000c0c60182000110441c905401c05102403e0a8104003c40140c0340d00c55411030b0416200317101c3d6500c2165107404035240c038217207650300807058001194072900901d600c00c0000c10001142503440c010300700b42194044240c46042c41d100c204a54100c040d58442f49100e00098552518100f03040110f800307144050b04c1e241036141990580d40325500c04500c00f40c004450b031000e048080116691030b1751849610018410f0180b0681c6d40d400b5a50144035040e1011403170605200040d001b1210203101110041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 296708983 1250 296707733 296707739
    0x60c2105041502031e070f030e040605092503021611031006060206090c0a03032007081e060f01080d21051305010c030c05030a0b030a02060309150c090108040803180111040807 77
    0x1511720300803058050442ca0300413800002181c02440d10460031030015001140346511240461400c1009a44204406030580700020b9482d00d034030041400454a442c0c25031400c041c098446019030b9001901405100f05160190150703030b4104444c034084030b1440028408241c0c0d9500203520f503a8225003a90300c2c2d029044003112645032a0708400c01380e950644800003d032800348400744141c07000d03400f0800948101345010a0002c010811100342d24503400310144280b5140c1416414060301030b01c1020382d985042c4c0103202d044008615808002128034040200781994418051082441d09980c1c5040c0e10b4030080c4908813a02001c02c1202c10301038002484203c0401408404465110310b80c4000507409001041940c01e440e0000c5548039002012103600046940000355a6402a65895016400b040c0d00c8540e04801c00e01d4694003419540390b0606109800c40080d0141c0030050006000050020000d0b500080e00100ea049442c0050020414451038812500d000da206018001d0726105400b400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 296710233 1250 296708983 296709037
    0x1a09060907060f03020a03020c0106082a0d0204050603191b140307050f060909010f1505030c07020105030a1404150b060913181e0606060c210504150203 67
    0x1c12520a640d80d001d038a50081000c60080d000300310000d040607000c0107004580c1c0f400340a000041d14043d40a004500404020501000e0003034078070b0410601d400c0308024075983d8242d56001c0c20754041d107020645035101d00009081507101c030002c0012070310761140107090043c41e00ba90f180d0f0092004580d8000d036141c4070140119407040c44040c2d0301d640060002d0107941806407410300002d03406041ca60410107110001403020380241c100d2080302e80703218810040310822900e241c007140000d051507855400c0c480305d00c07582881600d101905005000003c2065503145034000342c02c03412401c00d0000c01d0304041c5880c200f010321144030340c2041410141c00c091145041811078070300040c01401e00c0c038400251940d000c00b4000d8200b41000320118000301c90049114070400c01c20103000c185440c85500000e141960850b031154000608001d480c2d41c804000507440d164204040c029902d1614004480740400c80c0d640c46190401d00d8140c100c507400350b00b4950004040c120941020b00030443c00160320000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 296711483 1250 296710233 296710243
    0x5040209150114040e041203060302130203090c040606020f0105090f072304020f070510020901120b0f060c010606030e0319050310030203120403150e0303010902161a090609 76
    0x6940100c440c0086a201640791000c18609903040c1001d82d1420800c900740400e80e002035020307103440d91898080004100181c41d21006440290900b0441a42150081410b48170074440030340c1d01d5a4004042140e00200304250b00c0303140c00017802802510380b6100c00075110b01d5440f120342c10781d41c20003000c5000c0c1c61022500050010b030400c020241c16240070041c0304409003403038100940a506068a0905e6243ca000902c104115510001c1e5201103d24110746800c540c03031000da6000b4030600c01000c5583e03006c007622110450641020620003003040c00150840221201554012800030b8180d001c5601034000400715581354030100140390034000032035180c0c0700b4000d4030841c400086070f40e2040d55000b14051500301f205e042d42040310315143e5022070b00d0031540d800320510140001c50100100b104418060100700c0002000380084089031510319520302060051614954010505190307141100341200c0100e60840d841c1c650404107002c050841c00000d4036105024000d03000068400b03100019 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 296712733 1250 296711483 296711491
    0x12060f09050d050f0c0106060e01080702030c030f0903010f2a09080a02042f03040c080c012a02180906220b07050f0a11010c0207060512100f0e090d0305 67
    0x2908561803109001c0f00c090340050002d070b07603000081c8000140030f80240315500180115403500401642c8520000d802110014140411907008028000303190101000b44c4440c0281e01c96900d0301e0301c403100c1c00203002d048030700a00c5982510b807011801107400150241c0454a00c0c101d244084a40540d20886802d40c0307500614411350300c002032510050400d640444a00320401c12865641780000e8038401410010100c0302d1400100413061005103c04402e8100040510800a1144100c49000038119551620340035182c840c8201d0a0510440300c0c3c0001060340764010b02ea00c103000d41d80081a001d0200c144c81ca00744521640002880d94591075184a1440304140060702c03140070165a10348140303c0c01809002084424082c01d030036002024090b000100b856122a00540206207160303086070010b5a2400455121200c2001a00d4005040303a409040c1b4802441c1142e580004034071207d00191320407500c500302844001600c603c0d491686024016400580c1c400c60486041103041d03130f009407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 296713983 1250 296712733 296712743
    0x14041208040c0e340e091005120a030f0c02090a0c02120d061404091a0702030405060f0306040b09010b040e060f120706021504021507030e0402041d06150f0304060204030b0112060f09 80
    0x5c3ca1807601c0c0d00e00000240d92004241b50301c80e1466860b4408204519401404c3c030b840781d4040d0f200b0100705900300b1180085c620741444d1401d0750013980e40002d4001c18004d401c0a486542d0703144042c581c68828000d0b5140204c0c1800b00d0750b942c0300f503a148903009000521070717000d5069500c20b030315100d4a041e0041a10050700a0f050190300000780310700440b03545001d015001944410400000c081d100c500107400340e2554601c9032900d03443c0c045c0031b110640d501d10111a1054130808010300680c0740400c1620306540e0594041c481c43c0e070315000402d200c1c440d6210a198003000a21510400003c00507299060300d080350300780e0b00d00d060f12106003c42e92100b0380b4025413004855465944030008040944200c5000349003040451490402042c202e0b40140c100c11000c010003d004556298200754141d003001e02510440c0f9130400c0791546d1441070040c100781090710440000403070b00b0702c0195015a0041d503080710f041411965074915040c000d100d441e4040300d0079030030401c5c04050082d0901c60550381d00e4100b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 296715233 1250 296713983 296713997
    0x70f02010509160b0f13060801051e0108130203070e0c070c14030c0d020117101a0306090403030b03030f0d020d05060f090601030c030609090b0a14041208040c0e34 72
    0x400004040354010b00d00c24171212009000c0f100c000c11692560314010866900c407450380c3d5060405008080341010302000c0070710740c1d0b0703d00803203103903401a0807a034440303000744090024034018800139040144070751140341481180c00034000000f01e07a030010303c611485800c004101960701d94078480c410081a107aaa403680241c1c480d00c0b960304041023811100e40c070514182c29a051002965040b011099414140700202c003102841150180410303041c04040004110b411403408070006100600000c00c01020543c0303c04141069031810025642c0c20b90540391100d486a4890109100070f401030b030303d45086141020081440340c14203006c4210150005041c49900d9601c1c0b00055000d08a4802000304150356070400041d1180c00c2d11424003010b11900800c0c4076410002000015a060243c00500300da41000511000800341da042100c8400380e03040c03900b041c2da40c0703080c400900305450f4040c00504a92a08000c0e21185c2c101680e1500c15802003070036941c04a41418845071049102600041401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 296716483 1250 296715233 296715239
    0xf03150e1f0510080d020706030b06091f09050319030e010806030a12021f0221100614071406070f020f03090904020303090d03080a05010801090b010504051e070f0201050916 76
    0x590b0816580800108681c80e6019030780c3d60803a10b0710030038040b1400140c014810a01c6410381c54096030b46811401c654150900707500c6000a84011071a201030620040c683c503070302d1119801403115500605004040d1440302c10070b285016007800c210035040307000401300703000025903600070003849001d0a000380007480c6034405c60765201c4c81c4040704906141948500102201400703084040024140344e1580003503101e00021203c200310b846541e0307004a110104008010009060300d461804032101c83c03170114035040c004081103a041c0b284d520054051400d02000c41c07900a0000b41072400388601d59a0408181040901283c4580c03002e811540c2a400801c4a4041c0d403520107c0190010300080543c0d00e44094100080c0207009280400c5002c2042c482c204000a42c0350301c0b81c0e41c014002000280071484056a074440640b10501490b40705a584401085019450b20102c2c2c103280c000310a23200e4241018400900380c0d00200a10030300541c2000001047c8d084040703501003521001c5c0e04201c2e42c1c141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 296717733 1250 296716483 296716543
    0x501060c03080618090a0b0609040f2a0308040302120a2a090609050123090604020d0b040603150c0507050c01050708070c1e06030207021008100f03150e 67
    0x1000f81c00f4070350005040e0600b242c8501e60800d018000c21a03840100b0b08107140d450700103101c250007418544552180010000814075000144040700d44c0030210031511326160340c50610005041c0940d2489010b501408400c100c0e030b8800402c00d0700c0c000c450103c0611007060301c07180d88004c040001031401440301600340582a5020780080c134400c030008100401603d507040320048400d10303408405280c3d110401082480483d140c103000003030b4000050710010003120042a036114000d0103c1e1302a07540051056070441499005200f004001842849a40c1c1e59040482103e4007502040520030701e44140541458029130444a66503070000103010071125807001904c154000301c109403402c4100304400f1000802c0940ea00000e000058900c1194144400d0351038010421074004034145413041008001603502c0e81c0f07000500c8900e504c2c1013111643c1d440845042d502240e44514010740200e800801000004c000b0b2003030704800290b08004403120403c280c0c0e5100641440310120008078400121101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 296718983 1250 296717733 296717747
    0xe0a082b020124030605160c030807030e16030510090f0b040203010209090a050106140a02030d0b060903010c12050606070b0f0a0b0d0503090102060a11160203250312030501060c03 79
    0x14006000006490000c01490f0305501d660030041d12405801000c24000c010740f5100703558100c205492060201034003150007800d8406586c00c00340034030281a0000395030700d01c290800882c0c458090b003030b1140c011680c4500c0c504951503010468145c0101c512001c49000c11f0300c61901c0c001c0d005401502452101d8550200080000d0f0041e60555000c220782c1c0c2e09030f118188441e0188088601c0090329614240300104240d030310031b0380e824000d81c04014030529141d00200303840d038400352040002210358046000030014484d042090f50035508201c01c050a01d0342007081041c1524128000b440555103a00800c00c13140f0403013500801c001103803404141c60011a002c42a40100c0f1031800150600040d0b000444085c43c451080340c880c0d00000d0250484d513414050f60390000902602404624080c800b42c29680c007e40c020411010840c01000c03080d5a410022459038400c5120324510a04903008141c03842d40d44c6020070340f440c91250212075034551284c440d00341292490f980d842e1010b2100e550442d084 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 296720233 1250 296718983 296719063
    0x7020a0b0c2d280209180c0301051302040b0f041d1c023004030f02010f111b0613080c0a060c030f05160204051f060c08040911190e0a08 60
    0x103aa01d50107402c010385178900300d036003e0180322800700b40f0400c08590280c50001442c030510300030b03410031061004014840a0142d00c2a0b41220003141e04602c01000c2110045e002c0000d550080c01c1644640c40c10070345608002801c185007040d192940800da02c1c400d0060500003207030b401644041a600c903442d001c02d48004010b040c1501100356400ca8420303101d9030f43c00540013035a00d4802545c0c50003c641e08070300c0d007214014a6081000b811480e11b080c0780d0325068140c01c0e41500c00f100076100145607407840b040301c50580c1c2d81c11007114881d4851210f269200349121000d030103441c0d614008201140154003062050303606a41d15a42c0003c841421907094100202c3d01428101100880005075107030f00511344100c2a0142c004100d0001200340c0c030310714600da40a2814002902c0210b80441c400004480944003182008a24020302c844109079620840f00f840b03c00402d0340200f141d10b03030381c40007064030420070490301a4501521005140e84600350707140c804540c40802090301c010791011015a86c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 296721483 1250 296720233 296720293
    0x3060603072d020c09070c050601030602090105091f17040b0a02160807030206070306050604081c090305070806042130060e0609130807030507020a0b0c2d 68
    0x2001901e80d000da504140301d10b5003040541c104645540d41414a0000309510482520b41110117100075141d01c0c2d1127035018000a0401e1b900000c0300070880e4003e13400c99524042c060100811311080c44210385241002c0c0003040b0000c0c0c1d031a40001c1d505051184828007032030b00240307095681d80b2119164802907125440400c210b8180030314010118503484c014208603402600a00340615007041c005044a80d5a0401c0d44142d074141303c10b1003503a0000400d0501c0b0008131103217000d00b00803040b05031124191a440100240b14008001c03903850070125805000c2c81c130030120711340b0710121402924004c3c8141e860752400501d010040385c1d5406640702810034090341c1e4503500c440180030351042600317403802a00844000701d81c0f2018081141464081140c8c000040c54204031041c40c65580d101da648500301c406010007602082000c199035a24040d1001407424408440e0f441c1c1036000d00e9038641018500a5a106010805034110750b4042e8130071801c2408804050316a500090003480941800c0801d5512 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 296722733 1250 296721483 296721527
    0x1120f0b070816050c1b0d0506040c03030305091c0e0a033305070e010c06060e01030b061201060605040506130803040807051507020a03060509031903020a0908030306060307 76
    0x1086440d0000c9005804503901c902c0c60746030085000d103902c006406540200b010800103004074003c0860884004041d80d01d5040e40d082c142800940e0600e20980301030454010402031004001c907034400103084910070344080c080f565440345020b885465880250000d40e198001c0180c15a1041c08180e81c210001480051400d40b2a1181e401e515003650301407210070000f00c0e48104d18403038281310b10600055840309120074a0b00301c1c2d0080c80c003c5c40040150511880103502070400540fa0411000b40c070642042d2080e960f902d00f000007080704244c44c418007450602404022102042c00390b14280d0341c2075101c1e2460b1070300e04800d00005600c0400e0ba0307810034000711404920008140001c200130003c040c0180613903030816040103500500080c25102c2c1c2038080009030010385520308028200ea4001d14000380d41d40c0c40d45042811803241c0b20388150414284054200002c1c0c26a02410341401d455030740056064a440d040342d602d02c010350351540d000304140001140b042c8545040c00011007004414a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 296723983 1250 296722733 296722763
    0xd0807020a1a070212040f06080402010c080715060b03040f1707020d110103060617070c06090b1807090c0225080a05030a080a0207021e030705190e09030a080112 71
    0x1d00e0303012203040c90204082d039003401140e541c1000030450b003e00040100389410f14180003002201420f200703c10600c951000001d055a0140e9080c0182c103800c480c030282d0310a06ca180640301c80c08000301b6115960314041d030100e80c41c0304032802c2d42d10866002e100761081c904192141504091001d048811803002080040c1c01600c910301c081082078411416050004880000981911340f2608200708105402c1802c004a804d40c20035103801000034108100140034504106024207168500a0041801e1509000ca15120241d001c415100742d0390030707074800d5078507100d040b401e840ca81841000140e0040d440e4a400202d800001c0c0501007051210071031907541c0c0c110306400c003035a110301a90903030004502145c1d0903400c401c80c2c0350301c00d030741d440c0451500406900045d0803c22803002d004007544403088400303945c0c0302000048054000180074854616003007076481414005805007006800203034000c509003103400000c0ea8000c1c9480d8440d000540c0c04d200c0301ca006410b80f804142c0e01240405185 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 296725233 1250 296723983 296723993
    0x71106070309260304050f011b0819060e06030d020303160806120706050705010b010f05070b09101a1201020412120c06020d020403110d05030d0e0340080d0807020a 72
    0x2001403e034541c070480d1640b5060406506001115071985803c0e41885840012028007800541810980d0300740700c40300362030f80d0030080f0b01e44240344410666640b501c400803039500c00d80d11110788107800c110203c500c01f00d0708400803a03ca000682c0d804424038608031019400e1342c0030314211a40080090410014240d03000e407034614181d030550145c008a6400180e44081c41001c7c09081c0108000b804c15542200302e002c40201203104030300000e840c024070344010a1a410302030203140402c0d003060005016042e0554000c09282c0e0a507000c5d140701d0a1444d2030340c1070902040c002d0390100c42000414104290345038407400800c1c02c1d80c050950411403004034540001d69503202074003001c4020b00005803a40d04600d00000d400c520341c00500e10815694130310f000010070000032107203002808540813a071496400076492a500500400b0f480c140c3e8149141010320107840d40d2401c0c01c051048146240700100620030308143d1040c0150302164100b11000c0032168002d0351860b8010101c1d10417200f84480649038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 296726483 1250 296725233 296725283
    0x309152c19081e03010303140f03070c020d170c0d1805010c02150f040e07110d1805090a0906140405280206160605060f0a09090c08100204080105071106070309 70
    0x12040d440b030f80120050050591108000030350407000c20000d441d00381c920610b80300d41d0200420150070011041502021903e4005840b10643c0e44840c1c0c1e191014010149806c95802c060308450007441050341200486100394102d0000142d80c400c0048a181864011201040e01e4041030340c1194605000d01c44c8590320380001c01c2d940005500b410b840e50b04040001c0d00c0c00401609980c200710690700960000c520100c1c140c04450058200140c100c55481c0040102c650558000f13079001590000f0029450300a0304091500d41c130030740040000740c0020912a48908040e54042c01d00e911104000414400210381950410350b00350140400a895500240943d40700250005d54020030a10301c8080280c81d00a0035040321048030300c14401c810074070110f820145184500c14a1a8070b414404080c000d405d06c8403406450050142c032801b0394884507042c040e41c010300c50211190301e050002940c5074030400c0c080c81c01d0032000e00900555114001c0c220064103400c90155956502c50340c92284031240903031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 296727733 1250 296726483 296726527
    0x106020319030501060203030a09020301110d05180f060103120e0a0b0a0207090c0c060203060d170307021213151e0c0302070902090609010f0309152c1908 68
    0x40210354909001c91810720781500301d00501c0615003040010301407580c010094a42c84941d00c01d00003401211800004d0141070b001c841c49a5000002400804642458109510541d49040f08881250303003e5a040d5440c0090302628109070000c40041c0001103803091030006d00c96640c034260400c684440000762003090725238400c06032010005441001986c040c0124070043c080d07580204640e0a91500180c04160079602c0140060b078000009030180d941c01107615840740c3c0041c1c0d0015580c1d83c0380c401010325401034500c000944224101d00220000718401c40c0d2494854100c0c240115180108048130400c180148030180312034100901403001c071060034203c01e00045e5451025010090601a05140d21500a600b241d4010845450640c490400310b40c00f100c428644440c1e4204000c0003103004146900c4001c1014080302d0450441207500e0700103804001640d49001c00d070000d1101140c0d02d4000f0f903003014160f038010032402c4913480354120140542e5801001c0107413501e440c942c21443d000c0300c00c00f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 296728983 1250 296727733 296727737
    0x307121a1c030201061a0301170601080c120a150e070f0302010c0809011e02010c030c020303011202151b060a0b1009061404050909070609080d050904020331021309030c0f050a0b0106 80
    0x7c00100a02c104000c0003001d00440e100180c04503506003002d168442c406103581c00c3c002d20300542c148200601c2005102641078008010a268a03120031103a40a00411a01d5017158491300e64007042e244178102c01002101c0c2d0584039007850003202e47e106903098120384a01410302c00c0807030600d640300b020711002c0c0103440f40f00da0000950094060014040380d40000c06541158424070050004188284803a0798040d0100c1380a4000039903810602e01e9032155007211040c2c000c4614070441d80300e4000425500036402d840042c427400c5401000c0c450810340203503800c800548035503007c010b098000c0062249514000f40500d00c3c054a400101c1c404d03036402e9854615950045004003c15a44040b408020301015005801c180482100050041c059044160301c1190700002048502c030302a0001c0c02000b0b83d102c11480c50340c100c030440f29200352100100364015110180c010f2648040b41c4200c00030350342e060326160780403022501c441400c4099a40c0440e503601c6941c6500c0089100c030045a0300030015a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 296730233 1250 296728983 296728987
    0xf060a2705041b090807030c0b07170d151401540e01050a03030f0c060608011505010504050d140a05060906090c0102030f0d020703030902060307121a1c030201061a 72
    0x5004020410313542a8090703205600007040c00e000050407d400a4121403024070300e1502c035052800c0c070701b4414150709881c442420380001e1208005a41d5000300d140036416926940c4019a100003054040c403920b82a6400501c180c441115000c2d4031060301c1038104041e4444043c204c08900c001d154084940c1a52a01900c101070a0385c1803c4a800703510000e03000140c0c44d400719500d0300010138400000c502006042c4104011490801807051201090b0681c203d5030034840541c0d21f045281c020820b030034008001002180012840c3d50050703045501701c1d140648840080320070b41d200d141c230a6154480a42140c040c0e10020004207900704000c2e402050b0724006002c40e400c14201035494902c54842c1541550010301202c1000350000054400c0000d0421004d40d55070401d1400314014101018000e50041c404418800e5942d44070307140b0ba2031399400603010001059090760003100d240c10102002d40c41201c2d00381c00310407000d000502c1c0800c3d81c030900001c03c0795501d5400500c19456211002c075521100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 296731483 1250 296730233 296730281
    0x150302120a1b050a15020d08040302150403030911010f02030a0311040902041e080a0b04020d034a030a06022b0f0c0c050c190815060f060a270504 64
    0x302d041e0000040c0462064059030710380d45c2d28040d484075220102002842406c60002c0d0916000748060441e481d0704030004601d526241ca0041c1c0285141c0000ba81c0e41c2c0005100c00c48a54041c41c0c0190010080e81c00960400b074441074220040d2080300c01c400704401040c400020303580303494005440504240300078018030605440a5042c5200e00d6032180c8041e0b808a048040402d1002c0d220541268050341e599466806500701903170441c84c0400510174401390004407409444207070060719810760781812071b18414810b400c03240444a0b4403200c01907154202c0803001d0300050b0240c2c000c1c0361540e8074104100040e40c0b031500e0b5121448250300b140300c02542310041c5000044d0720748541c0d0114425030415040700c003110b40310103503a00c5c01141080c1c02912540310070030540412501e11401000d40354211080d6100714002c00c5000a0203680003401100d0700c00c1c5020451504038251501d403e600c2d614852202c1c000840000d400e001d244035400c0b41001d000001c141d50300e50740142c4e062906404007040007151 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 296732733 1250 296731483 296731489
    0x1030804090c0504030305120c0f03070327050601090b040902060c01060305071d0a0f0f2406020106150f2a110a08070528030b040510150302120a1b05 66
    0x801c0d40d242c50308100b001c000903c0080c1c1c01c001642c10245661400f1a62039a5003100d451041c07150480303030640640702000b0841810340c5070f000014440010321059080b5410425140d0240a0f00a4001c1c441d0300181c005106143e107591011501100041000c264403103240c01148150744481c25004081c2d44031001070092090030004c950060598000198080346203803400244403001070039008141c0d8580c20401c104d4002d5401c80000d21300c454004200c459a0303240780c00e02040c0858030300b41452a241e000011000d00601c034040865444661845040810762011a20051800595014003204003519064881d21500902e6034001d990350307908a4943c141016100b80e40126802c900c035021480003481010350119500b0106e450603034841c0a000b03612213000555807042c400d84c106a05440c48000300b4001003801c01070082d03000d581640d180c13200b03001072802030b540020441c865a01e4488020401810b0844141080303200740002c1c0c80050741d46a0300c1c002814081c00c2034201400059400740b000f85 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 296733983 1250 296732733 296732741
    0x504060e0303041a07050703080c03090111010507081303050d0606170a0c0e1e030a0302032205030a0201121b11010b040501122907120e01090f0206030c0d050103080409 74
    0xc10120025410a4644510002c2c42180c0b5103628080540118074081048001c002c680082e6600c02112a00d8050350514280c0e69009001014005030480e64008003401c0103106850090305659241c03804d664440d030b82c030256844211000c600300b03e801c10026030b4201c440e01c1801d01421603a5215481d0700a01e4800700382d8544068000d150b401e2a10f802c041e9071503046001e01101d448243c449600308055080e46050000b07028501d1500346c055150000c0c1016400300041c14001c254441008200328ac1d8103103506618a11300a154040c0d10000c01c00303001d503000d15107030b5603c19400600858091144015039400c00205807010340031a00034401d103444480280107080070408251801c00c0998541102c00420980608014101401c03001480007403410385582465180f0003095410440d0920000090907840b100c0701c094030551518001c15403c40d01806120a010707006104400746800c80d408015403a4030180451491a20400480448456501982c0d0003140545456600c0d5444c05809800796 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 296735233 1250 296733983 296734007
    0x10091a0f031504120504030507032901150c021302130509060d0b011802070c0f06140306012709060e06040507031e02090f0a09020d0605030111090111011407050406 72
    0x1e90009020401c1d05442498126401904508050111000c0d040155540c0c0b081c1e4101816602420b2804801c0c4282000040060101d044100d02c01100c0c2c0c0903084039000c428010350200031001e1080707103841840351080c8850240028181d074030180a821002d401c0382d005c40007800c2c013100c1a820810084c64a10940340d48403000340c5108c45540d41c075545508c0008070500940c00c001c401400c1490f03103400307550306440c0181d501454040a0300c0c2c0351443c03003c451000e8450007000030910f503801b2140300d071814180c3e801204182c48640000d141d030381e03041040c90500446200c08840280f4001401205400360a0050055079540e0304e1904160081c4070079a0300003070016040c541401000c41031180c40c030f49000c02c0c401009000586401c501c02c0001c000243e01109507034040b80306680070545191981c01004c03030020101007004110751717440c24542a46c0c030007190411700c3d070030a0000300a1075000391050400240e005000003003407100740881071007880c003d41e4036000040300410240803c68000e0f84114030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 296736483 1250 296735233 296735239
    0x20310020c0327092a0a12020a030b04050c040602010e0304050d0305070303140708070e0405010b0a0e0a090e0a120c080904020f0c0d0f1b1a10091a0f 66
    0x500301e0141c9807aa0b603403080400355880c4a540d001c44191120100c1c040003010080245203d803076051149416040500f001000102d052040c80349009290b0560119414003290380c0301c001092000c4415000250441406c1d0028151190038950740b0b41e41c0d900ca031038840d1802c0a501921107041c40e4009084403400e60380101b80d940b0030801888a40c1c0e410f0b952882c00e540c10300d0003035034861040c501180648000c100707002d2240440c0d802d0140035034012654500c41c41c0c565840408445403001000f058440a204044d9240010040746440b54400c40003901d4159001d1b1402c50b000e42e4442c1d40100703c44180b51840f071180c110294000c00c110707100780e4824010040f490714000c0001551650030051040c0015603100c0d95000551100586001007a01e01690800303040e507100400804003d04280425404c0b900090207600d0440da2140c010300008008a4010007000a041b00c20031101c44000005031080b802c03101041c200045125460086504041c100b69206a110407040d0910501210109410344 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 296737733 1250 296736483 296736487
    0x10204140909030d05180105100e070503310503030901021b070e010501050a0309140d02100c02031b0109080a09051306080d0f18270608030403080d0b06030a0902031002 74
    0x4003000c400002c1e80e13001aa043c50001d216220042290b09040108130501801c0d401c0c6004c010480e991002e814040f01c1008401e1681e907503e42d4801c0f00c07188030440e4035441c401d004140001000e0207201002503a2031844420b60807070348283d03d86500d1a04120340315206a90002650f6980d50505d241420340d141c0403500030540d19051000700407090078140103441c1008404264820050700c0f0ba080084030540283c106095940b054400383d84400022200b40701500c640c1100c482e40800f01d05c18202401c09903070156081c4410301404841640b4042c0218000e59203999001001c80c040703030003c0800c403105031640f4901e00c0c51701080c000102110b00030709841d1032406104006c80000400c0201c40c0049610f4074840601c0c02c00429112501d80c03e0000841d0004080085000c0b001c09148503c9482e0aa041108101d448104041510f603a402811615007040c0300c03c0000170020f00191044000b000c402103120340100300407490386e0300103c0d001c030003881d1504a04425418240994807413400d101c50158 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 296738983 1250 296737733 296737741
    0x1206150a0e04150b090103030509010e031908031003060e0f07080105010509070c0c0e0c09030c040614011229100c0b13030207081002090306010b09031b1c050102041409 74
    0x300080e000104064503896680900780d110b9412a800808007413401802c1c41481e503124107000703041e500450403030303808580e405144551a00c0c0000f55800e1050348060072030440d628650700c00540e5040074082c1158000c00c44070100009400d0701882400b400740382d004110202e1105046880c018156000301c201da45401c0044c89544c440e040441d60011a40c00c0c41c07400b0001038036081c45050380c99070005031190001c00501164503407010081824140480885a105200078100300850b100e0344250782020b4551101e50031254001c034810701000e402117500080070300e080c09500c90458082c0c0c00301c548006400c182450f82d8605200394a10074140340c90101d40500d42030f40c030000340400140100f84208007910100c410548204031000140c5030701026038071501100388903a00070390450f000152180c01004000b050b8550088141c41d5520030003001001c07443c42d40402200360090450b1000d2b00013141c08060700c040d84469071240c0c810752241000503a92442c09982120408890341e085100d860a64180 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 296740233 1250 296738983 296738999
    0x90c1a030c030c120103110f030c1e0d050a0308010603061502070504020d06090216020a0501050315040c030e0a050f0633030a0c0b040603062c151206150a 68
    0x249921a04410507540d5a45801c3c11180c550f00800f104040c40d0f0394250f001008100842004800146c1d090350880e0450040c0c100701600e4881c1c2c2842d01e500400248000d1540a88880398a107907180c015000f4072603900d4a889a80c1030624100080c0c02061080004118066140c45180010030074001140c2c54814039810003900c41c9000d00c5035a20a40c0c01140d00c41800b00c180d40180e00610b40c0e4001150343d5a0b0f240c00190382c1c022600e0701a40b180d41e401074002000d50041c41100e106091140e1070320341665145003004028400702c9441010103a54080030942c541c4100a4a40001d005c0c40003840100001084645003c3e401024120002074001c20300e18549250f84e4220400004a011101e0018000001c0b81c0740134001100508150f1814400042c1180c1140080c41559001e5800740002611001008208a454500003505400c0111407819510360a1017140d04001501c840d03680121901000840a510501c0c180d101500610705001d10508440204185404142c501c030402d50326060074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 296741483 1250 296740233 296740237
    0x19110a060e0d06110408060402031902060f0f07020402040e0a0b030d050f0c1002160605060409030801050d020103090b1807050a060c0308070201090203011b080601081909021c0303090c1a 82
    0x441c02075054102c550308005098100d65007000019205588503555140380642d228002d0b203080c1d01074041d110005a10b403403800306000d03500d030b00902183e151011900300107020758080001991230007010710445005a07600d000510007010800c0504400e400c1c049564030440709642141c40c400e600c03006011070310503000343c1070713a500c441d98003603c0e030315030b030007980400d0405500220380c00300c803413000a640c12102e440e408444000c9000e15410031031581d03204240000c81740d0320301e00603003ca003401d00104018900720300c84594540c81890701141c1510715603500c414211003507c2040114101e0207400c02503040c10010b0310001d180484035000c405280640150100c490410040c0404c2400c00000317000390700135044090071940c0a0000c000d01004401e0640c41100e58202c20000a0221030210780079600c10090301d07004210311100070611000300c203c1031004100300301d4200d0704407480004942c240c1a0307007201a51110f0103518041200e0302e40d8540003120508603003080102c86038042e045022071240e101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 296742733 1250 296741483 296741507
    0x504021206190207080d0501030c1e0b07060207020609090109020316020703080d05061f0c140a020a06030c090504090c14011404050f0d0b070905010807020c030307120e0319110a06 79
    0xb00059130340045040c001e074944075005003850078030f04010002082088544840d0708452074804841c03c1c04201d0510880710640718403030900c22100074041400030031625402082c07800c2c4014101d0b80b41200c0100841c840c0d030030076488280c040b0780c01700410611180c0c000100625071034a10282a105045594000c4180100c400f440305203552000003416684440d820030403184d401d00d5280c117220402e81c8000b00030054000e41254000710305240700f4200c00f030020740c110910f940200b01ca5035030703820704804030000c2c0381c3c0883d280300300f1400c00800601b0b51154480c1c80610b6006070f206c0440d40c0c0c00c00b50700701c09010b48640041e04101d080c0e14900442e06d9440161b600341e50046403075041d481000000155120801e01014054039070035403d2140c510307082a4030408458080e2128a21541c0301c0e90b007a6180c04910100d40d03095081004010b0010b007980d4400041d607100c50a10400300d040360008645030000c3d03440030b540020028001075061000d005030b02074001c1e41c202d0700d040c841c03401d04000401c0400264 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 296743983 1250 296742733 296742781
    0x106080c130b0a05030a0809010f110303041401060b04030c050f010212030408070201020c040c08060f030303100308030603030c0d08010e011e0e04110405091e01090b16030b0a03060504021206 84
    0x1e02e40c400964072100203800401000b000c5840155075401c1a083c80d6000c8006103000c1100507000400113406100c422a096209501842c210b94032070321814038000342c001d5102465580c1d9400400e01c800760170081c0c005903000e148004c4406081000f402076000080601074159844a00c801c4c542c1400d04084a5101307a00c404080c0c2c03280c44520041c2c0c03500c03c1c4204469489070a2403560960355502a640503c52003045541b12010320b4010245601c9100950340c074440b01010040520200e003507003000f540c0041014040b24a040000c402640c24241e84039001c00c001503902c0010001d85111070581c601400c1100f42ea11202007100d44550b50403a058800c031250305843ca00001c0a1003003800c0d040c05181d90242007449903140c649149901d45044009000c40d01c683c2030306c245a0090144110304840d81e02010140803500c40d140306104510a04001100b0190cc504041d512612400d2030b0600551240c0000710700c82c18507204100390b424448100d4142c503800481089400b80076142c0d814030005c1e0300c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 296745233 1250 296743983 296743991
    0x7050105070606031712060f0922080d0501150807021906150e061e0f0913050f010606110328030b031f150e060f010302041502010c020106080c13 64
    0x24a4200c0103400d1551005d8541d40f115034070041c4242489000700b008a41106610384696a80c1042081106450300c00036000f403110b20014201c0680d4000d484c080760003036400b813468441955181e81d0340394000c0403c0e4140c5619000100000300d078950852010f400d131806c0c0000e86103040c0100031358800c40d110815808030051040f11041c802260f01607051100f8200b5001c404684400420b85070340c3c0706450450280e49a108003807200070207000000c0251000520380340341007081408000c0b04480284c0322007960700b994603411000030b1302003210750040c1d00c1c070074000f0405528088020300008090001c0110f02d4100708403950800103982c3c1111000420380103800301d41041040c0c00c9004003404424640c051080c003500304e22a59036030700c40310a040c107000414007544070107c4c00500703120094842e01c2e800011100200300185480744200d800e4650600d801400c10b40d64408000905242484031001341c3d54030110f0710034042d0b081c040c8030003a000d003030018000c0c00e035928080b400344000940c103a58a9607071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 296746483 1250 296745233 296745247
    0xe040903090b1611010f0815060408060a05070f0e0108071103160503070b010909050717280309051203270406180b0a05090c1b0706090504060905060307050105 70
    0x2100c510000d403814180060f20740b5400100000008000c0c02c090341c20407801a40a2a40d42c400d1658024078011a43d42c0d402071340315002c80c210340c4511241e03015880b040510001c030b2030013010040d0728480c01d200d000108440c14401000b60a14115004100c104043d145060040380d820065a03504100140350000c806500501d0050850041d036002189140040c0705100600400201030402c0900500481c0c170756036030b182d40303001c01c070380c2402e00052181e045600c04111240d07818904880131099201651800ca070785c002c40e42d00a081c0d610030305e00501c00001d0040181544038030904050841510882c28000c0f0b184a100d41d00d001d108076081c2005400079401e004096003040428094034080d0042c0402a00c0d04a103041c2040512108940280b400c0800b03221031802c006241e046520180c42c5415903140c80c807aa05d541d0b8004d2450142a0121000740307450f02d0820021074005103141d680350306032035092804000c1510402ea000121150805041c01b007607640100b403070707402c441090070510390300c602e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 296747733 1250 296746483 296746487
    0x3190b06190f11120d0b0a030c03080304081c0c0815012307050304060e1309021507110904080408010f0510050f120d0507141603020405150a080d110d0e040903 70
    0x8a42e52115140c06a1070004d42d0703070f6419070064a441c080d411014450200c4800c00e0010710011444060a00a10364004001007030f500780065800900414400e0703d0000401030b031600d20b42c0f03113000400300d50b5590b143d400c207000d901034000398100c550042a040740002ca00c0000701507000d44682051464290307840364407101c0c0304908039a410741c1d01c002600d490b5a0b0381d10003d4200f610345502d03240180030384401d10f10356a2a521400c0d0310390b907000302280717000d600130807003540d1917040448201e84002a96203001e4550742c840c01504d02c114442d40c0e010791f036039040800c411f0039034030452849800141000180240b00202e01e40070300a40304103440b1082c2d00b4130410001200110900030005050184e0704c11581d03c0d036407100082c020760f40107204c00c21102c0c3e81140c0c13103503603050250903030030114041c000e040c80140380540041e034010910641540900c41c5d900300142c401d0802e640f001310705600035481d0216658201c1030320302e00380c0480341c0602020a84420090b0000340c0c03003411907201b19524410302c01098 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 296748983 1250 296747733 296747747
    0xe0a020409050f01051e010b03130602070b0910060308040b09010c0b04060c1e3e061024030903020709140a0e2107020a0b03190b06190f 60
    0x6400500c14092680d20342082038485014189040143d400e06000811201072404403092040741001c40201d00da107080c0300e2203030039000503095071840c00070850f100c0c0109985001a080301750140000c00d07118100304d00c1d001e142c90440c2401d8441942072000400201da0500c2c1910b041b1103030414140c0c0d444490300012a0540c0740844018282a11301042c0030500055a006080c104029164882c0c06005500404c220034170800716807000a50520400b003000000351048101d920040700d6128420550f00d452001500301d042d5440a103078450b2003084003110048000400a180a81c0001c02811252020b81511181c86424600381600c5204000406108202002c001c0c02420070800031504807840110101005507075000889080a144500f62007001c036a03446e41c99403140950b4004440740c6111000350300910000d82e801541d00034009150351550004500c01c1412151229007041c0650401046440c1501190300a41d002c2c0120404410200790707040c1000e005061000c110180400d00b21894 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 296750233 1250 296748983 296749003
    0x61517090118051005010e272a090a0c050a0507110d06020a020c090702190614010806010f17060105061b0d02061801180303020a12061d0105040902130e 67
    0xc518095082c02884000316606401c00c1a066050001340da1341c00d4040a206004e850785001c0c03914181c0c24032003100058000226885800c0c080e1441c4c5200d103d00e000d041400840981d91710540d55250821030f21700825100e50245008104210101d101580101140100801041885000913600b41406030300c1440108426000b07201c002c00191514188010307420800310800544510941e0740350610741003482500c80e454690042032810143c4008000c0741002ca2001d891880e075a99209008030040321889028100d800010003055143c000e5104042c125a4003006a1820b28415001c0c020400300d0b1440c1122800c50b0019205e110640c040c46010700400b0424080b4800d0007400808907401084451181110205442c0c008074101c3d801030030317500302c8041c6400131400360701c202c00024000d9000c0c10252540b071070328084540d81188140c0c1168000c2d0400039850070400e0f444c84100d11304080c550301401c808d46081c08443c0641c3c1c0400c01e00d040580f00090140d890b0f5019101c654030410000d250 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 296751483 1250 296750233 296750261
    0xc090e0f070807090b010309020906010305150301091407060809030414120d020c0405090106050102210c060403020609010c0e0906010e130908070b150d0b06270a0615170901 76
    0x208950351074085030f65400c1403082059032814000d003415998000d10640f4411500509455040d95030617004600421004100d1511100c0d810b010000d95182441004059031040d4800310f5032000c085015031130403c00d0323844641000040030802c0150300001c8103880444415007003402c1c04881180000f8038044ca1b1000c08480c1d40305840220500c140c0c00180a49010426a000c001ea525040030043c00c1e2440ca018060250380400c080320180400d409035030840f80d090313514840c14101c85940c200d003070030700565099005900400c140320140c9402e00c19541d10501c03908194041d58080004958001402083d013814014046e41034010307a11040b8440300b406414000c01c116a04080c1341c420002d411031b10041d508640b9180010742c0141e403800c40b07501c3c50a03005144e00720140e9155078898503ca8001c0c45c40350400101c1501030f802950800314103603141c0007180c0c0d140c4145004c0d2042000c40b1481d41c4088101e801544402280b5500700300034000883c024007100c0e244d83d4401d480301d0f014080f40a00c00e0f103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 296752733 1250 296751483 296751493
    0x40e070618090c1d060408070e100b040609090c0206010e0402010e0328170301080a081303080301090b01170c0318010b19030209010b09090c071a0c0301060f0801030c090e0f 76
    0x1619440702419413400402454082d00800f0842480a07600650290200795070205506002c103151410b400c1c1d40c401d80e151184050f040d1542d00700e01c82a04150b01c02030100340314100c1070006d10b400c4e0080c00c000e000188010030301d640c900700300c8103078091028001030b0510880e40310146840d2003d000040085185507a284c23036040900c07041c868403c0042c10103461a800101b003100230301100c0c00445e4101e0b21000002c104041d12900c481101d680040c0542c01c40c80c041c04800800030f62080b000e140204822382001682800c010009040b903040c10340c032245d40805600401000c0d04e03610080d00c0c0c2044100e000c2c0c6841d004040340d210b00401540c60750070752190307000d800d030340b10b801d10b0403000070590b031081c0c440462a9982d4030468103c0d0141d10341c11640020b88100042c90048860050010030340580018452071004030740c58050000c2c00d0700c014201c91800001400304c15009000900c40f42030302d2030084910762441e10740300014200390141303003d0940c60741c3e05202c46e4042044505190039500c41920303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 296753983 1250 296752733 296752751
    0x2071a07180e10081c14070b010902070c08011e051302040905030318030c1c0e1806040b0604050d02190302090f010311010309020102030d1e140105090105040e07061809 74
    0x1035102c80032240100c0c0c000c100080802d5240012400c41c82180103005620070300c4001c043c0039190700400000034084841d05003c6107000c1031542c1440740c001c0c240394500503a242194203041501c001e01c0e4100480d1a8100704221203160003503545100341102c9100001400d031640710860400400d0000003079802405c2010003018400d010000b94012800c00108258005050320b8035601d030f000f0403044c1403158222060217542c40015a901e56401035075481c145200914070340c00285042e0454500a025131012410082e00e410984503099065008681d460704091510000564914000700000c1c0036807580b03284c8000c2d15040740094805164010440ea140789062014842c0c0c00209120a030780c0007500c42d003c10070a5012744078070700590782c040e40918a4002041b0341c20f0003500503031625001202104910111a481a1240c4e100c402075031903000c8001d514220030030100700c0c2c0603001184240c1c5005204958184001030400882c1c14230304010240600d40c8501664030506a8401d01303100742040115 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 296755233 1250 296753983 296753999
    0x309240204090506010309051e1c08041103070f050d06140405030711090c2209020a050a021002090105071e0b13061d030d0e0106090f0e060a02071a0718 67
    0x1e001a00d095010402c03032640c0d00340045050f14030059002e08190090800764030812106c82c40a440c890000c01194030240150710507000000441001c90f00003460760050004104690410801c0b00c0421402803640798104507900d0510303106442818460b03172610b116a010024907403c2102c41071020386459400d4502800c0907a16a842088121080d1000c240301031814517040325410b00502c403c200e443c2c2042c0d21640700d40082d005504021001070842000001c600046000924180310655107050712042c01c44070280c900500d8516140c1014018001e1001a9901400b501c0e18140c02c060805010b40c0300c2d203464401520101800741c6101520401c110481844800c015005440742c401009000c003800801719052000ca002c5154a40003004a10013880564000d82442c41f8640c000040705c0d40c1c1c402c2208101c1f818030210104e03064076000c0b00783e1054003d00101b40d0007400c0314000c0d8034150859649801c0c030444480040030840d0f520000c5440244218400b004014001209204240d160115 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 296756483 1250 296755233 296755237
    0x213091406011b030509060702040b03160f1403060402010f2610060815100908030313030201111c0f18150b04020c0304050409080903030a050d0506040204140103092402 74
    0x704501080031240c1c100c81201d084056901140d8040d542c0508008611041102d154010201a0303800750711038810803643d036400e108d2090030708844170403a41fa50b40f52960040c055002030380180d600c0d0600c054590300a031000710342650310a41c2440e1910102d00c042c82e007030341c04c002c10303c180343c0c540d810400b0410030020b04190010b0044180003000600e5a944030800c50312454115503542e40740d4a0b6a9040c051810406014051072056081940241d80c5030b4030118a160000c0300c0a15450414000305000c1c1902842044009115030560600d81140400c0054164400c60005401150740b118940f031010741560000e2044592280070b0300c041032050400c000c6261b521401d0318691843c028107009036240901c00c41c0d00f005003160186040c1480d01c010032005108584040ea0b40c01800c1081071003507601400109503a40726900d405880d170000c4d03400310044030402020503008920402c0306220566469080e4a104002440c0100c0c0080e820700c0e20304a0305400c04c195a0b900c9203071044107800c1b1156500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 296757733 1250 296756483 296756491
    0x60306090309031b2b060b040203070f030e010b030a0506040606050f0a03030c080f0a031a0a232b0b130f0605250203120f0f0414031c0e0d0309120302130914 69
    0x101070090384e68860408c002c0388800e468010100d030181c3c07418035016000fa0416145018913000000310165904040303030802c0c0400100310f910780c100394200010401c45109103c00303070000b6100d4845240c0907001007421908a4000681030004041e10350041045802c2180c00c060040a41252a0030880d000035014040c4217054619000021801004074246224203004443e0301031800d4011251344c0c080d2841a80c060700c61580c00403100d090310407070749545100012407a0400e802280f01f020701070411010031400a4a04a2900f0500602001041e000b10503807041d940c1180000606484882c0f101000c1c0160900101303003410058114100700b0307000f0001d0a8048102c100d002c1d1507554042401c80c061000301c3c0e0350200c08a80a0100340824022029040c190496004a03890f10071401c2400408111501071040c540e9103402d039003555031030f080c0008541c47d4058101805008681d03601c2c600403ca0f8903040308200f542c0461180080840d00d03000400620000c2800c108400048082209000d0211 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 296758983 1250 296757733 296757743
    0x15150d0f060f020904322e09140f0a0e01062310030207020d12031401080303010801060603050c18010504030b04050307030905180f06030c090c090a150503010b071712060306090309031b2b 82
    0x40044007420f0b445605030b1213425500222b040075516030701c0700001460211011001c0750740e10350b008910000d408591400b00300c003902008038404d181c3d03010441c9209002c55a0801c06005100b6000140c17079645640300e1070f580c41240e9080d0451840b2085009003020145408080c1000c000091181c00c08401503042c0d5600000030b0000035154201502034440075038032428215030030030510000041075001201411300c1490418074080c1e5030307194201210425501981c0540001600b0070800da045203d490003002c0aa8603503500488003055049508001845498240c824000082c40d56400b03000d045035100c4001c0c0364096a06040d1400e0800e42c0040d42d071103000742c0030b0034400b05a85c5258004c0e050a003680783d83d200c0c516030a00b80c54400355040700c50120340300030301c20b503e2954602000c0080d0041e5840a2010318092601d1410145400380c06002006035400130402201151000700f10030034010ba03000246100d03100304070082940f1158421103000100d5240c0c144609540310003400c90324540c024 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 296760233 1250 296758983 296758991
    0x21c0b01020a051e1e03180901260f0f06010504050c070206030a020901030213061809020c0a020f0f0604030b070215150d0f060f020904322e09 63
    0x10010380c1ea907401d54001410980c0b01521004140b00d000040316090281310050303921800240d56402001d40920320a80455000451840788020740100d0302e080040044401540315454962031202000c02d1100714085450350200c0382c0d180c041c2c00c00503141c3c610962000c0703480442d030580040361500c200f8021103204904110214042070ba41c139050740c0300030303400500b1985141c030b517941e00000a520131400607051580900c405038000f40c004030800001c182c0c0b500c1c1c012139000c82d0010569003540a402a102c0781d4814002159140c1c03001900045699055503040f03190440f2500203007078110a4560f06501c094005408010040210340403401289950201c984844580b540b01039200402c490604079a502c01c0941c2005e03103007609414403414080c801700800c14026071101000d4803160178240040d04d0300041c40300c50a051a20502d2142850480d114488011a00840d0135030701011700304a0494403030b03002040110390221006a003164171303160043c1c010300d40d0000981054606100301c1143c0d0b423074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 296761483 1250 296760233 296760251
    0xa060e01050303030402150c0a0b180d080c0405060a05090a0b1902150406110702040c051c02120c031015021507030510030210020a0b13050c03150105011b06021c 71
    0xd0344d018540c0240740c07c085040040e19040a60803680d0f040300c291203104600808074a0704004280a58001c0c200400c80c5142c20b801245055494003103c2c0030001410100709034072026000b030764150341045900710340c1e410300c081d02202d041c0999494154400d0145030001003c4403144004c14880c501c155414210280c1c104080c0e0f11114211240101071001d000098001807041d4807030a120b0481410441c100040c41c0c01040841e00c102c04001d000c41c03400980181d0000888403981030403171801d0301c02d51030010f02c0303110350b0391400e00a0010820ba503c0840031034a0505a09100409080d047d0b9130308890b081c00b19002503907600f0f01c24041c0c2c800074030070020940c00c034485d0180310f1107000114407d40c8100d1070f55082c42030031010100030344210301513603080400062100081d54016800210102107200c1c0ca82003a13801e050301032020a200354000303402c507440184400140b50444a09013080c4003100d0f0202c0001c8603001034940005c2c4000c0c800140c82d00c2c10a803c0c0c00c15414106109000c024a1407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 296762589 1106 296761483 296761489
    0xc03030f07021e15060a0b13060f0903021c05010b0307170c03030a080a0e010f02030408070b060324041401150305161809020f090a060e0105 62
    0xa403140500c2001ca40c100500c0c456090303000c40203004030030b084801a580301691001208a100040009285617591580400080114a02e80c65440c03050500c00e03030300380c035140c022000805c50605600048520980ad50f5050300d9015007064401c141d001703440790480b00303204000c55103992140854040c644060090400403e9900c05480307403444001581030401e540e0002560190340b0074032015402d240c0c040340d44d58011001c644000b408280303001545003d00074012100b200c0d14000405d0200b040408801400030714000d11406496403104010541c03034035440c5001c510200451100c1d14448881c2c4002c09400612a00700c0002820201d000103003551424444800300200e41102001440400e101c0c10319121800039103242e805003041c05c210781420341518503910603660345004800319207984560445010004141e00440c0c54202d03d0100030700b407107001d549040f10440b000026282 = true := by decide +kernel

theorem cover : BRFrame.Cov 296582733 296762589 := by
  have h0 := BRFrame.cov_init 296582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 296582733 ≤ n) (h2 : n < 296762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
