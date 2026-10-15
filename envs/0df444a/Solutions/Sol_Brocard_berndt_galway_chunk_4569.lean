-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4569
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:02:33.946979+00:00
-- url     : https://prove2.me/submissions/2c4a248d-2060-41e4-8a42-adbd573985cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 821582733 ≤ n < 821762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 821583983 1250 821582733 821582771
    0x17010501080619020f030a0204150305190504110a14030c030a02030c0d05070b030103110a150e041a040213030506010f06140d022701080a110f0304050a0210080f0a 72
    0xb81e65800d081c3c50000f00182070009000e980b400c143d40c20310200401c5003285043c0e00500c2922880300345000040800c01d003c0301995000c8850700509100e12900c001c140100b07800858106104e000b030303420400c4841d0046040c0e40c42c55032000320900c1020303254500f14141030000064289040c0c01800d2031281030380201740d0303c0c504005414015142d030360f4650140081801300d0742c050032502c590b142d5a542e40e41045c00380701010110381ba106e0782d81001d00107030758020510b00c458201c4480d11030580030710280701088001d080480140310441d401d204052269900c41c030082c03210050f40c4008201060031401c02c41e140c603405030003c05000c88507a50170b00125400ca81910f25109440750310940d61030100400402900609100d0046546208440844259185c592a9642e0803c0e40c0301d0362159245030035402503070340c10090080c3e9924200003005190850500844e4000d005408681f41034100d0360202d81501d5411595800140350f04007030104001c0e162091310340100158809100b101c0056074403510320 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 821585233 1250 821583983 821583991
    0x801090807150b0d122c130204120602030a0e060603060f150d20030303061e032e0b1008070e0a030503040617010f0806060d030c1506170105010806 65
    0xba1481c07a01403148901c075030001e905015014012030551100c503d0803800120301c518055000c00d502003100860580004100f58460400f50302c02000e4101c400140100d041c4080101050a9020440401c00100700842d41242034071520005070340345000012501110090b002c1c40565820103c140300081c1e0700064600d806c403003c00e2280000e80c403a13558843e2018070182219400c84102c00d42c00c1c00344010b00c420101480e8441900e80300c1200c80c101050b440f071004599250f407012400c410508224400040320484080140440340c4a42e00302c0d0f0030703130303d0301d003902d91a43c0301801c91007456500d91000c2c0c090801080300c00c1d10100701100d1841c0b40a0a86c0740020000420450300e01c0c5150072039680c0c500c1000080d81c000741620303640c1c4e4079010018009944001402c44810712a800090308120007007800d0201d83e5201c0c081c110300c0e11204108800290805420340030040300010a001103001c0c10f00d10101059041e200107062890207001064803080e82d1071500407039140c50010418004045030389940 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 821586483 1250 821585233 821585243
    0x2031006171b3403030b010207060219030e0330040303090b0304260a021603080d0c230306090a091a0c070c14031203090d08061f020c0a0801090807 65
    0x88101207035030151031107055580c0c0f8aa100004080e681e003201542036203940e03c0c2c040e56003484486528001a40e498020748682d00050340042401e40f07000e00d6204001d88950311034078089a5141d1070301c0003c0c0c070701036070031104101801030b0b03040c0b420041204210869810706419800c90400c1e1458801600149080c41550065030b4004002020072040111080406039080c007010b4610ba1b0944450403a604000000302c0503219105504512000c0c1c080c10100701c1c2d80c0600210703d4001554188070240c0483d580342014441d12044982003040c0343c05246580303d0304161507540701d2504408001081d040605240b00303451600c41500d000c04c43c1410242c60700c070b40a4003c0761807031311482d54104040c820800c025028901e2403001261001605018490f041000c90032500309442082112031f40e40300545000040780d1080349a100382c14010007509902081c01808205c1c0c4180d1200c2d10940c207030b0401d07809001a0040544441180760500c0c44401034880100204200050365580103d18480c090340684 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 821587733 1250 821586483 821586487
    0x510090e19030c03090801231305120a0e1002030a02010506060a0c030e0a05121f0b01020316020105120f0609010b19080a020d060b030403080f130f03110102031006171b 74
    0x4e1500540c02113005041c604000c0001608078004050b0045400c00c0d52a201d400e580003081e600c0e02040d44024425030014050140c683c10070580c160180e020001503014842c503a0711203912907890100d0090310070100d40296949080c00c400080c00c6a00040020348030383c406000004c074440e8031458401510380c4c14145812a0694000040c40d8441c41b6801150b00c5002155030080c44003011468108019000302c020700b610b28486000c000703645080305504c1c0180d2042c8034004064118440704e02100f4010b04141e860314840140c4c80100300700c2141c1180341040528140800fa04041d42c02a00401c4d01500301c43c2045a89184103504a80070310400d400c00c002c140225048841650484000004c08402004a20359a04a002d0107400c1100e054010862810015075031540c0301c282c50b40300d407070325482d240850311095880c035070481a00c1100750b00f0811980000000804244010b601a0b081c18203492180303494104020203507a02d003064220300248005c1405160395040100d81000d20740803041503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 821588983 1250 821587733 821587757
    0x60204120516180f06090203090708011103060114131214251806051f0f082a071b1404020f0306040203180304230f090109020903100510090e1903 64
    0x44e0241806030080f42c0c54500c0001807040802c00066041d0407200040e0003442035056150804503180011a000d5012418a800034019030070f0480042c19a000f5000b04002403944a01c81a1131121603820101c82d10030901e14080301d82d903c10070403001c1c038900144400c40060b000130200700404180e44184030b2000020041c180940015401c020301500024003054504407910801e420301c180c01050020201d040201c6003c001481050212311858120380509107500300c603844491070541c2a800c007541c44405204610016005d0120310741900d40d01d9000014840c01c003401030b4004840d0182c80391090348104500c820481d44441034a81c80401110010b8490b9903000103952141c0111000603194040050007190050b1040800340a10400c0c080749038210514800b4440400118024264016049001080301b852290010304407000050182c4040341c525001c20410b8900039180404042101c03842403012142a10582203c1d2140b100101800e15041c001011642c0c00800301504000d646010f807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 821590233 1250 821588983 821589011
    0x30d0e010e030a150c080f22030309150c09080a230c0a180c0908030702151b03040306181a0c04030c090905070e010501090504021606020412051618 65
    0x34190b00d4202065240650401820743d00402481003440081680070000c10000c0342440c0d411881028180e07520403844540b00d408d2450702007640000c800f01a1540308101c0020301c40c40200c80400d00c04100410021a41040980301d800b82e5000035025600003806000859101c10402c01c4507200110b00c03542c3d40c2180c124207420b2000369035400c0c2d00019582d000082d4408001c3c40d14042180100f010411a0f01c4d0820841d0869024400c46803564000d21818000d440c21412005020120120542c17418402031050f494091441070401c410b43c101007010402e20400d40959071002040201c3c202100040707954120b60b83d407810002031010506a000240110001307002c0320055a00280c4d032030845075988031498050002d0802c100c45a0041c90f40000744a2216403016040c1e6005844289901d410130081c04001c0d00045618428924541c40c4c89001c290644020009441d40b540c01d610b000e03116041103442e02c14402075100c002600c91a04100100e084040010000d00414010622500354000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 821591483 1250 821590233 821590243
    0x2160605092d010b1f0f020a0803160306051e03061008030a080c09090112050f150106050f160b101409010b030402030f011d10020418020c030d050403031a030d0e010e03 74
    0xa1a070041c1c00c489504903119144001740c0402d00041e9209000380116801c200d80340e44c5281e100400036203043c80840d020440300b074181c1398078000924002a005540f58005080c0c8550000b080f1f00c2005030210701d0700203040078050194008103d024203141c00345440600ca03500e1040000d5070081100c110080b402c1c040c04901110300407000240391420b2942c41e4207a20f00f1660820030b0880d810701ca543d84107002054045003c4041c2c0c00030f1400d071002d0368a8a002960036030700a401c0290040b208014481c5249100100130601500070b0160302440d10304941100301e240400d800484100701400b5a506543e40c0c1c921140d03054802c00500551291502c0c0b000c2407a00b9620b124004a550070400448031001c0c103185101801c059481c2100d88500d01001030108a1280e03014003444816900c100f1020300040d50003c00e00343d1041c6c021646400161941901240c0007603400f00c0010b034684142050a02c0b28402d050034040d002c03006490f0b61136050402801da000e1500e01c40341070011098500d8401e41c3d080c42 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 821592733 1250 821591483 821591501
    0xb0105040f08105a0c091707180e0f0c090a14041101090f06090602070e010e0601030e07050a060e090a0c05120c0d02160605092d01 58
    0x16040741c00d031078844540d00d50703e00b10030010303010b072070700300e00300114490411840d144000c561180f02090540c4ca29482c4003844400c0d003600150302c0c0003011480c88901100310312051844640c005942405914002c0c10006182d100005011103940c48102d000c0d0045505822200030314590724180140c03507105400b030a4003507100c501030b00904120020008010596020419085034041116030f0303248089804c03100040e01002090700f900000500250301c00759200381500c81414404080c65441407034000e506101d400072400155828030411800d501080440b024010300e000355030741507040c2421105408001002141015141c01c028031fa0b070101802404064031016100910150301c0d014013600c55103600701041e0061440c100041c0040150b071295105410070359480901c1c20f0b400c0884809004030103071000031498002c2004008000b004d1004060065001c1003030300b1982c010741428004c4510007061141980c1001500c034070795a00c4150b5400345104208140000e59520b070710310740d0041813241 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 821593983 1250 821592733 821592749
    0x70b090303091c03150e070824041109061b190809040209210109031101020307052205030105070818010618020d06050414010e070e0f040b0d0b010906061815030b010504 74
    0x20081210306c01c2900e083d1081d040d680b1140b42644401c480c110400c0f05050f5100040404540c809411b45001d4100c0f0300350724460b180c1c1c58145449400010602e621030321100c0f00b201d185240100a00b00244825144101c00000c04440c0900c591605801846903024140c0300f1a800a00c042c0b5039600c0321010751303a4242e1403014040045103500140c0c0280841c0e00160042103c2c1c040303244c845131050003140e00c11000769507400e080c1003200381d403001d4804030f8000b41008014640e10120329074509100f150b11a103000d9a40300010b0400e01401810707120700404444543c1d040c18000c0c0103c10800e1320000e40900728480040c1e0b03507803408144030010140303500001d42c0700c3e09142d00d00c406002c520041034180c0d8a5464904201c0d00ca008003600c42c62120f0b05010780280c2819024200383c030f000d502104008d24040d00c0504245076030758503014050b400b42c1005030760650360901408200ea020780b080d180f0012000d110ba40c0f80d03080002b845202c5c42d04c81d2103182010b8585070070380c2c13a50f441101650010100700c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 821595233 1250 821593983 821594021
    0x902060c1c12060b1623070303030b01031b0e06070501110c0c0a031502031e040609030e030f030403080d0209060c100c05030f060405040303020f0f070b090303091c03 73
    0x642041240c01e001000d0700140100010b490341031001c0c8960b0040f075080d10b41d00307032034500d0001c00101e80d00401041924904008440402c040700c5010402084c22400740c044e0518506500d8007408441120316283e040518001c074801800c800b0404030320009516040c0301031180180c4d00044c0c0d4902c100d9100500340d500f04441d0303003c000c0924025100b180c0c4003d00303981c2d0041c044428060f000805100207400201040a010b400f51159402181c00a403d5100d01540c426104c141c0450100207440485025549510f04400e1551020305020341c450304034007604213002c1810700c103a43c03400b442c003026002560000b01c00800031801c0d4100d840311503018100c0f03a221600c3c481713859280c1d10a204010f40766402c180075448020701c82c100310ba110701c1c0c240d5030141407a22040e05000007071000034011000d1660811001c922004408082c1240044801c8890303a00c0e08c06203424450340c9009001c800c1654000d005000c12a1004101004900c1c002d10302c0b01200030b044517048000e8098050340e903940c0c1c084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 821596483 1250 821595233 821595253
    0x9142227020307050d05030a0806060f36061b0307020d1203060b030f01120213051302030c0d2a0e01060c1109070f031e1109010908060405100902060c 66
    0x4009021903410340200c003500d0440380e0b0b450500c55040100036000304260003c100c201c0f10756028040043d0041c5000e04a1428a040100e10600b20f600001c6e4282d1400310a5820141c2582040504c0c0000711071301d40209100251070b008140340740138007104640d916800c0f088414600300e04005a880741a0024524001503640c0e00f00283e80e1126140031000083c1440c40114045a21108a03802901072000c82106680380035154101c0c110301e01d03400c0380e100c00c030b8840c1400e08407858060350340184241608009121101c0c410580381040244019000c0c91a984481010502c2c41c07642107603c0310a2030304003042e0040715006964101340c0b038020b0041c000700d071400803c166a0241280e9041413207012621410a030400030007041100031550100010311000291203003500c00e4008000070b0851a800203800d0705100791000170340700c0003030720200028400309866483d5a0f10083d208003d084200151801e4209519081e440d80031182c0b0940f04191114589021500c50504862088803068180c2d80c000359 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 821597733 1250 821596483 821596541
    0xc0507150507081908070e10080621010204050315090a140a050111030618060a06210204120209060d170307050d0509100b010e010504170a12050703091422 68
    0x42051040c0c0010317072240005941071b0040407156004c600c010504441603080130001c8425940c002c02094000c50308040c0002001c1640c207440b004690078000160319141031205052a00a08000300d131030204204060000031000841c2d17a0801c0e1b07422403c0d00c124401201075892074015499002131966103407222202562031000080c600803601182c0291500900200c4e40e9006107060354040d03406624a10704109281c000d0520344411410043d01140c201408400d58040b82c019601034034079040a100c54004500d411894640c0c8420201d4002a6440342525020132217441001e5a8046400010108000c50302402c16a032603096041028000d44c074020000d51348580003208442d400d40e00b0030690440b598003608000c180020306030b41c1c0b5420700389442e165640040780c400d12040c00d402281c0b02c11022540581280e1642e501d03540f5810b030fa440989c6002480d10701c46910201c908200c4840c2c42407140c1c1c424000c40410040140c42c04045a40d503a0210014401110350342d50401c800307505444a15 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 821598983 1250 821597733 821597767
    0x1060f0e1b090906012106030b10061407080d02040f170c060a0c02042c0706080601030204030c050103050402010e190e1b04060810080303040308090606010c050715050708 75
    0x10720200801c41c00c0714100d401e220705800741e9189158031068090000b0000e500c102803070407520075403c0b40084800e0380400302034116030040e00280d03012428402000204644592404024261868180d00720907102c40014428001d241d002861414005105481020309405030b41c0500701e41d400043c00695203412103450500e001d0208034550241c0c0030003d07c9468a00c0a41700742120383e1710b500c1c440c011103608101c024802c0072041003c0c0000061106100400040c1d2016043c2411001b010340b0b03810b000001e8101030005150a04240c010001840000c80301194002121000c3c2808102d907205c1d840140da0000320700701d1080d08402c1c001c0d0b0782660918840032410032902c00198042d6643c6070841402010b440b82c1514250880c000c01c02000803078401c2000590040100110659850321003079103074110391050f507082e00024040c1080c8800c0c07110a000da650041d8003404c206806500399078603d0340714552403142c40228001b03680902c03603181c000d1080343c0a85901c5104241d50b8410080000800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 821600233 1250 821598983 821598991
    0x21040c091109040b0f01090b0c0a060905030a11060402030c060a0509033013031106120a060e010b030403020703140c03150406140c090f0d0f050606150f03011701060f0e 74
    0xa906018030013440d802c0103e40703100c1c4028180d440212860a00801c13000d039501c8400000900c0c46044a030078049842c074415200380741d106a01455543c6040c4500402c1c100241d2114151500b1000601005981c0010503074030038441540d2440d00d400240c00e0669607402503018458240c09103284154841c81040c940b00d240c2070720b0040001d8130300c07428402c00c1201d0007a11080c01e03113045a00d4060001c1200510b000280c014001e0101d45040d400140e201100d1005036004503030340c0c0d1140d00500c000c1c0d800515607405000e00c50300150461525450096a441251001818100003140c101981180a0000452074680641201e0005625402c5820100012071f0140d032042d1408103207400b2440c04044040c0191080c0442604090703c050820040070161201070758401000c4002a0000e141d1045001c86140514080c14a503d40003003405000010100c40d500f005000b04803500c08062060166419a8000404014000404003e160042c0610f070482c0c0c0d0455850200055440f002414803481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 821601483 1250 821600233 821600239
    0x11092a1911101109280b09090c03090d0f09050307080a170a020a080306040b0406030b09010506151b030f12011401020304060f0804021f09061421040c091109 69
    0x282d1949116074122410301c3c0340b00d000c40000300000000e80c50405030a1422071120444485078104942480f5042001d030752000d54000000f2072980140d04c1c0c400d00503030b4408090b200552551400f80110794070b41c10605082c80030721100c14090040140326408030300142501030115082c1d135171a0b0010f80ea60703c01e00881200c010402d403280c3c0035118518001d40d00e112030560020241e44555544586007504000c00541e00540d03103407450311156aa078002c0a00850007000400080d0910403c0b45095801c001c00d05070160080021501006640000311549403603201008083c00d03042180c1c00341076100f02980c000a0400c080b9140e0040c1c907010685030b0480ba480c42600201d0b0a90000698903801a40300e1103000c217010703140c25080580110f41080d80300c0c0c1b0007441401c2c0ca8107001568108200707045c1f0004000303410810301b840099003180b002c000c0d10500c1d014060400d4040d10060314585110000b405001000f40041000c101501196401502814005203d04114505001c24030b41040c054070784 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 821602733 1250 821601483 821601493
    0x90613090e16090c0504170c0406060e090a0902091801060e04080405011b2111070806220b0112300905011107150e0a0f0311092a1911 59
    0x284103c1c00d215105000003951101d50619240c120a410b4000d0112000307002c5002e030030913030211580d5510440001d0601038441c1041c00d0074480500050200003040100b04901e810001c1000d07903103850065034004a82c5c9080d00700031030407810560141004d98803544400c1d0104c0300f0310003000031443c060015141f00f0703643c024141980c80c108182c04244014083c0440d078000d40c1c03114964820000e00e070800c00741828011065034207034002e146004102d91000b1083d810000c24848130b0b82e983d200785d112554128000d80c840c130980c1c0d21040a0100184a420400d1440803024170811110300c0c20300c159030750041822030080146901c030030f180030003802c420350006841e0300380440e40398041c05609008101420003480464240034901e9020341c3d5001100c420302c449640c0b4501c1c0b55840f003590501415401c51042c5c9810f10354074014101c20260b040c2e0314801d501c801c1c00c200740040900448240c100c50000c0803000000700e41d400c4001e0b40308888490301540a03005100340c22a4200c81c420b40703c0048501168 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 821603983 1250 821602733 821602739
    0xc21020c0114040b06241210080109020105040e0916140901120803070f020f070617070c08070605060a03080a0e0102060f011a070c0e01170c0103020708090613090e16 73
    0x600407400b21002400c0011401c080780e01801c0ca4a0301b803061204c0e803114014400303c1d101403e809a0001111603014449540802c0f40c0d0400b10320a040040c40d846001f03105802c6264006410380c020f0340129841321040e1000903600761020802c8008031003650811408842c0c03100702180140e8106618640609601e0000051b851580c0581c4115180c02403c0719042d610340040c129508200c0c40028011441140d400f540681024018540100b0403525001c816100f01c180b003094000004000700c003403000c40c00c104804580c001c001c0340e52071030340710740c0001c2c03140d80e1100050800c65454001401042011a04c100d603590060906041c1c3d0509030201c0b00316503151034480e4a036400074061880e549000c000b41d284900d0030903000e0000d2a01c6424206031190701c3d490401d200340707400d0740120b0900d0b5004125104031039081c824951000000c0ca803c0d0319084941c1c485034183e01c690601203015010009103ca44603090601110150510240900c84d94074003466803599030312002c00c80c006c11802d5031800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 821605233 1250 821603983 821604011
    0x2040902030112060c1b110406030813050f0f180c0d020708032e0603020a030b030105090a0c0b0a02062710231303050c071d01090501080d020a060c21020c01 69
    0x803c0d9810745520250582280c26914000000307045008603800c07640305c49e40400090b030b181002d040380c440e801e0317420000c40b4039003002c00c4480d10160410724010400301d08075403140d0721000800800e00c07001c044405a00c0e1107120b07a2110910510681002980c80441c40b0410400c02000540c05540014400c24404039034ac21040000380c04070f9141000716400c7da100300b080c18000d8014015400389030800080c41000900805e09541d07044959000e02c0e04405c3c0c4030300810162550000291246011381401c050a49401030354603c800345c0004400d0542e424204076040020607400c1388040c000054442c135801e481444e02c0502400d0701159000350500e01460f02d9404800c03840e41c07243c0e0700354240281e03a1029803001d8403594844c1c140b2803d58001c01c0d001144039103440d059410136000305016480107607d062101c0c001c662042e00180500d030481300c415030f55142d00003810b59215810000016132401c10101c159041100310f95150515000e081000000c2c0046502404220003041c0082c0451440799001c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 821606483 1250 821605233 821605247
    0x303020a120e220213030516170c0d0809120601090c0c030e0607061107050c100503060f120304080d030f0c031b08090307020402030f0603010e24090102040902030112060c 75
    0x40c1a4101c0644882c640c580c10103c042c0842c0700302e04190051038000f40044d1403103025000d07007042d613265000c41c507100c0924180c0c12860004020f100c07030340399225920840c00d503126007087e00440c0c03041103880c44001c01d210015088030038140b401084081c40e20a20340100340c40c1c02d001d1158210700751600044c28201406850780301850395065483c21281c0d2458420442c060700620740660f9259134480521407540700c040d0082075924018402031107800380f03580030810b0010701ca528003010054244280101521110003a907585481207a8602d51521444001d610313500445e8404511846000c860011107a0994404030060b040c0010502c0800c04064003074082d1203d108031009440c61400c107480380d41d07100360350710381c2c0280720301003500e10303051082d0001400da800507501e0600f0784079208240003062400b40703d145012848a8040c040404510360f00b2070701081801c2503035008043c10030018003d0780080d030440e8080c0c41d14a10071900c1c1c0d6140c6180000981005204441035482c0ca000e61107400d0003455 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 821607733 1250 821606483 821606507
    0x40c180812070308220309030b0a02270414010f0e01080d14030a09122d020c19051c150e06060d0203030c0706032003130201270303020a12 61
    0x340d20b8607075203650813240d03640001e051301e001010300d4124014403215010000c8000f4020b50f16a02400d0450801181401c0d000e0302d05002c42e48100085819001e4582c200b40d602c0000c0d1071001c4503824641e010030090500c582c1d0f880c46020018001040f4007207903615081c241c44001002124176a00e41c0c800d1540c400b5010303a001e02203410106010019071400c001103a01c600c40b1000450032200300c0c0d84401418070000c10501c04100140c906030380c0c01e07035005090514552020400840803110000294840320101c507814001c242c16074890103101c0a842044d0010319001c4c19000b0140b425007220710928010764070881d5250340781143e01c00604e06501909124002c0c10b400f4002d46e481c1c6004005a081c004a8100d0b01070009005407583c071070301401110010503141d01c01103410224810780d0300d011500c61a070800c1d400418814040e04100031942201150360a0130040d40303020208000c065a04580c0151034502c07100d50b1300120406034042450800641300c1ca42200401d0503059090f42d180141e80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 821608983 1250 821607733 821607763
    0x203030301090504150207033911010e03030301090c111b0d02011214040c09091a09031303141501030f15020f041e1509180b040c1808 59
    0x10006000c2c401c0c05074009500988078022403075001d400380070318038260f81003d1029000300d40944210442e042401c942e25400e00240490504800785243c4440704450403140e015140119910007180300d0b90050362003e00032103004080725101c0da9101e840002804119800800042590842004400c000a6903045240080310741c117030322000c0103051101ea440c800105034100100904000303d05503151092100d03078200382010011618042c101070680e107506034040d05825281810800100e503041000f40c40c05080700c84c10807d03a4455454141c610f0007a188094030071001030f0b0700001000203a8123b21051b60500c400c0d076442d21710800042c214440d091002a2002000821440000f168003192001111130304400508220f030400100c000303508150080039203034014540c01500581c203d10070740000c0100740c8802e540809919001040300d440c900c01c80000144442845a8030000c0d9001440f9034100a8010080030f44600300c010f2a50b1203c110040e2201080d40e00411034600104900c0c00e43c0c42c4034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 821610233 1250 821608983 821608987
    0x1503020d0f020f040e0a0c0b1e0d06170601091104050f1011011a12010b0607080a0201140a060314060c090f0d02060a11060c0307021b031f0f0b060304020303 69
    0x180c0c440d1001d09070911822688211410301c000100d540d03610a055100b20440001d044031021803415030411101a0020241003005020510320aa00301010016110602d0591034441d524090203601401c0d0340e0b00458030b0758034a14605c03448070f600028118100d0b5820107042c0b0050300c00e94040241031045000d8284c0040d68500d08201d10b06042185500190a43ca40a183c1030003024281d400c455102c8000910100380074914075a500d480440504c8048454008119202c034200001d801231290500c0205904008524402840c0c003c0d80401303410116002c496200389032129101000f0016400f045070345082541c142400c032880086c80380d10400342428614508803d01c0c0802c4650326030030310344950042d010030000300140ca542000d0001b0383c51949610700059221480c05043c900300415036100e5040620070809100d40c0002c0045550045202c9200c4a5840d00003090a00d9958142c0441300f40c0b2016180d41c0c0c3c02210b6020420801c4140410061041b1880c100840703807209440c040d505d5441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 821611483 1250 821610233 821610259
    0xb150a0c03050a05090a06021b031614060c0610060f08070f08060301020f070b090d021b090a022802062410021e06041205071208270c04150302 63
    0x6030008081c540650b04282d41400145c00c00a59241c82c03603001000143c000c503480304940641da1180a01d030b52021800380030000e1444442e00007005443c840c422503441d280c10000816200c92048170307080403c96058031010710380313400c00580404142c0714100c0043c6101d01c0300030910f440f6202440c011a4607945405000240c64011a600c84000c0d00341d6905542c00c000b0001d41e910500b00406015120720024291490018100c5052201d41d524010a54101505400c82d2181d581748003007401c44201d4a1500c20380300c002500c8028040d02c1a00da0007440c800c901c606440c51010246420549245c0c01c590300c90f951780c0c4014905180c6090706045620b0000300144c00c0d0310b03060048100d0b0b083e0705e02c1110108041e00200644802009182014076000002440140400e4422603243d80c5010300b896423421409035540c1b41c4071007074911040304106031803010851840d0b80d2911910ba000e0182d00308015014071a10040d180c01c10412914800d900c0d2021401c0740c04000252401202d800800040710002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 821612733 1250 821611483 821611487
    0xe070f081308160f0c140a06030207060b1e1302130308070f0c0617070314130501090210050d0501170c01080702070b040e011403150711120a030b150a0c03 68
    0x800c140c0100c5940c48144801d000c0c0403c80c510b8100c16501824581c440000941019500c065081e00248030703182280411100c19240c100248086a03807034a0010b85d00e000c58100000141016002d407a0b00c086085840210f907000d0800b50f01c801d5808440c000b02d90801920080220322501e43c9002c1400c0eaa4041040418904c40c06040720364011011085112102c0d6070302152852203030002c00c0891260042c0200302040210580e41c450300b5418104040280240401140a00140721490103d034074444541009001c0d001080c031a940645512541e001c8480c020b000e5070065200c040c6030a00d02800006c10b1a4460b00300c0d01000c500c400500031860882d401103a49941c010076160661040940001d44841c1180c0140000c0400b0303100c50010354100340290701c00b1305101c00ca07079110358400301144404156441c0841c0d003000142c10440e51400701c0070001070416a030000c3c0d2110348038001c41e1807405140c2640080110a10071902c44000c0c2003039801401090240100386400103000408185c0041c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 821613983 1250 821612733 821612761
    0x308011502031c0203101202060723101b02010501030206091917070f060810170c060c06010302030f060c0a08060103270b0709030506190221010e070f08 67
    0xc031803841528540110f0b001240d162245151520320310650020030030250791340070303124680901340c05004e9801c06982a00002c1050003545805803058601d100f0301c0c600705005200c110f00c00503801007500c03400485401450005c1a83d800d40042080c200118580c416206214950503280d004010a01345203412042c0200108a0840404110a01c070400304810750001c541e4568103861000904005081088c0c1070302c2900d40d54040c0f000c1c002c00b102440900c4c004070b0070241c20340d980104080105400d210066180800055078545c01107400100c11100300b60109003681030b6402a012034140340c011045042c2c0d00d810071940701c1e010300c50034001c11900912078a120364224005240220303400020000b036546070030007204025020785084900b40d0070001550340069000d103d43c10b00268191441d22842e84580780100003003640e00003e0005003038011564141c6080d8030602100c0e0001001c50105c00d07103550340070701484507401e5810000034a070302d01c5020ba5000d000400d650340000c80c0c40d40312a084000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 821615233 1250 821613983 821614019
    0x19030309020a031401060b25060209042406050c0607050a020c1f0f02010203010605040314030d05010b0304030912231c0302090f040902010203092206030627030801 72
    0x980c45200d140c01580d5500001c001031406000f100101000c440f495500b141e41c0c9910002e66000300307011a016a6503c5188800c20161110f28100400c0d480d1400314001c0c8140070000e07038880c0ca01485190759008020440c81d1354a81208845511500c4d25000d031000d014030322090a10b42d000304002074460b4840c00242c10500e45c64012079848a03607400c0068543c40c001d2250016800e13105292241207640000d000310400c10600086186504200300200317a0300c01c1b400068401c0190340490700d0f0350b000070422501450f000c048208801e50311000f6a00080d40291020b40c0054034000010610003042602c0c0f00c691540049400000301100d074206000707008040c0c00d00302230300841850111a20102280308008501903a0040c1c2d00c039020010007240020b03801001d40103a1822180c000181d800100b10382c00d0300001c88801e1a180c0c0c0074142c12620f403d2564043c0d9082c0c1c20300300000300f000a43d40001d1650340b08900500c2c80b056543e811410b280c40c007100d0180c00261708500400504074144030104038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 821616483 1250 821615233 821615237
    0x4061e06120e010f0e0105060907090621090507050310050c0d090f14071a03061e030f0304060f08010b1e090607020307030b071818021c05040b01060e121903 69
    0x34510640003103c1c00c40d240703c4d6a41a0082d00c4a4050045c00c0c1c0030721445074400b60450740079005082c0708000820110207401600140294034503a009002c04070300030b892000001751010320048005203070290b2546258880c2602a110300742c07804841b8180e9001e090301c42e0229900700d070f0901e1401e03946c0c0e9024016034081035803c69100c1e50310704042950003107500d5524000000400c0306526020724900c046070302d040451050714050017440030581d544c2c052480b6658010219001d40c0c1020000030741803040f40707140c0038580c3c48005000585150049040e04420906842d0680c140ea81c0d030311000000e00c46c075181500c0e2100482c20b0352270b68082c07060283c0304a01016080d40c0c00e002c0c1c03a44c04603140c400c16400c260780c03018001d41040001507000a0700700c5064a050b900001131031070003440140c805400f403808101550085080b07003c04256220055840303042c020180113904060070152061503083c010500040c1e0b038008200700c1420034071640f1180e15248402020a40da01450f40f050844000a044003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 821617733 1250 821616483 821616491
    0xa02072702090121090507050a0305060c090102011b0807020d0503090a030c0c1d04050d0e01120b010e0409121e050f1e07050616020c100f03111804061e0612 69
    0x340e8041e8251300d44600044014000030790034141e040852401c41194031807403049030100001c0c0000350f00402c0c8190041140508241c0314070001005074050590301c80f01c0b0f4a80801207501a1065500229590280c0590b03000d980302c4d000080030455080c48200ca075821180d10041e0744c0400684074201c00000240955010024907498240340a048150401c2ea00c644201e0b10b4140001c2c0041880070032202d5070307241410001038400200103096442e01c075501140f26695429021001e074040c0952000f00d00b40104104085046840e10800f00b80703ca07507680300003800034100311801034034141c01c0356900200d50f100e840c101520000e00c04920340c84958084180000c2402c0148004001005804428407910103013200d441c1207500440d2300c0703010100581c03c40d032121110703504540707500601500060a501d00050b2103000240250068054800c50000c168400100d410714042440360111044070116800d1001d030b42c3d01d082c02803220501c402e0082079201c140c4810040b0030b01411308498115044907001c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 821618983 1250 821617733 821617757
    0x519090b0a110c09090703030323010b2b02030f060906060d0b040b0d06020405101e1d03060a061802120106030e1e0a030306090c090605030a200a020727020901 70
    0xd04c0d00c0c201600c1120943d80804000d10806406004008080c40004213280322480211592481c0000c1840740c00c3d4004000250042e401e11180019884640201c040c140d88440d5040008000c1d4002c8070b102401c4241440480d1003803806405103405004000c1407a4241001002000028848404081e0784665110040c1c00e0315160141007601440c000d0300010b0721140390106114500805030b03a17483c1001850b4a1004180c0c00030000c24040e00d80034504502c0304254980d4016171804079a0403d94140328a0f410464416520b400c90b1003035400ca00b81e4200300b13168203074440f426402500c0d030007000d42d0713400c00060208900c42da00c060f03010b4074860b04445a082458190340d80301d045003018110f05402c9541a0b030700b8160540640c0005158500c0100119800309200407d030268a00414040100003c086a014400350b04102480442c0c04240380310744c0c60546c00020700e40d0144817880094011448009101d030418240503030850702d41a480317183d2005d042a00802503102c11145410f1000614180c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 821620233 1250 821618983 821618989
    0x60c170c01140405100b011b080a05070602130906060201090b0417041212021e1b01140d0204031112070308130b0409090201172206060302100519090b0a110c 69
    0x540c0518004c00140c02c0c40c440d00310030001990540040c1c41c0c1070204081d0b00c18110300d0709000003040d4503000280142c0b500109903042725a071081020180c10f4030700200f146007054a40f00b0450080b200c1d917403000c00019555800aa080e07509121010740303403010200005001c2030360304070340100310b0a01c034005502d01900c0e902500c0030f50031004003c0d1500c0400c50a118061901040403500c10041103c9403500405440051660f03901c481e25100c0c0000d0fa20a140c003001c4c1d001e400075a0303140d80d250100507103881094038898000d4029102c244e40201070b0764055440d900b0041540c041c07294510000d4118642552a075161541c00b680d000040d08882d1500000c04640700400340028117100d0201007002d5903540001032034045905403981c00030301400248480a11a2103a000d02510090010010000c650a00320020000c0d544065000840c0030300b01c0d03c145031300030000c1c51100030341d2407518081d494950303048070301e003200340240c104603281006811041400713103418605949040c8204c9041c0901c15001c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 821621483 1250 821620233 821620271
    0x11130e030a2d05090406050402220e090a170918060117010608010620030a0305220b0f04020d02041e060b0f0d180b0c030f01060c170c01 60
    0x10010950404508400d907681e12622400da0001da6010710b202c048910342590754010381c6060701d0001e1000003c0c1940880e211500050014100100215101c1516220304407507101007a1065864510440d130200f02c0b4098840300074040c000c18801420410456503a110070074001402840072210103002400445d524803103100d0180c0a1504c0300c017210b00309140050002c1403400700141010070740100511000364011806411038030280f4041c001e0a406401207400003800c980141e4040c000011840700094058201074024807070260001e4004503d2074101c00640f003001c0c4010f0000071048003241c01c00802054072504540001d102d5410304089900140840320403a40c6880a8100c50303544601d10031980c41094020031a00440925000b018141090503204420070320005a5031684007040c20315900c0c0068030790b0350303005c1c0d400c0c4114146119844915041203640c000b400d10420004a00c852184c7d40091802ea40018461404880c200980c5140e42003810b100c805036513118480c103114110224 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 821622733 1250 821621483 821621501
    0x51e1203071e1203091203050718030b010f0f030f020409080904090302010603050f01060e041203020717091908030901031a15120f010e0c031f060f09051c1113 70
    0x85010030020b142c500000c16400720450282410310305a4100d000c500304851100c01c40901d403134000b03541da80d00c0c013042d20007605a11440040388100d041c044200242c2c14026416101e0950f22420030540e039050081000a1502004100b144c400203008018101508200c92a41c8684042c50501250030302040489441280a0300140c0d12000100144002030042c41d0032501c84200078007455041c070080b54000c072009000140f6101039050240c0d0300a101e541910201c9a0040c000000c0002c0c41510032065003020041612807881620b400c07230192031000340041200c0e0b00030003850400744030380c005600030b10317a002c00070185000d0244566600d5484003a0501c26036440310720a9280c024840b1104100e500040c0000a00c000d10350040c490203c0e410f050f19840700c18030401903502d40d120005040080c50342040780680c0894401c01250040c0c0180d030004c5103104a503113840349503a03544100000140140c20303641100f079144100c03001250021014100c1007401418401041815803021411106403070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 821623983 1250 821622733 821622773
    0x1b0309210310090203090c010e031014160503010e1303020705040c0302120c030103051c020102160305030403020d140406051303230d020304150e040b0a0905010f051e120307 76
    0x7045410074082d20100060b002c07000c030860952074421304076591002041846414080c000c003501c00b15a604000c49407100e8010b56013401614010002065510001d4130212000d203140304500301001c4c8203030143c034120741085080011644034821210092000500c056045000e88080424181c0f07a901500b6900d1160307940c0180d5075a080c00e0401d80c1000040c0c07428034800010801040490400614200b805810709c0d00c0150317000604105074024815850a200305c1044400701c48103140e0000090343c07007a40a902580e40c0c00c001001c0442c1c200144800c03400902d50144010301034113101c1e2000d00200e1030201d02850420743c698031100c80c198009644181402c0140d070303101e05141c00520101e107044c4d10900055060504098a6219103441c410345802009002c082c21540c540d200d801055441c6409891402c8190b2a4605480a04400d02a00c0c3c0c0e6801035100004403030401c04071035143c2515414000641681c40700802c00b402040b844c0300350301440240000008120140c9842070062450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 821625233 1250 821623983 821623987
    0x1e1f06020616020f0a020f1906031b0309020d080c0a14030d14040506011404140a15211202010e19110609010c0b19020703020f070e1b030921 62
    0xc0702c0d80000b111800b0014119000340c10f46600c80c0c100011100d00381641111001003040081d07000c00c1e82040c081c0f40c00ca02240740c2c060001032150305603100c0800e200f0f284501500c640f420400940a03520540c800175002058007000314042545000600300b03416815080d20002c00040d101c5c0341d08144241d00e01074098000042d1854030b4240ca00c00c11821503c04030458680b864a61582520b5a80500c01d08282d046468020051592613510401404104a08400041c144080c04200414003071252b02c0c4c88503281c6002241c2a06500806074561080040007040c01c00a540e401a00c802040b002005564860724184074049017403000040400590710128440300c1c0e40c0c24410011204141e42c00d001d09410800c520310703030742c0c00242440f02c981c01080061440e110040c0c102c44030106c55080388001440815071900b01079020480c1030064814104650003151074030014022414140d0390101c034202d803418940350155808000c1c580c04540c0c101030300c2d10032001da40b40c442c03882c0158461110180300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 821626483 1250 821625233 821625241
    0x8090d0b0907050d080409050604090204050a20090f010c080d1b03060b1309021b03030709030212012310030c090c031407050f070203070909050703050d020102031e1f060206 76
    0xb04003040051804a50801d000c030200c4d140c4000b00c0c4075600a45c88555207450005201761220f40080c083c05a02902c100081d02c0c01c6032400d40240440e0480240c03040480c0c0002040b40700e04420f460700740d07200030581c0c6100300200c030040d9a0100c03a9081110004001d2100d00c0340311009200d000c1109411241c00c2513032582c5494018200d444070307000310b01415424400700700208400b000041c2940e82594005945192150403c010030400700601c40c8030b03100000030800c4c002e902400800840f4420b03100324087ca02d005c0609401d030781c40500c4582d81041e2080180ea00f5070950421940c0248503a8401ca882949903114502104550341040c2442d585990001048a5261044100b03016040f030b40301d007107810040720080c00c5129203821100003140114408040d540c05214000c01030840c0e0904000030801031904584403807642c88140e41c103004244c001e030b41c1d01d030060003100c4c411106440300014101c0101c504a00d5000050304920007410940810b1710007001449043d4090b00341c0790010507a0b403034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 821627733 1250 821626483 821626501
    0x111011812030e06010b1b01050106050c10050906040305070c0e09060f0708070804230124060c11090c070605090a02040605060f0315031f020d0f0204120b0408090d0b 73
    0x180e0000e0702020540f40c41640607803010007240d8541034440890740103984086003910180308039243c0ca110311865290034000907810b0b8011f00100000c40c82c1606580d01000e01044403c11902c040360b110055401110000c0d0020384650700409400e441800194050350715003580d030700c8010080720000401d6001c2800d0100204a98849551041e10ba1030461030034904160014030034480030380002e01000000c60f00c2c03c40040246001500020110000c00c071101c0c084c21403081f1203c1d940003d0200c068000e0020801303c1c071030301e01802800c0d00044151107072555a01401181c1c040101580300480080c072074140050514084d40b402490b0310b0f0002c10380702c1114010401200c5440e800030340714000400442c5207101118007501c4d40041c0415542030b0070006240442d041103444005400702d0111061280d0040f6a1680601444400032408000e50801111188100c0c425801070400491041011100052951000540c0188600320303d80c01c00a0b40f44c0444c0b8400c0d024201103900f00b1000c020030001d80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 821628983 1250 821627733 821627753
    0x1060801090b090c07030c06180503040f0b09030706110a12030203061206011406090f060c0a050c01180509041a091f181e080714160503100b01110118 66
    0x6041251040600c0c14401203000700d40c0b04801001b02804440c03032020081c4001c03503208841e80341e866401c0740a000580e1422a03101d502074080c451207030801100201d4400d10302d0041c2c6030801c0000d00100146803d0038400e40702194003141000452246810600c00101c013102c03096005540e545001d622070824400304142e90003c80d488c500d65502105c01086103c04980c2032030130080058880c1941c400320100850300d000c501ca0025900718900091500c4900000601140d180340540207035908001101c1c011990f0500a440100380c0e0000f01b10248443d1400040306a00302d4441c24200c03c4280c0b400e1045901d00c0720031554880a50044440042c011030b162804d84042450164104440815000705404000c02c2040103440354a455090101c030b05403c690b2262030350b070030252803500d5401618007201000c4131000b404186004040c16981c20818105a04069400c01030141c10740b4404054414003c101d201030789410000034030b4009440040a100d03143c0404000122607200100e0340c1403c081071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 821630233 1250 821628983 821629001
    0x80f0703021c081518091c0201050c0301050405150904060c030c0c0f060b01050f1201140d050604030e060906040f03020114040b0403120c050118120c030e04020901170106080109 78
    0xc2e421074088128035a881044294461401440e0010143c0740f1804203100c02c01c51098180083d020206002c02e2050000309032075800c0300c00c0c1c540c0315043d0300504120309860b41680c079132001c480e0510040c856071070030381c04c070a5000104180385090141d418000549900742030b83c0039200e4607560880c8d03182c041c2e0f140c0604002d0036441e05110703000201d50340d15441c188007000b50107440300d0b1b503a851580d401d80c4104115040c0d000350390740303042c0c48900146070105404800c2c406d6440120758004403c01d50304061682281c069003001c0505030b41d5480d92400d40ea081004019035078401810072110785240d56031006800946650341d10880220b007144005050542010b030030b1012030710240002c01c03006103002d040b1810340e68415080039888440002c2952501043c0d60020540d5007803007400d882525860410500c124018a040543c030160058141e03001c012850000d1300080503001c0c229400d0629400510382c155042c0350405411003940c070214103521007070f08001c3c001a92800100030044a03170280e6114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 821631483 1250 821630233 821630263
    0xc06071d100e01120c05090d0c05150d0b12100911060a080a06080c03120708090904060f050612030409110d110a0201061e090b010314090102040611010501050d030809030403080f070302 81
    0x102c50704007000f810074000c7e98085840740c0c074015400c80c100840841090003d020140100500064044855015400a10f0110100c42c903000c419901e41c500340420f0340c03000190300c0180c201040c9000b00840909245d0070b00303842c480c1d8400400e5405460f4200105003005a56550002500b0111580015110940c1c45006250700245213800300750383c0812140014000610165510b564900e0030b080030703000c0c080d44590702461201c10403003840029000814090102d0b0020061070740c9070b0082001d4071404071040085640244800c0c0400919503010742c940d8190100710300c2c1051000b0840d170042e07032003030b07001003101c031001061202180d9024000c0001034826030351002400942c0070300c4028034003003a214074a00240c403881c031b600e1103034080c1d403154121170701481e00280203143c0489030720b020398090b01c24840081c0c1d00d1982c10084103018418907060700c40083c5600040b0391301e51002c880001020700390460f07500040100000060102008100380f950f00b076101510340455041c0a400d1805221460750 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 821632733 1250 821631483 821631491
    0xa1d0105090c0901080405150406020409150b0306040e070e04080712090506030a111b0313090506130b1909060e0a0218040216050106090506150c06071d100e0112 71
    0x80c0742c065450980741440c4080c40c064545a0b0385051103450103001c0301e200142c100b01041400248141c0382c000b232040d81c41c3c19908ac001c1562071501e4041210941c4621000c820b006c0c40070550360300d0182c020489560704641101c4049031103405141c492501540c0c00c41c2c05050004940040264640220740030109904220940c42d2514002c00c0d01132000418807400d42d0398070414040c420040e01e06842031260500d40d0114141c1505110541c0d9034030001106030194070086001039868074074000e442c030562016045056441f143c14080000d00710403400f003540000d1800b21805c28034450200300c00240800403006c24410301d028282c1140002c080c2002c00d08500401603100e901010090040e1000d000b0f481c01a80c0f11140750700300441d01802e40c00180039500b000b0f00011a41d40c0c2d604182d0041ca01214550b10340c0449180c100380038071500500400f0b540101e000074090b14058816010f004260303a258000080c410400941c40510f800d1800001c01c03c854510044bc2d607112542012140030010204 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 821633983 1250 821632733 821632741
    0x22205011407030c0f05060405103e091306090614061e090604030311010c02010207050a0b0c040b0708030405011406030c060919081b0906010503060d110a1d010509 72
    0x1c4214461541e0140a0000c1800b0503130400c03044072040002e403070b00700080d03595038189440c0c0142c5481201c031200300c081d81400e050f408800d903944000701c901417903066007422440c2069071541840c418a550b200f0451402e104a1031140c4030031102c40b07540079483c040040c0d0b081c1030511841c2142d52a400c0742414050703060701034045803512421034085900c7c1440e903501907114070000c00c855200740100079401007004607001040540100c1280042072048000703202c03038002c00d81d040b8201d00585501a00d660301c0303281c6400205500340652a00a00407801c2989031603210011144030380d0040e44111060940001000203000084c400c481891181503042c980909000000a50316468480218401c4c0c0c80000c48404d150307221540d07411914031001c1c2c0721400c26500ca0007203444c0c40b4241c0c816880d030701e07003200c00a1061170001c0e81148116416121542103440300400d000d4100a010021a4400307500c15100a0036600e40b000200201822402003100720344001c1d00d1900b407201039000314042c0c00aa4140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 821635233 1250 821633983 821634017
    0x9060b03011b0f05120622180c08030a020718091a0403020c010c080a1b050703120f0c080a05070614040503130807080c01032a05040603111306030b03010b0402220501 73
    0x2040c0c2040341100c02d00d003075440740c1d450801f8403185c42d016100820b1401d0344040c0326100e8180c00041190190070342c1c80e61941d5071015036440b032154020f500010303040420144040e000d00030082c180032100c0c8800180c0c040741d9507540105050050191031840910808000c1050f030b040000c02c1090380d082c0384c054403524680c0e564109034003c1460681c103221240d08231540211032420319051080e005800c84e54000c0e50f034100200c0440351003103003c00107550342452007038040c0a0a2804516035100301c0041c03411420710821111600421800c5901d03544544104040e0403a54508600480c02000603696078903142c003000700407200c507500c01401074000e494100a540d01c0840d0b0310713844100c2804c0200e05480c081c80c150004025071802c2d000140603040c1c690b240558000003400c1610f495480c100001002103000b082203000380c89100700c84889540d42844154031a03080440e6a10002e000803605410160026040c1d8101071b030038400e0889030070231100c0c031030f23491410250090000382080703010f042e66901c1d8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 821636483 1250 821635233 821635267
    0xa1b140a091806021603140c0a2306070807020d02071d060a030c1d0709050f10020f101e05010f060327060b0a0f0605070609060b03011b0f05 62
    0x40301c0846a98060701ca510020494100c40200d900600840d5109444006034a001c4c90300c40f0207030000b03903860340403c00e03400c4400101e580481e8120000c100303001d400c0d929824520001000c101058464400140311103404229640c0204503e855000d02c1c0d240000c4024a80300403594400b085510100b410407070381e00a500c000320f042d0f100320f840e07403071035031b28100807481445603503000500b60714006000080c03058200d42282d10803c0107500b501c0b45038441060031181c0401c40e00405030f200458500070401d1345172248040d4003100450041d10701780306070741c10340070300700842c441c2c000d19082c1e142c54844d102aa0f1002c9404a12122400c1c00c00c059410100c4a182c18941e500412040c50350f43e10805050400c0c02060135242c00780381103008250400c2d03144c0f88029094090020f03000d4030414202060032006124030200782c4855603215414110381e601e903030303002d05155103056070f4195442c014490a85c4003802804d11031000c0c444404000a040f040082c00f0000000c0e0306000c00c2018032106030458110b441c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 821637733 1250 821636483 821636489
    0x70207050d151b09081501050f0402160204050106090303081008060112030905061c050f040222022a0d03020906040b0703050913050109060506030405060c0c0f0a1b140a 74
    0x7414070024621030303000c0081c03d24560b5009650400c80781821001da1010300c07070066816407025188110040014100340032801e004865001c2a290301058050038660301a000d10705004981c481c80140c1500070a04030380d001e07000b21000030300003070b42401415000401150480d429400700c6800507c0d1083d401d03190346042c02602208200080084185845501c112000c0c02000700520381c4c0b0fa1b03808001a103002c5148034208071240c240030001d02085145140c4070b10131a0007510b07207a4220008100e4070201e801e1034210f004c40e50341c240080460724402c0c40030344010141400a880e99607203104600c0f45411a4840c070381c5c041500400c0074030001d0721030006540880d94407607203036500c030f41d002d1a0580c0c490081564060704a910149c480e504d11400e6040b42d07040714060502004601c3d240c00074019588000c4030058160790191001c140b038010900d0080c80608002001d403600c210348420154101858000103542d912070740803c03030021a112034981c00081c4440d00004107180c5e1840089a20403420b84 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 821638983 1250 821637733 821637743
    0x3091208280e15040c060f18090506011103070506010e07110106080a0b06060a090e06010c08121602030c120f0c03040b190822170409060f06050405220207170c06070207050d 76
    0x401f1401416015101884230f143d0154544290140c580c09050020502100d0540c001007800f40f0010f0344031400b10413100c0b029040400f414040c0c0c20106040c4a01001800000401c02855a840c0c000002881805e0143c80d11074013401c907155007800c0c20703044010040c1c802445a00100603041c002600000725004076454141c038120f8580d5114010380e00904080d4010340001000203580b014140700d4846603102c0c6000610404030b140d88404126541c2c0207070090500258481161102040310f05000391000e0005409000d02d0800c2c0b544400b4255080782e07104814124011408018001c1c084886550034001c40c5040c40302407a00d152040100021100c0301d81c82501500e4980062020410080070341c00484c01100c1d66443d81e6040840c01000284651120044506400b0486503c00da04440450340020560031803085207030031215101c8025464840000c0d403c016030000142c1d000458420071054801c00341c0c440f152140100d0a09200404990854020301014045981c404021382c4e103054000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 821640233 1250 821638983 821638997
    0x18010819050a060e0c01142a0102040302100206011406070b0a0507121a090f01080303010303140717031f0b03070e01172503091208280e15040c06 64
    0xd0801ca4102004000090045410110301a860a1001507a802e107900d080c2d03514030750032a0010542d007240c00b8a41c07440b0240e1540303c9009030b0401c6801c001001d004040340005103032075a00d03070009400c40000c410610141e0040001081000314200c0481241e00007a07810313608c5d107a07aa681e1801c030f44000403c8001d000303a95501064565219286501f0108074a07101009940010b44003c951000d9001c0a584224031260000d14510f80c102c6001d8101c0350080c0c015030550342142e8054880a40010b80c01070300706414404040410011015000702910882000d0340d0f904000395040a8030892158a060b4020503610400440510508032603010000386000b040054110004032112250100d42c0303196500803e0900c6040c400b03410f000c00c42d40240071079080c90001ca54100741c06560b41c0c205c015101d06488007484030a1801400c0700340d81701905003c8003026441d00c400850854104403803001c1113555030204012444401c000e55a400030b04803440c5216880c080d540d0f401b541d80d01d40980000c001003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 821641483 1250 821640233 821640283
    0x2d06030803061e0a0f150309050d110f0d030630080903121c0506090702060c0a0e030604030c03090503031c110405060706090204061703180102070812030105180108 72
    0x4856180b40a00c0002801111001d5a0361300c11207905c2c10038015410f070040540200102e81d030181c03044403661030b40700000d0038040755688415100f40b90390595038109030007005500c1415030b005000461020f0740316200000d0007410101c4c046100c00c60034420f0751613980e0300380c4804031141018401d5542264090fa103d50b540c1101c0380880c2c1020000418100c0c01c030320105e070b094a217030107400d502440b41c80719101c100a26584d0340708104000381c0c140d13900000b503082032000c035880300c1c030f440b00409440c1107904120312190800350100340342c001c007110140c0008e01c0211090741003643c0000c146000308001c80003036040480190700d02204050702c28080741047d60b6401d41900c480900350540d801003c000744025190112401d000001d4625000d0407803040d072514201003200d046042c0024210350005000314140304884046000d460004800c1c241035100e40c000002f21808104400359400401c00b40103502c0c0d51501d001d0041c203410303d40803810b44c2015a0010f00c101fa5000500a620040d43d50350036074203043d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 821642733 1250 821641483 821641519
    0x30c161a2b06060302280c0803131709180c090d02130207080c070e07080a05060114030106021b0907020316030306030f0c0806070201052502030408012d0603080306 72
    0x1060700d041041040c1008000203000740c043d800f900d41030611039445030860000003001c50302507140c1c80418012503543d12403000401d51401c003840d8419005e06c40105450801d858204610780000d40a092554000031482c0c100c1c18079a5012481080b8054000c08505220540c104c05010b441d00ca0317405114120b00c042e09568800a5000044114200c01c55a41c012814100600da104035208004c038840c400001807052603400103c0e1042120350340700c045640b140c0703105401505014245a04100903205d600e040040348100a6008080c1900100000102d041c0344030740c00c01c0c03c4045030b0f01c203070b0418080140c0c00d50040129560000800c14100130603a0b2403074141c0c02080c00b504040c1030745944561a004000e032048c400e0713058428401c200c45450751405801c074240c1c3e07000c030f54118000098100c605d20380e11207182d1940b5181e0070303801030ba81007a0302e4500f16400c440312140351101c502d13210052248044001803594100c034220080038005a030554450501c0703488050412400f41d10010342490a0403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 821643983 1250 821642733 821642797
    0x81f0e190c0921031806021e070f030204091103060127052205070902040308070b01120f060b01022a15030405060403051305040c03060302090c07020307051003020c030c161a 76
    0x13000880e04001c207940c5406c0000c0d036665601c9040c1e020203400d0176140811110002c2e02104680c100711410844600315401e00c030142c9400101100c0300c0d84107455404040c0e500703118150103070030b1400407544585085100b0300b035800c04002e20b000041d0b10b07003010b01131100340316090a40f002e19480841c4812040502e0704500c1d1007840c2d80303c00201d61009c20044200140280100300c1b03180031701036144250740c0b9020200c0c0314094080c4010300c0525111070a2000441d41d0b0090b030b44404050050b50707010b0000c03503003001005d40c00d0960250702c4050361000307800a03c0c04100042e491008280102d0070341c90241e80e1701ea92420003800140902601281c03070440710b035080b0620b802504020700f09220345821504c0c054007805044c08100c0c4a00442800500c41d401d903c13064455984c0c00a0051605a02d480140203d0301c400409201c105034081000000d180710030070040081c200214020a00d8002c0c05009081c140724941044440000120710300714000c03540ca0644a801c111082100d2100024880b010111 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 821645233 1250 821643983 821644007
    0x61b070c14130605030a02010e15040e04050f03070803043201020703020d02030c0307080d06092d0c0804060e0705120d030b10081f0e190c092103 64
    0x1000400c0041100c0d00451111680c01c0c005440d000c441c02c88000c0c0d49015201d05000300c07030b09a80140d00c460007542c4101c0840c04600400742c414007184040801024030740d801500244061050078007480700700702c02000403018a000050165042485560702c07005144000380010346028001040d1164015801c030029500c1070031207800c1c80c0b400340c00d00300960207504040010781c094054107185104050002c400c0324420b2105c04061440c004280d0754051040c2c005c3c0c00e0000842d42c1e1680b02180081140c8203514a400d1900000142100405003604c50441c44000304800c15050907400c10340c603a0001c141030b800950091000ca015203490048070300d40030301903000d0f40d130200406040d100402c04c08a0b00c0c004c40c5015560602450000c42c0034810710400740900d400000d0202400a00c46911142800d038a5a148031807080e4030325a610b45940020380261041005403580101d45900c401301d038454404501c1841c00c0c2054400d00c1e2540d40c44580340304030621400c0d072141161a82c209407040c0b66040030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 821646483 1250 821645233 821645243
    0x6062101120b06040c090909170a050408070b090105070f0f020d0809121207300806130e151503031b0d020708060c0a0e0913020406090608061b07 64
    0x2156959041c03038560054002000e661074000440441d030f507030606004403070000b4001c0e22002a198a00841c84004102c555000e880c00c80d4103800b40076050311074100170300c21103109684203511642043c03040b904000c02684050b180b098100f000908030b9820106440b0560b400a0b0075038402d1007241800584249000d0009500c100070f45840410003c404026080c01340d825a4109101480103030310030396400c8082682c000c0e051f003c1c00b034000042c10105500d2400c0040c00568010000300001e0006110f8050000c1d0010440d0fa41c1044172a0a020f2040c4a6040000030240301100382d0082294442445504600c1c2200e51700000842694904072110301c1ca600207011039950b4401142c2e611000c10002000c42c05600401c050044058400150340080c2d4480c0030203081c40c0c0e190b610800400354010300000d01840080802d0055556071500154442e104502c06174085410510400007141d140742c21209107649090801d00161000090080e488041c0b040074160303081c2c070600748400d5401403e60080c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 821647733 1250 821646483 821646547
    0x6010e073e0d03090b010503010207200f0d0b0a18150f24030507080607052d040308030703050c16110f0a030507090e1b091e0a02091201090b0606 64
    0x842c0d164958071100343e8a00480c8502c040d86d0301c8074201800d07445915000341014181ca4155444000600c400c2c96201c0c0008200c00b102c4010301000c00c50702a4018415142c0c1c5101c0c2c8200705604c1618001ca403034005014040c020700f05001c0c0d894903080c60403c103007011400ea4504200c140744540703070301c468001c4580e03406403101041d040005054007070081c001140d40c3c0c0101040003c4980c000039120380103c0d1241c03100b90900c441401e0f19003000f9401c65034000d18003914880303000004004801000951701548190382d03039240c04200034059540142043d0900343d01001511403840e4000c0c040000c04c0c0c1d009800450120f00b00c0c000404a100007510720740c1c070403c0000000200040002d9081c100c6410318018441d0100298002d601d904c1c02d00e551064000894940b04420300e0040703d100e610202e00c03021600c0341d044070307949020b0f03028040303825100ca6540040c1c014031601d03041c202e0100c19200030000740030100080d90341041c5020007503d554025000415000c40f5001030320072a0307035400e6055000c04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 821648983 1250 821647733 821647753
    0x3050d021c150503010b030109080726030c0301060807080108121c0213081605130b01020f060403080709050a080c01081806090706120c0c080c01180506010e073e 71
    0x240d07001407503c240c521039880e080d90b4500d01e00707041c09009150f81e0452403280c03c0685545a649481705075002615044800c0012030004540d013101940c01800c0703040a00341c50b036040440282004a000d041d017400d200d50003004006140d0005a01c41c100d0700d031081c07120380b18451858440d4007540b2803500030303080c1800420720701d80045400c00d01d00201d580c1c0508841c500e03007a2002510ec600c289002d0b0703a4010000307020080302c0b407c0e150840260700d0740610484105d000d1250000381481d805880440000d84050203000405038002c084401516003142c000c001e26242080d4140d450241d00340242c1031000c084005030000806d00554800b9210020a0303901925005502c0d64070342e44540110000310b20a040c005141185a108060343d42041303455103d40094651580d40c0c1d0381d0070928074060a59210943d469042000f80c1c850860503218070001c14055041c0000d81450000003070460302005800840c00740162070341c83c1111210f166400e207804040d000101d40c1404240d103031483c0340b06442800410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 821650233 1250 821648983 821649011
    0x6090a180911060403050705150d020c0615040e0c10020a2301112b0615090503060a0c08160207230a0e0709260708160501030903050d021c 61
    0x24a01d40c1e1149003212045403a80080007410b020300d01002d041030740305041c00c1c0150308080703c20010798121301907014108520041300d501030f03900ca1000480c0a800242c288541014603046404801500300c42c280220824811056a16295043c08622130038842c4c4802d050140207000030302200740c1204442126078000c0000a0f450f0b0b40f4030000040540c40c3c481000a072107008402d40d004000c0480700b440c1c01141d00104801e2840d0b514144440076070760742074001400c12408181000d0071019403104c00001345008205400c0403001060081c50307604050f45082019840041c0b1a480780907008105030489548004928103c1540c000307021458641c0348070742e83e54100c20b849404001c8112081124907440301290426003d05454540100d40c0049080c480000700340c158414003602514080c3c041940522814070301140b80d07200c0c032300c0344e080f04580705030b0340181c4034075035020b05020b0a00380422a85603038001c01c40e206260349400b0b81c6034003042c0241b4284034600f10001100c0c0c05c20041c0480c508003064 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 821651483 1250 821650233 821650241
    0x1710080d0f02070803030601090303030213080d211b0507030315030308011511060a02070602071a04021203040308040b090409120519090e15120d03020301032f06090a18 74
    0x81d80025200f010000190403000000701ca10a00040c2c0d02c80903520301c2c40c0c0e0180c019400c00034840303207800a610004140c01c8010032000c801c0e180542c2d0785040959400010031030242d6031004c9104481c1c10502d040400c0a17840c84034040005407458026592040c1e803c04a00810340340134800b8040112100001c281540120356605031a407800e40060741c41d18a180a907031660642e0040340c40c6410040c00a201c07900303c0e9000c0d03c07403039000d00760152910030b883da06d407040c89400b0201c0c1c80710303a80da642c01e00041d8100841017006080100e80158606070a5480d140d0250040d44500d049040002980c14200d807215017080d42080d81c0a0295480482c8030b1070040c0064000e081c0f030340400203083d4000d0031503c0c480c03010001150fa05070380c880031640300d41402032a50030341117410b96080050080008504181001142010200e9982c0140c4079419407414400c085500c004081040d01e0540c44003001143d4040d01040c0c100044034540c0e84d503280000860500c58075a80031a40290024202450800041e08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 821652733 1250 821651483 821651507
    0xa0b0a05041a0711060a09060f0c0203061807060912021309140703020103181e0f140f0106050103060303080609100503030d02030907080105040507030821071206090c1710080d 77
    0x4d510200b084082003440514010208510005900b400c400c00007103001d1303814850302c1c400516143c12003181c1c42d00071034035141c402c1d188100a030380000c003101c510a8003881004003501c0f40e880c10844092800c60b0b00d11900e90492230103481213510040465030140c55134400c0c61842d9004d030b4110b8070009403a0301c15444100510080c1d0220f8200001d40c1030012241c01a628496844110000c00c00201200e004030b0010f980e10459030a400d0b103504d03101041d5088644244100040c0040c40d101000d40a00ca00f034401581c01f040c181400c00d04180b0003c1e030000c1100f680407105480c042d913036948080714007280448035071015400d03000010f0400d03e84105500150320032094201102c58450342c80c03070403d08851049401400d5600501c5040c0001504980201241100301d12000300c10384c200c000202d5071540981c0d0b000041070241700c040b00c2c500601c0c010040207002c9110100400c2d182042c01401d0a0481303070300310380c00c0380b6034100003080c46100403444009040000f04450010a50803c00341c80140404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 821653983 1250 821652733 821652743
    0x120a02030d110d1802180105060a0809031209280809090a060308041418040b0c070312060e04022d010f11030d0e0f06070e010e04140703050a1104050a0b0a05041a07 72
    0xc03c4604125921000f118100d8030058070103490710b111480102d8044c80085c203070b01c0d0b335800b0810444004411080603240075980b00030107011b90042440c101b400c4445170810807400600b40c1a090008582117000342d406000098580071129540c04080d9030040256410081143d40042808605849403070820703004000d044c1c1c0c5004580e0805014440c0e400c0c42298000d2074100b100f00041c2d5046076202c0503040040c42130400f40c0d000c2c402c08803c40280c47c281d8001c904015190300070001545010030040740c0c4c0f4010b000c405041c0035002400c660304444e220220b1fa05001da82600d65465620911a544400f101d9405407901c415603030140ca809400e84030800c50a5214034100300c0041c45010600078040c4010362181d4510428020042d24480700b0a8181503225640e00031650007409120340700344c8203680c59540012949001d03110881190800d80e07030280000c1e81071105125a4541c1c2100c841942d40d03503c1c0d0f45881e111840001c46280c400c94004e40c0b800c2c910409002041490309000d44a59031003a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 821655233 1250 821653983 821653999
    0x170a0803073b01021e0d0c020a0e040b0402100e0d1403041a040501020f16092a02060601091d011205010b0a0303030c02120306090a0e0f031308120a02030d110d1802 72
    0x610f1070140d02075000d013a1641d10342040000da86c01c02e000b01c8060b06907a102818212105030703100941e00d0805000c8605a9108450b5410402149032041a107244010f9905041000910070301c041890703414185030092107580d090302200d5100000b0015140145034241d03864641c80c00c1d0400c8105542c001e4840e01c1e01501c90988404503940c40400c910712a4a2240d6140c104a881c1840420281440480109680901d6507130302550628450384c1c81d00002c143d800811440c06c0c41c0c40014a500c2440e440042500009009020b26101944426044441c00b01300c0d6041e80d1500d0405c14010044401c8003603125120050000405030145c010b0402581d4507000c0d501003e5140440304850f100480e2881c0e4403c000c20006503e102103507016945211a240c04c032181d5070071090404c2c1c07469120180d42c40c146038610600300003074001048182811904420641c1c10820b402c2400380d178a000b81140d1112058480c0c40000700e1380c4421040d14540300301c00340284022080d81d440c0b800d0841001406078051014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 821656483 1250 821655233 821655253
    0x30b03010e2401081b0f0d060510140a0509090114011509140d02130f2324240f0403060f05010305030417030912010204170a0803073b0102 61
    0x3856450324102e64207130780545035004007406400940700c00440042c0d4040c0644a00e0101912010300098485200f000d0000e907a051100002c0040c564560160400c0c20100041c0481a00e40100d40021158255250344460300d070200fa41c2d0141906440c9000180f15510000980c0d4803501d8840310340b0131490b103800744450344596200c407002140b400415003100208506c2801828019900b18420010100005002d00c500120310103441a0a60b442c50441c03902101901d0351180006140d00807001c0c1d0f028a10f542c0f04031107200542c03082225028450f40601e80307a01c2482a40a2402445000c08007038240c1d02e5118041c403607420740040c081a00e4951602402284000c9148074003416280c02200030b40c10b0614210070f80e0842d403039101d17411046001c14000c004464852010358490480b5141c00036841b54207041280c3e03d00700c1d9080c49540298000301040f404640e0b5941240e801070807615004004007000c00d2003000b00c1800348126048250700e44c050a14a007000c580c01101082c0c06d0382600c8120719 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 821657733 1250 821656483 821656543
    0x50916260307061e0501031e1a07091401020105090c010c08040b041d130302070b0a021501030f0b0f1308030c0c0607022503031d0a181b0c120f030b03010e 68
    0x1009000042090a9003002da1440c040c09102d0700075009c0c0310700e41c00d252200b4454881006440e0542d152004500d442400b0300c0b4910500011051091084c80200800d103043d008680d6078903640c840c200d06110388511590207200c080c40c01c03135024110620b601541e80f50383d030b21407010800d080303c1000203800e200000300d514021004100b1800c03642580c0100340d01c1d400d107920005260711210381c0805611544d0442510010030101c1580254080c80404840081d40d04044001c03100c0200001c042c0f04511003004001094120209546ca4114000d162a03968200c11b00c1e5080c41002111040d5124050030008040c1d400941c0001c8207161540d00420002081425402c503951404010082117825180e103916400c02c1c2c69400703102c0e00c0102070126081e40d58880c10080341d00c05030000042a2a00000316640107080100714000769185800910040703191144604074141503980301c1040700452090540c903100360003440290f0b100a008000c2c8452020f01076940b0912000300c0a400340d14440a048040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 821658983 1250 821657733 821657741
    0x9020d140703170306130c0909060b0c060106050408031c090209131a0705090603061c030504080609060103030c08070c0f140f0609030703020d03052704050916260307061e 75
    0x180e010f8850f9064140041b00c66001d4082c42800354204503c1d0360b4009242c09040c05004005d1078104072042d5605040c5000c0c07421f00c00e050b00b2600500600308010066030070000f003141d59140302403140710bc0601013004107201910170300d500654042c2c820010320800100f804103480945102e214034080c0c2003007001402034510307422550340e404076100b40500135483c180103004661000c00107152024400b29000301048003420510b00f0380004002203418406083d042101580040f00100140410340c035654000f024102c804100911000011414004003d0700d0f01115010f800e542c00d41030140c5894120880c01090294016841130b07000044062180c100001110314000019000e01502800c540a1201c2c0000204080301084010417204513240480c0e000c076a0300f503100c0145910070b083c014080106807880686120810341040500850300c85482980c00304440e41c190400598515503085694200d0504444030340da4000001d11004101859000701d5800c031028070315400544c003001c1030034112 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 821660233 1250 821658983 821658991
    0x60d140c0d0f0c1b062003041e260c0703081305040515090403050705031306090602030319150801020c071a030f04020f060d020a08040b06060a050d09020d1407031703 73
    0x460500f00c55145103012038130080303040c07a0048001248040c03000b4688120940210312600da003110100510003000041c516080180c030b481045814500700a450b03040c0e0354040322201c07c4da17105c1400d209d43d56080400e001d44188001c00c505980c0b00b56940e04142900e0b900c6962112503107140100041202d1a140c4a811301843c062207201b43c51110700c5040c850605c074080c20990510400348030142c00a9004c00003400c805480f0748242702c005241002c00750144d10f803a0040c6095410600400130754503005459444001859140800d446c241c80901452004554001c20f04a5000065148116900090b51022195400c0c0202640c0e1203401a42d8130300c3c003042c5e685004c14601d0304003140243c64500762148044e40c00605251602c0140d282801c00ca03840018003501003500d4008100501010b00002580840b040e50031514000607400024080c0c031581180c01c1c155035032400c4140035925110708040c1c860380d21800704038424403002d40d029554079042c4011214204010a010861741c04041500d0107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 821661483 1250 821660233 821660237
    0x609070f1512020c120a0302040302030115080c0f210a1a06010903060b03161203020d180620070618060e060d02070f02131e05070905060d140c0d0f0c 66
    0x600090700c2c0207076001d03002c0c40720548a003841d1206a0700b02d86004000300c8410f80c4006a9a40c0b0710302c14503081d80e2898610a6401c079540008104d5180041204190308504079926256080e1a0001442a2001ea450703000c2c500f210380080c0c08410800601d101010340600030300221040140d51006010300120b810a000030346a080410015119406c10320b1285e5000b0280c460004401c40c02c4483d50609038081891912501e80034420b042d0140440c51200c4210f1500e04084a103044814540f111a88140d4081010400c8a5104040002d007101e802c0411803064603041c1c0e945100050610000554503070361641c5070900000c03002d00071040002004c40c0030700305509144020700300780000c0d0403100302a01d07030780f40c4c0600b000c005a44e135510b81c2a1001c1880b000041800d1240c600d00e050400300d003050442302e86400244881c858100780d582c0200c44040340c800340d039800403c000ca070142544290360300c40e101c1003505100585a444001c1c0000b038101c050100700742c02c00324a1080966400c40d0f51440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 821662733 1250 821661483 821661497
    0x120302071e060c03050d090305091305040b060d0c030510020901020f0d0210240f140f18040305070606030605041104150e100810020d0b090103120c11030609070f15 72
    0x3503c2c081c020700c034a480d010341841c80c04c0499810303c45083d1130200320110001500010740401c14074101c80009000703245184100550300c0c259581148605010305464814001c3c0c540081c200000245070002541d8404265003ca80d11180c1c64000303900184620b60240c021085843c3c000f580004821955a2881c1c2c01003001a0103800001d0052560460070485002a503120b090440b100c03101e4403004041034540c450b800c503c4e1071981800844070350104c038803a5603110b031044450b40c1d415903440da170307181029021490f44c1c4131490181c90f60310500c8002001103046c448000203000301e03584814419402119038044205055041004a5600020700c8140400b00c020a0001a221000039079000c01e047c0006015980c5487c03001f4a06000c980601107207e4001074070100481007400351400b403500a0313550f9005541541d42e0b60301d44900030728410f420081c0860010050184003d04441d203040050190b0300c0d1814103665250311015140901048c0765102d01000030945010030040301c8207249592041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 821663983 1250 821662733 821662739
    0x307060203072f06010f0f140103090209040f022b060b0109050607060b0f060c0624040507050316050c0c01081003080c1c2c031204120302071e 63
    0x3034002400c800c1c200003d800c042245608200e4800d003900d8803940c0a0140003030034101d50380c030344a0140c0281c0c84540f2040b03000c002d0101a403480000307803040702000003038540f09003004074007c221404c40654001c0300c10091100f4402c54040560380c61303000381c0700c6020540c0d411200d8200d1108040842150341600c1c0d10500215440ea4031462070f80e034051408580c082d60b5100050b2950700100400e1b00c0441e070f0b40b42646118a44060407180f104010741d402414030144020b144d071035120080c005222501c88424404074500c01c00071078171042c0b000500070801810700e81070080641c0c2007120f03e58010a004800e03450b1041c01201a104145440d00041181000700c0c80110307108140a40320b0f0501e000134880110005180c0c0000c0c018881454006004031002100c0860680100301a200180b0100307945050700c90744101003a4885c0e5900445030410700c070a4201003454581c11031401c003281c0c1408500030401d03402c24648025880e000368215140c0c0ca44907600d0340c0302024031010400e00200d00711010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 821665233 1250 821663983 821663993
    0x40c090f0f06090e06030a0506070e0301060e01051f14040f050301050f011a070f29100303390c050406081617070909080405130b030d2a080903070b0a020307 69
    0x135500c07000250540c0e88042680d5542840c01400342c0c0c119010900219980c18a81024443e06004141e55035000c0c50315450500030440305896585480c007140405102003c10314091004101c0c090103908580342c0c0c171a50788100704940002030050921075401c02002c1151201c21180041c182c07900c64404045a10f255040788216601070082112920300d855028408034406444120307440142d2030b840154011010125581c192006010402070100c0030414000700f6407102507648000c59040383d4141102c17a040c070605a482041280144400c00f446000c0108500c0a6800044990545040c8a003640742c840d00740e1a18000029820300c51032611080100008640030301194060380401c0c0c516168844403208180e440012041d105400001342c20031860804141c60000050108030030410800e07a1000291600641940d110410080050581100c0d200340c45860001034144040204007481c1d04d0600d88503000b545000b0b109029612000403400034900480e100c0e041c2941c06186042016514 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 821666483 1250 821665233 821665259
    0xd0c060509010306050909070303021216030311040503060403030c1112030f04030311030123100c0f030207170f120909040b0406060b030f16020d02030d0911040c090f0f0609 76
    0x50076042540300d50300003445072100c0c00c2c02406000380001401c010350440c24081e25044c1c20910f152703c0b070701003000072a122000082c5c1c078903240703540362a001c100c0e04500300c03c80c1c800e409030b42c010030713494040c4000380300805406a21101c0041e00320780302d01d40700021010700e894407400c040401c0301c0c1000c0100000b030724400c584c1d0380e0150300034802d050010f04804c1d03800405010790002d03000710b24402c84000d07600044030003200b0303150851002200c203401074403044c150080109241da40c00500c40007606241604040c000e01050024095454030302c800e48200c0034000782d40380004190702040c0d0140c5584d030f00c141c0d8585030490300200000b030f100c0d02d0f10fa241d582e00c5440c0d40c03000400c1920324582e56034001c51f01c0c40780b0300000c2d1300811200e02c10701c0d8181450500700b1160440031540364255801581201a070540100c1a01c905c0302d40080f0000701600c040c14284985801d81108507802031808101e00442600080401c040e07503070084d5480790301c03512101003600161440c0240c502103406524108a26108e01311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 821667733 1250 821666483 821666497
    0x1b0a15030509031608070b01091e0b031c02011e0603051c031407080f0a0504020901050423040f12080f061210090804090c031e02030402030f0a050102070605060d0c0605 74
    0x710b84c03a0070760f444c0d445940203551240448416400056000501c07034841ca031903015180e0340304100001200d804074515000071240ca07003401280c856405d04130342e0358188590310705502d20314225602c402900384024000e200c90f00004400d4a001114500390b003c09114a4058a501000034201031042283c0c0c054400c5481ca202010141c546514500030704181384524090b070803549a40080e030600500365030075204c0082480895500d4201040b000d643c490000d01d0441c0d405540c005421850300c1b02c407d1003400b40ba19580e508a18482c14802000816594400403502448840380b1504010300200c401500a8a15210100222000c03e80f039245c0240c2c41c4612000d400e045034650403400e52414203031a41d140054030107039004503080003120361601859160b041c0e207103001c0008020240b6001460307400843c007035501d03d43c0840001c0440d03c0403c80300c2900744001d030444040089501d0b00302e020358404c0c02c0c221110360400c0c0c0800c03503038101140e000c0c0c14947c2c0558000c00ca2428800121510b401c110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 821668983 1250 821667733 821667751
    0xf010b03030d05060a0b0c0607030c020d0906120b03030c0d02010b0d0f03210f0b03070812070f14120307020d140706090501110c0703020f030c010518030715021b0a150305 75
    0x45c500050001414000749180030910010707161500d4816805400c94400098210039900304550300c48205600030501c0c81999030a0820007441c0785200007580040020398116501440006103484c8a00d20004100305070a9081c0e0091120340e0b40401400b480d400c1410004020034001800b900000e4010b111405800c03910302c5c0c056810f460004642c40540e8541d040b01c804059545c0650215820140060300203804001e0003810f011600d0003510440344210708002c5d180d081c1d0b01c2140d50400401c681c8002200720400102c824441c080101075045a0080d207442002d84501e03654444002d01541c00d04d15004551084903060603481c2e02c900002d0700080100b101e4556071740350078580002888001e03000f4007000750000d002076811071050250060b940d48a05200e076000c5041e4418030381e801011256981250304600802295000100e072408400ea0410452040d042c2c104180282c2d00140a514030050500e6540b159004401804590700c103d024689040b980407615407a454025001070360400081c1e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 821670233 1250 821668983 821668999
    0xe04150b0a090b0f060a20010f06180f0605090105120f06090f011505030d05130b0a0c05060a2007030c0f0c17030c0307150b0a0b0306030f010b03030d0506 68
    0x140014400840d0794201c041c20664400a910450070a040090241d100c00c0c1c0e400761078568041809000c0d041c5200050a02e5521004004d2203440f082d0040514004040b009009854a5403410302c0c460790302d182041c1035070b4070303102d400381030400540108000c852000c0c050240700e9003040103020030b142e10050001168803800a010b22000420002e03203101b034003c000900020450510514252140074050038400b042004080c0b056a90224200440c13101c00d007025070359050a03170403001d00b51110340d2150001719800b00749001441e41103014050b01d140b00382c09540035943c0b00581740701110503503052a10320300e0003120140b10f8003404e58014155503000f400c012191000a9442240c84040c01c02d00b110401d9034002d04000e108003d10100c0000c01081f0050350501e110040c03415a070f4003501d04047c010b402041b8000e021814941d111244c441e101400c0000e5080e1219044241903105480c414064807d10401030042c4c901071182074000d04006003e103140600341100702001c5d11024160603400104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 821671483 1250 821670233 821670251
    0x603020a050714071d010302210709050a051e070207050438100c0b040f1401021911010902010503010e181b01020c0d03120507180e0f100e0415 63
    0x104404444003540c6000040c80450b050807005c01008003801510040c24140078010700041e40e0380380800c0044181100c03103528030044010401c0c0307480721a41c0680710751407131300c800e010901c10281c010521172040032902100c03101c0200042e03051304004403007160068102441c18000c40c074240d081190794031591004228012200301026819134404858110b082842c1c100203030950900320001240b50795542080c041040807515141143c1000900040280200b03421401c00c12a00102d014441002d0704000c41d200c01a06419094030700700b5100070b2002c01c0c0305410031740e001b0384140074201d050340d4180d4030300741542d2a162140d520766030080c1040e0a403265000319034814100401251454104083c80c5005506d41d1200180c140000b4441050182c0d070203c0c0003c002c246c100502641d6500c84980c0004c0a6403a6041100e801c0d07690191611000c0d401800080e40c1b400002c0442e0150f403c141c0145416150681e408540060900c661201c502c10f80d000a00407890034012403e24034041d01003c00d003c10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 821672733 1250 821671483 821671493
    0xc0203010b10032708040923090d02070b0405011b02150f03040606050a030f02100c1704030506100303200309040f051e090c1e0901170d0311040603020a0507 69
    0x1015662840000b43e40d030b00d4100d801980c8224400342e1000043c107001344180310b40c5a4044030312550265101141d190701000d11a03206560364a90028a4214040481c1c01c1c83c08900c1c0e102c032980d99240e0010702c5040401305031184407908484c101c4005840d51082c20850100035400c141403410141d0b442008064034130400040a8010240d030568014661395914091074100102d4215070080c90107004042e000303000042070380e0080a90182c0443e01c2c0e407150b00b11400211040c06458200514a48032101d5554180010704080c01c1500c5c030501c10340d5039542d0340f2509040700b08071038400907002a04400c4000070240c1c0740141240e41b00300500c1541e24081c0520040780903207843d04000c11015580e0001c000b848400704849506180490440c201d040c140380c51015070360208000d08a1203031035103000031060000319075070300948008040e00c82444c075030b5944608000101a40d070316031001e0085496500901c1d20a00c520f40e4000301080c0d0660401d03003441030032402034100020180c2444020030503040819 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 821673983 1250 821672733 821672749
    0x70b07050301060906021c0507050f151e0c040501030207050f19060623040e010209180a05070512220501240902090a15020a020d0f031b0308070c0203010b 68
    0x94a40c48150750707035240880041c203c60720f0350311802c00c6400c110505a94800c800541c400180418980641c0b140000d0401300d04008444030f1500d194441c150183c01c2c1341407041d40f40d500c504034040400011740e01c40d1054510320402215801d0710004200401d2080c1d601035400380941030300031404c885101c0940440c0914100b41c1c001c2181d42c8480d800098410005c0902402010782007004080703840c2601417000c0c13803000341c140544900c85d5494001300001d0f8a0258150b07881140c0052405c03050541c4003041040c6000107a8503551500d04000001344818003130011501004914000e450050340c807800303181c43c03505200914405400c52100002c011490034014070103541c6400500008000e40d0350b600d0a51000941d000c140a0717030043c85565810354980342030404a444480c219044051600710481c04c20500c1200207612014039400031041c08507103900001941e00c40d84a00300009400300f5803c04080b0015001070003d070400b000240c0c41840780810490991014002003074400448000030102 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 821675233 1250 821673983 821673991
    0xa1a1e0a08030706060b12070f050c1b12011103070c020a03020d080c0606150412020d020405190c05070f0f0213020c010227011b08130b09040f0507021c020102070b 72
    0x10754404141c1c4400d11405101740c50040411910161511515010000324400001d00290612025081d44c0003564000c104a031001440740d0103450404c40c286000552021244c0740c0e142c0201d0391010440c5135008140b00d0489001d01c13448011b0b065550340d0004445840c0200c50803038003c00000000801a140c4162070403030203110340351181e180c010420b551451720700c1c010310480c8108a4000181400562301c0100c0c1c0c25102d0046400d08610324500219000760b0120304000e4001d45400f041117040b200e08900141e0308051420b00b40424154034400322950300650708045d240c0c003034884020001a106d020300812003032018040300000e90002d12514101d07000007103940750b240d4002407584003011132035403052030b03107540ca400c2d1000506e11000000c01e6884c00800c1c2801e5a10f80111000c10300400300305580039480c901400c0e00d6038507112500a880c0790881041c0b01d0089040070804844034900c0d004561003411568002c006180c000a034501c4035400c03c0310000c0c1955800c01c0301070007182800240902c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 821676483 1250 821675233 821675249
    0x60a0308030408090307090507123b0d050c061b1803190507060921060506030f0115052e03020f0918100e01150c0317040501050402090a1a1e0a 63
    0x615102401900188428204802407481c0c84e651020208036038a1000c40032f0081154170040380b80c04101154100c42500307040881d407140810b10740c1d803d603110000f480d10b04050019190781c0d07110707400d4041ea104076162400421400500ca5100380c07403214580c204840000404a43e0103102c3c01125281004000d442a41c2c0d6810454060201c00d4000d41d02e180244942000340c00f2104190f81d00d440030030387c019001040c168646002c12183d0b80c0400c14442d0f4000b0303940c000c00c074131100c124000b4001d030904c0c070a860091007803030a404100995400c02c0d13168610180e201c040c5040c0c0084c0d0442c02948620041c45900d803040c41035010701d450724050760b200e40d40c0290200d90141082c80703c040075000994492945c8015610040c00400c00000d50009034a44600300080e565200f880c059403400350710f0446441c0c62040c0c004100601005400c9030b0b00450003518110307801d48500130880d0030758105070007000703519036020412021404c112402070046032007000d01c140c25840e981c0010344400f08035405000c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 821677733 1250 821676483 821676491
    0x11030a06031112190c0f0e0f061e04090215040308030a05060d0503070321022106060408151503030c07090c091a03040203010905060c04031a060a030803040809030709 73
    0x4121180b0350402902d0000c03244180000c0300c0e10710107503540303060001201c0c0351890707040d403441084220400140540240c000f2181c9050b12103000c8402c040d0700301d40c1c02440440280c0803d456080041074100302010a0101c0348141c074110061201030044e50908917000380318080c002d0b0804c0c00d89009000a50b1162074041d5403030510301024419501c014051070b2040a8000c0707168005180003046808055141c10000c10100c0e255585d00d19025107107180003426400005d0400201c03480e46d0381c00c214000080c140150303c0d11060b0522019025600491203954071403001d6856441000300c6041c0c0c001c0c5001c01c87d1030200a900042411340d0454009039125038044034090108156070300451015100c2d91818042c81898107903508507074200d5a00ba0342d000d0030000081030554030290400240d00350068100da0f060300300a801e86919520a101c1610081105181c048501c60303142402c030700511000f055100030300d05503100c51040340d00107442201c03618020007628089407414442d907002030090b400002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 821678983 1250 821677733 821677739
    0x7030909180314032a0d0906050a0e0c030709020d06030c0303020309010f0c021e0d050105010611070b030c09011b1b0614070c03031101091a04020a0f080c0d0611030a06 74
    0x40c1c5410300c50090036820040500070401700094030f44c2c00d084041c00c906094600d40c3d212410034101c0c0e10030345844010032030038500705209020f10350300094012211000e00304100d01c0e90418154480004402d10b65064025090801c1542044c0c0c000e000055101140000d81950325903c58009205603401180940c00200e507030300b165a08802c440c107601000d41420807040c0c13125800150f904030b0004900c489034a00c00c01480050301c1d00c0c01e40c142401e90060081000e540c4410000d01400c06844044c0ba07640308601001ca11030403418103072030040400601c0e40d428290b0100040d14100c41e000b0b6951020480c0c180c15001141a80000c404400c008503184510786080c540024034440041c0d81103103070f00004000b48000a6070100b4202c0c01c0f84d425142001d1030030460030100d4054240c000b40640a0070300e45144800c3c1c101e003c001d1a0049100f140e26070303086503440c400c01107969440d21902c4280c1c3c1000051400c2400c0129aa442d1140700e0320002824420b841110b031100c3d0015180b000a90b96510300c18 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 821680233 1250 821678983 821678987
    0xc1f0e0c01110712060908120105030d02010c020c090403110a061a100e04110c0703060f050f160f020313082a22020405061603170f010605070309091803 67
    0x60392411802e1810207407151041c250550b80d0200c0d48550303030f9200c3c0002c28250501c9000c0e807081781d205a02c2240565560f41d200070641c0444001c1c003407944a07000354240c09601030f00500c2103000c180201d80140014143c0901000540b160041040d810b10403030118461401e042808441e0030035129078000280d003091030344403068150204c604540141e102031004001540c204900030403414046a01040740525143e07061194022001a81c00c1c504c00c2240110412070650054109216500b900308401e0f51030341240381100c0c400343c1e601c1c01811015180390013024410b0490240c502003e004480c41d01c110380345240460380082d80000d90b15002503103134012010803200003084440071002d08030424440040051002c04090b20f203030405c00348258a00c0c1c01c0c0304042d015103005103402884135840c0d405454102c441c0441401c0c044000420f050040e11f00700704800c805502400d450001000a80c0c00c08400b5545a4040407040e0280414044001031000d298010503414107190402c00003071680c98a40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 821681483 1250 821680233 821680243
    0x60e1303090812310f0302010e04050c120702120a0c110a1401050a020708100518070b0906070305120c1b12190504120b0103170c10020c1f0e 62
    0x1e59160f4025000540c428081c84082e0303080d41001001e000020304601c2c80b1259104481140f403084010030350000504010003021312070459000781c940310a0641010200b008403882146c110381d540d0310604c00c1512828920010603132113021801110032200324043c2d80050354011175058000101d40c00313054000c1042e107003116500f00100f907420140490904400000241186140034108440820280f5600388200300f9100104aa041511010701044d640440901b2088810003c0140454a898000440013440b4004c803030f006a001c1e400c062406c2c00f0005e99a100c904c0950800805010703070b0811801210440f401228420700042d40c444281c0b40c094000100110b0310912900145403030082c80f003924045865001456102d000c00c8410901d054a0714010741d0000c40030301c101c2c41c00703230020000701d040c41c14141c030b0040c08400d051040c8500200000e00c11803100918580200080c0009501a81c024011495001003600c4d4001c4a5288c420701c4600702342251500307140c440011010802040c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 821682733 1250 821681483 821681489
    0x90216061a0f0301021801080601090e0901020c062d0c0405093d1403030c060c1809150103050613090302030918010e0c03040501060b0414010906090515030406060e130309 75
    0xd6041c20341e40c40100c00601c40b206c2c9207030f06012141000031300c40ea11400540020f0400c0e08003108184c180340d4080b5000b500040ca00e001c0c03c2c400c0502040600820300c146070410860008480d01c0c2040b15942c01030501c4e4043c0c92450b1840b024000031805964807140b40d07110b50004156044a80c10304645104003161060004454443c550000702d0141424032440741a0342420254074407641e606001f08e0300d144162100000e06014036030071300071030000540c000e0042032040c0003282500c004000820000b480b00f80c03414066048221032039a01540203401981e0f000c1c2d0020058290506d4084001003502c005c8102280113800008003881140b4009104050380c0e0440c2011003a0f96043c0b008250607250064250300b100302020000408114094004101805051340010b484507901c081c8407040501004e034486c046441c140010405a00c9162400102e0700010302c919080c1c1d1940f98009407642c80540152006911050301283d09081244214094103094845c0151406107090041400442d50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 821683983 1250 821682733 821682739
    0x60103060f0f0311210f0c0907090608040201030b03100b0a08030903281b030201030e16060c030e1801080616020a230d051c1104090216061a0f 63
    0x481c00d200301c0b5268032000080e260301411010081401c44000303251a40c14440004000c00e400c04480c2c00b09a012408004062928044171801083d4000700421458101d510700b00044009608010b40391140300ca04d508540103041c000340b240000c0022034282a4a41540b030300d465140c0d1b20800550030712413092002030800401a608010254002035151350402680d9100040000e00d03c1c00030311f10f801c00d05102564090848400b001c101c10040e0500b00d194030003030380882e28080100480480c0410000c01400c0320b1003200c43e20500b0b0000c1900c518030201c900b034042001c43c000003103560b19260300c001001840120241007541c5002c40c81860503c00400301c50800403079140d901c5400e5000a02e01042c15400a10181030030b800d1403140340c4520a1003904074691051a00310003005800a00400b030b401081d82c85542540f0510707206030191035081203100c1454000704010072905034264058404d041420024030305c800c1d4207498000c2603070f400031080d04c0c049040c25150415850f1120a00700a902d0035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 821685233 1250 821683983 821684009
    0x12090c0a1d01030807020a080102210f060a1503140a05041b0803121302032506020f060414030913061e0e041103120a020102270a03120201090f0b06010306 68
    0x41a0701d0030441a040c40010b0204e240800c500c8110f65900c0540ca000d007007080300071521100c2041500c620f020401c1100c05024201002003801c401101c0c1000b03110f1800504405c0009181804100c800805070f4100d00405a03035070308031030106202c8140b8501440102c0000300301d0f42800d00f01768085005002c2c4200100c0000041080020303000300076107030580818042d42e0305039900c0b0312200800104140d0300075414018000e48013902c2c034500b11020080da2100621031191a180c0d4010381e9141c00d0700d8000305140c0e10003070000c0c00003000b8440f0741c1000d0802000341c90801e200300d80420f19810666410100035602c80b1300a00c10704071000180004410541101c0401d00e150500f815200c54010f40040d140344c8600220082544041040c6800f003007410312080c0d0750701210300c4001d000350828208a00b0068801d1102404410801409000348400601e1002110314564450404071100125501503540310740900020864000c424201c0d03d0181500300b00b58507282c000141251000d4101042600d0700c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 821686483 1250 821685233 821685269
    0xc090507090b0a120f020315030609030d02032a0c060a05010509060d0611041d160509010809010608072c090c01050a0203070822091107061112090c0a 66
    0x8015040000c032415a403400fa941c0c0076028003210900c002902441c00641025200d0fa42441c59074010347c0700382c03102d0807100300d83c00340d01c8205500c52005403250035581d40f0611001e1080c186581c01550441d10050019485403404035085900d240303103040700b82c00c0072030202d19032074405070034070846a104a400340100a10f60501c0009444203502610460103400d9046110080284c0c40c0c2c41002800381d400c281d0382d1100d60f0f40902040308485032a24040405480e00412900c40d01c905034544440d989448490400285400440302454001d2401030190740360240040d10150500926004c0d20441420072000441c0c85800c08203074881000e00518081d1050401910000100b12505205000d1a00c00c1d0b0f02c514a078422440c1d80070743d0002034a041c07070024142d500d401b07240c0d81d0001d201c2001d08040141c2581c40d030840b811181c80051522118804200480004e03e0503403040b088a0300143c60b035410018248981c0c10310540844015115a000412184161520100f0440141141d505500d6280340c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 821687733 1250 821686483 821686487
    0x711060106090e070309200102070b0301030b0f101a09040605181b0c06090f06130809040903090306050703051819080a090506070b010e0c480a0c090507 67
    0x1000d446400040f4018801140640c5e1280d00003180703294204c2c8a03256007020326266020041401440b2502610841c40000f903600c2041041e20b0403242c001050407119510802c1c0c201c4101c1008000700d848c03150315200482c42410450980e4100c0c2c881079803850700d5601d500c0034002181c0d920b4000a206030102020300d1601a24545040d82c040d8104440c1e622800913007050014a01841100c030f0312500a42d000c2101450300004c10105403410b80040314542d4942010b55040410101006025441c5c2006460a94101b54001500c41071091408000d0a6543d458a8080780c80640f00003002a4440d004d03c20700641c60894403000c03e00705009040103806010301d0703c490b038030026801020341601180d5011400e000b4042c1c1d40c001c00e0043e040958610052030624108202400349a4030280048041003ca00da08000d94586420b10758154827500e400b0b55904098260490040d000401d0807402c05041588d07060300f1500440c0c0303c1c0c0061030405068600302c1d90340c4019030040c41546280c0340030003403001d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 821688983 1250 821687733 821687747
    0xb0310020d150b072a1d0c040602190c0f03140c0105091e0a05030a0f060e061e0a0b041a090c0304030203070308040c030b0c0301170d081f15080711060106 68
    0x140c5c02800540000383c01c500325580b01d51004400b50040da100f041c0001ca5000d103003601d10307001414000c4560991385220402041d4000c034001c1c8001681311072040d1041620402c0ca0880702e41c09001d4520100d541c9003400200f20380103410841c0d075000c6040d0301d1040328008002440f80100242402c6040009480200c1c049031a084150030038400d0860030300103191120b1030b139031012b400007070103940d40c0e0407445c00c01c41c107100402d49045a44a01d4011031400c121000700e1a10302030030344102c092600c0564500c0e410020400500304181d019500d0070a40d6040d0384900c207828400c9030b5006419811030b20750080080c00c90004041c0b05c410001001008000717580071048418107581400c0c4121030381c40d541408640041d00d5000102000d19040034886030f001b01c0c5010314100c52000340349410346040c46410a4540d0325001c0d160010070390038404074811507441a540100075541080c0409c0c40d075a074422400125045016090200f0348107030a200101d54407407880c0d0f4881e00038000034403455260101c014516 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 821690233 1250 821688983 821688997
    0x61503020a111b0f0609060304230109080a0c0302030d0609150b0f191e020102031803070f0602030a0b13060f06110604020112090b040b0f0610020c0d05010b0310020d150b 75
    0x24032044d264840156070303440e0998110f0b14010380600c1d100d10301031401d140d642e07404410f03481286e000d441c0810381d059414005c1800703c640c4141101c3c1030000201040d9a56070700e52070300b101540000d1110440e0341200b846488010071495501140c01c5da000350f1200041c05643d001341e90314101c00c1026484551402d821244203040080c0c5900c0140540030040760740c510854464000b0441c00d60000001650540165000d0000c0201c0360880030500000e09503203118407000207011011160450021880c1c96016542c04240900040307100e02c040c2c000a010100030100c1c408400c0d503510340a000007050821402c0152401f4185115441c030b0f1074045660b42c2c000244001d0402612600b0706a080300710740c10a2800c2031380310866010310704041c900300815a604492103119408542d0000e440e6280040b0145046541900600404100036044c095032132103003038069078559203440442d211918100300040c40305156081c010384820300c0244800075140600c1003950300c41b507040800d0028030768000898180c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 821691483 1250 821690233 821690239
    0x5010605091e0102030903030409050f0a02030402010c110f030a03090e1b040b0f040905090120031e06030a05030408060f1302101803020307120501050a060f0612061503020a111b 78
    0x30b256050004034a0352142c4c1041c40d4243c0400314000801358207d030860ba00409072020404400d80c0e07222503540c121300040300c0207030000d1110001c0c4000b041d104c6001c1500d10001800ca201116909000301c0d26006100b5011400034001170700030060203917103031000c0381c00c4a81d00144d25500c00301003080d49054042c40c090403000c4a40011010b40840e580300c2203c005003d2014180124600419460b000740300c0d01070440c0250400d00180c01000706c0c0c09003202d20482040d49403802491006580b5082d2050042c1140d42510455a00b100454400c001074402030400000030130a170715210501144102c0041c4c81485901c020050800040e91000c44d4000c000340c40d40340c0822030020442d50000c110030b0950010317425004032000481c0d1090f0004286074114007410080c019030319800d9080c030450f02d051003104138134440c013081030084038800c00c001c40142820700800b20718203403221340d03c41400d00581410703c0801d5001401e40012a0400840400e41c07030040d002c1d140e61020401a001000c07600929144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 821692733 1250 821691483 821691529
    0x910061d090a030c2d080712141b031c240501021e0c130c09120807060c140a0f09091a090a0f06030c0e0903030103120c03090e10090501060509 63
    0x26141803a00c02c14030121042170b000100100707031400c045545603c0a00141e0341c3d1402e07501c405c98014010010320854401c1030780954642102029a103205040390806d4100380e001c01c115139082d540020b0241c04190040c0303100003414110300040c000440d20f1411807040318a40da4241007196071780206510221a0800c00600041c0e40b0200c80701d410040500b002581c07208401030510703810040380c2e014840c460000d8413040c00c1070361220b900483c241000200108a07140811122001507202d400c070615092160404045c91449025590f0098011001c0342d00081d201c94610f07860594844100b0004210803001048032107510003c07104c0000181d98541d0040301090701140e042c100c00e40c02540403a0071942c04000a030f48a19055151a4a52249001d906070f0540821840400032007180c0c1200d901aa40c00d20342c80e40c900c001d407400d01c0005001c0d01031004006000070480c41440c4041c2c880c007003944410b203a840c28405954129041a0001410080144140c640c603854140d183e83c0249041e459020f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 821693983 1250 821692733 821692763
    0x5120a080a08070e031515010912350a1b0b0a0c180b13090c080406180f0305030f18070b0c0319080108010c0201110a03050910061d090a030c 62
    0x5100840328413a9030350140300d000d400c00c1d419990080721038098016046141030300780c00800115550501ca001d681c81d498840b41e0103000040c1003001c0ca0361005402c14072103e5143c0820420316290f031070180d001d010712600140644070198090402d50b1030341d80c8517007480ca0010094582000c0060002c000d15140c964600c0c00e5090309000384010644145501981003070700b0b4490303c6402c9503801c00b07000b400e1510807201011807010141d0091800c100115aa10201540c0b15102d44010384010a402028403040c10542008200312400d0030f18003d0090b00e402c0d50b2824643d00074628950000d0807020880e00040a4008411021807044115000c4401c0c0b69152502d103000d503400c40c4900d0005034030b1100d1965024440030340000c4181d0480721200c0003013103407040e0130200380d098520b1490b40011840d0104405110786020b54070480c2c02aa0765402c840340c1d410510210030454507503400010444440030020000307503a40700e0000c3e07448140540030b000c00e8807040d0303005402d80c0c1d0003d20007420031400c04404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 821695233 1250 821693983 821693987
    0x60f030106090f0f0b0306060d0818030304240e060d0914060f09240a1e1e061d04080f070c0e0712050f04020f0f0904080405120a080a0807 61
    0x4400600b540d00020024074856240c0d0000601060070131880c060b080c00c40f01d42c0e4901e00418502d114040280c405900b1041e1960703911015403200f494000c40d86107009298005880800141000c0c1400415040f4030340c2c001a05040031100d054120010000030038240b041d59100e04007034403400c058080700420314606a01c0c140c0d000c0d985105c0d4422940c45a00b0801808482c48a042c500840d02030095030100300d40407900002520100744039030b03002c45100700461403c854942c0300407821007007051400c100e040d40101d504141c07208004000c2e003402c2c1c0c3c119111700200302072081d01c0007000d06103080d41010b48007140e0942080b0b00200040c2c40450003007102c000c4110480100d900e800c0d0b11084240889895002500754080241c030048000350040c104c0256402a030b10402e0701441c038130039400105035280d5007000103001c42d003640300350000c00052030b001c0540c55422100d80250300c1414090f88036428002407001600610310400d65951180c0300482c08106140b0803511074a1031460420744e165106081 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 821696483 1250 821695233 821695241
    0x724090803040804150f09050906010e0909010615030c0c0f0309080607081f06080411040e070b09040b01230706060b04030f050c010206010b0d09110a030c0806010b0a08060f0301 78
    0x101800552001041000300107080005000781c9084036501d0317101d80c00c40e1800300c814060f26241d180c0070480d803203001e00c070f079240ca4114940e0045051504080d03c0031403001181403a201a949850b035a9143e050502c41e83d08403184403207403030445190800c48950b084600400707441c50352101600402e18080d540303050610804e42c090251010000315a50344c01c0901c03008160100c01c4503420404134581e0245c0104554144400044130342d2640c0f000b0741e40d10340c0e49503081c2d40d04000020135800b0745e4440d881e50207a9070910011004000b4250101d80302c42031b040521050301c2e01b84d040c10307041041d1358684080c0c02c90035106100b44000c0041e031a588600040c0792000c020003031608500249100400d000080082d042031402500d40b0481c1501c0308024000d0041e84d68250a011b80b840c041030074421403410703040c0769004440d030a000b1089240b0300c0d911000810800e0819400503034200001300700601041104002441c0102401c2410500c2c2038071800c07000306007001c0500f11714403030b9981d201e80c0907040e902500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 821697733 1250 821696483 821696501
    0x7060305090f03040e0907050d0809010509030c10030b030609061e07031401031514010b090f0402221502031306110c031f0c0311072a0312140724 64
    0x400c4950355078950203104117054044400300d80c54402d501010407582850303c240948580e200b01800d0030004028019105500544200758151181c80d000804079a1641c0010b0181e000700d07140095507030740003001d040c1007a80c000d00c04100e035400b05090140000320040343d5600c0e520000004406502c1d50329045000c0c2030140301140c26000085d002000340001000c001c00004155001008040343d03030700310b125204000f4810b00f00000f0b8213108201d9203050182030402900002031006182c0b030280c401400d4a02d0f1401904c3c0070000c3c0541003440082d40c4884502098a15400203506240f1005c2421241110740d02400c01000500319014014030740070018120514001030070384088121040006034000340c0c44903008041801e05520300360700341c02441152580a51640c0f00d0b0314150040d1944a8143c2c1003085080b404201245244010002804518041c2d44900c00009036030224160040010810001c0b042c05200c08203d002c00190f400b0400c01080300c022556100e90a20401e0980e0052100d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 821698983 1250 821697733 821697763
    0x14100e040f0609080406350c0c01050c07020108061f1b0519111005180d0b1305060106030b060306090c0c07240f051b1e01140106110706030509 63
    0x607211013084550b00141060300c00503503601030034050744501c5d01181941d503010000810185444c03108202d01003617026611134440281c4a14000740c1a81039406c40d1422181c0210092002c0b07504030440d07a10051581d003100003201c1c0e451620064601d08403e10652080f0340061007a551112a28800d461100c034801d941c005007070304c4c001341c039003418950a20307003038a0211484211030b90180294588140d864aa0720020b0395400d08110a90348850b25544a81d99410341c030280d084040d00004500d003601074440d01c003200315044003c10b0381c42c1c414602201a00302d60141070030403030321081980314034040c4c1c1d5002d02c2c100c400500685807140c1307805c5544107103840e4061500400a01140c03244400ca03005000c00070402c0038040364100c40c0b00889072861048e01c1c103400241c003004941110542e0003580d0070340100c040145d0380c100000002e0403441018900200d00c050f5183e501885175030385003d20150040007181080c4102c4110680076a495132418060001410750321408030702c444204100641c1000442 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 821700233 1250 821698983 821698991
    0x61d0406090b0403030c0210020c0c0405060607120f18031e032312100503070512070509190c0f052208030403030203071704060e0625120314100e040f06 67
    0x4d050080182c203103904464058820f0030500c1000382494422200c80300505005846030800b49400c0201618000d000c0c0c40d8456014081540414004071b82c8414040840e11441c4580c9003040c0040c000540b840380612416408410410106100c54010b411090024184c405034031028601960b9601864200d005040405d81800e890100740c0c0e4014100310a200003400c5d40c0c0d540760800c042c8911910300450350590450001049641426042c0b5a182110b410564080c292290081641080215070b40071050f00366150344040c0e6007003881246201041882c1095080da4600c2c0081c2440c07080385140d00c8110500c2802c41d0380d040d2045601c502410b442e900b540c0e5a5552810002d5488d00203050030b81e24140141d08480c01c1e9406001103030216002904c0d043c04072030031902080382541194054149000f00005c1e149820840c000003039207850310a641007260324003448801412100c24000e0b00c000600d100e81070002e21009541a0740440307036000e0101d002a550b602c0c15130195400307014001c10fa2824 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 821701483 1250 821700233 821700241
    0x3060b0d0b4011010c060c03020304020f06074d030c01081501032d1a0a0506090f01030608030f0c0c0d150c1803030302041404061d0406090b 62
    0xd00c01103203400b000106090041c0c110601200c4668101038080e082003001001010000503910394410780c1060014106008130490315110a002da40007001c00800003075002007013104516000b07144031815041038410600f80340560b80d483d02c40d01b11070381c92004030905021245104480724424103007244500c03200307200c03c002071034003070740e603659813180300324070a001e00210090994424000d0602c0341da184402d0000c41c0350610010340081402c0d001003840308509140d41d240da00c0018a0b200100005c000380080c204c1a40407150400148006c8030510941c4407038020045d0303645401c266a044007044a54100112200d0010303801004a40c2c80244c0d580000b28503c0c00420000703004e80400010001a18501e4040310100030010304c00f40801050316a580b802507130340c01d0381940044140c4601e428600f03080d0015034150101e50318958803c6000030340014080c440580c84000c6019080300c151024480942070503240301040c0540342007407c1d00204500064140032598000c818040d801090711240d0b810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 821702733 1250 821701483 821701501
    0x8030f0c0c0f031c0b03070608040303020d1406010807030605010f0311120c1207030204060f18180e07091104060c1e060515030f031605150a02220503030403060b0d0b 73
    0xf10010000e00e100030704400904130060240d02c800000050151801c47d040c02d00c1034507610030140055080540c00c1c807480b80901802c0c030072144244842c1c200080f8601c1d03c0800103002e02d000070034490406060290070091a45c00481c5004820901d00b00411409107000c07010885021329016803a69900d1074050144c024041e4000784481410300f00410303040d075030f800420b40a03403290741720b80000124044000c030040c034800c001e00b003155060300c450b8445150350f03252504c0d04140c0c1d1250900101e41d4500b03207484080300800034540104038000c803d00014004081000040c042c51242c203040c0940003466001300549614007007030301221075609084100345810a90002c24007228090440895600c0008403803400050789091050114015458801c02031207043d07411075812000c50340c40c800c16080c0380200000d581c800d40310300d102c038200507202d0a0120324104221455071a0002d007828281c42405251000710032582641d070064000f2814041080100300301c030140100107018000c5400900c40000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 821703983 1250 821702733 821702737
    0x1608150303130e091606020c060315120d0e01170a0c050f041d0105010201140103060b0310180b0f010b0d021e07031206061107032d0f021005030408030f0c0c0f03 71
    0x1d03081d012940070700c2500085d50810f10f003d015001c05a804595081c1407031500e80000d550012548060103002074007680401d00040304c003504007010b03405c11044c030002e19034043d410b0152400d003480c20800c0c40900f004901d0f07001c5c801030408017600f5120300c070703500b000350240c400c549104090f00070316960346542c0c1880c840c0c51580ca241d8829280074400c0000f55661050003039995840c1e801618006036482c40d03458030024080740543d01e0305801050028200b80000f80b203103d050705460848401041c000340f50210001500408a404041c500f40060104440c50b80940e95190b80c2ca800040c0e8840d402c076038502501c10310711081040c10000040c0a010541d00c89a0100c5100c0355010a000c40740d00d81a0603600290600f08043c0d032030348182e0003040418015500e00f80c5a00042d107100015283c40c0403408066001e400098031110052b215200860510240160100b1103d103450340c10760805540d240d02038440030788400c140554032008141e01ca42a04200c13011305110b0340854212400501c94a5160703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 821705233 1250 821703983 821703991
    0x6050408060a0507020d0e0a0b1c0b06030c070b060a0b16060509030307050a140d1d0d0503040f02040c02120a1d0a0b0f030a20121608150303130e 64
    0x81c021440811100e645a0042ca03000e40c0d2142c0280c041903602a804691120600445940c020050480011000d4903440100003142170b01c600000070038003607031014041d80c1928090b14003d41d030400c104015a4010f1040d00c4105500c084602900d4446030001010208190041000d480001034095a21042c01d070b0380b0a2014402c00c418845a40c604200c1070301d03808201d810901081c0c042100003110380c440c0c41e10b1810340301d0811b9024104100c2c00710000445490004296029480c007100e851390f010200300030b0082410b145445c900c4d61500d0303503802e4903150130800c000b070103261138200c1211030a000340720070303600784810780b000903111880000700526010040c0e80e444207464820380c412281d0709001e5000b130107a50302d441e1191b02d8101c000c00f044100e82d000820801940350781c1c5031141410007011044850f075940d00c0804545a2141c20000c000c4030303a010300780d24001c5007000c441980507500328032200e038800845203841101070034801c0401c1c00c43c45140c2440d0700c5089041008600b404411900e2406 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 821706483 1250 821705233 821705249
    0xb0c0f37060f020c1b01050d1e0c0f090803040501092705090c040c02030903060f06150412020f0d0c030201030e120d060317030f01120c0305190b2208031003020a060504 74
    0xa01c000c034001c0050021418102c035400210308003c103042c81210358010028004a00402792400b8004c2240d80e0100c0311132004c80f0380090300c100100c40907580d208400401814540002d98506450321001070f26045aa105103602d1400040c401c82c5580480e03000e044500c00c13401024012032038003100c0b00740c80c0d07003a0403510b0b8440c0746801ca5000728640f001042c1c03251050040c0003030846480700c0741400c0c00c80c0c1d17004280755448002001c00100741a110700c060402450311400c2d044c81030545104000004013600b48040c0a01e003810340000201e0b94400030f90040b42c5d02130030002441448881654100708410300c0a000300b900c00144643c291184e688140112405161005003041748011800c80a04c000c0c4c42200e03003c544000107000428444a04d4240d00c6d200f0000440441d699907500f03420140c00c0780c1c101c1450803c8403520000c0c05210655980c1c401256800340d1100d07541040744140c41e041c205005085800040002640429907880040c003030340d0000c1c00287c541e0307a01d220041003548503000d0854 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 821707733 1250 821706483 821706493
    0x120a05010f030b2e0303030204080d0c12082d090615010801090e1504050102090f01210f020c011401081c0c110406030b010b0c0f37060f020c 62
    0xc2503a051100301c07054079400032080d80140c440003c1801048000c5a281c2c903181d03a0f10140b4804000c04000d260001e5129450150b103d900e0031609034200301495480341d083c803004105102c00203a007440f000000d90f00b81d0415078816240c440c0d00c100301c40030303c030218101c0500d07100c0b070210341c10302c01542d082c460403a03c011940f09a4424815140c2150007045240c00310361180300510404049402c07441100c030b803070002c55128046054082c01c80d00340542c0c007900d059500081002042c1010400070381d12400c2030030100005004d00311112465810b81c07400c210126a500b03120080c2404680440310741c2c0e0761a800a00021f040c1034108081c4131002c0c0700f110710754441d00790b10260200741c0c0c1d542d0065aa82540b11031180c41002d0f162110075030311200e110b90303005644032404800152481c1c0024080c000040c019078071f410301020406e20300610301094141e01d03488064070101048030303040d030852120301c4600440721041aa84101c11920500e0000500036810410b02140656069014050030140c1710202e80c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 821708983 1250 821707733 821707739
    0xc040213081006121415041101020d08090304090e0a0c15170c090105160f12230901030903120c030b01090506160303020906130e0403111f0c09030602120a0501 70
    0x40c1102c0003481a100c060702c80c1400702002c540340c01c070028618071948059960446c0d20b0040030800210407102161305c190f0400000c40740d5681084100041c2c0800c0c10700c0103a50801e14101c955038041da102e52003035641c490100010f028000c1c4802d10005510680351008141c8039035022906090b08942d880008041c80f800c0c6071202c0512040b940180f040103482c51516840c0c0004403201d41c0319442607030342c905a00c0c8410300041c101600041e081c60080940f00061203041100614090361443d481c81800d0200804010034014031044911008090800191240940c5015179201c1d5110b1944650a89404103658156070181c201c0402003174240c0c0c52107a584d84400403c03515019110390307201941e441c000c0817400a4040e500514207210001d000c1801c0089085400c240300c3e025801441444c64624107010070160011011254030003007074003a011144440d407101c47d40080d680c170750681150700d800c5000c40903400b400d200e10180d90400410366031003074a09905d01c61440c054405034042d510b000000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 821710233 1250 821708983 821709013
    0x50106060807020304150c111c03021902010813030c0c0303120b1806100e1509030d03021204082a0604020a21020d0611030f07170103230c04021308 65
    0x1d41c20354581200c01b40342c80110b9441101c405c1b80f130002c220746c6a2003000c00b03206180e039030b518522900d40405405c04010403070b901d40241003240c80102282c80305005100c102c0140e03009045194051500d80581313006441c241000c03603c015003000b0161480d03104400c04010305904c04180c5010320f043e14814482c000282c2c0601180e0742c0302c003581d0380c0b4102c3c03200040360f01440c0550300c503854039100345000300c070811140b00000d64074403803000400464034001a2034661070a040c0400403141c641800d0450500d05ca4403400ca2103980b0041c0b009101c003500144c5151030340e11103104c209031000c0d00d6034100000301100886550310041568160310420043d14000740c1c011b0015814080502d882c400000d05c0c0306203030b0a00203490800d8400311900c4e03031a030f00c01071038540310400a0b40c41403800208104c21410300030806041120740117504951184590018004071340042d601c0048544d5040d13012260a61008241b801d080c400711040394018000180080c40f1100500c6001c00d44295009590301c040000c820 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 821711483 1250 821710233 821710237
    0x60f03090c0a0609092004080a06180809062115010e030a031b060612030e01080c0c0714010215091c2d020f060f160f0c020f040b030a0501060608070203 67
    0x5050300113400c05000b480b4004140d001150650b00c0303884118000c58184140d00802e40158101100c15032029841754140082405010b00000410801d01101aa01e80f01c0c1d1821780700e8551924004d00303000860074401c18030102c0341c03980701d403424200d0403143c10300c2100b060f003a140b10400c00d400110503000307441003403601084044043d40d05894246050104020258a0000c010010740d0184e80c2c40c03100051a642d602e400080c1d640c0b00356a901d840c3e500310000034011f00c00140c0005c0030a00c051103c0054194001103010641d00180e80c494042c511010040745400303d00c456144690050307200340070384040000350000b61400000c1d096400790190030401c407803000714503182a140c450200c071505450700505094110488207031050307a0703038801c03450142441c00f0420f0700c01222005043d810002d0460b420396041500f108985005c5422004904006055603001c02c80644a51492250200ba5035507503404402032a030098141c6002ca4201d00b010303030081c84c0724031030100850104800580c1841c40441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 821712733 1250 821711483 821711489
    0x909141815071103070b1e010b130e060a05060c071412070b030a11030712060b0a08040327030f020306070201060819060f0e010c03060506090117090309060f03090c0a 73
    0x76039140c0750780707603001150045842692101180820010140410f00280c9100e00c222030a81844510040e02c1607445007614050f848100600401d100140e060825203003082d0486140401141494950780d0010381d0400403503000f42c0c2d00100010b000f602800012400d4012030b814135040103035402c0c00c202446080e0000703410740a500d42000078280100940e11029540180411000044034164030503042d10b03039030041e02d0800102d010010000300110315405444060441311207542d0802c0080540a4115003010b00020148003580079105d800440c1d004514007200c00c003000c10740340e00f50343e03003040f0500140407001a402402050000307a0a1401401440c088070b140c400100300d5181c600c0055100c4010600040f10503585503086541805224011440704c89031080000410b20207100340501150b109a00c982c1c0190010310000a5070780e00800001c11340b07200c02d02003203c2c650342c00501504520034100655440070011600c800070001c01d001840c4202aa2001c8540741b6804004009900880344 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 821713983 1250 821712733 821712763
    0xb270109021908040f020405091c140f07061b050d0e0708031903020415050d200901050a120903090f080a0503030c1836090a0602090109091418 63
    0x12040b0703034450710841c0c540d54498000d1841801c8000356500040541c0e509840070652548040110b140d0100b008100c1c1185140c0c50038500030124401c94980650302904048019544011400005210b81500f0090407070b0900755510980c48041d420184c09508552400c520961402982c01280d190000f01c0c842950a01802982800e00c0d0303d102906214840c15490100340c1c080c040002c0041655800415050361510b550b0340b5804111004421035610b04100e088003042005090382e110400380c208d65002d802881c0641c0d4480080c0c00c10b81d01e1540440c8070300240d038030704032140042c554010360100c1543d800d00000100da554034000d496480d0070000002c1d0180c0c01c10008112030b100124000c100125110118001900300d45002403541280036444292118080c4420007030550300c0425007000c80c0f2000c0c05203086c3d0608450076035440034a558010460b41d40083d0100c4207a009082c4a0010b14580000348401510692002c45840041e9842d1408643d41011405113036004914020221221 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 821715233 1250 821713983 821714017
    0x1801090b0f0312090114070606091103060939091f1209020d0b0a0c080a0627061836151b0804020307060e031b040b27010902 55
    0x780043c02559401605280d06000d00640c40c0c000c110740d02d4003c0c0c0a07841c062030b4006407917883c1000340c60503103005100154541c8010010050f1a950b44a1056080014046000c11a4a00030300842002000c03243d005106c40e50801c0d0295403840c2d0100030844200700f50b41000d80007516040d007140c0003176a1600740b408070303244e9001401250501e52107030100760700040945101924503198010036601c20340b1111000c036141c1c040e0079070517500711100980050881204002807841d01d0f9000c004110b00b802d5199040b201040c00034440d07009900f01c480a48107940700c10601c0b0b00080241d0340200341c0b100d600071202c15800c4070300091010041c10910312020025401210010311303500c8003007031b01c0c2e41c03446013091541e10325426030400140c41c0c1803003800e0301c02e891303041e002d00745801014984000b030350024040000c0f040c82e80c0381130b89000ca0310b0340e82042c2e40c3d0b040394280d544100016001e0107e1039509a04542d0a008000d8610b0302e42c022a0807031041151220340a0340c0b501400b0060b40700e103c0030050908a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 821716483 1250 821715233 821715253
    0x1140a0305070b0a14040e042010111014010e01060302091003020705010908041e090e1e012301060f0309020a0b0d0204091401030b0a0207051902010e1801090b0f03 72
    0x55440204013084c000c2c03400090800c000c0020684a400c142c00801107005902c080004110083d0100b405881a0704000c0074003149d84000298100b0352800c036a010841c22000e0480181030800c0300d050026407455040c0036220f000e500107048000d00740b292049265020000003602e0340a0300c05c442c18a4000741c00c00c0b0030301e241d450007038002e548400011612903507603140850104510002038400380500c42101e02d40e220380b841001e15081070340d80168404c40e1418130720b0680c640c00025001146943c0d224100c801401808880d030050000d204000d8006042c88802c17110030f15640d0302d00341642c2d03243e00ca201c41c0c5864000210101e40c00714030000c1d00030b401c8481c10b120041403074014103080309600c1c0b400740c40c00d1b0f115030180007525503000e4203902150001d8014020001c84c401340c250b0000b003801c811130078020780d5140c03140d5440d03c001081f840030444200410640e403044501d0031070745102a0001c08200030b058407483d144902403203a69103051030f1040d40c10381403812860101e400d0800500410003480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 821717733 1250 821716483 821716499
    0x6122d1e0512090a061404052205090303180109030c0305250809012a12090e042102070b0409021303050d080f061c03030522060501140a030507 63
    0x19008508814000c410340c030140005004101c070749494000104040e45070420a01809402042a00080305220141d01c80020000c08001510300300d800484044000c0c0203400c10506c5c071401c1d10a044010207080400700503580350008011401840c140e04090101c01114084500321869420002c0008140d040080c1c0800e10443c00380c0b0310600e5002403100c032045204c480050040c0441021200141d002c6040c140a42c2c11034a051204403440c00c00415200b9005030181d0b03500d030032080c0180691a00c00140050700c4c881ca85440152180d110350329602e04140c10301541c12100c0c0140c3d5030840718004007680001d84041140400ca0340c2c0e80304220b003403d050200a078040c0d08603400321000a44940400408a0020050195110800e80b5110b40606240852140308003000380f0960240649442208080c0b000d49000445543c00d81b43c00102a01c038001d0b80340900c0c080610014600c0c1071b240a680034042c595100e9412680000003010300b804001c803d04c410000c1c07522015103250031400041210703007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 821718983 1250 821717733 821717753
    0x1050409110f190f09050c04060801060309050a240609024314161a0304240c020c030604022409040203100504050709030c151206122d 59
    0x5400429150380780c120f403841c03d0000981e981c032894104422031402c110008040c803900b900040c01c0134003549030506025001c3c100d510103200c0d5404055490000205108090007016001c642c05914402c1622001040030b10f261414140b00c00014900303040011000c078644222440c4c0e146024444c42000c11480048444c04820010031000729040d414130301c201310556000001241c4506807419540d0399a081c0d440c58200a92201d03026481103003001e00c4040031050490380c518a08201240da00e954034540007416442c061a056000c030003a450040c4125503d40003100303404141e82c2180d1a03a09140209640c0b400281c40217508050340b0440300311081c9909207071000c200540d950b40c1d45044c17060008502280d1049031108101e20030194103018520b00350240c0b50300160f05141c0280801e0554540c1d0f03010f101766202d000d400d9625502a605a503000c1c090041c9460744241040201d0340d56550031a8507144409003c0303403001c401c400c440c40319412284010454481e550040b03a511f0201e956594440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 821720233 1250 821718983 821719009
    0xb100f1206090207061e18060c230a11060f0f090a0503070b10080a230109061a030d18060c03110609070602061b091003021909030b0105040911 63
    0x801d4888501150014042c0010b02c1071912880000800c1c80307030001c8400d416031107600e030380c0111402d26540741c46024021507044401c0d40c02c1240014001002c3c3c006840508604081d8000d0140c00003007125611103081c050308800c04280c4400c41d01d0080001c0ca251261400c4984110030b08841d0b003c01d1034441c1c00a4100d034408107450450f103051400e1340b201c0f890750700540000c0b42c0110420041060700d034ad071380812000400c0d2040080c10240702641e181503203264103105c0c24000018400c41c00000f40030940000600c2038220310200302588202c140038a00408500004c0d000c0e11440c80b80003400ca00c1000c1105040c101c0c00c511218140c04d000c001c075441903081d0750a608000320840034905010381071004500a4880300d00400d8802d00c4c2200c00b03800d002c00100080392440d80102842d5410352450221200460111841603075070760074100c141c0007409982c10441c41d000300a1041022107404c2044041624025541032034079130303641c07810082910303982d050040c04e00d44003c0ba19080c40c14407400034162 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 821721483 1250 821720233 821720267
    0x1030b0907181104030b0717010b0423190b070c1208190201180309090507080919030210020f130806100512102d090c0b1c052a12011e0f06090302040b100f 68
    0x509000341c001c0810504442d0003900d100c1d000080c40c2c1c0c040100124864000b401e500c203c404410400380c80c1e4006601503454f26a0110500e8800c002d0340034803c0d48080c00048140451030904091402d0060180803680034001040e4580380200718074500854582d445044520001d25210018000100024281240840640c440c1402307030115820a80054808441c040340d0064885200003511001e06980e82d100360f015030440b8041c01100c0a0030b0309010180c074401d440700d0010300168901c2910707050003034040c074400c18601681669a0325141d81d4402007803107d00c0c4821006058030701344030200c2e181c0a030b004004151001040108405401c05401c3e00c0121a40e203150041744074000070f050b1b83d011144080041410750001071074070041030719400710301c0c09621000e044c1100da902c0340b404140180a18000d45104158402072000351640c16001740004841c80425203507228405407c0403803c1c00f0480c407460814810509500706195401c2d103460f8542c0e218400f00c00c2401065401e0212002000e078 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 821722733 1250 821721483 821721499
    0x50a05040504020304060b040c0c11040e0c03060a0219021c0e19090b190302090f061c0501060509091c0318051501030b0907181104030b0717010b0423 66
    0x14141e60780388051449903000301b00224071180c0702d10030403048802172400c15080c4000a0010f001061144000c1c0002ca4019500091246242120149400c2c03d14800d190f05120b81c03002c00002e50703000e40140c0354541901c10342e20400783c01c040701a6103848142d540c01ca244085822807a40c4c1c584100b80750103c80001a00e441811171180c0c541d44505000c80e00000b50b00c0780ca50742d00402e58101040d000341c041d200e540703410700140c0c00c40c1e00060081c00d001d0704641c4424003040101e032199a03103150204042c0d0b0b070755109881c04111803828901810161183c00d1040fa00384001500b1a0320115492520710020780c1d642c9005400c486044e0020180d0308140c940c200303011002d4a00051040003588002041c204400c103241d890b625206026040c0241040420b0b0041003040180110031140d0b9400003240c1400850500141c0b813088007513004550020303041c101460140b0111642000d14001121034407500040180c1c0c8800e58240c1c0e5225a202d45514250390200502e40c686180e00500400800101001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 821723983 1250 821722733 821722739
    0x19080607030c090308030915060303040320060f12070e10020a020118150801170102040320010c06050705031e06030a0219091508011a181b0c010b03101506050a0504 72
    0x705c03564000b01c41c090b640c0da110050007082142e450203000d6221100714000c41c40c260940d52000304913503e4137211241c0a205640000582c0ea030718042d99540300501c2c00c003030380f203003869030302204001010786d035600104a1310010001c141c20220840710b02402030350014082070170a0360044800e50b038040e081d48001c02c0261808140c0013149401c62412511a5840c0c3c0041d50402628a91416a28404004680c410041000001c0620b5000040001c041c0c0e14510070200703100040c2e401c01c0c4200001050b052400d01000042c1e41c0010145004181d40517400c10104110a190f901032042540d4403a0b041d405480c414006280402c40e030190031540106000c1d00380d64550703c840c20307110401400100c82c407096006000e0407800b446103a0040020f40000c800440345140412481c1003181410030501120600040300058130b103400a0032913165620050b41d44604a1010f070081c02000700b128864003c0302075a00700c1d0140c074044e40d824507a100c01c00072490f900c1d207d01511241d010710300140034800d09000c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 821725233 1250 821723983 821723993
    0x30604090b0901060501020705060c070b0a110a030302041d1b0901021006030c0e07080f06120f1518030708031501110a2301021204021009030206160219080607030c0903 74
    0x100b4001c2031080004103010b400e04c8006410100503402072401041c041c01103580d801000986901201d8400c02803035620540100c04486031512007002e50118400d806030700303040640c541d00070011610201e08440404090802c1180d000e1010b907000d000c5613080030f0003c0d802000b600c1c010720755418140101c446040c0c1084980058507155442550003c0800c24100300c2d5000040881b984003607036103003205030307842d1005442c0c030b0300070300507003460302608101002c000f458104000021103c0680b5003110301480480060f0002d00d1000c54032044a408a4410000404000410342e04025408036031141150313a0140380720720040f2005501070400c181411881407807401400403642013401044800f1301e1814106c0200e1081034200e091074850382c41041400300d282a04031445421a90448001000424010003180c80e08465000a907100a000800743d4100700c8000110a0107442512200c2c4102c0d106080c50103205640e1090200940100d40045e9119110798095107811040d400c1c1020103540741c3c0c941c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 821726483 1250 821725233 821725253
    0xf020114090f0d0512010e0711030d05010609090c0e090a110f09010e0105070203060f0a0e1504020f0301111c0914010f2007080c0c15120604061a03060409 68
    0x36403080e80c2040000b042401028401d0741c5406400b130038014548003400703200c0b90b2030704014810403100106000105044034403909400344510303401400c030b0303850300302442030000100001c0c8034960120b00321100000e000040c50217a040d0b1103085440309001010310100740519000000c080e81c4071a60b640302a0b00000000e50702400300761000007212901c1d0140e0100141002424491050500000384801d034010b0703400040159100f140c40e2210000c070340360245030602608501015040301d000b48240a40c800c4a41000b407442540210356040c03112543c9403c2c14203c030314901d4607202c0c0380300400c494400421207244c8503095900407080000c0004564035285680e09004001c00d90594503849214140d0102d400b0340312094032002001801164121002d101e03c0c45544801441004042900d480c00c0d101840280312078130014200024804415420184962003e88050200d102440118406090074400c1905488a4000c3d07144d9401642c0c0603a00c80b50401060190b015464001c403900140070040c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 821727733 1250 821726483 821726491
    0x21020a0b0a09050105030f01090f0e030a2a0b1f08060a090303050901050106020d0e0f031c0f0302090d030c0f050a0605091009110402030912040b0d06061e0f020114 72
    0x995a03840751525040104021150b5000d1410400b0078014014040300310b048a0781160307921364000840300c0400700303070074090525010200007130b00011404086141d0041c0840c0080d200b0703500042401a0003260310754900c1c042c8800501010228000900d610a401501e403400b004108241100711390348901c400c0c60000c0803100006110348404d1407008040c0c26020f0a9080003903180240120760508600035990031400c0030b26010020210303c4140c1036210031820720a28040030301500e0b044460050300e54071444015880c2c200180c00c0e800c409a08a200b403081d292110310007003901601007600e48045403026100203080d00c1064500c1f11103400600e0811091100a20504002c0303000e1400481103030524034004070100000b0309103600940080c00300c111680070003404880041c6c680d12542c016900e0a0103c00344e003c2030060005000c28040401d001038451040c092109000154a425048507090440d44600c1c940402d64050042c100d4002d06010081034203078400021520790323400300a8038441c0155 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 821728983 1250 821727733 821727749
    0x807060609061a07050a021c0f0b01030b06010c0b190618090c15140304080702030303092b080a0f0e01020f0d1a0d0f050715050903010c081021020a 65
    0xb000401081016003880180c90220081c142d05200c10b42d11201c0d100c40e00040001c1c864031003102107145a10a149803143c2d0103800c91607130a10340e805480d204501c10300c00c0c0800d54100d280c80c0e0005901d5032060f2585035080d548000044156241c00e00607565150803500c43d200400c0d240c0c071000c120140408940c204018080c8000b06998206013410b40900f079040e0400b03040b00f001a10700321801a00704c81100305010125144035605c0da01d5003410303203050003000710095050000105000c00031100040c000031038180c50101700213807020300e840d41548080ba0320703031400400d0b2801c0000302001c50992124645d040002808140b00900015044c00c91340504032003065801d01050081e070740b041611801c03641400c01c00241d2204034070300d400501c40c10941000106250700b90708052040040502800e40145089028800b0313042292101038000d07005559401e00039881c0c00c4030110b0191044503024010000d40403101c02450920b9000c9040381c00e0346014400d08800d01c0a0980140c851010180043c0360741c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 821730233 1250 821728983 821728991
    0x18010e10030c0809120a050d0b090106090303120b18041a36071203030615080a0506010801050f010309030c02150406120c1403072102090f120c0d0807060609 69
    0x50701001c2c3c0341410240a0541d654084240c02c20103820060844008814074203110340c03582c0342401c400d0040d01c0e001c2050364014880310000200c0c10340290b4680c050740c0c82902c0b100205a5000300c1c0394101c51420700ba003503108850100b20340601d07103054280d5030818000c640858003ca40754044201021080d506401140c06400d040001543c50320810142000e10281e2640d25894a040040d030f17400705809500d1700c2035050b102d1035003014081ea01290080074014105203030042d60440103012a801140c0012a4078109000213106610900138103042c0c51000708101040700042d00110b0042240c1d0804809011000b0090300140e5904810010704480782c210156070b42e410080000c0c00144c00c0a03a580b806801c2c5040d4502c1542c1020403007000f11041034041c1c6e2623035201c0f18103c0300141c0c0c00d907040e10b1036603283c03200c0d47c10303030880ea0010441807109a6070344c40014403003c14803000d1980d40c403007d034068101e40d903d21514503007812519074203406500385600740309a589451040710100d0b4052695142e031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 821731483 1250 821730233 821730251
    0x91203170c1b0303093d2003040b0109020d0e0105011e151b1505040501060e070207050a1511060903180f10080601020f1b040501090204050618010e1003 67
    0x4000b600d0000c01020061425401d14a0b00c1c559240c004007020080001c6003410f082c800c0000c42c08603000c11000e0b4540b00700b04400c40100d00000d0000d1042108500707110350080807100b03000744c11240941d6002044400d607a203407080050080d00105090003041d134a0310340302d0385002024040d49010340b408401144190074402180c800381407141c0d002116041e002c600b9400c00035000241c5603c0b008425116000c129901e1903c007420740d403005403034440b40c0d14120907c070600c94151301a0090742c003041c400042607150b85c00280e9075240244121503100a46040500150346079850302c1c00e8285960a0150306802400041400c0c02d504075007240042d800071034000e819424041032010349017000d0700e0619080b6200c4c80032501d03043e00401c161061200c040080f0b00564400c01c02400e000c542c02e0143d03605c0c1440c05801290500344e120744144135505110000c14050003d100326400c4800003004185880c40d5401c413021030300351400000e8103102e40300004109507161035442203084051036800007042c500c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 821732733 1250 821731483 821731507
    0x5090715052a0f1f0603080a0315050409030206040b090c030705010302090d08040e04061a090a020a111204031109160c0c0b0412050124091a060c0d091401091203170c 73
    0x43c800481c0032131500342442000030400c02c000315a46ca0800d072801240c640ca500407004442c070801c0d403050307401918019001d000d051340880c03554051881041c013102c0035280e80b05026034500018507095419005044104804e6000c0d5004014500340900021140304041e1034540042d04160b205080150183d820401000aa88680341218080c4801407140d5400000031400703441d401088441080e90000b040c4207568055410720070300060090844007400c5014102d010b0a4109100440710070300e24002c1c9141d00e20703120320350501c0b03452840c40b590b000c54014802143c0b000d01500054905000c0c100e80400c0030f522000040000e0410110720030400c20144c03a00900f1100c051210404440b03901e48244d60300c0500544003812a0f10400c000305941c84210807500021000c02c03d04e80c0e000e440001d402c40600300c081544016509941c581c940515510400c0040820b0908089800914102414004400c515000d210714138060329050740131403c030543c00c90020340103030b600d60030745280400c042c02c55103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 821733983 1250 821732733 821732773
    0x50f220b0112020c0a0b040602090a0b0d140903030a09140607021f14010902090111060f07031803170c16060b0a061b023105090715052a0f 61
    0x19030a0b5001c51814030000e407480d0300c45e0b071525001000c20714481c000c50248600768050b210b80d06401080a50400d503210202030f907503031107140301c100350604002c0030606000101490910569001c40510320310b96980070940014004490202e8840068003041c11280004002c007a200b0323800e540081c030f1540c0f08509107401140240344415481d40c240390103234001c3d1082d14180707170444124400c05a294041c100060351401e4140c1c4003444603102d00f604000c07000400721031076030003501c4507102003240307412107200c0401d64044004080c000c82d210744085c1e00344a0041e08001d520141500c0302d0750030702c080c0c0349110500c40740b1441e0503030b221500d03880d03071000c5442c016041600401c15410001e1030751250b5000e800501303500da500a0311500105038041042e480c0310300b14420500c0781d980c074a0800c0361040001700081c07000340c0d888107562150080200301c190307080d440700c407009109031203041c02d164081030003020b0b040c848000c00003200000c02a20f140c41e201001200002c215010140c0003802c3e1070410500f20f2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 821735233 1250 821733983 821734007
    0x1050405010b0436020706020702100c0203030f0a090302151314012003120c0310061d120c090a021803030703090501050a0306081c0e010e010207050f220b01 69
    0x100d003008100a4030100303a108091000d5080400801c8400241102d10102c100b104e01240f80c0303000041610070003220780d0041c48210b1084400345100d44e0704080480703000520000003505903004100400c1000c10308030240002c400c0b94074003011800e88035404140304810074040c200e901e110200b13007080040c0c00000c0b903a019000d001d09891811040700300080c42850b010203402841d40c1a00c15540180506000301d90841740d0020303004089041c0022003054591048801091402c10b410300890002c0c0304455a044a482d1101c0d0001014255001c12480d001180f101c110703070380701d00c84040741076450300c0041324801e8207032040c01a11108107074051006600c1c0c5034060b9100b40c0082002100094102609800740c52082c40d040e500d0390086c00040c1c0082103d41c0228042d84602031140200c10343c0940c00440604041c1e9824100c50319083c01500c03044d03011801980940c220600601a60030420701c11500f071741005060306581b9282c0355241d11290300c0d0108016200d0f0300c41c400303881c995801c07020b84801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 821736483 1250 821735233 821735249
    0x20d090b041a0705031803091507031103040e010510170405071401090f14031227040b240f04030c2607150507151a0a03030801090926030105040501 65
    0x40352502d188010038a101c02405000d80b122000240110a1001c00c1580c9017050080c0c480d16851145465503030154210150803000520060780c2339a90020200541e03088601e42242c15400d130742050200400d10f100c507800340d010016003192100003007460300c0c4814007442c0610301a002160810024820000364241418140001031000700701007000003040c2002c48030049060f4020801b8007002a0402100c0e0359907a44440002c1606102000707511b90700c080482054072610001c090100500c020b40d071445440541c48a1011920f1490440c1060480802c003913180e461454900442107a40036604143c006490f28a100700701880301000000820b0303100d5448420a0401e1006030000e0b5584000c940103058000180c0403013000d105008400b1b5850b000e40c040310407030110702c5000008000f0001c6000b441c01a51802c88118150705140c035200003500d0700756075020111780c2460344020140880f114105c45212104000d02c4188841204c80c184000942e03a03090755031b5140200f000250f070300c183c002540c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 821737733 1250 821736483 821736533
    0xc09090201021f0e0f15060d080904090825050c181302010e1002060901051f120c0e010b0c010b100e10110f0c121903080a020d090b04 59
    0x360380c000580301c00294181c56060206501400241c0240584140b001d81c14803907075001c410041e101241303000341e64504204054481d9502020050200b0180c1130140c03007940100961040e03414a03030403034070059000703552607440c0c00d071000d2001c840741811410344840c0117020f2940030300f004018048081e130070101b220400f0903542587e508112215024044c0b0f07040814030244e580859010361a1071081200c01080351060030324005000e51280c0e0100c0c2c1c500344551a0900041e040c02d122044040b62070401001710b5111400d00c0750380c410149130307888140c4552100820004906414401d01d6020f032034203800140d11151906030030b50948000b545200d104003409854151880e45c411440d22007440d00b195004804140c40605881210000011080da4020105048400b01000501529151080d074094211041041d0390350341b1035601d4401c01069050401402c004240300d004099045255500010f242c95000c400000c2225004803045645032450410007090040320913004040b400102c1c0040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 821738983 1250 821737733 821737751
    0x16021f0b130203100506160807060b0108070f02070b0c0c12010c0f0903020906090c09180907050a1805091e06010501090509040210080a020903010612020405160e040f0b04180c09 78
    0x1392400b203600845026020208010720072085941c81c0d00d070207a41080c038079540c80d200c07410084083e000c480309460109444d900407824040c410440402004c220340c0c00b802046042020080d80c0b036004042090491081420901640e40d541e003003190100601c0000240050f02c10390041c00300b1041010480900c61044030801c00b42c0c456550b6507600c602d0440d01c0000c0d5a8074869403c4507402010b003850b41280c500d0b1a88400125001d030f03424000c0d1000401c503441c02d5a20b8080007011130444c0100b41d40c1d1424441c454802c03010a401c001e401800004c01e030341d004102e0340c10707030810b0758841420f410b40c0341d0082c0c1c0100040d5801000b5000503020590f004e0b82603180030340106405d00b400c40740f081c08103e807240018200c0000c3d03a042c0c68400000800a10500d6564465030301d0083c04040305070312851411010458400b40490310050380e003195101c1d190030041c620200001001403801d0030750036075160814010f00760b40b148515081008010952252901b590902d0510140305400c00d10380c2900d010060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 821740233 1250 821738983 821739001
    0x10305010e030c0a080a140d0902030118110f0d0512030a1b020307020f130e0105090f06071706030a06020406080702010c030c0c06021b0303011d06040603020916021f0b130203 77
    0xb0300d40e03030308000080e5a07075801910843c2c00810010080b60a81c7c3c1c0481c280010f0b141e15042200c1c064000c4000f406115840c240b50032418100d203400070401d0a8240f4116158100032003804503aa10040051040b040702e611180d0410000f000c0c41d40c00010b00000b00881641584282c600b403003210f0f50002110280c0c0c2c11b029540703200c0c00320081c3c4168804440f0307400070307034a0b01c040c8003118160550902c80d401d01001014040c001c251407032a03650003039a00c0f0160000b400901c1c0382c41050950f58441545100307207114107404c5001ba115a4040c080c4c0c5000101046c0540000c0004002d03607500c20101d4a00705c18000d00b150060b01d50941098100010a21555807102d01e14a00301d811000040c1c1e02e0501c628114108045084800200e0202100024400e2000c1100341c3c500720884400150640c0c49104204c210f90303150100941c440d20320b40c0401c01d0b81d403014076111120742c2d444c01201c81d1104021401201c180603654803802203501c2c0c80410040d400d00f48238080c024000d6150030350a5052050030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 821741483 1250 821740233 821740243
    0x1030c0b070807060b040905010c0201020d05011d061302090414041203050108210403020a14090f19023001060f0201021602060c0a06090308040c2c0a0b060d05010305010e030c 77
    0x8058415500c480b117209081d6115408144510b6100008020425603000041d0103508a03008162103c8c1c502000041c1101085000c02c03001c1c414881c800044e81c1d200c60400040012081416102607800d20030341d0340d961180c0c440c1800d69042406458480c1c607242c9085406003440b05100c3d402c0504100c0104069480005c4d90300040c000c84084a03c045c6046140400c18081c5900182d840101c0c060005114426581c614440042c250b401381900d83d58007680916211080d00c0508600586525180c448402c07a0b0184c82c9000c403140c4c5030304d00c460102c245065041e440c07003e4138074908400c10040102c02e40040c1400302c1c20009000030f50074102d0116000300ea0081c03000f1f020b800b9800020781e4010b40700d400e0001803611a4002400c000c611250708000303040c0981102c0480381003134516400f0500e03039030030b0010b84c2c1c14401c02089170340180404014480060400352000010315201c0e12619201e1703035810042c00d003040c0f001d58000b0f8198510b041c540c0c00c0d0350340b81c414800150000c00c1004224030000c11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 821742733 1250 821741483 821741497
    0x19050c07020a06032a020a06090c0905071e050d060306090b0f100e01031407080607031b1407020411041205011e06032102120403030f080106020102090d0f17070b01030c0b0708 77
    0x5c0700942d07100001e0b00c203074206448584000c080320b1800c4c00040400c201402108161741c58000204102d951302c040541d2400c4506c08005403c407007030309030414924801c800404881a01901c080b846d50769036911141521081c510480340e502c000350030040781d01c40501e2000d40c0400300d0100040503a103007519440501d5018003024004c02007100e00030708100d40070032881c3c000380701d020304481e000e1420a01c000c0c0104081005252a105902c2d030034142e261140f145184105154001a442c6c81a0713a803c100080c070403803813000c020180512000401c0b43c2506926041079024a0000c116540c2889020030071a880845080340343c0d1034141b06001040c50000340081d599144500401c40040244090780f414006010405820718002800310402d607100c400030f041d90328207890300505662949416801d0703008001d181038000c01c4e00049103011034034400d0f55540d840d00640c001c000781c1c0c0b100e40e4954140c0d804020103640c0440004010001c1040e2000303140002c2401c030400f41d040032610354903143c00e446051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 821743983 1250 821742733 821742791
    0x304111e0d1a01080f0606060304200d020a0b0a08061915050409110a02011d0318011101050c1215030d11010b0a03050d0306080a020f040519050c07020a0603 69
    0x41d9424100403086001e0992000041588007007580e41340d10a9650b9100c4c081e000002d8014000400c00030b081c4841924002d03079026106400c2000c507503147e51180d141c801c040c02d0b88540b5408448001d0b88580300024090042c10003d903070360300c01035480a840f5081c0a08800d000b0090350310044070303218a080c44001039810803101c2c4641c243c503494007284d16000d81c0d0451019549400c00080028042d10002e1490b02c0c002d80080c82810140c1051004031680750f2031a2003560010840c0a0700480c041040340303503481c414141303100b007005a600202d007100d100b11407403a0f40003400981d080c0c1940e203501125901225204102c1c1825050f400400c0e203602d12600c10100b400071440c0070504020782900060030202c1d0107050700d0320050ba82e003011039961000c5201c18001c603141c00b0340031503e0140441c604107059009020100707101c0c1d40c1000c2c88001c200041c2200e9001050315140129018280181400341001000498403030500d8010440c0d4821035500c601c05051811a6100501c80105c002900c100450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 821745233 1250 821743983 821743999
    0x6060409080f0d021206010314011e260f0f07090b0a050306040f02041a031e07080a03030207050c0609013e0106030c1a04170c040c050304111e 63
    0xa240c48001e500a940346a00e500030007144420462203513a02900c03090003011700c01301068640b80300650440d20354a120f406180c101030014007114100c0403203c00f070008440b5407000740ba50380b18081c200000001000c140290460b40078030114020800a1041383d0340c0180140002404150303001d07654911a101d1410281e484180401f03c030b40d508a0240010040a03068903281d14091400c031012400490b0224420341c94950000b00c011100085045011005070042c41c4008024140d801c411854407400075161140b41c50114048005100401e8400e21940700543c031501d04d0301e41607042c0f460384a141c03402001c0502003a082e52383d000841c0411090081080c8201c1e0806e00001c0a120740001e044481118030506003e803800815400441104d00a00180007050b48036200540d5124030340c0c036a000c1d04c00051005200028482410204600b5844200d07242c03802c82c10042000d8500ea550403101040f4003000b00000c0c41100851032442c803a0031190f45140f40580c8004d01003034002d91000f41e02031162 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 821746483 1250 821745233 821745251
    0x1605180102100501141305060109060e030109060e030712030203070e060c0a0821010e07080708090a0f2a03020310021303150506180f071b0b09030301050f030c03060604 74
    0x2071264040b09641d5090512066844006400802400d441102c1c012010b14000002e0300641e40700b440d000d0340c0c05948224449181a43c11900300c1d00c450300195141d56210060350000300b59100d20440100c0300070155403202d080341051090a60030060030414140100100130881d03500040d0f80e0825041100c06944414074518500d142c2003050100600e690000503818410080010f03801c080074490000000c1c0c16030302c89005004070b1909840304008100140c01042c100f80c02031000581c0448500101e4941104d541c4411060010000d403d0300c050503e9801c82e500d0032080780041c010100440500200c19181d980807a0351643c0345810300300ca80380c2c0441d00703d1020081c85410401543c0103071002e1180e0030741400110062a00750790003403144511001c01d000041394040054400e0a0707401d800940b40d900d0541c1695842c0000b082d42e201c3c034941510b140005100200b4003030140c04100d00444d04ca604080510030001c5884038500e104c2da2181c0748511031998009011075204500b96004180d20701 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 821747733 1250 821746483 821746487
    0xc030618060c0c1c1e020c030a06021b03040909031716050a050d0603060b04180c09020702040b0303070b160c0f060c110f010504060c0c082b0204030b090616051801 72
    0x1190000b20b550790111003a200130010380c010010144002600c40100100000700401d0380d07074404600702c194268005071154804507060394042c00c00400c041018108541441c0c07803e0b821940a40c2100000c5640c48000602b8180d0118000000700c03d00c0740400b1242c05e014416100340b0310f69a40c1141000000540780c610704d440381c0107451800900c0c080a2005640f0b900d051340140c40c4c1181880d0181c0d00d4490091341803600c3d5070700710000d50303001f01d0801c0c40e40b428501543c020354860300003a07030010748500700340c640da440400060030220b0194811040c0745c100700c500c0d1529540024403c2d801c01c10401d4184002c149410700494003503921000c00941292001c4054030340103090b0f0034820075405141703954041d000c419004940308610034501002030480303400060341d0004203004003070700304401031207125102075803250001c0140f90103a040040e50440c40703290341c050340d105400c22901d40d0044001d22000300d2042007842d0b003184111882d4240c0101c0d1540040c0680910298075000340c0c01c4000c6054a030f4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 821748983 1250 821747733 821747743
    0x6020c10020f010e0a02040f1e0c0207270e0d27030b0f0a0b060f190207031401020901110c090f07090504020304120206100b030a0209011b050c030618060c0c 69
    0x41032070b0080c0304005601406603141e00d0501c2007a401182014084a4006a01c1c85030040720350340c501c0d035003483c1c040b0304c400e41c00244601d100e40070940c0300788080800e18980b03600034941c1c00c40429220411090030200207005917141417070341080c50390048520b200340c1354001c1030368071542003c1002003c00414040c44011915015400907040c0300000d8288640f02c0105000c0ca482a05808801c0c0488405501402600c0c810380420b0440045c05100b5000410111700303100111400c1c2d4030486042640380d440341d0300041c4049844607050383d030000c7e55070740658111030491050b503020805008401c0000c80840d800b5403005265407080d88180b000100b15501071003580e4041c0001400c215203030701d81450584c0342244034a40c820058841d4100042d404c40c0c400c19410203446200d40d44506585032000c0c4100a90002c0301110305029445256014081840b5092210140614010f0100c1c540c0172090604103480507040e01a90b80c800d190001e40303603200250480c0c202d504908d0040da2041281e03c118181 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 821750233 1250 821748983 821749003
    0x603020711040c0503040b0115020607201204060905030703110918030d09110d0302100f020903100501091808042108030708040c09090314070606050d120e060406020c1002 75
    0x2c40c0c60049018459a48030018500c15031180c85800541d90321820440350700c0e1050741d00100180c0c8260f00050903070b4032603010b84818001c010200c856494008208030b00b840c605481040320400c0c049000c00806501207240c6009180079006440000e040d0740300c4080c0310701e00328181d50083c1180e03000700d07440e045001c040c00241c4032041c003540c2c0c407041c442c264a0f0140c01c12a0301514522407210b840c0d4560f2510b0030b28600c0240d0701d42c00800350700300f14400c110050801070140c103013030035803d0011040c540c81c00c1c804010864516140080c1d203604080343d1000b203c00c8152600c500d00e60214401001858400884068440e40f4550005032a520900200b600301107900092a0741c0c2d010080c44015a080b01c104c42c040e0f4890300120b5501070700c07010010100c03160034901500158800f01410383c81d0980e94024101d00b40281c0700490090380f1000800e40480f5003c50494607100000000c1107203592085020814103003c42d031181c641450120001e58403190942807903c9002c40a03402a07a01d40200846840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 821751483 1250 821750233 821750239
    0xc05250809031e06220b060a050d0c08121615110403080c010509030a020c04110909070504210201080604050601031508010603021c051207240b0f190603020711 70
    0x6005803000c81d414019060f20600d01d28400c2101041d04c0b00200d030041c408902110206046946994859044104020740300e01d802c000b1440c80402c00303442d16104980418043d1400d0529103141c41c0d080c07850145080220300002c2d4041c01003100080f090602110080c0c1c02041411a508260034000d005012107074298000c00e40c00100042045508005082a130400d0350003007042c2e6030740c4854a6201e02c1001b00800050308040d02c00030192401380c5c044503140b005040282c3c2802e00550109254140595030440480d102003410015000c0a00d07494258a0f0a0580020b460f01c00303500180800e68060300b1584165128000264664440da01c00b1242c1c1ca40081d04100466403600014005e000900059016442c0b40f92804542c01c144111110001e50010080104024541000704a40c0111400310f4481c401d0844484500f0310b0808a00e800300c81004001450007150401c10813034401d00340489000308998050280003484405d07094084400e00d0a016075110b040d0300d005040002032403511a8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 821752733 1250 821751483 821751493
    0x30b100e01120201020d230f07050109050307051c021b0d060f200c063c220302070519080f0615060c0703110402040909030e01030c0525080903 63
    0x9030308a4403542d540744280c001e800b6151131070b03940364085900c5869841907000500c80e4020b4414445c44074401400c103404810040f5042c405283c2d189400c3d00c580c0941510250301c04034044007404010b001d60300c85c205c00050340100340280314a0181d00c5007100d9802107034502c0043d04040c42904c66800801e90298041001c100c00381d810b4400100030200c0c4000c2c3c040240260b500d00025290b160b0440b880c2511510080001c0d0356500c0c082c110046145e82140c0c00440e0030060001001414844c00c14805400101c0b05a00d01d004090490b80c0e6910745200548005090700e050301198000c9041c0b010344d007003507a107c0f521850000c80032048440700d40c0549c41c1e6101d03100302c04a69060110b101402200c4000000c00c0880864003005181e001d400603100b05600406010000039400e80341e41001810301400c0541880d689812940c11034900040590100e4803060b4a880c1e6982e0611903907143c0189410301d14241100d0144514403031203410f1040075840840909101401074070016074821010080c21a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 821753983 1250 821752733 821752739
    0x1e04081b0604060c1d0105091e1503010e07052a120d0b0a090618050406110309010506031006060f08130b0c0a111203071b0506012319030b100e01 64
    0x40000c0c19119512400175009100da1000c40c600c8030400d1700c414605039111403c1044900030005410001c010b100140e41010006084c030307441c1c008444000000c1034442a8030f961400016240ac000001c204034100401001405120800c00c000300c40d150300c0100390013000f000340c060b61a2401c1c0c3d8119505c4003506011130300f60880d804540061300380c21803d540d03c1c6c0d50155520302c035000340c0700d03180541c4100014058915070307035505552245600030300039000031820b032210140480480c0e10584502d40e00d070351900d04202c0749007400c0040b00c82c41a0220010480c0c14a081e00c010010602d00c003200041020321000b08404041c2200001c0c1e1542d00f291300043d55040504514155601060400010504452801000503c045041d00140e200c0350391880c5140d50b0f1030710443d102d1f600390308144441d542c2c03a02c000000c0b68041107030a0280001e9090300500d0880c0026401c449107016200c01e2207180c8221030324810310500d1150300f044079800300c0850100e8441c8160051a504940c000c5d80c45005810000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 821755233 1250 821753983 821753993
    0xd09020a0b03090c0a080c0904140124151103030126030415110604030e2b050105060103061e1208070b09060a0e031e0903030f07060203040b1e04081b0604 68
    0x100f10413400c0f81c0071000195a540e2031602c8403411108260702c0f90070440001c010030045070741c400d42c150091000140c0361849507028003212081071a400d04c5001060018402081e030001d4000a210050920300030340700c6400d0a0304d903a480140a60154103c071004074152036440740c4004050b0b40e840c48280c98956071181500d800480d0021200c80000311210312500004c8000b086050140360559100c0d81d10700c3c07865050280300c50004040a81207118100030780000c1c0c04030b06010755158400ca00114090030803000060039100c81e44c22050721001c000f03a40500c001d0070482c8400841d100319000c50220203007810030100350b00803908041c0001150b001000965480854580d101d135000c1907003004820040340d0070342e0762801400d01c2c0115403582c00103e804001a650b01408801200030112403130180309001c804090380040008851498000c02844204250044c010b60701c01e50000c07900e80c4040c0340303990001d0948030140000d000f81400243c0d40c11210300007181c43d00458030080890b07507a402e1a280c6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 821756483 1250 821755233 821755243
    0x101403010b120609040f020418060f0b030c10022515050415030b0906091f12140303070507060f0f1407080f070c03080c0903120706050c0f0d09020a0b0309 68
    0x49090460b24000054490304c1c000c2c1d071240c026a0082c14100d24042c00341c5c00e1000034501e80c465000042a100230030400180580204080019040004140a80420149850701a54005803842150324a5117408000d500040001481c000e420088000c0c038518411a18002c90030b4201c0103035003801114000c1d5198008004100300c41200303102030030800241204404441118014a500c4050200841c0d15841e152100503086490b403900703030308890a1141400210b245d070383d101841d00c082c50403407401407000c8203202c0501a590303c0f010790b02e1840c200c100102103115601004109070380d280c2d40d240d2501282d900c0111a02c40c81d20341000b52203030002803000c50440c1140d0800c00521440b0018409125400d6024043c150588408070028280d5a043e1034681e4014180558048140088500e555082180301c1c1d1a01c282000966524150b05012050b00c2000700114201842000048055a404001c8890301d6820500000d1031800c6880018120805907021000959000c018050801d0002c15 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 821757733 1250 821756483 821756497
    0x71113090b0f01060504030b040f032a140a05061b090405151201110f0903190c03030801080601120f02040e12091003060b22030f0506010e15030705101403010b 70
    0x2070301e20b220b0780c0d960400b01d6280c8106d010041c104030110f00450700284205100340d00583c480d080107440d6281102080100603113140546159085030749111003030200403507032200c100c50303000058542c0548a48415658041c0602600482001071544405800d1200151407010b04020401c0c040381c1001c9480104801114034464072810904070643d403115814400c080032030700038803d03650a01c04000c244c020740d500458101c5403d03010700c204581c1c1c60b014001e80031600c1417055900c0001d080c114180105081070503008011150710900040c003e001c2400d19142c180ca60207110354001030700da407000c14080c0c810903403000c009100e5071110b6030039480144042e1880c008192414040003007101c000f1400d550703c40c4070302d4014001c20064041543c0711644415105e003040d00b0740c044031a90b04e0783c40b202560240041510681c00c00700052064108101e1604d401c08200c0030805001070240d0700180d100c40c031511541344034610b89009244802c0c002d0b2060042410080106901d0750307500d1310040c0301644100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 821758983 1250 821757733 821757751
    0x2152101061107050105030606090a080109060509030a091a04170705100e0a180b1008090c3007080a0c0f0501090303120504060f0e010e0120071113090b 67
    0x2900110300644035a080c2d88240c05180b009207070706490300006403900c0c2d1002d0001a0040f404000700a0300341c441c0c50340076004200c80c0e000001e404542d800c10108a59000d0410221030b01b08000144131250700c04019001e4650b0980ca080c04c0411444d40e00741940b10356400350011041b42000100200400300c0e5400440c0c205990b50048100440030840b0001c800d03119442d445080300c5c809010f4011600c860304201911403000103000e04030800000d440950759000d00c1c1c0042c4403c0100b00b44420b051001d0141e010095a650b40020000070f07070381c480300788000c19a8680d080030074541d044900040003440010300300901958940b20990406030402103641c000c0c0301c4c80000720752002406501c1000c41d00304403500740ea502d040c0050038803408805000d024005507480b50700c402c4030400d6054607115130b02c2c4510070f09000040081440b8800c500f9500b070050185441400300e03600c040001080c05c200c425080d40320f004510030038141c0c000521a0400c024441c4256860100083c04000030644014012200300d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 821760233 1250 821758983 821759047
    0x30f050d0f15060201110f031815100e01140402071a010b04170606061c0f060e15031b0d030c1721040201140a020a060f060609080a0b130215 62
    0x1c900681c01e807001b01c41120151042001640700850303090003d0354101840c5542034140c5002101c1d414030304451074032100302d24401e0100f407100c29540c44165000600c440d0381c160380c403036241c01001074208032420920b5020f560002420310800011011082e42d00c051501d403512556164411045241c0050042c1000e6072007030116240c000f80c00146441c8200d6006120034a009000300d0400c541c3c0001255030859240c903004100309188042c014071700136280c1c84401401c00d00e0559520214034078803a40d00c6010f41c002024410500480c2d501c003602254058500095002041c0f41c1151240011080944140e403042c00d60248911400020207025440302000120144075411681c3c0120303054038001d020850000f9500000c0c00b1f10405483c2d840d00900507a0000f6000d51244010b41d0415208a04641d9542c0403d200340c5800154100c007a0240c01c008000000d466600d590070424003405101c1c03040350b0001c81008558401c0410118084003903403180d22882e1181b24104141c03280b000c0035003010340c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 821761483 1250 821760233 821760239
    0x41a15031b030103321218010309050a030809100908070203011b020d0c060605060c0a1403130515070812241f031503030c1a060607030f050d0f15 64
    0x80420781e07068980085400d03503034004500300c403002440c1c1d1580018001500944064042d1740c10b0103d404000c081b0400c6030350b14200c650744140d062000c08002c0e414545458848000b2400024264a9841e45414008070540741e60a0340b514244015483c3c560040c1810030040400c40140d001d410380a100b50001d202c81080d04c1314403400340d1042a14400107a1041c802c0d984042e00c26240080b09038040c00d0000303241600e850218040381c4c412024a6166440581074000308110141032100708400c5901a40c1070224012010340900401d21074148103035100c690285030041000c3c00c80f20140e6001e03c04590319002005401c00c041c00494903141c001d0b61120084171100a402d02d21101c0c5c0f0001041c410340001402003a038111100070098004142d40d410002e0f41070b551050340302c009075000740c407046000119450222400c02a00c15407400299064062050980b900300640d40f0b40d590500341080d400346c07142c0c0110f405010714170811040034102811004c038a01298040e14072401c4c46049020b0880d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 821762589 1106 821761483 821761531
    0xb0a06030b090c01140f091e03060112060e01060e0f0703110a2a030e150702060d0f05060102060606090103110c0a05010203070906090f05041a1503 65
    0x11098200725080d6030440c1c000800444104200c078901b00c00300000c0a514003503284410301540c0050b41d04d015003a05106084440580030301140c81c55a1359100762803011000384403e075070302454550642c07802541030085506603441143e00500c25112201082c5a010000381500e0030160381d20203040402902200800f010005a9202c2ca404000b050010f521141d40c200c03011004c100a180c42da0003e6044890a6241e12088404400a140701d244c0708109120310500203501680029001c50140e405610120841021180030061a615100160b07501c0d42d05948090307020301c0600240505611a401014aa200300b09501381011844004035103003908000c82280d90b030350040104040c55a10080c404c00034420780c500341c61014500342c402c204440d51409507500858070b50b0750103083d040106c0d61441071074001900e0310400d581100e0b050041e5400c140c4030780c2100b4a035000030860b806 = true := by decide +kernel

theorem cover : BRFrame.Cov 821582733 821762589 := by
  have h0 := BRFrame.cov_init 821582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 821582733 ≤ n) (h2 : n < 821762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
