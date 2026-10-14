-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3143
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:47:19.959731+00:00
-- url     : https://prove2.me/submissions/ee14a47b-5c5f-40fc-9158-04d5c811f035

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 565107913 ≤ n < 565287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 565109163 1250 565107913 565107923
    0x30807050d020606010e210a03080a0b030312060603070908071203031d0604020603130501140103110307080307081804020d0c020c0d0b24090a1b090b1806040801020a020703 76
    0x1081c0c03080703031100002c0e00d00a0001d06650400c02c250b142400300d410b91b015540c0d800104010700b1181d064604100d400e000c0b0b0100340b6240030040e160405101c4c90380c202005402031403825200384180c1c030007440c004040714032035440440403800c418481c403200c0e0050902c89080324021525810b03e424a1480c46070b0440010303061101c07030955400b20404406510f0310050040032240c6440d402c0052940004209100b0a80e0020310400452405d0082025500381c00c03410600c59411804c10820014543c4141402680500c1c010480c111001040f1501d4680010710303c0e4035010603200c030072002c00359a450140c1c0280042440c001145880d0b10615094441d5004c0304c0d12403c85500b0302090f0810000068a035030b0012001508c0c0d444804105049003803c10702a203201c0748444001079481c902039448503051a5103140d407160f070015210051f40d51100a08080181c5440c1c00c02c00c0c800b03846038100c0b08246291205581e0060788070001074401902428009648a03241c401e002550340f0000d10041d03030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 565110413 1250 565109163 565109173
    0x8010b0f090303070b0a0b150a0f0521011d090615060d060806071e0f1101062408010f050906060a0e10050c01150b3c0c06100f0501110c06030103080705 67
    0x85070300c1c02380c03d03400900902c3c0303459904284411600b542e0b500c91036449182444000c0082e641105219645443d02074135240000e0720395410142d8191400c2da8090600344210207e4051103455040082c0903503100d00307807c560310540220034022442c1c50040f428002e842d1400c018021807020b002103102c6100d601c05640d402c407190140d03503505281c14141f03c60840411039040d02c1e046500d110f800e5100c270351140030001207003043e500e240e00c1a100c194000d8091142480441002d91150700c10460b0f8010040d05200540007414800080c002c21405000c191180d40c0000700c2008a600607010103951140c010030004a084040307001030500e0b40903e451540035440c2583d000759403905280c0220a03110a14012410110340380480080c16071108082c1134800341c06070507105a6481043c100302007012041c0c00c035841b04c100302d40d1249489030103800700c503001414035001d0054192046140c13084072400d19118403900c01400b0500e003411404680b80360032800020010050042c3c542c01028800d12423001c840d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 565111663 1250 565110413 565110431
    0x1015090e0d08040f050f241b0d0906090507060e12010203010819030c0b0f0a11030c03010303030e030c06042108060f040f150803181e04090809030105040606030506060f0108010b0f090303070b0a 85
    0x230ba48400d207901091200302400140c0c06044c1592000200910450b000510b41c185512001d03d081941d50105000600d009903416490410840185002034004000d60a40d4100b010068454843c20844180d10141080e030500780351103000c0218031650480c2c02d001050802c546a4203404900f00c1d80302c652542003c0304925400d4103c4122807240c3c014141030707801c50742035685c201c1c00340c040e002101c080e40c1301c141301881c0307116018040b40e406284961b01500110020780180c003844440c2c02d10407024015000c00b080b0070341e01c5001c00410003103030854001608000340e10000c00140b00c041c1c601000e4940c2c23080013142060002004090510010360411346140303d032010041c0c5aa281d10740108400000740e0800c0c904c4c107141e045203081a10074003180e030520000d000400c0c00c69108841c1520910f442d604c08105100c0180b01c0c0541110083e51111500d281c0000041c000090611640341e86100c0003650003090f90000d800d862641400805690b0b03908041d007001d00044200303a4000d85507501d840902 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 565112913 1250 565111663 565111681
    0x8130b07080601140a02150406140a0504060b062502210307020a15052b11130801060b071b050a030b0a05090c0a0b0c1015090e0d08040f050f24 63
    0x140d025038126600500c500329104881c100a2040a803003158202d2b2117100011f02c03039aa1f40003040c800c0506000c005450301d0b06003044015034092a400030f0045030f003040000b8210708048a2960b00c50f200701848804803406201060f0907054459129a060500d4148020300c03800100043c5402402181d41300c40702c98682012034030703132618004694045038041020f4158008502c0d4809087c00010380c141070500620382180c0c05440c118480c21000e88400214603991400e02d17140c10010700f005d000200103071800d200c420703100c030320603288007800c04840001150b00b00158040b049024000180100704299038910b449500240180c40b0704944604220010707914400002d104911490b0041070041d00b1403510703451a00c40e03440010070051501031038001100300d007180c0c00f840908901403405010b04510f0049240300f1192801e0204000d5000328003c15803c0d5400f0400c65001604a0600040203e80f460f000b03141c40028248540140242c1c6102c448014400078030140f10001d011020440b59203203910 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 565114163 1250 565112913 565112917
    0x412031205071b0c231c170f0d0e0f0d020d020c0111010b1e030c010203070b010302101e0203030601091d01030308060a03080d0e1608060708130b0708060114 69
    0x1400c0002022202021007803d120b000340000f060003040c031040c0da03e44549803220564400b0098000010058140e0041d9081425440110340c1c6a890410008041660f4441c5103003c441d070b0103010120086464000c0404000880342038a1482004008a03a5007070000d039207d1442c1a01c2c4c0c002d601612603082462400810b040b182c4541580c00703400032070702c2c0341c0c0190303031080402043d401c00e0340d80c0301003540d1b03151034800c414072240b80082c0c1a446c0c0140396104062034500c8034070300281190424044c1c400003c2d40b0b0540e0300d05503981100d4006281100b0b507001c40340365070400080d500c000100c107030340e03101c50b82c02000450081400fa030350507852070b40702e040c200da428149803a8005182010001000400d20a8030308036004131000b417050006994030f485410305608011032010405680705c8001c02c6125041000740d4407051082031686541340b62044503526400c000f8410824411014000b0705513020740200f100c146540240e0390011801c03c0c0d01d000308540022240c0c42d0101e166a000f140c941c01824003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 565115413 1250 565114163 565114171
    0xf090518102304180501090302060f0a0b061602031203240402251b0e01080c010e0d0803091f0203070e060310090b150f030702070f030c05061b030412031205 69
    0x295110540e00781440002e08500100e0040c4440030600342c40000c40a001d00c1f04060f00030390082c1010b00308810140050680502822980d500c1d00d0409003c0c0d0301d03003805843e9091552003d50240c0c001034008681040008c0342103840c90900081080b0541d1550000c41203600030a1a00c02415180d040c1070104a2140007805101950560556039015005141102450348104031407501588070181c0f000280c400d41c0c2180300600007a00040c400000c3c104071382c00f0310807000d181c2803010381c101501050744802c01c00000307019420000f000503c081d104001e030711885506189000d4099410400303c80083d00162003900c0000d48140805d50140f8003001501d005401485807444224940000704c80280320300d40e40903800502c1314002c1e50380c40f1900c6010308051a8450666542c0b0b2602080c000d080c06041d42210300c007076040303040606c04589407403404000e903002503511503034a16201c1070910f02c0e84060000181548000100810500900e000d0703084818426190071043c01d0103462a034054a108039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 565116663 1250 565115413 565115459
    0x160302090c1810030e010e06010e0606031510031a15030105100e1003051006111c050d06060f02010c030203130816050601080d0e090f070f09051810 65
    0x103020551040110009280d0542640307496a0703000c802c040401c40a0414514081c0881e54aa40d02201c9210038041c81030f94840403005000c066041084091f01248090701d218090b64020000801609101c2030344032001000030058400c07503211031030040117046c044021401b0b800000e41e00107054100040c040c54140c41c00c50026013035070708010a001c20034004091440c00c100142c42c0191564a50740d60000c1c41584507a00842e030752074109102400c45540344d216904025130220b036890441001300c1c1c50451008082c0d0950381c4c03400807610032034280c041c03492a07100207858000e000401e00d8001d080c40064140c6600240446008143c05600301c1c0821a583d401040e010040240000c2d2502c004040500c400c034018209103a003912010302c0d240b8242c002071020f074071503a14103003442c0d0040c1007010415811981012146004030207100304c81d001824080920510040e410706a034081c543d20303400b40c00d015281e088007840702ea000031b2004005440300d00d80441c5070400446c141c4001010042c40310350b50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 565117913 1250 565116663 565116679
    0xf05041a0d06080606031c0e040216050105011a0306010c02040b180f01080102041a0c0304030c0e04210c02010e0f04020f13060903030801210b0109051e2811030f09160302 75
    0x1012050501f80d95a5580030410a03060094001d13a512480600300c1c0c00e410140c07910a81b01145461800c46030103802580900c03420000c503541980b003103022607500003420318041c1800c552610226001d0140c10740c19607845403001381544640c1c401e501c821803042c842d10071100b6151340c1c1c99071068201c4c4254025010608080e107040d03400940180000c03c60710005c28126840c0a582c2d0301e0316280ca10240d0054170b880020b4401f84800c2c801e03080310301c802e079041c014400d072150051403001400c10302c20001c2c024144410b60508001564988150410500c3c0140c81507584245031702a1130040d501110030700039900c4908501113112407058005000781c950503180c0340c00c1da909200b00202d1036000c02d000004400f0034028504005000124018024034502c1004185401d00c882031602da031180c0c004004910302100b0030002c0300c41440760004020f0a00b41c07442d0728042000104400030b004100310700d1102010000901c00b000c200344041900c00c3d642003040d15900600d007802612510141e00c030103580300101c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 565119163 1250 565117913 565117933
    0xf030703081b0304060207030302010c02060106080402040e0111130518010528030807030f0807081b09012c03150c04060509011b0605011706090d0f05041a0d0608060603 74
    0x465004051041840700071000702c10351401d810f461603005800400041c3c220120810401d6024041c03000411aa400501959810258000c1544000406c0680b040d5200c401d03200e81203900703510640b082c00300c901040350b40b0103603490200e5440c0c00b14810740340038008003041042c000301c441c2d5003a07058a40051491034842d228400391030301c040d801c0c91217002804400344000001343d92000144501d5129817039102001d940c1341c1c400741120a00a24010074080600100072001c401c5000348079040b45400d01d410344074140040101d50342a910f070b80d42191001c1c110119022082400381050305072000314225242d41c040b00400c0d6108241c01d40392404841003d0005200d03141c050000303050f280206141c0568483d003880c05482100301c901e5400c0d80c00c1c5940b030b0010300560140c102001020500c03140207103181d0409052850380c48181807260b5003040101120b03081c420b0302c64411a40100032065103200540d50340302a2501c103600035041c03a076450303240c07030b000140100021404030b20030f810090140c02a01a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 565120413 1250 565119163 565119173
    0xc0803060d2102060a0605060a0e01110a0212030909090d021c0c020d060e010e030a091a0f0a0305090115031a1902040605030a060506040e0a20030405100b0f030703 72
    0x604407104030303810090742469114041100c0d951151482003a40184410b040001c00350040b40d503280c00281c0515020000340c051250400e000700c10240c800c0c07070300d01d5015460280e1541040c0319608020b40c800d01000d1004400794000020744485041140d41b80b40a0300d4034986a40c0d4ae902c603005c05000368000d41c080c0c82d50f680d000724841040e660103060003d1542d0680c3d00044c180540240221041607582206481c210824072401880c01203520041d0300e80301445134080c19410aa2151411200c216000c160303600c4003034820b482100c507903800056280d1140c4030015020742000c0382c11070b03195803038040d1a03040b0600a102d15801c59070441c03860410100c0b800c81100c050307038001b4003550101d54801114089812603200601c010512503841d00d49a080c100d511800b0b079100c075031180b81314220030f200a00400c201204da1503001920745400142b49111070300c1c0d07602d00f084807034842185030a011003007100f8080d0102d84211180b10300c4800f000b803141e4030710400440e810140f00b0541c0584c4000c0e41480007507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 565121663 1250 565120413 565120429
    0x607030b01200114040602031005030334080408030301030b060604050f120a02031b0102100203010e01360c200601090f060e070e091b0706020d021306110c010c080306 73
    0x2e0070001c00868044d49550488085110540d011111654008200410110b8000a03032025100403000f030344ca014240c090076000c0c0110440f0100c1d0004030305403141c21918a0004075003c480e40000c0180c2c4980d541c01145490303030802d2109540d03207143d8000141c1e0314508003007218251500101400350305081c079801c1c85104000800090300c184100c0000a025070350411200305503400d0b00c040e00d150269103000090824858a4030305103106d005200521162011014142c15100c140d012a101312800d0740d1550109034802c1c40100e146907036891300542584060b0070207003015405444d08960203030059050f1030000400711a01015800c241d0043c080350301c540d0010620a0740784400410100d40780c1080c0070b40d10505840380c1c00429002c488042943c24500040e6a0000700c41d03401441c080a122601d1025202d1980000c08041e80060180340d6604140d0695910660984641071000e450b080044c0c4a40010520440130384203804c1908141d600c5584030858441d84012001e0075500ca040900c0030b48 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 565122913 1250 565121663 565121717
    0xe1308030601030902040e100b040504020a03030f0c0c0b120c09030d140f0f0d11040e1f0b03070903031d0d150605060c160e06090612030c10020c0607030b01 69
    0x740d200c140b1304e000f5030785600841401044050140c01c3d08142c0801c440200c0e44582c2da81c5010764200780402025075643c1c6051030499070141015076203040003e1003250f840c0100c02c4014840c40d407a24020500d91203c00203820100c040301d10600c601d440c0d103031620240b802402c00d030641c181c2c408644007585912a5007100099080d200150341048501041080d054120542c0e00d0707500304c1b0101c3e8113082c0a40c10f01902c41100c00203200589401d041c104000103d0500400004201a440580b90f042d420748885036001001c801d0111030722810f081c080140918070702e101c150001048110398051180d00c4100351007080341c2c001c014503409a07042d034800e80054130502d540b002e00d5548607000641501c612004002d40100301307001c1c00e06090f10301c180a00284880c0c201d010150000e404000c1a03407241c0c02002d4100034100c0344084070340380300c080c0a0314500c10021500018001c201101c0e40c11401500600707110001d075030640d2415511030604408480000d100c5c207001405c0080c0d0701c0600a100a504240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 565124163 1250 565122913 565122917
    0x3070e0118060c02030c011e1d0a0909050d050c100911060408070932150307060203070c09150513090501050c09100e0114132d0e1308030601 62
    0x10103a01031842403168002d610400c04180c21000fa00210310741840095620a001d0078900c01d020902d80d408100452001b60880c140080601c1030880060705003036546102000070060100075450710014405410703031301c2080754030f4841d200c50452028000d0080d02c0225608000600c00700c118200c1b180003030f080500c0c00355001c00900d80c05240a859020082c4040c00f10800180703401803800b612041100c000750400055010103880060040c040032400300001d58401488450341d4441d001407118940c1182c0718540e1620400b0740015690350040003600095002e09107400300306586550000a43d070342c503510804e070400244ea09105502c1c000500907250159030303000040a884036600c1c1c80c01c4400075035107010002c07004501c5194510700f0126046403640c0304d18054150a0f40ca030006002c52100c10092141c0c1c00e40491000c41b0b500d516100c2070010b141094060780b8a00341403070f031801d072404c00080007034000d043d404001c43c106868007160390240e110088509101030150701c40c01d01a4001402280c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 565125413 1250 565124163 565124177
    0x50a1805030601060809061609090b060d090507090b0a051c1407140a080a020112180c0b032a070b1008160503190213052e05040506010504080303070e01 67
    0xd1692420418180030b0a919102e40140b07003804101b492412400400c2088500c0c0c0d118480d22000d41c2c401080c2d000c4a00c22000441c5ca2a180000030300940a4030f013101891510303220843c1c081c020001800d600301d404102041218803c80014000c1282480c000c0b00d401c04120204080f21a4410301ca442030140520b10070b10711240880800e500b051100e81c0032040042000040c0c0703640c1c0c0b40114240000f0b044140080182c010703594000382c043c0100100501032541d43e600200b80d032038407030641c549010381c3c0b05a4070881e042d142c00b0711040315002030300d0b90a07869036500f2440410103155210110401400400c003400c04140ea580c1c012824002825105410160352001030101b100b00044103900840300702c0100401d040400341850555520200b038404c1c0801c6a5540168a4481c14202d408006080115440d91495020790065680c0300c072480e2540311240b20f1040b810321090002080c0c0d00110b400348800c0c0c40382401103945c2e001301c2c007462419420030400705001030b02560040b1a0f03540d060400748 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 565126663 1250 565125413 565125419
    0x30a09092f0c0129091312080601020705030a0510050c04060804080906120c1c0c05091309081317012a031d10060f15050304030329030d030c050a18 65
    0x2800c18804c0d5200500c040704810300001c1407901040c6258000c042c2c00710103002c15043c6c0c554400c008000c407605001d104c82500810200c0e442488510050b240c00f07403c4840088181c42c0c029565030341081042902803400c1e012800a481c5282240d048400c207654000443d101c544500d4440d41c00000f856a04c0340f010040c070300c00c8040d002171151040c140d02075807a89030280400302541208101c0d07040c0740e0395450504955a00c0350400103451515000740c9400001c2e615407062100100f503620000b410110010950411280c10104003070240c0d80c0b0301c090a0141d09c0d40c182107a007611304a000c01d94421030b200822500c0400c812002038101c014615002c9201a10702c214103d9510f5218014103180d0480700e04001e1307004080c054000103218440500c504645480c1c1905801c2e0851148107040050001c086003d051003a0000303000e80307004001c3c602150500c05440c0400f00c2079075000500a000f110089102240607101ea44682131081d01c5051800d0080c0c0422240149141a00c41003079000303103404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 565127913 1250 565126663 565126691
    0x12090c030303060302031902010906230301090c0207061803030509040f0509010e0d080c0906071401050a2003041a1003050109080903010b060c1b0402040305030a09092f0c01 76
    0x108021400303a20700094030340c11030040c181800000800041818501481c020043c0d81c001210812904d00f07180900740d09034820221510032070581410484000007000100c3c450a4507404510848580d4080712800d9990b00429540042d81640815a481508400300046401072000b00341442008100080c56070000d190a4108c641c1a103084107169990300303d07503503e0303041048000c85500e101c0c1890f03002c42c90082d2848515204030303804580180c0000c1465030401c40b074160492003002144000703020320704e000c901410080c44004400c1c100c0203480c090841e640403420040380c0c0a5500300f0100207003200a0540c885200802400122000302003a1000004c1082803040b00280c81c8a8085181d888040e50201400d6030412013040b07200b030008101808030b00c40001407084071250ba030301502c0c3c00e18007040b000038000e004550002d0198000003c0800c4029480a2208241c5000a004010100ea040b01d020a0540c80030644d10010350080094000b09045002034118502d900c030000c00c016108041e8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 565129163 1250 565127913 565127933
    0x70614070627020a1719030e09010605120a0b01050d1505180f0603070518040f120c031d06090d1e0c06082220190509090109121209 58
    0x2040c1058580107060104510744540b00318000c00917040540c20b00c1c12541062525100c40b02040c82d04506441d841b40d00309800f804500c0c44041c8000c014245540c7d5840024146500c094103505055406400260003402244550810000c06a4505040080c080c1e40c180080c04001d21032020100348400006180d0f54020180900c410454403900f07031410b1400e690201160040c180c00c3c4030390824a8180250b4566082905031080180b40c0c00ba01503c480c00c1c01407103d00a502d001d828003410080990f1044e030841e01e0640d0240c82641c030118840005c04081000021060800d075014000f000318405614040c1000740095001e546094010340307082ca5240005540c9a40880e5a40305011703081161a81003450702d940710744803641e541c1680c1401404180c0746200300c0b80041000584625149841500c9800c0100500d00070f0021410121540a24072a0503020300c5602e12441662000420018041c0a040321096020080a031101003d034020346252800c4002c00c08091382c1c82440300049403070025 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 565130413 1250 565129163 565129211
    0xa080303071809091e081e0901020d1d190b040306092d02060a120f0614010203040f060f020a12030c0e040902090604020d0e030d0c0207080706140706 66
    0x2121800602c034071007a5030310902158040400d052904032aa030210301c46034070a01c0b882e543c160440d4041000383c500b44075240030f00c01c00340441d460541103c4071505d5010000340040c0d5026000c039150516200d070110f5904110810405115541d62282019802e03c12200740180c5240f100e00180552a11034017402c0b50095031042d82e4450711003490b00103100369640b0705c984c6003608401000304020110300002c800010000000d002d000006802d02c038291046441554216860342c060000c1d000910041010304103501aa480d800b4009018446541c0004101c8048414500102c203402e40f070300c2d03000e644801c801621201980141070048000484400c52092032170350584000822320314110300117110442c550721240c0030360310781102d940c0175950308660a81d001078200d90150341e5402e000641000351608403a0801180300c08541500051803d8004803196400c40d4221881c2990346c00c12590740d90480d00c01c0f980821000c0010030315664041008002590161201055542e03c14404c9072090f801e0f05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 565131663 1250 565130413 565130417
    0x1315050d05040f03080f0708010b1c2c03120402040c091517070e180606040f0b0c01110304020105030f090c060403140601140f01080a061d0403032304110a08030307 72
    0x20048008054014403169001b01d22217211180e9407404040c00f80034084180100c8482c411f010980394080109400c80500d0140d011038240074a1424000c0c020f83c1411885000080c1d0b0102d0408400d4140d001003034443c103ca03d8084840c175611280c080c80018000c1060304400c200078500082480c800b000d0801c10202200c1c0da03030003020750342c4040781d40403420013418030801c12000504aaa4aaa0b04a0100200200d0040145883d110320000400503c41c541c000441611130520026008a50401a02c190703413280000703115012010410700410300c801c4600a0110f881400410b921914115150f5801000d4008883c0c0e070080c200c0c0007035207a40060b44100c400121060710118034107002c4c0091801496074411010030034602600064100c1d0118861504024243e400030b459289280c00040080880c0c82d040d00c00c40300c510380500d208445c03c4400343c000c2406c22300d41c0170000f00d40c1c004031504080d03500c142c0d0a25840d40d0f500d804604040e40ca44c0d603401159044042442c0ca4103000071030003400c00e9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 565132913 1250 565131663 565131683
    0x303070203070b0a06060f030510080d120e06100b1b2a01080c1803010f092904050c09090a0510060f0b030c09060c10021303171315050d0504 62
    0x241c50000d05071600281380944d5141021010813007160003c2c1e00c0000c441c01307428041607550f18000840c0d1100c8141c0d00191007031007010040d144d1250050003c0705410700110381803002421082c05190b4a800959800c0350b059403500d420400c810844c0d024000e5400f000107160080040d280c0914944040005c180f00746c3c0f50700194403424500400d042d000a41c6080c06d069002e0b2800f800060700ca80904140b0740e410141000c02c07200c603941e081d0b109840680e0300000401500740181030603840c564010380200c0000c1459a90f6004817650080014072803640000108841060002400002c00010f800e00c480c61003180400000208144075400c42d0010044000442c1d6240480f00d10015040340e02c80542d4150030001d000c0048422011607400e4a015500c00b5a42c0610b108e00510b422a5840280105071001c40e02c8420580b50326600d4080784d010b06101e90040503500b43c8030a2034469001e060f1840069240704119030000c2c03031142410348410341020303401c0043c5580580143e84044804407020034503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 565134163 1250 565132913 565132927
    0x6060302090a080609121b0f030304120203040f0b0f0f07140105060d1505090a021e0108010501030204050619140d0207050d05090102070e06040603081803010605190909080c0303070203 81
    0xc140480c42c002c0c202140140924141300340300329180d007410710046580140005408441901400017000c2508000084a605a9180a1490716600155422111b41d01d250444115180c030010036941038854010b0700081c01e6103071401100581e80100400420b40805218142031b071240d14003d400014001d440e1a141c00d15641c0c262030031140010101403107203224656070030204110011200900610800008050301e80c07000040c40c0948400c4000d51140c982e1091100c4078221106044c0340c810203803211440d07030340ca0320300540c241d000b14040c0c150441c0040c4030301482000102403992110203071381440201044201d590f00d160398041d1502c4000f00c0e800040e03010400808101c113116041c02d500c0c206040c001b041c0b0000b500c076250b910416001c03c9005010455903626a80034600551340070b80f8040d070382c40b1041c42e074103070f1041100503c0d84a07503c0c02c04c001686040981c41d6035414004071968052503414040000000c003000c0f1015a4208010300500010009c10401035000701c02c1a0015512400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 565135413 1250 565134163 565134169
    0xe060a030e0708011e020702030f010c090305060709060c03210216020a0504020903060c0d0216061a09090c04020f0c01050c1e04150c05150103030f02101107030f0207090606030209 79
    0x30301c3c0d030041e00301c0e0380f41001d40e0b541c40000e540d1121a0203646a00507030b4071121400040c0c50000b1850030140c05510b44075403071203c01e4001454004403480390040c2e82142e5984002581c0c00c810500c030300000f140c440d0f11150f00180c03041c2c00d200030702c80141e0285444403080301c91000490300010540803e2444040182c0e0952074405900d4000741401c0b1001e51038032002c88042074a4003800b92208101c00700108403d541784046406a030b10408505802001d15100c80c00d10401810303041402d0030b00413410590740300103418903500c0503100b400c01500411540000009000007540545001c1451142c02d000004548400f802400c2c019004600310716103c0f14600c08403165942000c5141e82c0c490010030017084019000d42031008410118185080b50400303a08103541044200103070620b6900c00140048201600803900d181c1d541c240b039080315089154140c5038011101002d242410b504800e00068000078401c00c55004089018810703200309655074000349060302c409401c5400031980124212103182 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 565136663 1250 565135413 565135423
    0x1a01080106090b10111509011b0318030e030c060d0c020f0a17070c03060f05010905060607020f100203040f060804112b020301270c0509040b160e060a030e 68
    0x10000c400304210100d030960024920440085040c0705110300e8a41043c160041445034000d080008106c000a0b0f1501400c0a402044882c411141c07030340441d1107840000703219105810035145e40700e1400000e102640c030161043d0088010944c3e161046100385030b070710380b1804090049618101d80100c0e4001ca1464043d08000851100c150a6480800c407000402d0590b1040c01003190080d0017180c0e50f011500b0704118800180e000580a1800c250220b003d15496910a41c1255207070001000036444100c2001414450614040c0d07004924040c00000c2e03150140005400500382d00480e071074180e4590504140f0360b1244e101d080894400c101700418002404030b5440360340021640c4118240000800d20b692003a1402d082806030760400c00e0300115102540b241c0800302006c40c001240003141e58408107112011001101c44881c0c8a80c002281e00b02001c1c45409240c3c4942c80704042d030f403200566032a000104a82d07030100301d02e0341c24a9910f0303214100108042502a9404280c0c0180c180d01d981c900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 565137913 1250 565136663 565136669
    0x20609030a0b091e0607050306011211070201030c110c090c0d0e0f0c01030603120f020a05060907170601060804030c1a0c04050108070e10120e030409140702011404020103181a01080106 81
    0x2500d269054414200c804030300168030041c01c0c280787d0345948903580100e410300104522128094070701038005658100c6980601002071003640d0500c08001c0a0a0071944442d2213103600d20380b64010101c54405192441c02a5400b10f02001458244091020441c1c103071244038182083e039801c0034540107903038001400101028142030900384403082ca50b075942c039281184000001e040040145605091a10a01400000542203001c9079a9410039a4425844010621441c000b0f4121151080c0c480704020440604071901030b140c0c41155502c54500340e850b4810f90f03e0407202c0315150149890003030410701d0200c0c0500c40400030035071142d003044005000c584001e820b001c24843c004c0360040c3e00390307100e4005829400661610f40001000d03103009a02074400c160308443c4501010070f01043d45021584402c0800b54012b20515083d1604101a400c84010020020200c05041e0002c0c0240d4081e800070989103103aa40305104500c843d84a0048410b08000c4440f0b407282c0d06401003020100900030701c009 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 565139163 1250 565137913 565137943
    0xf02070f201008061f02030a0e0415210c0312110c0f0616081801030b0613140d0b0f040506181c020f0f01060905130f0f020609030a0b09 60
    0x1501c19004000388900c0d560001d000304001186000800540380c0c4030308000030b441030810f103805078070300030101075101d07042003115200140c004014a000c43c078090054001b200321620711401003c1c1020f80880f210400a00e07030751070b461160102d802c0003903481e090000095005026000410310049002400c2000b9900c0c056090f80c840c40e8816041d0f90346c40e501408500086448032341d13402c81c000d4000303c040254000600302c05008140d0400b2450b8210b040d2912100c01d0781c0800a07100300700100101405800000c10301003071218800c0c0240c0d12001c84e03007240380800400c4400c1414007581d800e0100c0340125013102c070502245c0140010000d04210050b004442903038800c0da091a03080d21155580320b001c405107507404402090302c0381c00b40244401c441681400060310030400fa00b01506000e420b1131f100712080c461900300040d0505020711010310586500049848046030319458400c0c0c030000b4048103a81c0208200301c051500d9804014043c0c03a50b20500b554a028a0702c03c4115080c00d078150805a1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 565140413 1250 565139163 565139213
    0xa0b061b010c0e0d050c0d050c060a0314010608010f0e0a060b270907021f09020307120323040303030209120105190b0306060d0b041703180f1f0903030f02070f 70
    0x117803021070742c076101c1c0105445c4400d0a0601d03042c506d00c0c0040388164240c001d100041e00e030b980740794540c00c4410035900c020205441660390300ca0489030b4400901c6100e81c09445007006000300440443c00c07a0b00329140d0366010494548508a002e040e91081c1c150400102c40a8012000195641007000c6403c104a07030b41030280c5460403029449900c0240f070340382492403c02902d4410200d56100c220701c590050100c1d400c41c0d407510201e04030f400440c1425030100d0322000c1d07580c0c2c0002400c0c010a005a40d40d0500f541443e14583d0140c00ae07400ca082590f500249882c51640411000d2281301d200e00001f039030b08008158103a515208550354003125a0080c0c001e1003c2006d03d4846e6110351020503406001407042c0d990350f0400000f080c40212050070460400414130401c03050072801012195041402d03503200304138582d00140d5507a030b804c0d005d10100032003061900041002e03521021626010b801d000c61140e035000e805801302d0b800030b1012600e81c0590340125080c050004410010044010740c03006c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 565141663 1250 565140413 565140439
    0xa0b10050306040209040e0109080913022113060e010c090e010e010317040e0114040608010e10050a0b09100f08030301061b030c02061306030c0e090a0b061b010c0e 72
    0x30098480100094091900040ea001032621140c1c4907260318600e0b40002c100825180c50550040d03440302e800184070741c1441c0b00110381d141c464403c0341c0d07076000b50640c0801d244810314020101c410f00145002503481c8920b40003008140a030003400704103118080006043c4c120488054440c20503a001a040c4000800051101e03810711052103040d80d0700400b4080000020004080312889680c0020380b41940d80000002e0085a410172aa4030a00803502408481d4035201018200c0d010080c1c600711560061051400341002640410f4010080000c08280611000701003595100c0030f0f5902c103002d00e03d110080218484140f0f1890141516034061803842d40340c168000c0540003a1074056655174031600d0000c08050281c1501c10000e64041d2070303039171a040c0800518204c503000348104404241002280804148106000044240010441e00307980e00d4480005004010704046e054101008004180c8111300050310360324807107d084000704100f80f100600400c1003080c01241ca0246407a100d0079 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 565142913 1250 565141663 565141667
    0x206091501090f0b0a18060e13020409020f0a0e010306060b0c07171011070605090601051309170c0703120c0213150e0a0b0901150903020d05070b120a0b10 68
    0x86046404000d00400c902c14520500801041e89070b1136250300400c1300340d0004a643e0303010b00611003800400000c00c102681d5100c44100c4000031195403511104000c001c01c0140b81c65030041c61440c1c000342450341c0c210450b0740447c2c9180c6c42e60704189141030211004104001e842c4c01341102034485002001d062040c226281c030b6482030240598070040d4500b02c181c101d813540400001800c1062400c0c140f146d4604840d110010340c0c040c0200b0740d0344ca404d050000d02601000103059040760406089540309155600301d10000308560001141e214180c5c2d040c0c80c0d44c1c03480c0400030f0000302c1b0360034010340120792071482c00500b1460f005452006003da000070318005030b40c3d008800070b9050140c110116405020000c6120a51401d4129001d0601e41d00b0a100c00004541e128800c0c928040d1024881e6988441400404440400c0004001760102c2c00501c01800c04a14141e9218403540071580910740300c41c800310694000c1980c0c00c2502d42c1010401210002a003d4141d584d00140c2d90580380400d03030140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 565144163 1250 565142913 565142953
    0x70b01050d031101060b03090f07081f020405120c01080a050112060c110a0311150f150303070b15100e210a020d0b041209080712080f19020609 63
    0xa11841034070300801000c18035000d02d240035001035560008000381900c4402c4002075400c01c3c0d64046580c812144030400300b40f1300051440942d02e24400600d2800c00c0051481b034440c2c030036107a8101440e028800003031203488040c4403802c1d00c0270b40c0c0013416004d81c031080018079076040101803011490406e0300400003449801d144110613900010041011400b60005581c03100024580c070a040c4180c18000e000d03d5440020a0004a20a000d81d115081141e905052424054401101038040d0b480070072000e0510916440f0301a4000c0d0a07607007450340f10b8441c58074500301100c00310f41c0c160700c01c0d1004060380362102c95440c140c5110300b0000504a05000441c01d0844031000b01402d01035407201a03004100e0030002d088929030700402a40c410707440c600d0101e9036030000381c030221880788144084203555801418088141d4040d00001c0c039203070340707000301e10020021814815644410700300622000d0300914002400305214440c02c0e048002c3c16054001d1406400401c8546280c0102c1c2c40a240c000d140c00e8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 565145413 1250 565144163 565144169
    0x110910030c120201091707050a060e0109051e060a09050301050f01060e010809191b06030b01021f0603020901030b060f120d110c03010501080601060924050304061d01060504050c070b01 81
    0x400e10050126440181c03854a00c40c0c010401e203806c105220300380c25400055840030703140107464201081356942401d40d4018011070700c2601003014900c003030010741002c050034511448090045c182048441012a0340303548112681c40c0010048030003444541000d0290582103460710b03000126a6252400050030307480104101e604121100380450102a420084502141603242d65000308080b03070b2800134230b4006080d1b407180c4400005003000600a01922400b940030406070041c02c0340e00e00c00c002d00e02d0100110130a801d0669034814002c000742e1200c44283d40a5845030100e0040c90802400b00194054010803140c412003405c070910320710003c0801c03d00103441113400c0c00b155030012682e0241c2020040c40c0d0740c035015841e020000403690300009020341255915200c18440d65100d100304141140303e59007000c1c28000314181c02d010b4601c190020740c0c0c4180038010002d40d00200742002011018001400103140c1c0d19100c0510080c5401d12074150846201f1b0002843c15640303940e121304e80c81c0144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 565146663 1250 565145413 565145429
    0x70c091d070803211008030307111504020a060c05120304060603050c0a0b0913060b0a05190c0804060503060105070606030302010b030d030e0730380606031003060504110910030c 78
    0x100c081058110440120700c0688006c0342526203070316200700c0c018400046190070341d24074881c02110074040f20004190900442d00684000103003410441c06952145441c0b4044525104100f1841080c059900146000b103100d42c03400b0846515504140303145c5411400d40328401c111052042090340c403410111612405c1c1629100c4507103500c00c120070002c0003030340d00522030124002245409964000020000381d43c01c0404d240d11000120412110243c01c0000105003030f404003c2400200d02078005503620020516105140460640d11075064403450780c800c4015030b440305c0387c03000076103000d0000104104152a04214001c0668000340d41c0f0082172041287e40040c3ca107414419041000da01e01c8001b000780da100408800501c1c01d009503440d0300c0d00d203214006c890f1000582486460719010004100e0403a40d182079154801040619800500740001c103689003034000002404500032140f156002d03828404011200350144004005c0003880070214070409601880021403030401082034900360b07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 565147913 1250 565146663 565146727
    0x10216060c0302040b12010e0f070807030b120f1605030d05091005040e150307061407110a1a040801050c120403050a0c0b18010b060c12070c091d070803 67
    0x201e0064000303104503000314001c031000140c1103070481c10600c2e815040340e4250f05404540c0e55603046036140d1a206540000004003103d0100e8030861094104a02161005000b804141562144e541c44d001c4102e0006913903801c41c2005c03090110720318903030100800058000d0900d030041c3d030b0360003441f600c50010f505101708030080581035a40e01c140186c03000f40065441c0c181641c1805403680d000300b000103500c0382c400d100718800410624401c0c43d0700300da0b0f040c2000c85035080000583e5480c0e4454250041103810401c50b501c001031071181d041c060721583c103010144603503e0f0304204025084d10300007401902c5e07400040041c050600b41075500950f001d41c052400b44d0300c0d18018602244c0901300e010018111a00b4402070200d0800c0300c3d9a21a10080300c0c0008000032044041881854050716a403c0d080350800e884580a5108100040c03901c244916106040d0946441e01c0c0c2080300d8001125203000d0144441285010b041080854003500c0328200950034007643c880c1c0fa1030017258503c64501c0480d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 565149163 1250 565147913 565147931
    0x308090d051b03040e040c030b0604060f0311040f020d14130210080a02040b0a030509010f0506060406050c0a0804061115010b160213091101180803030c070507090c080109060801021606 81
    0x1051061320301034240300200e2841d50415080400f110502d900043c0c607150403da0202d00c01d80342074418001106c01448a44e030000c4d280d5100c454480c0114450690803540741c0500c0c02c032000700c900c01802c90100502c800a00f000304540d04030340d205002426108855090350340200960b4410441284140f06450070942030354502458201038056a4000d0100b401c0104110206d0364040d0005172191505000800c18041c94049010603910107940c02504543d0400051190602c0b8600030000021404100ea0a0910300d541d1a14154007aa0040d00040e07a1140001ea140c00b0901c0480100f201844c020029035040c00c18540603449410041491900c4028030070301152900c043c170748208904c0260402600c1c049040c41703401c401e0310400c2c90b4002011041d40030102c0c03602c860098141c0720400021800c0d9907070342024032501d42c441181038030740b841420000502d0204a0190098580c0c080e03a0320803942d450215a0020350744590880981a40144444618101c1441da035000c80c9400210200719260 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 565150413 1250 565149163 565149217
    0x20303030f04170d020703031107030c060b0a0f080c03060903070b010608180607020601051314190e1f0b0a081519181104092003280308090d05 63
    0x100c076643d110807907980401c01a04c4202240c0c0688010ba000e91030501c0001c40c10044240d00b0b00c65040b001740860000c0e8503400c04103c69500414001c280a00720410450719102c0c1c610300c400c500e5103c7d15965100000300c40403030605101103500180c00b0b800540c104201d0350380d10100c45605000300300422055500280d540e122500035040360216240a032a007504001c04001d4550109000c6d05020340907121000f4a485014840c0108034070443d036009103140c4481082c2003d03c800840d100c1410ba842d0400c031411210244100c0005007000704030492068036034144081038607a045442c5104051020080112403004102080b07440c510705440040c5030b0320028460136513415070031107105940c42c25840c140b01015502d40c1841c1d540c018103d00318180a510104025611480030003000d01d480110002d003000410301580c0b9110707100030162800401c0122140311403c01c06002040070f0441c100b581014943c000312001c1c3c115020101034651546030b4200a4094821104040c1507034400c2c00a00380341030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 565151663 1250 565150413 565150433
    0x305150403121a061204030e0a0b1c021308030a0306090b0f040b03011b1d04050106021507050705031204150509030f0c0f0f0d080702070f030303090204021c1b0309020303030f04 78
    0x3500410139601d0710b0303c0c03003201548042c0450741100840c00282c800700103443c003039004200303d07101801c40c0381c500072000041010420320200030008041c0c092102e040444079000c40d070005040000000c0d515514121002016542a54032040d030a43c50b00000081e90b4481082c00340440009030340c04281d07804042c0c04a40141069206100d0600c0f40860304c240709540045440c02211340900d1103408107482c11304001c00c643c020700c5180056400880c0405487c00001103035684031800b400c000d030804560752140e500355408840300c0c598000f00b030b00400c02080444135019250780070408041103c1e180c4000e803699644100120601ca07003001050918000ca82000b181401381091800d03a10b14040c2f001000b07545407021007410b00840e031031000061509100140702c2080312200610000307014690740f4141d00500d00c00ca02a60819000c200619000c12030124203500c0c03450203030001415091a1040d0342c40204010459820903080c401c100300075075000000d994014081d5021181039031101c0c0341c1060b240b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 565152913 1250 565151663 565151711
    0x1031a062202040501110f0604060507090305030c1f0b10120207140705030d3f0e0f100204030f0b060a080708060603010f0b010c060f020f070c030515040312 69
    0x401000071418203200315580180003203800a8850301c0000c0300120710281c844200801240099100e48009004618250050b5400c0465800d0411000740c40340c50345030540d40400e944410790384c4000058040207490b12010381903540004401c120280959000031044030721304040404102c84400040341d00040d03941103581c0c0395805140c945181d40304200c8140c41c1d08552003124400c0c0035014500b868a8041c91408003100f1110b08025040d0900007d0199600658440401018448407100007030944910a4002c01c902e844000d0051800386003200e49450110300e94480c0c0e042c0103000c104000f802990309d482e0207941c4031412034203560b200800304810540560020180d0700c100b020004440c0c2e8042021402904107500a001182d22440443c0a543c8464032036030005e20981521008035120f0b6000c603008440c5128050b15200300c500c01c518440d086950b090307540101c100c004108102042108150049090070380c56902d203010f4a0107030043c07485a01c1d51b00c0898844903200f410f01c2e18a4900d00032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 565154163 1250 565152913 565152949
    0xe070f1806020105062403010e040f0602040e16050a0e0f1302031609050f010e0f0f03010e0d11150105060a210207020913051213120303020c1501031a06 67
    0x881070361424002c0c0681020782d0703564040c800ca40009001003c1e42e4a1291040307441c0741104d442d691030f082c0003180c0300c4c2d801401039aa42400d014143c00081e803900041c0f00429001e44140b85da41000d503001220f501d41c0384144070600004100c0c01c100305401c071404600145044540d90740c40c106000c01700315181d4403102d00740c0c8010300c0003003005001d1110510708c0058000d1565460301c40c80c0c03606c1c2407001420080310150b010801c03040c80d0003903070300d4480103854010001410004100310200b01081c2960b00401d10300041c0e4004000381d40310755901c440103000c1da1840c4001080382c100212007544800030f043c012503024000c001400b0101501450000c1c2a286120380052405002480d0120013508400d204034410581040480c03600320748034100324000c42c1c111016102a884024828055520030110b03021103007400704001a00c010301208400e80076000b5100940d0310f2800e100a81d0818012800030822803582c82c0050004c80d490071b03c44a60820b10500e401143d4841200060000084aa801c00c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 565155413 1250 565154163 565154207
    0x1050d051f060203090f0d0f0b16021227030f03030f041208060a05062208010c110a0506010501080a02040506070609060b0102010915052503020901080f010e070f 71
    0x541a1000340c9064009000003000034500e82c070744604070788901c2641003007a40540035801d108a04d242010422118034446c0850341454000f030750300c0b0b1b030180c08211171050035030f0074803420041c4031501403002d000302400c4101158900f0404c91160010f017100d124841d000b500f403418074151241c4082061062070700d4068101c80c0c5910b400c560100003414101c40442c1c001016194154005004100090054034020481c1020034104428882c8039000b541302009048462a450031243c80a0301040c0040c100c4080080303010341d00300e040a00003403080001891264008480880415400700304e10341901c00034a090141c9444a002040c080c0c051f5070046030f481400082d49034100400b0303034026140035110f0307003062001c021920010b81c00c0300d8950350003600d10304a11401d014214040d40c4a65848210920310ba119440b0b01c24400b4802401c0c110741a000c01c0e0300084801c220341c1c100c91503991140c4205040a00c0d981001c07213082d444140a800344040c05a07004003400400d0103000564280a944000d0803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 565156663 1250 565155413 565155421
    0xe040b04050c13052d0f0603030418090b090d0c11180f0f0907060e0112060b0403082232062a0a03020c060d1503060c0e03280201050d05 60
    0x18024441034540e4518101c440d81070a002400d5a200e45c80c0c100c6800c016030f402591800c0088003002d5004111f56031500040101050050071a00040c40b006103400000580721a14604502c00354005000d400c415130040c090303900101c0d84180c40554259110100781d1920820201243d02c009480151100726002076040040c8000d020042d0740c032071413200e101c6444a4980f805910b07143c1c2c100e40207010004000d0311602c2c00950041102482e048a04900000d68907a41c0308800002d403c80c0d002141c1802c0d00252400100c2040d0030303400554100145c2040c03200f45050181c0d0360781c009070f803903044507400010708003580819514181c83c4100f5014120959810f20843c0c0e00d00e074070180c00002000501e5910b582200e8280000705069801d85c103400402260000710100806504640102034169441d0340311001d00264071204403005610800c0080307001c84640c00c010b0a10030040448074001e5000d455800312951100201192003441c043d2501c080107000c1c00100c500d84955040c503102c882c1004140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 565157913 1250 565156663 565156699
    0x51812181e0616060c1106130c1d01051f090e0a0e1e16050d1419080405011e120f0207020303030903040602010b09100e07030b12150106090e040b04050c 67
    0x540b0303c0502c1040c04110380b4500034004e5501e4505d180140c07495503c06400107038100c00e40900851114080e1003105000d40e5280542c8881d242c64810420509861030010030650524240002c800c0c14a110308600c0758104d04e800410f00e40b0326100b0901c00f0640c41c2e0201c0c6400e241d41e4019402a5045029180061060040004803e85542803008903100381c0010302c01c003211000742c21003512001041030428804503207031a000840807401105803405000380380000320003443c841d0998036100d018400d4a80345414009800ca40d400341440402251028a01006507408501c82c41d08922524000914807140e0301640000d01034120000d4046c07000005110202e03600101500444d00568001d200040000080c84041030007a1500640c001c1400002e10018004950540c0d00444038900020000f0900c000650102c28480801e46c181e08484059000071940c0308106003d0b144a040c55007441d840c0c450180d5070749000410107010140301704003140800500344400701100d1070040c00111050f20141038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 565159163 1250 565157913 565157947
    0xc0705180108030f030414240a0b01140a1b0c09060b04050108131506170d030605091306091707030305060301020f0d090f0c0f0e0105030d1b050c04051812181e06 71
    0x781c1c4160080f144002409c2e00c9aa002c0c58818880607500d03000231081d046461080c0750030803da03040a1103030070410403c054120700300744100b040c01085020246c40c94500103008841203030700402d000810411081c001a608001c05d130f508054030819016148403039043c1081298000c01c11100c1682c180440001e209990203601c9684890b0001641c0e000c0c2240b0b5000d500700c40045c07180c16040007040000507104d040c1003d02a25a90240318040340c5040a0368070745c94116840f000d10703007032030502081d003005041d0b05d849031950124050f80214500035132022242c040340a080c06000b04070740c60314120810000c180c032001d484d0a901051114640380c944002c0103400f0440d0081c000300340a450000a05460300084e291003030049130310380b080d00b40390400410803000c4200d44142c41c00c0c464403181742c5598880e031281500c41c11150051900e00015000003a08041c946a809001e5000600803913201d45030020788a280410125003c0c00001c4a15a40461000711b050303c40d41e0019010482426031040a55 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 565160413 1250 565159163 565159213
    0x1805090402090405070b0a022506020c01051c090b0f09070305120d020f0d0204030506150a05090a1d010e0d02070b0301091d0a03020304030c060816050313080c0705180108030f030414 80
    0x12512409d400234a01c0500d0705481c4148030050f0312458118000354084d400401301e080169004000c8039074821440d100783d4101d104200c88c1c5003c00740402547c071840001c0b058204114202418110f855500e038250f43d452400320002c2e0084000540e00350000b0181e04680d810001001c090307441d8610880504000e4103d80310a842c40d0207140002484040e65420030000d2540041c1407407403050808052221810004007040d1602d940e80d10080c2020001885034805146030703030004102070052031240b50514560721262001d543c0400400e01c60492204140d905444d41d041000509541590502c1840091121951054001c0350840000d055002c0010000d8034040d00b009200740e595000100d550680c00c071680e42c03105842920340e0686606c2040116040079020301f41c1d03801610503443d0381c601c40c0d0000030910195489500c0400060426602c80c06a0640c565603da4003589480c1d000d03500ca120b86840030340040c8000001808102d01d41809104041142048902c40c03c1014840034002000c16 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 565161663 1250 565160413 565160443
    0x60f15090312120c1c090c050d0f060605030c060d0515090f01061e170405032a070b0a02100b01050d110d0605030f0a03030207060b0d03050304031805090402090405070b0a02 76
    0x3c0c000f0b0612810b100888100c1d0705071108195000c00800d20310700092090610881d40b4030301c5004001842d42d18884c50b0409a4040c201842c3e90032040d280140444109a0100340250004400546c10780e68007001d0320301c1d841410074082215640c50380840710701914522040da1083c0000305010246d81e5540c112816503000b900d503540c401c81000c0550411036558020302c40080c4410150b6440303181101c1c02ea90300140302e00100d90802c810301c04052a0142c1003403045c4440e00100503d203c4001b000c010000c010000718112a181940280c0000e44454410488800d03554403400c171088940d00c070b40e00b260032000d010001001500c0c030b26404550158484003030200391038107101000c00d640c540442d02120800b4124010303d160403031943c040c0d0194202c008190344143d0f0f200214016078443d00c181c040c0c00d1b4841c1d40c0302aa2481c261030054115104621540103121900e0424482629824201030304141c046031031140715681c51500b0b43c90404d941d081803111650210751484125000120744845601c11 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 565162913 1250 565161663 565161697
    0x20712020d1b0231021c06050d260f03040309260304090c09050a0e040b0f040b040312022809050d0503090411040b1c05010b03060f15090312 62
    0x4240c00b071001c0400c60196112013003842c004240c41904203441a0302144442a000f9140b000c048082280c200c800207501c103400510000781c040107184108000340c8000c644401c034000c1c03c0d4940d0a10026445040444151a0710320501403c1511060342d1780b0030450364840e40c0e03030715061400502e20031161184010040c00da081a4030513800d801500c0041492010003107051600c1d042c3c2442c081c0512000c4c80c0705101c180c2501003075584440070250041c19801000d8900d90600b40760800c0c10300b0000b04901ca42d000984140400502c002008a8115030980781c020040c00394100803000a01c50400a00103041ea0041c41510040d1480076000344464036840b03c4c28459561424800151103a0701d00501d9508100800159440c05a006403070046010b1466030402d5110812600e040c0c0c80807005001468000f031640c001841ea9000300ea0161004100540c1135003080804034071041e0340c802045102d00c000c0580301d01d00c10440020344103c0b00b8018104c90200650802d0707a0420340c010880134484080c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 565164163 1250 565162913 565162937
    0xd020d0228080411040905032a03030108030a05031909121b0308010e1e0c0c01060f050d06110c1504021306080a32010509010b0109060c030305040204020712020d 71
    0x74000e8031481c90704a640303a501c2d140e40e4a0742c0740c0324920011504158096a20051900450410000b425800001901500780482c84411440c4030107142c10070082650f20400c014403406001100350340300d00d403050030030030340729120140c4c040e580030783d61807641000e030303240c0868003082c009000706001000f00a603c034060444580c451617015102d40c1c03500580480d9641004101081c04001c0141c2e00040c1060040e02a035400050030201010070750f148280b00390003240903c4445803c0c07003600020300c165031482c1a20361030540403030f884003076640c030241c003907030369000051540f410350707411074a28100b0792040e1144140c0e40c050110f807804050f074050b40940114807501714840d20070301ca12000d40d280c45005251000180d0b40da14000d003564002c0044401000d48004129100b1807202c04c0d4100e001d900100300c601e842c2110500311420010b00c14100f011842080184580200022070b0803038040c540407545942d9800414003038400ca01009018104001e07541446030f0740483d26084060f001e075100b0381d003154 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 565165413 1250 565164163 565164217
    0x70c0801060b340308010e0c0301030f03030216020415030c05090c040e0406090203060f070f0c110d06090b01060e090a0501050a0b031f0807080f0f0a1103030d020d02 73
    0x4160095400e4070504020036440c5250310b04031650b41400f011070302c44040705403951501c2c4032840305104a010990f200c0052000008001d9400e41c0f14221800c2207056615649450205002c407980c05001e0541c00160800340c1103441202c001c24a8014109001c035500915140841500b00e02c003c0e075020307081500119061800400e90340c0254142c424103130900d0304184092403031403406001103690343c0d59080c0c40e000688082c4400e9108840782103040f0003525054901400140c0841900020441c0d080c038594005200002004800c1c00282c592500301c2c04d9a18003040201000100901011035950000982d40c1d4020700034201c42e202541e5086079510740440c1041610710a00a20b580000700180030300c60364401c5806075910180c0c030440e003070100c0c40b21039078621000202c3d00086d5554200d1305080c03000c060200101110441b5290081045000401180d80c0783c00c8000380082c046c101c18100c1400680e400c005a036003104a100c811999029030340c4c03031800250321400032003104020b9001415242e203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 565166663 1250 565165413 565165421
    0x6090705010e030c0f01170f010e090f07031113020706020904060515030604020702041103190b010c021c06092a060c080928121e2f100203070c0801 65
    0x120043e0080015807422410414181d03409468141009818800401c446446440702c43c01241004260196541130420300081c405000b030604c1c84590044c2840d0b0024000001c1d240304586d000b0000401203600000001e000505060701498802c4c00411400c0c18080513034010041a03030201e50130403250b036440040c8109a1684e4419216500c418000941c0c1424180c004000c1e0500c003c0000503490081e04030000309400640d1107003030850000700b42169404041c402c400b40c051013420f03c402d00420b66800240081400b904415000c0220032041c010480c40340c105050265002c51001c0108011488850710368071480701840d030ba4001c14100203140c034007400e2a151b1481c0c00c600868a000c07421414000f02c1c40001c0194508622440da105454120340c0ca0050090128200c00c242941d070641040c000b00080129a4102c500e0340605010005403120047d8412030000906880160030042030f131b4405400c01848650030255250703002c0141d5031b0210003011864454030181c072015448100650890b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 565167913 1250 565166663 565166687
    0x7061401050d02010f08071b0f0203060f01181e0615020c15090d0c0905010902040515030c03130501060302091006021608030306040b060d0c050c1e0a0213090f03020609070501 77
    0x400c40c1c1d0421251018130444901c0d5010145040044030b0140544038080300e1000301e231003981c005038015009401c42c5002d010300d41d042900804030780d1055051104012100c00740c0b41c21041020340c3e0b200503003d841c0700c0e05031403140700c800d0400c10858aa43c81000c800444426117504e40180070707520483d100d52601d07580010a021641d84920306180c00d600034051808910101a00e540729100c90001d01e0481038000c040c041d0200c0c107009a1510f140c00140000c00800040021070204140200f2010707a0101b011349a111a04540304640032089081c0140188115080179400211404c108401403155520701002c80d409a401c4980750480400b00300b01442c0303035001e0003525030410000b0454500d055040040c00c0c40c4002c14085c580b08038101c1003002c40303070406603800c040b030004644c01c440400107000e500d0300c07034910b20f44083c0110700604500ba1100c0e0380960080c4103c01d02d08800c0004550369000a11050b80702d00082a003026900380a991000c08170b541c2041c62250310804510355210341084600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 565169163 1250 565167913 565167917
    0x30103060c08091b04090503070210120c09142202210601051306050f040f080106030c06051608130b030a090605060d05060c0a141804060e071d03030f07061401050d0201 74
    0x490030900170403000d05002c6005407000d1200340041409641e501c14440040d00544c2c03030715044c14a40032400401d446a0b2160201448100c0008100b106143c0c1c00e4240421000c1b00c68040419031900c02201c803901e410038051159101003500700303030b244030038100c41c40301040c07910f4490141d6035043c01100c9611500c41035242c1c0d0091041d040160300d0042c00685003501c41005814249511140382030074228095200da080e981d1a01030400620004005c003001030841c51070886e2414040440c0c0b840101e42c2a04000c100b42c1000404800340c104040031000a0701c900c2d2141c0c0d03074a080c8400c00c48040c0035149429540310780b03403a01140007450300000009602d503010018000560310a80d5210380c503004141c1600601a030b611038900e03030386070350b90081007111b480030724052000b4811801e00044509640045030941d65040c180314555400c5081d002c0c1284800001c032000a460360082400c3d400f521000310040307100440c450301044003035007294554003030000d0599110b03aa11020401c1504e29104042c4c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 565170413 1250 565169163 565169203
    0x507030b190506060d0902010509130b1c120c050c040608010c03060e06010f3203070201050106021f0f060e0a0e0f010204150f0c0203070303050d2f0c07030206030103060c0809 77
    0x31780c001c160445c0d180f180c0141080b03402c10101c140420503240c480c44d19130407a965242c811011138035104503072020001c9003034003400d9800410340d29030808540361041d000520203a0b010b840b0411400b000b400d40000d901400a0207915500d108142c06030000c4e0000c08080381c2003000120799410803683d69441060141e42e0f022411014420541c1d010700800e25007100c0d0621100c2075800c0e85402c80760f02070245d000700c07125030f42c03480c0c111002400c60b001a0460021900304142c0d403550080441c0c0e501e540f0a40340030b00000d0402c020b00301c2c00000c1089a10007801e05c01c0034002c0103401a0207511414103809034500f9124941c00d0501c1680c01c0b03101e64050b202900d900070307024001c0280718101a941c5d1429031f0078000402100383d00000c0c43c203200c540c000c034005000003074200c0300400c05026100030a01b441d010071f0400307800019511700741c10400341c07501070780c400215003c200164100012801036801a00c07003a42d81d6100e041003006800d0100400c008101040301040040600003018902e04000d101520 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 565171663 1250 565170413 565170427
    0x111003091e020406080105011203080906040c0e0c0c070801051506090a090902130207060b040c0f0801030b0c1218160f0320060c161d040803070207030507030b19050606 74
    0x1028107903040c0703010303600715944180c0071540f04070910130b8a01805100034106c00d41325561070b004254810050141c1040d400220600c0300042c0150340000c183d03825140782401c0341e41c403401c9055150003916202c1e9480d10402800158410f41940403074088d04c82e20341028003010100d8140b205170f2144810994001803500000c002c050100c1c0e0010303012030b10050116440034408020842680c01c15001910b0f020398035018500307540340074441e1010380d0000b42082d0481c0d4802c000d01030041001440042d03c004c03a40b02c0003c000e8050042103550841c024664060581000008500c45443d80c0030740b82c41d01d2080500700801d00b16810306a8049800d204d1092300d80307034155a9568851010317060440240c0407410140aa41e50351130000d400d00000f03c0f40205042c5200aa0001c9031210b1648601c0d004081050107119518036121280d44c040e8200c0d61035542c94a0702d0804030329211056001074a42d002d104008410001050401c0c0d00542ca59060307018900442101d100071100252409580140200842 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 565172913 1250 565171663 565171703
    0x12150905030c070b030106230a5c190f02060a08040b0117030d0203130b010b0705011b0c030f032d06140a0302150403050a11100309 58
    0x10154040c03046003035078181414000d03441d10307140c019001031815100100c01444426840201c0580060b03007000040400c1111070320a0b9180d03c200043c210170043d07100503400e0601901c83c00c9002ca0010b01d880d00d440b640c081e8240308114203e54a0140d5818400803034004e03c0c000c907182c1c201c6800c6400001e840141002e80e40c5503480c12030040c00704c880d148103115040140c1d88200c05800d6140b203944803a1704030b00d420f1034a80f012440503008201c1014017a1100c1c02e40e0440081500e180030806c0400680e69190b031111100c4041e4403600003080504220004100c4009071809084440d1040000380000660640301c14684054000343e070b00018003a40c002c1002c64411100e4117104100742c24005080e01014500c1d4080c4040006d450704580b20b103c8101010300c800e449004010b1440e2090004129074200c0040c6080142e4440139105002d2043e0301e98111141004036402540d1040c2151604603030b07441c0a501c0f0703d170b89031445885641603850900300180a400750248240c1d2106803102c0e0344040e11781d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 565174163 1250 565172913 565172921
    0x21614060d11040906060f030507050315212b0c080315090a060614040302090f09101802120c01090b1b0708070819050304050103110d0221011215 64
    0x80c0541d200d0300c1d0a54000a1507880c001030001d04400440030a010b4142140507114074042c80c1f0030010176242108002c0780b96030140a8a822407000c050b0303c005400e003400003d010550032000b680040d8081082480007000010300b043c00003840d00c44620009076204003541d00302440c0b4010001042e0541080400544045d009540c0901c00b03d028600d05a600d60105503900000c84d0040e00072a0b46200603c0038607004505250030501080e202c619090450380801d84e803010140800041000034000f081c6030720014810150742c0c500c1c0d0641080081c03819039a0380c1da006081d0340160700410400e40368101d4a0b0021030741900d49007042c1c69502e40c191a0502c80c1d50250f01c040c0300c841c0098404608030350702c01404d21a000c0140300060040407060300304410b8909010080c03040b08800401000c410b400074101000fa2000c551090800040e0101d18081400003071142c0a09640c3d49880003640c0d9400a0441000801d0100d0100142d07003d603072550107c6c000c5d4440582c2c043d02c9800f1200c5075001e55040f40e00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 565175413 1250 565174163 565174177
    0x806030a0c05041e0510091a010909020703090806040308011a03071d03120a020f10050601091202040b040609020c011409100e0f1f05060612150d021f02161406 70
    0x88101c104c18000700c4400122401a6120410180c0c600d004100b810302c03501501840765000d26400920386003080010308090f4442c41203a04560700860804103160290741001d0082c40d440040d03984a2400d4623004000500900034140700d55140480b4000c41d074140001d992107080c0c552100c810010654450003d03450400144c1603043c824030014104513062440070385103107180383d001401f064140d0400c00c0c1c01c109500513030b010110302c2c0c4400c0000a0b81c0c401c000c0350456000000c14031284400d4008a030242c0608a01c43e908a82489800542107425500400b0540e000030001c008032104500200726120007a0b4604200b90700c43c014202c4003081d00c0d80200100c0343c54008442091503012015400d1100c1001c41b80c2c29420b0328400c00c1c0081080380a107503803101044420a15020210801000d0f41601070440952030078516803003601a1982232070090b41d40d40041180c20404100901c40f840852007551034401401000b15113180b0300e013101c20030020303200001c115401c03061020b0240402608812 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 565176663 1250 565175413 565175441
    0xf04060318080a0f200a020105030702160b09011209032001091e0c0b030403170c0d1103010816121101200714030303070801090c09051305070806030a0c0504 69
    0x108407000070025401010425075a444440c4808401c0300701a2407101307507081c500840030440745070141c40751001c05e011441c3c0764242403194480e1581e500c1240380c90360841e00c049020108a0303002c501c0300e4200d00603004106090f031700c201318455070441e40019119880c10040114a03c42186003d101500c1c101303422500001000041c4031181d40c88205280c0d143c03200d014250380000410005205001c1d100c031010381422030b20145182020f94009140b0091914542d41e64400800402d000d040400304503206564031900c2400f00b00701c0303040c18900e254401c4c0b04440c8103110b80b1200304004644958858202c0310050070a48803100a5207855042024828800d030400035442c0101500c24101001e03602021006070082c60001e05180281c9070701032020340d109101c1d42c401d1040118050707000c40c0321070641d44024404105420010016190140380d40c000c9580b01d000034071034507600c46156210303d21603003096881440c0d94440d44185610740140c2c441c0a446441c07818001d121508040d00810590301e090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 565177913 1250 565176663 565176701
    0x41502070221120c03090103020306010c08070506090717030d1104030c030b0f010e040b15130e03090a06050a0f051813090311161217120a0c02030f040603 68
    0x5a0014401d07030204200512030040300c0c2c1000b40c0002d020081502020940070780240b40000c1e91448070759074024405024101a000000127680d64464940e41820550207062943c41d28030526050303444400031a01c60b0124480c420740041c0300c500c5165600ca00c0d04002d0007031868100e02e8402040542120540c850000004100010001e4042c00c0b0340320045001d40c00c100315508250748128405103040c0e02101e040d02e1203405220100e00d01c0042e0540164481d00b140182e070b40c0c041c2c04a020350040c81e80e01c00c0c81616000090243c0038000c4003d1a07080c00440c0d920086644450003030b07c40f0300887c024400050b20441d043d181242c01a001040c08990070004800080b80310800590b450b8070b0007010610980d102e01300d0b00708040d0800e01d08000d00000c4000b51502c0304a841010070611040d10510400c0341c0c1f0ac008240c140030801400074101e141640100350b4030401c2c80d0003030103200c0e026121348240318130f0004030f40344091000c0191a4070b103a10f41e80b890f2400b4a040c0c4e0480290141e4142610f1031115 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 565179163 1250 565177913 565177927
    0x3230f0711061c0b0d02060315130c0f0e09010803070b0a0b1905040b1813081303060b150a081b0c0d09090f2f1303050304180b09041502 60
    0x40002900c0006494449030b03c1000f0241c440b8020740308905001801401361004640040e030f15941580c1c0d00416080e4201d4400c402100054500940c241d04007050918028445d0076440c0d0000324004104480d4649101070b1480d4010700072001824400d40b4003581040c17140c1e00024000103103181c7c100e0640c00f00072450a55450000b1400d070280240d03410060429441005581424041d0a20005040f10a42c540c0c0001d02180501c06c44000c0c00004101c01f82d0904c02e0070884200185d0b520292000480109607841c0e1a09000a08158120b503200340b001076001e180300040403044800419041e03442d0103039a00ca29414903170700b001803050205a14801d1080b1150b01038104400705510100d40d41d0180301d0707031800036050211100943d1103003c80d130424142d0b5500104820913540044901603411101c80c44001d20030005002c3d00031442c404503100c55000042c01400070150050f40e07a02e08990514038a040151012076929010542c0c01a0500001a0110350400d400021844000c0c0000d4070300b40d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 565180413 1250 565179163 565179169
    0x2041d120403211e05040b0f07030905090c1e1c0501050901090b33030106020106030308060108010501020c1302040b0c060103050f0c1309081204060903230f0711 71
    0x1000304460000a80106080051102c040300b54520b4a5404241210741400480000c100603d0b9100d003c540b0400700c204400c50520810403175008140440644e52070310615810880c01750701c824810341c0041c5413100e021840b4684080c0041c040c98400399000d103000d00c5000d210859010309654400c0c40d035828006190788066515604a50401032040060f041d0704190821070b913001c044c0c02250745907183c480954680c0c1c42d215601c03a5072010f868000c091b210303058a55169102d003c3c000b1290214000700c000203409405400c40d50590b81300b92524110b030350f1100011140124240b1400e401a1710049105c00359040003044406a02c600b020003600d481c1e1200c1c8042c01d1503004900101c0c0326401200100140082440583e16034000c91002e001800d408400040f000f2200743e048119259507011141c00300181d090449283e056000704042040c540b604200008001142c02580810f85081d080010200b2145200f240030b000301556904181c81000b405c42c0075081001e0407903203001c038000b018006507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 565181663 1250 565180413 565180423
    0x10c0b04060203060415150806030106030210050c010c0e0a05090601110714090108010516050c010e01050c040945020306010803031602010c02070501110a0c090b030111070f02041d 79
    0x9001d104090390b2424008203110864012080c2d68030b0b609031070784040c007000e403050001d035a072580c01d4a005021602c40400080c0101001d0b44029801001d03071101c1903440350010080c0043e100404000c002e0407641c070390b041e925000c4602d0225800100d11400b4025482c0030380c11075400800c10700d040510041d014010350700e002403542041116041041ca00745285c500342040c640036118500080c4180c3c2008036060b22110344500c10401408000702c0d929203a41c101f50300002151010b00c000307105071708101c4000000c4d1303846409034400544c10122140441005001a01d869807064605c0440008003211454442e5070360850f00602851a951560003503901089218040c02c1900051603607810590801c040696002005100b9039040904507141241c01092200c1102c80a0810350062000c09400508050003260018001a41c20b540031070449440d52210b25420340c10707402004a1091a00c00d070700d240c000e50340000e003082091540a4010305058101d0034119800100001c400c00044100ca4105 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 565182913 1250 565181663 565181671
    0x8120408041502030909040b13080a0801150507030903020613030807060506040e0715140d0c030f11091c1e0609030305150d0210120c030e06010f23010c0b 68
    0x40001240901070001038158200d04090b040c00154606201e00700400c150f644000d00142c00c1c20346103c001007a407141e0030710f040b050340d9011041640e81e03074490754041c10020702802617207290a0141001c5001030700030f00c100c0784400d400d51208060f80d0310b90b03030030401c0c9544014045160020070000000000b1110400342c1205803046401241d03e28148091208580041e60b60103030560005404109800c00040c0040c91417613541b500ca18031180320110001e00e840340300b403c04013079071a00c1c2c60941402d60551108501c158100c000740002c003641034961841e405464141d50b40290142c1c580d0346010044036240320507500c1003041d504211107020240640101c601000d80b4845d4890180c1010994144590b9500004141040561800725400310b10101c411200090140388028400b80c9454096510194060010603040c0801d481c0482c0040c09006544100d20b03440c41201d0001c0350880c8094111015101c1a1107440720500c40c0c2c0c264080105e8030312052034180810708101e000071440c4080003601c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 565184163 1250 565182913 565182923
    0x50117190609020d0b01091d07030207020d0f2a0b130905070c15020a05030a021309060810150806040f0309150518030606091302010905180712020301080316081204 72
    0x100d00403011340300141c500410100741005032a450600981070342030000c5200300040c8095851940e1140b000342e000744280c0401039440400011500f0030010210003644140b07100e42c1214441c00c2c4003103518081711001c00403440541c125040c0900503491100c01400120f940703408410502a90b98846008440003900e0000012794041608828000c50031000c183d004070103c0214500071400000525501014000045258001032500d420f541c01c10700b440d0140c0302102d0208a4a03940d1010a55662a51242d043c081401e0030444c518030208100c09504607a400300141546135076030b40e202c09580b6801082201844066170003c6005d002d1004940d20340011516010340c1e6054040841a0040488180511a911a604021303032511291551600441e456089220b00d0480303200595000640d5080560030003884441190700c40e69039100d0b18091041915080c0e041c0c075140c001501680300c2401130701c18962007040041c03145d52202d44041c2c4001e02401d5600d00348103401c0e140c0f4002003416181a58 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 565185413 1250 565184163 565184167
    0x6070204110c0708071a0f0d05090714010e090105011112040b071e02010c0201120e06040602191403040312060519050f0109030c03020f0f100207090501060905011719060902 76
    0x284042041140f0409000c900c002042081e1070615500d00c683d040a1030015030140108607030030415001c1d03081c1e40004007005010322181c54441c50f141c3d5501e201c1d00c80d8080f0384024005c46045075025105550464001030101c01c1960b01b020010740d040480f02c5101c18007482002c901c2c1d82d84035001800752010304070311440c259444105003451910030a20840169401450101820060380c005036420201582800c25690700c983c803181040c000d2108141c40d0359140600001c21041042039402400400c0c90851010a1825144022201c80740d410048910080d410030205000c20b005050503083d030440542e020171095110400709640c2c444120740c1c412036400c01c480c00e000d640f404415103c080c0500f841d1800e8411f1854803640901c10785480003134000c1014046c03144803601c542103101c41e409000350a918843c01d0148009589010740d01c0f130500c83c180b41400104500e032042c40031000304c4105a4502600e1505015807805811000c0c066004250424140394840c2e9040d000e902c00600301074000503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 565186663 1250 565185413 565185427
    0x15060c031801121b03050603070918020a150504090203040c0512060406050f07050409021e1204050601051c120306080f0d0305090313030323070609050c0d0b13020607020411 76
    0x340c0fa02c0100c50302c40140500f00540e0703480451070301141980e401014034000c280d81d154240480e041ca040742c0c01c480450fa080004404592100c0741d0b40c5840c00e8800d580f000c2c003403a5981c10701c4c20000c0b42203203554000342003000204100c00c650b801030f64000703008000c4000318541d540c0014032400d82000100003da04a0401c00041c843d140c803401e588010844070004040c90700200080040c465805080c10055004c507401c840340320045d00804800100e040c600340d449032003140d4800d0401c8100c03800c0b2454440d0f00d0002c030341400c3c1421480c5d800c010001207000c0343c0f01e95580f070101034010341890004041c4e0342c0170b001415900030000d050390307062050041d02581440c04401801d483c0c3c024420b820507030080081001d640d142e801244100d9406292440e40c4c00c884200501c0480083c0c107907101e82c04404a0188207000490384259041c510590480c2d811004074014404050340070340025044521082c001076040442c5955008403d01c010002480c14072541c0c00501250903140b5181d10b07943c0046014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 565187913 1250 565186663 565186667
    0x11090d06020c07060e030f01051620010f05041202160e0a1b030509070807050603010614040b0406020c010e040b010e0402090406030f08031e0c0f0a0c050f1c050c030315060c031801 79
    0x20080444204000c0c011440d1011021018021403034011040114400c07408030b40bd94031800d09849425100024000c4a0740b10070070b40042d000607181070740d001c4001c114155a00f400020311560031780200042d01036085c40c002c3c41b010079441c0101040541d0380c907205d5030107146650388000703540709520792000103460901d103c80038a005840c2d04045255885800709009070755500707069a04484543c604140c2c00c02c041d001c031449a004e250712441c00000e0208001c540310b5000b07c0c09602e414003c3e624945881422400c01c01925600c044040c08103100c191035a100e8281781c0c0050003880b00207480490115901c3e611039004a51100003a01c070024048240010760050040c826440050b909001400b0b0034002d40802c69403103003400000001c00c0001d0a0465076002c0c960709400e80d40c02034280e5000d6007074604101d440d5000d000320034061900500345007802c140500183c85107103000d88021400e560700d07401c5207000d028a002801e03900c01000d219001d10900100f00a0000341850420103045444603000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 565189163 1250 565187913 565187923
    0x15060f0c06070e0a030209011208070f081c0212340503010302040e06010e2422150b040e0c0f0f0a1b0b071b12110c0411090d06020c07060e03 62
    0x140302c1c4107500c1400d013007000d40d40b84030031f00b4195035604440ca40080303454079002409104850000f003c00100c40010420301c034840000c4e00c50343d206401c0100d2940d00c00710b5480200d1007100034281210200c4070103d4a4100790380c022030100c80c951a01c1d501c0c071001d1500500005a0340502d0400003980000041c02181410b014021100400100a0240d0350400d0f21b032010a50b0000c1c8403110040303068290015540714101c580c11954005820b104918060340c900d4000c0724014090740034200d083c81c2e006101171a4070810032003101d00c548201810300d800c18400d0700d2000c102814a610b484001c0c08010030f030801d003c0c0108000311115910035924059004003620004000300d5040c000d103000c68182000ca08480700840c0d00c85024a00501d81d0078403038480f880300c84401c0c034000c0c04a0b078001801d4a4015081031030712040b061b40404489541075030004000549504141c104d1645e0028068030515040c07129254058071311505c405810a08082115450b00a01e580014001001059104102d082c1400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 565190413 1250 565189163 565189187
    0x303270902030a200c190f02060a0e04150b030a0c0e030708010b0102061e13060e0a03020609011a0303040b0c030c0a08040e0718172b1803030815060f0c0607 69
    0x1394103800d001c03400c81400d8848014520354006240d91001800402c039400d61040445940102016118410300d0350090454460030851400707246000d00c880d85041c04002e0304001c030358046000600d140d4030003809070003a10318480711409018040f0410721150743d051206101800042c0c00000d8405015400280f070074001402d8541c440440c0d03c07250103444103000e801a400f100e0f00318071101440340351038075000404410003010500e01410540c2d508050707012810728000c00080c4c009002c50602d003808948004681216154598010401042640708010240001c00160019a400e102541d0400360501c0822901241c24000004050010011088803581c00c010036141400f40c074040016070100520b4a8043e148031380d411803040c3c3c0840c83c0d00301711544000c5011007200341005800c0070a600f1224034088101c011070b04411941603449005030f84c40c0222501036968003150b8482e41e4907940d0701c00020034000d411101c100055801c4d01c1c603280091503101032200081c00b0911306420024403d0061003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 565191663 1250 565190413 565190471
    0x70507081c0f0e040b010e060706140106090b031305010e0703051c0e030a0b150d0b2508010608191406010f0e060711120114010e060a0303270902030a 66
    0x2055038031501d030740805105a01c3c50141d0b000142c2801c1c0000503240301d440041c086a01010000e070a1040040d181c12075204480c421344004041c2e40c071540d00341d60031081030244102582c428000038190703990418100407214000c400000d0302d2160282000c5c100381e080d8000b0343d165404000d4003814010407403007020704100c02e0300d450f125411143c00041d4030307882001d0000d000560848041900b01c0307400c00840d000400020841c898207a00c3c2d2400b00843c9004440c402841a1080c90826140030501c050a05183c115521210940c1c00d000040e03a0440c0e0151503a030181041100307121a000301d40c0303c0d01044d5500001c4004051134a04001040c482d03070940d20000300002c0d5000d100701c6440d0390003580d0704154040780100b0102411404100a00080082c010a5600f44901c86540c502680b5146041c0d0b661001d013403500c0d503110414492125840d20000f8001540021000d100c40300000451030300c00296540f0981c0d0700d5842810100f40d80045da40b60036103541c1c07124418981d070700604522072064960 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 565192913 1250 565191663 565191677
    0xc0809101701081b0d210905010e040501030b0c070c050319050d1701170c10091e03050a081602040c0306081e120a090f030615120507061202070507081c 67
    0x1c04c0b41601070341d540441900400820b0021010030074800c804140752a0003151082e500c0d04580d40050841006200301e50104000089600b000d0074107018250503281c00c50071002e45600c81c400b1003507280c0c1c0a5041510783e017400c4003000c035036507600307200019a881e12408030088500e403a06156003003080e0032070254248200b03151196500f4507520031503811190b5541082e48061004401c65081020008003180d0241100c991901995040301d21107098416a0301c00c43c281007488640062403095502000c0c0072a880750129100084402006080307a041d0342448841c002744a50109058425104002c400300b91260030521980000b004202c00c3c180300822800e0707104e01010421601d900c041e4a180120040004d000c80c0300c9401440103074009c110b2200f2070010030340c0d40c0c1012401011a6080c80c4440286020300062030600c0030003210f12107812401400e8400d242c490180c40000080b0404c404c855002d00014020582c2481444010516080641100428440008521074136154901c0911150b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 565194163 1250 565192913 565192933
    0x703260f0a1b360803071208240f1306290909040c0b190216050303121f0e041401050f010b030604110d1e020405060a0c080910170108 59
    0x2210f081100d180320003200018003010001500758840075030b034205280c0c3c981c48000004125000200801a042c02045600c405009080c0708680700001a10380501400d03001c5a0003590150900d0040302902e8020100028508814003268003070000c00d8078440d03e6665007004101c881004000c1614214000d043c1040e4414481c1110485000b041e9115000301c21000001c0c0800141c1c2c808080a0070303414401640f146440607040c071620303c102c03031201d006014019030b04c4c1400310101d1400e404c0d104000c01550800081d6012030b002d010006008003442c8501626a02c0044150513000b0301030a0144524102d500c1e050801741e01c881c0030426001030740d80c0b501040040740e01e60080c0182c1980d1074079411982e00c1d01d030500064050150b01d281c510314000001100310b100505903100e40c00e20031344005100007041509c10006c0c22806180704240d04040200714640004d4400cac02c120780610f126000c911308252008010480d00e40c83d1041c03405c00704841941c81c100c43e0903041d100718010000c10707005010081e5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 565195413 1250 565194163 565194167
    0xa0219030c0c05030d12110403082809060801271b02060c04050607030f0c08030f04021c0c0504090201051b0c0a090905100914060c0d1d030703260f0a1b 67
    0x344000350511b86683e8803402c01c4a0114081120015600014270f00c4c0c88014488403024481004929111104442c895041070503004101c9903044a40580340c80c002a031030003140c10209818003580c03ca50203c01032110341801e040740700e80710380c144100e03051002040c15204c1c040d02e0410f0282c00c6c2e02c0c05100c1803008101507541e000c21035008a42c503140414a141d86a141034a500403040c900030040c8c00080100099144507050040c49a4000c6419120345100d04189801c51031048402400103200e949040c4001d041c2500207043c8284185400c5141c025210382d100000e2005c0758a070f1087e500000d20716849440e001000170b0180002110410500640d996160341d84c0041700c8890f07080d652105104800c0c0508141d80074410a101400c3e50b00501d010501c4450903030049000c02e404505c0c104001200346031300d031001e04000030303031000440c03030030380d0700d0b1000c0d00e040e1610400495100d0640394580c1000b1920a50540500a089982c580604201d24401c0a4450b18141c0701e180a0100da14800131a07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 565196663 1250 565195413 565195427
    0x16180504053319060e1e0c07060e070602010b0a0e060108130f030806030d090608042a0806011811120c040f0311030d02070302010c0303020a0219030c0c05030d 70
    0x1140548220a10b008480030040e0841500000d05208400b02c10803600764090751464040c03c150716400c0040343d84035000000b486000390390902c14034039a8810800071040c0022102c0c2c100d140b0410040c103000807a56002e0954807a074000c0324807908607203020070010b502401040d00e010002c8802d90003160510001480200300148454100054003020070b007030b88103401070501c000d0340004c0400c4444009041c003420f05c0c44240da120f40a803040b40324540ca014490300c0000107031900c0395a4410107031240d807035003d94410803100040300c840200c0000502440490341700801007041d58040d184a40c980940c42165590702c4009980d00c50810a6201d21140d2100485140d10240d170408000d03605e44044101c151300881d000b04400998072791020090125944849039020000c600703c40030100c80b010200d07190451840024007041c0326000c1800024000d030090515403d00744129a1074411401c6445003100c01c0c0034003074000c0f038801d042c0d02060042d645902405400d0640c02024003840c3c00d80300500e08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 565197913 1250 565196663 565196683
    0x60219230705030d1e020c06061306140105180406080601031401110a08070e100507110607020a0b03090c03010c0903021906080a0f090206071b080607020303060f040e1618050405 78
    0x20503652900f02080d01d80351440d9004418401001b10344504500f12425034071007055a10601c90340aa58603504271182901800042e02c80d590307000d401c0034112000664194100c0741001d0f41c407948000403142c460320340344103110003064500024890765140d400c00c4042c3d41f1814142c80c400e64108441d52215840c918101c90103091146000303543e1742e80d000130440d50303800c0289989602610b18044c0c035001d26480383c0901a40350181204216404000040100c03a10408800075080903800320100a1705580501860744100c030030003600c4030030010000103401c680030700300410040741740c1071010720950801918400240390119809880f42e407c0440150004030010324480c01161100588820400d0a4118540d15031303010f8581a01c0d030200e440d2006440b490a0150341c211045003000190a900014019014040b60340165140d902c07400c060007019045112425041a15030008060810381003000384400210310041807205810a25100344405454085954407400c0c08288004140040340300d600e8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 565199163 1250 565197913 565197937
    0x20a091a10200606010f031a01031104080307030507060524060d09050f030306031203010e370507020706030e070920040303050c241306021923070503 66
    0x158000c0a904580d0040d08801c20480841c41065102c048200040c1950066400345c9074030000454180307081303080f0f40030810300e11940d020400c14661154083d90041c880f42540309050f5152603214040030b803440d404076408400040d00002c24600744540c0d44110390b004015a13038820b0480209400c1800070511400c0d1251003070800140080b04158a6800710030a2a8000140c0748600110200355461790011554607000307001300c0348041010085d2504a83c1625640010004103484440c2c0d001c03100d0300c1c04d8411640005280c0b09415241c016030b45003203040c60103483c01150710302e403061009080c851035912601c103050800c440d03c41000c0000c0741c69426185455000600140710308400415092403c0380f0359040000024040b061591010003841c4002c200401c48030840c00c0401e28000c20342c4252900c1107d0190310000c520420441d601c00403030b95018200250920702c40207800d1400902203620030303000c42c82c002880301421088a030220a52120301030a030741000e4003901c480c2e0302c034480c203154958 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 565200413 1250 565199163 565199179
    0x5060906120c040f0608100e0318040609090f06060503031602012a05071a03010609140a08010f0e0c0406062016030b01030b181906060905040b0103020a091a 69
    0x8a14408002c4010100707001401481040400040c03c4000c00703841c060030415000d50645070b40e540c1c0c010300070210400c8818004524100100c07907040b403ca020502c0e602d078800c1e241d5400042a180b00c2c05440a41401180884410145031500200325102030780954000e41040c00a006400c26802c20138012a4082c04c00c40034100e415040c04090f444104441208944ca04607034002b40140000c2c403100b40d032200041d10481e10030b00003d50f803450009102d0b040000d83c02210034007542004130017514031007001401d00c074030603074644512609595840f81440461030383c2d4210511030010800083d011241c0c103503000c001ea00e0400c5d100800b000c2e070340b009a10103c45641300020f041401004490791802c050b10451000a88a10700032000d50002c3c4800ea80c020342c0d00c3c004c03480c520150010b0309000c0d58007034000d000c0300d46c45520b2000061000344c030564040350381c0d9000203140e8017070340201c5202d248107420542456041d407040041e80d24103034010560844c900030300c04c1e215140e89003500d50200780c1168090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 565201663 1250 565200413 565200439
    0x30e042003160c05010912020d020f0c0f0103140a0b0a0605120103080c0304030b0903070308070314062b060903180308040e06060c010e0a0204050c130314030403051c0801060305060906 81
    0x10f078081ca040000108250301e090a0358003030104200c00c8040401255080d50501d881d1500c0490365011420110384868022840b008214030740071603049a09081070402103040d60b00310001c04e0382098203e4030541843d0320340c0a0100c0c41d01e02803030320708054105030525a08203d20303c44080307581c2105010081c11030340001344811840d801001a20000d560081d03c0c000d079440d2024000740c80b1340242400b240030039a4907001ca50340700e001c1d00407142c1c0ca512100c0c0b4100a5640c680400514480704000e0071990841d0804445607081041c802d0800d9601070b550109100e001e51500601120b024058050071041c035440500005008034121022900502c80c07d40740703034403401c001400038454280c508109600c4c02410390b841403004208181d406008650400a956641e00c0708402d40c412040a049814048002880050309005408482e00c0300d1100701c9080584039943c0c1c81c42d14000c128881d021030b005800142ca0546d00c9882140507200c280340c1130040c2c2c03d003040031601415020f4082c07480b400541c5021 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 565202913 1250 565201663 565201667
    0x150905070b070302030403020f180f102c070809070314030d0603151407200f120309010f0204030c0b07110a090c0908031201031b0909030e04200316 65
    0xc00103424450412562088a4503010395a80c1c41407008074003034020010402d55504c0d0100310442c045000d81d0030b0405075a00c0080c00c1002640003440c40e5410f844900011038682001440c00c4003028805003541d072209401c4e80c203014400c80061003a0108460300040100140c008210401141c1e070206042000c40010700c0403500f140117a64058403039928061001050248100c80d100d08a0038425081058580b0405071a10b01c0340102c0d0088041601520700801d01958140f4807080c480f410300a42e40a803400c96200c0d420184a9044602c2000000c002d002d0a01028070604a50744240c00085180c1491540c8017480c80020b4803039800216000301e0100d003400124001b846d40348400820782c141050300ca00d2001c6c011300210f00c1c4100010154980840c8400c070000c1140c40c81c08601805020b640c1c61136030392004041c6101e0420042041405000801c0f54030b9008059400d17100b603e6016010600f1414441107421044404244514400030000c0d050ba440c000c5a40002080b81d044e010700d1081182 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 565204163 1250 565202913 565202923
    0x604140a1a040501152d080114030109030f270605090a090b13020c010e0106081c0206131103030d0519180c0e060f03160326040905040f0b1509070507150905 69
    0x30b8188403040b901d078110003103500c01f00c1039060741c014030710b00e80c01001c411082c503080700d4207190020f010442c248580c8810900454a502406a80c61002401200c1a07110b840d0a80510303841400811808104c40e00640f4100d00d4400161a805404000d604c0840c0001548c10840e0760303000c1041c560008403c0c1c48a00c00703412414240812800a10803d0760f5038444598030580e40e91036804c1c40d0b500843c007003500f51020071182d026042120044008170001d072039001d4061001207040d40e0510040106014909083c025144503206001440c0f14041d00c110b401010790f501403149510351040740d101000020740180d42d900076150480b10910490f5101c2000c03941440c80d42020320781c1403080644080b012000603809406a1780704003120b1031225450040c500d501c064207070048980210a120034064a440d0743e21103548603005101254542a0781d4650610010085d034401c2141c5a400602c0a0f25060126034541c000805241c81858a045901d8111045000214501e8060748650b072801c02d01c01d082103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 565205413 1250 565204163 565204217
    0xd1104020310080f061b0a083c0402030c01050304051e010e07091b020307031209020102010207060623060c2a220f02070c0306050604140a1a04050115 66
    0x81203d04c5842c400801c280d45100803651520b42d000b220380d00c080408800d1055441c1c800203a129544691a15045a00c22000d1200008e0400084502c1241c80c000c81400c089440c02c4054500452820140181400d042002d5922410300c1000c005000004000007080021080e20181c4018014500c07041103000d012240321040c3d0900c111800800e03d4000d07944005620740c07002c4801e40202da5000303401e90302d038018000040c010440380c0d40a40c400003110b0704821b14041c030501c00103280401c1580c45400701c13600c5402910540f003050149260798500d445e88a1000c0e0011911320b414030340354075002640c9000342c04114110200c010301810402117101407098a100008204109000e0f1f000c0c1400400d26a04080c000c0076030411041459442c00c510032100039581240741d0680090840e00da4a01600e80600b8594206644004540342076581a80303650141c003034100302007405015203195244d80c10980303003510321035843d2900400c40184c1981603280b14141900b404138504600c044c0305130412002d40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 565206663 1250 565205413 565205429
    0x5090405090c030708031b0105091e1002041401030b03150c0a05040b161b181a21120f040e040314130f08061b090f1206040c050d1104020310 62
    0x80c81c0414441d0006c40a000d00c03503044064400c0000e2000860343c26a00e00350341d20300a54015a8040003ca0344920503e400152410300700c0e1940c40089036083d08030b80c881da2001c400d240d04d04c0750b82080c540c0d160141c011040f1003240100714500114041c070001c0f9030040e109103441400014120300c01c03401076040d10000c000c0f0740012622032080d07240709541400b201404450b10f00a02d1104400c8140b41c401c07000079a48040c50f000080b20044404000409907016608090581c100d020303015940d0f00c080380500f210391803000360074032907a92844c1880e1004d084a00f42001d40d082c011300529214240903902151a44a40c2d003101e510349050603a0300305065070000d510300d84000362014003800894503205c01c40300310403480c2c0c0e0103641e00c280c0305413503c03010303905203406800e00c00302c1085408402c805041c801d5001400201411100d1001404440c61040c502c2195008071702041b00b40031f405008100100000d0b54203044085955407070850185108003054401c0c0c2d40070002c40c00c002c000e081c2eaa07010341840 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 565207913 1250 565206663 565206673
    0x3010e060c0c0c030f1c0c050a14012910031e090b130203030703180b1315050405090c0a03140a0203060301051005010f0c02240a02070f0605090405090c03 68
    0x41c0c803111140d40c03140312006a03601c01c5038070300000e030b08000640684284104016003600109400c48010080303034201400108800200305501185050110074802c13481100f941801205c00680c2e1420354010460108801d0a0310b02c081a1040202d141079034654812100c405900f40c00700000d41c0103050b20700f020f41508034003014037044031400ba030200c0c0d4014041e000e88802e680c3e8a5520f00c03a000f120050007074040d081132280500003070241000c8a0200048401ca00300c0c10384440000029030014502c40800030100d5404002c0070501d180441c0f00c920301842c2c158607050800340411520720b030203881940f00b11000100001ca2078805ea014040180d0345541f401d0060030a5159140079410640b811403082d40303020082600204440c402d2001c50310180c507000c0d00180300070419110038141c401d0698001800395948600040c0c8170040641c071312400d02c4000d4880f0000d2000071300e0a50150064114961020014000190480c0039604c6800f0104c40c041115500c0883e2a42802c0341c10311741e2078051080d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 565209163 1250 565207913 565207921
    0xa0c150914060609010f090504061d0307060e0a051c0c0203030a09150c051e030f0c21040308041206090203070e01180b100806060714060406061d01060e03010e06 71
    0x440402281c04554010880c0c0c0c00e6110f08081012001080c4202045c55441103800c018450702d98003c5030f4030134010240003401d034401c554003414a190800302c8260b180c00004040d02088401d01c5502617401c1000000c0803041c1c03042e55425642c0e10245e80095500c030b8044206e001c868440d00b20505401e078090141e81c0c84003440d51014203075003018081c5040004a50210030300040c07266954101307094000f8002c01070000c4030424454a42c80b8416004000d0108010141a41074140010444606548002d10303c0c1c810102c1740c00b22030b80c103d80b200461184200820400714000100b95410f40c1e00002500c00c0c2c82c0c074146000380003401d0025000b501401035080000c0d03500c0d100060b9504940c00009681d50a00000d00010b00b100c981050250b4000c03030314100300380303050700c0703041641d40c41200601424505001602c42c900700000c0c802d1545040e40c01a0100000c014031801340600500000c3d01e40208041c3c03280103182000814001c40741080114000445190341c250040d40070903036800150f4245040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 565210413 1250 565209163 565209173
    0xd0c0b0318030c0a031d0d050304080f1209010e13090309060807020c01230408070b03070f0815010c0312020c1c0c0c0603090f0204110d200a0c1509 65
    0x4a452a1011034403048100441d080442182d2100304810040d0103c04080d0f68141d0b40d900003803885140042c010801070b0540d85600f020817280a010704000d5403100c0c075040d01d042c5020f121481c0000140c121740c0c040a5813038400c40a071000c009007421b003d440e0010202c0414a0725020b100108940c0381801d0014042c150800403c40903100746607103294a40d5204401683e0b501501c1014600081c0d101c0040d110000300007000c0d20760410120951807800b5030340c2290600c0c1140f290001d030001640001030110031a0022201c0400010b641000080c602d88009180030720348241c0d031000d040c000f1340c01c603034803c143c41140a43ca80130740d046800c54075845600b00c056900d000c0000614210701d2200c1818020034083d681c40d03403200b58441c4101c201c0c24240102200540141402103c4402160b801003005a5981c0a0001d0b50012800e0031038480070540d040c03409541c6c01305034020320216807980da21a00d01500d821181d400b6401d0418102d011050724002900100d02d003201e0020714901484841000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 565211663 1250 565210413 565210417
    0x200a0210080f0708060a0e090a0203030a11070e010f09181506170120070c0305010203040305070b0a060612090212070b03040c0b04080615010513060503180118030e0d0c0b 75
    0x10811540400b82640e0320b034015140380c0415140c20740c0c010100344040165403100a00f203640002c244041d00c108c0034090380403030b2460304040030800229003042900d0080d40000c001134030003400541c0b80d55889503d82210750240b81070038000c04000c1c40e1242d00c034030802c00355040c0c00013249502c43c05442086204810314001085a0300850440980030540601800414010f5400c020090300311081c0c60b98120055420692103407804448581040b000000070400c00c0c8003445c442d5019031161503480b0110f20b0518001c05000709200312075480c000e002d100c00c40d0b00258402c52400410340018013000103000080000882c075800342001c0c4a590000316000090074055402103120346141d022060303ca02e85004240a41c3c003500310701e0352040c1c2c00200c0e0035440350107200281c2c8040c14017620f031030b90406c042c486031840b50b08094086640081070024200342500c2182409200034000c20036000c24400700c03140c0100344400981086115240100c0030b0383c80081c0074070b8050388840000d62556844095400503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 565212913 1250 565211663 565211671
    0x4110102010c030209030d080619080d080c1602060307090302060f040501142107120e0a02130b0114070204060e1501030b0103060305032a010c090305010b030a03200a021008 76
    0x1542001d07214100b0500900a0714080316000b0050290b0300124501101ca000c2e00500140d13001035031407640381e240030620b00c0d8440548000390203003900241c82000540445c034050801035105004220f41d00c85070111520924000c0d0b030403182507503030351150306003107488020540010394842030004500040ad10b00b076009100300c40080e2101c1058102a400180c01070182601c85100c03000c22040418002d00d070148440ea00541d1400c040707180d4110350302d03601c0848511441071500c5520020b0100c00b9032610300c1c0e00928162000300c081c4880300c0c58000017040303144a120325400c0454003280d03130f0f804c540e40c80e001180a0100d10b0440f04180c501849030b115884401c0c3d00080c0440e161031525102548240510001d5070703000300c011441c02c0402010100601c4164010388005039291180c00c81c8a0000c0c0219801a4110350710089210304500303055086540c1b202445200385c0c00000c0000029402c00b1aa002a07011199801107620421001d2400c1c0001c2d00d60095204413603941c5001041c1c0c02c06210385c0a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 565214163 1250 565212913 565212917
    0x4390e15040603120309080f07030f0806060f09040209240304031205040f0305030a0603140d091e1a04031a150301060e180a0209072303010b0702090402040212041101 73
    0x20000103901400200da04601000d0000c501c800702e5800414000c1d0000003516200b0000c00d8504000c01403507403801e03000312400b01c002130205410400d1040d40049d0340d94210741c0c2101c0036403a045082c040c071121380c07143c070391b407640110f8022400402c0c50b03940b0100b0031103444101c42d000b1600c801c101440411a841202c085001c68a00e090001c5880d03110301c9a00d1156074407484c503000e40c0c601520244d0f89070f00002c243c14401e1f9101c16010001a00c0300342400414180c51000741094240306502501224094002d10200f88940422000101451100c442242c06000e14ad603004036000305100003e1165070001f401700c0c0d002c045070301c4000c000e25108501c03c00e04582d000c03482003a21002c050903698503100346840044c20501040c00014800144074900408008641c1c00242c0c42d4081488401b0031105031000c6030a42035411300c058004074000c00d10b0403820300e05514640c10806071002c0c034003d6504c082c0c000e510440c00502151140c0e8110b48900102c00303a020f24510341403034041116000c0d49410341c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 565215413 1250 565214163 565214191
    0x1203220f06020a0f030e040b100207081209100507031103030c04051f02070303050d06080618010605010c15110d09150c02070f0911041203030c020d0804390e 69
    0x80d000e0310214882004650019400f910292140c5003286c429060310036a80e402580c9843d4030301795a50318400f000c10388081d038001d0084107141c03414103410001074110290300220f040015503143d6403400030403424110036040140c1c8075010ba04048450522041c54419680b1000083c0070000c1c05034005803045507401c80b60103031101e0300407003a051800d180c80c00b0080980d00c01c1005000090048014000e860302d1210b00041c02170b03440d4640e5141200076150125001c418114024000100307000c0c80002d41401e003004c44022000c0c0c0e0700e0340c800340d505889244000b9501c0500c00c905d881c90700304803180c95028420901c41c5207258102810605c6100042c0d41d0300d82c0c908802e09140d0340c00441c0400c210303175070000751100c482c0c03a040f120005001a500100d40c0c0c160100000305140c4c0700304406007000e5000b59030000c0d9500300010068600842c1070384450a018460040000103800e030012038200d5590725140d049020b4806817451040c2d13170780518840c00403440020114411f010b0b8285140300f078040d40c03a044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 565216663 1250 565215413 565215419
    0x6030c0f08030d0f020903030d02041706011a0a030f14060a080111090d081312170f09010f0c140f060c0c0a03080c04120b15040c020c1203220f 63
    0x129440c054401d4003002e410038000500d1001c859030190f10181d03128107015140094880020b07095a220b80d060305055940450b041c401c2d1500c100c5201c0c8051f455200900c1076504143d4586054070480da2603030744151000a511001511a801051160303104800503c01c0807510f2070100e2500d03404448075409000003400004005405004440c0c40f40814810545420b001c1c100f4060080d0001000361840c03d070400c040d07004114100c2801c00206190300e500c0240070020f01d054140c06241c100703c8101110248550000b00c1068403c45000080c01d007454800440c9003941540c521001c11000ba0014050300c0030043d01d03110100301c00d041040076806a602e59a01c0c0503030034080d03000d000c80d003003031a80c019500f0f2030001740030304030311034000d0039625801c0c0c1410742d166880352280034880003c44401804405002544803140030780400b00714111401e0120200010000350f56500e0f08c00c105200305807100e1101c2d440c150600444044803422142144c0081074010b44042d11040b0f44205500541a00000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 565217913 1250 565216663 565216679
    0x101704060e010c17010510050f0406050a111f0513050a110102010605030f06011a120103051027020f13020f0a0905010507030221040b070f020307050a080c100309050304030606030c 79
    0x10603243d03145084c05031016400c5c0018480d0442c541e0400d41c1c20b015080003480c0d4107480c8000a440105402da880036650703000100001e00f140407006443e00325500250fa05140c003420380e49219111103010500241070754620f2241c0e0131422001c0005000c1c5e005500d40c00c41805807407102d813800034100707800a01c40250756400b80f580d180c4d003e4140d541103800c50700052005814540000503c80302c544060b03411300746d07550301e102d12452013a401180e071580081c0991401020600a6600e46c528840c44541209189000704c2201d00304800000c0c41801034441928041c0e8400307500000f45115908115190001800e9070883c2d94019600e044c0812201c140001d050b61040c030403256000d07803581c00f40c1066a42c81840012900a07405003544910040c400814a90a641e01901c0342d14028003982e0680c90b1140103150410020750095405520a000c0601515038001550f9200303038416a8240324000180d44110001c3c418158002d013240030010740002400880d402c031000f90790160302c81050807540d40c01c44d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 565219163 1250 565217913 565217927
    0x50604061a2803170307140405030307060b01021212010302030c03060108100b2e030b01030204120b0406020f040e040b06030610270617061302030c101704060e010c 72
    0x14907501610310b40582c0c0980020305032051840c099054140d06843d140c1d503400c060400d00d00882022070001104000c1850790009120740120350342c4861174070b46402c15002c44e480b44a035410240c0025241d000b9104640d108000f00000740c1000700300192500ca1006000482079400e00c07069100703100c2c072a001111454046241c504842021004100300031f4038201041c060700d41d080d0500e41c4076803c405130006001c000000d156000c90400154500601c030204058200c80e900c0010303d0405105000034042c0d0840d41c00c8803804590006455040e41c5d40f00d1400d04041e00c241050000d480b600410001140b24a00f241c4601480c403515642c21a50345003402e01d03a40720002c4542029800e0305401c00c10440c40540321401c0850203c000d5003120800382c4030743c001075607850703800411039010a804068503a03034148041500050300d10002d81009540b0f4000943d01c0000441040c030504403001d605070702501070348148520000c0700c140680e5500d02800d0000c0103101c220051041c42d400c003a4606025841045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 565220413 1250 565219163 565219211
    0x60115121107030804080705060a05061c020105030a1515030212011a03062b08180d020622030501140402040f0b1503090a020d0b010f0b0f0a0f03020f0705060406 71
    0xc40740c102031441e00c045070213030b00203001a41d140740100101c6022076414001188103a01489000c07886083c42d000740b24488840889031b40b054800d0f0072043c80140c0e8407004aa070000d081c0d03a80800c8502030320000c16480c15555002a1242919021181d070b46509034020b0f00c070005004008a205a80e42d0071101590316044c0b640a401d0f4408000144441c03800082440503c0888001030200d03080903607110300e204960b50016201e580c0007090040305e208408035003981c2c0703003025504000c54100c50340c0401c1c018010320b0512042000c410508040c021080001a030055401100030300881038086070342e1500310b07000d4600b80d000b10700305180e8850146d014041c1000200b0060440f41e5814910305810105420145c8801041e020f159525005642c6040188030400d0080720b00b9074042d45440d800210007043c40c0d105030704581040c040d4440644941007910482c0e0324031705200000211685045000748240d900d40b40004001054070410f020001031903a108034030400e0104070344900400c60842c0030020340 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 565221663 1250 565220413 565220441
    0xc030201140c0c060706020421140703110d050a05100203040b0c040302011d040b060c150901050f01060305090a061b0f0504080a03031a0409050d0f0f090e1806011512 73
    0x40b54000039040c400c0040c0b44081c046e034070042c2025120b011180840340d44155a152060301d012a01c0148201060f01c142c414000340c0c01454031610715560046040c102003080c9219001020b004002d100c0207011610001e036120068403203003c84041d201c8000d40090320103540010300d21001804032102e000403942684d405071616030f04102d1021110900c11006c8107429005521099508040d44410019000c50708251b4060f04c1494401e0b0601c05018000615500040c2e0402040c803400c401c200011505545541c030b000704107a83e070003c178140b800c07044c620020255460b03c0003c0414012400301c0c510300c940a95201e00d50503041e01411034082c0107a00031544aa08080c000c1c0d000039000b03503c1005035480d00c490501003220b071900001d04aa01410060344c00760000519011a540e0000180c4008030b480c2c10002e20310301070154007c08542040c011b2058005d031801c08146e0501d60501130094120340d200c100c51083d0b86404111a10322401c1283c0004a0303a02c41001031422681e0081c0e01490b9880 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 565222913 1250 565221663 565221673
    0x20304080c06010909030c060e120f0d0e0d050304141c0f0f020f060a0b0307090207080a020d03050f1308090a170709061518080733020a080a18030c030201140c 70
    0x640742c42c0c0c0140401c00220349c20348030f5920306e00304202c8050060241c940145105546442da0100000d064036090b202400d6140c01c1000584252a08282a281c00a030000f1185050030441c00c0d0790b500e44001c1002c0c1c1c003015542c442070000703060350100d00300c0142032085d134130210180c4204400341d07501e030040034800807203402c4000050300502c2c556001c0f004106000b03040b1800c2940e00c2a40b0801c0f68407801050366480b000059112103e03404015108040c0014941002286043c18100032108009065003a132018203103040d43c20700085a040d074080f060010045c84580f41d89070b200940b8001c100d981c0100c0c030b0050304000610031110348500b00c100c0d040051261a05010350208403404400382d201c01d60301004000000c5240101000200b010300130540d543d5140200c0daa6500e100001d1010259100c0b00080284801503540800d82c40304965100c3d810a0300c82c1040042614038104c4040000081003424a0000078860790545140c00c0368004e8903121424000d18000403064451480c001d02c2940c82 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 565224163 1250 565222913 565222937
    0xc020d030f110301150801050307121502121302040b06090307090b0d0803010f05090c090f010c060b15071202160308071a07030c020c0303030702070e19020304080c0601090903 77
    0x2500810241c407800c00000030001d0300c02a103080690002c2e007103078112050034110042a1038005800c240502011001440d0340c901e0078500c50701d1000c03030100080420071215400300d910030740c90b0152148103105041c014038519081005102640c02440c050b4495401c0900f00c920b1070900c582281d84407031000d03010b00030b240d051090f400007519042201d590800f09014507240407500402c05103018103500d4032000d0682e850300c010410480e0018141c0c3d4540d890070040311000d41d5584004001052082c00d2610300b010a80c24140300420480b040c01d5000000209010650b01b0454003c260a81c070814800000e035052143c200d076602c07028007040d1f070b26034204403081c000b040c039042c05891624413455006807a81320507485030b00881c506540c040302080c1c8400c1c8202907240c050014841128080c5d000b0f600718940301c00001d41e2000c083c41500c1d050f1064202151000102403001451840e0a0409640e81d040c10310f0092640d40c04843c42040a020300b800100da080f03011700540ca21950035076100b6418000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 565225413 1250 565224163 565224167
    0x20304230f040b1507140a150b030303010605040312020c1002010213170c011d1f020c03011a040b0f04020735030402120307170a140306030d030b0316180c030c020d 72
    0x400302d401561001c0449441c000707242c00400c5107c1045220b81c02e011003403003125802c00103460300d030621903209802c14801481040d9201007510300b102d4020820070784840c900c030000d0741003011541d0320039000b508006c0d003107030101d80540083c03007640401040079480c0c659490300c002ca9050522515060364100c804a140345622401c3d540c00c0e00c001040c40002424404000201c0c080b04d01950f070f00360007181c1000c9031101501840301200601060340240200c0c000c00c040c450241c1d8000d020342d4459999140344401030346442140884809014104564400c000e080c50410400d0051204002c84101c40070205d500c42552800030490400149007415a143d9a0802180107511044a4901d10040c400c9501203804044010141021b0030709055440d840c2e11001826900d1420724110366400400a11030a07131000190410003a44034076000a4100202c00003e040c900d0402c00118410728170329000c600c030940c9001c502c80c0040455010805040c0d010010b406481d048490000507801c03200740151000c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 565226663 1250 565225413 565225417
    0x1d12130b04051f0527010824040c05070203010f02090405130c09180501020a0908100c020c0d03170906070905010806030a0219050d030201090605011a0316020304230f040b15 76
    0x2e109402c00d282002070740c0d4001c041e1001084001070017099a6030710603a0395604110915080f8040e011901004550301ba8500212a0b40c000000d0065a03a240540350851241042d01c007040c0e402070080c05503000090400000c0d41100c00500d01c13442c9400003140d00494421075150100350300070880c41c45c061a1140f484001c06501019002c6d03601c0c2260b0b01c4000490070b1005003102d400948501807040d05100030f0038903042d10b0522001e03441d0b1910000c20385c85030300001d50200c40c2c04100c40410141000b480c04031652010b501802001e407242009201c200200460a20301c600c2a40e61a442240da81d02d004450710141518000d4040e0050354541004d41050950349000c4850303640c0024541e03544801044d2050781555042c1d005035980c44108040052034021107004110844c0e909200c920078001500310f91101402c0c0c048036050001082c080300307001f841954000c102280300700c0c2d0121006040f802800813608481c0c2e1040c0c02411120800e45040e02ca00300c076511010b41075044c0a401d038100482c0e0b079 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 565227913 1250 565226663 565226719
    0x7030506010b090a050d0b04171305040216050102040e0f0609010b09010f0306030b0106090306050f010e0106050309070305010c0e1906080c09010c05190209010b04181d12130b0405 79
    0x8145008004176480c0c032600e92080c2403506c20314500c640c40c40c103410203142d00f4002c14082d1015100401c14840815014508003090761011a40141d555018840c1641e5820348a50004c11030350010900081c2d100c03c50f944e151107074071801801c4c29140d0302d050801041200900500c1c14a010500851002e548240e44010180c00c19040000b503044e201c0c0c40b07240d0465426405003000626082042c000c02485029440d00540241c1d9180040d50601d05c8240c18a44140601c1c02004804000110340350030030000d660040d44c1100080000b2103103400300400c421048516035004141d20b840c0b24120001c0000428111000c566410609494601000d1b907140d2050f004603040004031828400820f01c00d0028030580c0e00080100302114980d403041c0249c45034141e006441440d42403008201c41d80c8142c801003414240a54002a4081185c0c0890440e0440580380003a611411405024001c500b5005000285402d006805559078841d0309510328881c0d40079250704044900e542c10900d100d100046200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 565229163 1250 565227913 565227919
    0x110102030c07030c230a06081009020d0212070804050c12150901050a0c0207060e01050f1b0c1c020616050f0f0313151b02061c020301150207030506010b09 68
    0x16120314807200d1441c14403aa0015103040c01100390401074070724005d050303820f8070240440d91000155070000240c4058807520564051040341030004070400790281300364000d010941d504648400c2d1113144107001b50055655403c0115150f808580240c0c02140150b10951b485001000c00d118010144403c0340080d001111092143c1e02201c8000040c50201901c1503494000018040c50980101415501852008019500159024800d95600c8a900c03503a0324000c0c03d0099640707010302e003404458400d594031980c0d1003800d0020078054040118114407241c0341101e499031500309030740c458071400c0c820300c0c00298001c000700440c074603624000d5696918a8010000c0d2246116010000341c2041c20031755009139103030000a075404407800e845429001505507a1442110a00340c1213020b061010002c000c1070390203130003450280441d40c64400f1500345142c182c06411070a1107061400021750002c0c0210000075411020602901d4400228201103d4000f40242040e0f403801198130071544c0b0540c00560 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 565230413 1250 565229163 565229167
    0x9060411060d02070327152106030b0609010806151207050319060609050714090409152702010527060f03040b181b010210060b0a171311010203 63
    0x601c280852000d4500c01d406604c4400c81b112204221041d0020100c0760f10110340c0c465002401012a410a60304202915080416400c590300080d800da07a0200001044500d042c040e011080112042403280a04000c1d2145452a40c0340da012944400007101d851492880a071002c070150b160580070782c41030300109020b9a00c0551203d0110382040000d119460407041101c41100401c80d0612075400100703241c1e00108094100460000e01d500f10200c0403034070641000c030709059076903030350b5228500c01039110844c120b1482d110111034010b00000035502061509140c5614402c0c0c01e120000410598141d480a1a181080d0301e242c000403050301d003506000e08500c00300075013502c41500134000b2919084400b03032280350a280080b2144002081501c06142c41c80310f10415100000e20310072880400c0300914010100040100d00c5c0000701c0c820114030f14204000061100c0542000f410f81140d00d54030340201c0385509000401a00098810034490082d0701c0020b0041401c0003a90240ea0f40148140d138 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 565231663 1250 565230413 565230427
    0x4030e0d06060806070f02250e040c05130504050a080c2e0b0114030c1c0207030305250206040b1b0f0702030c1c080f0c01090c08011a0306010308030a061205030a020709050906041106 80
    0x89e07403405003102c085422030780d512000d020618110b500000c0300080c5100502140c03901d90f4900b0340320383c2c006400030280300010407218001c450a210380e008100510865413000b00c1c10412151019a030900a000302e180740800da644c480d44a1100083c43c41d0040030743d5851500e885580d0107855008511108039440d91100d80d814034a0701d030005100f194001e580c04540c41c200b4541070740011440d050a0019120550b41c804981d82d000b20b2811b61180d0001c1403020a5591900a0752024101901d20b4407074080c0007a01d032800c00f0750b450242000d24002d070211140300302ea50086c0929481c01c811186160403520302658001034180c3d00400b0301010340a90070342401d03c01c180c45401d40f1546201281d40c0c4c10200c000317000e81e0707209100d542002107003101001400c4140d200031070f4840c031040c04003411403100080003500d0890140c22920040c1030110403152480302906143d51203404c10300301c41005001c0c6c50303800a03403e00c0070b02615020300303d00030103000c150700e840c0d5545031102441007180350045000c5c4164 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 565232913 1250 565231663 565231679
    0x3010506070203030c070303030b090609060d030e04150e180102031b0d0b2106060919050a061502060108010b0a03030e0909010b060c01021b0102030f010e04030e0d06060806070f0225 80
    0xc0005502c49d40b80461414610410890707210f50040415004030008020020ba41c0e8a202d018202a90507040603051495102c0104000d001c0780f282083d0310300802007000405080d01540d880c070642005c4401ca440300ca0404006082c0e1109444007618918404d404181c4610408010111b5445c011400140001594045100841d03184141c640c00054140d601032401c1060247c564882c0d02160f0081003494a4000f0114825250340c1500180303684000040380b0011a50101c030150407444454003e0b9210400c0003592200c090180d18955401c003841a5010b00301060035106a960540359030780c81020031418002030301402820b01d1311564035145080c41c00d0f21381e20001c10001d0030100000da540d05101000c8c01d00344038044510002e5070710401c1001154014420072a0540783d40f4205584e0585440c14100c5035944030700c444607844041d0440440030861503600004c21035400c43e06488a41d502d0302d20541e8808141045140580c1020281d107200785054801302041d070340d0401e0b4660700962520350b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 565234163 1250 565232913 565232923
    0xf020a0605010b070302010e010e03030a150803220806070f0c060216110a140d060207020d0506091e0f070612230a050c0f0d090218070816090b03010506070203030c 72
    0xb583d1a000003800d02d090640c203001d04010340c82008000e00440305880d210315a80d1000500c07410303115585228841a449125201c2e400078a1300400b03c13600da8880325150020040e0360f4006d002c14044d00b07100050f48102c042619840340040e07840e11082c890030400e081d42c143e00d01034001c54407103a0820480001c00c0310040c0c40c11050b4040c292009241040c40d050014018094011760070720020a251101d1583c2e84159211040780d1000c000b50711040e0520102d4a5100003a10040484c001c1b041004140c0707030002108500030010740686c41140e071405103002d890b025020190301ca2500003000501c01103000d0348811000013a456000100301c89040c1e182c980c507110800d100d101d0020300d8018000c03c180903002e000c1e00841c01d803041a25080d01a01580345a12503480e0242215441c0c1555100350750b40d01b458858040c9506d0103400844c43d00c0a80140551412103c0c52003261000001d41d450354425100700c42036481022407280355900f054100f240c2904040301c2264940f000f0030080a8451041c49 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 565235413 1250 565234163 565234169
    0xa05040512061611071a2106040b0411030a2c010212060a050123130b0901080a05330a0e190219030b0d060218130c09060f020a060501 59
    0x142c441c90824403516002401d592804004005460b11039002c041404200f0000312054640c4010b004640c030b2007850b0660180740c200e280c0500c10101024203850315001198402c20040b9010440740640408210450350000384a140000040c4000b0b030000e541503000c501c655040c110000b82001071031a0303444401440703048108aa940109050301c3c00c5000084098100d4022100e5541c820b0400c3c0000302034002c8060086511804400d4a58092941d001118001e140700801620803c1d01c0e1424103406500a2000c2c50000c2c2a0701c00280101c1054440c180c083d105201540801c21038513071612000b5000802c9502c40d51410000d858455030741c10100358014804140010503d150a654107000c04242d00d85000b00e15004105c2c0008041fa0300100c1d49841d031007414000303a4441d0340c2006c07884d0300101c50710080030a0f10005000c444108a5a555204860110b40000c0300303a9580c181c0d0700c15078000340f01000c00704141c20360501c10305009105403550a249841203540b9080380ba221403055174070a80c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 565236663 1250 565235413 565235449
    0x6270c09040f060b09090c13030c05010807021f09020303091f0813080a08091c0504050a06230f1204111809070509060301090b041203051308030703020a050405 70
    0x148400c030340c1064007614401e08034a000400c5902c0c07412034646894031031864040d1090b615100040c0081604c481956102d04a0161300340043da00c0c0d18045401c458240036442c0802d560000194699100103400c88207510384000079040d01c182c282c3c400c0701070b040000c4102e030700d0b000c148840001525201d83c01c45050b448a0f000c2000031116040242504001400ea030001c2100e481840c1d001c101108201c494038a51071404400c1c42d900d03002c0260600c8001e04020060313250302d0350400b8a07103a1240180c03095690444804a03201c1c1c0d00d030740540782e03084021203021984842c203503251900c0c0002006407059105807a2a1840c025941e0031300e18003a04103c50880d421002c0701040c000d241007005042d1094441c0c41aa030080b401d00003495036a4580601c17030948621020b800056141c2c9082d0030044207103500a0484150f42010b00d071020180794540d00c1c2c82c0010b464080003e40c0c0d010140c24088100d90040280e5242d5202d050085020b90b009a0b0000e0600000f0000000c69840d07801048079900d440d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 565237913 1250 565236663 565236667
    0x1030216110a08150c0d060b030f0a05010605041a070303060e09060109060501050a050d05040c09091406070f0503150609121e010204060207170a120504080f0a080306270c 75
    0x80c00704102941e454021510951040302e42000c41c00301080c08176008260030584544900c0c00c0d6400d040a4800398014851040021007408841280c1544046c0100911003040c0500c0e178a40074212030f43d006911583c2d114032181680300c61454050801054003500030b280c08111917440d110025010030042e03400c0000da44c020b41c010450003010784520000740ca07003440c20744c0c94000c43c900010b1042c02a600840d0311207955402003405c1010002081c40100281d0034240104140c604103000d17003040010440f02940900400984003d02c00e030905101c60030303d5102d150035030319900100e60b4080351034155250400c804001103202c45e0741e9813035407154071590040240030342c03031400880b6030b100881c001d80b0000a0b80184010701c122900403410301c00b0345076003408081180c400d540490b4030b4005025006041d03041c03003880017a4056803180041090b41c5010003102c5003100141034440e0755004900e000b400440050010580b9450048038200000703042190ba043d01c4040034100468400050740c0c460010100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 565239163 1250 565237913 565237943
    0x30a020f130f08070501080406020c010b190302040b1002030415110703080309100506030c0f0621061f02060a05070201140109060501110114070c1406090303010914060d1101030216 79
    0x2c8019440252030300700054502c030391400e0000f80000350041c1004012035004903d420281109501400780c8040c0100607582c481103948410b4141d18181c00140e01503400c00d0380021890400c440c030918a145580c1c01546000d00d0481346009100101c0038010400c500034038500d0803d101003251802841c01801c0b2130340d40e414000300c0c4038a4000440c03a00d0085074107080c2000003943e804510000641400d554141042c0100b00c00540548195202015040ca540d048188801c50f250402c6104120581e500202d0b150b0514007005d002d0040032075100168401c100207000400c15811040d08107020380008200301d1160b29418810090076000010800d0346c66601b0000da680c0f040303800d610b10028200030001d8005c81c0800e00b80c4020014014024440c0e100c0180041041c101070288455101005490450500c2005551283d100788117070501c80d0f080c4000395004400003007080c2d0003240028116041ca219590f47c04520f0000d60300c0316410f0560078030aa43d9440d20624200c00782a106501c01004181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 565240413 1250 565239163 565239179
    0xf0613030c1b060801060206060d0605070e0910030209010602060f06040b0609040c021606050a0801031b08070e0f07053a0204090e010e030406050f07110a17011b090b030a020f13 78
    0x38146e000700f01b1903010100740007207601e40b020300d0426903800c0f00011030190f0f00c036241615100b0101280e41d4010048100b00134074220403101c46800e0703d200311490802e40e661940c00b00d994007810b1b0740014000017a44040b400c2440c05500c112151100a00740d40d04011045000808840b0003025403409030700301426044401c10208240d00107420315082c440d040c000182030040110b0414080100304201da0340441c04104c040c004002e00401242f000c44140a8039400c9180182030280c800842ca003c0000100303e06901540079140e400090b5200d51101070318030301c40d0101046813108900c0c21040c920030518107220041c0001d1003d00004040130400700c2c0750182c1e26084424940c1c82440641080c402800304c29804002c443c0300c2680515820b031100410704084d140c107013911101e5903001e01001d0700062954040c0e0100010710300c06500802040c0d0102584402c28580340c0f030f40720700003428144240071844d80100a550414000030005083c10700c0800d545425600046090481c08100001044080307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 565241663 1250 565240413 565240427
    0x3071e11120c1f02040305010207050313120215070f020307141503370207060501170a08090103020d020c0712170408190f0516170f0613030c1b06 64
    0x14000c0940d41c40c02012002c0c1c103840748402c18601107101081061031032035104a40642c2c000d9500701e0000c55464485103002540d0703a00003440c40032030b0301003a00700242050600804140c41600034010b207407000d150a1480c01260310160301181c40011121114003da00c0421101002d0881c4507035101c0b11103410f608011b00080254052440407034100f0400c405d0001c0381c41d0031a08413603203038007603490100304410840000c400c03540e95000451001c1803450a001068020b107040b2030710350380d10740c031000b000700800d0b41c032243c104001810015080098040c994460380c02401c641d048070800609081c9441246401e2450660005c483c00e03808460107814048907141603521345940d10300b20362800e1319044c010764031254245403000701408044006800e00012140854141d680001600c03d070561961140d0b0b10a502d80c01080c0c0110551411401c000d200052240342d2683c01c6401401d49a03070303c20320300313800c543c4444003142001001070120000803890840e0b01e041060840498400300e080040040c141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 565242913 1250 565241663 565241683
    0x150a05060102070506090d1103030c030715060914160c06090b06040c0f1407080d0c0807030e0f060a0b03070e04060c03050a1e20040609081b06040b03071e11 69
    0x148001c201b04011550760321204521540d100708500840d00b01080043e04500904007aa001c0f4000000c000d400c02c40460322000100d94409410088a61100740c43e10840b4170640380641d010b01c0326004103008010240060881202034a04001445c40075500d427000e50314401011203c0e40d00c1c4005000840c6001d00039410035000314540b942a0ba545040014041c10f425419080b94400015800082c843c000088859080e603034401030204c1185240300401c242e004440400010340b810340003102158000c40e400100b02c01c0c00c3c004060649849980d1401000c008468903454426140c00180091108090600c918040c100c0000e98210450001d415104010121030300d2038544111000060790b640180302c5030200106001800000c2210300c0d100003d081607000300c0b810f6010900151465000c950581591040d4060790100c070407080c400c203000c1580c0e40e03501d13034080000d01c8140b1014010402444d4810554a08045203c0c142100011020f1840f200480019900300d0007507140303442000b0554603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 565244163 1250 565242913 565242919
    0x102090319060b0906031b0105091c0308010801020f0406180e040507030b130f14010f051501170f041205131212020a110105090d170301180b03070603050702150a050601020705 77
    0x491710301140001d484220000e0180c41e0300d51000445001030b4442c4003070f1042044050610003501d51041d141503041240c0c200101c0002d4070440012800040600940d1044030004141c18100b0341040c50585411440d00c0c050404006244000036240b0f403400c02090045000d607001d02201030550a0030700c0707000002810002612070031210707480083d4102d001c0303840781900700300ea44044507802d0038001c1c00740c441d03022603001090806091100521164000d040a504243c8604002c00c141074003001d0b822800304c8404c00b000d1460000100071414008140c5032004142c5007035450441e8600c40d06a00c008141c114800316044202260704102c442d00590703050752880c1c00100088005075840c0a0640030315200c0904010002c10300c180700f0b48808441000440d4000c00340441d00700311900e00c2c1100c1d04248500c101c0c040c0381070348403900d2000358814500c520101a001c2e000203818080c003640a0000034056908501c00c1640c00c07442d030b13440e441646001307400c20341c8045464184800020b184c07442ca03400c990300c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 565245413 1250 565244163 565244179
    0x30a20060408040e0a0614090402011106190f14040f020d0c080d0f0305040c14030a0c03060c031422140a06060311040605060319060b070510050c040305030304140102090319060b 78
    0x417507c4220207030700300c58600c00c84040309640d84520048869150160710800e4603c00e84c0d0500440800c1d100a400300030016200800922140a9140060300c1003401480d20400d9107201180104400100c2d149071a40003404191460466030743d110440c0314250b1100103035400c10412200c000303600c01008909600149414415410242c59001d841146132141c0c44582085c401c80d16803503241401002c81680d0820803404000d980e9040420180ca000100d0200091400500022a21008801a0051200c02e0001d4001644241c4002c10700406200c1612a50042d20072140c00440c02c221014103548105404503042d40f03980b81c0b4103035903520600f05d94130581c2469011b102d9074580c50305980e4441d8074108030402c01a40501040700404140c0c21100c00c2c1031300010410140b10000403c40c1c4018641c0f00300b00704540c1c1b080d4103000380e40164080201580c00c100003150204182c0f120b5495041045c0000619080e140c0307000a160007403107507050102c0c103e41caa00d6000e001140c425042c5101d800e548a00d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 565246663 1250 565245413 565245419
    0x319030c050715021504030e0d0b1503060717070e0406270b010f0c080c0a03110709180f0c08100903020105130302072304142502030a20060408040e0a06 67
    0x41d49031750002c500e002081591341c0000c0d05161150301a0f60007504080c084400c180498204180c0100040b00c40c1b143d0844900c1c400d844a080c0018103a224501c150b07154031030003040b0038020074a48800380c084800c11030741e000084034a6032035206240080c15401420315503200b0007403a29074400034080c00101660b01c0c100c3c0251050f40c1159042c1103840441c5813400b01c0c04001e141555043c01039410340d81d0341c1e1044d00c1d404001c258000146000c29241041120540d65480d40000c00b5100e07444416a640340d0420711200016610300606004240300350810010103403103800407840e1420312204040b036203444e09801024181c082c41000d42002480540c6040707000c15850280da581003e00c03a0341d68443e09081c14842040707414650740320f0110000c000b44401c95a5120390288050f0a80d4401c0000c002c0c413400c680c5080204010078170100541d00618107000604d081500d41d15601445007403003001e20009a45100c60520003144a03500c6041200d07207560a120886440d07403002010300b071708949400424 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 565247913 1250 565246663 565246667
    0xf07031205010e1906030b0f04170901120e0c130515011e200d0504090b0117061002070801050a0603030201111303110a030f11151204060207020319030c050715 70
    0x240c0d80442d112020610840c00d8101300e500030300e0075a0001d0320800c3c0315424000058080c1e1100707402580650a1078115803600d0260b90b1841c4140500c1601180009902405d410b54035004502516485015650030400748804541000c41c07004082d04030682d124100070f04014590350701d03500c00f54280b134603172402d40103240101c41c40d400c0c1c030641d5000c2c80302c4242c0c201d07001c0581801403011960200d06a0340c6040d0105130244c050342207030143c2005582045042c10165110700d15400f2101b5130840034440a807102c4c4c003404000b00007005c501b81140140400400c46c00000d00031140503a680d000002462455400c0090845407444071909004400704516000c10060558402c10350760070040c0d0380c2038031409200062010754107500c01407070103001440500500030048064008a00b003900d2014103030158007002000761045401c1c03685280b084002140201c1c80c258040c000080c80942290a5072211040c401c0c804482c0a80440010310141c00c07580410905004e18002092110b0070304026030703116540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 565249163 1250 565247913 565247939
    0x1113090209040624170715050306040f060801020f0403020a05010302030c1209151905070503010812070609021206090d1704020904020a0510032c0606010503040609080f0703120501 79
    0x4041c00158860240044c41d1040039036200c52030018111105100741e845e0a42ca01c0c5040c4400c0c0d40c078641c054061b002a9070a07007035000786000c114550350781e40384d50b9070303042008018420442a0310000d561100041034043d0300f4802070260b4035981070700030741b074902d140704008048489421941c109030040c02800b9200780602d080d07407141c034000f10001105544e2a0b1000f03290a08001008424040700801c0c001d484041503061810380003980001c3c09503a903248000d80300c6100a103d4240300d5401a5602c4001c46c0c060300c080c00100d84540c0d00071030b25103650b8001803c01c44125401004640103101440a820300030001d250014045003000032014074004142000807900070000303800703910756a00040442d9280b415000241000514031003070703503581d803030010f0041440707400c0d1050030010464800e050b07030f000714080d011151103a4010565a44c850004460340e41014001315401d0361580c0000c0300058000d4090100b003045400000d0b2585501d0400400d80303081c0000e8900007500e4600184010350310b401c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 565250413 1250 565249163 565249171
    0x307030f0804060227010e0301050603031605071715100e1602011b030b03070e3d290304051b01020c0306090604030f02030a020316110d1113090209 65
    0xa05040750380d6203040290280c822210b141050a520906152a22010701c51046070130400380d030307802c0c40100070b402418221601544c0c060350691081c440220081c1031741e903000c40d280f4402c80540c0c480560b26100300700c1d0041078a080501c5600410040102a0902851207500001840e40c0c0c820051428841d60788481c2c0141180d03641d10441d154514040e4000d4002401190340c00c540750650095807040107004007502101a4424043c4401c0014a01149010940101103c5802440c4a40d88920404001400e0440081a0280d9800c401c0ba00449264207800030800001050620701c103883c01d0407840c00340c0f4180003145920500c00e200c007081000a03400c2000c08180d00d901c03110340c80c1d83d0050f032412000c004103d501d803003201c0801c1640c007008606980514820389030030005015141d0141d0712401080d8035034006034818040e5034402072990340b0081400b801903000340400d580b588042a080e051168017640c01c485001500102e505201d074242a103540104001c00c0080250340c00036040301c90140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 565251663 1250 565250413 565250417
    0x1501230403140715031109101e0302070b0c0705010e03040f030320030715021c021308030307020d030915050708091608072d1d0c040f0b030403020a120216080307030f 73
    0x41c40c80c0c50007111b000304503480ca5000404000200140c030700001d02e604450465240028103c0b031840220714002d0090b1503a00c1c1c2e00041d4408a6a00d00018481e540c0041e041034a80f50340300c4007004044401407000b0405801c1c445950003c08c0c2c11420081d0441940890f107900b0b5100c2140d840360300081c0801612180c9900491080215190080e510068018209490204240d2030441c0b440d01400e039000b44408030900c01460200781c0e5550a15450f408104c41318005a0400302e01040c1c168800e9020b00003681c8103018913409803e100c199001100e8003298003002254890060008640c0708010003c00c20000d00c244940082c00c20700401d44034205807061003440302800480c911200d800380c4107460300f030030201a00c100b4245d0b2032082120380aa007040e4000103541441c04148003406203400c982c183d403030002d1814149481e03c680a0400e5100600c05e50460194560010001c0c1e016000d2003c1e445265009001e002c4880c052004c604c0600e600592440e44108110030003e0b801180801c00c480d094 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 565252913 1250 565251663 565251671
    0x30c1804050718060e090304120b07051c0c080f01030c06180315050f0f090703030c0213050f0702160e06012d0807170f150123040314071503 62
    0x1898142c0c600401600400600c1040c100f10704001050350384440121021490799101507194007892546902c0349005030034040158003211408204500c102503080140e528200e494042d0000b01d1f031910600b5148612103298a9800c0e2800c0d0a6025a00540100001003d002254510b50720858400603c0c4510f0b0180300700721082c00690303404040000011034203c110996400400e1119074010202150452307510801030001c9404a0900c014071842002580004d14050341141c406594005048504271b0380000541d01882104503640a481d00891207c002d21515080201019040202d41c0103580f2104801e030100300b08000f50fa0360780c141c0002c0282007068002da034815111914440030344110900c0d000e48e81c2888004c5a00c03070f109034130410380303a40c40328003007900142d001034100d005131142240650f9040106202143c2c002d031344244014141030401052100030841c0d800614440c0c200111900c021030100700f400246600c0b5007041d201400a0302ea49070401245140c00e402824600c0c00301035607 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 565254163 1250 565252913 565252921
    0x30080907050307030b01060318170f041e06030c020109020609150c120408060709050907031a180609060d0323040306060801020a120515040e0a0f03020d0e030c18 71
    0x91010034060080541500e145985038105144e503444284035510000346820781140c20a04000b41080d521940000000b200c0b007032440050f030190304009010010b01000b0000018038503180b060a211100101c0e000c00121490864050204e07902d0404200c1503905003502c800040e03503000e048074030f002c0c0203e0701d40c105000c0516503c4000d01038009002e1151284910304803000025030080c2049444040850f40c80e9614403200725a00c140c184125500400c10a000c03600240c02a000510745031010a0920000b90b4002e0000d250000c00304010141e10564400b44015030400c1c0034800e5102905444441c0000c00c1ca0760010000d901d52001c080f5511100300030b010350100e03540c049a0045822880902c0740d00e40382c506c0359000754040c07030300400807421406900107080d6040c051548510b000b0400b810180304d210040c44054509a0f004001c1400f40b40c18210026192205042e0020f000c0d038000c11504642d140068090000c0020b4680f0951140b00021800d6540d10500030000454808092061722 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 565255413 1250 565254163 565254181
    0x60c23070c0801020708030a060f0f0b3105040f14040b0702250e060108071209020d080f1b01021c18060929090c0111030f04060c3008 59
    0x1c1c0d540c10410055000051020600107200040c502826100c14204070065a61450212a803014070488010202420041040680d95800b0f1700ca0400c555024141302c42d1054014004048040d0b604418181e0b001010310490800f40300790240858680003c10a400e504881ca40f034034034000308010851003400b00000c001520922101e2240c114104000c00381c0d210300380042400003110b014012a545075100010490341c42120034a002e0510b644403105407001c0ccc81200c2000d03140444041e60001290407035080000ca0780d8005040340c500c41d40c06e50391144c00c244825101d801c2c0013091070b000f070381c018044000b0642542c1c500c0598003018000002d142c07944d40d05400c1c2e60003080c4402510310386ca03080b4640d09210f8480d41d1060740065207807541c1d62418135941c4842c10707070800b41c91080d110340c0524424462540034404402050410000712424100080034409880d441a04500c00007000710130040d0401c04a52a600c0c41011003000001d00d0b40341403120900e910300b4a100340002c00505001180309a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 565256663 1250 565255413 565255433
    0xb07050304030f1a040b06011e0c03111509060114370b1b06130f110d080307031505011b0b0a0b2701060801030c0314011413060c2307 59
    0x50710034100b40d13965180c241065034641000301d60f150302082401e00305101d00c01080001d54503403181a20751a0318140c05403001c50310301f00c0462043c4400d1050510308030756450620241c0740320340f03201e40040042d13604103610741c19092004545c442c040d040160003101109520b05082061140200185c02c022030705c03090800811520703600409043c20002560f40014640342a442411243d14044400c9a1079900c580b5840315505400604940c440e45511000600f0b6600006094030008019118003845034440500f284d005882e03490101b5516603040c02103540342c109880040609080c03a4542c004009003030700301800c2000f00103084181d0400050304d4040c40d0760013980001c0010384600004050240328814001820100c41d0201c512500006100c51280c0c040c241600d0340b0030f405040062440ea112411071030310f1403003c5415500c809131824070b0720740c2c01c1c100da00c24441054000242c02990800c1812510340e404514200612040007600c0d14507c000d40c100d0302030503100010703520a61070074205002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 565257913 1250 565256663 565256693
    0x160302060f0c10091407050f06430b07020307150f1113030b060d1a0910091a0f0f010b1602030a060b0a0b1e0315030a1b0b07050304030f 60
    0x100b0324013008401408480d19011003802a904100c13200551038100300207109400f2100306500c990f08005c5000010105008501c900343d602d80b00428130f00c51040005044203141c1c20003e21068464041010b100700051550f030030065500146140102a86803540247c0905a5400e4141d8980c400c04c58100300c80c1c0d007c8900c03107200b07014550b1219500486003a50f0001c80c8030a461401003080480c00e549001580205265481040d2071103500c1c070340c0c01c814500c04c00200496118010f0300b2150800b45414090854040e10030500862a403500f00c0d24810b0201c000b83c420f00d020b421400c02c1203803c2c07080710102d1b03065070801d078181750700c413440380123000c0c00d90480640094040c014120450100121038005249954048401d22031070fa44801e00f081e036034020200c1c6103640d00e40c0c0c01840403a60600800654002c00400c8440058000e4000424039202c2c0c4035808546c8054226000424031402c00e910344040c000700140c1600e0441c80382ca0341592401503020181a00c5101e101210030886641401040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 565259163 1250 565257913 565257943
    0x702030a200909100605040216020405130503070b0415050411130f14040c081b090a0204030807150e011802100512070f0305010905010501120b0310020f070203160302060f0c 76
    0xb90320b00b104032079803549090a00c072803840307041110200d0185031600a64034616a004802c141085681d000c03c00981710141140c4002103602c130358040400c409100900d20350b402001c100d103603810946098400720b000240d001c400245043c041c0400910300c441d0700700010008450610501401104140040010f4070030340e0b030b03071524010311140d000d412841e94501c140d00a000900b92541d564103c603484282c400020106103040c21600101490b141c207010f90494181e200c010305098a85e03842c50f24582c007942e010b0b120340661500c00e40c01c1800b980102c0500014410081c0032035507007103c54545460003550000e01c2031503041450b91216106100f643c3d1100304441d803590361810715600140580540e2b41c0110002401e08001240824081c0540341c12510180e4512012400c0303030180c200204403035203501c1e90502034003080105814050016000d100b00c040c8005685400c58030400d45005084288400f2070704401404002603a01c104c299444600140c41c13880d80c034110141c1190404540b00003070300c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 565260413 1250 565259163 565259179
    0xa05041404061119020105041a010e01060c050a14030d0e1c050c10050414060c0f0405010509030708011a0a05040b01020a03180302090708040b060f15070222050f0106050702030a20 79
    0x4d00345505400c101d00682c090184405a00c07030048800112a0090141032928a405c0c001082000d204841c2400303118001d0081d2503040b9803955076144220582260400e10340c3c404035500141644622a400c150b1030344400511803503044c102c0351581e0700d86140240d41404404541b081144005016541c2080c0c45030700100540c3c5020318206203d10070444160392103108a0780081c4c00d4000d44000ca84840c031441e6511404d01d4900001151a680882c00064043c0103952001988141c00d004040e455403503800c0144074480c404091164040e030541c000c2d842207041a01d0b0041d20b0b42c02103058181d141d0146400e00e0000c02044000b034200140343d0009421100600802400076440702140e40624031070100c00b8001d40b038840070450311590010700c40350f0180700010021840d128107401004514805490a0180c403160420b90b6080c68584200d048815128030030080340300b0b21004018094070981c00c1840c181443e64000c60380e00c02030404020700310350701c41c004540381a49115010b620540028140c0b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 565261663 1250 565260413 565260457
    0xa0206040314090306010b09060d0f0606020f120301060323010e07090504090201120c020709060308040609050616020f180405010c030e0d120b060906040906050a050414040611 77
    0x96681508a905800058600040800d00504a0211500b072640140104072a9081049040e11b90303024030813140d03005a04110305122901d0714003c00500a070715590010322149418000303414000311020702507294019140349452a40640280e9041d1182840c0029880c110007018001d03107c001d5900503494240b4100026215081000c214031844260f5200d03158540d07600c041c04159902410001d000c14a040040b803c0d05009500c040b0402d0110700c1112005603031a4492030071038940d42c00a640c0350b80001820b11096800001702d8001b00b0381512b08902c0c007400302c44020b62075181d44000a1056007111708540b4180d890030701c4c06010140c0000300c00c0710b41c105072406500a11000840740302003818024983c0c682240401c070240c5c10b45064036002c2c0c9020151030b00c00002c203040c20032154024401e0000c072110745c0f948000303000500b81100c00051314605000c20805e6090740d9a101c2841281000c01c016004e950044c2e2594020380d12890100307076a01c0c41c90301c40400380a00c4121110000d0910390300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 565262913 1250 565261663 565261667
    0x60b0c010b0414071d0406091d16060903060c051c020c0f010b031002070f050d110616050a0e0d140106030317060a1e0e07030203011401030c02061501030b03030a 71
    0x14800309821a030800c00500c0b8031040f107403402030485000000c076601c40440154449107540c080c030268070007000002c070300d900c80010300c08070307201201805098583d4500f5801030840c20081080780e20380c0d05461407001032601500402800c44c0c1d001c02000c00361224403e02000307025000b40c8c1d50844050354800c284400b0002e00300d000b500070842d051614402c004540e00c5210041c820a0410354018010b07008074541064001c010758440700007110305040355026000070544c240075094090110f41e031458000940c8003201844e200c1c020381180a003240c2e10280c401d505402c0b108503241c1865034100600345d154901c001030b9061709001000340480e094643c10900106041d4042c0c0b0545e0321903114020314802d409168410b8210840b0303115080100640c041c840c100302c07903820324109500c55500380d01403034540b800c004594a0a42d202c074003113a0044014002f20100345003c4111110030301e010007880302c14030746c0250307581c60151410610a1310141c1d240042c0e44a50000304c5103503005421640c1c0c0341130780080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 565264163 1250 565262913 565262921
    0xb09010f1a1e0d1a060a030e070f030b040b09060f060915031e12130e0606040306020a02070501030b030a051f1d0a2901090209040b0907020a020a09020a02070e0a060b0c01 75
    0xc028034940c506035000d009111440e00b00d04d10305102504c114104800d5403001c7d002003801c103441120038070525100182150520200384044c40c41010103242c141454640300c2e5169401a0100741c3d16040701003081100d85100708682e90200301203900305182d8403980c01c00520004541072060701030003614418a0341c1d0030f9100088410b0340d02d00e0210b69110002607000c0d00107000322805080882c0d0340386410462a00d003014000d40000740141514032b440c1d07aa540d140102da10000345400941c00c055010446982c241c8102c814000c01580540100700c2c0996840c1c1d125000d4207011100700c12034100344004058a54461500220308018490070396600454a6070380c2c2140c000f045801c0c1c075221521a41c503004c2000c207100c4130b0705140b88081c12a400d240c203010284d085428450740182d81c07030510140d5a07030b440c65490b0040e0f50b190090584000140180030302082c7d01d8018140302401040803800c501d0780000c11008448064454907995254100510040e200a5010f02c021103404141182000c50645c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 565265413 1250 565264163 565264177
    0x70807020105281e050d0c030e1504060c0c020f010c110604080a050c04180b15060714061b04121a0c220302060a0804031817010b09010f1a1e 62
    0x5070352110341c25000a80480251314204c4500082c810700c090215041c2d580c0020083d024a1306000c00c1902d0080f19082c941b100c01c01075205000d24010920041c0710342403140c8035511a05161003c1440b40580209100c41c0b54181903904000c49400d4602c00d1254006030902d50b814024045559140e440080c95a10141e008080d5000d0080c0350405001c1d1a2911134503020864441a0514104843c0c5800c1000e400042c051400c1c7c4803d101c954a190fa2403800600005208a20090405c4414074078030b4501f600c0140400705c4404484145280c4800c80c1045d141105c00c100c22103e0000c0b018640b031542140c0c44007154484014080510102e003001c0d10150401c640c0c8003110b21904440009840c1001a0611010b0341214040101541c0d07540300d0f414196002c6c0c041d003481080c0605464000703070741020b0f5a200041c058049809141000000e000e0750020a030304441024807541042c0c842090f02d1654880d49034803854480b282210494a1000c0c1c80041c02d241203a007045505203003078014983d100d50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 565266663 1250 565265413 565265417
    0x305010203011d010906030f0f0507050d080d0516090519090504110928051314060601121109121002031015020319080c0d02160215040b07080702010528 67
    0x10f0010407a03548510501040360307000741300f01c1d8042c1c01c56250300c0001c00c85180191000d008071880410141c8074001c6a01c03a00307100780c1490740c0d84c600c03107100f4104403100501300d001038100c40641c0305d0003e0751104021080d61800c8840b040c6000c4a40d40390700f00020680e01141025040104200510810315040012002c0035034425009a6803050301042048a0a004110040100403203003000c0300c80380e000a81c4130390041031648250b00c075502c2e080c8082070b1450b041112603000c20208001941e0003002c00410520820060088103e1500e003e603150052424150007010010810085c034041001900c0745512686021941c0c0d0402c0250540c1e9444140180c100b0910100c020102461001045034040c00b80b90040c4050280e00007421180260302920341e45080d101403007441040c0300281700802e0130203041203000d41e40910b9841403000c03030041540c3c0d1035008503091108015600e865000c541c413182d403240c009692003015200603100c50151020400801d40c810024400b01e10255021a650500b59 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 565267913 1250 565266663 565266719
    0x2010b0a0b220303020d0507020114070516081207080307030b1e010f140307110f0d030501080c0d201311070311010204060c14010f020a020601060e0906010e0d050106030501020301 79
    0x180005203440b60759210080c01a4416070682444a11503400340210074814074203041074000700f00e00000d0542200f1000e0358141c100b1507580d1b00c100c0d0350070240c50040030b00d038000d040c40e011200030f030010b03e0050040140246d1400000207a1592207036105268001005110700c0100c0340709280203c0d101c80e0200300c1404a141501d8540341c10f4080c0a05174048002e010035503165a4400b60200d0702c40e0f031090070840140c41035a081a2100c40140310380c90304407006a90010701507150203a0186807081d5508140c5c05040b02c8c1c0c0180b0045118903020440d4440540c3e100398070210900301154101d4004903031007003410f1500d074440d21400174000040c070180b0b000359030b01001004612109400c034400e80c4100390202e40d900850000258405042001500710300c000020810050368000e400e90784400741e9100181c001000612115400111004100d070041c1c0d0302200614041001030300800b80c091060380300d02403a144401c10404250403003405568403000954895968500104030581c0f00196400c1385c00f90 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 565269163 1250 565267913 565267957
    0x1104020702090103020f0103061a120606030610082203120f050c09010f021e010b12010c090b03180a05060105010914030c060c150712052202040c02010b0a0b 69
    0x50003560502600100b05084603480c6a00300100054400081410305440b41d0001850050442c00e00c00c00600130306540765540f200d40d03075101500308020601ca106000500512135a0780314100c074071503d0b000c6803c10382d13219240d030b140710500c44c2c6103d51142ca9503041521543d080503488400352506c0c0b13200030003d00c014a14007000d001694021510260f0410090040384c000750f01c43d5410a4501f0140e00588881400b401040550703032003020b02d80711543c0c0d195242c021880c1410545011a40d0801008000f17200d410040241190385611800750450804408075071a042c10f98078000c0310440308012a0842441468444c0c1c440d4824405e140c040f0b0904600001e0a903800565030344500c5008015154852400042000c2a00b10340340c4080640308032588a48401403800d115401008a0f403140d01c0c1d09009d003110a0107454004250005241c039100f40c1c500b140e036101c650000c12950446020a5041c0d40c47c2c012801006102d5005070311483c400c07800160010060001e140f908440200c01540d010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 565270413 1250 565269163 565269169
    0x160305032a24010e07020c010305060a0515030103020306011a040e060f030a03020d09080d0804120e12010e0607110a0209040201110d1110051e0a2c070f061407081e0711 74
    0x4e421290000035810031700710745006610030b42c002c2c0d41c8040010044a881912800464980d200c8030b0515211040c000006106501d02001400e0043c1600d5401c07d240202c25144810540510b1062031b220000d030f0400700c2d0740d40d03459031108801c820000e02142d0b14013442c0e08009644800a200302d00118278001400306840f03902285c1240100ca994942200549076552418034200034001900308010170800c480e03c060751541903c00d01049408004505201c14601c810305229001d80b044050090700e802605103184041160720f0b0064044407000c1455649000503a6040030680408045004040341800c2c002e030020141c0c14451440f004444042c1f50036200542101c40a503142d03941030420b1510702403084c4400c44244d600548604011505001c90342810101600603c02104030420410818140741da00300042401450b40e01b140303c240903d004c40203440c0c0c3c1200890005201400a00d02060014201c00c4031051b21074080d40e800044060001c0c084ae0790012031040ba446142d0001d200790600d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 565271663 1250 565270413 565270439
    0xa06050406050f0306040204120308040501230a0f0905010213060207052407030207150c15060b090f0f1023180126040c0503160305032a2401 62
    0x50072034940a1400200d014215081d0300020b01071a03002d40c0030040810418001c00d11090500d120341c0b2001c0340b17800e1910b0f22038291500d2400000d001d00a000b41a800080c4285803550865100480080c103412010134010190950100181056000249107100b4291042d0180c00f1100907a09580f011a1030780200841d1207003e100003c1501000d40c0300c2e08040c062900201001c501c640102d40446039101d610f00b580141f42948600425410b110a40910007992140a5240034422040158034203120703100030320f0302441801500881900c22415819100c2070354031511003000030321840010742017040082a0760002c043c3c41d04031041c1d500114042b042c0b030300192840401d4540302c0b458411103540045900c503ca12441d0148484140a4150304403000385115010f207014030000c62405081c04149880c2000a00611721445002c500400106001009548240081180002c446880000121501503402108428074010042200f0080c506040940c20a46540e51a080c80c0c1e80d0b1030107440402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 565272913 1250 565271663 565271669
    0x915010e0102030c030702040e030409090c0e010501020c01020a060c050708041514030709030219170705040605010c08040e0901060b0406020109020414070816020712031701090513120c0206070807020a060504 91
    0x961701c18400c090052a00d038015200030080030701241c2c24280d441d200f81d8140e46040b0340c140e50352912400c09012107050b61031058003400c0203000800300448281e000135074420106402030110f5503034030701400c0220320401c11078520a8010640940321925081c1c11a11008036641c100086030800312501701e13040040040d6031180d01a0340340c54207440e26540034060b1002d42e0420b0f19a4040d40200046141d10704c540b002034484480030000c00515080109020498020790401418400002000000245000115010f8583c08030f484411a210310544502403c01500020318040300030401280352a0305503c4801d0f614003c4409000008207076800414810080d5044000140d41d6000904640c4150007043d950300c02d1441181e400325990181c1c02c5068080510440c0050b02c0780541c01c5521410581150250420f51001c00450410340084100d40b440c3c00c400030b2030309050b0088420401d004071030102440d6000741031550340359101c0c51301d042d081c5d1021404910880c003040d00030803a00c0c411016101a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 565274163 1250 565272913 565272937
    0x8010b041103010303051c060332070501051305030f0a0b06041505010c1a1501020714010c0f030c30020a080f09041e1e111c0207020915010e010203 65
    0x3541c0d08546080b03e40d40c0c000c00c401d0b013207c1010785014540003a6132007848010b5024040340a101e21240c051440c80c3c4501815454080b5900a9500c81c0300c600070515000b12002400c00075070b078180074004032041c009143e12140c0d150184001d4a9651035020a003554190720903a090314103644d900d4100021590300100340740740401020014041940a0f1048020150181041805581c914003060055500132601c04d8150742c0082c070380c41031558042103010040d10281d004c0c5100100c5480000380812400d6902501c9141c0003c00e02040c14090001b000740a0f03080346507041005d8103101a1001c900c01e00706d01c5018880c00c11112460503201140404031303070360320071542842e21040389004182230b00301d0022594002c1e41ca242400f80300858025001e09000004d0010a02a580e40c110107011600501d242d040d103401c264444075242010400c803032024121898401c40034501c1e09034440203001759074000350880c0d007440034081c090b2070260f0444200a4241c0e1100c0080200f9001203841380600748018030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 565275413 1250 565274163 565274167
    0x5130605070204091209060e0303040510050901120c020c15030f0f06210c091003080a08040c08030c0f010f1802100e130e011119080603120403030908010b0411 70
    0x1000610480c010110039000070000b08080360551500644080d02c010000c01285d105081005070a4120b00c280001180c12400755050a02d00000310b07004003c46403ca4003000b0700003130915910380c0900190316080046403010450074586010283d500c40c9106119803081d1070382c010880450030044104c0380b082d40003000c4031b0b226848415110a030004c020781115030100406d03d0300c0000c0c040ca250904045903614000340980c45444003444411036000d08400f040401c0b078581440071580c044200c400825030361900c049195103e00300001520070325000007845000c0000c010080010000395996541d500100822041c0c40540c41e1104690448450840d500421000e50003d80f50201c40d43c2c44150b8070342000f980d4100303c00700085644074600f410710060f695520083c1040c0400b44540710009040c040004d141500f41c4007103800c18140e0018100c200b202d42c100040c4c9a407400d10a01c0003003403294410b00e848540303d15025149106034002c0e0400c940c40c003425060701d4031781801801002900c0c000384034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 565276663 1250 565275413 565275419
    0x50a0e010602031603050c010c08060901080601061b03022112010902180121020f031f0315050601030908031003050609012a090f0b0702090f2511030406020706020d0513 74
    0x80c100300000c6011703404c1c81424000e0008a001c02c0c01505405100c60303039501c04501c6c001d406c100f044032040c0c01c201a113031b0050005004c50f94100c4400b100c00c40c41c40ca40a060114035140c00c0707141c540000c050405200d00751001c003a100c40000e01516a4be103007004803529507a22070f1201001c0340034020003030210140c000142e000c0d80d400780507501c016082c00c203a0140e440382d00070850010b0344d01c40001d42074852400801c201100c44100c0140003240c941000c1208101c0c595160300507d900702907462504560303528086003440c0e02940c080310039241e001d841c05850b0310b0260160008008580b00550301402080002034a60b841072040d4a00304000401000b0003103000e0100c0503460345600b0200091082c331350404603480507103249400003000c029241c5035542039188180813242c0d5002e050400380074800d6080c400040a003051348650398130340c1f42c140c41001110365400c07201d250307199110443e107003c0010045241039010412009607891602195680f54a2040c110f5403485000b030320440122030302c80d042c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 565277913 1250 565276663 565276687
    0xe010e0c01051e0a0503040510020f0403030e04021605010516030501050901150215010f050a0605091f030204170f0d0203160b06040e0d020a0201120204031104180f0606050a0e01060203 81
    0x18104207100004602441e203c01c1e12648440d62040700d484020410110412003000420400004a007c000e181036041c0040b491200c032142c0a2400b00605200300c40d210503409844541c142ca07248150b001c8200c1149800e802e0050003030006039034507483c01601c200c0340b2031001d010340074190407908003601c01c13001c0c2d0303191003503001400d45074500c02c00460040b1080501c55111030300d503080c064441c182d141013040345840d0400100300c5c2c0551000d014440c0078082c250481c0d40d6030782881140c20035883c0d40b50010143c2d100860081c0300d0b0341c00c10740b00540d1448400001c5200054815401c0c6401d201300c1c0e800c1c40c50014266980c0c000d0b01030300c02880d2010001800010300c07841d030071030f007001c0003800115443c02050245030800c88019048401a030040b5044d0040d980d1203584031003500303004002186402d0650301c0c0e100c1c1200d10b10603154021031f00d4001c145295200e20292255158201c5c12000b51484039280c030b1005020b261080d1442581c50301004103607583c030080c030b040c121034058008501d81840c039002cae = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 565279163 1250 565277913 565277917
    0x709090506121c02031603020f010c110c010e12031201030c05090112081e0720091012020d08040f0602010501080105061c0c0503120d06090908030c16020a060302030a0e010e0c0105 79
    0x8201c110300040c000c00f106d080d110b1b050929424402e8000c1d04042c00804030301421210f885030a0740070040103000e0070520203404903140c03448000070b02e4001c1661404502082c01d5000e910807015807407200043e104d80025500c000941030340c0c03041d46070120154ad04d0082190314042800340c42820700070a0300c00c1e0000388160000380702c200c81c0269040e00b03502d50103500082641240000303840c4d903d01c180b43c140d240d420303a2400b40300c0004112040003607410030b02228481040075015010301594010320010075513665030040001164011030081c2c1d2151500702802580e022071060202540c01c01c000450724002c1802020321402000e0310810042000c48640310181d01c1c0b02c0c2d01900c0c04c0b1030710100411a901e05004d540e1074012a61001a030303485030109146e00b1100c46500003507515182240300800201e0950841c1d400403c1c69806a03126900318014851010200c07000030f500802c25600000c1150301034002c0d51280005020400031050042c01c4182a61080040c2180d40e8100840e060002d44c01100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 565280413 1250 565279163 565279213
    0x8040b21010b0702040b01031e15050a06020c09070201060308120c070f12090506070b07110708070801090614092109030318150403081207030212070909050612 70
    0x4560903441803808490305500a821902541c0700024032203081d030074a409462a040740a00e4100121b44140c0c0f0405009190141105d00b415110003480001006011001000d85402010180d00c2650380e5030295940c0c582c83d4625005021400c00a000d950062207030700120798002c4081490f1001c040c441ca02c40030402080040c00250078845c280100303141d074074070300d50702403060002004158440e44003422294003544068071409040003104009070001e41c00d190030521509000049034090311304581094201d821945503841400400140e007801500035030b114601034401000710820854000c440020100ca00c0041c43d485820161171006c03002e40a040c1e200c00c2401e2003410451000c0001c2c1c2990f00c8803450456a800c2c001e00c800d031510b0a002d46c0c041002480400e42c2c41e0a255607100d041a000d000d82004150078200001103d05009030120344096a0060000c012441c0c0010302410428150050038001e9103804001440c50404500d40c140d100c1800d001032448400e0303000d00122083d4161 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 565281663 1250 565280413 565280437
    0xe0319170f2512030905010e0d0c06023103110103020405030c15041205061014130b0604030609080c0c060f070f06021b0f1c0804021c1e02040e01020708040b 69
    0x882100302250341106240c00645450f1303001700b019050341c18890b00359000c0e80d03203c0c8516013100002a5010303402203925204507070310400150b00ca6481000070b2183e102000445151000f9007150807049600f00003100c000d4910801a0b490f0704401003004400324051400307195015400740c1c040c03c409290400040c5803181c110140d061419803500e800d000c40b151032200444040d030000041c00400c6003051480c5000e80750054410680141140014100c10032680c030b02c514084d90b41010100b143c0760942210051900070000b44070305405450071000b03a0348400780c824400e004005074113003d4680002120020718503094900d003849241e0301d42c0c101c3c0601d404000c0394059420402d402c010f40500203948044109a00944805400c0d43c400f07074205092048104900036940b01c000800d550005c01da250032036015100c40e4a80810500c1004100091000241ca00405448010a6003041c10350411070203100303a4007440782100301c550a03420b134010440f00500680c030a00007441325241c250301406c4480d22407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 565282913 1250 565281663 565281727
    0x12030c050c061b060a2d0612030801050f150d110705122224110115060207081f0b010203070812040c05100e100e0319170f 54
    0x1c03070004800364026420000d000003030030143e95520310b0502c040381c1d1007081950140003580e0300620030004503404000f1040112080002c440002e00c140d400000501050710b890380d409151414050500002486218801c0442d810381c00b001c2d041211106c0300c11240641d200c1d0601e4252131100c006814804105c501c614030600649000c240d080280c5804050b400781001c0d40d458a064601c0f180d060181025041d10340c41c2c0b182040310301c480142d4091131345184640010044108441102c0c6902034a178404010f600b80b41c032003100c501c0c02d8240041120001d40071a807180341d584840ca5214581440f00080000b55002c000541c02a240c2043c11082030500c1540d00d001155912050b281e0090744502c00c40360101300402003001440da8041020306070031510601d41c1040518003c1400e00010b050b54045c00c1d01c01c1081001c2c41c014000352140b59002029a20710100d044d4032402d0148841c00242c405d0f000c0d0003910b4546031011022111040e8000f10b1940ca42a844003851440103980c58113865280ca02e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 565284163 1250 565282913 565282933
    0x80309090402100e090a0203100501020f0a02060306011710140d08041e15021b01030204050f01030f020f18211e03040b040e0702070501050f0a0c020a050405090a0312050112030c05 79
    0xa00051a8451b0b40c00400041c1c0303d0070110103884076a18141c001c02e06550040703c8034240408000f555000c2180d0454104c0d5a0750b0311040100d031541c00d44001082018800c0b800d2208600441a888040d162450004800810304c0810800c0f03a90504101800b407150400081c4500f031541c881c040308a02003100d400c0fa0840d50307146080222482c504a220040e045035444001ca440e145a122509080c01d180941c109410240003e1441e0402039000b41815510220404810b4041d019104047d060061307481c0c80b01e1200c080b00060b002d130400401e109400320004016030304411301d0700e080042d0b40440200140e4094060800b0869507084080344144014030000450002c3c00008001420b17507103c14104a050440c000f030314020150700321074148281400201100012041070301d0381210742c1e140c01030070900c960000c1090041341ea04501d4215040c441000140d0310b00180d0490b80350300c03d94070600d45800c0c42c050a01100e100b1300480c95096020f0f1f130444042441200c4c5510900c0c025801d0300d440c014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 565285413 1250 565284163 565284169
    0xc0f0203030f12070206070f200c150901030b0904081b120403030c030e0a06050f0d021c02090a12020102030306040e100911130510060c080403080307030f06080309090402100e 77
    0x30180c068200b8030304041044d003a42c1480101e4002c07e160912109035882c09501500511b918040905008031540a0560221003085000c1c583d040161400c1c19000244000300180d9020107040341c0400e080c0800c100050821240c81c2d4411500700305482d0400811403c5a034080302054421b000364803508d885d84021844d07010003040214429150000d141d950f03071038041e1064061500c21407059001900401c2820b4000045600380c00002c0c0101e075684a00380031100c024011203d1106141881c501062002003543e0b00801d140102100d01b502d54654039460350741a002d8048000f0b005800c10300104d00d59040c0b42d040f60580c140180c0503a0761003030501e0840030440c0d80e05002528070400b0840340070b9480c02c1000ba00da01c1a800e07030500744075619240f04103a15008481c400c450400a03c4415030007881410300035100035551294545a59090884e8001c000d0719480c40e00c01811031411000003240440003081712104078029218030050b80d115002c0104401200c039020f0144140e101c020140d0359 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 565286663 1250 565285413 565285417
    0x3110907020a14060a0f021201030b0603031605010606020601050a0f090f0b090709140409050a0803040311031902070f0303020c1e0d1a01080f060408030c120112060510060c0f0203030f 81
    0x10f040c0200401c00e62414801c03d000303440303031050340001031441001409109201c1c51520381c19a0f8002962003010f46501000c43e180d885041c000d1400318107009569410001c06403c40d00460b5a40d41c03c50b0601d98940c0100148040c80e4030440340342a80050f0b0401802050b0380045920b14416040064a0840c58000c600a090704556580010321400c1c4207100440e60400502d10455042d82c041040c65070a50b1400e0713030784907841805080428040009010180b103505500d00441300c1605994503150190800304c064281c1c00d020030b002d4003896802080c0c1c80014262001103076050f40c010001c58940005100c8818040d001030219030240d5548040161038021000441c5881007041c07905004220484814003207044e0811906ea13088224441c800b0300340041c0250300660000381c5580e50341c46840c50351011348030740913141030013003060300002071100c01081820403114003c0c48180107a9448858440c4007012600914011a800d026954003251a07500e003040e4091010b81164130b480910144003501d9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 565287769 1106 565286663 565286693
    0x702091306091a07030510180b031f0b03061b0f040306060b2205100c080408070b27030d050703030b09070306060905010903110907020a 60
    0xd19010415540305561210042101c0c1100d4501000d0004110701c144a50100341c1002500041c042e004807842682420340100080c0d00300140c520a0300b00010b142c168807030340d40c8061591134170304004010b040980c050548000750301950300c281c10340301810f10090180d0030040511400d50074840b034092400300b942496a0700c542c2951180c890300c2c00b50758800f070542410f2540c00a4901c04040040409410402002c08040b036503211007400514240303c0da039000313045109446506440b071408040c04910a1104514059558942c40e02d800c0032030300400305465000030420400c002d0300060003003104440c400303048196511030000e40c13660500c140301000d02800040b04010035200c3d6014107a4035000920300c02c00c80c01c1c070240040060403140280c0000c030340c600700082080c0d809090250200c0e039000c01c0141d40700c810041842010300703001c0c0c40d80c0c00754454420900005511400c205580c = true := by decide +kernel

theorem cover : BRFrame.Cov 565107913 565287769 := by
  have h0 := BRFrame.cov_init 565107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 565107913 ≤ n) (h2 : n < 565287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
