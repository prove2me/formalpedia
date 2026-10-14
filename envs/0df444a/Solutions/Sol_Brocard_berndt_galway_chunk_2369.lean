-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2369
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:30:29.145516+00:00
-- url     : https://prove2.me/submissions/1142026e-e6f0-43d0-94b9-440bce00b01b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 425899280 ≤ n < 426079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 425900530 1250 425899280 425899319
    0x31e010305060f060a0807090506100e09400615060c02090903250309290a02100c120e0c03060f092104080d03091e0807140d0207 57
    0x640140c3d21850000207840001812003940f25081c0c100c0030402c3e90041066900624041801041a0038100c0520034018072034100c00003040140b6500c1c95030750b11010f09094101f140c1c178426129490320a025912540c8280c1a015219030700815a050020121980c0150a90080390100140c000e50348603030300301414038819140490030a01d50f840c094505142c4c82d55114890109491501c1d9440740c040032040802d41e5520804100c0d40c07400b600307065211041c07202070890340005400080011002a00d4042c0c84201d12810400000e143c4603102e209004e0404080050001840071104190001e401d020f070701c2150003442864011829001440000d80d03018840c405001760229464100000131030303540080100005204440c10135980f02c03140c1240c1810025074042903500c170390600740110708259801c4050b0b03040500300260360000c180072145150000400d24403000350350804e8580442940148000030b884010510003618502c0350110703d030000b058059003070350513851715081c9202400d0b0f080c500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 425901780 1250 425900530 425900533
    0x509010504030e3006090607020f060a090609020a0f0503011808030f090a080309152d10030b010e0604051602030a0305060f0306090c1905060f03070905120102031e010305 75
    0x1a00b1102c0c1c01e282c260106404440403c00b41c041460340600c050020b550308001c4120740c0080304100210074144525030b0080000d10141446403444a001da2f0f460601030300c00105603581d82d01103003c202455105002d407540c09040685415a01c8008249898a80c4a640c0c025420044032714890400300c520400c0e0316900c20f41c40c46c10f44d00d44070401c2401c00c4008040c1c030828801e0070045000311765440003442c410003002009040c90130301018204260480079224141c0056051900e0088141742c0503035048403c805101401660346020750309003901d8042c2c0c405004801a0400481c40140419159109000030389060180c4d07120a141074100a12401c4c0c1500140c00c24800e509640f44650001c40d04200024110141c01c1a5030001a0030182d00f178980320700650000001904a04054a411801894409031010f0709490000416454441c0b90909054444c0000c00981078500982710440903240141840c3d50844a65105500030b60042d241c2c800300020007a6101c1840c0350503072805050340d070b1000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 425903030 1250 425901780 425901797
    0x90206070605060a03021c02042a111207060603020406080d050d0513170c01050903090618030115080d08060627040e01051302011206061707120606030f050901050403 73
    0x1c840e2001014083e002c543d00001441c0700002503642c000c9900c00681e6031005103a18200c1a104000450300e803050b001480d00420301910400c1042d4641421349194a82071900e42d400d034011303080d420314904004584000700c01050040601c01d0a5100d03500703036442075404102c3d05d5142e0800c6590b41c0c280720800e000080c1c04015064007140c0ca038122680203030300300c1103032042904c0f1551516001e03001c105500b070301c800c00441c860400c1503003402180d801484403400b4500e480000c0c0080369042c0705a99501d90361401d0b0b0310345060f054a00754890318540c00c440c54200300098031011000d403030b0440703042c1e07600018488201141840c41c00e44101e4500c40300b64100342c0e1309601d95003a0b00d80302c1007820700d14a41c401d55402e00b10800903420700429124201e00204040c50b60000d20015000c03100308040f100f00c4a01d050700612003140c109040c52104100b00b00c490302c940e92191001c540e0552201c045450240c01c00900107422500b6811040044610798400c0c0b0442d502e42c1d002500700c2d8011203001d000079140a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 425904280 1250 425903030 425903033
    0x3d0203010e060d06060b0318010b010e030615150304030f0f05031009050718030c05030d08040b0a05060d0606031a06040b03070311060408010e060a112701110d0e010306060309020607 80
    0x51a086101c504c00c1e980855150385c2d540d040e60182d00120b98601a07801e40030f071481c905030000e1095440641c0242031003418045184080fa58a04005290800084103005400200d549240d01b00d81c1d001d1001480c3c5689141c50704d001080c2c0100300e1008408551007004048034030f801001901d1058205408010b6520700d040007800c060140030748060305002d401e1901e1074406003103418003005140101413810701c2920308018545032005201e044001c00282e00e0501000075200d09466420810450000c2040d40700c0c1d10010b105403c004070010a45071030314170000104240c8400e20358007000000c0c42c200784c0c0e46c2c034501804140d80c05107280c2035042d04000301c2400011030084a050350440d02402c0366050a8591803154211080b2200f006850781c049010842d59000038015041141c0306141350a040c03035061840c2c0d00c4441260b01c221141160200c04e2552130764440c190194103100603108030380c2820aa0300002e041c5060210030b107800641000d8010510a010707010b000c002c143c0c080e021602c1d04605 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 425905530 1250 425904280 425904289
    0x50c03070b1621211404080a091706011a16170d020d05060316230102010f020301060e09101a0c070510021b090c03040605093d0203010e06 61
    0x60494603404420030341d00043d8a07000f5141c0f4010502d8998020800b9040d05a402a103d8220100400c41c2041620942c0b1041a00b03040e03000707940541c04548036081c01c4015525a14203801402003804091804461b106001400364101d0f181d11100c0c007240b20308045c4005581c0b03e04807102004243c603600c00400100f0741520090b00d0a07080180703d082200d005450b4003680e00000d4042e1555032240d00784805854107200700b200c04140300316006100d07840c0c5400c4180f5410110005500002c4114013003a941c2d000390008580030074038180c115501c0d038403544040c1c0b44040b003100c2c8a00841d8060009903802210304030f0308040c0c031002600b0810340c1a0900c0342c110f090303002e440442e20a000d810400900742d00d40a00209502c2c1c1d99030080c2c0721603c40c1c500100c80c054001d15685114041c0c00b401d100158152104507134000303070084404031b120303503511480c1d926001108150810320070b0640d580074501407030551280c028045051030305088a034111043c009a0000780220700c0780038000380100300d040c13a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 425906780 1250 425905530 425905567
    0x3040506070f061d16050406050a1503060302040f020a02060f10090e0a050f010b240f0d0b090c0d1503020a12021503010b0405010e030a03080408030c091c050c03070b 73
    0x1182002041612130514040c82040e002d21040c61250302003079140505040441e8104082e001c1a5410401c26103020001200d40e030461142090090404e61038403078480c4290098000f564003d04244210700d03200340701100944c410800f180040c0620404102e41503001c801c40c9005a19040c408002d040c24030000070028000107021002d00d01c10040301c00c0000d2424002440203118440002032400d035414184a000070aa405e003884401406540d00c2240c0c43c03180965444c2c407030034140c1907111590114554002c0c0004001658821380940402414501c140c00030280041003400034403141d07501243c0d105080c4510700001b5407206d083d600501a2242101e846e80940d0300003801e04009070001250b002840e0700c2a0081c10702600006410b00003540c00000e0310001010903801041080c0968800802e0904041d0000307051140000114108400750429100180b20092150380280101d8120101100e802d4004a5030f6002c0c00c1c0c60b03c00240f402040d0300302250340048509103085002c461000b60f50700f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 425908030 1250 425906780 425906783
    0x402090c031305120d15080a12030914010c180311040b01170f04030f111509030f0c0304030209060d080307260108061b090a03061104081609050903040506070f 70
    0x84900c030981d40810801c100680044d112111041d5884040c031000d0415903516158078058207207914401c1203800300018007031b40301c2c0d500010b269641c41c030304d030354220050048600050300045004103c440c803007134107501284400b60f0b0b1341c58181070300e07184049101c0010f110380710251043c0c075211010300283c189500001c0c0a6801450080003265140c00a0170803100c05845c5c003000444008100001c00d0340240300c0140c04161800d0001100318255502c6a45910f070884c0041d50b00d0724140440d40018040007030303030566003002000c2174480501500550352508130380704c2640f14600410200d829801c03c0c00c50121a0354000c00c44a1455035030300400e49010103141d1403624020340d100e4010090303c0801e00107501a2420b440034002509120030803c00c41103190340700306095001007243d40d800c0d5030349019040442e035104c0e41c080780d09040d0b000c8045a071700440e8028102e82c000c00403912085280824071000351007050800308110780320241030540c0c0740641d0141681000d800c000100100e03241d08058402c45 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 425909280 1250 425908030 425908051
    0x20d090617090a0b041202010b03060f0718030203071805010f12020616020d03080402100206060120160f060207060203090d020f060c0706050c0d031517100e100507080402090c03 78
    0x40d4030784ea41c0341e410008680580307600c11098160701000c0c1d070a00548004020440050840d41002c85181c440640c000d41100e05008441020640341d0451b03d607968020364004003518080341d0349125040f445002400103102c505c2c944000442d01c04000c10071802501d550a1020b0180c1c0902c1d400d109590b4804107601d0f0340e030b558103002c0000603030300c0140d1442824803ea03940d070842d04092040c0240c0f10480c100032400d64100508001840e6800251490500805c04007081e04800c90304110382000a80d1070004c0484018840201d500a02d040c0424100d4149500721840d0315502d40003240c40340161107101c0c0c2c0c040c0f40480c8201c0580f5140005106400c00105410f1030300300e500000c9444d20009500040220300042080940c4e44403d011000611440307040a00c10029400c5034100d01032054000c03070718801c091490300c0d03a510030200031450201078512020005203140c200c5441d984c0200c0d40030182c0403800c210004038072a10810320240596030141001c02a074a0b021220710450300000d1800001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 425910530 1250 425909280 425909293
    0x40b012f030712020d0311191d120a1712010501080402040204050d03020c0a080309061204080c25060e30070303080109050907180b010924020d09061709 67
    0x2003020503001090060342c40e0010818070a00e41400b5095904028040500e403006014203402900310002e0f042e00300041d864609030086030440882700c2d904085074515084031001801400c4100d0002d00202124041c0710782800c031160000101c0828802c40c418440c1c1c030001c900041003d94003a510a0703030003a00c01131015081c43c8d110004210341040940c0140c0c01644064840d010a013403410711040a0100203026528050003000803030300314401c0d902c0b0101e80d2004100083c00340140c21003a6960b100500381520b0040380b9150b05581e0603498075a504c203042d0500a0001540d6014004282e46040e0140014801b1411702c0d0b80d044010f1514010700101e032085601c08004ad00741480b940340030707500c07a45981001d54100803050045800081c601105540040410303c40c1611621100d0b40c1800140e40200d885080b2100480f00c4003003d40c0048c80b00d0b0301550b50309012420f8020440519030982e4222826594094012a108419480740c3c80104964000d08081c4819101046a21002e2a0101c455 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 425911780 1250 425910530 425910533
    0x90c0d090c0510020115090204080c0105030c04050405010b21070804080306030715030f1a1c081215030d031505010f18140a0803030403140c2a040b012f0307 69
    0x43c070f6100280010042c3d640c3c0c6030030070f41704081940300f8026000c41e113070440c105410140620b036103007140c40c003241c107104012000911080d41c2100311400741c03002600501c10f03940d440e078840c403807030b08041d94402c0d40c24003440300c4560401402011034816189a0758140035522191280c95250340081c040c50303018040c4c420302050042030104a9032425803950b400082d07800c1020b00301012500f4078200e40040080ca422210019178440ca83c9150260300740c0704603d442625490a8a214882e480ca02503050520608000000b0030100b0100c0340144150240d526800c02c11004404443e08003505840221038146c083c8010b51054210440200341410329282c074102c40c0c007641d4403001481d80000718040e1044c19090950611068100042c0740503002141942401d581c0607104031031410039070700700881c0400e0120b00060200128440010842001c14030410a01c0580c0c068a0000034114001c070304112461025501c101200b54074542000351080d121079449624a003080351021b070345001c80c8001e2003000c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 425913030 1250 425911780 425911789
    0x2100921030213260303011404050702100e01061703070c06080a0605030a0b0a0e061003061e2915031f0e340512091e1605090c0d090c05 60
    0x3c06442d01410040c4031044d000e000384418804090044056002400104940001210070504140045a022071107a03901c03031040345060020700503641c0003410701d90003840400e0f06620030416112200045200410588902c0e0782d41e1044290040204425541c2000594070982c841508624100404108140c0da00006440d000c0803c3c01601d41010010502c0501c500c1031041d00514040e0001600862510260241d55110703103200182c40e89403554455001882c007080e80d05014081c4010811100c031102240034151038604a0022440c1c104000c600400d00d000c1c042c480384050205607a40c6180d4600203001074840021303183e406c0040b50f00d0b00c0451240d2041c08100e1148450b41288001a02da200101d205100ba0310401c203c2c0a420880c5050b24942c4103045401c41c0070304002c4c9080545031078038010726101c860102d0059041d0781340d8491800718400320300c0b420541c3d00c8002d203864140c0c0f6201003200d01c041c02e4a40f01030703100c8100004203a052194020b00705950080b4501c421440c2d692003c103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 425914280 1250 425913030 425913067
    0x31b080a0b0d08180a0e1b0706050109020c010c020313170a0209070507121d010c05070503070801060e0603060c070b040c0b0d0e150f1b040f03060903021009210302 72
    0x1140c5602e4041092030388507001d0040704d07000e454100c444d09416890950000c03050040076102e5071174081c036060b01e2003400c0c1c00f0f8011200c00030b500000401107903035100360040081d008511610b19650030a0b04142c0140d01c0001910700e407201032018803054030300e091042c0c0800003030001e605042d03000c1c0c2c8500c9005030345c2d060390b00d510541c42a11602d0b078807901841c01e00c0c02001104041030078080925a410754041081502c15000c00003030902c4800074046007410340c54502980e110542c58800c00e00042100a4190003e604444a50110f10101d895200c201902c4a204443e140200502032005001084040c500340741c0103805100d80880c85904c50b900e1080c2c6501c804880064a070312600306880c0c015003004418060310a0005082c510b0604002001e200500608214480485141e181c10342c021608100c4004102c049c111000d00c503a83e2030300b80c02402ca41d19003034000d40582e6802c640c031158603004881d61035500015801708407404c404004001c41c4070182c0c000402d03509000a40c0205010002d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 425915530 1250 425914280 425914283
    0xa060207030e090a05011d0603151005041d0c010e152113030c150b0a080a140601060e0904240b03010605010e031009030513030803090d031b080a0b0d 66
    0x1600b00702c41c4280c0501254800c00b5101c1078503107107054010030030346181118403c0305c0c0308020b400c2c14040e290440064541a4411241007143c6907650503c100119002a50002c90303506a034203104441080314070880c01070240b01c000809800410140640d0740c400c0a401284640060441011a00c00c0580c4051500318102021304040214074100c08190f100c1e540750b81c030198040d030341ea4803030000e580e004005413400b071401040340c3c0e442d184407204c898460700160280343d0050700d2140460703564003400e59104001601500c074030780c000404c641c002d8030100312281070b41c0440e00d031480040c205600b8840701100c01403003950041f441840c48036032800043c40100030f0407502400880c0b0b11540700c04050841e44654001c0b41480380310384184465480214510320301481007000000c048120303060695441c81640707400000000480c50201c00c1222580145009148410403946011010329082d0700303c1d40c1c01103102b00c000003102032030604607209001c5581c0c0400c42c1007000c580c0d0700c1100049183c41d41705000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 425916780 1250 425915530 425915537
    0x6091c0c083106140c1005040503090301091b0e040302060103030804061d0f01060b13030618020409050609010510181805010c120f02030402060f03040501021309240f05060c0a06020703 81
    0x504000203030384162880c1c81c44c10303071001240c544100c12203a10368035000e80a5562074291200001001c0c800103000303440705800082c000f840800c070305103011215000c900300c10035134441c001040480e028612062440c402e540c1900144030341c6c0d0a40c1c0781541c0300840180101d8607641c40314845203442d1040d812003040c0c090048001c110102401903034a081d00c1c00ca030080940780700305200210031541caa18a082c100c0f500280001010f8460030040e10300802d460001a4020382088194002c215000440d1445122400000c100c907480d41c2104506100c910300c15449010380c4444030348100480c2e640710b185244058115080070540941d10a800c2d140140f641c0400f0400181052440380b0b800e01903101c80f005000800c603d149400d50010b502802014000b0500b031401000003010031009504968503581c8041d005030465980d201c06034080d00341c0c410780c5801e10303220301000c000c940030305041c3c2d405869402924401c5ca50a0106003c40ca4002c9075000e070712441404161404105c4031700c0203100450282d035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 425918030 1250 425916780 425916877
    0x7141e0705060f0f1303270509090105010605070221060f1816060c0c1706100501080f0612120d060801110a0903081303050f06091c0c08 60
    0x500d0703030801c04020b0142d59001c90701410000500c041c50119580501069034040100310281011140f0507502d10b004c840015810341ca0b004829180c1c1d000c401221012640050141d8031400302c5401d0360028880d41d00841d00a2140100526154001c80500300c1a268034221501c1134116091800d4800d4402521003034001c010f004030141d26491032107490030414010710340041c0f0700807011001d8006d84125800c00c01944008410008506282c00007010049101002440501c0c0d14070b4948000b55400030782c0340303181c3c100014294040d0151038880c11a02440c40c90b03680d0b5031020721000c014078519180c05801038080c4000301c621b9460180120341d4280c140001c9503400c010106003129580391951850340ca0900c07924419590002d0700100f5a81c0c09020103458400c0740820920300111038000030302d1806100701040a05400055151282441800300d503541d222003203859441c0c0507110200070000d5014030000c0701149a660003031a0350000c00d030500e404041410f0081144804c0c94241e461040440b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 425919280 1250 425918030 425918033
    0x18030f03042018100f03020a03080a09080709020405090a0c0503040f020a0503010e06040209011208030121060e010f060b040b12090a060e0f06010501020106060504140f030d030c110c010807141e07 86
    0x102000d8040d0045c4001000103500390380024a508103d403000030b02c980360015170001030f580b01c1c400d10801002ca100486465a0711070705041c003c3d4115029450051480303000040c0340c5412405140c2c00e41425071129842c544980c1c039011154a11054242d804c01290070001810b03803424460901119451405040642040d00c1086444801a406002d048030203807004030224550030202c0341110140c0401550880b0841d120f00f0314141e200c10083d040b9403070644416540a810740060240d20f40d0f2800401c907064840c03846c6003560045008005a00c04d00b84048900200195921500f21041c03c040b2580c0e070b040c654410b0241c0b0542440d41065402c040803030040703d82d0070040b107805050240028444203007400002010f42c0600d1103070075140c15401c208121180c840502c481da41c00000f5041e107090403841300f4064041c0150424030070024035451610b103500103000c55218424141650f90140702e8440d071008541c039030b210100c01c1101d20000c1202c00740c401d204405880360715000d03541c4982c940449 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 425920530 1250 425919280 425919301
    0x9020604090e0606030a02010f0f031404120e040c1407061806090b0708060d0308061305010b0a11070b0f0a09170606010e03010203040308041202030d110318030f03042018 75
    0x1d007204d03000740e001849100041c0e0f008201c00d2135842d242c0c50098405141180101c000e02294102001c1d0240b82000740010b1069056020b40b40703245541310050608075900038081225420071607200092131040440d0504026040205034541c0500c80200e02c544140680e294910100305048540b95075496070302d002c016011328207039172103016030410406030314245010540c1200ca0210040c10801c2d00c00004000d82d94100a038000300b6a01141000b156848411601591303000117030548c00300f0070000d8009941c48000602000760369801c1c0a880c103103050042080c0c001d0300010690000d008004801213106070400604040d0001501e00614050810500240a09122240c194042d900410400010a4021490303641140d03209201d04080100030750b041341540216070443d031880d400c1202e00200341840801440c0102c0c00c10144048510000c0c449540d40d100d06c032450421030a061000a003c1031010f000c1c0301140c9020848481105000307000210300c0540e20303a1000c458002101070102c50766170b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 425921780 1250 425920530 425920543
    0xf050c040518010b0f030c160b010302013c0e03151603060b160201140406022404030206010e0c09130f1103010b0d1a0a0609080f280609020604090e 65
    0x34240415010383d4144032680c1e2541c420484030340720000000004c5452012550221030303914442c1110039018070340321318088c0e0200200303110590000714030360026200c035200503c40703c002100d4003200c450b10803818040750110840307091064050040803c1d500c80b0705d4030140500310701c2c4d1450300300c001c80c2c904e84131041009101240101a08052070b040041c400001c80b01d00b161000b001c500d074500004c4800b480121101d170105140f06911480124001480640028011203400d42d8040b900d0010880190382c454200d20844001c0d0040e84040d0042043e0191005403d0b04540340f9441640342c18200d4010a584072030421641e030f9429611400e02d00e04417070394825680262821510103245500d02540d10201380680550350341c580d035440d032000b0f0074480481e14040042ca000381c4448034481d61440060061080381c401c280c842d00440301d444103101000311300b0750b100303188030b030f140c81c43c90149254200c40240e252001101c4d46591801600301580c0d844001e00010401c620001c106c002000118505048 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 425923030 1250 425921780 425921809
    0x2010c0302070201090308090a091802151201050907050c060c0901180501090519090507020a0b16140327010516110d051e031302010906020a0b0402130f050c0405 71
    0x1841806140b0042c0c3c1e0000e0321400320798100405c01d45441000700000d4500815501222055182000001d01105c0ca1031000545500031600d01c032018921150104491250060070105503c10310b005021a2910b50001600100d10317150a07402c01c0540011319217400e1065403490004080403625110340c2d0f0748141080c4500d4402c078404440d0a144c900080e080c0c450303030f0103454400c200070000d2105524030110688000c044400e001d10040c1007124000e5101c0ca01094181d50005c1d017000042c0070000b44840c0c10100d403420340e6a240d4515031031700803182c840d0806040501d0070b06104c90360043d02807008001685590b032034000012107003030880c2c6841c904c0441d26012410302c02200081107801c000482d11030403105290a0080d602c0122010723403508900782801c0405012408800d1129071240d0358181207040d4404c0e01c441c0100d0384c88590680e07892180c000014209000301001800608011082d000241d2500324080380c4401c4070002841600c5c070448900814080c041010401460528055000007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 425924280 1250 425923030 425923037
    0x1206050111060106030c020a08070f02040b010503040b07050702040e010c080106110106140609120304090b0f120d1d2115060109030807020609060a0509040f1a0d020a0e01120302010c 80
    0x4000705403164549005100b00c600313241d82c62803500240e900034800e03c41e000b41d00c4804c060340c0340c02a1501031203216800304142c0c0910301c2c040d0108040d500a0084a010f1034205e0440d5407150303a0140c00716003544c0581000c980290300d900b180e0062280900a4412200d01902c4498066044c640003c02068444280c0181c9a05041d410010285e0800760503844090a03640d09030f4480c1c400000ca90a0101d42c0c2100d400c5101c00600000c1303180841d4000a0703c481d0031034141d504540c0c40401c00451410b4104916201c1d00441e9144440794000d1002d9040c0b2601d01d0f800d41105480301000803076003042d50010030400b13451480001400c3d0f105001c02c00d01802c0352003081b45503040c0703000024250049030100078400317000054010190f41d2030409a0321000c00c0105400da0310010800300030030642081e0861070285080100c0100c00303c0d41c1740510028004030200c48030100d002c690070400710392143d80090740c01840c21000070813003404955125010b8204071641d08030071841c074074000b401c64880141c03070004c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 425925530 1250 425924280 425924297
    0xc030c070f0f080c0303101d0a0f1b020c1305041a10090f06051009050609040f0605130e0f0a020d06050406021603091d01210c0e0712060501 62
    0x24011000a4500035a004a0750012249052038500d8400c000c10002400d0194082001d20308500000700540c424809a941800b000d680c1d021440c54a400c00f20203010040c0407440003070240704a0758002c0300f62005103440441d500032104890140034a00c6281440140c00001c41c084080c2460348540c0d44803070308400c1c204040e02d0107440f4401482104122440c90b8a0988081034505641c1d621020182c11421010005191042e0181c1c00500480c410300e03004200d1103858001141c041c0c1803000480320040c01c0301e0700c2c0c52209810403004004203110010415a240302c08180c50300c4038000080e041104a400080407010a14030514090040394025841c1d0302100030000107844000600b0b10307180d0701c064007081c1c5444a01d4071502038014002d1403c5100c00390031100062541c0441b4610455407801e26802840344e100c3c1003101104401d00441200304400b4900e00c60f481c0c8124124500e40b801a07900c90702d420f0300c2d51155010810180d500c030000981d02c034001900000144a640020102420305c03088 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 425926780 1250 425925530 425925541
    0x608090304090c0c05060f011401180b0309151603150f0312030e0d1e020c060f09060c030403080d0c030603111e060408060a050c070507030b10210302060c03 69
    0x30380744500e0061000194861031481c4020380100003440b0040e9215080e6100b5191030203540c02c0c0f40001340f04000d000781382c19219001a50240e0b89c10242c1082c54480c0500d594140f0020308920740c409441d03010184154441003d00c0c41280800c1405907034455200303070401611180082c25920044000b0b0b059644412040040440d455028400c50b03501c43c2a40f001c10b110440183d00500646505081c140122403211080c01c1c1c0c08409a2107242906003900000000000c04030f03901e4000c5001541c02003020842c00090030301c040090407403200300800d0301d40f0f0400201c1160341580c10035803081b02e40c49408242c02c03180c0c3c051170040443c400000d20301005030340d00e55290f03110318040c1041c400313004d8a031140310962801d8400c41d4081d8500c5000c0c2829544a60b1004002d0b036449044601d810710a00c0c00d40030031070700101c1004a07040301d82c1000c028110300e821502d035100714032005840340b89182c03550040001e000c51810744902d4003440381030000544000d6410081d003400c0c03004007142ea03400801c104101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 425928030 1250 425926780 425926783
    0x10816080303042a240305060a03080304020d08040f140904020d032012070303060801090317100f06051b0601030b011205011812093318080601050a060809 68
    0x907440360308a0310b40c46519035040c0b0142812088200f8031a40e004d128200412151440500401d903010b041130402e108200f04482101100c805451070380c1e02000d01c1c0303420000309140e000076580242c0028000c006402d60b954a01401d5031056000c8403900035000c80030060411800c4c03903000c5030310041d58078040d0b0340340560005441c480e0540303005081c000c100b50010050480008803041f48020784044800a261104880000d230f002501c08030006410818040b40d40c80042c0292204240e2586545110180c0c40b4507000340088020301300709107607000701c500007140d00d04014460700170401c0b52115695001c10400e4440700d40780300c440340782156000100420000f9910900241180d5640c0c1c045036003d200f0385005405804041c0c03005684000e50300c080002c0c001380cbd1415685001c507980750300000541e508600500d200722030f101c45605160180b02044500844011b41da0348a10f02e280c160882148100800d200c400a80c000c5105a80207600502c40c034185147c110016006d0360a03e6034052515a0499 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 425929280 1250 425928030 425928037
    0x15020a080a080a150303020c04060801060f050f0d0c0f05210d030f0b21010507020601030503070602090a0503100f18020a0314010b0a08010507030b060c0307020103090314120108160803 81
    0x4408000780c8400003110401c1e5644a060043e5000000c0b01c139440c3d0300e0400039a55821940000d01c200c2c584480001c003180c05101741000c84000b50f045128452a100400404803042c00703460350409420052031002640c1da84045010b0596204050504c5003040140540a204503502000c1c0f070f440342e801d41c165403a001401c001000024a000f04400c00a030340b82d040541034091003560001104a030121107101c1d1040581014140900200442e0f5601d810403665480300b03110190158008200d014007082c001c0e002001e8280000d09024415a0b894006c20314200d5261b489c00c03020360b90f41200c07800e1508140503208103e90030540e2600c400c005030300007802c10750f01d91100800c01010720210350000002900070303a503c0071006000c511110703030324001c4602034042100c0190000e441c02d40c0c035081500e04607060b1a01034100e10003c504100b0716500540007028524401da040c04400e0240485840d454002407094002000c1010a5545001101440e08203e00e5020302d02c040e96440038481c00d4000010b6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 425930530 1250 425929280 425929297
    0x61814060901151d0711070e0411030601030c0e090c09010b070203100b10110114040f03030c0923280302120c010f050a0903080f0301081005010803030703020a120c030615020a08 78
    0x8200340c5c1d240c1e40c606807103c1749100c001003084e008105002600000000300b03c1e1043d0700808500c410340201c4000c1503264502404001d01d00b640209050012211820308280e00c680b01404980d10b40320150001400032109902c06240010000b44a10460a09008194404104d56018003400250000052098030752003440e000304640c0794102c108001094001c8e9410075040310065560b42001c0c20421116010034400b54003090074070041c011024414001002214064146142c20415502c5541400ea08d80d403652a33000504503110b0248800942c1086034030303c0c0d0040364030252031540c4180842d1845102c0d03c0c08007a0001c1c280345100e640c00140d4100d11115610703115070342e52016807054a0080742a040a8040e403001b10708185210281c000840c1a20403560031261035440c8140c03c1d6040d55804d000c0c51013150020310124103420700a4020b010180380e982030048a04c4903000141d000c40310b007240c101e00003a40760f107010042c0a03000340d010f044601c0b091001d400a03c01d1901c1c0ca90341441080e01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 425931780 1250 425930530 425930579
    0x5030405130609240602031603050a05130902130902040b0d090311030408011a062a1f090c0b0a090302010f120203090c0307060203130306181406090115 67
    0x41c64541c500065002a01400740600b0800c0012075065030310702d5540309030107100a408064540800c1084c0000281c42c4074a15410301c00c0001c00040e41e0488142d0808103043c0c0510500313100d01d510030040030301d014014001c50180180c443c00e0314902d14080c50083e03031080c03aa052040005120441c03200044880d072084403100495401e0700351071b046811510f4440c1c440500d000201d400b050b18007040d0003603005c0306800381c080300c1640402030030400c0500c2040d88090010380721030001c0019035101000072040305420f00c1071301c00e90b102e2000010294455404500026641c56414204016503460110082c09848207464209070140c000a842c2003914000030341402140c60030fa2500354441c9081030841d440d0711401795240d040024803e95a10400c200f0f0511a010719940810f81c14800801c2d50303280041645800405403840d00c03228003e02400c0c405040e85804115100041201404040803a52134a0014100c61502854aa086802e480c3da2403480c29100c0008002800c0b5501c01c00761664805603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 425933030 1250 425931780 425931799
    0x13170c031209160303030b090f0601020a230d1707030b0d081c090302030a0e10050f030a0608071502070b03060d06020d0b1903150c0816020a081911010905030405 71
    0x480c2c145005112901849040e0f160b000100c2010342c990000c0e0720399035044c0d03049001500c601500940d6000202c450394010390081407040d0219203000443e10300522028007003040c4401c240b000b00e007405815206040881c130195084070a000c810040b4661040491504004448100c000641c0079a24208081c0141402140c11030800d2508503c00d4228a44800c04012001161402175101d411865440b0301084900c40c40c00131a003401c131080c1710340c0030701651803514092070811070741a40d03000038055070242503a40d6808114001d013008a0300140520700c3c4141500020028001e04c1d00c03110350000340303490303405000b4481103856003610f81c038110354000000350f1201104004a401004484804c1d80d10540d003850781e48100c01c0f02001c450540c1e003d1050380b102d800101442c1c900b6601000c07a21000108503400144203440c41401c0120100c0f03861050380d2420721251075040641d00080c0e100f400f400409684404207036001b10114a00e800910f0090040c00c0b41604c40c80d449000764412a4095406d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 425934280 1250 425933030 425933041
    0x140307090510050c03030f0906130314070507030c0803040e280b19090c030b0906030c0d0503040b0f03010504291c0503040e01060e010903120507020406090513170c0312 74
    0xc0c819030f04040700404c212600c030b14010511700c44100c0181ca0fa03001380c0c01043d020441d00c3c00b1a4501e003c25039056207603000d0942c1136024803007a036440107506594a0041002c007100082c0c00180aa0080c14000c005540321790510b15001000070019181000340d2040034094443d40f500310f90300840c0c11040b20000102072f106000402d081b00c180500e0581e203441404808920b9210550005035110000c0e90208142c2c4d03002418001c0d44482034407184c1d40741e80400a4102103117090788081e0349051081003500d003020b546111415440e0080d040d0030355804000300c0140b145080c98454170325010000b000410682a0218664070854800002540145107030603021741c252100c861074508080c0d000040303035910766032011050b0100d4030038002c2d040001d4a0781c2200c0800d6208200c0321065a4000b2200702e07500000c00420307a450340c880141241c0040e100c1100240c40030b40f2340b00f80c5200e928803403261f402c1b03800319150100c0c0e038020944401b801141c082c0031401580030000250754105001002440051302c1c0d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 425935530 1250 425934280 425934287
    0x90303060519090c0906051e07050307050c0312040e04120905060705010b0312030c0301092d090210031523030105041a0105060901050d0c110d020d140307090510 71
    0x54110319003203401004120b11004048600d04110f0341550740410020010201c116460b0880e803040c1e1002820a118240d01da1844c84100404803c8600c181031400d034040d0380340c5095802441e004c0d2400c1c0c012064005031400c05110035030062642d945110f1501c0d0602c0e650048040e00908007800180000644240c0c0320300400001340504002801c1640790f80181c60030b540a03205242c0414060b01420031102004c101e0318080d240914500285a82181e00706002c0c1c03401403211003c101c1544503c0c12420300301400c541000103c10b00443c4021070b001d41240140182c005015204200b0980b9000026401c103074610b615206a0b2070542c49140305a4410f5081c0720550380745100c0d030f5415403a11013071000300004056103243c940002d102114150b0798507c100f05080c010000c00c0c50101e01b0402110503540b00c00d5010644124842c02e260301800500045c03146008401c1c40b1900240e44400108000c29801c4011002d500310300c4109189181742030480140003148034032809016102943e8094000e901 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 425936780 1250 425935530 425935541
    0x12030c11030a0c08071404060605040b03100504020f03010801051806014101020708031c02030403170f07030f0203010305120304030c2a170a080d020903030c03030604050601090f0504090303 83
    0x300b041141200c2d6444c4c030401911501c043c82092500c18410319100c403282850f0180340304175800d0392215400c240c500900c1e00d0f50303503000a08608070040071210200305580e503840a84400c108112840c0d0301da604080c08582180c0001d130000d000440901c04110211400159040c1501c07401140c51404410280700d80740540700e28482075450b240c0e030b82c212034200c0710040a07000010100768201c0d008650b54994903034481c442d10070100415212018551007030300c8507070000c2d41c125120345010a03030300c03060380320a6904200c2600c13400c3c031200c000402d10900c00d505000e0070004209090045296525590305d80c0da03118070102c0368a04101000c00010241405009036004190f04400789092190408960343c14409807a0a602e0401c6c882140c0414403040030501549402040340c000c2c604c42446482e40da01d60b40140220f920380a80822140301d054400780050a00d004003080110345a050010400060340c074018aa5410044001020800011201d2041e4100d03001a900040c0031445401c00710301070070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 425938030 1250 425936780 425936783
    0x10216080f09150a09050118090b062104020f041a04090f02060706050708070503090c0f030c13090b0a0b060a030e010204150c0606090e0a03260c040f12030c11030a 72
    0x8032503071081c01c1840c103c00200312400c0541d03606094151504010f445000d01c1c1220304102040045040c8078604407540301c101602c100904041c01d120300b1100040f2050910222003442130480340902c001c50500c1c1e01003d03040f2030308540070320085038545409520700401d0340c030061184d522a100c580038840e032992904603954000c0c000310b588441508014003d8823055402034005000b442c001401c0c9031260741036900900d42e1202408056040e1010003414065040040b0b174140960b0031a00d540d0303500d00c136409401852107a4041440e042e035003002d9880284c001c058001450400440300394a58504080f03625400f403d040c00920001c9000702240203024540103004110350000300049620340111100c284a4482e25040c081c4648840c0d1500983c1c000500c2c1c01c0d802e60141d0342e05000240030b454903c18004501c124460340e400800c1400403400d02c15103400001900009060040420031040a800361803041900100522582d40007442c182621601030a00340300c05908000c1b40d5800c1c400d807504c49 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 425939280 1250 425938030 425938039
    0x30d08062103030103031b030816110d02100614010f1202040302040c080109050711071202120303130c09020a080109050c0c0609010510091a090712090606030212010216080f09 77
    0x605108000c903580390f0080c0816400709414956210320715414040b07403088107906503944100364aa0525010032854039601e900e0500c407000480010301501000f00c03c0035100107074010041d42c80104141000c48020740c00500141000002d00b030303101d9810400c078040c4849030380303050403001c1403030b00d00341000b409182c01c001d42c040c4c182800c0c4c8001a0780003e240e41030316000074082166071a408000c1c1d9040c100c1100144141d008200c0401100a1010400c1705640c0040d00e13007103400003402d2003181558000c8800204c060900c0000c03200b400710400c00d100180c06408400c40c5031003480300014103404414810508a143c441d000681d40800c0b10080e181a02807510071101142001c4035a140a4402190010b0013042003c0000502c02d21034040c40768140c44003a40300b25400c0c820802d000c00f0030303c01401401404441d00b2902a000340902c9074224090098000050280c1544104485400c2000c1d00b4003041c1c1c0140b00f00000c0a60300020000c01c10f0740017070620b60700c84807018558068014001c907a50b12 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 425940530 1250 425939280 425939329
    0xf03011a040306290d02090609072105090d18051011030333060708070303090506130605240d020a050a0b0c0115031505040512031e0601050405030d0806 67
    0x240b00c03424000c504c203101c1c0c002601c0c82007010300d010301c0250021aa0080e50002d9101d0220f2500e0401d05813082e00b01d5011315210743c2c40909081800e0300d501d240c02d030841c0d02d20b54550400071203c10500440ca101c1501e850060101858202c428180703480034050305200c1e8800c0003034140d405025a503466004107851081d60740324504000700021383d1184032040c12a810060310101d075200780c82001d103000b12400130400b50504c0b961780c545c801627402101086061658a151300c0c804039500f0480641300d0b0004050880c3c2800c0c161419809580020303184003031000440e40c4c0503c00d9801648290728000c410360b0502c08103913043c00042c0c016501c0341d00607908100c000300c000c00c400e0541340c000c111132902c0c60000c0c40410844e502c480c0032602e1500c0060010400103d1103039911015800c850b400c0350142048400000a00f1548010340d801919001213030801c55a01502c220010404240d00200034201395007002d20780400f090302c80751051041b0b07007001070503000148aa0f443c15040c9112140c0e01110054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 425941780 1250 425940530 425940551
    0xe030316060b0103050a11040317040506070b04060e0601050a030b040515010603091a06060306190321020105060102070305070501210f1e0603020f04020c010902040c020618030f03011a040306 84
    0x20482c8001240c002814070002648440080c011150003001c00003440e842c007495a11904410240c89584684c146410000040c05980c1e0030081c0460300d00640300e45080e0700b0b052620074200d50451a141c1c4c7e040d0812401001130340d035060700c920100da8200305400c03025629441c000d402c00710440003402d800c5007641c0001c140280d240e80b01d040300310b2069112200c45501d821110030703210422074565600001c10400122641054841c2c602d49411030030b9800c003402d0b203e94501059000001c0107a4910a01c00800d409240c0d09001d25900719500380090f1000f1030940e140c1ca0307200c800602855051000c0b0100b07003c06218183d00c1e1f110785852402040120040746070300d0030040c10501c0b60a00c1a031220742400046070a4500c903c0080766801014640c502010006100103504081075460140d56520011409621103000d42001030f43d0940c05001d00e40b8203800c480181c09108240d0850640c01800195103410202c012203040d100092000200d006180f60102614071403a0002006103040145044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 425943030 1250 425941780 425941793
    0x312060e15090903090409020a0b0c01090b0c070507140a050a0e0906160f2105190c0504120b04020f030a03050c060a050c07061a1e03060c030c0a0e030316 68
    0x900511980722440721104040c01004950003098071605280e400070040c102903840c03d0b500403070440d803001d8022044140c0d5a4020b003070b1500301c002c0c11030007030751074410020030480c6000a281e400088030581a0134406962921755692005000304d0001c01802400341034596078141c40003004103001080a04003035141e1491500c210407c0c0c0b00364103148104004200212401000001c10386926a9820800c07079020000b100d13035003041c043e03941d44440203c0540c8401a85c60248500c208030700f141520b81030040070401c404a441c0c2c00d441c036081200a0000b8402143d000041d42c880b503402c42d003015035036151800011181e401c01842c1c01d50501c00c00403007000309900100a040b0881d00e03402692525aa26840c1c03900707940e003c0311002c0d0301c42c004101c41303000030344c1c9540315500b000350700c2010340c6c181c00700b02c4007045020481e0304c0408801089500d03401e4541c42c0c10003000707910141e000d003200d045040402090b6007034083c0c5040d0005000d00445140f4554404200f5a0410540b54148405c510203d04100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 425944280 1250 425943030 425943059
    0x607030e0f040b01020604110d08191206060203040e0402040e010501060c0b0708010612020c430e16020f15061801060207091802030304030c061706030613031206 71
    0x440c0512065116840c142c40d0512440c60b4900040e00a80000d40d2a5583d02c84074594a00440d075004c1d0b408006e03040801c0240b4003a00c0540b46079680401c204800060203481020f28101c8418210f00b00b10007489200d602009807400c40d803881041031440e8a9500c0010081d00c905100e2800640c1380c20000201181e1041112884d940955008006e0b603e4000c4202c038540001d014030340c0410b103581140e0403070142c43da004249081c04c0c001910601603c01c1c0481044100d540006002c4c0c4580c5030341640e180d01e6840c8455900b4121540d015422071400d600301d400540c00408a00105014200700c0003014000d01c04450308030000b03404d60f0301440503803044120844090b035445003c0c403406144121f01c03040040609040e103c480d001001d0591510400d003018208514804202c2e840c03544140006031402c0015101440c031030803a054a150500100a100c000386450060044100340e040c40311a490100e01d0f0b81d0044c440c181c43c007914030090300b0165910313801211074400b25882c204001882e4910707441e03074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 425945530 1250 425944280 425944307
    0x314030f060a0806040b0402010e042301052e030903180b040e1e06121609090605160f050a0306050d0507050f0d0b0604090c240206071b0204050a0605060703 69
    0x107198403d4503100c8155440c00c04550041480e440480482e001d5030185000f6413a0120040020940c0c5408901c0c0d20101c03481100109940310140005000c43d103400100712078030400c006c0e5001c4620b18004068000a15601821414190364011400915115418050a600705403040b05001540c0d01d82404443c1e225120305984c2c890601c0100700000039001030000d00301140c21841c2c00c0c40c2c0704d4404001c0001001030803107501c7d00c520702112580300803440038400180b5800328005900c1842d41011816078200505105e61030000d0400d140f040d64010740f84030841c80184c6490f80c0c0300d80076031209400409068112a5022500031002e004104c0001814820383c0c0b003e5a5071500076092900b07202540304c5074040280010003000c0014001c5c00c0507448014414012101d21048558030107551740c000d00060b407000e5512228460708009681c040100c030790061094a0321440359203071190b1102c414100c00c14003e00c915100c030301050400c6200d401480280c18020840c1d41d842c28685030242034100300b80720 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 425946780 1250 425945530 425945539
    0x306010f0f0206060127032a0e0a020307021609020d0f020f0409021303080a1806021504030806030f011107061503020307030b07111911040618090314030f06 69
    0x90051103580715050018207050681c00420300741d180c000064039a040703541805521802c2c41002494100c0200440400a600408a0840c0d003180340350140d420640a0f25050802e1a00060230031400030044946640065a48401a126103603008103d05000c100708040902111140012a03040d1039580100f45841fa20f040800c00301c1100c0600301c4c2a1302800b03450103903a0034240020055240745400510300d504d00564031a218036100d0781c84c1d0780e15410038801d140000f08400c42400d502d2241280c010083c2020b800181040048628034107602c0c0300050000b0200000d04020843c1902c04114181103030400c2c1000b07101069035000d511056802000381501c589050100700c22000000c1c141c110127694020f409008001d00356140c040d03200310060005002c20040000c040e40404040c4045d9040302c8101c0006c0030803618030b0820b010300070010f00d11503200d03500d001020450300c0702401c0e661802c0c28940f840440c0040c92410180ca20007000b528000c41840e001082000306261400303164400c500c1101c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 425948030 1250 425946780 425946797
    0x80405031608030d18290106020705094c060c020a03020105070201140412060f0e060106080603030708030a0c030e070f180b03030d0506011202131503060b030903030601 74
    0xc10400761100c15100c0c01085030401c00502030b0304550350b0041c8400034030180b0f0031805511190344103007102c80803001c2044980301200e410690b9000341a20140140b0052009015442c00d000000d030400c40c0180c01c0c00240f910400c40d00062050980030765950500c043d141e2044400340701401c160844c48071a40783c0c0b2090403442c0c04141d081c003c44c0c010200d81e40241c080400142140d00550340750b401500183d050146a075856401c0f03e1002004001030244507400903a507040500d401825900d04031100c0410f1800d04001040003103001900b80c0c1161080d243c910255156a000300303086100d458806003050784004100608410303180c1205c58200001c3e27408000b090310440711982c48084a0103440348110706d5401c02c0013411a599004072154511900015882c5000c000080c0340d5806804203900094403a010043c1640e0883d80340c0c0288905a5029440c0000d0118451102c076070700d000b40140d00300b6900388408828400c1d417200000d85102850603a0300d0030150703e042d580760000c5a00600046800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 425949280 1250 425948030 425948053
    0x1090b1b0316030b0a060c060c0c0f2d0b06031501060c060c090b18010225051201020904050103031d0d03050d2a0e011119020603070e030a08040503 65
    0x180d4485240651014006045885001d40680e4584a00c81c0390001c00d529107048880039540c03408401c00400060310380f419008074a1500100751255100e50740203001c60380b500035011417124002e0f81000d40e4800d400340c000329884200300c040b01e01801b5250702d601c04d600604004010f140d003c05030103940120b044400c0c0c5000c8e05410f0203001000d000306000100d0528407034001501d01e420240740d4881d1403e000310501d845041907421130b0010a0f6140e00101c5d500802030117075030180100355104510117030050b21500315810703084410816100705400b44d0030640d01070121100c00e40c1a1400030300014130a000c6075940b404d000b0405810040075000c00d8540b54a56043d1b841c1039203484200544c91f8a070981020303000960800144040108580301c0050301c0c1c0d5038075007004600701d040281159034503800c8501c010303103000501a1410281600700c540c070004001c002e02d400004410102541180c0301c030340c3ca40d560b410496950720030410031601841000201402c00a420b0007500644900b03803329104240e08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 425950530 1250 425949280 425949301
    0x315021b0a170a030b090406020d0b01080c191202070b010302010f02030304030c02040b0f090a021804060e063a0614040201090e0a1d030406020717030409200a0201090b 74
    0x21250003401d0800904812100d005007074081d00780c0703d0b41410300142d003141d55408109a98000c07a41111101c0e40002d44a00700c0ca2144150b50303e5581c00e00c0e0241d1680307006020ba2503540b06111081e2011030120580b5000d140c821003500c1c5040c42c403008150741b5090365280c00c4044d0308007804105e02041d1035110130798a0030b1000080e01e00c030719015504e003880c0d0281a001d000c0140a820440d580040d2100548100f41d182d8400d10345c054844980010794800f446803801c120305078402d0819102e54101601003010101002410f0713000b03a000c54900b074103e11400e0141041506855000000020300c01da42c0b50084072020942c0244c0e03018500a01c41240040e403400d502190840d402804106000030620446402c031146503406480080001145042c01900403043e1500180c8016141c0c40000d0912120742e05014060050550748003c1030421601000b0315100c1c02a8001c030f149899551244000e48020040c99880e186900a00e60360b8034100701c2c40c002d0103841080000e9444220310804540303210340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 425951780 1250 425950530 425950543
    0x8090313080703020906180f0402120a0c1a070c0902280f0201052d0603031606090c0509092515030203040209010b0315010c02180709060311031308090102070315021b 73
    0x22191047c0d007003030b60f4400e6120040f00000e4416a08000d000b0400d0007120030402492100e1809903030504446842c1c0f41034031080503480901c4654012051202000041481030848151054088003588408200642e41081102c00900018280841c1044a41150410b202c07401144640c0d0081c80690b584000070403102e0076426201c5000341c1c11030b100d0300040390080c51568100070020140c1e4076141c03e8030b43e2607071506600401621440e503030b10486001c00104821a000501c4240c81d600114901104000d4541e854981d030300c01c1d00510f1581c600346004107201440c025086000070404004a40d01000300250030444040340294003900010926403d4081941d20400340081a41c0c0d94910f100011136603603d03103030700c03c980000e904002012114011711001d071207088643d49000007640b40000040503101804d40d559050303241007092085003040304a032410391a411010345a5103842c8070004034070b04210390b400500080002c102d4038103110110b070002c00940381c03611092040300c41d5440c15662202d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 425953030 1250 425951780 425951809
    0x8040e090106140f030a140c09181c050c03030117060711060105041a0d062711120f0d020714011e0c0f080f03061e010f08090313080703020906 63
    0x5005400d003d0703030751070051802d070045240a4152000084640d82d8500110006034468105401c0401a08501e0805180c044e42c050440c030240058108446d24281d1525210440c41910b428079455220076079002e501100d0001d078000c000c1300c0c0e0345d60355064844005c05010b4000e0340e4a018a001080d60fa40c800c2d40003402891050340a0320f856486e000800c030003881100010800300e8002c0c007480c0c40c195548104600d42c540502004203441c2103425091149400070803d080c0b408541100c01004511600c1d0484600708054a2504180103001c00b4245421094543c840c514458601080b80c2a54041008000c4501007943d0b845501c444900550346400b031241d81000d034003101c0d0350002040d840342240e00e100502505800c54000500d45405110741d106030000305102c0e8000061000354217101f60140c2c032002105407080d4000d02c40300002043d4403810807444003040450400f00340440424000c440d10014070410727102ca21130f07031482c1e01500c800341440140d00c0f0b5042a80043e0140c141010f034040140e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 425954280 1250 425953030 425953049
    0x9120201171003020301060909020f0d050601180b030a11030c0a0303020309040c032003100e06130e07080a0c0e0702030f0f18060406170a36020d08040e090106 70
    0x4501801e5034908500c01003401d600c440d1400b400101689081c4100c1000d0059401e0204101c1c2a6006008400c9010304140340a0a543c55504010030b101081c1c1c10705454038011040329650b503260088000d002071044030765140c011031220200304100c6043d415070741c0900740c003641c903040c0b4620100f101e652a10720024000d40c004020719115442d1640c090709802c401800c000130158000403242d070403075042c1000d0030410f850000601c0004040007030b401008202c1030a2240e03540c6000ea001c1100ca242810002c0c103501d44810017200c403805c0500c040005130110f502160074441c100d040900c44590030303104d11562510b01601080d8418404400c0740c448a8284085078a001807440440000b6400710710b04540710302e82503500f00303002e40d15071700100000c00240c1d86410980803008200c00e015400900200b4405103080c84100a00080003e0800200107403070220010302425030101c0d01c0d00350002002544100c0703044500382001500d1010b00250385080b40600c0042c2e940d451000d00700c815600824040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 425955530 1250 425954280 425954297
    0xc01020c121801030902030304090204032003010c1403040c03061b081005031f060f060507050c011d0f12030309060f010e010302210102092133060a180c09120201 71
    0x2e0394040d80085090a101404403403070250b580d010a0120b800640040312603060001502d40e07100e000c0004200701c2d04048000b003111000b52803010341455030800f200c0c441090080f0001e402e0140600c0c40070700039034100f0402d01c0f65105140300f481555400c0f6000c007012801c287d022851011480c40810305464010300205442c00070100200c0005803903402c0c1000c860340f10300002c40c0e07030b8288540490051801d1384a26446000500e4114105821444002d04108102806010810f070f48018914501c8064400349044c3c121100800c1d41030320040c0c1c0764410b600c800004e00a442c600020b506102c0d81c2d0183d10b030030741640c0720201c1001918080c44040d40c84000340c000f403141d41c1205c50440c00407481080006103002440f8001c150b200820104561000c2c061903a4410499014081c41c0031420400aa070346079000842c411007a041d003030300c0f52005801400f00010300561508031440c4040d116805000b05000103200f99a0054201c141c10500001d041e08000140c07024815009a0f40942c141c459640 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 425956780 1250 425955530 425955577
    0x507020a03062a08181605040203071101050103050a030e06030f0406020d0e06090609120c0613020102070e0406020414060304080a03052e080607210e010209060c01020c12 75
    0x5002c15110382d024903072483c41d2400100e01e00d140403034100089070b20303444e0040c43c105c9009803402c0940d602826094000c0b801410741c08580d11022410b4a0084400503281d80314030704120794221100304050038940c40c0800200038064000b540400b107500c655201d10029000e0404d10015000546d00c4108455081000c200094010340140103a11034408002980c2c0e0081c001941c84c0803010b48d03140015400440502c142a00d0a000e110182c2102c0b1442500d0071613020012a5559030003440d4100d415080c0c541b0804580c0b0134813192005060440c034008090400d81848002540a0300c17070025200c81610001c4141e0900e2415684143d80122056040000208094000c1c0c00d0090118a1618815164082c00c3c003114075542c0403094200340c020859400c0030b900ea03107410400780c5a003060005849002d04850741d4aa14440c240c00500000303d00148400080340c0640030303c1c042c45034000c001003000540900150701401c01c072000c02080f20000d05030f0409507400c0d031161003000b910f450340002d0440c0703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 425958030 1250 425956780 425956793
    0x304030506150a030206300406020c01150609030326070f0e030706051623010b0a050a080d050f0c01050c0715090825140a0c0816141225060507020a03 66
    0x40754808102a02100d030040700c440f803510107c08940440d100c3d503011800313100a9a00344503405040500d00803481420381410400351408a02d031000508101c3c4e0114024582c0604820031101da0f035a4103000f000d9401c0220005c0c2c100704a5040d10310004002c90804811860001000d508650540c7c40d2240b805c0240034402259081181055030307501191041885016400500702c240e008060f8000160701c040d000810400c0311403035010500c1001401030034040c98401150280c21083c19061955072045540d0b6050352a006e003803d810000d51810307080240c200c5190004140d09071007640e1410031200c051070701c03900300c0d0507401010700720b81030900401800c0d2703003005000e0b1411004194142450111561400014003400b41d6111040d0007403611070040083e01406c0c0d2001d80a414041e15080104080342e803900c5510340b00d07190004581c005d002c2c0b00d0340c9640040700040c1e01d04ca000d8540510300514240c0f10744404441e8194074540125001850038418010b980300e4035402400e4880e00c40c516180c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 425959280 1250 425958030 425958067
    0x30607020a0b13050c13060603060b03061e01020709060b03070f021606050f07020301090c031202031206040504020a03150911030a030509040b03151329180304080304030506150a030206 81
    0x45445228851001400f40d488000204001b000c000021031031314140300004040d6038050b48035000b5041d082c0180000c568ad44c0c60340100005002c01400514545480100d240c07250320b510008405141c4000070403d600c1100085214114070f407a55401c001c0f110a0882e61a03c1c0a506020100c80489041c88900e22400c00ae180c0c40c50230025850424001d50002030840300b88103012a204c02400100b04204400514000d01c0c11b00c981c00a14100754001000035481480100080d2149544800040456884101c200041d6030400c0051075640001040100101040802a00c2c0078506542c0360250307103030000c1e01005140e8150707a0399042101050611001d0000c09203880d40c0743c052082d0f10183c1d0180d0385803c0740710b501600281c224404842c10a1458245120308855405074040c1d8001180300382c2c03098050f0041000030802440c600d0301e40350941940956086a84940400600001403220015413980a80541024403080324100e0b410010a405a4803009410071000e010b4243c4299464150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 425960530 1250 425959280 425959283
    0x20c0111030c0106060503090c090f0f040c0b0703050a090807080a030c051908041e050604030809031c020a02010201140609010e13050102270a030c050d0501021c0506030607020a0b13 80
    0x803a4145058418001d080d0f4015405c107a0010b0030200420001580030404071610440035181c0b0b07007035810808180461240004c08600340e40d030080f00440c042107107600100c00280744000b40c190b20b0f2403491400400d01c0d800b00300010001809001c007c60210300104101c0122003030300005120a50255070144c91441d030310182034896000d004020144d1083c1704070002c45003807080c81c01d960303698144007940c2c1614405004010000ca0072401c10f01113502d52104403410f81c2d4000a4031902e41e40c100300024a815103040381d41101182519107402d0311034000031590403840c0700360001d00100c00c4c00918500ca00c03104441c0c05a00501d003200401024012054079070300101c2130100a0240c9555850342030a81c2e1201c290f1900301544461040102e185150b00c3d111452001c0320024210f91440c0c0324000a07405070300555100308000705603401000b100358101c6625070705009200d0041d01000e980e2000402c000c45026000b0b018090000e8012440441c0c20400182d10004400d029200c540700440c800303c04400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 425961780 1250 425960530 425960533
    0x10080a0606051f09090f1b020c0907080c0304020d060e0d0306091a030a02010c03110d020a0606060f0c12091a03061203130e04031403250201090302100c17010f03060507050a020c0111 80
    0x101c03d000703000c044844070b1f0031954000b02403441403d0b051000600d0018460700400c1f400b0005c2c03086408900046030f40094040b20f02c508000c269040c004002c07c14118040f0365803241c0d6448140003074064109200b20780040c0c2c0300300080740900c0d05121600c04010301c1258550018128000151f01a030040108140a49811082c00381042c6220f850f054101c400340c3c0160b4050b80c0c10b502089034900800010742404e20703180607000c8403d00d0240144114103030080030740f0303540008096050b205119541c01800102c0821011010051040700c05600545456010b08504000d441c008100002140e02e0101c588259114291805e03070a0120340b01c000d08104c007001000c6808a90411031000954050f6656143d0601f41104017110400c0c001101484001564140302c05100030980100361582244560280410241c807014000c49035100085240c91000941000100744900d545569a064a124081c02c01007a00c554805907007038007891a042d801a4020030300500c1a5101e601a500b1903902c150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 425963030 1250 425961780 425961791
    0x10e040b0d06020d0b1e09070c0b070311090a060c1703040b0103080a050f19020601080d140f040f06050c010b0d0f030c11060408012a140310080a0606051f09090f 71
    0x30020f8261b000c0c03005481c03421841d02080b80d40038500341c40255002050f03410400003602d40b0350740e0501c0440c8010b04104c04d2682e18a40c2260500742d080480302c0c002c00c0103001144507500c4401c082c020a0010000703070b82c81d03001d102c444441060300c032080b00c0c040d40d00318012400980c65540c0d10401d41e4003204030001008000d000d172904500c0050f015100c2c801c9001c080c03074040542440d0003490082c05030b100748405e07400301f600e0280e920b400541d4201000080002c840c0c1c0e549111040c1c0d83d1341d209a92090500000700e4100244460b130082c0503250442101000740a100c01ca20100401c003400305001910381c610000091000038000c4505001103031141609480205010000400c00d07041070b4402e61081c2d45544060300b44030412030031617120803085000036500030200003006201010401d41100d00440c000301050102d03111040100080071010121040035480d40391080150803180f04590040400590700f82888480d203460409000c00d40c0c0d1412083d0b0b113800e0100001d0101d041e010102d02c1d80d9038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 425964280 1250 425963030 425963051
    0x1605010e0d0c180f0c02010b0f0f03010603050316050601170d0e0d0b0c0310120c330201060510020d020d0f0311071a07021c0c240506010e040b0d06020d 67
    0x40e6802c048400c500f0000042600d8003008030300070b40c0c003001102801c6900d0f02400c03507029910400072015008058070345410340c0d000800403070700408040c0c2004d00a4400420111145005150b287c80b4080c455010b4034400d9030b83c3c00181d0559a1101a2882150015442148040d20500086820400040c0184800e00706601c030000c0a01d0251034032203040c0d200104112800d034103240940018840441080f04580c9641c0721440c038081140203c0480380803035440703004540c94142c1c0000030720007200d102c5c00300b4078030307101d00a40200414402c403800b9600200325002010b0002c00d0540d405030454010f81008112000c081303810340d5028407002c082c141c1d01c180301811411144c011f02003280c490700e00c0c0c011020703405200c01d0043c1b0005100c0001c541c03014050300d1400906a920b541d05031054200340840c01c1c02407410340c0365920354400584241c0d07808107060441e0843c80d0401400340c107007a2514640807051009100c140c460700d190154212a0850140001500e10b13801080110210040043c3d491441c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 425965530 1250 425964280 425964299
    0xb0106050f1c0e190b01090903020307020315010e0f0c1207180303050919080703141c080f0106020303070203041413052701020901140309070905090706021605010e0d0c 74
    0xba080b59031980d80d21081e15000d11004c0002e00f008600701c010f840481c20301943c421210340f4050048503003294450f400f180c1018020006d0b500d00d84e60040039920030580c10b80e41d0141205e000d200d07050003040c0000101e1405003011070810301828413480f22600d42040e0742414804400301525100070051800310b2441001c40001805006e54441d544060f0390741c1c2507000700100001510071404204a24100402c0010000035503981101d80c00b4078002180f002c21040c80b402e005a11291801c040d406006440849a0140442c3d1241005250700340c040e9803038510490b40c9000444490015034000c201c01e1120711441c107154080700c00000c18580c4007075030114241c0c041d110161440e03606a040d240546003840d504205441c0079805070f0000b10700700440580006e00701d4200865a5109450010101d00510000c0c41000f000e0300e0480000e1009083c00a8044d691700118030540c401800351b01d00080000e042c1d040c0c01e00c01c99905a544981c40e410510400c42c4110184078201c400160311a0009800442c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 425966780 1250 425965530 425965567
    0x203130206211005030304030b0705120103061413263c070c0e22030503010510020102040320060403060c030b1c0302070e0606120103051006120b0106050f 68
    0x490003502c09011901c420b60356242e40050805482d09403200d8041c0403a4400100b81c800b00c03600036002608a0726000030940345031040043e1101d030b1522000000c01800159000301d40452200002c0130119a61166009038215070b2040041c41e88080d0101e204401c4040c1010001e008a843c0520340b0b860356100c0422401d003584c081c14541c0902c504901c03100081d00c00d000e0500e6207180c0307010a143c047c01c0d41d50140d07212924003448603403c035440c0c081026550100c2c12214414981c044000503010a42400327003407038009101e00d5100342e0380d00c20700b110003900c103000f030701c00301c960144030104070210074003c107503041c0b483c0f15480b5040300062000001041c8503010b4400d0707060071a1030001d886143d003024403494600d1074000d0180400c4500502c4000b07a4005803110466044d403c1040c010786401000038203622420250001c5454030000200c207101c00400c0a0b500c10300c3d50304042180d540c0d11451620701d507030210005090f00c030f0100010040b01d030044004000340801404017610b411404c94460b041c0b0701 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 425968030 1250 425966780 425966797
    0x1614010e124201120312021b280203100b0402071b3b1902130e01120c0909031205041109090f19020301020f120906070815040203130206 60
    0x81c9240100051080300c02071007005a0ba10a500401c2ca41c1002010b9800b01070b00c010040400103512400003242d03404e5410790b02d50b035100c80700704044d00c0411a44a0303554048114040c0905031700c003051503140000d0a6101c1d030b0141c0d015000d4440a03442c4d12050300240940350f4038a40081e02001000005141680c40a032a60391202c0403c020508010203000740c10703211509031001c041c50946d20708040b0114455071079040403614040115a41d8904001d13042002c2e600b24100c001c2c0045841400b00101d503e880058540d0302d10003600c01c0e0303a43c0c3c900c510000c5401d00007504241d45007006010000541d003160700114081c4c00c01520321700002d8a0300c803c45404640a503001c2c0394406030340b011460f206262580000c5094000d00c0f958003075240c16a261b5900c4a0070a03070108001d204034086440039010307214500d0001d01c3c8640c5881c9406100340304100b08842c2d540e00c5000c0e03e40011080c6004501c810301038503001d42207070300c8111114280002548003800c0c140005044e041c951005944400007043c800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 425969280 1250 425968030 425968093
    0xb090c0a030b0f09150a0905150f0a06170a1814010c030e070b0c070306021306110102040303021f090b01080f01230a1e020c1614010e12 60
    0x103041568008049510400390b0510480070440c1002a903554032840310340010804400310a80c4ca0b0b100e00094408506902c40c1348010704007070404c00300342424281020014000c0d5015040c001c5c14508009200180d0b00804020543c4115569014000c2d1400668048203a400000744480880180080000342c2e034801c94a0120030440c003505407401380940452005181402c2c041a50001c0300715840750810700403200e1044000c1a40922207200300b184400039904240110340c1e035180c07090180c0481310b40d0300481c030220b114002c00547d80c00e014800c4404030381c2c06034007802607915061400c1c1c1d0501240b030081032800d51501c0300e0350b02140385051a24000e00c888002081c0b030804840b5054291014901101c42c40842c0a8070b141c102c10345050800e5204013a01e40015101e05120042920040f00c00b030340060301c40c80441c41e001103d000151100b40741c1d03100304090400d240d4880c500305228106444890010f0040444210203050044042c02c425000034181d0310f241c0400715015060080419065550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 425970530 1250 425969280 425969287
    0x405030d02030f0d2d0f0c030b030c010e06090414092505040f020d0f27050604080d09050604050a0303061a16050c03030a0519030903050a05070c0f0e07020c04021911010b090c 77
    0x101b828500c14100100c6050034207008444448000a450f0f403142c1d4013050601010740c21500302c41d51400c046401c0084001c0c02005038180250b21600240422680084184528000340500c00203200311940c00e00c1e4000b601c1c01c80541441c00788006016a0114884116000d2158880290035409260b8010148201c009641e003528403500c00002007480c0038000c00450800c4074000f2420218038a0740c0300e0342119a0640d1040082e1181006240c4004050050f0080000740300402901054802070f95009503002c1c06811b0b00c80c0b4800340151840242040d91440400c000041e401c0c808101155a50203501a80c074a4003644000c20f013568070451030135000a130001030ba40a1078070401d0310a46058240c8c50308100c00c0079655000380c02c92047c41462000c0c848c0104910007004000782d031041c080d020070000c0b0020b241da1075148030500c10050b1504000350080c4500200141400d20a98180030070b00744690504409040c015261184c40c86c078050400c2d503d51405203007548a004c280d50081740300044082c0e5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 425971780 1250 425970530 425970551
    0x90903081b040f1a0f07030f020606030102030609040f031215090f050702060106050715140f06150901030911030d05070b090a020f0f0d020d03050405030d02030f0d2d 73
    0x180c01c2104481600306240070300080c0110424501110143c603121001d421203100c050424107001d0080e83c0c120f440b41d1130001542010184d028010742003205194003241c5d0141c0b2400c0c1010b00341d0100b2146183c1005040d40000c02003401e100c0000003031402818540b56480c500250042507034605520209001c01403202001000c03030300c1c411002400d508003c20050307410306180003500d0710410302c15202045404217015050080c030918070444264840410443c545070094042c650040c1161001c0c105400130300007036494284442d04252501014a81500d440d07040001540101600c2d082600c0c010300304441c03031149131020001d40344905d03000c1e29029120f0710f00745051208960020115030498108410090050715244102208450112006503a02401703001064148206020107548540944920b10074541c0010043c4160340b0300303030290b80d400c42c040c5c0c0d400d0340d40b84120022145041130420070280440072030780c0300802da54134048021204061580e0080b04104045544840440d640c94200700c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 425973030 1250 425971780 425971801
    0x4060801050711010501030c050d02060f0711120d021203070c0c0806040b1f032006210c070510020703020106080303010e010f0906151805040f09020a050d05060a0b060409090308 78
    0x42c1054008005d03c83c030b40c1550b40710400c05401c0d21803076002d1514116032004550700c080c00d442e5107203024581e507034030780805003006a08411919800c60140c0304c042c10700d118640010407500f8001840e0f03001049012003013140b02241d81d000500e040c003001905203c0000140200344a00024a084001050f05080ca8100281d00400140c17252988100c02e0070680407000061817114207e80c5c215101611854200b02070700344003104c45d200c82d94044400216454510071344400c0d0035512030015002d070031607514003801c1606441280340c0908030740e02881e5101c070b042901d038008041d4207200703100110344190303111070981c6190400e80001d02010b1f180401444841c60702105480209105002440120310300020b15588003000b140e03180802010015200320340c22030442020080401610800070009a2081003000b0010818200e00c61503440701e00180314a001034100513441e4005000d840b040c2c4500601400900a154545820020900c0300040d52030b0907108103140140a0703154020389240030b12940 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 425974280 1250 425973030 425973047
    0x1906060e12010b010c03112b020d02030c10050405010b04020a0c06051005010509041d0723090609010e0a09020d03080106030b0a0b03010915050a17100501150302070809040608010507 80
    0x807038a681c507100c8800081c3c2c2c0d12802018440f41c050514800401c0b07105074042c205452040d80601d40146501d90a48541100c00c0c0700d008882141d003035604c3c815160380e040380c1f20f2040441d0031200782d001030000c03c01c20049511190304a4030038030001800b02082c10118060380c11020010010030158220a400d0140a0283e16845104c400b11041240e040c84000703450380c083c03120200d0113903a0700c3e01e42510f440c10410b07014010100090848012650310740d503207503007840d444490644c140001081200d0604001074458001c0700005c0540442d07a0a20805510f415001040182480c1e10b9106243c0980c43d10b0000c0d0768024040e5a0302489e41d8100040074090b0340100d4078460007003000381e03001c01c0b020320720006590542c0c50031400441e03000f11002c400703000781e076003a0011a40070303c21130000103500c17503600d4882c0b20400b0903106944e180c0c2c180303c0380e52084650034801e04c001008000d4075200e040d0300c260b0041500c01e1150007200d0400c3c54a2012408031b4000e82c01007009030b076450090140c22904004da0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 425975530 1250 425974280 425974309
    0x60609010e060114181e01031d1e030d1a04050f131401060b0c061006022109010c06020c1509010b010c1b081b0a09110a081906060e 58
    0x44042402c26500003400c1490025244510708004208052031002d20003081210300e400030110f40e041800307120b42d2548050300008440c040392403c10090361080d0700c41d05010f043c0703200002420403040c008008400700601d01002507101d0204015100951180b40310340115000c100c42c1080c0c045640d031081c8001c0b01c9029110700355000b40e2038208187e900c60003441800043d80304480400e85c4051942c07040c050051904151040d080201d01c1004a04000445030301c02c2c20781540c405422580c0d00c03010380e100c10a080418848845072400740c010032401700001c2419000c10f24080b00e041e00c95484000498022a915038a03541094a03030310245c4803840c035074681040f03004000300300c058094000a4051000000700520014850744210380000a070b0003c4001401444e0035100b854054a08601c0100c46122999105611028001c03480c0a0b80d482003407405040c03a400c0c180360400d464030558000600602403000462245450507940a41b0700901009003416101c0c0098031000c4020040000505403d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 425976780 1250 425975530 425975549
    0x8060f060414041113081f1407180b030403050a020d0e0a030618050a05030406021b0a0618170c0405180307150f020a0f12050411060a0c020d0506060901 67
    0x41808403092908814558500840300014501d94207491007295020311011200c4204a1403000501824017103400d0243c47c25801202e10100c0c012005101110500b45000900345000000145050b006041201928000b4425040300c9656440c400415520403242200006c1020641d00d046580400002d020080c2c5801d00e246442c1d01100405c03004060707444082c12454894030302c031602140c40141c264074140c002c4e06481a1740e01a0a00f2a501d522500c01c48005120b20070140c4602c3c42c16070201680160024007030240e080ca408400c80c0e02584000300c1070a030121180c0b000442000292100c80301e40c1c1600003800380c41255508100855100400248001c800a0b000c03082504021049800715548030740b542007021094803440e0003c1074215a000a410720004000400d150411040d01c001c0655a950701d11b010070b9402d0b080305643d0141ca00a007513007000c1c03403914058901000603042078603d80c9020401c8a1803a00041d414941c407100585040d005041800914206491006e014050004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 425978030 1250 425976780 425976787
    0x215090303070c0204020c101506081303110c1003060906050607080d150308030c09043b1005010e16110a02060304030c0b0405010e0606180c03060102031908060f06 72
    0x819592648401820002080381c5040c00c0b400310758503541551002c000e0101226081c1c1c0c2d80034400002001904c0e0490b00f40301005600240051003580543d108a01440b4001c011003560780e01038420254071800c02800307006214450b603464a40c40111008010b581d5804102c2528001d101c80071102e098000c1c50151400b0860400800ca069003100d080542e440c00c00920b25584229080000380340780c00c0100401c100005010009100c40c1c0078040d020700c1103034100607050291403030011a54280504d105c4143c54544450200500011010381c17460901094030409049107a03030703204440c002d8001e91281007021051190183c01903009003d558140d04283d0355490064007007560360000040300a100b0100000042c0030035104004040c801d66108182c2d40641c1403900d00b040c080c00003401c4030300080c41400001401d604e00717885a29010b0f40385c00c44171205615400704144580c3c0c001084036055102c00c12500b100718019040c640c083c40100d644584660401208001d1101c4d1034560381c0f4070500050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 425979280 1250 425978030 425978041
    0x60801090b0115020f060a1e0902010e040b0616030201020408070b09031f020915070302101b1209020910030b010f03120309060603020301050c130b0f0415021c050a0215 74
    0x1c0300000e0565088240b15a50143c00c00d0089203021010304800000b030088806210915005030014101c02c0c0440c0c0e50401d0b524401107011302190f40802000e030014126941d03404141c02d159018454420700074201d185000d028440800c50483d80c42c204400507980014108070002003031003003031b02626992820742d04c4c0c0107a6000080e520224100b1002c480700310310a0001c6150046e60480e80180c0c4042c00f030552040d04082c000e0b584d608294800e6015003c0d54144005500f03003482101d40342c03440441030182e50407450000301c4203282c00703000780da0200da56000040d01603950f15070038a1155850450703e17034090342180741c40001c01c80c06038403c6030420034a00c01072000800000d00d2050b18082483e00054080071070400b0702c094000b42d480a50103510748028480441c014800400302c1c0c0700986070208180b9641c61011101d031007180c0650803841410b10017803045011641c586140700740c0b90710450b10b503495a4180c011a007806415050041540020f04c42121030301884228529410510301c01141e03e40f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 425980530 1250 425979280 425979293
    0xd2004050c07082517040e07020d12110405040614010f1404030303050603100c2c03060f072d12090c05060d0f0f050105040b0603041a0606040308071506080109 70
    0x402400706840d140402d00c0c1440c40c54a03c03132030040c0c0c03a001101c80001c00c201e4070500001d41d102d4010101a00070200029101600020303042c803195100e645c0d03981c3c1d010206002e000041519480c0b8066050f02000001915074440c05400d000d00200350307450b1045500b510016214023200000399040c03180700c2c0e01e2440b06144000907503085a40505012800340c0d0f455001906000210401c50700d03d52901080c000f02c2d0744e10100d038940081404804400840c00c41d1707598403200c25080041c940c96401000011a02c003480505a50000c1142c249041d4070007900e5031510000c1d0700c5009a40d44911241c08450069900031000008180145410410110280c90f074122003406401254064000051140795008403a481203403000d5501c1400c01c08184c10151840290201b0310680c0d1049080c40283d502c0c0c0e1a010044034021035004010108803800c0c65425035081800030f00950344441e0074000007010822000c02070a0030380c481c004402002ca90480200100c4003150003501c460f84c50b01d10b0510000d0807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 425981780 1250 425980530 425980537
    0x20d0909200c010f0606020a080301031502040b0c0a06140603061515040e010e060423040c030206030a090b09070f140f040603050a1a070e0105090d2004050c0708 71
    0x40384041040301d03010030030102110786640000481c00002036420b03003400065103d9642404d07000410b0144540c0c0d80002c0f42c0d07500c40918040c040c103100700010400100c0007964035084000041c409400d15035210000440e40c3c0043d001c20069030001c20b622000c1200e00d10900e0200c010155404415003454400f0a903903d01c0240911600f21781d19045005030781e40e031103040740e2507081c4000a90359a505c0307090426582e40d00384168114081e0f20404501107203414001c40000381480841c29203400b48120180e40c481501070025036500c1d480840100c056265040110301c205003001000c41d030300c01d082c0740c400c00000300140b085038540c000384c0c0c0c00e11105034000701c200210350310880c062550031601e10000d420300718500021a441890311500004000b0003098181c0103d00896078144d080c081c400d02c88002d01000c540c4040082d203100d0900071030b5070142d07026000700709001e05240c0030a0201c0da645035800c0b29002d20310089071500060003881c3d18050051550110306040c500b0f0510840360b441404601 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 425983030 1250 425981780 425981789
    0x8090105070330060801020304030e190b0a0806011107050a09020a1404080a051e0c130e0d0e030c0a0e060d050f07030605060109050306090a1b0b0c011a01020d09 71
    0x400000c29509061140804031000a40d100924070042d00f41880000505042405003c4503402c000001a10300010702c00e60b4403a0750151105e00e00c54010404021001b1204101c0100d405280c100105071507041c000504004801c645420800741084800075100145581003e400c03940885010300003901c52480040890340c0e452009038460302011010307076007030b840808903181007100070400144941c030000b80c5180d01c80c00f4105a4010103040000c10204181003c0184043d078018482d581d001d00b404110206d620b9090040000e01940945074103013880300c00043c11001440c4049074180c949410f008135034050004444040400d8580f400034050f20074018010351007403003664415070a100b401c1c8111080151400103850010341c607864003000800c17040c0d81d07060004080a40109640c280007039000d00500d07601d0000c2021000d60754440c140c10100c0c90302c141440e03281600000350807186402500e00001513000128180b000f020268031400e1104444d14110b60103568015500c682008403e0142c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 425984280 1250 425983030 425983037
    0x92909040902030109060b240720060d060501080a0c023c060a0b1c0b0405190819030b010c1401090b010314060603010c2703021c0b0a0504080901 64
    0x201901000035009003a0080c0194240d400e004c078420412949900c4800002011100b02c0f40c003061017140300301c22510b4405074110b040000c104410108806056110f0700c80c51000c0010840a190000300c2d1160300442c0c424210583c40d60b4081c0040d68000d080300b5481021b4000401c400f10706c80d04003d40d40e5181501c2c801c0d81a00300d0002d80c03c0400a28000b12511365501e5080c50a400c607601c1c038030356640e8201d40c080040c91070443e00d1078a43c0303171081c00e001e401c1d0608a494461419607450b1007141c00c10280c407c4656200e1a83c801c580c018000114104450140201a80720b4460602c088500b03440120300004140c90102c6044150384c01c030880e1a12650060030b030a0941030144c412600624483d00043c00603a4801e000000700b000c0665201a00e015003010340b502d6440316001c0c1401e8500303807060310b07021800c1d0320781c41a6110580c0380f40400c01d0110f100078569065407600450691a080010076004115040100301880350150303001d9044801c03003c1c10051031900e501d03218010300030071203841e040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 425985530 1250 425984280 425984287
    0x10510050f0616050f060903180a0f05090618070f110106152102040b04080d02070f170703120e2806050d0209030106060f11010203360303070f0929 65
    0x2032000401c45181c0310700d0b84038210b0f00c8505091f90303200e03640d03003100615082101d80f0715030700d440386d080a1040d80b040f15100c084d612100c5081200b0024406002040d854003c0002c1d980070007146400103945004600b5a2980c10100c8100c3c0c40040c5054901013550700c0c203070b0506504110481440007081c080380c0051600c403131204112030f810104024001d07480c0382c83c507001007004140d461a410081c0112501c0501f12891f48401403030036600c1c1c141600c150b480c89040b5441c02c00031003402e0071407080505002c0054904040e02c0c1d5551581d46443d440f1381e8400a9082e240001e00f03401d2003200070f981c2681050a520174407403000ca100d8560f000303500441040240200340c0b90300032807081c0c05860800c00c0040081c4141034843d031005002c28818451074000a85003035000c42411703418400c427401aa640d0810402e16000c20307a62900100440c1241c101000c1e58800c440354249050002d18060411555520f541d030301c00b06401041d008460b0842c000c0107000030080302001300101d652194250b80590070540703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 425986780 1250 425985530 425985533
    0x906171501050f0d230f011404060803040b121e0105010e041d0d020105070504051c080c060f1005011e0c0c0807030302030d060609081009020f0d05010510050f0616 72
    0x1401e005000308510090f00119011403003403826007024911600e80303d45d0100310000c2101c961606401a1001c040c42580d4500510040c0d600e5032070b0b003d40100207170000c652030307a0b42c0035080e01d07551240d408a2514103000c58940c1052240d4080b00d600100c0200810741c06241680a0320000c420610a40b41072110181c100182c640316500445000d01155210000705900c422495843c0c013803146203c1c00651900001401c00d90241e0107690544501800402d06c6c100c1499a040e4540c000050680b19500b051002001d40402000321078400c43d02c281c030410759810b002c0584402013903542c0101d8180404028200808031103c0b4040700d50403600d25118851043c507080c4040010f6050b0020707240d80c010070b0404400c3c550004004c0001d40c15a000030040660343c0d60081321030511034000c10100390490050340354914580e1300408007145c0000e0000018000003400500c020001400c1140d1036515a0f04100a88902c0b20304030b0000d11040d42c1c00b03616000110000344480c82241d071000307010039202c0300702d10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 425988030 1250 425986780 425986787
    0x52704020a260d0807022808030c0a03110724090c1d060a140d0510090f02040b091009020c070308070605040506010b0703140f0d0c0305070906171501 66
    0x400388646002c0200d02082d0318041e414400e501c2c100010300c1038041d0020902e10074204c1510405169010700810030f9442c5012107100610b4111080005240d00f1000103c0c200703070000e43c0a00303240602c65036110401c640260640c0c0305056404681c440c1403120714081181b045610002e000c0c2990304200395000600c1a9009002d1200c0140040002d01d0b000700f05400c0c00801d90100c45c1c00580a10944e0b602e407420051100d4160142040c1d02140a50302c64082c240007414088a62094064600c90703c2d98641c2041182c1c4180342c00e0710544003c0300f0a200b582041d225003d0f240e141a1a1a0150307d01152040411003540c4591040c0c56130024034800000b405100410256602044a95580250b81000d01c05001c0c02d0303c09072070318010b242c0002451608081100e0102c1d43c1a151206203a2941b01e00181603044612801814a000c100c081400000e42c480d0410442c1c480d20000354504102d54000c060441a07040a82403041406000c0000d0700d81890550b40070304c410b001e001043d45ca03800102c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 425989280 1250 425988030 425988049
    0x90f07020d09210212100606030b04050408070210122408030a020a11150304060204080705061801050d1404030320040b07060506030c0a0f080c09190504050f03040b031005270402 78
    0x400e45019125155406e0740b43e64104030203c81d503945e024080036280108000407a001658004c01100381009a4401070070306517540102c000d200d040c501e500c20342c00ea000500303031010100754604000390018003104100b140200780b00a490000011410050b00d404065950300640030b0242c096050403c481043e035603104201d04003403c01c9440d00c0e4483c1030900e01600a900700f800b946a0328050081d0215044c1011426070304841c000c10300344505460170320010f6132503a0104050300301c0b1a0f00d42e0401112003c649030700300d002d10310942c0e0020701e07001050500750103440640502c0031641c0d800c0204000070f810100956000c02e400c50340c00500e940f12400040d140000d913444039030304420003800004962481c1c01944045030508401c1d594010848010040381e1700d030448185144544001c17070201401c03401d600456200b80300b0f1044400030003800440301d245030005e520031400a40b00100b0004178442020a0800034041138401400005505941500307000e0180083c8024680101c002400e565035000c02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 425990530 1250 425989280 425989309
    0x102390a09020d020c071401050f0304020604050405041506060e13020f1b070626181e010b0a0e13121404060c021009030b130f02090f07020d092102 65
    0x443d81d0f80102c41c58480a900140c0f02107025000d98800042d4031003031540c4001240320143d507818a0320300e080300011101d03080503200340d800c10021b10001c901501c0b03520445001c2c0b8052103080d20810640f210050a4600507044030017040140f1301d0240407500c9501c6543c80e800c0b50350b2009601d807210f1000c02c4145010369505400d82d9184000400600900451800700340c44540d40e400d420030080b031480204203410209002000099580000c10030f041d9400003500302c41d14502551840002800501c03403071031501d030899000342d5503054446490301e4034401d80c0c00104603001c50b1380300701c0c5040f40c142a0b0845a8040281001d075980340c1c2c15218500c2881d91803a0b801e90654615159501d80200424030485030344102e000e40702c0112040c3c4003034016089541283c2c1c1c410400003695030f0f01c0001e28403101110000b00c40c0c8030020709681c401a915902d046103d01c0050a031203180745003510000b49030030095203d0109211520405000c40030085001c551600c41c0d5500182100440340b0106118622440f00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 425991780 1250 425990530 425990549
    0xb0f01090b07051015030b0912040302060a02010b0a0b090415030b040609050a0b0f0f0c090d030f02030706090614061206040609030512070807110d050409050406020f0a020307020102390a 82
    0x56491101c4821410170094901607101c895043d0341e451009540d8640503c0054044502800704000600c0e15100503e040e28080c40041081d4094001052004881c1d80080751600d6010600b0316490500b80300c0e516001e150141c07140c111f03038959103078240b48101c041c0015100d241c45107000020301100300105803003d41d00c0f480d0601103181412415400a2041d982e404848e02580c02141044510409982c20f100c0003c000300480c030314540c1c00351400b4613440d03143c2e01540400d20a120108400f40300740e008a0780038503000b0a06258480c21034048100081005100f06502c007540072550800141c03180d03100340d1150000810b04050308040e5414010544901203c145080030401d0b49a808003006010b2803140d1240b01016440312800d40e03c5100e5049580000707581440208255842600515009070040380010700c0c000c41c1800016080c0d11691000c00540d200003468400c659040000c65203140302d8040a10040ca42ca8900544004001116092140600b00c01b22003582e6007100c0403009080c800d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 425993030 1250 425991780 425991791
    0x20f0403080a050702040f06150815030109050709050a2a053609162f0303010e1003020a0b090315010807050a050315010b030709180501090b0f01090b070510 69
    0xc2c0c0007051a48031a5080b40951704101041812034010b001d01070680e00c400c0d0507044802001c0e64219540c0000400e00c0224030120000242c041d103082c41042c1039903000d8000303010441c3c00d00d10803005844024044280782407408603a05483c0500c2040760f070804c80b2a10300c42d4120181644201c51a006610000d0700d035a503400f0100c2c000c940108030164a00e0075440080c0c429103482c0c0208031000e182120b030f00e420300503c00d540d505a035209011035480c40701e0807030442c60380703104095500041c085d11241b0b00350281d100000500800f20fa00705815403002406180170101c604503800319000c40081d1083c41d614000114040440d80c0d41032107820482c15824002c2941c0d507940380b16442d47d0b000140300f8035018401c82c0801040d10306000c81c0401103030421203c9145c0300c0c0d10700503800005a000605002c20032499060100e4103084402d0503d10191240318041015410050120704070343d0010b221921440701c03030f0700c130384a00c1e41c009000000315566115119101c2d030f10390400c642003003c0238604003907640c5801d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 425994280 1250 425993030 425993047
    0xa120b10050306100e0105030a15030b0115080109060315090503070f20060c1b03030f030103031808150c160212060f0f0907032301021303051b0112020f040308 70
    0x10015600c10743c4101c5410b0b410001841d070a4a002c15100a0940043c0042000403803900c07040e0091250741001c1a1070400311562522861080f00c001c1e08503617403811082a8440b066640320140901410302440304104040c51070b0ba0702601240b1005401e440c2c5900c40041c03906224092040d14000d5400c0445940d2842c0c8620381061510416800307081161041d100400460811001380e030101030008000f000d07000340d20356041201202031003150742d141c4030411030892414131030f0f0090b50080d4440c3e1942005018146001545010140c1006c10343e58040004104950851021150440c054450701562102000382c08480b0825000d806034110300e441441d40324401001803403510504600c0120407994681c0304120703608203410350f0304200a0b032101d9400c0c80030be111402d5601c600080c4401820102010400301400d98001584004803005860010800e00406200c900c680900c080e50021050010350000ba000c0365010072441071081c0c0c082000e20303011100404880103940c00c12030b410f450300c614 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 425995530 1250 425994280 425994287
    0x6150c0615080a0312050901090b06150412080a0e09061807020f0d05030402040b120703060b013e0303190b060702150a030f05070e04050702071a04090515060a120b10 73
    0x1110340d80c0900c4c1e02d0900041c0c0c0c0074030b0620405270140d03440b040c04100c6803100c208000300d6144021304a0b5001c08100400a00c1e100e100d030b100c100c010f10400c80300d81c40c3c1c1c0545101512081d1201d13001c90017041c05404000d4682d4400307080c000c4540300818114020341360003200301d00d805120001410184907119400c210590020b002e507100c0da00c00c490611140e483d000900542046801301c221542d403001c0810b00004000342c100d584010010301d840000d99183d8080c0c4090565440010b852022030341004401e020522402035844021880086166052100301c0241ca810015014203000380d944044480139903030720086034805a00200072480403801907210060503803103200584d0110b480c00030300300959803103405520b12803074958480140d0741c41800140700241100804940845c094003001007110b101d5000f03416994203890800549490410111000300e400180c15203800700e4070401120415510601110307200061454802010050061036030040c19000304c00e503500100010402d00e481c3d51 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 425996780 1250 425995530 425995547
    0x81b070f090b06070201170c07020406030b06040b03011a01030b0d0803040b0106110c0604060e1908070611150403230f0304030e09090d030e121b0106150c0615080a03 73
    0xa41c440300b0001d8001400802a19114000e002804122004040e00300b04e174100030900c2c0d0111041c44454540501030380013400b00c0e50b850b0800c4458115400620519040c10700c591844004244c000f0041c2c05030008040c44150b030b03501907442c101515800010900e0320744500a4110640c8101c10903140e05040c03410b24410142409407038002611348a90908003000003c18510640000e4101d03440c1a08001c011142c450f4003805d4150060140707001115007504000740c0b00001c00c0c4042c003030900103040030002402020101000c240a0740580d5004e581d5400f41c404007038005605042081c251074400c1070245081c0c86c40010b00280c4400805d01064072000b84d0300a611851183e580d404204001c1c2040049049042d40c080a6079070040c41499006070082d400104c42500c0d039400c41e041da40c5600602d00e9694060242c0032000d4580702906003941c0000d001e03c3c40907044401c00c6010300c0c1c0311100018407007405418040d14035600c6103d0200250005081d450103800d0800c1901c3d010300c0107040c05800000f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 425998030 1250 425996780 425996789
    0x314030c0a0c05010816170a18110102060c04030203100f1508150105040504050606130231050a05060d0203040f0b071116050d0305210103031101050a050c07081b070f 73
    0x4001c203002070780c1014600c03000040c111503521507038103001f0075810400d02c44d4070040c0406411a0360302e89138000712016a031034110780c2e442a05038921b04032400f00024241140071300132030103141042c0001d00c016500411011100850100c002602e1018043d481014000080710350281ca13201d0940400c18010100d40140000040804040540d0703030380c000d02c07045801c00c03200074125030829004902c05d460860b603550000e404c0c0710005820207c68400d154a2801018240300c40c1544510001d000f015540c00004010001110156900f51502c40456007034070403941d6001420b60300100240802170b040210030740c0c141c2c00c0000c0d141e036480d1603000a80112500301a0203070740d00c9041d0b090002c0d140c00c400200141c3d500a4200000420b1940c2e050303600d90000f059000745806000080a950b4002400590085000340e845052103c181104c541c211035020300741c400c8040c2010f04106c0c40500d00c404550585a00400b41c41c1e4545081142005651001e5918071481c000c05600045000c1d440244c5020794 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 425999280 1250 425998030 425998037
    0x8060f060c01061e0e06060f030a0507090302060d0617190305070303060e04060b09150a0612060b0a0203040302100f0c080c03090a0306020c07080703020f10021c020a0c0b03040c0314030c0a0c0501 86
    0x6c3c1c03118002c125841c00740611030108844d040000884d2041d4680003150031940c20300301405403e45950010340580c20040459102c0756580804010001a0300c041d080c1ca000b100f80500405039455a11b01011600100c014050041c0000d400007094820340c0008000c202c2500043c2460500d8503100025294810415208501c0c031000302c0cbc8200c5104100f00c100c1c120003007413032907450720700f031803d540310003043c018500300b96030f40c03c00000c0701d0305400f0041c80300912950207180e446007184100585603070001c18180801001f02000d40c0e0841d080703614a400c107030300030344219200c6c3d03002690780f1301e50310800340400e4029103007840020030030030141c014140d0800080c058400054581c110076650301c07a14072001e0342c441c0010011940506089000e030340001641e1040d2402c0d442c40ca032004112102202c0030800580c0901c00400500607203d0200d80030b041d80c40c0301c181ca5802c0c95202c0240c01140ca02000c1d01c4440c0c56040b4458000b07040046440e0503069005942a20400e4281028001514425140403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 426000530 1250 425999280 425999309
    0xb09070b04090c030f051e0c0c0a0b01030c060206150603180a11121b09040309080f070e0109021204060f06150c060507020601030b041101020717100c08060f060c01061e 74
    0x18111070240e42d100d104515019842036546047d41898088060b0814034428800c200c841058402403001801c21401031000940301c3d45146840e2903c039241da40103904540101d0300f40400c003603950009403403112040312096201c2e1039196403842d0010500b000d0520a124642250f003c20100f210120f905100803280300b040305818507030403520f84101c44240081d2140301881d01d246460070310b42c496040703400fa1510f00c0101c0c1c0c070b07940c3c00c03407518005101c1c6100d60b600400080040e0948200110f0140080c94001d50904211484042a459018200030315803a01c175181a41c40c00075039840a0010a0401001203040b0300f6464094000440e2690a84541d801c01000030075050000804034100d0b60303c1056084195070b07a0711404049010012814114000c0b410300180101c2d41140d41040800d0000c05405400e00304103540d0200c412011000d01805500d034100000e903548d9111038034150805844069592049603403881c010007181d004010012114207200d0000b200086208041d906141e039484803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 426001780 1250 426000530 426000551
    0x403030e030115080c0d080c010908120703090309030807170310030510110f0c030d050106080702300a030f0507030e06010b13150e03010c051e0c0a0b09070b04090c03 73
    0x80101c600c0c0511842c075170024101500c14242401800300c800d000fa031500c0d0030010003900890a44412440c1610380200100f0289151400001c0454000b0a182020844954195030282c007060051102410280d000b0401e02c084c000000c40710007020041d40011030740c2c2d280c0240030b08210345080c0010f03941c074420342e45405030355001845100c05d101c2200e80c0c00b40c1850340343c4040307001c0c0d90301c258105180d40c001030103100c8052030035005090207458182c035104418034002a00074070300300c0d400741c180f0380e42c5501003e1800d240c1d03140348400c0d2102c01d21400251341d518110f0f07400e401500d111707081c4061071440c1a00f00491076a141d800041842c0c1030304150350aa0f6a90040f101c410300802200f01c0400403540800c11030200912078050762841203041040b030503000c10000a08441c68000000045800010960340805003000c811004015039003029041555002c4040d03600c7d039021400a03c1d125031440072603080c0408200307001c000c10079060003aa444e5120903d40010301892040080460f040101091 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 426003030 1250 426001780 426001811
    0xa140f01051909020604150509180f010b031320090c0c07060302070c05030a0b06120708100f0b10030c02060c091c03030209040f060806010503013c020403030e0301 72
    0x5000d000b820b80804108005801e280c0001c1c296164203c0e4407800410000980c038012208440b04011141c56032900e66400b070080c048020407404811644551100400c01d10160b2030010b51f05481c40e000c840750b2641ea0f845000245040b10041c0a80461504009e4000300c54412030740b070034984d4060301d41c06840d45454500b0002c6000307075000900d05400824080c001503201c0d6000e0106a40282340d518400c503900c01c0843d0900c10151410350b0203100d00303020010603040102c28000c006c0a074500608041c1c2c50a08010744550800c15401c0000f40c66030058038032b01031290440c448946005200e44c0c54440c1014014000308180780e0742c0b0002d40560030010308144041d006a5501b042c0244c41320051464a100d5091060880c80c0b0881c14991300303000d4500d09884a1240360601a411000054640d080c051120710b00403050348083c0c0304c5d81c10401c6821035403115481113440415040300404c54000e401c405851039014401155450a1010500009040d0b008100c0014a01b0950003009240000c10044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 426004280 1250 426003030 426003041
    0x91206090f24060102010f020408010f0e06070e041505030d020f1605010807080403020106090623100509091b13050f03070501081501020c100504150302120406050c07050a140f01 78
    0x100e9400301e0800000158054a0020560000c3c05200002d4010891410b01040346c00c035400000540e035680340395442600c800c2c4600080c40010000500d01c51401110040c05050700c0d000f61409107031184069686001e010b1984005880004c01703a90b40c0d5880341c40000c0d5105c80e0011241800d10481060702d001e024511584000e80324180d42d04001580c40c4401030b2100710001e001142190340c0c5135800907100605108a0340034025220010240c09004141000140034000546110300e030103100545109400c40102c900548090b15070400355a03401151840c03260f407507020648480000504800c04510a14514090350412504825034440510502d540e80c081406040d01140241002c20300f2001d039400d01c081010340503c1100c10801c0000003161610561b01116804030304045810f004064100030400030000140c80c1c21400c0c0030712040d10183c50301d000f40003c1c1105544102061405e0740100490704625040022142c1c00796862400f01c007020b20303030005082603000c0c08142c0e80d00510b060046 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 426005530 1250 426004280 426004303
    0x1c0308010608150d030f120e0a060e0a06050a0219110a0206091507081e0f090f0409230d020a11040b03031317061302010503070e06091206090f 63
    0x814545a09000d0700361030701407014200c004000107a41035042d103561040301181c0107511070758880e0081502c020380600f040c01c102c048401c241342002d54503040d4240008204542c02c1d0040d001250707201c05516480c1c1014852400600701500340b000b00048403140d60020500241e084618080d49124200101c50317110810301d4103000c0b600030201010242c603011024003440000200b114a403404601c0c080d811517403210008944600c008984c44400c0c3c48694a80b5040580642505180182c8410030511500c280c05d0769921903004014503c0785610f50358400d508040d40a5180c0581501000101a0801c40e10f200c10f0154803481342655400c0b4408141c1442c5240c1c0070303264101c0b10102c50104005842c2d040c8149805100a100080400682401000c010400042d201c00e07441e0f4404903980c10100d006001002003c1b90503d8500141d0b4004103d0380d01450625000b080300000e400000d0143c400e5101007a4070419284120300f003224003040c140d000d01000c000301c807400200b0103061600c4450f141075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 426006780 1250 426005530 426005537
    0x80c010c030c0b190e01091e05030d090602040e090309041505011205090123090606191e03080a092108040302011d0a14010f090e012705040803061c03 66
    0x15940000d4a15048a6013010403031400f40e650049103505035044400d000c40c4059542e44684c1008144070300c0f4541c05924000c4102c03132a084c0081e9448407540c1c1d1082052803042103603100c0e495414405242d0588019218000505409040075021590307640c00c1440361354415481d0440440401542100400484070103071203241c846212144400001d1030000e00f0b8051b195200e00c06c85480140a440c80c2c2020f05442c40c0d03007641d81c101050032038a00f4000415031030041030b6444042c50120b102032990002ca400158032158021011071541404642e941d00c024152513006c0380ba03030301c5c65801a00c81c01c2903034490020350036803c0003100c11520301211002c000e4070403a020171040c000355200329810900003007a5504d260510700140045029810550b11202c05003003090400c0a8035a4400d02c6640688074501c0c044104900f0035424006040042c8100c0c807005880101c0d41b14555262140c48013a000291410401c5143c02c1c00c000210303500441c0c84510440328103011040b04030420362641a0641c2544d0f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 426008030 1250 426006780 426006797
    0x115091401030207060f090303020c060106050a0804080a020a0f08270f0d080f0d1b030e0c012001110c010605060a021c11010f0b090c1602061b0609030301080c010c03 73
    0x3001074000b03500520b026211151290301c0300c40104da40d405612610303403207540c00680c0e40e06000005400d2050607040801005820409404200d81c0140c0d11500207070820091641c50000742c50030303407a000c6081c80040c0ba207541c0030001c90038800717480050031261030701480f502c1d0960b004c0100e14005a40109a042d0302c03d0410301d1590a50420504041030a8460200ca9107040306003201e03403035240c00841c03003c1d480c0d0743c0b90500d0501c600c527441d6000005d00060b04051000314400d00f03055413910200c41c0c049041101091800701501800124004161800802040807032440140003405a02c010903182482d802c010700040c0b241410310441d903a82c3d03402e501425401c11200b10f1030b051155114442010400c02c00c54030300103a8401c1c4104851492144c60000344510610180320351040000c0010300c49250038001041e103030400302482d280682d411603c0c29a9182403240044142d5900300c400d11080c8601c500300b00d05400c00000440c1600c0817042100c071025410001100c0d800644040100022883d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 426009280 1250 426008030 426008069
    0x5030f10020703021f150e0606090904021c141207080403142a190b0403060f02121821040603020d060b03070306031a0108060708130606030308011509 66
    0x254040c102c124803900c10748894000c00540316a9604841c20045a081da440c2c5641e0b105008030076a01005098041100269145ca180001e80d1405800401405040400001000c6681c0c0f203400700104640c80310802030341130361400d000d182441040c4402c001031040c1c00313290341307985080410340d45002d6001203401c2c981402c1d5660034400150503583c480e0795100d400312000c0400503803004500500a1900c928400350f140c89c0400854511007891810b034007000700b006002502c4180100d5003565041080410300454008044c2c0007403103040c80d200500007140041c448000c0014400c00500505c85c01103a40d42400d50700c1c032103920104200b0201003c030741040304005c42c41c0280c02500382039941000c001140d41d512080f01c580c9910842d80700c00003035580c0c0c2c0b0900822990b095158035092401114903060b60424880c04d5460602814a800b8041c02c4000680b0044210030040d08265004105109940d0b6a00d0060003100302030080a03598130901c000d100c69584900b05045c01c0b1419540744050380246c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 426010530 1250 426009280 426009313
    0x30c1b0a24200a030b0406062c0409050d120228020c04091b08070b0d09021906030b12010e0a0b060d08030c1308190305030a0e0d0f02060105030f 64
    0xd10040c0c101c0e50b40c45815101d10310400446005029821210140d034803020098020110781016416600c51071800e1020f012490b8029000c41030651224540c9e100b8030f2140f035010a54400340304100e507010f400c0c01380b03800400030040f40d030b0441885240c440142400c4031001748001d03401491040c1c00c44105800030f40384003030401a440030a0810a00540e80e41402d11808641a204500400d446010030061a0350340b91101c00c2d2040001c2c0240c20142c0390340c5041004e12462841400c401041907900e8141078001d5641c1d90141c1c01d0100c009100c0343ca01643d480c00c001e005001c2204030030f80b140341c40c1c201d84a4401010301031031030f4560158015115000e116501c983c64808050303c46604060340b88c0c2c0345030015030074400641c043c034582c1000544a100c000e201004501041e003001c0300316003140c0c1040306112215182d080d82d0981c0b40c24015241d9940950034001080c4030b003201c0016100d180c21029581d5000b00c062140742180383d00351201030381c0307039400d25990340c000881400c40c80e80081c2c1c0c1c1c0341d200c1e0300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 426011780 1250 426010530 426010583
    0x150607020105040b0703080f010b09030601180e150a0501090207021f03150e0405070621180803070503040201090f05010f120204080607080910050c16020a0b030c1b0a 73
    0x30505205007455200c810a00540e00100411004201e20605001481004203481c40c01010452070140c0380007810301c04261154010701c83d45203501740c600984010280c150b0024410065031070200d0345040d241d902500d00480c4107030780303c11406203420008169002107008507441a5005000c0542c00d071030040d034000442c001044654100b55843d5520341d44030317040d41c038000001e05401d10038a505003442d003426418010703982e01100500c02480b28240341e607180401180c24a50044100240f246100c40040000200911005000140020410a02c290003d02660181e4000c4c0e840001503610b85000c04000c4015002e00c034003203000006038014080c07064445e0a20800d850744054101a600c42c601840c0040945900d404200008200106e0a0040050103500010203409000504024280c1460351040700704500e002d141c0c111a030025034440c020303110001d051110200c2d59a151603048204503402000681c2d032411010130410304907400c000b47c112107203078025503200070200050a0101100c00e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 426013030 1250 426011780 426011783
    0x40c150c12021e010209120303041e0510020409050a0f09031d04021b0106150f0906110a0c0b0a020c2b0f0f080703030b1e040c2a0218150607 62
    0x30560b400d0340700c9140a0f0381c402c000114454009a151180b9104110800c00c9a85c8107411580c42071040201081e05400c220b0005041001c41803001d00850401c582450b1441d030303d00540f240001000540c13420f250340203511502410004120740b1103c4c2c0c5580c01a650380c400041d00080e403070095008450311031803000000000041c401441d102d20032003251032503d401d03100008540d545071b1040108120a00204680050525003482c2102c05103070081e01e030324940c3c02882c007081102c0c0f40c10041c942040008220b19900038003500c50075aa80c901e5042650b114446120040c02100100d64150818175489031110350258580407840da001010000d051100030310a039202001d1055560115418021301c1d085640110b00840d1740307454906000d030640b15040c550134080e102c031441c03108800001505a2035009000c66001c910014941e404484e031074120610183e0350406241d442c0307001c10f5600002c4c0c0c02240f003030b81c4505084600300705e44214100201c40c071200c070550354030b0704001600d0088010140d45 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 426014280 1250 426013030 426013033
    0xb0702031c0219052808030c1e0c011d030408060a05041703070c0201200c010c02011101150f301b0e060406080c030c0906030106080312040c150c1202 66
    0xa01c600359405440f030301034407400d45968210861141180302d031069030000154800d40700315100c8840d0342c0c0358000c52000030101d03001d1110100701e08409a001c0f15004400c00f0b1100380c42a201c042d82c006443c02480743c6929201a60003414540b07040d0131020003958100c0e02204040c10003503480f024070402401c00180201d550420036924401e006e0b10300c002071030140074140c2c0c4a0b084401503100140c05d51004000d03140303d42c4110301062042c0358000407c01c005900c00c0c6480022480f8610050b40c508031064800364655003010025810790a401d9640ea040b1103424000d40c44c40c3d95500180090b03c41c807004030315095888810f025003001c12440761811010b115a0004110a0814503045980c03802c64002043c850b00c10f1003130004502d0702d0700404004d001840080c001d91441d01d8002075480000200c07460040c60781c4070001d00151f8003075100c00d005000c0d4030b003581d03a1143e00c4245200b2015040742d0440e1a18070801000c5180c00104003548a11007440d250380420380e10a407110202510700d2000c85085 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 426015530 1250 426014280 426014293
    0xe0a030b060d21080915040f1a0a09020f0603040203060c0f130b09210d11011401060305090d03090206030c030a1b050d0e06040c0e090a0605040c0501090b0702031c02 73
    0x500403120548a528103d00e150f2505441c2c0000034070300003014009031255405204544580d003c1104042d400c00d43c0020404a01e10319468810701490b205101080812540b07070801000c0485500641042c0d132089070300d200022441d50401205004c10744019402da0710000020360048480c100520000d00000621418610304030700c2960310100300e801400c40008080348103130440c20640c0004060003140004000110a840c1d0b026030f41c3d0a05081d28001c100300d41d19640c000c9207082d40103003400b2200041e00c40207580c48242c0580038040030f680113480b078072480101220b01c0e4480c0c40750000d0f05034000c0c00e8510b141c49040341d0710307010342002d03100d03d110594500b4a0055a4442c512011754603c403601c038603495825440010b011690350810030023885c0c00820070400090f5100c041c10317003aa076440e100c0781640c1d100c20310013900d003011014005180a2405080c8000c0c005141c50200c1214801d0b43e540c0f092540300d208800d07245c002c4980081d055030102c245884110719240e8980311028035841103501d03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 426016780 1250 426015530 426015533
    0xa0e15090f1621060e0702062e08010504110f09070905041a1c05070b090607140a051603170f12060319030305041b15030902060f04080f0c010e0a030b060d 68
    0x100f01c0b000140d501405903541c40c1003280ca115680115400461030004e0880317071406010040600e414034411070b540c0c240030035040121214641005000e400c4000080015103410315100301104900000c1500c1824030384e8001000e4a405448148140000e41c3c0e140f10b0246054180405494003000000b00101410300400807519406054107400c00c0100b0760b100390740c000e0b041950900c01035030080e00700158100a00102c40d2900011511943e9000c0685508010207a81c114100460004000d00a006400b00d0032504885503070600300740da000b444a0035a601c0d075022200796070320a094070446200000d200d860071904580d201c03140c2c1b042d130140c01d0360242e1940f00140700c10701c180c6242c01c501203aa0351050005000503400051521510740740012200c90500540c9607030000c03400e44100400d505c4111a008549842080c0c400513405240500d48454444400710786403036503031000d03003081e100d0b04280c0c505540c8140340340c0c06c2c00d00c4080c01455050703003503031601f02c0d1420008000a40104070850300c0c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 426018030 1250 426016780 426016817
    0x519092a051c031805010f0503040f1b030303060b03060f01111006060507031b0206090909031c02070b0601020105040b1501030204240f0e010512090c0a0e15090f16 72
    0x840841c0c10244000c010b6071030083c00c104044501e800220b20f18520034026071342c1198122000781c0c45420401c0d140e6981c2d00d41440e1020413030304002c3c810542d0a450461040703c95541405481c8603440a00c41142c54030140e41d01804120380950380b1640c4443d00c24140e5005d00956100401c099050f140388144607c0040192921030b030000e80006c00010301c40c0181503200401c840d0400390000c04d600380400c07980000d14140250020f003072249809a0205140e008108112030020584100e041e0180c150141c40000942000e941511840c6a000c0010055803040c4103003403080c0d82c0030850100e90b0310751050400e101c0340a900b0300c5050540c20003000c1009070628075403c8807850041d0042c441c0030280c8034014080b21103d12076400340011000301c08000da8201043ea00560201f80c2490380790b03078814486c140707004c51428a03035800c80d40204012a2060418148510942e03000c10324902140c207440038808910301c04ca540c1c0e080b0108080100c0c8010324048501d05e840b071064a4001008090840c200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 426019280 1250 426018030 426018049
    0x1b05060f1906060801140a4406010302181303110f06011e1211040203040c0509040605070816092c0a020315010e1f09090e010519092a05 60
    0x24404140408010030040100f0074100008501c00e58080c00407524203030030660802428041000e20000c4a0320111001c40000b001c0020b5048d07808011100c0030071007581d50380380d04003808240c1c0282030003c003007580c440b8045801e0f8080d0403102d03d5106001110340301103682e002000c089a0b03a0f0701500c01843c82c296010010907018203035840301c0340c40007960318181d080002915400400c004050050b440042185851f030089046800e46016a40b030b40c5030300c2c141d2b07000e210759001103600c1030b609414003061010795401244507905a071120030315074445202e0000040d000746d445000203003281d0020b200350400849201710456054100d01054403c031810f543d0413880446907030f144517601008005001c0507031000303103e00030000c0c01e1689800708140080b0b030044075101d2010131010800c03c1002041446102001c00030868503204001080141051b40d0103080150f803049024807550710600003460080c400c034410103a02c02619140c40d02c10040ba815031510f0061301c4d0380061244a0009043c3d201c0a102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 426020530 1250 426019280 426019289
    0x40c03022b021c1b0c0503030103030e0d0b07080a0e070b0715020c0a05030d0b0604050109030803180d0e091e010317071b080d0327020d060603030f1b05060f1906 71
    0x440e0039031000c2188407000c3e0314520b403881001a20170302d9401260000c4101d0741500d4152912256680e2402c0100d0081e5105040080c40308103000c0c2040100765120380600d0080003c1e1030144001c0d8150b09507580e07550642e0254082c902020451580002c2d0b9090350300c2c605510300d030380250502280f43e00d40c80c18203480d0340d010790b09a000050401c40e504110310503000180021181c0341d060509040008010b2951800000d11000000000c1120242080303100078003100d094044554050349010300820f14081d002d4040e00512080d80800c45800041102c052034101080a00e016a880d684428189400031034801c00c03e94070420040340800c5c640c0c3c41e501c4042013100c2826000a2401e0b0708545016541d40b44030b0101403400c01403682e04058003800c180c1c1d9098503500400c40784407900000700d0118043e007004103150701d014000410140c000715125500d21681d100c9007002080c0d40106641c10702d003000c0080054000030300295103c81d1001e880d0f41c202006507208100c203241901020700300c03403542c0c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 426021780 1250 426020530 426020587
    0x305011503050f01020c030d0c020c0904030e12150c1b060f072a020112060504050f010311030f03031b041502070e0a0e0a1104090f030e040c03022b02 66
    0xc0500610404000c0050180d645800841c68071244c052055220301882c42e405088a4582080041d5580b00300710884944400500d40075181c01c2070300c1c018201c40c0509504074059010002c508840010128602882103203094068016903a002003a000700d0307004000c4080049034101142c400c200042201600c80c0f25088001e001c04c2c00d1829015015485c101404c841a44850720585070071110032080a100740e03030a080403414811985810409880790707030412904585082c0c100316540061090041c1200d00030040c3c00b0070b140d00d83c418103480f1062090f80070020790042010a0820410b0060700a00091581000c1d050a03260407814210340388044407240140e200d66814407284003004c2c0c100e508003000034400c209480d0103d10b9079446918824020340713520303180300307400300b046e2036540128480942c020858142c0749014500a13145500616145000300d183c010800501400b910854612403503100b0040f900c1950101d40c8600e1498480c02190600d400748520004008c0050003049040310760382 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 426023030 1250 426021780 426021821
    0x1a0304020328020d0c0902070c05040609141603060e070203120906062206030203010e0601141e0405060118080f16151b020d06021b070e010b07020406030501 69
    0x101031810890003a031806404202d1180d052a504644a6030350465066800844000040c00d05055122040c0e01c890030041c0002042010032800040b0103068420445d410402d103512401e401045a042d5043c203a02c404824010031070302d42d002660401000f88614021030201d403104034001c16904203482500140e4400b1454030f06070b140e581000f680c8104a040103002c64642400001d1169090540c0442c14028503403509240034101d0b00aa07014580150092004070401d62040f0781d136420911501d0b112034920480080355180c05482c50400c8240303071441020303005e0104100001060003809040c10702070440e03c60b000c4041420b0441c0c0003000c4d40c4000d025004501452141015038100e114100903042c407409011103d016404207218a94620308450300000c0c1180c00b1003030503501c1070041c2d0710080307201004081101a070020010301c0500101500502e88540390381d83d03600e15170b000e20441810001d0043c8040080b400c040c2c95200c0c00240040f50440e1b032078444908480b410503050b114003c249 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 426024280 1250 426023030 426023033
    0x70602040e1b0f070c050307030c0f5603060114070f0f02060c010509030a0e31021b010f0b06070b0708070c05030a1107050402040b041403071a0304 65
    0x1000d440d40c010306007001500300300b145042e0031100c0c2c070519444055404021540702c007031000c0c88001c0320207801c0107130071200d00f1a281d00740a05111401d110b440c4994114441c086500140f400f241d90b0601401c200001d80449181025030b04101c1e1080f1204c40402c640302d00048030300300c420700b12800441d040c0b05140d4a0811a000504641420748100c0100004010700d20001d140440e600012036007042c1c0c00c6a01c420540700050280c031030708041d84072641c00d11060064030000800145103c0400d074807040d00c141b000c2c505110840d1410740c140c08511404800c111450359803840846100700103002c00600d4064018a03128200301a40400071303643e0755504090040402c10700c155140d260049505078100305036aa20010008402070061013000742ea140800c07a028054003520b0255540203055980f216400d4000900381c260040140455106500c0e000035141864800c075810b54280002c0113107098200016100700d210040d07030240e0144107856000445404620300780800006441c11283c0c0ea041a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 426025530 1250 426024280 426024299
    0xe04110409032d0905040507031b0509030114091f0605040216120305190b0f1c0b0f01230f0909060a050c1804050612010507090305010e030306030706050c0106090207060204 76
    0x3c8007262116040c09444480d80d42111154084520450340440c856980d12804c4000c1c0050400040104410b03124452045400001034000944250000c1005005c0c0000340f60a103001612000d11980111015002c21001401d038210355482c003980c0070500e5036442003c81c00308d0344041d280100b40c600700e0881d1010015034003c4c850050a162500b403096062500d11180d50180708290f040034190350304007040f170716140c0580703030311030720318018200427034103070400700c00130400c0b498607801ca8101c0b440e00c0000e0600451950540d069561603e00881d454800c001e4250203441240c0b15960310104902500601d40c0c0d9200945100e1004a4090085c0741000810b0f0b0056442c05804400041018400110081503100d01c60102c0032046034007160603100d020100f44984080c0c050a030080d42040308100340e040c2c1250f4114110b03441a0000c02a2074056052152280015940c07130b54035802c0420100a400e1182c006058550180000001e80c6a540c4c0700c0d08080341d01485003125101d8021034108020b410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 426026780 1250 426025530 426025577
    0x11031306090510050a08041506151b050309010e180406020a0909020f0d052805180109020a05220507020a11060705070504230a0b03070f0602070e0411040903 69
    0x142c81d00c00301e950075400c3c05003041c01520001d80410038000b0004c0c003400402c50305d052141d2406d0404000403500c5e0f8908566407800e10510401042c6000810101e40c03200e04e040035a01900074004c1c5042c01c4402c0c0044401d64122040035510500b41507030a00c04c480b0004c1040d020364811100141e03100f24900e40905060150b038448803c00d40f06000c03104400341560110340d00d46056510015941d03070764440d11186c4a800c0d081c0c903100b19100104c91418030100e6032209001e03821400c0003940b0343c420300030b2080c20303540d150130000c0d0804154002005942084050950322090700b01101c485505901411006c6903011515200142d00003482e5200b40403800c00d00c51407804058810915112032903c1d500e40d03400c258414680078503595520600f0710018815625140342c404c03148070f241c50a021070504050603080c4c20003440ba01401000280c0060360350554421a242c540242c00c800345403045505241308014030503a061100c039004110b10f56140e11a00c090389200c0e0700d0705c2040000050441c0107088 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 426028030 1250 426026780 426026789
    0x60906150102060c0d0b0a0b190801050604080a1e0b040c03030813030e0d020102030903010f0b09090a020d03050d4106030a11030a0f0804090509030301060f0c031103130609 76
    0x100410248640401d469045800c102e408417404200c000088012800c50b2003180d0141a0021010603400c14940b1400b80d008102a016130325210240d0b2641d007001a24800ca102d000815445100c2880000e0260032030069528400164010600080e448503030b21700740300321011210350403007a4041c010150800c03242d6070407003d8400131195200703a950703010b080070704002e081c10b2058000707030941021684208121900d20070007800034003110b4414401035001d4950462002d20880326040000e0510301c0010308100c169400034889a420a1162401d586075032001c00b400c1c80c0c0b43d49a070040c100e2506400c80c0c101d40c91040b000400751010243d5036941c000b055015181c54400b1410b000d00213079581c00900022a181c000041000300d01d040710010f8500754101600410700f030802900d6000b8040743d10060400c035100702c2000e01040e9280003049450b48000d0190101207480b121031851081c0c0719201d200707411b51007414a40c40440003121103070320f15040000d01c0d5030840f110030f00a0018a611040f0f020081 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 426029280 1250 426028030 426028033
    0xe090d1b1407210807020f030a02030106080d1d010804080315150301031b030308010611031225140f0306030c0a080607120504020307380d051609090b01050c060906150102 75
    0xf4450795840b051244100795000e442021010840c1d60b0070380d0240803400189030b006000304203a42d43e07002c94507101c4020110355000f240d0814280e11030000003c40180080c1816590002141c2d169542d035002031300060302d0000450003010b12188207454000c041032101c481d040f040d9072658594501404200803600c000240917102420420010f0b4200b00e41c036054540b282813621081030713a8810135155000d50006240055031401c24030612146141d000c1305101075070440038904007210b06003918035441c0840c40010141c000c01036603440c12803050180d500020002e0a813181590042d0004041004c2c03600000d140360001018481300b55005422944003d1903084280880d1070710b41c00103510f40009110b0306042d00d681400341290800348041c2000c54170314484640f45040c14800b025a07142c0c118074a500b03401403034000030404a0000518050a07050345c1d0740ca20304103034102380304400075080c41c80c0a03c0c1804014030080e1701e213007030501c1514441c005040003081e151801400302c016046035001d01a065 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 426030530 1250 426029280 426029339
    0x1b1006030c1d0c0c0102071a09120f04050f01090e0a0b130b0a0302040207230307030807030b0d03030e030409021b0d1b031b081c060e090d1b1407 64
    0x40200040301c2c0b0354002103c20800c0d8484140d41045170180c41601c130300410000340c19100000c035040702003105010f512080110303034500000c0000415284104a0121040f11080c1b0003040280391000e91100c4111b410f00d0600f0080703588000340700e1041e5060f10812000c90315400c45403e0350030445160300f814a55001c0910840c041302004c07500d40301d141e01000c0e00684c0c000a4010922000c3c13400500c00b003030740341c0e1510300b186c443e0349604d5101e4101c40300440c0012024408102006d00c240120310a0210080c6864994002e554041d070040c11606c10444890206000008000d0310f0b07032010300f001c0600e906041c05160110100075040c0051100c0c95800c0c8045440100b011109030940c00d805540d050801c1c5c019844946d151000b08041280b004010b900000744114030014030a4800000e41d003045414014941c13502d0310b0b145c2c802000c41d0301c1401c03680042c0c600d815040c2b20f506103044881e4424040d500c000d0040d201c890b00384c0b26002e000c8256034014181044241030050701901c55100c100447d495 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 426031780 1250 426030530 426030569
    0x402040f050d08120c0a030c020622050111130501020c030d020a08030901062102040525050f12041202071a04300b07031a0a0b1b1006030c 61
    0x54590940c01a1800b80c400010204100940d0200b201c1d813580362030b007412055240c00c0d6038000da41c0d44486104000a03013442c41500e452400010140d00074550350285100d00c0200c0180c1c14030003407600105548941d26076620007041800c4100800b84440c59040401402d400d001c0068980032030075002501a601030701541c0d10340b40c4d000c10700d400126480301c0c4080d41c0c3c0c2c46001e0003501502d0300350402c03180048030000c0300348003401141c54004610300c2540c4c2449540c0d10030710080b00040001011041e4490103802c40c0201910540007011340480c52414181022420105000c1009d0304840c11507078655080303409140350b81c040092100600703810140050186070a03900d508039010300d1048100814420314071241c1c8559001d40c50300036864181b80d00401d00003504004c60a11410b40e081d1020030314050107403951142c421480407004202601d1a03811034038050700b6262640c00040c0c95a0050b1103034001c0050004144030042983c0b51940c8081000760850600e0080341c00d05522040c0100390f100500b40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 426033030 1250 426031780 426031799
    0x10051c1a04020105070611040515030f04020f0301090c120b01083f0d09060f02040308160c0e09060f070806010c030c02010302040f0e04120f0c060b0a0306020a02011a040204 76
    0xe480c11203011054489031a140700603101c0740102d0030010706250614400b018441036200140085600440302c080f81e20300000f0008000384016201c0b44191800d8034006005400c0c020807e2026120180c000130317504ca610340756100c00c00c180c1e400c541d442000181c8080d040c0040e5000d818051b000c0c207070250041000c01100001d40c010040340000448100c809580341003c1411480003c074402c00308800e50b03880080180740018400d4a0b4101c4440e45014400b1107900c4492003602c0507250b00190b440c0c035000140715681860301c0460b4088078034009094021405403500345407540620401001815217080250717118200910003000401040443c1c002c001c52030303a10400c4402d1958050900501c25026400120080e00c00c6420502080c807413040c0c00903440501c2d80825200b01c1c05480121107a03220340704120f910b459803003030440000d210050040e01040c160707441003803081d030300030b00d010f0304103640c3d58400381030760407e51030400075075551a071240505c04801c003010380b0b90b41c040f101185440d05204807003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 426034280 1250 426033030 426033053
    0x1209160e01060c08130b03063303040c09180c060f0c0602030910050c090102010e010209010c170d05040b061f09091503210215060303030a0c03021210051c 68
    0x41c2d080000300010f05007800503940498429000c221014091141c0f2001018031a500655859009041c4a0f0b030340030910b41c4c6a1414a010008600c10300840c0341242106422030f000503000791140c0c4140b03840040c0006103440351110342451140c0e0f0054540302d0f8180f800312502d050b03000038184004040329409490380001c4048141e64000401a125144c0200d01c500e0150310540e4440c1b0f80d0303c0c0c0300074402024111009003040c0702c400d81c0284036030420041031500740e0180c03000441c04150403500b08000656001118034181c1a02c05c003c504014800d601c0f00c098507401c0d1015100c02074030000340003541c2404003000780b88450b10250030b1a9000741d80c0b0b00901600b00e5101e0101c010b655410100410302a80860310300540d002104000402142e80c0c050700c0d001e4014501c5d102520418008800e40034070078081c01d202c2c240007400b843c21660350021580c080c01d4120001d800b09603007045802700201c7c1c428038450040d41001038489480b41000148801c3c2c00d221006000b00c1109441618000b4256100a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 426035530 1250 426034280 426034289
    0x8150102030d0c0210061e080102160609031b061a010201020712050a021e01021308060115050901030b0d0c030302010b040908070204091103032206050408030a231209160e01 76
    0x90f103e00344010480c00d04e241340c0c04400d151400e01200080046080e02d80d0f0780d518040c400c1c0c007810241d442c03000034200d10804c14050640440704034200701180d6580e2106a4981c080e0031314070040211a246203c080c007041c8404c80302d05994401e2108400305030350030300300403902c00c1c0000c624141d03039501c5200d41d00b103607a0441420060001500c0f11760324401e100755108a4061200d034091540d800da4098041d4001440010900321000b1001030380e6800011028121810321046d0040c1001c40b0000311034660007686420b06140d00c802c1d10140e00d441d03010030180307a14050400400550708626009007590194110385101c3d50030841c541c0041000041295121035040310002404101c4c0d00d0729002c2c0c00c5c1e410070f409a144c003010440300e400824210740034907600191425035080a89410003a0340d14000c50042401a510a00800d00068080e1622410305050111b4030540d0f101840c820b070303409500c00141d040d003a4681d102030011601042100044c84c0c10b1060700c1208407810605608280a0148036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 426036780 1250 426035530 426035557
    0x1506020724020c130b1201050405011a0a0b1e0301180c020105240310020a0c03110601030b0f3403060e01050916030e1c020d090e0601180f0e0105010815010203 70
    0x941d1130248102d5100c1100d10300040e054815100110b140310780284011501034a041d401c011b0030207080c00c3d140c80300d046a15802070a110000d4100140071b201c0d500805200c0d8a00b0320f07594401c042006900001e1402490107048181c08804010601d03000e440c03200d0495800e583c10720041c00010b40c100c1181001c02a04c2c550003040a40300e99000a10b409039041b041d41d03d16100041941407180c2c4815111484c030f0281c0c6405400440346160b00b643c030301c001d220160072518044080f4104803140041d50b5008142c002000001a151070704240c50054551310210400340d4402e01d07441800d400d8050b140052070214a00d0005615000210313020f240c002740111400b40b0003440c41403005009a0107484100401c008649080038034080055244440d00c002002521445141e5048144110081e4083d9802000c1d0929603840301c00040d586241c860f1000d0001944034000840c41550100080006094240c0c1c00c2e062540b424001400c1e030500030b001d01c842c010420f611504280d800004444040340e20b90ba = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 426038030 1250 426036780 426036799
    0xb060a03020a0e0604090203091501081b032104140d020a05090402010c21031b02070501080c04120507140a030c060e060918040b060a14060d1506020724020c 69
    0x20422143c003048074441c540d20a002280c0416014501e030301031403084505c40110b079005501110049529602485003800c5030b401100146449040c0c0000742c50214005011640c10340601c00c4054003c0851000c181920a000b01d42084500190803a4005200c01600c480c80028100d802040001403540295800f40d807000c0d000c5800c592040615010396504110204101070404052540e0a00c0f0490900b0019090044102c903604811104401440350358000340046482c0c0401995440802041c0d648420350500000511241030340c041000540f24a010f0000e05090580c0800400011070211380103040078142400024003190b074603c1696802d05203404520340074070001e0b0491281e4104182c0044036440d81c500d01100c04103940d4007851144a1300140d079528642845502861031240141e80c0c0c0b804203428140d400d0040003015070014101000c80e0b00202c10080e021400310650041d001a8001c2004220070301c0d11231402d00500c0c0d400e40440c888408038260080d9213810414403a03210f00c43c001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 426039280 1250 426038030 426038047
    0x150206180304050604090b040c0e0d203003070201090315062102100e0d02060706090602070f030807230a02010e1b01080903070218040305040801110d0f0b060a0302 72
    0x1c1007658000c1a006082960340c540300c0c2c040c400a0102c854840b80158140200c80548a0245140044101c40030304592040903d0b42c4840d01d074580100c1034508612540d0f94504207544841e110303a105907000c02c41d003030084140e40341e0030070000021000503142c1d500f05002c110010717a800b9038400704498100d0240048600c2080b00d45005050940c41980703403800c441e211660511012140c40401402100c0301ca0889445017001d403050350108004c41d5000082c400703000c00621301140030301400d5000700800105045683d8929040340c1c0440d80544d44141b01c42000010164400e03102d41d488191441c03c0c10031a1241280080081104c01070403101900c040743c4400c0c078074800d611030044408200c0c120307420b40360001144d4442c4080c80554a0001e108040050403105002049508090b4040d11211000102c059510000e03c0058011001c00c80100301c0018181070034001d031200d10791103020392681c5440340c1e040002155681c0d14407034103041c00c1406480960356610280c031103016403400d0140c0e407102c60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 426040530 1250 426039280 426039283
    0x516050f19080601060306030506060d081c0f020304050a0507060c03050909091011030604150e060603061507050325020315060409061508010b190902181806040615020618 75
    0x342e000140144502d500005e10141d054020b4800c8078000c0080d555181c950006010409000940280c00c0140800014144007101402c20101c0052910300140022403088600c050364401c0e901694030b07174005400c0310b082c888140103080091503a410134036105181a900a171403070259001d1140701c2c8450500085048005002c88603404800d24020040c2102c212036101d6650426209140901d00d400b555401c000f00030780d8040e00742c40754070901c0303829a070f10041000040d034402414250000c00e2101e2502000c05140c000c1d00145215001564403000352846400c8030300503022a0f1a90142d06480110150b1404551000c4890b4a007000c140f46603541c0012501034072110310002c0c00f00349001441092418150a13100a0700c8580b4000c1c440e00b8000c84c00c2024011401d1000c2c1c0c81524a44810040303401a80e0003400c00d00202080001030b04180000a05c40c80c408004400900208104002c05e6207858822800645910720038580707070b00c084031002035460000401411110f824141302a1001c00b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 426041780 1250 426040530 426040579
    0x907121a041d0c220b0102011e0501030b0705032502190f020a0f0b040603020a030b060f1308070605070209100f121203020a0e010c24090516050f 64
    0x41c000344450901c0826900362078081d0200780c4080e000310f01000070640307003046048050181e900c10110002c040c1c0349540004060350005141076658a0204c80301040600316080c90700032440c10005125071441c00c0c240c0d030101d0018001c10420804100b00300c01d00d41c010703031080c075001ca041040481d00f49243c441a46071071041102c0300d000c01000707030700b4108000c0d02d1010140d4141c8261507011020396610522040f507005406a040396107028482482064483e80c080d2041001d1442d011500341e002c14041000c170392204200343c400d41000298101c0340030121024100070509007000340001c0e8902000140640154400240314800c441d000c2000840701803000409441c0d115480045580c0e94021003c00e002c08800494030800d000740221501c5000e4400d4401040715900c0701160b08840030700448041408100854040440300203a0132200044140758044141120000510350704030b0a0545c601400310481c1c00031103000e82820300407516680356484000d50152039900c490b40e9034076440401c540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 426043030 1250 426041780 426041831
    0x60c0f031509090c0f060933030109020d05060d0b070f1106090303040317040c031707060f0b0a09091101030504020a090e0d090504140403080a0b0306090a030806090712 74
    0x40420a2008654010940841600c4212411714040e10400c00b4000c1a00a1100c2c02d5442018018040031485040c0410b406417801c0d400000807280401c007180a581d0401e0b00b2801030180d011409a149407101c3c440c540d0016021280d80060740c0c503607039035020700e2032000380004104840b4955814806001300c8140350503540a10503600180f4002090507502d400480e403d800181050036003e042030a854251802030740c101d4200400b09041d5200c6034940c606050180514020400c21031b008292a441354108000344403c011850702d4a1008000b0103d00726044180380a191911000c001824020056417584003800c01207015511800042c00d0031255034007055405007460054030031554007294050385601c0c83e80729030070190340700c00500003111044200d956014811401280c08680034030703130311540300541b80c030040340b0501c510001c641040d2050b2080300c21944102c030200201a04003a91540c0190b05036103400d102e00e48110020060040a0791040b1f00ca5955103403540c164900d04007440201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 426044280 1250 426043030 426043039
    0xe0307060f0f0b010504030503180d1b0305071502060f04020102070b0a051e030c31030b0a050912190201061208221220030601180c02060c0f0315 64
    0x407044400d9040c06084011407500c001ca00c1c05400318510340c0100191015030f40c11500031405c0149005403419800c00000d10f1952010309180301200060b511403464034408150b2403000f8406203585000c501d817007041d4000d05104030380004180780c0c09a00042e102e60007040c2e0741144a868895000507030903c00250003008061100042d036040c080c0d041070052480d0700c0c401e40b4649461500d8031420495000c01e0700d65884421080040c2841851010b003c079215500c090703040040e5084d550441541041030380d00031201548290200001ca40c8580318603a07201090102034140b1b40c59081c4030440d01e2040d2610060355410004030708544c24800d52007a4050030304040505000711180c100030340c040d000140c060031340c0541c01d080082203002c000c003000100d9181c0e1403d07080340c010b999038440071303110691451091072482124455081d82e0400c0101e00a2007000e00c9154070782d16030001101903600c464242e000b590b020a0502031020750440481d42841010368109840751a1840c44c402c28205a0407080d0f0311 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 426045530 1250 426044280 426044291
    0x1230c0f0c0706080c09060708070c0506030a06090b030604020a17030c030a03022802190503121f080601030314030403050d0f0f0c090b04330306030204050601020613060e030706 78
    0x308600040c0da506446064413011015620066000b85a02c03401c90701c2c0d07400c4041404a0400110000b001d40585032080800041203519840032401a4108488505c5040d031510401c001d6403a00f803052500b906d806034090b090501d025004140c02c0ca8991142d03410521038040f80c0781da038200500079070b82d942c2070803415280d071045540c20007000303500034180c1c1c0f80802e400302c03801074a1a010070144020140854001d0010000000d810300002d20941c482599640010440d5426044036403180621070b000490581040c0c4150009001c001445a005000c00780c0c000001800483e0b0000d0701c401a84820b121034903500e070b83e0707483d046806002c0c610324404031030b0500c07140204c5542aa01b12119130410b000c010061544250402c0b00d101d40148100d20305804100700510903503003100c443c036003400f1920301c101000400b04003a800c5d44c1000c0d002400300295844a0500071882d050084542100d000d100800072070500204101c000e000b0f56400030103c0399100316203002c1702410b0080c1c5469540082c4100032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 426046780 1250 426045530 426045547
    0xd02060d0f0506010f110706050a0c0512030a050c0a02190609050a15050a020f030604090305040513090501050109020f090111010b0d0f12030203100605090406050a0306020901090801230c0f 83
    0x82d020035501140444c0c802152a0901d42c4500d581a50320070700f2000408a040c50720a00340c0f01a8007884d00b620402004006041c08640104000c03419840e015011980ea481c0940d48034048a80261211903030301c0c0c0410003480d55641c0004c031440d800084010b400300d04182460440000c1001100080103400f41040540500c03c000b40c040c00c00e0782c400042030081307079206400038007244910301c040d54815102f4004103007036083c503a1200018a20904242c1c0c682038840000994040740e07101c1002400ba150414001001028050346004128442d0300b0b5080c406995a0b00380c40780101d001840c10030031185818540c0000940101c030013004007030010402e441d803c0c188818502071803030060310303407554100c180c4036420f111f8402c0300e102d0000c113440d80b4040c0e400c1540448565000e200c40366405a03d030701c2d0128181e80d0340c5403c0e078000c610031900140c0d640c0301d800c0058406a6164040c814507490207400740e00383c12050915204021120785681e460340d0320040c050002d809545114118510041031404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 426048030 1250 426046780 426046811
    0xc0b01090504050c0402040f1403071d010312030b1e041b0512010e3d06030b13090c1404060e0408090a0b03010b0406050306131a041a09060d02060d 65
    0x90165010f00c082c1c5000c2e042100901c401e171b01c518401c241480000c0342e810001611036041c0d003441c81d0b1004003561099541e0b5180101031f60300d521074a210718030031a00100304000c44c0b042c042c1003200981c101800503820f54800101d07010714600801441d08c00d5540c1812603a5259800003070642c189608650200712410401040e039003000e08010500d8090f4400481d46102d0a9040ca200342c5c80310302d02c00c0385124a001211006103008140583c5510305400e100e41c500306820155001d0300340c640e0002200c504103403c021008a0240d00701c5401483d04450308c000c00c10710400d500548000508107120039000101150060940358004015808047c0c180010081000001d02900d51b0486c0e0b03030b01c2c0603a181d2080c48402e00c803e02c0364100c02601003000b0005d050180000c1c640c0004000c103440c0801c032000030000c058031000450307214005c94960046005160038416640c5d040d0f4040121355030120040c002c61134000014001c02c1c441c400c030844410131940c81c2000c41c0d800c0340d209901488140161200038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 426049280 1250 426048030 426048041
    0x2010207170a032a0e0303370e0f011b0803130c05030d0203090f120a0308040507080d091701022b050f0f06040b03120c030c1e060106030c0c0b0109 65
    0x1000003400e010501800040f0000c01a04c6016800f41d1030090800c0c0701010384403d10150750f29074040c00b080c0700e00c084440691841c150400340e05131303100340200240c2c0c0c0104204140c440c01d103014085860545110340d02e0703808000b0150242800d200315000c401d001c000c0c2240c5000200101090800000c1100c41001e90500329122071050300030070703c4c2c81c2c2c85e482015100d0318185134000042c1c2c0140201d848a00d0544030658212078050141242c200c1c088040d182045100213041d4080b032825000e00003040001c1020400804054004d01098412a00010704401c1e0038406c40c0c0c040380c04e4003036503460039800798119801000c0d03220002203a884481e2030311400c414000d900065083c90307d00000d00381c18240019600c1000307042024400c0f582c8444c1048024128172901a40601c2000e1880003018581c400a00400301c15000860b101c40361542e11914100d000c4180100303061800e081c42e1010480002c1e40c9064648504000c14121a9072104036011110300002070040705055000080103030441d80301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 426050530 1250 426049280 426049297
    0x150e0a050d03050603120702130603060c020705010216060c0606210b0702030a170403021015050f0f01140d09080406030c0f0e090610030b030303090c091305030f0a0201020717 77
    0x41e51128018914194110780049039029010707040305803881d4844006800610403c2c0c0300800d00100307905124200400c0718a1508211400e541c7d034805060302c1d0b50100000e00080409100030012620303400410605901c161040c5018850329000210800c40036400c40000f8141080c040341002000700801205056029004e03201d070703408040868111440481100c00c0740206807542c50b401c444c00c1400c0d00b5928002001902180103101e484e041030201d0f80aa002c1c82d150701c1c007400d003040d07040c4410000c52884003000c7c40d2240ca480071000ba040d0740c000c1d811031418000543c0701604c4d080f401502902411500100511046c00010f01142543c1c01d98040000e64402c3e81da01e24031100890307001d6440c0201c00000d190301119103800184035281400c40c080c0254a1444c0110b50190744d071b03010924642003951026002c3d00007134613009060402e42c27041540701054460040c0d028131f698903007988030f110f550b0650004410001d20017504600135012281c68540c04900c030155070b4000740b030800e41504180368 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 426051780 1250 426050530 426050533
    0x20702030a120f0f1106010522061403012d09020d0c0e0f07030902010c0204050903070609140c0d1a0c16030201060f0b0405011b020f060a02030301151d0904150e0a05 73
    0x5480c000303c0d20590321445c04000480041105900706804c100c40d108680d4032005001d0205840f500b4450600d0080c01c0041c4401d039150300d204580f401c20182907501d101c104804032003070b00e0b00d0108040c000003510741030607105400001e0081d13900d0010135542c00c55010098074510001800041804944010074030412150007010a13a480d20002101500d41914002c1d001440c1d0b41c4401000d441c06d5409103400001c001c2c2100c1c0b4148660399420244c5e0900d00c001e80303d08800e0788907500382c007070305005400540008885030b524205455031846c0c1c10100c0110711700c588800b010001064408004221200000f0800070f241d2a00c03528603000340a06581e005424601e541400b0010314580540709407800d8440584540070b0811540d18800300d04180d502060f139200d40b0203079003a62140c54550051007200c00a0b40607551725070606c001d0900d102940640c43e800c210003c0761042100c4003600c500d440c410000ca80c84d1000303841e21b0234400f0408604481c6030131040e1505000d10480350300040c0d100321080c4503c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 426053030 1250 426051780 426051797
    0x501021e1206041a190f061d060a0c120207030f0510060e06060d203c04030201030c02010f060603091415180a06110405010e09010513020702030a120f 66
    0x3001d10080c2d44403000300038240d13009500458000c1c5003244100a941c4101c001e0310750b06030360301ca42c0c80d40300e00c1d8580e00003804190b403100300408a440c2d2030241c40841c0c0d001d5030600c3c54007018803c010400000a01c0c00741c2095402c0c01088085482800034100558100080c0e100e500d50b0b030b0070300585842000d5505400b040c6480400107a58452000d214450107004004900346604103400308084c014001c45111120700d8110200316a006080140c01c43e00d04610000307000c8442c014010305545000c1c442c0c000707581c2c1c0d007243c0d10213000110b0048900b44c99082c6008241c0781d26000c011303400b40411061810f55581800d0000c02c06691661243d6002070245800e401c0405004034440d03113a80382040e4030305910401e00300145a048036101103580c1c0c4502030b011291200701d65141e50003181c0d000b90008441480002e810481d56a101c04a00094441114106070310b51400c0d001a50061b046019140129004a018029035400380010300025403c07c0b12100e42091081009100b40482002c0c4000301e503054 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 426054280 1250 426053030 426053041
    0xa0515060405100812091804030315090915020d090c08030a090603050402090f190e070501080601170f0a0f060308190203121b04080f011e0e060a05040501021e12 71
    0x1a0a0121001035000d050684031710303140e00b44658800e60203d50031104030921148650340f000700c0d072031145010303030b90010341074145070462202c55002d68800d03440241000d414401141d041b9071507048410500c01e0043c0e0390b14043c6002e10240c50000300140c411600c1c0c010015507100040020080100c4c19981d01da0300a44540c0154200c0340305640294022031210700152143c1034a51a16801c007061803204040f49441c00b0445050f503c261000c8103240d04185d4040040b542c01820182d008403090904113402000c2c3e0400b03804046000f800317901446c0090000c504d0452a5a01c00020717030003c01c1c030a00405440b4203110050b0740c026101000034003213628101101b02d00c044103484000300d03200c1d82d407074060701d65469500307507c1604c101028014004000c00074002c00c1c10800d80c56202c1101c000494030f040789103820810b240c8000c800d80300c0c082c200921240665004500240e00c5107444c900002c0c26141da0070321500901940e5010405101580b542500c400011405000414a82180500e10765a20b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 426055530 1250 426054280 426054301
    0x1b031303140a1e020f0607060b01020c010f02100c11070b071101110601030809030c06031f0504152c070206040b01090c0e0609040b0901120c0906060f050c0a0515060405 74
    0x2403850103050340b509043c00d400b070703010210aa503d00600003444106031001e6080006d050b548001800c4410035620100900c8950701404140c001d82001d0911409403e20b1000194442412907100c6440e6940c07041041501406021704130800b60400088501d00e90301c0307603210012a4440c03842035a203511401541030003980b09805030041b503078400019180340c0e440c665500240d500000d0a26600d4043c00c46c6c203081648030400507510840240345801d80b03084a039034104000d20001e8000794092804c0660300303d0742a508890320412a206041c218644580602d801e20105c2e64283c02c44141c401e00c94103214006500094460140780218181d10007a41e8420b9a0812140040e1018011480f482c9a48440d032821710702601c607011018002291501600c000070304c0e00a0260031240c43c5d69402d800d000d040c004450254000380c5100182001598206000903000d402d00c40051400c201002500c1045880b046c8072100195901c1401c64500e0301c00f150341070900010845140d80110f1900000621000d01c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 426056780 1250 426055530 426055543
    0x30b060306130b04150218040c0c120e0105040302030106060e1002010209010f030b1f02011a01051305190b030c03010314011e0203090111030a020304030e0919021b03130314 76
    0x80b41030150300200d60070703078640240000040059420413841a8070f02403090841c00140105034080a01d0248428490200002c8400000301002041250880000000d0901086402510300c40c1068407002d98032500480750345c411a00003e4040d400c0c003d0001e03c00f82c0104003940d1012084401d8000c1602c40ca80403402c0303010f5181c07850f00140c1c8207404001c0f0140258030100324008080d000100802c441d168910386051840d8070300700103030354542c0b0b0f10000440d8000d1003c20035200746001032403c1c20301072a1292300c82c2c8500a0600c5440990464071401201e5000788008100d08064951649000c400d0004280c1091200391015080c40c0465141154188500309019041f030300c0c40ca01d64642008182d0003500000e2422103690f507a5044400e0740d6001601a5120302d04022003d030f031728640b5240003084219405440c07400f91035480d06001c4088c1c41c00000490710142c80500580b40d0300f250384400c08031035100041807541d020000c2c420703442c03003010540032054a000b00303e801e01000c4101d88156440c103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 426058030 1250 426056780 426056791
    0x50a05010c170f0a021902070810020403020a0b031302091810020a080f0601051605060a0f0b1c0609170705072102040b030f0619051302150d1410030b060306 69
    0x980006040f214800e141550070042c8220018181001a00d00202c5512113000450159001c00010400e42508000580040c40740c41ca09504003841c40c0c0c08100f8100e41c5009062888801100054168004481d004d00058005042e1400750034521151160030100c100148410300403000001c400f0800c0b1300071140e1120155490034000d40c1d5080715060a20000b1341854104281000001650345c00b1184150040f4081c0001e0010760130700c581004100c2d40b03150401034415040040c5482c1c90381c0d810b000d0982101200c4681501c4012038901440101110f110040203903011541411581c02a1805004543d10840c02c40d9451522010808541490300c0c038880c4101d07010440c05001418a5045900840c4d009001c07601d001103440c0c14282003880482c0c10011480000d9462071a04009005240c1c12041c00c03099000d000b0002d03004114001c0045003840070041c4000750b500480b0185510500041004290034070712403e060034078030712a0210344801c0c1d81072800500400c00b58034021890741d0285 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 426059280 1250 426058030 426058067
    0x40308010501201b0405091615120207030503010302192301021f0b010f080609040605150a0618061110150807080c011e08010b031909050a05010c 64
    0x1603290000440f410380c030348040112a209541d210190164040282c2c0048a00c1c8050100d0f4000b500e01c244030490720007d09030400d45d4072074002d01000341140a810000d41e40b04a0f69803600440c0e02c0401e8441c3c00074580180205440010741005141d48200a58181da20840b2074840c04020102c400e104030116004991115071404054454a00260f01400d4248810300655041030004401d0304949441426136100c0c494a0307480c280180c0d0b038090040d40440b1a54106000340f41050801b183c00c107031000b440101803a5940c0c01113100c01066607411651410b000f04403072010f43d124000201070040307021540101040100001c40c80d60700821034208104001002850040c18030030120f805000c1107440da0690381d074071140c0405c020005020b4034000e08a001d009001410301c0d000010030310340134a8030f05840e80c070354100141074196001c140e41c0d0448600760f440686079115404481004e640a0050180e064504900202044401b194180c5924051002000711071507894007900c2d0352001880e800e101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 426060530 1250 426059280 426059297
    0x1b04081915020c0d0516061d060601110304060804020105090418061505060708030c0702030604030507020a0605120403030902031f05101203050a0c0303201801020c010509060304110402040b040602150403 89
    0x4588a900548114546490101b00c0da609548901d0112445081d480c1c07401c00c4420b24000041c40204a1944c102c4d40c20310308291141d400c0401d8641700d00940c010002040240c602040943e03200d0800d8038007034040244100f040a000007504138000e10104000c580701d606155030302542c2d10f40c01c07145500300c2c3c90103415a1702c0d089081e501c03507642e0f0344001c1280c22044418400728026840c00c05c44544907038441c1d00c80a5580f2403074010400302c81002c4e4021400c1040400100148a20710300e40306400507030605000c5004401032000078201622032044600d2105143c0400341000038680140f40079460055102102c140c0303c00181c0140070001d0380c05030101d4000c020416840f8401c0d2001c40246000749000646246123510101062000c8841c200410202080503801400c88a140d5142e1403002d00052030103049a80000e00305002d0020142c0c8105404000103042c06441c02858201d914001c0046580356260103641c100c541280c0100f10061180759040003412a8503000b0501542e0981c881030319 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 426061780 1250 426060530 426060553
    0x703120e1002070b16080c0f0304140f0f011b050d2105041e050a020a06080708090a05071206060506030109060303020f010b01050306060a0c0b07020f21031b04081915020c 75
    0x360f03070541c811031b0b40020401124281034420312100013400380c00406036a40f0340c5800004841060321410140c818141ca0005030455518954800d110280a0916507003c44042c0c0100c4038042030540080c0c054050440580c0301c46501c00c80b400a9000c2241005450480307030540e20b012100c0464009244002d00c64003095100082c0328600320716031261007111806926075020504001c010ba12500124151109200505422850980e8020380030300040441c0c030f41989a860b071318400c3d4818144141c0140003920306001503070f046100a85005880e00c2d5403540c1d110038a034005c1104e4842a00140030301c000105d41c002d0103000d800e0892105956807800e5444032010800182e21005c005c07800e00200d45041b000060741403070f90f144500f440b40c014111148490092501342141e0907020000081e12001c1806518034560a40e038010a1008081c407446111801d071407214841c50708030f0101e500c02e10310b03a001054203d020030b005680c81690304c1c070b043c4074050a100050f402510b00d2100c003074001442607a07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 426063030 1250 426061780 426061807
    0x61b09150c02061e030406111801050c0c03060c0a020609160306021602100309060c0c0b0c0304030e03150108010f09082205180a0b0f011d030703120e1002070b 70
    0x100041c0010402c502d48104100c8038164a2130302d4441101c61200841040180a0944a440a100c243c4c0000500d40b080c580b1212405040c807181c2c20f4180b000104010281440c10083d00b09a0007000c0d01300e40e80f41c00c0c120414005034109002080051251400013118001e001c111000121019216510305a06550300d60000e50001a07564844201c407824a03005a13884003004010071203652070010350b07048182405810b4070182c0150400f8010058080e00008081ca0b0415522403491415503441c1d0301d1342e2404507000e02829000d04e5140c414103281c19144402815518101c035a950003c001c40e40e08101268256074020380042c0502405126049600030020300b41d003900020350525200d500d44840c00603030b105050200310707400c48442d4020400d51029502c01c941c0d05000c111021501c0d942d08600081110400c4031700c101021182e0700d003503042c94408010880145074460700d00c88195100920090010707840740e07a038520071551100071240460011550303405846824503000c0c42c0c00c0080c001e41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 426064280 1250 426063030 426063047
    0xb03030403030f230301151d0d0f050a020a081c0201183207080c06090a1502030c0123070e0303030c0c030910020706092408061309061b0915 62
    0x50803d4140b04408544c1c0c8035021000b54003805550980041d80040808010f00480207044a480042254810170b5215075909041c0300d8280d42c446200c15000040345051401d00c00b1034a0000c2d00500e5012000c1441080800c00c14415540d100b0b03040a15040c04800700d081e1111184030900c0b080820305508041a0b0380c4c9558124120310000300482c0001e080ba1100c1c04003441a21680107400055080c400a2000d00c103514201d8000c651180c06c2c0039444000810381805c61280e0301c0628802c158407014075000b44140d540b1010303800c00802600701100001c0c603103c4c81c1a1f40101d009003c600c0003a0030316016116103541c0c800c000e4011401d40c3e5485088a103c0e51100029240500c4103009004a6076030320700e00c01051034441d0780175100152030044003a203007074001d030003d1107003000001c0098001c14075041400700101107464108190303168074011449042e852100300681e1414130840c4024040a41c100f503002c4100d0307008608600180400c1140d001d101c5004d200440641c5000703e08000b0b03c103c469 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 426065530 1250 426064280 426064307
    0x10b120309180c0c120a09060806030c10092117030405100c0e03122104030219020a09020c010b010e01050f1204230606030d050c15071808060603010b03030403030f 72
    0xf42d407916044c80c000c80c1c40c10503201612085088000340500e69554400b16a00042110341021641ca0030210700003500c0c0d014514460f401081030714101403405100307520b2980203000c100c040084056504d0503426181145d030809031802c0800c2d84047d14040700801c100c0b440307250404041e1148102c0d070300541025200d074003845010850f2412a1a500365014802c1c039040c10f030031400c507550b60100c210400e80c400d1210000240040d10076070030000030035000300d10300f90f540280c040b002541c0c912078130000701c0c1541c903030300308180301c5202164410744100154030100d5041404d803506845602001d004641d00c0c03145140c40004c540c4103010190300000c0020710150440c0c4100202034041c0d04240340542004000a114001c0e607001a043c8885030030244030f1110107201c1e9241c05440c005006401c1aa9411038500700c95003400e840c2d00103140248030300c03101032103e00721600480c0020380d40c0600541d5901c0c140e4845200754a0401080d400345000401c4604907a07158031601e02d040e65100003540e4071100c4005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 426066780 1250 426065530 426065551
    0x8160e061e19120b22060903090e01031101020105150109030212031605070f0f06141605010c0e041103041722030c0e0702060907140a0902030108010b12030918 70
    0x52400c100502d4200c4240504903445116214407280d05284640400140c0706010303a01410422550035600380d071100c110741c0d40140c0c0118103000c8600e000c032462481903122150710a00d20002004020807004000060f8409a00901c201d484401140300f054540c44040d90101d00301550070801810040000c441c0e11030010162070400c24424013401d451401c800c4111025040642e050142c80710310655031011b01404210281560304109025050f54400c8a15101c01c90011800c1c143c1d40781800594012079a000000f80003410001e40c01402c64034020307c150323201e6410070f13000c59140082407050324807690300580c1240030720074440010005c5074491051040c0d542e07000c074040114951580c000c40001c6209120048045180540d12546c2d0100070b0031140454101805003d68100006020b00c10b5640210059400141d0b113000500b1400003940080c001d94004000040c00c600c0c10750154010f04000d541c0c0300c3c10b01301c03280b815548a218410340d580d8810800c1a00750720340c0446000c0603038042c94810 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 426068030 1250 426066780 426066799
    0xe01051605013308060603060a020702041d010c0e010302130611120c0601060e0301140615091503150109030f0f08040503061302150c07140a0b030108160e061e 70
    0x900c400d5400b01620a41c843c9074198040c3d0103000d100041d058002c200e441c014101a003400c1c80060746443c0084d282c01400c94020501105565540d44142c0c1c0e11101d90340c2040c400c2500302c140c5070180c01c3e4180d0072004200c68603001011075009008072545203818005a000c50f0781408010b98901d81500c66001d010322540942d001c1500f10000104044410480242407940c0340000051811a0320202c042c044d1b41001d0041111a00d442802600590102e40008030566090b111001e14010505140d50046103040400200b0021000850040302800010102d040300c203401581e03101801d100c000c20643e0000000341c0032900309000c1686603841800c0d868036256540c4000703442e040040d54813008000c00282e03d081145052100402403980030100c0604140c002603403117803544840c0c4262100042640711600b400c0e81c59010341400f0703080007401591203507110200700e56240e0030710408945141140c900418006c003540821441614010002e402e040d1174411000034140e1400c0646070400d0303442 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 426069280 1250 426068030 426068051
    0x30212010209130e210304110102011b0509090601300f060e060a29090d02040c20011506180305070602012313080304080405180702010c0e0105160501 66
    0x4900e01e08041034440300841d21064503c2254106195122645d00b521710240c0145400744094060341d5100d9001b44540c0c800c0002100141d001d030200c0900881914156900302040700e41110140075084d40559540c215951660010360f54403040d0f9059030664841000c1c82c00c2111100100a0740441c00b07908080b501d01520042c10054030341c00d8104d02c000b0040307041048000e04021a00f4402030017613220250304009030782e0018644440d00031a203080000001800490b50f180d82c000d18841990181c07003000806c0790010018060001200c0d420318201c0c18801c2d404520805004130781480440c081c40d885801d10340842a220030b6441900314004520f1410300101182040c400700000305010b800100b803442c142c1154030311040f02140390b031150010800a02114401c044028100140e00041c915540d844500300000382c0e00032540140d5000c2c400300740e040030300c00b841d0700d90f40d00504007034000f44140420504203498451104d2211400600144041d071040101e110001c0c6509010340300004050100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 426070530 1250 426069280 426069289
    0x90e01270b1f0f0e090105100501140f03040c152604020f1018052205040201110a081b34091104050a0506030c03060d1e0b06040c0306030507030212010209 68
    0x7990100c030f035804120608100b45900f0200340d950190014008102c0c40c81c111030034075900203843c001c4a042142d010f02800208031200304698210b13580c0407042d0703147e1420349000004a2000e014800103000c060341d429180702d004550000144414040c20b440c0c03528043c03d03d00100300c0081050743d1210280d65803500300d440725400030740a20101d03039920110804e000c1140055040c0c55001c2c44c0504d004040d00800e003805031210405040030310030b010605490700c0c001281ca04003210011039540c05103213080403c1282420007000301512445100007010844501e05881d000780045c0041d03940395107180913801600f43d01c4040d242101e101c2d00d01d028581c43c0d096040840d040f1202000440c2c40000d0180590704d030515807240180f4040399803501d50702d024540c880d0f4900029215500500d0320742c1d025800c1040d01d800034440c01c00240301c3d11790400c0890518201040060700e429000343c1c03a0001c02441240701f40159010389420200814800345141d0034844410241d101505455600b4005950103946 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 426071780 1250 426070530 426070591
    0x33040c02070f0b040e01090f02070816230c04050601050c0106030606051f09090b030c0414070e0a050a1205150c120f060a061206090204090e01270b 65
    0x24940e0040c07103040c0c01c1c4011240c0d4080660040003c42030144410088401030304802c2d81500e404040208181181400e91806030040002c01072406601180500ba02035100001d00c040c24092021148102d90241003007601c03400710789003004a504071245401c2c08d82041d070040c40d0400b0062520b18500107082140341d0840d41e461b002100c96a0315a40200018130704410f440d82e0b20540f44070035072103455030314401408119207441424102515451140300a543c180101c80212401070700a1040001c030103440301c29550116065030218480103606140c80c00d024204000f5220064900c01c0250306005490794800c0c9180800c86a51203112008801070340f00001284c003850039030380c40f0b5455807513402c1e01e4041d44400501d2540e81c1030300d0b4400c00035180d0b20401a6403c88845040082c03460515490200c06442d04d6006010164000200000c01c24910382c446400d40034428020806080160007445401c1c1502c6400812a41203800000200316071010345604680c01c5280710b54040354149410f070580c030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 426073030 1250 426071780 426071801
    0x340513030611090102100b09061c02130e1903081f081506100329010309062d0504050309091806040305280c12180b0a0f083304 56
    0x104040f40385501c5580411040e00c06481a81c0c09000d5070900308080740d1080d100401d514803035900f4000300303080c6c84507415040640d2600a03150310007000044400d034004c0c1109101c5028030307104801249040b14100c030411040140d042d955080d0301e07115035070b42801880641c4191010214100e0002a05400c10490b0030f0142c0c3c0c0b010301100340340c90b00a00301300f610b48841880f0070500d802e2046410000342c0c2803003006041d10244601790803240514004038001c1001003002010140b030f000c0e484c03480b0703c07402c006c15824800c0103d030034035480d070100c0d2603006444050301c000380190b0050207103020500d0400c000ba03500108840c4803009a0030312500c000e01d8094240c50580110b00e0003e100d603e0000c19610702110800c0000c680c0e82c0717a46102000420083c07a15030301500780d802030303492022062704c02c49000516680c07100c3b045000342c2d264103940c28242d0040c100c41e000301d0884601948140d0007040041c0c401c80800702188001c1281c1000c403a086403007d400181048030031124006282d0f2a48a005a45e4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 426074280 1250 426073030 426073061
    0x302030619030f03081b030109020d0e2a01031e020d0b0303030703021c0e0d080c0c010c021014090604030c06090206160209060402030c090d0512040e3405130306 71
    0xd020f142005088480094191104c120076030340300803e1060b0b80400c41b07045401c80a0010b070340344110783d2000010924000300038040e0040101c000c0074440305041240c400c001c0030000087c00c039031240c015412540d03a0740d402c2840110480c901c200800b074503030203004002c0044a0104400c0c2c03c5e100080c0c01c40d402220424040707507020a4407030b09039451118409102c256140304010701074024840300d40d03420280300040c04211407840064441d50502c07083e9052028464000d00c00c1c0a2044c4020352541c03c0c0540030094a403801c94a842280707042c0c04100d0054840c1d4015101030707221502c040340c100c03036401400d032095501d50408100680380c02c0000c2080e40d85001e000c02004c4071078810808d034448040c003914440d90050041c485003c007171904440c500300c800c0741e84940242c41031400609041e41c02070480b2414402103000a12000046892882183c0d1840d83c03038244070300442103420b49841c16801c00340141003170b0301100c00d060003400103005810035032907080f44480d620313038a02040e100b4510790b18121 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 426075530 1250 426074280 426074303
    0x210703060516090501020102160605040f0501020429070b0610021501060804030e0102390904050c180408030c070303021c0e010606020c0603040b18030705030a08090319030203061903 80
    0x2c0c1a03100c40301c0800381109100a5103441d084c0800c030b6440c964480c0c8040c15040d035600200341007007440032140da9140d03800070003036450381d507100c3c0f4414080c10034100410040ca035001030366000000030b000b1180610340c800340c41e0415403604824090880c86c0014a001548200c440e0700031b50810403d0828024803903540d0b40c40c400c0c40d041c50018010f04010651038199071041c141341e40d410704251450070020302414912000e035408454500c40c42c12842c2d80701d84e00107801900307000c1401004105000b1109065910000d4070700410f000d9001c3c000201c034007415070213060000c540d080c14908024a0b1940c042c2c0b50140c1801002c504085072a1032403071905545680c0d506262000d51001e0041400500369400a84020301044010400c9032000410050120404100140c4c001446852035400c031869101106d840d000b803490f2240d501d900119032400071410841c002141241c0000485250403480300e4808079034000d040f8154040c3d00060036040e84500e01010310500700024481f10f100071401900382444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 426076780 1250 426075530 426075571
    0x417031314010518030720030304090f05010515040803040509061816110304081e19030c0c140105090405070320070c0b13060c03020a0f0b0f0c092107030605 69
    0x142c0c0e013800111a1582c10500a03c00424800e03403801c030411901390030803000100e650300080d003107202d203420051915140440440b4580d11680c0014103036001580e0814100302c45e00c110494070300403489015041e5004100a1107181051100703d500000003a2a085a0071030074004e9010168080307a0f42c11408020780450154558031100007542e01240c00040e51601d07080001090f20380000c08845c14444029083c0c07900c0b80352080202c0c809078907210f00001185201c1e0f19006241c00004402600d00300a000808100d29a40f044485034000f81616001e00d000a04000d00026204c0281081e05055807200c080144003031403402c8400b002c902003a07180d0381d1300c0c20b4a00010103007030302e401c144001042805a0f80c0c4001c044918a01640c5c0341d401c02c42913810940c41c08910b44501404003c05a4040500500810002c0c0250501404c0c9140311700d6030a0780c50403151440c070301404009552212000ba54106d0081601128500c1d0300c40200c181d40e041030b140c0e2128001d4402c16a595480600d03a10400003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 426078030 1250 426076780 426076801
    0x2803091e0b060603060a060c080d06170706020304062109080d0c12110703120b060f120601020109020105162a030b0f09101812030f0b0904170313140105 67
    0xd5124000701c3d07005043d410300d01c02103041e100c198040c078003c1c400c0806421081c40100350980e00011140e400a000c1c0e1138a42c180d01d4010318928002d09402e00c19504081a5280044140c8003940d190703a030794001094207040c42440781c603103c43d140d504442c2e03100c511401050000c401000f40306000d00000c40d60742304455005290340c540405002c0c803182340035540c9400720010340843d41115003500c0c1128a843c070154000380108902d03c1c805600803400a96445681d240c440645a030580454103074440341c2e200001603080e110800710007030020710204140400c0542e440300468016001e4030940b602d4014005100b2041d500030861000d038901d50a070204204030703504980e0340c1c0c400c0c41102c0c8034195082c020101940c0324240040700b00d06c00d40311a500450750401c03140350300f0000c0e0048100d0003410b1080001800400705040818203050a0000c00703012400c200210b14000c0e50300034680003000c094107240e18120b800203003082d105a40d90b0807101d0041f403141c4541800140f041d030000940c40c2403d03180b42 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 426079136 1106 426078030 426078053
    0x110603061306031a010608060102060c0a0c02090f1015080601201c030b010516060504031404030b0f0a0b090601111e010e122803091e 59
    0x828013408007000340124079080f94000859881c0d107000c4441c02c6044502c076002d0391200c1d000c10f44600105c1d00901c0c803108103203011398244204c2c0d07000603d403400a41b9070700e5103074919006000d0312545100d0074900810031007501503031000c8511005000d00c24000c1015050080140d080040c0f407000d0b891130a100781001041d1540100c802552032030412820340f03038000180c0341c50004002940902d00b1100304504a02d9814028201a42c0f2100034003c0104120104200c92010302c2c280350030900900050340c8031384207401103440c240c500b4641c0d840c03000300f072000007a0174200b21034919140c90b0078454110000703203041e0601940300441d0b6450544000002c001162990748052201001980218901420782c020b070303000b0076019155071583d4051446010728075810f0803283c85c0301c0440b04002c0005c4110038200418603412540720304525640b80c0b8201740860912103150010002c401100 = true := by decide +kernel

theorem cover : BRFrame.Cov 425899280 426079136 := by
  have h0 := BRFrame.cov_init 425899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 425899280 ≤ n) (h2 : n < 426079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
