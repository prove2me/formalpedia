-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3414
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:36:09.075785+00:00
-- url     : https://prove2.me/submissions/9f241f4d-4507-4a12-b69f-04ede524b3af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 613848920 ≤ n < 614028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 613850170 1250 613848920 613848929
    0x1030219110f010905070608040302101d01062c060616110f0108070f1d0306011d0609070c02090a09021c030207050105040b0d0c02010905100219090509151504030309 73
    0x580d240c800b1050500d5003a542d07204400f41143d07100d00020030140c2e01c50313002142d00600910603110005100000b0f82e040d2401c4c080a100900d40150500c1c5548200b817207047c0007451030b1040741e0748444500d1185d120902d4404400c03429410000000b41050326444102d0307035607940000c03010300d44020b149400254a54400c1c0c006000340081e00c4580c40e10750045200600403e51034542c820400340442c0c00303e03103174201411224203c1c4910754982070706480401407a4040c1209514104160400e500018501c0c00010029485200c0d10300501c81d40d5604003a8400d6900d030180c41507142c2c0d6642c034121101501d80da41d0000e4004181440f010710b4050350030b00321016588680e095901c41542d4900458203405940518640b0b0b9408010b80c14100695601000c5c046820307000100e120200360316240c0c10851207402c6914144c0d00080c00c02d04541c0c12880d08100507005042c4110368074204404903c003002c0082c80c956034000200302d203445681d100501d152090640d0703602156526103a180042c0358a07141d01c50b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 613851420 1250 613850170 613850173
    0xb0901050f10270b0a0e01081605060a030b300c090618060d080a020a0b01050402250309030b0118061a030610110105010b0909060f03030306040b0103021911 69
    0x4100e500d0400e4034510100c4803d5a6000c003048a610b11800c0043c0c1c0000c84020100d98804034012a500c0d130b5885800104505882d250301903140041041c10450f0244850561100042061101c0c1d0394000940e4064580c2e407130001118102d00c00070443e100c40502c00321594004081940f4608000d044600da418800141680d12160b01d0f00c081c04454441a41d01d2a44034407810915012448100c2c2c40551082005060700d00c0e41038a521035802641c054011600160400782d084420b0001c0b01c281940142400d590840c6802c5a140400c0e036801c80c0240c0f2400305452800f41c0c407092607c202e54800240d40c0140c44002c980d40d442c0d084444282025a16440301801c01000045a81c00f0142c0c0d5558500740180041c5181d54441c104421117000383d034050180b010903040703246c00013030912502d8041c003c0b41082c0c0d03540e0a081c1c810016640c40040007984110b10102000384ca40d1404001d8a03040542500d004c554550080c005a02a0043d0041d2010402c04c4401d07060300942c1c03124003034684a000c00c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 613852670 1250 613851420 613851451
    0xa08030a0f06180c030506011202070f020604060e011d0108040f050c0406090f0e0a11060903190302010603020405090303190b0f04091203151203050a0e0d12121505040207020307030b090105 83
    0x11130a4090312011a41180407541c0759242816211140d00180041440f410117000c852089900150564010350020380006594000d544100e58005404010f20710f881d800c2c2e507181e02c0719440001c00300e00700107100500944090240b5410450708201c8450f41060040c014400d4548404100300100040ca003c0aa09414450140c504240200e100580160001c21030700d0003c82d0001072103e40c0d40004505a0544100c80d046201c81ea88280410328880c4203500110b0250315500401059620140550110381c00820901000c0e018003a01c895040125180104d12261403030000b41d000c0d0000150b45400c107080c03408000c01c0202803001200802c4203034908101d48000000300400301c1c00e03907006d02015409400c40b25400b007400755020b8030244410389001000c80e40584082561074010070b0003195040150303030f0401402c1d40c100b0082c0d450306011140405c0010303002d220807a900d09441c0308041c040c95000031041d013952028030010b400703541c001002014908201132042d00824041700d0790000c140c03108 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 613853920 1250 613852670 613852691
    0x3020d0f05010f0e07031106090a0603050603100b01081807080a08040e090a03050d0209060403020a031227030609020d0b1e010b04050f040b010c050111120a0e0a08030a0f0618 77
    0x80c444d940c40e4411040c0100150b0303041d651485003503141503d5850b44010180242c2c0728958884007900b024200960307000c220f40c1803050030300d86001011010300e10907d050105008040c0d80c0081651391050217203000c180310141c0b61001a0900d20113030445034184c0034440d119024441090010812144070404d000130650341c449038541c541204402c0100011010400c20007014569000361070901c0380142240d160658a0740040c2d50b0301c95652003240c4003005000c04140c0c02d44c020001040c542644161100e400c10181a001c0302100c0302d00000340070580e0340d48408159240d0031021022242d000e0320070030f901c4c10801c0020724804032490a40c0000c540c4031001041160048082c0d604594014290701d5030710302100c04000160007220034082c1082040032403000414024040c144140002d004c0321a55203102001c11522010000e242e41c220300d0400e07030319451002002070b0f13180c4401d400045054490302d50800c408054034900080e0032206042001c041014a4007040394466800140020882d032a200c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 613855170 1250 613853920 613853951
    0x24020903150f130c05040f23040209130f0212060f010b07170c011b030209010f090b0306010804050a060e0705100c030f050a090506040e0f0c0f04060f0903020d0f0501 73
    0x80310300502c1d030603100001c90004034035240382d20700d01880f9901c5090840d45030000b250883e000d2040018926403038880e9800f208903810b000646500d404003040302da5150680106002040240ca154511060006550240100701e07040881843c0d00425803040131400003c3e45950304029100603c1011100000007002402102169607940d80a915518074041a52400320150030141c5c05030400e5407268007026005c000400c00300410b0000f43c80c01603d4103528000180104116000141444130b407980a04c00d0b2482e0006030795104001740380004d00742d40c035450320074100240342d071000b044181401207140c0c10510101c0e44606448003541c1600060800540840302d51040c4903001e008a81402c8030844120700c528010000383cac0e10390030079074030760380e51a07021801c180c0c09540304421000c85282400100c814408096420440500001e400c20b010350000c0c0c03c042c803840c414a0140407041483c1e04056000342000e100440e0006d240d0f2200c2200c45c01c0c88000d134480d4180c00c4615503e40b01500000241c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 613856420 1250 613855170 613855213
    0x5010e041a0403091206061802130b130e0406050906160c0303050c04051905040615050f0304060609020d02090405061e01050c01020c0d021e0a031b24020903 69
    0x10450001200034402400c0d4031076007000a031041c1c08100b4000c001140e01c105100040540f584102000614a464075401042d140c5001003540101401080035911030240c140c0e403d800d560705480c060b5910140504508480c00711076002c00d154100d807004100900429900c013512494604060b40d0280e81d4062100714052401072001c000f0514000f0b600e00464882e41c4220303404028211000e01c4c19441d04001ba051680080fa01203c201d1103010502c454140350151000510404a0150240001e804040c12038000c408010340c0c0000d0120000e002d10045421010003845000411175549444042800c06903004030300250007a414003003c5a86030601c00c00e0b01d50f101d12050750744d04600107800011103031a8440b10b403403001590280410704907000103200c041100d80d0740d030300248051040c045e00356480c0060032201081a8000f810f9000100e038100d00919034604480000c0c3e041d683c841e1400800c000492a440c08405001002e1800c0081982e0300500c1c6041049086842003032038001c1100a406 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 613857670 1250 613856420 613856423
    0x50721080301180603061805010608030717130b04060f23030c0a0c0602160203070e010312140705010905060106120204051e13140a0c0302031611070b030a090605010e04 74
    0x50400040020224207402a100610100008289165a070b201c04069407146547c0c1504408040006010003600340314a100401c80751020754180305c020749031200301c084400c05d01204d031480050040141585464014040d05001c0c500c540c68544800006002e04840303642d038000b02d0390b0840001c8000001549400c01c107441980003d00e15076070160030b03240640050104405021116100703c00140c40750000e005516034060390709419112078010949062001c1d0b10219090500c42c1c010b00205a02e00b0450803d0303286418240f00c44c0c114009154014490703a0340240440d443e0207110340070043c002c20701c14101c400c1640c030a81c514150702a0107040744254414690712801542c0799000c65040400d00c085114070040c1182490f65041c0880d1082d00c9a8003031102c0d482c00300d00100200d0403120301c21040091854a411800d5141c69401d00f142c0d00030ba10306900500000d000f1000400303104000110240010710900c80d26410103c2c10034002c0c2c6891a07049030401d04210004c03800840ac8040a03101c0ea = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 613858920 1250 613857670 613857683
    0xa02090a060f03021c0504020a0515030402010c080c0d02060105010e0105130909020a051002061f03030e0123040902031617010308090d140f060711100f18050721 71
    0x6191200c269042c81c003058545040c55000c0c000c07826008009406030301c2c521480f01001c12149024410003800390b0258201e2446a0740002d0010f6042c220b11081e25449a8203007001c4e645113071181041c500710b01038503440da43c162090030344005c4615400310f20396049500030313201d07428500c2c1c0c42c1c4015545401080c86102040b440e60808002c8024550402040980060708001c0c2c201c0d00ca401243c440c401c0c880a21015078031040a2020915010030307100440d1120981444107941180d034020204100c0300141c604100c00c1c6035400c804401d1018940384141c030580070719580c0e02d581d21b00b1000690400c580361f000d400440000000490b02850315501c003044000105109070b0300f156540308480d041042c075140c21200b05259040000c18000792148003000f454014a23001c01404109450b149000301420100844c1d10220141c44a000964049103000b2550201e10340c1030074040a001040318490494154001c502c800040c84008540f0034180c81140b080c01c3c8400504c011040700700d142c0b2050044c040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 613860170 1250 613858920 613858939
    0x50607061e090803040b01090b130b010e03011a0a0b0f0415020a020612010512010c091203050705010c0807020f01060b09131401090b03070e090604110d080403030203040e0a0209 78
    0x58100d6105100890300c0310700c40c2010125061186003100c039455030840310070200105220a121404180070f00520100005002c03880011012a03401060107000000150300c80c48131940d168003178040d030324441d0f070003038020858040c01e01c0e004460444d201e041c10b400348140a42c00b04201c805602100c440b00540301000e480c00d442c012102c0c00f00c1003c00b241500714002c240702500142c1d1241c0c0141a00e40105605502650400c0104101e4812464000c0d010740e160100001c4220b03041040c49040f1401d180d1440d030b5a0815040507500c600c29450001c00325460480504006030300000c81901500b5940c1c2140c00c24100d44061500302c0c4d540d03010380c80c402e10003407200031035502d0710700d1003107081c00b0300b02d00049192403d00b80040d61500f030a80108140c140c46403031100c81400c003000002c00802590b0029061820900c004a4031010040c2c00503043d0b010450b000e100b02d403100c040707004044d544805459a1140d4901b00291260030500544c2002c8000c40c0104004520a00035120080401070481c0c03032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 613861420 1250 613860170 613860173
    0x17090f061b0a030513022d0f06070f0c0e0901020d061e060806040b120a0501110406090b0f2208010f020702010917010207080a02100b0d0b060112060f0f090e0307080714030f0a1215050607 82
    0xa5905644400b25180cd240038008288100d088d00c580340101c02c0e80340003603141c0007904070440c1520f903140c01440c0b408200c409420185c03003811a822080300c805042030000b0b40c4801c008100605528000250000e4031480003031012400010904401f0740504003c0040380f11034566021107204a104000004d004560240204126032004208250305e68929518001140018a0308844102d1408429804244041244007401e0062055401c0e038404110710f400340b81c2d400600401d00354001d880301312580c00d0100c060440254110703504603410128070380d100c024441c0300035074810500c5801c40e840c3d8144205183d41d42000030700806525030008194003c1e580319001181c501c5da4000c020680192140130016031040001d07907c801400e80c6000d8401540d00780b41d20402618480700f8005210740c0100003440124541c0801d072904294400c2c08907840004282c3d50a00d940030782e420607856031000084901806401000e8079100b001e0f00c04051141c0c4207072052094030108a0701ca0142c0000080000d01d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 613862670 1250 613861420 613861433
    0x30c070f0b130306022b0e071e060503130203030c0703150606050d180c06200f030307120204260606220b0117090f061b0a030513022d0f0607 62
    0x43c910782c80c100c0f81016194140c1b050b9950850a05500410399a1000000300107081c04500c015000d20042c8104a030400010328840d03143c248203240800c080400410032140c41a0100034080383c0003000c5a46036440f0a4203aa01c0c0c806d01d1001f1a0303003a5442503445034030f00303240c051441198441c6c3c9440342040100c610311f4002e024540e61501c6018016810200003e074484400700191003d80e9035442d07d9440c0414468000186c0501c8400a9010801045010200100b120350040301d928000f0355502c496030307058003c0e00071a00100a601d90b204868003244a10100206018141170100d072855101d0a043c4424481d1900c00d0300c0e042105480c0340c9102e0304154002400c2c42c407042c0f4203440580c00c0102c0c4020350560070313143d4218a82003144403481ca607104110a83d0000150301045034889110045d215040c4628034000e028141c50318002003040351501e003c000345540240c0900340c88040844407000343d0181561084040c2c403465080c070018141240d181c1d03403d20001d41424031740b280a03210781 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 613863920 1250 613862670 613862677
    0x80f150115020d270e01061206080705150408100f0605061305120c030712020103060630020f0c0d080705070206120c0913020c06072c03010e030c070f0b13030602 71
    0x812007000c130f40b00c03030003c48460385801d400500b00310054416550405000038145041341402d00039060038a0381c107001807900403880400b20340d02107178648009104903080d15514000e07540314655038011600f4106802c2d0381d41d0070816002d888007008011440d200c500704074107400703141c0c51103552040020003480b1500300840315001400c40300c400c5403000f103082c000091900e00940c1051300050350410203102103507054000e040c01303003000f810400b550340ea4580401d2072101c10300c039446494000c0780f404036000168550403107018804413101e560303840c202c82140ea45c0e1000304101c0c640001e610800002c8240d032060b4291444194024000d81c50220000c460303807102e02c0060700c132080c82d403001c21480c00d541e0b49070035085166180c0c403440540c032448110052414568021708031820301c00001c2c4658011b02403043c45c0030042d840e0958012011425102080c014043d40112903014440060102c0f0900f00000d480e04c02c81d6401600b483d4000c2e280c065a1015000d0700d0300d902c11140b074120040c000200d094014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 613865170 1250 613863920 613863947
    0x60904060605100c112209150c0f0f02120405120705280602010b0f04050a0e031303150c0215040807020405040812090a02030c19080f150115020d 64
    0x309409890390b0000b07911100074105440403883c115500b400b0005060700c403483c000c40441d69000810b80015140f01191030b42c80700000f4155642c10808100071048104070340140b031108041090101c00b01c00038003503180300408240030911800320071004c0c40c400030f982520044c0035840281054544001c2c040c0d04101c1558400160144080104070340e155401d41002410022050384a44042d0401d8400710701041e400510459041550000b0b0303a450301c00c501c2c5500ca00517200041c1582d51030400000030030500300b003494240000200c0380203031006803003070409683c000c4200c2d0703001d42500244c00040340d051100600240c0c010407003104801c01e100c02c0a03175029029003000780c50100540c1c006002c40740115011549214080703400703000602d0220b9110750084d0848024480e02c00c1640000fa03480b100c034420980300741c0a60028010400340070320f8140080104104844643d54108245911100065264410f2200d940300002c0c05025894489085a078107801500c4620341051080394480030490b078 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 613866420 1250 613865170 613865183
    0x5030c010c0314190912020d021c0b04030509030c0a1203050703051c1b0f09030b102105161805060a18050a0510030515060d0c06030507020c090906060904 68
    0x1240105110003c004059041414102200320b480d81c0340090404030041e04803c44410703580a07200c00507200d01155600e4036404442d00d44084c3c0707202c1c1000d0384003415100b0050465010809110030035030840c0140c04a4402142541c02080c11182400b090300a9442144c60700104514142c0109018000404442e406490810324100006070090303050341da0b01480c50f07020380d914818680c484084031803083d5185e18514005021840082001705450841e000c00f174200d8108a01007001100c1c803000d502d000f0b05205c0480c204042c600101c911071814035000903641da00421a0151011004640d500143e1b4130601d41340510404515041e40200401401e180d0450720004022445104148035400c0480720100003040c1403900b082d104080d20b0000d00702d01c21080c10800b050001580c045030445510103401589180d942d510750005013241060314014160440e901000700e10750307905805c018810fa210f5021981d0240708402403154102d400c03903041d8160380041c1d011a4440c038280c100d00303811074010710 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 613867670 1250 613866420 613866437
    0x5030a1112010b0901080c04060e120c10050304060b09070f0c020117092d10050903040308030108070e0618010603051b130501140a0504060c0606030b100e09010605030c010c03 77
    0x1281d2401401080c3c100c65034154011a400d241580d2100a040d4003089103904903007010f15181c000f4207a031296900a5105045034086014200410032692144143c000c1c290080881c0984016105070b02c01d407816601710742080c441044e00d081542105000f030030366603100441caa10749a0216414040380c00c0c202e0410000001000c50315111a0000e80110809c0000d040507841190b00a40303100b0300051283c1e020306d00000565004403001c02c0d02c2d03540d21507000d0049519a24402c5590079481160002001140080004282002c000841e60251000c01c079000e001500c824081000d00380a4007000c0524044007001404a0392003504041d4000f0190b102682982e0080039009000f0f0300107800025642c90006010099980d015000d03030540d04c24050110300c0c02034094801409442035000300414000701100040c2084107540c030440003141c11416140ea0790400c40150048491b4030b00c9510300c0c60300441d02040d11647d06104400c01c45600400070900c824140c4010f41342c460006030203034284038500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 613868920 1250 613867670 613867687
    0x303081803040e161403180708070f051503060a0909150906021e040e070e1f0302030601090e090601090c03110d090c0e040302060c1b1606031b05030a11 67
    0x42002e040503184520310441c0743e203090340301c0c1103203c98101041e00800000c1080c0d80801522203040782d80140070552103500285840011914140140e400f0840b1841040000107120a8007025a02a41e1080301c0500780e80c1a46c1441c01c01d1400103441d00f40c4d02000381c0c0740030051602c0c25800349006900c50b045418442085442c49011500c1e4a90182c13075503a00014504144070040b4100115990480034080c282420b204503c40e018400034211018810a82c0d2400010394039010301102c0700449404120341c024482400074060b4000350f40d9035002c45d42c8000046860524807003402e01ca40240c00050507281c2c40c29504401914000100c0c400345030740d810043c0b80c480303104030081505814510000c40c9030301c45480d10448200003944900d4a0f41402024080065408110150443d0301e1404041c2c41d8071030200c3c040c01c3e02e40c1c1c024040102e88500450750070600041e000c1103089400c151070421040040c848142d440181c01e200780e00000c2e800700b0000e0704014042e1301c81002d810a4100450a01c943e2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 613870170 1250 613868920 613868923
    0x1030c1d07051c0f090b090f12180d08041d0103030c0b0a02090a0e041709091f180c0806120d0c0f060603030504031b0501080f04051f0c230403030818 66
    0x1c212034009441d4403207170150180002042004d42101481c0020201840700d49081e0b0303101c070020380800c4a64880060b0641003841c040700b0160030500c0042964590b0050340c544114250320a10074003000480310307140c07480c1004143c14894101c81d0551074007101203c10703a6403000e02e880014800c11100380d00b48041803042d100d9005004c040c0c014405091000c2c00c20b0b0820200010f06c80030b140c12050410080b940180d1551514160011a04849094200d41c2d20380c1c0c0c2c14010426800c403220300360000d4200e8541150582094104c0403460322750700c420b51288820f200030701803246281c803840c3c0e01003e01c0420301d0744903151005806000d0750403490180f01030f50380d810a6072040d50041d07000440c0407800788140008001101081c5814101c0244140d2400001030907425004180046113041440041e060080c10310504035a00903403017450240300030b407901310001031110350b8482002070105111108242c600042003100d070400b912119041c54a9560125a940e03002024440f90386c000310302d03800da440e10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 613871420 1250 613870170 613870181
    0x9020f060346020412080a020c090a060e0609010501021f0b03030406090f09050405060a050604021c061403030708030c1b0303040303020703030e0c210a140601030c1d07051c 76
    0x502c1d56408420054800001c400c44100745103081e400d10410080080c982d03410441180c03181c0c04601c654440c01ea404099050641c0042c80c16006800c0908110315064a540044181c4011502110350758690f202444860b0009001e02c43c00b40c1d21040b160050160340b202c070380c00400341041e004908040f5050101e811074000e94003803008910099424003481c1c01c414844c40140c030b00792808200c50302e801d0302c0ba00ea4903040600008161903403940410415100c03a0104c3c0c12035400d18041d150700d280040084401010544103540d964103e010400f4804e103004422201d02c241c121070840c0c1182c0718010041e005910000c0d900c417503907800c086940150310080c000785110390700036100107855039100c0c100501610b142ca201e83c145030304103695030707589540d911090288d038040000c20300038130348652a0020b1803c42c0003140500070746e0f47c0c001c43e00313280440000e01c14143c0c0d22a5424404255070f0300c051014141340340e041e403440c415070140005e000c90701c40c50103042032200c0c02800070100d4140382407083c200c61 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 613872670 1250 613871420 613871491
    0x28020604080f010605011e0e01050f070c030308150603010312020a02090405030d0609020909130606051509040c020a03080f0406090602030a15060503091213030819030f09020f0603 79
    0x100302c501d003105410001c0c40390b0001042c0c20700b8215480402c0e902e40400706071012a40d9014411801c4449070503074400c1c0709564107540960b0519944498a0030540d0b0202c00f9807100f10f0000d03064900042c040200c41248800c0c84001800c580d04590031903030340100c0035804210740c9007140f140d488a4000760b50340f41c860314002c42c011000b07550380d401e81060b20810341d036036508070254050040207510300359280c0c00740d042e91294601d00207060300845440c3c038002510469001d20340c000c8803000000c02400c0e00500401348140122001c01141c00d0b40724090340c44019000d405804a20780b0310016641c0c2015029480e80103101c1c45001403020840d03651601240c2042d54000800b40c0e44802007440c503e0460034240c050300550804d10304501c0c04020455443d580d0424600c84040701041c1c0e80042c02010580714040c545c8001c007503450f032100044440392071484c6000c40b00001d00b880d05800c100d0030203206081406401410b05a140c01c010014044150b20140c40c110300c0a01d0080100e8000860314040d03003810 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 613873920 1250 613872670 613872673
    0x204230d08030f040c05190e0601020a02030318030105060a050a0e0c12040c03030e030a1203020a051312031413090207140d05030610080f06040b06040306111e0306032802060408 78
    0xd04140c1410172102d038007500710714043c2c41c1c4448010100b25010410a0071529481c00c4d0f814a41c0d100c0004074240000c2c0130000390140700100c4e035409800f20381f8070b43c01c1d040142a4020421a501c64007009a44409403045581148060800b449080f290f2a04160720803140b03200c55203090300b240a00a400d1504440a480800c00e40c9414000c041d4484081c02d501341c0128010910180c40391141c1810540306005001031580c0019803804079405241a22110b106c010620f03c42107940c1c1e905242103141d0610203c00140c1d01070070341c0702203c200300c1c06d441070340740d40740010320110f41492800002580211030030383d2a83c12840d011506c0c1c3c0b00400c44105d44040170340e191503d90400d0f8040c03007010001100c8241c140b04c5002c0c10840055100116250722210480700070400480c01004a1003074400e54001500c22800c24281085080800008000ca01c00d0b0480e920071004c110480c04030035010035a207883e0b00d40c01c1150300e025000c0c884403442d903500049103541080e01c1025070000350241e226522070001d030b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 613875170 1250 613873920 613873951
    0xc190c0c08030711010503070806010819090c060818030d05150402030406060e07030605010206041b0b1303050d0c0206070f0c0503030a080609060906060304080304050118150509010204230d0803 85
    0x10004e641201110382032007800c0c500d081d400d100e44007408110b002007426041006202c00141c200b402400302082410002c40100103100b11810603600d2506c280c051f400105110a001c41c2c05103841c110104044c4401101550500d0a2084d00c0009000050540c3c0c144102100000006075500e01c0218006c0e403081c00d000a066107068000c40344810024000014585040c20410041e6008170355946e00c40e40c4002e0821610202800707210704c080c900c2e000049003a001280b0080f040c00602c081c01e06490154040700c400e0780380300004549041e20712000a402c103600340910000100c81c031134001c0c01c05200b002d21159060b222800320749140c102d2185400040c035040103200b940c0c1050449240c00560588800c2000c0c40c0000c040f9110740f00107403004040d80c1000000509102081d07000009510406c100e582003040b15040202c4d1916490f24203000781403601c0c000c64a507460510894044848500b1140c070600f41107e0f421030012289190035400000d00303a200070005040c20025031040c464013408051 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 613876420 1250 613875170 613875173
    0x1404210201080601030509102003071709010603170d1b02030405011b0b1308070204050f09060f0106081f03020d2a080606121507050a0e010201050c190c0c080307 71
    0x86a10b029000f036060518103000c1c41450500407a00748224500300c0c4000c030707445012414a00c00440310584490088201005010503603500c49200310643c800094842c001c2d46030303202c000e400c0342d90a10009248001c044000e5030115001e8001d49800c0795800307400200f907a030fa40400454600e02421107401a04005001c0c00b00303680110b407031161614001c4000c4510051551112074940c07025080c82e01c00d058030780c6031004202c1c05030100c5141c1036018206022070f007031840c006071044000765035542c0c55000303440014011015100e10581298910748d2001b1540c0c0b2a495003072030720403a03c65030040150b1424404070258462aa800c00c1c1140300d243c0f00603048404071402da210400400c600b1030ba40803046400c02410400003045e07900604111404d440c2030340031341c903464a40784804070f14100c04003882d02040501908800507081800494442485284a420049080b0352007210740100e81d000c24000c0849000c40e42c6442c407014015818494280540d545554160b551103500194255000180c20300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 613877670 1250 613876420 613876427
    0x203070f0911160b0c0408100504140c0d1b030803010b0702010e1c0b1005030a03030c0206060a0503120a0314330603041b23030f0601151404210201 65
    0x48095108180c3d0604000c40f41544080d10244000b401c00500d50003c00e114001c1c00701100d0042c40540201c0341096040c04c800c10181c0f800306c07026265240500c071003003140349001c145038810803801000082c0343c0c9542d684060701d4001c85007480050042256000c80000d1140004501030081d00d103400740c9415851000521407280300c03c40c0c50040303416103240d5600441030091003172104c0d44540c0c800002e03610665440c00c5800264030443d85845012030100c24580c0551040300c140c2c1d070035400e44a10380e441c41d041c858202c0d414890150503511402c031940d003000d1441e0143c82c0c02340042c41c011442e0180302c040700360490401e803209a02d11040c0382c00f0700d01c0c2c841c0101348480a18020b803604071925100038001481400f0080001c0e1000e546903610000104c03a00c00d00d00d000d803000c02d0b21400598200307440e2100f6984228196402481040d000010f43c0c00c0014078981200c20001c2c4501d012801044100c5091030504c200b001419000c1c400880e041d10a0070030780c06044030510038902c00052500004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 613878920 1250 613877670 613877681
    0x11010f0f1a010f170c09040203150406150512090304030c08100501060215040210030b031f1d031b071802070b0601090f12030c2a0611030712020a0203070f09 69
    0x701c1c1805030966044212075000003000308880c1d2205040009507035000f4a960035403160f1104c0d150310a10010402400c42c1442d07034500c21010080e60100540d0340ca0340c00b03a03103400d10003403a91004241c1c18499402c0d1b410a45481e50f5001403441d05807828283d0341d96950900e85116008400c55410080e0032044000344d070310500380101f265100500850b411054042032543c0040c00103405244200881803001d80039404c00f0038020405401c071b03907031080904039185032038240043c2001e0080c00c3c0031200032040d0000042c681ca83ca0785201840c9840c0c64400300f2070718205240c2d11001c1c01d020b00d1900007803107000550140e5940404000150b69500a8a000384100034000e0009060007000081403203940002c1c0142001c5d03c02c11005100070030130500b02507d242c5183c0700000c102ca412516025446e28641501068680b40800039140a5880e21425034022804142ca00c010f42d00502001c00401c01c1d01c0c004102d580390600580e4143d105039001309041c0141a0400074000c0c40700f1108101140c60391140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 613880170 1250 613878920 613878971
    0x16050a08030919380907090b01080603031615230a0c08060603090304091a0a1208120402010c060903080f100e010e0a020c0307060b10030204030503090111010f0f 71
    0xb0407250701d005642c0e8201340061250300c0c0c0c0c0801c440a50941240e0040ba8410031a007072910b2404810346000c603d076603903c00150140d070710301e00e00740078824590b940604202d5000304402406141000e2010203030f000e0000410b0302c1030710b207482050701244110a0b00e210f04180045095082080100503e20115800b14060001c42055240052002845912100054200a0403202641e50340c4502003043c2ca9802641c100c040313190302e0b00c40590000c500c1b040409802e05c006542c030400b11595158070b070501003682c50014003500b40400c00e40c80160001003109500030310505000c079040c400c6071a0482201c091020803008036001d101400041d11005400d580d015481100e020342c0c907414000122f503024010f1003181c00e004900008141c04410300d805a070301d2040c40c01d049a072105604e0801c00098002c41c8212401011b4103c0c1a5020901c80d00880b0242e070f82150045192249480044681001b0000901029542e400034460040900c1c0290002d060014401040307003034114103113540380d012500301d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 613881420 1250 613880170 613880203
    0x30b0408211302100207171606030b0d0303020a1715040f1e02070519120e09041a060f04110904050c030709030201081803130608100b0f16050a080309 66
    0x40082c00e4440310b042c041c40d940e050f1031400510b51203003804d07031a000c070381d4100116017122102500341c034840020303121111040c80031545403940e0b035441003682119041e0000c0c42e00601392000384000309020350010301601000385000c80c5114016040d00b030080b02c0c281d0345003807808546c010100240c41c00d409181a00c018003c0c0c10045000f001c03c4102103c0b005840340802c0e1600441c000051100500221034150300300b034071804c0c040030a032404942e550b042c1207664002c280c14040442e00f900b02986a14420b0b0b034031400821070704882070071880c45400000d110301e50140d65003079400301a0f1503034010300d02c182c0c1d040603c00340c50b50036550410056441c0140748220110b010300030024600d6011003003108581c0c0a0a040c102911101d12403e024601c0301c1c07042e8030b9840300095016207080e1941b5514100c8071a83d44070711042e02c42c00060300c2020198856054408410b01091281020710350003011120404141608480300f10340ea10381c104011f03040e065525a1020007000754045061106400341d60500d803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 613882670 1250 613881420 613881487
    0x90a03170f1c150b04180b09010905100e06061c020c0714011b02090f070207170d0305060909060403081f081605060f0a0e04020903011d0c0406180c09030b0408 70
    0x4412a02a004031b109500b012001802c1c001c3d502512544a403d44d124007410003851583c6a88071100609400c0d224078a0144074000009070010055071201d002c2d040042126103045888000740d15074042e90702800d01c226034204a0100111001c1103024010b00ca02210032001001107000540b00c0803002102003c0000900700c06070042c0d030340b0303501c840d80600740e6001c1c1d011545540e0401c901d40240c640003502540104240701c2c0480314005a403c88815041d0b0382800b20b03603039920920070703035a00995000000b544110040741c00680501c038402e0b032040f0f0a58448a50020000413240c1ca0351580d440f404403a00560021124249811005005000240c60b603601c0d00002c400e0104441c400c42d4203e204102c089040c1800380e80e0340b50120b5503480d038000c0c02406030410450307680e0f080d00c0c103000c0c0706021b42c8110168101c01c0c0c189406501c0498840302040d20a4050b02c0f0036413800703885000c880c141088042400070000078010444217004900510070603443d042e02400302e840c080301244101f800000600c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 613883920 1250 613882670 613882679
    0x1903150b01120218060f07060606050c03160302210403061521060f09050105070f1409010e06120403110d090509010303030b21030d11090a03170f1c15 66
    0x40b81003100707000c900d400580e65075100252110f190b14a1410320f40c44900040d094524146000103800a180610300801c1a26610401a01c1034440ca10710006c007a0000c1c010032841c1c07489039010081050107801500d09440e503039440d80416201c440a009801a400b24081c4180310343c84c40341482034100704143c1d118040c10103004030070a54056107407015401107144c56804218581e0807070200006204014440c141080c9441800380608480c2c803030014004800c1550000e1080c102000b80c460004051407030418600c00459603d1111200b40d038004504000e044080c0c004030240304e104c2c03402039907142e02d84d01c40a081c040c00c3c2400410080c0800c00446010b00155441c08566030450f903141c1800a152440c0e4000305042c151007031714946011320f8107500303840240c1020005060105001804000442c1141d224203404c2c021955403581090001c0800d1000560a000f423120446481a00d141061079403951590039034003080700a02c0d403440e070b829450038400c030074003416605c103c030600503d40700f9050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 613885170 1250 613883920 613883927
    0xa110f0a02090703181203140103150b0d120f081005090f0702190507080d180e090a061a090906071403100f03060b09010503030a020714010302091903150b01 69
    0x1035120103072051546a011a085500962112021124440306007903100e4203410318400303024542035824086400e0242210081004500081c1600d5019507018203000f44810180010518055955000490010500003242070b4030301c8084400d2071303543c8129030410050002080244083c20503e90780140680078006a03560002c03075644451002902c0510395a030b48401c030710f001c01c3e1600340811030020689a5090040c0810729400303071a180b5003210000102c4410807241080d18041264400c424281f040c01502242c00203143c00c0b003804021503181460a44800f41150504032404085034103803070009925050801c213140d0b00c801800060042854480c101410010800d100075445500000001304803805007a5400007911200111461058a91501c4d400a0000c5180c1920a04000000040502d130020071a90754494a502505103280303002042562680005409414580c09000690b0306460b4807802c41801d0303040140c54070001e46141807046121186600504059082c4611040300d0b1741c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 613886420 1250 613885170 613885183
    0xc16290f120a09081b07120f08030622020903070b0c0a2307030804140d1208070309020d050c1201180b0a11040b04060311070b071b0206030a020a110f 66
    0x84991051507036a1084041002400b00c12002065120081a00c1d00340006140100502c0328022044a074003d1b2100c1c100c0804140544005010003240690840001c1c4244050768104401400b404010f0040e1055542c80d810711980307a090b42d903030201d0140680c1c0b030b0820801c030043c00c500344144c2c5807201d103090b03a0b621814245005070200b101c41e14260281d05422210940c41e0140700c1c16645020f849140000860b4030070302c2800c8102002e104105114a42100083c1d1215841354800d2103d002d90305080e10080002460003050603030301d040304005a00d030b0341d40e148103940c803840c050440303d10080c0401403c2408007011010b01e80c900500143c8042d440143d1400a5400c0901c200459862040780c2015184814211a29220200300062556000405001510019141400312808103884020f1a0140316405048040c00401145056000304010030084181d010103100c803100030b40105800703030704c15039101440b554006040d402d03030b907400000301ca054071001d400380806c01ca034414090f03507501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 613887670 1250 613886420 613886437
    0x30807031805091512030309100510062a05010c0509131104091a033c0303070323070207050a05061623010903020a12020607020607050c16290f 63
    0x1340959403103040c2e80e10160a0600344070101142d41d42d01d00181c1c910b45511031007403103241c1c0c1800d002c00300721001c0d20362204409032640c80d17560035a4060f4401007409804140c0f140082e2844990712070102064080c013503200926002c0d11081d0752020b04905120a0b2802d0751062403c0c246045100f60107204c2c440101d03030481d0800c40300416180aa00000d40080c81c6240043e9418869101c1c03a183c07042e106400c1c90700e070080c24041c82ca50040302c0c3c4900e90b00144411148140c5800c04c00018111900030750200800400705a1120180b484091440785480000e4480402580c490101049a441d02c1401c01028001c1590074506207080016001458090244010000c0ca00031010800c1103d00020102403200e07110000d0052108505020b51212105101607603881b10310554440c05078000680180900c0300e0307a00504032039450250880d1580c0166690742d400340a0100702900705c0000700030f000003070310a0303803000d601841c644948074902c040312000e030003c4200141700d90000304a040e02500ca200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 613888920 1250 613887670 613887691
    0x9011409030322080c0312040e0411060a020f06180703111906030b271501021c0908100e060c0705011103070c0c050f221503080703180509 61
    0x2440c0440c0000e06600845000c07030300d564440c00d40c038280700d40314040160444900342d0550740c08040110915858401c0c480c1c040e402c90004000420200a1100c8165405400f07001c4400003802c48900007411030744091030910050f4000b81c1a0b12141c0428844950440140c00071884040c0e8503420360303500c41c44144400b41641c000820080401d8450412410554401d0342c4489500c0391030340303c05002080300001b006d000b4803a000211035000c1400b60b41c081c8207968043c1615a5035141c06c07014803c403418069040c114025082100c0035044403101c064a851155140c07a074885040c4010949082d1780807445680322800c1c080701c40124080422425082894600c0e2503540d1551810100e000d0240e01c02a04c0340d03414000f00300250117030b000495221241c46a284031000c1c503601e41c2000002030101c2b90303150780001150007255844285c4160408030604000000c182c6c100744c1000005680c2c0300c2c0c2e1040d10460fa00140360001c065014611000a03104100b03140c00e940d08000109486480050000e00c26 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 613890170 1250 613888920 613888927
    0x9070f0503100b150f0705060a02070b0f04030e130e0f030301030809061608120703150b0904020a17010303260c0f0c0f0109081330030c05061317090114 67
    0x296150030640c4504008900995a90758034100c0805099911034501034500d80500e0300400c201d116280210b52f011504162400035a484013580483d202d94060012400c0c002024012500e5403105845208489040c94000403044808145035080c002d103242500709640082005200244410007950070168042e110580ca070350510b507816031900030a071006801c03514080b41e035545226020000034030800741c9580c180100504860240d2801103140105403140c01c040c00a04e50380c1c2040c0c0d0181070444010318007001d01421803082054508030a80040d0b0000303c9060414480c48600c1000f081072256040900d00280b42180d564445406a07480c0001c1c50400003800d080080010403110760000444030017004011150310b4115103650018440b002c01c008486000106c03810303440c2c0e403024031020a4110182c403040c481032018003030751000011814424804090740108404210003841511130740c103114007501c458200082206150300c00441281404c010042d000c0e44e00c28803c01d11080d01c0b080700358a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 613891420 1250 613890170 613890191
    0x1b0a080d0b21010506040e0d0c0213091406041103070f0506090d051f0b01020a030206130f0f0b0601082206270317090703020a030b0901020f0c0609070f050310 70
    0x70402c1100048441000001141c030520810643c00680030780001c580030030080c800d81c4a1152128850340407000454940b0020b00050700701a405034031070000200001a01902030b42e034050703404071080d401c1070003a4040d5040000b004400300012860203006c038001d0203224584440a052900c45d0b008980c024a00030030048000d440d10050100d00c1c80d80705083d188100c00c6101c403001107100e8400d200c2c850500300000d1510550001c1514524550994003400144e66004140f41e905000b0000449816000c5030004020500041000c49403921500f0442907504200000410700360000d400c5c06400c80e40a0246180c02c01076482d500c0960380c1c805404a0303442c003800c0344901d840452040301c0581041075000c41041592020500c0c940302c03001e9060b29040c2c0c0303510441d1541e40c2d403a400000e421000c2c0c4074044c008960711140030342c1d1241085e0000341c90113031104060b58298100201c42d8003a9407122091080c1d100041c40501d02901c04020340c640f0305840c1400203580c42201070003490105503580072020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 613892670 1250 613891420 613891429
    0x6040602090423100b18190302041104170d09060305091e07050a080105060d2406060c0203011407020d0302212719061107020a03081b0a080d0b 63
    0x503014040880320f01101c80440110000fa0126082182c00c03600712004500b600e04442031390711000082841411170b80c040c0042c1326150030b6200c600008920280c1002005a6841c0560170b001c2902e0602d843d112443e0511419a008000d0408202c41d0040540300c01070940c070006100444640d8900801d20b40c40e840b0340170342001e080e5904103424080c5007030001c00403c00020000100d07081541d04880f0140c3c0d945001d4201c543c1580e0443c2e100c1020303510280415a8a6072000ca2811b9014482005070381d80d001801c21202c06a02010108102003070700703000d40c40c2c288140058021060800741c024036210070001e4440d500d00a600b8245580803804150720010b00f60403600034001905031103036900304a1203da59a0500d00c494024070718541c040c0c1e142c0c1c1040819100c10140761640d24507000c40e40c990b224005085283c0034446010300510043d40503079900307000c0d14025409038041d5540c3d45501d00070745108401c091580d070055400000a00c002550480407900a107075001c50010701038644c0e00009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 613893920 1250 613892670 613892681
    0x1203020c0d031a01020a050c011110320405060a0e01150b121014090a1103041212020f0306040b1f02030405100827011508030306041d060406020904 65
    0x8400c0d10030014074150103038165104075110380d0900040e58042810f0b4004903620340f51424001c01c02c0c0c109151240c1d155018220f202e1240c0c07110000c0d04c280032580d40b0ba4000300c4641c901402c561035540c81c482100089010704204032621090840d5a5610b0507850f1650b450307801411640440f6500c84164502200c20350080b0b440c400c009008258181d43e544010000c1c1e00020802070400707031a40c000c205004007003224071040700d084200076110107100908110307003010005d000c04003d90302c48076018001d1003154020f5100d14807c0b0000c03041c012500310003d19507244a840003070054410024007180c4a10002580c1c1d0091007184c02240c080c45400102d0502c0785000207800c43d200381e0142007005e542c1c000c40600203442055139144440341b441a4215002c003000d58814200d11003064000030101d4450508901140101e40041440d4010414007141d4041030fa111030960740000c8288181c6243c103000d912a8201c42d205103c100506450b0389544441004c3c0005005d554005500402c0d5116070700b01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 613895170 1250 613893920 613893937
    0x110315060f0a05070b01050d030f0c05010b0a150f0e1c1b0e0a0f020315010516080408010e010f06030c050904051011182d0f0a0803120106050406020604120302 70
    0x25141d014042c0d01500c0c0c1e030032800049030540240700000c00e05d81810607901c0c903003075007594800c240100e03400c1007907070080f074080000e83e41c2e03540740c1d4280740f1507807592943c0e04001c0c041c3c225141d054500c0f01000a184414412000040042480700000300d541c80c5182083d9000d9440d10070000800c55107090070095071101c4003c0d58190068200240b241c800300007162040896400c18440c244075848410124402195140ca24148410840449520801c00382640441005210400c034030030780c4810807217400c15800691140c0d107130b050741c1111010038065480026104041400500d04613528224501c20231300070a40a1410700000038140f08e800c0120410240b01034034200002d4100001201e8654030503141d0080f030416948921100303082000c3d00c0368a01c1311030943d200c1d00c804000d06141400400528241e40100944020134090741c582914200512a403c021541c4034252350030190715800c16030112060000a120801035103401040d101d0348aa84003039040602041d1060a5009000d42d0070f1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 613896420 1250 613895170 613895197
    0x9180c0806060c0a0b0c030405070f03050307030c020d0506150420040b0a27090501120218060109030b18120c030711010c150e0c0604050a09020307030207050a110a060311031506 78
    0x4c6c4480800040300560285011ba0309440320542c4605168151246500c40108103500130008080400e100f0261001a18802403c01d04045100e0301c805203880c209460040c0ca0010b0303c1000ba5441c80c2034881d881c005140360040c0110706030403c03110b00f52402544222654400f0020345d000c0031070f201d000c7c4e003005104103084188070b903008a040d0f290081418060189c20914250006c16280301c654590441e040d0b00528600540f030140c0d00c4201d03103603406401c03a41440481d000102c0050180c2104d07600c901c00001d00616205200c0103034603d0000303100f640c64011b0030104100e12602c1030101c21254502c0d007124540e44c1c2e0510280040314034400c80e0f20702038440b450700c240e00481c12106401400e810302040c8101c8510407109820411140710314418950300c000c02550400401c0d802d900516401a124107006040074010340b612414503041c40f00072100c080405601880a01d030012089025250350304d010081030703403541542040b41c03102038103207448106001140211a501d407800c98100500314032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 613897670 1250 613896420 613896443
    0x5070209100f060206040b0a0e03370518010f020a0602030403140309010203160e031e010b06070c1d040c0528150801050f0d02150706090309180c0806060c0a 69
    0x2080252a0001a6007c8401d150f8120100b00800381d140503480d40710700c0c6c44010b10b140020040302c080e403800718003204000b00f031030340c01c00200f8028820645416001301c42d141d144c2c1d60b031122984800203022907061a4140030104940c01681740d80042c01d00055a030045005070341c0c0d1140e080a5901c10101c7c1220245c0755400001c01c1000c0700e0640156005103201c0c00800c9103000007110030f48085007144840d030b03003550107600030100d0000d03001e80c0d0704100100840009107540054011545640c45420700792500000c00c0010462100c4509040e01c3c6045170f002000e0640c20155202e00e850105441828424a85c0d0842404056907001164540454001a48540a58820b034004420001036004800b04600500000d00c900380040850b0840b40010711200d11580307503a003006405000e00e0815001c40c1410320404001588621944001c039000f0780f1036607030300c40c9840f00503051140200c00c1e87e860103040c00540620345800c00d504039000181240e900c7d440b070b40c0c0e2503600340c5050740c034100140035000d410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 613898920 1250 613897670 613897679
    0x60403080a15031103010b0d150c11100c080106020610090c050c06181504260c030406030501030b22080d0906091a090a0305030708040809030a05010b1f05070209100f 73
    0x400c4c1036000610940091041c1a9581c003004003400020202804108040da1741000c5000a07900c11412084541021040201c680000b2440e028920b80b4141e000c1d50356003503040035160020311442c0103120034070044c056460100784081c6040c1242c4141c044c5c5540300c9018481d1a800380b8256104245150100c61144c500345400c844084082c5000300d03010700404014202144400400f244166040340b450391211050003250b400600b103c814410444a09000b0500e040d1024801400106007a40d00400c60307504605240706d25802c042d22054285c03c90044943d080c1e0146040350050f180c021242c59190014010190301070050410000d01403031410200c01c0c00c01078482007010346440d00407603440e184d9450101883d60b48850308006004a02c05000090f40103220f29059603000740b0031031180d420042100c0c04603180c002c41e4607003225181d468840039652400c01c0352141800320020443e800e560125240068a14803820101a01914114000410310004001144010030800c41c041110f0341d9517 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 613900170 1250 613898920 613898933
    0xc0f03110607091a040b2a07030f050c040209010e0d03090b160c0603022703101b0f0302210a0204080604050d0f05090f19080607090305120a02060403080a1503 70
    0x41c0150343d54440d6801d07107105020070003820340c0d0594441040240c684602035900c0e424120041f4001340070400d60024841d90b10000748a8200210f109401c0032402180500d4843e080018500459018510600c0500c3e1640c1e0f00a412500b085410f45440c895a1040e040031144038010390004900110000381100d00c0d8221114005241401030300b103258070a0321104200c0583c8203024101880e561a2b6038207101d62400808031100e6424006c040b41d2a088490800b00199800c981c482001450070102007400d6a800101c1e40800e00c2c01494114981208250070f9403450010784c61401020109800040d01403a1690440d0054000d401c11549949410b19001c0e54603c140105400021040303000a000e003401401038500c0c042c002001d18041000c40014001c0b0140003c100c1070075100c10410000d00c1810600819000e51350658a082c8086d0441c145540752201305c48080d10300c24400c001d000c2c56250301048a0340c000d50305140800b280d880fa030036800050701801042c1c4441c2011100c00100300801c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 613901420 1250 613900170 613900187
    0x90318150215060f060c150a02040501031b05030c0c12070503131413090f0f0b01140607150b130c05030f0a0b0d0206090103090f080c07150c0f03110607 67
    0x60603402ca81e40d00401e507003505042001540c4054001e18680284030191a09202500b14504030004660a103100781407c00728100d01503815900c240ea0002c0d080c0410b5a0500a00e0b01064003100d034a041400a02401400ca10001f8414880301d040800c90810b40b060a02c515800b070038544420036124009428869100e034480d4180038460110b0300c600241d00c84285000040d40c0200410480c00c1500c8080104040d14144908070f96000790303240d003000000c08002ea020100350282d20341c00c1d0703550704184d0f1041d110940c420265110300400e019500004940941140840403d030341e000c6540c035114400300700c2c0d4603c0090551711107418009800003080e407100145104501c1c48554242c59101e5848080494501c0c0c40039a410841c8500120b002d0704005000305483c3d00189070020b0000e4541d00d801c1e181c181c07151390489005500050405034a0700401050015000160b95803016903e603190103003980c249218024a680c0c03036010072005050168111018048281c010354000b03280c40c2e50024903d19 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 613902670 1250 613901420 613901459
    0xd060e073e0a0c0608060102161a1204060507030501050d050307120c0209010b0d0605040605030c0405070909061202100504120b09030f0414030f0601060909150503010c0804030e03010c0e0103090318 87
    0x241c00e400021b80f158070000d0000c40328132400144c00080343c244030450007d00c503002020010036100300039502c08080c00e15105845540112400540c50500c918000e05445040c3c0c89244180b4a40c48468042030000c001c8860180e40961080341150070907030185e907049210b13500071758440a401d0000442c4aa000c0082186805415042220740e482d00c040008480c3c50b07005d1319406a0224403890030600701a071256420042a041c00305100e90348039241800c0d940140c0000640030034031103130181103081005040e01d94408a085c03150405041c200300040007440280301900b6181d0050200350080030910454600004d2043c03181d9507039803a45070708241d0012440710700b4022711604851440100c40810085e042c1c4142e903584021440c5402040d4000d480304880708401c0d940600400a26680c0074030642c0401121616854003500e46810003a0034460b1312516079001c0d904000c4520b1040c1e85c0300c4107407074180c2d000342000101c000c10b5040c12910348590350401e001c141c041d450041900b40064034070b801c3c4003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 613903920 1250 613902670 613902677
    0x1406070807090b070b04060203100b0d06060311030105090c030a091a0106110d020d141b061008010218040e0a2310110412080706020d060e073e0a0c06 66
    0xd550300c3d8680440c9100e9031074050f01c1e0054910114000820540055800540e4500746a05050b124403052109502400182c0b540c4c0d1780d01c0178204040ea0b00350045c0a0200c6145800508642c94900031030800b01000304900411000040020805010303070380081501e54000351141801d1641c82c4081c640c000c2e080c001d0f00080354000c0d00482040c1c1300056143d0f6031400d5580039011892004109403941814819007500c0404280b145000403c0c3e550890040c01e85520002e09160500d20101000d92000740c0108645074010030404101f61010500c034480e0303030310985000078103945009015041264086000382140d01001310242000207000d0f541ca1110100801c0d1400e003000340901038100d805030030b500c00c000b1005000420090b000241d42c0181e40f406100350302e00d02035070755584004071b070f004400503116181c0d40c100c24000c0000764107000364440312500309080900800d004104140d44004643d0300c03800c1c10814044d00344200c1001c80c000c00c0400404840c144c401c0c82c6400300210300c40c0e0040b036001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 613905170 1250 613903920 613903937
    0xd060308040303112a49030e01051c05070c05060c07051b03070305151f080604140f070612050f0105090c0c0309062110061b1406070807 60
    0x41000402c12110140000d6191050448001c1c524a041c00c5501d0504d5401b62a0041d01e0312030104c264074095441d005840c002c1451401d00034410404100c82040e4502141781c555144c000070380080510860810900742a900c034085a40799451200e082d86c00840d00d0303818602403061054004907450a85807281055449643d28102c55420a0041920240c04d030381c0080405c81003417641100300160031401030305035215540c0f20744070140b400d120071100300034070041c0c50304019070b000d2540f00028410505c0300741d40604034500081e041d540d1001030400741400c19012000b02280380100718442c1c440c0e4a12042d210100d51b905009840050169440150310381000b00085d4545a10082181610380c01002540302d61141994034000fa0401d00d0a04034600c4100b000612036620f0f00007404030701180c0716141514201c8680c641c0e519900103040c240b403e20a0f00028403501d50440d821031005100c540240446400c04c1c03c011000004102d07120040340a950103202d05294042c010318820243c5807299040b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 613906420 1250 613905170 613905197
    0x2918120c030901030501230904050c04020a020a0b010503010516050c0114090a0b060301200c071a03062404140117040c0302120a030c0f1103151e0103020a030b0405030d060308040303 80
    0x4002d040004d02070701f400032084442c02c0d51800c071888030341050148044a0f55003200b000490701320790000c005040540d100c0c44036141001b050001d05400352000fa8000e20050901c01c1109400303020b240c0000c402d111000c1024140c1c040d00750b0001018203003a143e690041d00300880402e48588172a041650200301402c001240b41c20140980c900135814151003e01c100d04030b4610b030213260001080400305018100300065600000c18912900d5190712001c21750300d0524508005401c007003551520320000d65901c003a1082c2203128203403411501107000e8905501304c0c0c0c00049814461101c0c1c05501d81c10950203100522a8119070002030702d1003520310b0324940941c010074907543d00d4445001000510003204010004800d106c007561210311407a1500303904080200081d0401011041d80780c9500c030000c040180200844846185600e4551001e049a50450300401c011055a0101402e00c0741e648000c5000c12800300708940c2c0c1d0140c101c03020861036849240410030b07580103210903000102c00418000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 613907670 1250 613906420 613906439
    0x5040b0a0e01061202061e12060108130c05060d060f0803070212070e0a1a03010903020616030902010503061e09192003060f010201020c01021201032918120c030901030501 75
    0xb0162007140c00d640c6042c4c0200c4d400c010403603018071030040007280d24400c1c01800d404508050449560074980e407140d14581000010030850004049100501625181402181020300e06405640041e2101550b87d00e00c0000c440c09818598441203444480c0107001825039030100250000601c21114809000c0014280c1c1d550b50302680258840e4110318008200c034024144d101c064045154840010032000e41e0000900b104c0800d20150050707084401040210780481409803c4940746040801602d0450b80000300340e4040240120301808081000510300829003400380e000d010020030703400e035078504110320701d1942d40d1104d1400c15081c1000000e1240200030030395010072000c003007100344c11a55100200540005203542c2141555405c02000e41c03003100a0006040c004c0c2551195002949989006100518000e048541c484607101002d282442034810950700204d03060307210b1300ea0b03a5402051904000c00100c3c1c454002c03600156022031014040007500080c0001d0320304204903030b0703100b070fa00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 613908920 1250 613907670 613907681
    0x7030b0d05010501210b01090504052a01030608030a1d030c150a021002090d110a030206041403160b071211071508060d0201090b071a01090b0a1a090409021305040b0a0e01 75
    0x3401b0580180041c00b218043d54031840c0c1c4140a9001c84070308104180440d0800b0385e440002c0221010450840262960103004003002003030542c00651501d05040d10080007500803444a4003603072200b4448100f00d030340c00c000030341c0405002000300c12101012183c6e1681031340700d40c1103800540980b1400740c3da003413450300c00d07150740a40c007804486070811542d45030250099801201603119428090220240c0c94820150002d48024079908944500e08420145030148100a400c4840109070081c0712000b8000706680c0090340c0210007a084203405101901c103000d1070b8400300300074403450303100203802c08103c218800c0c072096503241c1101c6e90b280c0c941889115141c09174040d003c514102010803840c503444004120490080143c48540c10740c030700070a04481d5003070384294070540d03c07411a200c452400015038002000d011010344400200820101006d0280c0c1903030b1341c444d40e07640c2c000740155190300180310400d4042c4034040105180500e40780c070200f44140c03030a45e0464a806000d072507910051064 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 613910170 1250 613908920 613908923
    0x80a05090a0f020d12182408040c150c020906041503030f0e061305012601050609060910031a010207030203100b0a051906180e0f07030b0d0501050121 66
    0x5000e59100a40b2049240442004102d0304500e031281c9480c00710300c1004035060611040d98481103401c401c3c5800c403d0500c0560010169101c0c1000110717015164402e2044820b542410501c95070740d101d040940c10715516500c01d42c0b041201c80250940c040c0d00c80340103410030340708641240298541000340000c80c1c61100c2036030a03107140c8007028004280140b1101e15007104c07030b1402d41d4624190001144c03da401070001c46180e00070b29201403100b50b80116040c03403601c442c1d1828541c000410841380c1e107046418491280510780006800b40a602e42d5001ca918010025144d80305d408a10000240180b810600b280c10482a280781c502c5150300c0880c1420890380c00034001d00c0b03251010400030005000c1c5800269100344a520000b807280c0300c50903035440e0700c40704104002c4810302d4100040e108040f03107a100c0704c1204518070306000d80303498004415089401c0c0b0740c812100765182e400c20340080099400a1343e0000d1815036800400005400081c1070b50544422056108143c944602c840740742c0040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 613911420 1250 613910170 613910173
    0x11b0225050d02030111031f1223010219120e01050f040f030309061a092d0a0b03160306060b092b0204020f1e03090a031b0b0a0506010f110601050d060e0106080706080a0509 76
    0x282000cada0708019810724aa2a00c001c001403414612410040e00d0f000000505030203d1685ca003200b00d07903c450711034444d507540c003600240700d5854012144c0c5048038006100a0103101242c0e00d01041c5403080e800a5030700d50b8428810070640700c21200b2442140343e9441c42e5446400400002049005600942903030490341e43d01c0700301143e4861807a480360000040c05079032510f681e180211a82c1da0100045c220040c248041c9290a50940c188001a0b0300690084042d1810404c61140c0c1c0340c0310011074492080d07044148124107210a8040300c802035000e90b004e0351060010417244040350a02c401441d074800c9100302e40d07104041600c000001d901080300c0c0da41003508010f00a01c0804c1c050200c141240d031102c0042c0c001d04115555070b600112003a00c02408940d690b008014203560440100b43d010105401e2038030600d05140400c0c1c1d0707150310501855004514401c0c24008104468204500e9506101d0090000c2a00e410055645001394403507030002603400004140780040307502c2240e019114160 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 613912670 1250 613911420 613911443
    0x7060503220c0b0c0a0503070317010909020a05060c1603030f030b04090c0b0307170703060311121f15150f110703020f12011b0225050d02030111031f12 67
    0x114660040d00501132084107400362454100014a0a00013859020711a481c0d5681116004c1c010381040001600200103062400c1c1c0c421016a5603020000101c4904451683d5138103101d4100e00d082c820300401c10300c14820701036004010544c00440c2486204c500713980c10003c55070402c04100503552040d0b809411080c003d802800801c000e10700465105130981803c100b81550145107002c40d034812038007400041d079201028401c009840c24440c03204001101c1e86918036031881d8041e41c07170303100c24500f01c408040280044600511103401100203a000038101c144005d54034015000003101d00c40c55107001901258000c000580a1030940c182050200001c0240b54216400d1142d404480307401b813039000299030030000d11102c090003404070451140c1d0f0f111040d407200c42000380c80d01c07a1030003065000c404c1f0a03150648025201185c2e4048420031518801e071030005001090040030a00300b1203022110001c10460186080c00c403a40ba14403410410749501e80e80d42c0702d103034042008203100030005071688 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 613913920 1250 613912670 613912679
    0x906060103200f0703180605070b0703050402030c09100b0a110114090307060c02150a02070b01050f060a08180601080d11011e0b040608190b1609030f1407060503220c 73
    0x56000d04004c0780b00341010078400c0210040b04803801702d194030500005000042d072100300070031104020313040003d0b41800d100a041681c00240c0300d018030b038022806403080000080c43d50442a0200d8000c02e21880281c0d91a07400642c010040c10f00c0640755450b0b0742c2800101c540340701003250aa4810b1004002443c100102565110042d01e94041c505085110b0340400500400001800b6409400b000c0401603594903503203072080d401c6005a200e0b40c410440a040c00115449100c201c41c0e003900300e440c1100c015501c020940c121410b040060704101d1007244008641e0050005681a04125940319611582d13050440300e0b0a9030715200b102060804109418590081290000c200b162001400800c8080d01c1d81702c0c803494a100c0c4040c4a1040561030300540a00c64841449a00311014403000391805142c6a00600046403922004107640f400c0304070603003404546caa08185440c0d00d0401c0d24041c90b03850780000c0c0550010f8403400c0d45011200c00751203580e07021300740d401200340d4071600005185180 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 613915170 1250 613913920 613913947
    0x30712080d0605060a030207110f130e030d020310063506030f0d03020d0606091d130b0103030e10031e1a06030f01060e090903030408090105040905090606010320 71
    0x41d050420000ba110341c00482c4594860018090040184e940183c0700d0302d0501309249403c10394000140201d2000091400d40e86421040342c6100491a50108a820030001c8030b9146208281c2400038192002c000c0c004003496290510044800700c0c1d0318180c1400344500f91810b148003101400036824445c03030804005a1a034034071541e00000040c15035041c0e4086820050500c01052240e5000030f90024080e00441041d2007220042c0c1030910300a401242460302036400500c6000c080f038500c0c01c0300c3c0001204080c1c800b517015055079000b401c02200f56501d203000f0788250420011248034082070074105003424402c2c450b42507418810701080c2c0c42841200f059100801c0e40f04665060b10503000f910011989801000314010050808400308640c074000d0000d0000362500400c5108100e40002c0c011002000000e884c0c01640180d0140d40d00e14003032006852502c2181c0c4021008c40c1840100b2450540109a1600c00d440c00e0300c040c00744044d81c0007103540c0c1030580c01803181403a5061000c1074103100c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 613916420 1250 613915170 613915177
    0x102030412030c1e060917070201021203042301020c10050606180105040b1c0f0905100c050d09030f02010e0d020a171209060103151b08100905070c0201020c03071208 73
    0x1412003d41840110501c1c15042089290517500662a4070041e003c2020324a00400524841c51541e4184003103540000e40f41c2d8560440242d00c000e0103c003080902c5802411140704260300d04e02050318035000c042e824086e4008450042c201e0045501604124003903000712803049000501803031500f0410441003000d0f00074500c10904020f0b00380800320f0392603001802845041145600440007041260fa91410343e94040c56203407101e03060982100c0042c0740000c1912101c8981d840c08505500360030b204444901402102c071001c00e0508820105142c0c00c19000f1028565031ba0080c0710710245044240c0d0f40d9a0014280700050b031140030840d02084180d010f0401c40306000c0602454104003404092468906884607822604070100400821007405190f05604164203003c1c0100700518038090b0301c2e0a09203940200348115171001428800c1c0769815940940308038007041007035017080300008000003c0f0100481c054481c03034140140d14a0001010300803202101c200b10720b8000141d951500640 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 613917670 1250 613916420 613916423
    0x7120c15170a0b1210180b011a0c0304230a05060301060c0203031603020f0f01060f090e0109060516090b131a040f0e040c0e1504021e040b0d0b0102030412030c 70
    0x42d83c603205801c0564516021014044141004200035400c5200d244210b5454140c400c0c43c1d0500f0310084000607602c0a4120304517080303601441d9107035140c801c0c200c2080c1b0804407580c54034000000c001c40c840c4400320035404412003224880c13120350150410310010b034015018041c0c0c414001d0004000c1180b08030220041c1901c00b409407030900e04458400704d40ca810034101240903070007099100c0c144880800c505144010401d0007845050320f85070a040a010f55805140e080585a01402c1d600000c00d400007080541d01c00c00822941c60310700e10703910034014001300c040001001400c00091300000c1400f66181b1842c01e0f0b100020301440c01c14200a1003417079040b2455212804d0200060382c804071230b003600040a05412202440c5400d2a1001100c015900040c4a00c800030040c804c405c10540300c03480c0180380075100180d4540744081111204420b06d8804240d02800040c0810340125000141c40c285031030b120b0600c809011400160780b2402540a1001344c00355444040d008648541c0d140e11099 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 613918920 1250 613917670 613917691
    0x170d0e060d020d020c070302100816080402011418090c040602060c07030908031216110a030809011e020d0b0d031409060d02160c080106080706180807120c1517 70
    0x400c5243d40c10b003e030303008106280625001440108103604115100710328800c05807900301c0039403502305801120716890820550400c0890f9000608590141890351207803000e44141681f1409500380c0c50381549034240e0304500441c0c40f50081480d40000d04d0035103054450725000790880b42e981c42c61000d003a4108240135400c0201e0ba00b00080c0240d400c0c0b000341443c2088a4a80c80039242003056041c8900181100302c041103244914a490100003084c80031800f40d05180400440c0c071000d48050141c400c0703140441e42d03503584034408907160300719900404c00252035001c18000ca01c1c0c00b0003040500040500d0180c003084007121500c4004405500400140b030004107040e0414490b50300d82c0c0100e800c44041304c222480700004000510424442e290001e004c035100a00449083c404010b480e81d69511a444c1406042c85100b0303041c484591000c0090a00380080f2101150f507150144602a092a81558890706524020400c0c044020404140b40b04c2910340103101180c2c8001804c103000002c040800c40b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 613920170 1250 613918920 613918927
    0x30b040f11060915130f23090c0409020c100c0f020c03030304030207060818060a0b0909070612023001031217153d0302091804020a120c170d0e060d02 66
    0x5078405a001b0303034040d01100c1c4101c41018030300c0b0707200020010403164403441200d40d0020401040000f60847d825508003000c05a03c407440a008146017100d80040c0750724081c02c15401c110103652041d2209040030495080314031040a403070a164492100340c0300600160041c1c0030900c040380c0101c1480f500418409080c036102c3c0e00400e03d450500006035100109517440d0f100904062130404c0200c0d40001da108040c0041c1d9290000c0030b8104550b805500c00040e401094018a44009400b41030f652200d02a0306403101299011400702d0344400d001c00c071140528650300e02c0549115084000c4142020f030866001a100d8030312001d4514101600980e009152805000b4100304102d1401d0700701110800d0703901d5074064000c0158840e20001540300405d441800380c5486075480404590b454a01c00161a0082d22140003180307100459401c4100c0a00d4200c0c009020004005102011034071000c2d5007001d001400d62259807103410100b04c04000034181589007009140c08001840ea030441202d00525 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 613921420 1250 613920170 613920179
    0xf0310110705010e150c0a170705040306090506061206150d0f080d06080c04111e070503030403020a03020c0117190f1a03070806070c0615030b040f1106091513 70
    0x39100c00f0140081140c0110b0305e104481141d00076035a4000d04210038581c10008429001420350f00304200d40003100c171808001c20400b034024403c49016503004202401011081d040032652480152003080c041e42042600d24004100410040c0c0034035080b0800f07480d0400c020703040060199074000d00780c4017a01d0304240c040c0041d81000040c895030706c0303580c40070035042d00d0901128109890900070b903015504205120844250040490341c40721500340003100755041040350203025003d1038400920601c0008140428590002128401a071003030b404c58204140c40340045803003500700c542c208014420784000c604139000c070750820a20310140c0c02c0700184801d181b441c12002d550070201400c0350b07240d2100c01040300d42400d2001d400038015000c000c002c01e0500c081c000b0325070100340e00090041603450607002c6042460350f41200c0210f800101004070340c00e15043c6845402441a01242e140c4c2c09a04518024102981550024400241610756001454144196a6210303400d003040350500b1010128 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 613922670 1250 613921420 613921423
    0xb090c040f150602120417011b0203040e0108010b130c1106011403011a030a02101e051c0e0d0c0c030c0e09300a0509131a0f0310110705 60
    0x81c440e950510105a00102141c0c000e4110b00300c1d00704000f190844580c980c00b80344101304480c11107103154000d2103046039900a5030700500d2803110b03d062442040d400a44840d07030000161064920034828a4000d9903902041802c80b01044041034114440c15000c2c00d4003040d0b0f51091242c942e660500350b1000181a200906000c1d0981100c400384150b8034105100d0306013442124940e814a034542114604401c0000b41e840780450802881210309000810f00c00d8401d030000003c51060014134400c0d4a4070704400381054102601c100c0c0e049600100031014030546001e207045040c02c45000c1d040143c20034804079400f800e010410740310b100010000100040d003818201e80203007603122540d4090300f41484500d040032404d1000b11080321800c0d8410004080e5010309224040104e10f0540d600c41c02c0243c00c0d00c0500500d140c003607004c0b13124041081521001d80000c126203a00000442865510200700503904410010b43c0f9090f610120003001c1e0040268031a030001600003000c18104205035a906 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 613923920 1250 613922670 613922681
    0x181101032301061d24041a1e0702010c020f150d020310120b07200a120305010f0b070b06010c080f09030d080103030f210c0c02091b070b090c04 63
    0x81d1282000001081565401022012001001c0d660b0710782e0b0040b8040040d0030260882c2100d0314005180b0801102d10303c510045030b00602d5003220213404035200080c60380301030b0025012801c07500d00c02c018101c07142e5400300845400c1e95058403440081102602072040450328440416040b504421011300082d44400c0a00144142c0400c05aa01d151070810007101482542c01400080e09014010b8009944030a0301070380270280d49803042c035050002c0003404d09003414000030303c200c0c0100d4142000b0b00c034118260403000c000e10b40302484666030b148002c032452001c5101e070080080f401d02c41400064840b181054200c10145006021503c46441d01d102030b500111381e5501030680025a0b0300035003400d0200400340c1c031a505141d585036145031000703090702000815440c1080a20b07583c50f0142e40502544001351902e01c00100407150480c84003600402d6039580981c03086588000007216500464841c80c07082d00798030f61841c100700c41359071002c2c8000005070800c140c42c002c00c102001540c5981c440d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 613925170 1250 613923920 613923971
    0xb0706051801050603030a050a12110c06070f120e070801060e0115050f070807050a12030f0501080604051f0b04050a021b0f1b0f0406060302120a18110103 68
    0x6000e06201c1400c0c6256a00300e00600d46a90400b070411100b40e60100540e64420381c90705145640b8016071408948414940c4082c0d56031503d0a2105069018140e01030140028840104c80310340e00c0c0e01c1c1080e120902c3d0140f400f400100040c0c01202da1000980080301c44041d4013003111b64454a030784e41386082d6145504000008248503004002e1094008a00c80c408402401c1c1549000f005490824007071041c5200601002000504001040410000e0040d01c41c0c12080304641200d070340100802401c0d003006c01c142414104800443c0c00d06c0045a02400356901c00000c0c08401e4600014203610390510903505281943c440c03200c940b6840ba8000da602c905021000183c0c0c07102c086481c00420105802000c40c264462102d08442d6500000c0a850303000b20094007508400e09400010030a20104520a4000b42010790010790190507801505582c00180750300d200e19a02d0060304001c841844001c1c40e0240340704444007000c00c0c00c0308080b800c51130042c900407425180015003d05c3c1080704c49032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 613926420 1250 613925170 613925183
    0x1b05060a0b1302120606220b090415080604020909120403060902013509010905010f0603211e03020417103c0b280e0103150f060b07 58
    0x10320481c245404403000c81010b4488904504045038060601c6450341c000741407600a031000584020315a11f111800c45645100340c58078817149448020703004160f040103615034019410f101008214200310f5001c0000d07600002d0040145903520f800704200c01c400900804c440b030007024929500c0c8403040c030040002d14011030002c034542c0c0300c1c0d1000401403000c45004103018402d804246d4102c046420b080c5403c0c1c03a1801c0b00d41c0803502e40004060060113110340040082d8a013004240031100e894100c04c04480c080c1d10146800c45051000d540303250100340000d400202d000300c40718a81c00c071039a80f12010b502c0d146001410aa2941e808005040615001c09003070b03402010699010071681c0200b00c044c06150001403542615000640302411001034490354040c600d401c202100038082e4050704900000901709084003240003501c8241d0000054804214001c5c05008511400350794a050704890740001e440e140789a400306004028803194481500060312500c0020b4a02c00d108080c00c0d40602425 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 613927670 1250 613926420 613926431
    0xb0c0a02070e091905010b1806150a02030f0a030b1519021c081506031e060d020901091e02041e05030106050f10030f0c030b0405091c1b05060a 63
    0x108064544030641e4018001c018000d82048003c180c0803d807007501e0b0080c00522a003144c00c51400703d0141034400041608480c0340c0c200000980c0028583c540642000d440100d010903018020340158458041401e0142e0b10410409980c80250070041c101e1140d58030740081c0131240301001982c60307580e5002c00f40600c0750100da11a289041001c00d603c03091ba15000070845d81680d503018407490b10001e02c0301010700400d800050000e2110b00003090391503000800041e941d1420209440003841c0440c5c4a60024510700005622800c00d0702a01060350740003444a6a036a28004540000e3300b400e2041100400360f014148014011600150001d4000c04001c000e1050321801e81072500c038240d0303108600c01d0381000b504000e00d0700c80c61051002e4200a80d40012803580d000000d5001d03000440004508511380b440707207a06c595265002030214a4111014400c40c2c0302c0701d16035075171524440d100d0001400c0d0070b254010f0703c0d409030303041001e0b0212800000303080200f617841e0310703080071811100b03c05410b07101c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 613928920 1250 613927670 613927687
    0x1121419050607080108060109110f030c0c07060507020a1211030a11030c0307180216170a030f05310209092d0303070f09091a040506060702061806070b0c 68
    0x30b02125900c10340394a060b0784103616101100e65100010700c607003103442341c0e69400f00a80c0e105040480320603d1034104036030754a08040c102200150701030141c01220f8040c013807000c0f034818410422204003076002001c000c41076080c66041403040c0b1202c1000c0300c0c80300d09502d402c90640c400b401020500c0f8000c20114014451013007c0c503003040d119160700d40c4250001241030190015000351400148130441005032600004002d03589034541e6210082d10a01c10001542010f900810003400c89a13050354090100b4200c19031014103592013030b140302c3d0080340540b00382d50b90304018907006420035512528084800d545500441d03104082170300c02c2c807003a410003040b900c20003a8005040503440703004500c81306460050150542c82c0e00021b029070f03040012580010b8600352045481d0409410b103610308000e0000e080c0042d90b000c010b65100780f030096082400144462800740b0650b00100e03000360969251005403207000030307040101014150704c920184504804203100000c00b80c07044012540b200e6840340403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 613930170 1250 613928920 613928923
    0x405070201060303121a0d080c190f170d1107051c02070905100e01080f060a0b0a030f080d06060215131101050702041b0905150408060112141905 64
    0x10184015a0b060600810010350302c215030391442c801914000404c0b10717100d0290044103404440c025841202d25000c1000e2040c01f4004110403031801f4101d1b0050ad042d02d41d015000d604000c1e000c0c01180c0800c020402140e401300c0c414003140082d501480c83c2148a041ca00c0c11a06070800710031070341c400410322001f00b00c0b04005044200c110b100d42c00d0720480c21076800075541c1c0b245014000c201603c0d0b401180ca80e8441400d4540034101c10030030740c2e24035078403006016554031b50b01d44407004a10600d0003090621419229402c0740c4000949000c0f0360f142582c81d0768601030600c1c601124401820000360944880b2882898064101d56010b4190f580c80100300604542015081031040303500b50700341c03d0003e506901d190fa295442801e146440d48160300025004000803e60f128145444005566615a2040c07104041d5807040380d0000860420304606a032a000b54001e01e02d4a41c80030006008000700c1b040108803851085400961244032444001d0070701041030401f850301050b948140042280 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 613931420 1250 613930170 613930181
    0x50405060301060b03061002010905061302010201050622021605030403050706120e0c1e330403050c0909030c01240e060108040215131e290f070615030204 68
    0x411070091250a052012a03406444042c1441e44a030704030042e844e030720328000e400102003940c1203800d903141031512600314061082e004c00304038015403a01c000150b00c0e20f07042d8001642c4022107454050400350b044101402940403450848907500c42079810070006004000030300c055407088029184192400002825610016600b02d07000d0741081075400554030006003a0034401002c881101d1100c3c00c1d01c84c0201c0118036002416000400c411400440c0540b80c00d40c500200c1b86100c0e8035965241a4070041c0040c0624000241180c114941614040c6020118950000c0701e03541030300e00d01650225298216450350301840c000404a030a0702c0d070f04c8802000024014100740302c0f80001b614164000a04c82640203000a01c6a10401c00e418941c1c2201025113a204101040720010349882e020000b0f00801c000c1059901143d40c002c0106140401260110a2030b410240c0700145042841d801000380e00104d50941100300148040c3d0701240c590701804c04030f40b0032202050042825801840140c51 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 613932670 1250 613931420 613931431
    0x1d0a0c08070b07110d1e060b10111908120a0b010906030c05121504020c07090b03010207030212070302030f03152b0204020706061a030a05070305010b070209180f07050405 75
    0x800c0c0315050100c0c00e10044600d000b0011644d452400900303181001c9000f041c0c0d20a0a40c3c1252006c007001005031960045011050481c3c0e1002400710b04002120b520710301140d88207040d00002d008080b6543d0f11024100c083e84100f0403030741001271101030042d8110084400000751901c070b240c80c40c200c2d41c000a040020f0603440c6402d01c40c1580c0440b025040344228038600550340c200dc03002452070503225500c030820f104000c3c8255130b20070b00e1402e03055403102c0c3d03402502d2030203140840d43c003460300d01417013203e440b030b44d045d00a411414641601141a500100000d800b0340c04200480035401445800a51041582c146071401c03d0a184040c03101d0102d0300c848020302a141107000d206c101c012102420611541140c0240c0d41d49441e19120028160580c480300080d0440d1240c00d240c03008080245210301e0b0f00b805d0411560b03603801021826580b0a200d4106000c4003004103001504250304d650740d101382c8500001c50003035140328041d8545940100044030a400c002814001c41c03030913006194001c0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 613933920 1250 613932670 613932689
    0x7050406030b09130b0601030f0f02130504061514120f010303020c040608031e090402131e03151d06010602031b0105090c0d033b060a0e01031d0a0c0807 67
    0x1072074071113400706000c91030100c050b09072040705c0c000504030303072092308002005c12811905005070449044890081d41104004c50403054240e180410103050a210341d000f1194441808041405000016501140d2052120344081820800ca2543e03040000a140c062640a515495035600d1414020706080c0c0340d44502c0d2042d030034903104000d641000816581c08051010110342c1000c504100100c0c01e10070030072056006400422449202a8007134400720440c2c0f6140da015040110100f1201081d5455020040101b10624401546140daa0740009180b0b0480003014600542d000e88292904100342c0c0842c3c0140d20010b00c2d500b00c1e8040400c14842c2580c018000e00240c20981d44180d115401c2440040c050300c50318025006140c801d01e43d640d1a803d20851000c9600820000100d001e46102c0c01e14511400000380825242000801ca69084c8503503503601651040440044001d02094640c0800244001404048030041030015880782c03403085040c130540c030b443c0071700305800c0081070381c0155045d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 613935170 1250 613933920 613933939
    0x112141e0f040b060609031608070b0708040902161e03030c171506070b010602010c09050603331507061a28150e0307081908090f060307050406030b 65
    0x1d420150586900a54001403c100c0d07696a00040703902401341a2403d50b05207c2d80c000003e082501004003030548501a0640f0303003140e100c1740114220700c200c80d001050084104002c00006c649940a8601c4040501d00124103800984030b01c85d41095160f040c80f001019480c101003010741600c10100003c10a007045401f0150003011100c038a24002c0c102131428100d020703888940e0f9904c00c103e4103299030100030390015585401c0700034000d202e036207005404901860408922403400e081964070446294150140d514100032040500006980b10072034000700c00c0311106115580c0030300b4248484441c5841c66101c24203801d060042d42d83c0b410031a1a9068143c11038881920340003c1032605c0b00c0040703486458000c41b001c00d0140712140d031344a200c5004100d41035074034450340060002170207001101241c0c1859128449039854035681c1a42c03001210b804100d150004072104090b01c2c1101004040c0c81e0181e0b400c801150955008070b4030940010030004040c03000704e4052007110540c00055031040320 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 613936420 1250 613935170 613935181
    0x406120b1f0c050f2d030f0301060e0114030c0a120207030813080d05010b03010302030d300e01020703180803090906010302030a0905120301090b030307020a090b0112141e 75
    0x21141c1c1080c00140421100140c5541409402c021a411191148048502c1c0440351209803442d1600f03401d07600a0152100e40750386000c90004140c92580ba02075802d1403450346004400d54030032100416083c18000315042c4284420b90f10409035201c0c45c140c002c000c3d6551040340000700170030107103240d02032400c1c4180240c4012aa0118801e5400214142c14441d42421802c10000301c6c001c05211050650a0a001140e1010a000694102c0b842601212071a098880c02501c58924410700324004040ea1040c9154904a8070400601441080381c001260280702e0703c501c2c260392200300c0680c04030b00c19080d06c1486a1058600741c0081079800040d504003100900003862411000d4000740c101600400892003c12807a800100800c3d40402220380304118210354000c103420134410040783c180342800681c654180801103030340b89a8014548403401d4200b100640007018400116410003000860b40d658004061081c2100c145801d00d60402c18030b8039880d091386041c0c810340031032140e1208005014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 613937670 1250 613936420 613936459
    0x6040b030718021b0304260a020f0609060403150504030f0f1d062106010315061202030a0605060c0a020405100308070b0a020d090803091c08040b0903040302060406120b 74
    0x4202d409207503002d81d681c04046044500c1045603002c0d020700e030000240c0000c060b00030340000c10300c643c481e5000c1b01c034050001031202c0c4c0301c10010b1390103504000400f036148407900d4000000c1c44000c000034003890406880b0b80311480c00c07010050254000541d120240000c2c1500125000f0052506141910202ea200c40e0001c150b1044a00420000c804a0342008000d54a020030355007640d00312041c1c100c1c100b80c5003000e41e0480c2d1050b608140800c1c540344082c01311499035510f00050394115280c42d200722203071402000081d44010035060510355107801c0070907595611030003048540b4916009081070130310303401003008450001c1d112450031120f4130f804000050140040d40d034100d0b00403400015a5541c01c3c9800041d10505000590306490315043d50104505040914001c030f050400316420490300c40d6944501c48858080711001c00e5000002400083d80c110150750703c0302c0784a090300c0c1002c1e03413580410300340e401a8010070081800098068601c01c1d86100751007041404131030041c1100c12051507803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 613938920 1250 613937670 613937699
    0xa021309090b100b1c0b27010905090d0c080706090c0e090c0a1e080d090306050c03061c06152301030c0509060f040509010e0f0a0c050405090601022406040b0307 71
    0x83d01c80c1c02041200d0f40202c0d1a030041040b20700203000020442d9501461f0302602010102c1d460740e07640740400228201d0014400d9034850302d08500100508443e00074180c41c4500d055000304c0c0c0b6003104000610001e991402090b511900c10448440032070f04060b034035a404000100520981d0348a4000041107944401b904c20403607840308019140e5501000d0174460b4650141c101141750302c1006401445143c4c40390640c1c086a000b16010421500ca80d1003811061109071040380d40151505138442641070314452035800a4032034540094668072401c0140c8a1200d03603884404806c8c2480180c17001180c0da200ca2801014003468208625207181501425034007400c03210314061440452803002034450714007142e014000080c00e000d019070755002c4042031340300110380b681028401d410215400415500400d1203400142c0c0f1914140b03810f003400d0040701400102514114403d02d1406c480c000016150000354441c40c2a464050380f0b0180d041c842a2010300104038020390000c1d42c01c00c0100f8020200d0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 613940170 1250 613938920 613938937
    0x601080906070f050304050a050f280f08210a051006030506220f0603060e070806070507020609010c021e0f01090f0b0c010b1f030b1f080a021309090b100b 68
    0x110b41c680d203550030462314000800000070322600c0780d418001c2d100c0b100080e440d0f280e00c2e8840381b09410605040d50b034030620320020034000d008662010701c1c0307800120154068108810744800a14054450141c40c003031821040c0d84005140b6610018001c808040520b200040c081c1414280001e061400c003040c04101c80803407200203c0c226030b0884c4846690740d082010f40b004018818031000b07440341020b6008143d0308454900c1840303078000005401e0b070701043c5988200a2611881e050130801d40074031001e0380c8914896410407a440a40100607955048881e2090004003104501000014240320404070010070040c1032000e444410040046000d00010641d2100f5442c2910b9440d000d02c041e007d803c1710003465510001e184c01c00003941c0c00c68080002c40300071603a000c0c0070404d2114280446591072a1074441320328035890034800064090f084c000d4204c007603100d00514000320012035803800c00c0aa04030040043c1c4540441060201054807260441c4914034010103981c94940007003928072440c150b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 613941420 1250 613940170 613940177
    0x5060a150c050f010e1c0912060b0d15020702031002042601060b221a04031e1b030201030f0e061f18050a0c021b01050d02130306050601080906070f 65
    0x1c00384104a8103110500c40c0c2000d10000b880b0b2080300d4004951584c074140c2c0c8001c542000c1d55810008207200b1200c002c100d40400d0652511594107444800160070b1400c221508140814042d1300004c07440c0092010f80e5040b010010f880314480d2040500349565145421201e90044c0000d00612a524040600c918141c0901c40103003e116440340d4050005503020102c2c15502082e000355a03101c0c078030604c3c4c10200313540c10600031541360302042403040c088028500510300d050006100003074020f810804031004480c2c54411000f0700d580e8004030061502e443e41d089100e010300400865826024030b200780042c012080c4891100702031640da80b03201c010310060159850380245000100c0c03400c801c8002c2c110300986a4150481909428054841034131011807040c608159503407018404a0b00d03180103003200d0084c040c088070900c01101d507504080d40010344140d0800c4030003038414400b05420002c41c131404001c905880e041b4000752007801c008118000c2c5420002c10400581c2c0d020300141c503107440030304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 613942670 1250 613941420 613941437
    0x11e0e030c030318090703140a0e1e0304090605030a020d020d0804030602030f1815070f0203040b040f062007030f080c0604030305162609191505060a15 67
    0x400003460840090011605400000348544981e52600c154104c4444191401d8030300b511036043c03c400300c2c0c4000e404940751220940c049072900354180c10943c8200551001c8807160449a50203414004040c2c400580300d40c80010104003507503240c0a21001424102c3c040d00d66400d0039000315800304888030000b840383e0300745140c1e6010840c0701000c1d10003841c0c0080045480389459a11642c1245081c1c40c14200302640740081c0400070000180780841c494000044295034464a80a84001003080d0318003041d400188800b194803070074180900000d260840700d801e10103281c0a03016000c00302e501401c1c00011400e042c144043e860014009044030b9000c900c00200585904050045015002a0072150f020362002c0c0001c0c5580b580207203000c0c920002c0c04108540c110441030b912003d29144e0406807090b0703241e04641030500e26040d01e80c0003d080701500c021040f82a0103070004000e03454100d4001d01d4190002810140310703c034240e8030403000d9500351803440c205000c0c0b010724600304044604001090703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 613943920 1250 613942670 613942697
    0xe010b01091509150c0b0a090515150d0c0f0608220804030c140406060203190c0213090b15040c0e0609040603050102030108070614190c0501111314011e 67
    0x307000c82c1c0020075520550614a100711310b001022030710104402d44840d5401d40c00300d00080710900c540300902d03920100504100504c00d2620903116030041100c5000d400201198040713407a585081c200040c491003244040d5401c062188085500d036410400411010000300422001404284e004440c034400102c0024019450701c02014802d5820060a9110303480000032600c01991040f9000602210f040c0102a11100d0403030752801441c1c0e00701c4540302019081d220305c5014021040c403030b90010780f8070301a69407a80402400e46043d081c0071240c1c00401d00400ca40061810102961000308440c107100700420880700030031241e901d00c0d001d44a14030004491113540d80b00c1e4000e03c010b6038050005d546941e500c0300400e483d008180301e40b80200744011940c400110800c02102c1c200c44100201d400c5c80987c021086a51071981081111503650364402c142c0200800303030113084003410391101c207940107080003403200b55080315a84031414800d001240d10745464104046141007182460300c0401508072 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 613945170 1250 613943920 613943927
    0x12020906060c0708010c050a02210d0c030b060a05120c04060215060105160809130908040308162f19090c0203070c090c031b050f071505090708010e010b010915 70
    0x11075200344e020b5860b082c0c07150007250b0802d014040122281c0c09640b1014020401201400b01c0001103000c0e10b0700410400c0345d41812507200c0300701c20916180024250090401140302c83e4030814442c008600042500c80480d00500100f507400a11480c2d070b6403c05242c074001a41d6148d161408504201c411000a80b00f070340701e48280c90040214420340c1c0040745142c10300003c5540305a205a01414128240c0c00814405005052006600441e090715241c81c54070f800c02c254025802c003105420b400305045020480b09544d0107190300c0105010307000186520780c0c120700c0d5a888004c40d80200d58051050580f5010356038a1400c4555150021030300004910b0124103501c6030480c018603c10110754086110189a4041401205680c038100130002810060802c80014801c0d00d6000540c200174940310801d03004040e11401c0e2003644050880e4515040340801d840382147c400006500804017005a076000b40542404000c1441c000c000030000d42000a1081d034080c000e41c88810203401003608203510 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 613946420 1250 613945170 613945183
    0x5040303110a0801170705031209030111040801020913090209241302040f1a07170d0c0e1923060d0c1e0801050d031d1002150112020906060c 62
    0xc10005036540b4420802500b5020280103203440070000c070b8420b8403030410000700705042d540020014074842007009904031081d071111705c005405540b10144080c035020310f01d020300007400d01c40f8000340c0c450500c0d0081c0200c110740c4900d40d1132410705040f038620141c1c03079a406603a00f0080400f508140d04009640ca07030025003180131140d410410b00c0e5482d001b00d1800c0c0c0c1c0a442900d41e9800c001c040c1d1640c0395032511460901981039100c0c00f404010050005e00900c01912804140302c2c001400c25401c1480784c0f080b5092102042c000c90b444044011480c0740c940c540b00e40b900214460061080e013444905c4801a850006c02d00030010038031800c81c12583c0d200305840700c0c1c910803d014400710011741c0e40103283d4002007a0168484103040e03e5600601c0c0952040350684401034580c0320a40c0f1152811160a445a03840704902e0315190802c641700d4480d00305048000d8081d400401140300180000404820144e002c070000318009d4080c107005907a8090744942010342140c6842d141c52141c0344a904249 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 613947670 1250 613946420 613946441
    0x3060216080a02010209011b0b07230412050606011805010e1f031b0f0e01080c1308030a120e03070b331e03060a1a090a090219140405040303 62
    0x101c0100700e03002c40c5030341500105080034003030380c0c0d14501d01132022408010000e4828003d00b01c0ca404000910a41d03ca03501d2003204845440302d5400156240001c0383e2a580960007196045e030110f00c1c082c0c1489001c0000c08d80160b021302c1c0c407003503000341d20445ca1380f148054010b040c104510003240c0741c0142c0e81e071000e10340001c070100955414414481803760080c625018550b00c500e80c0443c00c4050140a016401503640c3da9031100d10700b00b4510001110501e0004000810100341400b202c500340c01c060b14510060076070384d03004613500d03a030809000d00b00c2c6a2050613020301034241442d07609217020120640348803d0307000b42201c5054482c2e540304180c90841036242d1101080c41208090b0b41c40240b4544614200192111702c1c18100000400e041d051041d403100d80c2580c040340100b180410544e1100140f010040c4080c4400c2da11a00010003010f401d80ba00c82c3c1b110b4841050806526204120f2102d4640c954076100300b442c540b000494a002004403c41c1c41141d844002a080c503010707030071050003107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 613948920 1250 613947670 613947683
    0xf0c1e091503140105070e010c030f031104080102210c09060f0d06170102030f060a08060609180111070c0e07080403030b0310061706160c02120c0301060b07060513020a03060216 78
    0x40068950f01d00800003102c0380c10004807401024220780d401b070b408882881c1c0c0c05070b6468103401d0317980740c064001d840481d4410402010400000070480005c1c030141c548120720146403a0b01c2c003004000c12901c06005400d20810050420a40641d641d8100c111409800136420054450b0030034624900200318035817158a00c8510010b00740d0384c0d69810340c02580300c0d00e008000a140d82d2036400504c09554441c3c0076004031382d405080402c1d46450f003103519030b6014504108443d841c0c960310601c5030035a1101181120107000100742c0303004000f9400804400748c8805200b44440d0320306500000c2c0318031310290010701455511801a010f0703032800e011010565503207201c1441f11594824460719a441e20f100f082c2428040c42d00407400303842c1c1038445446100800e07524004005180d40801c404400c0c1c100d1000c5151281d51072114045d1030138007900c0001c0c4070f0851034a4403007007076050a03015a80020588900d03200c004146800507507a000b44581a45d401160068556140c140b258421039460200a0b204 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 613950170 1250 613948920 613948943
    0xa0e0c070503341502221d06030a05150a02090a18050906040c171006170d080c0301120602070510020315120a11030a0b040f0c1e091503 60
    0x952039440d414115402580004241c2000c4080f52280a42d100490040200c505050b010080c40600d4026103109844e000001c1d0080300001030300311207541780d0b51010b4445007445c0c070588640c04078001141da0014058014001c1010241e807496200c0d41110750288045400e60049552200e0300e60503a041404040e0039400340b280c0303032000352950000007800d00421900380b10010700c4415000c2203803070086512840c20611942420321141240c00103042c0840340c3d106014201412001c28000e10380140759030340c441500b80c4482031a031804c00c0362000100d005e1060074402d001c0124005004c486c1151090010f00c090078142c0c1ca00040a48104074016050344511182d00500c05c01a0740114003d58a4040300200c0310480e83c240403801241194000c1c203500075804910210360103004051861600400360b4605980a96a411240005031015698440c06c3c017540c4c010027150780303000c1c4040d06043c071040c0045440204011440009401401c20064807850b04050500f0300b042c122001d164081401c003c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 613951420 1250 613950170 613950187
    0xf030b010905090c01090603110d06123e0105040321120603020915030705090420010c1e030210020a03020d0c0e01090e090c0607050a0317060a0e0c070503 68
    0x140a6001e000c0c010040b490440421801c040c002094140e500043c0c4510018529109040d4002c0050303000407000c3c1300c010007501031088510701c03c41003c0d002200a0300040c060342c3c00d0030311014004001c01c440c3c031502c400146540c80d00c086030448940380301041d0506810309100049440e40a0356000400601054151500420118003080c00c814a15038820002c1005003d500c1c068699510000e904140500d02046042e000b541030090320440240807108219a144080ba20406c42250142e90401030030f036042000e950301e080c400003800403d103000c0c00c1070b4420b40c0700c2540314801c040300605000340e410601c4003014000d000200c10202060342c119121103041c880500031350300105007000414940500300747c44038000c2c10604441041a90365804045c241440040b0a032006862904141b2441041c03c019a460314000c0c0b030f40c140301318040c146d0000946006443c1e11010100c91020000a60411002d9126000740c442210b00c0021802c0d51516100c810703108901c910701c4060014080080d00ca81d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 613952670 1250 613951420 613951433
    0x3010902090118080c0102061609180b030a0b0a0516120518120409060e01120311070506030c042c2706010305070f0b03060d0201080c2701030f021309090c0f03 70
    0x70010700b002e030241c1d612592800000c07c00c58204401050100c0d4440e42d040c4a2f0100300710380008002e022400000351008070400280c070b03051210300125440d440390000c129101c0d156028540e0054000e0703281940002c03001e000607010140300021296600d40c3d07600010b9802140e00c0409a01e42e0692007600d502c0c042003c60070040e90311900030100c1c03c5040060001d424203520442c64121654820030981030703400c0d50f80480752030080030f06074001c911542c94082150b0f622074000354002d03aa001842950780c0e140404d1a03c003c907484006548900e4200401c9030003448564030b181d800384850352041c01c210b014001800c0e80d169000101749072807250b50000f20400c40002061001c0d500000560022075540d104041da440c4400c4401e41e400040c50401c1c000103500501c0f0b00790704000c943c0074950030644110211452280d44000040071040501e02c426141d58052107155604480d90900f0b602e448800010304005071028403609000c55691641c210030320842000190161081c003000140b1140c1d41c2c2001c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 613953920 1250 613952670 613952683
    0xf090305060f04060f1e0b01020304030b040206030c041e0311031b060313050304080a0203010e0a0305120a060801020715240b0f0403080c070303090e06100819020d02070b13080301090209011808 85
    0xc031b07200c91600d05002044e6000000761011030f944810200050f0b40c9a500b480280d410141c082e100140c03081c8400b1440c500d50700c1000364460034103000394120398a142003425460308542002802500312010004440e100311707044030010744065580c5640d0f070311114101034a034001c141d03001e421804080784c08501203d01050010b0018001c80003440124070645030302d0340300d003071030385c40240800d404000d6001c02d803003807102084c2d0000500400150040c0c0c0c40c0f80590a90f0f00510040f151425580c11800380c6070104c1c42002c01d40c20b000c00d01c4070500c50780040c1c0d4032025000e9000c1c1c80320920003c52400300c440380003011074001e181d10098081d251944e402d0380f036542d0080341c04110041507801c500400c09103007964075a071140130001e0034810103c08810b000c1d511400701410509031a201411084109c14007070000303100c2c00100490040e50b031452420240f02046000c0c04078200c4075100c520190106142c1c00035241920038600d40103a54000000060b14000d403814031404250040050004a007680441c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 613955170 1250 613953920 613953971
    0xf081015021b04021201171e030304200d020f0d170403060608030a080411041d0a0c0503010504050a170421022e030902010c0501050c04060f090305060f04060f 70
    0x3030605040002c20081a4040d02000c0d40401d01c441004000700301044640b0100409080c1c01e1300c102c2e4104a0381d840211084200410143e070001003403008110010011600110400640c40301707801440340080c000561880d0080c0c801c60901c0c000c0d180c0e50395641c0740c8526450340310041038411590512013520030f4200c0c0c07005441481c40c0600002d1484000300840b441005181c1c0e404840e0340d030b16a00d442448069a80c1d0b240c20550300c060031b0070044128002c04101103035050041240e42c4043c034202d0103a4400d1780105021f82d0414080c440040d00c0000e0038820f00c1c0c1d11034500401c6101611803070f000380c019948224032802140100c0010321800e074442361500b0340240d6256814071200c020705001d20341d034900000c80319680358000c0401c1c6440303a4000340c031180c414034100e140da10f580e40300c441c00c0d54070550301c0130240e920005040010541102c00c451540301203060400070540380d515265211000180f000d511444840c1c000340805c1040d510901c3d400041c2d010401500304280b1140c1040e0322000d02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 613956420 1250 613955170 613955203
    0x72616080f010b0f040e16170d0e09010306090503161104060503010b090604020c01020c0303040602030906060904170a111605010f11060103020f1503090f0705100f08101502 76
    0x1001940c1d0030180907000312500c01400c4100030b4100b18007804002d26404400034080d0081e00850703202c0012000c0610300521078484100602c0395240d074450b003444410f81040e000d211a6071418003050302c0c0c4c1b0584030304490300300c0000504460386041c00e03819880f07030042400d1807400465411341000403480c010901c15509407410008161204103242c01c9079418803086a01c100c1c0701d0009203051a0031f07001082010641e40c009030810140546007882e43d04295811130b000d54001c8100f2101600400441740e000c1000c480c00030312070400791500d000e05804509420310b6000006403070308456002c0d0b804610044031500466048410300e05100642000e0b6000702c5000a012008215100f1300c91480540f1002102d409418030740d00e15070800401140007994a50031030801d100b04881000c0000c0610300c42c0321081d0103072032591108441d0704d04260b17440e00224814120003410703441d495400503c82c40044c0150a2a40e01e50711041e4000c402c1c0040c3d40c4c0452030340d4031444180c200b019030102d0054080c0ba562070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 613957670 1250 613956420 613956433
    0xc0b030a061d0f181f0b03010218090f01051c02010309020a12061118010809010f0603080301030312140a0b032b091a1903060b161a01060207261608 65
    0x3484500700c201c2440d80700b40740c3c0c0c0c4100100b0000c070061720301d1701c030403250781200014480d90502c02203070a81e0098419407102e400c03451800c1640b801c0071140329510650600c100b41c019818200040d107102404114040c103208980075000459000e58042c80700e00f078000f02081e00c0d9076602d070342c40a491010548221201400c0848800300b001d040d4007900c1e566030b1b05030f08421591508000454039400020202c002a6403141701c542d815072218490000a18020342c24196a0360450a02510000f000001c195030140380c00b1804d2000440f0602c00d540001f4201808540c1195031000280360075051008804480c2c00e940003030010941071504442c0d2011591180d10b281030350f4210f403141c0d51031283c048a0307103c5410006400b1408400b0b00303540350110b46007000501035899130361090f49908500428000e56291034041018030901e510a0008038100005020340e42d0b040c00c0300251a0252403241c0e500031074541c1e012140342050390041c040034240e800300321550100a500b0200700c40340706200d031000d20301545 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 613958920 1250 613957670 613957681
    0xa080711030c130222030f0302190f02042d02090414040b1b07170301061d0a0303140c1c09290706020405040c081906030c0b030a061d0f 60
    0x802d4501e042c160050180030348910054248010b98014101e181482c1003000800c101880c90028210141d402448482c00318101c9280181c40c11000d08400d40381d41e1402ea1040c00011740e06590280070aa054402207a8500031a600300988801000c151112004c000c00700d80e240b10f890750144c00181000c84050010b0071400c42280d1090005650240500810000080340031051000380020580320001e100d140143c20746840369414040c0070010030906001004100035580010540348602804441041d107c1c0032030002030000b0031912005051104800401031503070385040540d00141e02071400e9030a10913481000d9a00754042d1000000800c4403c60046017096011048c202040e501400c00d400c1c41c031400c03d00c0b22039500b210307030100c0703503541c0030080440c03592540d000307025881402c0e4464a00d0341c01c0c600f60202010942c510948183c1e854154200302140510030040c00722440f40c45603540c2e984861020f4005002c81c0d0f04541c50008020350136139a500c1080c03038018812000700c030f45040103071100b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 613960170 1250 613958920 613958923
    0x16031704031505042622050d05060709050402190e0a0513150b0a020a06090219060f09170a061e1d060c0a170907090e030c0c100f0c05030c0a08071103 66
    0x14654404c941c1705c0244001040144041d80006003030401d00d03040c06185a8500001c2c1c2c0c11541d00317104a03110b4022205211071035030485003540140c0307411034042d81041e04403000f0000503a11038000c80304001c2504c100c01d245440d500c0072000030f007e001d000c6280c104064154240501803240c13030000509451034000440307100704416180a07035001e07405012900e055407101d00c090148030100f660b00508007108006894440140c2b0340050880d0340b10b084186952203400b510008030359000d800402141a82425160004034013900c00f5680310078000340c42400c0380aa101c805080ca5070003607500c3e2801003900914585116119411507242e011107030142e80b8400c140c50680540105000462030b82e0303400c803654010003001c80c3d61200c0e2210441752943d660f550008251000d030042d4000316000040c4c003210840c014402511034800584001c18803902401c03000300101030710b9032400e0400c82c2c0d8048007400c11000303000301c3d082c203003406049405102081c02c4c09040e580c41030b0011034110000c003c3d0842c0d40e060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 613961420 1250 613960170 613960223
    0x1509031106091c0606080109290405060106200106030305131a07150f14060102070504020f090907110f03030f01080105040b0a05190e16081603170403150504 69
    0x100036080f080079501201c8408030040040c3c1088503031070707110b100100f10302c40244a2200850701522506442500b51010070503241c1c42000c100742c2103103004003040041900028482e0458001c3e00c0d091040400c1e400d00c141c5602000a407401c001d5081002c0042810341c0013018000400c107182c11082c030260f41312854503500d110401c001040388000e11803040442c14101311015014180c185c0800d2110031491341d0000c448a03482c101c05541b0125081c84043d59040109001424098400314503005040d42502901e00030b094900344a0a0302800084900e0711445429807085851400c446010010382041d0f46c880e0401c484040d02c16601000000303034140305000e01401150030001e8104603448406029014000007440c14a40e48107407508841550001c0c0305106401140c000a4400b0301d45a15040c165600280c1c0104441e40c0200701d903540c1404d0340e002e41e108882d880144850550791440600086000d90340c8040c0100801c21440100184107401c071603c110710880700300118501d13a09140901c0c08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 613962670 1250 613961420 613961437
    0x30a150f060329010f0c020d0521130312090302060408010e010b041103070309110a0603051e06090f040203010f020a051c0204080d1b0501090302150901050403050904151509031106 79
    0x60341c141135004005072202c407801031909800440c15a000301e031480820003011500c43e8428040d0301151401c1c0d0046841c8819040619440c000e48030050b06064070040c0006402d50b04071250f0102e046006102003030045501030a0262159502d4400a00134041400407103169400c00f15003140c2072a107072040c402414403840c2144e0458540c08801c4004106008003210703d041c904002480301d0b640d107050180107106c0781e030300030603c0d280c11040d00007810010b580c3c0c0c1a0100341802413000c0c5940da01c41d015445012240c4000c40c41c3e4407400001d014001c60a40294090710005542c0c011b140d12030010484d00040b40940210800d14200401c200d20070b82c41003405035009844c107004031500ca24800383c86441c85201540040d121500d6507070852f50a041c041340942c1c07000c6410010500b4114030150322a541c00000c01113460700c0d4401401a12501040e103100f9039942c1c5444d183c0c1c40c110000c440243c01001030300d417000081c040c4003030b1000a15000988226005680301c07283c074509901210901d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 613963920 1250 613962670 613962731
    0x50d020d030e01021f09050c040e1c030228020f06011401050a02010e0f012a1202070f050d320406030b0312030f040c05030c0114030a150f0603 63
    0x80d0098504440b855015040d060440c00740d407560340c000d03100c5081e01d40c4c0650600540012828882d19009241c4010348800c0c60060b4140080c040028401056030004500d1030403400302c88480c0380400710020710555180e58070001103c0d2001d0240c10990401c141054159000c851080f06140c00700b5030b955000744210f000042c540841d0503c035501c9100500382c6e8041c1070001040c12400c507046203042480729092401543e40d54403910500c9040421100702030002d030f14202140c041d880303a0041000015408804506400040d95801c01904042030405141c011049d07468002007000010024130010010344101e00c0640040b060003000321014a6403819141182d41c9000d00d0a18294041d00e4812803913036050088180d0a192041000025442087e10014042403071400380f428001c551619000107000740d0160081e40e00990300108088080c016400d0710b10307103d695120064000c3c2c0291141c042c00d072403101e200090500602d08240096901d151018080c8209596506c0b408103100449003651 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 613965170 1250 613963920 613963939
    0x13030801060c201c05010e0d180302090411043305010c0209040204110f0c10051e04080f0f0c0705010e150a0210021c06060207292101030b01050d02 65
    0xe015041545030020107000d440f103040710004c41003448a44002000a44842e51201d004546044c4140426070314640c60f800e01c00c00311080c00c4d480d1400c030101804001c0c000c0940e1408981400f1058803401901d07800100305022031107110708805d04801027504945210422114000820202e5080e60410313150f0613550005246055000c20919210140081c0d81103a50380016100c000000390003031024102c0441816668034140301d6442c03908080c6480758060a180c803080c480500404840207210002e002d40c000702644550624441d03a02c105842ca1420f994001101004c0c0120a0003506403980c105080c0e0300002e0f070b0f03000151954400c000c1c031582d1103c4407000000005040300050a100c40d844e10440d00c2c0082040005001c9038020707100440c1310808201c0d0f40c0f000e411789002d0f44014140c1c0d84083c06005203424400b030784000074500d1800d115a08810303900d034080d0710b400030b866400283d4841d80d000f6400e11400c000514030207010940780760214000110302d80c244840c0c01c030b0609d980940504c0c1c1c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 613966420 1250 613965170 613965203
    0x207062a031e0f11031006080106080f010e0702160f050108011a07031d0a0b04171507050a02100504030c1a0118020c1504031d030a050304050906150313030801060c 72
    0x280700e207003c40442d42d980ea10040340c810404601561040814601e24010103050920113010766405070b2000040000e100200a15011599007460450381c1c09a0704180c02e840f012401e03810110f0040e03243c02c00d16903299000501a60642506044940a03242e0401c540d807514103072100481c8043c01c450119004002c0040080d2281c01c0b1000400c100e150600801390300c02c00012840c00c43c9a10400f50000041810300050091020490f408450b4bc8000c14510f0008030800054500040c0304200303105000c981410000d0003402412100c0400b00e10820040c541464094201c0c000408207403007117125220443c0c10441c80d842180c1c140d503540c85044205490360300c5420040e51011554480c0f90060214402c110121214040d02a80c466142e41c2c40101c451303400150707208507074007180384260302407801c14000c91000310884003540c100780d40b048583d507140c102240120120000c6840002400400c00c00d0000d040d80c1f00300841c42c880c0d5202e61640e40d03110720440f9004820107000d040703041102e001d05c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 613967670 1250 613966420 613966481
    0x90705031512030a0e0d060f0c171006050c030408010e0615011805040b0604050306090a0308070903080409150b0703031a06041d04020a080a03030e0c120604060b040207062a03 77
    0x10178401d004040401581e1203503586410f45000004041d0320703e407146000d90300c80740c00c001007518201b00e4800c590701ca450940a0701030504a14843c0f0014000001041c0e03a85010900c1264080c1044000a1240c04990030b5090342d110012500b04214284ca605629200c0d071003040c0055441031003c0c84503443e0343c1450100700003010050045640711004200c00207103500d090200620510502e000340c14900041d003005407802c139005041404024007000d0510002c4d65035000d031419590070040005038001e003a010514502d91682119101540201c1d00038201039060300550407804c40303501080012900c40c001d2141501841c017442c828040140010f50750300d004158610751003800101420b84d07095980070382030b04018202c001a00002e44807103099003490410400d0003100312040d5400e0a8003190014403a4843c50050300c020301058a03200c00d00302a40d04c0f43c041c4c81c0408e4120030100801d03e44403c00f508141c4089039050a02c00c04c0c5104510140c0c000d205103c030307038100050441c03c80314200b074481 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 613968920 1250 613967670 613967687
    0xf08072c0a090b0a02120a06060c1403130f1d01060909020c0c0a090b03010e0703020904080313050601061e0806010912080d06030b0403090e09031611090705031512030a 74
    0x1c1c1c481603070750158400400c0c0c00d071515074001e0b0f812080061350ba84008414240c2034500401d0001c103181085000c120a130b500801030001c8541003001402c0c42103608140ea421403048880d01a000c2030200400301c4c440006220280882d9600b2040400ca4500508210142202441000089440d00d2000c02200c4825001003142e4081c40c001c0c1c03000c0b494280005040200c01d070b00000c030300556452180c280b40c00d0034031a20304920385030340082c0707119450b55001818040700240001d200c44004808500700b806014110398403554004c040e500e0542c2c581000070032600e2480510103092000042c0700c0d40441c041c506160042d88103955510f0700a0a1611149803003248542c1200c1c101020001ea004814107445100040c61045844c040c1c5418581001800300c180c94200a091441c00024400c0d052800800c4940000685040301c6026520b8201798014030f11010302280c000308041c04100d800d650190003103208201241244014a00c50780c240811180d0a02594050341d1080000030700560040c10070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 613970170 1250 613968920 613968931
    0x105060a0e07030e0d0807020c0d02060f0c070e15180906010e1b0c0312090304270b03010e0606040c050412140f070806040302010c050c0c09041b0f08072c 68
    0x810380c2a044400d1510380700417400c403200040c10031018031040c50340c140260038500304110350f500c4440803150000b503510b100d218200b6811b88000102c00c00c03203c1d4244881402402e0113060345825250841a0a9400e0510380d48917100d01043d080300d080600705000d5007405450900018400303a800c01000e1201c02c040942018140c00a0f60148540c209008004080c0010890095500d440036a0b608400008014291303050355001440180a44169461100407124003d40d000c050040456110b90041880449464065081041181071134000082250240800391010007554010110403101e44c0a18092a104e840c0000c001c1c0c00415050020f40171802d01c0c032003c0c4c0e9044544001203a181c0403007503216082a401543c01c101c1415020711810840000c40e04109103404c040c04102c98481d23296041d66489007501b080030600b40410900054058603040d44a194040d0b154030300d0311001d202e60306c100c004a01c43c0c5180441c0308482078900c1c0740940e000440e4401040480c540f24669203000400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 613971420 1250 613970170 613970177
    0x1302040906080a02120111030a020703030f06140907031107060e070f0609061701270908180f0d0c15141801080714030a0f0207021305180105060a0e07 66
    0x411284610711075800206030840043c50403e0052060180070020728114241d180d1510398001c0c1c5280011080b260301040c4c038040183e031750b2541d103010b9004100d514141c030802490802c01203903c00c1041c40f0f5880242c0115000403003569800f50403000e030340d40760b4031503201001d05000090008101d40c000000c401806000d9803590341d00c606120201d003869612210004100c0c3d241000b0903504001c5984181d03009841101e41581080311b4190700d94901e0700030f545c8668901078554454104e56020005440d80070403240d80c0d8121080c0c0c2d0120403130380c500c0054442c0f907525600c030314a40b900c2c0008034140c0358400103190000c0d103020041a51548400300000512200444241140c1c201400900307142844135007049244800400041014100826070401e100d40786110030845a4124156540315621240c00b1681c41c00b0b0750102c4029000d0711000940010414001e17408100041d0032092256006a0b40140c4400e261004e5038240d80050300c01d6a00014030311010f100c0e0440101c0400da02000a04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 613972670 1250 613971420 613971427
    0x9090b0a031a072309090a180c08240612250f05060a09140109180609051e012903070f0908030a17040c0b070b040c09020304030e1302 59
    0x8680c6149600b4460801960100c40410400380c16001620f0348216003641c207809094154801e207284040c842d8540081c400d41c03103040000d403407010903003041008034010ba03000d550140192508142d5103c0354058080315020303900c288402e8000c460b0600c003d00700e10f20342254054440390280700580d0105071114031103005c2c02c1c1300c040c1800c041c40303138406255a006200c60f603400d207000848018061a03400180c4107480030455003e8080d40f005604050320911b030052040e0b0000e02005031040d02c1c055000c81e1118a0010002c050000f0a6000340200d5081c05c009101e1a43e44d1840300d6801e070b0f40e41e8000801d515101005008c55005050094208001d9144054800030070994140c1590001c4442c40002550030070000f910369032107094000105140c000441c00c014016101a1009c2916010807c00e000b90340d001a092041c07414013000107091000845545202605140800100c219425202d116452030300080143c1c00d4800c60f4800c40e0580d581003404041d002c104000c0d507142c1208442d2081e02070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 613973920 1250 613972670 613972673
    0x7022107050111120f0601052701020c10090e060402040503071e090501120302010b0f011704050c0a0305100605150d02030601030b04180515160c030c05010f0915060609090b0a03 78
    0x840062007070810880741c549013441c0a4034801c041005c020440d80c10050107008100c140040d07038400001814120741d40031490a50100103c1c9042c101d40c0c0095400b200220b02e481f050341e0403203800b170240d03008002024100d0f6690000d1009a00c114032415130035078000c500400ca00e07840d0480d038000301510a05406040c5507200000d03020b44100f82c014904202c3ca41044800300742e024401c8220b0800c0030703240150031401d4000060184c2c03401e020707d9840203c2d034600140400c0401d2107034150b1040e0041c00d80701c200340c90341400c981d100030091f00f802c10b162410744086030714680f450030003d0079100640028540604010f0407006500044e011a050644881c0d4681996070b89009031541d04000e02c020850445150601f01c4c9091000c00c100e0000c0e640803070903c82c070a04902585030948035641070034036030b000741e0745800c60700302c019520702400c1540f9000c02046d0b03800d0243c01444900d4044d00da43c40040c403401c0a5141210541c0c070503440442c403a01020002240143c11403d10018010986101207a0700e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 613975170 1250 613973920 613973951
    0x50a0506071b14190f090f0f050f0403080702070b0f0f162a03050304060c03110303090a0b0105041b110f1903090e040f0305030a060320030105070221070501 69
    0x258014869000c11405000030908255a50b2080c100e01301c2500d14205103000c900d00000900c034080d41040030340301c4c034802e42242e006800c0303880c0c0340b411054200080c1c54420012284120227582c03c0300011540e401040e5201e1001601c4015601c002109030710b00120304071040d040e07902a85194101c030a06110315200502101c3c00558075a000f02a40400941903a40c00044c4030206121000740e5840c400f0300b40003142c0b0000c00d0b03c4c2542c01c20b05100b0100415070406496070031181a84c40c101e88000030821903010b2000c104101c4c820701c1941c07400800d90320382d0200070989981500c81e00c11540d46041240c00103102e001b90124410102d02a91301c0750340120b0304542460550400e0410a042c0102c079035040641c0158020028460721560300e0080c103056442c2d60b24a40340104c06001c2000100118a40807220740c4840d0003103510100703000003540d49103440a880c100d054403882c401d51070040081e11441c004200f048503c41050b00d00b400c108103480c0f40a129802000c41a130312990303998030750401000c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 613976420 1250 613975170 613975223
    0x903050a0b0a0c2303100b04030f20091b0f12060a05041b030903030f0c02010f0b04020903070b0d020705060108031312030504030209090f10021c06050a050607 70
    0x80c030481c00c507440c1c044070241c1500d4140722028108030109000820703c51004d02000142030101c3d00072560fa4032424098150004140c011001c104000100002008082e2030b9008085100340c2c6000400c201e610461400305011003045908002e070f1030001201a1768224001ba0b003500d18040c001c3c24000d0790030303083d0110381103140f0324800c013202c44d402e1001c10b00d044c2d100304005140c100d80500009501031946440d00014603000c0041c5a02d40b07038a4420107000c3d8020150780300c10720104104010040d50020f029209412000030010700d0001401c090382070034000c580c402e0704090004e015651070000c1e503013941d500c00080c0039a51503082c8a4000000d10512445000700440350085840780c4103818880a2312903a648841ca04070384004011001070380110644049940441d500403240d41d0f0108a581880b81640542605001d81e8180e0f0300311000a5000e040070b290000005284011070364101c408070341085c082d0310351001070b00741c08102515180009003215441007844145d40c1c0343c10010b20a4008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 613977670 1250 613976420 613976423
    0x30c0c100c1206081c1b021c0201030f110412050a0821010806090d03020d020c06070203030a110408060f220b0105090a0b2b0515010906080d02120a0903050a 69
    0x2000b07101d0841110242d401402c01914512015141d1800303c07000744800b08000c3c0c0c6401c400c0c82041e0124002c40080c0c40310a89580e6005000f41c0e2a5801142c6d11410100f180001240403900d001c9503032070120081c9c8039111002e81c01207885441d040c01e10024003402c441912080301e0391311800c2165030000f441080a091245445c14030100360f8000089002c1c03a41070705801520b402e80c0b080080224000300011400c0000c00c09040069403a00c00d035400d94003034814940031020720711454045c40511703a8000021031041e45440703820000e004038040c1c81002c074400d40c4076452030765200320081603022080d441002c0d004402100c1d04108810a511307440c4000280d5003007941c0c2d2a00c0c1e5401049a424040d0280740d200700c03040010044036a201001031408000c080401c6070f40c40b0016080444401d90100d04ca15603a00b220483c3c0c007902c40d4020450a04109009082400d424400000740405001a0b0b00c08034940c20380140400342d104140507111900031203010b80c1080020710380000401d030240300d0030040300d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 613978920 1250 613977670 613977677
    0x9010603140606120a05250503011505100201020a050301090c110f07031506030302190503041d01090c14030403050f0712170f010501020d230a09030302060912030c0c100c 75
    0x1483d004041113074104e4212040c0f0042e801c0b4942c0c51001402c003044030a030842e10600e98120b10f100c14103100100c030015800140e0550301e850004145200103500d040c04036181143c122401c1034180108a00780d00604e85e00e080404c109100604c484031a0350040d443c04502450005840074403012010702d00150701c0c0048150b81c000c00d9007801030080341104200c090329119414020b0900e50b690007036035a2400616020f5045200083c1400c000d0240219001410711404000c4005440c0b215448803610038404c0f4250303239280601d42c02103075019180b02c0000124070111142156030350388069030a50300640e4900551603003045032a0021340d01590100942110b03985000110181c8104444100d6014259610119002c0d0040000b40c1e80010421550403182c5001d4001d04501158141ca8001701c1900307080341d040c00715241d042541d200500208a80c040c0d0b00300c440a071905d00c4255202e2051036117144c0c01e25000c00010711100c06610042c48550704500448080b4003103450034004442203042c444001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 613980170 1250 613978920 613978933
    0x9020a060c0c0509010e070309020112050106021e01142e140915030d180e1302031b0310020703050715020c0106230f03193c020105030901060314 64
    0x500000002c034001410302078400f2002075041401407008000001c01900c1019101d400792011a41314000d08000c0d2120724000340504c0d40c480710003a4031503840c00082690320308070303c0b055041000140184080e104003215400a03d484060660442d0103048440d160100d144000c4200c0d4102920501d05c02008a41c805000d540c48040030485001c0020b48240036a41e9900311443d00d80e5004604202c001e0101c1c00c100c512030b40d121500c070040e685298004141a94042d04000c421010f45400c128918400c8060f645141c1905c4400d0040b0035118019540580c000c50707182c11092200e85c018035581c0d00a003401410031071103a0705d1030403029076460030208950b000f083c0017000b040240540c00281080f481c030042c1c3c4000c44100550036080e511410b511886000303440c442a91024080605042d0f06600340d06c140950506001d9130920b5004a000f2206590051041c030345202c00305580922105180050640e00c980c2e001107a00750805018122155643c0b03030000002482029152450385100d0054401c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 613981420 1250 613980170 613980173
    0x7050a061b05130905130609060603060b01090f0b070f05060702010e010608010e121803060429130b0c1303050a05070f0e040b09030910031a0a051806030109020a060c 73
    0x4014016080940602c60103010303845901d1420001c080955400722400581c030340ea410b0b9942e104d5400040003914661900520109201040d00000166405450b00344102d01c1b241004544040e0b4600c01c2e4243c810b075210040c41224070000042c4850350203915800c40001540c6c4031039051040c1a1003003400350703660b01009480050217014010040071090f000308280302c00c200075261662420395018083c0f010000b145105c010580443d0800214085c00701c40580c0f800d490021844c0c205025800c11050003c8201040211040c410034400c522440c81118a400c641e91640c80c070000180c260350102d507081c000c4110b00c5407003500c00e82c0110700502c01803082510b41d003000307410280c05821170744141d92000014061f00c0722010b521a08254040401d100903a140d903907440c2180211403006174003480406450542a07030540150701042010b910804201c0c000740d040107908407007441095080b283c03001c5042d2071800703140724207548014003900202d0005040d600258020550390880000f00e54902c11420 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 613982670 1250 613981420 613981451
    0x421061a0a090203072a0602070f1709060403122a2003071e030605010e0f060102011406120106030c0306051602030a0c1e0b251805011407050a06 64
    0x200401000700b0441c40e509000000510114140310341c0c81c0d00e85010500301c04404000284141a1500140115200e468524189041d00308401c5e05407203030a602d610a81d00c0084c800122158240c00070729062825103580d803010b1800e055004900103012030703915108040c11105d4984400b002c8868802448825580351070200042c8403001c102c800000040b81c40000d07200051a801aa141c0070488040403ca8a40300c07415402940c00081002e0705080001500520445400c0c2c00740d8808804000a030391448012800c03248030342e81d810314503190940402c00a0a00550010100055000204d18280c40e80c0301d0b2002640750358001c81e09140e03544100441e41c120280554404445032003c0c61404013245802083c02c0880203020f043c0300c0138110b55040031200c00070041011940306281c017a032860700551204044c20050a010b9440f00e00b54682d140346880390221000780c2903101c1042c141a4104001182c6440191100282160080140c4004960104130040c5101e1007030380301041c2100c4c00544003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 613983920 1250 613982670 613982689
    0x105070203030a27111f0207050a06053105040e03090103140702060a0515130b0901050409081206120f0d1d060315150c03070b010b070203030421061a 66
    0x300100d008101c075802c540502c0070718602010b500407182a100100b4200081c6e0365410324070030040c1580000b00382208250300402c4440407100200c60720501c1503a1a40d0541d9244201e106c100003214801c00a250b914289581d10fa0a640d2021070081c0c50f40c1c0c440002c9422550f1050310182d0561010a550b1000e690600803009101051030300c03a1628101090007941c0c6810140c03100d0500c585600001c0c0135142d1417801d0024010001b403216003200c08500ca658003d02c05408041e005d0344060f0008510707402c140c000c28008941c80403000d850600f502c4140d01c01d84102800082c0e0042e1909104403848400700401c1e034107901d018000d014031340200000a000c0310224800b4500301480381e070b4000103941c0c0d400c040d03d51041c900301c521016501901c0000f0a9101040b260b09087d6802203200d550600c00080940340092041c11004583d9032a50905881c40c017500c98000e5140c1e10410050200c012542400742c1010442d220440303030b103044d5035541c05c01d43da0280120010300c40102d505044500d481400c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 613985170 1250 613983920 613983941
    0x40b031b0a020d0f020a0605160306170c12010e01022710080a090f290114150a05090a0b0a02010f0515280311100215130f02030105070203030a 63
    0x24585440240c0103902d480d2103c0400c814080284080580c85000303004484000d64008405c00c028541000802074680c101c00e00316002074988400070800b141c402140070172000090005001c0c03d0680c0b403c0050131085005841c0d40b03952149480341801c4001d0016100034001044040340c180f8210244507055046108018420f918854a050b80260080003903900214160004640b840aa08025250a55101004195004d10707411240c4e4998180425090502c2c03900458610381d83e180d00c01a090410140c01c113522441544624198447d071100905000b481070510600f401e0800000440540b604d0380310b0440c5410008808164179420302c646000070750b07004010407242c100b200c007284240c422801d00718010307105200d51400d9180c808a402d1802c0311003010f50040b41d5101c0ca4410800c20081c410140180c00d07003412000d030203001040c507080d2010702480343c0b04281d8414407046003502480805603017071001011100d0150320203010b010310a541d10f400644e0389052401c51f050441d4000400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 613986420 1250 613985170 613985221
    0xf1f050103030c0807051c08090d0314131502180f010c0b060f010302091f0e1f08070302070f1407091a06090117040c060806040507120e0f03040b03 65
    0x41c030000e6000014500c03241c1e000340d061901d60b0034034900f85140091003154203400d1880d07070103c3d91000740c0c01400e1920541d403800a403448502803480503800c0d10328103440300c841800c9481c001400341071100c0e074401078140113602b02a00c41e150b000074101240c3c018281c160310880701b070280110038202582003000460b070030311300098400ca0035200c07807443c990007604080c4a80b07002005050703240e120350140c40765a100102904e0110300d108804170010082d0404903008540003400e018420320f088281100c0160900010903511213071900b0440340300ea8014901c4080c10303824003040c008181c8034035021020a1144100049209195100b180380104d1548000c20031403e028050215680e07107400d24868078002d490803511a42890300583d0440391544001d210b00ea14482084148400c01d01d20a040360450340711154107031608004d100a0358021140341012987c294590f0700700805030b40c0504801d031601010707548060040e000c0241168001e070300c0103030321200c0481070012000300f041c100030408900d9130 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 613987670 1250 613986420 613986431
    0x806090c0a0e0d03030e030a0507050105090a0209040311070f0308030714130512100504200301020306010f0c0c05130b01021b10080c0408010f020c1b010206011401110f1f 75
    0x2000822141d0724400c0c080c000c00c0510f508a08140c06508031800c148421025640c0b01c0f143c1a0000381150007100e1b0a4a456092001007019a000480c0103540650081c3c8038011a40d11a03c040d5032895100c0d2401c8060f2103000800a181145c0000010156210703004041da2801c1c42c2e80010040310074503421800445003041519180c8807603c0c5018121174050301c009a1958074104108d0915a4480030070b44051700f06400c201c10004900548200440c5048442c00d1240404d000c0c11b08034081101e419000c82e000c282200c0c24a402403840040c414420303101c0184803074071440400c80707030840c00140d6008291640c28903030841d81c06101c0b80c4000a030426103401c503900100c0028850100e0000d500051102c002d0215560800c1c07032088070040d0200740c1c028031447e01c444c520b4100950044d02450301ca405142c900030710458445000c1c540c1e2440585c01441e0b141d00b007034550a00c030350554112a0510070084070341c4201303950074010150880c90b28000782c01c0c10688080b40c07001000249000c1080a881d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 613988920 1250 613987670 613987687
    0xb180c060a0f02010e01020c072102061204060221010f0506070503191107081f0e0a2a150906170106080c0c0118020a0503010903091203020c100806090c 67
    0x2610040c10729407510700c082044141d001d90040c400d0400720011940001400202c2420019401045680958007048940100c080144880038a414001c0d40900700700102d0240c00e03ca4015290041d00408005127030071040481400e0401d01d140c030f554481c4261800400411036078000240003000240c451516201c0309540741516442200d04a0365407a20641c0001d4100d07100d205640d02403d03800e81220388c2c4648820000390f99101c0000c8407400f03240104518640c0c000d0b2030280c1c60459040d107008010711103e0340c0c2d9581540360f010b000c0e03c407240009100ca42d04244682201c00081c01e030032001c1d074401c4e10240d00042220f0240c2c0c00c00c00900265805102c00384100ca60b01c241111141c1c0303494285510345104022841c8205810a02d0369820844580d41543d40310f04003c071201d01c01c030b4202c03010341c0d038403800e141c203983c3d201c0300c050003107100c024080007901002d1b4401c045051091056032558604c0b04001100b9800b00305110303000500c5801041040c2c10304041454100840140550800004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 613990170 1250 613988920 613988929
    0x30e06100e060402030717132001020a0f020102010b150c1905030a0804020f06030f0f060a050604090b060c060709090c03150b0703031416090e010806040201140706090b180c 76
    0xb404070350189a00000140e5aa4820a0028012455031004100905060701810300d0700e008000f061b00c4070300500c102c0b0341010400c840c98107284076068014100f0080d140d200d080d0101c40d003c0c4183c0c1555201c0c030f0001c0255503440003041300ca03011101215100c8500c1d200583c1b0301400c25040300082100c0000b0349001c50000420381e40107000c503180940e00c2d5980c0d4404950740400150510360003d1000c418010341020301e01a4910541c0443e030288019a6000c00b002481d00d00c03807040503044102040180210f0010350086012600c1c05001c1c0d40c5402c0e0001c40451404408842400c00a2540803051007801c50710b01aa500010040c03030305001c456041d00760800d0607441032054140a0800040d40d00806003e5000500095404009012075181050b00044460310702c0c2080000103810f1134020a00650000240741a04d002c01e0040035199150f81c01520a014019445040c00205104000c00154503006030300800e445111411000e0030b080c1b10203031003c02c807485003840d1908001c46c0c03550240c68 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 613991420 1250 613990170 613990199
    0x3050c030601050f0a0203040801050a0614010c320a1217010e060907031515090b030103110d050f06090a02090a0b030d080604020d050103110a0b0c06060103020f19030e0610 76
    0x107041da000d17903140c40b010010784c070f10f00c07895102110759400d001c1000802080b50780180c0482e601c400e422242c01c081007004691040c82164001c18901034070721800081640c030802e026a180900100400200340309013401c0c54040b080d0411509034801410303922100340d01102c0601001c4200030242e006504240f0340b0400c1c03c900030802400b0303003440800140c5551094110040300c500e502d4030000403940f251302221a50400c600301d0004242c050314002040b007040c500303e81c100c0e03401c20801d88031254128100b08944040b1314098031540324020141703003200030600c00c46000d222000c0041109500f6403060250090000303080c58642c61401d6002892034401023211044071400e440e00120580e01c041c0040c000380603000c101da010f1480c1070008804c01030780140c00042d00d030b000c07a030000003a60781b030390280e01030720442c203d410300d90300402c0210300c055000e6006440181c0b1a2207015082c0000161250440861640640d000a4582c4400381c1400c0040c005a90002d0346420591903030b80c1041c1102c0c90060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 613992670 1250 613991420 613991437
    0x3140405030f090a0e1f08030a0c170403050d08070807030204050306071808011107020f0f03070b0f0d0507050a1e091202190e0411180406021b01020a050a03050c03060105 75
    0x2c800041000d000e40d244203082c2c000d820010b15000450400361009000038004920310070860f81d01c080c0c0410380b00c0c3d0000030b88541013015074a440c0f0500c480d640e00e1010440040810b04da910003800f02100060040c0b1840700d6928841d55584020b00d0175442c0282407010103000a824507104200911050710041440395004001d4204060700e140c0201c407488200c031160b4818074655203840d03112080d20451500501c04180212180b4603807069440c1000000450904501c1d803640c011801040354400f0301d4040c106003160014001c0c00c201c098010700f0b098401c200e0360280003880000b4030207005600400c10a8582c0785100a0040700c5540300e50103031003069603000d082d9640043d00080c4c4115650380d00c2c03c2c445a403074204c1e801d0700c9aa0742d043e108042401034400b00c80300c0b4607601201c2c00e175080004900d80800d00210744c3e080146c0300c91f00c9040007503214219642c0c2110001c2c020540b880c9090009100c4022142c1d201545e40c0d1104038020102d0301d0140658126010800a00841c0da910500342c07441c54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 613993920 1250 613992670 613992697
    0xe151509070806010c080d02180a0f0314011b032f09040e070b0d050601080a050919020d0b090d090609050d11010c061104031103010b1813051501060314040503 70
    0x40c3c4441c401615403011604004102800c0003507040c0f42ca207201d4010f0142a01c454801c050541c1c4600200300d4528814080d440b0020000482003011a260400c5900c0501d9108e000140400d11052103031a00f2100c0340700100440d460700491224036005418090360410700180102900301d8003c1036081c01e01c40c4080c80d07840340c0d44403044403e40040038000e080051132640c0c040d555604040311198050039040354803a01207586400040c48800300303406118460308129010b40031f88101c11401c00c10361071610303909076042840282c0c2d41d00003950807a8058002c4001c3e400600744000c0ca10002407010155030450070410080b04004c21003900da0362030340d18041c2d61190f41048425405001210b8040d030940303004c0d244900304075600142a101500034070030703640240d1090031403041220505090ba24400d115036080a4040d000e8529a8040200950000145003100c0e500141d03a07107a603440c00504480510282050100410207550540314400c8071180b0010300c00d00394a03194031070946a005141c2041000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 613995170 1250 613993920 613993937
    0x30905151606050703052d07090b2805090a050d02061e040302010e0406120b04080f0403061a03190f0c0e0a0219051806070f02040e15150907 62
    0x8100880c000c1d15800c5448410a0904004604010016141c1510003034086482d00000c90402968030030314030291031080f1800c082917002c0c0001d211032450002d220070b04110540b9004540f581c407aa00926055480f640c0421400943e040c42c2000c001514070344609002c801c0248000d07644074051000211001110f1851020040b800824841c0c41103845004800c5020b203103025a4445c05c0001e030041d6030003a41c582c8440040c0205000407a102e81c003075114603000600d80c05c00012002481144d000748140e5000d410301c14030b03010350252500709802c1220001d8441146a55180304190503800f440c03002c0b8000c001d920401a004140b03004046405003925011b03510040034484009000401400c0030501d4400c0d900e00000001e009400c504210b00e20700300c0c182005800c440c860420f036003281801180c007141032024802040680d500c038500c06c45001d00300a000d40b000d40d54920030f120603545210702a0440400440c240704a22600801c0310303851640b80c080304645c5460300003817158800141c1c10305003075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 613996420 1250 613995170 613995199
    0x151b16060b0415051509030a1202060601030501061e0c06021611060403121115070c151a0f0a081005010509010608090d030209010c050a060e01060605041d0c1b0a140a030905 76
    0x544070340704030b1b07581611418100c0b078204204031410b89480781140d030030b4400544540d401101541d00c02c0c410100042e02c60420f12810b0742e6036a04c54062000e990422210305800e5035201002ea070000c40e40c20411200c0152103005000c1e0b160b104200070343c02280c100b4a090f08580c3e42c0d485510903c1462800c00c4105002004600020040100504040c0c12074000c03034a0941001404000040d00464071705121007071682146410740104030b014411603040902c0350301800144810180c0405406511110680000442e48010b00405c00c1d01424080d01082c1c40d030501c5d09000481740d060780144108134168042006800d4049500c0c0e480e80c2082c5800340c1d4032110000125030b0400c2044000d805400341d2100744080200a601000024040e0720007031141981d81d850980d040e0045128035642e4059803030310207001c0c005902c1e8103948140110710842c101004840b0803098454880f094402691041d0040c03000e001614140b01800c103a1040144010001550020b200411a11406008084900d101c1300f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 613997670 1250 613996420 613996459
    0x2125120b040804090e01060311010c0210080a060b040807151b080d110d09061a13050403050c070f06170c1909090e10061502151b16060b041505 63
    0x600130146101c00780103441d01c101c4d04a0080103284011610710021300038254007035006003100134085800901c02c0c1c84c440c858580a450307003000280380c0c80c03030281d96100224401007001d020b80094020103000b494074134140f180000d0503da44a00d02c13414003484040da694281a551002c42c03c5640c03012100d51241401c028000c064441540c280e659440d01084a8207080d4480e400814644e0140d0000c0c05600707000220900311030602c2ca08140c201c030080b156100300b100c942e0402e94100e84289401c61038800ca41c0021402c040050b007040c20748040d0719104120301030340215105003862101c0b0705020141407000c40010750b840b8038585144800c440051307c01c8041e0203a6403200c010030001d0000d00442c2180802c86446006403128102801d250020128940c2010044c5500b15070454009114081b548030110400c204020184d800c10b00e640040c1407500c601704006400650300c60a124041c000345032800400341d6030170324031040c00303189403800702c2d0102d030b40000c415000c0301d0069500c6100e0881000031134 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 613998920 1250 613997670 613997677
    0x90301060909170f160614040501090317071205100e010b040e090304121103100626070614031302030d080405011406150706020f0f071208160e2125120b0408 69
    0x40a25a00102c100014030078190454bd076024480d0b0b9503420030300b8080408a00d00e03c01070b68883c0001d4900b000c2d11302031018940c400380d04012280344c0d0035115903507813070000e003004401d8022220703002011804020b0501c3c082c0000da0019400700140d41800d04107050b069a03502615400380c0320902c1d0b48010011a20140001111589901e40510940b51100fa524040c4815071618448240c40c44c1c00c607070004000866080107403851a501d0120702c1c0c690302001d8481c1c3e00050008018410181800001680c08108101e00c0f02110388801c8440c2c60a81052421221603000311182845102d0422420380d40c1c1c01c02404440e01c1034910341d6103461803818010024082c0b403031882800480003442c02070000f5000d002d00b030000d2144494000c0b40001803401c50f03d5800903100c03c410203200d0082c41202c1401142040d050030006420203208016a10301c42c80c08c81c0c0d5001e9105a250030038003465103030035500242114825030400c6010f010340e00c0d1541841e0310424450b80a01350090080114040241403000c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 614000170 1250 613998920 613998941
    0xa03080403111809121b070902040f0f0b030a0504081207021509010902010c02010f02010b0604140418030504150509030d03051803040302130c02030c031209010605010e031011090301060909170f1606 87
    0x12511116190362048000b91300a0141d1102218050000201140c400301d1410030340e4407022000c3d0940c2c4a1007841e2010c0d000c0903004444114040c8040401c6c140740a01c464803c2e00c160340148601e0031405c40d0b42a413104081c3c422007869040c0184400980d800c200e1504109034207181918000714003010803801400320500c4039500100c0042c002520020545509141e503004884c10000d181100100d080360005461004010601c2404100690700c554552001d0800d21820818078207148800000d0820461030400004295900140b18500300302c1e03540c130860403103c1d000452070702d421078001490b0056031000c1c0c81c2002ea1030b1840c510525200f80b0550f00103e11700803c6944a052009048034410421100c0e050158a40400021103610403040411248005000340442d10942070500d00608038000c1841c0048208001c1501144c609129410081924078800100664a0315080d0600a12100d010000c1e00703090141c07101d1a5441e01c201c4c1e04c0410072403880d14228030186407050103441c18082 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 614001420 1250 614000170 614000173
    0xa1a280807051305010608041b030803010603020c06010b0c1e0114070f110c06040501030504030201140a0902130e0c09090f06070915030e1b0a03080403111809121b 72
    0x80025440800069a00681c0c20031a009005025540c021504039002441104001030300c2d240420b001c80c424002d6420204400210308000c01d441e40c607249060760003030f0f100a000a0340011402516102808514003401401d0007462401d00b03164901c66841d4407000c1401465114004102c1018a01358444d05100c00d051000b81800d10f40b021005d003100d03840400b104041004002c41d242400404145e508204800803c414103041c24070004500034500200b049003959a41c0c040203081038142d8520502c10712001d9400b18000c44c40d032040c402c1c10a01150340e414040d00b41481d0f09d00ba0800491070001050301a00d4030f00140d80e40171003280c81d02e030a810b000c01c283c0c060a024490000e62200000080c3d42c01880c2020100344030640440c00c4441031046040c564101e1034560400f100600945440f10340d00501000d180e036200d880741c2141d03900a603c2102d0f0000d140305400340768105034182040c14200d041c000ca103030389003103003103603498a52441c9000c810f0040058900c07408190100051f0200c6a01030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 614002670 1250 614001420 614001499
    0x300209130e0a020907020705030307060c110a060c03060e04020f060a0c15050103031b020a03030e030f0106140a0e040b1501030207060f05180327010309080a0e04050a1a 74
    0x1004a0302e4041c03050b030a80c0100d41c05000075480c1800001c462007201e00144c000c625000b03454803158010070940715403400300102c040e41c1d200120000c1003005000c5000361400641c491145070003070110f83d619400107448104250402c405641d4204d65070001c454150b8901c0e0b03a44580000c100c444021812000f442c5c007101e214990030f10003040c1e003c075040c0c2e807080d00c1e40300000c811101000c0510038802002940030401d4627040c00060300c584038080340100d001c0c3c1164040c0300811009825500780e9000603203d810300c08007600c3c0c1442c1c403c1501c40186280140c40802e8102034952295102c8000c2101804003085050b1262a0b4441d03130440b44417941280702040301c10a4102444081c0070191214041c0b4000e003150408600700110844007200600c1c4107042400500140d0b004040d035000600030b0500d0341e01c50308600880e0346d2000070011400c00369211201d4482020410046800241c15107a20341e1034800c410714140403204200c01c04409c1100c10702651039240345241c4200031007203982500ca11421 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 614003920 1250 614002670 614002691
    0x307141813020f0405010302030604020d02010e0a08031c15091e09050a0b0c0a0f0806030a08070c090c17060112200a02100203060108040b18030f040630020913 70
    0x1291080c001da1003160351100c444800402c00090344c00078000130750b042d000040800d00625011141c561840d2040c1403259044206400042d02d41015a11101c407e4000007140da126101981441c042200c201c88200b00c00f4150019144043c10140940c500d51070b82d9030000601000c6041c001c0018200b6031900344844c0d111480c1185d21280d42e1817049400e83c0c1d82c034010408006010003507682541c5640c0e58204c0321030b0500d00413103030004c010300309035011f005804242c804584008020105680540d1103811001c3c9800d81c444200c4900d00342200400141d0b55404903552244400281c00c02001d1800c043c40e0403845403020024003408602920034003445c4205030807143c41c00043d024880d259001c0c0c500d2000c6d00b0255106a1004a03000c0d4002002400090b00040b8040900b5401442ca00846c3c921551041d00662950b4002102d498102001050401040b58000314150350591924404107280800c00044d80d01100c0c4015188032081c0c0106001c0320380d84030b0380b14041c11040b103044107004e200c040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 614005170 1250 614003920 614003941
    0x9020706060306050f07050d020f07020411030103210834030f0b0a0e06060c0a0501020a08010f0501020f0601090507030e070e012103020718021603080601020d0e03071418 75
    0x5210864001d8100400101651040c0300401c6c415130b1140c54a91400303110740c1c032001c02075019012100f005a01070020401584851081208124070500e90aa4039411414121078000c000e14450058290000252030f07550ba1020541d80c00000011040702240b050103010400d40030000c01e00c0468180801c0400310403079054210f441a19584130f410445a15041c0902c0b030010304038041c002011040c00c02090250405800908010004505032001c074240b030f94500782607034000610780001441e904010310440c2100004080100b809000130201e0484444c0140e4403804144109420255103000041c1d16502a4001009800700041614803454031000c10801880c000e014442106001c07000804808010206041841e50143c0040c04030720b160041116160002d8104036071065000d0000c0f11500e20043e40900b080f51181c3c80c0c000151070108002441d19440c0b4000108000b0040c010714929203022070280103840348000c0400c0580428000f068018001800450191000e401000000e110f0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 614006420 1250 614005170 614005181
    0xa1d04231b0109050303090d050a021c030f0806030a0b04030504053118110105070807030509040e07122a0b03011502030702010e040e0f010f0b1212030c0309010609020706 75
    0x203a1051204800780d01004480103142400f400f50142e100300445809072078010904030140388038004035204010f00342e01245401c1d00b0070843e5800d072440010550304142d081244801c25800c2072400a407140391140020356210305000014100d0444600070509052041080b20080c10f00034088010202100200704212030060041e4000300c2001d0b00c103500e1520250280b14a0f003c008400000c51444544400e000c007584004018103005007001103800240d071f19005400c2e4035000b91102502c9005010030310003510650040202d864010301d2050050440110300301a0040d0400c0c5400040300011b10a036030324011058092020102486001403072a810500841c1a01c07000d03d10025101d07882d85040c0d940303000e0004001e0100d410b40654840a040a43c4480e2145240c142140c1801e0700320101c0320700711540400c03c003600c0c07034464103082c400d41003681541e070822041900070319007d007955680d02041c2c000035003e9000365900201291800d8403d400800c0540f0614400b15561030386c502d80b4500078103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 614007670 1250 614006420 614006443
    0x121103030c0c0601080f1c23030601030c090305060a0207030c020405100513091707050c0406082103130803070507051c0f08070914040e060112050106050a1d0423 71
    0x3c251000440c00070000b0901601c00c418a0f00141045205003400f003000764180c1020000b0809410f5101c1281c1c442500b0040381c40240c10120f43d40c0c5e060400004041d6100e20715060103120781ba60782000010000140d10741d110864480058517400c80c0c5c0782c01c4a50315090701c0080d50280c02c080900401d0404000c0f07e40c101c42d81100e401342000040e2174400266454520090462110603800d0103c0301c0c900401881624400d4003a10714600035640040c04035600354001d00069400152000380b10340d40501d2608810522186507030a40c504442c07603030781300307160084003c0100c040840407808450040069850007030f801420354202171000904852580303d0240c1300700c001a4002440f516030303801040707298080c00682c0d6a460390541802d1500f111030115045c5103822558941201070946002e100c00c501070030082c2c4046121840b18240582900c0007500803a1044150b0002048025102d01c030003400001140085c04141e0340d2401e103d000c3c444c0131500f950504102c90f542c5103c445002c182240b950 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 614008920 1250 614007670 614007673
    0x5120d1a27070e040e01151a03270f0105070305060105040e1f031406150105182e050315010504270f11090a0603060b072303162d121103030c0c 63
    0x190b48403124800c0940c0e8095944023001c04001264441e151005c03035080c8806200c015001038040203005d84c0c03600e01c4402480e151a55100c05011415034075020341600401c0c00d01e00030382800c0c14960940c0c5040f001520509c000602041800f01c445400c455400085810000c8640b0600c0ea03441f01c0c9450301c00071242980000301c8034600700d2944d802003064807108210740812a2016040b00300340498821180900c0342d152504004003c810380c00f40d9503442d4800b6003035031030a071a402d010010503c05000341480c0c50600030b040c0300600100e07240740c1c00b42c071134100c0d21145d01022040404030b0100034013510440c07542c4117081040160300c0248c800014402000c01f5190707038010a030b89040490480e449405050b036250020880c0340701240d40c5816800c1d40500c407042c0d004591451070815403a50f4010005d801c041c0e040c402a1009005242d095008034010070208003401000390704d045802814820401000a05e00090301f5080c503202c0c254151034400184100c176503c0c203103a01100e8103500941e1104005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 614010170 1250 614008920 614008961
    0xa0308060402031303080901090b070c02130624120603031d0301050f19020c070806160206060d02121903031a010e10030905120d1a27070e040e01 64
    0x5030070203100b1640300d07032030018071001010403a5800701c61146019010118564a48071454042000684140d014a02988031099080c0c61803051203004408402c3c1c1c03506c1103140500803c9a4852031a00800ba07001e6220b50030400805070308241c420030181204032815500d891004401c040d000800b13800880351520021b10508500420107080e01e40440d4030494801505010400e03242850345011483d40003030ba0090f013001540d41109290160560122103d54003100c03d200311003407464407200130141e01d880605200c1c0740c5100030840105070550003e005032010390b60700c04586400c3c0016000c56140205581400c0401c0c14014040d0407001269190420500c140c4a21580a1403420114031340c003800024242e0b0003140150000c0c010904e095071a40221030b01c1c46000003509004000d070b95045a000100d050100408154003081c101307101e4000c034080741b28107000e91064040c00a29502943c040000c6a407140c2c011038803a9120480c0c00d81160924180c05981901074101e40111403040c0d000303008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 614011420 1250 614010170 614010181
    0xb0106091a0a020c0418080d060603050903070507050f012607110d0905151303031e031406131523010507020913110d0501050615030601200106050307080a0308 70
    0x480b0300c520400540564840c0310302071150f007030075000080301802e0b103054a03440d2130080c0c40303a0034558442403800b00c2d02c99440e50305120040d0148111508081c540740118100f8000d599a140c2e01c40c018014144582aa000f03010a03aa11501600701603009412041c210800c035201d18099000082c0c8541021841345405080380c0f200006030851014016503611400a20b003500b445041040007075400c0c0c00810405c00d40c04c125800c80c811000461107a40c0300100304403012083c6054506049402c0d0404d420041c24048500c2d042030065081881140d0811003c021045524001c0031804480182c02c0f100b500009808801071050010440c52440c0a52141c04d100d00110703407900c514507009500000c0310020030f00c8441d0f8010a600d1062140307641050700d0305000002030341619009800c5480781e44070402c011540c01d03c800b5585840c007603030000741d056040020001c2c00380c0c9180101134001e50f03070404200c0e0b00b405007500944004c2c000a41982c01031f941b43c0900c2501c33800081020340c0030a040c03001048 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 614012670 1250 614011420 614011469
    0x32406090c0a09061209080c10060b0403020a15020a0203120c01060f0e0403050a0516061a0d02090c0c07150906020615031b012d0e18040b04030504030b010609 70
    0x32074909056583c140183e007003a0040c0c0d00c03802d410a0781036110395211030080001341c1042c002d007d102c00301c1005100300d1110903540c105550b400c0d0805002101e041c070080006880350006a001c0e510010b428074226441000c080b880c08158a4000c0c1d030500c15120b0f402600d00e03603c002049000c4641000b488495140c141a18840307599100355400d1810072800140440d21600107006c2c010b069150103032620102c0ba40d15007402081a400340c80b804e40c1c40109400040c0054590000d074401a60707001c0c6980c03890780000740658130040500810728400a104003c405051042601402120a41e280f02c0303205814000c00d00c0e8414000e0501520805021508800000402a411040c000c0c014260100901070460340030106181e41d906010300c1d240103441144400001e01c1e00d110700b00c80c1488803202d814030010001c140c0920542d0181c204446001c60350303030400c507969600c2500400f040c800b548480c074046665200e035600203030011442034008075401e5032141100084079000d24855203c4130a514211 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 614013920 1250 614012670 614012677
    0x20903073020011202030a0f06080a030206010519030218040b01050316031b0b030a09030e060406080c070f0203060901050f0c0306030303040b0a060b0a0309020a0b0423032406090c 79
    0x80c02c2c0c402c0c003607440d5441c0e030010500034005840624080100074090b803040e9040e43c0044e5680c41c01291207003000c4400000910482004014480080a40100d20340b4082d4031001d041c06450b0140491900c00200780c8510070380c400046030b0142100213045d28032403111482403000e58003120203108690000405140000e00c0150404440da4500c0c03040e031030b40c3c0d2624240c404116544175090703109900012018003140c06184100c640baa400319080e074a924005100c1e15100c10100e10545051000340122903014008030b510291b1207154076030b0350000b410110103109039401c00a46c5442503c0800444070010f400c254001c0d845c0310500d013901d441e41c80001c601400100c1e6021303010381c014800507002c1b8070304e42e09454108168480000310652030b468040c50552000285c071010a0710f8100600860a100d90f400c1c00811651911074249800c00d00303401d050300807411000c0c0da5082069080c0320141c3c4c052250a07078001448900d10a651744d0411810342880d421242e00b8803030581480060990341110044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 614015170 1250 614013920 614013923
    0x307150b01140a0e0904051c031803050c030903071d0907061407060605060a0315051504180b0603160e01020c030616090e010605041703070510020306040209030730 72
    0x4850642903582c0c0d91800603041400c07039008200e10039404c4901c948848001d9405240520050b10003150103121811001c00700711041d108042c0340c0703458601d0060340d09250326404c952503d007050352000c40d09030040c518000c00c0d1032150301d4010448002405680b000700c0150500c0c030300703000303204a0b45d036100c0c05501c41803144a404c010403400012580c880104038018007440d442040b00041494071600821256040500c040d40440c0c2d884401c0d8506907080060300340203000c2102d204510740038100f88400395020300d108082006042c514040291b55258000401c038100c00b0380055120700d8442040000001c00c3c01c7d400c800700f4000ba286801552011132564280f4a000d0001c3c85035803148582d0303144407007001c0041c01c100460501c001c10103030031100301070340240342c41c0e5900da0b2150f00b050364400501014400900c8181d00c01c1018000103a400b08128074292601c0d0301c010703241d5440c0800b040107481407407100d65250082450204492006400e0a1001604100420003848002d4800401407954120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 614016420 1250 614015170 614015177
    0x2100213090b19092301140607140a0309091a1f020c190602010b03030406140f091915140d051302060a0c0b070f080a0506030712050307150b01 63
    0x144040d049940098000d40c0b006880380d0ba03040b104103c0e00340c0001150300070000341c81d200d900c551611002600076100d0b2510901049800c0d51410b889038103500385240001d40503960110ba6807040c4015105d00d1030b0071124a005a40a190141c90f00811400d018080e4030310443c5003652520305861010001c0c117507240041d054003040b14213043d500303030383d0030461000c4804c6200c0d86130010180d8442480d8030010103649881840400e00302a0301a00707660040d55814000e60050004005266102912850044200340350654038000b10071003100c0c03481942009071b002044100c0190b040400c140c609005c54000141c8010399418000d07003280c2490404202d584030043c1480100c20701c0c015680100d80000c0b04c00300542c22403c2690114480342c10441448000c68450040301e07040c400208000303039000c0014903254181044481c400742000f20081c240c00007150b503074000a03c55807020071a100141150309010000106903103040c55903540504000c071707883c1600c103589400c2804c6500a0040300d80b0140c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 614017670 1250 614016420 614016457
    0xe01021002040825081014090309010c1b0b0a0f02060f0108150603070306051006020613320714130b0a0b070f0b150103051e01120501090804060f021002 67
    0x12645080782c82400c4244295202c0000000346005080140c580c0901b811030f400303d05103041c6136005204c003c0040c11035107a40c10030805444141e070300514402e02a03600c001c0c002801081c6d50080f126080043d040441031010001e80c2e1070840c1d4000c8040d81903440641d00b150010f5541540c405511807003032065855540c0071158600c441c00b000d028890340101c014084918091b929101c01094500076103505061019114041c000f20750b041c09003580c4040341e04481c0c010340034142c0e00c1c1c000c43c0703c06414038003042d488080042c002e490714a03000c4c0c03401b0f40f0000031200c072582c9030640b1195010003107084501c03034000c07211003444080c09402a840700c500c3c02021545114034003186000c0c0c41c0c0c40908101c0d6101c5510305184002594030481c5801005142c0c0c05032140c841c03c40025003199000382c28591995441031004400c414252021415242c3c100e012404a00c1036252031805002030035001006a01c011402040103030340403c8900114020b6400c5400a20103108032000701d1240c03030f15072034443c08001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 614018920 1250 614017670 614017693
    0x80405011811030c2e02100504060b030f0106051e0315070509103207050a030e18100605160206030a05060a050a0b0d0b0d02040e010b010e0a18050717070e010210020408 74
    0x40545d10302d00b1180152115800b08114010480308201da003200c004da030f241c02a41c020700701000100f44142d1000002c00c2120b080900090040012070f40161a10301d542611860b9030b03c0902c0814044480c9003100c4070710b41080840602260000075685025800c10245400182c2c820a0070000c203103145503100c1581000f100c18401c200b6030107450b011024900b004a000000c200300004503416010790b8032082081181d4003007200a0305000b24848140304480144803d03100d0164040e0212200744c1000c40d950340400000103017000c58520081d50200d804002c10002c02203680001d0300c1143c0031942401801d403600200f201c01151030041141d820390034426880141c08a500075060380e0001030105021480c5a8001019256404001d114507510303070a20540b44e58001500440d0f00008844045041e810800078024015240c19403000f26521400841c035803038020407034845181e921400340103040c50504005800382c82c41000c114010b200c5d580800112404520a03601603c946801801108082 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 614020170 1250 614018920 614018989
    0x80a0c0c0f031106071d0405070c050d0c03020106060c081803160f0e060d1227090e060105040b2b050304060c03021203071d12010f0c02011a030706080405011811030c 73
    0x1003002c41070ac0004220100800c1c0d040000b02c203000203d40d580f4000c0b000c0d6150090940b0070652012003441803482d0b040e00025411820749506500070085011110008030002c1e1404007580f40c1414156030729107010031248590f0005409032115884074119685588007132040c184040c80000d80400740c04843c05031000e1040b56400c10400000c0e00c0c2d8a90385904c1c01100752050580d0380301c0c008042d543c4401c070955500502502c1c3c01890b04803410481166a040498217001d142c00c0520036005001d01800c40d8120a082d01e0b52440d9009000c6a403141c4d160301004e064003810450030f90152140441c40401c5c1c8217110112882001145e840c48821182407401e8101c503942c5000980c0c2c0300c903c4a0510760320003c03d00c1402c80341e00c4600c101041c00720749014040d08660000c92081c012461a188d202251380f0002120340c00c640d11454080141d41d43c500b4840c2c010400b8505107441d0303501d200c080c00140100d941d2a6200c210007101a00c1c0c013035900304200400c60354003280600c080b619480d0185000302a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 614021420 1250 614020170 614020181
    0xf030607171005181e0610050c070801060b03011e0308040302040207061d06010f170d0f230a030501140a03020603060a0e1006110d080a0c0c0f031106071d04 69
    0x10810b0400481644a01c0083c0c1680070061a11058401000821100c01498441480e10f2441c20040c0d201c913040001c0885e9049040c01d14030001e000307001401010074141007180200620f4841c0003003190030b40311044170300303c0d51080c8502c648010101c6030120000c640b0412081c1222761180a0350300d4203185600f840040c0d000848195406692013420585000b01450100e41160441014100e5581481203440049001e030f008107000c140e100c070500c8000b00380001c1013480c8201c50305004215040c1070b142222203900703920150b81580c0410340b071443c001d0941000b0b40408a039585040c040b81c0c0c0c0b03400c10490040341c00058594003001540b010400f40c18010015500040050240200241c88208800c0044002d407200a020341c01e078681045030560100d0410110070251000e8602c0e06c1000c04010685100908050401c03550b5030302d8902060700824040c0c2e44a90300506226401c00d09040203800c205602c51609940e00404001410f06031003499602d103984075a040022040752090b00b800001d00d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 614022670 1250 614021420 614021431
    0x3180b091b090c34120201050c0a051e210610110d0f030209060a05030901050f040b0403121e0e010608010e0a0b150a1e08010903080c0a0e120c0f03060717 68
    0x83c0700c0298021407070100044c1c002c149000750702c400403032441d201000307003104c2c00100010801602401498034032548002114440f0b81406160840a041568120454801e165800200e20880c0001c1c03009400803003000d921030703081168081c1103401c0d9500700784c1b4907141c40c000d041c541f6000a221445102d0051030a9007070030b911458014180001d04000ca00141d0100030301d200841da000c410000e139140b0900070542d000e070b42250b42c00e599081c03958508241c008090002400e020107c5114038540a9a1303000d040c10910790104000079980f17a009240040c281c100d031180030ba509080f00400d1804050040d10301c0c01130048d0050405038542e844481c007070303080948a61301903522140d0361440d070740d2102e000c407025210070401d8000401c0c1c111803030803502c8940e1b8004900790741001940c80109411110300c1d40d201e180c0e045940e40d15041000100c882640726500c13a03520204840307070180c1c0f40c06c002604040091003552180c040c101101d003010364030241254100e001845090443c0b5081360902d10340354024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 614023920 1250 614022670 614022727
    0x6010f061e090f14040b04090809060d0e1006080c0405090316080d020406050301061106130b0702010b0a03050c03010e0c15250335040303180b091b090c 67
    0x292580c03c10300507001180c1c003000742d00404d490803038402d10307040c0b042c1083d800c000c507004c108805440e9515407043c02103104e401d00c03580010035030010043d03c54000074101ca58040954055904405080300106014040c00c844c511540c500c5130170300d003043d10550b070181144800075428140360281d071034480750354a8012100044240102d07841c401490000d0b01c05080c2948609440e90704080001300141910f441240650748050140b0880c0042c0c90381c1c140200350040d2465042d03135141c2c0416805481105159074010300e41c5000001488404140b80c00007550440c020b0095070482c4012a680c0d42020b01c1280d4014080030601d445502c0c00d10041c66041404c50841003007804d03a01001d840e1101000c419008a05c4401c1203041c643e80175060010070004500300c2545440540141aa010a00030801814141c0e00c0ba608070890325075141001a1642c011a010030914080e0520307919800d94050f00000107017582c100042e2858128034082c450140d554035917040504801084c01100b0000b580b48424 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 614025170 1250 614023920 614023937
    0x20d060c0e1f0f020304031101050a1403090705040b06041413061a09012606220606021b1203070b070e10200313030206090f041d06010f061e 62
    0x240e110004104282c0c2003103946409100c2040c003018015886034000079085420400003440011a41d9402d450703508000c0c600203884408201041d1440c258610840c0c030311820100070480c1c2c100e0009801e03800e840c001c0d034051240352034032350a010042c0200d005a110f0a0313504194440f45080082c06404012540e41c000700307203170b0f690703805689107891464134150100e030b000511181c80b9600315010725065065000d8004031a100c1079280b02c54528050181071007010b001760340400829004945007510200301078204017107951480040e40d10802c42c03c400c600b5050b2480101c840c2d00c2c21090a4050582d48400741d89040c41035943c0000c480001030104040c0000c4101ca8000d03034507a0085880306095503101c54078040944265004040d028a00026175076004100300320f406084580c2c02003c1f2541901d0194546861000040100003a40c412941203072924000d48240392030350542091290724241510000d90300c4080100031b8800c036000e10408075440401c7ca0750080c00301d52644091042901e40b900070b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 614026420 1250 614025170 614025197
    0x1030902031501032003070b090603091c0c02040605040b0303071401090b180f010b060a0302131e1a03070206040818091810022701171e06010804020d060c 68
    0x9000b00207070010755110035414039105d00900007510090401004070010411907243c8446106144a84480c681c02500c02001203804100208201c2c039004040c0c551740b070141d030000da034014100b0314582401e81c1300c1c0341040710001d80e40c06c0921441d400e07000064091031070b10300980c681300d041c0f00c9101a8090300c4d40d85ca1102e0404218540c3d581c40c0580f141c3c0e403905102c007084070300035464204840700c03001c0c06901d00143d0b40e030350b65150b004480c03d004050801686600c0078110440000348154042c0040b441614400f941d0062101050020f40e900e482440b00c0400c5c80c5145440703540021901907000d0303800743d000b09003c1203800001d45154280c0f00313480056050101c0100300341c140103460380c10141c01341050440c1d031207405110850316880e071800114141005038803044e6500040d9260350000b0100d00d100103034180d00c50094005d0b00a00e582d1200c1160602c4401000c108c20401c0c9520b80c004000004600b10350301ca02c40d25805150000c00015600344030351174004c010130013000860103100a25900c0c14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 614027670 1250 614026420 614026453
    0x1308040b030103030306181401150908031b0d18060c02040603020d060905070909030e060a02030405030d0c0c060c15050603030904090515060904080a080a061a070309170c0103090203 80
    0x5003e10300c80d40c1d01151741443d08403000032403c00284c140804606010301c0a0710b0640d1200783e0707811520710000740508548116803d4807444142d4012030454000003030792880720b46d80280b9080040800300129040c0f03054100c800c66a000d480c041c2c019180444027010010305104210303100070f450000b0000070710140d8a80c0000e46044110008460f859110f403072040502c1030600c2094001c010485044c007003804581d80007803c20000c00d0310188201e40100f40b080b0080d1007041554041d020141c04c85141d80c50141c00038011403810b91084481021603500410017600c902d20300003205511401c9407120341e20301111034000e8000280590340600c418803585025036607a0160541e880d000c0d1026058840a40da4100088030b0001c03c4180150204002e0000050200b03040742c001054a00c0c01140340d4a030b54009402800c85030740285518440c000014802c0801c40005100c12440b948641007032655541701407800c824061654070f0250880c10321a01223500a41050724141e10060545011400c20300c1a80c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 614028776 1106 614027670 614027677
    0x60f0402030a0b03010903121a0603011517011217030702060c070f0c030b1501030b0a050d08040b0d0608060705090604170a0f0303020307120b03061308040b 69
    0x6040080903903c40f1080310300c001e00920400c201424010203980c0c1b21820b071200145000401643d030f110301e00c01761181210240c41281568a843c00985003400c8085151060150440204d0041000380d00628040c003031480d00070704804802d0a01490000301c213244d03015800f0041044c0880c0350f800080c2c0036030084466042613030340c0b007041c9050b0303c402e01d00d07072801803210203030300004401c115060b06d201e8490034101c00c1c0802c0003100640114280d403040c5500603000202c8200c01e10140c107180512001c4140110842032400303589144440c0e15512045900f40301c2c650320300c020b12940741c080c40506d4210f4024981941003151800000340d962185200c1c8444514864045c00b06d554000e0146080f9583c200700124a9907900d806c02030003035482100c3c03600016024101010525640748916011a40094018480ea0f982e0301407002044022142c10b840c0d40006000c002500221403006 = true := by decide +kernel

theorem cover : BRFrame.Cov 613848920 614028776 := by
  have h0 := BRFrame.cov_init 613848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 613848920 ≤ n) (h2 : n < 614028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
