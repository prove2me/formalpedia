-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3868
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:55:13.281358+00:00
-- url     : https://prove2.me/submissions/869ebc8a-a562-4ec1-ae17-ce609570a2c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 695503597 ≤ n < 695683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 695504847 1250 695503597 695503619
    0x131416050609180405070f0305070603061a070305131a0d1b020c060c011401060f112a0409060606110d0e03060711010f060b0c0c04021e07030c0f03030510 68
    0x4145590080181a540680a03e0300081c03181c0060089017903400064072002881c030314400c5a007042d01c00750f000f40c008020b15585845a94010300700252400e0038003182c04d61813803c80c80383c0315024042080105094940e03c4900c180c4000030b100a000312481d4a40d103041e98441c941210200341c1e6207078a009001c1c01c503020042061201004070740e02525900c5120010440c00f40c0040c2c10225456583d0382c03118001501c082e21684c06001d03203449a100c10100354070001d0040e41d64030440749075900082c010411101d10144004910b40400e40d505507410124004a00100310003000648404d04100000845681010f0720711400c1c80d50001340d5940070020901030b102c0c1c0d20300c0c0a6031754041e4031607030024140394071440740000441020702c000b1404c1d1550011070020340320141c201d00e105003000144410008000c001c08500c40b44140c07019414099810010b0004504086d441c1004550004002c010144101600c280c0550f000314050141410b5003401402440c0032070392498921240d03c4045090000b43c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 695506097 1250 695504847 695504857
    0x33060c050303072f07050901270b01020c040216110312030f04020a05210d1b020d020105160f050d03020309100c020123041b03020310051314160506 65
    0x840e00031442c60700d034100101d61111070f032550301100c90280c1d5800109a265107103a06600d40c80300005003c141d0416003001001041a0701201104081c801380d8800b40890280c1a8020200018005034407122400184e041c800d001480c1c40d0302600c00140400e40d5442c40e00082403140c05004040d501c02c100109140e0742704605411101011018000100300c210851803607680b26102405648540f6900c1c0082004028549400300700080c101d030500d510f2281c20085201213843c1440c00540a00005408506400803500c0180c0505500d040003000d40e401403044451008420358cc112803003070982000000c010b00901d044138a40030b580c044208040c468001d80b4095080040509402c0e07805950040c01001b80311882d200350354852140c03002111030b4518000e04501e4060002295140900e42101519003921002405e0b1003a01e00c28000b580b4005201c2c0100580054006401d448511162120340c40c0d200c0001c2594406050070060300c43c0202d10000c401040b941140005500c8404102c600d000b4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 695507347 1250 695506097 695506103
    0xa1b02030403080a140406020607030e071202060919080d11070302011713120e03190b1317070c03020906040501050f040b04110f21010501020706030e0133060c 70
    0x901c010300228580da002082e0750959400c200880310f54106461446411540c0058003580054041054041d0180503080b00d1400c3c89001e0140c146c01c100d9034209411050340081c2c028000440c003c0d01681f00c005400b03254600507030301c00310881d9072030407800e940c3c206c0d401e002c2001844140903034000c48000600c042c2903aa0507181c040d84000384810a460914000700110040043d4080300d5000c0f0710102c03405491a200c940d6101ea4207000c030f8050602c0e02100e00d0500000c290710f00c00c0b900108200c0c3e0a01da030046071000f4003060000b0b00d814550494828500d060f03d0b21034000414400b0407140a540c00704991080c0c3e10403e40340d50329410001140c10034891940c100d0313440c0c58221640d2829511410707220600074800500c85111245016a40d00a88001e08104200003181ca4a02d000b14100d20000b030f005620070700b0305604090000b034481e05a4442c110a054884d0888699064207401014000100110b8001203003440d144e0001d440c2c642d40c10141000d580f012010032400d104000c04110150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 695508597 1250 695507347 695507353
    0xb03010f0504020a0201090605090c1c0b0c070c080f07062c10110a060501080c0306071428030606030608010e2116050321071d0f06040306050a1b02 65
    0x4034080502000c0c1d402039460201715580d800e40140004c04620841d4040c41c0d000d8003c0c6000c00424040c0040307440090303030001d40000400700d90000150540725403603100c0b06829406823117183c01d10b0080e03c40b90060704500613a004803001c400f11464001509021a07805949404078410b02c081742c5940c4a0350791284000d44440411415554142070010f100c0c207001e41e203040080e41d01002d010600f000b42d40d070402c840d03540c2c1342c0c0c0042225070010000002840000c030098000b508243c4400340007076806000c1442030120106038520203807180d40342c00d14507149040c0150303406914070000034000c2a007800b44002013881c200d000318280205100344141d410040004084964581c0320800003a1f041d45001c1c0b051303003030802103219044101c4d0500d213034030340c400d2000b1525240d9502c810004102d01001c818942001d81003088000340c0e0200c824240b8851511410940d001c0c600003040100110708040f6400c6240000c0000401825a010610840750ba410030031081c00d400117010301c00440c09001d0801030f4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 695509847 1250 695508597 695508599
    0x30904140114240d050901060f060507030305100506030702010c0906021902060c34150914030a0803090c0909030906070b090309040c0306150809030d020d0b0a0e040c0b03010f 77
    0xc1803100f211002c41014a6055414100041101c03800e603014090104030251120f090100c1c5150900612024159611080c1c20040c20504014003d018a400240800d921a000b207038414591140c058081c02d0060035540c1e41c0d1510000c041d010f00050006000001c00fa07810000d42d851021a000001c20044101d050b0300d100b4035020000180c0207080a10494003c204c540801c514000d404650340201146800000103001140b945400d40b060703204111001100c50506071003176121003014241c0d4035141c10101d0a48588020a280c03030700c003500091103403000100b0b1102c18980001d00108140e012610a0f071255a110011354890041e0504a500b200c1c1c20f104000c00210268000707903120f4003020450703041c480c01900150540762018480c901207036660b9003d104500221020200c004214102500c5605044031907668038481d4181340e01310254042401066561140c00c004001c4c00e0040c81c480c0050f480d45c3c4005215002130300d003104d000124000c0000d00a04140c2564100c80c046e0300d4014081d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 695511097 1250 695509847 695509849
    0x6260601090501050c0f011410090e03030c072906120307170703140301030305030f060103020a090302090a02120a020a0e031204060309030c12021c030603050a0609030917030904140114 81
    0x35005403513017040314001e00c2c006040c0c19009201d81c50b0211158440f0000c02e062000322000035815035001458a942091443d0b60019000170842c1d8100e4840000c0303e0307075501c280c1800e915070510111200400d22100018000b24807000c40d9260048400f243c001452441a00c8466583d128001b0f0052941e800342c0080c043e1151714070003502c0894001d007071001c42c3d03030039000c8000800d0380300360400c60120f18048188101003501c00d080e0350f4000c9007801d04526015000034080c00d4146540b0009104101140000d5004c00da20380540b0307420a40801d02c4240c50428000500103900020008400184240d210814600c1d00003034440c41c024204000d0384ca02030030401c041b00a00b0740c0072001d806001c1c0b82110140014404036201102000c65800b4000d0180403080981d800344c4a203119004040c02c000c0c0a001141d404120b4002c0715600c0900000c000500f032030140c85070b1075598000c034401ca200c03007401c0e030309410044002c00c1038610840d0104841d070b8500b03001c0032005100780074001d0b6405d48001c201d0b072a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 695512347 1250 695511097 695511107
    0x4051503090106080601060c060b0f091801021c0b03010506061c05040201031b0302070c06110d032f07050c04051909060f150e160512071101050106260601090501 71
    0x1001c10011500b42e46503074050b8030301a4280d01c140b00207120304001c070301444010b200f100344003c1c1c00c0f47e040d003a4081704000662803403c0649020502008803a0000c1e07013100960403500020044030110740e50043d00742600e001015a071503258025400c00000600600d003000c2100d2181421441c61503416102035060390040070000e108905055450701008104601d200d10310a56507440e503000b41c0d4441c1c0a00e0400040042c5070702010034848010041044a40f010a0643c2080c00d0341c40c0000c1c502400d400f10042000c2c60100c000103c0580400110744800303024001c10186001c0c0003100c95012a003010b05c41199801c40d0107407100314041881c102207000a80010089a014403008039440f06140c00728011a480c0c0047d54090101c40002084811211f00200758420011140341d0300e5140000d401800c248200b88280d03000c2c0c00020005007001d80505000106138045d48004c02c0b1a603126400a011804520000b610410f0701c2c0c0140c01419030300340d401c1c0d0700c02c49069499a01e03171450000117640c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 695513597 1250 695512347 695512351
    0x11401051f02030904090f11010f0203220314061008060105010e01030e010902040e100b010e0a05040905070305030f1803030a142b060321090b0714031204060b0604051503 75
    0x7140010804e090301982c50340501075005000e250701120b0700c4010302c0c083d240000020716040c1408541d0b1048032640b50080155407103201400c40b00ca10090b03a4200c203507507224440e0001405154414010111004005000c601c40e02c2e01c180001000ca07183c0903015940d66003440b8076400202d400c5240c0110754841e0300036600600780c071000410080008c0e4000340c1a2422080403034140ea000f2038440d06140d10500596880c0c01d000e00b001440c1c0140301020a800c1d140c0f900540c0c0c082c503143c22a0381c0400504020004c0155000425280c07034a065504000c015484011111018204a8800340b03a520740441150a00400790312403002d0200c007c84e18100507005030b21019082e11310b80856684100c0091031341c400c5440d2070400007880c42d045152001d131001d184603d4100c495864034013551b4081e0803012401c180d4100c00c0807280c40d24020b1400e207103d1038506404001c14040498012060000d100d103041c0a584925030a000c841c440d20203102041c00785200709942704084100c2c140301d0081400c000c0d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 695514847 1250 695513597 695513659
    0x80f0606061c180c0609050604150c0f0305090a1a0706110c0d020705031002040b0a0e0f0d120f051c090606030c06020307060b091501081005030601060c0501140105 72
    0x2480c503032406500c0c900301c502c20780540d100c410459401c8010085600c04c1d00000c0c2082d4141455032904010204d140c1d4000ca0154603480058110ba00a849024a03140740a45600c0008880341411501d0020710507081a05428060011100007117002c4203517000c050015059200290f040c40020303155a4054848014a1230040a042001c00203080b02400300410032403158005202c150700c0d02c0d081c0340c038001107881c1900a951040c0014000081c0c884211410080340d4900303100000e07290000500f00407802070360143c0c040150088030007081084805c48020303403070b0782e02c0d00b891580b40030394140e540c0c0c42040310f07a0000804481528a07030b00000d5001030b9403140115000075001da00c1e1303501c04100c42e0803070f0442e2016070b1001c2012030402c00756002d42480010113944110080c00cac11000310501d1035a109203981803001c0c0c80c0018903412121903500e0010715008088078215651603002400d038a030411401c0d909942081505020305803424015030485802078040b400034110355800d420552000f003085 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 695516097 1250 695514847 695514877
    0x2031204020637090801050702070501180902040311210d0f0c050703060605090c04120807060e0a0809010f020316080703110d020718091101080c0403080c0604020901080f060606 78
    0x1102021980c56283c80600c00780c18821640d1101500b0240c0141c10550040c036aaa051900f04200d080d4082904011581e003030802c0050744280313803400e4040c03190740e810000809101040010a20504160900c0e00700700990740451003c0d154121055003035502040210355074010041d0040c040d200300358500100c40b65140c40c200001d095600e0f1801d040e082e074000d440107a155903040c07045140849036903030081980644145054a0500500c00851b0144409041890301040180030700c16290001a01407030010240c902a005518207034000390071000790640042d0424507882c10b030394000812140112082e400f450300c00821a51240d01e82d1b48030080c220108002c0c0d001c04160041d040146800d0600c0e59009815182d041c055408010100c01121040c3c007400c1003240740205500c10684d0b680e0000a1030325000c29030b100c40011005200742d600c0204129400a410f4014110200709180514803c40c2c842c10640da80300d18196031a502c040c1d440c071280c1c2222000c50a40d1030f054008284110b149000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 695517347 1250 695516097 695516137
    0x903140d1808070501060503071206020d06031407060e0f090109020c150f0106021501030803060108042405061503091b030721060f020c0714030109121806020312040206 74
    0x20a41c01c1c8140c5802200c51040c0464008204042806a8000340400307400800140d80340640b045009080e200001c0c201960009001c2c01602c0c40342c00c8207014580281000d07540034040135040390b60368211311030100010b1b00246404154a0140748444403428020300d03620031a401c0c414004000e602010240d072240c4170380d4030b0f4101211407100700144500d0302d00c603100c0080c1d80350100c007070b091940c04a0032070802d00c41200103000041505090b00d400410a28120700a95038514001007950b110b030411403c1c008442621541c800b20980241c0d203c0c840a0700c40750200c600c4d228801210340410b5580540c2508100d604111044c9156000381e80303940c0003002c6950f49965283e421801d401031a044c40d96095540b48654180b201e50300488400c85030700ca80852406441c007100e152520304d540118445030b28507140600440d0303002d40142c2082d0b0b0300701a102c410401c12910160076000902c100424074103481500144007030001c415164202140b002d4608a03a889500f00420307a0f00c030781c030824540f40b20006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 695518597 1250 695517347 695517371
    0xb130b03070905040c0806070c03050703030e07080f1b0a0f060f030b04021c05070c02150705120408030913020304020303030f040212010f050601090504050c090d151104180903140d 79
    0x24540c000d50007901217003980c0741445485404d0900c001c0c1000c00f0300556010780340020303a0100444903074940601d8000341a5910107200760504d0040d50003482c443c8200b03160418112004200001d1074081e44001120820300881440066680361080d0340b4500c4c08075404004040c003c2120337021400051900007600391803100082c04030b03040064501034060003990400074010640c41030f00d03004112800c0508000b80c550b1700140c00a46524070220529070040340c07410420008211007003084801405032601c1c2d07078403111000da49030031590340d80d480b40b14110204101d00080d842181e0041d03402601540c03455071207810301c40000707801810482e0000600114042400028420b940036040b40d5103012505041c4100010107109003a004144510b18010501a00407281c40488041300b00036a401d03103107040203050054000201d044400f03003650415508a13146500400140240d95200c1c641c03140400b000c5050b6411900102d400a02040c4481c02010718012910041c3c05036100c140e0020074079158240c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 695519847 1250 695518597 695518601
    0x50c0304031203050c090d120e0301051807050a1503091e0609030306050303090310090212160824070e060d140105090a09031202070f0c0803030403030f0b130b030709 73
    0x54429a0011110b2200c011610b41c180101d03600549070f40b02450600310301500094603410b2800d0000c01e901e0741108034a598a026a80b20403c82000030000c06c05441d0040003440e031410840f40c0290f01d405445004102d80c0b810005520170359540360b00c3c448441030840415801000748034801d41e030341d01040780c248c21301072404022024400e110310000300c1ca42900f0300c0c0c058251600750300410310a400034002e0207056100024a64103803c0c3e102008a030090250010131038400982002180c14041d281100b101000c5084091044401003070494140401205030291310142000c0c81d109080c00000110b00318a03c5030603030050082c00185102c0c41d00c0c0360b00c64030404481280740020520309a0800400880c50420348450380720305006c90603c2003140ca580c0080c28036100e40001621070f07a010940380148007559805504155010281d07a410035101c01400f9565081103c0c00c800082c1401c0310340711030728640d004030744101d00003400341140004000f18090250200b20820364141c425080005401c81080c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 695521097 1250 695519847 695519849
    0x604030c1b0b07061a0a080c04090f02061303170301051e01110636070302060d0b040524010c050705040c12052d0f0105122a01171009020307050c0304 66
    0x30ba900001e03211084000d20000d403001c172403070300c1c0700d034480d944208451000410321300c1010310106c400207401c1540d85010b2041d03040e00503011b1340000c00400c10403030704440481110f0607207004665224103000240804100c91009019050f0400000600081e082d12548600b42903000305040900420304601005494034901310341c40b850141810005050320481250000c041c001c1808118203100b0514414903500c60051000a014000001d011030b490340341039109a2000d200100240040d0508402201030402e1112000343c00c800c2820140700590f0081c12454261a40000500300e500d1624003013000a00b0580501000d00190080c0803050049030700c0b032117218003010180c000a084200b80c1062441401011640b031240c0c6c41010b00a50180c80c4290310b044400480754030520448403140b240c1444203a49c50380c0250665414070030400340c1e4541d03115041c038000380c2e194105d000004000490707100c030a4409c0c2000381083c0f1800d21203440507800840c0d001c000c50401d0303860305180450481c030315802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 695522347 1250 695521097 695521103
    0xd05030c0d0c021b010503010b030117030d0603050703062405100c0b0115110f120d09080a0801090f06051c03210e0d2a2d140604030c1b0b07 62
    0x400c201a003203401c001c00102e0104002846e02c20304641c10300c0c0d1100e81034031041c015150600ea00c1b02480305150010011500b2458480303c0a000e1107940e4900a50349031f8071070008031512030600b00b807a0306c0804507204504d611090140c984541601d42001d00110105407141402040900c00b0518007207030104d40610b0080c9020060043c40c0b1190f200c3c000c003420050680d2128030f810010481d00515400104140442e10f422002a0f4600c050144040140fa40a1000b0706524010601c03d0f0400e0304480070904132500d10100703205040c20b90f40140112240d81c01450f52000c002c0200d1a200420301c02da01007250320a040601c0380640020040c540d9183c2482c3d8241d00e80e03143c08408811050a11000310344581d80d0a0111825030242038482c419210100e040d00c007641e80b00110740c2441002c40c00c241403804030000403e03010851040140c03044005420030740b00000110124441c1c0400000c0d0326110300d4250780c0301c03130801b215a035403884240b400c41180544070805c400f02054030081d203001001e4080c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 695523597 1250 695522347 695522353
    0x2a03040b040e09010b03070303110102120a0504020a0b09060f130b2a0604080702040f0b04060902040303110304061e031b0c02042415050408030a02010c090e090d05030c0d0c02 77
    0x7260480b00081d81c600103042c0305240c2d04004130f0307007403a841c00505039003500d82c1800e041442c03011b01c214050080c01429000c41c10390600b0002e210302442243d00c6203010b64000d441c07120b06a40c4540c4007a000c8c0c4200e00700c003034004000300641d100746800f00024200c0e12461a0141b80b1050342c0308002c0015400140d21700d80c0003100216000041040c075042002581003000140105180030313110461240144000a8012621000c2254a40c006c0d42d200070301e42a0300400800a103911200c20a0081d0001d0004030007041c500c20b00319440b12000002d60f001ca03980c0b907030349424481410a00482c0c090404840d00140b5845038140b0b010f4101000c0542c10028003959800d08407070141c010031003507504043d84500420710120700303400180180c4e40e4150544024002c84009680c91050884845c4250b0740f1446040c0004101603980303503810340000c02550503559948410548892004046c148165415019a40b2080000c94154081d00c09960b02c8445a0220340c28044103200c14403d803096090200c005030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 695524847 1250 695523597 695523599
    0x30105070216080712151b080615040b0940052203032c1006230f1302210114010c11030c06070b060102212a03040b04 52
    0x182d441812100400c521002060154a010324204a1030704950004d4a080c910a801085550700354014521200c0c2000c40c580e01609800d1004100043c1615224401c60072200c0c04040c215130f807001d840940300010380603840c14030100100b000201100c0c81340a81110315903000088000d42982e001b4440584000502d2180b40d40c2003180115440200800400303c4210101d144013004840c4410043c1c1d0f1504000a2103500800d0b05a120b00a4156080d11a8400740d140d5004441c04a0034410301e4500d20320600446440d1403205102c2100b42c1203c49400d4901100c00007d4a08500b0000001c1c1001d0000951240c81e480d482c42070303034091089102101c4810321500d04035001200740c0e41c014a2038030241901d1014280000303210074a02c00010b0049104d0004500c410341e0140004403500d00020304060751041c180c0340c0b81030020402c543d554054015511000c03180420480007090400c01410050300e822607240c900880d50901980505810059413645d000d50041000144040c005041c0700079119 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 695526097 1250 695524847 695524873
    0x21204080304150302030f071409030a080c0f071a07061e15050f0d0b09011103040c0e070f05040b0d060314010207050601121a13021801082109100c020301050702 71
    0x840440c58003018810020042008201c51f8095000034262402e1032141c01c3c0d0010b07405140c040c41c1902c42d810301501580100300302c9400001c00311510045c090781c01d12a00b41e440c542d100d00707007440b0b00e08800050303081d0041c0f403424030001000030314400c1d100061a46501c500d400005001c20000114083d9506416580039810842020090108031200b0401000400c04611005481c01009244009000104505150a400c000c601010840030203840b80f80504100e201c62045203d002409010840403c54081c0b1400b100922207800d900c617185090324000b10302d0100d90080b0380050031240da50b0004400541454218407000404030005070310b845885c148141403000682c000d8001e050300d14494000034000855030800c6020004001509a4841d4583c450301080480000e5101d00e1240d00560b0300804002c11a040e1602030f400c48000ca4540045801000080d0881c03e40c1900c007401044400d181085085844042d02e01d0312100f000b840d07a000c40c3c04e48100b070b100000560428441d468207 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 695527347 1250 695526097 695526119
    0x162d060f0e120f09040c05040509070302090616051f0515030c0f0d0309240306140d120504051302090108060a0609050913051b0301150f15021204080304 67
    0x8182200d200420150100400860350303140006000e6416150204070a1500d103c202d0a03901e0030031020704240309040380f16130010556030080c051740f07125200c070401142095229100752000321501503c15403a02550404a0303100d502c500b00d04582500c20300000301c02d401c0c1c45030319040b0308a850150110b4a800c080c01e04545148031500401d000394842c05881c0781a940340003503490506030503180020b50383e090b0308049850010301c0e0810395207041d2007003100103a400c0e03041031415040a02da0341000b965444041c0d404c81c40b900c07801c04585c410103101400020491461020034000c803103013000351405aa80021802c1411516803070ba06e00d0f580410b10100c1d43d600010500e5103d04100c444800c0d5900700140940400518051280290440000500101d05007a100e03134000d500300c3e0483d482500c110007010342050541850038060350030301e841c40c01c034074801044000980d6111001111103d08010b08650b1840d61403240804600c14500807022604800006201901019000d143d64a040524410ba = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 695528597 1250 695527347 695527361
    0x609010f0e0a02130e03030903070b0112150b1201092001020a0c09020d020409110d062106180b0423031932130e060303162d06 56
    0x125241800344449608402042d0701e050303298111040c0b100220b0f007140ba038009007010309660856205c0003080c8295074a000000d014100c0c810400020710b42e803a01800300d0030410a12006020b64504c2d0203007500c040064004e00085080038107492600000405030900307545400405440e50201002c1c0d034080b4020340c1c1e1615144130001c0c001403070308804c81c1da2030503442d1500340b00b0f03180040d6000c900003c0b40e0202d5011500140001c050a001d022048520500700364000b50700c50a4480c03402e03800083c2c55089041c905003034200400c84000e840000c0c4c035140054040e8190000312407030010814400503a4502d50b05005034001e2120a800407130710710006035400c2c07607915001400e81c000d000b044050b40c1d55040c42031140c445841d000c41a04500496205003000c0940c0042012050b0004003202901e01c1003e481200108012541c110f50750711201101d01c070007a110035800d07404c20408245881546e641c44240544151508242c09241c80c580f805202c10007407100b00f507240c8040d0907400b4080766004d12a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 695529847 1250 695528597 695528621
    0x5031203042114280206010b0a030b0a090e0105160503040506070e0d02180910090c090510090905060106080627060607140307051e030406051812060901 67
    0x52440c00c1507220000414000700e440c0902d0240700503a000101e1203440148050200d1a26071511050a0244c1c03851841d03003e2002d0400410079150040c90510000788203041315440c55100c1d1034005540401c03005812107100b1107403c014034a0002921507030318820b5820b2100340d43c00000e502c0c18660300e000002c0900300d0048003001418020310021940200300544c004185040615100c8929804161811900800650b01c88481c0c43c191500804151505100d49490300c19214940b261f2440c4604540c0e1003035014102d40c906500601c410703889a409240c009800c50303d8020b00f0307a42c070021a401d0ba60481011111608142d004100fa560440d0b041c40d0071050441c0c04c140c4507060721500b4240c0000344803903410340045c04800302e06280c4804003110042500442030707841e00008000600d5a0754400c510484182c0b0600c240c000c110b8482c106102541c2d90711501a5250528180003103c06820005a500000700245140081903580590503c4080141000fa0040d0318010040c1c2d402c403810381d1129 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 695531097 1250 695529847 695529883
    0x3020c031c0501081b0f0406080f010b0f03030c071802040812070201080c0415140c0a0b100e040803071805100e040b0901080c010c080922051501121805070605040503 73
    0x2034464a40e58141d111417a00195050500d031100880050301030081b41e0f025800c14080c48980502040c0190003402550b1015610210059644000c0c0341c1c0d80d103e0b0040380183c58104d44402e00050034150446911480707460320144c1400c1c3c44221050400c080b003851000c1c00c0c040000d40c4c004550304130030100c0d03010740c60301d000d42c2c205841c1460a403402101c1d84ad4074402c10541c007072400042a14082030700c0341d546c1d0b02422600708030750500d001c940c540400c0d592107104024a13200060a61008200e0710301c40ca520894203401e6842e4801e0558061801d9a01107511031385104000c20130f80c9a100c418030308102c2d56540c448442e02d56005010494001c3e06509005600c248010f0042c040006a00e140604003880d0001e00b5283c68103243c40b07103020346139002c1e078850462200311042488600e801816000c003564204100c1d22201888502030505400c1940819900c1075204115102503000e0100300c5110f1a10514105180d40c030b20382845001d0300404042100443c00303021b107060411140d04454290194 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 695532347 1250 695531097 695531113
    0x510210b150a0210060b0405030f0f0a0219030f03170a0b011b02010311040e160201060302030d05031f06080711120717040801060305010c0809161503020c031c050108 73
    0x1050511107022039404060000096001d0440c3c400c220800803c0c3c840f802c2004903a40f1750300407691a03401351040301c1c4a4464121600c0140d90040f64030058295a400200f03090b075516400d004c14403404c404098894090381c0710010210308006c641070781e468032a64a403500e41d000c45540c02d101c1e58011b802180014030b024080c1c01180d0308107010701c6010701203160b81c0315910340600c0120702600c0160154003440341c010900144410284881501450100036500c03005101d11074100d08075000792001940c943d001e0b41441030110301070402540c1100c3c810000300c4640050814200555440d81d10080000d4824010052629030021800d074030342c82c095028104290103000307620214059110080d140d245000c0b44a4031943c8810b0854008060307020080c0511036580c2800c600030f0484001d0301010030000400151000c01c04240e401401c0102c0358903140c240d00748540208000f282c0c5e111282410ba0801041d21710200030005880f42e1040402c031003031015000c000b010700b81d0744107910180d1241c1c401c0c10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 695533597 1250 695532347 695532349
    0x109120302060411040908070515010518010e06011b05060610030e0304230d0b061503090d0c060209040e0f21030115140d0b0a05150a11070510210b 65
    0x540c0030b800c10782000c4502c02d107221300c0d000100284000c100091401c0d0000a500c41048004240329a1954030081e584800e40c1c5c3c0c0d2000c0c400c80e20648042000d180348442d00622241c0b04510716103401c05410314002d1008202041c0c0c10070702084180042e503599200608201580c0707092421462840c295250501032180c495100700d070b6a000754042c0c0c42100c040c91078180340b11140c0c0c00301001405802001d42c058920103003003d286028082d556907000b504100701c1400500d40001c01c60380101000380c0140b56010138a84222101689180c040383d54980070803081c07843d540c5500810b440461440e020f081c10821061a0038500340104407585800803c650341c03001c984000704140d03030440342900700f44110180307040400c6540c1040c0807131424074010003180303546c441c0c1d0310741d4000c21002000761001c01d0b209448070f0803c171b0101003e1f00d81209000e005c00072070b150301e40305043da0b09811024400b1100401d490324001142c031a202e41c0b4050021b0302e4000a4044600504a021502c0454513010000041594 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 695534847 1250 695533597 695533603
    0x90b0f010f201606180609030b040209060d080f1215030c13240501020d110303070c080906031302090f07020a1217071d01051c05071205070309020109120302 69
    0x144002880e8841125441500c02c2444541101240103010380041c0d502e9a0300a800c10782c0c0c06038114031904c1014004103a5030300a0300201c080da03030450300d031a6950b601c940c200160007400074a410341048201580c00c0001b000c140c050610044a41e520684820704203110100007480117001e4480d5001007855451039440c04144181c8119040c1c4030450414002e02c0742d24054118031071581c4200050206000907055907041110503079000b642a1035107084810012550341c0104e4a03000680d800070004030f40000c1c091380070142c007144540c1c00582001010400103c86800455012141050640c09601145000f9002d00e900034249500154141024140290b40e4094050000d1414021b1519500f43da4000d202401070b41d000000c4c0d035407a41c075214a004001501c0c51000c901d0708a1080c00e400135035802241540d94980600000c00060300203240000d0280070064204418812424083c0d0f0f10b00d0840d01a462060b021a00e0204540e021440014200803055021586140461500c140066404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 695536097 1250 695534847 695534867
    0x2071227120b0601180603050f010914010501050a0207090203040602030a060816030308040c0909030e010201051b070818031911010c050c010c1e0b010e011703070b0c0f0301090b0f010f 81
    0x41202d5400c980e55000042e20001d035800000304284405134070000c3c52580c150885840f8011010740c081c426684d41c4111415600410048000c58030500c0050103554071030805403030520b0541c4100c070012555441440c00300d034000d42e02502c845400004008010360f19000d018002c00d1400e008250040c0702c18040ca0400c02e01c0e0000a04002e68540480c1c14451000c174001e01400d0b6034001040000c0c0c481c0b901030901d145243c4194055420200025240703810444400c10300d80f9444003461030b0081c581c1c0c0e000351369440003211403a0131440410707480c12510100100b00c10306a8030000506c1800b020304000894003113401c03c090410030b84c5c400c18000184003103400096130f1400c0c03c00b94003940c0285007040d14001c0c096600d01e948018403005800303001040744524125040d458245810b640c84820010803001c1c03102c0c0038092a4400c2100a00141040e0300d042e5010001e080001d0070902034030f00625140d0300030381c8030100c410303151044070302c4e145010202c441c00200b0901300300c074881c503800402600740d40c11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 695537347 1250 695536097 695536103
    0x601141804020409020301080f010b061303032616030b0f0a0504020903070b0c030a0e100203070b041a160210050708011e05090a05041b0315050a0207122712 69
    0x250260300411600c494060318040c00610070195125a108c5e0100b580d503101c50417000f812036003131000c2c1c5603c2e400d1000440f54501604801c0601c480e080d92000d50f090948030214800060019105c0e081e00d41188a2046c0540b0500c18100e00849a80708010256401204003074814041202a2007543d90341d95a0301d81200c0040d0307000350303d44100700e0010342404030035803001c207060100044502c501c000200052810940c0f98039288180d4604200f80244060400c00560240c0e00c100100804514030035003003a4854803038032180c8600d00a00005500101090f41c03109001c1d44060000c81e911034040c04000561034802000708030b14900718600800092061147c00d0105105250b9054418080e0b2240b1000d0b04d40901241d00900f003000c6c1711001000d044030141e5511007100240302a0a0386859204216900b020550a03480e040849810041c10040c020010b900d90800c14080098119800b13446080d2658480080d021400c545410500d40d10644011014824010510103490b0321714190300c3c140d030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 695538597 1250 695537347 695537377
    0x5161d04080c070e06011112031b0415050d06080606090a0b0105070605100306110c0a03050313120906092907030507080c06062416020303091005090405060114 70
    0x940341030a080074071928410b0740c55402a2100880c0d0b1348420740c100303402110300780e842e441c0711652a075035107071160307462240744100703030020400b048580d14020030081c410325560312000e2030725503140c0711145030341500100d1001084001c181489801051310904000302a158050300007460002e0000d80c5405000340400e03000303a907401c101c05203648100d0588400e20340c08581003250f41030a41034100c00d20802d100454040c1d0038481015119041c6406588034009400d005014101e0995000c0d2001d41000700100000254001c650000c42c1980f82c1301004404580c40b0700030b400b81414402003500c104c0e900319030b43c612080094030921124a00d0294154003160032082d468030407501e400c0340d82e0b00c29130002030000800401c158001100210703200340500000c9403040141d542c070440204802c0c651080000c0100b030705005420083c0c0040c120262000e1008095030700c1c0000d00c500044216800134495000210007094110301c5003454420030740c0291b0242403202c072001d10380c0d02c8506140304600781c00340d00c2c070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 695539847 1250 695538597 695538601
    0x20102150a0f020a210618050c0904090b06031605060f070501060b030702240c121005060c280b010b160507030803192a020f150405161d 60
    0x99a07000354900d000202c0c00303540c2d1300290360000700040300304034404100138901d0205010054040c801c0c101115244a4040c1c0a80b00c2e0303050b0440141401400c0154110302000018001d58840c4100000c481c404c49108010b4144013040c1031800b0303511359080500ca40d00708418800d40d40c841c02900c1250401ea50707007a03a11500c030b28200e8054803041d44081a041030200034801d4442d00890916100c00d03001030318042500c5402d01c8600f12030815129400e01c41c508016112100c8416103415a11000082c42030039180e5450740410301c40e500508034118a6003010140d014807810303441c48884500780c442880c000054130b589850312000c0c03042c4210184d000000450901e2031105462004c24a5082416140416a00d042400c0c0b103910844500c0d81c81c400b08042c80f00998500d100f5081144002007a50b141e046140c0c041c03101030810520b20f1401e510900760a03140000f4200308555861031a66070400950800703103803452601c52030039069207061a101005014800706070303040040c0500c12101c0d0101da5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 695541097 1250 695539847 695539861
    0x303190c05010c08040b0702034e01080d0903050c120f0a05030d141302040c0e120c03150903030402010f1106042301110d0b0402040b070606140d02010215 68
    0x80c0c24600004050394240040312000d0398001840b01e2182e805864641410350319aa0100d80341d210700509091080d80080011415200b1001c0c00001c50800c0c80040c829208111804500605019080890302400d038005003e94403060140340c004107902d04003608154199581c440d214103800d9605070145c900c018000300f14003004c0080388810400c807019202d107922207007480f94a99000c0041c240b00c003400d20b400b000e080c40301a18406d01c2450407142c82c5448440c03503400c0001400d4403001d80c2080007a8554249510750703a8000b5048920f0f41c8400030441011100185410310034042d10004c4400c6509013040245440401140e03405542407030103280c4150707501416540c100301880000040d10520041008000c3c00c0101e0703425a0940c4008554072106400b04503090f0b4402c00a50003091409021503880c441c00ca420410911200070409402d0035228951010780790401d48040e200e0980b101c000304182c2c0000c0382e45845010084e86c08066505090b00080d40c3c80c0400c50181350a00c6688001440e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 695542347 1250 695541097 695541107
    0x17040302010248010f08060132040b07110a0b040b070f210305010b03010f0e0a1b0c03170112020907020c0406060201090201020609030c1f090f06050103140a02030319 73
    0x244980c0500740e03c11524003516a50110390500369464040b4844009400165004100452061105070b48021000b054100502c80592505080424010f400c242011000100f90301802c0a8042480340310f1305d610442c10040340500001740083d0103101d00741c07014003144a04070121030030b0303980740d41c1450380da054075203130001030034681c02c002802005c03080c02041c0c441020840c400c007892070266410701140e41c0301c3d510340b109440203100e200c41e031414100d401c0100c5c2a407000c060b58800d181c034200141c18030840500b042940000c20303071440014440c5444004160300001b041122807102400341210b503040101d02c0181110320000648202d408200185500b41700304078050400402400c1448a5076545902038042d0114140403805406842c0002d08840700001c02d4a89034072040c2d004202c0440c1c210429a0b0300f210b01c0c0810400300d5200d2010001103801195030080152062030001290362441c28140201d00011b05004010b0b004042540b0140c0c0e0000103655101c0141c0020401d03281c00e010080d16 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 695543597 1250 695542347 695542423
    0x815060417070902040306291e1503071107090905100f09020a09060510050c0601050904050f01060324090b070e010909050408031503030301032409060513170403020102 74
    0x30f101400064003104104d2640c1098010a103d8844002034000101e900c0c1800c0d40f00c810441d40100d4003510010030202c00c02c0550109490103000c400c158220190a41540d92044400f174000c2101c6c80c00c08101ea0400f008444010a005241000000281c4d0f44540d1210091392140708613903243c10710000d0843e840d6103d4003526500420309100c180e51782100401820305031151b030340701c2c05001000368403450080342201c070600104000f40250b40c2c24002001069030340988265411b11620b0201c100b000024841c0a0180d40141c1612210361820300c2e1040c0408401a1040300007406c0c4441000050b003803056081e004a03803410400d0046010200482c0c00024079803200061a04244c00e100600180c10001c1d800307030340c0128031183c0310308400c0c060507030b00e1000b0b1100601c40c060b810315001d10040340e4130300d462000c4601c0074080b40d00e10041e00c1d00e070b098072811b45500d015136a404446004000131740c00000d410b50110000355040c6455500042c1d203980011146088800b07010054400f06049505040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 695544847 1250 695543597 695543609
    0x1230303030a0c0801050105070b04020909070312050702040b1005070605071b1103011a0904171306110f060135070e010e010f210201090f0b0901081506041707 70
    0x280e2030b0315001c0c1502000c2c0c0700000d40e407004110900004a12544200102c0c0c80071074004102038080e0704c031a0f007403121841c0005c0c4008850300030141c02000040c0c1c2d03000c5030000070346542d40790b0b43c0300d400a00401c000c50b1884803e9a10600d0214041c802c05600f10b000d07100c01e150094000280303955140015108144484401110042d400c58146e08021160f101800f009400358020840b580032502c000e003450914422140e40034030303400d00060010b4040c0307002a0300801c0380c2e16418100381c283c0d0b492007070f114603030340101c40890406420400c1c40d142c104a42800101404001c0803294900389445100d440c0d20420080440c080a0b20119815066021030b04117454501c1140c1c0c0f00356503403010740c89101c002c0c040d15413081d00c000c00000d40c07840c0c00c2c441c03403050792010070603002e0b9041c50344110600c44417000801ca042c480b0000d40050b4490045010100070800c0400003a81c5004207030005000741002461401002c042c039080003815101c107800d032410354a01302e4085000c0342c00701c0061858405564005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 695546097 1250 695544847 695544853
    0xf060b10050a0e04060503031e07020627010309020609041104030213050106110c010509010f170708090c030601120b04050a06020a0507020f0102030c0d0e0d1e0201020f070608012303 80
    0x140300c0340d1010003055020b0640d591410030300030341030402040c4d850a00c00c0c5a0306901c00d01c52004640003600c21080e40908000c070a600d003405d180d0204150f60030189913450407010540400390742c3c82c00c40c80900c101c00c0c1c0c241703400c0114180f02d0f8000b80c3d283c058512124047e5a0300c2c0e1840c80007003c800c04403400f55030014101c40520301c0c3d01e01403201074882406030700300203603024004074066100000c1c21128000140c59450410b40103034011200301240c00c040b6000c00000c0f01944290500e02c03206e0a002d0115617840010501d04821030074074251002d5a8980281c0c4030000401c5011904180362040c2584421020059100c1782001442e00c0341c0c1c0741c1c0c0a07004a100060b2f41035515007100080400500c03c0c0c903180c0c5181c1d00c0708016a2607001d803190465454100011945605104012080310311200802802d1080c10300d403034203d08443d04110001c1c00c020109130351400d40d030301004405c001b5551f1308002c060f002c0c1041c100170041c3c4818407130001080e1988010151342c6441c140504a922005811 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 695547347 1250 695546097 695546119
    0xa05030a080322030207030b0a0609020a030b040c18091d031308060a06080616021608010f06090207170c190506070f03050603070506090d0203061e010b040509040f060b 74
    0x850380c07541e8829142600a81c4806104185990b2184401424950550050701c0003603d1512080710a000003400081e0300c030742e10031010421000620207131901400b156400192000002e00f404100d8001e00d484105108845648078241d140c4400c03541c05a0b4443d08010503028a504070150031000d00580d181d03400d0001151704036840034000d098a08840950003110903a44401ea07001c2d08403151130051000a40000c5c000400340c0c8885a020350001c80a441151a00044d5502c103000280803070300070a0741a51119414100180c3e02c0c041c1c00050071070707060300718944580390b80c410b12020b820603400314070700398045000300100300107202d03050580d50110f8410704050254078010703840e8001150030780c000c21400703006542018440c0c410326208800290042ca00b0713905160420815411030303c43c903541b204080070302c17600584052000701d0003848003031508245c1d0340e40001c8101d40004160440a443d0b80d00307200c02c00c1181d591403c22508160050646031848005007002d50141c46c402c03880a80090100314 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 695548597 1250 695547347 695547353
    0x9030c1c1703070804061d060711010506060c070302010f0c0501050708070f020615120102040f08070f12030804080f0d1e0b0d0804090e030c0a0305090906040207200a05030a 76
    0x200c514040c4520039034008039003031200c1c4000c1e07800140da044000844440000d00003c400358480002c554494550307a8107911000340980c5024012a44400022109640e446c500d250900500d40c114070b044aa1604001e1120b100586d2001c4512010707041000039921901054020492000c0d13098111000340302c61316140002a01415003580e52800041d410b07502c22904030b01c04030742207000361100c0c5200155100c02c5400c01c030048014460a080a5508000004641e40f41c502e100c0c0c014544100a048428903003800d1600000550740208840f125141c500800658000000c1d0f6201d603000741a01c0c2c03035030340040040465000e60440c894005140c201c2120f07112185042980114045200a2000100b01f8083c00b0100c02801402403117484240304c1400344265941101416130311400840c1d080c40c844a06052400340c00702c0e03041d40801c0b00000d800c4154140f003400a82c0c8000192800c1d0b2a180f01030341e0790840e490b9a550940c0c5086802c165002d130f0360703481140b41801490000d04440d808800f5003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 695549847 1250 695548597 695548639
    0xa0c150209010f0e030a20040614030c010f0813060230011502060c0706150b040e1005010e1002160617070906020303071805150c010e06010f060509030c 67
    0x81c0901d011822540b4030903180c034400e0404001009002c1c1c0548940c0784199600602d800c0603130b091a50612403034041c0c1600380c88034407072100180003d20008000c034400805060400c81041c03101c1d410000007603a0910000d0b00600a10b80141d10801409040c803071505085000f802002d105401343c0214020b40300100d090300380d00e07008501100240c824540d82e0344044900c107421343d0f00319070096004400050a0700300c0160203070001c580198000706070041140a00c01c0030010b42c0d00a00740c2c040010506100007918408400d6102d54400b1071035643c2030030070b40040c000c5038078400c090784616103034203a03440301500c00d011032400c030f200300c10741c0031801c90311898007a1803290310800000c00d2183d000c00241506200d5010901221a550060340ca180c0f180c8030103c4503003124045110445d100103c00003410746521b4900e11005080945190700c401c500c140c4603013914400343d101e005580c400c10040c00001260100802181c01a080031655140908007003410020101007141e44000e54401422041c4086 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 695551097 1250 695549847 695549857
    0x1b0807060b1203180108040f0212030705010b04090c053a17040501051b01091a090d020607080a0905070b040b0702031908250501320c030c0a0c1502 65
    0x3100c00e85034004000d0b408035964090042d044502060ba801d03400c0482d40a10003c980140c0100e1a144040c483d940201d421a1070800010403c1d07800003502c0301c00d2000a10423003400c40c400312024004006140c5500400170b030380c0c0c01950b114240340d5001440815040e0024407810001948a01c0c0c1c0c824821040000254080307419035014500f03076a80984c0c06041d50480b415100161101400c102c0c0f2070910003403031040408203980301c1d0760751250603011170f0101e4001040314101c4080040c1520340004424103040c0e60b800c0040555000509000c0d005410481007540a0802a400980d284aa040c114500883c2c3c4d44118a01c100000300410b9100700c920080c4441d600035001c0341e00c02c1c907440c1a04143c088801c0310140400000b445010000385081c4e90303610300003001a00b1007207134000701c0d1180d6003120034603540202041240507000c011f452022090b0401e5118031807d0300030516103030000e5003071480002c103003000b5801c0004900926178080c2c81012001c1d50024403101d940081203d20130000d6000e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 695552347 1250 695551097 695551099
    0x312060103240513050c0f03040f08031611010507020714010504170c030d05030f0402041503050613060c020a03050f031f0906030506100533070503040f0b0f0403031b0807060b 77
    0x22a8000c13203007582e8001e441c029402506901c0c40d0054642c504420b541020300122618a025214600402d09100145000d00c0ca0b0310041400c0d4000c4e0000640707002141394004882d1790528040003043d07070700441c0b203c0c121044003101d5080790f181000121064030a0b6088207046401a500d0034040010004869010990071b07011034248041c0e01600b81c6031408101c0e4680031940b07004000070014181500b111741c00001081034190195100da440f5070030284100c03080c1d424006e0f0301c6201828089140500701c0401100d00180c180f00003e034800401a00c03481c550401e0030075001000c1800103059080e500460407150103188211350701c0d1080700021307040c1440140e4052050801240b04120341d5031100049410003040c1d68400b0202d00c20310680b020080b4001d0351883c807030003211500080040002c101507845480510343e51400e001d40310488091541140301c0040d024400e40c1c40144200041b501901c1d014140242c0402680300014032400051000400c0e010000c0394031030400c50305030070070014008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 695553597 1250 695552347 695552359
    0x90503030a081801291504081006062c0f030f030316090f0e0703060801020406022401030b0f1306090c03110108061f0903211205060303120601032405 66
    0x1038100710f05400d882800c1c207882100c043c501d00941041441d554110f03000e0002504c0380300501400c0211402c1504503030301c0140d142c1c2062490b003110300c8442c0b082c0009048507040000407403504101140c07220304074008090208901d0101c0c10b4061361410028034400700c0040c1119443d00e007c0364074544a40040d1004141640031400c0380121900880d20788064414440030300030040e1401e0f00e1210761420240888080c035942e0800803581980a000034800f904481e002411030042100444039400202d40c0081e00c01005e01006000043d01d0010751500b00814259500160312a0400c0e031801400d8100001c01592800d01120700300500076014a0450b40140c0940c4900c1c0c825100640c0c1e05003080b10380c0d070b0b400f000c00f281650210f031040c9004a15600580b42030344441340caaa640340c440420803e192403840301314400072480b0f90f03409541c03085d812035004410b20080c1030005c01300b81e0381c2c001d040c426140301003098000b880c140d100b64003203c1032000a0501c0200d070307004901d800308184028040c00d40514 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 695554847 1250 695553597 695553631
    0x9080715090b01090c1d1201090305031e010b03180709090309140f0d15110c0102070c050a06050d050a09200a1202010e04110c031810030b060306010f090503030a08 72
    0x111145c802c001400c00b0035241c20303958860b009500d0b0000141180c60365801030000c00d0300346c030b141030911544001178401d0f15860ba603403c04081c0700354a02c5030342100c0c0c2d203090398081c0140a546e5402c4143c0340c1100c045081c0104450a11400394200401034101c1e43e441490846628207056006074610111a00400e800010346013500c1880f5405006811403900031340c0c0c3c1c00040000070091051b80c12210307918000040c0c4001c64202c465101e9002d240402c00c1c90b9004203109060040351344c2580018181100c805034803514061003c1e001d802151a04130320300e0382e5a80060010092038000c480043d034080420400048001c2d444100000400044d40c090030130150081804140c0d103611900da00d80584607500f00e030301a00d0400000d8009075414603010401400a100807040420291100a0607004400960640b24040c020035507514480d0100305401d11401c181651100000c50703070400d60070b03e40f0400340010408203032003070b000d10f9200d1030701340c800040c0518805602001c114050745085100c2a060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 695556097 1250 695554847 695554859
    0x303090d030c030b01020606191206022110030f170d140108160b07020f0613170a0b01230312090103060902070c0b030a1103010e011e0e010909080715090b01 69
    0x480f0411300e21405a8051004111907150008949000c1d802c1044015203054860003413161b120b0300c07980e003100c140390003040788503840d008624120150080c240c0241d1407440c06030400919440c0903c00600141030071070070300c002e03c228080c00b200d51104019041c0c4d42d556182c1b2036803009000024182c2c1500b0000b400100e0301c00408907403203000045642507680d000342081e031a41070550002c8001c0380e003d802c200603242281c0350b11004d4109011714000842c03080c0c0c640405038070103c2e030581c1c0d041802c0d00009582400100e01c0a2a141541e00003650841816003541d0030541c40c00e0340450f40c0341c2c1740c4500e000c04600c04803460b0003070040203404c2c1d9041c02515581d401c0e0509030b02400c0402001000324003014404400750401541c2d0240b651100410f440036010402c0080d5070080c1c1040c1200781d549030041c8030405031400315042284203014098001071030114a00c1444a06000b084107103500d035105035050048038015901d5a940005001c9121b880c041c0e20700b8001c004030b110451303c002280780000340f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 695557347 1250 695556097 695556101
    0xc080a050703140c0f04030507032f0117091501181104051302210f0a0b0105031017030c0115080705180402040b01110f1b0406030f14030c0303090d030c03 68
    0x1070b800310342008101502c40007413011a542224480604a200502002000c19030800a4000950080807154215010141080550310440b503c0d03c00c20b2071440706070541e50f43e1000341c0b280b601e0800b1100515907200c822950303042c55500c40c40d00b00130580c00c00020800c86103480400c003508440d00f0f03040241142c40030042041e8002e901c031b0541e010000381403142b62050903800900e6584a241941c0e8100018503125080b1070314152001005841c200e020000101d1891040010300042401c14a05500d03140d1212a03400050340540c040640e40c0640c80310b0594010015144c07111087d0303000303012484041c511054204524494418507128014000880381071450800903115200b18519515a556070203110140c20714550031410011446d40030100002d061106451500c140c2002d0564450b005080702071356500800024444d070324120007000020b03540a042d000269112804580040b09425018118020405500701502001003000702031000841c400415440030b0f2410496005404c0003181 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 695558597 1250 695557347 695557361
    0xb010306050307120f0311060405070e060906090a09050f100e0105010b040e1501121404030e0a080c1309020a0305060106020601240e031216030822020d0609060c080a050703 76
    0x400c060311001a004100c40700503a65043e80641400907038501c880b141c0230301e4002c00300c4040e6900e4018840501900c81119046078200d01700701d40740c403428100710b0001103410401a244540301a52210070ba42000010700000c0ba0303404031a0140d910000d10313458090046c101c0c5800e145543c1d40381600115880006030700740c03015914418000e011039950032040000e08030321100d519041c803401070f07899100000c00c4e0084481c08103a4010500b22800d0501c0c010300800e055060052152406d600144120100002c0310045910308592100e0015119066030300107041c1d410000e50096901500401403020000310b40f8100c0d200359003295030b41da0340c80790b200d000c071080200010015500ba405a40755148941c0f02c074524000014159500282080d0039041c3c0c560001c80f0411781d020032140c0701030a140c0c004ca00a980601c141c80c0130801c5251a0082d140480c01e0414020300c1249a050750505010b040da00004c00d141c0d009904101c54000e021000e49809400c4a0407401c1e50b003440001041d2034440e0007042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 695559847 1250 695558597 695558609
    0x5090106020c060a09150504081506011e12110a080c030f070e03030904050103060614062811030a091703130501120905030f0d0605240304110904060b010306050307 72
    0x300003503802d0740801005a1240140b802080807800004c1200002101c2044062869455055945240c48003450500ea43c0844025030144040100724036a41c00107001e040c00c4404040940541010300c4054815070900e000b484142490403c0c0c10107508909001850391030120303150f0410a03601d080c0404054402100c140c0039124900c404601950301403d02919242c3d0020282c9042400c4000880d0484200364815144661101001c0010480c4042c80600d444010b03034002e0328101100c2c0002038840740c1c1521444480b45810f4165111a201d82410703070700c80c1c1009003580d6031600e5000000388851414050f185240e91854080036084a0010032070b040200814009400c50f4036000041d25010301000881c020181c9850704240001e01c14402460408030f10340d01c00c0c0c0c6580c814031804040381c040e9080a0f018010710424140042c0d1030300e1003800c41d030482c02c1c80710740d680d51289001090b4900c0c8840c01500320041c1d0082c04200005500941ca0765178080c1d80801a080e03484007050781d07038510b0b8861701c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 695561097 1250 695559847 695559853
    0x12030c06010f142d040207060203040f06201b03070c1706070c0b040f05100603032f070e1003080f1c0203010b3405070e010e010501051c0b04021809010509010602 71
    0x2000208112a104c014001400d200050b12503606991044038215290003912503a40d08000061117554201c0c10f004030982e00c4410072003950441c9100e900080d510b25492040d100014000800c22540c45aa001d1241c4940560f981004180241e101400d41c01c180541e20004103034a1061505801d034982000c02c803a401c0d25151030700c807040c0300c440308140c94502032441540f032510150b015403401903210b1703510220440f070b180082c040050024034940d0005081c120101c0d01c0c8200000740b100941e101c4172a189101c0d15901c0c5031b11010040343d40018a00c1030301107212440000c000c4003509600703110000c0c0744c82484075000b028040b88002d0003400c000701800d000c40220514154488062483c40c16032a00c661080f13190b403124800c0c5945022100d0760700c81c0c041403000da4001e88041d401040403002a90b801c1d418580040c0c51030160404104000f01940c52909800c1090b402c0045018000341085580350072035200045802c00603214240505401c13800018942419940c01d03040703c1303040e80a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 695562347 1250 695561097 695561149
    0x2010909053301091212110a0b0705041e0303050d33030302160806130201170705090f030a2a0f0b0304030318030e12030c06010f14 58
    0x440d4004040140a16070a079203420b10100c800b64035802030861503120840300e8180300c41d84400040c041c41e00c98010441030b03284081d40500090141408499600385824002d0360055495581031138489050b9010b031400346e2840a010405820400130700c103440700b00c80d100c1c95212508004021400b45484001c0010b0310401612a80c1092079021a0b01411a00510b5114526611060480c0c8003050201442ca881004080041540410115043d200c494800700b91503032510250544450340106042100d555405803241160300c260b09011403c00496600a01420240d0000300b89030010546070340110340030040d045481c5030028052500039444441f60070880c40c504103000310b071b0591041410042201c100041458000314030000c01030050030b51600e17100c0c42c0604000701a03584103074801c4c0b01e00016240103000f00313a10101c80b000c410000e43c0e241301c0040c0c40401040c610b1103000010071042c01103100100d582c0308007021a0080710307404014994500a002c00704a0300841005510340101e6803090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 695563597 1250 695562347 695562359
    0x9011b1a150a15090e090a110f13050403020f011a1c120203030f010905131101110109080403060f020f031503030415030506041103160e0301060b040303081b07020109 73
    0xc0c2540c0311541c07002211440007401c01003216001c41e078000403901280880d03040000c03940080700d00e00808060b1800c040a04200e10001c1c3c81d04008a006440d100030780581c20020384602c40c0400c10410040d019285450388810508020941560304900501a65800900070350050282c100007144100744000d50032000070410501c0030b4001c80102040d4900740d27050000c034039402c0c0c034440c841c02c15401466482c640046107402c045416000022003500d00424094175141d0320719801c0c1b4a03131340b08045044550340e400040e01d40a0060342040b00940c00e00d1841070410807904080c10490784100414800c9800062292003a801141204882404288005800c420b198050b025081202a0650746000d1b11400c0700c101c458050100e0401107a11001401010704241c0708440c00c114000001c141181040841442c4092206003000e041104d448490030541e5403e501003030041813000f424542d01da50724038014000040840343d2803c6c00b505031303042800f00c003003020480d601a6030503034803d11103d040031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 695564847 1250 695563597 695563643
    0x27071d190f030c1e0f060807030b0907050903011425032c0d0311040b070c0902031302012a061d0a06200702090c030712090809011b 58
    0x9500c036840051900c000180d01299815600c091800751101050140c00e00e500450030341c02009401c0242c2002880c01c010600c030300703018542502c665207820f00158132554400c6001e000c000041c0c50f44044900f00707021406410100404448034158004d00010400c540e0f500700c1c03108212034004007160200041d81200300040c0c11240f039550241000122481c04445012416150124190104c04900003500d00c0010070415018900900d00d4140421a4045413641c0180200c0c80380180416004c90150200240c04013a00050001e20200710f48900d0322400304440300c0c9030315201b0f9011842d003c803c1680da02d050348541021001c0e450807800480c18a036078120007091401c074803c40012809051180c0c01205000c032424450049030701007460208000c0300300d620054800c115038440010456040142c90f201e4080707522266030b03041c0316142c0d0f0366054180d40c01d11001410607110781c40d12210208008e8607034041c2948160a81e0f8003140702410003500a001003c03a480644107000078004201021119 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 695566097 1250 695564847 695564869
    0x90a0209060111031809010905190f11120708060a030f02010c0204090212060103201c1e0615091802090411032d062406070227071d 58
    0x43c07400c02010b24078a200d2070b0868114a1034161002121211016240b8102c00101c5c0900202107040029003080b003c0b100ca109810744808460070b8075011300040e6113a19500c00c1001d100b08541055a4140810968130f84850496540c008502c450021480c00d003029072410050741d50040c5410381030765280d00150b0b1401c9591508a0b8032a89030441000143c42d10484040520400030040c00300b03504619009414003802401c1ea039031107403410748100407903880380c0c000b0052070852401e00e820900a030601030720013110701d1800800100841d00c603804001195001e400d001d00001075485405407500021800d60f01076103000c0e980d4030000e41c00d000251500c00003041d0030610503442100010003c001103400d0580d0328090300d840500c1d04074000c44590041c445440e03450030b41310150055181550a45210366640403ca094600c626070400095441d50021642100c3e002020715084140a1241500288641c105001841d49482c0456541070141100b41d1b03500012650809140f1603100a0041e882d0703c1e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 695567347 1250 695566097 695566099
    0x9060b0a120207080f0a02060405010b01030b01023319060b0a050703030b0a03021f020601120305160c08120a02010f1517011d01061d19020306120f07060906030203090a020906 77
    0xf04000800c1e10040c2c0f0300091005000540123000180b520741400750844103401d6207141410b040503810b03469607034042029010528040031025029403110000003c803d418070366845058220300521007030b115600503900301c24a0040c0140305040d20380d07210318007074041c8142c801c0110b48c06000340d80c00617009400c41e0002d40d6001d0145c080095403a00018880c0301d02c80e0030600142c07031000800c0700c02030b0305100c4a400b40910060304171000e142503030001e1091188480ea50804c4003030889400410044511410080105000f151a02401d080441c2c126a0003c107482001d0761804c503c0e80074108250103114030744e010f00c003001c541c000d1600e10a03504070a5030044184640d5079601100c0204507490341050a2000280300000e592410090040081d10074400c00c0054010b8986c1040030740a400e41c84007042c01141000581c880d21001c0210b440d400d4081030224050080d06842c940d810800a40d0100f00c3d1007a503618203035581e80301e0082d0b04a21050317a041c0c8030b64000c0d6a07810054203002d003180c2d400c924 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 695568597 1250 695567347 695567363
    0x4150c02030c04090b0105040b0402040b0d02210403081e060306070323010e06090c1204110f030f0f060a020901020c100c0804030b0a0506010e010c0f15090c09060b0a120207 76
    0x10b507480040e0440c1d1603200103c1d0b005400c1030040c0200d007403603ca03011b000001513508610345420720810410a0140341800684940c002035040d161060006040d850205500d10a14040c00c080c03601800c0a041210a01e184040c6003440c03d590b003088100c0d05000300c40250182c0426103403c2c0742103024001c00c40410400e410f40c0201403032908a13000c5a180200f5401e0b0711240c071424003c0030003003218406812049000700c284681044070302c0301c40700c481d001a4000b4403541d1503060440422402e1100407903240e030600490352230118035a00802c0d84031f00c503200300040e1a044e07a07400000d6030890142002c00c45c0180d200e030551030070a0403c0d900d482031000160038042c00a00d41566100c5181e07015030022a4108140401d110680b2028060b054010009082041505280100003051908030341030240050f1122078008003803202c45403407500d03030846804d014803000d41c950601180035040e40c451244210701d001000a22141b01d50700303464460000d42d5521030700049480c8030f000607401c1500c0648400c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 695569847 1250 695568597 695568613
    0x106080f1f090506100212030a0905120409021207140702090a020d020c1b010c0f200306070203041a09010c0b100914040b1f15021005040b04050f0304150c0203 70
    0x60300c0e07001d400c004005001000c2071502d80b12007403010400c4074500060a55021000510014002000b92588100c3c1460009004c9036141805813600c58283c2c3c0301a948100001c01040845664006020041d80d1a060745c0068560300d00840314501e418098103100365080c42441c0040c68912909900000c0462000d8200403110440c00c04076801604291745952050080081c13201c421241075a800c0e009081c005c01900f142d4580c40550040404010842d000c6400740f000e01c1c1203845802d120340c00d80641203503580d2400d16400380d0f8a500900a25020f013440341c0d00401781c000e00c00210381c00c0503010b9440c81d00e14481590751031100c80b00607041c001480c00d0000085400380d003502c21840241c05150030f001345410310307040203080700740040c040d0080205196822000d2140100c03511003140c606881040c4103280c40c01c1c04074100098400004011401d11080c0014401e05034080380c0200d010342c06860490407031200c0c5568034807444c46040044c0d0070440340003c8480c000c0100f10745050003d03060310191 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 695571097 1250 695569847 695569891
    0x60d09024207061a010210020a090b0a0210060b0301080708033906040b100e100b0c0c12010c0908031201120809040f0e0c0409050c04050c0903030c0a03170106080f 72
    0x144e001d100303007010b00261010b4480c4144d0390400c60590130044156046207000c412490040c0312009074000c02c16840c44c0041c820120710f10030884881c8003030b40004100012501c4d0721013140103900030b12541055205580700465020800710031540a4140700314080c0a403c1100d86103000d4441e441d0000100e007916202400c00443e0a0107814030981c410643c841c2d0705c0ca00304500f030000648a4202c1d24078456200c0030411780a6040310490103440120001985039003407031492034502804800902d070810140850211071003815000045240381c0c3e51a00540652100021035482c041c400d10520801145e000400039403411040c441095070090608a1405082c0c4010a040d03c020281d2142859a586408500800b09100d41c2d07a0701082118107020b20385540d220282c3d904c01100b0307114861550b9901089414103800100c4188d604040c05591710b03010b180ca0000d0300c41015000507030100f2450941c1088d0f400380303110914140d401c01c0e185c1d8421390700c4442440501c0e03180144050706070030402c8091241 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 695572347 1250 695571097 695571101
    0x18140a020306131b030302031b10020a050403020f0d02011202090301020f07080306010207060e1503090c041d06060105130e1b0426010207051903030605060d0902420706 74
    0x701c0c584509070300c048015070385080352111191300b0f124200c0707030b140c0041400000c2c3d01000b1501502c183c503130b070075449401d05660340d4106520115164445440000c82c40c035840e4008020704100e90003243c0d0182807a141c9024041ea058218130002d00060110071001e0f80d030780c41c99019144041002e070005080840340f6042141507449080c0940360050007104001c0d843d03a0400c4000b0252000d40382040002e0000d1012481d030035440b00c10041c4800000c0001000041c042000c0e640c84400100b061203082d0454082e08180010030703a003d0560b005001c001211540141d0448041211440110303070918a003000c42c41d2180c001400321920f4555085451401140900180c0094a84d0315150002203c0c0e40c0203070410050500ea0518159005102c0c107004240c001c1342d0b5003180702e0100207442c480c030540e1500b24010715441d00041da0184000c05d061044815a07404021001d01c02e5809c20000740300501115011050110780351442c4410600d00c1007c80b020354001c41407841403e00050500c41541d0301c01c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 695573597 1250 695572347 695572351
    0x2010b1e01030f14070c1a0c221a0a1704030809070e091506040209090a020331020405090f010608100c110606060f07020a090c0215010e0f0601111b0f01020118140a020306 75
    0x2010034009c41c141c03003840103088543d01e92007290040100290324200c2402c0c821a1440344c2a504010041003400306280a208803070341040c01f504291103d86494030380501801400d4034001c02c640315500c00450b0041c0441907860083c1c003d00024601c45060024428228030000c10301a0015000d0060341025102c1c140064003034900c1e0036002d42c032031901e6040b007410160003503205c914a296503800b20108030040c903480000103806450100c0c040d62840c0c0c02c28680707002d102b180300c815807800b080020001d07800310342001c0426202d00c0c01c0c0050100f5000031903090340d03d0b18802c6495000301010650601d0300e000104a241e11a0329414105a03460300040c440c0c60340c81d030100b80401d45130700301407100e0b42e4107003d1030300d296014204013002541407505075505000001c0200b01b03002a80800710351a071b8010742d40d00414504140c101d8007035494a200c0170540303256074201c42e8010918241c0a5600f580103001d100040a214500340840c50701d1901d40300441440020890a1401242107840240e101440720034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 695574847 1250 695573597 695573611
    0xb032e1806080a050c0907030b0f040b010e0d060507020c0937060303080610080c03071209020a0306140105030127020f060301120c0e0408040e0702010b1e01030f14070c1a 75
    0x260417450081c005d81c070400030300003010540b81c800098801d41c2c5040107003148038003d50300061000c15040c0180c460100e240c030b030264010840041c075070402907139400640c4100d400340e0940e1460340c156010b0000c40c480a0701c1c807402248520740756080154a80e407429030f01801c174400412111b0a5405d2400c1295442d070010350000e1049010490103081c0b1444445000307209203003040c0c4525260031520003c0c040505508100180c4048080901e18107410104500d6001400c00305815a00e02d80f00c401049240700c218a02c60250000051600e4184241c10012005140190048030f088840b0b20b40c4201d40e00c0120707844507084d030504155456080182d8040c18502600464050180c201500681c055602c41c2c000900c40c0c1040000058030301007601c04903142c040004000ba166040268007400440203069080010496040012000956a54030891003038900300301c102c00600306401078032003030394100100700c13403081c081900c1c1c5110302c4500c40f41d6030141d00202e401012001c07203054120415642c50b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 695576097 1250 695574847 695574853
    0x1302030a0c062f030403020907090f0e090c040b0310200f04051201110a2a0b0613090203070b0705030d020c010618050709060503060d0803010b032e1806080a05 70
    0x160a40c20f080780500801d00c0707103c0b1504854400c1d403d486699038880d502000740100f0000000c00d00085c01a07000001070f09003000300542890305d405400012010440350100d00d0f00c00d0354001519800c2c00d10544c5281040034016080c0c05030741c1a00325014152052802d8491051801c1d0350b01c110401e14041c106a0f0b904c2200c40e42c2d00d515003010014034140000303884000340d141040388840241d1a400f208c10703d205d0f9050441c00902401d0045d01004222010420302070109882c41c01086100882030303100307c030101c5c2e2000006c0b8280021900b240c44049009400d0790007160184407800072400605180c611030411680b401d02c40d2000f00c004d030f13002136181c410389070b440d000d0030b00014480c0510340c3c0c0c00c600a241c00304414900050010a002d42c4c9100e190300380040040810b04c40e40f83c0c1300d5105001034002624a66950b5540b0340b02c0820781c402caa280c4100c2c4041c0300403a254075152034200381c802d90300000a426142c14103103240395802c141c8401a101541d16200060711113414445500c0b0307140180c0c09 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 695577347 1250 695576097 695576117
    0x1032f0403170c070e0906070e010302090607060603050d0e13050a09050d020714010309050d030c05091008040b0603060105220f06140a0b030105030a030e030114240d0201081302030a0c06 82
    0x25140c5405201d0700b00780d15142c010b0701000074041b800140203601c1141c501c3c00e61030200d27038400140c2c020303c00d03180c0c9590000313000074100013406001d81021040b0b074403500c125081100041d0701115041001001203503c0a08d0b9843c0301460743c800c1d0000c5400030f08048001800e480c666503014940341480d2841c80144c0c02040c0100602e0000c1048607903c500c080c282404980d815603281c0780c40b405400c119005242e512100c501c1c4503449070058440721000a0590b01d55034194660181041400329021545000007800250041c01c010a855048440c0902408003084042c3c15000c0440c000502c0c40522580d0b6409103c8610f41c1e03401568001c0130901031b0341000082030301c01d101c8180e8031070b0003420401d03200f00b00421664900141f80342c0000d4161034501608005540003e01401842e040310303810b203586400388202d4030703003582660994020806245456503c17a505004074400b9000c3c0290120344040005025002c3c144005580b83e4401010390300c10540a0341c6228400c501c03a00410001400c0403d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 695578597 1250 695577347 695577367
    0x14070e0a0603090c172a0612100302130209150a0e0d061503061b1107050d05010219200d02060a051e090102191103070201140c01050c0d0b01032f040317 67
    0x24088070f08000c11007075000c80401d4000301f6070600c05d0069800c0c84243c40d01c001a5402616510709000d9540145442a040e641d0743e0110040e4001c46100f07441070400ea400c824080c540c0408403240c0710110344462615a031920b0410001d160b01031b4056070000d44894042c5480002e03003a10001a6100d6100040c01014030081d2000c110754802c0c2400070300c2044104071440c3c900009201c0100e03002100c486104c91407900c2c000e8064080c240d0354052007aa286140d611054126030405100c00300c1c02c8a07654060800e00340903907694500d440c201d025070440c2c404a07031440301c25044030350700a406031106c02400350b010320801e130342c03c030106d81c420401c0e50f000c034003500da125106044c945180441d103099120702e0000c00800e0b40368402c1e0740000707040c000d00c130b10303150740550141c4103440c19100000020440d074039003482c0b103044551250508030052460301291010a43c0644a0070842000900c100c0b014030222003410540c40a18400c2806001003e100000c009482c0c4540b240134000708012240c7c4031a610301c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 695579847 1250 695578597 695578633
    0x306090203060d021003021303060501050f09011a181c03030506100203180f101833050f0a090302121507030510030f050114070e0a0603090c17 63
    0x1820004615004000707009030b40e65490740007091542c04699100549a046105a00a10805041c1201403220000000600c03e65074000303412580296403001c1584007103010000148424068040840f018200c0c40c140d5051030380c00741411500f00404000e171010340d1000104032119821154510f01c19280d02c0008165040c00790076000201500c100306981125000603480380203807103202c0c403005128002c0340000e996010484036500c5014150044400341c040008006690020810004c44020280042c0c1c46082071020109218182403810324002d00c0e100020035501c021280d40201f05e010300200c0c280c0e03800348005001965840d22551620f518600c144108546494a441203d0700998a048030100c2242045075210084e4600050640c2d10f9100403000d8118580014104034146a5107c0421005500601c0040d503100c0090500303664603041104e140e100c0824030f41c0c108049a504109560003500410560fa21400540b0152912040814905118010010301c294040b2550501c1c86440c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 695581097 1250 695579847 695579849
    0xf15010302040b0922050723040e07080a0603050709091a011a070807080316030e06090d12063606050d0b040629041a150906071407060306 61
    0xa00382503007001e262503004802802104074081c064100001411034526440c82e01480103405148204401c1c00c00107402001a040d8859131041d60145d590700b00941a40b030025101180c11441c46101c00d40e4230050304032010600548461101c0341c171008003100140c0288414000703060940d0002504801034200070b1103c0e0300c00e02581d400e05940070018000c1c095181c0a25480e10340c2d0f21140c81d61126946029003282c4079284000c0c02c03802c800300502824600281d403003011959a42d40601c4071314000d811540e25010180d50a0410380d0020001401040c01451200144075603030311b001985c41c3e03543c1d800b40f850380c01240f19071080c50491034075007218a1900840300514107005000304403650030080442c108074040302c4090006001000041c04010b05a080304e0a072540c198514246142c45905203113114200881052290381001004e2401410759082d022003003000408014144259542750b1081d40c1c49028001e400c41ca0420003c408030701c0c0000001c48140090006150309450014014100c0c0c00b5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 695582347 1250 695581097 695581099
    0x3110706050304050d0c0c09020d0f0e0d020c010e0f090c0d05010b041406071118090d0c05060604240b030a050601030b031e0c120102120606070b040f080f030f15 71
    0x10b2060102055000800c2c1902035094184072914911074100828890b20342d80c00140801d00000718816858075503045040650452081404034001a0019980321a1034903884c4c80164000007007800e2661041070303002c21007840035240c21a02d0b050724000ca01d001d01e040320ba42004520000391262580d40b81c0c42898014076860420500302801c21131245500c14100301014402c04012881c181884001c03440440c40c203600511a014206611440a401040c11188a545401a90708010217030b4020b004185050303030b102024012507501c21003001f0080c6104c6064103204001080c07840700b628031041f081d002401085d5038654981c40c1407001a03007551030003040341e4100f40c1001401d6442d80c40020b13084000032021140703419032640b5004140e00e055280044603500c180500340340c00382d0000640c010061031070300d5041d500e801d50301c0308248892441446002090310090000103008202c1a010203500540715500b080d14140c4203500c450116081560003046100c16401408a10b44000c0d0100e08540c0c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 695583597 1250 695582347 695582357
    0x606090906011a13060c060f060b0f0d0f0608031201050117070305250e12120322060504140f15151c140d030b0904060b0609090403110706 61
    0x500586080e8407a0300c10720690000740506400c6200d5a2015400d507001d0350000d20501c078140750f8604009010806600050361150300e8403150780090340f000c0c06003400755101e07285c0541c9002e42d203a460030307481d600900b04444513542d108006c5014404901603a0300401c0c00c1e0000b15100e01d0710018244072001c040e03110754142300d0444103121070b0000f0400303403544c07041003410001240c2e0707500c401c41d8900750580d114145038a41d19804c8010349c15000079010f0041401a101b100710540c1c0949100c0c0d071801644108120401d09100148505c800d02c000003056a401c840c4079032010079180d50741c40c10346805480880c3c1c84160f075425a80f0010042014201100840c0014119604c150303218100941018211141822500c210f600268403840001ca815401701010440600d04500b800059030101800404084c00390141114030f10748a400741d80c1d41804000e10000e8552610750b1104018980450780035000141401154803699443d200725204a01a49481c0c8028048008186c10150300303402040c00c0c08 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 695584847 1250 695583597 695583601
    0xc0c19080601060f020c0306090d0237020105120a0203190b0907030e010e06040507030303061719171308070b070305040e10030203070314010b0d1101080415060611060609 75
    0x900026207504403051410003074012000800c00300d04040d095106960144500c0e800d00803501d0b0700090000c0e8244003a0b080d00c40d2100300c41101e12120f03086150481e10142900103441e1000301e80b4280b40104c61050400317625000300d0032003035800032000301e030030b01100baa0220420249a4a28802c1c07103106054000c100504602000002d43d0b5039400303000c68003010380e11415010040025805125540f0a01c0c04444541c60585402a91540b41e8081140040e00380a0002102000001e8603040300320005c014003c07071104043c40c00c14540002e1410b40d003982d0112100c10600304190001c0c07104407201803504040e01c1c1400502171519030b0a42c85518440c0040001a002c2680801074400752015000003804c55221501c00d91440d913850b410181d814014090b001081120f2982c00410003c0c2c441d00900040840c90200880460780b48009442d01d9203400e00d40345198411100380d0340c8580f24410000c4400e004100500c103d4105401c00400310301c41520842002d103081203016072206045454224074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 695586097 1250 695584847 695584859
    0x901061404060303051204050c0414060f01140f0f1603020d09060801140f12060906040618020d0809040906150303020118050730030c120c05030906090102030d020c0c19 74
    0x6200346c204101843c00420003280c1000414051102c808a0060040c880070161075007140000100351400e80c0310f4201c05550b0207241d405034400d100ca00307841069450a010038031103095140d40c40200d01a10801041250f803040428008071006034601960040042041c1400c1c060100383c010740082c07040c850882c0040004041d10440d11228140c00c0d2184110301b104100807070359880030b0b403010903200d000b890b0401c000034100264286c071a90055405108a0b1070420001060704c44850002e9000084e880310f810100d0341d620000c001c1c0c114080c00001d41c40740c15031a010200c4501c201c01200071503000070100280365090046a62901542c02414444c2d28039130b07200c607551445449000040b01826004002c0c8034a800310034a40c0e4000c50008002c94416460010600e40d0340356000c88103607220703d81004030b4520a00c0c0e81c680c629808801186854440e1041002a404c20f015070740c110b1004014500c40d0402c540050800c62003844000d080a40307145040108460400c2070541074908180810450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 695587347 1250 695586097 695586107
    0x5030105100e0a05011a070812010b130b0307020a02040203130b0405160b03131103160305010209010f0c03021b13061805250503250e1504050306010e090102120901061404060303 78
    0x44020040c641b2583c4d42ca90749406031642c0a01d180c6881001c01d183d00000780711096038001e0901d250801d0000c4062a260341d4001224081a510b1800591009903800011304056004580004550f19020031480700f6039501106503801300c8084416070000424401e410140d800818050080400d00a045103040400300844401c550700140a241c040c0b2100c1c80743d038605002d402001e09622b22100015a10ba080c01c502035070140d00d15a0014250003100c843c4580300c0c441e5134400d150300d0760240a06150030f51124011181944105502502c42c600c1c800451010340f0568000b40f4450103040c01e101130801d1400c04480000b00400308100300c09000c504c0f0403030740140032018191203081a54a03601c446505000340e030268044000f00100c0b010618480a8115111020360403003190101646242a401c0121034040c0b807040b950103030301480051010200c0e41344010750250113400014240034510815900d4480150b1f82c45026955400c1c0601c0600c21000303c4222074201510180900791442d50000c01c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 695588597 1250 695587347 695587379
    0x1b030c15031b0309031c181212020d1a0d020d030809120f0c010507031503060e0307080a1e050406141305130c0306120b070c050705030105100e0a0501 66
    0x800c03454000002110340c180e03540c1a68001c02e540c002c0035141d182007080690790b41e1041c121600c241002100c000c03042c3ca502d0003410201c4400c0841e103a8091003607981c0c02d02c110350180440d0103000509000a44014961000d8070b403803a08040046101802800f040640900380b140c810b00625081c0900c1002da00c404e42e0307032240d959151600b10403a40d03d11807054106501103040f890300d05000500032091001c0200174141e0550510002c2145880301ca8041e1300b100c20103880f42c003900002e40020404950164070160040e140e207403d991900380a0756600c00346600c42c02c0c000c008a100454000d84036010000309514800050a10074640341c2050809000300e002d00000c0d110389400000d100400540400664009042c0600820110500b4000b641c014141c4c01d00c80c80002450880002141c0200d0125140019002030403000c0c180c480d8541101c02c0d508421041d61540308034180020319072000d00c101741c49000c000c00c0d49020103040a14032078904070b001e0504d0200d80d00b404014410140c0755481c101c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 695589847 1250 695588597 695588629
    0x26030408030901090b0a021b011b050a0e04050903041805041a0903120103081c060308090108041a0910050a05090c0603060114040e090c0604060f051e0c1b030c 70
    0x40d40720390340d0581460140c42c2078030006258510711030a000e072024250b0040c020b02240700028420340c102d003101c90350032100e03540103104080b20908a028502030060340200941e0250f031400c100300c1203080c40401c0a40300d094980c042da03944000f0303041040d100250030340034880103003150520080c00e098032841da042a103180340c101031011030300118503010000c00849140d944002031600c01ca603980d05103c0bd0b0b40d00413515441d0440c54000100d520b810ac284901002d81382d00c841c1840c201880c2200460350010b0007801168010384036180030760340300c1d003c4101a200c0c2c0c0e00350f0001d1a41c880c2c101d400c241030b1840600600d80076410300c1c051140146000c100501c2c80360f001d864294a9603600401215604809010405440d9000070b02091030900d01c0041482180341d002100c5800015000303000c1700380305500c40c08000440d03000141482070301ca100206004c141000325a0860116131034a021150b002c0c1e4100d1400e0341c02003514011120306076a107003100c2c40d000c4001e000c0001d158000f003072207120390784009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 695591097 1250 695589847 695589863
    0x10509150406050703091a04020307061b060c0905060f0324100806010210330b1603031d24160503060d120c0303150b0a110c0405070903260304 63
    0xa08540c0b00e43d02c01c1c006c454000f549004180c152080102d601d000c00d59099021b07005403100814014060764890401000f1094900c1c0f00e01020b0f01d6400040c801600805c0803c209580d000440e42e40303e0014100d007503c44641c00d90742e8144170116500c62520310740d0040c3c1c05031941034000c110b42c0d920843d52900070100d0801b40c6140c0d8808004130b041100011204103e00d10b031820f001400f22559644502c000c42892441e1004019900d540002a29505c0351610080c803c1000003407400021502d14001c0d84a420041409101c0340c056592400c064480601164403601084d01000c2c4d85810b40e000c0142a10b07101ca2940c140100c08a0490705000d1103074051107000004900c0c0c5031180451102c9940e040001c10720490010701c8000c0c03107000b0102d010b5000070b0030400c04041d410306440d130050854068448861604192400a44440601c4441d010541c02620160303090f0b91260700449100303442aa031220b42c5581986403900c14030030040401e048000d1190000c04640c5080b0b01120741003500441e00e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 695592347 1250 695591097 695591101
    0x3041d150402160b0c07020a1211210a08031909020f1507140106060807032901050c0d0906120522020303040b04090c11061006031505060c07030501050915040605 71
    0x1070f84941e24812480281590980420403c41d8041c06001e451854400c954541300d0994401800792402a41d40016041889480c0c0d80605880d0505400f01c140c00810b00507101c0b104003032005030074088500016075100c040002002403000b000c1e0700329461008404010807203c0d46135004983c1008034804141d010b25410010320440c010700000762000107501850427917116041e1304804d40604214881c44000c16005130105040c940030b4000d5400140c09000c0020300142e43d00c0d4003d4240b4102036650341809010040c0410456042c0b000c0c000581c040c0d121107504901d001d0000301510540e00340755407480e242005110541c00d01082c1400d00e921081c9000f003410001d400001d0440c45541d0200c0301240000800240c0014260840d8400300240d8549401d014184e5180c00d8564030100c891034054031103903006011a9001e40d0010b1b07418010340203900c941d40d48620104040340e1180d00c01907519402a4420820040c090103007541c8035403881e000d00341714001b10b101d4108440010b00024180d54a580c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 695593597 1250 695592347 695592367
    0x209040204030c0807090b121b0637030c2114090106050a0e0108030d050c13031104110c0307031b060c050c07050a08030d05061f0203041d150402 64
    0x1901e01641c3c000d0b0f54480c6169841545640e501c269209858517181480362898061800d40188900b0f01c4446014206184804508640e0896501c5002e80d0243c8184840c6904421280c4141c11015003450007804485100c1c90030114841c4200d0000300f0581481c1880000c603501000610110504102003164202c1c031174102d0020b8030b10404414000e00c4e1784810800c8928054202008890042d15051000303030321102030b02c207442d100340110a50f541c010803440040302c42d65408264002d0041102905102c41781c0f05080344040c02c1e5005440c0030481c607070f80c148903240c548110852003441441291030028000080c0b6203078011140098107020746130052000b07000507009450318099108408221520341c504018061381c024008840d15481800b0022801e424024600c0c42501e16800046081046410a41c3e024110041c2065006035450101d622107005001003034940050940103191102e0808044e40020710018001b8890340c2080b10511460b1840b000c441c50704544183c2d40035079104402c0c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 695594847 1250 695593597 695593601
    0x10c0203181c0516060c030816090315020702030c060307090b0708041509081e0606241902191112031e0d0f0203042d141c110a06020904 60
    0x3010b11118100c0c0c1e4200035080007000308210350040c0c071081c4803810040d21000d08a400b0010508010081841030000c20942082da20441003098031074075000401e1031300eaa031108020009100da80ba1440e402080e84021407400340641c2e210070800349c0e00745007103261095004140110318072171542c0c640b10010b4558240025082164084c0c10450074464842046c040010550301c0745104104841c09104e5034402c20900854a40906c103404070300170b003106e449107000c02089206051408907001601c01c944404040640c0c064488560001c1015145000d5654080e0404c02030200c2206000310300c551070340000d400c0742d07024100c40c80169010007048403041c1001c0e103144100704003080c512242080700c0c442c64207000e008220030311070382e03506004061412807888282e010a8a00034020b880b20591000103542400a00c000600714042c2400d01941c681c94250f4110f11800e04102e4a41181e000c4107540b80001094000411091a147c2544400720250310340b540302c9c84400406080e00060003101c503540755 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 695596097 1250 695594847 695594869
    0x70b0f120402130203152701090203070e150417070608130c03051507110c011b03020309060a1206050f09150a0512060915100603020304031713060608010c020318 71
    0x40c0c582150780c0d0521381c40c1d03050200d50403c1503d00c2076107056101d4120b4503d20011007c21862a0080081c0d6420911800040d41004010307070204903250040c0c0c2807a5030742e00036540748440e5035882243e903141010190071103072030903091454080c4d01001007081216401180d00d588100005c0203465401c3d01440d1000300f0390040e030710140441c402c41501c12844881501c4442c050101038a4590b00d50a08240391511520001141d42c04900100c01401c86000d002c1581c52156129206581c540455440020311036040780360510001020110309a0240c0224032555029060423a582c6440520950000b01c000070300030308141145503403080007207840c4c94003403403079000e04001000d25608e09000c4021555840717040761592818801c540d4001982c010800c281402140200400f404603401c0100680282d440507200310108485109201081a508040a13028045861300d0105000d80c5003007070340643d80e440e0400d86007a4500b80081082e19000003c50f91551020140703101010103c031700040b140184 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 695597347 1250 695596097 695596129
    0xc06010524180d080a1e0219020303130b040305010f0209060a2003030108010e0c1c020105180402030a020d05100e1305191b060f050a0809010b030d0201020c070b0f120402 75
    0x2012281c1c0040144404c0506009a00c5075120303034080e02e101c10091602d13900004400050703040b1803582540c8400d58030094020b03600284c00c80c0d207411403a0345500c0059440da07000010110000c01e00b401000000e01491518500140080d4100f00d420400140d480c4030f03060600c4180141500b0050701c0c03600b541c810300c407900092416a510ba603568a2440e010342400c0c502c440070f0380200128502c540c80c010075416075640ea0410059014181c0307500545540d4004926400c6000d01c2000030003e0b542c45000441c40350301ca0346170141e2561004100b401c01d941c006800c0e020072420314030b400e100d444090011643e1080c101e204601d0304c24102d040584c10800042014146008025110814011003c032070b03412003c0c204052001540c2c3c0d51a040b038070241910590400250100060070116204191046e0005642000000c0c0750444000003841d00d900080c9010140c4d4010800c0340400009100c400010a02c20140e50710300390701084c4a44a5204c1d030301d41102802c260340c002c5000c4d5154050a20216a1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 695598597 1250 695597347 695597359
    0x3011401030501020d0608010513170c0a12110303090d05180423060603041101120b03100501090c05160b09150f0105040f0902090f09030903030d020c0601052418 71
    0x40c41c2e0030514041d6100007807000041341070603000642d20074141304007445125094081d040064065641081240e83d0202c04246402c05016000b140e0100340301708a0054811000e1040c9503440d240701402c0710120145d030140c184c0050003000348d03603c804500c03c0d0f040c00341454250340e07071031811280340c40c807110700c2101940052408440741c01c3daa0740d4040940c000c113828610040c41b55144d81c00c1200c10312003100d00810400100c580104654044c94000d00d001c00b43c21004540c510124000c82e00c2c0008181c40f02030090f4607140104041c0080707111f426241c001502d1b2082c60714092407200c07c1c3d0302d01e80d0803008100e10814000169107405c03d0007259984020090340789210b040030507000c81500c4003802854419807038021080c41d0814144a401c000d01e0b409012034100340c1e61400c5154540310000e0001c10940000c022555031075500788010103180c90f88035801a200c0c0e00c90b208040c5861030580102e401000715000b010f0300b40d9281c45881580426040315982d03203102c1d00403180150300d0100d0315250000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 695599847 1250 695598597 695598599
    0x617073f0c031a030109020d2d06020d0e07060203120411091608090102030103030e190902030a140c36030118060c030615030f140a0504020102160b03060d0203011401 73
    0x554190800443c079200207100b20400d2000b60205401c0303c071400d800941c05140c2582d00000990750b403000740083c01c09111107024204440251610031071444000b2500941c1c001003d5040443c0742c031442400c00303a007400400c1d03001c0c203015001c1c0d540e1003005102268040c040b0300207401c100011500c0c08000c3c2d0050b01d080d145080c04551030700c0201200006c50040f8401e000003c0543c1070510036207040380d405985042d03c0e06c0045050009005442040d060050404000803501c902940000c0d0b0140c8140c0e130300016000e4941c2c004a02480000d05220000b01d070400100a04803139680005076000451035255080788181a141c20000c09100021034040d400c012614411020341100d00c5c03821801240d082c468910365280c100d0858945000d15507103200c0406601c0708041c465440782d4156020f0980000349840142c034120200401100c01d5443e1035110803c103c110f5030b0520010b03041102359152040c00d117080404a074694040185a54080e05502c203041c0150b40e02504032200200d2191b925503255 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 695601097 1250 695599847 695599871
    0xa170d0e01150512010227030309091503010e1203150307170105011505070309031103010204030b010909021810061d0d0b0916030507050d0c0b040617073f 68
    0xc0c0c0c0f00c1c0750300c900c80f05000d01038a040107008a603245400e40c4805402800c0c440540d42d8045048204281c00d480b06110704c030b00c40d0311b82200c1180500c1c4084408030801c441001050300351148503907009116040440a0580b01c114142034179009200e001080d80600004404a8a0228140e00500c40348402c8007520880102c103500030340c140c440e0031665010540300360301c0940d001d206069000b0002500e0032410004102e43c161002c58498000340090315040e52529000301044003a00458800f95454107401f00f186000f484a000e0200700c5a00e44400b89402d500450042034903124840921500140026940d001611b51801d1004001e00d00710809485080402c034003001150048880d124908044503040c010380090021280c0c003000402001e41002d0902c2105900c038101250b402c061181e000c245d01c0800c00140019000d9aa1038102d61058103100071000c00001e00300b041441000c40c1b80141c40b5100d581841c000d85401c0404200c01012070350468060351803c425221098545809034810b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 695602347 1250 695601097 695601131
    0x1504060b360105090103120828020d150b071e0206070f0611030910020d060807060f090605090a03060b0f03030307020c030f1b01080424060302120a170d0e01 69
    0x11002000c901d100243e0f00d803428031241030001e00001d07180702c0c8a161120a11440303460065400030007180444c080b0004080403c0c1110000c0075014000742d004158402024040d10030420803004405100020924200085286114084014125144010502d05540f507601d103003201403035000c1d203034544e900100e04042080015400b0111000743c00e0109540d9400f00d81c3d01500d00914050014204140d06036040d00001d50184001c03002145c1c89131000183c5040910481d002410980ca5407080a0081c110040c00945942c00200900c04148002e000e5a1280210380050300c1e0300c41000240c610000c1c1c0050400c81d813448a040e40f5202c000100a044c42d400706005529110541c2290b034641d030402d084907200c062403111180e81d903040284803180f035845003851507003240c000c06500c0e03050015050000160700c00c05441c0044191144070030002c600b0000c00e2118030b104e090002d000c030122030f90740c0c00300c0608481d01090070090000c940e96503007204a0b40941302000d0044000c1243c07594843d07451003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 695603597 1250 695602347 695602429
    0x105180a06110d0801050102030a0f0e0d0501020a09080102040b0d2304141b030d0c0f0c0b090901060309020904030f09050310090210050c060610110105190b01021504060b 75
    0x182e54007492603001141400ba688803410380310143c0145090458900d400c98070701016440100810864510540c920b4581c0d045800c0500d0081001581c1c80c16840c41c0a4107002c80d540c41030f00a41c0c410401007003001d40e40c500392034010b10308280c0420703040b40120502d00b501d100d24601288a04124052000300418110409075401e40d01081d900205581203104042402d44400300e50190401c490405807644100701400c1a41e110b402d071459100c1d22500c8481a031081500014034003030f800900c949107803800783d1006004203924a4140f020390503582c04100074581c05030000b42445003041071030046600443d90080a018040c0464000d08a6130003040081c09589030b0581c016609a002d00720b48a1040003100d69800e900c000400e0b0701e459036400c0c0f005074024603400c1c0e410400808641c09001c0400e005860048040086a84402101000600c00c450b040d0641d10305650103244c4421065200707203030081e4090380000380014800c40c00000b00f0746101c4504105101114840d204c1d415004c96000000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 695604847 1250 695603597 695603627
    0x1203050a110a0e011b02010905040209120d0207091b1d030f12031f2105010f090b070906180504020f070f0c06170f060f0f03010c020c090a020909060105180a06 70
    0x7100150402880c0301c005d226010307029000500c1e0200a0107282869001000c811030090a030700e18a1260040c01410b10480206030401a000b42e0020001d00405016051021032680601881c0451071400030b480490b100c010184809a4949403006da0f035400e11101003003e61070010b0b41c080004040205000b039100310380d010004d550002d041a00349030301c1050003080c1c4841e50040c0480401000b5032392000c0c400004225155900d9820340c5c04ca401250242607032a81c81621011404d0500c007070302400e00c0d54280c00071800c02521a24a011304501c1102100c2124010750740160f4400741034a10b881548540080949826900b00110003044440c0c54410100ea480d40e841d075040760721805902110100655055444145600100b4440e1a1150300c12602900052501d42511400c1d00428256009a91148051380090700b1187c040e04040182c1c50b4442d0384000114a407405510028140c401c01034001c0d41009030101c0c031189070b1078248040c80002680186080c18013552034400412602d041c007040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 695606097 1250 695604847 695604857
    0x1030e0a290c04060f08311e020303041a070803090d0807020309100e1906120f050402090f06030a060216020a09180b15040203090102030f060d1203050a110a0e01 71
    0x108051160740545054030402d030b865112105c0c003800c0c00c940b0b03510301910011030302031240070050804400046500d640704c00281d0100b00f160503806c010b0840054000d24025800701c1c00c0c10900144e1b0040100d80c1941c41038103c150a6a900c0110a041c501807182c0040c1002d0000042c000380c1900010511707403072043c1c0d83da03110540d91024070403038483c0904c1c2c0e04a07802081001104002c02d00900416900900181040031215221680c0c8698501070340d00c5140418450419050f00c54401d00554249140341d072000d005505041d4003003440481d0091121581c64a41e90215220780d90500c00b08001d20380041081d0341340d85285039044101c0c03000c041c0c200e11a000e1144c000420814601031600c0c4101d5000040c1e40548c4a40c881d403006600040c00e520982000c903030700040c140e40b144060b41c0109a440c00060b12454001404d03c0340748000303080c581c0301382c80c80b00e40400011141c07501e00030802098074002c101c41d22143c0300d0701d016109144c40001c0c000320110b00035010951001280e00301d01001d90359 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 695607347 1250 695606097 695606101
    0x13030b0c0c070f0303230d14070201050c210a09140c03060109090b151c080702040e0a050601230a060f080f15060702060d050c040f2301030e0a29 64
    0x41072828416440010081b0b480501c5145050980300141c4401c10150303550b60749800f40c044009402c951000040301c3da0144c1c040c0c24480310590901c01c00380d02400b6100300901d0940d00049003100c18a5600c1b1903800c003c0b42c00001910144181c0003000c2840d030003e8592080201013251545a80c60300056034024443c001c00025001700c28043c944081d074002e45810199110440c0c061044008200e2041c0c202e82d141710004103041c4441c022403c400c0c041c10140391652494410002590100c81c240721160303211076000d401107540428060304458488250b0800d0503a41c01c0768201c0e07181443c100c03079409003600c070b4000382e80c64001c449502d0706070503540c6440c500e0ba0b44000b0f0031380800c015980388135038a0139102010340c14106903004118982c00100041d08002c00b481e00700d41651012900108034920101e070811460161003031903400b83c4800e006d40305590007400d0441a01c01d06030b400060400d900c03001c50350b16a040900005484c50b4001e007000c0d000003416809408020600d41d00700d0000d54271400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 695608597 1250 695607347 695607359
    0x20f04061d0136080c040615051903180807050c01231309111b060c03062808010b030c040b13020c1f0903080601030504020a0b13030b0c0c07 62
    0x500040c5040c4142c41e60a08848800d03204500c0e041c0b01000e0041c2c0004215a629082100040c000c00500301c940007405c148a0a00174802544c0709940011004024084d07504038882d000001e542034030120b03102c40c00582d0280e01040707014013131028043c04003400e000c2011302807140300c40c000c0038080e01079012940da0074680001110200c04690b52000d0380d0b061400942036041440d0000c14500a0031400c80307142c21f0302c441a403000c58100b0710000c64003010004001e00185c0c203e411244802011801074511031400c40740404a6201c002c000303600c602d08940103002003145801400c5481c1d41140490b4942a48809225000f400d86c42d800610030302ca98034240401d80f9050054480f1808003900c0010003091003d9941c0182d0008800101c5500444207113035800078804440205d001240a8040361003405420301610310040500386504050804041001613100c240b865011502e04214903503840440341008031103600b16030001861040004103022445d583c1c10007400ea0b41b0045000e55400329074030a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 695609847 1250 695608597 695608637
    0xf07211401030b07210f0b031c11030408100b06040305010f0b0f040603170307090e1317040b031611030a2003030402150c0106030b0f040317130b090709020f0406 71
    0xd5010b010900c172420005425598a8110340c0c0d90760381005020500e1078142e0300207400c1001200100d1090100c00c400c00014a601c1400d010341c196821026610346801c01c024140c44032131a240c8040c032140c81d50320004098440208481c011a0080e000700508055101e40e800a403000140e6181300e0540410f05100c40d152911803102100d52041030203401044140760720401390002441801032041c0300b000010308019403050584550303049813025032900030030b14001c0c140c4a41ca0041165500003444144011000740c1c04594005104003516a805200254120352540340c030f07245e00015007c0403440030000c90300508451613100074007804001c10543c5071280360307585c001160041d60142c04201701610071148c640080c40c100d94903100115442c0e445e6214256819404d880354406030b142c0d50300300414160b00c28890100107004000880141c2803600c08503014111340340303000d0008643e20b0b02048041008000c0e40004000c00b040654503a2040003058105812030f104840200b030013000140c4516000c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 695611097 1250 695609847 695609867
    0x61b041503140730060306091410061a0c0a17040f09020a05031f03050d0e040b0102070f2304050403020715021f090807020d0503180303030f07211401030b07 69
    0x45500060004c2c14035201c0c041050703901c10500308441e80c0c4c65001c07010401c503000b050889802032002100050644041c00e00e450900745141c02520700e041d0091080c00300c0c2c1c5a482515959604090740c44035071401e41c960400d07154100c010b1250b1103d400010181c0c070000e0140044840c50800141031f1941c2d86158000e038800d03a1207801c0051820000a03900811000a94000030321b500c0d046600c039506ea945103807034039072803880c410040b035000d2030b21003010700d014041c021344440e0a10161520703d150000707500007035019008038680440d1400250309a0000303041801d018000040080c0840e0a0500340a502c4264a010342d0415101889402460900000c1e08030518400603602e04805a5401d1580d001440005421201241c0c01c0280b88056901c3c91442070740ca5000c1c070095661940b003560000d00b0015041032050080d002401000201c0c1c90401e08a43e100c3d09500706800742c1140500c0c0910f00f1402c0d40d44d80300f03a80d0b03e13280c030b60b00f0b0b003007000e0100c203040e284a0507541406454211045d5060440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 695612347 1250 695611097 695611127
    0x7060b04090c0f06110c010c0c0b0c0a020439020102120f06010201060b0a050403060209040e0313050907030c0210020a180609060305072c0a0f03050109061b02061b0415031407 77
    0x80624240d40651281c44102d01c05802115038012852b203d1507000c4d0b442e40310ba0704401241c2e1055400d4410f620f407030b00c190400d440b5402c030100e4040c90f0040c4a0140c0245003680c844400000388000350b0031034000e4044543c842c0e03c0038001c0c0d85510f88100310410307120b025242c0340d00540c0303801000318035240c5070001c6a200904c242c444504003451580d071240a903009101491b0410380714030a8016403901000907084800282c085407141604100034450444002011074080505241481004c00d40100d070b0218001100200540d440c00d1210090341c04004c00600564a4101e11500180b1a54000d2280e03003522100c0d50300b80701c192503080d030443e60005000b421f40c81480358080c00c40340500034120001c103a417901405810721103035540340884090700c003607005a80c645d4480d21028200810351088050588080304201c058980c00784000303556603c020480780c800c44105020210928072503060761700030448504161401e01401d02c00134040c011030300c9040044810300c008a41c1060040340208a4910 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 695613597 1250 695612347 695612353
    0x10204080604080f0d0e0c01450308040e0f01080610060f020f01020a0512010b1602060a02011107060911030d12150f06020f06151507060b04090c0f0611 67
    0x94035120b508440d400ba1444c0c04e200d41c8100181c4040006501943d08400101c02c0900521700c0000000b410300c401e005503031841d4040305001600402e840f01e0300b8540c0f00c0d8110101c607151908450702c94607226120f4101a2607418041400951003003942103e6100c2c21400181c03102130399030790f444181e0700c403002e8401e6860700b00807000601c4440c1c440d144010316241d480c4100c0c0d82400350481070500320307800350b001c07200052000207040c1401c0d8460b0714668010582110500d1801e64800c11200034000403030002441313204001440351300c9600c00d401102c44911203001455407601d041c58207500409000c1400c4414440350074010015160104e1008000002500d542c2c104080702d090a000034a80c01c141e4001c8614403010100320100c1ca103d01c24040c00c019001801016455a113080c40c0250040040401c0d1420005820380e6032224aa00d65181913401520354480000d0714240b00070301014046660094900100b190074805480826000c5848400c10515400d880308000c88090b40345103150340042e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 695614847 1250 695613597 695613601
    0x60e0f0709170a0605090313080319020708120705070306141e0601120513080d050f0f040302030405090a14090a170a05160201230306100e011b060b030a03200102040806 74
    0x4e481078001662091203502600d10701001494802104485908080e2141d440860041d426600031401c040f186501c5000800c00246884443c980e20b030000042c00e044c10001044800c10440104908005564400c80921159400001c0a041d05800700c80c401c2000349104800407003040106c801c0c41c0030700010b94440540242580e0b08801805020301400e2010315a6104880414080b03005410158032400010410342800d0350300c01c45008000e0f2040000310412405d110009800108a80c100c98054600100c141d840b8454500245201c20b041005000e41c00c3c10010214008504840394510a200e180290000c030009950321780500103859001c80c4080202d60071520040402e82c1c0c0c581d105250004c8915169100c00c0f0004447d104121103484010060108503d441e0200300d61310b0740c3c10b244c005003020402c1c000130321800c00100281b66880081080000b805841e8000d00e50003d005000c03201d400e40b0525000346036082880070461140380c804201580420180219401c071140d03140205265 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 695616097 1250 695614847 695614853
    0x22060806130905031614060a0501052112040602031e030114041a18070201050114060703111c020a020103110415110f0105040b0609060102011b12060e0f0709170a 71
    0x4000300c80b8260f540344810b2000540204002e0421554540b14111071b1035510101b070180c0d031904030003404071010242400d0043c445600ea0300018001c071103025558101d00c4079150071103400c1070041128464051000039012580359000002418542e4850b6401d800c00c041c0c0d00005150b42c0030078000d040b811000d20304030038014a026041450380200c907054888141d40e8940005104c030304c0842000001c0561a410042095020b11501d80140018010040c0000d0800c2c0000e00c20f00c19040020240b05201c031684110402c20041030752030f0300c80c444402e840c100a40390041d544004d2088224002410041e1b184004100507095804680807140100d6920700d50207800e0300c1040c03124080381882c0c03085a4020103e14400d01540707000368001e0320007890500308103040c882c8c1e5850052416042d681094415641080c0c0b0800010007c2400d251055901c0070700d00480c80030340001e5102000002c104018003848000721a43c803030142c060342e100c00036010f0755180301590307290743c81e820a9042c0c1c00401541d804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 695617347 1250 695616097 695616101
    0x3051908271f060506070b25020309010f020f1f061e05060c03071a0103060b03030702090f0907090e1513051f110a0f030c0e150c0f032206080613 64
    0x1091210000c04a81c0c0c644610100d20301c2d1b0071165040e103003060b00c00180403549251190510652110400403004011400c601956900c0b410003001d04210b000e01c1000c40c010b02c01c0c0f11606200b080301d0706413418081e40d05640c0311000100c0c946860920301e0724030b0003d003039062001020b502101c014103820809140108000803074201e0244d10181340401c01c250380005056030302d000014161031042d100c5039419070070503808480b82011018005d500411100340541e035010b003d01d40c4056a003207800784a07a9090303152030034160300740c3c440c540706c900308241ca80031800041617109641400c01481c5101d03940703800f495824103041a4016010b81c010031324444141100581628803114052000b1552012403179007050f80c3c0c1d00c42e4507614000340740c069aa5514075407500a0209140507840d01c880c03900d0001000030000720744480000d090718030004403400c22080911140041e07540b9241070300d40b200c504c03402c001c0c002c24a200040d4400c090a0402003155030084424074050b910142c2645c20030301064070b41c480 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 695618597 1250 695617347 695617393
    0x16033605150115020d0521090106090e0c18011d0a0b0d03030b04050105060c150a1107121e0906111c1d0d1703040305190827 55
    0x35540266001181401c2015680d80d00030210f50124052030b02e900c00000b410030700d180b5030700810404100240e40e0010f1102540c1108a8658100c030025901e07107403129801880903500c0216502d060900400e0104000710380f200302c00d002070740c08600d0209104030b0040c0740b603004d0040c1a4202d1070321108e030705d9020301d0390105648440d1503000041c2255886002400071120400c00700c1c0040d8903030149140038105801264010710b000d80d6082e0900000b581069296090800d40c180c0c1c56610b0340c00034800c001e960f0800343e4a5141c00314643d23030781e05003410821700c50044140e40307201142c4004104034074909903030040740c2852540da448a14050500404488a035046d4030580b550b4890341e10719200e40540c18000b083c0c80600e03a1210110005400c281d126021440d80c00c0341d11540c104d0030a40e0114800d0400d100d0440ca103281c2844e5039954520341074903140640ba1050000464009441100c603030045e0354240101c40403488c0031002080ea24905c04850b1940c00a0980c0d41c01c000c20204100d10901d00c101c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 695619847 1250 695618597 695618603
    0x60a0c0f030c0f2f01210b0405040809031c02030a080601051b07090e0a0c060f1806080604050c0a1713051204090e15070c0218160336 59
    0x11584001940f03405401005400d8183ea46640c40d0040350311104488001d50141542108403091034101140080d00d040c00700c50403c040008076a07500e20944081c0d0f4480303007402c400204208a40c1c2003900b001d50460b080690858020300c0703507424006c00c40c50400501d89a400b0a40c0c000d500c1c0c1401c20104898540c4098280760500c0700a1080c08180d10401f01408803410380100140016480c2152500540305007c0c0e0958264200034401400f05414041000036260541082c40705e00d940302d0000c403211090550020b80c5003500100124103d50f0041c1014000c040488051280d5110710010f01414485c8440d03a20211b4200c00f1000c000300d10b9218019404881c4440c0e010600c40140c40c2c180c20b1068000c04000c840d20000703814001c101d200d10038412084208001042d0308100c1c00c581800c16040504040244043e10780f50100319074aa07000141c1c0c5c0c103800f2083d41914100044210100d01c0d40c0c68104004c0b07803d003090000d00f03400e040c14500000803800c11a80e0302c0440e415003011a06000d80c419 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 695621097 1250 695619847 695619857
    0xd0603020310050901180302070b030c1312030f210b03010f06120b1305031804090218040c080d02030409051005030d020a050111030f071206090c090302030705060a0c0f03 75
    0x907a80c2403200c0341042c0728210001c6920310341209071074215140c00155000c9200c654800c2c41c0404d50018075081550607403c0d00d503940e40c440c0e08082c24280200b150407c442545800b001c80c070440d640c80280c2e0b200e0b1107600c812000100070f110948142e080b11065000040f0803844220780d050040d04080e0946501030000075401418404030f00540c3c50607080309108802e14a45901000a215981030f40303c0600c00841c41040c0c050350b42c45032207104804182c42104542091140c090351940d01541040354020501c441c407001180a541103940202e5040e03035a10044580080d03000170108070000b41038101d034051440d0a04003a120002408003408117185140e80d1a00494a40c070204071510000c00542c000340711a40307035845d02c1400c1d103101803000c03203180000f230051107281170056100300d8205d542414411007015102500d8001010a030380b102011500b0201c0c00f100890f00122900281c900983c1901d205a0701c4000380322040c4241c0c034140e030020b4103030050780c03011900030700002da02c840c4a0f140c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 695622347 1250 695621097 695621099
    0xf02390f120a020306060d030c0b041703070f08100302090a0c030e03040803030f091b01141306030e19050c010503250302130602010e061609120609050606011b080d06 73
    0x210303800c070215119003140307584002c0c040400c0d46000c01800d54440f1007282c680c6001c40542c0d400511202030000002d1100481c0740104081000c110502d00301e01e14050b684076181e19150030300a10600c0401d00c1d2038082011400401e58081c51400700d0720949801611900654031103c445000801043d13943c5420150745140701341054809200a00042015400a41d01c900307142e072003000040d40242c401d05071507004070300210980241c03c4030010b5145007404c00c59404c03442034129509034458210110780c6c1c0c030404c40021031415015848441703000d140f44200c2e02007180e150045c48041118100242141c3e00c01910910150700c100021640a41505e5407000200e041c86c40c0b0241148103a503044010075004200400040d5184440000a01c0148002c1c042031507a0000183c4861000d01b5010780c403113861080000550140f14030740010000c800e02d201140b40a4104000108001a0111441d0180d50013148480d23125080306d070302445811602c0f142d41d07041d51761342c04007a5100d40b2070503100c1038036550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 695623597 1250 695622347 695622349
    0x1003080903071e050a0608090601060305041707350f0904020c1209010806040522020a0503070308071a09060a0b130f0e120a0e010c110a060f02390f 65
    0x242801001d019283c9020941c03c01003000584c0c100d5401003801c006d01c400c20896000030008640741100c91909000441d43c0b59030070005510110101302d800c2400e0000341039020440703010054031000c0076044085551008020103103c1d43c4200740649142c1003018004909414501401000000d400a000501d400e01200b221401e140d2441b0040c1d02114001c1052881540c0044400794840b1045904104500e0075510880300400c000c03020842c0408055800001c6403244c00803203020b480d00504075504a44d407031034141c03c160b1015104a4410030480110700f40c4012984525000780c0e01c610207450241d0301c00b250365004001c41c020141d4400554400482d2009c1c0610070700c20382c0d2642c00d00115003003200b0308101c1c0c9025120081c0c52005881000015541c503404280600107a60034601034408000c1c1c0c1c141080c13505900c01d00c859001a042c100020400d81105082c001030a06800351400c02c1c410b00038034981c001c0303c4042d0040c0c40711003003100c1c0c0d00e0030422200c0e407103001d80080910110f010804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 695624847 1250 695623597 695623619
    0x62421070e16080703060e1303030f050a02070317010e0610180e07030b12030d0e1e030304120e01050f0a110d090603151202040c02030f07120f0206100308090307 71
    0x380ba22400d405042d404085840e0348059242c0d8001854202805214508118546004001020701c007400300309030100c000705407298200b1018010a000b040c055424075660003c004c0d408124203d010441003020010404031580069040f11042d04108006644100070700c1011130400f1508800c00084501a803408500f03103908030050800d07038540340740d1840c1c4041d000c3e08403095020702d544a403010041107441103d00100319070034050b182801141c0c5038100d803010361a0803d0302910004400924858000d014400406107202c2c501510110030a0341c6415002e4403100311100b6880d0004104000308012281c03d01c0049c440c0300303424500242800c16804029040c81c8400d4415000210b10350010080c40b54140100a060441080700c2e0b0780003840d01888185c4a1178441e0000d0049841e100400c441a0090069510a42c40601110307070f01c00c0d0300c0c0f8068599514a1b5039903408210550750300f00b1007500c00207140c1d10890030001d03200da144d03007151143c0365183c01044000e641841004000b240c144114 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 695626097 1250 695624847 695624851
    0x30203181902010e01030203091b01020a05070b0924040501051315020703020909070e1528050910060507060509120705010e0606040510060e01051b062421070e 70
    0x9018050264801c910004192900d0855528101401401801800b1401007440441901ca41c8a034032081e00d21800141e090102d00f080190482c09608000070300c107601d00e801002c1c400c1c012100145a028112000309034030304201c0910940390810f020610455001c0c1c4000c103a40c5225501a00c441590b50801c40e10b1343c0501108040141c02100302081141802d001ca55001100c5030081e000781410000d03002da190788002c26100c040701c15106107202640724100352850030000c5140390400c8107200d0301482c1036aa001d100302405003100500150740c014010541105480b441c0c1e580390320301020b0391a81400f03070401070141d0030b01c1e00801e6520032004090b0b800030071905214100102d88011414032070b0303042045c02028103020394200820401010f0f0f00842ca40c0075a655410040c5245191200489250049400d4441040d108040001e05103500280503849910300c00d26988000c0701880c00c80001020040449422a065885810719941616000c81c481030519084940e140d503200b012422451381 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 695627347 1250 695626097 695626123
    0x603110d0207030e031515011206090e03040312051e1e18010207080a0f0209040c0b0409141b0d020714100b090c030601141b0708030924090103020318 66
    0x510760944c0541e0a0034016102c5903541c1e10408106481c04007681d410061352505010b0400004a241d12082229036210102622804008205648521000503600d90090006a400d000300421030b8030b505114000f00d0318000600c0e46039481440c2c00f01ca01c4611a0880c103030340c0340800342c4503480c0006c4840c0320000d000c2c0300051505031144400100b0019003030081e140c00600460f000022814041504004041001d1781d055511044560b10340c1010502c0b8903154101d4003135124001000613202100790001e41c800d0b0300c0e00c1000859034942c5801c01e059410f11480c0c203241e6060600404002006c1503000d0700c3e84034007030103c80c04200d2500503c07605001c0f111276032a080a40c0c460b140051401c041072429031064185d0249895400d200e400a0407044801c481484040000244500c1e00040301c2000c07803410b4059407c99208580311528076807030342c1000c0d4000d0700603d20000c00d20010f140c40b281003074407810040101460031015034011006540014a0b4040a107440000365841c072104000c40140d50760 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 695628597 1250 695627347 695627357
    0x60209040c26040f030e0307030b070810060203120624030421090b160303061d090c010518090603070b0c0c040606031a0111120409020c010509030406090603110d020703 74
    0x1541410038607803441108841c1c0c2d0307031101108003c00a100804a40403890b00340c2001d1144011071800680741c802c0c02e0308000d044011280a0294641e00440c107140074034400481e0320344107516041b040b42e40740103040c120340c02c0e507001c04003091f42818041075106141c0620b1003403100e14500084611900d0340141c408031407030300b01c00858240a0255582c144c103098a54541034000301c0c0b400c006060140282800c403a1310315049a8100c040501a40c02000142001e400b44440c11441441043c5042d404880302c8440d40120421907070f10b50310401c00c4481ca280000745c108407001c441818002d40e4036004003410340620540501296021034100541a45800c400061203d54200f0050205503122030b4008000d050402d134000c64030300060f5540f58007000080c40e0002001080040c1c0510f0f00403c640350806079080003501065200b8150001c0040301448002030001c0c0d213541e00f503241d036031042d4810b01d0002074001400b441528800d80059000c40c018414203420030240082e19400c80e4030600d07003200410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 695629847 1250 695628597 695628617
    0x21204021302090901030b10170a11030106151103040915031a04082203021906030e070807030b0a0e1204030b100807180e0102072402180904060209040c 67
    0x200c0c1c40c4150180d605410346041d414104482c020a040710b0040c0402054032096100140c607403081c150031880104401c044054050f445040c07102e840e814105400c0d1000c1039502c1001d01d0368201405407030104c030f0186660310401d00207820100da95103506030418030180030400001031b101030703a8040c6106117415203000b02c0f0301c145503162010080684000d420801c046c5c400400010a10300ca054801d008020130b0004be591110315030740714040350107804c000e41c000c01115555426076081c0198009594540d1010401092021903080d038851040c41640440c0e0300039502400007460b400c14040d000b0456040100b00352070b83c0c00d403ca042440c0f50381d203841c00b95004178041080c041c01602280c0c00c044140324a46180741002d0340c050b01c03140a03000e02c8403c04240d0140c0c00c045501039002880c1c00707403180300031911146a8503041c20200c82d040d403501c0f0703885078000e003441e03580509200300d44400d010181d4080c0c0e1410800706000300b0000080c0291002d503402e202e00450fa448a002d00e44080c8040ea030340c0e004e04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 695631097 1250 695629847 695629849
    0x5013512040611010506220b030a0b0603010c0207030f110a0317071101180e090304030f061b080c0301150c0605150306150102030909100b0c030a08180604020d031202120402 76
    0xf541e030050701000c940e810442801080d07210300c15881480d2010344003901c4000d03c6000400090011200c0d017682610460000ca0280a02210481d003c0c0e0b508a00030301410421520490380d4042601010f491506506c1c1310000292400014110180000c0e000c8404541d4035250f86007240040c2612102402c00007940384100a031080110031080403d0902e48441d80740c3d02034608001403180100002d090814020801c81d0f0f030200103481c01990b00c2920990001090710b88030014152011015000c0200c0d12160315111340a03d016922440c07480303140500350ba2810300400d07507984c400304018041c0141b01d4054800701c6c01d80d0150350b1145080c1c902c00061000d081050510300300004205c0c206082d00389020b030680e030781c2c040221143d40d481101c110000d521803202ca03012004565000c5104100d00003841d01448030080007406000c80720740c440810b40e03511944c40b0707084040c5d070404000c2d45030850400100180381101501480500a25040502d100044c0b00c01d0704a07400078099408503901c2d0b400300011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 695632347 1250 695631097 695631107
    0x3030a0c120f0e040c0306090e030418060605030408071505070e0109050603070207030611040f06080108371a070903020a05042307050d230901050135120406 69
    0x211440d2a08000070106100014010143c080c100c0d0f208a1711501100842c3c1c2c400e8012102034407880348104410710302500655030325803040c4100c15103604600d40740d208480c81c1d482a43d044035015190281f4603544c07503690640c182d2200740203ca00786218240d02090301414400e10b8030843c0251114461506000c0001d4802c1c0607a0b40705078480c6034104108180e142d03010034100222540840042007a41c4d206100c44090b008582280001004006001a50390341c0840d03064122014a415640340c01588000ca15071509654110216110445d26000e0a07021165040700028040c0d0503c040f4050038006440180c072056030680b001880404c024400e40c60880140c2c0c0042c2400c8504103c0c1c010508110038110a240c0c1d80700348c410301c480000034100340c000c1e4100d90840601d00010001c005011568642441c581030403002d0854428000a00034241441a54140c03007406e907075500e511350246050405200202003010940d481c0035803080c0c002c01c00b00452003071062520300307142c0c6542c00d00c00d0040c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 695633597 1250 695632347 695632373
    0xf150603010b0d110d02010311031f0e070f0e01030f09121b0f030e03030c0106030803011419050f0f19050301150f030312060b0c010c0f11030301050d1103030a0c 71
    0x44507140c515680e0000402ea0469a5103044040e01d41201798aa5800103034004c104614421012580010405c80643c0170415800c007000d4003c010240625211040d41035040d40450304a404038240136103000409020f40c0681040740130514000c140f80c1c50f1152844203503a10401c00b2610031015076105050303950006554159128030000c22010211642c44040c501b2035490b00217022b0115040c01646652010300c21144241420802817007199075911380f03004240d0092007146444030700b15001000c28a060302900f110044d0388207003001c01c0c0781440d0800289a928400040d030020003245884c43c1601c0f44a061030491040d00c00c01d4080d58903010a00d400c0da01c0320301c0e050100c2d0389603030b00c01e00c0320352484c50f5440705981e054a8824003281c0080111401041c06400c4070221600c042046a500c04054000d00d940322140d03940c001c03a4504c3c00d0390903103900e003015a070158650001d200610040c14442407070401c460088003881c0001c0c1d00d00000c070b419640324030701040c0064545454841404441c5070945 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 695634847 1250 695633597 695633599
    0x3050903070b0c0a022d010b010c0201080a0b030102040503100504060c0905090708070507061a03121c020708090604030c0303090506120103060c0e100c031403270f150603010b 77
    0x10718003841035a4610542a00512000d0594804940940395601c00c02424100300c6142078500d0012840702004007603090b516800c081c007582000c05904080d441454035243c07856068592000301e0b11003640752009400043c142030b41642d030901c400556550104007034540c90040c480009441d043c503007040d900382c40c080c031110030501440301c408002a8441c4c039100d40d808901d61510001036120004100c0704c2d0300c80c080000d00061300b0000d801c2820b521a40c20814500c600b2003c1710762414034141800554011450318003450558008400c0365030081d90018a0b08600c148141b902e441044000104250455081658200f040c034106004142d0002180c4019200440f030311800c02450119909442205000c014110b940312281c245029001d14844c1222050041c5400c0d0701c810400d00061940d1030403801680022180040c07040d2444240c41107d020303909250740960350065184185450f0344210141203014494408683c0b9900310078801d03c9820f04a840620b22a418403004041c2502c0e01003c41d9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 695636097 1250 695634847 695634853
    0x90b280603021f0c0807080409050619050d030923120f0613060e070902030603010b0f0307290c0105041103010e0c01120e031801090e0c0d110c010912030509 69
    0x41c00981d4070810b10542410500b4010f007181110710030100c0d000945480b00a00c82800400c05900b00320f9841d01810554000e284100a40d64581d0200250203400113940d1030301e855041414861400e044100d890790901904050340341680d545480c1514203000702404105040d45041c080b0585001134115011940107401000c4076401c51031202c0c4c480c04054030290b08210006907440c108880c941100328800180010390308420354420004002e54401c031a40c0c1c0c865440c0255100680c58406105042d0040140040c1131850401d021501ea240d100c004031403460480e6182c040c00c2c00f40d0365004003c01100c0300c001150742e00340703480d100e0386242100c2d480d00e20071303414100d4040000c0e200140000e402c030000d10f01079000303d000c50b0180d00200010b03103210095000000c2e00030841602c149150b000900b003a0386e084074482d81c400d0765030000c50040e600501010b00070800f0300c1c2110859009400c1c3c481001d07045615058000100a007100e40e0684112400da05021070040d07942c0d01440307155400700340400030b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 695637347 1250 695636097 695636099
    0xc0b18210601080a03120b13181106070b06100309020a09060810061409270c2b1205121317090a06110102040b0301061206091e020d090b2806 62
    0x1010700a100120022801b1076580e209006a41c0c1d1042030386416035185203000c0080031440d44c600041101d4803c03090350300705942041400f8604090381100d072181d8000c01d00d40400c1d220b803401c00c01403a00c074810840805071107800c02c6002d81c1d1144010b400800d403003513001501c0c81c50000010b060200c00054028a41e240100c1004a44030a4600b2200c440003180c5241e81d6946035840703a152084c541d841036000804200030311001c40c50000d0b03101103041d0f007242c2814426606e0080c505102204000d03864521205010400c009407004550307058072a0541011410a200702081c41c900850480d5904604900c0014100502c602401d80c1c84400c0c003600f802d81d2603c004031010825041e4030788160010012541a9000380d03d03401e6041d0f82c017a115a0b548241c2e07a59640a00409800b10070707440f51103640c501400020000c2d01c0f0700c46c1c2c6139070840107120b100a2410044c4d10034000e40002c0a0140040c0d190315050000070852140e0902c20240c03c88048807140d41d12810850200d41044034103501450404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 695638597 1250 695637347 695637353
    0x11a010f08190e160515070f0c0b0307030c080f04050d11011b0e030f0601050d020f12010603080d0e0105010503070b2a24040c0b18210601080a 63
    0x1003498201201410000041e8a5001c05810b281c91038502c4281c0c0d25140020714074800030003080421144200903e10140c0d280c03184100300341c0c410a01c0c4040c05101c010424800000c0c030225151000d180a0601001d80a070340d40e00414440c1e00171161080001e0759010b1980300c0d0740d0001d40d1143c2101e600b003001c00380352900d40d542c140d6990180920006001c81004004642c510035040004e00180460a1307104008000c14050440304e50b009c0314030b200780192170500700b0546000640038100c4400030f241b280840c06540910066250144840e500b0036815000c1c8071020307800b40681e02c000d40c0b05000d55a900c00001c00084200c2c0c40100b81d0001d240d0504004105d560b600050440503074aa010f81d5640d01c1290388440c11160100d810842c100120440415480c92401f040410490140c05651369102c51080c052120480b011500107000703a101c90000e000083c414000340c1600e50840540752901ca203443c0c001460381c4d040e00074094045110341c1d2800701c401401c1c003020780101083c034024603102040355 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 695639847 1250 695638597 695638607
    0x3120c0a0c090902370f1517061507050105041b0b0a051b070e100501090f051e0102010b0406030f150c02030d180c080d0f0503010b090603091518011a01 67
    0x8150131117051540442448041c420324130065020f8079201d041d83e000e41d9039250599281c076643c0716240700499030000080342c0c2c0d4014842d4201401c40f14012880d00d503114410001c550507a030740ca45800f4003040c041500091802d2203581d001714000da00440000807403580c0b8000200d06c1c0d0304440d910501c184038450840c0c1c0c00005690011421942c5c010000c00440100c5282ca40c0d5a40604406602042446810300c0341f00644020380d07000780c1e04c4101c0c594503400110f0b48505503101f41c41d0440070f01413000d800c1303100b03904610382c400c40144000b00305000c800d0001000c3d18515001601d0079075090303149800b004040c02224040003690b840501a10b10701100c0030b9181e0140804480c1d03032039204c44007020720703800c00a0000398240e40240442e0311241c80d00c0e0341580d80c2c2c1c1c500c01080e01040079802c00419842c02401500c0c100d03810800154a03007e079000a008890300098030440962040380b60b0604405440107005100da070207600c030013070040402150242034490043c0e02e000c0d4096801040380451740d0007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 695641097 1250 695639847 695639869
    0x203090f0f0d0305031501082725090e0d0f051804020d05091b1c080f0403141018060e1903030c0f050405061803120c0a0c090902 57
    0x1103819100e80d038196030204038404465450550b0124030700700030108068010300518080e220340d0501a035500781000041d1211841501c183d11002c040e10743ca40c100582010300c49001c1440801a141440103089464110708031144110307c814401c0181406001c1180c81541d904140000040800024842c000744c800c030b070400d04040c00c1020000701000c150b0381c0d0004100300d4107030241007103580702984c0d4490001000d003a1588a81d9008003c0d00d5080c02181d08004600d480300201102c10b2032801d40c0249040c101d500e40111035200d000c2c400c80180000103000f500023140140c920300c28400325407043d03178181050180c0e4401c01500d410203040c480d41000300c0c80038059034800c2c0c0004170105944c0320780d032424012404149000048614003c10980c0c10380114000b090152150360120840800c16240c1c0d001d64012950015014844480c6003038690712004010100582a05e0031800c510000010380d502c000380f80c080f1540081811420040f420301d01800800311101e04209410b03859000440725807407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 695642347 1250 695641097 695641099
    0xe0c06040e1803070506010f050f09040b0601050c100504110109060f020601050d06020c012a0306050d02100306050913030206070912030c02041d010b04050708070f18171501060f020309 81
    0x480095103402c1400700116400c66800000326002582c2d00c0020b0b0007849094000c040c000c100f00e070f40762170844c144086007070b010360f500c901c0b894665512100116400d03005035821196a102c0c0d1a443d24207280c051180360700850248461100f08c146110000d4160400c581c0300e00b0030049a0700100382602e0340803881605403401150051558032007402d040b0003a0040e841d020510f9442c040e40c80c0c9068101000b080d1070803810800740e102c46050520103070110761051060940001900c0d80d000700510300094bc0079100750300c0382400503080c0e842d600441d4034410219110900c1424681070786040c0740d010010103070320046a160000a050901d01f6042100c40c25035801001d000e03079030040c00110b580c2c40e0010700c0000c08200b50000140040300f400ca001c0e003000b8485038059803410000c560300d02e1090001c0c0d44924019200e0105c3d001841804407106040c04940741c4190302e250a0100d0302c6804820202da801c014440103246000c40541602d180c8001030f80600c1c24003d61500101d04a60040240c0300d4082c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 695643597 1250 695642347 695642371
    0x6020331060c06110307051305032d12032d0103020a090903110f0a11040c08010e0a02040302040207060212092b0201061205030c060a0204030c050411120a0e0c06040e 73
    0x2c0140b9018010340000094080d641d00c01004102c80c0301d074030001800c1d11565240c0100e00c0c0d55076490038191109100444c14038050020700a105001801c1d00b880d480712641d0600f280d445038180d08514407107400070399900c8064030056003031411618446030802c1c04820700c9044140b40f9407450340000c80d0801e56214152404d52185040014036000707509482d00001e060003034400312101496035541300c001da0381c0b0071641c05a0401181d00142018421840b070840e1648a80540d80d0030940340d075212032030003000440f0b61b9030200400700050310b0300c0c005011140d1090744056166000425038400100000340740252a0703214000d4005265100000009580e940420301c15651844d0ba508a0240c50a60400c010040040a00700108040040102045c50801054030070302e0f00d90440803016445a0b10001d0301e520f61281050019103442d6009880c000c814418132890840240d0410301d28220440d5440f100641c1ca80345d21901e44424800611018000c44e02c5a2601c4d0a080f031107100c12601509402110b8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 695644847 1250 695643597 695643617
    0x80706030e1e0c100e130917040905040c05030a05122d03010f06110c0f2e080a1e0b030a0c1503110a02060a0b01090f0602033106 57
    0x44207101c00c40d2052500c000100c00718608101c0903903683d81c0400c81c1402940782040740c070001849804401602c080080c040e40c0c03054500b0705203801803d216201a10305084103100c00d0000c4418030010720007803501003000308003480c041c1080011100c0c1540b285000340c01c0300300003000040303020450080c0711030350440450700d424160000804001010041c144c2c01113030750810a2020350f0003000742d4101c4503815403951000b5103c04040700c5003402d0034041c0d41c0b182d12030b801d44815403900c02140c1c08030000150403040c0e80b00b46c906090000305024030018690810110140748084d1380815901e0740004206802d000c01c2030f0304140e44111705070f04a03100209507500c040311109560b043c0520b6140507002158112103545032201001d441c038000301d00d10b0100e4603108181d8512520a0107803009102c107500079014990b2400404e401030810540d1150401104030740124034080002100d03005818154000c58485003268180031a06040e929044540d20b0000c20703807400f02e444c446020007270312035510b0a603602c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 695646097 1250 695644847 695644871
    0x1030624020709020301030b1b091507020406060c050607140d0501061805060429040806041b05030c060403030f0c061107050154030305061804051b0604080703110901080708070603 79
    0x64090f0000d82b560041501c010880d202c00c440c030140c002d1074005c860412609541e12015214228443c5000342170350402d100244400c2c0c0140180000c6905006002c2d00d00051120020202c0f40240c00007000300e919540c00011030315905140801400707065401529150804074015590004c041c48001c00307c810303802c20301000c0c3c046016540280075070702c1110390a04052812848071049190307600444209400001101e18002032112a00a00948601c3c9054117580341250004d641e107110f00c2c18020820001c500140742c500c2448140c40c10400e582d900c80c0c0d034525040f4251040803028a00e15182448039220009601180c0c0040301d034400022000c001415a6043c0303d0713055090305e400c2303039001d2a0025080c160990091131043c1001c40d034540c0e0381403015400801e4220b0541d4064419030000011840c222203107030a0f030441c100f00401c0f45007401e60b80c803880342c60700d1603e0b00103e03020905007191440728201125003e0241c85440050030825003041d402030756500251180070200340c0c40303c0b03d031062 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 695647347 1250 695646097 695646151
    0x633080c0703050c1006240804200a0305010203010f05031b0402090d08040f261b0a0f0f050406050105071101030c260613092001030624020709020301030b 68
    0x45104c4074207844508551030003000c01041603100f8004083c4105280440c0f5035410080c032445a02192074211031171f00d41c0d071646403d292000003020742e181c0d50035007803900603a5034004101c0211710030302c00035a481d0305240301c82030a06000c0c1d114501075807080358214489524000c24500070383c400c2d138005860311a6540002d0460180f110003409d0706d10006404903040c81c0c03a4140d0819525061001e80100c0b069114400320b254011036442c005411003200c0d81c1f11003a03180180e04c04d0210080002044548900c0d000c03182e059968084514404243e804000b01d092038041c40000345802d00303080b0b00b0844aa2204580c0d0040158240d0400d55200304d8840b0803400f42c0d4480040d51070700c0c4000c0740c2c4206014000b00045009490840c81f850b007014882c1401c181d14081c1172010782d4131070502c981820f030707584041c84d00810540f1880d06068031000080307242c0115446a100c4814103c075450301c00000b030103019090a41c0d6400c03219040340108010b001080341d100c20b0b290410704803120030b05072a10b0314080d442 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 695648597 1250 695647347 695647357
    0x220f0221060a0c051c0f150e0a0504020609130902120f060a18120f0225090203060423070807230703020c0301020f0d1802100f0908010633080c070305 66
    0xc00f03c29170b45201008021503920200ca44035400c6820807500c0541c05504011501d5807058200400450700000c0f1024403907000560001d2000e4101e500b0507800d00002050807020704601c90085550740182c0085d460035141246e840c2c3d0061000d8181040003003405130301d0301b00040801c00f40c0c50f161440c180d00e010855402d0342040360044110748080c0c5140300004e00c01141d920307101c00148180040c001980b20440303000000f41c5182c3c011710446515051241002c1c3d0002049194015034440a101d40740d42481c5010b40c0d810008085101c40380f4014102400241c800762080c0104900180c80303510500551220750600001c2c443c8a94a8485600d400c0b480c0620085450b9010b50000c54004071000d030180203082c05142c1c0e99824403108036003440c5e801f5080007010700a540266440011695640600301e02881a180341c80c003408074586800501d13094982c03560000920a10a5031504848002c000e60001004099110b00c20401240c4600506e910300240040f44030340000503814041500407000c50f8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 695649847 1250 695648597 695648617
    0xb03070f0b090d142a2218080706060f081501050d050319020615010201090b160903210f050304031d0409060513110303030c040905220f0221060a0c05 66
    0x90200481c85034190810b0030341d00c2900300b071800300314a10b407200e00d80b0104603103040c6c8454062249150003482158081d00c542d403d200510110040350030003140c2414020100d041c0550400700e11149001124110442c4c55802006c0b541c00c041c02149001c500780e001141140c0c0304950703160929090b030500a0851040030014445c400c001e0741600a000d8000c0b48440c070614010310311040c00000080103a007611215200106111002c03800203414001e400840c4407410414541401410340780c0d038400340c80940d035862090f510f05011440b40704040d80b0841d490041070a0345001815414595406031003040114807a0801d0035030f200c480e1100361a01c1d44030710400741e0000000d110900706035250203216540e204c1e09841070030a00c1c20755181400c0000c126805284a4110203141928025120b0b00600025100d1010451003148403a05078158400c051903141c05980c104c40c008066104001010407103050f03012510a0704c1b462507000810108140b9031210700c881c00400c990300030000460395031180305441 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 695651097 1250 695649847 695649853
    0x1140705010e0606010f05030408130512010605030d14091e1c0b0a06060801060e18072115030f02030c04090f1505130816150b03070f0b090d14 63
    0x90050010540141c0000346030344080d01c100381c40c3d00004440110341e00e03d0b8034001c01c1c003c00c04900000c00d000e000700440c5429140c4540c1c05a01c410001e108a0456a41424560b456060034080d13031900380a0758148a015050090400345840110b020764002d1045561203150301544820604404155811003080000c0044c000c0b6809031069215010b1a185e041c0c0e000040c180000b840c0c1e0215118210980310980c6420200f6842c049080740d030743c485224a00c0d00305156064418501e41b41c00581d0340030358810780b03441d81018082c40d4580301001549400d4040039041c040c00140d40f046008418054a401c003146418004003400030902d441000d07007035681c10070720b05031420b000d02c100040d141d00d05070304c01c106010108210003404410b840083e01c208072211106840103000030404001040051904081c00385800c070680c4503d0080310004a0101c25035403034401030300480c641405450082c0900c42400407000341020710780b1025004080d8018014a0701c01504020302101e82c507503500f4040c01c0701c11 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 695652347 1250 695651097 695651107
    0x61b1401060617090303010510110d05090301201804140907050108070e0f09060316060302134401060308070b0f07081b09040e030703091a0f090114 65
    0x825009181e076110b80e01c000345140c50034241c00c1c12240210360145442c400103600356402c00c01001007191100e01d49005208450b440404030010a11114128450070b80700d040d01d420003481407600f500c60b07000c0184264850340e103641115620031f509840d032174144002c00003011142400410001c10300f001c00d10026002000c2003042c1c1e020005240b0b0140c40d02a0398040590322070302d9082c0d0b00c05242c1034902c1d500c008960300e40d009a0401c0d0f64580c0c0d1102004040707030640b49541044000c2140315030445400a900000d0607000c50410000707030f000400c011426208403222101080d5842c43d42c00342415410510443c10800342d0080c800302a4100d10075900070400d4603a2490300c0f420a900c4040e045801e40c3e69000022440c505400c3c404c0d11400c4103482c0c1c03e955540b04202c07003100d600300304149000c644050240c04100e481c1c510480a0a04044000303580d0b0741c46a0034080c056060325402407800711011300d4181a544031000a40f0610035079002c0c03058856101800595290704142294860b4000c00b0031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 695653597 1250 695652347 695652383
    0xa2d0e010915030804030b04030c0b070c031803050c190b0a03050402130e0c0d050708011406040e01111b07090915050f1b1305030607050c19020a061b 66
    0x414981210384105082000b00b554031254116841d082c070002d00380c1c42052104001250304e04400d6a4010b11034a071144004078140c2c1e0724850008292804000500f05c802408105130304440d40c0d0780d05002e0400d5000c1d07160b00d51346e20140c1d1850b00100c4103021701da288207134241141c0205074010180145180d02912801407034401401804120703010780c803903245640000c2a00c4510f221f5400700c20b5a00300505030342c88400007407090324180c0c42030031910351060a0001548400a108910480c45558610b2540741014010441507a43d100ca0700c40050745001598440d10440f442210030696003681c1c0d00d4200011445070905180ba103910100603281440051410843c9004034920303008015402003166888018081c250018102c405440300b0050891581c079a903001d8010b0041081c10403c0040020788031008070741040c906030746101c08074102141403202c1100902c505403804549020740b070100b454580000743e601119105610030710041c4004040c2004105420b80d5055070004616441403010003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 695654847 1250 695653597 695653619
    0x3080708150109060509010c05070801021b03040807120309030605070c1e0201050a03021c1a010906020f030702090c0c0703081306030501050603040b060619020c0414060a2d 76
    0x88540000903034200001d4039203084000700a40a550680d5203205041c141a41030318640d01c41041d0350f040c440aa2a00c03000548104107503000740003100e00158541200c12060701d42c00080000d45c14643d00301b4401484101c00000f1000300311101c2c000041007484550400355085272480d0000784c6517508100403c07191036041140200c5240c070450b984c65004840340c01c103411050350003034004c2c00034000700b040c2c9010601c81e4001d480140042c01841d1115807c8107488000c640001d0742c82c45c030700e00948414040302d60300301010704010402c80c00a00004000b06980c10740301c1c0724801d4000d10902c0068085060851008145c0b004d40c20a802200d8040d1740360b051480064008121800600000040100d28148207018507130403144050031680c107648803681ca60020030300041031181c1200c01070100750341c1088030450005003406145c001d0b2031000c05d1070003804140c40340707140c5c1504010101d10611889460f4540e14108840615405082d051000100c40015030b24000042d000001c000300e0102d00340e820f01f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 695656097 1250 695654847 695654851
    0x71e051c0e0904030f03201903110c060a0f090f050c040c090f12020d0f0321020c06040b040203071e140d05190203030d0504081b0609070306110d090308 67
    0x360300c1c1d00e18042450000c215420804460003800103d041d000a14158042d40055580c0c0d041104000320540210000700d0998101e4612001c00b800e044a4020405401d4803880303000c0244210310030300e400e4400c00c1081d9542e00c00b030310360302c04213580708628101100c00b075200f41d4580d5800f041102030b10015003803081d03a5445c1403040d988074501c1c2410a200960040340c1600840d08403070f1a2088461800710300d0840000e2000c0d01342d800c0011403501d540025205003d40301014400e4407044240c440100d074401a000a06544010301e910400101580400005140b6449030340200007588690300d0380f0103e8140490340e4485203121204401410100701410460f1050b40c5440100c030440131444020040b020b040420003800b1a040703009410246085000c0002182d030004d0110307482d0244031003002d011138008032010354401002040e01306581c1494100c1c6102940068020001d07070030880344154441050384401460140d450004c41400a0000f040d10089040010b04110003402820094030418003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 695657347 1250 695656097 695656153
    0x191202031801050a0c0c08030901020d06060810092706060504020301090b1207030206041818031e0201050c16030201140f010611070303080712090615051e06071e05 72
    0x800000444501ca10f00c50751450008a03a1030484a06c2c094070b55207800c0d4005001034105540801c11a450402680140402407000395540703151441c0030b0306800c10080c40d0350400a45541030080f04100707985090041d1074100a600c41c0c00c40722031603074038117800140350552042d504640040000038004185611502c941001a41c15071002050601010b13203401e46c6003c000d500401c10711051005840c0c0c12824001280a1700300041d0420001303004600081d0240c0e82200081e444480712010100d10703900f90020a26240028005414090711544050165025081080d0141c09084061601c00d410a4180764030040b5078ac5100c0c107010740900e4040509000d0b090100303040412a45480c0400602901141d81660351003580d07494040d0220345480c203106110009503191500e0342c0205e51103108451203402d504868064141c82e004c140800080c180f00a42d00c515103a1441600c02c1e214641110690b85c3e00035000000e0a0b504542c11104c000d4030b49010701140f01d0030249076640c6009220701568010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 695658597 1250 695657347 695657351
    0xf0c01060b0a0e0d050607080c0d0e030d0f020a0801060509030a060f0b0f060304050a030e2b060b120c270c0301050906150a0305091e030319090206191202031801 71
    0x3c95414003040c0181984010800d0380000001800701c0d2040321002e42011403001c070985031080b400d2890098401d00000b280f200e800008400d0344544ac02d00c10805015080401036040c103c0640001c1c08511051140310300780400058101d443d50b505100c413042a0703034050030400017517282000703000080886605250145c00145000724040c540681964400e40d40071000704003401113030750112460300c14410045d800c69132000040384504c601e003000d41d242c49100b010340601503106040c8842034540c0211018006d5050b003000c0700003502c0100b0040e080c19030584a400c0e0028180851407601020003082c0420720210506110303200c14004000e40c129081140c0500054580704204016403032140403040c8182c4007044182480303802030301b280d64084100c6082e980004e460108461000c3c210345a040001d82000040080c41c2046982020751107850b8030701000341218650100b0854865521100450341d0030129444503984034445030403022405200a54903421b000194200780c4101c400e00900c0744d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 695659847 1250 695658597 695658617
    0x609110403110d05030708090f060a0f0305060118030219080a0305071505010e0f100b160302010501170d2003070c05030c04050c040501050906071a1b18060f0c01060b0a 74
    0x203d030040b40e5912258210010398038242e900e80d500745a03588071520050b040b2860b015140a540d403a90301604000a603610b0743c0500359182080201164001068181031041090080c0940c000c1c00000b00f065943c15960440340410001941d26110004d074000552807240d045c0c003c00b015840b1002c1c2280d24841d180b82000941803800038010380700240250000b44803050001428081c80f0041c442e00058134400030180b072a220303800c00346585e200c90040818200f000c60401c0030140d092003400d0062580c0c4444107100741c150f0008603240c025406442007002000300d60011002c1c0006022920030100808a07075031503d66142c035070400c113000d200301480390140c21b80c498020b0519000d1035125000b401c8000e0300d40760900e4010741b229082042c0a540003d020301124002480d195141c0c651040c098008840c6494400032070300414000b085003084550b41840061118100844100c4060f0001c0b9095502c0e00495004190940505100500c25600b86600043c601c82d850340201380c64510307a07070340603005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 695661097 1250 695659847 695659849
    0xf13170705033708070b010303180906050f060903071715070c020a0312031107050609010c05070503270315010501090506090303030c03040c0e0411031b010c021201060911040311 78
    0x40c01d242030128540c0c07450b410958284030303c46040480290f200d641c003a410207010351108a2000f1007600300700d010964a00c9071418903101400044001c100b00750090158508290204082107000901c040c02420b020550080c0d03503400340000c5020b41043c412034108003103240b120a03504d101d14061901885402c0e800300c1c400c28422035858001e0f0741c014010045040c5180d84d034501500b00c10600000301070740c64005900b1400040000c05405020340d00900540c108500303040d0845400c0c0b400c0400340f020400030702000820100995001100043c0d01400700c0c0c1030301e00502d5100040b5100c690f0700d8028500ca030030a01019000c4941610400e07a981c50b050fa4031501848041e1045440041e8558008d00c0011102d0641c08001c41c1c2c818807480840b99041e590380d001c950400c070251401c480c6c800007154528283d0030104409040500106c5040340750207240d000103002d01030680406070040031300150810101c10250010401042070b614200304a40c00e00100008030f401600080380d0b8030b400c944916401b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 695662347 1250 695661097 695661133
    0x6090501051204080d0908070b1e01090504021302030a0c02071a07060b03030c0102490e0c0907030c170103081209010605100f1e050f1317070503 64
    0x16618180c65881c40d244080440080d04800200200c030b4a800401c003400d41107005005808000d071103a005107489034210301c3c040c1030018008081c03120304180e07001c00341851100510784c1e0741140d036016030008603a22240045400c0c980d000000c244624000401c1c1701c5c0704049940a41194610b59080c1c0e403119443d4483e0700d0307040d620000542c4c0e140c9801d001c0240804e1182e070102100d220021f00320391603d09404905426a0454254000714601d0780e40043c00f445901c032944140c40d54011410b0200d400c40200d4547c80c0843c00b0300803080c081c1e0700d019906e4054420006d00b40c0f0900003c1c0405030718034118400801074130f1480b440302c1c00613001851240d10200382c500064180d95100803850b091180d00c03600851021401015030b440e80d0f481d40b00000c1e2a4541514541c0c4080841e6280b1003640c90304603015059003003461040c0c02460b4600d01c2664402c0c2c1c800199645003607440780941e0b48200d824085555841d00790440204080c0810382103e0702c80d80068a01c0440300c080c0e0a48009080e04603405003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 695663597 1250 695662347 695662349
    0x9030312160e031c17040b0f0a06030305070f0320010c03110c0307033002090a05030c03100c05090301150e220b06150d0609181106091210090201090609 67
    0x901988401001d0f168003214004244884400b885c0a0342c034061031150140d2240302c25103082d2000c0d00d21000703000f4405508881d040d400398840000f889075919503540104144514a00038101080304041d1408241c411000140032010088040301e1255009100754000c190b0007043c00b02203840e1409031103560b43c4601c2501c000ca0b103100d010f94202102da0b2016100f0280d030203400e542540d00700880780440d001444542020b011700510040e21260203005218000116402c41d40c46640039558914050343c0005038400001d40c0f480001c9008401104240d50707a01500e03032400e6065007450302d1808401c8a10f00c410044400345801c040c400d440c1c04401140c0d209030004002441480004d45001040000018035001407020f00300c0c10600600813441800c80c0c002d2000c18191584070001009040c3d802d010307140140b003082200088140542ea900314100f040e205005006440106400140d541c9840110a1640c11403055845030b100145590008100e6030008074041510174001041c110310660902c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 695664847 1250 695663597 695663599
    0xc0f06090d120209300607110307060c050f040303050309060114030607080c07020a14120303090c0d14030a0c030311040b370e24040b0d0209030312160e 67
    0x20707450704900c0441002e03500804502c0c1c0c101d00748900008400c1c0c02d13407017003441e01c1030807409052030410b000c9005410710788003030940000c0048410300c0039041c0742e0120440b49055401440040c01e6154240261360900070034408200940011074000107064101006610031400c1c082070342d0750f0340c0c2c0b00c0d690070322440150f003001d64250707102e00001140b0500034100e5076084416000c0d01810032056900080004c80075800482060015080c8206507040483c00305070615401c0d400f46040d840d02140c140ea50751070b690015071089501030100340c1801300e00020b00300c0c220300c07400507680d4858203900d020b010822204000c0740042e01d4803188034840c3c032410b01502e0075100d401100510f466485002c141aa07803644401d036510320b4900e2292000348903404d91841910a882e203c40c81e900105030b0420a4101459140883d98400c10045010842240d030441d403e66442c1c2d050f841d180d41505045400038000c02224070b4045c4000580101c8101400600d540f00c0d4900e05003101c0c4900b0514001c5a6201418909d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 695666097 1250 695664847 695664857
    0x708061803040302010c0609230c090412030b15030403030615090e040206071e06060914010f06080c0d0c0e040c0f0806040e101107020906030d0906140f0c0f06090d 72
    0x43c001988100381c6150102c0c09101d011907188420303242c50150306006c0c086030840c0581c240041c0c0c1480014401c8080ca440100c0e010315081c5004e4444900c10880c400c003e50400d55510820810f070ba841d00e460f001e49181180c191900c074a800e1502030001c0940d03001d0801515401020000458410850380056858240d482810f5450319424090f0362f801064048403071505040329417800051860f9031503101e0340a080040f0300b00e03103858205c00c110340303010143d0305d440b041d0f0000610103038050440d035404468491928448070355070315240610341c8c018000f071070800a090641003072285030b200050044c80c04044404201909c5080e1080e90840c50f004c010070b02013410349002440310318103640100d030741c1a00481940c41c52801130a03100100d80c640e8120902f081c3e4041810301c1503003404440941e0007a400d40060042e01079a050103040000d00d031060303004021082004240180c0942c041da10001c1001c4445915180d200d18401d1311910388095910441c400c04000802c068000911000844069118 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 695667347 1250 695666097 695666099
    0x307081210030816060b0409020f0d030e3f0c010e060d060602031e0a05040e07090302040905030703021b060406030b031504080c06070207180504021809070806180304 73
    0xd000e0388880040c0344920078441d0303401c00804202100002d00411a618018041100e082e1520308215042c04040038000c03403610503441c0040e01c0b203000410508004030f82040c110541444e08403002403456840a4100c0c000d038a955221000ea0240d41e2203004511050072589140300e4142410280594813010b0150300c05d518400e9a03501a21150100480c080d1421b440c1180d4600c600f0240c81081d40048010307800020200b40b0151b00c01c0150f40e0b030181c68011540b800383c003008014074a00650003860500301c082c90105a00364010300701e00000f1503003e00103100450943c14071301d48a80003c107080e400341c010f44500010a0b0040e0310911020000140b182c2e040c203081660460060401c3d480c0d070b50f01132041040707020b01c032480f020076039104c0d078841d5480d1562401c007103001c0c1c1c4c00d03e040901598207560281d201413000824244034000030340c3c0280000902c0f81d486000051944d4081841e2000099010042c042030100104081c01910311280482d400c5441c0c012400c1c80c2c3c060900902800c0b40c02c1404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 695668597 1250 695667347 695667367
    0x5032d04061a181f061d0d02030a031b1b080d0e0306010b09010c150608150108060109020309010f06240905090f180d0f030b030a03140f0d050a06090e030708 69
    0xc1115046940b49100b2001c401078203c0d403120982145c2c0110000c500d42c02075080c0ca0020f038001400c1c903031a0580310758054032510b40c0429620612040018140010b0a018480c0310b080c80c0b0b00d07080a95000001260750301a040d194001d0a00c95004d414154042d600c0506445401005d00f013007090805001004142c0c40c03c200b0f041c1c0f581204503800d0401c05082808030210b10240c11a000034404080c0c0000c0309882c100c407003440d082007048e5442d0005908001000b4107800030036200e044520442003d41eaa40d10806a00d00505c020311845282600c2c1100c081219456002010070f620403c00741641e509500245c181d03a2a009845204d0b40f024050001800412600850701d4004902c0403425880043c2e0350728103400c004001ea1a0400602d13151009a4441c0e030500501c070441400358084d048201064400400541d240310000021440014000340e250388030030100e81d203a8180000400c8603042405070b040203098944502c0c14081d00784200c0b5503010708007108070f0340d030f40740d005400c60b180102e598 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 695669847 1250 695668597 695668639
    0xf0512011802160b180f12280e091810110c120c06011508070c02031f05010905060604061d0102010b0d1b0602070b040605032d04061a 59
    0x2480d900101d9001d0002d215003462881d500d001051042c3c42e1404d103858404101d040350202c006a00240740e200800300075901c030300480c2441ca240c8502d07031165a190300c09503048441d00c070100484059000c6900800e045164010700905816504072254150360322a601a888550103c48a00c8041e0308a0a00c00c03901c042c46a0007644400076084200d4200910b5050041c182084c0315020303040141d000800076081c18080c0405800b52010449034076081e038040400901d00040140035a0501c8010702c0d101c4107666040000c0400980d4201c1c154540b883d6003100d804c0030305428401d0800807800d180210306075240480540301611600d0783d4149140226140d080c00011042031014155543c03804d0112040d01c50024885445008040d034401018415546ca82c000f60668042d004541110009108002c001c40072a41140d80c903103002d948a8039002140003c107801c54003001c81401000e1810750724090b81800840c4298044e4400700030088002018000b140112000140d02010504007124014060 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 695671097 1250 695669847 695669879
    0x6090b030709090606050901060807030e0102190c0609140a02150403170304060b0621090109050d03020c0304151e080f04121101090b15030c0618031002070c060f051201 74
    0x134501c081030459031a400708410040a030006800030f40c50104001d0b8498150044011a21030a4000c51520944945a650000d030f0103100e1010000c5c1924100f041c40425003184200c036030401040003807140c5040400c0d60342c5100c100700700e000740c5400040e404140e407514286c404407034019004688040300c04000d140c041d030004108845c060764070070f009880c9071591400340015100180210b00e24040300c0c1c1180740301200080c01c10201f40c0c1494061800a0404113200060911504007da2152507007040300b4110b002e0703500311081002c2c0f0503600071500c40d8000150003142c00c4141e0301c038450041191088614050440324280020307580404a00000c0103c10180c403500b020f4075104000d1510400407a0950b404003100fa0b82c24240c42d002d21004035801d04520071140801c600810301c00010130042801c0d030090200200c0003108031107010030181c4007407000b9119070034041e00440d038400c418500003010240901941001401e52950902d066014408807400d000320101504540c0c1e181c20160184441c43c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 695672347 1250 695671097 695671103
    0xc040f0515034606050403140315090a2028020d0e0a120b060306011403100203071806020102040906061d040911130506040c050a1d0307030b0411030106090b03070909 73
    0x2104405418030400c0440ca070f09030602c14240031841c0d0900703041c010b0400030646a182060781003082400384004810700c2003180300c0c005a840d0705050740d54080100061800701552801c0d810000c1c4107045005001000b022082941d0891058a000e003000c4500c806c80c0700140400582c1c40369480b111a140109050469560010150808680c5843e82016069490340c0c0031103000300003609100a5103010b2000d1400b400d400d841c138500c107a051000080d42d43c84055030000c1020350000114500314450003601100300281680d501e2040c1d99114000d000b54094460300030402c3c174104002c11a544911a1201c08c214500b0038604a100c1c6042000001c041d01001111900603000f03a21299454448400504d0010309400044518006e4244815180700140c40030420500b00719130340015800045a04000340c07a92000b50803911035001107403900784150005803003004444d04000400110b010f80044c11384081c0d00a0003015074030b0302d0b05810746031544a16585070300620070038030110040d60300c038588080c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 695673597 1250 695672347 695672443
    0x1061208030901020f0d0f060501030b06070f0221160614030f09101a090f0106050403080a0215040605090c01020706020709020a021002070b0402012604030c050c040f051503 76
    0x600f81100c80d46c07100710094481500e039140340c001c1901500c01c4c9802404217003001c0c00b0100b01480019840e1207051001004400c0d12036511081d900c880e00107451014007013441010840101c40610340d1075030f078601c2c001e0b00540c41046c0400c005108030450880002d03d00822070450302c411916900e12031004000701c3c2103100c0c200580c03070261144c0c054940e80301051840c0321000750796182401060000141a5030300b03841d018004000310740e8800300711000c0301d812a03800303501d604550108134100801003002d65002403800082c03000303000c0e01d0345c00740f402188090100c6d00030b242e00c0c400680e11a5624410003016070800783c810402c02c2c4840d00144405456032051324600c5004590b81c204030307013204e542980e810414104000455801c048070301002e00c4c0e0188020300154118410100c0110300401c000c0c1046840340b884030400c1810405030b002508010300c1401070598680688000700750496102007072095101015182d81004219400041c428040c44d140c03909098040340e9083c00c480503810b0060b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 695674847 1250 695673597 695673607
    0x609010c0203061503010e120904110705061f05010309020306220c030b04030f051603030c0e06190801120203031b031903020406021606050304033204170106120803090102 75
    0x1a0b014042644648a8040c80003090382d82002450f0844002c8500310000c0e510804d080d0341000e44403416144031140c1164041404000242c614199000f031800c000e1540c4500d03c02d0110011004c0101e200003050124201c0510395074000440a5410307120001e0f405030001008114070f020261000c01002042c488809c0c210169542d605c0002c118a5000b80c0384202c1c4482408100b550203204103850710325901e00103003802c2c50405a481c90000c50000103050560740c1e00c40340a858090a82c0c002e00b51001031016403500f02000e480c01c5900c20b0806003400186001001180303801e04061840c42954020703000b1070502030302c0d5a4800d0086c100d0760316018a444203000c124000702c0b107008001e031840c1241e540562580c0c5030040203850902807803400f1003480e6503e0000d0041e030350b0000940c3d03032080e014501040054400601459071810020b12031203810280e860042e05050080002c00c121142d1424074603640002e03600c014200c840724003401344030850b0480e2550200c0c91480c00b954004480100052601c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 695676097 1250 695674847 695674849
    0x30c1c0c020123180306010905042a0f030809041427011b020d080702070501080c1309060603270f08071103010207030905180906060d050709020705010203010e0a090c050609010c02 79
    0x250300131604413a0041c0ba0202c0c202440e04080c030403a030040c403189505214900b41507070346104205001c054440c46c8404088244515002404900d004180e011a0180f01580f070b402c0c1640143d0124a016010700d0030103d981070010041d0b071045105241224100105109040104030000d6165503401210f40d00c1e4010090722260041e120a0030b08076a4000f0400321100800140514800901d0f117010354011250412060341c1004d501360b8044001141c4541d20110003507981c65055007500214103003894004049181d9400d030344459908800c040130201a42045e100300c3c0301d03034405010000c11558200040700d000800150140c8042845205803180c6050000301207822600030160540001c2c18500d020040c0381450b0313980040b00106070040c0c4840c0d146c01e071700d060340d6104040c111601800070104101d05100c07003407100720050300001c4800d5588d028141040f030701030b4000b0300501100c40c2c020b030702144620845201e56001c3d1540640a1a60b00d483e207410000350760811003149040c0181d820b400001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 695677347 1250 695676097 695676167
    0x10c051f020318060415020903210c0f070f060e0303040308030f0103060c0f021c11030403150b010504031a0a060b0703030f05070f0c02060304030309080408030c1c0c0201 75
    0x40504034000050300d034070f818900c50320340d0100110981d80035004039040c44003081004001d91908082184013682d1400c1300c80c00719251404a042a03003100800080307100c50501c0c103900400b480468803084403400b150800c5115110400391040304211021440c0811580d4064155418034150040560703080540d00d46510406500455404403140c6484005004105a0b07114000030488980b03003860350f0585c10300d8040e41e0307400c0320500716111812184000000fa44110544140e84100710207482d1160354078070f0081c1d981c40003134000b43d0b6080d007041402805940f2410540d02140e07000503600d00c1d004c000f00707000880c1ea0009441060b03503540303e9101003500d4172031b603000342003681c8603646c000b520100030420341c0e04071400503002804004010030010140791307111030314014454048503c195039850f146070035001002c410500070001c0101007400611048044003414540341000240c40d0445012114100005010390001021400310301c0000c016501c140c00681c0c203409100f5205a46241480c1c400c41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 695678597 1250 695677347 695677393
    0x2031608091906031b0e0d022d040c020303060105030103060c0c170c250603050c0c01060f150305040b0f131709040b090f01050d1a01060519020705030705010c05 71
    0x40c01c2c01d0440c00c03c0111960511170303000706400741140850003100c2c8000081400c1c0140420b0b03072203448881c0b000000c0d90f035104c882c8401000c0782e601002c142407051200304081d01403084114030891070005c0c1d40406900100c02c480c401c8105a468902d0350303085603135038801412142910b03802c2080c162062800115201c00b9180884070101c00360340c6450498009a1401140340051091050000715021491490032648001d84655003000300e415a0740d5075141641c4d024015807000c00750f0032308400080119041ca2000705807005a0140781e900300d8050415015600c007a5001000040c0b2800040e0718601241182504021490380e044003d0100b0340742c0e141f01d1020a5805410341400050401c07503842d0905ca6011400c100703554841c210714010000c41c0c000c0005104141c0103892100105040165034441140317104a001d4807151035503102c0380002c201e90484208146007460742c0d0001d00f00c0701c1c00007841a080390001402040e01030700300001100c00c1000300b0801c5405105000d0000a5503000c00c407040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 695679847 1250 695678597 695678629
    0xc0206030703110a0504090b0a050f152217030a02060f151008011415071e060f1409010b0a0b090402040918020a1a0301030206130803180406150203160809 68
    0x6c3c1c0700e5003003110748011a448011011702c0f80212482c104440e40302c543c225004904100c504014002030140c8071607080c0b10f03400714403516013014410954003107141c042c04c4d001d440b5107030742c012800403102440590b81c1c443c0414800140e4407000009007454030711008243d00c6441c10003902c0d075030040c3c0070100d140320700c2d50010640861076450041c809540d0005c4686030032101114003079411120700300b61000768880c802c3c000e0407210a1440301c03e40c1e40c00364682c3c142c035103038071050800140f035821800034010a490100b0484280860020030204441401540c3c55050001d00310f400f4503242c0070b0504c0860340950700c01600300d40c00b40000141800c941c4075440451540d19000c00140e240c80c0b0420411012541140d414100144c0c0c401e00c3c0040544e0a881c10349505170707030950303803807015034030180c80c4213055444030304c8600c00040d50800d0000c0111045946050544040c07103030984811030300280f800c60000e100c0044e4400c0c490b80039400040c10090051a01507070400d890800c03500007141c88207030410458 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 695681097 1250 695679847 695679857
    0x1090e0a0603050c01021504170421120804050d030b0118090e0c1206160201060e04031701081c030b12010c0801170601210203010f0f24060c0206030703110a 69
    0x8205010040c0048000813500340b02600600c02c400301840050a005000030700030a0386d0958000c0340c500103008175000303040b8943c0074183c17641640b078030315520207004901103a142d06200040e00c021409184400d001c0c0c2d83c844041c06c4084e04014044006145160200b81000103054100102c006000180005030003001400300b181c0ea243e8141600c1c2083c07805000b8001e42554074080e001460108229801200c441000042c1880940c81240584160340007001002c188400744030415402003401c810101d112000d150301a0303607960722183c490762882500b06000807043c40310203200e480ba600591104d8802403550f880521100d00403400c459601c81d0400205440c2001402281e0f030b0400074007160505440200a40d40c10400301507080070011150303411006044103e50110740e401c0d0428101d10f640d414040100c20213003a4400042d000b0341c001c15035203040050701c036003c01c03042615a909640c0c8685aa00301c000d490741c01d0003025800202a0420550345505100c01405030070f008004605c10f03071342c803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 695682347 1250 695681097 695681099
    0x10309081909030c09140114010503010302010f27051009140f0a0b0408010905120a091a0d0f06050109060206011409040807080f0a120e10020a0908010f0c03060f0608060f01090e0a06 80
    0x541b5405001a0040d842c0780e51402c034400180d03a40402200c0c152507080c40e0500201c004d40302d0640e90010420800440720324082455000700250601c100112003003100e411404141004054a40f003065024140000c1420010001c036802c241c1ea041164240142000c041656540e02507500c0350003c0e04205142d9450301e18400070f00400300b1100480f800075203a0f040c41c020801a01810040952240c3e580190f500c03203500311016000c1c1c2c10303102035012541080c00540340d1159070304010043da0003400c3c0030481c070540100e0103030310004906059074100c00501000c0034015040249400c00144119080d1004122031800145104040c0c25804040c0500a8036a2002e0700c0280814415400343c100c20352502e250581c902d070000030510504890010010303950001c1c00c4007211404010b400c020041d6080840e00110850240d01c14416020690340400000ea2038a1402c42040c1840c464440013a184102103841440c200d04140c0f10110141040c3d60800d41d00c15003e0103032a004c640c2caa07101d90703170740d64 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 695683453 1106 695682347 695682371
    0x3320a020f030a05010f3c0510050304062a0c1407081c0305090601061202070f0602030a0c02070b12090a08030108030a0e010309081909030c09 63
    0x1d00640d43e140165151010b00803c1c420441e68004030000021071800040300d58041d000e07481c0b03c4410108600c2003850800c14024950a2044c40240e000074443d602c8403aa05c00310744054540b5900ea2070142002c1040351300d81f84401c1114440b1203141d01c5100c2030580324090324801803c0c0001003005a08202da0301b40344c01e2540c600544101c4001040342400020766808410750201d0074110740d43d4601c000c5040c1d9100b075a28100d268000001485183e000300c4081c0c0d1346a050410050801d1010384420351580b480a0040d100c0035070010500810081901a1043c0c20f03d05000030480c591500603e05400d105400741c0d0894068500c000c1a030000d0180118002590400b10481e2656102d241c4540c50f90310103410240452a6020104c150354081e0007003040842d0171403202400c01001c02e0010214078100750429003000062500840000c4082410030f01070401c00c0f10004034041c4c044 = true := by decide +kernel

theorem cover : BRFrame.Cov 695503597 695683453 := by
  have h0 := BRFrame.cov_init 695503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 695503597 ≤ n) (h2 : n < 695683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
