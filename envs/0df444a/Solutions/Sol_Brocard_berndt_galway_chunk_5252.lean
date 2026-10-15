-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5252
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:15:14.39398+00:00
-- url     : https://prove2.me/submissions/a1725537-b1ff-4196-9d12-4e274025d6c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 944424460 ≤ n < 944604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 944425710 1250 944424460 944424541
    0xd1b26091c0804050c0607080403020913020a0b09030105100b0f0a090806071d010f050d020703050d05070216060905150a030914160506040e0705250c050a0b0a0206 72
    0x9400e5100d982e4000b0318509814540e1404180001c158050303101044114080b810400035101034035411540100c1585071074a42e56000081400d029602441020700014003c440000030042820183d009010070b503211000e41036900d196105040315003004002c88241515168000c000f01461800d2009190b41c03102011803400808581e444041104849140400c401c500b14200400609180c8a0848610b0020003003550003031031000708a039034021590404240c094000c2d101c5540001200704541d1410400c001c0d5540da818814084080c0f5440c008030f8094810407540040d03a101800ba01e0104021105050180c0c1c80741034224109542d4aa01c0c0f00010184480c06261500380001000248007103810035010040302e1340b005100305000c02c010441c4000801d40c80b41d02c6a00b0307060103501d0307a4440c02503803c10808445c5049144ca1524803450400c0381d1402520182c40d42501c070003684640b126000103d5114044031400583c0c0441c00040e81700e843c0070690b000300394001d003604030080810706440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 944426960 1250 944425710 944425753
    0x4032303041a0904141303030f020706050406060e0f07080403050310050d03110606220b0f0904060507141606200d0522150506060f0d1b2609 62
    0x1042c030000c00503402c00c00e440c05015501040c50700c1050070f0040c2c03d00c407403018103803071041400a09150716045480b001000c1c543c10f55581a4101c074042c88075103094034140004081e54000c81480403c07880200f00e10000c40c80c0020300c1410603071118161038507661000e0700c1e42e810050031303a4403c036603ca0000c15691101d01c00c40c03180768882d0b118140030100320303800d40e813304d517004180354001d202d21441c9840300c1b4401039101e2001c0d0170349100014020040c05c042808043c9058600741c10040342c2040c401000819800707030b84650030554038605003c8030304c482e040d01880703030784942c0083c84400ba24400204078141e11814003d00800d40d0850700c01103158101103150040b01d40004580c0d60354040040007002c964040c0c0c00704100403005d4200121707071b0b500e442200e04030034220901d143d0746000068454a8200440d00b4540c9072a01c00c0b91038906002504003d080b00300f50025224040e40d03c41c000300c901650400303d030010412007000c814202e464030140602c4000704142c2203882b41a903030301d90800d40800728 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 944428210 1250 944426960 944426999
    0x50d120806040b01090501050d1104120302010e07181e1a03010605330d090f330b0d2a0e0705040b1804140604060b0403230304 56
    0x45118501212202034140440140036602450070036640b2103050303a00520400c15507109080981e04c131004140020000c02d800072800c0754200c00017801040720141c00303c0d01d0000c02d10a6009000880ca0a200035850f04543d1107803004055102012845940b900c1d0068413241000782c11083d403240815001d5400d44010f03104440d4083c0501c20040101c0c1030a00904020704000c1d50b5031501504030b50800140d9400500c7c5400220310003000c03c42d4485448001c9500851407400e05002d44102030406840c54a150003040320b8403168130300300205026100300410760620380c1e035044584000e094201791001d062050781e01507101a492254800080740800c240b05070004454003042c600a0389610050440c0647d0030400742c440407030007008046035010085800759080040c4d03860301c8606040071500708000129880754094180501c680d41c0701543c1900511910048a0901489540d030090003d03500c00c0c1d000c050b201040c03030b210316503401c8130841e03041da1494a042d00310303442d05686001201041418004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 944429460 1250 944428210 944428223
    0x120a05060a0209120a17160803040510140402010903030f03060308031009242112020105100603020a39080301091118090712020f0706060e0405030d0f06050d 69
    0x89480c914100241038210190b0003000800700c02240d512803558448500403044808031b00056105c0d24951408030001425038401541600e0303040610700140c89207680340742c10030300901d414001c1d904036602e40c0303c0601554060316102c40007800c584080b00c0d0624101c40c80d00525171900390000008d00c0441c021845100e00d40c2d0012901410402c8050076075420381d44017412440e03d140855040007156000d0b80455032403000d440c000320351a018450040e03100e080040c140c00d460b41ea040100c1034064200300d00c110003000300d5848150702c841054080340520b49d003450000d042203500d20b001031640c000c40e0413018980c14601903c910036489030318000c3c11401c01240c464401000400080001c0c0c0580200c40000c100c8c9242000c0701c628404d200300880b400700c54481d1502e000070916650040c088081e00003d4404190b5a8220401c140c03a202d9120100440c1d007a4078001c40010301042e0040824000c5912601461034500180e140d900501204003481c019150368480008260380c4010001341480e20850 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 944430710 1250 944429460 944429467
    0x7200d0c1e0302180a1404061407020607120b0f03010915141608151c05060117030f13052d0907020c011805090c0c0d03020c0309120a05060a02 63
    0x1000c800d4654603a02004200100e10403042c0010382d40c0c8001c407070410b131124240d22420399500c00101c01a00702c6c8084001200c03100411f00085c800c16410038a951034044464100396100c01c03004a9558008840380c1c40000d9000c0c0c00f0940c1032180b600b0500411500038524001845860b00103030849088410895050003032500043c10801303603014100700b4800c044641100d91510769007007402030f585080a02d00f0070403103030000784a41c5003d02034111040c2d0b01801d40d640642c4000c80c0000f840003206401e4034244141800080d0300240441d109030a001030401940c1840e80088408000783c100011400d80300b64850f901252644503000381c180c007a0402c507142c1c1d502009503480203240294113907800c1d0084c05a4400c000300f0603000902245403840a281c0b80341500b031031401d00075010f005130300520b50280c0c10700c0500403c4a070b410080c000c000010703400c0e1815944a0700d026000c03886a03640311041a04180280640d62a080f10502005031401041e20305820880da01d0b181007010840701014001d9012 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 944431960 1250 944430710 944430719
    0x9132a03030914030d080402061210050f04020c031b1e1c030905061b0d09060f110c06070f1106090a060e03090604120606050a0303081504050c07200d0c 67
    0x201010000c14060b007440075122060401310742c807103101d00c03a20401c0c0b0000c2d00110b403c42d2150000c9901040c00c0c20b003070150504019880070301c2d01c4881d01c520303480368541c000108035034503142c8221265110600300462408031516080140b1003802e030020710706801f48040c11000c0081d0914402840d5400102030030b01c648094440240c0710000c3e240b900200f5141540d010001000000c00d40e4000504c20701c0d8030400e498044203130069120f4803035840d41075030600000c082004504d4200d00c940c804100006d200d80c039600e9402c80a113005603002005154405004608118018150601203100c00e10340281120104036000e49001401d03140c020039684880008018003040d0b1144a50410b0030700080c5142017a10400140030780112b02684c211a541511454200f10460340035100401010741117580030b40e920304025110003400c65101d40b1050108410415502d070a20600e48540c038110310403030501c10551501c1e03081c8400d241c0114070901000c500420b0301d03a22556802d2940d031040180d03c4565007032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 944433210 1250 944431960 944431967
    0x111120906160203030a0f020f0c01151205030301030b04060f020711031203071d0a12030234030b0a2c10020406022107122c09132a0303 60
    0x8195005503540003082c10300d403e41c00f20403260007020100300400d1440b44070035458001d219106810301080800226034020020640004400c0314105e0310450100346c1d40c08154119028000004000390801c000500008203c0d012240e003003801000c0008002202a940a0490740186002e850741c0d584440f0a2101c2d03e000c010001c404038080c4122401c40c00c0c1598003600361100406019070164044240700000d40381d07154008003c0070a400e4240c643c41280c100a912014540000d44000940c603808c04610054104860500b003220401c030700050b441c649076950b1040018000c420102e80b10045900da2050084c040d5068281b03000414152102c1d04030002d01e0002d12106686615005001c1084015000300364040702c0d44e41440380a0940c1c0112201038090b02c1540c0000741101d403007058503122107a0080720551886032200350b4002d41c1c0e04e001c94404100368062072495018500f2000209494507100c000300d509442030103020468510038400c0b8074024034411000e0903200d0035002c2081456031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 944434460 1250 944433210 944433223
    0xe190b0d020a050d03020a06050703150f030816030e0306090304061106041e0312020a09030201030b040917130909050c040b120c0d0c08060a140c1602090901111209 72
    0x2100d000020460590106400c009940328561013006091a07020a260092001a0403aa031280041100f81b900c040b000d00201550584002c3c0c050088401042495010100304282ca421064403401c0000c03c1140481401c1c014000320200301c12400d2110245d1000c00680e070013035034440055038440307081010040c405144e01c3c0150b40d40740d00010a000104201e1810356443c1c40e1080c1c0d148903114400d00341507131030701c05075030282ca0460301c0028160900c5910140321821749200f43d80901449142000708010340f18070060207800b0110700101c0c00003401d480380c0242480d504a4131800e445d40c0d95001d40004031001130805940716040012118481e00e46882801100d03801254288032028191f44842e88c5c1e090f03103544607401358142030440400d10400c10f5484005100c064100c076000d10b4021400e80141040ea444100808480800b040d042d59000081d280340240700c8445045203580703170b002c00140c04400350039a07407595602c80070003083d0407543e0000c208244001001c809642041c50481d4503055 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 944435710 1250 944434460 944434481
    0x3060f030a0b04060f061404021e0403050d09090207030e1306090e0303010306050109060e150402072103110c190204060801050f1b040506030412020c030d020f060108010606050f130e19 81
    0x240b800505121147c0142c001d00c030010303070079030700140c481c500718103080f00700806260718514400c0041070010422600091001e14030380c3d65510862015500e01c01c48080e8050b05400402003440c5418012645c2806c0140c074050070327803071040801c110f5540d285100c00c40c1c9402003a0310b6290000401031091080301d01601e0f00501d0351030300800405140c108043d511103009801e442800e80e045052010301d940d607405036488182c04c8031401280544440105020501c03500802000c2400d22072070114541c4107030140e402016400018002c0d240390300003808030022080300201d038419915100440e44900c00d2150394440d00341801182c10b130f400c103d0110814924007014044c1460010481072009881b041c1c20380b600142d001d0a800300c0c200308800c0c282d00380b079081c90b074240c0c00d07218010130815180e60020322070801c482048140c0c2e8040e43c07a24822400ea03812405000302094040001403100c5906900803d003081c900c01180c40096103c00d00c2d50b0030f03054240e840c00c0d0004d84c50f050107080c4003402e1043c000c00f403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 944436960 1250 944435710 944435741
    0xa020a092021100504140105041505090114041407020a0219231c030518040908041e1e2d0e13050327030a03050f03060f030a0b0406 58
    0x440310b09040001d040d405060503055801000031031102c1c0d4609400c0f8014242c018001e00c00041c05024042c0860402d12a2900c078170f04040c0d059801315013104440080e2070b00039000c0740b2140c0c200b55680981c40c0e03100001640090f69542e03010800450f040400307004544682c09000c001c01a401048912070f8160b98058000d51000c400700400d40c9040c80c0000d90100000d000c2c404003880c000003a4850784c600300d00f0300310b8a003401c0c5414101680b00780206082c00d100b07040791007107441810a20013103030b044180c001c1948400b000b0500003604054502124800c009148244054848005801a40030001411550011080306011301d080403010050030000c1d024207581407031071004030722070801c800c0d204486440100c0404149402c0f00703c1c140b00d40c260b802004503a41d6038816240204130500400c0b1201e20380116690b4200c040c40c000c10010103103500341c0c0c0c034070341440e850108010084c2c2c4040d0031180d1000300000e24000b80d4a0038440030540c2c5006401610403450b0505040d02039a1041e0300c1000361 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 944438210 1250 944436960 944436967
    0x1f1d090d1b030c05061f140a120602040f0608062b17130303050d0b0109120b090c0d0305130504111b03130e07020c04020f19020a020a0920 61
    0x55074021811a6150501c0114400c1001a03007403d880901000a0280460007100100004421456003860340400f2003090750100f5603446101c4a400c01c40704803a41e5210b03541400c100501c1040c295102e070028082c080052030641d0769280c0070851800760703201c8404580c5c40f20030803140b803a12000c140e00d0b140c40c68040d1040c94511560b010b200c4240250b000b0106d10442c011110603000f280c05441e0106504041c2c038404c17a840e403c000d8020f8021214020102e400c20840001c2c03540704412140448070aa07218285030020340c1d6817550340e8031005023410790920603050030a00d1a070b50072070800b043c1402078890f903660f19040b01c0c584012610790303002540540c0c1424144500158401c00702d55070503103012550001003d040340d40f1410f500c59940e0313100b00054403000c081840000c205074070380958019002c4591840358441840b06074043c403640714205c0380081c002400122048000c0d500c1032031442c0706981c4140d44643c00244080e5494210102c0c85a45003600104030306200c10112084001101c0d881c01c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 944439460 1250 944438210 944438233
    0x702060f0103121206080a0507080d050f160501050f0609072102070311010603110a09150b0c0c180916050307061808010c030b010801090e0709051f1d09 67
    0x10003403018400142011550031401d00002c3c420510030f1408640d6140c03d109040d902e04070302d5944c19503400107980350301a40d84002805900090103080300011030310741c1c50501c10030110700c02260300070348021451002029080c100146003841114810b560500801c460340c104131050050001c0010400c0041c043d540c044490581640303029400c1641c000d80015a84006a207422180107260140000350f660811a000c01000503144102c0d8491405075050343c1c00a640700b00404c10760343c02407185d425901d00c122381032101c0c00418005001c00c028020446070340003501d4000c540c072030340201a0b0995880400c41448404101440705004106c001031600301c1c41810304000035101e8440740b10341010b001e00c2d0b50f003609140d80b04840c600002c0c01c0090003040044a81800900078251600c0c0d942c0c000340c002d00c00820001b41c00c0c442c00360001440c00080200380d08000480b40144005031072401503185511111551010110000001d011038207a2145101484091500304d0100540079400c40d4112a40250 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 944440710 1250 944439460 944439481
    0x515030d0206040809030f06090601030210080c030a091a0709030b01090b0105030604020c0f15010807091802010e010201020d022d09030a0f08070c0e091b011d13061706070206 77
    0x240c00a8001c003044d03036142ca9000009151000c94506240c143c040d0208001d180b501c0481c049041345e0007560b1209010300402c42c100c5507068200d0701c501404406101203829140242e00184180b071003024000907030001d404035030380010300c1101c0800008415010610400500400da0350051051500c20710a501444002070718500000386a907014076404154200602010065010000750140a1380d0840d10310356414000c0302000d00544c2c4452294850000300d000907840f0b040b0003805501005598a00280d00444108460744200c50443d90203104000300c2c00403d100a00c079046000b0101d2001c10451103d941c0b2b034183c503400c544075a801c144070045003078901250010b841544011890114500c0c3e1400d0b032400e001300840504001407a2901245128034500da982c02441b001c0c0440d10301560078004a009030986400c040d000441070f0002005100d06504004010a0001c105240703566521050700100d0300c0700c0d0301200e0084501405001c4c0c14000b0703c021030700b021091010741840d18003111403c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 944441960 1250 944440710 944440723
    0x15050d03030f090b090327010f030c020c06040603090302010e0a082a06150306090a12030c0e18040218061e010c02040e0607020c0d0c0b030711030406030515030d02 72
    0x1605050b1074005040d020403103a40660300803580020340a0890600c250036a135282c020044292100008040c0d8400320040c00744c0c10025440b050b594031540744194903040b8060304004000310250301c42d62280f9036881e40c0302d07000782c000b130985658009000031035414001d00f5a1440f03005000c094000040c1c4001080d80f20046035441c407008041240a038051102600c41d881c030182c49032501c0c0c02403109000c2c4804030156605117514040b400c8842c80e80356901ca42d6111403030800000d2080d03840071004090386000c0d8200341500036182c24825401ea040d04007281480d5160340014280c109107004101c218601000030070755907448811a40003501d41070001c82c1c500940094990064054030101c44c1850703100c0d4000020781507000e8400e0160120740d2442507a102d0040d0b590038098020f10401807450b003400c402c0081c0c5d03981c20103140d014462602201401c01d42c0068852420400b48800000e450101000240002c04584d41d00044624100040351040b08200083e5032183c1c2041511250495000540 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 944443210 1250 944441960 944441963
    0xd051501032003061017130c050102030a0e040b0a030507090c1404210f23060108151825060305060103060302010509011419020618070e1815091015050d 67
    0x20400944040b4006550116040c0c6e820000113605108000703001d0428401c81c0e43c1135100c0c030820038245480e07600580c2c507800307940202c80000304010342502c04c510706600031090002c409000150015280d455a0f82020025001055100d807220300d0080000d034445520507a00b45050f14490a0178104400d0030f140380c400c020781203084200301c014041804440d11201103141d40c4840800400007120f40d242a94490300341110101f03014181c00003c0345140070503441500300c0c1010282c0708a035990300144030400307000c0c641800d191080f22082c242c2120714051066075145c038442044203407031401500400340c40d0000c0030701c1d04260400380c0070030041c0d803c2030070380300358030002d0810000441c080c0180110a01501c4c1d03140016540f01ca800800894002c10103034001c0c010700c2500c8030f10107011100c0356034030a65442003010700070b036039030001c4d05282803041304403a011750000075509146403141c03103201c401d10242c07800500c0350400c1e05050045041480342e0908611210a00c0f41400e113803000046241010850 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 944444460 1250 944443210 944443219
    0x1050907050304150204090207030e0a0605030c04050d0c0312021b01021c03050901110d060501020c0a030f140a06020a17091b10050f1219020906040b09060d05150103200306 76
    0xd48104040d500c5d010348002e840541c508648450319402d00a22901408424901807004c013070307000c2500b034030510890348511505900d4610702480c00d07060180d04100b810b016103044a280c0720200000304114020703c1303165401d41c0207003c20000180c11901800c024440503066502104008030400703503c04017a4040007003420001865038a4281903409001e521225403c00000011448001c1c0c100e98010010390b0000c0c0c0c00c4411402040b800d10003482801d0101400811b141d107042c81c0090220700002503400b5108056800244080d91520f003070360402e4100030b01080300f840398020f04006d0184410b902c449000c0003410580e40d03140e210350f072402d030344500c0d04d0189032840d013811122070041040f01c05a6000c2d003450382d40c83c002c0c0c00341d5000110040d1040c8000180503106040034071924001d58813101001044603240614003414641c040d8000010036410082c103001181c92144907101e194420588802c41d401204036002c0010121040d4400745d50042184120080c003560114082c1c2c0e5001d2401c0d03c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 944445710 1250 944444460 944444483
    0x50103030e04091e0b07030606080408090d081e07020f010f2c090901050702120703020c0d06140a0609050c0403030903021519021b010503090c010e1c030302090901050907050304 78
    0x10316100a01101c01021340003e03007400b0200800c000c010120317101b491241d90400c189501c0740801c590450703041c0c4000c1c000306002d0007103021038a03181b0704039121980710b551450b1400305a516245103001c86085820105003001c08c0305020350502c03c80c481c040c110300b4a0f10315003000c1e03c1a4003a19032020000c3c15640075050a1300c0c403898100040c0b1030400550010004942c0e0b01d4442c040c80e018003800c4075904014020b250380c6030030340c0005030141c4e1710b03155041c0c01804a10b01800d0601240032488501a00c1440d21000b00d80501072034001d566000c3c201b000008540c41e4100002501503a01c06014039501e0f850800040010030391018035042540d40c115000c2c2aa02598103403a1924026040490351034652003001d005415000034015210389514032080500305491401550140000c4544e00c400e0307040010304d903690798460400016181c1000700104010b0001e404901d05044884000700c0119500003001600392600c01402401004100c5045540b8617018600030028000544010030640b03021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 944446960 1250 944445710 944445713
    0x902040608390306120604170c0703060905010203060102070e01120213020f041203180b12070c061104050901080712020d0501021210030b180c0d060b030d050715050103030e0409 78
    0x180c0c2d4050325800c02000711040d201c01200b90701900d500c26981036224010110040c400000042006845107801c1910604071003100b0440b070800e5070107140c5000050003889030100c0007899500c6041e52190040b800142c507440c0030307000a0701d4142190030908203006800e00410030740759100000d0740c550354169094007400180305d4200c1e001e030148008183d00003e002c01d01058203062030103402034250107680c80c00d14030440c000c600361030002c203805100d40c42c00d400c00210061010314113689402c00e032180b620b00c41402041d1641d0f000c549048900c05800c0c0740c006000c004610309000010701400ca41e070050442c103468088005035541c8641e00003806075054000b40302c1846400c0d81a2004489612610326003440c1c002c0d20800030b13483c1e40c00b080710b81c444241c020600c894a159648806942c2900090030f0180420040010082000f00104ca05984801c0403001680b0180105440640030b42c8a60313441d042d0914110043c40d0300b10084d454a5441c00c0b0040020036031042200304920390644000400f020035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 944448210 1250 944446960 944447011
    0x619020a05070c1d281802040f0b040c050f040e040c0806040605010614031006210614031c08190920100903020904080318060907080105010902040608 66
    0x58980c0546260102400000c00309540100900755180d0f0302e00d565266a103551403405905000040404031140802a0001100c0c06601c900e00303082c00d030346c1c1850b180c91882c2e0024040d0750604040c001c180b40c44030040541c0307040500890f4401c2c481d82c10308504010380007140c20440d00851250703059400c06070b40482d0a100030401c41001410300d4400b03031039a520302410054040c00d400e10410000480e40da1000c1d2201c0c46400969020300702e603561342000c2c1d42c0b804d1000c580c1c4884108035020304200c0701107404060384040c8640c000030080040032242c14336000007054144040080810203520240008200180e0701580580e4450304904007011040042c889050007480000c400400c4034290303030529124030b060f9111190400300200c888451207070303c0e64422103822006100007500b10b10417a0124001030824005140d0003014181a100507142000080b803034079a06480100098124440510034000c007801748a0240c00c841c081507180c0f51524a00070f104010040c8042a4a076031071544d011070802 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 944449460 1250 944448210 944448217
    0xc1b14032a060415030509101b030f0219210212011a120a0f0615050d090204090f0c08010c0503070e060a030923060a0c0e06130f030b01080d020619020a05 68
    0x111881e00d030108004e988040e00601c0c064518100f00e01c125680c1c4105213205000381a540c82403480c407103d0303101c140c41003034028100c1108887c610603001c0c003081541504802406440514030384d268011040900180c041c040c40540ca406030310703801040071108410b444000c4a04441003542200007410650074506002e01810b1024a07049480e081449105461508000b0081140a908001d000c0c0da40c1d11541d04214004004000b2510a00110041012a0340613000542c00a1710118510340680e8402d06e0710541082e00311101000c010050010003002d00c204c0d0f03c4549a0b080480c80d508002401810111402c108a8489c032400540c00003035600c240c0080c0b4006070300680d075610440c24244585209165689009414820318002a224001c68020304420f0105c0351141e012010f032480c1801503076031006900c80f44040350002c00042504119400400942c00750004684075418008804e0408002a101804650000060100714003c18034408418480c6041c0140d9455543c9403d075203600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 944450710 1250 944449460 944449469
    0x108100b0a051810021009111201060e09010606090e06010c0b09031c0504020d0204050c040f031101030c0804020a0b0c0c0901180605011416030c1b14032a0604 70
    0x80100e44680700640140c0a820701c800f0341c00c072a0389140144014844021550070b03c1c1c00041c1d0100c020980c1d8100103600840f402401000c03050761000d82e200c00714503d040c180c030b00400160b40d02c8170100110300484140c550000d082e070000b40110380c609000203200322520701544441861600106029038000c05007011400d6000030149107503c1c110034000d0712900025030780102403080b9180e10803031016034031607240302e581d00074641b541e80354080e003d00000788001010004855020000440c80a1156080c58001c40c814400111503807024000101900e04030840386c802e100d4401c00340001680c80d100140180c1e0710107803c40f030f00c41c0703412800e203031074002c0301844942c01c5506180045440c00b107022201c042e2082c0050184080c83e9604011500d080352640500b800090500c00c6480308409244c181807018081d1a00074a04038140d00d44026111110340b040d070303030a5041201003044c1908a50840038007038040340901400d00c603050801740c408182c403a00c00591000b2425401304c541d1480c082c0e0340a0b2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 944451960 1250 944450710 944450729
    0x12070e061f08010302031c1209020d0f0c050a0e01030809010f02010f090c080105010b0310061b060606030b030d02030c030703030e120c1005010f0302060a050306011218020a081b010810 81
    0x19541070160400600380010f80c003d00441c075407440021450b01c100e280200003075840012403800c40c000000140000303101281d01500d0b604410011035403c1948020450084221031405485e100c104082c2c01080d502900401c1104d50040012800040a07555124401c0c00c4c896542c145113242240100700c1404107021642c5001c4004042c044004c0400301901d0a860080141d45d0301c6a40200c41c0340001c072130403040c0300f15148040c40361b6441660300e288075441485080e0740b50700460381e6600964101c5d40090001940e030350f401ca4440d150400081416101c80c2c0051031620148014a9441c0d11035000080c1c140f44e111941014204401c001190480d82e0610149440d075080214980c0c942c4448014951100c0c2800008200902c4001401342201d500605885c5400c844c00001d0f20603800003401d00f8144026116000d0a0301d07000e001c0d04600c2c03907803400e40781c1d0b06031418810080212441c0d0070805c1030f1303403101c000714004c0341c2d48107440f140d00c840074206540d540c0e0700c070405079076070011641181d2200d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 944453210 1250 944451960 944452009
    0x40c0c05060a1e050f0402120102070510020a02010b0f090601030b1c050303040212070b0304030309110909011b03050c1204300305070513090e030f120108070512070e06 74
    0x120515407200d115280f0402c0502a821084807221080c1d40c8280d40901d101000c3e0004940149449008110801480c40c00941071034641d485150916104c0ca05046040b600012040700483c0d085c07060300300c20741e030440c0c541c51001e05190200f03ca0f000002c0020741416551041e5179681e9540c49140d205291326a00c04082c902000e1425030348940003a541240209408141e41c513a031038000c1520f000351005408807a0840e501ca0302e0480c041d141800082e1001c241c51407007450340f40c07940c4003020701c10700700c000002c074049406d45510f8198001108050302011b00d42028001c1c1e0300502d1085407241c1581c992415515100ca080c240007401785d40040000f17001d003480c607001c0c4142002108908005590300c003040300365100d00098500c1d1007101c0501c5000d6103805801d22441c1d205620000c2c0085900c41101c0c100381456043c18001d503c00c07455410400014801007180d200204001d030094042611480030000300b0700c91181d6285500e000d2100182d40543c005409070721640310f860303948881c2c17810300402c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 944454460 1250 944453210 944453221
    0x15060c072c010306090b0105030f0303060d0206090d0302210c120d060e0103060b03102c010e0f0307050f010c020a060f11280810170309030304180b010914040c0c0506 73
    0x3400011421a01b001ea01c0300001490315001c03c2020342ca0040c0d03000b0b07620355620701040295040d0060030072648500c060100850944139800001900b600c660010314812020b84000001d8000c95005c0d18140f040401001d290b4080202e10400c903034038003004517601c0340c0f030900b01039002d4051030304002c1d80300d0300c0c0e00e0000061082d1900711140d01c50081d029118014070311210720007a9a0341d0200c080b40740e440640001c801124030406e40da881d04803840000380300e024200c032040c200351480300920030b560302c040340c07074014010180291900301181c180200301841148001a44500d0a020301a01007035503218001651081c9401011140d1402c00c4d04c1ca0b03039500070011141c04001d02c84d404a102a0202d000c120005000d000d225029400400d50701c01034516244080c80c450003118110007a9010602c04000146c9041000d840500310100c002030070f6000d445111000c0310601070009040060440e420040316111121482071040706450206040c00907006c2903981e095a440018694851501000b2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 944455710 1250 944454460 944454473
    0x4080706110307121a12012a1d0109230307271e0902010c080f09150f030a2c03031b030105060d020319050a0515060c072c0103 56
    0x14443ea8458448032184024030000304111008103903246040c0c0c5c600904c003811440e01070030074071103420f0310f20011400345000d14190056448841130201c0342d184c1c942c03064401c0342d00002d0784080030511044081c2030348544030000344152200c1c800c01200c0d03501a1809003100402d03e1900181030320280032034210580e144146210304400d14440e40342344443c4c0c0c2484002c0700a078001d0b0020394805003d00d11400d0b03112840c1600404084000303e0500044114150020f0708178409005490501c0000e5511240301c8800d00480042011062065410420044204a8104080d01e400c16402c0600050400b640d101e12010300c42c40411341c203400880c0c0f50800717522490020003940324607070701c5e400200007003007c003040f10040c0001e0040990100060000d552103418981c00385601190405440070000000b07c402e004076001910b1985215881c2c0040184500030450f920404100558009181c840e60004881d121095030080b9140100b032055103004030b202e01e04040c041400c0940c041030b00d959403458000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 944456960 1250 944455710 944455717
    0x30c0106030507060801080d0f0311070c0e181903050d0e0610060f0e18070311070821090a0b04050f030d0b030708010b010f050d0627050906060a06080408070611 71
    0x1000050b101c1e41c00032a080b00c0200e84c001d00c110380740d2984003505000a09c280e000d80441c02c1503040c03482081c00314001080d0a45590300041c04c00c42488078240c18044400b0000740c2c9a500180f140c1e500c569080002111102d04200880390145003040c0c4440d210402c4102800320b40c9200410303841040305001920b8400303000d40c800c451861316404461318085106032003100402c2c0c00b15511210480100d414044255007580e800041da00e80019202494011030301700d60405e50003a07401c5500440c50380c01046178040410135810642594108902c4c080010568a2408000c01041c681402c3c0c081403c2050030000f1007900130744c1005480c3c41d6000c150803040240101d2810501c248100d913000948003106100701088007006a603640b45680e003241c02925290300400d03c2e010303001d0380d40900040200500320030843d4401b20b60700d048001403070007900c1025200043c2850380300342c002009004940d541c00240200b29849410300040390764845c00c04030180d001e085009011141400c050f5400442140d004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 944458210 1250 944456960 944456969
    0x1115120601081f0317190908150402130e070e0a0207061404020607170f0a0509101706010c03180e0f0c03010b120c090307080d0e040506060301090509030c0106030507 73
    0x190b2420780da440d200031424094000070100c03643c148240c28004500007000031090b600703502c2000c42c83c1280302440d81c295454201641c000041c0d240c40e0602c4481c0e4140300c5d410f40c40c6103202000e0000c0c2481d40024a11054240d91403d0a41d42c4400c0100462000d2000c03900928048140c40350b2440c100c680324010f544584021101685083c00c0ca002c0b10090940d040c4c0030f95000f40c201d500f0040c032581d9915400c1d0008410b408031140c14030402e01ca0340746180c020721079180720b5a600d5413615404404e10204015403420b51060025142c01c8810464060342c1d01607014400340790442e2021903908017903466440d091042c001e40582070300086200c1c0142c0d05c806000319004007031b041d01566440c4400d290760000703000c4c61800600c100480134400c41c506021940144412100074038061504000924140c0c41e980b02e04102d80101c081d94506940260700c10000c404c058500344510b01d006000590648814090007511315500c0c40030404e17841040040d580000d8401000b0081c1c641c4a04005a440029108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 944459460 1250 944458210 944458217
    0xa021209040b31050910050402360c212707030c05032a21010506040b03010204030209010302131121060406031a0c0c19050f0106060c1115120601 64
    0x74075045005100d12031081d40301748064054001510624405004090010b03640801003801c1136400d0001c0e00303985410144004625002d0020000000c0c4202303500900c25600310701c0a00c45458041c241a092155203201000d21403007941e6000c401071030042c10050003500c080c98030503204026200018004044d24001c202c1d83c00e0300e0f0b41e04d0301050396500e5984540006407030b225800010f05650280b1f61101d0300f00c028402e05400340c1003a0b104410b84000303801c80321540e456009000640c103191181e942c241c0f40590083d45003504580210700c070301c141884024012444210601c2d84140c26610100102040d2b9444030f584015050160448a0f030b101d1070070021542580109005140502c51001103a51002120412191080030100480380041084403441010008400f14407401d02144d240010008000191120079041c6039141c81440700d4801220ba143c4841030150035000034030346881c1039114a0600720301150700301054001200d0459491a00310208400c1300e102000e00d407075817240c0170a80c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 944460710 1250 944459460 944459539
    0x921020f0c04021e070312050915010e06010f050d09140304030b060103020301030b041e0501020a03141f12150507031409011509180c0f03170a021209040b 68
    0x1400c0004911440000b60300c001e00762180d1111049410001c0d00c800d40c007d08202148a19011980c0c0a9400444e1560403d80118081e0b1101880300e0866038090308121040d2415858580c0019100c6c06800d0b1103641402004030304480d8400030b40e00654407043d8051071452015201a0f20710342e03a0307000341c00100e440040c1e81e80020440c4d4840c2c0700f075a04880d0082c005841940ba5503c0d0700380c54a28540d000c0140e800d569502c41c000c6030007400104218080d41ea400501808400440884890b01920550032040102541d4200c65103070b040400907525007101d07400889006141c04451758102040d000d4099040404001c0d032585c050340141941945018650055996034031282d0881d03800b001301c0b0030b044034854000d00044405601500d640000c1607540c80c00303072030551075034110101217a0040e0702041e00d450061041140e00340032010481c40ea0480542005154a8042c0d11001a43d240300001900460402000d54451700078454000000e070180f00703000150072100c2007450a40105600c03101248 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 944461960 1250 944460710 944460733
    0x7030206070c0c03150b19090b0409260d0903080f01330302090901230d032304090c110f120315030a0507060807080105010e010c060921020f 62
    0x20701625071060762040c0201c60044c215500c050f0252005034040c6a201c0c0d44140c10311298440c0180c2d05108810340ca2070251551610300c20700203541c41065910701079400d1400320f00000d0303030303c0c0c40c0c0300304c2c101001e12118420042104c8401c0c00d80915608001d0795401e11040314140754018002c207008030701061030301c0340d6aa01c4030181400007814095a200c2c000d507008101d0803105588104004030440b6150240c0740581402c00148808400e030001030030700b811420710bc40b49040405070420000400d807022049080313a40c8000d40342095880d01504401103c4200301039000b000c40c202c038040c012002041209202c580c41c020040c0d40b000018444610030200c215034030f0080024181d00503c403018203e807a40c1d490085070321540e401804180e800d84a42010900028020320000c1d010b0162540c2d408c0c2e00b85001c1034003c2c8000c5042e4840350610104c0181c81660703980c000e0b00c01080740d030040310124945800d4a49100030b0503c013030100c3d000c040d48009203a61540d0100e0954070f0300b40c00a04558041c28903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 944463210 1250 944461960 944461967
    0x3070509060a0302090907051218010b1e100c1502030c09100f091a0406120b0301050103050d0e1c0609050f19020112060509130807021e10081501181206020703020607 73
    0x700010680741c1c01080000a01c2010ac000351600342030940c0b0000300b030b803024000c08110b86040b50001d8008d150250300c004449030800080d0b1001c2803d01d80340580c440009501c0b0004407442e65840801003030303000000140032801c44011a090540c024000c0d51880b8009200202015480c16406002034920703000055481070f1555404480c00c0350b4003400e840d05242480130b403403d18109110507042a190030b5810465a0700703100b41d600a5000d02d01038090003043c030b58001e0100d11140301252186c1224118200d146911041100c01198000c40c00182504107080642c5404000c4510f1100c80c4110034a56095011042d02420124400c0c1c803188400d50008000b201607403410301400341c0258100000801a5000c0c030800f0781c41500403032945d41307040c0e0740c2c1d008640d03100090204040c0e0345492140c282424100380d810030312070f40c0b030b580340c00300140c2408095042c1e04a02e00001c141084200f11a52070740481e18000b440c02070100c0c2d041d5840010035444d110010350401c01090b4058003c40c0000b4030507502 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 944464460 1250 944463210 944463217
    0x9120f03190c02030301290f0405010906050a09050607081611040c030501080c010c14070b041409040c09150e013003022a030f0a050d1b0803070509060a030209090705 73
    0x5081d000345045da0700303007d01c4a1a2680f030402ca401104146485822210741640050210621100c0101c1d61242400000b42901e0b055500610400104002200b20b0551101400d0141d540407610284d5500c2c2d00d0525500601a500c0c0c0002c0d8400560106002c000b213180400d01c402e40295014452138011790004c0e021114244503c0c54190000c00403080150f20405215412510505100103508100c0007110f103070038440d070080e020a0400007020311282e10114080c0303413016421180e43c0800d203403a45d030342029420980b044051030790311029050164000c1140f8080030f4801301c01e201c030080d80e40340d0900e0024800e901d40855001400901450000b0410301020006034068000300001101205c884d2581441710301240c845007642a01c03c58140d8052000c00341410115000b00300082c080e040c40c90522078880a48400d21841505001313144481d4100070302ca0035001540b0944070b039924142604d940c800c50a03c25804900059440320503501640036280c3c00ca4240e0701702c42c0c5941c464009403481e12 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 944465710 1250 944464460 944464481
    0x5031f06050a03050a021c0c030c0311060408030922180b010819140316030806120606011b0c1208040e130305120901060312030c1404150809120f0319 66
    0x304a000f009000d03040862289607503407c8046400303164442503c82d41e0b4594400e410031554075440d04001c005206051001c425580800c0700c0d079900e0645000600c45c3e40c4e01c00d01c80300034020010271007180c2e080700c045040007640984150303040c00400344003508204004840c2c641241c20a100e48004101e1100c00101c2c0f9000140c020401810100039440c1c03808044420701c00c1e030020344410031a00801c04024440300010b54466140e15402d07040c000e04000300d40c41c010b5000d008540c000001c02c05140c0e846240d600c400781001e141100c40071043d08250389548041e0304007813900034551501e8003c0004490041c03085806a1903000031a4588a4094440c451605000b0380051828031401c22000c42d10f000c21604080031000000700e0549d29078072504410200903818001c250b48014650302c494000c1c0c040d8150351a110b20391840c19090005820804252100e201c7c10001504001640e5510400c42803002e080100e540c20f0b00d41d4030074580c81503154021610700c4011140c0611203256000070340039084115 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 944466960 1250 944465710 944465713
    0x1b10120f0b0a08010e031c0b1f02062512060305030a0c03020d030b0109060302160209040320190609230109060b0102030a0806060d090f15051e010b0f0405031f06050a0305 75
    0x19045040010b500103054904200d661042502041c1d603c05009c1c0f4646000301040109584a81001038142607008140d0b101c0d01c85490444035048003161480040001281028280041c40c0301c1d05800070172030b503080186144000030300360f000c8079000a5030011080c0300341d08913408910340400480603291001440c0d8046440f006e028000e00340681c02a080c9000344e4058142c0c01000b50f00000d002400a0300d081d0082494003114040c1445903254241600c05070600401600c034101e411003110441400000d0a00c0f541d030300040c1c0802050000d40440c17441c540011440704002d1016050003040340c0c18086681074504891038032170b0350020040c0e80d8214520f0300c1e044825a2000c0510915a2114030104211580c81a0000001d248100502d07000c9024042882ca840120080041100e05c040d220001342914250008900e0080c941c1050540e00394008281d1242c2c0c2c20701e0408404d01441e0480c4c1d0f40f50090000b082c122942d900080545001204014450b041e41c1c0c0c01806a940300038000034125 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 944468210 1250 944466960 944466967
    0x10503061e130303090602070b180f0712030c0f0b0105040c0f200309043b0618241605090a0306150915090e1b10120f0b0a08010e03 58
    0x4149282c21500006000341004030700c04546903650b000302e80c04400101c0755020039905104019407a00031556030b100f6800d009009101c44050003a5880c1800c0c41030b02c0e001e8400012400425100b600540d008a50001d0200c10613542c0d440c2020b20100240603140c091b514001200084600c0b44a1510b20340103103441e2004003a2180d038000400980d0075003034940d0f501c810024081c55480300c0c41a090341ca503031581c05070400300186c076200700a031541140c10111002c1030781c0000300122010900c2c6070405003c080512103000610450342c20402c110040d44480d825040ea2200000140d003800c0340710300c00e032086400c03852801c19410360305801107001080c1c01c011060f03400d2002918a91006240c00c05030800701000d207555a030100250b500090018900914009040200e91400d0003035880d844141030107004000b42615080700c0030240490303550310540050500800d05801880860346800c40c0c41414006103030901201809010440c4143c2d020780002c070000904014188910982c250100000e90b14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 944469460 1250 944468210 944468221
    0xe031602060d110a0207090e0d09060810031a180105040506192703140a0507111c080306010f0e030a0305031909061b030515101115010503061e 63
    0xc103030800624101002d40c3c03251a004803c1c0c02c58060b001c01c1c411940206031681c00d0100040660320b0500a09540e5401200c0b149001900320f84204282d40080c586059103039204d80801e15000c074141d00c054a0000e051049013a23440c0c244401510480340410106140485801058226401140d01a01d540c001d540403130b100c03038901810302c82050700110b0040340d10768444501e0b040001030254a051503582c0034141008258002c1c0100e007160700c2c5045081c0c1000c0c2c1008003d001c5103d81c080003000903603000041d0307406545405441c0b0801e403910b2000000142d880c40d00400d50b600984451b400302d000890b54183c107904c01d52404080b014003401900d00000c00740d50650312a00003400740c01c9400707081c2c81c0200c0c46205903c580900180552000710314040e101c54614400c1c484081e40000301360400e005c011072215035070030345100c911081c1e903c0d5851000956044500501c40320004110380604901c030b2160048a59041e41601d00450035100c2c0f9442d664442c400b9001010090607413400040c0c00100d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 944470710 1250 944469460 944469469
    0xc0c0506032403010b090c0c07060206010b031f08010c270b160609020d0507090c0507020f0111160909110f03070e040201120f021210080a020919020c0609010e031602 73
    0x802c101c0c0140002c100c40400c04001000d00c1e904803601c25414a0100309a0341101c010800c183c0240b0741400070342036650604420340c06078403008183c0d41d00c041d040d00b1040d4142809041020083ca240d000820288100d400d00410102005000c4285491415a1400749284540c803c10440d248440f449150200e0440f84442d48041d07000141c903415501d02c161405611000c040002142c031503000382071300c5410414040c0c1100c41c00e000400c108041846400c00503115151400090b0b0b000342004952b0103000c0b40070a1800706070039640d00080c0030880001451140310740100a40621519182c00550881400e11607010181c0042503419032014100b0811a24501d8540350418010f16001401389402c00602d4280d455083c101c000095001542905100c04400c001d904940c00300400380055113041066541e807100785101a201e6407140c0c0104280b00d48e80130007001002100202035464000b0820384a44a48088030511115401c0000200700040c01004880c41c0c5800d50000e41c207146925000c0c0b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 944471960 1250 944470710 944470771
    0x12022b120b040906020a08240a03080705120c0f060f060d0f0305040b030708011502060f011802070c03030507020a060e0603150f0a0806060a1d0a090302100c0c0c050603 74
    0x980c01030303035800020001c105540020702620b5500d898115090801511344545c65000e82c8c0400c0c41c0b031514012040e4150f8840740b07a503003200d41115296485210508000382080400c1c000320145840c002401d29030004081341c19021614488161440c42c0c0d00e00c42400001b541c112081c5502210081039040000c69620600b00e03d980030b864540e00b0301c0e84402d25024617a105484d40310124030031400400141e15041d070840e101207400c0c80905880d041c070340d03500d01c6407a8060088112482c1c40c11642c41c1200700700c0c3e040e01c0000d07801c560b2249549642e03080180040c0d00c13540d01640105481580410051b0044204120b5402c025003e540f640e920018417051502900c00b82942c448449042c00406944240e0003101900500000e052541003400c10002040e40940c4503440115100e5610b40d401420a00b0103644101c0b0000302151031016490121b05002c070000b104030941f45803c0002042c20b90005001c4209845613404a420326140d50811085020031262540e6441c0b070620342c900100502c1040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 944473210 1250 944471960 944471981
    0x17010c0509310218090c16021c02030304030c03060b030d0905090606040e09010b040c02010c08180a02060307050a0305060a4e05100b210a12022b12 65
    0x100d04004003040e450030591340001c0042d40da20fa40404410858540860011781150510240d40c1c904118100d04078090303002e00320040d20480c038810380e0000760b9402c01d004200f40369004081d29602c075100d107000c1f8102d03882804152070041c80c1141d45900e905000410f40c40c583d240c0d48a04035002e107014104000f04000410058003c00240400a0840300c25800340d070040d00c1c420008102d5180031410700c8100c4118014031002c5a0500d55811071003500036000030340184119000507800c485c4902910318154a2200003034000340000704000c0401e9000005d01000042503505010f80c1c2c48000400c84088858040c080c0c5048000985003c1c050049015014510305402000c8a80307202c128609411820f00702d950405102000000c13040003000c0c4500500f15804034820071800e8000b401145c150700ca15002070004004003890b00800c50001c10681680a6101096903640c1d20f0f040c0c0300945070000d111120141801440e591400c81ca58070050003604404cc0c1e55036014a140c4da0004400340c0f803140348 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 944474460 1250 944473210 944473279
    0x80a0501151d18070f17010c0905010e0f030109020904030f0e0105070210030f0e120409061712030c071e021c0302100b010504050603040803070908010e070521060117010c0509 77
    0x140002c0c007290340340088000340130008100031b1800f840280d80b802d41d0501c05819003082841c05042c000d980c2c01c0311b00400f00010580d002c01c0011101c0c03001ca4010b00c0e84074006584240120204410950b01c04865001070402d540c6518100c00d0b502e0040d41c40340a0007200a5110700318071142c0c1030846c07296000000021078a4808584060350841e21030070a007508501c2c55001d8000071f0148a592024010a001044001e0303890071000036503035100d07480790911605425076040010105a181c0043c1003590740640d0018082d503000c0e40c2c0008010703407105488100724010040c0001d070003024010090401c0b00d698240d000b4060341104044040300906c0d2100c0c20b81d040c0081840081490746442016603c15032103268000e5903810411b1016004d2580d030341c0f101d0100c0e030400000c080411404583d810445800f0340e5034404003a103040c95480085003035001d41c4c11500c22040002071811038841410003400d4100020420030b0520304040b02c0714441d0242d40c94008021134030300b50100ba42000f40e40b90a150201c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 944475710 1250 944474460 944474473
    0x230705030c09190608150d0809041e020d1b02060709032405011403160f15030e030c0c1306060215101a0306040605011d041104080a0501151d18 63
    0x45294a54409a000900082c0c050810491155444018a030b40c440702213407d50102003155a0315210b5210302ea0034940140c3d00c51b0b13807039400d0206c071500840c035510700890155100e580c0301c021300000f0020b41c182003030040c8060b80090715050000c18458000d001e2070f030b51880001d0444d100c1c030b0003550344100f8003030080500d0307241600001502d2044134007902079901c110600700c80c103804044ca80512040d20203480280311000300404001680d10b0002c4807603071443c1c4203070f00800c1e0714194000c0c402030b50824201d0200040d480ea40502c0810038450000c81100c03007441640103180601c1c2200c2c640d004010140e8000c080c204001001c622069901c9000302120b13950054072140c2c41c403090900d42c2c0c00380303070102c201000340b040c00e19080c02014040c1400380f9080c4540310030400112501c8600d54030490040b5511152a20740c40310b5001280e0145c00381c44201c600c45006031801500910070074000c0b036100c0d226507001149544010084011a10303210301c0d80c442c161030310107039096503070a0102100900d11405 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 944476960 1250 944475710 944475739
    0xf0311070807171b03041505190e0103020f040e2a040311040b18011a0a0e0103020a3b040501080601032004110c011d060c13030b0a230705030c09 64
    0xa90b00e1044c400c0040c4d0165440360328100103151002c0ea039034800e1003404010310440803491400404844040c40c1da180c00407000c01030341c006070005d2295840ba0540014009004100d07490401c25460042c07c01c514050400c0191110340024500c0541126904074400c100403c0414881088041c07600c900400010389940c1c0c4800082c001c00f80311000f41c42c0304400c100100071442c010381e1410300302c0311607580807483c103825103c00414042c6030100e114145640071440c0344015128034024155411002240100d1030040c21004d0040f5400c21450601580c5210800390305041c02e00861f0b0403101c2c074500a181907403c5542e82544200c250300100300541c40200020500e6503940201345490180140d503030350b20038220111034252408241d440b0b82a01c07086420310034012000480c83c2d440200124055181e0141346112040030302030b507102824950444c41480b01d07541240e4003500154401000941c0b009840944550580034100d4180000c200240300240048030240d0042c9480d130001400c1c840c0310a101e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 944478210 1250 944476960 944476987
    0xd110d060b181b0322031e030e0f0a050615130c050d0f0911060d0f1d0106050a0b0301140a050603040f112223070f031107080717 57
    0x74218100c4100e01d1a5040c485911026042d00c2484402d00200c1444c51424000d0300c40210710a680800c14030031018074180c107040c03241d444d240941e0008448611486500c280080141c80d103004210000c1c0a40c08005130107036000519403440c158480098615699a0801441d403008804242c9170407010742c002840341c0c0f548622810040703a0f01901c9041e2128420306c500d0040790001c03050344c0f07401c518041c0554003040040701c2c0d4071a20f0070101c4216a1b60102c208901000d0840740c3d01400d0b096084c81620703880401d4004110b04040c503c90000c1150320759035030401c00c80a11500c01c50450580400062103149004001c074958040007400050240c0e0f81c410215640e54012517042d628840414089001c2101c900151a5400c000701d400c0540458413807102c007001c0d4000f10f240c00c0c610340e60b000751801c4140d200070400f5060050340a98011440c101348080d2034400060742038000289080a0303452108415030a5524803500402d0382d0b0f0800300c0719a41c0d104100c81050046284036028400d54034103400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 944479460 1250 944478210 944478229
    0x3042607120804030b1308030402040b04021b24011805100509280b030c120c090f100807060504030f020406030215070218060306192012060d110d060b 66
    0x1c1011102c0d911132842c1881984003101512a68142140a440743d021400090a6a0700070b50125000504003a9842c0014000c1c03107040c000040e1f03002c0e6624034000b01c44011900b030b54404640100b12200030540398400001110034050700c00007080d503100007251782e112644040e40c40040501120741c29500c2c0e100040305600f08441500112a030900c94081400e5171520b005461100808284074000f00c100019450b8600424860b000c0c40312001e4014500f82c0400051454140207446140c19040c40408090301070002c0701c6528000b8048500011000f10015908048811641e6124101400e40c4c0da6484508008641681d005840d43c0b408000b59595501c1c2011600c2048c120607900e01c078920520442450240001040038414400c0001c1600c0105059900903032454100f12140c141da58100c000b8017145081c40259407004803880e02000e010f00042c8000c18040362900021341d00c5404202081d00468002810182c2401155506080820341c6100042c81000080340407076840780495003411 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 944480710 1250 944479460 944479463
    0x16020c060f1b0f060a0501080c01021f09020f061204020306070813080903100501060f09050406120f0503070510140a05040f030f0e09131115160c21020a080304260712 73
    0x50346d400041001c40410400b00094070001c3c009064600c02034031210311b1207100d58252215198582c3d0b2030b0021540d900414015200006220548480c0140255641d1150444049019101d0b0101007010b0602031442c2038444c4070b282211000344021551000f90903040350b10101d40510480782e00c841d540c245401014060482e82d5940c030b43c2440011030040507200240d20030b0307000b2443c0c01e00500c514014003c00b2151141c0101090060145a103015460b500c907004014203d400351205451220125402c6580c5107882e005010040e038994821103000c0f540155001025040b9080241d40020b000f4000c0000c00e07045810300d080c4515442000c00d40188003103600b190f99481d500e0505c1c040180146100101c8141500c4842d0703c030708401d180500c81c1c850030040905218181c039003201040040113080002d40b07000010709119000c0300001a80300c4e818401d040741b0584009401051800c2d0000c00e640032184d2008540701e0341030400383d840510613000d0b1102d13140d134060300c03001141d0842041881c42106 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 944481960 1250 944480710 944480731
    0x105130b030316020907050f090607050a05100209010306090e0c04090501022b050907060504060c020a0323060106030b130f0905030a0f0e03031603030b031516020c060f1b0f06 77
    0x224120301c10804003000003446c0071306126052001d4035992004006660001c030f02034801e16900c003014240030b0b00c2e245035036000414603c1140c0520f184580e01c2c1d0081c1100c05c40a88003408142e4840d0550003d4410001d10645d03280d0180780e2164440c90300b81c000b1302400d40103400040c80d0003491140700e480b031500940c00b01848502c110041b844c038400c174071a582e80321100c9400b801026040410041c11071040713204000401c4640d440c1c50003550f40302080b01005592105203509010119040c0790b0191089444002950080800000d2014003d0140ba0500d48004028407038880603030520100524003100c5800d0704994a04840001410400041402c00d4540d03c03002c401140340b2000030052803009100030300a070800c0c08070050030006800000c0707060754141404209144400040f900c2c00150001c3c5064043c280c0c014440354401289c81e81c040320f149070382500e842d040c000c1c3c10311080784281ca81030f090030002040000b08150070f248000c40440c10450940302c07100c0700c2045085c5482001d4a1342641d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 944483210 1250 944481960 944481997
    0x80703020706200c10020702030705220f0614100509060c0c0d060203060306010906060509130e07260307110607170a02010b0a0e0603060406050a180b0601091d0105130b0303 76
    0x15100104583d85d6400c03556201540b0340003459001c41d0300c41e081440340b58020504040e07045c410f102c10988034241003012000c10401d503010381d414140134200c07911a03400d10100004426483d405c0150095018082a1301d409181018003010b1101c0313a401581900120b02071b042e2481200e560344020514a24000d09000d0f07180d0038604101741c200017041c0c0c05140c1e0503240440c20004250031a040d01e06001089401400000424600c100988880f0b09129024040c0345000b0070035106091030310040c13950405030842100212241d0070b0b5a4451020042c01ca00044280012607241000080a09500c9408014000001c01c900051540c01250340100581d450340310703a11807814103a4050000744112101c2400038107181d0013007922800c000c2c1000c0e10560701d071000194500d80c290020200b40e280c818403603124a00a05048240340d200b40d070030314001255010002005030050b0020100c0a0034041c41502691800041265880710510880e0646486a190713404a6a051000e000c007028090880e161 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 944484460 1250 944483210 944483227
    0x919050105071b050d081e100609060f0905100219141209010c030c0201030b0307030f05300c0c0d050d08090105162a0804090509010b0108070302070620 67
    0x182050100c002c80d1824807003d640000b05100003500d40f0103415500300406282c50700009800010810800102000c084d6020705c9100904581c1060860390940e441c0c0300312648417001265030f2400c101c10013000884000301409a450812000030340080c0600444640c84a60040d0b0b60008036402401d03130300e16002a001d094050310501c9540d02c2140c403001070174504605480068240440d105000e0204081c01c074180085900030340c42450941d50040c2107803a4079a6910785000c5d01c0c2c2d502c40003212b09004003480c92100242c420418820001c01c0c010304141940450141c00d15504403407502606071050300d0100c0581e4641108525240b8002d001038017030702c3c40c03184018111080140c80c4018503850b0408121a011150701041a041403500d0012604628080c00070428200c0040020720301c441d0041d54020059044020011100045001c2c00207640304144142200d03010714480303020408803000540c0d070607c0307503006042c01031007600e00041208030301c00300d101c0c4100303040c81c20303039914100044214 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 944485710 1250 944484460 944484467
    0x30237090b04090b0708040512180102100c02030913060b040f030209060f0a17010f0531080d051810020a090e15010c03020307080d150617070503091905010507 70
    0x10a24410b035010702c50064180d031099402c04004128004100b02500840c0030801c0a211030303940b2084082d80d942d181c42c50340312020398551182d0600ca01510400c400811498000d02074414805925005541400755002c24070025040a11060032402d98840f004074a2403040c030050409041040da4441949045106000b500c1401410491140d0240c00d8400c815590355103001050f141c01a4002080ca90140c42c164094510100b5001205007004c041203210620340d86200032071030003406c0d40b0b14450042c14207035100218004010308090001c01c521400c1075055082150082c0e0104d188005906a46a1090900d807400c1c03a500003d0390000380e403100303441d4401d19000c050203074001c24510310300b000030003881a1008107030414188032820741c403841858020300503209802d8020007210347d24107100305180014554908802801000c100003c2401481400f64200d0665104403171009911800810b9a00b608028050b4186108240300c0d121fa0740000c08111000c18442c000208450409000c00f5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 944486960 1250 944485710 944485721
    0x70c06090c0e1806060103020904020702041d0705060a0e0613150206251b110a0b0c1915050c16030302091e060a0c112101050601110703023709 63
    0x242e900c60320500700f01007104008112640c2102e000d00300180d80e00350b54030210b00a402400006548180f808610900d02c849100d620b20082c1c00c0a0140c82d412911403040200f9402403c140000245121017481103e040100040c0405141760000c940115960000010540100e1090800507003210041c000c009114000c205071907000c4586400d40405241e43c0200500d00e007504800c68034070b038540d010050240c0142c1c3c40301040c0c00603002941d095120000000d4035448000803800621528004480ea83c241c28584991294090026807003001d00d00b0b04038014110140c68481201e60411944031101d191010481090744240c0700541c03030386403882c1000752017042c2981c6827110440150204040342d0380c070700c21929055840d0074a11801d64070340c00c1401082c0ca1904589401c2807205050014914074610319a1207284840001d21456030303240f004507150450560281c2c840d50084505100500d40f0140c52a150f440310414845d40c80301e0001e0b902c265009a81703407e000c002d0400e10900408130f060092 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 944488210 1250 944486960 944486971
    0x6061101060509010501170a060816080c01020d0c06090203120d060f0f0302030a030f11011107060b0d0203071a0c0d0c05060906040b070503130501060e0a15030b040b070c06090c0e 79
    0x50f5183d803408001030404584203083e8400d020000d0f00041908146a01c101d001d46018001c070341184070300188024220016010394411403103030900d03c000940c400a1500e001d1600c559660030b16080a0351680701825410400300d0703250040602c91107414420401030114110b4238540410403601d400d00d40c2c440c20203036030440c50580c1d00e80881070000d61000511051029810316004408840c40070044440840d1184003000700c3d400c01401010184800703014000c441c2c0105c1080050080040820105c010f42d0b0800a4060300070020420041520082c003c0c0340204e1140703014902507110030701c1401d04112814100101d03910780004c900340700b4100b18059001e000c40000b0306047c1030070780b10002d01900060008080040010002d41c05080c02c42040100d258008024441c0940328410003003c04812298002401e01d0480407091a00c07226101d00100d80c3c01001e41c124a03240c41d02e0760381d0a15001026101400f0035850000300040180c4a03610405004401c5680c2680c1403034800400b00344040c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 944489460 1250 944488210 944488219
    0x3050d0b0303040b34030507120e03150c070615080f24150d06050a050c120a09020f06032406041536031b080d03020306030709060611010605 62
    0x10038010360304040102c5401c81d1300074125000303030720407112021118444945c0c10114001c800d081a41015001405440b00c0e83c860741101c0d83d80c06070030b41c00311580c02454210960540c0100c00390400342c1c90b08254903800032210100e062800c2d486442d05010b80d41043c80020007030300040c2040143e440d05100024520014401410941c814014201d892558281460310f006056902207140c8400554652440d1f04002d0480b0f281c1041342d04014006010480d03403004e089082200041e0455102c0c0100e400c07003c0c940580c0807894442e0308205000340302030f95080343c021a0524814880c2e41d50400592b2082032905517081040c00310b6480c005040405200c1306014100c10301042c0b00c82001a2032001c401c000624103410030850030700406110381c0a8049805002e150085525070502c0f081001406a81c002c1c6904440741503011003069281096214500c0c02d6004402d00c20705581c032940007140c00a0004007110280d50f1601c480e10101c2e4020760051021032040e00e03046c1c3e0808002e000f0840180000c44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 944490710 1250 944489460 944489467
    0xc030705040b13120f03020f12040905060d060e03130501050708030114130c0905120607020601051302072004140f070e180c0307090e06060910020109060903050d0b0303 74
    0x6001901a000380e005501c910100403c0c00c401600714200c40c1802841120103c485040590a010004904c80803040d00140a4000e031885901c0300000d080010f4448085581d00d0316160100000c001c00c2c01410329503001031003009400125806000714202c28120030040d41e40c81c0500d080c0c5058a8086600060501509212030f801042402041e00d04407a000e1030351a10340c001700d200140c080f074051511002142d261441018825611030145001c1d5107041d50603e1b5000d814013103490780c44900302c80507801039000030014041030038002140c1c041d0b0b210b191400350a0000c06e55680c421046021341896000400715608411481d0500800c2c3d0144104165221281418824540001c1c001081e22060091a01000c1243c0d240d403c41e00d014034201172046182400d018505107183e41c81920424000b0b1990440030070441140c0c2240d42c003d210045c4900d18001005042c880341400742c002d1803055540e107078261404584d0600616810700e20940e1703116a01c000f01c5501004440502c0030b205d009a0090 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 944491960 1250 944490710 944490721
    0xf0b0f090705030c010809010b1f09053712060c0801050607050a0204150905010f0504050f070c0f06230105040c0c030c020906210a03121406011101270b0c03 69
    0x8104e0440e00311080ca4243c0081c1d4409002c140074088036100140c102c1001030301c140801101c800f4040f0f201c4070f00d40c1d841c01865510401c20450b010074028001440801000c002d1041006560440505403551088032501d0f9a074101c14100c4c7d00b031810305451640e00c42c103a154500b40d0102c511805000125012414507110740c4440b0b030303100b01d010002801141c0e00c0018806103280c0c2310500e1700401c401ea03000d02c990344c1c42e46842c100d00300d03851082d14065405c220120340780440d000380707440c8212500d41d030380085508145c44c1c201c46005804c00644000d9074500c030700c1600e0740300940003c03d6042030395200c0000e940f4200c180720894941c07400c2903007003108100c1d5a17000032303500c0f00d80c2c00700711a01243c4101c4141c440b840001e1403d80a00b502850955490f0040c0c185110301081c0c440b02580a6214460100703034141e042800e4408011400c100c00307464000045480d8024824403104494540001030000b0b0304410304280902e00c407000f00c50b1407191610300000c02018201041d405040042c9490031b60905 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 944493210 1250 944491960 944491963
    0x3060315160e040605040603030e10090b07170904140405070807080316050c360708040813050910030b011d040f031e080103120206010e060d030c0f0b0f09070503 71
    0x2009800c801c1242e8602084581d40e9160002809000024400c00050b6a00e2402400c04040040c0b030034007881d803100c1d400a60a004462000881c0c030586a01864144c20f5907801c0100400001e200e03011007424488010b40da250b510801c5080081c0240c1036030281000d0401529111869001208540c48000b00380080031002c016a048079034448148410b4140b98503000e410020030000c410b800c400b00740541808000300024100400b01e200c1c4170311a0300d4008204141d85010b0407a04480450010404500010300c1d08004010300da20440c3c02071030b003a03243c10000c1c1981000b5904000c200d07003201e406205020123022020700400c0c03051f000008031402d2564211114000400291116421003e61018580201d202d942110401d148908110810b00000f5200d240e00780000e0780d20024202d8000016800001d000e81664000341344400f00b5541d0400300146003050700130803410010880d0300c1c207000880089602d0800b43c0700d01e0f1013072003500d0008a02070351301400034005211980649010041500d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 944494460 1250 944493210 944493241
    0x1021504201c0809010801120308070e0d1b05131a09100e1315200904090b1e07081b28090f060512010b090409020909010203060315 58
    0x80494045401107400c1c0001d4950400010110600304040064604000c15440145120402600e40c2040743e601e5201da52501310909000a0106014030041203500b4090150a8140500100910360009440d99900c00c3d215151904c3c1000c0c4c80c805038140241c1c9801c1e0351001c1d010b000c50708200103444421102200c070a203011501d0b03002b5001007022403172080e4550160710140c004120841d2007170030042d0500c504000b44810a484680300315000758003140c4c15018224215120241c4140003401c4c00f41d40c0441c0380d200341e54140e03001d0355890a080009005c071051764810031920350340c1060035040784000b17032500b58001c2101c010808400c0404c46014440c03c00700b4521620464075507259000540034000301580c01845503d0209003451b0047c0e031641c40303a03601066032038103500010070580da45801e450a001e07581480b030b204c9003580300520020114034003800b02c40c00028000314560010ba0041140c0003c03e80d0500d459035000010450b240c10200213841080780c5039400c90a4615004840d04420203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 944495710 1250 944494460 944494493
    0x207080d05060d080c060108060f0103050c21011e06050303090a0e0a06050a03050d11010c050702010315050d0807062009010f03060f06020d0905100912080d060f030201021504 77
    0x26aa0004a00b0684592155000c91588010740390b5895000d8503d4665403542486640c600d403140500040301c58000940080c100ca0b03004004105003c6543e040004c0102590081141c80706840c0c0c1222411400340078880780d00f001c0d1502c03071604440c00e01200d400d42c1c0050704414001d9001700000303409500d440c1050f000710b810368440b10215413120341e4940090f02c0a544529800020850044248100812400d480c0001504c900d00249442910b090a07280060902c1001c242c05001d0240554081d4211b64031030141e154880f8903907615800011100c9144400a45040b0b00200d0b000080140328443c09400d0f1000345071800c00500c2502c4040b080c0d21505942d241003013419002d5102050090f000f0502800907a048180741da61120340c025075030b0030803007182000640300c10710004803800c00c61106242004a0b40c2d5a08140d0304001213542104091813084549c264100840a0040d60500c1a00c02070001c11403c40c1134289580002442d0080810403185183c00480510002603031500b54007402030b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 944496960 1250 944495710 944495737
    0x503060c03040318180e0d021b130204090e0d020c0303250b0403030506030c010327031101180218151201061a041a030403020703060209041e0504030e04020708 70
    0x340c0d0b4900d012144036018510791540710001010200e944240841c0002c00010310740340805c010303441c950b00c880c5ea8192a40e50a0302507004190603003003104882d4410110003a000c2c0452000a4262410100f02e92041c0e024560171030751040c00b40c1c0094014001043c4020451005000d071a15440003e42c6034072480d0209203d80c103e811043c900d0060a005410485420012804040c41c0608000d005090119105172080c000c40086180d10b43c0a8441c080007030300d140c801c0c0d0100c2000720a41c1c80c7c89017142c1800f901480b02046e21a041c4407000d000d0300203040e09008071340790180c8140c4144680388107000ba070380006903408001c10021003008403404155800494141c2c80c1e550110980600400c0c498205200085020340000e095240900013401196001e1b003800c03445c1c01c1c071002c2600041c0020b480080043e04041d030b04001069481c1c0140543c24802040094842d010000700080450000d20720802d95448804020038550031044c0c1264290b001c0e41c0c10744ca840015a54801103100f80f1185c04c03080d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 944498210 1250 944496960 944496967
    0x190f0905071b030e0112020a0c02091302030d020d08240411041814060405042a1203030c0f1e050f0f03090303150d0c05090612010c0e03160503060c 65
    0x609104a40c20281d502c0c6809800c0000b24080c00d00030700180b0403000545c0031582c0072210f040340c8001c92089504490242d620b480310500591308126140402900d81900701e03607035182690150754284960107034003c41b50000c1041c0400c4410280603800001c02d40c03540401d500218030f100c1542140082e000c0ca104440011f80000c0c03210041c10309001d5608401c0608903102000d0315840c40310380c4101048018603404070807603964102000143e400442e0000e0407000005e410362004003a400c968180c0c000c50241c081d82c1c1a4440c0d07071003407001c8441032007a00040c5c0c0303a070b035141001034010907044a009035901c0c04400f080328200d05140c852041701c1c1d2079410400f002826164041081c41601c030a11000102190f890900d42440350782d039002640c100b10f01d4894010a005e0794580241d100b80341c0341d400035501407400e04d0007080104051009080303a4000e0b407641004c80100000b0b01c1346141c80c01c0d81c0c0d06c0724618840341405051800c04102d01040344441c00c62018401a076000544640c0308400341d10182c1e5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 944499460 1250 944498210 944498221
    0x31c1409150a17010801091e02101b06020d0518060103020906010c0309171606020106060917014721160905010612180b0a29190f0905 59
    0x3101d010304468440403c900000109898070190031002c819801000341c0c6c400e0b40040c603060103c40c800c05d08000e52000c203001d2030070b201902910300601c0b9440360040341c0c1210b030055250b600590703010024803c210382c0d983d0100042c402155040c4400072000100030f01440d81194045426034030f0241c01c960510029078191020144602c0700346001c0c240c0f020740c800700c1080441c00b140e41d0340b80f010700d207902c01449540085100c6105200c2c13001140c15030756031031001d0341c54001c80540b244440c61032140d82d55290f0080b10825910400c12049005070104001d2000f103071650328205e030314241c00c03803040041805c0f640c0d09030994031a80810f00049820007690b1080300c405080c14036001803e0380b102a42c2500038070000c0d04500c95440795048900c682c0f10800c0080d590522079040b169200203600c43c0e001c0707012402c804158107643d0140d000c60310280024044424024a0418007040f2a48000d1127808004040ca00d04103010684c0604840c03041d8109080d050015148100b1013600490284642c0c07440010fa = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 944500710 1250 944499460 944499467
    0xc081602100f06030507120c06300902031b03210913090c03080d0f0203130f0804050a1e080d080714070b010b090102060903040b070f020d02031c1409150a 68
    0x10040d80e2144c211102c2d03596400711091fa00109240590705144084400034180d030182004d0b8403029040101031a1810400c2c5201d40d03401c85140c0c07030001e26503071250fa510068400b000480000a21354500962410030748040504c1e1014144400c8d0040700e5200112180c400a039090381ca81010860703528013140840c0725030030011301001c20045c03c241043c0a0000074056000d000b8070303040b074840e03030103004100c00501450241e21080e503401d100350000c14004008140d1143c40c10340414402d010b020300d03040d540c0d4001110460b880d00071451500304d2000340400d01302e050f02030b00300070040c0e00050803508210002c09408403e0084c20170050000342d011800700401100215000c85070b000c01d164640e5611100102080d4003c6c0060601511400300810400e240000c1920100c1d101d55000b45d18020701990b0b0b4241c1c3c040c2c0351070201e0700415022226401a0b4040c800c4034a90110b00302050389640810100511140c0180400c1410308410440a005500ca8075060a00c0d40103224044c1e03650032000208a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 944501960 1250 944500710 944500721
    0x70602030a14010b0d06120b0105060307110d0e01030609050103020d1202030d0c0309030e01080f070e0316081f05010f050114070b0a060501180e1b0c0708010c081602100f 75
    0x140000c0180302c004102c144060020703014850480404104d260340b944d528400400c40410098520660b0320010042880d1074070086521203582e1500d00f0528003400421031405c1e04114103030707001c01d130303484201942540c1c51312801c0001d281c03078201400a9455074010520350011503601a110049030180303162010300030070480703c001200316020414100c0100e0010014110603504900240609001999070340c440d9240c43d0141d250440c030f503103603621071200c2519144a00c000300c0d50503000303070840503c100e5440b801c43c40080c0701110140000c0003050001741d4170128503950100b480c52031304005100321071940700414280d50b002e007024510090129080c401c0350085078401800f90b01211704201c2403107016048a030031201c081e240c1c0c280750421102040341407919405405d200e240c807000011030300004040e140d030490003048451441c01c8506020760f42400c500d80c110149a17034442c502030134282e40c056401d40c0e100086c501c600d91074a00d1903000a40f04c050054040080343d4840818086001165228 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 944503210 1250 944501960 944501981
    0x101802060702180c0306040e01140a0b120303090102030f0601112104090e100501090b09060904020a030803011d0109020c030a1d0310060905070f020a1502073f05070602030a 76
    0x302d991501e0204c1e003120031540111045070166080100c0c0c6440d11070140209044019018000703003480c5c0c0c40703140001c000c11819942c0c5074801d03134900d2403128104050004500400720340c00003507a030b0301c1c005240a240c2e841c003620a904102050f0030105581101140951154940e50709040080c0364000e9031400c070780910703004201c00074904102ca03001084002158403150203884030030b000d26a40c405a10b01200c001c00402a0410b42a400054183c9408507216500500c0203081140c401c0d00c0303495a09039034009170010008004102506e0b800c061030390f136086005154180055182c000d81400144d1a8050003c000741408500380c41802009030300040c0b600310300000b804980747c12040c2854400984554822108024940001302e0b80d1540300d20381290307004116800400c2c0c06103140d0b41d49800d041c1e8a4150381d845503070a104002c000344818a0303228004511040c4002c07203d0610b440c106c030084034060700329007411081d0f85072600d0b181c00101360786070190020401a100c0c1e440301504809032191250 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 944504460 1250 944503210 944503249
    0x315090e03180901121704080105040b04050601210803190e010209090a0e0a030516020631030c1203090b0c0304030c0b03010501080a0c110f0c0102101802060702 71
    0x8100320001800000740c850481880c0c140c014090410040c411008000e00408480d1103440000c41d01003041e080040c2d03683c107403200c002450305030795254813401c6a00644046428440340000d01090000c100030762409810038085031904410445e54044070580417000007490b400c8040001a407501340d02c0b00c886061000500c0502010b4900c0740b03098000d50142840e644200c8090012484550b01c51091140301d004810080c951820581c40548081d00941000c042d6803c2c203611100051700c415006d0704460100c001081700c0051071402c80030031030b0313501c9101540301c0e40004001c00208040c1c01c1c055040390782d6000e0405410096040440742c4032300a812a05069000140100d40c0c5070b8000000c000310303405140a0300784c042c2c03642d000c030324603110a1044600103958240802c42c424095804036256607441e007488a410409054580e0510408801d150b5050b002581501c200356014400a84008002c4808100003000701d5202d0700303c1c16107018068010300b80400c40e641191507180704030005c0d119001d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 944505710 1250 944504460 944504471
    0x307030e0d051f14010b22181d0a1208070509030102040816051e042d05040201020d0201230903121306150302061605010b10021b010e03030703031509 66
    0x100380384075262500d0b121042d901e140541c60b500322031403184c1e50b6042e01d85500c1444d1038031803406150800030181540700410626981400580004142006600024031500204118020b03040d805c0641100010b4520030b900f00b040308a00240e44900755400800140c2061043c07a21034490440340d5006081b4040d81540c4002004141e81d00700190810800c0c1c0e14148110030340340c480041c404807a0a4000300060240c44950507140c0380b5040d00031305180c0c0301481c61081e049070342d0300c4801419800c007603035403202c256038400344070555074140328200e80d10744140001d005220ba01000408000b000c417034002c03511f04134130003c110340031010300403143d91090002e4200807908290710030f69035021442d00304072a501c1c41c200c000c600c41ca4469540c0320407240c00504d4613040048588003400c070b1111440303084855541c0c420680320030f59650500031b0700940300307503000f400e1001141e40c1c1610940601d0031058140700140070045416500042111191a407610300031414110402030304c00031540c141c000d0240e880c00c14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 944506960 1250 944505710 944505733
    0x10e011401030203330702010b0a0321050906072009010611070501080c0406080a1d010f20032712270907030c05070c06170108030c0307030e0d05 64
    0x481003181a00e0013102543c078050054003815895030180381c0000c00500c42c2054040e024102100b640da800115400041500240350001465400191f0012101d0000c1d00c803100c0c40d44c0e041005000500c8038282021441c00301f07480001110350013a0342d002000da0010a201024142e40030f141403070300000107071501c0150758440c08040c0a050190303003400064810b05400003021341c81007058034002c4444105141c60310781881412159008021b003101c0c0e44a8945c0c403503000303604100800745002400140002651811074520805852a084c9030641c1560030006d040683c3c404c0e002200c1d044103002c0708013400b40310320303099440024994500c0c03070840380640b03224102d040148134001d0104403042c1c60200300f20740c60843c0540343c03814200c04441d00801040001400c90b030080d880104881e109061650500c1103940d41c0142c40d00e859001140000d0307600034031040500b010b0032034030b01500862020f541405444407500390b481c080c0603000b508000e8003a2080c0d109440362055210300303507040402d50340d07000c640 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 944508210 1250 944506960 944506991
    0xb0411040f032a0317070f05060720070b0307090801020a03050118021908070c0c08070504060f0803090123180307080109020f040c11061306150302010e1002010e01 72
    0x242c0c4015541c0200e40101142c5004100c03142c2507004401039404200c480c01c6407284507081c40760a07210740c1d0002080010b20003048400c00b00c2c0343c43d42d21490060502d803a00100080c801002038107012101041b003030071000f0240f000300b000003d0303480c41a14207499556075601111100d5082c1c3c0400744c20b5100003803942c0c8982d03042e000241610300268801c0043c18140f00317404100e2082c03400e40b03401c1e50800081c911130b01c0c2c4206000ca8200a003440d1000440c01c3d0390f1165920442c80b135008a5503540030b4a070810aa08280c007072500240303801e803c01c00c405868024482e0702d0303101e1550024100a095000c0035032001402e4032416284101d404400d071240300341292003c0c9110364000d402e2113846800700c0050701003414000c0040e486d0f806800c201c1540989014000130b041a440b440e8207200d2051a50040d5680400041d882070041c940798010f00b40050074030307401b2900c4114508442049081041c40540d03049801c094520400b07840b003a010340e109900403801481e801881070000d500340721188606098 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 944509460 1250 944508210 944508239
    0x90308130503010507050316140d02040e15030604050d0e0a1d040308090c01140309031b0304030c08060f0601120b0a17070b0a080c0714060f0106030f06080705040b041104 75
    0x1d040e4000c10080c0c64282058403140000ca420a46903100400c941c10078a103e04603210146031514145414010a00c1c1100180d0308030b0303002100484002020000d034410481303030550541708180e01525050425071030b525140c07100c1180380020b1080c0080d01d81e8490b01d40500040042141003101d003000e6290701940302207910291400e80000d105180030400c0d152000c900b840380c20405031103210144004400300701a540004044901c14002480b000c006680c010036114040c0c48188003075039a032411031501c580503044541020420358006d00400c40f1100c201204107402c0b036400d00342941c05800e40c030402c50141c2005a9029000249408002010300c1c051410710384520400c1705403200e041d102c0d81c140807280503010410000540c0c400110720ba81d1f060500621000340a101c000300e40c0c40c5d40704011881c00f0820303606240380e4044000100403c41d0b05201c1e01c060072524500511601c0e242031501655640740340901c91245985954501c42903442d40d01413200c41400f0000a6201d075030b10000c450b038014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 944510710 1250 944509460 944509469
    0x30b04030f0f030b0604050409030e04050106020f0d05030106020a0b0604092a050105120424060605030711010c020607030518160510081905070c1b05120c090a0203060109030813 78
    0x200e268801912083c068000e14090040c040d00340d5041601d0b19007000302620f58100300b9401d02100b13011080107034482c0d014903806014560000d22140c0640c0014034500b4411046034810008140014880540d02040c40074910781c010a0000c1541c4400000400415000c103000702041c110f60b4442d0004038460354246080841030100c115000e940340c005403000e114100707030401385420140024000036014914011030600c4602e00341012401081a80300b29040e5400c4880811004001c1105080c1d000d01c1c40210050440021f003c0d44031610b4029540302d001525403003d15450ba000a076440e45070035488002c2c802100c1c01c9503800c011340720340c8019020650041600a80303840f10103050701d80c02000114014449080e2420780601e111900314014400902901c041001d035000c0ca8002c10011100310071102d0114201482e11442c01c8100240c0c2030180400a4207034108000107100c5544040398258028518031000d80c0d0796075442c0048800300802d0700003d0043c0b2008c19502669400418484141c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 944511960 1250 944510710 944510717
    0x1912081b011a040c0e04050c0717040302040f09020d030e01120c0c020a150807140f030718090b030a0308040c150216080102090f0d1a15030705060906160804030b04030f 74
    0xe5900320240016111035440d070b031000c181e11408840311750610380d010b541d004401c01303000b50a2035026039840e070001900c940d2407034034400041003d00035840d141c070030003c0192007030008001c1e5a81c1d590200741c10010382d110103820f0011010201140740d0060f03002104040c5c4907003040010015052010744181d039402c0c0b040e4056100050702007134407603204624410820503078075010703280c0d0350f0041c0440392818030b103201a6074a881441903642c00507040c00078501465031912061581449098402d600101c140e002d0581e441c01d007948110340d0748000c1102142141c0601d44030819a40d0740c10300d83d20050013584aa81c2812030300701c01119041c0c0c0800c100c42120501540310030714560300c2c61054281d0142107007965004801c41143c20151a240302200400d610440040c0d001c807045c1d100c119000c2408440381d6462134140501d491040c5824440100a080c04440c03003404c103690400814500e0103113080040a00d150582c4a0707042c084940d003a1001154400403070189850b10340390080105547d407091a020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 944513210 1250 944511960 944512001
    0x108010e0615031f0e030a0905040b01020a170d02071a091515040c030b03100209030f031e07030c050607351504090611090a051912081b01 61
    0xb4008540810300340030001c0c000c020015140500001030100a00b5103e031841c0c2d07600102500304814000350045181e545c4455001070300e0716052206881c1e140030381d0340c119000701680311700040400880c80d080102c2c07940803607290340442010400038840c0d2100900000130501501031050102035041d840f50000006840c0311a190018807002e0943c1078428a201d040c215407d96001d08056001c0000d41d0803e14010802d081d981e03010a003045403d085200009400144001950a040150b401040c10420043d8a4503074012500c4801340c045594000c04120001042e4040c103200c1c03180e080d9003a4120060f10301c2401c0c007500103401d03c4071121025103540e940e19050030083c1c2c4030031002520305041407801001540e9090413105046550741c1d50030351081d500c0d45004007080e0300b449050035a103504c0440640c5e0b41c401354200000c00030310b61301052043c00410103801d068401a105441101c0c48168007000650141c903000700c150080c0010601c0e482040248004440d01c150018880c200c403403a8403018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 944514460 1250 944513210 944513221
    0x90909050102180901061b0614160f05040b1902010b221104050d0201111207050102070c05090118020c0703060f0516031107200909070f06052803060306050108010e06 73
    0x10005400d06c210720104010181519a4801c40503c28544034810380000034405030039040c0b083d075400b0a881c80505000007182030003140c0e800210300d20180905050103030806183c080d020885c0c0c414404000800101c402c9611a0701c0c0c001d400842c096040246034940c1c02c0a182e4900c0e40050a424242c003002d030601e00d0009c001e40088013118203440f00a40144040d41c0c0c070b500152180e00485003031003510b214408440d241481b00d0405490000c0c811800035907036240d02e0820003481c4141c0d0300490b20816010004102000b02041d004a06c0e0300360302c001503110503581100ba4180300e007662024182c036040080e940343e54a5680d102c548100c0040020f00c011400d0143e04404032071f04141c82120f2409c04110000c0440c0300344104a03010051002c004132070340b003090003040301508281d03003074000f80d0700400007401060b40801c580f01c05410586030440c00c043c04d0181d030306280c4160070b0100403801600c00e17803003013600e101e50040005941c208070140400c0d6500d8610314001c1001b100c00030094001d2601198 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 944515710 1250 944514460 944514469
    0xe07060c03031401060f08061908010e010506030705060403150239011109040b04021b2d030f09030c0307080c0f0103090c0504050712050f100914010b090109090905010218 75
    0x241642c5c0d507035503800302c00d11000005807009803020f0300195106820100c0e19450305a80c1c0c0d0108080d00350000045001c0060500d61825500c015058a00c01d400000043c8003540b5070030180d40483c2e030080300503170b544003030008007100901c148149154000125a0003000d0141c015258401c0941e0402600c004840701d500d60a003299030700c4055180440e410002c2c2540c900c1c0c2900080c2c00f10b03400810040c6050410007404002c000c1000030901e4580010a006402135a4482100c0201201803a806010030901c16903544034891044130095540c0c02060005480d00c041121014000000d8125554542c03240b02e01030391505111091307407184020b20320101541d4424090443c02d150f0041040014a042800f0007002d040002c010b84100020f8186071107903200e5034060f89008090080501c06d590070006180015814150407000c03043d400c154034188114161510b103411031b030b907098034180c9440074800121416130559004402c01414400c5000038080194000c1101036804402c1c51820100d020901 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 944516960 1250 944515710 944515751
    0x180115031b1e0e060111060c0304030905181602160e07020111030a020d0605040908180a09090c0e010807050d06180f20040513020d060e07060c0303 65
    0x11540480401000051000d1415022000d40c020079504407540324076078144101c03a207582c46030000160b041c040040186459003aa0031441c203203001d00000c4000c2034500d80c0d5800140601e002190000b0004013814032805040016000007401601c0e0174a031466500c9148009448075100486210340741c1c0041e500018110304600054108508024602341480308040c01c010702030429075494502c10015180c403440254402e1466260060b00c440c0350030f0680c000c40b40c1c2904540d0295103030401c0e06001c03901510945101034001d0740322454118031240840c49806696100cd1405070420a1030410401542861002e907041d1485141c0180c1c1c0ea10b92490340c401151060035005840031004c04042400ca82000c03140942582c0030014130b03401c5903254011110500300544529040b609050510018161420419038040310706202038102000c2152031548148002481030118841400401200d81c0040004050100589503403552740d2001420403010504200c0010f842c1c03100072a0001d881d01d825 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 944518210 1250 944516960 944516981
    0x110717120718080613030c060f06080a0308060405060d020d06140702010f0b0603040206190e1c05061e07110109060609150b0a050301122a090f060305101d151801 71
    0x1541c40540c5c40f0f880a544c5940c0d0200140c40442e03c4045c0b010343e600d00d80c024103004000c040000c0154510500b0001d01310803000d48843e2146062a00340003840e031760300030080c005540496038400c12441c10301e040c8004010a6242000820100c4c041020150701940070000c80c0e0701d90a000e000d2412180d003005068841114000c0d40200144803041e440814120400c681e642d0301d007807100e07a403501c090005800c4011030b980c6100c2c13010000004020041300780007a98001100860903410114200d1613a951440003e18a804005242402014094094120140b280d41001c02007080d5501c078205800509030021112411420400c40040d43e5090b040c101e03480d040d0940d45050440e42404070618020080700340944114600d05e102c0c0c24481041090840340050403050004528900001a0b094a40b08031004140501e030610400205601050003a030b6502040c40c0029001110800d030900754000800c44001807046132800094030b04041c60484c0a40e1100303c610842d4401d42c001030b800d0b01c1c1e00c030301c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 944519460 1250 944518210 944518231
    0x2041d01031524030b07030e0d0c080f04090501031104110a02030a230c07080105010501020c01080f060418030203030402011b0f11010908011a131107171207180806 72
    0x10403202ca00055488096071a000700314900c054980003c03003042d08203050b001a110b1003c0c2d1001d006040342c06104400c21454100040e205002c00c48a0140448a4210001e081d040000646131428001402141c000e440c004500f0000c0b96141d0418420505490b8010390082c0d14100418907c000910281c8040c1211a8011803801c111420125900101a603110b00c60026440200d6041e41e401c10182800d5003a1000038800f591a12040509440047c2d2000c3e0640d0020280c280040c1d07031140c84d9980c000b1a0380c1d80c0a0007505c3c0c2074040342c010300e8013500402002c1400380801c010582d000c070056010318002d985c0c0900862401c2886102c0d000f10040040101d40b90b4242c1100041e0310709280072030810141400030010f0340c0d030440c01d802d503611800c85103e0304125140904a41c50642100c00380780300d15440c200881d0040400e41d0307045105280b0050900c14038180c11800001802e030440304801c01c80181080d8078100a6030161004400c203000980c1110390041c04540800c0024642d44a0ba1b620b11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 944520710 1250 944519460 944519483
    0x31630060c051213030e06160618080a090306050a0225030c14070609081b12101a0108130210030b03030c012a17041205091302041d0103 60
    0x103540c04010806510050300744401807012040003100c502a80c1d100301c00310901488011424a0010028203491aa061003120140201e1960002500e04442c0440e031011000400d0400b82c04150080104114001c1880c080060000340403a07102c031091080700c0c841d4500784004d80741d4581c164107034003800510180c0380710802d540140d200062440419140d0003070070030392003040407500d610807014005c00302890a54050081048041d0744281e09000070181c26003d05044900c60070f800c030804040340307500c610030009203041e00f5540400b40864800786900300d4003089400103515214500c440e80c00489404600c00e04000340b83c4803072120b21704191950081c880d80781c402507035000764003c01c900c01d00b031505880140305207402501c0900c610302218814001d0240c0f906640300082d5a26066071880c0b1040203c407021504000c4850300d2815000b03540b002142810040b0040300716540c0c011090210343c00410701c0010803440500742c1c010020381c5d0f0705c7d10f000f142c08040c0c7c0705130444081086c40000d11100600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 944521960 1250 944520710 944520713
    0x141006021c051c05160201020c06040201110f0715120e0a15020f070501051f060f052107090906230402091918050f0708070c080405031630 61
    0x80c10759403004038a420a14100304455802e180b10461030b44007001160b54900901c0118030640c03141c0078100e0441e2009610f0250004840764035100e005e400241070120034211402e0500f81880320400d0745c216502251000c0f943d07184150140c1301e020f603805001c500d040d900101c240095010f8002c248082c4401070000c880b141d51060140c00b41071480880250b400d1140d0792082d0808401480002d01440000c1082d0519401c559000c80300980b8505100440c22001c0240d143c202c0301400542445041c02c0d078691110085507038950f42600c0d400030f401000c0f18100441039801002d894142c070108c20f010001146c072280440005030031081d0910130030182115501c4117242640040001110143c5125248074101d0f020b608003500307540140c2249100079400c1e074080416445459403000300e00d540c000031824043c0001c1e220b800040c0c0b110b802c0144200c00e4106000011040b207009003000383c112100b54140010f450040c004600a910700f00c02200d080302e080c615441401094202c0d071a41110401109 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 944523210 1250 944521960 944521993
    0xb09030c121612120f18060801230d1106160f0b1b09040e100615081522201314010e210313080f0609100c020f060103030314100602 58
    0x80d105100800c00c01491070b4006c020310707540e00c400800d51526030103032035414140c3c08104600c40c003442c403c4082c40c90364188020344d180c07070030050455040018650030b10082c2020640a12802c0d400035a84070b0a1495042080341c040f059001c2c1034016060f08401e0f0b00c0e404203008480f040315413468a000b13400c0c080d5815600c0c25500030190621a8030440b140310514007041020380d0200c0d170010300d40c0c1801002440c05036801c585c0c0c090f80019001a07a1442c141d240b400605015403034011030290410390026003100a1030b61b07119032410010907039481190341d50800b04e070030554488075080003801107075030000420104c041030690501d04140c40d0144041c444c80b0034484001c442244e44099084000d041e40c0c48038800384010041c0f4010380c4d1030940042c0c1040380c1c85141c0401c15503c1401a8498010801200008200345865480002000c149040d2980d07049103094a010300111150003079800001c01c1503003680c8a442105031076409406d903a941d206003c02d00076800d10500c0c002d60011030f15034008503034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 944524460 1250 944523210 944523227
    0x50a0e0d02150408060c090108073e0c1e0f0d12120c050a270e0a0b010e1002060109050415050403090513150b09030c12161212 56
    0x350031200851110780000c0c0c0c0c1c00112100710398455000003010300c50014144503990b480000510703c43d1600292400003801d01c4002464842009580380c2c2d0b8100d04e510381c0b200510145800c1200101214000840a140081801424040c0d203d00f84100b682800d01c41c0001a180c904040d070107400d8540d0a043c4110500f0301d0f58000c1e485503003a405000054424000c480d925501031780c4400f64081d14045034030469140c0d950340400c2c4201840542179899004105951550b80c0b038480017940c1821180c0840c040b6296044990304030f08032000c1141c0e4106681c411000302000341d07144400d01515405104520040358404801130b08860014040343c4026009150010b10a1020350b4031120017000d90320489905640807800074009aa04002600d040e44d900d041c002510481081101c0d20344030841201104c0c0d05c24060014404194100a079400380820005150044c2103200c10b00000140140c445441080c0d03505201d0010101044010302c15002d01c86660f801110700c0300150901ca8184e50710074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 944525710 1250 944524460 944524487
    0xa03020d110f0901080a1203110a030e0c0402040e0604061e030818100c060501060302130302040b0a0f0f1502010501051003021b070b1b03070f14070515031e07050a 72
    0x5095441041d925410443c84c02040f2080180116407070914000c140c00780342c0c6407468205428480c0a2072505441400c4882103546403d001030a40d0058201900300020714400e158811300c040b60004807143c588070058815901182c0421481e40c591200105031501481102d080d854104002e10005d00303480000c142d00400b614407403c03a4414600025401c001185501001964180035a02000803074025180507104904042d42804521800400c00014520019220769203800c11001c42e80c6407014640054541c900004d03100c1615a62400b040341e9892080c03d40c00502c00b03090003085841032041034142c41005200001c4c0d602e5500d0b04502075000914580b00840700307903120101940082041100514004d0105a294000c00c1100da41e1407000011004564200304105c10000b0f010032204000035901418400e82c030400240c610785000c4150300900d4104c0c00300f07407202e5961105403000d14400c1e4401d1118000c115092021641c0410701683c80201148043c801c00400342d0043d48030b9810f24 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 944526960 1250 944525710 944525719
    0x14070303021216020606010f1b060212010b0703020f071404050429060f0103141b130305100e0a020906130b0d0614010b040b0d0f18060c08060a03020d11 67
    0x100c03031035885680303030400742d50f1203040914800b14004a00c0d01444a150301007001d003425203a80c250ba0700c014084001c7e05040090948202c000681004059815507a04a6100d0380f14840c643e180c00042001e94050b40064015204903850460300c1d4000250003416600180d4102d40d018091000344405400c016008461003605401c034201c020f81900e807000508a61019038014905090050240100d000b00543e4101401c01c041044000800100c194119039030004000128256080d0030380c0b85e02641c00b41031041d031100c290010078444001441d890a05404500700002a0300c5100f1303d544640001d0000d4101011000003800b62622584000441c2a51580428802c291000081c0c1020b0505001c403040340da1109510a55140740b0b15083c054440c46045501d001e040200c2c00d0300703d0103904ca486240540b58903100c0d6044480d074011640c140300040540b80c10342403c0c94000054440ca50092000807005130028001d03180402d0900d0449402134103152805c00d05485815641c0403254400b44c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 944528210 1250 944526960 944526967
    0xa180f1e2a09020712090b040b0301120501020c0d050a03060e01050d032114010311030c0d0605071b0311010b040506060d091a0108070f0602060408092103031503070906061407030302 80
    0xc078003c0c002002c510b03200742c003440100724100c0e001400c44580b0750446c41c1c2061081c0f1040c4444105402180d0558024200c40081c0c40e01c2e91500c6800380c401d2010319041c602030f500c02c40d040b0715088405842c6400c89030b20305202041c0c0300c00301e00c0c803914000d01c1400d40c0410100d18520100b806209103100d600100313082d0403110345101a9410964280c030070f43d14505c07031502d0010010701107040c858461022085002c0c01c2e905e2030080019515240507040603041a90316004108540d019449117046a043e15024804441d09800c01400c04107464401c1d142c03650074005102d840b403401d13100c1c261203190010211030034141c035250840001c04842e00101d4001c0c0b41407000c1044040070321441c50007000ca160081c00c03075504225500c0f400c003211740d0001c0c040d0740c091401c0c04000390400c02528043d603400c1e21550b2800301022040c11215002c2c1c9200d01903400000103010132900c521885510a0700705404840d03101340d46120244c1160401e20034100000c00d04582e180041e00c030580107006041c02468090304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 944529460 1250 944528210 944528219
    0x18020904030503072007050a0509070903030809070e0a090203010b0a05010918140a0b03120f0403022205090d0e01020304030b1b04080d020a0201031119080a180f1e2a 73
    0x20710042c101c1d05c031413951103031100304520700e00440920040c1030150350a04880c28810009804180503000040a000c2030a0008038045804c005110003022086503415040c1001440c8000604180b01d05a001e07500308080c80d04070342040c0ea00034080301e8043e0750340061145040c00c20407501118660920010352510390307000c8903d041310001800703250101c0c1d00003900385c034913020036147c04c1c5c0860396030b10200420703c0001c1200d0120026181101d806445907802c064889400c4d12041121a10419006242c0b40520100e0704000601402202c020f459000350340d503000d001660f69008900c0002c0440a09100041c0b80400455260070000c030410311450030151a03c909904000740c050301c900c0142d100d050b68a09544c1c1c180116550210055089803801c3c0c01c0d84a01c400e9490500d0980c802d10141c28003160b2404a140e000c07000c15003651315200c1c03494110340303020008601c2060702138030410134081c000704410244142a0a019601500c00c0341d0b2001c0b82211040c02580844040c60700468407000021f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 944530710 1250 944529460 944529497
    0x41d1f140f16090605092110090b070c0f06020711120d090b0a051206010e040e010213050114030f130b0408091e0a060503130602040b030106031802090403050307 71
    0x60049035a5a01501c40e842c0807120050034464002d2503800700304210714100070041c1c0190841e142c20344140c40540d0b1401940d030601c42585c0c4140c98602d15407103041d04000071443e099000c010a00c0c843c00c240140d039282c81078100e1701c0500b030040241a0140d01c81e01000082e420340d008003626445640312959080150340010103640300c907011009131b40c0000200d080c90b1a0b02600507409488201c40ca14241020a8401010f50090b20110b018194518010072a00c4c4c1c091102d0b1000108020400d02852420503800307030107504154100d0141300300b0340350045280d41c0940001d1082c0c0303c82c50812810f555621001c000c7c1c028001d0860403d401c0c00c02d4042c03007c02e42c0c0c0c40606204a004100d825511040901400181030420440341d0f10310740c0100403000c0943e640202c448c102c2c0ea0343e240070383d101e40b01c1c980c00c1101e0030066040113001b82d1000500082d80b031f414501550483e1519102001444100d00b07401c1c3d5040d100440003544003040c040024002809003026540044d02c80c90840c2c812189a030408 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 944531960 1250 944530710 944530751
    0x10603060204080610150c060e1f02040e06060f071b08060f2203020d210c0c1703090a02090c0d1a0307060215010b09220b041d1f 57
    0x510f4a41080c03040002203451003585100410100026071030f25642d0500081c400b4940f078030010005511200b40100054003002a21840021044104101c81c9146280e1b0020351140c4188041e442000d0001034861034007100307a842d03d003150030900f46001710b90743e100d0003000b2001c04041025981c00501103484882003201714810791884500c40711a040c486500904041c066581120403005000c41c400000d9001c151a10583c100342851920b00c140c0640c0d1041c075820000302540c1042c9001b8422404550090b5590300c00c0d8041d06941d022590703840c0701a00c0302e1008441c1840305a00c810395007001401c14928050380b1030f810300d400c181032420074200d1400340c81601c800b40d25907032940711011000e0b18061050100604040c0010226114400d044000c4100144601c0110000100c3c01c070300240c03244400f1440350b2081010981507903c84105405c001d00031f0804640c081c610b0b0210a42c1007509180b802c01c0342e003417220014181c00181801151448488596817002d144d1105c401d0300046014000d403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 944533210 1250 944531960 944531969
    0x6050103110406121110140310030b09060702030f070c0308030a32010317071208011509060503130c080d08040614070914010903080a0c15020307020c060c010603060204 74
    0x4103000c0c1c0d08020801035643d41d0b08070f50b10032400d500c0c0140c0090305410184031101c00542c0c54500308482160103481e6025500ea4104191900104101e100c0d81c40da2000e1003079a2040c00c04404984400c0340055070341c641145c0071070150b4000c010600c401200b51020b4801c032841294502c03003841d01c030369032200c1c140c1040e10110035045d180d2105007420080c3e00314814400392006504480341c80c1c1000780040c900c506102c0500f41000100d080100e850b4024112041c0a41080d00070071190007000004081020034851045d40d01c1c000c00c589410740f88200801000c41382240d07952401d580792595030080000524000701d900d01420030001403140d00610100c0001034058868a1a510b4076040000540c2c082c00c00e250805c83c0480100280703260401050802e4030303012036021003007400901c0143c9a21840d40c001030540304c030116202000680c480d199100b0302d03106104848240f00c0c40802081030f4001a44c0c030300c026802c01d4110342400e082c800040e04014406c0400812700c5a580d4a84100700c1e84190407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 944534460 1250 944533210 944533223
    0x41716060e0109080d120e0a0503031006020705034b0d180510050711090123030111160303150803130e040302060c030402010e12071518120203030706050103 69
    0xc1e10a515030b00800302d20018001c62001c1c040c05041c00d08000d21507aa500386180215503200c900300340c11101044400c0300e003540301003140d07528180403d0800c0a491a0301c60a40123100e5080007151074100810a15415881a58000700c0c41590030712201e145c1400c05680c0744141200442c44084061020104483c4520741d0080c000407061038000400403440102030041009194608011a89656080d01c8501c1e02518015849200300c1c074240b140702c40504516580900740d8800820b2074900403907002064400441c10140144000c8149420707034114403210a0f00301410b02007407507100508551090746900c00d1400140094555241c854600c201303400c5400799920114241306901c42d10615500a00403100e0100c0003498246c0d0700950361b03c002883c00710f65003408004a021a40502510011914010801e2203488825880a550740500e441540880d08a4072030b159035683c05140c091454141d5210608105170508014100380c07401301d4000c0f6094032080254202040c414820300e40654030414 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 944535710 1250 944534460 944534477
    0x909020114090f03250f15050a050403170301050a050d0b1b0904061d130c0302010c0807061d0d0c021f110f01090302120c0d110309030708100501060201060b04171606 73
    0xd41020700c41034150406c2000050a080030f1004041d0500300300c11070907082c6080781e42e4816950048403e4061980020704040042800424140c04100503505072102614070043da075540e60200a07451030345803000361500400704081180c007442c00716a945004240e03484103150118400100d021641c0b00c2d4400b0b40c2c0f6119880c1401c1d200c4ca80d07108502e0b00141e40e903400d0305510501380c4542403010080c0c40b000b811b11204e10110341c2080f00d854140c44400707800090810400c040385c0f405910a85c1105540d020718050710aa14441e180030b2418004041d070040d1a1086200810360b55494480c4001580e00a1109105c2e0821081c402088090300040d005000465420054031700a46018600004080085414040106a1580060a10541d502c2e52801401d07030701100b401141903102c0c041c54503416000d0000e0200344a01c00003210780c00e1101c0c00700200020781c3d95000481c01c07100d190064003a8000108010422020a51172142d2401c0d0341c1c0c81503401004c0c205c24094145016544803070702240c1000b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 944536960 1250 944535710 944535763
    0xa060506040b030a0827180a15180e102405011d011d090a02040e16020d1116030b1e0c09060a030f090311070909020114090f03 56
    0x38002c2c0c080800c0300360000c10b2180340d55a10302d40c03140034818040840e00600e0050f51040003a920400d03000c468081c00d05e415070098081038100b0003004503a82c000300c40c1001c4007000d000c4100d00b50f900031a44000448040c02c5d69610380440030b0240c1000e521101c0c8503800301491120482d21494203c0780c80390150403180d402c020501132140c21a58440c0e418401c9411070600c091084544c40e40860b1001d2901050310301c0360441000e101210000d030742d5007004a4208200403410396030b0003002034994a90700049255a070300030f907200128035118007000681202c4101c07050745004500ca45009503009046e10482c0e00c0c07542d500402d402155105540341c007141024040604004030501c2245450305683c141545011029000c0a2041e244040c1c0034800000d1101da0480c40b80d4446004003644400501c00680c3c54180180f112882485600003405001e000181007083c9104080c105907041c0c660407419011003010704165040112881d0f003003840400011714950301440000d1642e000c03d050743c0c0b445ea032a03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 944538210 1250 944536960 944536969
    0x9010f0611010203061f050c07090b210c0910080d0e01110109021806040204090f05271908090d03082a030103141f060509060a1211010207080a060506 66
    0x1d19401016441001445020384542c0b001c0d400b09042484880d10005181c001140c240c815250f201546015051000ca545003c7e5000300d440001d04991241152030b404901001e50326001d042c1d4031041d071020810002d80e0410362260390b0f21401c404109400c840d91801031508144981c80c1081c000380e031000c108901d668008041412601858000f0040d5164990100c0c624240c0c0c92a0b03568822410000079510755610b0701158040e0415090600480c043c02004d80301a100030f4556010302e1541c104041844000301012260189082004081d0159441110b8440000701740c1e040ea415001006181000d03150b40700305402003440f03640c07042441d04d0026809000f1103850441544200440728441140c030411b041078905403a0408495244007071000e003c68070740720700504200b00650b500e8180340c2d043c8140754400d0044410680f00340d5265503a0388100254032403c0e01450401c1500621b800c00400d481d260f0700001c401c1c1c10b004554000e52180001c52034070003014011543d0507180c00070001c0c0303400c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 944539460 1250 944538210 944538227
    0x1e0807090507120b030318060904020c0105090f03030c16080f04030308041703090c060904020417150a0c0921051e0106150804031b0803070f11060103020a0902090f09010f06 76
    0x8103c0804c2040072001000680c0740d110b91440042414030703d07403500e0358569404084615201d07004004541d562a181203407800780004591410b03030340c0584510500d850501204491041c0c01c810107040c584000440700384c1c041d40351802e065809500501c106c074089450b03000108041c500a864501291405141034100d04a0031030200042460500078843d5000000071403041105c01101c0e810780321099034020400a02607035000e880200b1080d403140005490110b1480002196600d40c0681503941c0040002a58080c1030b40b980000c3c0920b10400090928440b603018114240744c00340c460200e10f440d020701d0444402114051903000d0400c00f103142c40248200001002c801d44210382c40310a014002e0205180240090f06004040c82001401003903450720310030095010408544900300000d0040c414506038054001040b00c40701400c1c9001000030f183ca040703a40c02082c1110341401c0c0019000039402182c1171540244c24070103c4412075441d071410314081d00c0842c1503e4002c1f4500400149102e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 944540710 1250 944539460 944539487
    0x3603210e1903050f0a0c020d060e1b090105270a02180d171c05011211240a05130b0c060c25110916020706090602071e0807090507 57
    0x4410034035001c006a04002901c0101d060a40c1c41626402c103450251401301c0a001c1c000d52002c0c071052290100005036001000d081c103200103c0d03400040070104025144407007115180e0100855004004c9880c0105422050104101102040401d141240c22065034140c030385402d910713000b184001c0000f0b42501000103181c41201e61070107410240d00c8801c2e02070240f25142000c402c0006003c1c208a0a0b80840080e8401c0d1501c20480c0c0d40e0b562a0300e409001f0301d030b10111054052007802c40c0c80c500d004001880035911148286107024621011250301d40d202d00c0d40301003404000e208507000f440701d039200a4000c5c60180c200a036a10760b81e000080c1052401403040a524400340000b001403060a42941c00010703040c01ea40f0007852450500c030525010502c6103030740c004289030410290784060380104409010503000c07a41d005d80c50f0f000640f403040c1180103080050b40820b004014019810070307440708101c10000707003407441900e8141041c14411690850062142ca4200380544194009180c540c1308 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 944541960 1250 944540710 944540743
    0xf0d0f030903140313090207060204050a180b0a050303030a090c081f0e0607020d0c21111011180a0509040f050607051c0e101e3603210e 60
    0x312051045c40b601581c18051546259408207130b200410155034115405041e00801804150342e40344010055900c05440c14050241804002001d50414030030640a0b144014007071400c541da840d465400078958504151000361002c40c002801c0d0205001401011024040502680c155800e85000391244401c00c00c500d0740c0a1800c104c5680d90100b130b5480c58000701d2034807400340c030000e0411100003c600400003a03218403c1501c0d29000390481001d40c500400c1005491645801c1e08000044410b0101c499104200800c404040d496104485640d079040045c2a54841500d0b00042040b0101c1181c0464580e242885e2100c244041040341a62241c082e15100d0320744940c0b6010001c407112000449070349aa1281480e0000c0380c414407a45101d90450081000040481498040a1a40c043e82c4080325032a0000040c010150700601c0400400c003d419144141c80005d0055901c080e404c400798108094101900c034030700f41c0d1001d16030b03004046100110703510710b2131205a82019890001d21481 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 944543210 1250 944541960 944541967
    0x100207170d08010302060a11010f0228050405041d0307050609190c05060f190f030b030a08070803060102030f0c0d0f3f0e0a0605010f0f050f0d0f0309031403 69
    0x3095402000d843c1500e038140d40701600c400201d00e0954424111541c20710f00c5508001001c801300301544d000d01001c1104440d144088961540207203d0701001601034400904100300a002505103500a156404d0980d2020002400f81441e91400d6401a4100307c485030004001d00485042c10450b61085000740c0d2000b42c2c18044540d5140b090030007503c81e03d406071001096003580d200040382a152034032070300c41c0303144400b58000030020291031265680d000031900e010900301c603504000071916080c503480f072a014034100702911400d44681004001a04500c0104100c02d0411651070290160700d019200803c400d003a03640c00503110110b1150002c080064054186400c000d28080056100701d000d04407085041c010682803250003246105000b00b42c0c00d1480074040070304001105080103009600421450f40ca40d4030700f405800042c418201c0c0200a04401d116515200b11032030f07600000100000c00c188165528002031119003901500898040082042842180125018040000b1010707515 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 944544460 1250 944543210 944543233
    0xa08180c0a090f140709050405060406080109241103061c1e11120a06050a0b0d0308100506040501120507050d050c03041202010513031107050a0e09160e040204021810020717 76
    0x11541b413500c503c5100700c2c2c070340300455010380350750b806200035007844030081c0310b0b030503030ba0a100000605154044608802e007200d0010081c081e84951000c26550390801c52958035500204880c0c6100003143d42c104030040c200c204006444900b41c06400c408441070fa0049224030f080c00c855454103039260318015244c507039845448a0f00403070b9000c981079000400050304e840f01c1041c00010003104088136005100b22500c402415040006248501c0c203560840042030344613010701c180c0c1e00661280030301041e500c140c00003509643c5c0d00100d50250592a1150400d020a054901681d4065826a40007031000007030009010003005440c84a07a10360000340024282622103a41031784492101404100103902901030003034042c8070349001080000e003800c1d001d030f03140c01c281e99101e41309542005440c801c175516464490140c1030b8032021100c11354002d15007991184c091101135448040c2a1f010b00c3c000c021480720541c0c41d010385d410004159402046a02d0800d46084031640d1500e100103000d9100d0700003030a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 944545710 1250 944544460 944544467
    0x106091d010e0414060703021b07122d030c0308060307061e0c08031e13030c081c1a040f0204050d0f03170403020a11060a08180c0a090f1407 62
    0x904442c0c600d151032100b9a16401c020358046111003112880b8000c5406202c1d500d40e05170040c2c80704805046200b260f0141c41c5030322540d20f008a10611240e032443c4801d1301c02042c10308081c4484120590171662208840f1000360ba46e03160341010407000306800c4002a8249507110001c9503010500b134005101040c10840058000d02224040004900008080300d01a83c41400c215891940c8070441ca40c807428003170400c90034211420106104040003800095407804822804030040e03403d9101c10340c14143c0364072a20041d80c032031450214001d105800d02901040f0901c52648110346203071034041d0010120301040151213004426009582c0180410700940d0b481c1c1030071004040d44481d8071f42c0c040e00035207415034411400300b0360848002c00c40c2d81000107054003c1003080c81144641040c800c0b20400104001c0c540c020140c5107400500c03a03000107142120752078a0b2118601d01c2804803a60b5040f0400010082d106982080791800c3d12044206030340b82d0b250041d00120300020841c0005881c0c040c0004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 944546960 1250 944545710 944545769
    0x8010e07051e0f0702031203250e09070e130c0207050a03020f06210f0402010e0621040c0b0a0509030c0414040f06021e031504020c120d020c0303010e010609 69
    0x30584400020f8000c00c07080030003080390000c507400307816035440d500c11441410085c3c1045484100440e500e02050751301e400150090b4040d1142621504240c00042c0f00380002418000c24039410b004620421090645d10740708103680c80000700c3c0b0007241ca40c07000b10f03009050001540c080c4c0c2c010301410b01d082c80140d40d2900300c03a8000109580560715109080320602801080c9145900620484424002004450610f41e845103000f078907641201d00702081403041034801c0d0203000001700304d0001c81c0d146c10342c180e048443c2c026000c2c112030b1030480d0b11580b00d03615940c03240c000d4001107040080c001d82c103400c0034440703d01d1088003103600700107010754010072a001140040009004200442c0004100160740e4140c82102c5140c0a01c1142c04941c804503510320780c0280c603204208034001820010301d2a050003250076180031100504a00d1400c942c00d5012600440c8074100c0c059020710004100c00340800c081c2d4024030f0000c030120303055450301d00041d1451580c1c1c1c00204207080d06903444d5220216824a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 944548210 1250 944546960 944547007
    0x90f03031415150d0509070801050105030316111f020706020609070e07050f16030c021804050727020c0601050a0f03120e13050f060f0f0306010911070c030308010e0705 74
    0x43c8689040a0090f0424a114140045400e103103041d0900a0704400000d8010603610301100800c0f43c8d98a03036080640e240210103071118101204400c85d0000b4032000e0103205d0b0410702810800c405002078800d0440c41c912991054010b90040314208045581001600d800a48050150030441c4c1080038103c62180024500c0703042c000005108550050110111441854603444803038074003485240003403c4111800090384a01282da07801c0002000f040012030140d41e0180040102e1840c1400d6404103540b98407144c06400f01d0341c0c071500400c1d449400100142c1207510040d04a039070600c0300f08410b085490304070022502c07818070140300003812941c2480720100030b82004640ea80402000a50540312001c101a52a0602c4148001303883c0d040320042c01007404441c070122001c440b83c03d004100784411110b80e45039002d0b2004100360034080c1e000341024070521141c03a00d03100f6103407a5540d8034110b0754801c0380024145401000040c071681006a0003883d680b030840d11745100000c41d410481e0007200c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 944549460 1250 944548210 944548219
    0x1030e0606042a03060306061e0e060a0b03100305070b18150403060c02010e120f04090b0a0506040608010905061f140c070b18190603021c090f03031415 67
    0x11082021140000da0700c5101107016803103410410000380c004d0180089100c110380d01e6080610114800400c0c103c026550031018402003000d0f49400190b0343d290001170880ca4019042010125040f0360b01d10095101da050840e41030811032951900d1480d100c101d0303020701803140080c817a501c0240000200707411082c04c210399981284507418145443c40c400e0760b1008180750f16048003040c00742d4041d0000e480e0005558199003044403008410215441010001025a981003005105400c282d40c0048042c203005001a80c1590b00d600100d6410b13401a0000c50200e03e40c0c1004004c507448a001d9140c0c481000e50b801c0e100581c01d8401c2d110740c0d08041c5c0046c0240b00001d5006203105200100742c6603034114403c1182d4400303903100e09003086684201c3d0100ea10f502c00c01c900d00003504042d40400c4041e1045105c2c01e52081c5001c5044000b5000f20380788440450081840c1c0d03903244540d00800155a025001c901d80100c101d15020f0111042980d40d0291501c08001b0800e00c0c414514011080540699 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 944550710 1250 944549460 944549471
    0x30f06060d09061a090c0a050f19020609060a02070818181602070902130509070e04050c090f0d1104020a050915040608091b010f2c040b01030e060604 66
    0xd006005030806160880d207899210381c10310400b41c00031401100c200d8000c2e0700480500b014800b00c4002141c0c2220001c0f4200201b03d0030a1286004001c045d03880f007001414240c0b4801c5101c0901050030103000164405020b203c446c101c10700c80250003d5001d00c08605d020840d42d9142c003103008100e00284441d03907113840024180c030707450700f0040c4400d0440d2142440d0314281c40c5400300ea014031031160006100c0d003880440c0501c007610840300c00d001032480200c6d505150204000849000038010810010501100c40321611f0302d0046038001d074403000f12151103011007802e00110048580a4030704c01d40b00ca0b070307a003004994021300308111002e0a603005640c5454040b01510140b00d07a244982d0401c603210b00c070160605052028205a0304603603100038084d10742404090740d030050003c1040021031412204503456005030f902100d84c40043c01e00f1004000e200b0341c0c00100d103800c0420080465074149140040b031416200300c00d4400001d080421003100959801991080024001801a607484 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 944551960 1250 944550710 944550721
    0x20d0206010f090c021f1b11100c0c05060a0b150a09140d0519140d0f0c032006040203010c1701050f0f120a061a090601210920010f05030f 61
    0xf131151707202c21419030901c0756849406d180300200500108200c01030b0510701240105005104038076078071200030541c0040410200311072503075000b00440d00c0101d003445141640d0200203481070082034032540c01c0590005000134080244040b84021210003070314560704002e1200400c2c4c101d40c89000392a10b00c4400d500c40c04072080803c0110480c104098454440e0b030550b030051031055650000300e43d116000a6012441351002556241c210720718442c0414000f009404030710744901c1c04040f0090203031618075040702e43c2c807a042610303c1c15544281c7d0140c200c8020071040d41001d01a00e80c102ca00307440d10904191502032800765079201070282030310070542c030682c04849584400322141d12034002000d10030130b084501030050780c62001b004129507050409621440c1580d04050700e0710a61000b511103c40750351030a00444189101102c64034013a43c0700d40404112540900c41c80140d00d1090559000101c03401e414014402ca042d102281040305d00e6000f404910790150030f40360000080d41415403240c480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 944553210 1250 944551960 944551963
    0x40b0c0405031603020f0a050618030c12060f09030c21040302030d02151509040308060d1e0201180803160c030812011401080c0a0f2d020d0206010f090c02 68
    0x25030303000e039034548601c100e20f1403a01c0f60000f0360404c4030b100329104000c1e403020806100c0d285101c0d1055a9005200b8882c5400209102c44003841510008080c1d5810180010000399500390880c06406107a00141c20845841c103110880c2760040c0c1840019401c1419202d102d95661032110308141c800201280010f50340760b80841030307401541d8011f09503000d042542074029500e402d048840c010300064107012505408910500c01a140800f41c4207002c00d580708c1d10700351000368010340317580d81225580e20000e010514a14540149802402d132b60704d41c10300e00d800010701184601ca140350810b0f10001080011841c000101d5202e402c7d0070465102d91711190912001690081e44040c0c2034480000d0014240d40c189402181603d14200c0c0d03102101855900440d03419108980d0100e06100410218241c14021455001440036916145000e031940390031900c0c09d1341c0f440c0610003442d1404108500041c2d010301400c0c590030180c0c802000103616041d4003000a451610402c0b40040e5102d03070100c0041e20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 944554460 1250 944553210 944553217
    0x9021f02030c100209010f09030203030301030303050606091504180e0a24050901060f08060f18120705010c1b080910030605040c12151a0c01090b070e0f0a080303040b0c 74
    0x30980182c543c10001021914007070b50000c48514009102d07031840000c8540510309001c180d035000b0700158103581c20740c0e0701903005000c00362000b90300103000c1c0300b820655580e0b202c5880100d02c5106045498602d81040f92100307281244071450031500f08102d69000b441c00085820a190b0072106070b400400e4022040300909129000c08030800d07090400308845d4400c1500540111040d02c020200c0b0700f42d45801080e203481c0e054032451017005d100313404502481081000c0400260b81e03202681c500e0450b51301c1901e0706511508007190203945401882c103002c1c0c3c000c14841000c02c481c40c1d1400c0303c0c1c0450790750341d1202c0c801d003a5a43d21070381e081103014103020303c2984070308040c0c20081c00401010180c1d10002e8055051581002c0c1c10f030b810403055004900c9584000e5049805001900d0000b404038070006160740c001c0302d8240125965440703290085001c4211b02c0e405228561a0707500340300700d6030050003070f103414400000c0d010307120402c020415000c0010442c0d5129402c403183e00c0e030b40e03160380314040700511 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 944555710 1250 944554460 944554477
    0x12200318060a0c080f07020d0c020a05031b0909060402030715170103050c0a150f050d02070606031b060306060c0308130c0f0e160509150706090f050c010309021f0203 73
    0xc40d00c420000c00165943c4542142e0f84551124003070360303807070b1a08400c0c41d40d001c6905600680282450203c4d01c2c0c041c8075021515807004040c60100ca0721000400d282100a060040c6072411021410080c2d09281644640041920000e000030340781580100c6c1c2d41e07011500c50502c4274050382c4c030081080c1d031080c40765020929000740d0011a80d41d40e414510703070310082c0400301c5104001c4c202000564072009880584c03411119103030348030640c000045c01d80319a00311107012280c02303808000f11000074419208000144d8801c001d0703529660709080a640800740503402030014540b0701a0148031440e00070072004420f69040c60400040d80e1240c003141d00c0c001105400030035505000700082801000344a5450680f0030200c0011441c1e0703601032034502c07540c00001d03024002c40c40800060281c1d0400302c800c0c0c00815298080742d840c04030641e4644003100c403146001d9504811f90040542045400d02c42026806824a42800050240e0700019401041c000049046004090400d195035000784103985000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 944556960 1250 944555710 944555713
    0x31008030a110c040509060705090604030b0f071103030408030109020903010f0606030c11060f040f05070b0304030c03030f0b090a0506010210020313021005040e010b16150c12200318 80
    0x12440d407007001d0002444500c0020b0b40d4054040d480c241424103104081c810070908000f0700392602c1e003a109643c90b81c0308542541d00804204004001300b009000c015025100c0d008905920f8601190010611021240119042c2d041001032001284009080d04c1c195522400010399601041000034010b14140603c1c182c0c20f8100580080d03031035010381c0483c10721040c80d1900c0190554500c0455143d9400f20740007403082c0901ca0105001c206031000790981d50744600c0031110503540354443c909031604200c030120005140403152000b0141c3c14018914881031030341040c850840d501f00094103c542c028500f42d4042c2c1d42e40001403841c2c0c070800c808810180070901c110760707070b081440c242c10014000d145c0c281c0c01019680881d0b00302074411021941183d122510004031642000d102c090142d21064213082c0000d00b03184a00d0200b034610075071451003124120001400301c40300001800f5444c0710703a0800000d034505500800c03855a40103a070010114458416540d80d5500b250722601d02840c02c4543c0e070349 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 944558210 1250 944556960 944556967
    0x190305061318060e0102041d090109140303060a0911160501060f0605030109060b1c02072105030f0f07050913060905090f01060b070f11010c050f0c04060b190503100803 74
    0x612104414000b1a1030044006009a110440a0a0030b03032141d4400c1c20b006c00d041907040362910801d031140c69001a043c4002042882c0141c8500c0e403011f99441c822045508000203200091400300d484900401e001141400130041948030b105280c09544e00c981c0b03a0207401c168050401070b081d44030101901c19014450b042d95110362000300a50801d014200001c0d281050104090044000740c5242900d41480465840501c03607461021b50065001114940f0081007440341d00150300382950b4001d1515034a407522841c1040403008862009802d4401c038500403421301602c290300130102d03401c0c0d078800d9031240308101c0400481340051485a01070507016141070244035401e01c01284014600304080024011140c0311003400c00e83d0701c250340b002031111814041d120001059419980742030001418103030600d04d51904c03243d044c02d407184091082600801c034846524a041c3c03191801620450451a041100511143c2200c0b14141805814848007100255400560003000c2c1e0140040b41c1c00e40e500e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 944559460 1250 944558210 944558231
    0x2011806090602010f02030f0112060b03100c021b01050901180806010909030807020d090e090114040b0703150b0f09130c03021806030f0c0903101401030b0c1903050613 74
    0x41e185010300070065007402891200c031416030007980d0188012100a11b10359203482850140c0c5003030150121100b0751900d0171141a964140085031949d00a910b01050580b50140000d0929807601c000c1c0d080d48511041032811645e0040c242e84401d0001c1c01c0040d1074020390700310030114880b0f540c0031002a2042d000045820340321608540c4603907100391501c1c1001d1702c0b0514140c0e100c040000b800c100041d40c25504200c82d0402c4519a80c009a234000005894152118030f204d40703210848055418084090074048111380c148030b0344022000341b41d288a44203090203071211591103104400c0c009c4101c04590003c4556a0804112900710300000070817041480c030602501070341000305441040429030469031303524141407040300c1c450310880c4905001559504030410780c5401200300d098040c481d04142d030048202500c9845400041e21b0821000c9625510b4080c0c01042c0040118031114024005844031401544842920020030700703000c82c041d5949408515168000c640040c00d15090030101030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 944560710 1250 944559460 944559467
    0x190b0616050f010e0d0806040f020702030a0f0c1403100f060509090a0309090605100c030207090626030a0c0b090c210d050c0a0305070c0b0304210e1c02011806 70
    0x1403101d6080c600078003400061640407505c5050000100700480c1103500004c95034030782940070f146003e14210780107080642c107030080f0385441c0340c0c040c08807087c091400c0321100b4070035003480290041c00296000710380a420303900440e13200e0f049580303070340d44580e2208010703441c038403060b00000098000136152103101c0c1380008400b90b403400c4407881500802d0040388085034041c000d000f070105440016181e030080d074511640c00c0ba04202405c105404600440001203028041c83c01190010103091361240d6101d540a60040580305002c14030030a03680c420004994001d400c1f80038000c41c1604030034248890303610303604107600b42035142030f005034885108168134a6880c8446500e802808d0301c4011150002c07041801640c2c1072141c4070720800254030800641d40003d1144000341031213485200141c0c8403507901c40d114a02600259412030345522400c034249210640c1d6a1614042c0200345880d2511203040808288000c00017440ca80f1540038020110086d640246440d507a000b1352400c5841d441d540c1e622004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 944561960 1250 944560710 944560723
    0x2030604050a030809010506011b05012703020c042f0c15042102030f0a091208040e07080c2703060403080610020304142107090c110105190b061605 65
    0x2c0b0003107443e4101117007510405114143c414001a114080800440c1407010000c0965480440d401e6403101c10503140c840348028600007916086006009420451030043c1c01c100e0010201401949440000703006e001907042138000d05807000491a23120000350040f10dc4c58450784985004c28454851240c92003940740c104c40340315074014107020503109002044440c401c203a00c10350000503441482a1512102580000e25001086040420b41942e82e455003283c81c000050b0f0544072500c000c202046100004e94480d0340c00000761500071014079084103510103c0c0580c0e21901d280030103d44801410910040701d070340d9a41c600a0460b07110345090700c0c0c02842c0110480e2058080d2025a038005649400002668143c8141c1101c0c540c0b41035503082404104141c0103441400c00c0291a02090b00c042d090110b000542144003010401e5441c0e000301501d403031240001000c45d68541020040507800010440042e1694403101181401d0041c000401314014162904000d88054070803038100940016070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 944563210 1250 944561960 944561963
    0x1021203070504231e12070806101205070303050702010504052d040902060d110910080708010f030b0f0a0e070e06090f06100c05070b0c0f120f04120f02030604050a 72
    0x480311140c107296184c1c0246040488450303089100c1c0c48040b10300da001c81300801000c0601400010503220350300c0500e0301e030200c40d6102001c9030b0809410721259aa0a00e2041d0140030f0140c04403051000603542d1596550192201500704580031407040304580c854800c0303d0003000f000701040099002c0c0301c2100b5a8135901380d907c0c03403404a800c2e000125030401d0300503800903a80003052503041200c240a081c0c06014694110074440000300310030150340d6640b04420100c0c0030170b40e079212001d19044c9030140c41000181c020a11001d800101000001e9000418682c800703025408031107542c4440719240d0141444804805a0b4050f4180110b40036044d5060300d8400c03001203980003a59200d44001c51240d04080c0e5909030041000c01c05191903500404240100340d20810454504c50fa840c1c41d502019005100001000c0d00410840902040c04000214601c400328200f0b915101d200d01030541140300300c1c0f0a90f25132880c03100300e96041c05002c4140c1c4103c0c0c0d030050305450051400c0e01e01276448a203d01d10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 944564460 1250 944563210 944563229
    0x61f17030a02010b0901050d08070c080a0302030c011107082a010c0c060f0e0c0d1407030c051206010806061908010c03020a120e060708090a170a110f030a030b01021203070504 77
    0x4c03044803843c0c0500d1480c100d80300135081291180d456110000181c3c0069026101c40208401c00110001d08201d07042d40c503402075000d19203030606441085d0070f47d07158184800141c0320138001d59020078010011144486440761610b5201510072414640141e54185030400952810402c44070544d080802980e50700d20645040050603c00b800035811624446101d181a1340602c464541d0350a0840c140240140110f80c0d840d01c40e6070010f80c461070260190022200310311402410003040c01c0000500d40c0d040c1045016085545c14521001c0d035550300201354600c18025081c2000010307640703442d01809083c914000b40301d1140750220140296010100a03c005800000882d5020f1240d104a104104420000d0600d17070f203e112045a2010380a0403d0f00c2c83e0103191f407440c0003e00100302907070303043c0ba50b030280035100d509595020f0b0048845d40c80292140e0042d6800c49082c88001c4116105407925050014000c003043c00100c0c6403000741c400c100d41e05a00041130100305600b00d405481121075504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 944565710 1250 944564460 944564471
    0x70f32010e07031b090623040e0d1b0204021b0706110705010807030612030c0209090c0d120507050d021b06040602061b0d0618050106020708061f17030a0201 69
    0x61545007241d0820000e80c0d0309800101c0b0500000d994003400308007510341041c2080c0c060303444032560022a0425030004020002c0c0350040300b0740b441c511030046000304040700c08104401c82d5180081d291060311805100304040541d0040c1c10011034582d00c1106600a481107403105c20059a2865192988070000b40078410741d44005107951080f6001003da001e0b1030003401c0f5086c40d250040d076018034090072100c1415203510340411507140d4590440d06071802962032487c1c48905006020103d540900503c0c029041710040c58000e071103030703503c00038020b610131945500052904000c49607030142610050850050302a1951215070020b0300300014041e80c40ea00d82e110004c94108040c41c8198461000503801c60b0300010340112105881c40d00056490701c0c008e2602c10410340341d000301c0e0516042507031081d55446000038803581d14461540944414002449900d08080c0c84690b554402080c4d01c01904510103245c007981d0342925440d0091582e141003080200340c000f882d944a42050000800640c40d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 944566960 1250 944565710 944565803
    0x60f02131d01080319120f1401090b0a0b0c0313031a060303211302040615090f060903080715090c1d060f0d080f030c1c140c070f 57
    0x200658126500394004601d8034250031000001172901090303100c1800294800c43c0b911064a002d51300f01c0445032100083c40d120242c000280f0004180c1260001354038042c072402d400c0e100c2d00c20030410b0b2044405d9013512074801031201851485007011140c0c60304000a00001086103102500442e40704015080d140ca41d65030050603a2030141ca10b00302e0020405043c503401b144942c00c1c0c159007108008002c282e00041c10b40116054070042c0c1d00040e03101c104240c24030462a845500c1030302800700a10895003c03031500b00003c1c07000e0f81d0f0b8000502412800035840c010010881110016040303100c0003800101c2d013900300141c00004510a032907002d107003400c1d2007240441801c032483c441c030b0004200040c008144001d00614111f009000c03210366000f0040080401030340c902652048403404241992020601300f5620303809101c400300704502e41000040345000c891041c0381d941c01442d085000c0d460381c11130304245080305524107014040e40980742400c1d02a104e0721514842c40d0f46c10380904c40750300490 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 944568210 1250 944566960 944567009
    0xc1202070803060f030a0605012706080c0910080109050606010f03020c06071206080111030a0606080903072012010b0a1a03061014280305130f060f0213 67
    0x4640008201d08002c01c0055480d151075010b9a42200740030b01101e0900b40c0a982d20012168203800501d600e02c20b2038000304000c01d58060b16103003e00d1903041800751910308950305945e200740800041c400c00145000803260094070509100810940c0020b1000484508000b6101c07442525600c1c0003c2c007050818425500a00071120010003078401000c8680d12000c04542c184020380001034400c1d1150360020b038200d402d000c1c2491450b1041c1ea080d541e801c22113020812030b036180d402002440404000c109000310007105445417507070080201c28141c050300e5401c0f4064100350900c564040050400091142c03415403184c80900c0b02540c841c1005030700c400c43d1091041011108040701d403030400001d034040c1000003961260b151241442443c1031420400f180854000061045040e8007107600e44410101e220140d0305220301500b0304001c03905100c012000310015078070000c2c0001c8a000070174401c00420782d10003200c0d41c1030f02c40c0031505e0f2840c660310400582818800c61680e0362250245034021000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 944569460 1250 944568210 944568217
    0x70b09040b190303172205010b121b030d2c0406080a0611160305090f21060a061406090a0b0310030b06090106080619050904030c060f050c0901030b0a180c1202 70
    0x1a000ba40742a1220090617283c40100d086c1d40440f065501c031804900d944e10b900ca420602c1d4180307100600f0460751150001d11028094040b1607210f5408056401c904e00e0304030845118903038414004070201951402a16084014400c9560b0400c0c54044002040745001c01c1c000c905610031201032000b041e012030030304403500a40310b016003a000d01c1000c04001901030001008600300c085c0c86039049800c0d403400120700740881201510100c810a1001204c0c0d0400e01042303500000580b410010b41c8c2c14001901e08680d001000345001d6140080c07414003941c0c41030008402080324510306960b0386043c00348010800b02608c000c440e42041e03d00400c20903e4401e0419040e41c074241c0d4ac507406a941c884c05c0162510051402c0c4440c54000d500110781901c0304000b091099000b601c40e100000d00724a4502c046a1420fa8003248441c90041070160040c100011250820310919003c00c07080b10940003e49405e6441d484034009000c4903c8014003418141c10006e07402130f294036002500348001901d4400d911 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 944570710 1250 944569460 944569471
    0x7021801181416200f0f070e0711010e0d0914030120032205010b011115160318060911240f0415020a0b060111070b09040b19030317 58
    0xc0d02c8a000540041d0815031050901107180780058040f40030b0b440310702c402d9070048100c40c0d00d030304881d1122415020401260550300c0d0308900a107861444c00d801e412035150041c005130304024901031440f41c0500c00350403141220f11715000751080e03400c1901c0e024154031560700c101c1111803592843c448a80c034040c03040000141003121104402c001085807400c941c0d1000740010101e03240d0100d4006084400c86404800c58418400064540141c1001600b1400c9000008080b50b0004010440c510403500700c00350461040c68030801007109060307090b005081c0c4500c2d40c0f00e86050860401c400d021040d04441c0381c51380106800c034442c43d024020312111030041c2d03201e000ba00102140303402c10341d05080001c0100181d4031810300d0820707859066040a00c040f0465450040c0e000c81598001c0c00040f5040369003180090030325400c03034001030142640705c030340d06e10507461290307404070f924040b54440d50007444c0140802080b030b55808108042e1f07500d54002070f000c00d034009007030003098003c00001050164041d2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 944571960 1250 944570710 944570741
    0xa05030606090103110d060603050a020304110f01020705280609082802040501090f0b040204060e060d0e0a050d0e1005090d061e0902090903030f1602030702180118 72
    0x65540038103014071035200705a05810540d0f0b5040ca007410303070b4903070b0050580c141442102050300344c41c0c00300050544001030702441150740704000b8400000c40015070300555680a88000c00d0201e01040180d0810a85600054101c0711000010740c0f0801c2000e40c040d9031900007040071002680701c41c02111003990714090b40105038856010905040309801e010041c240c00e84901c0920210241d001c01d041c1c1e2403c0e4030240c012900c40c404c025000c00030340a00b07460344809540860034603182110090180d80224803c5000303003c006548004140f150b003152544000314011542c030320300245400d5641d4086403020390000340310049a65003920340041d100c40c0c09801d42c0c3e54542001e80200402100c2c070b04018049901c0c0350365101d803e400841d204450010351495000000d410b94050041c0101d0300e20050810416800401c1005405200580c803140c12101045040d0090302510000740c0c45c521540d20040e502c6103810030b4000070701c85000d5806040c2c40e55450700c510501480050707503059408020099211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 944573210 1250 944571960 944571967
    0x9091501030f0503070618061b090501030f1d0c010f0903030203190e0d0606090b060f460e0f18070225060207061106040308042a14060a05 61
    0x10800740b1044100c554000e20559240c52542d0342e0302d80440ba0003403080308a41c09035515100501901c1e02c100310131303000105101020f545010130010006d01540c00340c40e06155545080e24044111036100c0c039000c1c000c084601c501c0b50200c031002a61400414400c900042201d800f0a042d280b00301c1c0d89008a9915400840c108191030300042014039903580101c04008945c5030b40b0000c3c1da50001416141401641d00141541c10542402e065941924113140114800c02032161000c501030708440300c0d03e681000c1380d10040c40341c145280c024841c58050710b070400341d040c0c88a000d00c1c10b400d00c40403c4030110b03202c600740701c0c44100c02c2c080c0b0403000d0807960364018400c40241104045662982da400401841070f90044405690054800c0101c4400444404003896050143e03075010880c1b60080c09860500d000307401d0003242d4540c1d890070018070040c100f211401c04202000400d60021540030001c016400c04c07041503141444103455280704041d5516400c61021001c0d0400e50216113484020f5030f1114034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 944574460 1250 944573210 944573213
    0x102d05190302130b210607090612091403070602040513050c09040b12030408010f06090b0607060c03111602010f26041119061e0e010810050a060207050909150103 71
    0x1440103c0d104005030290301d8003050612030340d46800d0030001d60700c40c1e00e200c401d42a00801071840c101d4020b00303413808d001d01c0003001e01c001d80e04500c1c0026032848a0701c0c04188100b07075142013010308a580411242a00c004584c00b41041560b801403c142d807000c1c0c580d44080c000032552041650b0054030f864046240410002c041350816411154940d01c000c1d21001e0302102400003103141d544144d0140b1040c0c0d40d15288503080c45050f0259000800d10b0400c14015000c03408000741c614070501100a05403580da100300d07a081406034000c40800c4840045150711140307008a10717428801401c6d001c0f070009d010710941e992041d015140d5401c186204c0c50040e4441c1d040401d100b601190050b20566840b403000c840c3c602c00d542d07100340411880c500c0f0414400b9652410101800c0048001c580c041440480964601320582c02403042c1844502442d00300c085442d06040c4a002d158240c110941011074010b010400310340001d59001181c409607001201e5645032620152145483c80814628441c010700400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 944575710 1250 944574460 944574469
    0x190f080105010507210c15140112050c21011b081602070e07050a080c0a210e0a0c1508040206030a0203090f07030b0106080726102d05190302 62
    0x92801d00c1829003460b04016103042c507401c3c911702024070300041c401e00b88030f40030090100005200d648190340288113001180040c5054404140238000300720440422242c2070003400c100039451010050700902ca00301210003040100d898041c5c0180302c660900030100c480b410700750040404803680e595040304a0302c600721030b4280b40d414000d8080851154040c0851480c2a80115901500b0700e41ca950b996807680c0480503051403402418081240c4080c401c05d2200c075004816256100000d405461010541d4840c1200a140b4481d4101041c4996001309041020014a00003035820241e0031031040c2c2c9643e002101c0c12030301120002e4100409001180a0380b040360003a603000782d030342410b0700c10402801010518000043c0c3c42600d40380441d10042001607088001c1c01e4000d41d20f4641b11005141c00042c1a01082c0f20310000c0010f00c03070b440f001490181d605501d2002070041044407071003010340c00c601c031403085018416080c58564048400246842c084010b0840a01035441c4190388514540800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 944576960 1250 944575710 944575717
    0x501030c021609050103110102030319051b030f100b09060909070c02060c0601030201140a020d110705040c05090f0a03050d12180515100f14060f0f190f0801050105 72
    0xc0551003407103904503001c0c9590603032038041d01c51440700180543c9075050031281600b0307090045042d500f0800c18400d0f014002e9104017030303005580501050307a441d1340c1c1100280140d80e0300f40b1501c40001009105c1040207001c150b40c052152403100108894443c40c00040b00d1080503035495003d07070204020481d0f410000702c419805003003410310302d496090940100e4030552140c1c2c030440007030300244010b00c219a040310742c0b065064850703004e0f00e0411001c420060350f01d0032400342d07000601c00820010324880c1c9e010000d900260038064030500480d00d02c400c002c0d00c90341000c00300c84c0c807517072301c5103804c007810b040c00c48415045070b400100030a0440200082500c00d005400b10030004c85031100e600d10580040c01000901482c4180c004100710507810454900c0c407540508014404454080c1c100114862a0180c5c0150f444035032a01a58000c60f800191640c803c3c0200c0000b00d2002090000002d12607802030515a0114030b090b8690800b103c00848041684821450102d40c02c68014041c951090024 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 944578210 1250 944576960 944576981
    0x906040305161a0a081506072603130f060b040e2b020607080901110712030c080610032a020a02030d02010c05030703050a09020909060a0f091106090303070c0b041508060a050103 78
    0x101b96040c490312000c607030300c2e5001540940c1d050a0301111a0000d41e80c40b103002500c44043d400050550400303d0740182151603000010701001c840e844105c0c00d000b0306500c50450407100500c10460000940200b945607055541e15402c03401b40c021888c140080c0140c040f511030301003a40542003da48603207098903203074030103000d24003250341e04c0e2117030036110402c10001c00d4114003072000c1980c0b03807000074002000c1e100c00c8492503081144c01c0c001d00c043c1d07840d10360780000c0c084080c1c14082401076840c40c0c40c14a24440080121502c400407210b1003040d41c000c0f80215007140281c05440103c0c034185801c0e400e03502c410943d038002620800015030504c3c4031f0b034070007a001070000d440400d001d26990001034020400b5201d45600e03810440c1408804601d6205e680b000d0f20480303070280401290b40d2550b10802030b28011140c01148002515051950103200310f440c0c03075501c017400d2070001c0d440b041d4014a1790805e0103024100382c00c004005040713031301a044983c0300740001059041420b00301001180079082a20382c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 944579460 1250 944578210 944578231
    0x20c3c150403110a140106141906030c14130311010c030914010e1002010e1e060c03040c0302130506031624091a0c0c0603010302090106030509030906040305161a0a08 73
    0x40d900005000c5e2106903090400500020070014100f002021184d020400000c0c0320700c40000c8a126800701025407402140c4c1d66041c006004180b05106480998042600ca81c80f0900090810010b041514814007500d00030703101107030194407510055522910005016012510746c2d00100229180354181181030306040c949003c1e482c0300600410603144064401c3c0e005030b511144502c61000d0200f1612101d6280c150207581d228514611041e16210040e100764001980080090140685283e07103000555000d8181d01c1e684c540002854010041a680d5910030300403107a0111072010321005c2c10301511560b91104203000c441d101c0100c0040002c01440c02804a00d28001401409600c100c2e4407207110b1100440c1d135580404582d50811200d0801d05100e08414401071000d03031030781c0281905680ca5400c00141b0b42c0c50380354449103140907100410ba40401e0004012040040104800000b12100d6026051260700c4001321070050300081c420100e50641408034981d0389101c0e001c41c2d90084060712 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 944580710 1250 944579460 944579473
    0x40b06060405090a0f0507081e1506070507031109011d0a0e100603031202130b0a1101090809090906010e060613150f1701080a0204020c3c15040311 65
    0x40202e010b0031400c54a0410195958034170324542c6140d0300503240d203d011440d150f44146849a020f8440141c0701130061440984040014008500302d01c3c607180d014402003203962030b0411454055501e1660340000ca41c801003601c0c0680f824180f50303006a0690300800651003031b182d829a0020800000142119005030725003c5410701200c0500c00d40403030b10480d10b0007040071030a508000d1f01302c1c0c82c1a1050b40b4103a204002015040ba03842c2c1450042d0b07070392140c205a50b601907d208031040007250525504a5103404c2c0c00c0030801481200a16a6043c2a14a10304c41d1740d60307011503030322401c091044103800d648030700003d5880e15119005010309510a040207200c4d070784540085c44501e09603001140415100089488456007290b80101000c1c009000c2c41c01541c1030001c0c05480720920b400090103a034001c00c003e103a0501c180050010316844190fa404030b02030050440d8540303101c81c400d6803000c842044100445820105055290125428546480361565502162030124401d501c0c0510f00401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 944581960 1250 944580710 944580719
    0xe0a0215250819020307150b0103061202030705060d090501050c040905090d1d0406150c060612080301030b0903040e010b0c010b01090524040b0c0a11010314040b060604 74
    0x1820000100110862152201c4162100d24110150880444407224250100c000050030b00e03412115400b25403568009907014601c0d05916600524070001d040001c00c2902c00c000020592181c015644241d0302803092039030795061103251a29610f8065019001440148001d003848002804102c1c0f000b000020088041d0301c6150859030165600305c0030b18000a41080496001d000720340d08142100c0c040c08601c05607040150072820000c4038250503007101400880349503103a80c80317040102150b1740a404405050b00c0d0040c220500018103c406c1490401d02090010806120314103090b44201c0891860b402e5459462903613800410204a133322003000080b03605810210710700d008000748603a250711070f540c5140082c29110142071040c10449140003c0200765100d10341c1d896900160310380301101007104106503e50b03101d650010750083c580010038800441c00000c00c040030074000c603084003080100200440071390740f039020039000382c403e040f000c900031400b408440c42e00440001c00284c50103694 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 944583210 1250 944581960 944581969
    0x3071103070902070b0a0b01051617070b0f07120e0c06030901090807080315042703090806090f060a110901050a110d031409010b091504060f09061d010602100e0a02 72
    0x40714007203568031803c030107120100d05540542802c030351f403d00b001410324a181c1c40d8201c0601e8821405841c0400581602041007501d00c00c403a101d58022a90008034900740c01241d444070426030b4000002604008640706080c014424001211030304400307414681103210030070040790030140002170700355030b0341c030703102001428500080c40c0280c4074251084e00e918102c0c243c2c807004088088101d00036070801c0782c0040e080071140f500b5001d451107a01081e414070741900302220b5901c0c0c0360300314035101d11854050280c0054005500000440c01c3c000f00e40f0742e40d558004501c00d40d102c2c003612860521052000202d01d43c028405002e1550103803030403040d5070512094540c646100b0400c0c240202c3d503100b400180940b81804900da008000300000c1c40b031030003620046180c1c6100208040603200c50b040003552107540d190003010050110000072481f080e29521180b00421180c4104044240c0b02c841010b494200313031840604071a030302d802070084a000800001c0240001d00441c000341c0c0508848403005944 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 944584460 1250 944583210 944583217
    0xd090c1706062d04090609020405240a03050a020d15060608071d0306181614010215040f06020318010c0c110102070f12020612040f050c060a0203071103070902 70
    0x4140101114140441841241120309101d07a18030900d07201c049003da004001415070b064415074001030900c4480c24401d00511018100940c094140006e01c0304c52800000101e5010700350b51a10092001d44200f003191042a03440010b08540003a00d48070003515050031049400c9001c0c41d512900303104075044400c2111200c0c1c10400100c0e86401c04d001100398840041000c0038812030500d0403540d0500002031381c8240c0140460301d000c4100381d00080c20361040c022004020560703015501c10940b100000c882100100345014010b00c0342c1d034201005682002071240c004c50f00411079052946440d01c402d070203540020520520540c4602c0c03813108500c401d104483c158685540c5034101403403540380c84008080b0340c0d400da0341150b10240081c07140b100e40e0b04203001280c90182e02c1c50325140a620204070280120382d51a03c0c0980c84004000600601c50500d003800c521610960b920b542d2003004010041c0522441c02005a01c10310441c03001401c117400325100d0050080403038569941e40c1c11040c0580c1e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 944585710 1250 944584460 944584499
    0x3110705011b080f0a0e010e07061d030109030c0305090d021e04050106051e09030a0215120f0c1c060e1905061c0f03030209060f0c061b0d090c 63
    0x307540709040d000d00c0a42c282c82c680300491a141450480c1000d160150b074521000e050003084594660980c06425025071005c8901c2000000341c8401d541d0b9828060101c44036083c04410a18103280c0581081c0742c18801c2c03ea54541c16121444164565202210079800071b421450300036618a12100c003580d40caa00c004000340c20030300c076500010580c100384429241c042c2e20501c24404188440054840056041481c4c18241c003416903c40c0d2540000910b841c020a0000e904105d01004004590108134000d140c016020500311400c0e8848007100d500d1000c1c01c43e0741000034030b0140701801c84010300c054202d800d0300440c1c50103d0380540310144030f00c80c84401d80c0d501c2d840e6003411140b58460007090140681c45030007110140d10781040c070400f031041025101d00c000c20941c00c80c580002014041e505440e00814040d14030741d120040407104c0c01041d445503101c41824810500020421181d00110340740e0f1800c0b02000c1420118a819801c0190901150480300c40e4503403540400c000c0d41c3d01041d100d002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 944586960 1250 944585710 944585713
    0x21031f030b01080f1b01120603060515100f02030915121f050405040b1617330f040f020903010207060f050903070c030308151f08070c0b04060c03110705 67
    0x10b51602035203a00d00ba610340860700b03803900709418641348900710a80d000384040082c00e00c0d5074203040c13174100301004041d25000101014a081c080c4041d114460704514a0414146c41800e0078410141003695503a21100303040005900c1002600d48504000e42d00442802080703903650b0030000c203042d40812004048540ca46860030400404601c0d00e410f608840007818182c0b03003008103040585034070300f40b0180140f42e40c800940782d82998080e02c0c801c95103032244004114034060241803203980f610540c507180300204411182e101113020407810f20303084080c4440000300001ca602d1003000501028240c81a2125081503090000350003d440a00061803110310402c40014020480501003048405c05021a481d503882070010000041d000e00d4480260394050406a20541d203041642282d142210142a002260303003049800000440c03410408011040e116011540d40d8030310115111542c00710040d2111290300c02103000f1a2a0b81e1240c050081c60340390204180b0600800ca911a41c001441107415 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 944588210 1250 944586960 944586983
    0x1061805030316020f060406050708160c080d02070b03190b040605190f120201020d051e07030320190503130b0103080a032406030e0c040e1e21031f03 66
    0x714075001c5505e020f8041c0c21140181028284040101103014070580144030307210000b500c94005864070b03d41050664401a052074064407a89065212a440441c0002520031b07030704013203441c08403d07040da48100b0180b9881181600d02c5002032004d001702210640e005582c8110100d2a600c44554031811450b10f07640b90840a890880c401c0f220343d046038804000454150394590050381d0124002c5807045441c905107403211441b008000d55030307400d2080d038076121000003030041c01c00d034054011007089042c1505000140c55204185c0019110b0880b201c0c1032068400d149d040039a0140c8043e5400c00039491100b401e400743c591321202e101e0000c0c0c000b5a0100000310300000204e506001e4007442000740403404200d007240d030580e000c02ea041d038064401031644943d000b20042d04104035086151200400c03c4c04404410580b00e500d888071001d209066074652901160380c58800100754190030b15400d202c0724032890180e0200c0d05a0800380c080c44502110552008100388044002d20140d800f80740340041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 944589460 1250 944588210 944588213
    0x80c040e0f1f06021e0d170a0204050d030c050d0c1707050c03010614090108012c030c06270c0607030e01090b040807090c26060d060e060915010e01061805030316 71
    0xa05c00002e280b50310f81c036031107246e0020f03041d5807102025011668603d20b0025640321404020003034001d507080107412240200c080010b0581c001c0402030740a02030b8040d5103100c4c1700110111040440d064028001d41d00e00c64041000150360401000c0481c018419140c0b64500303c40080d0a441c1c8941c091200f41d0035120803146e151038461002801132843c0c00c001c002e07e691a80452041c1c4104086030000545822198141410240200c1d0694a4080282c5841303180141c000d44900d0402c05007070b10304210740d40c442c6004010004452120b0b8900410083c2840c910341d40c1120780b1402d00340841c1c10040303807540003c0c01d034140d8009000504218005480d0319420800e00787c0c12035001741c0045041000c0401c02c02001484070001004ca0b940c10940706a2507074400001c2201030407942030007048a0301d001c02450031103c01164403801040ba01007600c1c52011a009400c250100a01613255440500001000f43c180200c440702050f5000a1030a8002543d03800042d0842e04502c13003011b20406051010340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 944590710 1250 944589460 944589493
    0x31302150d050108210a0e03011e0e0a0206030f15090702251203080603070b040f0806060909031213080708090a05060f090d110a06020d080c040e0f1f0602 68
    0xd01500f0340c00c009001001d40f0712409205d1005180302d050b000c00002911a01e0a4030802001c01d04403400b40003404201956520490000d2143c804000d079589000000040282c0104411040c550003c1c5140c0c110340382d040040c80c075090041c1103010a583d02e90052042900c50b4100c652050030150042c25803075140c03490700850020302a07410703000641021418441e52a4440940070340b25003528101d100c80d5210404246800e5054110350b05c01e03c0040303000160f41e19501d0113102a04c41c8882a11800d407503400c14490001002e8450942c0ea41091100c901d8410031281803641c44450380c00b0850010034182c807a2041030388079400941c3d0700030002403100120b00b00300300c540c401440c0c01e890306841c5c480d1140032400a4080c08503154400d030040006174003842096001003c1c00c02c030003041c10710415540c55003c0c0d65080c1a1000d2000f1610260010740d040ca9040d00f550100c452445000105989952107a941520300601c0c50303508a07150490060781d10110450b40000c0c00c040d0700201811071152a214 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 944591960 1250 944590710 944590721
    0xf040b03030717030f0f0f0a0c020c12010c180f0b030403020307022d030a170a05040518010e01090e0309040207140a030e01022e09030512040606030204050903070f08031302150d 78
    0x480a00300e018022042144047c5643c4a11081000555034048a00403418944500d0480d507104410b00d84d950350404042d03114104280341600e41e00d004904207040b41003050101d2003040001c40081d40100144807450700151303403280c42031060300d203840115400100c0305110152000300c00702c54180b50510070031590b80403540640048008115080040d6995035200035050406413400001052080c0c1c40307030041003a84d003e014014039006901c0c02032041c00003000f50901c1840803060b100d400009200040c0d1082d1038881802c0009149032048420038080a9841400100c81c414100300100701c44042c10b021000c856071080c2d880320710450203040020314111641398038000074000024040b000040a51130f49508400c0e5060216002c4803a06054039140164a01c840ba000d4042e070800081005651003007064a100703c078200600d845203209a59a4011110000c003178001040c4818041081c910203180d00c0507880c455443d10403130075070100c1c002c484894030b014056403011071380c1000309002d801503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 944593210 1250 944591960 944591971
    0x5030a14120301060909060909050604110a0f093806030c070f0606030203010b0103020f1611060f0c120412060f0e0f030910050322260c0c0405060f040b03030717030f 73
    0x1401500c09d0742d1100341d1118000703040100792001e614034248550f100c800c600d6000300600184498a9550b170036a00001d00900c4036905410601d050003000603111510903203085c0e06010480d030f03481132101414000c844d4006017109810303110501c841e40015000400301c1091604c04c2001040541c5184145825036603d50302050500d401400a482c800d0140002e0f1022a42203240c04c8103415940c1c24003101300b00c3ca07052100c0d01701500040100c41c081080700141044507220040342c0c8144540400c242d445d010b41d01074652451b15048640c008180180c0200e44030b980c040e1000240c00700c1c91900d16180c0342415208040b0f030307040421001011b03d020b180c00c002c00840390805610310300c0c10409a150402c6000c0c1903584081100d00d0100c00d101e0202c80c9001358612207140100c0304200b4441b0181203800c50ba0444035184106040c080c828180f41c01458022400500030011800351141080007800c0c0c46204940c1502c4184070900c04501e178003031414008101e00300300e43d580e42000000c00c901a04010301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 944594460 1250 944593210 944593229
    0x50601080d0e190305030f1305010f080c0c39090c090123070309050f03010c05041818030314090105090d0e040902100806130605030a1412030106090906 67
    0x16062103141c10a80390000302d4021120401c0b818103c143c1d0a5a103030a07078201409900c07020440700d0909200400170315540803c0102080110394540045078155440844080010050740200c0c00e000078110181c1458200082910140c0003100184020300c054004605207200325802000440e10580030310707100c5c03080305a0341c1d000c10b1b2825041c082403500c1035a0304c0c6410030164040c00650b4000a400d011100c114100300140e40301001c0c10001c001d280c880c0102d5210b4400c2c00160700c1d40340340500c5000f0714240c1944400741401e00e03180701d1402100e6842034402c95103848101c400d08005007900d500d19458440c0d200041c00b01d0300c3c922580e14803140104945101ea240030f080c0b10248400140e4990034070401d28042900a15100c04140034114402c0001c1d0840c041c0c40c0d84508942c0c00100540c800c84040d5001d6001d0462807403214150703443ca104240d010b800078120000130031040314441000c88100c9045896141c6210008130321980240c0c080c2c00052800b0381c0c2072080380240d002c4c00b0020090781d032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 944595710 1250 944594460 944594473
    0x1c1401062d0e090709180209060f0d033e011104060c080906041d150423100e070905031501050f010c02190e0906070f17151002030705060108 62
    0x680307900761208600584010759880070028103000b00070000c02020f0b0030914002c0c003440b007880260601e407a2022404030301c106500030004559091209600d811008003d065400a02e510340b42900e141d8550261406038804c1c07540101c00070700d01a032000001c0722003042c01d103405182d8051200c1c2120070140000000007010001041801d50005540d104c0540181c4280d0703484080768009a1148140c3c2d2110140c844506036080c0f110758003d11b600c0c81038050b03002031030030644124200412128454a0f590701d11a20000e089020401071000e16441840000a0380329580c031030400c5840300c8403c8490800240c000407003801142003e1050b12951650074004103070355410100010f03a180780e6810107504020f04141421f0540d603414001040c40f0b95010014800c00d6201c1d00100c2d581c0300125843c056910441d00400d0701d45100744048034049490350f0314010100c4a01100903685d000240281c003a50030f50b02054003182c1d440c50603443d0345ca20a50000c40d80c6140c1850490f08101c0d0503408100c280c2c1020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 944596960 1250 944595710 944595779
    0x41110051305060a0909020d0221060102012711030a02040e060916180b01090b0c0c01030e0d0f05300403031508030906070507090207081b0303151c140106 68
    0x85a41170903551a03441c05a01c40040c40c00e920000e0088400d08041181070000c058600090041c020b402214213070700a2201130b10302d100068030f2605040a0b210041e40100303065000c65603641480c0e40401000341915a81100350300000c0986000502c841c04d103400160a03c03684071001c01220383c8001d0048400c0d0070341407800e00800f80c0d0012043d9621130b0561142d00041141e031042d002070703000e008402c01a0b17848078410f080300c0d03680c0d066840c480ca010070700d00690501343c1000006d02c5d4080340e1555440d08040201544212039680010982e040d000c203580340607841c50484646110a0100c000705603008615290030000d050300c3c00012402c070102c0c42d5280621046101204441c2004000e643c0595601c24515080d4500034555200c0038030544041444410010000b004000f154190002d040706804640e540035100d11040e11421600084030307158880310304000700e804600040558001082510075224040c00d03551300e40c100c14959554800a01400c41012401d910003461404100c900c142c08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 944598210 1250 944596960 944596967
    0x42f1b0a020906220c030227060d1e020403030302071a131e0b0c03041b082112070c0605070318020402281d0103051509041110051305060a 61
    0x500941e02450509013012205007080b1021000c1c1600702c0c40400080d030203103070000c00035002581c880c14421311030440c0181c5109641054000080014155454031040c8800480203102005400c0d040c0815000ba91000303501038400b81000354080e40f40560303240c402d0b00e841d45082e642140204900d03140b00c8240000902d4600c41c000202d070f480f5441c0320001e0031180541112000401c0c0c020001c902c2d600400c040d804400010714055031081d01700d415000620f48410540c2c54540c0114041c40c3e000b03501844254010002240d00c0580740c0004c0c3c3d18007118211a08071900040f40c910b40480c1745c500d440420080303d03100d000ea105440745010881c03212244070200d1011090038001c0d2007140c0201c1c50f4020b41c0c101d500b0308885920015102c1000c0d100003030010b85800280c0e41140c0950101c00c40c40320036540240902d0b44209100d071404c4001050304400c004a0100140058803040c1c40045001140d0302d4a904075001c1416a45131305850703240c0613104d991280010340003680903d500b4060200002d41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 944599460 1250 944598210 944598229
    0x40b0412050c010204080a110d0312111605030324030c012d02070f080118140a0c090e070902180909010b0306010306091b14042f1b0a02 60
    0x50154541001400300e0600321002d00500b00e0078052548005400108503c000852903c564840c030b1041c0c120194100c20440420844131025001c0b4112a41801d46080c1a602c8074030040341c00b01c3c201741440020303903026000950314901102c1d2548000207111001e54010b2203410f000c1956400300340804a02404a40c40d48280541241444240303580031103060500c080d03440125030741d404038005110a015009580f18507a20510b084a00c410401103406d40060082031042044500c00c0720108401d5a1880b20120035114000034500400160200050f903104204001305860400450007086010156007001071684c440ea00851040101160801d00c086215203245001c40c2c007080b603690b0b1400740e98050320302c503000d2075490700034400044100a041d62000d50a1030240314403000700b6800b4480008100c034a80145210318070001d0706000c1c1850113800001c1000709440d00e01400c03000c450200440c04410010401040da40400c440400400711b081d820b100003d440c0040030305a0355900400c45074407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 944600710 1250 944599460 944599463
    0x30304060e2b03022805190e03340f150e0307030f14010f02180906220e01020705210a05041503020405060c0606010f05040305060f070c020a1203030c08040b04 70
    0x6402080c0000040f05d101006044814103400d8200e0301d005981d0020440c0c2c1c030004402814110f5599860706d0140704035054207000070b001d402082082d07052070400b49000c2440807034040d02c1589052001c1c03110350030140314005022018207200c445c4c0c20010200e0380d1801c51340c0741804101140100c0c034104c1d940061060200c98102204212a0f205130800c401100711800303030302c441c540c00c08102d8103185246600074041c2c0c00015044050a00000303080202030107055030410342c045014496142c00032415220300803040c110700c3c000101140d802d0105820f90304250070a03141500b00c0c0921040c40f404002162548001c4040143c2c035117540b1040281986c05107000d039040b0035440180705410140258101e5001d40b00040031140c0312905042c070f06503249000c646070b60005180c55a0920306c42d0154040c0c50569600101404480c2e551f028440340e081030003414081041140074403100580c407542503401c050f0124400c8020442400d00300078040d103007901a03607820005860104004589881469134029 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 944601960 1250 944600710 944600717
    0xa090302010207092717070c0e1302180a021b060901050a200f0409020d0e0114130f0f020d0b1e101e0b0f071106090307150908030304060e2b 62
    0x7484c070381040700074030480b2000c01400d1b46001030b03000107112080d088802103502100c00d40c0030703c0d070310f0a44006240c07480100081d000801d040c5072124180410010341e81c4480322074401410300d0302c211180712014151500300881900080248200e02c5c40030300a45038824080241032107106d00e1468180340d88208005403009103c400309241d10150444412100240755240f400e644030104050082c0080c10845400b48481d0b180c402034185688541c21020b00c1808400d510b4600300c0425120014a1404103404484141c2e01509240041e5201802500140d01805904078249002c00060386610b200c06403074001030030800c0400841d44407c6244c0c4040d10780242c928004d8034100c0450072140c18554010b100d80c01c0340850301c01440440703140503004507030060380480c815131841020b0001911071001041d030076400007141800851210010300c0d10040c50f500e42445429500c1c04450f04540090742e080720080e0316030202d03445100c410005011541c104003482d04038825003410350580910b0900c1d00d5000d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 944603210 1250 944601960 944602031
    0x1a0c120606030f130804272f070809040f0903120e0a0f1e05010e07140f1219120e030c100f030902060408060403021218010c0f0204020a09030201020709 67
    0xc00c17040100b41c0d40106000500a81ca105150b1040d0030341c0750054101c682d0440c9042010803204c0f440b03c0910902c0110030324800020b103149641808260701c81c000580d103018041055001e0398581d48038190700c4d20142080000c681400c0d140042c10400100d2448003c10704043c1c51b04030080c400314581e142e059100c136041c0301401c405c6c03400f144400e19844d520032811102d81c40c210f003485819040a4682161503090718202da8640101e0040c0200c60481d0a4100b201100070380000c2c01d004140c54031503074290040b5a14090040c18030300b240111000115030140c1b0020350070007140d4004a8200e0108402c801a00c1360402a40101e400b6008880703c500c1040007681003c0728041c02540701d048584e80103405180c0c0d41c0e46070a09290b2310101076030120014403034000e20a01c0020010141c8081d2465100c01151600c1c1c0e5400440f940301c001201074400100445500300141c0d6103100400b00002035440f400c0c0440d185d40000390411a1703a0340308469450600452008401400d181030200c1d2030041d444144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 944604316 1106 944603210 944603213
    0x90608030403060e0c1009030506010f0b311d01140105160201120e10050108032d121f08010b0612041a0c120606030f13 53
    0x51a003007808240005411034122440108008007116502e42e140f0f00041c01c8080d4600405011401e01c141c200101f002c02d0014500600384aa402c6071568a0803007108210311603851040d81c044420b00301e502c1800c84a0307138280c0c00e89032034140070f0000a40b03460000f22030400f18800101c8a0b482400001030496809841c16800d020681d100c9041100540040801d01d1220101f2414007400810710544aa220f110310030b50102c03031500a2240c03074000d001903401c481e01070b0024409074108011003070750719841c101200401175444c94070300040109190351041d40e005080b0380103803070400304091014400741043c0d0756906040d10301141030416500c030303201822142c2c482c520542107502809140410303c00750100f964401d00400041d66985c8544c03400108800c012681904000c9004c0394a11b80c2c01d003c0304203035900c460242c41d02c5155042842135240514801002d801c00c481c0802c403e0340 = true := by decide +kernel

theorem cover : BRFrame.Cov 944424460 944604316 := by
  have h0 := BRFrame.cov_init 944424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 944424460 ≤ n) (h2 : n < 944604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
