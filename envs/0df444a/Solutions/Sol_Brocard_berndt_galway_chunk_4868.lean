-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4868
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:00:14.427995+00:00
-- url     : https://prove2.me/submissions/49e8554c-ed0e-488f-90ba-6b30b09f991c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 875359712 ≤ n < 875539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 875360962 1250 875359712 875359747
    0x60a050a110c04060603050604050907050108010506220b0405031b01051602040f092a0e04020108041b0b12130201020d08060d020a03080a0f08040809100e0904200105040308 76
    0x280e1101d0b02480b00c00800b280c481c1c0c03003400000c003800d030340114041c2005c405000445c0c5018104100c0c5400140341448180d811100c0c4a04680c001c0c0d80d0140e4030259030401d900504180c0341404001102000001180c042000141c800d4a0080302550390100c10604c1080c40905501055408604240000c0c880c82c4d821078030608401e40007600c041032452a060780783e02107540c100d00c102c9908002d101110307100400d08124100e0f0411203842014101e003030040140401c400100002d041040120024040018048101414a0781036003542079030750301e6a000b02d1881d081110342041d4603c0e058000b80d00c1c1c0c41c040030300312503854060300904181c1e50720100444001d480280b0785900000340154240060700c48003800001940108a0191503004814005028500c40c42044003040000414440400c8221084a0701c030101200c441030059103078a001c2c2e640c2c0016543c4030364032030403490800040c0606c8140b60340b1290310b000c66018031481c2c46401541c00340a58080034011120502810a010030741059 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 875362212 1250 875360962 875360987
    0xf1406071112090111060f0a0608030f09040b04090b010306090201021b06090d1e03090503070b070c09090213050403020f06010816090f020f0f041a030f060603060f040513020f060a050a 81
    0x1401c0072417000740c0c1e20042c40c019080e01c442c0c0002940c0c004021000c255485224040c00002c0c018505e040f00800345d41c0440d0280342d000900c110ba45021548655907540d0004402a9110b1103600c115a03490612000400c00c840041c2e0141c060081050503452041d410921100e0000b0907090030010b1035402c0c440c01c0e6142d010100c60002c4044005042d0502e001d61100c2360074030a5540d10074560810081c5414260b00c1d920007842d03004203201d40000200c1c05070a0200382c607440d0f00001060240c0e400000e8848400c504030055440c80e0030107000c28594003040650043c51340c20119806a40d0702d082e078503510030842e41038030032400c00d80c2014040610f035500041c5540443e07034005400d242802e03e401c110f07507100075029400054000b900b0070251403c1c102da00b10940c41c1400c014203502e4500c1c42d1203c0c030400101480d01c41d50001000801c2583c40801c000400280500104041e19210643d099003200704401a441250301070310a0706246000421200c13003140694403542000c0a41c13a090720203000e00d90 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 875363462 1250 875362212 875362217
    0x50603070f23040618060f0503120f09060a080a150513150305061608010f261015061101151221020610050301180314070f14060711120901 61
    0x400b003141e681d40c0600c0002d00704500200c2c1c60281400002400c55401c3e900a240310703050503404022aa40c04a07100b403d140c14100c0702070356204818418500e52103514103a46e0301c200040b0390f03c03541a07407100c15280700b0b0110340c108011110301c0003001e80440d0f00303e114107580491014102400d03030005401001d0044120451444540c4d160390342d85042980484400845c1919100340748121580101214014107a9514410316130f418100c1e03035440656120110000f00300902c1030340b00071401c20080451500302110040001040300c0c90b40c1581c180f003900c44c1c08002140302c034900c1900301c01841200780d101c107490b190b0039585280142c1a0884601150251041e22200715418130301401400d20000984050f03015108914228000f800811400d0b0040350081e031500e5881002540c00329501c1340304540506100001d26988140c10640d0703c04c0e840010720505c50001e940003001185a110000b00ccc09030310503501c25680d5580121010364541c03014042960106010421030001c0a004292040062 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 875364712 1250 875363462 875363519
    0x71118180309120f010b180609150616050d0e060d1107170405090726060a05030a030c0b01051801090e011404030f020601081b010e040603060501080d03050603070f 72
    0x107400100000e02d43c0788011400c0d0051035244807070500c20722404068802c2103074445081c60350090244441140248040c0c0079084a0001c03a1a22082c08040d905680e401801c051b40d070002e01203082d1301b001c43c2c00b008541c2031040303c43c0c41240c580190581c100070340340174144a00344a0117010303440150082c140c00c4211080300700701c00f41c08130b41600442100c619211075155075032071409040c001055030040150080000e0710115601405900b03014011010031710011001c161501070000702c410030503a200c80d50500c6555000400c00d50407449100d40c41c0e001c0c041050746603a9600c2407106a002e6614400300c90311071440184444000c1d98005103a540c0388800001c1d000b48142a01e014004007504d059020405081000040c0e40c2d04024050250045401414044055039010700c0f4180c8014620b034180011701a0300061511a035000000441e040442448a541c0d5100c110752201002d840b00000a803c1400080f010b080c0020705004840c612024450b04c01d103018111410503500801c061031102a2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 875365962 1250 875364712 875364727
    0x60216150e07050303180a3303061a0304020f030d02070603050c19050d020f0301031103010f0b03030405041a060703030506030f07030308040b06221a041428110711181803 75
    0x40c44800d089040e100c0580504008035014080c2c0323442c8e039003055101014202070051040210342c0c6280c200500c0c0000b100358817902c442c40002d05401040040540500c612041c03040d80f01d5000480300c0480d401902c0800094a442108044170b1040d040600382102182804041162107500145000c1806060040c240800f0540c1440c1c0c6600a80c015601801981075100c4249400c0c4100065102403039000c120200345500484d03100e01480c42100e209554a040c1030340b80b010f030f400c040444094028452a5554100d240c054010031003036130814000d204500a42d0500c0b100000c111003920b405881e0a515660340d55160203002c0d60040505401800108400c41d0001110740180c00c1c40ba00f152020520481d62103070b403820400369001039841181000c81e001c0e05600e40b602c02d150444c0704020a80000742050401c44510129103a03102080e9283c441c620303020301280d10291100d03a210300907403030780b1005520070001d846000c50003030705400c40340d01d000c6801082c500144504543c005020f032400c0100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 875367212 1250 875365962 875365979
    0x922050102090a050103050411060a050c1606181a1c1806151202090a0e060906100906030302030a0f110106061d040608030403030309060216150e07050303180a 70
    0x4400049499a4020544140394038164071010040c00d028601007203c1d00d002c0d2a20200100a09120390060780c3c0000c003c89218030400880e03600340901021101c0d498034840c850190100700d8410341001070881414524407001440101301256100ca429814000701c40120192560200c001c0041c1c04285055503030b1030020a004001c0c00e07402402d4900f044031240d06100b03041da030910420110a5505420a2080d0f9100105800c1c9180d01500c038034900b581d4400100d80200b9aa05000382a4420710041100040c40042c203030b48150103040301300740c04030ba03030b1007841c0103880050100502582041c818420010300c6031903001d02d00259850403a80c2c0c40000d02e5a01d00b191555042400050fa0391341c2d040300d000300f10038201107030100107803803c1008526125000341c41e4001e0f03000090805031912091401d012482d015101c81d610301c4c40c1c49105290300c0385401d41c0a24040c41f1b0740b920075800c0402c510003100022070010300321500038010314075000c0800005034030351000028542e4020880280400c0303116 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 875368462 1250 875367212 875367271
    0xc060203130f050a050d0f020703030819050421170105010e03150a020a140f07080a03060b04090b09090d270812070c0e0c0403020909010f110a0f030504020d0209 71
    0x10f0240014060405250500701d003081d4007402c03141c05002e0300340d20054015600180f15001c403038040c60001881e0b200e00c42c1e200c100d401c03003a200002e000d08181c140818400146500d00c070441c902c1080d05900c3c0525007064a04201080010500c1004040104542c0d4041c068000c0340280003801d945100005400030044c6040c161410308600390302042144070150003840c0c44240328a4140030605104221030b2100301c1c2c0c0b2800200621281012441a50f040d0280d007000000d4040b0500d1581c071180c0303844004006001c41818036215000b08808152000c5000c81d0131100503007640d4031340180382e0525000e6020107249080341000c284442200103900c00040c8071a80604e00e00c00700c495079034105400c140266200300e4200c01c80082d001c805200c00101d1180c03c850850394180c503600360503594030b90080d005040e01c240c1c0b084440e04007000006404151700c0107018504107603d03440c01484407914200c08440080ba002500003141200b07160240c0307000841c00c0d45c801c0c0c1350710716071404580c008c64603903428 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 875369712 1250 875368462 875368493
    0x60f1e0301050c18060705070306020a02071203050702272a12010e0601080f07030b0f061306180605120402031c0203030703051503101d01022a0a02010c06020313 71
    0x242c07000c5281924100000024074134200708135002c600302403807911401e490702c1d558030001b0314060740069100d41c928002e20548000b08000410010f4800140c00d000d41aa441031030100d01c00c2011024000c001002c01d48a008032700e507858000390542d6515174280700d2549c401c1141700203100c04102c251400703030740e640010b1481002030042442a035143c120110404600500380360305100000c070401c54458980a8000d0f4400c0c1070f4034001c1503802404001c5403200c1c150300005c4e030700040c00003008505c000b0008a80400c45506a45d410618414891880c0c064501402480c00180c001c204032000c3d13410004203250001d0004044c2d03030210110442504000c4000c0b1117540260b080807040050b11505480380e160306c030f2501c01100e14a840c5c0031000a07221002d04000704c050603502e05810030050040d00340c00c3c01c1550100d00841d580c1e21800b94800500a034094803c01d442100c55140e00c6044010034400c1c190303541a120b40302100400c0d52540044d410040041e0f0081c0007548061002c2290407500038501d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 875370962 1250 875369712 875369731
    0x4030f170f040803271c0c0f03060e070b0a0e0609150313050f0115060f0311043201080f0c09150a0f020601030503030612033f060f1e030105 62
    0x1700c5102c03004150f000c203603c1510408020461070300900c3c0e502c03184049916036613140800302c0c0c16680c5203428266a019900081c41c101001c0c0300100c1000030075440075462002510898065a607034200c42c20462003200c01d101c3c001211a44490368a05080c0048c0071500300040c50745640450081902030250012100307180c400c00c1e4080700704103000043c0100c243e6040d2401c0240168425140350800d132621a1060b5402c0081c0d040300d60381e0840c40380d841044101928440660342d03a5a50180c0c03080f0f401c2d003c01108004e00e644112020f240c402d66400d05100c00e060315003481644c0c41c1d500c0040c2002004101010356074040041d0051683c4440e6141c91074146c0c4020942c44442c40c45c070003807007011114074038020365002c000140049200002035a60120307084503444103082c042d12900d0304601903d080013020b0103400c80350800f00004d115034084920304801c040c0e60200540d1070025402d14054500e0390300503001005010003070408070b5403a480314440e41040d0b0196948400032a003113901c100d820105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 875372212 1250 875370962 875370967
    0x9061303230f18090109020702150d0b040e0d1202070c0e04020a1802030411040c021f060f14040c0906092105030d1e06030201021e0c06030702060405010605010504030f170f040803 79
    0x3c0318600003a80c103000d000c424904605090310740e40841c8402c4030544481d2100040407510340e0700d200003508100d0513020080e0007802854ac100503103a58034210b04032440c01148800181d41503004032442500c2c2900c0d00450701c0e061a80c50304188031154080503109a8121802d000041803404a204030f403c00719003030100050780c900d00f504003840c48420411400784030b90300700694040256400580c1901d100408c0d0707299400b92442d45041c1d002081954400d40b208d900417a400034002e40e0480c081c031100344042d1400d00c20800c2e00c4600312a08851401480c2c00300303040d00410b10150f03450b84006c40800308000901030628080703032111403954104406c0d489585450302c01c0b90252280700200c01c00e01112000301403110340d0450380040c0d04c0b0505c48402071507400051504a1000c2c104014000786140080d000540e80e080051000f900c0e40c1003114281d419600b08800040c4a5108400f00c40460303030444c080b212440d40c1940e500c8480e5000810070805908148076119055041d44010401003000b80c0c000c55 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 875373462 1250 875372212 875372257
    0x122607080c091e010320180d050615040f110c010b0307081015030c06110c030a080904021804060b0408060603160e070306080d030509061303230f 64
    0x2050608010000c0064140c00d00c0b12410715141c40441c64068080324078030196140c90034004070000c0215148042c02200d1016030100c0c00340c0410010484103503907444820481b0f58007002d0081100c401c0c0d4005100e03601100c000b07034054140d03100000c03050340c009001080c840e541508000c2500c5288043c500300c9140050f15041c0400e00740b040c0c85001c1d00070b8015015082c900305103d03440c2c0c039200c03000a01c495100c40b03a042a041411030710001441c0c0c0018003d40e4103403900c200608044880a9107207261207900440400b5180c001801d003040c1c0d900400ac5858619540140700103500f010180b000300c240e00070220708003076481d03005400141403a1680c940d00c41d0b10703003202c8915200002d00f445000e43c1155150030440d004003405001074484d840710844a903162210110000c01c0389501212040c0201000110090b42c95003101e40548803610854000380c649144124071464603c0d0001d010400c10101c604080c0d45c414009000072800700e0105007084011034240341590300c01c580141038080d1030685076 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 875374712 1250 875373462 875373467
    0x3080114010c0302060c1b010c05091315030201050a0e0d030f181404021b060403051806030601021513050a05060108072106050a1d010630122607 64
    0x1010050801d10b4076400c24466500c3c040d403600e00140190a00b5880003a1000b50b1020038a001d20380f080003100204420340360641c009100340c10800f65103100c5d4032415100c0c1810a100e01030800020011007040302c006146900555481e884100c4040a00484c1e41031028141d8408036030000080c000c1e1101d0b40c941283c1c141c01070203601d58808510b40c004d00f6103414409000140d88a1050300820b5030300594580d1041c110701c3c80000308ca0003010f420302c1000100010164000042c040342180b011404041d842402c003000a140022500c00c2d0040c2c0c4000c25450040842c4401e490b04141c0c02c20050b02c102c02503071106810054644001e89040e8421001001318000030007500c0c004148003151120260500c6d500d842850342c400001900343d03030b140c0002c20058641503000002e0803800650701c50103803181101c56806800a841050610b0081140103a01824042c040e0580d520101014010200302075a031003046a0781000c0d600100700e9070010f41c40015040307011101c00352907801c19115407860030a000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 875375962 1250 875374712 875374739
    0xb130e0a060b06040f0302060a021606050903100c0f08041e05011d0604080d1a0d030e0103150506090d1a0702070f0b04031208060d080d020903150f06121009030801 72
    0x2c2d40500c600304420400c4800e50f040c2e45c8252603040703600c20356507a2510350403441c01e414101500306800c08104005403591b004070040c10354100a9040c0c1d509000348950070021100380c0041c0c0300215001030505d0810a01c41c0384a2a0301510600c008920114000c584a000d00c2d0f9421017260700781e54031540211810441c00d9101c05061101005004901c3e05546108440c025180c2000c03010303843e0000d1041c000c00c480c0f04e00000c0040a4001c80c0c0700710b01401c0040515031442001404a480d006035411100030401103d020b85001424843c50329111005100020030b11110594038001c0f070030f004807001d00030310f804e06000b80c110358021b140d010b0900c0e0146c2d26004655000c2e40e43c00c0c50401003040083c3c50800d222400b480103041c0042241da0f51000f003040000d150a00900403080024024182c864541c06040c91304070640441d0840014456204015603068032181c03000700d000380000d403c51070107000c480800c83c0481c060314004100b611000040e142400c07400c4000c1201e9000601603000e0304810f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 875377212 1250 875375962 875375981
    0xc0201090c0f050a141c031e08190e061803090402030a0e070e06031e150106110c040b0d080a051606140a09110103110702060f03070906090602030d0b130e0a06 70
    0x5a00340200d0602c005008440c0c240d40e08021b100036200c3d10002d00d0302489800080d03440c200c1f6980c20807058400010803085045400043c1e8050300d00d0340f914620898032503002d20041c0c200007042141c848685c9002813017103000038481903120401108031705485900285d4040e401105000c11a402c0201c2000e0070310305107411601e1840009001c00003039075400559100c800c5840343c81440d01c80b5070080010300300107100c01d0340500759801c4000010080d0707200ea03208002c05407400998228217100301c03c10064078005a00582c0c450400680f650104500d08010004a041030401c145003c900c038540c0c03919144905c03000c0d15034a50340ca50300c86c5080e402e5039000f54042d081c01740030803461803980d442e240c0e0400c0082803a41019541c1d10400b540d100b0180807100b4894009010030b44401e11a0042155030380b0440b41d41c4001823401d00001071050080c0280700599102d60051810b050702520400c005120042500c0d42c021045104114030001600c90f00350b01041007006890350005038149441510070104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 875378462 1250 875377212 875377229
    0x105090301021b011a0d120e0d02030a050a06050601030e0a0206030915040614010e0606220803070f0512040503100b1f0206060a0e010f090e28140318040c0201090c0f050a 75
    0x131b8010025070354401d0000c44500c1c6040ca02c48034211a00841d07981c80300701400a41606c168800d18050040010b444040b41d4890101800280e0b1154011826941e1800c0309507020361007880c86500514184003c0d40d1700440701c0d822650800002d6000c03014088080c0c0701510015903031450500d04015140c240c070301401d00c00207404d02604001c0040355191244001034408081d01d003600465080b050070810300184103c20442e500c9802c181480c0079410400b001c102d5080c41001e0101422016030b506031402c90300002d020f071410001c40000b4a004c0c1200c4100b0942c8400313070350240705080c1214442e410b40c826170759000b0051443d11205001030b030006070b0801c00145460300700401c41d5282038020b8205035001410041009403a90f031070325242211007569120501c0e03079401f4000c203c7d07900301d181320f40c46802200310001c21003452085a4a80c45200a5280c445401403211240d6040035080800801d4142c0b0000030389a0b8a61140c5005d004030ba08000c5100c0d06480c030820680c43e015125070301507d10311 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 875379712 1250 875378462 875378479
    0xe060c0715150501031509020f1201080c10202e0b0a061b1509030f031526060c0301062003030a110f03040302150c13050105090301021b011a 62
    0x1c40b208003a44826100d101d04240d02e0700b008100c6800c1d4032000c1001400c50b800c0542d00c1c3c80511074464804c0d0090149052a02c503030380300008481500141c0d11590000150808140c4214048126219210800074441c04100c4a02c50150090200300058520144030400501c10921b02d4900450f40c400d403001d18031050400c004800a41c0e5541080401ca9903942801c820300c0714095007410310200c031804064014115403031b0030030541442c1d0304a502e00740d00c2a500ca405002149400350102d0b03030f014442006000c500c0e40c0a114000c2d00e10325800303045008400041071890314006141c94078100326484da40c541c00101c01007240c9500000344030b2004c0840141d4656942c00020401d036240030041c1140d101d1520f80e1500d0302d00520210854174a00d145105032036682c600781c10069134039580b0031b110314075002e80c8200150341e0b001110191601c00314060703c800030f00c80ca000011036654100d0120140d06540c05c105914102c0c00c1000c940320500380300d02c0080390341032074070a240405140d241c18450040042 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 875380962 1250 875379712 875379731
    0x71101050403080a0e070504050a0b0f03032506060b0307090e150904150b12160605031509060f030a050c0a051005120703060e0103031d06091c060e060c0715 69
    0x4080f600d07a200c041d1400c0003c4244001040e5881c1c01c185500c600e4101d440d007810b20003451001e800c40503c410040d500038500034501801d051741c0b4400c0050804408518140007202a007080054811250188ea0041140c45d00c03003100a01350751040c1d65240c0410320711a4104064460003440701e0307001044500c0f490740a074682002c90300c1c032000140300911501d1600c40c0c07192000010382c040c1250903005005c8003100c070030410000369a21100070145d54042c1c3e89410008807684a1411284100000e40d500a0348941c0042440b0a080300a4080340c0d10481c03600d984012a2030401926008600420041c10896040401d00c0b404819980289004405d207c584180007900442140c05010442d9880c3d2040d80d52128100d000782001c3e0002180f00750717020000424150f0002c00100d0070000c14904c0e01d00c0d10b0041003040380922407045081d4020101d07601c004c981e1403010f500b03480a58000c1c940810390308200504642003003021151401d0707144000c0760345020f000907e4000a80c2044080040100c0c0c482c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 875382212 1250 875380962 875380967
    0x40b01020c0d1103121207020708120f0a030f0e032809151e0306061206080c012303072007030c120f0615170601030b01050613081203071101050403 65
    0x80c03002e00582180c10048460410791002c204064642c240b101840d5114188607018200315070083d18a4001407161700c1d008500d42002049400111581b0407140d85805401ca40100858001050400034943d5403080d182903910140985814003040f44061a030700c411408000344040c007030030403c441500341c400401141076003001001050b582c1c0102c49040070b075542c40003242c810300307041401c0032424110188103c0060309900a00c090b11025140e43e0a408040031080d4211403041c480d510099000c02c20f01c03540c0754007c1184c2d620b01c0c500c88505102254881158480c207500541d89000010324080161500030440402e08a038013a046014004240c55511424aa00074034014582015811041a01040707147c0e80705800c0c3e554480310510041e8224542c2c043d172a0175900c035602000322031150a603c0a040400d42c103041c1c0b03900c180e203503105900741014442990019620800555500040400c0c036590030414185c0d102c03d9450301c99a01d10b04030400800e180c44030b180c2071007540e0400c800c0c080002d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 875383462 1250 875382212 875382229
    0x60a0c090929030f0a06060303030c081308030702071205061509010f05060307050903011a01181a0a09030c0801020a0306120f030809031905030f070810030303110d0f0b040b01020c 79
    0x140c1d955185210303950000068108144000b8504c510b2045c41c0e511006c10030103400140842e4041d440030090020700841c00c1d00e10f10b504854600c1c04003095040e4500180200700615001801481141e61040e15040d450000005200d81518103034040010084864400212010140c40607980b010182d49410415400201c141c086c151107101c02000140443e8840d9050f075000c014002d00074452031189114a4100d90b00d08204c4a0001c2d910008002414240d100c0d1501110440c503044114181046020185070f008415800104411202c0000105240c9031100000e440c0e14000180d42d0507000002801304c903540e030b101400e481d00d032100c450007294440401401c140d4040c1004900343e600d000459041d841f80f030008001e488644c0d00e1640110398858040c0d440f034250140107440c0c80c4c582d000103030f513040e40c104c0e0a0f00c402031100e0b40610020303100350070011000280d100380c2400d02112030780c40c6060707030140c40b0a894090759a580d80100c91410f40175802c001182070014146030742e4654089550300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 875384712 1250 875383462 875383511
    0x10b04061a0708130b0a0e01030209030307030311070b1918030804020402090103060305120403030e0a24090918031209020604090b0607050a0515010e010608190e060a0c0909 76
    0x400011400070240001401129074404240040790f04d602d45903003034500309800c40381c2040e0007e1201003c0d00c00071f50082c07086a4520b0030040c000c1d030802529aa0840240000c1c02e100c001204c014491200018110f2102c940a035400c12031492030750141c00d20035401c5841003055080d120204005880100e03400c04049030700280c0540340981d441c0d24103001a006468544c0c8020300901c107460340c1e800022412400717081902d110703680d410074000c004003c10210742e80f54068100d111803c5107144000001e140e80703c082c0700e952814068a040e60b5114040210f4403050043c2100b4160443d420080580c4490300b00350309445240200b0880085801080090041e130041c41c3c500c1d41d8800395556150783d1a03040d28400d961080c11a403030501c042c07034002d848200f04201e24044941d058000306030b42622256143c10703924595a048425524929a5008005010310100c04e542c0c0d16428a40003010500c83c080c030603200302034089600100b241c4010141c0c07506520411860b0f240c84030925982c0e0036041a520311 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 875385962 1250 875384712 875384759
    0x703020d260c09210c0105040f0e070c0510062103120e030417151006020a080a0504080f070509010b0a02060610031503060510050603071b1407030c08010b0406 70
    0x850b5901da400500610803441101c1d03010007245a02010603082048220071440340c48156010320401c00010741c1c450085000d0340d2580c5000000c18007060700032100449d070002c018a058a03004065454140c2050307265218454055110003003804114528403004100c41420002c03960340042e03907100242070641400d10750a606403109102c0c0864001041940d0180144003004100d031010070110507030755a00700794800b6511000000152314981c49100352000c5a17070315005448a020340356210b0103117911003656501448014031001c1091401002a59041c90400d40100b510742d042c60b0030081740c00d105034000044040304010300205140e01241103030f04030b0019118048034024030103046d8050300c0700c05140b40d091016540c0010501c20b50380c00c040d009501c804004404103440c0e105200091008541c454007081c1402218508201b100310303078440e128024207180103001c001400d0030b418412564400d130b610340482c2409000416003071250300e0142c103044804210881c0340c40307001d1080514151b80c00e00c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 875387212 1250 875385962 875386037
    0xb030c0a081f09141b310e0a2a08040204062d05010503160c05100e01020c0c03011a22230603060f060609010c02150703020d 55
    0x3aa01001007107152901002c90015110603255104000104440c400a02c1389a14100205849140c030100d86030a003803020b1200c5241084848280d0303840700010134a400a5040c41c0c1d4841400515140103c000c1e04004400200a092150601d42641d801c4045034a0650008121a40c103054032070500b00244141d08149200b0751b141d000050050403154044203c0c2d1034407143d001c2400c4491910040384010342108802082d458100440346400200d840f4010310769480d02e00030085000e40c040d0403000e0311403c100d40507107440036202e1060310408013803012280c0d00881c503030208090600070000c00800a40007003060011503c2c52079811482c0402040c051811200c031803c0c40c90400c0c45800c1c0c4224560424002200080c0144250802c1e103110f806a01d40860301143c40c4d440c0201d2914060404000c00495a448100401105a2200506505005104031a800181c44a8002d110f110500f410110b44404442c200a402c03c450100c07480300f0404420010307058031007400003681b2440741030300601d0b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 875388462 1250 875387212 875387221
    0x5061305091b1503040609050f06070e06030415090c091d03030c0f0d0504050616020c1e0a050411070b07080f131703091b040908070b040812040c09060b030c0a08 71
    0x2002241d43c0031992910074070002c2040140f00d059080303142d00b03074030a00444072901e08400310707542c40d000160b9600d0002006407501c00720602e4083c014582080c004c840d00901c0003c81a020004c4481c042801c44450a98160030011082d640c41890941d0007200b00b10381d078116140c651702e07440741702c020050ba804c49404250b040d028682d58003514141c003005c3e81c0411041c180f5092807565960b04aa0405480c1c4015418080551000c03861182284003e0000451003c41c204050480c41c2c00f1003407203801c6400184000389542e12401802c9403a05c01e80103881d952030241c18800007000000781001c05100c00700c400c0c400072280000c0c0702d5901c440c000940042450b0185010ba0442c80e1300318504004e00004418803000d40d001180401000003a0545505140c16850600050310280c55000c6c00242061042c0c034080f469621261741e00500c5501d92500d003d1900744e00c452483e0083c1d500b603580d2600b0680501200c0710500c940720107040303507503602e03801d40c9000044000c42d48103100e50303042080000400705 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 875389712 1250 875388462 875388469
    0x50603070e1207080c0d02090f090313060c060609290a230a060e030d030e01060906030c0906060810031211031b19030c03200106060305061305091b 65
    0x44612000400e16428203201199481d82c6001c2c0c0d000e00d418900403403040c8085ca14200c1d9440c0f04481e40507103140c4450b03941c6041c0024002c0c0c02055400c190104000005900d8003480d40000a0315150f21914200c0186050003421680e03e50040d0b004207141240713123003503044d1004001040740402440e80c940780e0402d00110b00c5803c084c0c1d0007405030709101a45110380809003011450b0a90341a2417662070b00d642c0d0f00c0125030030001d2500003505500401c0050710468032a401c520040d502c50000416041d64070b60f009821961141d1040c1d07036a02060b00107024940c0300d4058000288414502003801e801c12007242c040440c0b40d8070000b0240e02c09015440030745070044400d5410107940e08282d03511a0740543c0e816504008503da070042c14002c0f5500b9a8401e140c0d2034489440d00c0e0035581e44a003440d000c0e03800756403e07514035018219125400d040514041c43c240070300400342c0510784e804601c90410030b084c000010352008411000710b051600304800032000069450561125401d0780c0f002d0211080131 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 875390962 1250 875389712 875389727
    0x21040e0c0703030f0f2406080a0c1727061006110a06050106030608100e0d2d091401020c0f040b010c0803040b180a0804150e0409060c0e03070f05060307 67
    0x10b500038541840451150320410340d10a01c203803221084606c44d0754100f4804003100e40b107a4018080070400c00740c040780f50b13078902d0b44c8a201c0c0700095060441c8031207090700e200760101d0310072a00611012410b20940551039a401c04180c000c5030024000c0450f03050002410120904c280a22420410f0700c1e502c0702d8201c07008000800c605a0040c1c1e00b00103950b15840300034040c1101c0e004d2000c1c5442403420010055900f40f180c3c100d003000d401c001d0070446aa801040b41c00b010451881e2100c1c46118a003004694402d0750000d0702240983c13a448101840d02013090f140c1984040114155002400f4401664441589040300004100c8000078a24910f0005035034030031141720301030f015400100420080110701c086440c0540d001d441d0080001500b1480700307550f01c0780c44100814014003400b0400070540c07240640c254100180c14407040c6078408002040890307075148015202c02d904c505000c100c26400004040f0002c405034051b19400e03040c00803c0268400c2803081e14040c4038000001490f9521802c0d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 875392212 1250 875390962 875390981
    0x6080d050703020d05030a1e050916050303091306080d08060a14011710080f16090b1302030405010609020c010b010e030606011d12010c0206042a030f03020c1221040e0c070303 77
    0x191012100b42c003a030f5000140b4084848944512501a4210008100f480028120cc400400561a1902500a202504074125000749140740c5812022410101c14841c0c2840c2c1c110035910708030b0510300300c020040d071880590300180d0903043c01040006181da10280103500241002d04180c141c3c0c031521385841c030052a0393f11010107806560500140c481010035481c200c035001d4504140d2a985880c40402140d010000080d4403048480c0b190103203010039006540d2050080000281941c1c0d5204405c0c00d03a84448a1980036035036910f01d000b103079a00622407042e00f0ba0144d009002e00c2c40c00400185c41b64500344030188200b040108070401ea80c4c0d540c2641d07010425000c1c000d01003622100006561510203032422074440d403c80810100c170300090b4414005d00e000c1d4860100d40a451900c61103285001c00c8002e42c11070040e4825603045031240c0d5240100e15100703070010014440d44018280b28804101c7c03440c90310880800040080c50717440c00b480d03900074442ea030402da9101000e250a5004084001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 875393462 1250 875392212 875392241
    0x100509090402030f1207030305180601210501090c0e071706011209081b07080c010233010e01050a09090203030d1d01060305060f0a090b04030305220606080d050703020d05030a 77
    0x1454442060804000d4240c1b40d02c00e4074103020a441c8c80c1ca4440c05041800c10000c1c0c550b2114004000da02124240a5080d141c1503016130003858070b503190782d0300791007001d841900c00340302d00c003c10094030b00460a83e50b03004415240c00410711040a242c01c04004002d061681040201c100f0514560b106070300c01061240e0115100d03a40d42d0080035079009540d03003001401c0b0f040c0100100002c41c0740300451050310000059014184160443d5100c0c40e50118016003412104144111408010060075600d8007a00c1e00380a0b05e6850b40c5400200214603030303141c01c0850014109200c500050300c0c000207403104c0100100c13000c16000644000070030511072081c04c4041701d40c01c0140010900c0404518580242d0005084112694a04400c20140c41c500c6400600f0042c1003000180420b00c40d91001d40c01003d41001d046e912007203d5440307001e610301044152816581e4680411003010f08008044201c4801d0420f0750900c040c0f0313140a522600a00d90b0081848000400283c1c1b80750075501841484540f403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 875394712 1250 875393462 875393473
    0x60f02151506160203060915040210050904050a1521080c0a050a1103060c0931020703091409091f0f02040e0403110f07051e060705100506100509090402030f 69
    0x3d07481c6030b103039140d506000d0b4000e0140201007040c800c0041544030b8450b0040074510820b03220b0382d00784001c1c245160302010030072000380329003d000d984c2c038040e80780284450720300843d05001c0d04480b41d1040c50030f03074024160249540304460340c142c207144000c50f01c1038201001903160160041160b080c02400f22008045008100c184c0f0100000611503d446440c00c0d0304888155807070718a88882031241030640341c0c1c08900300050241c0c008400901c1c0380740a203000b00400b2641c207140710440598004100840100e400703c0c23030900c0241d458803450143c1c0320742115858114106a012280c4030060000c13062540702c0400c101c00422905a000813030142240c0c2000c664650b640d00058008140540b011800030300d10f800d040800c000c00203410911f400381c00c2c000d044140d00d40000c220450042c0707083d07007e00b660341300c0140110359204006050701d98081d0015043d407410b03141b1131104940008040c02d102d4004030201c0d1001c9603001d0281e900319501590140e60646660001074501840c80c0360058051164 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 875395962 1250 875394712 875394727
    0x2030a0209010329071b0c051023030c1c02040e01120302012003060d17040308040f060c05060705070305091306090e0f061506040803040603090309060f02151506 71
    0x1c01e1400c150009522454100040c0c510600c1c0d42d9054265841760008061042051000300141e9102d5590740c03055a41000e01503941001c254443c0d44100d00c4804118580c0c4401c64601c0e000403021900014207044501c1c3d450220071912590244000101ca841d90316001001370312820b0707040b05e000d400188200412580d441c2c11100090080f034004600550a01d076036021040609c203400d00764445424078681c151750710700d02800742d9960302d510107031294021070350b0030504000c0d03030002000030b18041e000a5581da07040890512202c1030903840b0707004001c1c03155940070110b4008a451030b08885180390035030740d42000e800d00301d405006903141140c1c40300c0710a00c2070001a14543c020001c4405040003881608400d0f0314154840101034000d6400350007132800544613a10311401c0340700c40c000c02000c0720b05081e11115010318580040d044600841c7d50703080d40380145078000780080300401e01c51500409111000b00c000b9141d44000b442d1030010348071500072884c3c10701e901c090b201e1803487c050401c1da1605070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 875397212 1250 875395962 875395973
    0x509040f1403430b060a090212010311030706020303150a05030d020703020f0d02150708280e0402190f03020409230907060206130629131b030902030a02090103 70
    0x100031a0b001c2100000d00102d00260003011000d01d100d4070894034a0fa440129074a440b82190390007000b0603480705d0303050300c0072030351103803d201500c039000100c8400d62903507040d032416180450003c140540319500c410001c000c0e41c0e9000044a07400444582c0340300e18a248003001c501c203540c941d0001c1e0b1741402441e111040d540d50015009088900031152944200d40e65000d100c0d003040c2101000e9000811800304000e0810307420001c0c080c0b10300c01c111007071078401242a907101c89240864901510703d1044401ca12280d07100310f44894808088a045151140e442904c0f10b00c444010010002c1c0700c2000030f404049802035040d94000c00300c0b840140451800d10b5001402e00802d103800d03600c1104842c01240b201c1e84000b5001c0180d9005400034002510340891104e100969a40200c4403d03480f82201c1d00302d1840300081c0a0070311441400303240e049100d00100a00820070680803982280340c800e18140d1142c13400000040f008050034002106d00460012906040010710040c1d08400c07a44000810002d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 875398462 1250 875397212 875397247
    0x2a030a050a0623121509071712040509090718060f0f06081b0c0a0c05040e014d190507030e01030e0316110f09010509040f1403 56
    0x1040345400c11109803203150f41c00554803826034907440c4034104075021605041141c081d94403981d400b0102c4003205202511551820402c940c0c10b01c030b0b500b044904200ba400702007400312041c0d401e000030742602400d824107900700340142e03c2081d208401c80c0f03020400e00e034420700405002c1c118454680400103030350003000014000341d2159041c1c91501007000200d4100c5030b07020000f036038003a031f03151180c0e52500381a596500c1d80d4000e80c040c41c0c0d142000000d1060b032080000300100b038403c20341c007896039141100f00000c80d10740111042e20350f41042005004400c0070310170340030300d441c3e41c01c19940d10307511600715036400c000107184554001d04000650388600030030030b01608000380124006007031142c007540300311070600802d0300080115000c400d080e00d1540c025000340741c603061003004032420034040000c464124468a00283c0704440c07401c100400300d041c06100c50320443c01c15104240a949824081299088000c0002c0d10b812400e20b4244100100404940c03440f0701144122a141d0320b121240c0b01310403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 875399712 1250 875398462 875398471
    0x6061a030603120912010c020706081e160309050102071b080f061b091903031b020f10090302150901120b01022116230105010b032a030a05 61
    0x4499400000502402200031240304400103005402e10030070a4002d01840d4000034140c550103c0b40d1780960303140c8103003403049100b03c1c0c080703038010149035140500281401c0c0b0090200407010750220307200701c03440034003403041ca410003134540201810b202d8001d0100d004140c42c09000b409540000744003814043e9081d07814a00d403141080c0301e4079940e5100e03009540d840c0c0748002020680c004030f000407800400b4015070791003901c18408851520390201e0018443c0342405000320080c08031540c050041c1544160340c910b08051004036041c00ca1441c3d000101c0350f00381c1c202120300c19460004450115841680f10b10001d6030701901070751052014452840c010b41160303103002d001a48208030501820030038019041f0344141078000e8004903040041c14010000002a8004440c40400a0f0307502d00c5103162100c0502c60049240002900c0c000c40d030054605d1030540b9141303035a81440b00501c4805102d2003100d0b0040501905072f94210170560b400d0803034488520782d1800aa4000c8204020307038050760805440f4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 875400962 1250 875399712 875399729
    0x10e040f150b1215010e0414070e061305060f090301140a050f0f060f01170c09011106160507050705130203070810080715030204090608030c061b03040206090f0d0606 73
    0x80c0c86941c0140180500441409441100c00c041403090000d1341e049110b42c00c1c1031400d00d00b41040c41d404074061b10400b4407108110102d0908000c001c030340c01090345a64400847d4110315120314001072030000700d66400b0700e600c0f1380b034000f580301084041c2004881300c0200140080c13105002c141c80d89031070340780c003214038201460900c000200711443c101c0b50079100b02043c00c0203450580741d02c418020440d510018144c18050880c0900c1003103030040c080c4622801000c4002070b503c1c0d901c0000105480c0705140b22200d03680c0310b0014001c80e00c0c44840003048032101031414980307898441c1402c9241542079882142c008004a4995601c01c046030000c5110b28843d41b64075100d52208680148601101d100d10300c095004130301c007880324840d549009140c402c0b07580340140c1000d4883c0b1521003242c074aa404550135510010340c5580140092000d5640100c4902c01e00e4000e6001800c0c240484c40f005100a01c20b40c00002c8403640c2d036889012580d120000642000c0c9a4040d41c80d0544c001c00240c01103461 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 875402212 1250 875400962 875401001
    0xb1014090d1e0b0a020f07060c18080d11070b0a08060d06091104060e090601180608010e1c0f081515070f021509030c0d0c1a030718080c010e010e040f 66
    0x803110b409000300e80403030700303041d18841c6000b1490312810010013202c1442001c110742b101091010002d102250700181c403524014110601140001030151104d0902090441c4c00040381003183d4081e04051b03510142003420401040e9542000048a600c070003503008100d0307840c1c40c509906200c0401084200890140c0701002010b88814003108000e6084540b070040d944034600612900c403c00c0c040034120000014085503043c1c640c400c2a01b5216080d414401d280d10000801c2600b208101c0501802c52039400d1a00030380243d000007c080b194001d20411038121600b0185110b030f1a00100d02101003080138049032950840d26142d07000d030002c034000341c4c441c0c1c0c2c1e89001064008200800c03200803e030000c00502c1414580790501090007140001600c036255041c034001140c034800005581c0c0d4103242c1c0305190380d9290550000c3c090020040011550a8480100307020f640c200207102240138009080407040b20301d801e40101d803280400b000480e085414610705d21074480301908121040c42d030b8100b8828 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 875403462 1250 875402212 875402221
    0x2010b0f010908030d091b0e0f070e0102061602031207020102190203160b0406060504140a0c08010b070b250e0111240907032003010b1014090d1e0b 65
    0x1580401070707016003912504200400421035410b86d1204045511841e420503405048010283e425010342e441804240c00440402190a149048080d44200d0a0409a0107c4240030000b5510040107204641540c443d03602035031258000c10a40f040c0b0080a403501c0021310f401c4030700901035005042c46040c000d9002c152a005140044151100002c4c03418248869200e543c44100c01c181c4050001c0d03483d030390b030789501203900c0e210350240c10105608810304400750f042c44880304003216001e82004081015610060140641e02011a500b054110001520300c3d224043c8041650305100c021801c1208550362000400d9006030900f46c81b40fa090721550b140c5880b182c2d00544621a1061103034040c03003029210103010703803000001f982000e486412140180d450350f840011004000f510001c0b44141c2e22152001e0746024001c054500c24143c541019541039440042c26141b52518041c000c14000b00d2442c4203510350603000c01c40f41d90032800904100c00301808000540e400140c058807480300d04ca0004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 875404712 1250 875403462 875403467
    0xa0f0e0a060e040f06080d0c03171302010806040b0d0312110310090e031606050114060711060a020f0a0f03020d05040609050609061c06060906020f071a0c0a0302010b0f01 75
    0x222041c1d512030341c0c0201451001c000c010600116a0803840343e4980010aa4050400006481c1b0803103449041c030084150601400c01030700c0e4405013920b10304100400500c174103592000b0801640c2820300303070382c01e4803120001009401a40728598104100140300010300d1350000200345040c500700400c010304001d48160150500c000ca44043c15049100000c025502080e4000526079214100340e030b0925a4240c0c62428220304100240c1c2d02e140c448c001407100e01400582202e408004442003450900a603444d40b104e8021212410700ca580045181c100d854000e2001c5410b0b2038131001070702c105810074079100c90529840c040c2078005108070403076941c070715004500b21000c0c0c4d0b18035200d443c0704505c4c2401300421a84030401c00ca8000109014854120341c100e036401ca0380f11204800480d41d00c0c1403090080030840705501c02001c542c4039590355004006c010407000c09031000032108007846243e00c07011740f0312482240003041c01031180c1d50200090540c194028001c7c0c0408880c000c81c000c1044004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 875405962 1250 875404712 875404729
    0x510050907051e1206010902030103020f06310512031315050409050a0f0c110105070219172208060f01061e1e0f0206130b1303050706020a0f0e 63
    0x241a00203c504003180d500300c000c0801c3c52000c0c8802050b0fa469280008485401c00e01c1c20307400003100540100050045140940841d0900c000c1680e0ac1c9040c15541d181c03014120100b0400c03000111080d003110340d2000444c0f00030401420001c5c224240030f20200da03000d9074aa101c030041015407410301002150071503003554481501142c91740c82ca8101814004018020003004d0141d10f03280b036681e2428820507009000e10441d00107143c58401c3c89204070380006096410082c02c090442d041801d105c0c26000c602800840900d4100d41d00800c04080d400942c0c440d0b101f0300203180145525140c8036141800003a07140d00030344ea0b058003a100c15442d50000e450070500280204400b20b4039424401e200301850102c0d40360000d031546401d121052801680041310120303030302e03038500080501c000000855010804150000c440000c941c504035015111100d4154000d8100000f48600b9400d07003007810701ca081620115900203108640d40c1125460280410b900c200701c0c4808500000000c20003403800c002d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 875407212 1250 875405962 875405969
    0x120b0a02090105091c0b040b041b080d0302070c0e01090537051e040308072c0f010c140616080601230d0504060e0f0a0503040902070303060509040510050907 69
    0x16621300786911601007110f00140c030700241d2134252001501e10082001d4001243c095030042c80300400074149030a088424036010030480d034011108010030032294200040c5a134522a040c0303001604da5006107045024040c6907031040c1c240414910010604000c554000d80c0514464070f07500760080c404010810080b11590421a0384400b807283c0e04400340300d10f40001d9880b01440302c034a200104003200300e40d04580d0030b84064000541403800c104009805c45401004031050405ea13500070030404580c540c0383c541c2d400902e802aa8006c07240811a40550600020f00d907010383c40c000d05600124940f650f03100101c1303150341c10454070407080c011540903240c1c05014840680d21036400400c0d501d80c40000000d00d01482c02803150404c0440303582080c52246902403031180001081c0301010061640c501540c2711603c507496004040c0360000a10000119011204074100168841e0002d040980040049a2049801c041c54070100020070201180d0b240321201c40100c01c10550f103d54582039918000c0e8003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 875408462 1250 875407212 875407217
    0x10f0503150105091509070806011209023604050c01031505011d03030918180316060c031515080a020309030a050304150606020f100908030105090a09060501120b0a020901 75
    0x1005004500313200740c1c4903a03c5400102d00d0b1141c80c103000040f031036002c1c00b150044009006403091041640c0c0c85030409070f85280031001848600500e400160200c0e0186044005c80c030701414081e0070151505108850a500c0001801c6251905007001602c40028900d0240001d1600b0000e183c00300d040c40b164015104181e449184044103840813031000034020001d1541481b0a01141950390707244c0c0048504101c90301400300e40d5060060700c40700030010b44000c42d540c580050020b28200f030846c003000d600a58000ca80407504801a0000350f00500814a02183c10282000f01062000d0f02400003d003044c001c7da18010785607079a829040c100d010541d00a8a1a041003203800340240c81900a1600b290140254161814051294100b00c0300e480c0d2107003000d83c00035140e901c0582402d021001c10a4602c040a20841415955000c810b120500031148107400b1003000c624aa0995444800701991200041110356102e80b0441c038920130040048496102c4100003840102c000c0c025a443c3c0c942c180c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 875409712 1250 875408462 875408503
    0x80301062c0120030a1809020f030606070309080a0803010e070c23030904060e180a0b011502030c060f0a0c0207030b040305071403210c031b0f0c15010f0503 69
    0x5400441d200440f4510581c45200707140c900f0b00c00004148001c2c4403c1c2c08a44035444050301c20007808015104650102c01c0f910710503c0b02003101c00c0400120381e071144007260900d079500725a14081d5201c031f4036500200050302c51660800c00300031808004505840c034000300809540e17107072401185e503103402c0039004001d5403041b02c04400b0160441410035004504005407410f00c00c40c0350100e02190b031603901401c645104103041c0700c041c40110011801038204500034103410a15900c81803004181803069540b8002c080e40d03507400ca91720a00031b45a0a01101c420380d281814845005d107100c1200703403070144220f031400c49080e1400e0300004841c0100e031f50104000e001640c454406403640c0c1c000c0032090710341c110300071034040001000f40010001c0212007026240e07841e20040002803079060003810b80460520810034031202c90341140b01d00c2c1800d1445541c450755a0019009440c1a0150306661002d40c070442d49410000307801e901c4014161407408018110721a61a020540d86000c1003044017140d0994 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 875410962 1250 875409712 875409797
    0x90f090a020910180204060305060a1a1606020307080916030b0c0d060b0c0a05060711031207021c0806090a09032114040f0b10081b0a08070308030106 66
    0x98455a60f111515521054400d0303a10a1850100e84c1c0c00b418000200d40d0000d42803080d5501486087d801290030354850b04240d06102008020042c100c1202c0710001c004603020311110402ca280ca080b00754804815505c0341030000c00a407134120181d0b130411650103402d54980c4051240c1810308116504000d01d118136071a0804004101e0b442098004146503d0b00800f14001210034024000880314030010a480a0340c0d00741141080c0000d40f40c101045800e04290007101d40020070b48661880c640e0b4003001d1600e921300264540100a50030000c05802848240861030300103403030b2445060144c8001d02c61343d80c0c10101d44222211360b4030040101e40f802c500780c90300c00c0124052465100d4188000500300e26483c0c00710b83c90403000ca40445003d40e600800004002d05007054540100f00840842c80c0207040224460304d50b041007828484400c1107000501c403943d10410b031407008200203820380b9102920380c01c0c1580e135a44240201800b190807900f0a0385180e000e00b9072820a180d5101554410104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 875412212 1250 875410962 875410969
    0xf0308191b08160c230f130c02210702040509010903051608402306090d11030f030306010e22060b03061801083711090f090a02 56
    0x200350959081c0d01400d289560020300d14242c4480a00082594a00400c0701c281400303518100d4154a1790058420719100842600d603d11145032030f2900703031404110403a82c2c020403031529440e443d1015031000c1541141501001b414000c1c00b0050003927030180465610513542500b42c503800c400080c0003e004103c206042045900c01c0d6003010300c2440c186240c01403540007408640640140140d68000118446100c500300501074412880d07460208a840741c41c1020a081369480c0d0348075808001d10760625641e85d41e42d83d900301c1d445188010002d446240150400d04c0169404014141c0644501904031084c0c40c80081601e114480580d42d240f00603d00d603050000030004000503620140b101600d0289012040c05a41c02a007040c3d05500d0700c2c0e286c0942003001d6070400c0c00130701ca461404d0790014069980040303030403022890706900c16020800c510340c0541c48007030000384070500c0e00050040c48041051100c2041d00641080318455500d498126006050140071394401c440d9502080c0710800505 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 875413462 1250 875412212 875412217
    0x9011404050c0d0911040c21051503030c0319110a110f060d050f0721020a02030705060703020d0506090f180736050c0a180f0308191b08 60
    0x54401d91500b407480c19120f00c41a81c1d2401400c8581150081d120443c0f8101441a00805681d619090010900302c112500004040c24150300c000c0b502c81c030000f0082410082201468040501100da0b03d003038035010300b500c9403c20544070b078454103601c44509246200300d40394103609070301c04050704a4031090745d294002001c005d00c1c0160070040c240500d03456555000d0140c42040350310100030540f0319080041000c8100024180c06c00d20050f520aa1000149501c2603030841405110042e44e501c004c08081c2d10398052064024010b00c50101080b815036416000f03040d0b40880c425041c4506d485200402200d4141243c4503000c051401000950a0904004550386c00a0850a80b0442c54884000c0e07040c600c003503041800e000c01c90368102c00b040e05d5081c100d01448085040d0030021410010140c280703a11440185170200720f40d000900280c8a42104044d000b040c03001021461140d583c6040b6103150445080c602da40e04143d071107542c40d81c2c021030240078811000031103424036003142d03603800950f074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 875414712 1250 875413462 875413471
    0x60712020a020c040501031103150c070308041a0c182409010c05010204060e19030506010b130b12090d080105060a1805040606031d0d020624130e0c0901140405 70
    0x51048500010f41c81d102ca20405010314010851252005c15103410305107022a034140d14102c14041904008040b80424143e0318504d50605d0040050384550411280302080c0c080c81010145008061008483d0f80100034554185d8050b907070860820407000f0401c080c45400d003076090800788020200c5449030000000c140c14a414140442c070300b42d95446960883c0c015820800200c2c02003810304e0b405140800c403840740705542220103203a05095540c2c1549030401132042140c01140418854240e02456040070043d00c5102c181c15181d034081805101e045030190740092150044103548000d00344240040d90607254003810042c030f0a81818230841d03c142c1d0b100d44c0400c4403c05d4110100d03032583d581c01141e0007851259000b1900828202801c804a2003503011701d840c0c1d03405003880c1e050498000c2021a4001200d2180c55149800c08c0608000c0e419040790703032903011929104a850f00e103129804001c0081d086d10840742280c940005014041c40e00b0f02801c4114000d40300701901a16207900f1690b0700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 875415962 1250 875414712 875414717
    0x70b0c0307030e07090e0120070303111b0703110910170a02041112060604031208070e1206010e2223030406030f05100b191e1e02060712020a 62
    0x24801c103203c0751402c01c07646030002ca0960b9158100e04980400074010002c1c40d10008135901c00b40148080d51103411301c20424000c052581700c0c10b030242040d4544040d00d0201240042d0380058180000c1581d88030402c600040306c104a21650482540c107000030810f12400283c0c034080c2d00305080400c0e285028940401c1d854103440342484010058445004c1c044081441840d001e803207450703240c1c070440c102000030030540c00349ea42400204041010170060070400c1c0106d0070096110303141d00004031940c1c1540301e01d041d0001098079642c0a480710029920303040320742c0c0b90a82501500c8070030404000c1500826401110800b01c0c24180110b000c100501014044040c0d00d560340c00c4d00302601506540144d840700000c207070f03101800d14110043e4091150b10030100707808403e01c2e0742054118035081c0103070501164254118240004558090100c07240ca44800d1102190744902c0c1402c01401e081c580700e800025510303810250705809000040641c044e401a40740d100450030141e04410081d0030480d0002c08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 875417212 1250 875415962 875415971
    0x309030e120c031f05011d1b040506030103081804050108071e15180f050907050d11160c0909083a06081b010504181410060f05070b0c030703 62
    0x60581e001c200b1503e40110b85800000311040c100420790803100140c0c4441d00c0c0008030845104001e80f83d048255000d054200c022223185505950110a4015074004541122000001005120800020f00301c01a4a003200c41c0c0031030350205c10f010940360227202d2601c0507400f0a509001540480c191804280c400c40d002064013551400c03c0300a046520a1001c08140d440c01c4804241c814030b4a80342c0a030006141100c0d14a190a002c100300c0f0100501e0101040001320301402000c100360090300e42d0010303070003019458419400b00f1038060482180c040301c1030034420600003029403940c0209c0c04020b030003a504c00d003011748514042545008012690f0b0351800c1650340301041b0603060340d00c2142d0070b0310054000741990420040ca403030b009001c48642501e1b000b801c0048040c2c0c2e84441158281c0b1342c26071a891011200700b142e14060030100700150f00c2d41c41d0388010070030041e00310b15000080764899583c04145054400082c0c03070b54450502c014200b401c03060006001840341500030358108245280008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 875418462 1250 875417212 875417233
    0x1b090f040b18010e07030218040b062b0b03011a010e03150403121d0c1201020d0203040b040c1d0a15080a0302010e0c300a1407060f0309030e12 63
    0x4820041c540e2414403060b580c100144076031030503c0442070780324207682001c5181824808680c460780ea2551030300c0d8070a54072200c03c0f02c1c66440d41d90545600e41c02c0b00c04000c030500e210710b0b0701d2102d03c0742001048070700034035101d00000c0314a01401041c0300f540c40c035035251800101c46d80044414082c060203568042c8500c40c0340e2801c0d0884100c00e14401d5000341d0750142400c01d144481001da8100c104c002c200c00307940c07c007a440302040101d0300c101e40500403105000c24052002e07a490180c0254401c541a0603c04410031007032000b09691349200703d03c0317200d01d0104240c843c019044900d601000121200c0064000107051403034603405020380d140306c00c6100100598800380c1c54038000c041202100143d460302c401c1c800054040000c00d038000b0049981045a070104104107100c42c1c2b06601d801544102e420300d4031880e4100f40401080280c201c0da98000409410840c0b0365144154070940c0d002400380102c1b000b115119110304021960305075a02000c7c410707450200710041c403441c070340143c0b18040c404058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 875419712 1250 875418462 875418469
    0x100608150a050915090c071a0907080f01091208090706031a121e0c010c03031109100c03020601050613090221130c051008160c080406050903061b090f040b 68
    0xa40300e058a0a01913042c0800441881000400078007542d403204802d00009000904403c3c003180703040d0480c02c06542035a80c80310403600d402d4a5502c500000e01414854000340740e07042d0030402400340544001000b0622002d8200c0b00c00c071044400c9080b5800072602400310b00d20a800c001c0b440141c00300c8a007101c6403264005400850844030442d1030341e0142d172140c00144011f0078103c2c140c00010015141e6134181200281c4100f510700801020503550380450240d0740c10741425542d1084000e8203101d407001204038054540210041c081d000751051900000e000c8c5040801c4072030b024010a80c07400401c0c44d040508000e90808164880c0c103002c8152034050011141d42010b2103420482403e00f09941a03060070316290b012034010360f0169901070113059910b0b8100841d1074100b8020050410301503074040e4200c0e5510210f9074000c06c2c2c140d00140000b19244d01501070408003404405850050f2034844503d1903a45035007442d0b2010310014015150f043c03406003000303003086001810110703c088042000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 875420962 1250 875419712 875419729
    0x80609070e06132414071a011202030f0705010c0609060b1e0a08031918030b09030d0c21021317030a031815090c05100314100608150a05 60
    0x8420000d1800320702004101403d0b40540080260003551840040742d013840113144641a20a842882d0400264030040015038078071520161049001400e407961600d9040400d04c0e20800268400e00c0380c20401c001c3e84601040c070400b00d0b8016111074422120325500c00002d840140000d46141d40d50f030321944410740f03030301c07003240b4100280465440da2030f06103e023000401141a000f0105603802400f2000407807103240c004221030541410403000b5140200e11000e410b000c0d541008202d913000c0f03028451540340010240c444034120b52018050030021500864074440002c00600c090001c2001e1032880b84c1e02d90b40100083e46000046141540c1c59280c4105510302c00d05400c012603000040b50b80165074140700300400e41c5402410b0300785524a0b42c80f04a487d080340c0e180107141680d00e182d00d400f082002c2c3d048400a21000e4548a12002810300c00b8005104260440510b01d00a5000900841c1d01340c9a40d02502c034039440781881034480e0034400c845070003d03070f0100c2d4001c441c00002162581d5078070341 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 875422212 1250 875420962 875420977
    0x12191104141302040e0a020d06020915040905040501060e0f040b0705040f1202100206010e01030b100306090605151c03030203090304080a0c03050d08040b06060702030a200f0907080609070e06 84
    0xc0482c00140351040c401110803500c04821603800090412006a548040010303d568101c02d000d80c642c0c0310080090000c240b045103030310900c1d400044c00a0030403140e4100038031943c020300082110b035985106503112080121200b0b101006140001000260030191681e0414140d01c1c2030390509031134445460b85041e082d000061441d200240900c11450700702d85001c2080c210b8805031029515140003404080c00c1070200804403c1440d0004400029542142d001183c014500b071052008509142000b0007007074601c16588448000502c2c4070b0300744880312501001b100701d000400102d071a20100c00a4202400808a50000700000100075404020b407042d03490080b0269107105182d460050314041c0f01c5c0e0140300c24881c0080c1000007045903880c1c810390103007064441d5555800e0358800a42050321010006041342c0c4001c03240d188a075042c080c241e0034004180e0381820007035542c42c00c004c0b0182d01111090f00103005440061640d0400d4141c060b003220090920034245441d10b000a50260081e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 875423462 1250 875422212 875422231
    0x120e0f030c0f0d0806014e06140105130f0b04080f0c130e0307020a0806060102101406011b080423060c0a1713141219110414 55
    0x840a8002505010508440b14403000900048001c0c000181075440002d00c414184500c0ca5140c0010a20802d1f2411100c1c1480c070201e071711041d1070011085030410400e00032030300308030070048009440210312416090301c0310400e00002a0120400445450380031120f00340c540c00c002000003404d840c060a0090141c020034031055107407818094030500d4a59890102e4000c0e43c40003004e0209501c40c2000942c00904011000c260b18101040040c91845086002508206001000074840502040443c0603807001da00340c4002e6000071900b40252000008a031034041040008036400d0740c01004124030030701280e00556051070503515a1744107034202e03034400c0701c48091940085400150840c1c1c601c04030034045030100e00f440302c003c21080d40e40100081c020580402415440d021240d031206845062020056240078136855003003d015a004c80601c007802120180510090031030b010590411040e61840a00525000c0d5154803160f0b401240e10f0350b80013076842c5804484c02a110709814030940201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 875424712 1250 875423462 875423467
    0x1a0c060108030c01200306100504080d230f091c05030309010504030315030302101512060f060501090e0a1109040606080402090609010b1b12040324021306120e0f03 72
    0x155000d0030360749031042040200b40225401c8007205c0305082500d41000302070b90090031520072040c007600d0520464200c191140700701c03080b03c1c1240f6407120303c2488005800c2d00138a103481002e90345003c14003408141c0448a40d080c80b05541d64100107480c211408040c0c42d205d1400360b142d4861a0031a0700541c0d81d0741c100c1c0d441e1020041410f40500a011007a07041c0880c0403022451034030020745500381007007507210450722901d140f0081103005050761302038411680392005105443c80c0860007401c9102e000302109041460004966005204410840c0c40c40401991310395920b06c1c4c0c0000500b03003054845001d41003440f0301034031501ca0344140d0700500000d89651a40c0e0805004001c04c22200030306842c481d140000040c0000000722082e170311000030000b000c01c0c45aa81031010b909180780c492101c1d00815005c9000024080000484243c01c05000310715080300411a0749041a4031910354104546848600c1c200015889406103120492034801d00003039a501c036402e42401e05642442c103450940c0301 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 875425962 1250 875424712 875424727
    0xa080a05102301031b020703030e04020306061603120f0501061e0905040b030708010504050309090a15030f0615060e03190506040b0c0c01020d1d0c0a1a0c06010803 72
    0x140d2142580280806800700c00040c5082490b2100100b407800a100c00d4440750201c2009034000d40091100c8a04104800c501d00b0aa05e0000c2d91a8401d1009800003031644002d60090700b050701c220303409454040c01c800d00c4c0003079806840c2580144020f040f4204403920f240171207c0c1295106030700800300074042c0400c0395490710000030035070030240040c14139480783d0542e44003602d038101c00740801720740c000c1c2c0d0045080d401100009040402680c86008903509050800040010200003844040001c4030704030f8490703d03030340d032828202c44541d5140204202058001e0000c140c042e1100307030407079200c0d58010130340494207003100c0940152544500041820f449501840e03103801d002c0044140a41c1c040c0c035170784a803d80c40d90f43c0e4440010700050300c03050071900869007007000001181c2c81050448000d549e1988184080401489000b13007950003841c0e9800c00d025400c03808034219221840041c48440104e00b015120091913503c0080020340481c1080366080c0c024040c48018000e21310a0302440c2c80c1d440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 875427212 1250 875425962 875425981
    0x408010207171216021516020f0601150806130e010507030b010e061c0b0910030302060105151206010905031006170102031303030b030c0d240b01140715020a08 70
    0x50402c40d626030402e001442001a100400c03507480030742d01d80d0340c11440c000b00c50181c3c10b0144c0707107042d80d00f54283c12042204100e054807011540580b680d080f58192018200e04649400c0b00f806441c2088007a04801c0c1d99882c412600c594201e440209170040001e04207205c902128808295040c040e511030040051b40340d054400c00c0450002800c21507640c2001c1400603201348200440060304d540503407a070031302c00f003000c0c1c0c05901d0484024008440f50f040808030b000c5903241500c0304030300610485002150074284036040c2c0300304452807910203080c0f002c00741c0c107082c03540303c01448641009102c0750002451b40e401c05c40c4020103980e141000a800e820242807540d4000381e40c156041d40d030700400030b00010500c0200c030301d82c1d410f405103070009100c0e01420000303040200481880d5841602c1c00340200a000c0c0c02010441d89180d104440c030002c84bd01c6403d0415542c5000042c1c0c00315061400403201e080720310000f020701c0c5104800e510041114840d02c0c104076005165901d00140181080044081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 875428462 1250 875427212 875427233
    0x3031409060601051c0b060c0a15110409051503030301090f05010801150b07030c050a03050a020d0216050607060608030309030a0f0e060a030906090b09030c070e1312050c030408010207 81
    0x226054080d0065181042c0040e28500c01c10b4840b00d48009200e281402c08207807a0b0020781c3e50b000080c0896900c2001003003c1d55a91200394040d940000c1e4003038a0131111100d4491032510400c510f07585c0d400c00d45804002402450000c0003080412484082c5804565061000718007900c007072080000c280f204142d111084500582007149180e14090450460306083c401e860126481000965511042850125114450900001c0c200e1085061150405400c000900012241c59003124400c40604078104ea1340d00001a003c0e0065074a00c0f411300c4942004030041c00d9050040314042142942e541c030b5503242d80d2040700c00094581002c112074880c175500080c008045000d80c54004904482200010414030a449115003403540d119000070400a250f0448089250010700100140ca07040705aa5200c1e0302032842c86006015803d004900e4001c200085805003c44052000310708025640d5030302d41d40e5001200005110082c024500748440400040c005807154200140c1c07a6003c40c40c00b451b044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 875429712 1250 875428462 875428471
    0x3020406020c030303240321120c1306120e06010807030506160816030615170a09050c0405070509030706050c06070504060c30050405090c0403031d1507030314 70
    0x9070420406d00a6030100c0a04891200854145c00c00910000500007032402043da100b55074000123001d8120308000c40c49001c0e2102511034500c1303c80035610500f120b80c040c49000300000c1e00599508003806100e00c110600c040c51825910300154244101c00c0c207525006d000d81c021246c1f980019418001c02805000482e08408074a100d440d0200080d140548100f200411551846c4280140000340314402d07041000141000804a0006401d0510040c4401d20f40c10000142031441d10114980810b00d102c1c019000e6088006411010000d00800028000240c421f404010080c043c0d414240ea052010100501842d00c3e01036956100344a050f08103500108464107000003444200491908444413207450b0741d0001c4401d03201c2104090400384002030b02421001420782e444c006822030382020040c8140c500449151465917201c024400d190f215600000300015000010301400e469046602c03645801c00404146040004d801c00c0002c0e41c00a49003030b030000792950015003509440c41c8105411 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 875430962 1250 875429712 875429719
    0x4051305090615152205030c0609061602210c041a0913080c07091d0c06030a020903100b01032f130b0c243c0703020406020c 55
    0x10361a01d03400c942e80360769000b80540706485a6507446501030f541c0c048960010f0b1541184c65454200c0788600a0007940c50000d40c0844a0f042107003ca802d10b400074111b440c00000505c9145492060000d1203401e4000c5001d00620800c5280243d0060b80c4049201c0c12034220b817211624055a00e85509207040084850305000300d01e44451044800040c000301007040009944640503a102e031904e40b507901241e80c00141c82c00101145425003540007043d40c20841d1460350051021002107544c0c0c05c240d02d100c950130318442c0d220001455450130141c000e10703070024040c01e006041c042840301080c2004404185000c0807a075418418a0300c2da010b205148480b43d180c031201101d218480070b001c1c0f1200c40900040082c1030017280c485a4402054900ca025084600506444500030001e10740d0750340c0f118620700c82c101c11100500001842e299001c51080e540300c4018031050903008090b9480740345080181940c10300300c10110004980c507141040c0034240d141d900680c0c8510307241b8000c1c100840304440910 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 875432212 1250 875430962 875430971
    0x201020709110304020f060c0a140f072904170105040b011d0c0d0b0409080301050a0b0c030406200102070311010b0103020c100b041d010207030f03050105100f091208040513 76
    0x5116416a056950199040d0303181b04e41e86c0c2205000413514010b41c10000440d20a801081d0104554500c0141c04106440c2c115100815105406070316600980605800396113420382c0c03a2136604440303c0c072120008404425516091300c1c0e26a140c11102d2414601e41c01da91540280810059845520390050504a20101c4520310501d4000840d60028006500c03654003c101c0e81002420b60340040d1003901e0040c401c11400c46640380061540e0400d101d0f446c450a100c0e47c00060b080c1c0c80d0412a02c500c1c2403e0043c501d4641041819030355a9110000708020281c142d00700041018248014000da0303000f03031282c540e80d15409000c1420b540c0410090341c1014014040b0072914600000c04035508a540c100203d07603440b00102041c01002900f03501340d002140c40003985095803045d402810344900940d5072312101220a44141d01791507080c40307000e4012490002c1d0b141664450302840b03001c5000c1e4581405a42e03900c540d0320703080250f540819680f444002400704128130340b1265403401301c24002e00500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 875433462 1250 875432212 875432231
    0x110a021903211a010c24060b13051f140703050d0c02031305010504080a0609051603030c03021606080103030503150a080102040501021621030203090d080901020d36120f0201020709 79
    0x1000100c0c440d0f421b13801413103026450300c14581103030045c001815007454401e80712100454002504641d070b115550044140481c542102038101d0b000c00c41003202e0752101c88441d1101001c18181764031005d0140c0c10040e050111019109090190400c0c1c1d100b1035000f55120300000a00440845560784007505115080004100d8004c0204200c90010340100300001c507840c0d1400c18a0404442e80e07480d00c00000d15020110406400800c020900740c000e40c01c890000d001c032400a40114020300614000c01d40120040000a1283e4011984084094201e070003000401c000b00300c02c0d01c103641005041e80d40118040c0807550381001118400810780203807104039494011462081c000a01c2d42030388910140e101c100c117140c000c1003168003100c40030b05181d1820b9030341e081c440703030907082043c81174014020141c003007111034454035141c01c01c45c580103c0c4c3c41e100b0070828986140c071300b80055440e070b114003040000640d0031488016002064056441700c86004880d01c00282040324940040c3c880514000e50345 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 875434712 1250 875433462 875433473
    0x3306180603030f030c030212040b0708090a1110020f1204170c100e030f061003060b09040b070305060d0f06050f1803120406060905040f0303110a021903211a010c 71
    0x408400140d040c00517588001e82022000b1f40305a103004004410054240002c12282c02d100a1082c180d90f61003140b141c6400890944030059110080c100210100c0301c01814a040f6002e9050309445004880380341d4140c45141d41448512000c0021307484004c1010020034031826031880f401c05619000d0484080440001480b01c25024000c070200201900c45074002c2d00c0c01c0184400d22000030f800c8591525050050351100c490902007100c0c10342c10700c94a5920380c140741228a0007680e10540701c140c295102d0404034001c0c10001d10303040d0b0210051007040c0200713200743c110302288c0b8042c00002c1281c3c40d00030412490388034003800020302034516080f004400e9001101343d540030703a003560803c1e4054449041c45c03000703009039030440c040345071400052008000109240402480c402d0710b0500803d503290040000300d009050003c40541c016103180d031130901c564207100c3e010611a080c11043c1c030005010b442081c4840c1a414a0790381ea0716200d04004404902406407103034024a403004083e00715603140c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 875435962 1250 875434712 875434727
    0x807020a0201081b04030b09010e0c010518040b0301021303031d0117070c0813060c0b0601080105180402030a170d05011208040303050c011b02030909060607050a330618060303 77
    0x5107030b54148211040d09130b03101100848005607000030781d851207030518100460081c00705400c0324690b0b1241c1c0b0217403546d0707500440503158401c0a4669140b41022240f041c003000c0d211203894964195400c110902510010398460806103001c0c0e41d030980080000304082c40752810a51000b4103020401500c00c2501d07000c03516060348050140381c03582c80301103186015841ea01441d481100114003070600400c4261740503000c1c0071001d00500c1c94000300c0d1100c80c015a0114401c0c00b616401042209a01c040400c034242000d4000744041c04540040305a1740790307449104100c1c680e85060280020700c50804083c0c6001d56809003903011901d08104d60700e90b861a180d88243e02c0000c05004021454172050705003980807942c4010040c000da020040502402901d03680003a225034030403403000e00411000d040110550f0b502c0e80e031000080c842c84205443d01011f400a1044032242c11800611761001c40d0591214980708601d0180b01058660070a0302c03940d002c035030318070320560344620307101c400c1000c00da00005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 875437212 1250 875435962 875435971
    0x5090331030f1b14130c1409060c1207021527010e090703051b090a0303050f1e07150c0905090705040f0311150a0c03080c0d050f06010807020a020108 66
    0x1040d00020800f4a0080b000440307100301442502e40302c981c0058260610a074152913510700310b651103121280c0203641d2040300c5200c0254070000d40700040207a4040c00f9400103040030b4000810040c101070b0f0100045240ca008611512901e030710120741c02c1c003141410f0392400200c51861002e241801c02003038034a00314440c801440600c240d02c025242c50141d00030301039030f001040058019112403a000001402414060364841d03240540101c8000321081e964050340c402d41c0c00141101d00e001c7c03854400b140e01c1c0c0c1140312415800c0e8010402d080030f44140040c28082c1481c400181c503251040f03410141203404000382c03000c041030704080c40d211910b90700801090648100302c0781050691100882200c450045400589070100e10081c0481800b252004480342e0460860b00f03407100c640e802c91041d116000c0c40030007070041802c085410001070301074aa6160720a100103a50380c10204030208038415140c0680d00a68521450028002203583c0400c8003070740820240001c1c00c120205500003440800010b2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 875438462 1250 875437212 875437223
    0x5060606030a091401091401110d02030705040b070c091109091f090e01050a050c0c030703030230100603020415081503012d140a090203100509033103 66
    0x80000c0351082e007640b0110741d031504141d1621041d204001c49034000c0c90001300c1540c450324010056a1028414010b9454003400d80c500141081030f0304494202942020b4080700601009100101c2d0184010000d040c459002d440004001480c0070000000c0f00e4840c1a2140c01e01002c200410361900e40c10025500886030740010001058456840c06075800c4940084020900304a0358445100c415040303035003d10388001e4104030680340c00c969980c40d0700c83d48018444036002440b5101c0444d00a41c01b42c0405003d40c5980e440e4080070300302503103510a000c01c042c26090314800a000c25405c0e141c41c00005850309041c114a400d0825411001031000c050400c1c0c10031492200040000b08101c40b0742c5000e12014000380031100000400c0c164043c110005061051854441c4010480080c0102a4003d1041494040c1a110740e0017000c050b2260741001c0c0c0c3c141c4288600c96207908502e00c515486031a0210203181c5400041406440c1c114000c800500c029892042d0340c0048861510300d241100d5004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 875439712 1250 875438462 875438467
    0xa0c0f061b020a12291501110f010f060812031302120c060412060e0115090b0301140103050114150a231e0a17030a0f0c080307210504120e032a010201140405060606 72
    0x20001e0514080700709d0080c403119400c0112070f1038a4501c540000d01500c0d042c0007511884003250301d0302107440c04211462014111100d00d03003000350824a0500a00c8410321003926100a03044000c80c1c2994000d51082a08044c802c1e601d00034049a841341482c40401000240200311640c0b001000c0031149016404550303644803a5010599002d50060ac1080300c2e64640c101c2c550303581c0c1021402000c0b400c9a01507400c1c42c00700018501521030a0804002c40001d100300c2c202c07424120000002e10300744010790f8060302102440e089907901d074201d21500035421941101564241403e000c2d44e420103600810b240d40c1d1840100c159144c0200a80d4005603251408482c070040291080306c091100d0303040a8079010002082c0070400380c1c882d8807071041081d000700d4254011503540c040f008481084038040c186141c0e0076031450200d44662040d10307480100504541e004021140c102c014040700c01d601c02c1195509100d030984550302030003204403940580d4260351940c80c0a4807070035140c00e00140b0841c803802c0c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 875440962 1250 875439712 875439737
    0xa0f0327061d060a090302010509150a09110603040609030219080f0c01060b04140a14030a060f0e0114040b0f0403090b090301090f050a0c0f061b020a12291501 70
    0x2101a15a844850b810855030386050583c212402403840850039070040d400d24001440768200040d0704030740c1a01e80311543d44076903074051081d4020701c03c404045804100a00b280c00440c0d4600c00070318065070085400165081306403070080d00d805500c645440c040400d03450220080380e4540141c0704c0000304078030003903640e9101c032003194014102c54001d00b58140b4003050128503010b0109042100b4101030340c0704030445886d8404080002040e0344a5541540450305000c000350b11a00210b034401c0c0f8000000c2010200580000c2c20355084041b01255030034450b0421081c4101c0000f290780040b82801c204010781802e480c0207100d034203580900310050900007000740307061310250300a14070140c10540400300070503103161003922001a0007060720341d01d42c0c402021500784140d440c0314084500c107444130814500c103800103003000c1c111110240c1e030150802000140040c3e080408044603031164582d20501e00c110340781e1000840b04503440c01c5021100404102c000070040341641600c89090a10100358042c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 875442212 1250 875440962 875440991
    0x910090b0f09151902010b030303041e1106030a0906063305090a17010f0c0f030f0b06070f0b0c0304030e28150905010305040c030b1009020a0f032706 66
    0x9040c40f08550b1040c0014803107204d41c1e00c03000148a075440c0b03640240440c03908a000c15540b0702060720054038800342c03101c0c1c2c01809000f15aa00c4945445805070088034035a110001d600d6401c21680c900d105501c3d440c1b8002045510720030b0001138214034810414180b10204442c4190b06283d48030300220104c0c0c8003a02c2d4050003a020b88984e81b01c020900d54902c0c0d02d0703080c2911030302c2100022486039800c0110707400e2800c2250091038a29052581d46144d0210000c00441c0070703010724a408801070b90399840c0c3d001c5645540d0018071005009414090b80402c80c1e107400c1802e03030001804c11155000078811b100002e5072010461141c540115142110300004045141e218058010400c1ca01c0040d400002904007000b030344581c101a440d1264421207645100540690f281110014010200c02100340005600d4100d010740090900c8150500d040c0c841400804036032040120384d000c101561552496107034540240c0c2c0c2c0810005064000da524500d405404d10080580000c140c1078490340200e68880 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 875443462 1250 875442212 875442229
    0x109050907241106240d17091809070b0d14041b05030714100203040f0602030403150c0e010809031303141014010b0906090603010b0910090b0f09 64
    0x10310012011020244507100452441240b410900030481c2110451403c1c00c010408034816a01181d0500303020104112000848903140d0350503501c803144034054030210341d0b0b024904465814101e42c580d0f80c4d0001900308048408203100005007480300c00e0403c4280c10011400200300c810700c0203507940780e0a9031382500d8003800303480c490340342009103490420090201194203000c04100140140e14225121010705440f52818020718906c45000c01a08151341020200b00d0b040150301d1058030308041e00c400d405c002c400350550180e40160f10110381441030045040c038a4002c2d42d03135100308000d0090402d1020b04001c4610554030706020f594030001d10101400d0007284c044a8001061601701c5440f4a0a030b80f00300c0b0b0f4102c1143d03241c4902142e0307000d0000349104045c4079511034600502681e1800c100c075841c5600500085411550034071140b14992a03800140d4040c055248400c1e84071101c1c1c90a0118450200c0c0708081004110001008030000e40000c0300c2084025411465941c2200c0c800300e045007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 875444712 1250 875443462 875443469
    0xe0105041205030319022703070806070f030c0f12020a031508010c1103090a1e1802070302010c0309021c050106170105070801120210110c041a0112140109050907 71
    0x10048540603000b0070001000440c0b181c40070712503219a09610494007002c9005515158185480c1d802c4601d08030205925818100c0c1d0005080780c05043d11644100d09000c01595100c0103e1403400345034112503054042c05040014901c1c00e210002503102004002034814034070041426400038100180c148240c004800480c21028841d08003691080414000d15041c45070400064081506844003c0084120fa00441c03000b4580d00c41c0c2070070308a078810702000804c5070074070310803e202000400e01e4030204a04001900524010b850307031a40d0070042e095a040241d08000c05140c5425030340180d43d908140700001610040020000c103207031070658010035007034220055107100c07100c01107480001508114410034107650b45483c1e0380d81c1d40112202c050640940298000103888010746520311442c00c101c4040d03440801c8810b8240d080b8041b40c1100c000c100c0c14401c1c0707160001300c1d50785540c004802c0c0042c881c00d03103401c01843c00b00f0020aa400c01040c0a03041d40306850380d003c985017980401c4000d029 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 875445962 1250 875444712 875444729
    0x150c12060f0a24080906010608061210091217010b03060f1201060501170103030210050c1207020a030f050c0a0807290a05070c0b070c020a080d050705070e010303020d0e010504 77
    0x510f884000d4012900740c0d00c0714899040c0a81100c0c41205407040d04141e020f541c84400410090742482810386500c200100400c2c1c00208d522700420144008002840c58441150800106840e081c14039084880100d00d01109000c040d2100b0030280c0078001403981103401030300b112038a031b45441c03000902c2c8020812001d0760050b0000da00e04600441948900101c0b4000d88510000b001180c48002100100f48000390150b080b60043e1032601071590407495000d000c140c605403404640b10007205000c4070550b9102d0049c0c1c04655404101504007030070514070340540c2800e81c00c001c007050f0342545e100c94000009040c0b0f41c010804a08021110140110b0941c5003890341016119001c842d80e0a0441151402c100508000103d10300c1ca0094a2000c2d915400802d032215903510100c050342c5290511804036004031408900040d868424000b0401800c02c640d9503d41d01c01d0742d81405413511180340c1050420001510042001940006001140500c02d0030002d024000010045c2c1d400d00599011802 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 875447212 1250 875445962 875445979
    0x120a060c1404060504180b090a0504110604080609010c18060e0a0305070e090c0d0209040807020d08160b0a0e0c12120d06081902010e120a080c010509150c12060f 71
    0x10303555000030161040c5c0303200c0b0b8841480000151110000d540c1c1045110350482300e1400442e42118081e042558018018007441c1d0140e003006020460079400759100201d641c22413030070301c81009070a0003421607108807498001a1090166080020070583d40b06520270b12041c01c04000c0b4940724004480f0055401c413003540d581c42c1c0e5500c070480400300200c94250407405281a240740e0361030040c98008100d5009010142d959803242c0d288586680181e0060768040100034245000503600401031800440c0710070304180800c95807400c15448007024062070426400c00c4003030114850001500410b45200b140d81100d0300351349148690134081c0c03080d18500707110000100c0240f0403c881c4c001d00e04550908048030036082c400000e81003c82c1d01081b000f40040c2034010f425105140500c0618031341c485910a07201607102540e590313155a408400c3c40301442e51240200900044240b21810140d201a1700c00300e840e10381080c07111035511071380c006480040b1800000c5546a01c030040c078005410b001030b00819 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 875448462 1250 875447212 875447219
    0x50f3c0d20041508010e09060601030b0d020409030207050a0e0402090606030601090909053d020f0c060112020406080a031e09210c0f180e031216030506120a060c1404 73
    0x181620f851a145801240c203220000415604444065118012903009002180c9070540118068403202401650060030f0380d1412015a0303445c412403560b64841d4000306103207032820741880500d08040e44070700c006000d03000811000d40c5070301545550284007100d480d0394940c1e0b01c0c0010380304140c180e04900201840d01c01090304000303000415040899120161007030341450650030404120717604104408090403403400e070410003041c0d0007514440910644042c02c14020f040072902d401e80981c0004114007501141d8000d40c20144186000b801c0101d0291141000b1505c001d003540c501100c81022880091340c0c03c0e08480e00c00e40e8000702408500c4424020800c3e05810b0711174116483c0015150002c1503e0000b680b020040342600c11070b42603140d18002070342214421402046032056040040c002046085140540c12501511400c031602048000c4a0604001400c458006159030300514945840e4203a030840003986001140d440000401e825500c04411281610740b490110018040401c020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 875449712 1250 875448462 875448479
    0xc0302040f1803021b1f11071e18060308030c030912040e060301060e01060e04050a0f0204030c170106140d0302070819050c060f19050f3c0d2004 64
    0x66018045e981000f4403401e911300412003d03403800041d42d06e03819040c00e00704101c640034403000304a19403008181c8828a07500c444c5101d080340c102040d4241d01140410070721600c07403000076952403a151068200040350440d03942500c0381c40003500a501510700403002500c41e80c4100103180d400480105215112542d64030001e1050405481c001d01c203500f8003502240302c02d4100d003c0c0e81240c008e1341e80d03001340701c5a490a20000302005816042d0b0710b0b450310041c08a20205000074030040d40b207940d0084c900c40c0b91101c0e42d141d800843ca440c024030f906120003048130040f041e440e224100c8044902c0005c101980c90103929004040e40301d20140d010701c491000860450030f90420025006106640e0560303644010030045205800c1101c00b805401c0c0600c1c5004110040082540c1030302d418018500410382c41c0400c855002080d0040d900c6001030008155440302d15410340e81c8140004031150560a100c101400c140203216440800030794442008200031007400c0c03007001c0e4240c0c2e440c0040e0303959142e000e407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 875450962 1250 875449712 875449723
    0x50303120708090f07121506060e120c060a0e01031e06090c0207080a0b0709030b0a091101030506010215060307090f060504180f0303051810270c0302040f180302 71
    0x88040340c200400103507400404500c1080056095016141d91806c00c0c40100d000c0880460a0b00d00350700040d0403070b030701c00b0681c82060090840b940f0343e07481c61120304040210b4902400205105600100300150860700c62a0681c0c003008218240645400d107408012030091030441d040c40d0030710710034404080c4a02901da002c0d40948050803801e1001c0300135541c1c141da440030588640c0245a10080d5420b001c03e000200007a081407891400c028040e503a601e4460030b070b40d0190b80710200c10365550f03a03441c01c120300e0800107103032024282006d10a6150240c0081c2d2a400740014104049c804d11001641c0e071398081c411107000e8048104104031500320222302078010000360066601581c9084040701e01c00d03061602031103a680d4480900842980240c3d001c4018240140c8a03920020b140201e1603c01d05041c4000f5240441c00800041c001c50712031001c6455400060703408500340009107444010410344840e51043d283c06450109545008a40300c400814a2014042220184202c10340030194003040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 875452212 1250 875450962 875450971
    0x6020d05011e05010c1136060a0b0d0c05090d05030d0506041512050a060e010c020c30030c0d1112120609071106070903020a0b030106230405030312 65
    0x25081c40850000d10340050a01d41c018540800c0001100e4170000304040031090b1403040140c18401034030000c503041c201e030030079031510a00740e10801c1b40d00140b0803403204140755208200700c82c0c0c10036461802c04108400e104540b520a05640c0390321540c81d01601038001c5803203082e8068407540803d500b50030540d48940000070350802c41c81c00d02012940b145464001c02c0d4000d06189403031a085460807007104448122080111400e000b00803000000ca00940f144101c50301a240020032440800e01e4020b00303007050380d032103548202101640080c0070f01b41202407601ca010107156104414a90320902403440c0102c0d120081d40e07101c0e10899103107035a40011020706048191040b56007985c04803034141002c0c0074490344048005810340019000346032681116400c0340290030420350307a074180540b81e402d0200840b042c001065000508000310b0a103031152070300402980c0b840c581154103141c4010312481891001140001a11726518584080b200c2124002d180040440381e45030300040004010010448 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 875453462 1250 875452212 875452229
    0xa030210060803030126121804050f0c0a0903020607080a0f09140d060b0d110109060e090a0b06120a0f1802151806040b090f100e0108060d06020d0501 66
    0x211200e50088180280740c1030700c1c62600030b1030840c0c1c02c000002d8003040030509902c41a0380e203022804948a404d120a040d907030b1010703d900c3c1d581c2c25445c020304506448508064001c0349400c0c108200424004902170301b100c40203414035038070190321104a90521240d040650310210002d920410801c5840062600100f05d850f00c4001ca150400159910912841040c84d049140340c8070351f00500d03200e6040c03514035124010000d211000c07240440e10360203ca0300c040342c5403000c130b20071071000b980c212800400171708680c40e00d201407103410b00c04544140030150241481a80742e140b408031540c0e819050b038034140c2459056030581c3c606613210b5405400c0002407908070900d44150b9543c042c050340d0403000a190090040856255101c079618007503401241009401001c000511556a0300d02008200034030101c0325090702c0b190994104040c03540282c41580c401e03240a2000c10000750803910500d05c41500342801d081c2581d8580104008840101c0010b01d480d02c005aaa4615040c079802603040e00d0488 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 875454712 1250 875453462 875453473
    0xe060a0b0a050102060c0901121d01201602151903020706050c03010501231606050f0c1201090c120501030f0b060909120702031606020a11040c050d0c090312020a0302 73
    0x30b01c01a611040140e50111205004014203102540100da115040c014034500000301e061002040d800201842c00b03083d45aa511200c92030b881e0303a008100e4404c4018420343e114603141c1200d2407010381f101d400d40001d004002c60040003000b0624030307041d035401100f0480944801c00e04680700038000d500c01e9100310b804928000100d021004582c094034142c1d40107844003010381c100c81e620700074001903000319840303204405c00c02c100343c3c50500d04000c4c0280e40305039008211400c040848004282c40189801c1c224402804a043c0440b21a074003541190203040c00060b0410244000311100500d0442d800203003030030a0000800c005c1d100c80800b01550240e0044940d540380c000c100040c1c42400d41c6c2000c807651041201110b40150300004188640c8002c00726071191200724201240310255500c1440542c00401c800d02c00e0081c8103404804008003110b0411600c01c441d071001c0c156016414103060120341d80d03160850454051001ca13805940c2040c50700090440c0c0d600000d40e610081002103005003d032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 875455962 1250 875454712 875454719
    0x5010b03010807060e0112020912100c08010503010917070501061a0c0606010201090312270602090319020616060e010906020d0c09050d030807090e101511070e0a0e060a0b0a 76
    0x183d05e00414080b050b952401c44401101000700030b0b400009c1c8103a8030040d001e0043c41d0701e1a041024035030355180c0711070100e0700210789071700980380c6401644500d000764103100400d000600c0d01c0b81c100281c49003031011035485021908010b80100f0701c0e9000b401611301d400c095500e0501150010341418240082111490b0761107900484c241d40c001040100456030413060070490140641190000ca482c801403500510003500700040c1c40e0880200a0300d0003980000c5401031400d0074804202025006c010b4280c560783e40b50b0104030076218014070031102100f511824010030070203410070650751215000130b1001c40102c1c200000290b00181404540524000415484a020795800412140000c1c81025452201d0310140c414100040040040101c00740021030312280e0540030901403000010030314030841c01d001e036408040c000010140d0a0101d04074030b00f1a525000111407041d1a00da44500b69191a0345089001400742c00070420f0060260408001c10b000707041d80710000844040f10544006941e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 875457212 1250 875455962 875455967
    0x21090e07031401030602030612031201060908060405060a0203060f04150906120c0e0c0f0307020f070e0f15010311040602150a0e12031f0803090102070915050d060f05010b0301080706 80
    0x2d8400003500403a144900400110350b480d03001e15803040f400340c0b80000c01e8500c10071860039035001400d050b0809000c2d81c0184101039200008501516001e00103107400e01703243c0c988903907c131402030003804110f0300080091815140c00ca44922082d030054403d0203030101d1100e0340c010008850041c40c01003803400c54005114039800d126080d0541c0c114555580e1541071145030901d040d001068502021070801c804480c8402e040300442c452031095002c3c10300d10001148041c01c0004a910201c2400384100038418047c546400c0d046c0c200c003030300442c1d259540016005030080c00c004c1c00c6064070904007040010b842500860803020242c043c0050319101e94600700c072102141c0c0c580400b00d60700e0740001c0b200e201024008006640000d030100c0e00704640799a400b030151806440d42c02c10800ea410101d140c130000e58040201c01e01900000ca0280074214204403407030259000c52080794030840d0200031441c148940390f4804400c5030040380717080c416903841c2c1056500a41c82803003101624403d28800240451 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 875458462 1250 875457212 875457221
    0x30c051015050105161e1a0610030b0a090c0908010e0d1b1703190e3004030501021216140301032004090302010e1009020a0303050721090e0703 63
    0x505500316074038640c1000c004542c160054480e40d460740342d107101d003500070451241a10500250214100e00c101209184c0446842c205400c0480340350151001d005503980c0b038540340038501d82540380004080800d50001004141c5962245108034a0a0000c52581c0e0340980c10030f003914954002400500079022460350b4820202ca07400000072040c80c103003199000c40302c0c4800d44007401400c2061041001c032940b01703581c0c0d10660310400014170b02d03003240300700025034043c1140074450803000e080c222480314842c901c03040c1540c21142d03d06000d4584c11528180d611300ba1170141d82c008000b152a04140e0f07106640c00041074400c40c015040d8002a805030904c224003124401e0300042780c16083d64a156103160540d0502d001c0031944655241402e001070b16284940c60b4190b01a90012030181d030f00302c1000d4180050390b4138240d1100e040603050f9000d600c66030401d43c1107030383c03500d807070f50741d0340c071181490034a291058514820288440700e02c200c00590010640090702c4640b030009440d900c0f4a42c041c0c0466 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 875459712 1250 875458462 875458481
    0x5070806041404080a050a020709060f030309060e090f0a09060f0605010e0a030302100c0e060310061b08040312020c1503010f09060e06130f1d1b010212031e04030c0510 74
    0x1c200401c000381c103240c170501c003400d202c07c420f00441c1c0c0400c2d101e01c0000c058032566002005640c0c41000e00f0800d0540c0030700403500a0004c0d08000001a84d1440420b000b5a0f0003080031101a02e031502107005606254400c500440c2c0040e800c000721252120f00d034000d0041031040600081d0f108007042801d2401c144154201c9a0540040c000e038101c1d6280c00001e4006511080c09201c1250744d280d1082c2c48150040d44a402c08102080801e03040c860098410030301c4040f0081840c904180400004040c135040f101500c2d000b503010007508204070400c9150441e01601d06812a4850502c401240d08160285042c6c9480600340380c0280d481e90600c2d400c60b42d044c0301e00300302d07807401c41c02240a50600001803211501501d0b030124600c92000d20030001e49059821011440100050300c405d0100e09100310009414500281c10400540d040001e40c0e0303815206c0307c412802c4000010492010a030302a09404a684106140807403a26003005000b0003c0400152454001d412072030401c82014468407085 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 875460962 1250 875459712 875459723
    0x80409092402190309170f28021506120d09031509020f0f18070203090f0d0c05132903010e010c021207030e04022803060e0c031905070806041404 64
    0x51042800c4000c0c5c140d0714802e9844140d10b042d0801003ca8200040071400d100c0e1138200d98445071454000d441075010241c3d00c0700c5500400b81d594010b039000c100f00b90075400c4c5002c4148241c452400040c61821900f25200c03c610502c501caa80ea0b03034000c2d00c0b0004032401201c06804111000d44804140c0384020303c0294031140c900e007031140601d41100844920310740a41800315041c2440c41044050000b55504005a40041150b25882c50301d03000c000c202000907140c80c200d0781c4003503903501110021806502d01c10281000c600c1702c0d031b841c00c3c0d00244540c044a007405070302c0034580e0010501100002c202278041c0d42084510240301d032050190b080c41001640c02060288100000300703150350084c040c2141003199a101002c100da4a40c0085c000a1032040d03107003102000b01100c0914040c0a40005506160410302e040003040308040360280d124003210042a66582c0d411070700070702910324480c11140c441c03524090181c0d45a00c01109445072a0650b01000140280d8000c0800a001100d00030b22 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 875462212 1250 875460962 875460997
    0xb0c030108070605160b090708240a090201110706031508031305040c050c01060b0307180e0a02091f080604050c0f09280303020a030201050105040203010b070f080409092402 76
    0x4a407213440184040300d11a1080300c2c07081c070740342e84d00300f00d000050314900c04a40c4a01001e12846401780072004800640410507010380d000031048552442006003464000d56480f4020300c1076902800c0c4100c09101c482d400c0d215031a495450203402400d00d81c078401b003a01407818003c506440f0010869001901d0a45203100561408040002a110403000001000012302205d100c400090007803001030100f000c0085c0d100c2c0703844440100f240e100c9050040701c0c05210318003002403501d0980243d800010800c400b5a64503a04804580b02c03407140055504805000300c2c20140707140e8068a818001c11040310240850b84400009510a0041c8140c0d081c089400f00403600261501e2100e6000d6a0030020312200c0c0d18810350410100080650b105501581101c20940304066080c8074160140000721421030565051446101d5107000e8074a00402c02002d40480009100200b0140d5004042001040c4059081da143c800d590031018400074a06503901c4400042c0103c0a0003502c84192036aa001c50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 875463462 1250 875462212 875462219
    0x721020c0d050a0219081308010b041109180a021b1b0a180f06030503040b031603060b0a0f0e060d15080d0e1903150b1008040b0c0f1b0a0b0c03010807 66
    0x460711103801c50125881c203c1000001f600da44821510002411802c00008011304804248800c2d01c1040000c0c5034244000c102290441c0da400d20104a00010320003080300b15070700c50905a00920440e540c1c50449840544d10032454600040c500c10000e103580c14000c41e000150040c4220360521703001d180c4a032250a4041c142007d596803000b0035184034002c01003070596907621b6407405c6601640103004002d50000801100075054440040c01144903c1c0401c1600e20703008010b5107500410801e0020482d413500d00710300b8584a40f00b40102810010309880d92855403004460003420340b442c00e41009052508001001040031400b20060350705522140e44140c10b0800f0070030b00e1a540a50710a0040011401001241c000b8840f01030f460050320000503692019800c00c00c0302c0b0841450f050801058a0070000010080c408054021507154541503c2d95142074455840b8040c13451098a41c4180b4521030402c0440003030744041ea50700500403144540c8803c40950024032090050041c641d00150041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 875464712 1250 875463462 875463493
    0xf150903020706050a20030714060108030f07020310060611072103050915030c040e0123011d03101b050a211e1e02120402090721020c0d050a02 63
    0x41c0305150203854125080d145c5d194030481096241540b5001d47d80c0042a034104008981c0240901d0360303840c800400e060361400d040d00382c0d02c1c440c0e450600c178400c80201f981421510100a991866400b10005100d100e840c2e0000411845207a09035011920803910000364854841880720b00c00e80c1e454810454008064030166050781c0b18070341041e007104045424051800d454006140124840c103d0541c3e110f1402d9490130160304180c1081e00d148240c5180000c3d2400a4040e403413204034203007044030031030b0f0400c40c2d08040a10000503e9400d8065241080e01d4a26590302022a5810341d980e810285015131204135914096501e8540129002096103040b24010490341c3c0100d0b680c8007008121038508400410040d01010217826030301e40c9a0000101903243d5081100240480100840c1089918601410704e080701900190003400f1039070100d040c082c4200d02980002c0e03d6000c440c600742c010039148000075401084032622038001c018030040312611039412100503001660003041c51000c0480107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 875465962 1250 875464712 875464717
    0x21c03090b151206090d030614031b0a0b0c1c0e030a1b15170604020f0702120f010e030a0807050301050d1509021002010c020c0405060a0b070503070f0f15090302070605 74
    0x55a02c040701401503140100c040001c035200307580d0035011b0aa6400d00301c00203001d541d0150440c42021a0f0303d50b1901d07094a0000e40f0740b010301d40c8048280201c030705820105910410940052080c0600081c80880c0707a24000360040e000324400340c415500d0f40c0c4c03103202100c5400c5143c1100d54940c201c010008045908410080f040f0740f4440340103401182d1315846200581d08000d422400700d9414500703080c61803205040664490030946055180c0b85140141c80030030303c11850024400c2e0032103015441c0c50b010801228619518810082156020500450760713641c004200800006000d00700182c0600e2040041e02d04a6001a204803400030040e07a4072061b8000c284121200c0e255038040f150056a10090b020001001d1500002006504c1502c02820525031004042c0501d017003030144503c1e0380702d402c0071400f1240500602c0d901c2d8031840c5020b80c254441d5240203040c00e40b040c2d800409101e60f8030829002d4074030034030030508552951031f001c02c2940d20300d50014000d030b0410801000928060f000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 875467212 1250 875465962 875466001
    0x93603120e0d080f070f09092d0506030714090a020703020c03070f090c03051b031009110a0905031b1207030c0905010f050d0c140103021207021c03090b 67
    0x4280801d21511080c40d1150744944800060079281c1840040381c400c0c1d464a402410a03d8550510b110300b03d40603201400e98800c2918090f0b580315030034003c1030600f2104000c400401c000c0035101000d1480400500010780d6954070900034120b001801c80c6003d8851882403c0140040d1010354603070020303800941000100f541540500c50040b039842d6024401d003005401182000c43c0258104507200c0d00301e40080604500b818500b8003401070a0100c2c01146c401c800340a00160790f2565507400b90000300d0581e03404540e189007401844084441218050144c45020b59500c2e84a41c1e951020590746170100c0100004d0040110003882060428188a02500340700104942059a0300d40d603c80701c0c1141c0d503010140d000c2d95000103201c5234000310480e000400003103038111110b584030745076031209010502c640e9001c00921040707813125074069015101130050300860004585884003000e91290991146100c020b2403034008082503600034032580d440650008802d003016078030480315060070a029039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 875468462 1250 875467212 875467247
    0x15090115050307060e240a0c03020613080301051e100f180302180a110f09030f120a03020a090312030b030c0a0f060c050c04181101030203010b0f070609050106093603 73
    0x3d0b041e01b04006250020710b070b1115142c1d42c9064020440c20001e04040340501500441604520907102240960341600d0543c1c108650b00c420101184100300d039144840b02c05580c2104c1d155203507020b960380003181181d103c0182d403106000144007143c901c01d01401030000171f502184d140c0301e4100d104402c2400c158040e1034544006050f008000500c01d55400610000d180d01e5000105540b5034242400891039402c0c0841c01440243c0c04646064618010b624030a000c0640c04a000c025451040c0007000045420002c000000041054002c02401c0c40c80c460380e010f403082640a080d03d0400d8030004e000c5400c04c46450465509100c1e080b80d442100c1d440503200c0c0e12070f2078006c2da070f02d0362207116100b00c050501d907405820907114505002c1c9160356010441c1410b2041c00100302d13140340303442110640c00000142c5540e4607090b1411000810210742d0151896282510104032100a580031304c0460b0584603141c14029102101411101c40c2c0c41010560b6140c0c8203110800203002d82d03030700e5034444000d2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 875469712 1250 875468462 875468509
    0x15070e0301090206180f120a030807032a230a0c1a0906090f0d1b03052206020f01180305090109230103180f1415090115050307060e 58
    0x540004c1c1c01e0344c1103e01c0c01080680d100c40c9010b86840d0403c0340348002d50003138940701902c2c03070b29551240c0c58148900f400b609010801e00099405840b0740e00004181c114583d14240712134403107015400d03112050b9408d10201d0314440c0000c40c0c001c45154500f54045041460714030381440382804680c2c61384401c00840d2050100c1c0c81c02240b9040d0082e030b8503c10011b620003080340703180c0301c042035150000300040f0085540000020400e05640480440d01500541c600b03529400e50304e180407243e910404000c0590031614011f680900b1032200403460443d0090b60881c0e00c14011241a182222131350520034001c14000c03200c25001030701417400740003400414104043c05aa540045002441c02c0c20800c0188007000c1d00507012541c1c2503c5031904580c0c290009454a01a581d500c200071030020348068241c2443c42d21803142150b003040000300000030b01070003000340c2c00c0c80992103021703000110305103009010034034001c1480e04000803c2c00032500d10b6654043e100340d604051000c01c608a2141c0c4d600071b54231 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 875470962 1250 875469712 875469731
    0x90b01171905010e01150e011e05060315010207060e03060a11040b0403030509011b1e170c06101a0a030c0e09040f0219080c040e0102120c120915070e0301 68
    0x1812607107016034090750001c0750b0790040300850b0342100d032070b2046200b403000044002c3c4004150326204505440d1420120340390f40150351000160407406500080e40480000700300140da05100301d036060002802c1c0c0895405544450054501c41d1000b0201905a070108002908007507517600444110b2900801007480c02d9140c102e4400103522503041580031910001c2c41011070750340a610714801456080d044404242c071595072802070514411015182e8141c1070303901c4240101550440d403400d844020440d07891b1590103583c0e40710201161010965a200d883c00a41c0300c520711022440540006034582c582106400190020050300000d8410441130503030700441d5880d017030800da003d540900062001c4425a104015000c030b01d01109039841c042139102004403020016421100f402c0c00c0300c0204407509218401402400341c0807035070302000d41c4142030000b007108075401000c90107040200c2c80c107030f56100b12106035a100150700d640d21100254000605d410302c01c0f20000a2040c0040010808260307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 875472212 1250 875470962 875470993
    0x5060f15130e0d0c0302060f04030f03090c0b0c0d02010b04151a360103090309050f0d02060d061802040602060f060315010f14031605040525030915090b0117 69
    0x80081600003050007000084e040c15010400d4551084000c01c01040394589581c00138071155100214500780340c1c840301180304012045440c1009446055043d0f030315240c44090742c40c0c0c1c581c01e510404001d0f52030100d05040e41e0a05000f080c0028466110040088e46800114100c121220040c480100c0c024000120b0381e805105101e10040c603034a465080c09891703240c200108200300102c80f41410301d801e40701d03c0001e810a244000f1901308031600000002c4900c0410651144010000e5000000252650000c0e03203540c8000152008072901212040031100c645040348101e004801c056481140002c0c00c2c03900440500d0b91000020301550701115198106103201d80d820781102ca040028510300344803110401d0102004414120002d2a00c034100038002004448140035a900413612200001c420111302041246041304096003210b10482d0540014020107840100300d0f501204142c0500080c10785003d0800e242c4c4d04150000f2a80c0d00e03000c1000802404261b6019480c002c00403485014007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 875473462 1250 875472212 875472223
    0x1060b0316090e0916051206010311010201020f071214030c090906060c030c010c020c18010b0a020a020d03170109051909110d0c0305120301060203160606050a0603020705060f15130e 80
    0x48590000340404031900c0c10b620000401c5400c07040c02590000d45201f604c0c07030001041411280c11189a004450306031004034017900c181074180c0b6510300c0000300708017044030307207140f4010001040d0354803a50001003081c855020310043e555466045020f008950481c3341c5298600d030800d000400c007a20305185400350b0703411608440c0318070700c2c80c0c1d41d55940e03429040d4050100c8448880d00301c4180041d641c489268210020301030190700c00c446400305801c54454020010980159002042d0300d070208000c5c58001c0c021500b0411404a030950344000162251503802510701519105289118280040c4808001801e103504192200356208031003103a0b9803507422070101d816000c0c0e0a40310807142141412482d14000c840300640c590002c00041080c07560120580e03110181684a209850110741040c6c8c003d00129007200c1d50115900340d00103001600366005146407446401585d00c0e684d20002c15040480040320b501c00329030400e0a4000003890700c0e1100d0b45641d0340c184070000d1204840341c1030a142c071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 875474712 1250 875473462 875473471
    0x200a0e13060e0609101b1116030b0714041401050d0b2211070201300f051909030504090e010207140f0613020303120c09041a01030b0301060b0316090e 66
    0x1074000c0001d1000c040d4040c4449042e44006041c01c0c443c1c91b005e40620030304005d03400441410005080d1090f0705d800001d04c54604c55245224002512a450741002103021783c044e10243d0104a20061918500c00e110741038908443c000c01d11a0064078103100192550b602c81a400d0040340c1e1799041e90071a41d6140000080c130b144c0c400a000094072903040002c422078890741000c02d030040083c001c10b030050b079004440c4405840e00b8880310a900400ca070025403242c80070700722011568100304d44151201c1c00c56005a12407042d600284800510403040c00045840901d000f07000503a0030131080c04151419044401480d44041c00145040c129031100150214084150a4950004020007051202c108502030700060780c0c2d0074280703c0f074003184c0c0000c1d038130311a0030051204840c150000694124946003a0749600c80b01030401d00c4942c0a00c5682d41e80d41803401c60090200307140c04406152400c2c144518026203541c1c485041c40c0da01c071036952001d0680030445090403c940c100010640b130341441c40c200d00a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 875475962 1250 875474712 875474741
    0x60c2003030108010b0109030b0a020a05160302010b01270b0c190c05150313031d1e01120b0a170309100810050d050a120228200a0e1306 60
    0x803541090f030ba881c2501e22501c5860304010101000f400400c2e450444660055000400140e68420000f420ba489004100303c005192801c0c4001405064040d00017040030030090340c031300e0000842c8140c4460100546040c4440000c0c041000748801c2481e54001d01b00d400c940c030103c440ba0400b0160351054141480c00072540c00000440802490822200e144072050729000d1250940c9001090200f6025907060082e00300070071030100a40803448082c0b0b4000004000c3c000f60b105c3d072541546204428030118000e800036904c120003501200003889a00400c40004051009562510319031591041c0310106001107030100300041251559046802c004210898840c01c91a01e0408a0100034008582c0524001ea0102c004c02e00010804200d1083e0701d6880820b009443c800d50104a151600c0c541c4150409a9040c94a91102c1104240d0381807840c404d50309004101c0c2802083c25509a0701020745811180f800424415002d040e091a940203045007506400343c0055160901560490f2104000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 875477212 1250 875475962 875475967
    0x1a040f08010b010c0f03031104090e0d0503071b06021207080405010b060702090a0203131203020706050a060509040f060b0a3c12020a050301240608040f060c2003 71
    0x205008500080014030911000b0004414100d001820070714042900034078001321500c0850400d8001d40c0b151411081807181c640e00ca0340c40b001c03040d00a00e01c000450600340b14041d211100144203100316440340c00155181c03450781c209201c3c5072841c441d451400b100c40715001d00030803d0320000324200030301c620660b17501c0c828241840d0421031300711003089506a000708c808100304400341c1c0b5005076080e040031080784016601d03600c060880403900d4103000000d158507080c3c007512403900c4d456000381030002d0107004108030310744541035002c2c1111118800d0035004094240064080307502002e50700720b000d00460002c1001c0c00d482000614024060300085480045011020101444406148450403943c11000700c1d90300344000c2d4642618070f500c1010340e2006100300180c115140c59000d14000d0034060024051112001007002c41454015201012818403000004515205455090250750001d41380c2110100b0764444101601d1840001800c0c8071508002c00700d03e00710700d140700124504840107140c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 875478462 1250 875477212 875477219
    0x6090402220f0e07050a14091018050d0c05061605010c210c020616090e0c0c06092a0d1209080f030405180405070b1204060b040e0307060b0105041a04 66
    0x200c801e0070640216160803c844104030065400c04111202c82010b030800841c032542c40c290411151042189207a0001e980f407000410fa030341c200007400c1602d407440002c0b0303620ba9114000d00241d51140d1102809a03042840c0400075820300100030054062120700d198030b180c1d040c1d160942512001424480055070145205900c501d0380d042071016080310040a21001d6041a8001d5441074042c1c281c142d021507803107211201d18000d001c880c1c001e1160311501207440c40c0c5218100e5282c0c2201b50303074400502a1000113030131420b0208400f4414914401c40280380c003060f500c81508440305500c80c030b4005001521560120351b1b80c168103100240030b40d8039040b01d20b05000400c0e00304a0356850030040d80d401400280b00594500244419807424000b10314a540d6480c00c0031485c00c2499888015481000a020b510103503240180c80e1155024031014002c443d445814401100e00e00b10038803c040c0c002b40030390300010b000c40d0045103918905141c0f442c2095200c0302c1c0400b10303000040340784001000008041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 875479712 1250 875478462 875478479
    0x2070c08070608070f030603031709030415030518031c050411040609020901021005060f01120b060a1e08010303140a170a0225080f0d0906020f0403031b0206090609040222 75
    0x1744541d020910b0f007801710305e1035550050001514560b4508000440c84006a07541004000ba1001446121024180c0c0e55052001030001c0409492040307040d808100118091040042100c240061148900c65244210200c000081002070011140701380740c282c00044c02d079141d014030006005500c1e4010390f540d400500181c58a5800d03204000000e040c03108110590703507040b00300380d940340003030070300765002e104101c2208010010b6070b000c2396110718082245880c0e150b201690304541882c40c5600d6202d2840b00c0001c7d1140da900b41710040001b40c200d0003410b00c0b443c645000d024501c98509012003824500d110703031445501c08a5621002580c0455116204506441c11112440c813070214069142a141ca415409110b80d00c6800798020700001c11079031814082e031003000700540000c8215150f507850745140029034402d12042d00040d129042c040700c07140b84007103c039100c170303600a00840c589554181401100c2d0055400350b41e00a5003840b8202c1720700002e040941c064480d88111210b240d0a00d00360 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 875480962 1250 875479712 875479727
    0x310090c050d0e0d0813080c0601030c0e07021501060c080d291507030c14030f03041401051e13150c0305160804032313050a060f05040902070c0807060807 68
    0x9811403940b080c40d51000f143e800c06861783d0004202d8441c21040034050502000c0c43c42011045d403c503104450000060015138005001034490b0840841007517101c144040342c0d1001c03203503a401007401050004020160240c52810b44175845a402c080c1400002c00c0e80e441100d02c00b00350801100c0848403000020919100304c003000ba9022a40c1220540b034000f41c3c2c1a8074080c0c0b00000b001d100b02c1d0b035025400c1c01400f0b040010140d41c20b10440e0f948901880030140c0c80d80007a00c08031070052210180c2c02001c0018081c0504c11048400d40409440b07082c444100d03110006018441000100d210100104200340300244078010619008501c03188514001000c0f603c00402c10340102000051000c02c40b07501c603d545400641600e899841c88180c040a0920000c0e84a0000209100090603200b500310701801d080c111b61044641040055444205440c11b0209601200c00140c0402c030600040c002980036004950083d0310180c00c142d11400704c070b4900350103500500301007082ca20400405992040d003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 875482212 1250 875480962 875480981
    0x40c1824150207120b1806180c0406030503071203020c0703140d090609031419030e040606020d0203040b03100302040c08040b060f090a020702281e0b0306060310090c050d 75
    0x40443c07a2500903a4500a81c10042c0186100c42c010b000c03d600c4200c1e00c2d00e001c0d030920385000ba50000c2c2000910b00341280880d06a040302802900d0f9100a05d01d0580302d0700701100d070030002032341ca407034042e50355980100148402c4105055013880780e503101c2982002200c010394820009074640c400f18000d15880c0040c800607980402103448000d102580c2c0c4101000110b0303a1100382c0c5518104942c60413400d092035080c1e4058600070303414040080c103030700040440c200d174003d0740d003040010784625040740c0394554200d641015900c100030422055010740011688540d0038001031040325103130750008050700e900151000005815905110512520013136103a00300104030365042d82c00205002044400c40005e06160800d035004c00c140d401c2d521010f41c03510049100c03035111681110100c0385e804440029000c0d503e140c098030504030140c010140400800e4403c01410b20b0b0070341d0340c2d2008016140d44014404003804010380c1000a224815008600e00c0c0c005071388400e03858034000d0144001300d810070035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 875483462 1250 875482212 875482217
    0x414100f080c01051b150c0712030603020105190212040806160c02010e060d1e0f0f0203040f060b0619020105012408070305060f0a090902010f08040c182415 69
    0xb4080d484a07a00941202c0c02c1c14260780309043d80340198841c84d41000c82074081c0710011a040c804215a505018000b40380c02e40c070400100d40850100c0c8402c07400c461960000078080752040045c0741444804400100300800c4510444515007030642127940a50050760060f4044d900440a0010540004814a4441403203203070080345c0c50b4507500001e0940400b83c40f818024200040d69603c06111178201800c0105c1d600d0884450802c840d1000008082101e0800701d094130b4948a514180c0036802181d008a030802e004010010840d10341c10000c204803480c0a51001080001a8000e0340e0100f40b18003504030350300002803e602d40b00200301e406600c0c0c40740c20072030781e070341011142500c0d08404055005041440c0c00140d503540c10700803400c1040494040f42c0d0041c0381e000300040d82c44190304241d500c42e00c00c4c1d03111000c1080720401501d20074003e82e802400041c1055040c0300424000c0c00484242c0082100803e00954492203511112940010700c48a0f0034204010b00c0140c0c528100c640405030b1300d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 875484712 1250 875483462 875483473
    0x4062c070807051803031c180f021005040509090106030303050106080601080a15090e06100902040e15031014090607260c09091f0503070e04110414100f08 68
    0x8480003084808000c015100340700f008201c241640d10a000c044c400b1002c041c040325950307001c201813503a544a0800011804d03d040145c3d101c040e803807ea40c0140001e6210500000c400c20320760030032800c907805c1245641000803c0c800020696102020f083c001c00417800009011811802c1c02070075160160030007005c3c132541c1021703c510340c0d9001082c0c03a8001c240f1100000d8281e07c1007030310768117904d4944c0044040c0742003500c01d03081d82d070020403503e02548524549200155490303019406038082d03840741d9000f0f40180c60010742c83d0481640144800750008082e074450b00c0d600300e069000c0304c0b00902d4800901b16500c042046e006020080740d90001240d00f00f0070b800e41d004205480e061140010601c0100c00004003090781e030982c080071b440d21500c00a041c03198500d040150040310a4032404000c0104018080c0040c090601040b64000e842da200012081c5a41e161240d000c4604560f0072150071036581c24070242d901d540c034101c030b03401005c1400f9a04041844e0003c000c440e00150340100100d500320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 875485962 1250 875484712 875484721
    0xe011403011803030504050a0206040f09060510091e03060203010b0301050f03010e061501090302063603030403033617061510020f07080d090603091104020f070204062c 74
    0x101d035031a00590514000c9546c1d41c1d240341842c00d000a070b02c002900540003007400300c4d142c01e0715107a110558011040800c00c483da10400c01c210070183c04490000300d50000805d00005001070316030104084410703155441c29580340e541c102268800d0340702c400c0c00c00c030110050046103018421900e4848049009200c407c107400c2860ba16104040c266002005180d003031103400e83d0007030441c2002150014515600e60b0070710300074140450b0100c00004110400140c002580d441034202c18540c041000c2c1c01142032030704640d402d440c00610719901d444100402d4032490b001c070105240003280b0381c402e0bc0690500a1034801708050003403007006411100e4000c2410440140303007d8400502d140411200e503e8071030707520101642030242c07100100c54540244500498103060014102203680c01d60341e10081960b03a14802201259501c1400600301d02141c03000014078500f030740180028000c215aa1803038443c159000030704071541075101d41c006007902658a4140e0700f8039400382280803600c400c080d590380340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 875487212 1250 875485962 875485991
    0x80706090f0603050f01142b0201111903080a06051c020102010501090b0d111504060f0810180509030d0f0f050a2a02030d060b030910020f0d1a0a0e01140301 69
    0x1014058110350350080311000055549040860030601c0e070110150300c03608e04e00c02a4002030083c2140c00d074045460310b91510180c10340058803003149480c504070742c20058020365080342d01c5a005014085251744841001c540d41c1c0e60140f1001200000e56020303c5805141c2c4006800e440d0140d011580c880d2034050170700c4003904d6000701080b040354404c80343300201d000c0c1c100041110104080d00612030b40082400b00e003280e040111144000c0d82500da400c003503076070203000310b08150750f5000e01042c6c5040e00b81003809030b580a8100d540c00031107010503a410300f00241d0000d0b0440d1100700a4020b595100c8038040a010064865150420050342050110410980095001030500d248021041c0c15510030710b00420f1082c01510400010305a0910440c0e0342ca00a6007620742060780d030706900c0e010707440122074410040d200b2580303411005885241024100140c8000601940d1804144281030034040d55a40d520410900d0142120700c001c0c0b400c1d54104030415087ca404544c015010307a141c0315002a41c082c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 875488462 1250 875487212 875487241
    0xa03020708060c09151e0d1b09050118091e0e03071a0a020d060b04060f030b030c1005070b0702010903120209091b07050d0302220b040308070c080706090f060305 71
    0x6400e81d591740d0fa403507409000c02854814802119a884103410314004d030680340300e00900c40400c039a08140700214404036416211a8071940c2d610108050030740400c62035011300d9414000e081102c084882c4140e882003001d05031240d04229142220a041e500b03032901c406841100002c100b404010343c107000301c0b9035034030400340c007001e4940e888000180f0010308414503170340458400e40c002038000e104030ba950391680c2003945c106002e03900c042061800d82c050750501c640b0410001520050080031207940308014000780020707606020003001401c00408011454000d8090b005240310340c0001941040e80c01d004000703085040c514610b00d401000803081c00d540d001061a044003c1e440401441c181031a40400c40b0f1013126801007040c00b13000c0b44520305a805034003a00c0b0140d80c620f02c105c0700e5600d00d03840180c02130043c000c01100b00010301c0705001240512018010a600c140040c5c0c2600c1d4450004526140003680502c0009034850414171005c5011406400107041070b0030f040c0200d0519400400065 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 875489712 1250 875488462 875488477
    0x90303021e04120308181b150c07141c050c011404300515220206030a0c020c0a03050c04150e0a090206040b070803010905010617160903140a03020708060c 68
    0x420500c01148141660240c0111b00140110899a55a00c0210f0384921011214502071190030384550742c075510004e0b40d045400b0740c2d4281c1c003c0d04941f4103003044800b504404108058004c1441142e0303040700038001c1d200d039003001d00501c0106074001900000401c0140d9446d40708020100902c010000c0300c01c1d07901c0302c00c0d940c1c13200c0b00c40302c0180b041c4e0b1a80d0008000e0381c3d60f015106204501031100f8220001e040a4012102c2400f50003141e10482c0c1440c04c60b1800d440000e402c05001c100140d0944201c0d40304400328007141c4155040f0740001800541c0702c03c6260010b6034a40c00400c400410707882c040c031920b00c80d403500245c0b02e400c0318034000090010020003407602002684428a04003199110400c60b000342841008030f41c0c40b94440c1c100407040703410901070800400d18013400803c2030f034024040d12584032941184007555503030381c1c40283c1c20750b90041c03065824010441c4004c400160000d031105917407004007005254010690800a15160503903200b4042034000d1414006c41090712002c07903540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 875490962 1250 875489712 875489717
    0x2106030623040b0c0702060406030c03050106020120031302120706020c18190f021b100204080a021314011202090f092d0a0302150903040501090e0a020c01090303021e041203 76
    0x503034402c0d880030034600c24000002e611140002340400e03d19015440414074030103680c5c080105a072140000d13400c880c3d08424a05407907440f10011043c96045400940e40050300700004120020030350b010400c0795242951034451600900014041e1541c100300c035078010717081190400100d16a00400b1807014401521a44410100007607805808041c0d4005140d0425400c20466079041c1902d2138407850600d5a480d440c86000b0003e00100c2c4c0413844c02503030190351880000c1c0c1141d101550030000800084069141c0700d5450796900e24441e500b4500c241d0003010500d9003444000114410008148401000000b40d40c241c001401003a03140024000c0300142d01014469000d2049201501d0026080a10304024460380320400b00f01680440e10841e40521911400e4198592509594881c062409803900083c031101e001c10849243c02d400c16001034505100501d41b00da620f4ac2c02c0d0039200410402d030042a00055101448050001d480d190540884402800c1508118014001540d4400c01404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 875492212 1250 875490962 875490983
    0x228020a0b0a0c0b01081606030e06151503010b031504090c260609030c010501080601060503060409020406050607060603140f0a02120715020a1101090501051207210603062304 77
    0xb001d5004a4a0708a03640d000026016251380d40c0251598a0701089100a000400d120000640500a001e0049000103910203403825a550890380c0d400700c103a01c80358a500070001e94826640c80110701c0118043c210405510340e0b240341461b01012806288129580140d03c2c122031200030510081002d41611252140402c80c0d094940c08501c0d41407000e412484940504d80034421481d0000008025090906009000c41da9032615020388800c024890480032031f00400c0011424a403a90140c07010360301c014030025003143c45030085000b80d00905411550b4943e582414401d10480200c16450480c103880102820169507903901d81366424040300038051a030050031020701d80c030203100310000743c8043c01071071301280702c01080250fa4541d91101907400142d01d401d8451194820240c90742035801c1a111f052400441d2520041c80e1000240f0110400c14ac001a25440c98040894103810b800000c2c0c6c0407514504508100c0111080c54041d140790302000c1e03801d04080200c204005600c603410882d041c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 875493462 1250 875492212 875492227
    0xc1f050711010e1003051501050403050a080702010c141b03030307050f0f0d020c0607030f090210080a11030106200622080d05040311150c220909030228020a0b 70
    0xe40f8145900415680300220101d01c1440c0f962640c8010700c036480404200700c4004003140150398510a90102800d241c001c101640086000724000f40442c52062405605644258403003e2a10485c2008131040d900510701508400c080440d4403211107038102e016515604240101600078802c00310014088030000c03a030072000214001c1991201b01d0384000c1075598003c03d510254480f00121003540200389010b506086022042c030940a500d54050044e1910b50041035051b030302e45200178118403c2948420b00442c044411b4000b45000302000d4072903000390031040456040c81c3c1e800340d0a40c0550380c04842000391a18a15005084401644050344070200c03440c1016401351142800d80711000d07040400344070030550304c40c021036171400c0820181c8091100e480e0307510310710b0001503500241c3c5140600405064090362065a039002c1954818800700d555690141c0701519048507003034016801903c0940400c0300d4485188592102c0075030081e00d18a00b90b40041c421854501400390507400208082 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 875494712 1250 875493462 875493467
    0x6020f010614101e05091207030203122206050904060e160c030504030b0709090b04090f200a0906030b07020a120804060f0e0724020c1c0c080c1f05071101 68
    0x3049501d07104140e00c00031132604801600079844106003c4c0600c000c0c500d41245102d0104501040c1c070381c020081d00c60031042d0410580f007070b001000306503202034106410303111080c0c480e110340d40208174548035140c1b00c00c0c84100b04030440740290312002d0100086010000c051329000511244654282000c0000c1810341c20b045804e40910340000b030841207142c00340101c20381c1211004003101e1000384284522a118424801070b5004800d000b04045002c0400c03a0001e15403a06d801100d9603c480d420f501d0054620026041030340e2a0303c00c3c0506596088180144260041d8481e0300c400b041c001003014002c01d54075000d00741c141000c140308111015000c03a01700700450b0018001d82d40848403c2c003c0c660407980e2141c888060b8850ba20783c049003800d4094907030b007260a07242c0c0142907640241080500c5d00c0f09001e05101b55280080c0303002e079403d4118000030400080e1401520740300e0000e00305484400148820740c2810700c0f48030300b02c0c10450400c0c03001c6079010301151101a88141c12011015032203006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 875495962 1250 875494712 875494727
    0x616090b03010b041a0403120804051018020f03010b0108191d010e1b01050904110f19030c0c02060d1d010e030a0e0405090a201906020f01061410 64
    0x441003424000000a22206910003078001c2c1d0360b20300c8184034540c9481030803040a01ca20700c0001c0070f08140b120f024110741e0007030010a6115010b40141c500c9080c00700010700c121400004040c1d00c19840d100f08905500f00800b41407101c400076402007098a008600190681c8001499102c18507800018602100900d8000d0141d00e0007682c022a40e0b00b0303040d0b100a029040300b91500703c0704c2c4141200c1848145948004812808068540d240342c00b5080b414400504141141a400d03000304011103120001074400401d5001d0741040c0385601c200c90540300030203850000d80b80c803080042290381d58002d40d03241e008a52480800181c0020700e11115800c1008032510390042c1d0055503e0151000710341103001c002026106035a696000c10000001c1c00c000444400f035400034100e500c5010241c0c00115503a011035100c0360300c03817224070a020309400040e03015060044541081c480e4000d003000040c0c4c0401200d104010054024007095042016240e01303161000613481c031482001d441d03594494082e110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 875497212 1250 875495962 875495969
    0x10c02032802072105120d0e06010609120819051207030203151c020d0b150306090304031e0f08120a020705100b210c0102060105010c0c0311120303040506041203020a02061609 77
    0x945907009030f0006c210381b0380e41120000941850601100400c83c250110b01d0318141d513800d4580c0d00d850750600404182003c1e4001007155445c074104103480818414508501c12a22a40d403807a075100c411048080a808001c2e001105050041c0288821841211410303035894000b95025540d442c00d482a01c0f00207074010748082d4005030101800c0d0213100240c030010b032240c40c00860800b12410214181030340c940c81243c04006681052105200241c888440340000350890340c0300c107050407043e0300c40500054a42004070340e05000000c41e40f02510150480603403003403107440c0031420041c81e41c68035525140302200741c4807560b0b603998051656a8a005c08090210441450020600741ca03e1503245e507900c03110103540c050301c106800041c00d503224101c0c0c4400b1075801910105080d10319559051034842c0034180c00c2e4400159030315280310490400c0a50700c00c41c02100206042d04103824520b4900026411354020540100440d80105030001642e5802012014000a440385881400c50f000c80c2d107500b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 875498462 1250 875497212 875497223
    0x6050901030f0f181202152410020a0b07050304110918240c04081b0a032a320609100f140310050d0c08010c020328020721 54
    0x14601840d140c1c40100f1300903800e100300c2c604444013803101c0090713075038003046e44030040d11750201c1000802203c00b0038914006021070703000c100318009030f0343c00284000c00240c44490050f8403200c1040d05021540c820030340c006000e0b0070103516500700b6448440e1001e030385c2c4604030301940c140b0003c0303010300200c4203041041100400aa501100d4184001300d209020840a8180c030840ba0b00860303000042c90046a04460720400140804801e20450742c9a69140141c00e50303002c000c0500002c046031040340000d85c2d60030b03020302c010f4400c0503520010030403912030b0300100814031009403018509071a040340b039040c4c08078520314004550a82d000080361842581011508a80d61039013141840b40c011801c0043c6030000d44405007404e03402040c500280c0421502003c209034000000c0103a818206a1121aa80515489410152104400340c01d5451944181005901c0098002c14110140c00b0548201840c070006820300e1200b03500083d50381029024a00c00e145041c0e00f2012801055039002c82c3d29035008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 875499712 1250 875498462 875498471
    0x905090a0c1701120512030c160f15020c06131119090e03130e0c0702040c121407030b030c0603010b130320011103070b0403050d0f050901020711030706050901030f0f 73
    0x1130100607030602e034121044409120388211941c072032507a40e041d40c3c412170031060541d08203c00504540301c10008903500340d400c40701c15540d00c2c001c20f00c131100d0006583c101d118050390b20849040b0641c50460020801540c8191a2180d50300044e8039900e0341e80d001100303c541d00c081c00d80312112110040c54030340c407a00c00780785000607003418000088068480441c82d100302068160381c95140035400c070300407980f181004800304007000052078258409414141c0300c0c58908a0310a05150304001c40307a240e810946028100382c01c1240296040c040d002d440f9401380d014003103109500010038070f81d010600a00a6030320700401e07070350f078030040040c820b2006580000505040760720300c0c0398005013807140c40c4115000502e000026600100000100d560300d41e4003040807100c1d2398450318129076a8101e0b01128852940300d0284c030240c444c0501803240144613080005903100c0840c80c22521805104582c07034080e8004110800032190008180c40321501d081c02d0200c0ca444008219400a20442e202d00c2034003840d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 875500962 1250 875499712 875499719
    0x150309030405130b010311030106080c0a03090503070c0305062d090a0c09090506010b070f11011e081503010c050307030519021c060f141302040807080a0309060905090a0c1701 77
    0x180c2d000407540a0b801e1b2010003032903041c11400715152009000c2d01e00810959000b0a80c0015440018450842ca9240025404071607584060969018400945000e445440b041c028080e042c003c06801a18030103c8005e4074889841c0e40c82030a0b0301c581e4076a41011440001003c0c22000d04c41c80d20074a5103d40c00d5031143c1d4580c06404002d0064607000d81e0640716110010445504030300846038119008461071408055555a012030100000d14060402140ca12030002074030b41e540c2c0000e030051641e21155590b00e0b04a13614a450324021901078441c1e03052205110600350010100c9801c2115860003040c55980c00e51340910140316021689205c500c009030b42420021040b643c4018007681020521200c1c0e078400c1c4048042045004042007540380b100716158030b00d0700501c1c514110f642500302509040d80d9402c40e074108000e552080030f039074001c00f800b1010154018960b9014000d80e041070009281071402003030004100034403801000b55038130310300070500740583e4214901030411075510070103685 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 875502212 1250 875500962 875500999
    0x60d02091e06040b010507110d021c050105060306040b0403180803210709030c092003090309010212030106140702010309230d1d01050304080d02070b0f011202150309030405 76
    0x100903110008001d50082225032a0078020701c166048140e46a5062282684070f1003841c0b522402640d40c041d458941c0f041c01a1664035a000f900340a00080004e541394030f013030440c2500e500800c928801d4101c4403c02c03001411416810ba04079402d480c0c0388810a01c40c4140714490034507070b000342c0903a11000c20050aa80c000b481040280b0341800603d40aa48542d0350503140c00d000d03400004d0101d80c86410510030403070b407170f0f100c1d22010141c10144150300955070500b400c0d59000741d6201d01c0da508000750201c0c503541c0422140841100c0007180358070395071400703400034030140c0c91100b0481ca1500014659096a11030340000101c0394101c4208119500303200b4106a0340248107107240c40300e010701d5103400b10b11030180b00c1030480b88049010035002581c01d000112019400100100d6141b0010b0000000c04c1003a48042c101c0c3c540700c0c0307201014a09041503005000380f41680026042c2c003108030b042d401030710381040080551000301c10307094aa03141c0d40340050460150750001e81e00003d0840301c00c8080b56 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 875503462 1250 875502212 875502241
    0x304080301050a120c1a0702060705070f0b1602010c0807140c131a0607050a050303040302010c1211090f0f0301180c06020105071418060304030806090a0203070e09060d0209 76
    0x64003103c03014042c607500c00d4014602074100c000a4003040400703104002c1100c182c0c128007081c42001d00c5051034606e20703500082d0b40781c00410090710745a01200c410b00003900d48005900c0a01510440c041c14240c5001c8100c01407481d090700281045417031080007080080c004140e864850b401041882e00c1031a000c05183c1c0e4955283c2c17500c2c4903149041c940c032880c4030940b29090a54050135401c68495640c0e501340540d50303001d1141154688503407000c03d0007040d000d10142d80141d105e43c0c004600d41021901c020461300d99020992020340c64070140c4000d0745101c2c0101d860806064820850030902040000c03403140c1e03900d4005415508160304942110400d5000e1400544a000c64503082074465600720708030340c0300300d4104001c54201d204140c882040741002d4420351190f4814013910b980c1e1200410029007041c3d900b10041280c2e081840018680350f1002ba4ac8034501d00e50450071441e0403800104100da08c5800e06004001c0100443d0a85d242d6610070540c064002d003105106080140b0380c00f140c0b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 875504712 1250 875503462 875503469
    0x3030216060e010b01080903071709030a03051201081504021e03010f0e010f05040308010b16060213053a0507030501111c0c08060114091e10090302210f030304080301 73
    0x80d4609a0713034002d95809907500a000d1180d150003142080c80507600d1030712100c2041001e524404051082c600c2d140d50801a00310464802d0361440e032100124000f0400d0060706130020b0309243c200119402c000801d030700d01e49500a40440e40c000b00700201007054000040320f00261074041d42402c81c03003418030340590811990000010001c00440004088800881c2d07026180180001c080a00400981c0c44c8103001e02050301a100d404c0c503401d181699600120b030f004100780101d49420b03e00810031490b2100c5100c076107002624880352402d40c000410241505007880f40381c400700c0c091038103d0a02000700900c0024541c07150081004c80c04d101c84124064008500145007082154090141c0849601440d0176490712a11002c00a88517900151000b0700001041101c4100034495690503680d00c480d060001c9030172920b840d100881d503000f44124144030400030002c0c406a01b00c00c00c01621f9032648a103d00c0821200d007152150000344450420f091800f1440d281c2c44080280701c28407170340c000110704a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 875505962 1250 875504712 875504741
    0x7180c0e0a270b0306041112060a1a12060c13030b240a181a030a0f0c17030702060903070b0304030905090f090a0b1f0303030f05010905041e0303021606 67
    0x24400d28251003020f4407808024550560044000b01d000200d101400c41c480500007031101002c084503440082c80c1c14811100580d805031541c1000c08280441310b1900b900520a4400c4000421074402a61303407104003814060502000050040c0c030b403410100480091765105800078441d04000b44402030124440c2c00505002c650044403684902c1d000300270780100d813070020744111581c100ca40440c0081c1001000c0011840e503181103441d1594043c031220032490302c604036400242d036090500440d42d40d00358010590240c6520301c0e00c0c00c84d05000080d180d180c2e5040b00d20aa50f040039002103420040990302076803c1c20320200c144001c05400c0f04110040d01c80555281510765036182a4004802054500480c9500a40050800b048141808607403094000d60349043d500182188122194482d07801500000e41e0303503c281000c103d06000d941d0041014010620090a20b5150b40000c0c0c000f003454490300421506000301014029010b5070805506081408a1002641800c001400e0303e003050109 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 875507212 1250 875505962 875506019
    0x52d0705250e1504091a04033203091e0a12090320030708030a021608010c050a080915070c0201020d18150c0203010213031407180c0e0a 60
    0x29524038252001c000c507200b15035441c040362560269a403031220545909030700507845840250100300c92000451001e40c40380807400300c91403c1d0600904103070032800008800d1424088194201e0082c402c03510300740b064101da540e41d0b5210003c01074980042c8080b02c01507403808a500d0600160701281d80c8849a0059898060750b5180c0c410884034007200e800020201c400301c9220521030f0821244185611a014084440d22900d03084c0c141d145401081e80800180c0c02140c04038140c4151a10360320041116000174021115a590080e05a014600e210300070840039400180d14501d041042c0d0860781140c196000716400d00c940002d000b00211402070b40984102d103503444c2840c0c4290340c02c28511524249207880e00381005a49640c0300c60940c039440401c20f611440c0b10141e6400e200a140480d041c08000e51000d02c1c52030458050b03940f85540c515182c101010800c0400d0501540c00c0d410300404800003070100c0050030903070340c80020417081c40c0c000c0c1c4038a4022440304401800e60380e0b103c585040f143c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 875508462 1250 875507212 875507263
    0x150a0c0f0f02150712030e0c130213080a08070303020307090905010e0106030509031206040c1103030f0103060605031c030b120f06070e061602040203150d05010b1f052d0705 76
    0x7030180c03251a00c000d00b006822450b28007143c0c42503002d0100e90b00035a02303031003001a034600083d04410305503d01e1b40104c0c1d40010071440014003104502c0c001c00511000d400030302c5150300c6918a6010350035018003850380000c00148010700c038007605405412030030020011135031a00910703507410b4000d00429002c80d2415002c03540d031500010650f01e680310307030722108982680c46c801400050301c8241d040c007090100350080b0884420051018510411003018511125071460074000c0c2901e01641c482c0d0f000e41c000108030000e500c10300e100a48141b000703041c0891401c0d0074401042c0c3d2040301d80140740245c0140307190000d40c080041403680c0101c0c8155940121401c0c10010045284a0307442d130210b2409861480b0001420250003560b4021030100300c8a01142d22080450005241a001191640d5541111070418548003400c0d14014485142200b00d110861101904c0d0b44140ea169010030320800104142200500507194a440d1510382c0f059143c403e01d00e03209a841000b4031610501c091040c8c0c075403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 875509712 1250 875508462 875508499
    0x30207080c09060f220e0f0c1f05160b0a090303050f010f0314010608070605041e03021806031f0b09090c10140d0207120806040b150a0c0f0f02 63
    0x40c0d000d103d000b4081d5002214150400c415015600e0403541103000102070003410700b0303161042c50421076014003e000075082c94648036060581c142440e6214144a21800801200401590740d0048090400701c2c0d5403c0700fa00c2d1501c080d250342d4002003404031900c0c1000340b10145078212102c2c0920a4030107200d0354a90141d20b040000c000d001d01480300100e0042003000c25034030481c000c0000d03d080000169640c85001440c100713451038105002003000064208010401c116051403c1c140b0119401f40040c00c550018000001301502656081004000314440b641c05209031260b0140e090f00642e5042401e01600024010401e1820721800304000003885040022606074903110005001300d8030052820000d0714048e414a50403e6a01810b0180c1c0d5440355441c8000c0120a025244401182c04604802842d00c0b8004004034000d605048c1c1c0c0d00c05036240c1d42c205142541d841c401064032201054811225605100c0000e00b002c2c203030010150a002401b00100c41d0103000307032003940740c50032001e450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 875510962 1250 875509712 875509729
    0x813030614060d0809010315150c0c0f26160e191808070c030f05070e07050705120a14030a050105100c0507030b1e090606030c0a060e1318030207080c 66
    0x50300300c5104100745c0c84603601c25800104842d4041b610268016201e034580030647c0c410441510200d450102c10400340000000880c000b000983c1d00c42101c00d0402e0400d0040244464a180108606014003c2582401d002c01e0b503810f00c200b980c1d4606e06554840851134200203079080c0000351804445400c0d901498000c0e07031981c01000b01c85d414a054550b842d800d091f408818150303940c4400d03140c08000900c3d4071030482070280c010001010064284050410b05441c0503140382e081c840304002040000d00d0100c4c000c0c2800c0800855140c4aa600d0036050f40c0244070100c10240809002040014075006030f03000d5030588000703452520070005070312015a0220703072050000c0e05590141c0c00400000e080d5840e150b500c04140e12200c1c0102d41d410039248001b210503101407004d608407904012807818108015074001c00201e0f4101c5031180340950150050180100306030050f21000d541c213140d100240c1258104145058806c0d10242480c10000c3d10f40d4604d0140e4840c6000c0c071030044140703181c1640d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 875512212 1250 875510962 875510989
    0x50c010f15300f02030706080a0c030c0c121b150b1512070504090c03020a0e01021906020318161406030105060405060711102001050708060d081303061406 68
    0x1569481200d010040d0000400a8a030883e80441c0200b4441c006860511410009100503120508981001502c3c1001e49120b5403040080528203901c03d04500c5e4407401924080d50850310140981c2078115045403080320f1207004001c0c4050900001c4104100c080000c0001e94403a103040010a8004040080c611150518005403002c18070850300382c0203440c40e060750801c44c1801d00c0c5160507500e000803410799001c41000300220b43d02080030a4050340099501400c0e007000d102402d00070340e400c01503040b000300d502c40107880c90f503000c000107401c4401d000c911703158810a4422a00c12142407000f1224171380d0940135611840110880002960a00c0e0040c0c9040e114010f01403818581440c05106054205d03000035900405090007003899070b21100041000c5082513034400150901c00d950194050032024401d840343e031300d44410019203d82c4100d80760781140080341e03200101805420220024040c01038400c040c041e43c22000000c200c050740c02040101068880b0344047da44030f60811485038950360 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 875513462 1250 875512212 875512259
    0x14340206010312090e0403050306180c190903080f0a0906020309060d05090109021518010c050703030c030c0c0b03012c011a070b090604030810080c0d03050c010f15 72
    0x10062001540d00000188901c0b19444c09a6000f41d603410041481070040d01c00390f02103071002091005904003000074200c0900c5491102c5000e00382410840c1d460301c1900b200130590152214855540c0c1d05c141c0040b001160040c030b4481d00c51450301d144052b01d90010000c5008550301000c0061210700201c2690307104040101001d00b042032505000c406400c008006410030b5503541c02100c0140c0d201c1d22071400c07196814480e40e8503000362910b0542030a00007110309051004807820803000801c001920802c1d02d6062510040005c1da525080d980d0302c0d004d001c004d140905111010030710715803441c042c60481d034007035002c1c0c1503042c4448114400501190410301602e000c0000521500038021555548805c03c0703080c0c2440c001d090b884001000d4010b542d0034005421100c01e04c000d042c4c3c8602003582003100915030343ea0051600c1c0200340e84243c1c84020a010301140c0d510a01414040d8040d1914000508000d0140c060380c1180c0d80000c15440d0810300c04001000800709001c000700d42072002e500c401c030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 875514712 1250 875513462 875513473
    0x30609130c050114090405130203011512020f030309060a0305070e011b14100204030605040c05011b12050904020429040b0d15050a030b1e0402090601080a143402 71
    0x20045031131907540f0180e10007680c010418000a9110761044500c12555400090300200c40c0344105070071741e8448125840c0c00760f8400030610880c282c0d44040f919850341101e0204a41140b00c012a046010b494a40c1d0b81c014804a90030711015016080030f44629442d0b0340746a90341000500541c1d40840d01503480709412242541800010034001d80f90340d0292403402160840001014000140ea0080c2c0085943ca03071518140300402500c0c1e4441c01c054402400c1006400d20300302080e42041c0f075079810103460141c01c040d4072089a401041207400e0b2002c080c1c0295510341c1c54030580391440541e1400410b00d68008480c420502031501c05603801d0301c1103207506500d0700c0240e040d0a0701400d029414841c135408202130005040d90742c26140002144180f21000d45071030720448004000c9d192204024072401100d04200044c1d6401c1c0d81554800800d0a041400d0b480d5072251400500070500a00104803156041c001f40d885482c00564151490032581c0801d01400241458008a080041000360380302 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 875515962 1250 875514712 875514719
    0x3021903090203010b060316020f010c0f080c13090507020d020105222a051003020412080d0b0a06020708120408070e04020105190f030e030a0807140717030609130c 72
    0xc1c0d00080042070009001003409100c4100050642d4020b035048000d80d004151003d480741e40500103584c09101070740003000818498070010302551030100c034031380401520b40009160141020300b580d07824118a203481e03050baa280e101040c0106800c0d55510054420702144005e824414000e05100d0009500e40c08a00c0d140d80c02c40c44061401d00c41d0407900041e44d600c0f0703140c001800014030780c1440c662480000714186000c0c244401c81511944610815004000034020791000d07600c0d00d070242d644228a5030f90382210710030f200020260710354940d61217012a0400503c0351b60020b20041a039134400300350b400840e00c040d41d0140b1485980b15003503903034200b400200250b03150481da00d60b000d801814901d20b01307200b08020500724801d21180402098100204501c0503515104454050004000441c03070a024800040e19100b0000c19050400940c1c1049588940c00c80064880c0c050b402005280c10318180829003115400403141d2074010006407000807020000d41e10082e82d810f07003190003800c2e030904 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 875517212 1250 875515962 875515967
    0x111608030a18150c080108060c0313120f03060518010513020f030708100b0403260d06030b0f0f43321615020307090f06030219 56
    0xc028104404540e07030b21055011450b60b02508100d81d4402d20709407600d0380c00c00480c40215241d80d00c04000f00034145006108001002840315000106400702030f031659668044181ba0001201000f44500d1941342c0d118003180d000040100c0040081d03c0c1481140e07143e006007d0890f85804d0303074118014003000100003e0801c00e4960340d0f100c10b4074901600c0c1481140000e0030b039070320983d020300010360030740d08004144001d1105080a480210840c0746814078546502e9407014402d190680e5958014668913074420000c4100c170b58080c1100c00a2052503560704081c0c6803010708803072400710450418005201c1400c66501e4921800400c425580f0a0850749140d400c08414280a011a003105000210030003e80040245980c0780503515602811a880e6040111440042600301d20300d40000e06400c0440700ea105903440340c2c40d41c1002d10030500403400c1c541c155a410321098800c0a1002007031280032540910f035030042d0f44280c0c80c00500c49a03a800224100e03c59207020503095014604405030452 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 875518462 1250 875517212 875517217
    0x150c06151e040513020607050d03050105100c03080702150114120708250b030f0103060b0406060f120615080108071e0e040809030114060406060305090a240519111608 73
    0x80a144e5003100700385065020910540c080c90040c0e900c0d0340012003c41e10349905000f51800b400c0195051030407107a01c490080c05c00750041100406004071080015201482005017100d0041d00b425802900c1d6940d141c2c002d00c0451030080035000d4401910804800c410000e041c00440c1d503150014040c8420320a8840014982e10842c03d05010f4501e0b00007495001110145020328550400202c50754036500d00001100c5100c03800a0280e4180802001065000200c030880300307665040a007583c06c0c41c0c0da4040c00a000310303040340c400d0b10070044080e403d40f83d004250a060314090011120010b49072041030100d502c440514150003c0d04800500c001e941d1601c400746c01a1050602e181000070880c0000c2c203407144c2c60310b003440600101041211910b07084c01a41c0041000781402c00c020704144440035200c00c081c02d0003074000c0741c00f01020110042c03e0460386094001c2d4050800082c10284a101d804007615070300c1c50b4100c0d090a845003141c45a40b4112491200002440294440b190f80c6064158 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 875519712 1250 875518462 875518471
    0x103140f1506090a06140c0f0c01030f0b0a030209060609030f0a05240106031503020616060605220914070308030105180c0a180b0a030203040c170d030b150c06151e0405 74
    0x1b81d001b07005d50703241d03000108080942c0a0810002d0041011400001800c440340342e10104925410080180f41ca030311130410780c40c292901550301c1e400c0c4e56034007404180140b244d140c080380c00d442452110070801384081340507003005200300296080402c4d01e50030007000c5040180d294101040ca2001007007028081d81c441c000410314003050b560110303500d400003852600405544444d01c002c9102c840d080000c05d128500280004a42e550f50210380410551244880784c0c2c28022120303500d1802b13400f4000741030b140c40d10b10440c00c030407190010307124a094145608284a41805902c4111844402c40b0800050074421465101490308005140c042101c00100044e800041501040030106600c105840144202c42d095140542c4d40d04140c54000203100490f03105608944940c9000959101d0124200808000c541390104426044500040c5910303600301203884280c00014403c0401a40400d41503c181d01d44051035848000400601269a09003d642c2c01c620840c80d0b0b40305d582d89425445903402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 875520962 1250 875519712 875519747
    0xf06011e140706020a1e0c02061308010c170c2110090e0d0909020703020304170705030601060c1101030902100f050c10060509130c050d020103140f1506090a06 70
    0xca4810200c1180070360300441080d5a07058000071031825442d0400010440c0140300003881865180c003041c014140601024024441c11000818242c14000741d0080d901070440c01000700109102d1040140400d40d04503244d43e0141c00e000006289110b4410982d44a0750b08080d010020188805403000041300050224056070312601e8049105882071041d46200d104140003060b050004a0014101d2407440c6c0c48460708a0040207004006540801598102c1e1405a44401d011144840e140d0519100c1d1704081d030140308140c000035640f5401008080520b01500b501584c00615030700440903130784d520b08040c2d006800207009402c02440782c0d8400042e0212480d100d42030070b115469460500c0d4882410103d01511100300384450710702041d886421101c050300ea0103130f00206507640b800c40d00310703031143d18800c01d50207680c102964040d400000d09100b1100001b007151900f5000740300402c100344d5040c00d80107410140301803141061412a03401060081c0500302c01c0380f41c0704e0110ba03961800c0860307010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 875522212 1250 875520962 875520977
    0x1c060b04060f1814030a12030b131a060a02030c0a03020607080a0510060e010908060f010608071701060c0f020d030c060b01030e031b120a0906170403200102130b0904050f06011e 78
    0x402c0c541030361f03154400705a13500810b600c8204c0c010403020781c01d100300c8018140c2c078110100020313998560409860040c10340e50030b920740303501c1ca4003a401d600810b04200d5050080c81404001c251740440c2039446842551a198129110303000c050003141c1e000c450390003015160304410300a1501651007203034482014907145112a4075020868100741c01034550319a81090800140102c64018138006d07408100c9140c03c21100c50481c813802103441040c441d1405000803100709505218156401c4107000342c0240100d103c9103002d140c014140c4400701015a4154034000c4000c3c46988240540a422800c0000440c20720b102c2481180e5688640c0991441d01c0c400c0300d000ca03018180101c0600007041e201d448200b46249004400760010b080142c410605090500030080060f80285502d07002c0103148040c414116080e0754240d0082c440c51840c0c00c0c81f880c080300c0000d5010b100342d0040c466904255020f016548501540f0040341d075007695801e0106400b1911a903c00844030105000c4c98524a802c14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 875523462 1250 875522212 875522233
    0x4060c11040f0216140a030c0f053c010605133c140c1c060f150212091c1104110c010b0a1a1c060b04060f181403 50
    0x20100c2c1d1004001300e404550400c09075040c003401c4854484505039400240084440b1039800034a0f038981e91f40020700c41030391130341c0b002d0900070108a40c450500c0120070061001c141d034100f03000141c2200044403000c082034401c1055108040c02070324125079014003070070000c0140482c0a006080040d04d0040842c1407815407072003a440d41d48002800c85505d02905401d50f400f060f1502c01c1c2c40b0b0a0348440308111400f024418040c4190b41181c0e030403980c81c0c00c52035030281c2188486000c0d103020351040026880c000000300c2c9021020038407240780c0032030f0740072521071001a211860090080e0090f40b075014330060301c03018045c0c5103065040030f40c62080070965950341c01000090111040b030f5003400b00c84040802d07000d03840c417024810302c00040740465114044030310380b05140c1059010b442c4483c40c1580003250010400c2c02410005012600041d0184165512110004503e4002d071041d400050800f942c0e060341c0f0350094011004445010340e0360407040d82004001c000141c0505141c503014403448030403e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 875524712 1250 875523462 875523491
    0x910060609090b240418020705030d0b0111010603030906180e06060a120f02030a0b0402030402151b0a05060406110a0f05390615010e0d0302070302030a111504060c1104 74
    0x500c1806031540d2591254146480400b09100c00b040042ea030302d01c1023240c20045200002510194203203a100800c071000e0010048451000c030a450a84660a09174084101600040c1c1003050361842d668a204100c0c03041c1d59400302c6c0000c0d20030f082019800c40042845402d2110040070f00e1089428032402035100106448112802c46441c2c01080b035001c03041c852809114060801510011501581036042c190002488001e21441d10048068000ba807040040101a0300c10b82984d40403060740e10300070703c0303040c50364480c03030201c80888400d89403411505007540802c003a1880c128031590786114280b0302240c2034419920040c0040104400e040c5d40305480e03030340c548030004a490780c060181080c1070149949803825201602c1c0d00004122500142500d03640b00348202500b490840311000c0301c059038101070703041c41c403140c0010790035008000072203052040c0d400c01c9018401e0151a40c841d00b071078500100885010f140514400a035070303580414040352410b400c01c101388400410004e041d075940202d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 875525962 1250 875524712 875524759
    0x1e050c100507020d0512070c05100908030907080d140f040f030807020102010c080c09040513020d0b04030228081e1303020411160803091906050910060609090b 70
    0x180c40c002070322a03041041003641400516080c6a42e030a040e401c002e015000080445001002031080282c02c800d800c2c00d001d420407100c107543c204408104075001490174801002d80c01120561405e03c07400600081d106e50004502060300001c1d03660390b6003c5131b1001c15220980c003400100d0307201c0c24207100201d10b000801d046640114441c1c180a0340c0c4002c130348006425114484e090700d051000a00c200202c02d2079a400703d40780c180d401c5a00090580c4c400c0710141c079483c000318000e03400c0020384500008108500c40117070f020700c2c081d400b25034103203c800da14006000401c00c07404182c00010b1142d20b000843c114050715128135031a0402614070304030030b00214160072000e840c1c0c03421040e0a00410541c10329100f403c0d003104030750307564901d402c1c0a400700e8604000c0c40100201140030020000307031000e00502600501045622140c5520344c05814640042d160644214480703014510700405048001e1003020102c2e03215407514907140e0702c2e01c01c104004014070f21007540c00c20551803920b031450908520 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 875527212 1250 875525962 875525983
    0x2040504050115030e120306010c05010f140415060303120504060e0d05030a06050613050907020304030803250806033d060e09030c0a1511070321020a1e050c 69
    0x104032241402c04031006056032040080c0c003403c3c2d04030b210b50010114a06c4122640b00b9020308043c401111103141560043c0030084160319500d04d000c19503030017200041103850140c0e0040003040031540598408108851242c030004003c180e000a0101d000e04090b04242c0e845401075500290b90b107180e1050b02c1c106070403e1603000000d48000104030001410744504000303000c00343d03201402e014620b034680c0d070068510301920b8401d00c480d80c000f821181c800c200300c2d07010310344c450b40581c0c0701c0c03c102e000441a6141d480c000007562050265000c45036210301d03500d5209150040c001e0607014441103010445c16940b10700c40c98502c07403800c2c5111160841008000b801e000c059000030380180f801070541e01900d0003404003032080c3c0042101803d085400076403c40f01c240c01650001c401289a401a0700078229511341e2098440b01003400020306400c404040e00859083c2c4d000d808000100040908a01ca1801c440010030301042c414031440710040d000b0f61310801641031a618100c0c91080e014904140c084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 875528462 1250 875527212 875527229
    0x1216062a050418180f0f1b060206042627010518150405030f030405040e120403140109020409062c070e130c0320010804030e190e150a05030606090601080406020405040501 75
    0x110780d0410a071380402c160701c5644961f0041c0821b0900d50025210000a04040d00408030302141c25410070480106403010861000c3c840d69803050a201560b4800e034030254280503d520b040c01072515401281294440124510b60f014010905020030104906241603110030150038000402e00e61410001001301c14034480c000c40c0c60b58540410001a07039600403550b013694104500e5480300134103c800355801d69502205a403c0e420340302e540c013801400500406980700341814141c00601c41d032544081558060685241440c40c00b080c41120401440000400c590380600010042c0e04650301c51690803403448403060103540382945501102e030341107820030707a241500440d080d00c4410344072042c0710200c0b100b820000c00c6840c150300c0c0070b043e2810304407e160040c4240e019540c1089603107010b03540940741400c1803c440e41402500d0040818107a01c00e640919039200c0041940d05d13000801a10a1000410061040e96204011a55039801510441300590203100c041400e603158090a40a4800e41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 875529712 1250 875528462 875528483
    0x40312020127060b030c010f1214070c140606011b060b1e1315030b0702160611010b040608030d0b060c0f0625021216062a050418180f 59
    0x10b003409411581443c42d1140719601c05202c0106c240d8000010304174407041c0741000c0e05480510041c2c00c002c0d000c412140801c030321142c0f00300140f4a401c10341300e240b007a004802020003110840946aa1054180ea0950100320003405403003400e00b198041d403400034410040820101803800c0421202040c40380000c1540382003a0300300e581401e1020030701101c085600030034001245004071000c6004031600016120400310070029003c54020040d4480e05034401014041c01c558400b0005d0a100480c04001610f50a0000b164041d00d42402002c00b5105c494020350f1412001080c0c1000811080b02a5134101006100c41e07000001e083c0000c10007051a04043c0c0308900d09003c499040c400090104220780102d00d8000215942c0000e804628000c2c1c0400b050383d49641e50288080f607410130400401d4981401c0550305007940002ca103a0815540d4034150041001d2408183c42c0b500945c01103088944c401100569100300300d420443c812040309018440c00b40c0c9503102c45412070640b440554404000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 875530962 1250 875529712 875529791
    0xe0313030b060109060507081b1b010f170a0b01140406050a0201050106080405060a0e1f090c060c05060c0a0507080406020c09090708070303080c091210050a020f0403120201 76
    0x75081e07541c03050091800c90f844c02d08180002e4454010001b0140042501141ea0008815044d04034805192680c0c2194100010b0415000b120400d0b1401036001506043c461320802d40034103800065216140f40d03051065444120581c000c040c01038501c2c1c1003100344194103002d0001d5000400c0500b2950b2f0341d140d541c0312100800303829071300180c5c410400c0100c0c0c4410000440c40114540303801203181c0340007162104a15840e44e2030145952400040049840d80a4200040f164045404241301c1c03030500311003a0f0ba50f00e0980d41e070380701d004014207550080c00000d0360ba04c045400909042e265400d00509040f42a00c0381802c82d08141c20107800343c0d20503050500d640c94400700f426400041503009180303281c184000c0d03a0703d0366041d20000381440f070a8004501102d007607500b5540441800303055540e400c500d44040c2c641c0d8080c403204d01c0d80300c1ca1811011035800d00290085640c00b00e03100c00c2d0586020301d9541e601c507400c105086100119560b9001c0e1078110101c0d08280c07030040c2e80022841d01003031003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 875532212 1250 875530962 875530973
    0xa0e031501060c110303070309093818060901050d0f0c090b041a1005070305041a12100e0c0c100606111204081002031f09271a0702010e031303 63
    0x2107280d004d84290b1040c8000d200080c2c0c0400c60070151103401c0740203d441c0c0403040300d902401c0e944080343d035240140c001601c003500701d4071002c031000b551044403c0b81910b1103240d085100080290303203003130304001c241005100c1c90904010985000d03200381c009520321038440c2c0321034000c140140c020000b82621041450708501e013502400d01c0014122980d940c00c07801c0280081c10950f54481c020f41405008540b001c01d041c0078801740d800900002c03145410805d4001e01da401280d20100741e0520054129000c60000d41040f10000240d58150480b0f050544810102491301e82014100b48611f2041c90401145c2032198040d080080c900340e1282e03400380480b5140c040c1070150302003401c2c440d039100788010040c16100050000e0410201c210040c2e50340c440307441d600030031521110440030200c03840320001400f00301c651041202901801407031780401000c8400c13600f00c8851355005003411950910b055030340f185401d45a6009101d5000004608024183c042c0c11500442c0f404600d01083d44001c00c10b128 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 875533462 1250 875532212 875532233
    0x3091f09060614090115140f0301090c0513030201051c02130e0c0a020601090903031d0705041b2c1c1505070903080a17280c02030a0e031501060c 64
    0x10024420f80c0040c0c2d1000420003451051007445a200b00054002c01e40a011f411303440100307994a0039090391000d4000344c011480e8028450444118a000c0d500800c8074030904c00d51382040700c10040081800c0c030b190011541900810f40242c0c985010100ca40c41102c220b02c000d0072020303040101d2900c0c0724070780b04d03a01040902c0106072075174248003040f1008107036078003160f5203041d04c55074800021007010904007200201819034420108192504001c22149400681e5508a4004a070180000703003140d041ca00352801102500c00106480820348511540001e60315400000101400044175082000086c40034080248111800c48100070306028480301c688c2440001d60032203400c0c890341c1480324005101c0c02d0503200c060282c4a000c107502e15040e1041c0d640f110380310090080803045042103d444408064112403104601c0d45410078451188000e0051a040001f1a00a1414504407000950740891114112545070040c0b419085056411039840c41c080e200c41d5544145148281c5029017652 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 875534712 1250 875533462 875533469
    0x4170c01021e210705011103180d0e060d090c090209090a1802130f1d1608031c0e06040b0f0f09070501030f0b030f21130b03091f090606 60
    0x120b0022a0b6510205000441503d00c5a50354140d268040008559042078050082c0040241d400c0200f40e40000700b02074061405105421100b00c3e0100a204030242d40d41c0113046042d011601004c01c000907441e0440181c030801400a80c0032031100d4141d541c0c10000003580e00b0201050382d010a16190302e09208044540c4803142d643d041000583c00c80862144c10803200000340304080b8081c00e070540803030301e801104c030080c522a4180640c8507581044a01040c0016040380030f40f190480d10301041c0103028118040712581d501652030980d0701409403849450aa04100b061500c420340803802c00380411205104501a00b2403054608180503c03011500001e05518035820307601003408440b1a004c00e1010031902d0900340001c6c4040c180e10104050001d1007586545070050b03003110b0081603004100d9480000300c152190b92030181c1040400320302e00542035242d1502d6170440061004140700300085803c550070b00200c03406408a11018141001c01542c14100d880d01c43d5001c00401000c1c1c000c12014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 875535962 1250 875534712 875534743
    0x1612020715080c0d1820010e01021507030f02070c0e04020f090408041401170f01080706110303011a221a04030b0f06011e03052202010210020d0204170c0102 69
    0x100c0c03c003407001044900403c140031124075076959941d8501c01d0b40d041c00c00c06040c0c1c44500d81401d28075030160140c5500344c01c0344481c01704003c42c080040a42c03001ca0646441d160301d40c29184141c6904e18104c1c018084412800095a13081000c80c02054882e0807442c010401a2403d07694ad141c1441802007410215003814011003400052000040c440001e980035550000c14040c1040546001220710312a0042c240300d8200f446c1c018003072841455000395060350010070440d09100d581d540308032242103800043c0986908188010700c010401c51003010150381c1588540342c2041e81c00c261143c901d9050080301c28000d0160f00003003104048019805820307240401000c4d081a03c1c607100c450107400e00070820b50313032800202d0005031642c2c02046603002e01302001e24591794010301550098001c03c41569400c203a040000003000343d100000541e0300440e98183c5c058040480da020100c0060b4008540702c43c0b510b030b000e1001041d0340b1840c41c0040e00007031086c001803070300034002c00029040649035a09901c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 875537212 1250 875535962 875535977
    0x1c1d0f0318060406090e06040221090c01081e06060c0312010f091b05091305010605130f080a0803150301050403031a0301200708091002030417030a0f051612020715 72
    0x985600b01c0e08480031521b241d09a00c83e150784040c0094002c0c0f0401c040f4140ca07180401401c61184190590310f80314bc032034a800c9407100680b550054039090004c64510700391074048481c03060346403201d00b080750b0060130103003407035050490041000b81103400031190400c101c0c10140c010400c510606040b24001c2007014000c21074101c035504140907a07001580400d003400700005207420280c43c2e02500c0c0c140e02e1510041006296107554004020350300c40e01002c00500690b0001003803500c92002014101c83d0000c00034180002d490340c81d50b00981000344003074408080303048100d0103034400303005045c800d038402d540020710040c205c2001004036280c0d0300214083e03031405021810942c0c10b820b5061480c0c0120210584034000c0d40b415800500c14640c400e42c210854488000307400e500040a00709851b5030300f01005450105126095803030284444d85000078400c0d4418282d50b501440003070015034851101c4140320a11034940351203441034458154016880101c04021a100150305c1c480c81c0100c2d481c0c104d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 875538462 1250 875537212 875537219
    0x100e0405390d02071b090518070803120403020a05060f04140105060d06150308120f09120a0509011724030a150c0e1306030c05061c1d0f03180604 64
    0x6514001d149100c1c2e04290300007030301400d008000c0c01c0104184010b203240c030390964481c210300010704001d0341c900794902451000720343c0c4050042948001c0c2d82e0440c009506015800202c0b5140c44400f074400e8086d80200d84c1c2c3c410204d070b8180402c5101d008401d90110490502d8600101810500c940401072a4949024032165603030703c00d052001c90f50003000102d40500b40d080803515161450303000030000d00c4001094111243c0040c0054415010082c4001c01e40d612058002e0710b07810142800450400100800907001c4d0140001e4a200e070b40601d841d41c110440d00e0240b100e12401922021a01d03026101401e080e400c1003410b584d0001410350242c000c0c0110b9603184401710f0320f604d80c4030700210f48132240000110700c696440c144102c0010020703003222081d10303002e6005050f2400180c8482072030a20100b07050070b0020468071f0040148003d00e139000c0160072000000d1048040b0910650100041d8440800f0100018156604050051680c520201e070b01101d00d005404262805404280801c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 875539568 1106 875538462 875538571
    0x310060909050c090103080f03100504090501140a0c0210020f12010617010f050109050d11090c180909030a05030a020c0d260402060306100e0405 64
    0x8507540c0300b20f401400042502400054802e401c02c01101a100300003070000d40d845404040324020301919040040c040c0c0b00030502c151410781d100c070200900150b500505641141c0f001c00208960580568042c5d02d584503849641e02003a40494a1240c1c00c4018089541c01d00c66013094001035a12a9070281c040301c441d85810300c942c81440008507074500316080c00e109661050b141c2d030001c9454101041404003000e1340440e420302c40d07010416116207904002600800d03400d81d010b5103400c0421f8403005040500100079220340e100f1014440c014801100700c82d060011890520755aa4403001d007a0043c1c42178403844503180c0305613285403000c20742c8940c03403d1f9190618a5039044651611072031103805501038401a44c0101d04102061252600c5901d084204229090840c081d54020000030101d40382226040d035404964420b030301c2d58410702d061403540c06500c1c05c41c01c4980780200009 = true := by decide +kernel

theorem cover : BRFrame.Cov 875359712 875539568 := by
  have h0 := BRFrame.cov_init 875359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 875359712 ≤ n) (h2 : n < 875539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
