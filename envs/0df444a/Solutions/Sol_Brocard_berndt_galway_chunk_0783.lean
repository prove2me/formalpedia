-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0783
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:45:31.767049+00:00
-- url     : https://prove2.me/submissions/268f582f-1cb5-4ff8-a486-2bba6f239e57

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 140647482 ≤ n < 140827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 140648732 1250 140647482 140647487
    0x4090b010617040f030305091204080313050105090a0902030a0b0415030b0f160e0109090c08090705030f0304120c08060f09011a010f080a0f0914010b010f05040905060315090a0c06 79
    0x40940f0010700c0040540300b4540400d219810a0350084120001c0d2840303e10507007150400c44e0312590001510382c00c04107129006042100c40440200003e003011840c000e00e03c00050308504130360145038038440d400b0001c14040041c0ea400300c500104040c004000c0c0720310941d6419101b0a07140f100700ca00c00000300c006044448a585114090107900511010b070041a00341a5920002c0c040c4082c10010030440c0011580d02c01e0040300d10030815034441d0004ea0a195500710f0070000e860304032501950100b5034620140000000301d90440f2401c0072001d012100342c0c503001c402030049a10018241c0320746014049144042c034501d80c0903004039802000713444064460038030240340b040c05da28003152082d610300c00403501400c41d0a0f800300100c400080c6160031008203404541418005640000b01c240031160059001d1082041481c02420001a00c043c0f0f10700c003d050b0710580c01b41c05200d0b034a941c042002c0c2e84081016420302451204018028130309040543d80e2540000760680d400d50000f04000b40160 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 140649982 1250 140648732 140648777
    0x105040209030a080d14012d0602071701112205030115060c03020106080f0d11120703111f0b030606010906020d110a0804091418030a0f050904090b0106 67
    0x4090003030a101526900ea4001e6a0030070b005c1400b101781c56a00c40c0c4269600320780860701030010344d08040c41c241c4c2024060902640740c00060b0b54003400c481c0f000d001603034000a10f14101c441060401c41441215131119000d022002074002154601181c8007562061044007228030281103003500840c0c65840040500b80c0313119840c00d0940000000d000d220301752103604a00500da00a00010400954801d05207191030040700140304241c0200c802d04845c56440318142c25010904002008071340540040c01825118101c40182407148081d52280b41e800c040c024444040406084400d40495600304034014110b4414420b10a01a00c40007403107940c022191002594000e50040c0b01c00c00380003c0c146d03091381c03040c2404034151017003044807400030b04c0290091010342415000446c035501a003008940301800600718030300410259038a0902254000b0a417104030549240151f106004d20307205603428030900320b4840c1c006042444540501c500c54a030141282c40700d03680c5036000a200d111014148 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 140651232 1250 140649982 140649997
    0x16080a0f1409042d020301050f0108012117220608040f080906090a08010209030105071b0f030909050a1a010203070308040f170d0b0102070f06020d0f030e0d020a0b01050402 76
    0x1d107024440c4115500300b07a40241000b80c5079842e01e0342000b00d5154102c0a01d00c0c0c40e40c0d0440780301e4000006100070309003003042000d256000e0801c00200e5040040909003042c50090403418620015072000c20b1210464811443c0551102c107190340d01c03050708000ba504480902e100160011042002412a00c142d03211445070f60002007144000c002651030403c56885110300c01e40c0b10209102a030099541c031104003009040145c00169100083c0e414142542c200824904c18000035444031a03640c04981c1015404992144501c130122102d46415642e019031900708440311880c040c01c000c00100c0f00d610141c0810152220302200d104a407004a0340c0c5e11523034000400064008000c0317400185040c100d1096540b055540e060134440800318500c060b002030044040d0b10b622510100007950301480754001924130003511070129800c1c070b0406990740044526520402010841c54410940b0a80c490358100c003620b400e0f10f0200b545290000e581c1d90b0000400d4030b40c000e10304000601131030144215400c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 140652482 1250 140651232 140651267
    0x1103070b0c0d0e01020106080d0512010503121209011805030702041407021b061213060b090402061b0a0206040f08060c0403120507030203090a1203030c020d120e0316080a0f 76
    0x5030302c11070440d00c109655100b1410366480d841e011580c100c0510008081c83c0c200d5548030f441e90700406038101480e80613484503021381c1242c1400341c1e54003000411110148100781c5d800301745885420700075005101c102511143c02c049083c0040c2003000110080c40d809000300c4051020003420640488404403c1d00c112015911502d2184104540001b0411044e01d00400352401c1404800c4000081301044607010414284140781c44100107062140010b545800e89084000c0c0c036150f404900c0e80e12584080b03040d1040b00c0d400041c0c810008000703002c3c1c003a50242416417166515030324032119002c20300801141c0d004550006034800740c28010307a001c407600409281002c462640083d035107940188416821408200544c2c0380359240c80708000c0091480200606441025040087c11902509001011504100340c000491a400300c01400142c24401c0c000031060440c2401a00d14850704a213140d000c6400d00c6034806105415002d800c1070f11051b100c841440b240c1c446e0445007580305403c1c00c82c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 140653732 1250 140652482 140652493
    0x9030f0b04060f0e1c020a05010e1f11030a0506061c32040807080d02040f0312030203040b06040b0303280806090405030304030f050714010603020109060306080604080a02191103070b0c 81
    0x600d40580f04030040c9940c0c61b4015100f543c010307a02d1b69400e40c1c11645c040141580250465903407400111440f08006911180402040e50745600e10400c034030015000001864940c00410080d94030701e0100c9003c8180010214100b050300b0a03460b015002200400c0303402c4000341400b01008800c0806a10f40040402000c0040c0d0b54070b66480d1307188e40244100391640d80050111424002561000b0009000410b2007201d90502e90314000810038030400e485010540180f040c0800201d01240d6184c0040e400c40700440e5501c0d22001080c503600429090103008400c16425281e10744207008190024606075850007540c2da90310f400e00c518658180c0c2c00824652040000031b01091041644042c81d41951901c0343c600801c1c1d860384040411030001c00982c4da503440c401002150303007092140000340b00c07030300741403110501e001c204d07e4031910300400c050700601d1300040024041d4803e0041e003900d050700e0620139040030380d1b60070254180ba400f82e8006001e440350400100ba5440ba40c006e80c0c4044480c0c000506 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 140654982 1250 140653732 140653753
    0x501081f120507030f050a06110a020606100201020d0204060810081f05040609020603040b1608010609170709051008070e040c12031205180601050609030303010e0709030f0b04060f0e 80
    0x84854031840309642c14002e50300044002a4a0102d401c40c0c503009000815102100f402c0100482d4240e0314103003a09181041080c88143c0c02154a03640030b4011500540482e181ca03c0c1a806841007543d142c2d4078510000d0042203c40d0804582070091410f4400d6810380c1e51034081c042c3c1d0740d03041074501301c0c542c6c1200d046030103c2122507041035506c00d00c644008180c2c03210b6640820410340094400301e80c41817202c010011003100c210143c004510703203881c104049501d00f1a01a081c800140113801024074808917801300034500700030b2a0300508101c081040f0314680a0700700a14402c7c03034003d50480d0b00598100242d540c1d00c1013040b6005035000f051080c0c006150407d00c608020384208210140103c0322800740c000b1102e80304562081800741d1805402c070b00100b604a0501505800291065506104140d1161000000da078150307650324190103056111000107481d00211503000074001d0310350041030001c104d4074825141c0185e1143e03070f060010500034040003040da00c1c00c40b1640410340c45041c42d103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 140656232 1250 140654982 140654999
    0x210e070e0903270a03150f091212020c0607051b07030c09020c1005070809152a1b0a03031116080319090b01080c0102030a020303060607020a0509100501081f 69
    0x80340312824003c2c0983c0c8800648002c20350302c40d101d0f802030352968044901d00003164054020142508014481049110556906c14074001c01c1e0340740149c03c0088028184402032041c1d811641c5c200e8501c4100c46051500c61402013460340030f0100003181c0c1c0c1c1042c5400d1960700d0005a040156688420b620b0b0310541018145802900110180e6100b4840c0c144661079031800c0d48120b5001d003480f5070f1401e09503d400d210282c644882003020f900001168410449071109840302d01c80c3d961200c56141c08403941c0807412000078041c05098820750000e00014040300c10000420b01c0d1000d100343c809025401c407100f90402c0600481148199110070200110005415500150f41c0b03c00342814001038980761100d220100c0b054501c1c200c0703088015a00501c0000001c100d0510320b03000900c003e528243e0206402500c0340030140015000301800f18001046503030303408100303010f0100904640c0862030711622990100c0390910a45001c104000049074001e401028551044c0c1d6000080c1e402c0c461800c1c00f031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 140657482 1250 140656232 140656267
    0x11b031b02070911040509040f050c0a060503060d0309030507170705010c02010f0c020a0f080109060605030606100e06070204020c011b05161e0b0c03190203040209010e0403210e070e0903 82
    0x102100d13140411000c2010303078812040b1402680109400b021051461520074504030200064034825080c0100800c002079025003141d50083c805c1e2510b0f1800075461500360792041d8a0340004126024142000c0f410048480e0507090138488c04045483c0e0940c2c440c01910640c000c4031006e4001040540b088010710b0140c2070a2810303d20140c6000f40d91643c814200b00e21403c070303401400d41c030b075140c2c0540400d0000703500403000034040440c0501707507a0505400241c0041d2410320a0703024414924182581542d89a0a031060641c01901c19561404031002c0240284403c801c00301c0004040300d84040c83c6d601c640180c8200d2604440500c4101d402e64990580901d61248000c01c2c0700c44044807100020714140402d80240d0311484401d07180e091010031494892a002c2c1550441d92043c000c010160399841111030444803a11a030b070f00c560b11075003000c4407040741018004645180310401030020003840d611402d9020098030580f8a20740d1180039a5500000969a03181d0f140c3c82440b0349113250005251 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 140658732 1250 140657482 140657501
    0x903092310050a14041d0a0908030c0705060717150607080d020403030912051902061306021c05031e0709080a03020c090a050601080708060a0503011b031b020709 71
    0x80d4500c0258558000355010041250210001d003000c5214860242c00001401c648001c1040d01400d140c140500700d0300b6518812407416202c0000c0000c00e50b41500ca600000e40960046403660f640e140100c0203c0741070344405022503080c460840043c0f1202e2203880d00380c40859012001c0ca60903140c044c00c0c0c4500500c04105c2c80c0c5c0c44502000701d1800101800002e20f1100c04103400941c40c6c40c65410094200103440d0b000007170152003603104000080300070680812410107075448445295403400800c030f0b039000c1e601c00088081c07010342c00481c0040c4c0008007503000118046503e81740100c2510708407031500098410342e103c14400d280c1c0c0e141c03c080c0340343d00c164850315501d000300e8180d984c0e44070701d440c0815603102030303002d60030460b02580e19051543c1881d83c050300403c002c1c00207080400009000d03000c0102540200b01900d000b280e20390b5284115030005180060013030110001c01d038000c005c540c0141000c800881c1c6491405c03048514103205071500d9081680289c00400c2c50702c1e4481019004000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 140659982 1250 140658732 140658779
    0x1a090601090e01091b0f0c031202070827040c020304051e030604060c080705040302061204110307030605010503011b0206010b0a021f05040c051c0f02030f03210109090309 75
    0x1d10114100c98000b1519009003040b100c00324407013011204a8030890042e11014041250044000740c1c5a500003a0b0b558525600d45855032004501515260083c09a404020a801e40c0059804945052029105003900c1c2078803070031041d43e00c8075041000300e0702e0b00c2200001617001400100050f1070008440c00841d0b0100e5072490308100789038002818080110b80c02c40b4a0356895101034802580100314660024150812501d81411500041d4050084901c6a4512290400000c0c104420080c546d050440d000e021034512540300d11706500130b008240075040c025803a0a00018600c407a00406007400b0300e040c0c0140c2041d0342031a065442e07d500031200c103401d5100302d200c2e448405100040780c200c640030001c00090b0301e05103440c1070902d80020b54862481001c1e140c5003060040038035041140526482443d40d00e05a03910300c04681002c2d403c400030381e01c4d0700005c107820310340c4120040250100039040000701601ea880f04074520849a51080103000100c0500090000d003101c00c121403110300815 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 140661232 1250 140659982 140659997
    0x302100e0c0f0f031c050c0c01140d1a061c0b042a0201091a04030e120c130902062d040e0403050c0a052d0118020d02180a06050a06031a090601 63
    0x8941c90070b0a111465030f4200003d900003510040d880c0144448c40b1004400d1904501060740b61080e4000740c09894017003003d041d0f44400368070700181e2260840303400c41c9010b80385940702c00499424080d80e1000d0044100c10904004400d603151506103e0300864400300301a03d50704840100c000b2500d80c0c0740901c15130542d989d400b2400d010625500200110301b46518442501d440d09180c001e10891480307940b28001d0f405c0502540c0f107000082410304600030140d0b001c00e50302c0f1403000038030090805220003075001040011000d000b84024030302d018900701c003002d0403403008070540701c210018411480354444581110000c580024440c2c40101840c020607400c59140c030f000ca8070384c5400d15134241030340543c0c810a103443e208104404500100c402114000803c017030f08003800108412840c40d030000b80f003021200d031380c5002c42d600c07c1d0340c00d170f11107010075502c10003440c001c4207031070060040b405000d21400c0340e40c100180c940e00c00c1c00b660301c0104c0b07084144044403001001380644404041d100c5810310500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 140662482 1250 140661232 140661253
    0x91b0913090f0c080102070f110616050102030105010206060a180b0a05090a060305011d0a080d060f0b0903070906050609040908040515070606151b050c09040302100e0c0f0f03 77
    0x50300a00300c40c90300034590711032210384924000ca035804682c4d112441990041c030404001c034210010070901c0c5e5422544ca003140e0304050002842c14820301c0c46058400300012840c3c000d2010541c082c40c1652801c0e022100b4903102c20b0101301c0003128622480d10360901050308004c2825480d00100f070080300192550307500544540c009044a841210300054240d03542000b0000d025007401107446005a0758a446c010300f1003005076645071000028003805038a0001050000e10b111a0b004030010401002e03000482c9841700c00388062175009402140c030a00c5210301c00304402d422803140e00100c480c020440c40c0b0f840c02180030b00c00a081c40500076039081205020029254513100c0d1000d0301340e0300040c19281e540d40d03145000b40032a110794121440399090001202e601c035400c10040620700200f11102240c1801c0307450000d15020038138141941003070710141804101a0001080144200303494810b001103902c108a071a82c4010348010242c0c0808182c074480d444d400c0c01e00303020f078400d040501a6100c2a01d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 140663732 1250 140662482 140662519
    0xd03030c050d09140d08011a07110d1b080726120408010603020112050601020c011125081c091208041a04030506010605070b04080306030a1b060905091b09 68
    0x4501e9400c0e0b40c1c000780012442c403400c106000b001170088131400c0c5040994103100001c0403c0c91200350f05150003100090031030912101c00c0d6032400d020001403010001c00c02519110400704605842c030603034052054004540380001044400c152100115169104203004ca4400b400c018620886403103030043c5052072144608075070080c4090a8488004100c031840d5100040000200c1000b03000301c1450b20f018000d039a0382c08684c403040304500340f0b0a4407041078140c0312141800311158285004083c16014810801e550800c044104c50b5814103403000506009100440200f000100700b0014201c030760706225120b16200e8611880340254149800c6c40c0c4c6901e02106400f180b2030141d2111140480e08204101c6d00700001c071301400f0746103401c034100b645ca40c0d40e890380d00f200648010002c0f280800054460344080140307681440d004058110640502c41255803408906e0043c5000a440c903030340456a400c0c540e00040c0038812400c80c2c0c02d91311480c490402216008107901d075510203140c1052121520303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 140664982 1250 140663732 140663741
    0xf15070e011b05060a0e0f0f0606010c02180f070e010c0201090e07030e0709050a1503050705091905070c05070602010e060a020705030405060c070f0509010308031b0c010e0102030f07020307020d03030c050d 90
    0x601c00c0717900203642e24100c08510b00d040b405821a0040754040702d401c01c440c3c00d010071920f42000080c00c0006801c481880014039224941040f11201c85810003000b188209001005008140c0c0c0c1d11004181c138540d100444039601c034078001038003040180380108007515407014000c1c0d200b4824a4009054803800c107100c1c1c1050b5603548188590743e240e0040c0705a1000605c42c080303160010030b50b42e500091941d41c90903110903141c8036441c840c40107000001c0342c07010324403801c0c10a400b01040400c0989040f4601070b007000f44c0c0d80c0703081d2010702c035200000c14080e00501c10300818000318002003a4036a1005031503030207940b001504a603903010134400003c8580350800a0400300e43c50130040c1052500308246007200c1a10b0f0380c0b01c644922103c0c1c0c010030104690710200c83d0010303280080aa04881c1d9001c03001d036a0721941c140b540c010740ca814940e0380030020650103140285850544401141c8490404a98074000c80001079802108064200c00013030003035011200c8600746062203400c1c100b60601500446 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 140666232 1250 140664982 140664991
    0x503041a071e0c02130203070f0c11040e0303070e120c0d08040503070b04060f02012009030705060f0409051510180e040f0b0901060b0a0f03021201080f15070e011b0506 74
    0x41c3c00d20869204501d002c0b144555130300c200c070b0030441c00d5180505008007000d007401901424401040041c2040c00b601c28002d0741038940280040c41040d8000b00707119071340d61040740d61000082d2204640d0165140c0f403890001e082d0300c940700800008540c0400c100e65412014402c58400350200800541c40c1c4050140800805502105940301c03490b190019041a50700b20280c000c6901d400c101e409040e0016605801c1010b60903030382c54407440705c1c5010030300d000400e82140d41d00c15008103c0c215040d907500700410548080399170a0055443d100400242c60b0302c100019507102c4488010045441e01c15916180702511064400380807990311198083c44c0c00c015a001c2e0751403e42e5400060902c82010344440d000314018000300303c0e092501c3d0b421900d07801402601410048100560039441d48a0740564200c040b00c0641c2c4505541d4501c0070b00d54444410340300c58180e01030220081e524840c40d95040344500f8007601e61a01d0f0070341c4200112003140451200380005000480c2c004049101042518482d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 140667482 1250 140666232 140666237
    0x204050a060206091204030c0e0702031b0d0201111303031b0602070303090201030506011e03020a020102040b0c0a0618080403060b060d020d051008190b07140703080103120503041a071e 81
    0x150304084e180c1c9800c100c803c02d020112850100420800103a01c0c1d0031000454851070303111510b527200d821007203003580300f0343c90780c104110102042c41e210b8150220f48013882440d250002c001c038000070130b50710055001d9a074100545c841d03401c00800119004004444c4407803051910102c0700c00b080c0d91520200d8001c2e05041e00042e5458000e41704550301407181c50f401640c2428005d20441004040b50300c030030480b041d0101090780108004030800d000350107680c0503108100105858500301c004250345c6001d006d41c1940c1d10f900b0311145c1040041c440c007001100d240c1024455103414103640311070028001590b0303041e400540c1002030042140c89840a07180f1000003880118403820154440c0b48918501d4004a41c160170032141e40846014220328041e2840d4400c0d540e4115943d01c65090b10300c803000b520300c1420003030001750100816902941d064180c03442006845904003500c8811212400110350043c81c60a031403140952028800304a55400740c002d18142c4401c000d04010602c4d0038851000403c003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 140668732 1250 140667482 140667493
    0x603010609031104050408270a030302240903480105060405070c062c1f0c090b0c070512070504060b030402060712020a0506040b18070501210204050a0602 68
    0x4000070307043d6001c0d110f1401c640521107801c0503101c41180d13100d000c408491150706940170000007140b803108403841800041100034107650f030b0308000e500c0e03e2490b040041d400d010f0941d80f40800318440101c0340150340360700065007030143c3c1001e911038920707001421002c090702d100419031281010320100c1c401c90303442d1000c1741403030b142000040d804d454010789030324829070900d810840c1c0c45030b1190f05c26142642101c0d010801414600d0300405010900c802100c0e290300c1131184081105001441c0c003141e804400308514180c503004035010480d2040f141e0200002c881c03d004000040c0000081d140b2080400e050750845962200000c01c4030040f010074402940041388102300380e1410744101001000d40c526030a03c1c61805a00251451003000c100078681c1c5080403014000303a10801040e08a0f560000444a4508150904a0052a04841c83c8003606220543d070207011102241e240b04a41c01a102e80c040c0c0f506000c00008007083e800e901481650b400d0100080550b1003090001c0185519005400e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 140669982 1250 140668732 140668739
    0x1203050f0414120d0813021201050a0b030f0c060403020d060f09060b03010b2e09150c02090c270415030b010e010b04030b22150e0d02070f0e060102010b0603010609 72
    0x3c11410110048030f8035401c0070188070049034104014035030251158000440d00080c40c0300085449204107440d600760340c80e000800050440d6075001040c210005c03001c580005003e11031203603460314410b1142ea004541400200018206616003842c118450480402d001309005129412a52001016110740d912118201d0381ca00b001e1148100c10041511501030010091103c6101c81150072032881512550220107601c040c07040c0c1c15900a0181010342171031811030342c0001041081e00c1c1e24103904c161540000b01c3d52038a8028100c51130808a1101102c42d07000c11512441c4c0410380c00445a0000c0d00e524240441081407880080994482c41500c01c4039410b060340580e2000707050b0841160288100800d01c042002e105841c1e40c4140511105209021002d610f480307800e208a10081c1100482d800781031401e4001d4110002040044c000c035030310030440d5001266a5034951081080d00c0c42404414081203101c4441d40c0c6c0d1105041c000410070381003040205950354401d034450f000007442d104051 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 140671232 1250 140669982 140669989
    0x50f0106030c020f0319030605100309050601060309020f100207150c05010f09020d080903011508030d050603010c200304050d0b0109050601020d1403100b04060e0405060a0602071203050f0414 84
    0x20310350514a40f00620310240c2000c07145a8038858144000401c207201e4102100b504d109411140203020301400300d0b07440800582016001e810070780000c44450003404d001081c00d503c00d20601c7d803026001800c002c81da819407018420302c0f80c00c40007140114014990080381280e254049840080c005a403071050f4141c0a041442c21105211036004a0505101d010340c05660f03492003284545400010319a500c0d03c0800009004020604000040d5640031500142206000c80600172403c241a418020f42d42c0705802c05080316804140c0b84041a2601c0d054035090140f5280316440c110802e01700ca02e07054076034000444e40d2115550403030790044900b005004540c854043c0320303044082030008000e610b40144000c0c010340b00900d43d40d1030408010001030001c50070345000f80300801107410180daa81d502c0d840d00030290100001c10703500880c00c2c1030100341c807400c161040c4011603203503030f025011407814802c1c0120041c0703020805500300304e810b0080c07041d071840307100090009000894425045000c83c6051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 140672482 1250 140671232 140671241
    0xb060108090f072d0e0612100612120824010201020403081818070f120b1005090a050a0302060d0b010c140714060a080601050c0102070c0f06080c040812091201050f010603 75
    0x1807822510b00000c1002800c226190342c1c00a600303c0d1901c0d020170081e10042d10b04080248001c070402c2c201400000d00f842051401c05801e40603070070800bc4040788100070340710070f18181c807008488580100c0c00101710054000304101200d0510002d460540d0765102c410590b00002050112282d5006100c0c1030392400050b010409003085d9180d080910702114007401e104228a0b112042c001841204000c0040650040c081880002d10b10380d0307542545a4001c081d038100184003401011100400310b0a032030410100000c4075030051195240800032420b40000d81070407110241400b0300b10300d0341800510040140500440407000801a4524041600b2810f03110381203e18010700e010080090aa58000c02095100400382841c903914085841c8550091068000203050201000c0003c10340e6030070350740150700b201c441c5d80e034280b2961969408005a445640b084148540c010082d440e1025030840247c514000010062030100c2087d2000a0a50b4400c440e903003e0501c080e401448400e4042c0704 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 140673732 1250 140672482 140672549
    0xc0206010612092a0905010f0503070506090612010b09010201051b120c0d020d0209090a1806090f0c03030e0907050a02150a091e030e06070b060108090f07 68
    0x40259524016001d004181c0005804201546a52101c014803c02400c298a812040107074180f41d541c059002d0b159401542c069a0381441c00c1000028000b60b42c0001786d4203440000303026203000d43c0b90908200e0540d210004054010f1b0060250f040c0364114010000d000f4040400c0700e81c0d030340705c0180009084030001841c03190307190b10107210100700e1403184081e00c45044034090f446c03501c2e480380c41030fa07d01402581c0d0f0070309156000182d00c0c14084521340241c000003005455018554941014a0040d82c0d514240401281038180f01d00d8085032107600044012409000c00c00102900e07903c81e58411a41c40c0c0041c3d0100d0003904002c801c9080104046500084918145041405203d0020344500c00c06a4200d10f0141d601c01044402c0b5030344e032060608c40da204c00351032000d01074000c0c08074150041500583c041014003d00c29a241401802c9608a0354001001e03552a600c00c1c0040d50780d41e90203000c060003441030895205c0c08007410000070010b0000b04825222070201066801d400002c1c121 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 140674982 1250 140673732 140673737
    0x909070902031009051e150a0305011107020a05030703030c1203020705120c190b06040c17041109071e030c0c1416140307030314130f090c08090604060b04110310090c 73
    0x780030341c3c958001b144a580145c3c608290008640201000075464034154101800c00c0d460803580d5400303880e18400504405200b51040c800c03169640701015200c121a20003c0e010501c05003010340004c0e0803210200000c029418010b00b421410380301c0c00e00d4603005c01050110342c2c500180040ca800304c02c1001c0b080490340e400c01c01d071040c03000e6a500118240081c141900a40d102d201e0300302164010400348080b840048403503c030915044c24031103203e0300c0b0b02000502983d24900400e10b003034800c10072a2180c0b0082100d400440040a804400400130a000c440c1001044961400001d520500343c80c82c5207a54002400c0101e240c0c03480300140740865000542801104600030b0b0750762004186c07102281c0c0c01d400c007412506070b0301e20b942e1980c4c487c0119446075101652004a456103040c502c40781910000d0b0307402c0054141d0100c064079515402d60390311985500410001e80010707100d800c00b194414010b88042a0b400d0585540201078000343c0d031002c030383c0c891603d0034440608144110400c1c0d00152 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 140676232 1250 140674982 140675011
    0xa1703040b160e01030507051b0706090509040c061b0206030f06030601060e1818030d050109050c071e1410021801020a1703060a0f0305010203100602120405090907090203100905 78
    0x5000242640307a084983e00c1c107042d241c40019480b43d01a90540d0108000d51240600401c100e40c403a5484806501030f94011402019011585083c0030703000500c5035501c6507018041c941096000d907100845200c1c2c403101c80091810407801a11000d01030340c012240d50011005034101071042500b03081050300004200318184842c00c0a903503460390002040b01107140440400d8541c0710708111440341c07a03a01100240701c005913140c10283c866100c1c40c101d45180c0c10400c5680c641444000c1c42d84101d800281c000301c8080d80d00010504000608031000d88550080d00701d0002d20310b1070a0511440c28403d01d0746d80e1340807507000b590070040d2a40083d41c00e070134030141028462654070302505451181c1302a011080c04400103c030744c1c035000b80e41d1008e0720302c11859207801035692600e2400303907008403800303184072108000c000781450002904452255a0590407800c060404040c4800024000c01d01c558038464040001440501d52009501600c1c0003848038070a80c2c10700c0407071070580d18060020004500304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 140677482 1250 140676232 140676271
    0x20d06051e120d0522030203070b0a02061b040501032301090603030e10080f04050a02030303042015090409020f0d0308010608010807060e040c0e21010c050c060601030902030a1703040b 81
    0x407404517541c98a80c1c0701411401ca02c3c80b480800030540542000390140304885001c80e85407030309030141c0015001035003151031070380d00d600140c501c00160201b4107010030703014003080c030ac0d56010fa08441005282c8e0400103410b8a1101e40c0011070000c00e074002d17142590341c3d40c400d10a01d079004106202c0380009440300d070310001041100501851009004488944441003c01c04125061003000c001c540c004080f02c6c0c80741050304020f80c0d140f080c00b01d031b000d000c2505960400c407410b2000c5110394200c10b108650741459403100600000c0c10351840c003240d0082c440c502e124001c1c4d13a814208020380d4003d599a5240b9810300201400505041e040581c01d42c0c0016020403407560b1010000314540410b0303030042908407450009a82480a0461040e88100f003062002003000e82001c0a1035042102c800034008482c3c0c402d416511881060009482c9401210004001e94020f03000000d8261003d001c852030384c0310359150301c81c1d000ca204401d100d200400206000a0180c0c107115103402182a6410340030000300d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 140678732 1250 140677482 140677487
    0x9171903090503090913050714270408030c0d0908030402121903050a09170f0115050f0d0524040c06030515040510080706050415050f0d020d06051e120d 67
    0xb850510a104044a900084110040c48030340c6c8080341d8814200c0e16441c0d140e040000b21400b15080c89405102040910001507210000d180044172540500303038059119a01c03151010b0344020681c01e0011820002d402c0748d4078581c8a0440100c4c041c11302191641001c0c0704000388805002007082c2a80d109102c5048070000c20301d0100c4485905040007503991150300025103002070380360312030b80701c18a02d08295800b2580108645480c4c800510003040400541461000d810509025150308030040009d02051810980410413156000b081150320601084040103c4104624032649940140d08140810001d030407804001920140c1001e00140c07070524141c02d28001c0c5c0303101683c419612130f808100c21407030000d07001010300241c03015608103c3d100c00c009011603200d441103c070030a00305000204c2e04ca2081054400d41264031110fa40307003403840502403020750000d80303a0342c1c002503440000088a581e215000b407510a0741c442505403207600d030400c00c103203408006000001078000551100c1c407030380e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 140679982 1250 140678732 140678737
    0x160503010e2a030708040c06050c10020306041b020d0e0406031e020f04060f0e010f0b0316020102040902071103100501060e010c0c0305030706051605160803070309171903090503 78
    0xc1c0904048200b60520801601441c003004164080101c00802c1c03080084d80204a580300701c1c003441114030f00981d031f54000c1303c041c41040002800c640142c0841ea40c580c84d00d4008640101c00180042940c0412040300490b401264254002580c0b1107001d2090b09508118902040101180c1c104490b0f803071601c2d10028400403280c954522483c00301200110340e601603c004016a02400400c480c5482d480040c0b62641140254400000240c0002131502d80c0f2140400c241c40c010200503080d6140c00e00540c01c41003282e050541955000d200c089070903402c502c05801c80a00420740d601c501c10083c0709048c1010303161001903071807a04000042c8051900684c810008241c00c1ca4010210300c043e05001616440a400017041f81c00001100014090f250b0001030003641c9401d0008809144071009640728401e24034004c4600f501e4400c0314001c04c1d5048040c40e4041c0c094140411400510394404019281c0040780c1032003c20b000c50140c100d007010504010f025001400c0401c00311986485180d600d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 140681232 1250 140679982 140679991
    0xe0a0e07050c070b04120303050a15031112010203240a090507030f060602011b11010213030f0605010e040f08030a0e0d020a031101060302090402090c0405120106050328030e030321160503010e 84
    0x41d21030000c525021030352f902107100c2900315000442e00c0317a100d2800310052855051071912904083c50441c003511818800c61b4001ca400c4002000c0e8102551568898107075020007465002c000e4240008889095001d224850784450741c00084184140702103108a0b0400c1c2c102108580c0f6041d150a843c003904140340c04160143c1c1049508407494150361030180c41200d00d13442407054802c1c0000200301c3e103441c410f02d550784038030b009000e103a0b210488003010200c00c45020340740c00016814800414203200046800200e50b12000c07d0514120442902d0041154224801a84480e44e1101415130008500c892800068000e010701c2d440c580008041c180054400f82c41114800b0124030320a6030306084500501707020f01903000c6540b508486500a00482c464a4002d00a400c0d1418011041c1d0a810315103883c0410307810f00c00c00c4151002c40fa020300654002d03400d0300c010001100031080b80400907a142e81c40c0b82c0e44c12640e25258210380c90a44842c100d40b0300f44a0b0a00042c41403030102003007590301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 140682482 1250 140681232 140681237
    0x1206080c090c130b031008030903030d05041104110a02060c090607081c090b041205070f030e0a17010f0e01090302150406060302041d1e030a0e0a0e07050c070b041203 73
    0x454540300d501c90103d11842807500303a00400350000003501c4c19140051846118001541c16150b076480304a2a260310404103d0360303060300f081040302c1120015600103900f16010322800828034044a001c10211502d052500b03c2606c40450109000c035410046181e0251a44290a042031800030201c3c01900528400800c00c40d00442c1d6213901201c1c5ea00300000c05040d581051190007014204440d504005807025106110f00b10f03010b40e6403078000c8040f43c100e04d40c401d1011800420700c0d20308403550718038110103a621030301e00c40380004d0445d8030140e4040603c0c104000018480444130030304044800f51000382030140d040040d08000b00e9004224031844024810f2217a03402d03510f915100340280b5864100a41c0b040c508030032005000c0940350030030a1040302000b1207000030110055280100070007150344503954410806c4401d440d2054004505003400030302442d4440761981841822113304540d0030000440200390149610001c001c0c01c03005012800046191900744840207200c10381c6200d01405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 140683732 1250 140682482 140682499
    0x14060903100c030c020f0102090a0603020c010f05040b0a06081609020a09080f0a030e0f0d02060a020a050625081e060607080a02060a0f14011511100c1206080c 70
    0x15948091201c0d6101d18140c0004114420034010050024000d1880760320041c81014082510080140708588104c280101520030880c0f07030a100328060742c807034060036002d5503d401310045419a80d0041a000307502c111400540f030b14000070040100c40c0c0320f51180e041680b090032014082e16140034101e090350300b0043c0150b40e884024105850220f09a4001001c0c0d00c42c001e000d1f03010300e40c08035108546520945d50003c0005011041018650312451150350040c0310180e40c20040ca045001460001b1007401503803603941c2c0039166641080c2c000c85d0421081a000f007507039080c10032507282c800807907000e45c1090817041c205840421040d44c41018201c2a511030740c0e010585690340d15060b00ca010382d2000c1400c0c1d8a0100440007900c40605035845e500c01410481200e180741d500b401035000060800c507030304080e40c0c0790102060001c84640e10a00030f00040020180c02150103100852003e020100082024290304000810205150486e81e080c03d14104061091500c0881c40c101751031402c031005030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 140684982 1250 140683732 140683747
    0x203040503070b01030302070303090b0a1d1c1109010b1c05100b190e0901120308040c05040203010b030412081302010309020118080c01020c0315060114040810021903061406 76
    0x30724500c0b860401034003448500300000201940040c6041c00c0e45e100307070b07241c030207140c0c0e604810180e901580c9805002b00d040a03031040b52080500a901c00c0c800d10013004549004481d192803150907090704415035065000c01c01c205480e0610000c568010700c00c1581c0e00d4640146104d00d0341300354880c0c03a03000305030396102c40200c0c40c041003020039640504444031030303650382e071105041c080c006051000300100440c180c411150300e54500320400c68122800480860312254280da4111120140100100c5030555404808920f507225403020394064038101c45925580c0c140b50a0036143e0034115944081040810801c2000900c2d0805045a5913070b23080c200810440c000744010307036584035203600042c00710101c6800002c42e0300c000114840029004c0e000e40e905524040c0c24540c1f0740c5041c2b50401c98010801010881c84d5101d10654038a00040c2d050301030400387c440c588103040ca00d848600150854000c038062070b20f000e42010385101284682070800840b450810100a00c04401d641d9034401d28020a504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 140686232 1250 140684982 140684993
    0x901031b031205090108101a070816060905100b01090e041e0309060f0c08030f0c1303050304090501050609090105131d0f0606030601031e03030902121506030102130504020304 77
    0x440c05150300402003219008140e00040603034005076102400600010301140078003440c040e140d0241d68072a40c204512400402200540c1e41c031140007260200800c11124402c90100c13101c0050303c9104283c00b26041109052042c640030410114140301c52610b100841e440c0e80117010202143c1d050311000c01c080d40d0707508214101c180b002d40c03504054680900100f0406074041c2050040e50515184e0446039848154115144120407000500040082020445072880c00300960b901104801840e032920803401150300c007950895200700c8084e400030509100310000350041e6400340c04259403050a022682c1c1c00603243c0d0380180304a5001305041c00303004224400c242c02003400d590a1a01520306214541d02059482a290b1080080380c02058089000ea1401040d55412079030091000d808026154404c260304844d821300880c141036490329000c00507195280c09190120710f06000c0c10342c84c84e48040c11000090b0003019503109910400041460a446400000c1525410f540041c0c990303540d407400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 140687482 1250 140686232 140686283
    0x309060908130806090a081206030f10050a0c08090c0108060f040213030210030903120e1606020c030f0c03070e0c070c0e091603020a1404200c0714090103 68
    0x141503910000b4441c55030301d42405030320003220012400c64280d075480c2100140c83e0410f507000180345550410241c5500b4125010b6a600600024156000329803410080f03071030000d94180c1100c03019111010171462940c10310134084240c5050400466500d000c02d091500d6840d01c0c2e070380c41c0c14845a400410010348030341003070309510b000c043d108540d501801358000c00d030050503100c100e110720242c41810b440b9074828020342d900248e05403602200c0c03800c2c070f65161010f043c100f21154001d05c80e4900401d0f1216804607900e00030600c8e0340203000e884045106241c20044200a04013071030340f03c01c00c1344c002510001641780072150304c40134407200c580304d100846900b88188100a051000a020040383d0703003170090400d80c01a01e051084a0741c19802c40c1705401c04481611010307500c1112003100b0002024090b242000d980d000402c005292000c040690047c8899018130440325180414400c4005404010485c05408003004460120b02e1100000d0310f004414000200780c00d81c0c4441942110161006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 140688732 1250 140687482 140687501
    0x20606010512073509011413030c05100207062a0f050f04060201060e0703090f0201030209060706050424050405030f0c0f010c0e04380325030b0c19030906 68
    0x40440d45100c284d901860090345000c0e81c04c200040340000309650000511a070100c1c0025003002e0115590382404842e0210700019058041c00308070340800001450034001441c4032409402c00584410301030030004102c7d004c0d10052022620a02c007101202044856002e41602c400e1404642040940408407540d000725039521320320107800f080101d9959011741002d41500c445100b002c0c0f050351050310031030545019400141c00141d410503840301552083e001014034190103400107107030900c0f5607200c070101d48013100c00359200340404611100204603514411190220b158013030001d41003507140c194482c0700d903c803448484400082c0200542d031081c01900801203020000b0807194040780b00140c0005086004903104514001c1e0070804003140710307034003031040c3c15015910b0503407403d010900400003884c10000d81c0c1840782070503109100c9480703003032240c05060030081420001d145d0300d44103003070b4180034240403c2042c00340050400902c541812901d000d146245c0440ca038801400c00300e00a012800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 140689982 1250 140688732 140688767
    0x61a03121e030907170d0e0913020d0f0501060602010b030c09060a0b03010801020903070501050721030213030f0501053103120e030a0e090702030702010e03070b161202060601051207 80
    0x4102403403c02055100450312580c41000c0d0015130000083e031266120384e40500451011800b0540c5401c1c1002200e6029041c041e025017220039940014001d038284042c12107510500f401100100710080c002e0000904c550b00003440b002400300d00198071040044411405a03007050009001030b680d240c400c0c0000c2c402c03150301a40d2540c44100c00c5010354000032099020340300c1c140e40040d407944641c007101c940071381100000006d5200316000104d0403040fa28910304241d000d10110a210f020071401078021842140c9140c26044070340f60031829144024805000e00c407070022580807030441110000f104a03c50b00350403c0e0300c42039140c04e503113030300760410310240340ba06e440c41403001d580c40040203040c0d80c4131903120250a070411204116682c041140c221005820030700c80c000055010702c0401001900060903610303203688403c42110f081c1c02030722295190a0f6a452030a0500013014403c52403407000e072010305140d01e8000c0018140388540e400320103100801a0000e80494818050101d09110b441c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 140691232 1250 140689982 140689987
    0x515070803040b1f0501200a080c1f0204150507030c050703230a1e02041b020105011703040503070b0d14070509100201060510030e030c030a0903061a03121e 69
    0x24106600808402c441c014948030b21503111007403501d20020140111741050b9286001d1142800304100c0032001070700c0d0180b051017144105400110a280680340d0643c1d401e00500d031110041040b50104044000c040c0e010781d2041000748100a0396118042c2030711114141a5a51040c924088440c000010400b41c05805410b03808810028840344020182c8003004102c03c50701c200c00f1380075468012084004100d1101c42c80da00340901d0700c118014940d00c1c001003000400f180100d00542c2c6108000210000603590b84c401840170700181c42070b4846d1011100c0c01181000e040c4400700ba51240c50340141e0515440100701182d06103500c0c0c100c0b4100096441090025080280000c0c1c9160007803440c0c1032181500c1d03010a07504500c14420642114002032090345804510f2000741c00400b480b03600200c0c2d40c0020002c41107400005c0005209605140d40d90320605d41c550708240e000ca4000c0900c440c410301990f86c525600c0d9030001031021007201040b9441d41e50360050201c06e0b000034001501701c070120308003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 140692482 1250 140691232 140691241
    0x10f0c08030115030501090203060a030308060d05100b010f09080a06020304060209121c110a140304080312100504050c0a0e040209102001061505130902030108010c090503070f0515070803 82
    0x666549100c3c01c185900d0911060b40c172518600d050b40422144550441001c240c01c04c0424407808942d03402800c05042c95240c2591900d8080c2801885000c40c2d81d21604d070540207289e940e00c00604d072158841882c02c60351003400d02c1c03413041d150350b440c801c0a0702c42a004030201d01405080c0d1304031403812000400e40003d03100920200d54907503144080d0b13103100c0400c16500d00092806400e501c2d04020600020b0000308906540d240c0e0403a19042c13000c0c0c0c0620043c40080788003e8108020300803a18140e0340c1003250700d071501c201c1c5998450394001500950802c0c00740304141c801002076a40f45001403c0c010004510040428000d00130000c40a91100c004100a0305503078014900315003211701009a680342464030355860b400d8507501d201c0d80001c1707002e441c140c40100344140090100544a034582d0b94004d6900c5854405980080c0c10001c010703550741900700507190700f110102e0010001a07006d800c40901e0550441400002441040e01840c5110145031000326120110360b0519408002d0036244e080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 140693732 1250 140692482 140692499
    0x9020403060905100218040522050f06070207030b19090b0106030b0f0d030e0607150c0f110c010e01050c0a0204050408090307090207080d09060902090108010f0c090b09010f0c080301 80
    0x80300b1000740e6481c0203641c0c908004a4a074001c0b80e40c50a1402171490540c1010760610000703210003862480c20b51919280e80041030340380418550b0003402040101480a070b240c00444c14450090184401c0d0740c0f00400420008080080c550341c0b00c5070400074a03448031640c2c05c42601a12001380000e00c100314900021403003503056071019030014010f88454142e40703811030902190400100c4041e0104060364520300c8589450341c01401024820748003980380d0307204a10101c00751000c50441d4804664650f029110342a846000c80608a030403a0003840740d03460b01e0380003820050740440385070704015000074001c1107108104400f03900c0c2c60f40034208103c1c9280500b03024405401801e5600c0c828003c40d400001c4060050003665641a004a1400c0c0b5014186d0b10b444001c080040049030b460351034500071001360352010034442c020318005001081080e11804100211000b20005506000c074154081c02424515000d50345092001c0c280185914404a4203581c1e11110382c000400e010000400441d4902 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 140694982 1250 140693732 140693741
    0x9070201050115090e0411060c0703030206060103142403031b07050406230d0c0305060a09050607031e05040c0512010204081b06030402040b040f020a1706010c05030d020d060902040306 81
    0x743c0700581107100744402c1038212014038043c8524241d4000f0400400c0106d0300d242c202c1b80b0358400081c85146401700442e00c40e0708000442d40107030050b8100200300251960580620440c0e0780164080444910305241000c4655101448810943c800e100940300c10352403c10441d0300c0c040f400c900c0c030702c0410300c007104507a03454042c1c0c02014092420050000741881c50710080b240e400d0300400110041c061610b051144840b1010002c2d00c002180904c00004501c0501400c3e000d034000c4900410442e245041140c03400030040c00c500708062070007180c45c0542c24402034411a00c2c61091010841e5161800d000030740e054a60411980141100c85410003004150300034400c071407194080da5080d00c8001d1001c485100008031142d00310344204001001031406510031050810001c1c0001251420000c0e07031320882c0c01c5081d04038041200b60961a50460400c2c065a9100c0024a080030301e1001c10394509860b8040c3d0b1515003600d640108011424000681107c4094002d2440440d141c2e90349041c014084d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 140696232 1250 140694982 140694989
    0xb07200628030c05030703020a09030c06021b0a060f0e0609090708040501060b0319020a0903080307091403031e0c010605270702060405070b0c01060f120c0603290f090702010501 78
    0x1d19208035003482806030184641006140d2100750566645610542c041e60140b00604c040168503040403000880c404035080203058ac0d54018602c800c800f542070b0701041c5000c1805e92117116508002c110b6147d04c00c0313000b170000700c1ea450b011440174001b901040b02030143e90f8280d540030207408200034500da4466180381c4128003510090100903620302071035200303100c140c4010070004001200c1a6440543e60000d0030b9074504d030300d095808141e807070700c0761110f542080e2510000100b212504003c944050900c28490901c12805507140c405402c130b422004a51748181d903049428007107100740160f1020f41c080c100600c00903140803160403440350940d0000c030745015011103c80416000c11880380c400070b00580f01da42d0280003889a035084c6202122681c1110230b1424640d03403a4003010401c074158000410080c00c0345241c003d1116600e281400341c5115035000f410030146041c41840c40700400c1b80f454900d1076110354950103200c00d40400704841c90f50303580c4d0240d009001e0800f44840158150f00c446c1c1207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 140697482 1250 140696232 140696287
    0x190e07120318050f0105030403210b0a05011701090504021f1809090209040308180304090f0b01020a0b04020d020103090506070903120e010203040b0d06051c03080705040b072006 78
    0x1080300c0c0c0b001100340c0c202640606500055180c080e62400e50007030b00290f4109002e400c1404000604480b65640443d1004030359015070b44500c0d0240082c109081c00401501c42420802050401c206a540100b1014450104103a4a071404103095441e02011007000010500c80d22941540c0741c0350103130200720345d4a001241c001f2034110000b8050107a110709140c2c00d50040c00a801c544540d1400c640504014001700042ea403401c041c59840b0404000400040c501e42c0404a51003010a1610080b038081e004194103640000c81e010740050082c1c4182c1c0d03881070781212480485041c1d03000480041c00d0054006006110b14024840e07070300c1d046414101181d2c840c110f6081001800e070004c0300c0c0d51041c42e11450150b0300c14002803007413000010240030300500f03041c4002601a0303031f6000901d000c1501404286d1500f0410060020700d5440388070603078042c20038140795107040e1a00d55500c8040c825950060140d103208a1404c1c03580114144410030b140c0b0003001746440d039803190014207408041d141d1440700d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 140698732 1250 140697482 140697497
    0x60905090c03060310090201050408160812090904120216090b0306011505070602072d0302010b041a010e0102072402190203030307080c0d050709080f0a0b190e071203 73
    0x6441d084032080740e101d4000500640f0903401c0035000d203005460101412414002d0900022401601c10051512403255144542e141d543c5019140c0b8181749601e60000c144450810002c00642c44030100c0c541c00c02c1d40001115000584980101d06020070010310394003e00d0710f62400112900582c000d8001210210140e40d21079a80c3c07068020340410340185180459400d00118004c6411a806002441d01442140140000b14048040100c202c03014903410003002d81c02c1101410b60910440e04d0021065a040001c440c8100104a28443c0d0500030b86c100541043d00810710f0b442440100d0040060855641102d105007000b200b0030240030b103000d0010300c9194204084446011013000c109500640a1031a5440d0ba030710498842000408d0419441c90401142c6130b10001d030b2041b40d1040300140d4888040b0350504125a0400e852103c1060380360384042002d001141c02180180e400000401d0742e0240040b0741546600a00710b61480c03800280644c0c08002103000940c485d018480f0f00c255500ca0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 140699982 1250 140698732 140698741
    0x9060e06030f1506010c0c030606260106060507121e0f021212040b0919030827100506010e06040906060917030307030504030c05030c010603050c01170c2206090509 72
    0x9030780d0840c3c244820f81222030032010921950044c440c407034510380200010400180c0369180e01040c1d0369154031404a42c80c2040010f5601d014503440c00c450200e0482c000e1000701d2030400d0042c073340e0080b503102810480045500c0326000b40038894040c94072001030440c0303102c1031641901415901890304c2007400760040c3e072604e40340300d1800811107070a409030400c4041c50361155111030610000041c0b08407258800e607100d4621411740da6a4400e000f0703200b907440c40c140703190025254007480e16064400407940c8801d00802c4440348045500c48845160b030900050541e00c880048803807211105103181c00c0200050080f89501e460b811101c2640c1c0c041c0c0300e070409207544200604c00d451421510f05101c2c1c005001190303a45100381c11240e0018028070301405407c82c0c41c2c4400d401d66024a0110308a69583e640070010094148903191040009091075011145060800409a2002400340e05030031800900e50120340352540f0411800e824002074007890644403c00501a6165406903620a805000015 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 140701232 1250 140699982 140700013
    0xc0204060603061a0c01150e160e0603040b060a180204091505031e0a08030114040f0e070509101208030708060307030c0506070609051006051903030f0804060609060e0603 75
    0x21203c8021030400301c0d13009031146691030b0b00300450300342c425525640165612004200307a0005040040c44448090404680c001d41e40f42540f01400c0502070018040185a42c0d20000d0341d40c05604200d694031a0354842001071f200030301c250090a61820303445142c03100300b07603168040c0050301d05210303082142c00c04264803103c40300700512031180e25a00c00035118801c18001c44240c51017004640854240e0904c5603a5080a600f090700700c1c07050181500c03203c007030928050165540095901d0010850b8031300c5000000d440d03904500880b03004201c810b011600d0940c22400101c000d20030124a520380131041e190100c0a58070503102c040000e0b00f040c0c0883d0b0305103404a00003048035070004c4079140f143d00d0711050069681001c5010350b5015680da000e04049101030024000c40d0086480000d031250818080040c02940c22034540c030001300010703050000940205040703550b0348442c200002590385900d0520f01418054000b40401030a03d04006130045820b80b0582c09144100d0540c0d00b030102c4080301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 140702482 1250 140701232 140701241
    0x30e0c0d1106070c05040203010303030b0907030501050604120309050d0602030106080f0601020a06240803031009091220030a0201050610020105040c050f0604030f05060f06030a1205090402190c0204060603 90
    0x140030038014003401c801d90b1502e6001804814825080c09131960b0340e443c0040c041760002d81c4150007181d100c200b0f202c09454054521540483e550030204115410070001c2145402903010305015030043c564603a080c180914080f2000b0b00c0010840d4901c8a030320b203082d10180d007080c441d600100315040b0108000d40c02d0103003054424801030780205030904c0103880d00b20240c07089800400701c6150076000b0002c00242420040040d007404002103507681080c5001041e0b2100a03448031804070701c0c11f040d00d80000c0611206c1030032446546400c040c000071941000d0001d014000d520015803000184210403070b901900418440d000882d0024402d00004200fa42603c1d003c07107004006400c6078a06103c2864550302200004a0260034282402d03283da807000b8181000800c2664254081c1003080070701c03040c4003011070380500300b98080c100300240c590314200034020741d103500e109201d00460150042c0d25540d042e580010002c0120340706a400b0307036a01404c40b50601078141d004909100c1e0100301d89004c0e000307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 140703732 1250 140702482 140702509
    0x5030405030919030203160303020c12030d0c05040e0f10060f05070f140102040f14060a05030103060b1804030c1208010f03020904020607060e030c0d08060d0803130203030a030e0c 79
    0x9907240246010401140ca01510300f84800f8a11400f070100144e141000440c112004092000d0310050031420040e24203d100c20449114892010510b00602d9001c401c1c5c540c001400c4001040400302c1040599180c051600305045442e00700c8200145400c5440d012801500100440c2d0480d0381c41c4d5038210f07010340c01140700101041c0108500b00c00215907080028000d402903440141c0341c80c22407407550aaa20a0307000310078840b818081400380554141c01d144550b0350860300070346044400310f409001c0d4001444003502c190740e5000d25009a42b0b0300c1d00d40000c008461070007854149410302d80500044440304069a00520781203c0c91006409413002d2416540040503070141c3c82d01e158204000814000d10032030308224240720b40b00005d0210302a1400e03100e01e10024540f00c0d0219040c1030300d032a04041900342000245c3d800d00141ea12000761000040780c0003100070766281d0307868030009038045d444600250540300024024840b140e0561040c52542c04440503552102d0075002000401c541181 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 140704982 1250 140703732 140703743
    0x9080a080c031b072604030302010b060901090335030f0a051b160c06080603060a02070803070e041d0303060109080604051203040f0b27060f01050f0d0f0c0305010b01050304 76
    0x900c61018407403c80180258503c1510b0144d17500c0b0124000042e9000107105107000b2800101c2c05204040d0280200c902e002c1c07007a9161420500d52f48002050140341e448003038151250310315590714242d041c207030070403a00c000c941c010141c0142982407114039034800c6503d0000240400c010600d100218011140100c401044110900030780c00910103c51388200d815045280704411100d00007080c0d036101c80001c05154607400918a444800c0c5414024000c0c0b20444a0348100328003c000b07003410007640e81102c0189002e00c1380b6440413000c0703002400388030b445802d10302c00310b00742d107415107000801944150000c1c0c0c0c1e094001c0340d50380c1d13500745d407480e007600c000748950082400301c02080842c0b406542d002e800b50040800030405611098415881524101909503200c0c03e9030071081801c03c146054103150200030f0803241380180700c115031b944040c040c2900c15020700d0044040c80d66846020318105030410760b9491480214502440d00d81610320084074075500340034011a00b507000d078080c0c9200750f4011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 140706232 1250 140704982 140705011
    0x3080415020609070b0307171006090e040f060b0621010501020d020a030c060b011701062c010206040f020111031602040b22051f0e070e03070f0303030e1009080a080c03 74
    0x6100c0040e000103040b00c04001240e00c00110301034111280c40d0041c201d000e00d4103890ae00b45035008180842c0758001541400c030a0b01480300103101740c4c0c40c4404c4640c002e00300003072403201c3c500050411702c41c0c449281d8020410800c0302a028074040c0c1c03150b0484100360201d0756907001e03545042ea120408030340043c0100700e180c1a4500801c0198100e5006810140750258902e2103021410031000c1c42070b08038100040030010f40d02d004e40394040306400041e075417034075503a045560b05000030341d1000c0c002c100410160284904800f164001e40702c804004003000150f0740c69081d00960500300240c000410b0780b103181031410820403030a06284000c81d5240d103160550000480320001005032002030401940c425907014081c0c41e503800300300301c0009450f880b8058012402d091900a1000c100703183c100c0e100e90410b0720100044a030002a4000300c1e98141000b01c1c58070701080c80d660400720003800800c0d1a40c2001140005c101254004004034566525072107955140d06855843c00d000131502002d985685 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 140707482 1250 140706232 140706239
    0x4360c0806010906090b13050303070507140a0f05061b01020301080d090b0c060c0a0e041a01030b04060602190807060e0a0c09050f0a0b0f0414060a0b19030507180308041502060907 79
    0x860003801d0715407000030480c0347c055882d0301192035580052016a5280c0000d0414003041901c840304029041080351119045030802c1003400c41410b0911030b4031301c6200005462400c10041150255848020900864480d03070355902803078a40d030403030b0940c3c1c0000313240c48800309024a2a0302541d034400d200400030700090b600d46040401590100d00d02d4000c0c0400a03104e10295961070003046c0110045030700f01300b180e200c11800902500c442c030090074031660804034140105540042d4041c4403e86095414600c01c0050510356418496500003410580c1080c05e40301280600161032200300b0700ca13299103040140d840803580704941c404c1c0ca05492122020f000f00e80300c40b82c1504a01c00c3c04070001d0141144805980c00181100c01c2d040f040c82486803e03d040100e5440c02c2d210080081c03d04803540b6140141c1180c501d5981401036000c4414140d44001007400c0510600103c9801d229004140d840142c80b420901d1042c0c10074440c1c011460354003d162620380d0302c007241d458018182400203041003400c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 140708732 1250 140707482 140707499
    0xb010311070209090f0109060c080a0c020a0201050f07020910080c0a15080a0e030a09030309080706050304021e102a051c0203090604090b12030f04360c080601090609 73
    0x15003c1100b9204004501c0c80e00175080c410083c8081c031a680c0002c0700a4174002c05001c0420080110120314589600c07011125004900c1c40c17001542480c2c6150f42c0d1036140c0000d92180580d0002a4104002d0030800844500030750058060300d0784603044504081d500010041d41c2c0c40603009203205082e22001d844111400340d010309d42c10002d071000c00314518143d4611a880c40c1c010846980000e08186008c100345900040400040c04030000501103c03800c1100280c018840035000034007986595000003041e62070b444007400171100040c1070000300302c01c41a0007050348401c11400c507201810317181d01c0390340503149145031000c0079441009441d00c903850f03070b42c250303e070b00c1461900c2400c0d40820040140b040c0e40303403802080540940e000019040020310f003485a00100e0113944117050b44200b0030040403180020968049540c1c0100025400d0310362080b0002801d0341e00c3c125200f03508030151040101c145601300520618940d5545d070341d640e407004011503400c20740f80308110200d5642c031030a015102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 140709982 1250 140708732 140708749
    0x5031612030f030b04020703030c2d1b02060408070609090213030b040606030b130b0115090515120f0a0b0d0b07030207020f0303030403030507020f0a0215160f060b03010b0103110702 80
    0x40d2801c1c00540d07134103410301180981e445148200d00107699802c400c124144c11802034400c00621024000c0601114003104541c2d0803102160320900502619070002200180c0c60030b8240c0354040c25080e141c50341c443c025a0788000e0360007400085560f4401c01b04a85406d442034452102003980500f20a920710f07242c0c6204210302034000c0d204107455007804004242c44000d9240a0000307882c01034036500b030b10f0410845032030042c0c02448007600e190010007409036000c0b114105035030084501c0c004207107040f030f8011100d100c0c1d102c2068840d496002006822090021258403e47c40d4034000d00a0400c07074000c2011915134200010546442c0b4004643c4452199000d80001440030300340030340c0c1d8241c03840040d180d50011181140000e4031a41080140c0d5414030944402034100c074020f1000d41444c0c1d00040001a03004006500714002061811200c007107103050b002259004040d44222400d1810140c020380401c6562501075803c2221710003155110b44651164411070800160400806a080000701c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 140711232 1250 140709982 140710007
    0xe030a03050706091202030903010b011107270f0603030e0105070b0c0f0d060b0703031518110405041509240512030408060f0702150103152a090503161203 68
    0xc0e0b580c00d0104001200c0c000a8180c01754141c00940e200c0c0e0f8810304041c203492100d441e0504210007081d00456286000441a0503200001d00b11022017141480940c800c2046840880d045410308890360f0b4203200316844401038902a0361220b03801d2102c4d00040d60607204c2c90349c00800003141200012641218800584407400301c441d0340c503250102101106043d6861038202e1024090000380000c1055003500c1041078400c04d42c80d580880c9441c0000512541404882070f8007540c0d01c40340007100110030790301101d02820000f0410403a103601200660980c00050141c12506d505e08540844d016058007401004801ea0040350090b41d4140f206001800c0c00340030316011144400e010102e0206010f2103130520641d2442c070030112a242c1004000d2a20b12070000c107082c44503c6000500200341482000c1c0007030801d1440104145030500380112000c071300c01c03020302510401c041d80000c1a540c030641c84001c481044045031801e21085101c0e2800e1540740c46070041990304030358200c00280c015140240003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 140712482 1250 140711232 140711243
    0x30c0b0105150a14040b0c0309040e0601030804031b051203070201080702280804030206070b0a0c09060c0b090f031b060f07050715090803040c150809031b07080f010510060e030a030507 81
    0x601b0390340c0d202c0c2074a68020340140c401542000c2a03841640c185889288c905034030a000a103000e514503242e80880d4482e9002c00340c8080400300703030b40b101c2c000c44048010051802400010700d504909080703a480360400541240010400408108420700c0010b03170098801d0940e040801d0464103981d84d0070f81c00b0841d54100c80c03140d002d000010241e80c42c9005480a240581d00b88034036460901140401c4621703044c4031009010350300500348140e651085109448542c428082c1080340c84201c040d0307203050148091540944400074080315561480491114003400c400210740007500c0d01e4039480b825500c200c138000c000072030522446000c01c401e400030000507c2c1d480700010701e13098252154021680121800d50710b5403c082d000700501c0ea540c202c1007001380da4510f0001c42030f0421500c07854480c03007003820000c0310b21586460454414014095007000b03060300002c075182c0e031000c030100d02c1c040c2000b1118071100e46e4031000001021400b403280c41d400c1110050180010031910f960a85c0c0039005500240c07003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 140713732 1250 140712482 140712487
    0x5011803060f021b0a050d08060d050a050c040f0b06030f040305042c0109020a120b1302160b0601050c101e090302010906180c030f0519030c0b0105150a14 68
    0x1c00c00d01d1040b42258900c0c41c002699a644c2046000d1407003d003001001516070052080b50041100455403501c0c2903040d14004009486500014107943d0003040c000c1c000c3c1c001e00c1c600f00d0400100140e0103003452400d403010300800c20020140ea007110040500650403400c01c20000c0c007801c40f000c404a5019201e0f04002d81001d440d140c07004500b14581c585200c0b0704800c9040e99810940080719180101042c0d5401d6103003014803400103158104114400c01c1c1e01d0313280c01842c01540d681040c4c1d07001c01c003d20030046480c0c0303598a06008078246d00340000c0c1c800010f0000400da003075100350100e07642c480105005081420000c00918002c04107031940c45004890f880c4142c0c3c5101c524010024140d020754000702e0f0002c2c070b0341421001c032100110f4030b00040244000b100000340c0c0c1000250210f03900204504942181800d01904083c41040c2c0e480c0111018000c0d0010140c00582051415001d070010410b282e032030344140880c4801c01804200d58481c02e1002400851066411100000700c2448450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 140714982 1250 140713732 140713739
    0x30f0403022a1806030d12112703010209060711010306030f03050c0f06010503100e070b041203030501080d0c0b040c0302040f021c020924041a0705060f040507050118 73
    0x1203030880c0000c1d0601e05020407890030841c518109000101618030349140700210304100340069602c10407010380360180700000c030b0187d03802c5080d50f200001c5800920302c1c5c0ba0b41c40c20300c004000080194212140c03142c1901ca100c00300c50382814826207245400141c42c1c20720300007058880d103018904a0210504240d2641404400110405d00c4a00c0c414880c4d01e40130b031210b0540304810705000d195201404c140d0b1010004200340d90307002a00d4511032407048030000d4a40010f011140c140f28054204c2409070f000007500150b9885481441da602e14000c0d81c003003100b0b9880320402902ea08101d00c02c076000500000841d008a00c1615896070401c1c0304143c09490140d89502050548408210300040c080d80420002c003c00b0001c52001802900250118500140440061011500345016807003030500b0650b80d000c54004101210042c113540303001c582c4282040d800010069200403401c440f28020000810b4000114002e175030300465100700034000c00c6043c1070046403400b0710610b40164843c0e0071403000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 140716232 1250 140714982 140715013
    0x10e0304090b0306060d2301150b12091b1e09070e040b030c0d0602030c04180504020f0402180f01020114010f150f05030a0b060c1009060b040b0105030f040302 70
    0x1040140800500802c004851008060401000408041c0580300300c240b60000110740700a04003041c061803440709035a00d85400720305d00408100c1007113585404c243c1800300741c143d8408040c000b40c40604030141c4565488102180c1c03030b0180b02890440128042000444503c1c040d10703071032603d03940144840648100e101c005521010251000404540240120011810306004030120300d0002d800803e004da020001094040041c140050141540803003c280c00510410407180208403000001c0c1c070b010401e96000c40180801d07241248031355188000c864207818140240c48088024603003940c07047d80c41c00c040c050901d5004080d641155652444450b46405040d07542d0301a04100700b03811091804c04807101d0100c002c19411000340140240c203000441d50110441750b008400c00c0c00400d4081c6034034003054450254a607292011300070281a8a94040d07240e22a681207405510b0034010b644107641032104803421403070701da030010720100700203201000c030303049107603001840391044490466010940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 140717482 1250 140716232 140716237
    0x204021b030d0e07081b0d050a02030a05030c33070e0a120b07020102030907030609021507030e09010b0a09060c02061e19030216020907020f0f03070507080a0c0314010e03 75
    0x150b6220a9498aa01c515034038204000405030824100501e06241c1c068a0802400c80c2c03e030109219080764542e8100f000000c1c040740307180c035501a0484e100c0702a5894643d44030b030450085000288101c5210220740d5108108004822f202c100b1a42401d296030f030300c0c00205000080803070f000d0281c0111002d0880e21200d504034020880482103c1502d5000e00d0403261110014214404681c01442405004d5402107040c008996210b80001220782c40f610102d1035040003516511880d043c04103d000501d50014910300540004803035489050380c07200c000c4503482c0a807050640004582420511016000d4580404618002041141040c078080305401800b5000110800e0b002000300c1c0c1c0c1c3c00552841180d56090100324241941004440c044510140990300c4000e4802c10300a808244010700a2008210300a801c00540740c6107000f0344043e82d41c0c0e03405004202c4451284d0703130001940c01c6001c150a1040366012681148031440d42d2143d0b00440c01442e504001556202285040c04004000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 140718732 1250 140717482 140717497
    0x15031103010b072f0d050124090c08090d1d0301090f12030b0306040f020f0a0303020606031e0712140a051006050603041101080709081b28030204021b03 67
    0x44240e03a03500286403800d850a09458407014482001c00d1001d1144100761544c004035605441402c1d851046040481c00b42421280b011482c071103220030103070780e0302140b40b100d030a40343c14074000d001d00251000e003200c12600c201d44200c0190407a00040c45c841c2d10507403a090404504901511070301025000283c00c440c40348008607206018001c0c01810040c20365504d0b800c00015080401400b0107003400300361680f4000340010035541c204030305081155959040c2c152550f901030b101803102a22483e002c0d40d142c1054400e58428480c0300168910041581407000380c0c42100d4000d0910381e481d01c2c002660074007125408440345803907418401610f10342001402c084601900003031546000075000c400403910b2a4000d540100b40410821000c18011044001690028030300320900340d80f8544102c2d120f4007560002d145a018407080300c0d0700d07249880c0c41015141c0382210001da08015400340502c19803c1012410310446050302c040026107081d41c05480001c1110000b4031090010040440c2103621400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 140719982 1250 140718732 140718749
    0xb0f090108030403140f1f0f14090f0109030903020f0607021002070e060604080303040210090f0b0309120a02070b090301021c020c010c050a02100e010e011404051b0a1503110301 78
    0x6010028000551035261145c90031201901c440c0c032174400ea071a110200d00c000b00d648103c0d620300403160030109034441a031076446140c04000032813003c10f1420a4086c03c0d21401d00314030409458064030181841010340481d490346592a2140c070755402c1c02900030b110b0a4166004505024050240c0c84509071385010128940c0905200b6050016030544000064a050300a80d0144070504c00800000212908260111528a4800020074080301d01000941000c00000401440001d13400c26010156002c0c5000f40c05481c0402c080c868000064080c0018130702c0141d100380c8003006400c945e400140007896000c2d0015251410310614540701c91601030034000e03215400540b445a00b007007841340c0d5107000528600b1381d207856400c8034025944d85070301032240041656140081d122190035805103001110302c0b00280902907054042e00342c5042c048405449500a101000e140d03c190100104070f40301d4028070280c10a4100048821088006001c400c05d16607a0640c8811341e0391144c02031402013030303100d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 140721232 1250 140719982 140719987
    0x11070308070804020112021b0316261204080903160509060405010803090f0303070f030e0a0f150c03170103050601150806060301060e0a09020d0902041a030c040b0f09010803 76
    0x92900400e18803000740031604100041c801d00005070380c0400c016a140704104009031f25001034103040d98200c807404075001810700c80010518245244001c04494240c0607082c107481558040c0ca1421a4202d078640e14611a42c1c100003603804080e2404255412038006e1005605002d07862000c01d10b088005519801d048602e02d904008a18041180316844030060702c007804203514109040d0303500e0040c504180c3c800d000a194880e00c42e1030802c11364004c0382d081003010b46140718900307015100c850007844a81c00b5107003503031001c24010704454a460454080d0b90300b120b60b00d98845001c4407401c80b5000120100041191503c1c2c0a218204040b4041c0d030041002d0120307035151804034800d5101e40d074000720071b21240000300034544d560401070703904480b002d00380820a0b082090014102c0c42190f0001c0c4589880401e00308040c0c2001c1d444500c08610945080081180c08495619104004500c4a505a001031112402c9080a401c9000d072403102070704801c600c4e02c0c0c1714005550038009801404150303001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 140722482 1250 140721232 140721247
    0x50601050a090b1806030a0206070c050f0109061704030e060c060132130e031c0b011b0f0c150c1b0312030908040f03050c0f010f0e041503050111 64
    0xe011100300418488104000c207403081c3c0301284103440100006140101400e0024096071000c3c0a4803544a90080003d9a0b84c05a0b1501811043c0e031402468003500e81c82d900351039594015a526001e49000ea124228a4100c000103401841c1c0010011000c00028244c10381c500d803604005040d820020f03201034001c540c100340d40ca05511210701440040030f80c41600e01403011407507a80c00c0920450030344a840c020f207c880030000280909030b085481c0c622000070100c1e50b240034003c0040242604903000d01481240400440c0c3d9005043e5a10801b440400c040c000000c203090f50104190744550000341c0b1003540d800c44000962009103624003c2018400c41c601001480748210303100e80d2040b12080c0605080d500c0310240f000481c40c100c02410754030203941701440884001d0350000c105002082c0640343e02d91506e40d0b110708100b030009015104036600040298000d003079684991000e60340b500c0b0882d280d141040f000d0114a4454a800301c001100840407039801e000c1c024000900302d6540f9580e5a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 140723732 1250 140722482 140722489
    0x109060603030c02030129130b1807110a1e03021002030a1508030304030c08030c040504060b0a0215090d0302090a05030a11090c04080d0324080f07090e1507020307060905060105 78
    0x641030041d40b46841114054000c0ea1f85801d4003a240031003a2080041e46240558084c000e214041009038000c0c10358025020b12841141020300c51800f41d66a10014801e01046940e5806054030052001500300da185240909010710001d5460180c8101c0b03040d85009180c0c2002c980c0140d441e90000c03a190a5000701001d2403d02c2c81d0020280b40000f1451880c25450041c907a03820120001c00c42d460020225180c0e0320800e0580b409054010410045c06558440d1108180d018441c003501500404102d421904031001089108100300000703050812a0701743c04030025844856030b10b41c401c00160001c9100d450030454000458461310900c0e000203411810005820b2004020800d00c3c8010030040c4140c0402140a00c6035071411704011480c0640054402c0300c00119514061040300070403800122142c000512015503030142c13003520f40950319580301809a80c1041c0003604d055010300d007a015500c2d02800c02c568010030030310540c0c2c200039180e5125001c1c3d0780c909206a030242d1011006104030314 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 140724982 1250 140723732 140723741
    0x903121a0409030f0e01090308120c040f0801470301020c0709021308030a0f03050406020c0303040f060506010908060609101503060303030b01030501240e12010515030d05040b0c0109060603030c020301 88
    0x1082420500c0d4814510b98511f42a4812b028070b2001807a581c1d400702c2c455000142c10f490240c0482d101c3e445001c1d4458000c02d008201051503180100c03060010076480c6d880c6005034600001d08500c4c001c1544c00c5000c3d01c601d01040342c41c0200c1e015035007081410442441445900003400300075078090380e6005007101494101d007040e040705032560020000045116001060342095110900700801c030b5a41d9402d020000f1300561043e0112030000204000070014103102000d682407080c1010000340d140d4100440301400540502201034bc000004500b440c90104c450b19841f034040889220015211038410708542100c2c9060008640c03600c10600415400d4000c0070003100003840c1c00c0181e0362410302c810700010001c07199040d0647d202400c101203503119024a10b00c034400a0030000140540d621400d008000460320100c906180c0381c1d071184070b440c01041c082480001c1c3c1d41c44c0390a281c100340700719526a00c01040d80d81c01d50350b1466000300140b841c1c000c0c9001503002e80c440c0008175030640145030948 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 140726232 1250 140724982 140725007
    0x30d0c1e170a0c0504030c06021f0e03040303140d090302060108100c090909020d06020a120f06050f100306080a12080a09030203040915052e02010903121a0409030f 72
    0xe038100500c0c109030702400219520001c90000850356152807401070b101803040b50801361070318002060100358987c00085414050200300c60a0702030810244490045841c9a0320204180e00100070820110348a400d03c0d01c3c1414011150918102c00400f000d01200c1000380b08030056000300c030042042d00c40900083c194070302c60310014414050346800007051501079009580f06143e4880a2130155101e0000b0703400c81030342c030a80031551101c0f85030003e840d030812012081c8a00b070820300303904100f044138061003084a17409407414065240142c1005040d82061000004150366510002204042003040300a0540280183c0904c4800c15500030308000d0014034041030380f4200010b180c0087d900104440c1258482c200c005550746000041001d02e6010703038441caa201203030600c0190444051180d1151050380748040c4241c0e4014400709070b098840d10a0003a020032294070b000d00c940401a0000049540d800c024544480d07582c40c0050100e5004410076800140084105c0420540002c1614041d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 140727482 1250 140726232 140726237
    0x1090201021b0d02010f051e0d0c050c0c040b03030c01050a0515120c060d0e01090c08190305070b040c150f030509120315030304121a0705070f0204050405030d0c1e 72
    0xb600c20706010400000840100034100080714220b148410300c40d03030a840b109000c0c00f00800c0120f04010006c24141c000da41030061541c600740e07240281601072411200813038040006011703170307151000401006200e08003905816000c100043c1011300d00030306c9000d100d102c084400050904146041640002079100c105000e09103080100c01887e0700040c116180d4901100e04960707408001641380c018015502c502d00365907080074602400c1013014031001c0180d445034800c0f114401d00d08500d03518082503104021300416002c00000b000b268030407410382d510900402801141d0385e0b440004c0020070481c243c3d8580054070042082c42c166034035026554101c0f010100030255420280604400c502c0702400511902811000500c0540c50a2095500a0410050b05154000b19091003455400d05205105140b20752100181c2070a00070300c16203100076041a418030382011380d5400c0c0001001c2c09003083d1207c4c0300a01c2420010b00c01c90003404003c500c03542d40c90048450518980000c0118016a0000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 140728732 1250 140727482 140727523
    0xf01020a030f09110409060209030a030903021201020306010f0c080405061606050903031b0d1d160e042a0506030a06031a09060609040c0506030c180f101d030a050109020102 76
    0x204d400214892000d07103045030001204800c038600280244241411290503004c0d0403001401d05820002c0207044a0080d10320100407024038041c5c60803403000300e0b011404a4661054244c0444c8244440c446291240f0040c81c5815101c2000940b00e400c07030203082c650306142040c444104a203070301a040d0858400d10003141182000c339580b84a000481869109400b00840e03144200301c1e503a0000c110b45220f41c1d0b8845410310802c42c0c0385444201c0740d41903003412a40d0400001d90070142ca80c1c014492601702ea841d9140c004a1020750031054546640250060143c036404521903964000a50164100c404000b41c200d207940340201e0102400107036603680b890340740c0400115010104269038880c0c3c0450b0070a00b540d50f80d1170501100205500b08a0300300078088100031500a0002c024660030003451501c3c00441100010021030174040c00405400507008a84120018003511002c0314034282d81d400f5032812180300c8c2c007003440c11a030590151001ea45442d800c1041d940c041c41820b03607504070140c9041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 140729982 1250 140728732 140728751
    0x117010b09040803180106050607110a080d02030913020c0d030204180506130203060d080d09021509010909050c0702180703050f1311120102030403020f0f0106030b0a1802030f01020a030f 82
    0x200328000103203c0440e007100101010300905e000c1d40141c1c003231710000306041e8498a850400d12483c03032039082000d010b6151514041542000041c2c002c0d100c0003150700851405030840280800710b161035a890509540030b001d2145c44803001c0c0a42c8d05d10f00460303900162a07070301d003403117207080000b64034484010075151506012054a0307003103540d280e202d112140580d40b0b890b00e00c0416001401c080016007503003000b003a0705c50b90041541190343d07034070300072542c004400583e2007070005288112034000d4042803140c10100309018454016960040c6e80384111803c0100540100ea070101c21800301e58002042481003060450705489010340104101186038890301d454403081080b4180c403200a00800c030b58040c018029518507242c41d8110030004e00030f41d224241403602035070b101403489040034607004102c040400c541d03052181c0c4e42166006074a00c0c90507150a0300410041421400c18420030b802c1040520160310204103400e8024102400141e070b0b1a0407540c0101224100035145114a042c0000c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 140731232 1250 140729982 140729993
    0x17070e01050d0c0203040f0e1b2b110708070519080a03050408040f0308070303112508130b0307030b0303040e040201030f0603021e010305090d09120f0b0117010b0904 73
    0x211000e9610b6200001d040e812000144d14500503544200b0030030200003004590140096001c500820291201e82d4a80c0345000310520580101e640c44400104e0710484100c0442540a240d844555400400103850080294060107980a03403003d6034150000120441082410440c08030100c0b824000c1c80c2d450481c0d40d442c400544500d140000c01c042d1608045024030415030304480041c01c1c04081c10b19031568a1404840310340000d0810380100c1e01c0e040e10844840101c06c00c482e0b200304219501c081780000d10818244c00b01542c03505403803010080c0083c812101600c0b0078880500052501c1e01c4c0c607483c00740801003e4500749107000d4060381050204000a00018040f550081c1d42402c0105448080202003402001c6a0780069441604006200c00c81b015000090f110180c080e60300307101c3d943e29012442c1d500c081070309400001980c00c110401041d515900f101440601c680094024481e0544584c129400e083e0084105142805030010303040009104034503144078142c078000c0b03080c60181c80d00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 140732482 1250 140731232 140731237
    0xc06200703050c130b130902040f05010315020703030b120c121c0e0418060b0103060905011a070f0503120f061009090e0f01020d05010e0c030c0301180605040c17070e0105 75
    0x441d8019803134100451006070041e0000300c0f841740050030a0080700309070722158000d8400410268000c61070003409035510380742c6001e03650689400884962203141c0000301200294840d5009038201940d801091120341c0e699111080d1034030005000f0b01c1035800900401c011800600b460b1002603115140705080f0407801822100300403101d0810107510341510021501030099040c40103605c484002d180b4041000faa442612a15000e99041005646a1002c5030445000303001e42454800100b001e00310b803800c0b0f40f00070080c040c8a610342540590351a503032140745030888a10741421411120812038207000d01001c6983c04107044130b880803907800382580600100c00c507004414641d9111503001c0b803580410443d1020894200c1c008550340c00010381d0003402003000b0300031440c3c21240c2e0b6000c181100f0313540058034018860030b14507a24691905004a074589581c0c4911200140c031118005002e0f5640d01c20b00b600300a00740c80700414101d2115500081900003001e032014400c44d020419100e99000c001e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 140733732 1250 140732482 140732503
    0x11d040305070f0210020a0312020723071a03010602010c0f053103080910140a0c0f080d02030603060601050c07290406050d0c0206070e010e04090c0620070305 70
    0x3880e6603280c445040002c2c0f1406940342c083d4000c0005070b40612007a90004080100c940203a03501601c4401f6200881e040c1e00c18813034040c2c081d401101c00c070101003c0006002ca01c800d441c2c0b04440540d49d07251890b02540049403001c100c00b410110040204540a0055200d208110b1411a0400018400c05062070143d01400300c10b201d4544c0f02c000d44605211500098030201240c9205510ba41c1e1038280903607444215503600641a12204514a030300079a41f6002d500c2c541540c260400d0a40c00c022516a00e0605c015128000381e20b1004003c900c0309801800b9041070b0303410140e030340e10f004018545041c2000e000907040000030040054813001c007160103016175010740c07108914104250019261402c81c0800200c510030005000688641c100e4024940d00d51314030f000f4003047c07200b0ad85c10f030380314502140c10b440442c1c1114602c00c030562060082d0392050038024000119076241d0385070000d01145a400410210702c107070850380c4070429460300c04480c0050b200b0040490170b05564641c5d484481504 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 140734982 1250 140733732 140733737
    0xe030f16050a05010f020901030b0907052212030f031d03090d02010e060d0b01020f030a14030702010f0c030507030e030306030703080a02100c090302090f060a0302190504060902070b011d0403 84
    0x10a10401c00800744401810180c12400034000319507001c81c5007000354800a841e9000c81c3c684481c071400c50410400d0907102d0545503c80508001d585041040540c40d02c20b00d10504101c102c00c04215070307114000c6100043d00079943d0111000c00800042c04450f059859003000845059075541e02242c00004c46082c810706a5034a62501c00ea03200594200841c3c1d40c4039607125802103000405020207900503108140240c0c2280c050700c81c20400c080c0c032449800340a400166080b81340b4000764503c1002590080c000e40f00009001c0c9441000c981182c24610307403400003d0305c130828046625454015802e021240c00091861401c000b800607a49408500c00206103800c082180b01da0315000b40042c0b000b6035411107080c0324407002c511004002042d1400128440d06015020800b031410b039401441c81a90003404811350141035408105014854040d00c08282e0100700c0d0100307a5407124050b100040807184400b6850745010301d4800b0140c001600040d803060072507103022054005d1800310541003034050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 140736232 1250 140734982 140735017
    0x7020a031e060f02030603010b0108090616140c0c150f09100e060307080f0a09020d030e030f0f0c100305040f0f0c0302040e030304050c0f13051005040504080d0e030f 73
    0x318121850907040c0d00d0141c903061920031000c0d55140282c004620551048000301b00c0400114015240c0c144103030381810141e8058400100d00301090814001120303d0b60502002450001d145600142c0c41420207218035006070345026882d00f000c2c54000d40100501810347e0405442602e01002405005262031040700c03c0341c6101c954501445000300b640d08080d0241d55039140408002d400350506a54400360242c2e20000100d0400c40f0303100e01c204199000b0424040d411481c1c074220b59031811586040e605015030403904c002c0200c100034528281001030007800c2501140f00c100a035201c2010f41550515007420104400030350350000b80075440360300c0030005640708031a081044081d02140c0001f500f051401500c240d40c3c0c200040550311940c403510440314004802c1c010300c0f9000b202500b0140d00081110703524041068640c110a5002080c50b148100b9140d4460000b01070f01c0c426034003030310742203800200300300b01084a004980f20f9200b1741004502c3c0c028227003e1452030784a6002d4040840d20350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 140737482 1250 140736232 140736263
    0x307050706020315040603140c010c080315010215011205060915010608090109020405010905010e130c0b0c0a0b010b09030d090609090e10090312060f030807030302030702160306051b07020a03 84
    0x31041343d80700805015008010071070301c91030051f982e07004000c0c00480038400d25401c000607602c18010703420402e074031218450441d150b25500300d00e40c3e0302141259065001d2424085491020892807078020b041a03440c24444103400d0070f2403400c10f50060180c001d035400000085440e2140101000e0440d18a4034100045581c2e00003128010308407480029441418040001052007041d00103e059031613a407502401500d810341000f0002685a2000309501c1045c44200850740710440a48207d1082070b094803901066581e50026002098110701d100100c00300756080345080c10401c00c0d01c00c1e0000e09000303064904181016001d0f601c2c0d440340104494680c41004000d0300d091200f03c040702c07200c02041c00409203a14000c3c05211640c040840c0b8545050800551130b88503010b0300080341d8101e203138240f400b0300d10380741140a075000900803015485244100c01c01603504020704c00c0158081c0f00c00084905083c0c0c404031401a070014034584040080c4208030141c2c0c0c4004202040302d5000007861200c590 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 140738732 1250 140737482 140737501
    0x150f0501180510020a080a09060809010902091f030203030403060e0618061603111306030b01030216060e0a08031503150702100e010b060a05040302041b0801210209070f110303070507060203 83
    0x21500c10062208401242c4201a5604511404161541070700d802100ba0703200802f00d4221800c1900c00380d0b100c1022408a80c0e200f042000c9081e01d145888103c580c80350702c0b03802007842d40c1e1060f40101c401076070383c0798468021801440099000107d15200d450003404482c0c141d565810090400700404842c1a00d84001ea4045d601420302e401c0f1032451662200365122010709070200341d05c292400310b4200070204040b903129108440b81c000e901c82808024180c651142c01c001d00850440030f440c2c1c800e0a02a07804071b4100ea0145228100c03940d4066480c5107403009160500541c140d14014200c1e08000303010302d81c1d8001c14900f8640610a8001900085120750603001d803282c0e110b195000280002c403810307683d5002c4010019030b8000d032010f0041c030500002103002d11010b5072102000840d860010b1142038a00001c1003040c034442d80c081d103000304450b00092040d50041d0b40c0607001c00c4400d0806800c031604194102e8251144e840658190300d84038102420074450701d10000c04081d03001001038040030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 140739982 1250 140738732 140738743
    0x150b030f0717010303020105070810080d0e042007140105150613210317060609060a1101050709090b010f1b06060f032915040b0310150f050118051002 66
    0x80b000c415101075540c0d6414003034000e2030150750410000300d500000500581118410078129407504006007941c10180004580c51190800d05c03551081d21341d1142640315501454910010502901d01c44d520101490a6a0340c60f00a548d090401e034100700c10401e04200003442001559001e0340c0d15507a4800e14442c2a15008403500089044800b2680701c03c0448030301d11034005807074400e44030711001c45107940e2140b4000300101c8086e98060420481107c1e1030511030080c100001c0c0c24100408041003038411075080da1000c0b54480002425084204030038546030240e8100c1c14405e0030100d6200b0420320000303020b07050040000c808040c0c005640300800100d50700260007070100159813078455490745440c07044603d000001b0080ea030111088010444081d0359645d003e000300c828800d603000c008005120140203401c041507810b005102c01e189072540e0074001e4070b103480080c40b1071040450500c0140d032154000b9030440341c1001190481603d403030303540184520544500700c0741a80144401c81c0203e01e0314 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 140741232 1250 140739982 140740007
    0x70309060608010b13090209130302030403120201050712090308071d03060411010f02120a0c1502070507051518060d06120503040501080609040f060e1c050d150b030f07 74
    0x40d0700d0450006400e03070041d841400131240480c0c0c1d083c41390f604a20300360306603040c090020398040c5107400429009d400d58211824050310030b00507a4207140d500e0311050f1054402d280c0f0040580d44500800c05220f030321900c21500000042c1041000002a0301c8c003c0c40b100c0000c00600502508034008148000070100c10042d04100600310350f120324040c17511415a4400c1d8111038040380b50400c0c6610714a0010491184555040429078140040c030710049920040191041c6c0b030104a0200d04030907800940010f001140c0207500800e0005d00c0c1c00144480401031100a0030a21818082e2495034090150013082c40d50040f5091600c41109921110007000280d01c081c071040411104402002404405401207800c2601c65031281d580b48024400c640e4002c6130000c09255403600c1103000150180e11004040546504444003407138500403200e12040390b4400000490710126010754016064084c404a14801c1121381c0c08051501d4035070100e500000d420f0284910081d800181018422020807401c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 140742482 1250 140741232 140741243
    0xc1903030b13020d0e06061309020d1a060102070e06030d0c020609030106121110050a03090507080303010f030605060301090c0303050703050d093e01031a0301060b1201140108010b03070309 83
    0x20221242d0042000350300402120b0101030070180c030350300c0c0e204011a8291050201a00c0e0191504142ca03d800090a01c030900700da001c50318400b00d1740400e4000c50124802e02941c1121103a0b8140400064036010f17481c1d21170801c41c2155400c01015440125182c100c030201402d006000740c4081c80059070900803070340741c15059807070000300091a00448070000409401040454183d0f9600303802c0c010781c401103074584000304500b0459090a10b200b50321200001e40070340c00b030740c0210b620340e09078a06641c420382c040707524003a10480602c18070006101d00d0380c1241e0200c00030060700030740d82e0303c54820701034034130018042c082c011500c0401c1c58010f030201d417101d180300002000074600c186041c44c03c0213540c10010341f0240c2d45c500842c043c6003585100d1a801c00700d4504d900302c4000c0100044000d00854030710352400b001000030520058a09000740d10141050300d400c0ba48901c264540c1d0101101c050703000e00c01c10b04403a840c0240c0f690f040216a810348252050703080c3c0d240d03201d202c2500a0200e1000c000c0c0b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 140743732 1250 140742482 140742499
    0x80f251106070309230a031b051005160306030f1412030c0d0e03092404170a030e03070b040b13051e15210915011d0106050c1903030b 59
    0x1a203585a401019454421204142e40a002c0c9241c404c5e0b0485c0d150101825500c00d03a4981d000c40c1c000c1c03440c20400c0c1217600c460000c80102d40e40d900e0a01050f8042d02042e19240c00600a0f160307820400c2441c0d1040c1440d0802c041461526626500d50411101401424210900e0310390101d00f4011104d6005d402c2e8a040da507420500007252490307200d9010000c1e513034540300501e0003400d004022550400c034000e08640c0001805055688208001100210406002c000002e50700b0724a0081403044030582c80500210304086c1000b800020741c42031210301c25041143d00f48502c514200c25103081d9098903601581f9942604000c6440105641003580e0148a901d51001280742503520248205401c4d5540043c013880d800c060201030040201c0500c0c1e1840c8022014901140c6d15041e03540305100004032594072040c03c1501854200a8100540344144a400030a010380e4007000d0034010562464124070341440c4100c6a500e960040c12200e0044402c0c3d000c680a02d0712a82001405100c020060407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 140744982 1250 140743732 140743741
    0x90b0a020102040806040b0f16080a0f0b0a03060b0a09050103150513020a08010c0e060307020c06070503160c17060c09010e181503010e07080c0105160f1101080f251106 74
    0x603401c0c0c3c0f080702c3c6020740f080d00781d00060300044d04c200303074000c00ea440751540c00c503c2d103402c840320000e0550174030200b003a04d54a13701d00c0203540d1108540402140100c100052140d261010b20050502c2d58014401c00c0e030070880100f0005211149110400e509018002110b4640c0401c078080780502d01d174081d51001d116603002c500c100065120000e141035546a00c841c0091001c02e22242d400704840d1680540c07c0010201306c2410150b00806089100707800f62883c212400b031000000050400007a500c8500c4140184600b4446540a20f02003101100034042c9240c14404201e4610a07982024108000c065400c078841d203403400c0d80707081662611004500c91502c1c0303001c8240c017a045030b403480c420f40c00c00401d682883c002080880036142c900700908507960341c0c130006507101d60140d050300c00041901c007004000324000e403225414082c4030b1084005070b03203001c034001080b045000d00354140d041e0054081c00744c00d8036010494480d013858404004000d048400c0207560b00e0561032541140c0340200001c11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 140746232 1250 140744982 140744993
    0x9020a03060b09090c0a092409092006041203050d0507121d07031205040b130303080c0c0709050601110609060103030f1d011419030903030b04090201090b0a02010204080604 76
    0x1442c4807030161012946503484100c8140d440441260301c0d82c102c280c6600500a105843e00301c103d10502c903040c0c0312850105182d60411401b0a9448400c00c0c40d51006480c007001b0220052010ba045d210342c54000b0042c140d030016000b4821071182c40096403800000f1000c140c0203005450a44060410400840c80c14090140030025800074545a061400948560791003080e401c0a0401c0000d50040601900315074600b1403905541403100103006040c080090f40846100c000c040038040c650540c40c6081c40c608c0c001d1b24440f80540094601c51040c1700340350110711700241407421980031480106240d1503d40c010303602040320f10441c5545000f0300003040b00e4500c001600e281240d10a0341d41101a190244041303428603a400d042d0091182501230045641d0300c01d0034070480810600d162036240081041d000940d00d85403215940200e9120030079202450b806114a0500235001e5805020300005940000c100c08120b0150f84540328022600106c502d10035070546d4098140401251614140741c10035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 140747482 1250 140746232 140746241
    0x160b1509010f1406090a260f0d02030306041a090103080409110901050712032306031c08010e041502070302010b030106050613050d060e0d0c1106091507061b0f020f0606090402060d09020a0306 84
    0xa406141c4a5858690044d4230000b6004040c40469405542075444400412001c0c105506003422001140710802e0f059650300c1070800e0095114185c031303039034031458175000c0b0303059841d01c3d510840b0070341003400801800c2e6003180866103059400300c100100815428400c4d4000c1c804900c51000c1c0c4000e981c4a1110800c40105c2c06004413805c40844002150701c8045515043c1c2500da000c0000b00716000404c00d10b000040540d421502c10840446007551080b01e4004036000341e507045d001030703449803182400c0781000e1107528041c4c403054450501e402031a42c80200c6103003051107201d0180d01c14561302400e0207080d60044031200e950000356400c03200b034000010326800f00c0810681d240b960061800d107052800340f0841d0311021001c1e2001004038108040d0750000e400040007603076515210642035284549074203140c10300040e00d444a01008a81810080c40e000380307041d240301c01c0c0d884101809200c1d5a04a4040d0388243d044440e03994582c1d0b022444005801c280e03800035041a101d280110400846800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 140748732 1250 140747482 140747549
    0x70b1803060a0207021c0303020c0102070303020a0e032d0c030703050a020306100e040308070e0a06090f0e09060c030402030718020307080f0f010308160b1509010f1406090a 76
    0x440300d00e511030480001c101e1190150095100c200088000d40614001c0031402c5200c7c080c0c140103042050307007810b190076640a0741c021000607a0024085c1c1e01241c00013404080080d00758002c00e060014207000e4071401d40101000410403da181604404800400c0880e41c07440c0058180d40e0495928548581d03602103449049129004850006102500f101424030803191a20b60003419611952420358101402030580310810541c18130b40101516035003010001040c0c03540e0b66210917845c1081c0c030800c151050b0480a0b4644110043c8100c005c1c0c00161190045290104ca590382d49442c070020780303000c0e6542e11071201401020172614462400c1d501443c0301d10919210101241c0d5255603c0404a8084504084101d6030800520210f018100542240903000411128403491600c6040040104880d08241d10152130780410b95801c08101c2a4010b03c1d080b452803000e141800d429041c01d140324042c944c0241c2000c034a00303819603a01201040204680e130002c20b00301d00b003003140d400c04000201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 140749982 1250 140748732 140748739
    0x8070905010b0c0d05070305090402032401050705060105041503120f02072103080a060b1c0c0203091c0501060f0b07050d020d140d11031f091814070b18 67
    0x40000030403800300c000700d4014005100141a200030004e1003035556070410300c3c040c0d04201040c0520f0105441d00d1000314018200103c4404488141900c00131068001d0030341281082010f02c0304000082d00015490305461003102d021034080703050030701007100d0181c2d548094800050000b0154a160b0410406680b0240d941d090301c1e0301903151501032040c11450040340b00390110b080c4221010910500d0910b421102510300030801c2079441e1089000340e04105c0c1c10515402603c50782d140c14010912035000c6090250001c0c508045031080068401520181c0301c000c030105241742801046420f5021502070907000c001c1508554552a0721130301500000404c40f45845a080940b8a20f40001000c00c0b41a00c1e56907241e203a516401a140c5140c1c10001c140b4203d03c0d150031071410150a410091441a401940107200d030407208054050700e020780380e014001040c98161184075100b2010081c0c0c410310303005200c4400b01c2c140006124980942a44074050318000821fa0b60700240004d00000b001d04400c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 140751232 1250 140749982 140749991
    0x6031014010608330406080d11070f12021003110a0c0b07080f0601050c0102040801020f22050f0d050a050a05030c0d0315140105040806010b091002061618030507080709 74
    0x40b503440c20f43c60140c84c0c0034401d14841542d041512000c11908101d900a000840c000b555400c516150a41e010300400c04a00c01404200d80c601c1c0400008000300b0311243c00342c400a1605200c4240500d52084c06805070303405280705c840a50181e0480e00c42e1142e0b59032029070b6042c410030b00800301c51010004507640f42103140440c582a01c05e220040c012070010000703207442c2d2612801961250702001e18512155024040002c840200f82302800824202c2c0c0f514170b44e180a4284032505540004c2c080c40701030617400006000a0300e59440703200b004036081d0b034000b40f92203640c142149800d6040d100107000c0c5c40341580c003a0030054044050401242844c08407404000070101c1a0241e6040000340419110340310b0042203c000c10301540e940581044c1000b600d080d44070346429003814000d80150510310800501201c5504018240d000381503458400b0340601c0c00c109507883e204d00c140200c520100302501686400043c1b44048100003150f110080b6005c5030f80e124001038a0f5101486185206e606c0c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 140752482 1250 140751232 140751241
    0x6040c090e06060111070e010f1a3a0c0e03011a010804120314150f0901140d0510020403030309020405010f0602100509031603020c0306070e0105090906031014010608 73
    0x403801107081803180c0802405250742c0342c0004440200c1d44007614003082c070940f1400910018000c60700341c0600074080303100045508100c507500f00f0100c90741c030080020350704101c90f032412415404490b0485d10001400b030303003030012541118031f049030f22109402e245181c000c07601d0a5503001080340d881400306500900850300703580c10450300381e10081d09490201e2042d1002078001a8902062641151281800244540e0009030022a00d00c2112854058252800c40c00828905175054846100c0c00b180d40c003820358140582c12511054401440340901000c0c030504040040904c10b0581727003850018110f4071a5500d0030000c0160948800907030103103181c800040760b007419000c0840180c0d40380b60008e001108080c601d00004000051420009000902c2568441400400303e504c40b28066402401808182820541000000391528040c4441e120303030403c82e80d0704030302601c500c00000c6820448030795440004c2414a0060444020020b02e00400f07280200d10101c0381f1070694a0580d90351581c3e40da03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 140753732 1250 140752482 140752499
    0x3021005090705060d020c0105040b04030810140105030a0b13020a08011d01121104060e0a140f061203070813080f03090303030c03180a0c1518060c0201170906040c 72
    0x103a803400d031030b074000501c1481141012401040c81e070700100001441d110003444e40c0c0c1e003154020344003217980790520f00034001803503070140171a5000b00d425101080d041d0320740307001140e0f00c0302405415410322001000154000d0410360105d8000c80010304a148484080c1c45c8c04002580603a0002c40031482c0c007800401c00b80d9550b41d1900c420300103035041115603401c0812080d2120842c40f0111010b07164107488200310303240c90150000522052031102400d0600486020954901d030340c1015039032401030200031450548138130460304540151038540c0200454105039040d44603108010b4801c85e00010b07940d0b0500b0720064004201c490030410760b03088081a04c11152030380720788031106905505c00d00c080b6900f03011103002103030066010194200d02440f221500d03402d0415142d400c1d40c840204400801100b02200e80811190515180c10950030959100141c00320003180038200421160004000459001d946400c0b00d007680381e1219600c81c505803030495a540b07000c450803030700130350001e10001d29040c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 140754982 1250 140753732 140753741
    0x40f020f121e01200310120804050405060409020109060e0d0602040e071106090a02041e09050105091b0102100e0c150918010b03150a0b0c15060d03050d2004080a030210 74
    0x4520b020b00d50341584130442000641000c0d01c0d01c3c2c1d100c480000001081c1c6c0c4001c00f501911445444804e0f20f46140c9800c010403150001e01c007a010758217080030000142e038480c82c0d19083d50039509008900c0500071000c100080c400903c0140031900c0054003003180c2199030483c0d44150440d035680482140071050700d0751143c02c00c0c1c0d03441d01c069115111081c0145000e80200c03580d80f01c0d0304240c1c400c80d0301e083e004070b09541c0b03484c0e015102a5568030a2050400d0f05101800e900000380304001c80308045800000e41e81e4441802004241daa41c0868520442091248d941c480c06c008084004007119a5400d82443e03000006091140c030501700c1c82220100c001e000c0b98121070540501070308582e01d0309800d8041c0b0803000080780c0e000c25041008507103240c403500a4140220401c0007003100c4030028480c5604410040c104610940140310141c0c0020360080484056a44030400410200107007808280f900da4104d83c40004040003040208610b80000380c402c10903400ba034219000c1402c00d051980441c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 140756232 1250 140754982 140755001
    0x30102040e070c02030a08120415050c0a0c0c050901030305030f07020615190503060c04050406050607050c060d1104090c1b0c09090f021207061412040f020f121e01 72
    0x25620a000218003e01400e0030211203400a81035035000161a980c49035035510841080b031900d0482d07000d0000380000c0070300000080745060341c100f0490808401c040b81ea4011031181204011010b031005081210b45026080140360203041403120b561a441e000d0441c0d041101c02a08140c10040083c0c1001d200003580c6024011442030368507141141000c4c031446004409601000c004110750016058404010552041c0310118403d52518245020070054a04076030040b80308070000d10401e03010900109144441c40c004640f416030f10041c488600003e450031629030114a14045070009440803541c00800141110f50344000c120112a44d1101081c0c99151010300f0030200c1540c00d2040c14041e034804440c003070003841c0c40c1c002c0c604d060740040c181c80c210100c081c00310b801c410002c015841c1c000102c0c0508190740c05401d0b0415100d03400c03c07448540003c0c00580181460440042952241c042d4112610b8014010307240d00d031448882da560b502c070000d000b940c1414000c03e8440400e00107101e440c00c00d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 140757482 1250 140756232 140756249
    0x18140d080f040f05071403010e070503070b070f060e0d0f0c11060c070503070803210f1504090b090106030b0106020f1c020c030d09061d0f011413031a0603010204 71
    0x6440d128210048201c004100300c52600031080d240300455000c00c820801080e00c201c01600d41148030083c14290741040b00501c400e1b5000e120f0500040d038000c40d1410640342720f4030845407128a07909004545075107070000034003903615103d044d0310001c0e008182902c0c4c901554880d0b540d0000314160883d9890303c24000503101043c10b0815504911f071031300080ca180c40ba403601701c41444d51100002401c00311540d01c840415400003e504040c404807640001002040841e103039030510300b55600044080d4010082c5541000c0724280c41c0c0a6561903005528558122071000060320b07011400d00d001309454042a588100c1c0040001001403001404011100503035018100c201d404031072010389004900f40c58815401071601c0411251800c200c0d05000b100f140d40c4202c00140752071005094645124441da50100b8148051a1300361262602102032031801e03c0d200030107080d080c1e00d807130f140e0251103d0103401c2c0240e104000144848200441c4440d019605220f1560302c500301003500301e11580c801c5010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 140758732 1250 140757482 140757497
    0x3260103030203031b0417030705060a060e04061503080406030f0605041802060d0e06160906020109030c14100f0b03070b030601091a040509042f01020714011218140d 73
    0x4e8031711303040c0d60580c80070008001041c10981c80b0810a1020702e5004850812980041080c0081c04810040305820603000c40c000c111260805820b0740e00a030008101411282e02c0382e01d003082d100c4038200c070080150703008060380d40c803552540c2c0000c014254540445008508025020030145000c5c495589003040301102d0242d9840c1c264280012070308007510a02a4650b24140d00e6410303a801d100c0d0034400c415100d6103881d500001c5001810303030011030300080b0840e1314101551000a420041c4104940d8218050200844d80c1e5000c1514114034003500410301820103078141c4038400c40f070308958504a800c60640b10a83d884412126040c00121401c0780000c040c000d0411008000301294a2000c2b00c5412142c601a1604003203001b03284241e1b0100c17500c44000d030904034030341700f2403022201c0520304445054030400c0000000703580325518020f9134020324203a071001c0384a80c00303102810340042050b0014031454240039a81c40021480c0c1c40103440e840341b80b41c1888510311740171610400e0560f15884030305 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 140759982 1250 140758732 140758741
    0x4020f09060618030328020609060c1605010b03070906080106060c0c0b09060c030a08040317071707052b0b060c07030605070e031501030507050303041406030a06120326010303020303 80
    0x41c611140b0f0741d8255010b0004010300c0d450b0840344001c51300510310700c1000c608201c400a0000b0315000f0018081109500070300188480c1c440b900b0203c0701c10000303001c80d01c3c040c06d10a00340b040c01811051b40c2c659040c419002c00040c42c150b0794100e0011540c0000080080945e01c810035182d5210201c0010030042c8015401d21500007180081c1514610142c825801c02560354401491540400071641c08149207070104410140e1007c89182c082480310035103030b018145a8000b070080c0c465011280e081840c40d60000b41c2c0e6a00c55402c2d0303001604403040e19007144540e00c05013100448a020320019150500303500c49064200380044481e00303045075004009451441d191200206000742078101044a0b6a5040030b095030204261f001e104285640e0082a500d980380a910f0010940d01c9580030341c0060204124400031078506c00103c03282501c440390780380d450078048402041140c00c0500c40071680d1819106141d817080c660450303c0400b001403403103803030302c1c28070b64028142c24800200103910410014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 140761232 1250 140759982 140760007
    0x602070b0910090f0b091309021f0311070813050a080d120f1d0106090507020c090405120c03030f09120403030302130509010803120f0f070f020a06050a0504020f090606 74
    0x150184003403454480b00d550780b190340c0f080944d03403a07500c90125068040b41c10243d83c60002c0822884409002d401c110310815035010640302d02c071840d0240c0c01e140080d61180301e4640240c1240307403031860ba003000c1e6a0b139000d40c0c0303000c0140390002030047c00c0d01c1e6003030b20b03000c101810010340103c20748241c82c00900c0d544041d22004ca603201384416038210302c50344440f0450380210450088003003092448a2011542040e406007500f140c07910b0340441d031260305000074051080c0d008200c1141d0310400f40d401840715521030400310b00c0c0c4a100d002041d4207480005000c1403844011002e9802640c1da41c0c0d030300400d9123918240303039514240900c048030501d001b0001000040e010707600515143d499150b601085035903920001e00a9803007640f00308075035000011140c0d22410100401580880200c000b084c80e4100b8941d00c40741c280b801400d0b0010301c0058014507103068000c00010144aa10220601003845c0080040d800b070102607404070b000d040155803125403864a40103a44c4640301c003034002403c0462a140ca03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 140762482 1250 140761232 140761249
    0x90504210e030706110609060709051011060f0f070804020a060302091f031e142716140d0b070509060d0204090203010e0c070803010303030506061605070e010602070b09 74
    0xd0314103000c4040c0100010791824042400100403603100c07515604012a0b5150401400074602c18054000d84104420a500181e1406c2555406c0c0c40c1c40740300c01d01001c400d54161184081c03603503840c403d0008020341c24070901c50041c403c0c1900c1804550a4442c1001600c1402098600030350143c0c500c2e4051001c98866030141c21500e0005003141c5607029135028814800540240c00d170002619000002000343d1241c480707102d2481d00c1c002c01c00c0711141e80e1034002d001c800054403c030440000d800c8414109a081189400390102401c156010312550605c3c82e01d40700003611408900c0c42d0a01c8410070030b4034010b500704460603000584c942466030b034600112140c2e8007486855502c640c0038480c01e00c42070a24400340015001007000140d90754180708442e0030818008000240e070400070440031002500100130740c9c3c1125403505000c02c00f0b40320003001078994002d00d0b003143d0303103004c550841e4010b014001541604640076602501c009903290f8074120b8484526009005d900c010821102003142090500c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 140763732 1250 140762482 140762543
    0x71101140712090b0706060f06021f021305060301080a152903121c05090c03071a040509150111010612080c070e0c030108011a010e040203131416090504 67
    0x40140b841ca0302c4134a11141ca8200c00300907030b6044e94420051041c07080707503d000700180c070060009000214170511980c07200f10701c0101481c155500422010030340b280102d400400752400402884e142d40c0c4541c02c081e6101070b81c0c04180c1c0d0400301d20303001c0c1d984401d02d44610b4000920041c2e20a0705a0300b813441c042e03000f1f94021042034040c8504085003507001d03803031405080d43c0e0344c14950384034640010f030301403c003680c202a00280c45600441040c4045950000b44d11044611030840118181c20491340403d01e401b82d80e201c0354000e84598104100c01c0c401042c608490002600c0e4a05c08103481c000b058201c2e03485014041c481201da0900070b0204000502a10b03a411250b42110141c030385461112041403410b540b484001c44001c0010b20003160203010b000312000c071681030360040e405034000007815070070a801c0307a43c0502d40c0003020890041d015131000d014990005000703541c0c4028584103d545400382121100c0000c3e90f0b61020034904558080c10f0b0007260065860741310003207080a000c1d11a40c1580 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 140764982 1250 140763732 140763737
    0x101503061a0301020a260c04061101110a030905211e0f07060902010906030e06010e15090103121b08090103020a090801060e24090711030717071101140712 68
    0x300401d810341d6090006018040d00c60352000403d882c44440354a1101d02c03540007940c0e801584040080b0949001d05171822500c40740341914282d0342c11004180100902d054902000300001401c01c1c4d0340360140c11030f05240c1d200d20100c800100d14a28200360300701c1c10100240d445030041200c03e0042c2e940c8040e00301140c012108035464031a012550265650010324100c0709191902c12900c103540c0c1041b182802428079080034030074466941c3c081070b00c84205018103c0841c4030b9001040700000c04821080b8039110203041d810041d44c6a00b0001c0d10202c261000c000090b11104480d04c0c0c04112180290807244d1010590342007481850042d0045c1d001528810104030161800103000c0109008820040210760990b9806c2d052034520007134019111001d030700d01940b44041c1803500c1e8440c125415882906c03858000c01205a4030401ca085d40300b50080a450905040c1c2c581040006000080007500d2240d94125804213901d00103403100400c010382c12121707100510603400480c240c4940e0300c0400030300d407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 140766232 1250 140764982 140765021
    0x30903060b0315010f03020f06071a0c0d02130503060603070605030103020d11090403050c01050f0601170a0615030203010503070f030f030302131a1c0e10091e1410150306 75
    0x4520780142c4003d03444030142d00300c03041702003040d0308040c2d540360b81a4005586241c034040840e01c502440a20300700c078100c0180d20090020310501e26520a46012894250042d503503150711b00d4541e004204039003d1648a80038841c0490359a140028040044584580341e060441e8030319000c10400c806010400d4a480105912441035581c0c2d89016611403031003611803640740c41c0c0c505862400c550380200101c0c8109154030501c12140e82114121125100c10301640315255070b0781d07002300040c0c200e0f82d00003d5490790000b20000c180c0e40540280d0305a078029411203440c0ba50300c1000e020410164400035146400c48960000464401d400410f4001c104401c2007601903074031001c01c850410040b510130300c40f02020441c540d134840045414207841e8004401413100181504070f02e03440d1502005c0c40c1c03a00d152348902d545d00b0080303041d0483c4199400000113180d0769080742003c43c3c499110660a400034000c24a405501801c5441200e8803940e01c1151030720303424195911500104040c001e5004428950f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 140767482 1250 140766232 140766253
    0x3140f0a090e06060f091c1e030215010b0a0c05011506030209011106010501201c0c051c020303010311120105040836060912101406060304030903060b03 67
    0x6000003803010000603550240c5141c50015401c01a501c068500c9100d4003040180301400c88081c000c0e070705012801c441784c00e10212483d19641c41c0c0d9034603000c000d10009115420114200140000c0245903000350290f4a180b104502c40540300c80d424055118911014007c0e80e003140e100d0032540f55524418800042d80799a0913002d41a40c6165900220000350000340a14195074800c0c9101c81150f1094002c0541d0750401001812040310b80440716500301e5014032020200d60100220300b8265171140c010000000ca00c800181703d440c0c6240b05450511624403042c401c0c6038000d0050851300556400340d402c5908650702d408009100000f0298081100040d07990305000a2042d640910312442c10140d45803540d03500c0602941d00301141d20388001d0307021180352410411000c0000c080c0343c00c561040d61128070100081c2c0580400001d1021442042800416444d0315442050888040d54049015640c0c3c0da0170410144000c0b540200085c100f2941080010603d030440300907418000d0544001002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 140768732 1250 140767482 140767507
    0x4030b01030c0f090b090a0f02120108100e0d021f0e1e010f09020a0902031b03010b07030905040b01171005121f1103040803070912080711010503130314 67
    0x2080e0000d07501c0c000c05840400555540074004001094040d009100b128000000030b04400c00081491407080d4a4418032941202035504440d00340301c03099904180780d40c42e41040c995230503002c00c41454061510526440e0050001a4a02c0c41e801d641e0060100107428100c010842210411100d5915100d03110080c040c2c809012120340030003514800c24400451036901400d4409400c0d040150b6841c0c140194056280d020101007030716a03440026a49845034012200701c42881c1a00c7c0001e04d40c044000b0440c0d814440081140c28000c5d0348644541c2d448800b080300303c84011880c24003007030a01003500f103400d4502613802d901c500042e09000610350340c0c902156140c006450300010b990400b1504c45201c00020550740c0b90000b1440b001c1003100729103400b030302c0c0b14480580090401c0e00080700086400d84224214070241c18100300c05a481101803030119036541210001700c41e0300e00c1c1d024500c140d552040040d24030600a2140304400341c200c9840076940e10524848800032101c2c00c01c04222105e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 140769982 1250 140768732 140768753
    0x30f03050d1803080c040f051512010303020303150609010815010c0c0807030201110118020607050a0f080702030c0d02010503070e040615210605061b01140a0b1e03060f0c0403 77
    0x30b540103804800351801e20340100b40c640000c0c0b0049007884207000038011401c20f11503540c150344040d00c0c882c902c81c0320711084448a0280180c00c0350b084400600200426901102641c02902c03019a000d00858102003048084e01508404c0e40c005200c40d80010f410320b4251052003c80e09060604400030303501070729440303201003c54001c810f180e44040c0d010011564801c4207191800440b40081010035810007120b0500d813981c400182c801c02c00440d0140920009000d000d0701184c0c04410005074210703610388412580c20400080c0c4c0302e40241c9001300070904044003100c144a60580d1011700d181c1d21a48207554094014141d180c11030f41d949000324880814102c4407000c41856110081c01d91000203007440045445069a40341c0c4e4100714040081d61140070a9540108200c002c00c03001c00c5905c40101d0040002d1782c203c4c07034a00700c800c05200b41c60b65103030b220050001003138450906c14080320000c4156100c02d0308480360903a0020002814003449080159044070740c2400161800d075403a19900c0c182e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 140771232 1250 140769982 140770001
    0x607020a020d02060901120f1a090f0105061b06090a1502090d02091518040209011a09010c03110105250203041a0307050912060702011a01020d030e100c03050a05060604050a030f03050d 81
    0x152751602041220400314042ca000c880c1e0844500401d440c0140304218080707010300c1424051203020645500c004900c0f03c980b407130700600e80101c4003289091204a0354840d03445d42c0658a100d09880058214802030003100c04024001d4001081400b00360300f4841c2c03280c0014911460000d00580400f20b81c2e8543e985207e03005181005100d103803c00c7c0c010085040e6042e4040844900c00030081e802112380b103002d881444c102400e1858000700c00d41400e071135500d40e081c030f031480c15445e000800520400342060491001d40181100e21561040c000a80e928411401450707940d82503840c0c1441c100482000456200b882442c02504202980300480c942d00340c558031260350340e000501000401ca909115001e000980f041603660b00502c0b400002c2d40307a002051030a0101354440e104006003000070003010090400000307081020340c0c02c5640c020010030050300d04a5600c0c0c1814040349952800d82d0548041e141e009200c100028910b5603884505000d0b80021014003000380000d0b42440d02c40d12070074610 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 140772482 1250 140771232 140771261
    0x6060c0f01061403012007081902031207030b031b0301020702191509030209041e0c060302120a02040b0909131a04113309040203010312020607020a020d0206090112 72
    0xa050043e0040c907920140026402680f40012180030009141d0300d0041031107203654480d5403442282001c50f080e100d007d90f00c51510f40e4840d140c040043d4000014503100004541202a0344c486410440a460005c10801c0c0d065100680d00300442d07a403000c3e013448800c0000c000610340750184c0e01081c88101c030702101110040c00640d0070884000c0c0c03001c2c400c140b00311a160040501c1c2c111350005844220141c0082d02c001d85000d0701c14410140d00940032030342d54109442c8001c441e81c2e210014043e5100c1b43c0b4a42c1c0315038020300851404001c038000e440c1940ca410070410309010020061011040b1300511120400d4030340610f4002041d01154500c82c0305080300324450b01450981050540c00c059040749900444c0e50040d04189141c0c051094030000b1082c0310f08000041010140311517602413411259842440000008100201030700280d2204101d9001d40702039a59131401a6221002044040d4000007140740520052421500400410a05041003113000c9140f00c0f064044640d060030b042c02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 140773732 1250 140772482 140772491
    0xf020301081905030406031116080910080f0705030712091109010b1804020901020f15040c06051c2a0309030206060a0f090e0a020d1220031206060c0f01 67
    0x2448414000041180300341d20103410501c189650b40d950341c5c45148281e40805a95044000d91150210122460761016410101c1100324604250306968400300f269446041c0303811800c150503009074805841100f042c40b03000071643e16228240c0301b0f948010090010415038281c0c18090004d903125a0034154041c0310200b24001011081c0840204103811403810840c052002079598080810501480101a02e01607100d243c4034005030300c0c003010842d642d00320340540600505255100500d8503ca18060041031100e142da410082e00e0f6413103102511703000002c0d40b05911140d400f80360003075551b10080e4003000242030003004c400000703803100c1000e030b00c0041d0b1110b501d80145a41040000c0c0c00042c100d80c9581c4107481c0100385101c00e50144611084251200030745003180e5014403000c50900d4001d05074954900952400c40480d9401c489407402250704601c09034443c601c0e19520491980f5400002d41c80c0504140c1046110007008148a62000340bc00c40c0c0075582401b0300c0400d8400d2200b600208 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 140774982 1250 140773732 140773739
    0x50c01020106060306080d0c0203280c0518040609050a1208040b0105190306090c03021504091a0904060504020a0f0b0a02100b013204030311240601050a050c010f020301 74
    0x2429140141e103c54105420f0070130a000818003c20f004490300c0300750070309280412051010a0505500710f440a87d0185180102c010344091240711002c06841056180e124640311006c002166100b0070f50b44900440c0c090014000440907404943c84038020070440c1ca6410b12641c400d064016202e946500090001050104006c080404580500780c1120625000030420b2301c2910201140e1001a000f01d85130765055003808010040c190207950090f10754182942d045102a681e80c2c01032281c540c0c01031418210180c60b900c50040107000f10f000600000c030303948071500da2001401c4090000d81c2c1c8512440b00000703072810690001c4000701b0061b0320091312900e413481c0c0030782004d800d00c01c6241c0b480c0c204042009160f0380042c0c80d6900071081840401554212010042155410005008500c90004010043c10340008401c1180a81007045881000c801003541450f040e44181d0300c1d14002c80b4401041044d8066005040c4100561074401d043c9403c001c645800c1d039116a0b030b05640c581c0e0020060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 140776232 1250 140774982 140774987
    0x207020f041a04110f030a091b0e04020d05030d0e060a23070f02030f0708030a050a1503030809150103060902090708100504050a020c0f0d1d01022104080604050c01 72
    0x40d05490000c45040082800841405114600c0720444034411690703180e010220038014000c1d40d1854052200242d100d10b88561000010f02c0711440c141c440c020305880400780a2115110142a80d07108132030100c29442d10b5091000764203c40400700c3d42c5000a101411340c1800c180b0446108020b05c600070880380c1046d581d2201210742450074000c4483e05403c2d0104000e0b102c00c14103400c55094070f130044000c4405002203003140603102c41c50f07040401c000703051400e00880001650041c03d900104000316217640703091104403084007071000c2414000031700030000309005d004902e80c03120110b410303104c1400c0104c142c102c3c5010260002c844c3c803982c0c0c1925205600303040c84d02d954040d602d401c10a4017410410040405440715210311445142c48000040035010941c041c0d45d2010600011a00000c5d030200ba501c0d00d4240740149140000c842560641c005140e2004802d0070082c107030040c201e212a40100d0b8240f40030f403242045c84007801000b00192540080100a1045004401800b0b0b44200c58000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 140777482 1250 140776232 140776249
    0xa0f03181109090f03090f01020f120a030b0d02010e09060415090504050c030606010c120c020a170f01110a0c080705030a02030a0807080f180a05010f0b041805030f0705070506030a020702 82
    0x4030300c244d6012641a0702800c400008446e0745010496166400c80c10140040303107410214a203901c1203005500d1500c2c82d505111000c0c1c5141c445985003409540c1324581807080c0d940444002034006421440030100c1c41c00e02e0b1409a401600140c004211200b80a0b0710720b10700c1040e680201f884994410420050110602501c00c910b2001c402070003050410000082c0101100d90018040c0304480c100425030074040c1012001d01c40d400f03006540203a5a03018034440d05484e07000303500d405015108001c0340c06881846005c0504811688082c02c241020030120380405c049002110801020040c1e540030480401c050102d401240c2d000759030b25803500d40000d140b95405400f62041c050307480144445d5540e4580c441768441d514050000e003103201b0390900c1e031030100b004801034240c1d440c00c909a6003440c4c580e004030b1203905058805000002c52091100c80c40424002d026203950011310014211041541c000d140702406141202c3e842500c1b0000104140d0054a10002265000413010114280ba421 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 140778732 1250 140777482 140777491
    0x60e0c07050c0f06190201020c0a0b0402180426040801061410090806071b0b10140604030c171c0509130e0a02010f3509120a0f03181109 60
    0x446402e0340c9000f8000c50218041c0c440c89418280424452004291007503055440085188045950055850a0801c0018000e40c1c040c0e02884815004025103610f80c0f500900131640004001003411000c01c0d185094a00001c2c001200e1340100b00000d4446c0e008d00503800504540721003091001000c07420004840b034000011028040c1c0460700b004598004550740b0381c4810103003045c0f40002c1000c60000035002401d0001840301c00c1810501070310300c2c2d00d070804805880403024040a0751018104008090003944001482d010407964280560050082c2140c40c5150720000c0f5984009010900c0000d05a005061800248041807094181c40e08410380400c1441600d07080101d080e212038a82e884010080c0c0290500c1841c094100315188241c0858100e0320482104608204040007402c00b005503291404116864050114005030b5000c1243c900c00144a40014980003c103003017500e840884011507400d059541111122402015180300004c503c200c0c00d0902d04a40d0204100740410042c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 140779982 1250 140778732 140778739
    0x6020d0815090a0605040510030b0a090804140612070215010f060f2f070305060a02040e01030f0203120406020102031608010f03030c021f020303040302150606040308070303060e0c07050c 82
    0x1428800700c0709030754560540c5000260380e612860ba8505400d0701c00350410f60302141c1c102d49000300300002ca1107054039150a5a00c140483c07055620b030040da076130a9035012840034001c40f07410081044050449113600e8176640000d454542071400404481001300c01c200d5034240942c200780041101c07001508085400751448010089800d1308001d0020100c00f801c110b15000d00130703030255002c81d500702104510440760110a404180380c0e00c060565840301d4103440121a94410400400c84080b050300a6401383d03079402c0d401484c00d0f865a29190741d40055550141c1e01400b031070401c150b02418041c000d0028120300d400160303490800002512101039404070401c100301048006000300d40d90200c007481201c0d014036105984001600006441250b84c0c1f9808000c1d0300c40b1003403510007039000b1015500c90760003034007900e01c1140d590064040340a0300b211860343c4600208820700001c1d10460151500e180240b0380003500a49079000d104a54400307454508131224046800401c1003000c120100460b0020b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 140781232 1250 140779982 140779997
    0x120a03140f0301090203270109111f0c030509060415080708041101030e12070c0f080601030218130c06021f14070318050304090203011a03270c090a050106020d 70
    0x2441a810301c1d0006010700c505080c1c0000104810300d031032840032068101d25100061040000000413030003800745650444103221000e0b550704151500e60040000c0d018040c003d0801d802c1e984204480a11003d0000c40610100b0310808001362910405440034240d851250458014041d5014207980301c01008101000012010040004d504060036006140282004910040600320581c14006002c0316001000c0021400070300348602d101d100c3d012205c1c4040413100080e183c00380103072120401d0001a405c020849901908000c24821041e8040707500b40541c180705031548daa04c41d001561340d200d08016801403c042da00071881e038104a1032290241403c010860302c489a0004048006024100b807540d05c500403091483d14070340b0032150661200580b135503240c40e0f04400000390030038041c85440600440c0c01c0c4484600c8c41003180d000c1c9411500614501241042179082007da628000d2800d0207440c40000158460b604800c1c0141c2c1c0b010004515581007150080c0f400c0208119002040503a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 140782482 1250 140781232 140781247
    0xc101109010c0209060a030203011506030b0a0602060f0403090902030708010602010b01020a0b0f040305040815040309150e040902040209180910050c07030f03110c0c10081e060f120a0314 82
    0x40105040b040d40c1c1955a03101c02e030343d400006240401103074401794055007402d8002c0c04541d81c010340034058a0040d2400c110041014003400b01040303040c0039850260340b0030f602040c3c08551640410754454440c2c580800c15588404c3d1000c140c3e0415940319000c90b03072180050140716020700403c4030b540001c0c401020f069290351113161080101800c6945000040130204050510805c100e034041c0c25600210f07500303004624481c01e001c500840302500002c404640c007007040030b1b085e07050f440d11540c61759616901c602030b07a0800c0b00508500c20301f240c2c456400c00c0f0491042d114000b0242c1c00d2344c100a84860a440d0031641385080c03014800200d26018682000c011a21a104044d500d031a501031500076502d049480c1e044e80180001075941a683c48041000007001c6800611680001c00a85000c0304000120360181c5d903500b006c0d60303040d1004a038002680b03d041b03404600e00360300103001803c0b80301210310b600100351410b440c4102d0041a42144a00005064011405010f85d207030080059141455 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 140783732 1250 140782482 140782487
    0x90e0c070809122b0206100605090d02040e0109020f03010606020d20070e07021605090106050708130f03022b0b092103090706030902210703080c10110901 68
    0x600c140007004500040384558403900e4149000c001c64003028111030040c060f504504100c0b40704208500d0070b440710105442c02852000c2945030207401148041c1f03210504081d0151141c1d04182c18682d00103504101c080e02503a607030b0084c011040041e00001070003c00030f0042c000c4004550104900a0703060443c01c000e0140e00003480c4007003440c0d92900219045111115088140d0307050f00c07041cad407031140300008a42d00512030786250154801d9005c5445401e07000b040c0e000810010300c1010751001e01c2d40c0c01081090300a00c0101a00752049102c1f51400150303101200e540c840581121921720720f400d100340112304120001c0b0454010001004040c880ca03407180c00c0791b42c404014001d010500d010003244001100300f01069003905800c21030500c03840c40f0345400b8500c0e00120f803655010300c030300d04000645078040c0c0710701d0182e00e4004d810030a024900c07108031401035a001400c6000e9119080001010030310342d1001e000c0404040001d084036071a01c0078101c2c281c0b00701c0c00341c080d200e03a000c100c0e00604d680c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 140784982 1250 140783732 140783737
    0x509010311010c05060726060d081b030310050a050102060c03060d110907030b01031a0312030405031309090c0b04050f0405090309130603062d02030a020405060703020d090e0c 77
    0x2540140c9080c12801c030300c001254080d60b52840100f2074440c49050000c502c0d08044100400003561900f1031521150041c40d04000c401607660a42043c600d400c840d000c141814000c211107290403400c6a1290340102030f0f07a2955008498000205089a0007030200b8a4a450103200809091005004506007445419424030000e0f1007148294000030440c0c041190508102d038001340000e00b09200751629000c041c2c040d203450924140005e00d0308032042007406008620804c0c1c000082e00070002c40c0f8801484c82002d51000c0e00c1074a80e0320003480700d08041106040003d01800c502400850081c143d4540b035500038895270022081090207200c140801d803a00249104d0010b4210341c0403c150302e50b440320350308610070090510781204032860544403c1d001038024404980c41200b013000005941d8040001b80c14200d02c020502000201003403101850f02d801454004500c42d000514203951000050440c1e40071190403400358202d00142c2108981081c0084020000d801880e1a0303071074070005001da40e2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 140786232 1250 140784982 140784989
    0x507061101140a090309050306011208071109010b13081f150801021809061c030804030e0916110601050a1502010b090a0603121404170c030d0f18050901 67
    0x1150145031601603000942100d4034003003054201504a041c2241c0160103030222410035000f240300070400003414203000a04078103c0c2e1070b51048401d04e007403503500c00d103140c1d003c0d05041d21000314640c40325070103680f0000b0481c001c04c080e824866440c607104002524900070b42e40104c6540d004200c5144601d01d11100c1500b1181c280040000e440c40350b25491101043e8030740101c250b6610101d104101040c2c891541c0300070b45011501c035103c656504080100d03194481d82c81048014441d000c1100183c09010340541082c860706296011008141c042450180200c50200032020150401c5444035004406010320804080140c0700a40c10440450f20001591042d0101c6034a054100100c00703100390310041882c0300062800c021070404000e0fa00180625002c03e50b54228585801440640600c004074291132b0f4500649007000d00d0010700c0c862102081020030718901a030017400c0000d5405100300420b80c0d00301c3d22205806d030304245008180c20301c4080341c04030144402405102954564402a044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 140787482 1250 140786232 140786237
    0x1006060e060a050c1606030f09050304030303020c0f06070201050a1811060d0204050a090209030c030d0e060d0f0f090308130c0902090a1d01080d03060308180103110d0e0607020307050706 82
    0xc4054002080f2440c0c840c501512402d0701a02000c0340343c0d03a1900c1a90307001c48a00e40d40c01c0c040c40803007002c2c1504803100744030001c1c000d074010081003000900030740152212024070000e680d107010100c8099810070f03604413503a0005075510403c001f58a142c1d8451000c3d11485125107080d9103110f03603552001d2104500115100c4d4101081c440601c1c406901210090200070704051980c039a600c000c400a034100c2c0c40742c4c42c402c1c040c0b200c000344d0310b080001c1c83d102c1d02021540ca0340c5400084c6418080b055014001c5244101c0c1c803041d071600703412200c0c00388404d0000115000103a88100382030040940c3c0001d015018400c508010110114200382c6994003910703a03048006030344001000000340006510381c040a00c1c0b208600d690140b5140d0f000c002812202c0c1c54003500c2e040410b40742e08078115051800010305001d82031140080c90044901c40113403140040c100054207210313420307443c100c90b08032079200c88210341c50b00c1d80900e1110080c0051608003042e07000640c2050042e0f920305440e01014000c9604 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 140788732 1250 140787482 140787487
    0x40b0f0106021b0402090319121713021305010315050105030303011208160209040308010305070b0f070803090a081c0605091e1005130506030607020706020d0c080d05090604051006060e06 82
    0x103d556164101d03030704510700408a4081100c110382600090440301001c0e1142c220410070b40941601403500d400001c020f4260407441e581e5450b480400000110b60140d812086400c01b07200c070360031240b00e442d01030350141c6141c22510384070a40040a07550160806070090b0424001000b8000c1c140701d4076190030383d2060500e0b8032020280ba9052130082489400b039072001c280e000380000d040d001410241664024004d032218a5119011a01d0b14482d2190f80c00c00640100621400b06540c64091074000311f6000c21381e401040550bd0b0541d181e08110b102c1c3e100024907a440c01421010b0344140d600415096901140c1c41c90042d0041211403100b408000f850980017000680d00305210030404043c020040c407407040c2d4000440c600c401010100e038042d0181c8216008030701f495000162410031120540c2c01049902440c2501301d03105001d54104545000c01440000e01440d060300820f03208401d4000240410b20f4103013000f40c90a1f00f2015101a602c6c90316106018550f480383c091840b01d5019610141d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 140789982 1250 140788732 140788783
    0x302010203160f0c06081f030201050304030518030d050c010612020f46080609101d0f0a060501050d110904110904050105041412040909030306080f0105040b0f010602 73
    0x1048040300b102c01404c0030103604010540d190006400740c01206404074803044c1c4c0c910103241c0c0d085a211404080c0c0819410301c006400a44a5402003524003703c03512203d9210009001c2450308226588a03400304e20007250704a1000b5007441408000d00d07689209180302515500400c981c2e03c640492580120000b0100c00103030866111040700340b03003091034200c0b02140113940b414400306c4541100f00c113869441030002143c03040000c02c0c41c080c0250704041c00c4200320a001907001001d42010300a14000d0054a11018a409000d1102c40641240203040c44101c203103866811518140c00507031003165109091404a8050208281049000e03140f002340350715a0b04049503203694840303440d41e201c64001c00b084204041900302600981c41030451008049030806140d0f140c40842c1282c000c50482404100200344442c0c0003001498021f0500040700c42c3c4844031581800391102400031169191420301040003c4c544001d5800b00090304030f94015414081d00a403140c01000c3c40d588034061111a81 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 140791232 1250 140789982 140789993
    0x50a0920040b0c070b0a0e0d0c08030d0219050a0f030504020315041514070e040b06070b010f080709020702090103060b01030f020a1706030606030d1b0c060305011e030201020316 78
    0x40540c89440200c251a1640c40ca22038030541e0241d500d550f440d005044001400741c99181c25a80203032916201c0e00f0041c1407d0040c401d0907071044409036400005e00c0d000140801e4148000c00e40300e480750030050b80d184110308181c500e5901d10f0b565074040050400280b03a00d141c1c00144a0428802440d000c1203a407280d00000385005007014494040c800c00348103101c2000312040210200c440707000024001c0003001c540d80e0648801c01c0743d6080105107008001c42091400d81d120340402c0d02c00900c25070820b14581c649088400098015129428100c002404500c00030424031006240b118001e5103000c0d002c2c0e021684090040c403006207404e071a149015002c0c1e000350402590b01c0c0c03030000c0031511554503810050540c007003c0e100c81d020b13041c2c400c0843c1c0d29080100b00c240c42180050300038000c0b104804001c4032103078000c0c16403100811105003541c0018136001c200c7c0c80104115500443c181d41842071051220200702c41c02c5254021200c02000140d1f00881520102001d0340c00d1f8032413403051414803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 140792482 1250 140791232 140791271
    0x4030f0303020d0507120b03060f0a0e030408060405030c120309032b0c05090a0501081e040503070b04110a060503040b01051302070c0b120f090a1104061d1609050a09 73
    0x40720a0982028100040540e02c0f850140700209104001d02c2103010307d00c145034854500366000d0301076208050018081c41d84035084080200b80c004126441e055070303040d0b4070b810000705840c00c4030141c000007507180c420f05082003151100000b540c000b5185040ca4007040c1e5881c070511000401607641c03080302d5408480450302c03c1c40c0441a600e014810004641001412a8460005a48203c2c0c0700344012680354441c2c40041c0c4a004079035001c82403410054101202d1a60080080310305100170401c45000035450202c0a000c0d074400c040740391080302c1d49000c00800c3c01d099042641041418020400410340d8800ba182c11540300742e45c0d0f44008051444818083e108030b8001802d44014010002000c0e241040103102101c4e100c140c140c0740b91600c4990b54002c07d01610061600e030f01c4441c2102c045034142c4441880a000140300142c1c041c2e44080004103d04070f4107040361005100820002c2400311180109031407106803a000c0512030030407001401c0c7c00194010128943ea42c1c91400c4949084c3c21003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 140793732 1250 140792482 140792497
    0x6070f030f0615210c02030909060a031b0e01090b1c0c0503120903120f030c030c07060c0203180f0a0b130308131403070509070309050a0629120304030f030302 70
    0xf0361807036811112002603c00442140c3d400702c04081003540d10000581c0e07102d802d00840c02070b8080d51034005510208130503498003600181c4e10228003000000000c6642c03032080100c904810007221040e01e802041c0c2c54514059002d5240c081c1040752440c06030707441c0f0000714070b03120090401466005060070090b88480c50b9800c5960184035501e8140d090400c5c41e0090014a401101111282da500e0043d060f01e50090329002d111400f018030102c0d030529440070103141c1c0540401c0886041003516160300c0c09070352181c0c0480d809070700001802c48512010100680303a454081d00c034500b5580110001c9200103070a840382c188444404200003801100151940006641000c803194641c406180042c0904400d4810002007103400c2100380c50604000c100f0404030f074801800501259a1a08190b014196506080361240222038000c40000c2d050301c100007681c103904070b070401d1541d00350034014040340022000603c500152964044500e4002041760b0035680c0c401d43c02c12a28105203010760103070041c2c03d0b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 140794982 1250 140793732 140793749
    0x60806010c23010f050a020c070b04060c0305030702011b0507020103151401030c03020c01021216020a0b0c2d0306010e030304050307140d0b0c0a141303030f14120f0906070f030f06 79
    0x3041c862a00740c1b1303401400c1003800c1c40083d41d802554810321101a441144640c8000c500d248054002090050b4043c581c03087c0c0a00021502080320007040c135000c80031107d0013003c18008500c840c01e6581c94411318200e860381102c80c403c3c450504640108c1142d42e450510304242c1c940c410030108911940564960590341002991108200e00300d451260400710b9564200c1c010094101e407149100140441d00c040c1c00480610050f01d410044822a80c4002c008140b225001400d00d0408014046001a80b44950a60603100d0800c0000108540d0440101324400e90091100b07210641e000f14a1004803011038000e00c0001d51024081118001116006400c0841000030032143d915036100420395824959201c10b0800038844e500040e40c002ca480d4040188a159002c0c40040e0041c1a03001d03c00020741001ca18003230000d00405542e5100381481317003180c0644000d101128843c0704c81c0d02d8000d08030310042d14081c40c000100914039200d03260360000705030311740c0d443d0b0070f1104503603010728007410000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 140796232 1250 140794982 140794991
    0x40b28170705091302091212040501260907060210060b0d0515090406020a020c0a080d08040201120e0109050c01050405060703080c071a0601120c02070b0d06120309060806010c23010f 80
    0x13900c68500a400c06480c481c005c0c5459205442440d00201c2c1d26a000790303050141c1c0381014244801101c0c40b00c40702d48c0c40a140545210300b00304908540e11180c1c800d6420800030300b6006e082240090030054415403902e80743d0308000040c04403e0003034094170b000c401d24043c0002d99548038a414a00c1c0c50380d201d4102c1d00401b8201c02d200c2800001e40042803c00116001c680031542c104003480041c0c040c034400c0d000641c2107680c42d00c684910031010503401074014588000c080c80540031980440b201142070201c039030755882c00a02000000c1c0026241c44409082c1142002c0c940008a811403281c1003004082110080015008500101c107681c006078105034201150302750740000d140e1505003901c2c0540410340c18070301000c040c143c500821580318050b90103401c45a15011180182c0d0304011002074116880390404034591100c09140542640240c0e40e0b42c4260b4542343c0e015000100c091f000904100301c1c07a0019021803045181c4032600a0140581c5e840c4c03580c06044540184044815000348070f080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 140797482 1250 140796232 140796259
    0x24020a02060403020d08060a030809120f01061415040b1c1b112109010e030a031806030c0806220f0b04060501110c010c0f0503040b2817070509 63
    0x140d100e00c22880f030380880e00f480783d40720402c0d00d40c2001260100d500941016060001030700c010003421050101038a03d10f10741c0800c0084500707101c1d40c0c514985145e03643c2d081c02c01541c0d11900c40c0d00c0c1480300c241c5291400d20b165000c42030440c480c3d4050000043d000084a005064002c40c8200f110041200e0802141030790049803d12604043d2904c0c0c00110380e4004405000e20100710329440340c0c0c034926503010003907000580640580203000e2450501001108150b00350320203008801055110359200403041c22860b45810072103d054100754101403420b090704042903080201d06030040c03011240072202c090000110003286c07000134011240c05041070141000080142c000c40d007000011581841300c50744910044414001c14a0300281d00e03070000e0303191409540104030103401d690084010309010107171911800c0c40c541c03199021180c0300380c0c00140a02c80e40e14164641805e0a0749a2850340005a59880105003959103111243e200c04c4504c00b140c4018002e00c2100c20750304001e00060548080c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 140798732 1250 140797482 140797487
    0x190b1206040803330907050c0106030c0e070903030e0f1f110106090c0c0b060301020903031b0106060c030c06150906060504050f030a020d0f170c060601020d020f0a24020a 75
    0x703551440b419081200c1a0000c120204c1c001091203070301ca240918401d8080c07007084141040540f940090020070400c402c0300034803c0c003ea2003c0d50040440d419158036201e00d24108400c020f00b198100a03080000b44006503000e050124101001c0f00c003400d00b5280c1c080060742c0d400002c013141e0281401c10040000307042e0000d06040d004800040200040c0740d440c0744090a443c104516000024145410400051001e20440d5000320014000604003414800804e14540c041c600c0b600030400003841c1d03140040c000b400380d100580514070b4141c038500c0090303402408031000500001c0c03605444030102c90000c040074030444001c1074080340600c00385a80d0b0b00044c2c4154024090640070307070b810044505041c00c000402c44a51580501510f500764481d407502c42c0760221511f011100720036000f421305501c1c88508041c114841c090009810b060500100185c5040d20107040c00c802d54010280d19001403c000c50469440b6800040d84461482c88090b0442c1900081411052a80c80410442106035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 140799982 1250 140798732 140798737
    0x1020909130510060b0f0d090b09070e0a1109010c020123130f050d1407030503031005031623041e060e0132040b090a050603070e190b12060408 63
    0x28040e0b0305444250010341450000d803136140c010300680f400104440441e24210100511010341d04281c0013030070f80c0c0540c0d0f0349104400d0540c1d419000381d000c0b25017804400036100c035581d003045218804000400860320610250300900d0802d6041c022103da640003035900503628030060080d00c0d09008900f031032010503c001904512141c5a02004c0c01178080f42d00d08401e01d00320309443c0000c0018a03454411380e136127024805180950322045c0599540000080d4040001c0d40c09107a017862428025030070135091500d0a40c58a10302150342c0c611480400900c160082ca09018403070400715081d4413500400030501809512514840c2e150030040c40341c00c0d540d03075a4026400c3e114056000c1a0a982c4c83d461303500d00c20380e441080303074a074100c06000c5d5000b2031050b00c03500c4a0b09005040030600c850703000001005084104d424001e4191504200106443c0c24031a07a800361516607495107440c1000b0744103601113048164030402490740c4e84000f5103503507a030380c40c441c4d0359442c0d410483d0005c1c1352900d010702c0703541c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 140801232 1250 140799982 140800021
    0xd09020406090614030a05060c130806010806041203090c03140a140109020306060a03080f03041104022208010603030504030b07020a120e0f0121050c040b040303020f0d0e1003020a0201020909 84
    0x48102000300c03413080c50042050140107400100070540c5032180c00386000c3c80c2d0712500102c1a0b08050090005464030180f10041c02800714001401e420301c0c040c1810700c0700c030000d400008200b40c50f1641480020315005400c6066075005002e10740001c0c64100b44a00c1c10503120409044044104841c040c08141500580c56440c401e0303043c1c03441603c4210501c01640364a0200030140501403141440c0d01170380f40d002e964054002c1081114024070100410200d80c019a224450b20841100b0035040e00c08101d28400186590740081003000d185490041107806280001402224903030007150f0a13a1003080400721140c0c00441007015090000300103051440b4840000340580c9002001907019800350403032990004056060360342c0401711001b010002c18000300703a01c26001042c0004101c0078414406040a14442d800401d150301d410840c0c01d1400d01e161501d1030410030b5850b80e10440e5110030702d083c11210172900f0007680310201d04c0002d0b07000e8000c400055170480c4d0058100216102d018041a606 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 140802482 1250 140801232 140801249
    0x14070c090b040b0306010e070e100e010906050a0c030315151206080a0209150111030c070905010e07140d0f0908040312021209010c080909040c0e160906050d090204060906 75
    0x1407004410900064541809a00340d2642100004100c40e480b00d1600540c07101c101d1504018200500000071494001e0722080f4000a10302c40e40701040f0f5800c80404c6015000c6410300f9810911b0a0a00a1040c180701d18001d08064588000020464403d400d4401034400100340c40040390244c080105042c0b01e0401c060145c03810721500081403070000c81c0b045050f68000d0000e85680d03488070682005040d034107071024100941103071801d620782c0086c0050001d02c024000a4170046143c80903840c141c2d20103030002c020009020050100580d04150400d680c0d105120740c450f101c20214510700020221524002480c034203009038403040107902c0d4000d20507a48108070403c40f02000190403a9217888000490403080001c004000181d0b004140002215200b603820b145004001000300740b0104060740d00b180c0c00022031a0510816a10049042d44220b1040d400c07003106000d80c4009040310341510505043c4140041c50700c4180542c2e81050350466005001408030540d9902c20304000e00991007220803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 140803732 1250 140802482 140802491
    0x20706021209150106090e090f01050712060801061404112b05090105040201080c0c0a0501020d090b0f1608060111030a0806030c011803140109150606090509011d040314070c09 77
    0x100000e0820f029041c0e403c1c40e134405413940e0a00d5182140f890300500b20300850f00c44c6d4a1843c41c0c1280034011a846054540c0ea081c1d00302c45502c40c5081542c1c4207070410041641070420600c60100c603440b031040d2a00c030807940800c0e1151f4403c042889481816803180401c03401100019121a0f40c00190303000b440740303000400c03550395070002160072a401501c00030f00168030100070560300d98a250142102c41c8070f03136040c0c80f1401c030160703641800c9900c00040e08802070b848410000030b03c0340c41d02003142d0201c40c0c0310200035540f51074110380780b5420b0f82c5142d900602001c4804101d26034881e455061400c4041401c0700d41d2800310000c003406c003500840d4018481d01c6860003d0071305520940d40c0c080150b29005a4581c4d9030b045540d40781d88403655241e4421191340e02c90499000c40d88034481e4076424090040c2c001006070511100401d202c0c0c0c5504003038007a01001300108a441860001c91510425186442404d900d962804541d90150128000c80c10100440c0410070b00c1050300c4014100e40c4481c00800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 140804982 1250 140803732 140803753
    0x306090a050d1e031e090c0305060a200d2c060106021902120118080d0c0813020108041403040b09010207140901061b02041b080a270303020706021209 66
    0x880e845850f60100c54803481c55107022495a001c0d80110300740b42c80c43c60303e4140252040c18418201c0385010000e480100103e0010814000b00f40002600600c901e68140920060071945610721a894403030070b00d04420000c3c038071107168040e912000d6043c603507400c2010400c611541c8844030404c940c4903440c1da40140000015041d00004091081800042111000030311b20f408008200d80315160101055482e5120060042c24074002d100d00c081c0310300b0720262a10540f0514004980352515444148030f030300f005019041c044550b80d1a04140d09182210031071b69549880c51482040f000025407601c8045004038240c0303150f40181900c41004c0e4201d40e0040d54843c0c0c01e00c145400054034503004a000300061200c1c1c0d11030100702c404560b4400e1409003d0340b440d07020808071a03158012185a24600b800c5a62980e4419149500130f02c641c001400710a070b6040119008242210101c800600585d1242c4100740c029016620302c030783c0184046484040400307009480e40c1d0210303500c01140c0900010300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 140806232 1250 140804982 140804987
    0x307050d030b09090115090903020102040509040c0602060916030b0402030a05100209031603021e0a08030f03040b06010806031515120a0b010b04030c060302030604020f0c010902040f090305030c07030e0306090a050d 94
    0x79080d0300e2082e41d50700e1451602e0304c50001020008c40540440d50200700101d081d85a010449000380c1c42500755403121031a044000381084c8014050901540080b5980041d401c0c814600c0415031342c100600e00390b1510303a480001e10340070401c10300500790300411151247c49003059001c1c007040201641501d1652080031641d07d444003183c0402540515191040c8001102c00000d07008443e0000c0c0220741000c0d1103000052554000c0c25091081704c10020420080207181e05249402c00420b0800044c1400d00d600040d40319802c1518811210f10484001882010050405401514090b0038000903102c618840c80d15208020300079501004008000110844031404440490b40c00c0b400c0c444040f0300340300c1e08801035071000d001030364007503002c1c00320f056801d540e0401010713074011401c00012080345034030612068802da086084d045600e400c0e501c0000c6a08001140c1e0f200001000c10b944d0b802807803506070745085442c10350759010f01c1400f08112b1146000039422140303501440485006030000d4008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 140807482 1250 140806232 140806241
    0x605030a032a020603010905090d05031e04060b150c15040f0615050402030a0518070f0b091203030907180203011203110709150f1a03060607050307050d030b090901 72
    0x400145400c80740c05441d40b0601c81c800b000c00300155032407440c00c0190300050100c0d0420b0b040303220703100c1d43c130001d00106401c200700d075424501c801d0a0a42c1989081e1400002c540c111a640c406050300d1140041d0800c40c556000d0a004d50000344150f181c0c409030144400b4030380222116040703c2c0305105c032055000d8500b0882d00e02c6164401564400341d01507560b0344018124250720303152854244040860a5036480c005940308842002000a461900c80b54204d0300180c00d041640340364010000c18003100003145003203401e550f080e841903030b5074038004804110542c0f00102402e90501020003800a43d0502080c0001186c0341c0b0b407400c8907650a0800c226003284000c5c45010100003107189020002401519071043c6003072114140c031001d80c2d41c0c01d90241551400000b035400104154004d002400c8000000d1014080450601e010802c00001c85005407001500d40c0744141c00205881c400c020301082224921540320090300c1c00304c4901c100c0070b0064600020078a2050300da010020344109414401c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 140808732 1250 140807482 140807503
    0x70302070918080c0c0d0f0605060a0605031b0d06080a020112020f091512100807080f03030c030c0d021201240807030515040e060901110f07080a0c02180406060503 72
    0x810348120070050341c43c5030590f40300b10b4050100d40280991200b0799910444103034070b65400f4414001800080c0e20f401c108441000307001e544500c0d0014010702031554002c05a075030104006458880d20240d45032664414002c103030180d400e603070038514085035800012468440d4240f0030703203030525449001700c4403c041e03005a613a9150520007d01200859240c003400114a80d00101d038103520b4450702c240c00307000034002190f010035030b05a0308804102221b410018100244807400181c0030300b61001605585921000d1b00306c0441c0040800810403007880c1c50103c8800140d204030031561143c031600210004a42480717281182e0a502170140f042d645003081c5c40b40e4000c071b19a02c0308603039926010160010300c4050700c40317906c40c1910501386000c0e4443e03100c2c0044c1200c800c070003803440780780403600c80342525088203040001070701c03d01c21010110380103001d85010300da0040c402c40d190098144115100b52084101a511270310608244a032a1281d0f001c4500440c066041800202e172a80c0505a5440385802d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 140809982 1250 140808732 140808761
    0xf0303130b1302060705010b1302090a090903020c0306070201050a0c050c0a20130203010503010c051e07031202030a05070207080f07060c1103060903030f01050d08040603050a1506050703020709 85
    0x12200c10004030015071480c0d200021068082e968010354001c220300d50800d00084905a6490481102c10b1401c4140e403450f83e80f0020040d803620b40b000001c10b14201ca18441c00c11700a0311078050f00c040500901005000e032901804449080c83d000340024060441981d1003414580b600040d84001c0e4800c0003111404000b190041941e0021a603a4281e9030040d10110403c600600308414850360740c04030b0b200c00c52520384801580703d5041c1001c050865088240b02c5003405401c1005c0d0358030403c61000e00d4140300640c142c580d1a51a5418240c42c85020041d404900600c0002000784103100c0380d01c800e001d00100d600301c4201685500030740342d4039800305035031120703503446488104080d505c54001012454800c01004182c03021003004286030160a0714004c20a070404010452a40c1c210200c15005103c11030f640d10b0503480329203a1004610803030080c8001c05445e072000420b010f4080e003042c3e1903044100802159a650b50700018000c0c5c00100c1c1c2140180654500060b0f050407c0c00744008000003070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 140811232 1250 140809982 140810011
    0x50f0d020c0109500a0206040617060a03020d0b0a0e161806081207030908010212220b0406052d0105010f0203030c09121c050418020313033606020f0303 67
    0x110407110010040e484c070054244900040200162602c0d0b0103000203100688402024803a9902c03030001512000303100354010a1202d004101603550040d45501c043c0d0404103000316074841108200180c00030136403986092046014610000224850700800c4440e010307880100344140390540019120700d44a0b5003003e82c000180c10075142c0014006002091085c20a0302400d5070301d1908a01760780000a040b030400e4580d404002c8284020000c14a440000c1e48240e80c0380c43c20b23684d5a0b00701c0d14000e0b2014042581e604006040c81044144010048082c0c0b0343c2c0c40304a2081e800c443c682e10b0401d0160b02d001a000c4035085900030700000c182c9018100c2e100b406070510400e001400254071410074030b84003601c915400018142e90204141d1100a955510f840e038030741c108540340c80c0c0e00030101c904195280c410400c004000e03164528140c0c0140d8586002164000f802400c007142d100d6003036206100158007154046a29003140040d800c981007902901e14a0345000002512800111203003c00c04400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 140812482 1250 140811232 140811353
    0x3030609060405091f050105010f0f2a050a0506090c030307050c0f2d210a11041b020102090a05010810030f060f0507020f01050a020a050f0d020c0109 66
    0xa6004144c2c8010720b2000c403403138500120310040703c400e041c1c00b41441c0785549400500042d40d00c110701d40c075000881c3c200100c0c0d0010f42e40c0004c000084441e0402905002948880c00d081400d2199603d8140c00000700c50104e112828019204c020580c8d0b030015602c29210240c00034140401070316040d54002d00504201190203090140384800444010750196401c1030269407040c405c402c40302102c14520803150000360640621060080e00340558414a04000c500c440c030110008010360345640c030030340c0c1c46661580100410090240120b07500c0c004c60400c2c0c00c600c01319505601810480d5000c8a03443e40c0b0550744c50041d900500d040c0d4640111854540b07007803004c60303106448400d401d445204005a0408060895401c0394070075241100184c00c83e104480341a1000d008040d08081030020851030b2a10040c4041c0c000d224498178248c0e502c8011441c9191007007280d05864a011400300248200b821a24004042c29907416048818000c0e61504500f41d00346122000045a400c0a484411069 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 140813732 1250 140812482 140812489
    0x50307060c0203010e030c0f06060613061b02060a0e0112182a1203020f0c062502030a0602030f0106030b010507020112200c070b03040507030303180b010f050906030303060906 77
    0x1c40c030701a6055034840e194002d92903070400040543c080580050108840b484c00118100030000e80824400d52050000700c82d00961800010200c03511070400000c1040320322106d81c03002c207a00102a40c808000b042e2110441c0c0c000c41d44607180c04003660b988118126280f041d008176882c48401c495644102500480024140700b901b5000f000000103c820035660241e01c1e04100d140d640085500c0f60100403518100b540400c50304514030880c1002d010701100081c042440b0380a140070548190310f100028000452140e1100003450380c014082e10080360070b41c1030100c0030f50700c195604104c8402d5a0000030b0310902c0380c840c0c841c0b9410165101d91038030f41c4503001100c00c140310034080c6512656864440081c501c482c001d08030160342c100c0f0800d4035a980b403020b46007040302c16440901c44100c104100b00000d0310201c0c1c64010307254541400a5103030480c4800420420601d04010a2035480380004141c1e91461204482224021208624180d5900d000e0688902007a540307150844003c8010404602d23 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 140814982 1250 140813732 140813747
    0x61e050a29040b3006031c030906020c0102191403010e10080105070c0c080f060f04080405121513031b05120f0d14010602030708090a03080f031f05030706 68
    0xd04101e0362420140c80c2c6011919641c006960300ba200e00c42400d003c046090300e45400d01161906141030252490824040781c0c0b65010011902802910740c004d072a0450700940c8110f9605800c00350464558003403500b1107000b0f61140844c081480600e0100d01006403003140183d41c02c0c45030303040c40350440c1d1a007000040703201005040d003400c01ca5011804141d464091080510600d00e542d00c1400c81d030b0741403c00c400740d1003042c3c000c00d8054112040205140d10300007040b0b0b401c503607589001a80390340c0750b04007070203d03010700d420066021988003103840d1035440024607821000340c286c0e006055601c7d0ba60307000401d54035103580140891940c0406245450384a51440001c03400b800c207881c1c01180140741c0f80490b501a600034280510003113001d501c3c1d01010b1140c2da07a11741c1c0034141c0100315410480081d42e240601200200b07036181c006401101610bd00000c00000c6902140c0c4a0700c0c2e221904600c040ca0700105c5104102c40010710125060640f130400000032030300c0c0a800703080d0300d07410b2480032607924 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 140816232 1250 140814982 140815049
    0x3040807090f02091c020108010e0c04030803040623040605071d010c02030c040f0f150b0304080c250e0703060302060405060918040c0e09060609060d020f04061e050a 73
    0xe9800d0000f0701c0651034030400d60002c08105c100c81d1242100c2807001400305881078001400a04200f4200841d080581d0111810b0300c0e0000ba84a40300e030b03603a2a00e04050700d0b00340c030702c0e107003090342c481c5175045105195100300e004071721414040c01955a403110072268082c2000c0c840c8501580c44c005107400d54041c20950b11594006402c1c1c4031662403c1c070100301a510b00182092800f42c1d28400c20005050301d100c1e84440c6180b660661041a10701402c5a65600000d400034255400000d82c0c85d150741410041507066586904081d83c00407088540c102d50f243c0c0c0b0b80301e1345004182180003e061244a84654416254000c0105050504000038000260030070000c487d0451140c0c1d51113508148204541441350340700c1d030707061810315052058801d440e11001c1e001494540c008024804103944041c0703032581c030003010b0b103003200090b40398000141750f4105404142c9d0098507160003c145841c90224090200007080844481c0d00c1e510418040c031111684100009e2040c0454a210320790138583c644483d2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 140817482 1250 140816232 140816261
    0x60d03120c0207081b06090f12010e0d09050d02100f050409050c070218010b070b0703090b071713020a03060510230102120c03070204090303020f07061406030304080709 74
    0xa03044010342203811038100c101510050383c0300301002c201810040150100105140110b030104010303883c0465040e004045500e40b040c41d41c107184c00031980754005800c0341a58103800900615410700c130725a450f9618041080c001030ba407144042041e0900c50440b41e0101c0c2e000d0005600080040c104407200d00b00309071130a0401104001c000313142d207524000d180c01410305a003035990b01d16403441040945141e40302015502003940004004c4580c1c0001503c80c03075a0080301144032079a03a0f103001c400030460030400030450b510140078080c3c016801100076092042010b91020036803101081c84d138003081c0411000b9444184481d09000095864211503000221000c03185880d9840310101a001c5180d20314146240811404c00005580d0420469041034043c4200170316200444006035102d2240346c0004e8052600ca0b8104010540b090b030440e02c8005040030381c161900407a10b005409007d00a0103d50503040f80c0300843c0c06490040100c8040700d000310014121123140c509824080c0c00110082200d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 140818732 1250 140817482 140817497
    0x30402120705180f01060f0203040308090a0e04030e090903041a090316060f0e060703090b07021504090903090512060115020705060301260f100b060903030d05010302150c06060d03 79
    0x4030b03502d45031a52000c110414080f61401c1c68000302210000030141e01034410401c81010707039652560040300f21015250000f1510369540791760340224030503402c07552000303000000d03107002c0105060348100c1c004d54100303080343c104110352100940242d40e03001e1070049d038280c646001070406071010300c980100003000010b02a101484504600019081c1d1294001800314203007140c49102141c0c0000c0c040c4907100e084488600704111510001c2000d8518090301c030700000300003003180945d503920408000c4039000c0309034a5643ca88822a90001e4003e401049001c40c0c0c00c640085190301d002411044011010740040c482607280c03a0301d00490140002c000e0056004008000c2103d84441000314041e05602d0000c402c00c0d20152071500e41083d1000d091030312504500c04c5110b0100022801d0340f43c00d140c0b050046289031000c4000740280c440c014003141d051100007905c080040711600614100c9000311807040c140c3d0a01c442d408401e20900c820070480d42c11120010390145002c1082408030750207032a0070300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 140819982 1250 140818732 140818739
    0x121020a0504020f0702120601031110030b0d060b010909050f0f060d060f06030b0c1e0a09050d0506010311060f040302010c0f151d031201090203090a0b040c030c0e0702030304021207 80
    0xc04a0f4060040002900c000003103400c19810001101c0047c403036420b004044a6165441307141c40042036200b8544510804400150034074460342125030407200090124644041324a0102c000b0070440e01054003150b420702000802c9034451040d0b034032560003d0f00f0b88966540b40e090804d80e00000825195014842d02d5140010411901c0703425060f01c103a020002d5610700b541403400c00140000c004440c0040b0800c406204041d9100800021108040740c2644615802d00300303030742d000150f801c4680c000c500c40c1050b13800c2c4100010740300d040340e02a01800c6841c642c40c10900c05613100d400c4104640010801041005502c039011320b5905500604445030541300990b80d108528070529880c40409860761a00c581404902580c0494401c441d0011071518000b085840350300141480b44044450380400000c0200c1d00c140010030300598041d14003c554901450300c1012501580000d5402041c862070100e41114a00b00710b50107040180c00442c1035076219820481e2008600c04507522601038802c000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 140821232 1250 140819982 140819989
    0x80705061801020f03130306200d0e21130f030c03110103090b0a0b03060c030907030f1b08250501080a051807090609051317070602040e010b03010602150121020a05 72
    0x406d020f55080a031824250b18504040c819122000c2c500107a07401c00506840c112000741048a0900b1111000814108503c0c0034103400c14a00d0f1040850058508280c14910b100c00001801300301c5c8101c02518000f40ca0b001c0183c840d448901004040864804090001c5070300d517061072009140526022078004996961102c07654025a11080f107540c5405003030031b0615042c049940c1c4254131000850030351034050001e5684010600c17000c1c101301b00b03c0321040c0500a00d00000c2600c400354880028003e0341d1200c00c9651071104003c540304000e40010301c000ca03540182404c038102c0c2c00595a20105440b07540240000b000302608201c0c60071804681d040c2c06640c180100d1008044ea65000604035142c05440070a50720001c014411441344c2a21200c001403848004549200d420140703d83c03244141e140000003441242c10401d003d2411400000300061503000850580b1190707801da03103d40e460340d223908010010038000c011070801e205888017040343c540082e050405000801d00c52007aa0f075480031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 140822482 1250 140821232 140821237
    0x30f0b09120403080403030e0f1f050708070b160f0903080f0c0a0605070207120c03080c160e060a08031e0a03060b0711011e140a1205130507080705061801020f03 71
    0x204e840c01030200d4100305160300035903000807142c404d4031242c81060390b080009900c0422000c2c50440d0700b924000d44e641c181e2041081c1c80c8101d500c03050907030b5180002e0501300205001250010040c0e14881e90b041c0d000c0e445a0201501c0c0105500e8058031982156540d100941103520410719201040c0116005044108001646030b030060800040c2400c040314000c0c281600ca41203a070140d02c040140100103200b0903410401c4a402155250b2030305240851a403d00c040030a41000400402502050300401c45507401e00480040f41c003650712640e034643e8113860f03014418281c00e0035024a04c0521080c8010b100038040756085140029040d07840b02c17036004540c2c10a220135114a01900305029065800880758084400081d030403120582c415540203081030ba42000c80f141806c0301207a002c0b11280195072003034010104200911052070140349420202d1a20310782600c49200300f21000407880404510403085e0307140506018039010000c42c0f03130b00d00c00a4800c1e4a60461085816065a0040a201 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 140823732 1250 140822482 140822489
    0x10e0f0616060e010603081801140c0c0315071d03030c030409050a050c04050a14010302070602070b0406141e1305010c0801090c020304050a0306051015030c18030f0b091204 76
    0x6000e140d1126420100200d0781c00d107045120f0b41c1e141070fa051000c80c8448003a52810070b04c0840301201851080012122152a440c002d0303452880810101c60145c1c0100d98002405002e03030403500d56441004051510f510183c810302c000c030f800c0040b140180f0300b05c0804450340f034001070210307407500e4402e80380c84d45958800c1d03114040c20b03030f80d560074044090000c1c010560001000450035041508040c0020503141a6210b5401c11034085465441e040c2d020fa0150342504d90880003c42d29203402e400c2c00c402030710b800c40d01201d43c0c80c13800c10900e1444201d0304507540940c2103100494042e1210064001c1c4a1001800315076044c00c074225250002403090140760001d96080e079401c003c03940340c0b41d859425641200c042c41c1c00e5420511091085032107202001085982205006c01c607500ea400c400d00044403da003100c24010000b9001d018070300d030144c1200414081c15500c006250505021a1041802600000708040880d800050220b02c082a2407900b01000d1020340b51040c1da08400b1043c0d5911561 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 140824982 1250 140823732 140823757
    0x1060509180105060a060f0513050303120105010806010305040c17010f02040f0602070801110a030c0e1224040203070603050915092a0307060f020703470402010e0f06 73
    0xd8418001e8402e0292582010055809500b218140b007000380400700d06444410400c1004112090201301d12584e5800400c405401d8903075881803501310208084003402018045640c0001041140d4443d203e0103100b1038000c60f117440c500e810903c02000c0c00d540300401c07440d950340341c000700304c0b030080b8038801440202035100c1680d601703d2800d5006802c0c42410b6000c400c480c0d141042d103c184000c52001c44822400034940001e00340c240324001c2e100492418030990700710450198a1801d010001141000004206003070408502600380d03c41c0e142d403080310001e400d900052420002e040c02504191381200560080e941000300c000001c21031100111030b03c482e20340c40107040c0c075020b200e000010b05005508400700c052204003240843d55900241c401c55007001504403080500c5072007400500702859101c105845184491071807405480380404140018400650080b00420010400341d0142c0e8031b2400606580e46c0c6e15001900c2000e0b2284e002a04059002002041561000700903d031100054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 140826232 1250 140824982 140825011
    0xd1a04030504061d0a172508010c020331150809100c05071b080d0c06110337060609051008090a0f060b0603010e371a04020f0c0d0309080f070501060509 67
    0x60f42c4235080d40c10368079a48041d500100031032200101000c0500719600003c0b503d03c5624281185181d4511090350f101c0c030310410300d0400406031564052401e6021740a0340e0116a40c04000c81d44900440c0c600c0710102012600030400b45001907a4200c03a0030741d80c1c0880c41c0c4603405a075108a2281400c08440d03851f00060759150440c420440310344102c0450200d480f03210707410b600e01090700c0c40a2481354050200c030007040c106144020001d01242502241020300b003403048592303a8038068403641460150702d219051144140356141d200c0c2e18000d104441c414001c080c0e428041d11403420010101741c1c162030745525500c41d100c503512100000d60003800084000c10300ea2800b807407400240e845080642030034040c01c0340301e852182a101c00a642011038818000348200c4080c060200c206280c0c2e6407103401500100700e038600743c4003030009071911518000c01c0d5040210008821001c80c0d6a0000c010007042041c0600300100f1800009415040d200380c0c0001202603c8a00090010400303c2d4501d8040068 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 140827338 1106 140826232 140826239
    0x602030a09020a120b090f030405010503090f01060e040605090d0807030209030f010c0c021503060603010603020d0906090b060a0b0708090d1a04030504061d0a1725 72
    0x600c0303c0441542ca5103141c00c0c035030500c001580c00b0034070350001440d54100401c8074440c130000480a980741a00b4180150741c940c0014000c0101c0303220703011100080e54030911500c405481e5074802004185014039160090741d00007002d807885a00041400301c0d030319030804007441e00001c1e5420007585078400c0b03c01180c5410316080c100c7c14251300f07061112140e6900060705040041c002d407081d0002407003003442c1052714441680e01540040d8100010820380e807080d8041c0100388111345d00400c010f41603450b25801d480b21280240c03001e09d1000d040c00482c1c0b03816034584000b854030310441414101252111a801e0050780c105e14011f42c801052107040054440c40c0703803800032100d11a20020300302820002c009030001e000781350116800d0300000c3c2150710b92070682c002a41e801000a440c05041c010707071803c900007002444640c0c0c441c5884561060b41c03110041900e031030043c80c4060f8a5440e = true := by decide +kernel

theorem cover : BRFrame.Cov 140647482 140827338 := by
  have h0 := BRFrame.cov_init 140647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 140647482 ≤ n) (h2 : n < 140827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
