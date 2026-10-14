-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3574
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:03:38.919539+00:00
-- url     : https://prove2.me/submissions/394e90b1-ebc9-46d6-ad94-0970b5c7c28b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 642625899 ≤ n < 642805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 642627149 1250 642625899 642625903
    0xa0e04091703040b04020f0a08061b0d060b1908010e0406091b0602010c0905030d05090114041e0e1311060c0106090c03090218040203210d0207081c060e070f0c0203 72
    0x20059010710000c9113241400d004210070300c4802c490b0144108103407001080300103404101180d100501c000f03402e1000e010100e440762184030b5860b580d010a40391800c049030389101d14001c0c0061380030721000310786451f2040c1401c1d2440c0c0001e0013945e44140c0c1510000b0f00190b031503000121a0f03840307032050442c0141c01e0502854004001d800404c09030351038038403002c101c41e442006c0d0300040104400602c00c842030404060300521400d2400350400c942551140101040c030001c45000344103580d18000304802100801d144d180e601d010b400030f014682808190388090148040c03004036004110540d1036189001003041580c030441d0118005c1d500e80c0000241200d00d441014000345c100c1c1c40200e00c600c1c0c280b0400801d00c031241000603800301c3d864244005038074000b500d44e83e480c200c0d80040c08a0034200ca0340d0300141c0a80621800d640d4000511141003002040c0582050441a070303560040c0c01d4140c00c030340191a41070003240d449001c8a000107588a00c01e4011500c03070511400c00f0301c842411600800c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 642628399 1250 642627149 642627151
    0x4080c09090106180624080727150210020c19031e08091905060f0714030103031e030b0d08030c270a0b0a020316080c060915010503030a0e04091703 65
    0xd03540540da4241045281c1b2000c6010030070184a010020010210316005000da00b0f0160104040000700315a0071034206104581d103c6110151485015003540c42c80607c040b288107041c00c00040c0184041c803c01000c03a80299403c0c030380044007070121018100310b1440207039040001502001500c080c5c04982101c0c1d18134000301458103658640e03841c07401462503072030010312031400c0c0501d00154180c08080380001c6001a0400003007035120f81c00303880e6040300f19081c60300700c2c040c09003261001000008060300f044145803400d5105600c441c2061101074140c040303500c15030600343c003c4848800003001512140c02950721903628848582400c2c4100780d00500ca000303c0540500890700d01d08611042c0c580410034800070140d0070031140c0b8011920304000e45901550510400042c0e4036040582004500c005860030280030504030b03422450321030300c8107036904901280701c842c01c582e4074008585ea080220486d80030400640703c0d0a0640c4410051000600301d0b66011740381c48060f0160b11107001d094034011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 642629649 1250 642628399 642628439
    0x1406010f05270f07140a05030f04050102040512010923060423070f140306010b0708130e0a0c03051b1c020d02040303020304060822080304050f071706060604080c09090106 75
    0x300c3c03460104030240035106a40e4580fa05528103010040101d40d1080440e070707001c50024100d00c0980c0791440d05a000e0702941e00103561100c0703800c0844064440540c0f04880003070052040d110301044070140c496907206120300c2412190400700c0042c0205482100314103e5000801800e0210940d0505043c02e050843e00082c04a030740214041050000c078103407009045800b2005040c0e01d505d020b60310040740c8954140100b095a000c20740720500d9103c070820703000403d02507645500390328020310080024000200035030080b81c03814001c1403442403a0524000341106000341d00b40b4040c035041072100ca02c81700c068110321890b02001031001440c00c0d40050001940b09400440c0c032107082010103450078600403c191002a80c803d140d00104813442040f1014030740114806a40e0780b120f040c200c0c141003404403680b8440c4500c2e40001481010308039402c5540c2041020741d9030385d8403070404125480c4a140309008455100e401c02c20030307914000e101e150b00400c000c000010704070750782c240007400e41d04040c403e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 642630899 1250 642629649 642629671
    0x2f040513060e0304060806100509030d05190e0922050a1a010902090d060b2d01020c030c18060a1a030712020a1e030e060903071406010f0527 62
    0x28410410203002d4102c1e0208914059030034542448801045008024282032040030119440150940180121665030401505072030794181802c0740508030f68080d40c4444442014050030100f11481a240107842040040041c10702e81c541e0300c0034241c00d0454802408410300240c00c4c850002d50100702110549100c2c504500d5114042c41765100100310507849050a1401040394250390b5660480380101260301c4540090411a0000841c09103050410102c1c0d071202900d04c1201d00090444569225940076801c98510300407507014540c40342080c800c1c180e0004004051803000034000300400d0307804100130b0246005261366104080400c20b5000410030100f000100784000305601c60701603c43e00b00080300c25807500008000042c005072800301e41010041240c404c940c00d2500c00e0300101d5001c4296000c40d42c407400c1618101e42c50303900c880030442d803c0040ca414185104004145141266900400d0300d442038034103410700c120100706440c8a400121200b40340c022412484017228028408409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 642632149 1250 642630899 642630931
    0x2f06040209010f14100e09040507090e0a02010504030b0601110a030f021204030305180103020c010609020c0c0a0b03010905090c09010323063312150c03042f0405 71
    0x61007150141030b0001010b10a203400b0500c0102030b0246444141c0c4001e9445004040c2c2846084803031180300c07507085510820200910082c05400502c03101078801a070b1041080340002c0c281d2607594046150000e0102d6402c2c0b1040012500d8251059800b04041c1844481054150303903860070207104a5049000c604085640d0401a130b0401524019070008a003051419055450140c614003e095100d424010302c0c0300624083d034444d4041e20107400c001c00080c04040c0c1c4911002c006074006038a1913040c1d00c1840501f00742440d0200c01c071802c0307882c4181c1c80c52035030b400c1a2407074000d400b00900a44e503070302c14028160703440e8070380000710390003980100f03100355294904286d0000c071004255150603040d40810144401c0c0411040e50300220342882000c4040c0e10001c442c400012003001400c10342c441d00c080c200b803070810008520424000401d4410442c00d58038001074850600003660302401d03a0903140e0103400d010f10315003e00004100301d0400200920210380024081c0d0b081140c00e1005101c04070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 642633399 1250 642632149 642632153
    0x801030b010b03060114070609020913063606180f02040b0433120c08120c0303010308031f08030901140702180705040305011401061106162f0604 64
    0x103100c0c007410702c0c0a28240366040002c0000c20590b00480d44229012002500b8800c101c5240e1010404d01da020300b044a00e8a0070a138480910000288207640203401c02400105ca64007984007488032040d0154140045150310068000c01099030000f22807855a81050552202812403e0341819104200e940c07848000f1b4414001669801c0c80d004c0e000d01c0c202280703481c011400419580c0d000480e24002c000f2008102d0910052003000da010080d1021007000920502c02504204015214140c00320380110b48600500025407107460a1070300c0c1c0740c10034030042c00040d540da0004c5400c0400700403400c03d10105010029900d92055000000a2b48000350700c170115601b28604005640034030259608041c09a00860324220100c2d01000d44e41c1410000205441c3c0103030269006581c22030020041d104078120300001c03071a000e00070780000c500e45604c1c0030a9984005842340c410079a11030402a8501000c800f0385010300101c051500c1d07410500300e109100c24580c2441a000069417000300101d080c64 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 642634649 1250 642633399 642633413
    0x2312180102030a08040213060b0f0a09081911040e010e0a11010306030834030c050c09070219050c0d1506051002030403080c03070606060c02010201050f15060c1c080103 74
    0x9812000d056410a100203440c26401040e899070158060310b41c628180c81003a681801400e0301d4014005440c800720306241005810006007481c0a15621414001e0b9102d5245903600c406014508031040c210700030000001d01010303103240da840005000800ca440340e00c071000f401e5515072051001c945d48890141014044045101c0040c103800703003410403800d81182ca40907010300c10207141c58600458070101003e44944044000131020b4140b02468000c6814500100711300d034510000e4030244202503441d40d00c1e280c60240180a40a40e0b00204100300b00f000b00414000108a001d41d51406aa582c40c56070340c41c2d603400220140c0c4120000070008004000c1403003194102d4004a004000070130700b9010342600041214241d980141c08184c6413100c001c1c8251451003050b000900042c144400020059048848002c009200346c0080c010350381d1b681e01903403010508545206508030850040d00f0541070076402018040e10b00015101362044e0b20450700d0000717901c802414000b40300480100280069 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 642635899 1250 642634649 642634687
    0x6220b070b1e13030e0a050904050f010516091211040f0209090a02040503190c150305060909010903080613020403060c08040302100923151824042312 66
    0x2000c421506142062482c08158000c3d074003004003405811600c200740c9a6501c10035000034800200440201d140c54602191070742c40b080c2e8555070325800d140c0030507000050105141d070861016554000c1d0309160151001140036101c2040c1c5443c1828080e40134540c459000382a070303003071001c0e0001d40d6031200c1405111300348000030920f00320175206110a10840d50046440c030140600c01840e490008068246040c00c1400b660000d41a158a031040b19001d0703400d504914482c0344101c513440515920040d486080c0c0f4407080c2c00400080e2103100140103442c160300390403a070906c0f2800060400d901c99a4500c1100e005000340008241200e041100301a4100403400070341d02000d40c18030810407107940e030641d001c0b0a4406c40140311003400501c0d1844108101d0000110003003404809036040c02d4070803004a402e1408140b0141c0602c2180d07968629400303442c90440c40c01a0407040c5070f980c440c0c80e03440030181203c1e1701301d40d401c810710b88550702504200310b41162010a02807803a600c050304108680b040c58 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 642637149 1250 642635899 642635941
    0x607030c0b1f081c0e120d080403090b0909010b0a050d0510170d05040b03060d120e010e030d14070218010e07031508030a0c0213020a08010807050301020906220b070b 73
    0x1c40210074410190000c1320ba4103e1080600b8110301c941018800210340701d00c5d140c00e0000a04c101c00c003020925a004007420300403030107621107501d03280c1c9611005516108000e030302908480004010081c0c02000801030024601520f03041d03003007000202d050010b95400351003010320810142e40c00d0280e040c0514130998401c045600900c1c4080c0c0502c40035050b40140c0c85080e0851a0200008a80341c49061020700b401e64071580d10600c0a02c0d80d4400b03080703c41440d00c298000b80c410880e045483c02d00251000d0070980544810240ca42d0903807a0305000d502420089812968801c4a40d05000c210000c0d0350180091030310002c514600032000508440e00c468100e884000c2e11101040080b0b004070440390220300b9454680d9480d170003400492100090303551000801c41c0700083c1d003c0020b030b003c1100b5059864540079601603030b0b9100101400e0380038500341140e010710104412024903441c00c20050318043ca0400036105071781c2d2000300ca48030390001c010a0f0382c1c0c401c643e02000000780310001c0e00c20101c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 642638399 1250 642637149 642637153
    0xc0b040b0d050a0b10030b0102100e0114161b0c0b040b070b0903041d100e0a06090e0a2a03050d110c030d0f11011e0c020d020604020d020607030c0b1f08 67
    0x900000004000c0c185c6200f02000345652400c45941c0359200744280c00e014a06200107020b07038003501005a00a0641e40180034903180358102081d100082c1000d941c3e00003155503610070001020031580c05618004c0c01080300c100041304c1d4001360305203078200500000e12488000d652241c0d40c1c4d042401c4000d800411018072034008010a0001104866000010519011085050790341e030031006006d2900a401c400c3d6490398403400c011150000380c0222081e43c07561041032014004241140c0e80d141d910030401410140040c6c8006806c5d081ca48061540e660307280103008000e0350701e8481d6801d241d02e610942c00055202c8107202c1180303d003000700076102601074000b04000210404000c200d583e05002c070204006114a041c14001c600b500100780300c1000075a040d010b66032510b000801015802c84003001742c0100074003d86514004501c89115580150900301e40546580c00c0001a6001004c00c906200314010500086072060b901180f04420801580034034444910204940c0035007984144942d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 642639649 1250 642638399 642638411
    0x5010504031d0603160309050f0105220c0501030b010c0c0603050f15180a02090307080d08010e01060c021c06050a0905191109060d0206270a210c0b040b0d050a 70
    0x10751560f1080307a92004e4511021440c4815a000c101d0191202e001c0c085c1840c4500c20750304c44e0440041d40641d0080302c11b50185074500107084040c075103007900c410000d000e40410801c1044654040c1d000303000c2240741490300070f9604e051541c8481040010b82c1090300080c0c0c4e50b0741007241803000964041c4c1c004240a03400014801054000781500c00202081c190f0b81c1350138404aa00d1010540558805110090a581c0d90303603100c3c1041e507540c0308900c55140004400c0c0f00001882d580b10403019068030364564030b2440210054081c48428034024501d8a06990a407003080041796991007000c0c05000c00c010003180140441c140f484c41c00408400b2109003203d6681120b00040d20b10013070059216080c1c4252210703a54400010364106035a84020307400c102c000070441c14a122101d80302d44a50a001d54103540c141c0d0440074170142d02000c1c040c0000a05a0704031545410003101d4004250a106607100440141c80b81044141c1da0866030001c10403c0000c916608901c00901a081c2d1100b2900e07020088 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 642640899 1250 642639649 642639707
    0x10b03010605010c08090d14031216081b1e0a081f050117040f05010c050c0f0109022d1c031215051002150f0402010807140d021804090501050403 64
    0x30b8401c8400d80c6c0e01c03c0d0140145403040008807052940300b1f040310016039440e0740000180368002c1c8411181071102c0d0034016000c010079402031020500610140c6a0b45404500101d03210406070712018484030303d80010311810703560021900c020406c40103103659200032400e08808000180c28016080e8511400441c818840b599100034154401c5e0701803660b0b500c040d11141002a5560f2084d0405481e03542090054100035070800018000010854100c035480014818468200c8140305030082d0b0051121440c5008241c00200740100300b080781c003c100301c15400c4c0c40010000d4480d02c0d003110042c16008440414184c00c11000200030b43c02d82014044a02c1041b810260030203030340945440348008a04040305248200030008280001540ac500c0c1410311400118085108a400300d00207605500041d605520400c100d00b1506011170350301d41012200b0883d6406501705124103110442408484401a07441c1d014603a90a0300460001901d800d150030010801054a00080c07100c0d0908030201003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 642642149 1250 642640899 642640913
    0x60f0c0302101a18040309120f0b0c090927061302061c020a08010e0604230901090203160f0605070503070303090f02060c0c03101e0513080a02010b03010605010c 71
    0x44000780701000046090403031504007940c1d04a041c0441d0030000032402504c580d24140069400341d4001e4543c901c440d55119120070710f03085140c0340184500402c043e6540020401200140c00c190f5103009a0306003803031100401c4405204403800b010032411a40024250802c04185201c8078180e00d004d0b01042c070781056095000c0c035220304002c0c064030002400305d00048024920481038240d844056654007050080100080c90a01402a003140d104000c64580d103080d100d070401000c0440564041d04031038025000d001c10b00102a1001c554075083e411006a8051151201e18683d42c03400c202c595082644071300b10015a60003240511400f0440e42c0e003c0b40002042c0c6009917450718010034885510319000907580d801d020029082100403801140b100d03000300e50701d149100140d0440764254090005801540c01d40b40c052030f1135003180039014200101507004640e0292020b05148148222036130b0310380d402d600c02c021440c010f075969080f581d800e140038000c14005100910b00fa019a40302038441e03007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 642643399 1250 642642149 642642163
    0x3040501080f10180504060615080411041d0f0c0d03020a140327040b01031104050d020d0212060f011505030c0d0617011505040504050303190902030304060306060f0c0302 75
    0x41c01029200003d622100c103004a001401c0b2a0000c0d0103c0c0030854050805031030300351003c90b0b070541803050128103000c183c88a02c4c100703401e42d52408540e80312501c03100c05a01c602480319801948441465648509c681e008214400221000f01a560800c5c07001e0345c140030421100510038040d01c00d4120100e640055585070854114a440300001c0300c9502540c035601c01c0c074803035420b409030101150326403621045110305070180c1540c003800b8034a035150046003124030402c5061040203013480f0a1000d410401d0b58201c109101074841c03880c1e43c8040c0c0005440c1030250904010a40c010401c2000c0201c4180850740100201807415003007820002c0c0c0508540001411060f41c500701090501c10091140c110800a1400c042c03201d14800e840f440040c083d24491200c21100c5080343c4bc00038490038240b050700c7c4140c0c1c10201944c290740310b540f03101c01080020072045090729202c801c0b000c0569001d1006000402a507280090030038a0000040e0601d055241e4003028410000260000321790041100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 642644649 1250 642643399 642643411
    0x40609090b03120a110a0b01091a0a12020301090206070605010503070803090d0311190503130b180f13020d021e190806270703110f0703052104050109020f030304050108 74
    0x1d0f80d1581e00c0071008550b84100e0500c00f080a204541c044800c1c0840850f945040e5081c606042c0070350341460515184030207141d540550044401c06007040317403803844071682120702d1000b000400c0c00b1400c0d80020301c0d55004030800359010340d0340d10010450351030200300000c001c0034518090360070940d655002481c5130900450150a100e0700000d01c50809106210005900400d0603e40b00500744030308200703940350081d501c10380d03034107094100100b04031000106580c80025a00e1400507403c07400340503c080c144089a030a600489103c0703440d0000c0b15240040c0c119921203080050300d482011081c01d0285002500e04800c0da24100400d182d210f0240c02800307150392403810303c160f00c3c0c0c40d04c1c0085505581510400c0410030011040c19802c80300100603d0301030000f550b01841151140c0b00801c4d0541f282035900c1070031640c00c01c01c3c034001a004501800e40860001140092455106004031005c04100d0b02140d440c3d40d00c0750010210300c0c1400080722a42c8040d0015030401d4200780010b0000c0b680a840 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 642645899 1250 642644649 642644683
    0x6080a030c0809041b020105060f03120d0213050a24030207020d170c0a060510080f060a0c0306050a1502010c030203062b060c0f02120f0405060306010201060306020301060203040609090b03 83
    0xc409040c4c40f5034000f000c031200960f00d141405034004200a009110941706144280514088006280f07000121709a44c01e41d0029000d00c0e0160603150b41c402988000c44403e08520601c400040310b03030394248c2e0303480101001c1415803103800b14aa0700301e00c40302c4106401014140b041c003403d00940c591100c4842d074035510074039010000b0f0501010241d54040d01c2103600b01d601c5007000c0300e0b081040c1900b044e4018007522200c1a0400d0711031800588a0000d42d103b03020340d1340b000002503050784170364004184060090400050240e22030300400c200e5606038020404e440a0000c00e04190313682481108641005842c0460840c1414000100b0003000c1400201c1031000d110303c4100503580840c41c070714185511480410071440a080050f224030031510720000940100c45400c6c0c2401051421206403642c0804414600341c00c203001c100d556000940b80c541150340ea20004030001d42d05100641c040d000c40c0d00110b441f20319080005122180e40d42050758800c1c10110000c280c0e450010ba002020407030445 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 642647149 1250 642645899 642645907
    0x6030204241806090e1506030f130b040c060210090305041715090a2109060318140601180e0a170f030a0212090606150a0309081c06080a030c08 63
    0x408680703862540000c0ba0060030503050000781e03103070800303185070032078400c0500c070040e9507150401c0702d50032201074044503040307a020400141460f1400c0001607020241004460003920f20303441d00d10540c5003c85040719440850b000601c0425010025280c1ca420584002d10040d88a130b0703001031860046200310300d401c24155444100340c0c1c50600c0200307101441c0e803c4603d900d10740314004070380da00c14103c001d80716154213003800f02a1640d45482104c00d0281c42d2100c25501b850614101c00034404d140740c1d4152111500b1843c80080e102a56000008804100500e50741d41070440542c8412491041e0720046450a10500079401c00414880d4809421110580101d03020040400017032103a001404c0d9a400c001003000f0b043e04182d8081c0c0243d00100c8000b0f0455961100301d00ea03103220958108d50300071880d806450a80460070011300b508400351801048285d070070356038400d580e04001201ca0090306ca0748071289044150b071103075070010890f1000a1180d0300e100d8902411005c604400035120f12800a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 642648399 1250 642647149 642647219
    0xe010b0d120e0613060311030c030c03060a0509040302010902011b0203060c0c0f03120a050604050915071b0501091e0c0b030c12011829090603010f0c0c050706030204 73
    0x20301d002d4080301c40900358a0341d500d0a4040400072880380d01609001c80c2c44e0160041c4018080c1050320311070b80d0102c48003890b45c3c030b40ea000403a8a4100070140c03503101d10f03404404103003030b2514000a03014501c690004501c144103440054078503520721948035030112803d941d004c01342e500090340581080c03a801380c01e9601c1d01c3d41c0c0b945c2410f020042f100e802c6103100000f50340c214a9280703c0e04500c2041245800c2002e520b4840400090314030644200d50340368001c1078125000152590103507002002c9040c42114044a9106180c0164007100c00f80da071655504811000e2000c5040030301c2010000c1e00100c480c400c0c166451400705100b0f401a46801b1401200203849680c83c2d200b00c611111100740101455a0f40c2c0c0c000c112420500c510401e06c40b400d10b070003040e1118903607508102421105044040980e6000c0501c48403403001400303968159200c14100f40201c00f02d104072505084c1d40c1c0e0b254058418507041252501c204c81c0c0c818010103104010420080035011400751299040680742078500c1d8100b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 642649649 1250 642648399 642648407
    0xf091008090c1c080c0f011107030e31061d09060f2d07030e0705011409010c0b16170f130614070503071206030209061903060f02030a0e010b0d12 64
    0x103010b000707040d441e000500e5241517600044101c021100c0c4030090106901207486941c10b801035240040100c2d440d9003d030344140c82c2220b240000394a0f04842c030300501c1e0226011510704000440d5001496541311420f0203a50308510150340700096000c011102800d0180007203540341001084d40d203500c1c050502280c01d440a2800403001086024100a002c03880780000d14001c204c2038030301d04c0100b4900300381d030b00c0c03124008903074142202c50586810702012000d03060142507034885650b15040106603400400055a81c0304414011992140300c46c0388440307011800b402a124030215a040c3d800c10004001603500c0d1000700fa540070910004004503c0b54510300034000e40140d5150001429400382001016544400550701c114001e560f11030760703100300249031001c960716030101039000710002d40021b0b001d0500d006000004100b0360700b803010b02c03540c6e5142c1c181110911090407503000d800000b40482d1900c0d900405110f802600000c20a141100e0005100070b82440c10080c031b01c210822140c09400d0107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 642650899 1250 642649649 642649699
    0x40f0302060c25090615020a03030b03190803010915030b0703200c0c010e060403080301150527211507030b10020304091b050703230f091008090c 64
    0x303c0d61154001803030040440d025006501501c0a007a02d001d80000d81021101c40248048010b50045c081400f95914120084c00214259a1b018400e04184a952040018503580803d018074034041d125410b03c00c52005640c10b2200b51b501541c0310b1035003807020580084010b030b0807007201d0800064210440024040d07181800c2d0f952a44e11f1030100b07407103420040102d0851901d41e401d994200c601e25244007040041d01403400f001c0c00301c00c3c003800184004182012464040e000d581840303030400a04080000e1845070030724a0f940c3c044c07007074990034101c2c0c10b01914920042070400c80b00c48200d40c04c00c941607900e00740c03942c5083c0801c0b08070010910180c0a039005888111015103481c05031b8154000180d0b13a035005100b056100c515007892641d01044030080307038000c5000350351083d207003d050f9141190400c1e51100c0d803280e0003504000703003461614504000c0050b9048444510380f00c00c031900c2004043c415003105007003400451801c10070480350120303000314103800c1100c2d0f4a0903280e01d41b9001100c020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 642652149 1250 642650899 642650923
    0x10b0a0305220605060103060e220503090301050c0c0c041b030c1701090606110c0a271d0c010903030f05071412070203061005090601030203090c0406060914030102040f0302060c 78
    0x2c1c0307280526050007410740041303120755030a0302d00740b1604da59000b0302c020180080700d180002d445070703071484030b0382c3d0500e41d050340380341402001182d051105000000342100c100362410703c400b000001d040b00410350f051007801d150110407141045400c00c1c400d0056802d0515000c0c100405684040721450326004000500810784102c010040c0c560310340300714400801d220f0050401050f50180e01318501d40d40050403001904011300707020360032444c1004505254210195034050880c40c2c940c030726602c2ca2984101051a8012000381041c1c140003100359081030200407a040c10010700c0384061000c2500848090781c0d0b4202d074904680d441d00c580c20200d100ca0380444503284640903070040f50800c00d1501015190040c000c0342aa0ba980e00ea10711241d900c58118400c0c00e4212504e80c00041c807560190b0302550707005814000742c6000300441000a41260003a41001c0041884048244480241e0701031006040301c0640085141500380f200ca030020808030703c0000c0c031880d400194003052000502004e40460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 642653399 1250 642652149 642652201
    0xf06030f0e01061514040302100c0510020304050115080607140306010e1f090b0a090504050403110a03021606050f031906050a030606180c0c0f0201020c0a0906090f05010b0a0305 78
    0x645580828120301d40c4d0038040c2000900130340321081e8001a0b00700b01c0f001c5070f600510f260394550b58441e0030f0302c8070382503070209881a008900100503280c0076400103600c1140306000005540360603081e51038074662030b504030407002d40c0020108042c00390040c940c00c48030070011010f5500c0c0c1d039031600125556840345030a0341d00075565500000c1d2402c40380f4540320b48040c440d2070345c5040944034665003585000385054400041c1010b1020031450501d0f6001c41e4000307000f40340c151003084c6417410306441d000703090b00200c005a1004c07802c120240d0803c041440a0308c12440c3c164a0001c06c00e030501844d000113850000051443c02c04445888140e600800050034058484240e40b079403800c0c4800108128443c806039150148aa420f4100c0a8400c120810307a058840f40d05003507440d00c0311b803158041e03020100c2c198803500e0308030b6000d5940d0488140003400c2ca01c402003140d03420b00481405503003181284d01c080e6400c260052240c1d19200e020303a0f010fa1401d02c4d000035140e0701d41080b10103c0c00d102519101007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 642654649 1250 642653399 642653411
    0x70807082a0406020610120210082a0c010f020309070302150c01050c0c010b0f09070c0f1e0212010c0503040b07050d0603031106150a15030207060e0f0607090f06030f0e01 75
    0x100750007041c0d140c41140e48020109107103550794183e0700c0341a8442c1f0300039441040b401042c495a405444100d401c00400750751030410b01ea611001e500400c050700b2840180711001b29054000368000d0180903c0745103421029821410008001582c8010303501000b445081040420f02c00203481005480011201e18000d008a0800702c50719807560744500c10800d599402c0c60340c84046414820340c1c0b00720b50720b40a0600d070602c0c1d480c41c5007182d105210310000c6440b9000d409a0f10049004514110b20700c500442085a400c1ea2a10400803481d02140100790070f80d062504540ca0701d0380080c16641c2c4107402600c03400481d903400004a8191282c000180d104501d8404040300703140d88848104a41c4d40e0040841c3c69544a2044d80c522070010b195010b5805007030400b00384418001d40c10012910b842d58200541407480319504c01042c1c810344c03020480351f03501c90801140d46a2081000c1c0e40c02202901785444a14244501404403030102d0181c1400e140c3c46903541c032150151a80212804c0366003034020850 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 642655899 1250 642654649 642654659
    0x301060909030908030c03160609060c0216141e0613030c05130228020c03070e06030c06070f0221030d150902130504050606091c0b070807082a04 64
    0x500d2100750075000104150000300c0d882d00000215030fa0082110002d50401800c0b521080d0000d40780d80f4100c0b21952101c00c2a800900f10740204001c8800303039000360244480d6003100c80000c0716181e1200d81c02e1002c480f10b030300d0640c449510707444490000384000f0803540c20800108245102d0340c10150312248070184008140440020103c05403901215a03a0300300034000304060a1780a203441031850494031009903d0008079800070305a00c0c800a0042d00e44182c66200080c0c20190349602c41804110002c0401030740740b80c00d005400101408603240340c14465143c41d00c81401c0404040207020f90305540d00040c05003140a00603880c02d042c10116640e5411010355a00078101c00f41d41c100e08201d01503400700716844940282e8580c4003504a01c6206146800108009420041d100031f030010401c10403055607407240c841111141c00707201d04d00309000841e0300d414280c2d504004e11241c20080b00c1c1041c0481c0303940c000e280030741112145503030902c00d03049103010700c0a20b00002d005000b540400540010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 642657149 1250 642655899 642655901
    0x80a0b040204181a06040503060711010e1e15010b0f130f120b0106030507022505060406050a090608070e0607030e06190305010f0b0f181c02040b0a03170c0c03010609 73
    0x491001c4c0c0301d0ba000c20400c1a0402e02c1514015030050640c1508404005002d5034800c1206d05801d2008400104d40064503d60303e60600204400340c03004e618076900c1003a11910200701c405148200205c01041940c50720724400d20b18014000c8000c00b40400084280c0742c41b40d458007580142c01e080b1b0203001440d0703641c0203078400340500400403181180e689000294480c00fa04c207180c4202102e402900201d201741601c2410141d0000c251481108115004502a1030304070141014040b29100c0c0c0380d50b520501c0c0e02900c10700c00ca40c00301c030820150f1400c1004240d403110341556842d03004c1e240203441c1c60182c513003643c5c40300c80814001c1d0044ca003c0f415a18202800e1000b401540300c0c1d4604100590f01c95244400600207070058001d01c2c402040619101d0900d0701c0100003d55982c001424203410100000d075a400310700c51300c00100b200d6a01d14200b0f524203407054040105049070280a05855075503104010b403580c1104206048011400c0400078000307006400600030020000c000c1151100d04081c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 642658399 1250 642657149 642657161
    0x613180b011d091302011112040303090f050f130b0d060f0b0604030803180f0a0309090509030715020c010906020403210512060f13050f0906060d0201080a0b04020418 73
    0x1d0000328903040e04440140400450110940c010f01030140da5600c1d1405090a58100d400890400072124000d404a560a1280d843d030486801010303aa0785145040003826030b01103420940b403940c034843c41008269a80f40d40b61211950030b0714203100d8140700c01c00c100020501c07403013800d0f000304015562400f04503840e840f10742c0c034020b041c401b00035100c020001d12069000d58080145020010000300b454000038400740d4600786000c4d000c0324204c5000e581c8007801c110307580c0c03001c40c0030070200c2d04240038004c840c0c01110b60002c440c030003c5040c854940c07030b510007008081005400d400e50004244c8151542074002c100d6007508210155626582c0f89003080c8042c0030028500602010515010340f110310a10803640003100c1162841460345540c010092101c9082c03a00715400b8000c08201400080b5600441e44500d0410310785511b1880e00003942801c20034001c003000d10880340c1401420041c2c1c0c020580c80c3e01b003008841c001070032020794000b0800901c1280c024001002409190120700b04098102c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 642659649 1250 642658399 642658421
    0x60f0515100c05060402060f0426190302100f0e0a1115130e06010905040515010e0306010609140402041e060e1507030e010c0b010603141f05061318 65
    0x2107603040e900000c071030190300c40000078555000300021801502c1d1400117403075000e04602100385013950304c1c01c500340720303414844002120000650015107400428050760190018100c400da0703100d4071a9134020349400c1c860783c46000240d81d8404016610182d58020920a08090102e0b04080c6050503e030003034504c0428400e00c68081441d14114034040344065030611910748045015407030420003628000e0030020b10b603504100d0703505000185a511802000d008440400c649242507600d14001400449031070241c40c042e60080f00100140c5601203480c1c0b084900c0754004c215100904000280a44166808551581d00440e075280c051103204041e20221034903038407002500f05181043c0300c06601e184140c4010850140324400120780100095003144905140c84030303460005564040c0510400c0e007280002a585040e15605296844020740d0054000760114002c408403040f4400140000d000b03030742c01090b0124210b00c4408428008902a141008668801800719041e0f440140282e0203a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 642660899 1250 642659649 642659659
    0x9010e06211f17031911010c0507050c0907081918210201090507060c030201090f0803180f030711010c0609030206150f100f1704080d0b120d0c060f0515 67
    0x4001400140950180110340f103c030041c60030f000b40f46541101d25244805940d041c000640c240003850ba000b03224200c2e03c0940c039105c4644480603402d00b1440c210084988038000c0e0314001c2440364003508109500c1d8070040f4120341500504011020502074100340001d51007108028000034200301a41100940050b580705203c240c100342d0402c00c90a841c02a9405007141d00701d030f9807e001003445143d4400e1002e01900020607207016960b40c5101c120840241a501c0c40c0e0080140b003074101d0044610f83ea0191100000c01c05000c040c551240c50f441890401031406c1198100e0810590042c1d00c1c207a501c5400a0040103018060709000c0e486030f0b01207410301008080544e0310b5410f0b2410f25500141000b000d44844d400e407000c075401b1b0751940b5940c04440e05000e86d41088494615a1242d041d00c140c4c8619425621078010072941e0040c1c3d01c4a15440340b10b0340d021801c40c48414000100029000401d05d0445501812414040010040300540780324007410b01c02040b90249503440d03500704501d01528 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 642662149 1250 642660899 642660961
    0x903030d0c0e090103080a120b060c16052403040f0b041407240e01020c10020c030c06041805040812011d0601180b0708090d0f1709010e0621 62
    0x1001907500f42400000c00b640e1b810b004c0d81c804c481c410744400d01540311050001905d0100440051b0b815080300250440503440b10300c48140080580c848600240002d80b018100d0704441e52820401d4034540d04071440030103010001400b80502048080382041c1c10056000d070608050410721810b0307a4899080c0402d02c1072400004040054020a54204101d50240c9543c030310500c1c000c1b5000d1048a46081c114410300a070f2070200c0c0e40b01c204c804408121038005125919405050504080c003440a452041c1001d100c10002003454110a10b51030304121000a000d81c5d99113440226030180f8040d0a02c581c031820004a482c42000c1003030300005001c0940388449980c2c100045440c40d601a403d2040f03840c40c1c0340c04101051030304014190441c07081c0051800c010440021076104241c0400544011840c40301e0103080c8508101101c900d007030704012491800c0613090001c0c105400d144402c07030081200051151030707085014a0b000308400300c81c27050030450412003d54200010381c004c02411b8298010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 642663399 1250 642662149 642662177
    0x70f230601050114091215090d08090102131e0b1303110f010e040908160302010b19050307030f02011e050a0e010302040e0f0903070c260102120f0901020903030d0c 72
    0x13482000510603058001880c1030052010b03c0400c10008444145900c50483c0c2900080c2001e075595110301c1d8860003c2c100c1d9012040000c10048000d002d121559204029409100e4000d02814095400b0404500e07022160811880f2800005500000c1c00220214200340b90b170540342c20240071640240701c5007000d048540100a800240c070380010340400c4462840c0342c070904003900011111401603c1319400d000c100d0b200c0b45221849a2004c0700181d544030010852850114003480c0304042920f81c01c49030303d04000209070760390802c0c04064450258030044004580c402c1744440c0d00050040c402121246004902505c0b58200d003800801252845680000071751092081d00d04669542c007081416481d1101d20000782d04001d450700c50240810820034000c00c540d0b4410500401034070481d00c9200d0141c1007820364101c20036a01e400c150340104030302840c501c0440c220340d81104900940310447e45071a6007450080c07148480146d00f6000106021000c044154071181840c0c9254503031000c018800c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 642664649 1250 642663399 642663407
    0x12050603010c09050f0a17150709060801180605130b0f011119020d080c06010e0a0515010e03010b030706030203040c080303040305030c0a05120c0307030e011e02070f2306010501 78
    0x20002010008030031100400241c40c2c001d04810a80801415070040302e611482e01403141c7e0381d0080040c8140d800312020000c0f100321000025440780d21480d1030540f10742800c900404040041c8208024240402e08010401e065580880020640103155502c6c03112420b00b902c0140c0745103c0414880e8290405011940d4020100518000c641201414081c5109002460080d05402050360000410300c02c00c4002070110340140038204500000b01665890606950305042c0000c2400c3d010504060078082442d4911200b000d0f60402400c0c0510005c0058020900400d00400340c0c580c144a007900010314550950300442c00f60740540704480442d520b50340c00f00c0d5244805da82c0100014402c0000500031062040688488078280c0381040c580854640842914001501d007902d02c03030000000c0c8440c1030342502c62042d521150300001d001780c4a03c03035052246d2010741c08000c190300d500080d109007004588011400342075880051544010198620342e08001c6055040c4c052501c21440089065802 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 642665899 1250 642664649 642664661
    0x80a0b0f0903070b1e010f0906060f0c0b0603100203072d02060c0706152606010528030c091b02070b030103061d1f14010b071b0b07031205060301 64
    0x3a01008503d05080b659501504020040078400740c82c0000720060040340010f030303035680280001140a6185030034900d82208031950340d4441310600c0f820074010383c011a00220304040b4a608241d86034225136034100824246084001058031702e40c4004100f00c461a000100c2c825402c00c0000d0107103c000c00354294152081e4440411800341e44410005028030351414000d2085d03504c1003401081d080c00c1e4130a0140c299030550090000c81940454003260101c03400b000b0407101147d84028940c551500011860f0080700303c01c2d4004a0004001c546400074040b51564025036001c035400c1c281c1684c0d80303103400c02402c0e07006144443c8868907560f444014400120a401d6039554001c0320725591079959210001c100c11090010340c071090400305030000c907003800052000010400d9040700081b0098901040703a03c5003043c61410440c110060040280740c5041d10300007941f200303100000b0740804404003418045948444440c0341c1c0001c1a07010160700990303004409185000501c012b85640d400c150a0702c1d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 642667149 1250 642665899 642665911
    0x607060212091e160e13120804110105180405180304080c0f060c1911101206080102070804090c031d160905060310091103011a09010501090e0c0a0905060301080a0b0f 73
    0x31344c1c1c0d0420700c0a242d01c04506038000100586071032100c2d2240e511800d000c092120f0240100348003004110502100b00007401610b403091801610740b0020a4844600c1942100c4050040d580d45000a0395030101000d04001801034004070390301c03075560351121650741303900c2d0396038601452150307001101c1d60810380c3c1910b010114803009000407215461540c600f5000b0b920042c0d54404419a03064820340303585081583c0440c1660740c59003c4522208076078161802c0b60710202607030380b0410501d0045000e0100380c07020780317549820103e40900c030484224080c00740104a140e5020040c00100d04400d000184540803d80703640340200b00558070a02d1008071402103801540681000c850490000c956500ca901d07080d114203c43c5194001c08000720b400c41d444980004048000c80700c00441d9444e28680342401403031300f483c03c48072490401170f9046151001515100c2d00c41c1d00850b100c8222070140d03451001402010740625140e603034641506503a8580c1c108190780c005c2c20b240215240b50784000b00a8481c1c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 642668399 1250 642667149 642667183
    0x1c0506151204240906020903010c0509130b060f130608090606010e060c0f03030108010902211f02070b04030509090f0f06210111270901050607060212091e 68
    0x60b40e2900c07900026100081c80081d0070080012064820001d4424582800d004000041e02c1d840c514003498215a0210030110900c902400301c0a480d0f642c80c0f406481e01d10244101050300c142010121340c00e400780d1200c020610700301048081c2c180c412481e80d0f00031150700707a17520034080e241d0543c003948420050310700724000f400150440c03402d0b061240c010801c900c1c209040380c0d5001c0d2a5076841d1300b160820780050390580d444250341419440c1c190030908903018641e00305001c1b159903074245541c0c0d0740d80302000402c12510641e1501040300e558143d0f1030706501320711040b10b1840c107031900605651004964510884d480d0000c90400301488030441d00c05c154011030742c4101d881d800b04002da1122400d801340445500301c80c0f0380d00c0302c01003800382216080030546d0058444003041c140c0807021450710f40858107506411f80c0058640d076000d55079411140190b808607030344c041d203060001c0a4820b80d03ea5154601340720040c0500c09400003403d481e02610704000318036050802c2c42003a102d851b040d8004401c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 642669649 1250 642668399 642668401
    0x2071403091810060e010c0b0f0712110307080403110307150e0c030c01050c071a0306031c0e21011505090105042a0c0c0303090e28111c05061512 64
    0x10502071581700c140d10300141844292401195541050004100c6400c0845100305c0280078100d40c2002111400c445000018400a910a541500c003404010503203070030040744101140c10305024101c05500020904c00390395032107115003403003005150303101520f42e4017074603003003100c600880d000c41ca54540e082c0083c043c12004c0c4040004403015080004005014002c3c0500040c002d1040012100c2103c151066107072070307180900c101402e140000324205040710301c010201802c80d62040b1182a481012169107110081c40340440044d0403900074034000a610700007800419070740c00c4811900300c40c800c889199040ea00e0310140015690b01040c4140c002c100041c07180503900207403020000c0d1081e2458907101004a6440c2c41105a44a6000340c010880c0c0036400c0c0301a0032100c403030b0703580450036045440e0902c1c3c030031100185001083d903034101000d5450400ba912960740608481c130a0345428811402d50341c1c0c11009800400e41550300c00d1268801d80c07090700e1006054401c1e6840802160188501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 642670899 1250 642669649 642669659
    0x30518040b1804110301020406020106050f03011b0f140f180f0f0603090c0d080316140a11070e010b041d010b0909090a0b0a0c0215040b07050c0102071403091810 71
    0x51650043c00032511004c0d4244d640b8825102440074000034642c95002150180c034200034400d404c0d4010450328000d03418010044c10381c0f100703030b140c00f0341010040c50b04180c205110b10040310151358200caa85c003d110002985050800c258001d410600700c4044000e01a612440030018003100c5111156080020011044171390326162011b15480032200050b50104a5984001503446c1105141203a0b49103010003440307c08030041450040c05001c900702803075505000071008595001b005280c0007000800e20380b14880040520203031f80100074800480000b56199540b80415801c00d004210030140340c0700240c41210707100c1c5001d0b41283d01d1a0783c1c15250400b0342c3c0c03c1c03010304407000f011100d20b071190451301ca00003a115401107100d90372210002584140d4458000d0405070303021041d40800388000d007440701180c0d8404046130444068107190f0742d41ca60000d0928064000c3d640023600c03201c807250311881d4a00012006088400084500d510042c460003040c0ea0441c4c0161260a0711179010b03c000c0c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 642672149 1250 642670899 642670939
    0x1110601060e0102101b17131410060f090f1b0311040f030b45010605120105010e0705040303020c04111c0e0106060e010c1b080a030518040b 62
    0x1035009010b00c140c5940400b08142441650105000c024050044040603005145c0c0030210400164092902441e14100300108d481c2603120054040c21441c111069011582d1041116184407002e48500748425075482450780e2704a03c0d503200308421f26090110b0074040944c01e210b5882c04035060300b0884000032003007c0440090900c203a40403400001003001040c2c000342d445801008500c248400e444501c2d110f03129035410011050b060f002881c030080070300400540c49072601031a139951700080c40c0504e00045203502501c0aa84450381040349100c29003001d403019040700c1e046c0c0b40d4031500802c643c0c640500c11511480b580c40080d0058125204d500700a14091700300800c03040481c185182022401c0c544007030032009511075084642d43c0e540c035188050100303010305c0e8003c144900308540d04000c04400030740303004409200203040d540d000d0440c0b410b600f800c0c80000c014000070b1040b101001011320703000c0c0240e44840521080c0c0ca0a042040c46140fa150140306013034100544039507070410300c0c020401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 642673399 1250 642672149 642672167
    0x16030b0a09020d150e030c100c05040503340816140901091e1803180f170319020607030513210c02030d0504050a1d061e0a060e010e0111060106 63
    0x84e4083da110442404000000c0000e0200a801034014140e0300c201e2218810440b00b883caa2801030060a1004116075500441c5040c8203400603803404401ca00c803840141c9920902d2407108144141075140840d9507500040c030000d50030100c420712a91183c032810960000980040d4040d0701c0303840341b0700510080d8019000203038130942148601e180b20f41c0d09540308042c1d444411f500c825480900680106141e0305c0441d02026449112825501b541001072110310412113000d00700860305001e140c90b4a40200300210740d044c4442200b503a0482c44030100082d19030f402038400703a000078104070100d0341078840c0380e00c10840c056100510841c0d848101d0a420040780140f040501446402072101c4013584052140c403010301c0d1641d5905903118100020011485480e40040100101c460702c100340b15a0003408460308000103c9241011785c0a501550300c2d403114010038903401280102d00000e8a1340c00490b604d04401f800d0f00c40ea092168003000441d03008000314035640e4640d00000040049a01811140d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 642674649 1250 642673399 642673433
    0x3f1810020a051b0703210e092d0712090305091005040503070608011401110a12050a020118050c0906030a060e0303040201030506010f020601031e020402030c1803031303020108130516030b0a09020d 86
    0x703520b2800349a0015010401c02c40714140030610b0200d6016080c0c203401c100c512740ca81e20340c4440106080c442c60040120030080703109040550781c1c100000074140102c0540c3c0103280001c2075440c4184030140000c000340c01138420140680309460b000700e542405411818103a82450400080d8400c42000444004444400c814014000c0f80b102c0e50105601602c483c0303550720b407600e03040d42e503a610320402821a0a0081c2c0308408486c0d41e54144d00090f0f0208003000240d00032900f2404640700c40c00002e0a0040c2504024007a40c80c1201c01d241d880c1c00800a144640c1c000d0700c4c108600d60300c00c00152044d282400340e00e80181c01450041c40081c000e01101000600b6141410110414990116081b03a20942d400103030380d880407400310b408401c1400c0d240f4007180181c3c0510b0030001c44482d13044014005000003030500540400282c210030580701c2101c00c1d6138004045881188958002d4801c50540380403ea507100350701710001e08615454040c1a52942d40a07061a040c0303010354035410340d0a070000d030314 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 642675899 1250 642674649 642674657
    0x70c08010e15041e1e0303050f06030d02070506070309050a060c03030c0801050f0409150f020403110a360603080c0624040506060702063f1810020a051b070321 70
    0x24011002040f10b001d01c170b48510a44000800c1d0500344032021040c10001d001c18401e504c40011700c0240382d07011030410308481c402d40360f41e626020945416505a07c55411464001c841010b002030140d40c40300d0161400c0380203403020485d54041450889000c07809010f081e404c030114200907d00c03420141d00a0403010300a8010380209001c1e1440c040558603e648019030494010a090042c81000e840c0951910700c00c80390342c1d81c05450701e40c10410640c000c1662980e07580c1050100c40c1c0ea2a54a0006050002c03503c2080188945174034120441d070f00070a070305140c940300e45070001300000c4a0681d90150030140c240c0150062002d0410403016004c018502504038a0500c071843c01600c40c00b001c1c00040f41001700980300340e060642c0c1d0614060311002c0761440c800a00142107468480c0302c000716007100154107031040c88a61040524074020803102d468078101c4c40000d0100310f099200000d082c20284880c418085400015070703490351001e250202a12091111400001004115044440080741da040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 642677149 1250 642675899 642675923
    0x6010b031f0308030a0e0f19080310080a080711010905030304140103021209070e0a15260a0303020a0f0c020a06030504021306060c03031409070e0903070c08010e15041e 74
    0xd00c5954136007050703450f03510403525a420041644421b000180a101072000182400040c000701864031003c0742c0b40182540c0400008150485004030407c80901026000c55401d070354681750070f2460741d00010040d1060141c0040380881036200c1e14001c0104d880040040d810a401c01c0024500c5801d098402c81c18158204031540781c40024100c0e06110f4103c04014000301c524040e016011420011310f8004200d291035442c0006c1c0703446039002c4066a1040c0100035021030000d04000e25111030106542c01403056103e2242016415001080a00d440d0340e281a58030502080c1a42e10840c2da0308001d502056000052081c03500c6a401030ba4403070300050840200c0618411500111502d5811090003e54450002c40c2815010301500e2100410390000d550b00d0325050045d40d8031500e080c010114103170100c1000c9104030b002042619002074018007450f11003596601114000c00500f041000d21340144041001e0aa070712890b91446035800841c00403110103034a46a41b41c0d000e80000449050310701070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 642678399 1250 642677149 642677153
    0x307030216050f010e12040e040215120907120503120a060b04090504020102010b0105180d05031b060f09010c120b0103090b0906040308060415031e02031c1106010b031f03 75
    0x200001d98054024800341c6207403450b809015003503800b00f64592002e64000102c0c0c9101107030348000c40c0e0807219003020110f0a51580d1000621b82c1a005500c0003e400021940d00c401e241e00301642c900039044c0ca000c860070590b540038044050902d22801901d184c0090100c010540c1c88001810707408202c123440024025280c0c510f501c7d083e00260020460f10303913107008000842d602445100020301c002d007810350429001c204030380c054521824482e400765030143c2d120000c0080810949030703003400455880701e006949513101c50395102c044401810040d0117034007140e00700da010b02c903600c02c00da503a50710298a25040d00c00080901a0364502904042d03032441d1150114400c1001e00c1d0082e03402401030f011900385414010088840074040724411071400c401444566445d074100030132254000812000d200581600f5160b14295540183d05800b50b0451300c46402000c50b031174416040c0544950501c0040000c0d0303580d0711102401408035007607007007004c01d651854611000364900d48030002c40010684039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 642679649 1250 642678399 642678427
    0x60319020405130c0609030309080109020f040903020c0604090b040f020a23120a05060102212706030405010e0618071802070606090b0f03060415050c36220203070302 73
    0x507921038000280c0c81c6c0814000c050340140200700070f00400f0001c1c09285040c2c0c0005002510b0200c140c2e1007290748a0b03451080500900202c4081c45000300641e03140c41d0780c0d4081c113018000d59401c20384900c0c45c00200300010003882c429107046504540e1101690302c0e5035110001c484800080f1446c0c04017090080651220b860903c461003003852003000726040c10f1070000a481c180301c60410340070442d0440e124030040b09000040d240b01725a408800350b41c5080d512003200d03d1600000c1d9540c0c210300c0c000100010301030150005402503040348200ca03020754400c07a4502008800c0e66510b03c3c40e420850301000014020007100c103014803250001807034001141d41d02c400311881c13a4042488142c0351f8071410903030b1070030080714124102d041c0e001d000c41c0d01e06540e60b214140400c030b44c100c084c2c55803135020444440401c401d0f038101034012801405440f060400c404103003454120140240b02c031017040b42c03446090a403500e00c00f51105211a441300700d482940c6030040e4100504d040c0816034203100c410152445 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 642680899 1250 642679649 642679673
    0x4031103070e0702150f0f0708062b1b080a230a030e15040810051005030d0e0901271e090f02090c0901020d120219030e010506031902040513 62
    0x5030003c00c11580300031707005042a400140240c45040400c0100b02041c0e02624101d03a014803d8588207400d0b030754030b000060b02d540301707040819000042c1a80795106001e40b4101300341d201d4014620714191156540d4110000c260300e000e20070031904201c03c8000058000101208005040e40e40c00a6a420800c14945403280455007a000030303140f04402603c0e810030303038400d500349101d100c0810700e031070b05003100543e8138507a824400840d01d99410001309031810307009030400581002410b41c0d4156680010040806002ca141070740f040b2803000000440e603010304005a00c0c2c0500d0791609600c1450145204000c1104404110301101617503502040ba0301c41d48107580d01688200725541c416084c5005200780c4110092140e01014001c00041e00300d0380c0c001400c0e002c4103a6920703010b00b60b013104410200103402502560f10700c060000e60414241c07038141e044100c00d5032203400204983e80d140c008040c2c1d0b485480c210004528440e0042c8005410607030091984010000700d00503a00141e903984003c0030305 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 642682149 1250 642680899 642680911
    0x5180601033306030b010203160809060c030318010212010302100c14150a050403092904090614010201050103020f19050a03121805030c060a030e01050903180a0b04031103070e 77
    0x60703001c8102c1145400740c2c501401900d0645810800707522140000f0f5524130403070348180242182040d05004110400c022210360080c00b4180301e49030109100c010f940c03034000340c8001201500603030745000c0c203190510a41d00ca0705401c1140c034609034a550240701192001e401400e08001203070480340302003587c003910181c2d854480c000905144220311170041e20b403c00507041c1031402d230610701804042680030240000f0703100081544000c60114281001801d0001410512590000301d0005020300142d4000c0d0100c602031170041b210203d40400480c00ca640c00d00009500241344c4c1154403030b5080050b0300707404802000010320b42142d1140005801c01d01568001c8691f2040e02c0b145501195202c0d01008204c030340c003a0012000341c01d1000103a110540001443d0103404081407203031702c0c10302c290801507003401d6603002000181000e046083d1254070a1301503c281c2100c800490005040030f550340c0f0119180740e04a681031605550f01c00342c1e284950780b9840d906105062011030020001018203000344 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 642683399 1250 642682149 642682211
    0x5220203030d0b1915020d180b0c03071a0601112407090f03052d0703061a27100609120614010e0a050a060e0f1b04030606080708070518060103 63
    0x144150350000d05d03008180c1158410049440609412500c0e20303488c91040d90125a20513454000340f48445255000301403025007202c60224804189502401c1018020030080c0e940441854840b925250b4400d140a03004002503071803a9440c1601680003c0140c10401c4ea152201c1016564102200c0000c00c64005444540200129202100d000c00d950741d144c2107204514050b0703071011070090380c45480300d2001403c00364640e1001c0c01c40701c1c01c08456035015a8010308203004244034625140c04003c54021020100c1811004940d00790480c2004208607a800c0d0b951030902030a10054041f03441c001c40c1c0c1110180e0301c90441a0514000314582400303854040490b07a03040c80c00980000136140c0251030100d007280f40c19010b000300ca5070080c007140d000d8002c8c23140800d0350300c1e0300880803da82c0f1540d81d100940003012602000708039854002004a0300300c00200c681d002c0e25034101540350403080c8103540d4804012504140703640c0048920f50340c06207050400142e42030070404a0354020900c1441600380c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 642684649 1250 642683399 642683429
    0x9020708090f01170a11070614070e1f1b080307081506040e0703150302060a050c0615010206013609020103200d0209040905030d05220203030d0b19 65
    0x2400d2148a0b803007000024a4130841004200d00d48030b08020001d440303d039807181c039200350300621003142c0c00320b510095010008220381d541c980032048507140b09844d41c07400141c0c4800d084105160240b007021078001d92030405003031840c0a0030b09071940f00241e884c500d0101d01c071444060105500300b014511034425038503090010310f80b005200c54895029007802c0c1c8a100140000e0240d0031031302c0c2c0040e501042c0c03400d0010701c0089080c003101d28440b40e036100a6022030001180d0241e60380c0b00d006021800b02c0c2c101201c3c2c03030303440b148550701d012402880541d006a00c1275004005400d000a070300d40e4903145041c02010886007294002080e581d0010034840c88a440741400002c559140c480d40c040e08001740d0480c0c603031984d010125442841805506a80d5517000f04801c405030780d49500c04442c2540c407a040380d603035070121104900034150031100c120307038085c0d0700f00f244540f40c058192900030581c1c014040c52030031510340340200c01045d43c2070040e174014280c0e0400758282c2e0b0030300300daa0002d0400c0f2000c890f45 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 642685899 1250 642684649 642684667
    0x31b0111030f011e03030203040e040201030b03163002040519060f0608070e03060402060c0106050a031506080a0302060408161e06200f0304062405040c080411010c0203030409020708 80
    0x181307400d160320300707005406800300f0202e0b60200a41d010f40d05840b22101813074541d800124041e010340040a58540104100c040700860000340020480f0180800070349807445003103441d070030034124001e40c1180841800c0d01c000145080e0344040d42c0f0443c002412421702608030000e4044405039048a00131000590042c0309060700f2001081d480001460510143c0034141b000c01d441e400d000c0d1000313005400c003080d0213091035003c2d080342e0080c3c14054045203802e81c1d40e05200501075200e2070341e40d607910300d010004038440c40d02140c50640540c06400400164990fa03581ca002a80b0500d04060841a8900d40c02d0001766a82c0640c41c450081803001c940300802401c001044490802c8000e14508090b33101207103800c2c0030b00a59100050f041140740d100e6880c0d0800c071016103290084401c01c010285c0310b54400703844c180000010b5801c1580c00700720800b50503500b0f030740c2c04100303580180c05205180d0100d01c00350300c114071420286c2e10140a4034200703551545e0060a0384c02c004c9089a02c0325020826501e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 642687149 1250 642685899 642685919
    0xa030302031e0103030c020d0206040b310509040f060b130b031c0e01030e0c19090608011a04051017071a030112300c0b18031b0111030f01 61
    0xb18075804058882a552540d90f01400c103142c6540001c0c003402c1130160a00c00d41d525070054900410389140d01590b00d41941c07c4040d001052030b4003000c0f08501008410030a2600610860191034024000303000d180c690340c6910001c0000c3c01d104070780540d207804203038405454400341c00c000e01200c3c607004521000c0c01001c040c1010781216512400759008018010080d40c040c00e6492480300a0030700040703203000d5811013420440301c54002500a52142414500c203100c55160300c0440c0d0740303080100403181c0c0380c440c12401c2c0c610300e140c0d00c0c04500b5110340b0f0038218a130940c810390b0002c844090380391401d56949103460104100d40c4010840d03802540c010003620b61550300c088000c410b04411246150305060044602600700b02c405000c07985070a0341c039201d0800085035942c041442e600e02c40c40a0740c45035001004002140030841e4900d24080100d403161004003071651700c0d905800095400c103852480520003503404100415850340d00c5401441c0303034040000086014020484240001c2e42c14224066 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 642688399 1250 642687149 642687181
    0x516060905010305160f1101020720090c090108010311011205280b0306040f020a081c0e060c07030201121103100905092a0a08030c0601061e0509090c04080a03030203 73
    0xb21112034035401004869100407040140c986d50b040006171130447c600100d009000383c510041980000c4050040050071298031a0700307000088a160210350307102d0081e402140503112600c1d0124140000500003d041d10460422010042c07406440f800c170340783c500c14140c80d0141c80100010700701803050b001c08810343c0344084441003119028401d5440706404139548070002003024040700c02c060045400c665541c004c500c018810b0404030344101100d40103d8401d4040c06256401043d55080046803508100054403d402450720140001034516001561100d1003038034444503031170b601d015003040e400401004d14080c1545803a85841107051441d8441141d80c0501414682ea0100081110390f01850851030340e6038000c00d8640c649141c2d0000030600c071100302d4009103000d000c003042c824510100040d10038100c8100e40c1d0780541c80301220414003241490b03600c45e0800980104a00540f074204074a003580c100c1011b40302c0a2415544000e11030410f031804404800180d0000248005c1811944e000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 642689649 1250 642688399 642688411
    0xf02131413050c0d030203090603130b150108070f020c0d050f0f10050f010e1602010902090403030e160b0a1b0503211b030115030e030412021206040b0f040516060905010305 76
    0x103081314004540740a5500e000d5030303040601c11400040003944115000413100b6219038011941d03a00c1c0c0c10300d84600d003112100209aa40068038440025041d10312414003082c2c00a2950050b2000100038410f111001d001c148083d030701481141c404481d640800c000040110b400040a405001d031448603090070750340c3c050b00d081ca144048a005205030301c82142c0041d0005503d040c0c4040b0a02d410f40181d025080456010b544014800c081000740345d015000890100018020340300c203514000c095450150941c0603101d00300c0c9051000c5e00480f40501e60355500c141c0103410303500036608143c2d10f052446c2c0c080c07100c103030406a020b445070903001100c0000c0c50b0401102d2455010000481017900c4181c0014405c100003414092010072445000354000706500611400756a911a1580074104422040903800c81c05034500c0c2d00b0b00180810b0209030300d80183d9100f9003036103281c1c4400c070520300c1d0b814014009882038060042d0550300c01d03180104020003818681c46030495240703410005401c0320001007607 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 642690899 1250 642689649 642689659
    0xe0a081e010c05040512010603080f04090c11100b010e03030406020d08220f0602090d08131d0604110c01020408060a0501060c1205030709051507020f030304030f02131413050c 77
    0x1e40b4a075150481c094400341e941c02d4480050340e010780010303140981055400500521030004164024020f1070000b0800c0e10603400341032010800c0c2c48000c5409003d0190001d101750051500d0740d070741d03c03216000004071035070500d05400020f4a007030020381035900c85e61107000982d0007903102c0b004132074000d03030081d0b48512503d00c0c0c900910f482c2464008040c100a8000b4804407007031505000b0020150306481030301501410130b000008003480d00004551010b03202d803000141c2281c0001d45c020b03c010b0748004c0d81003200c1c900c10681e1500028003006e851100031f05566a9400c0c00303400405802440079000820003e0014082030802d00401000c542c1d06070440d60401c9500c114541c007140050702c18032807042091170541d40c0c80d0784001d011034486565801c1203600000d440722002c0151100006001c3c103500031102800c46200000030150b5034412031200501107400708074101b0145c6422807107200014852400802c0c13050452081c142c507070208a031640c00740e0841049080c14042e0402c10851041800e8403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 642692149 1250 642690899 642690911
    0xd0b2e020a0803070302030c0f03180f1b04090303060503060c0316080402103e16051c03030207150e0d0212040902030a0e010903121a010801060f0e0a081e01 69
    0x382c8241c2840020006404c0c56000400f00d04040d020310300325840f903000e5001c500d45034100311007928620b02c04010203440034030a032010504c0500e00811a02030701c0f58030300e0002d1056000c150a110140c619510168249607031a440025580c4051299910480340d42c401140d8034a000307070000080303007514072007041082103100c100001030b280c2d00b41b10106020345003040f1525040140340c0103045051503d00000003d50800e42c00c0710b40c110200602c1c1a82000401d0300d8420240d04c0c81100040741501c56107600403240300c032913000381c1e141c0e0007d9011940203107400340c50030f0b90f41c2e203a200004124004413a0f125956998500c0c4da0101170001c0f80c801c80d1a40f0180110442141840900b03005da8024401e50715400800b2421100b04c640c444542d1103104d07402440a44080e050141280c903030b02008003145e508001070a40001c581510803c2103507416110910941d09001b8212a80614295060305020340b807155001c00d65250f41d0000b00810611004000b06000e0702c002070607214580e104065039a0600d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 642693399 1250 642692149 642692153
    0x1501031a0c0a05090d05070f0b1308030a1e18030c03050c030616181214070b070302060106050912070b0306040c050702090103140a140102030a060602060709030204020d0b2e020a 78
    0x4211007031142c088980d1100c40e0a61b040003403c0409075407000c2002840100001910300c00308024000d038410640307020204503540c2c4440c039200d201c4d0700f28903030000d41026005550b01783d0480741551116020300d0b2114110484203816486100c0070b400540b00c004c40d081040041140c10003044d2000d02054000c0d0410741005407030315840c90711004140050010200c0c0540000054084040040c040d5690409400b10141004001e03030088038100c0d112401707082c0e000300350400b001c811581e45640c5940104ac07240e1a201040390907810035050640e00611103d024181d9174020042640074104841800b540d030b0519008020464480e80940420702c07000740408400360303030760111041c1101d4118042345031941d907001d070050408030f02510080c100c440c004400340c01640154040e501c2040c284104000c1c00303072107842c180e035180f0044980d000001d1070388500b4401400d10760086c0503002d8800e2404108042004001828200100d802a030940d9029014251000c80d003210060007401c03a0001c2c0075100003076 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 642694649 1250 642693399 642693407
    0x8150103060b030109081603080711030307030c210507030617030f180907020c030705090435040b2503092d0303080a0f05090d0e031501031a0c0a 64
    0x52101078456a036a90080b107032a2020b41040e100300e5070260703086171340b4520002215a6074000c0f040030b41c002041d010004200b58001c00101c800c4100c1e1304029421540d500000320080d100d1440144208015600707980511a008490040700c0103402e04003040710700e0141ca0003421660f15600c4000d182007031040d07902c2010f102001b10740442c5110880b003a40ca5000640c0740074545211002103070045541010003e1031640803440422001040342078480481d40c8508004034540e083c1c40290890112003281c0441c1103519108000d04242d002c2480002c004000c0e080040390400d074049410031a0009a5211404003016000741164400f181884030034403640b401807003d041c6020300450b403103240880310701e100105e0815456104465605d421090b45901d0002c201c05820f9404102240c201404591910258040c0d24130803d9620009c205140302c003001292800c0318908500d405003d24119083e12000c0000d4407800b07503004108900a86000d8540c1391342083e80181000780e840030502840f906030b82c0c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 642695899 1250 642694649 642694651
    0x5090c060706020711120d030c0f050a0c0c0f15090b0f030f07140409060e090106050306070f050c1203160305061c050c181806010b030606071a040305040e010815 71
    0xc0b030042e1a000103150103403031100c1032011207902030301130803214006100019001d01c407803820799030078032a086580300c003a1a55680c110b07030800800d805000300450a440f07910740c4500540a0b44800c6e003155030340e090031180c0201c00d8102e46182d0500000c1420642c1e0000880701c01012621505d038a032008003219150b090002900100128503540c0c0400c0c83c072441004081d41a052480c20280d0f5207a51301e103801c0040030140f0400c107400c035000f00025a440e106124000403a1000350181c60359a807001e80803940340303440e4000e00c42448804d2001040c2d034a4100810700581c4240303c80030f517030b03401c140c1154241d84003200145010941818100580d5444500c4500075030800c803845c0a4004a0381d1a141e824440c1e040801d41d00a55204500c203495a0307a00f1107280610525100e2041c80d0003050f03080c9480d61000d00400780d00341c904101154035400e00e14010800c0e140218114501662040c42c840c200300406d403001d4000480100d000e000540d0303141403517401082d0603c001c04a02c00010031910007800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 642697149 1250 642695899 642695903
    0x1003060c02030c101e0216021309060510080c06071a07110d1d0d02180c04150846022a0d080403050f0901090f08030d05090c0607 57
    0x145a00320a0103a80c020030a848030004950142c6401400c000301c81c00081c15811062140000f0380102d681c80c14100d80300300e5541345042c211519540b01c003a0248010200040076100321681c0c3d48905134082410361141c10f00500070503a002c00602d260601c00740c42c00400c0140c1901c518010071851000500c100080d4400c1003480d00c00500580e80c0040c00c1c0c076880c846640740f07001c44c0107861440300365642c0b02503403598131408040e245182071111130522200c91340404000b500445807858100700340086511056116641c40301c5d40d49465215044900c54090101111010079000c03811312400c002000092144403800300040c240c0ca200c0a0241c580e110b10740781850b018003000e807a00320305008990701250310f00003201140c10040200810151042001d44040340c072076001d103542c0d40c104140701d04211402107803d5502e01c0c0c1840301900002007150f100348a00c0e414400040000281d2641d0030307640c0c5000300003400140d62100c00d840c0004054510041150525800100c2c200302c0d10340e1480150b501040d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 642698399 1250 642697149 642697151
    0x71110030b03250e09010f062403360b07031a06070c2111030105070c082104060b0f121c030b030a2301060b0306150714010e15100306 59
    0x34000b150350503081103580c2101890229000410003011300c150820381e00d5520200f010000e00d596115000d18400300300c0c1034818204802707120580b078a0f10980142071420502071003600c10185010100c201d5030101001040c002c501d640401042c480004040f552010031401e080c0140494081c2a04003583c80003a810b21440001c01c6103000e1004822904024000c2c146a4a211260f03000001225180750030382160690180780c011520303400c06000b00c5d4051120b0341c60300044150383d940d940c6907540180c00b195070303080014000846c000210754900c0b80120701900000400e03811034014003600215503e0a507014107a400c03002600d480e000500d48403890001c0a130991940ca8800084002e4148005c4441e4144a890100410702c122001d500c0404034281c4620f1260b955141c00740ca007690b0b210b105c4c0c0d58403008103100003a96401d081a101451280c5405910301d044125581c1120308030b4444010a100d030764500100500c030000700503075110a44100d08075025403400209001140300c043c00700030421 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 642699649 1250 642698399 642698443
    0x206011a07120c050d1121120c0c030412060605040b090109050c1b0d0915081b220509011208161a070f0206010b07021008090c0402071110030b03 64
    0x60381c4030729003030039069034400d003582d0034a800c12170018040051260402c03040d020782c0c803000c40c0d002d10384c41d1010501c959400c0c05509120322140e01142c014402040381c08804010003081c003011b00203000030301c050098089071421108860908008496041c2c00080c0614500f10130544565074050304c0504455510344041103d83c0d4422034130802d4000e407003100012140c81c442208815002103600651007919a40d80703001e03070ba61246144820b0307450641a2021441d0b0700045010415001c408400c0d1031403503007205181c0303110030080851074861415400c600c040040018446031401d8003c80b0300504844482d1110f4910b00d032590001449407443c40f4500040341440b0703104001f511444600610010040e00016180811001c1e0044008245180c014081ca100115000e00c41c1410f035000c040d0040c01c2140c03103400490064075054009072041200344200141082c107513466000914959224075202c41b951092201807152200c0c035140d85a00781410941c002c030407614001442d070240d0088420030542 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 642700899 1250 642699649 642699683
    0xa0f0828200d081c0204210c0e0c03060310020406050f07170705280b34030c020c0a051804080c01090308040b10081b06090307150206011a07 62
    0x1000801c040041d03003080d4011144028441e072940a802542c503010f10941c100c02c07580c0d160f0400c0b40f09600540c0000049001c03062050380d0301d00780400201d4400c0c42c000d0704154840c09a580441004c9402d410060300000412a2074202070211311240700c4030b81c07429030030b042c00c000016100e4011005180001c90020805005029030a800740034040040d200d17482c0e6950741e5080c00c40e2180740440300d14000c030300348208503222800c10b500c0c460802600952100c04644900404036034001208141c8840140d102c180740340c120840100c00e1312981065140000c148100500c0a41080b03400c0320102d11131119000204442c0c5c0700e000180f611041c100c2da419404d03641d240f5200405001d032144001c203079072804031980201a000300005000e507010b00c86880f0b880d035945c5060700302521103014110041c3c01c1030150310701d00341c04030188401d0984010301d030303034201034902010a00d400015802402c5080700d9194018105030140109405400143700c6042c0780300018a1812030761007102c1004103c41c8005c00d24841d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 642702149 1250 642700899 642700943
    0x11031b090603070e1903080d020307051306050a03061d150d0b100906050301020328180b01090e0f03041404060914010e06030307200f0a0f0828 63
    0x500090000c1c42503840c3d0500800080202c00105800ca01415140303200e403c0f0714049283c4841100c0d805003150f071900544800e550060b400107426942400424031901b20010310500e84c81020b4640c1c3e61300c5549612010382c0007010348095070301080070000560141a500c0004110241d0f025a83d2194420044031020104419003101070f006403a8030001010311070030100c1d0807100001c4400c0322405104068860040500301d00c400e440800080ca92003410211084034680c10380585683c5610008850303000781680e100b444420300040380c60455420052003502e0072480307034035140d041c85001400345044180b9030340e541c3d00c80d07400f9400310045d521607d41c48580d240c2d0404006400725007014405041e03d0008075400e084203000d580720300c01040001402600300007068038419034201c104807040080b82080c803120307003000b0250790380c22541c02c055004d0a5241c5e40c100c0070003801c84120800b860791030030301c0d6141000c421001c903401051618408000784001c110a0202035070700301c00301401c900c1000210701 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 642703399 1250 642702149 642702157
    0x203011a0109140a1d06150f18030c0414100906030c03080706020904090f11011d0d0618050a051207030c110d140d090915150201090507260111031b 65
    0x100c000d4440c0300320801035108045000e0700507034064901f4015004905849142d0b40500445094a802c040c09062000c1c01588090b22a80c000a420340342006050300105095400c3e910040f01040c1001050202c0d41c6040040f0304c000b0100440104041802c0d40e66540d01080039220160081c0303008140c400c184520307581100c0891800900c100204d1071189852036448414074000e840318031091070441203035401560301720b0004001c411400704807220034080118107110403500340c0f0b44942d01d4011085103155050795176a10b502a600409016442e071400c01d160041c08503a802496a05004d440c0000c1d80241c0200c01603070344400280340d031010700400b080c5c038141c074848098200300c0c0c1007400c0d0010000201e810300708042c3c00d40d109104240c40d60032800544524011398444010011401c205e9030181e4038860a40c1c04580c40049a01c6a040d1030702841c01c1c0c51508064014450400802c1c0042c51051013103410026020081c00740413803650310035a2502008002d0316640c448943c0560501509600311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 642704649 1250 642703399 642703409
    0x715060608010602010510061215050a0b09030f0f0604020103050619170d0516030810090212060103050a09031e050c0f0c0f1c06020703050904050a090203011a0109140a 74
    0x1001020303521000105031034070070b100f808003652910022030f95a07a09403c803042a41d4294517000c44c003181d43c41040e40101200804030b614002b0001c00842c5943d56030380a42c00424442c071200b40c560100204040c10540c00340c220704015071080c80381d20754000021980d154010340908000510b5911100820113400c40c21400702441c0c0021034007c00c3e5001c80d0311800000c01403403401c5a100640b4030383d0903a82d5109480e2014826000da1071850002071048480c541d020000c0752203120100da440701540140d070001c42d0b4504081d90200104a0702e96407512403a640312907541c400b84140d84d26600e01610741a103142c540094800a082c1c413a101500900c22201c1400320b410486050348440003800352034412110f1035620800d40750350030000c285040e041016004501c13240c0c84c45148490fa0350301c4025031040d14110140f0206205494841da600e1040c0c038481d5151020100321907003540304142c215803a950f00c0c0a1494070008480c4201e0341c0c0101188140c51500c030b01a641444d004000030740e0b00213680c0c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 642705899 1250 642704649 642704651
    0x1303091d0429070c0606170304030b0c1b0a050c010c260426010b0303040503100507020a020a030f03090501140702150c16080708011109060a0e0613030b061e060715 72
    0x10f02581e290b1011101d003200340525420018180c4801200340410712211548106600070312051001c500404075207500800125102403826841001880c40c0d015600d010a40da038100007200014003000b40001c0007100d1007440c01029003502c980d211100b00e007011074402d0f10b421a0880b84141c0f0311584048a0140c0100b01510b010000003001c1006c203c3d45070f9240c6038555081200040702e6003000400d40c7e054031001400b401c0218410b02c0703008000e00008001c80118401d80c001000962122103501c400303107004884601c4403450504014200b5812580040d040240244034034031802011030070741e80042c1c0d04560a41100b008100d07034203214091100507045600416840c450314000c6809048101c80c0c541058031003642e07503a40d280e400c0301c0040700301aa2440702009480c0061070554000d000c2c0c85118208070554144190226035580c0000e0036108032005208418424040324224440d03104c11f040328134003455614500c00c620751807a9000c13410700070301d000703d12441040000b1010750b469040702d02c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 642707149 1250 642705899 642705901
    0x20d0e1309020409061d150c0a0503090c180f10060219050a201005030402010815120a0c14040b0604050114040308030907180216080d060b031303091d0429 68
    0x109041d49620703201300e07503030151084220714804648000081c912030040f5803511401e004000c441951540c2c002030070b4000c03900406c100405103035604841d24000031050030ec1c0b410680340442d004110400042c015529200080030200a21603002036022200282c00e041b00006403042d2514070316000703d0990042800a04440303002c2800b90341200c20444100c210340d03c29500004d160291524072080c0c0c2c01a0003d0010380000b024503040740c0c11110b4014016042c0320b001446229510b0030090820340843d2640c00070401080600700c140304070020031108590802440b252f460009a1a108070300c102030500040d0115a00084a410191030086401030070441e92464141485510b41107240a0101040c1c807032b02265607014002d00c255202d500c00e944201e2441d184944070b07120705410142d088c940c041d031941d0003c44d00c0d0a07e00044e41c09a4192240300711078030100d00e80a000d050003508003406041c031418040122500c1709c18a5900b140e008070040b0004048441060a49400310000045c03501281d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 642708399 1250 642707149 642707171
    0xa11150c0a050d090f060c02040c11060403030e01060f050105180105161104050a060b09010c11030106061d040c08010b030417040b091905060901050904090f080a020d0e130902040906 80
    0x1060f210910a240d40c1c03160701c902d817658401c4000c202c06020f01c030009141e001149005080980c07080c0704401140c03d019000001001c410b074600101180c04400103900c40ca84c00d1084174003402864003506004240d0102982003c0000f0010b0080c03151403411203000360381503005030340600c04980c00b80b4400ca03000000c40016042409050700c442c0c0b5528099031900d4006046914140704001c150b8440c4d01903a450111034100440701501c4c5600e00743c1c0c000d03032008118403855900340b080400a040715100d040b4018140e1554020f0207100c5070b8130900030317424140c4c0c1c036846503031080c00d0034150740e0b00a0712180c40c1c3c0c0340c41c200407440d48058407a40720000c0d00001c011691116000292170100c9045440344c1c0094610480c01c10b90200d94030515030131800c1030114114a46c0200042c0c2542d4101034400107480d1030640741e1000141c1070142c1a0741a100c005154000e007541441580900d01c01c0d403c1c04c107200500c1c0780108580559800d050b14206a480c2e40400440d40c440e0003072408a0782010381800119418 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 642709649 1250 642708399 642708403
    0xc190c08191505190f1416021203060102031204030905180114030705100309080d0504061e0b1828050106030b010e030a031110090803040201110a11150c0a05 69
    0x100c2410303500082e58000c4019800003500605119401900c180a0b03603240040302100500000d8020724519511141c407442134554010b4024480c1c8810350600c50240e80f06c847c00f070f00b00b051540303609054520401c10000b040c0d800108032450508540c5121880c1e5813541401c9a083c0d0564129661110f10710217420400003904078000d042c1e030a2086511075900800301003661740c00c010310509410420000360798441c6400f95200040700c82c040c814072413516406070b1220080301c004a404445855681212000ba071b05240340c100380c2d50803060f004218030024400001e03500070352031508402c02e0401c040016065130f2018110504940d140d801c020080014010001c00390401740500c50010b442c108481c078103584141011400f94070301402a00c00711186481c2101ca865002caa0f40109109000b000980c41ca40c900c81c1c1155640110a05a04d905080c4001040024611540c8203030781e100d4011200400e40117482d03041261021191190b0801010900360301c1400340006410181c091030044400380400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 642710899 1250 642709649 642709693
    0x30010c02150601020d080c0d021e1e040803030a090311061510140f0a02070506040902070636030e030106080a0203070602151602010b060703170a020c190c08 69
    0x2070a00300055482d580120794031603100c4900d0780028812800f0400b59001c85000f4840c8c40d040000140c17070280080c1900300007150185010240c0300000880c03002d40400c000b454001c170130700000540e2401345444902584d80c000a489542e0541d41c0d68860000c26001c0c5160344481090401521064540034071081da2000a00503414050304100411412541c030400318854820303546180541020210340028005030400001d5000750f100760040440d607035139928050401004a0040981e0b52595490300c041506c2103190b69424024003020141402ca081840b544078010420f05c02c2240103900e07007001c55840c0301c501096601540b8015000c69850b90200740c40030001e0094089400c181c1d41c0314400ca03524604c0c401d2100302400c000021a03140342003018a5060703109584004107503650710314001201580454001c80100308000343c005840c1c140034a120764001c588a40c11420f06d022500d100361120111407041c1c240c600451baa98040141c2c0d441401302a04880c011991034088010340c0c2da039101e00d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 642712149 1250 642710899 642710923
    0x1306060e0907050402210c0c0703081b0304150e130c020304050f030c090417071a0105010314010303120e070f15080a06150302030a021611100e30010c02 67
    0x128000403e582c1858002c8802801a101106060340101101d8105108024000341d50300e0030200b010900041c420410343c0d003c0c50150051982d9800b009a1100701461342e80260a11504140410011030303d107041a84a05015401c160302102c0104c4006607040c1105200f10a84500d000c1caa04441580000030380180e80717003a00c012020402e00420190341708075022502d5401007a040002d80064050710060742c0e9010068952802c1400c5560b84000350400402001714809510004014a42e03060098060140c0162181001541503880003804102d145030300c41812a1607100c000080c030800c000d06001050308003110141d10382c03201d00714441c4a0faa0541040000e007980c0100303200b2415442510300303e900740d0610f424004080d00060340650030040c80c1d808403079030a02405130710b0701202c03206a04682c4180500d65940740b1030020804c0c0c1c00d610f10655001c101e5840482e040300e8842742162044013030210110401100000240d1594803c8000028100d509100d59280b0700d5070005406401d8503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 642713399 1250 642712149 642712153
    0xd0b06030d0c120302210a150501080403020717030403080408010204091d0705090a2d0f021213020604030516090506181807120506010906050102031603081306060e09 73
    0x3181c4040e003203503042c9400c1c20141001c000400c40400b00c40c0203034014240e03004206100e02d0341c00c1c50000d040410000071900181c03000d4940b40500c0c400104104a000a0102420504002d041c00d0320004d6541d12580100c8000d11761035110b804000718100142c60003141c1c030103030081c3d441d82c4034004a4080d411a01c100414141850609040704112208000c00345a495000b0302d80c0a140400b00a0f0b4404042d03d218580c680e200c2d400900b51c071050303040102c4880d503220703924014004c240410080b110290b2200b01168818052a4484a4800019030700890b00d100401c11060141c000904648030300e60000740680b181c004010128440c0d402d600342107510b1080104007aa50726400e008401c0c03013000340003011010901c00a440000c40040c0c071400390103010110f540300c64441100700120740e03054a09484990150004100c403401601846010f81310038805181440400c0c194031808a46c10070700101804000e00004107000d210445804e40315030408014414503580750031818200070160f516107054 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 642714649 1250 642713399 642713413
    0x1009060e100b0907082203020102030415151206060b0a021f1103010b030a0b06030a0e19021c032a0b061801050f040204030803390406050c0c0d0b0603 66
    0x940680d120380241041d000d80440c03001d03584c2980c00c85412800500d285629a85003009628040c45951104100c5100c2d03000141e0300d0400341000c08981103c400a00003140c105102040040001c1000004542c4006a40c101d9030840749000c102a000a8005100c2c1c140c0100b0b5030041a540040c550303105810804080a81900c10300340003040d5901d00b00f043c400034004200410841d0020001541d1004003201d00081d41c0b0140c40c00a80310307510650381403200585030500303a4040c0c981448485100c1c2c8804102d0181200b240d4081249604404070401d0444910b1000304103140c013500000e000d14010180c1440c00150380542c4031a128040b10040e102c006031407000800c1400d140031003804040b9044610002c513843c040401072050345441280b80c0254003480300100040d100b0340514011407048004a5482d034005480791000040c42a101804040220300c80450481001c11507040d0b41c07103071401039038071b59490340001d152a00d80e00c0181d0300800302c50070f00130500104064883c0200341c114140c03000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 642715899 1250 642714649 642714673
    0x100b0a0509010c080a170c030c180102010f0903090f090509191a0108030307030e0d080109020c03071a0109050c0f0f07020d0f030f030e0a03050f030402031504060c0f0c050a020d051009060e 83
    0x920b010454820603803030020003078014448030002511a142b00c05100204030324540564100a50311030100403408501c1d40301c1c0070302c0032410f00c0909201030040f0000c10810703403810401107503039400f50360010254514446006e00c14028943d000421124400050310001e59448000c5680c2e54421518680068980075880c0034500d40450500160001681d8134155a42020501c0d402584400208001c0f4482001000001045000c0b4000d2900e8202e001400d07a40c50403000e0b8042d50320003014021440c60810400c40c8000c0008240c41c40c00184c86101c0c0d03103d409610110740240c194490141104c008122038408241d804809628200003940c2d003403000b0b140c030001a1350f03030f51100e000060124070207126540c00e40b00b61501541c1e100f8001000c03952020b40051182e80380210070f840c02d54807541ca56071600c2c8082e4005041d21f01400040c0351007170600d442512001d881c1d01e1a00002407240c48442d8070103081c00410004441002c40450b41000b6020880c60028000c1420000303064072402007114100b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 642717149 1250 642715899 642715921
    0xd06090b042d0201021e03040915080c03010203011505070f020d0f03030f0c091205101b020c0f06090d030c02040c0203180603090d0f090801020a05070506100b0a0509010c080a17 78
    0x11220b41c1a0001d2981c260829411b03564103003c0c0302c00b000030b48801e21000440a842d07010ba00b1a9a07155858882c14a0a01c0300da00c6c148a070a00445000760b0040004209403424607000d01c0d000501e89c609035860300010301d4803003928200080f010390300c55042d0320001c0038802d40b400e445000a03ca070300c00b00041241c0101c4542542c81d07080300c0f4000700d09070034000c00c00040c840c1441d800443c45401a90700d074500d071030143e10840e013046024440c50381061103100c9500390100046181c0020403900302e04464140b03000584144140c01615005102020150b02010b008520210910b540104203100b0000c40010081d96900100c2000540c0c0c02c00a02c0c0200609080007128010317501000501482c907040340085c3d62540702000b8034010803a90b0300300010030b0300d420710160104c5581541e5840d03498803a400d0841c903041e40541901031280690008018030790f8030b00c0456048100c0c0e0700f032035a2120303500c00042e606140c0c80f4001034001040001c0951120b6801450074807540411280c40c0f0858803000e405003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 642718399 1250 642717149 642717233
    0x3010c0e0d08070215030108071406180d0b0124030506030303061212030c030a05070f0c121701030c0e0c0a05180a0302031c0206090313050d06090b04 66
    0x2404100141011845410584900c07400c040c05010b08914090041d40410f81d50940c042c1c0c43c180141e000300041c481081c09103c810b000b01f100c6104456203002030030004003144200091300082c0c003142e2204042603203440301c4003105035401400c082595a510784c0b84103c1d0080c43c1d22a07100048800808107080390181c400c43e40207103005401542140d4501090040022211005420078490038120003e46c1400740011485070040c00303181a12403c014404c0f41c19604003401800500c8120000b903000e4a0344050111040e90b0441040c10242c07000d6113040c0da00750400a88102c10380c2a0f000084240b2880b9030341d05003281c100450b10f3308166a03e41000040d0301850721480d000030030400824128104155294080e9039005100c0e0384050341c2c1c0d6000a1412141d046d0401c80071008280c40e50304581c051110503800100c0c000518549581c40340021404000c60041520401910385914140143c07548880800da42c003101041180c1041d0400744003602c0310001050f400203c49006080007141c8882007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 642719649 1250 642718399 642718421
    0xf03150e0c0405060a030e190f02010f0e040603081c1e0902010207150e010e01021906020d2301140423062b050f060405030a0c0f0510060608060301 65
    0x948801030802003209000c200151000352002001d00c00850070740d80301e0005100c05419600e0000d40b6a0315800e4040c28900b40880901c0d840809407107030000b0440c84154414240d0f424070340314400c00b0130140152140c1440c001c0064009140c40d4010040014980060141d50000d1a140030140130a008642c00e50340c5c603041da0307070104412031083c0b0360540040e000004c0051050042e148216118401002c0303034026942105d0016810601e01c520351358220790421a840c0302880a41049401500121150502184010803103940060004404400c591000c010358092440d40d8203a66500740744030f00481c90038001d40c4007103010100c4245071407900d40705d481d440840f1944c4014480c0e001501c20082c2000080c03200d5046a0006015205003600e06203000503068081c1c0d00c1080c05031f990428901e4016041c2c00f2098a502c60070901002c40d0300003040d02d140c08030524020f10100000e1500c0c40710001c0f100c0c1e00030004d101d4201e08410802d207540103041074030b800341d907400d0459507403804150a9920300040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 642720899 1250 642719649 642719681
    0x70902090f10090e0c090418050606010507031b0c0611030306031b01020c121b03010e0604121707082d070f0e18182a220c0f03 56
    0x6075004a0030a007010680e91407450900010b019681c002c09071a403030703048603034040000c000030382c40c400c80c85c242c41050340b2342c0c04a402c070000140c2d065076400c0e52000003825150500ca00071462404240c4249940f0300a0492108001080e1007140750982e03880e082d500846001c03991854010101003000000c0d6031150000600601c910082c0044004100000c0001c05045004007858642140c0328202242c50741c80d00c1300020207058280f048103035046400d0a0506c3e02c6a4140072101d50706800001383d0613045604081301540c120743c01c90b401d03515141d0420b140d0392509402c1003000705072030308100540d210303008440c2079100070201c094040714048a0ad000f0401c044030b80724080340c0d440d0b02c600303c4400c5507192400d140740b42031a12000940100c03ca0140e40701840942030400000380f0f111210381c02030490072802440b96502a420900d5070096041440b2801c4138401700c2e9603441d55400c0190131880302c0010404100040c0840c00e42c3c090880300403590045500e01c0801d800340c91291141703410040705815 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 642722149 1250 642720899 642720919
    0x905010c08041a0c1b030607020a0f0206030606040e09010608010605121f110d02070c1a0d1806020703081509070905090c040302180714030f1f0807140307090209 71
    0x1c003c02e43d01d2003051680000340600c585680c00104100c4100815440c18590101540100400d4a41140200400308641044808400103604009080a0258101d401503141d564580204905010f55400388a81c2d503040d00c1401190f42065000600303441c0803000a000ca0350700d0307200b0301c00c0c005008403100e100d030b038480c081c031040104448403c0c031150303003d5607804140410f9030244442e09802642550105990008141c8100510715818070b00801d0400b40100c2a4840c0b41c800800502400f0400b41800b904c0d10100751042c403038119060704041e4001c00440d101c06550a000303280340b0307007200c1074070210310000714412040c40c040417102e100700c0325030703070740c112107070b00300010b0001c100c002420f0010a104207200110060303a0fa010300e0b810f4032405a4480440d0b1910003002082c4281d2002c07a2000311004200b404488140b003551a81c1c004003081421090b2041880c0b000000c004a900203146e038003a01c80003044d0b1500c00d01c0c842c0401007040f0701300d80e002602d908d00c010480c03080100c3d042d0300a120740 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 642723399 1250 642722149 642722159
    0x22050c12010b070f020603090109051e070807260304051c06051506031501050c01090305030f1b0a031a040c110c0a05030c010e010c06020a0804170304030c020613170307030905010c0804 81
    0x1800640d0712923416400820119141ea4413070749003541039280501090145004103400100400c0318400500d00c5000826080d031078000c02040014844c101f080000703805a1a41d00301103000c1046174010000900044442481a03040886200d0241c80c00c0724040e0030040440c0150700c4c100c4080b41d208070024139451035501e4901c40c0000c1c080840016606110050002c9103040c1000c4c8181e091a034081e80b103480d6246003490000c4141d8200600c1400c00b044450300c080310380d200107c01e5841503004c50800241700b072150020080782804414100d035106042000002085a10003880c81c4a00072039402c60349544a4001044032406c80c2e4051107070160302c04000c80b02e242d072250302e00100c0302106050220442c40e03e5118901641c2c0104488804250003009120400820602c2d036000c461210300440d0440c00e29680081c00034515090280c400c0c070300443c0c0303089820700e40540071006001030103076030b05500c0d04148803e0f202c0e00460380981c049007910030001080e50080c040500342d1039210942c4d03440c0500706 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 642724649 1250 642723399 642723409
    0xc030b0108010b0c0a051504021207030c150509040219031505090613020903030415090b0403051c0504080723030d020d03020d06170618011a22050c12010b070f02 71
    0x140c0f140c1c5070148543d90185c4041642480b5840040385146c010301881d207002e0040c0203401c0007030842d00005911031801000482d4a1148000649040d28510040d50212040803509409070790344050340302d4070000342201010704101d45c590b1540115103040c81207003480184031036150b0080c03081540011403200020000e15003002d9242c3e440a14060050070048450042441c6410a41161040c0c190040191300c0c0075030005080700c000e20500c01801c0c030380f60a641e1703056102c02d00700152551580c02058292240ca000c2d0007590041c1074040100c0384102d50f1203100b1010070340c3c0b0300d00d002511460f20b40d803072080e4100800c2110303181075540c004003030403000003004400a501450618000340e03070b07030800400c8000000890120b000c006000502560514147e602d10102c580c40d1403100d01ea1401c00f0b0122840034401c001114071808592620481e143d51654003042c400c210070b400c2c1000e00c0c181c00c0104000e41c41e0003070020301291054001040e07884200c040441d100b10344014000000200b00d090051900f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 642725899 1250 642724649 642724657
    0x7031101111c060b07150f050705070b100519090e010614060313120309060b0a0602061501090b13061710121e03030b19050a0b210702100c030b0108010b 67
    0x30515002503041d59440f804e0290743c006500407111030040180b030206c0001c06004180341241c04107000c00441c00c000c0c1c0003400700e12420400410420a800004400c2031105000301f00a100290140108180d46000040c04030702a001d900c03402d920f811426000013105201e200b0540d1100c2d0500c40c45d1031001020400380d9040103104070520b190804610001070382003c21050100920345000c260318440c0d1900c2c2043d51255a4214041c0030000740030000903a000078442e810041420030f4400c608500401243c00d40019040100c6103000010300c045540300d13480c0c0400484245941e00d103583e02040da0008010341c0d003035400345103000c4100c0040c03300c4004154207040e050b100f85403185a4213020300142555244051099000c241e030b41c91800858280f50351040c85002c1169a46d10040e030514001500740c01c034034051001002d1002c1a802c10f284d880d37150390354a003000549454554600301500940c0e0b022496039923104503042000302200c10307020b8040c003260170070140c440403982d0b0300b81040d050550300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 642727149 1250 642725899 642725947
    0x1b0618030718050f150d1e0c08150106142505060901090b0c13030f030314040b07140f090112200910090302030a031b0b0a020703110111 60
    0xd411002507003010300311040709100300045010900380b601444000c80c4d620001c00c0d00c6003400500041400c2c603603030040602d401980c001806803c1c8490304419840c004001c54009104614909001c24001c10015503040510300f080c0c1e0182c0c050b0380b0360070101d407555203454034982000c20501c04c4031100c0b0010060203460141c4081100650007440d02c40c1031402000381d41c850b104c1d95403801244140300182a0050748680d01d85102c82c81c0400d507032002d0144514034030004e400c94805007100381c1018401d4000380d2090703180c040c03d06a00d042504005020341001d4030004040303492450075000248041050700c400e000301450721402c0090b440300650340e40c4803c000d1000e841e69a2044840c400d05c03e07500b40d0300180445110140c64004100601c4102129000b0301c1052003035500d020030069034002032107041d0990601e0b042e2039817075100240c218982c07607020004003203503203800406ca103001c05680900315007802592420802a02c21400d50308903803030102c0d0a0242201040a482400c04480304046684 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 642728399 1250 642727149 642727153
    0x207150e0a06020d0e100e070b0714010501032004060509042a080a02010306091b1d061b1b0102060714040801050a0204061205070e0d0201030b180106021b061803 71
    0x1c07a059581a00700c0e8483c0f144594069510607050050f4070081284403030040014404106841030030403010340c2c460003445041100800022048200491a081c252074040054000d100a50b16840c04041c03026401441002c0c40c803020229001c18034050240804844001d005020191925141c0a83c003088070f0340f0b845140362a403400640305165000780d850041540c2400350000800620004050b91955403180d200ca9041c2105c003070401100300342c0d11600488904069450740340f0034a15003400001d1901c010f9100e50042141c085642082e44104c0004e07220310107480400c1030f03040c62005204180070400f070040c2d2180000900c40ca01400083c401001c401c1481b5050540c1c0f5203a240c01e5500403240900000e40101c0c0c100151900132000d07480f600f040c2582881145040307040100201c0300c0c0e010040c4901c17007248440d070559000e03070300484010b50041d000d600c5e81444044814080d11083c400d00c00188070f00440b42c8002c0e54540c6500d9003c01004100a142007800c5180c001c602c03048480c801d07814 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 642729649 1250 642728399 642728413
    0x20402130807052d01050322050a02120d0f03050619030807050618031e070f1110232a060708070914040f021e030405010f0207150e 58
    0xc106015004002050108002d112090412052180c16220104012402c080e0540d042c034071600c404a620340440781c00c0c43c0080e240e81d2803071080658a0920009552140700310007031300040c040c002c116081d2079402a1402c0034814407503502c0549d6030010141d90341c002220141c0a000c0705100b80c00050300810000c02c00c40e101c400c04049080f40181da03074822030300c03080002103002c1040000e0103440d6100241c40c0c0b0701c006d0401b0500e05191207105940a5480760b142c8e4a80780c441c40e14030301c400d541c1400d411900c0508580f606107400c52018180c0841548030b21503110f01007040301e11503d400001e03500c44014000c0380251708032014846800500e00d216454036040301c0c0001040a400901015411403001050b041c280f03000c0242203070380064005000c104041341c0502c44130b40200d400003041e4601350350014502c00a400a20000d001b002560000b4215001c3d03042814070426015501482c0500e00820441c402c0e96003080803846070350002465150340c034503150300400869000d8850190f4400649103a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 642730899 1250 642729649 642729667
    0x1602060409020c07170f0d210f0f060b0315150706020c25050913050c090901060e0c130e0a0b060d0507170403051c020412060605100c0c0e04020402 65
    0x60341c0140204003555408844c0400038151582d9811040769100d001a10020f240644d025485151a0030384906000c0f05104440303a041d12101181410040070303c040010102c0090004040d01030070410000d06400d2080118007412070a0480c1d00590701c1402214440d620001848141c00d102480705a80c504240042030115003240011b0000c16010740241a405031246440003200c5000f80d25250640490442804551541824103400411220364a106103201e4a0b00328078001e15811700c20f030000a2502848802030381508a035042c0c1d0042c890040301381d0fa4003020080207008510002c20b03c5a15010104a2070200c0c443ca0358201180300c00128220b482c1c80c0115800d80e111003540e82646a849081008082e8010122021000d01c02c100d8095400c250310003d245020f88401c01120342d00c0808070146400141d4121001040b00003a107540c00e41050410f4030050480344640c90069449a00c400340192007504441d0f8003903800444511140d0030541620304c611002402203801907420801d80c05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 642732149 1250 642730899 642730901
    0x160c020105091503011a0304030203040e04080706090b1902090603040221240c03090c270f010f06021c0f1713060b011d041a0a03050102090405010f0b1602060409 71
    0x20f40742030b109224941d654503003040129002c0405000000c9081e040c014000000d901000322030843e5280b141003992521981002141c5200c9d01d10700404c803603d803109000130003080d0400c0380d2049682418401040e861100424164810450100d500c170070100000740051a0000c440420050030101202c601e00700781c0402443c090b00c803051040582c15980c2d455100310036020313425601070110f1184070700b14100382c03800b1a034410b03202d101c1078403d102024411501840e20030001d003841072298094011803c2018003448040303030a00032610500f14a44010900600010b4038040800181c8286524492905000c9940328420303250002000704000c208000580c1c0201020302402e006074551301001e050b072510408035a840f498a6041c0400b0001c03000c0b1081e240030725407102c4042594046000f000c503481858125584160075903001040220102c18848154007600450303405407030410559880d107490091401480c41341c820f5176071081003a0000f03060311419504005101400702ca00780f82d1612a908 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 642733399 1250 642732149 642732169
    0xd030b0f09090123060418050a03141c09051540060b0a0614070b1503120a030c09050a06050d090611070204050a0b0a030b090a081801080609160c02010509 68
    0x304e580c640c040070b2010518161103000c0c00c02402020002c0c01c507260365905074403040c0070000a070520400d20f200d41200c050650403150100003c06c0103280704508071461200801d0b0b1184162690b12038900d21464446101c03616900522001d01c803154481980380141220b03815016000303520500402510a411000b43d500480c0548562030109041a00700b05100d883c042a9100c0000c101040c0041d90b004650182201c2c400c0d500007801c90081d64400300c01200c0c103030b44d4200c501d8051203035403400d44421280c1d20181c818080c030760342c092224081010707007200e8403800c0d801400d40c050030541081082c80d008800400418844100201d03041c8043c0d1104000c5071320740d0705000c0c1d1040001441c48110315044c41541d03032040400e4003c014181626010030034078400703404010240a620400705900346020021840c015600404003661019401d0a4924045c082c2d64074901040d008000320b021407a08041c01d6100f40345180c904401030740d00480c00c803000c04010704181e050200401c18003e1507101c0203210 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 642734649 1250 642733399 642733451
    0x1905010e16030218010f05010f0203070203032b05071b11092505030405030708031f180b0909100b01050403080c0708071203080c0d0b0414090d030b0f090901 69
    0x794441441d500612010303102c041000b42400d0700301c1d4014411054020013030016a8820b280024600d00c10020a07481c604c5a0382029501d4400400eaa000342c1c0159103d40c181f100d400c902211013088801c00c15000d07541d017580d0b1603004c1142c00708110034250b9a0320080c0d030311318010500307202c01c920400040303040318005079030204050600c46003103202c00c1d0040e40c10100b952641e18010380f85160030b48aa40c2c50380201c0200600c801d0000011401841e11441e80d20400040800c00c1e25090b543c440a0707240c004846480100710038140f10000c0131518003030240c20b21522122028042541300411624010851251414140101817001201240340403020b0195000d1003401000a2401e0090715403903c0500e620101c180f00311240018000b039440100241c00c4103044140c941c961884031164009410710f9071b0803540103803420718000b451840046000b802280e880c41611a058a0540102c007607842c000b540c07a8006411030320749516410000382c0103501c0015400000b0310040e0741c400c0505c1101c514180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 642735899 1250 642734649 642734683
    0x90a03060e0606030714011b1b060201060f0e0c03040b040204060b0f0c011404050a0b09012304020120120904090f030c03020c01170708040f02062d04081905010e 71
    0x100441130408012400c040c010700b4400c1c910310205d03c40000c14841c1c40c84151502c18400404002c10002500324558030000c608000e90f00c002d817100c0d0000c0c024011403080181d03060076403070300042541145c3e010a0107424000a143d01c0c582e56601c4081d81c0c00d0b405001260441c1c1d0715600010311300102c1014200e1250400201681c41000d000c00300d0079203050184418040c26118140400a0380000d440a44207034440f0310103641c1e68801e4121750040c46807004c3c42608481d001d03801135200118030f1324a803085100740c03034410803d01240e00103801141550f00511055000c9400b61190041c5400500303002c03400240302003140c030040d51312034500000500e0203c002c201456100c070205501408203850b0300038280ba001c410b022882e06091741c0110f000d041981400380c03a4000c102840360203c5c22011864015004940c1c90880c039080c44140002e00035030709000fa0546924496100d04070b41220211040900200440c0e075180d031040110185001c41250599690320f0340e8803c2d18400c0c0310021500500d041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 642737149 1250 642735899 642735901
    0x30715030603060524011d031c11163005011e141b0d0e0705040612260412060c030b010809060103030e0d170301060906020d0c08090a03060e06 63
    0x14184068810281c920340c600306080d122085c20200c404044240400d0900e010707004a40210001c00c2201c0c0d041840b140c05008030b1220294559034000541e907014216600c041680300a03100858603110702203140304800b02c11103402c20074000300c0d00e10306070740c07485e100d1044101800f101380420021a00d0002140d0603511801075405450b00b40c40c000390040310b40d003800d015020b03803107419001c0c07428021302138845008451861105500c0300000d8038003602c0c81c48010001145020840c2d40d0b00c009a1255620890030000e0119044c3e411841c20b181c803079840300b1182034400d8604260b0341b102d0800c8060521030b0034140400a0388a0801e01c0017450704d8060140092500c8484a0003810b42d48440401414401c0c81014001d00034000075400b81125014508041d60602d060001020000b0b00c0b2409003981031011840d502c1070034068000c6040321300f6511903980d2150303941003ea84500451b080c00002c145c040b0011000b00780041c0c014851840000c0484204170303129a120300c111804451064981d1307002078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 642738399 1250 642737149 642737153
    0x1032310050414040f0204110f16060606140d11210703050a0605030a03030c021e0705030c040e0706050a0e0405010801022703070b300f0a02030c0d0b030715030603 72
    0x101c01c81514031507a60b44183c9500d042e8851408129003120000e001d16520084141d5000d141c000761851040200341066a80740250302c0c2c482002c60942d41500c0080c43c200d8005022401042e50004078105590084d041c500c048040b9801801800c28101d0f5205c0c003042150640c42c84041d80403010300e1180d00c08209420b24510040c02c845000308000e1007246042024050703907030000781031480e01d0f906140109180c10b005104a050a035441119010b41c0781e070300c034103591300d48010035140c00b03551055046428656810080200396465003050048540042c001032020604c00c90041c10102d40300c0c10802c01c0405840007113400c45000741e201c854265800304014442d4818ac1460915100f14082c21083c600340c5480040c0d118186403081c442c41c4180014080d0a003100586c80b500a407401001c01610041c201c28501d000d454102c40091070807140c0380000700f111000d882a2402200600303603440c00c00e014030131542c000308054007049078580306603003000541c0c0c40206046120951079690100301c0e14070f58 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 642739649 1250 642738399 642738401
    0x4120f11122107020109030b07031413051011031308090a170c100206280c08061009030b0403050a030912050c0705010c0b0f06130203040f0201260105010323100504 72
    0x502200300c00b40350401c01503004d40c0e401043d000550350000ca01c02295107400e10190000c000404106059504403030412110754a5075000c0c0804070700071000d9270100521071005004503940300701c4404545c882440490041050445c601110314441c1c010a483c0c008002e0008803030480d29480034000850110600b10183c1c01840100e00841041e200d144000c4d200e440d020b51514030080009803845400380b4001d2007103072410910040c80025a508101451141800610b0311340119440c83c0030703041241505450511035000c040c11690402064500ca4030f403542c2c22a025806420860105a00c0d202024007103010940071280404c41512a00e58178140300c00001d0070701c043c80e0b00c114144040340b08102c01040310b20303803e00d61015527501402c0480d075445002602440c1c4c40c0d9011b00c1202e2021040000f00081d440c000b42440303000f600c2e00b060007540740c0e5182e10b140700414510a0401c0c5090010441175010740c01040100103107015140c03111a04404003e880e28040b10b10304446829280200464201 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 642740899 1250 642739649 642739693
    0x1506060e01020c1305090a1a0114010c0f06020306131406030708160902090d0537150905010f09030e0a060513031b030b190b0604120f1112 61
    0x28000f07032000840d00300010b0a08456080c20a08103521030b000035004020922004903880d038404016009144200d07140d00741080240910141220a0013100041350300030303040114502d5000c5a03503642070b202a41e414000c0e4001411040c0c01c49072141101c81d00040c140550004000130440042e5903203044e0003050714006065000c684141c010278500c0c2c4e030a403000310120094564442c8056600c40e0b50801103055149442c2000c0e00d280907155041050185104008000c4528030000b58462000c4400300454202d484500520310034107c10070350b9601003190402c035007482c018400020203550908880040d1040000c048001a0840f94001118580450014041c082c1e0740740c158107018440452400c074058502014014103205840415041c800c008003002031070344001103a00300e0810a9075204140b0741403900740049401e0915840840c1080030541d8100c408000025554264a80f5071a61601510005a0b444104080700c0401c0c1d40380c2d00345017221416440010081e01907820400000c2480c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 642742149 1250 642740899 642740927
    0x318060c0e1e010c0c030204060605030f06011713063c02042601020705030f0304051920150a11060901050105031e1f020406030c14040306021303150606 67
    0x1e02040032601042c00b2150100e074104081c200061081c0e00c44c1000b9100402e00c2d0b10095004e4201000480e965501c9405903004d552044000c4100d6202c007801540c54a010141940c240c02c800b500040740d40000a0780706082c507001d00000940001094401c100c80c5101c10390300149404089903a540070842501d8032018606000411402e00f800d005c0444103c16481011694503250400401801a02941107503400d5a010003103d96410003940001c10301d4000321015103150240720704e005191180c3c002e5146401d40e200d0101180001d41d10051401100b40451203604100c440301c1c00d5034070400c0a4018a1301500350f460b10b45030580786090302442d02a0091094196905050040000f5140080d2801507060261016508196450072681c42c1c024a03001440c9040f4402012a6109031264001c0050301c002c2e5806024080007008140c401c0911406c288403071107001c110820209006038050003082c0340910038102c110366242c031080f2404502c4102680304568070101008543d4103d1100000c2e14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 642743399 1250 642742149 642742159
    0xf071403091302120103030819020408070e07170105010f02010e0708031206100c0611120403081b13030602070203071a27011b050f030705061902040807150318060c0e 73
    0x18540307144c0003031048062000800740f2807003401141001c0c110350102c4004007901403013107460341c0e50f80020f25590000c511505640101c1da0011610841c030984c0030960422001e041843d1507460f0400440303c024141d8418021556500b01214a201050240500510340c440c01035890365000f50014050900180080b403154140321240601c1541001403400c665400c000700160000e00070a0505440c416920001c409091050401c8105600000454040c2c014500040c4502c1c0100491840a00c9840329184004444400403c00180c1c40c4e002082d5180c03004c0c0039503200b07550340c8500c0502c020600b80700e46090240460608409200315480b090812944514041254003020019000742038400d40c01c240603030441507030028403500700440d01d156210802200d6480d041418410b48490341a2080320705104d22103a05a480c180500a440c166a16100038005807807906502c0c42c48d04051400c0b00051684840aa50400e01c00000381c440c000d00400300070500f03840000e0000c00d1200c00c82145c920030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 642744649 1250 642743399 642743407
    0x210f1501060302121504060308030106020d0809010e12030627070f020607090e180304120302070e0106140c150a0915060f0b0903070902070c151e050f071403091302 72
    0x103000c40144a170002d21414843c032175820b101340800c01900782e03500041c090f500700200000b6415070010f071a00c1c4450b2955601551500c2c1c0b44003075402da4141401581607540085035581104801c4401176030008030040009400300c4042500113864083c181c00f910b50801200104400c8581000502c10044002c3c80540283c1c5882c801c054480c00c11340c0610b00c500c0c8510390009204070740000b002250482194103c80c0c56580e2180034440c000720f1000120f005000c0c1c1d0000080541006404a0580d400c0d0745521407a4556244070002c1908524100d014600c202484c0d50b510032202c041d6180203040004010440d170b17050381081007400601500c600b00f0546018002c026000050041e1820740e90120490307543c481c0d659000920304001904824040c80c8000354000401c0a55020101141c14101d0610b5201201e040240d50b803214101c01d850403051504c140700e01451003180100390510040b01000d0030407002d43c4400f030a840500350842c3c165800000c41d480340e45000c5481e580203907000c8606600d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 642745899 1250 642744649 642744667
    0x90d1209051b040b0a08070f0e0c09090c0d0905031308030a021b01030204180b100203030c0702010c0f0b0702070303031107080702040903170906010f0501050c0c210f1501060302 78
    0x3a0b80a05404003a28094002e031031800c03680e640c0c2000c405540300800807001c2e643c8030740841e62142103600c1400b03071b00003414500054a8081886152240d0754000701d040c20011340e58280708a1000c010206103034841c04101035075003548240f00340c03022140030760300641e2268500d003c001d440c170000d42c210440c260300910030030504590006085e101810a2a007511a854485006070064029a0800342c03271301844103c4202c04005540c0050a8642c00f00c3e5201d540c90b40400c020781c2c4a10090f1031802c1c45610400c40700d40035500400c141c144541c0700c3c490101040f0115191070300541c0c001d907003800c016042100d04009043e0b0502841c1c42d0800c01d440c07981e00c0c0c81d0944c0c0d00d40303901e8401c2c035100a002c0c4e0340719150356040c0740c001e0604c180302d18000240903c440ca0007100954442c1405d0264601d40c4060140c0440c00354400d2083d6003250320760000800866810504205844d0048903461760f510340169011110340005210302541405e00e50010041912002440c2c0700c8020140c2210b42014814000402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 642747149 1250 642745899 642745903
    0x5120109050d030e060610120f050604140c0403080304080d050108010506120f0309040e01150b0c070617060d05100c1701140a1701020403050a150f050907052205090d120905 76
    0x180144c0215003111464024580981e00a5803505400c40d00318940506010b400a292b082240b00f0402150204a421100500c100c603500c025503601451040c103010500001d51098000e5410034080d228031070038070301d00059070700964400f600080340c207075182e10910103542440342c01b800d010f0401601a2000b40c3c0107502940d5030340900e0890701c1c8507030740714610f8030741a030800e51005640185c400310208002c1d1329180f10398440e41c04505001da00d48502c0f000002c545101d81d84c00350480c1c040007503100706a11210204520901c8002e4140d07003034028542d0421000c6035500c02d9441840706a210324049100510a111034210305a00c020941e1185d0b200611003942c40d080b076081640c400a106520444058031100d0080c000c7d500001d040b0b101e4030502006225100e07220f540d095181d143c0c28001e0103124214801941d400345d61642042d80001424001450407400a4061590480556038020b906240700701c1601d030103a4461030070360000003803882c550354040141c0e014410580418002301d41d95030b403402c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 642748399 1250 642747149 642747151
    0xc05070b0615180402070203070b0c0d2a05010209180a0609110d15030b1e15130e0102090a090603032604020d0305161401050901060311060702060405120109050d030e06 74
    0x700c0f2801c0c2d806103c40300ea589aa050b214205e401608640c480ea0310b82c80c2d01090343d4440782200070144900b0402e40c80180c072400a04503602401d051416100f003104140c44e80044240e9821501035409000c4500c1c1c0e501e41407040d46162051066241c09410006254021511207410464a050600204400c4400554221150042011000100215625181c2005400d9600300506a558850500c800c6180e40c3e0298030101030225a411960b4440c440500903c58035160b480360000c460190052003555982d1003560449030110001d8500000c540000c0c0309030a00e9007103d0410b03a954041881031651001610740d08603244400090300c601e02d19600504076000420080c4035051502c0d041c0c0802d0700c188103468550761507034806a400300142c60b096440e050804110072040d86004001805420140910b00840b908807030410030244000041c441141c5c002501030b070300810100000151611180769005400c0030580c00040c09001c2450118184800c4001c0c5a04150610304072035234032080481e602d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 642749649 1250 642748399 642748417
    0x604020d050118050c040c080603151503030a0201200901091503090b070c031409010f120e03040e0a0c0e090a0e1539160804090c05070b0615 62
    0x10120541a52800d02d016100129580903e01600104042004000a003111400c0f6040314180821a03c2040c211000001115441d42c11f503c4004800219003000e03403000d401008c1c1500005044c286207022a2a41d031112100c400140c0d074035003000c40101410b0002c88607000c01c841c00c00b8030389003070100001c0005049010328000214480a40b01c0201e00940c04403d00315400750760581a440d0056000d4812601c1210540100e40e042001e045021998811100c006205840d51001460341c8cd030304039580e60012440c0c06410760b0710610b022203102d0801c0640001c01290510301050b203070004004080d42d280c800c0700e2041c484501ca0300e130300d20754170300207610f07840703803c0c05000680110301c15082490500d038032040f4095a010002405450080c8d10716070500e034810b002101180040c80002054000a100b10491a20a0600c2010300300d05071a51030706111801807410b039040a84512051003103960380e80b000808100d000030b14504010a4092481e4044000c0f2800300413041600d21400070f40c0b20300515 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 642750899 1250 642749649 642749659
    0x204061514040f27090b090609070305101817041701020a0507060e0a06090809270a05090a0b01081b120d0e01050c150a0b1f0c03030f0516091502060402 67
    0x400b48031341001180c040b101e0b2628180510512015081100d2001829180b441890090100207600c0c82c4e8001003a8044a40c050002d0540c892008000401031200c0440c542041e1120b1030600040f81c101c4a9100f4000000c4440e00c1e40c4610b0108080d40445040d00720b01596401400b20350082d90b008000e550300035410074800f054160105100d141840d9480c2c2c00105070f5841d1481d100107003c0d00c41c001d4195600103a034541c0b07541d11840148145542c400c000c213a860303008078000034500740c1e80f43c00041e0400303080400c46400d10329958400071540401d800100c041da2100340141c001c034202000304c0e034080c0b4086d91205074080d5100380f650380f1910300012290500014410034051039104000300c3e80b8041c03108080c0d42d03100140b104940c14006003914000311050814445032201c0c50501c1004040e0f00d0f282c2c0c0c80080c6441e4904007278504034040c81041e41410b0392041c0d05c048245080c0101403240803588209201200c5640c00580b000070160010040d40d034480d40184c1c0500e4000903001d800c1501152 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 642752149 1250 642750899 642750929
    0xf05090a06080d03091106040506160807050a05010b011d03031e040b0a0305040c06031e0902060f04090504050f0303011d0c0f0c10050c18010305090a0204061514040f 73
    0x103612400380c107031503015070410700c10b0850201c0c0301e41c0e0650200c051540308400c5103070351050000c104481ca0069000e00b680c811030420042d601035a0240403440c0040c441e021980c10501c951320b43c1400d21140d10001c0e10607075140d5104003070660380001110b221401484c074a81141d0400750100703a44c3d00410810415010203108100302c194010003c2c0e2b40108502e0000564800001100402030801034500316001d5a84000100e29a0b0003170184001e501c08000d10380f40d900084001ca14040c01841809a0700850704001500d04035850030003c01c05800070a60124241c00e103890900e00c1c103140005c0191440d0000c1c80140540c401080400780c9030082c3c00f100d0100c03a100c0660f014500d11480b9810700110600248410044101050b01d81d980d402c40c0604105070b5650713404100c0749129658030001c0301c0c200e0402d1840030f0341c0298001600b01104404480c41050140d012408441e1180c10600b40710341e0f10094950041c0d400860314400c0c859000d0388038101840d01c0703203460090b5031502400740070700700490f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 642753399 1250 642752149 642752161
    0xc030e010207080304062c030c060a0e0405012408070816140d0516030c020619090605070e0f060403050a02010c02060f2d18211c080f010f0509 63
    0x7540b000c2c1007484283c0f80d9807a40c0307800107050104001c441c04880c1e40d0120040b130008035481d43c00d1800c12070140241c4042a561810091143c1c0710308102c1e0148205060409900e468620845010b000009240401c0b2504540c3d41d049400c81c030042001000102401c2110066105e07100c1034000b890340c0701003070038540495415034050355450158509100089000c00345440c45400090141103d2070003041403406c02503080b01374400c1c150094001d644620041100652903054401c40701c690b182c00041c03460600d030b40768801d4820948c3d000780052013107410483c0501e0311308403405013148222449443c09245681e003d481e02c403804c0010341400300403841d070742c155141e80040320020f005c03114101d036a5a00c00e44140715046041a4031500712402c11481000d5402c0300c60803605014001806e01c056182c180d41042100d400c0c024806180905610420440c8803042258400071030840b03c0039070032050068030040c140040103040004013141d40780100000c1d4103080c0d0305815100e060360700d81c400e9a509 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 642754649 1250 642753399 642753403
    0xb090a120c05130f020706020d060509040b190902100305160302070b270f01060e060108150915131e090f0303240803450307050301050c031f060c030e0102 68
    0x80100d01031390303070b000185460401201e03a006011003900204104016500c0b0787c1403008000040310010030466080c00860210112400c03040701e0383c001c44601040c20400c503401716000500054460b000719440b402801046036201c0504240b58040f440e00314102926a220009400c2d001340102007600d03c00220703503a400700403820a940130386d401c1007190015001c4149580c003c0020744241d41d40380c24407102180da158840d00782c0034060500885e0280f01ca240060800140101c0500394846101801d0014200c030b071a50400400c1d0035200c200c000039410f403004e02a0801c0e901c0460348800c15403602441c6030004405059203010701e41c040c603000a4070340f18200014072a2440040c21088101c1c504400030342c540c0d00100409500b0342220700807408860300320350f031400708141000010b108611200301d00303020900124068520b101c001d0440e2050f1350b4400200342121810355100c010200000200142d0842903200100e8000d00044002015454804010f010060368640141080000b846a545680c42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 642755899 1250 642754649 642754661
    0x5040909050c090f0403020c0d0308012c090c010801360605040f0906150e010b0708040b2a0c090705070615170c01020601030f060203070203130b090a120c0513 70
    0x805804a0078504100c10740135403c01088601710014400d854882686080c0003842d0115103515855400b1a6401c2035001001001000d0b050040905100394000340e031440d1a0a8a008640e100080e10641203040d000400c4144143c100c0c00c4d5029102505d04191102c1019100041d680030610347d84107600d070312104020342500e80c40035511906105001034106466800701e0342c1240b080c0c500304520b036540b1010340d2480001c0d100f0f024000e950007004001c580618002000c8240c0b0036007502c0c1c44c060721050103080c1074000c9401841e10300440345003a0740d5488580d111042c2d944d4200010030101207900d000801c4104001c14030020414080f41c040100882c503000a25520700c40f80c0c42d0814a03840340c00404150302d0201310750b90103214410b80741d42d00f94000f0404a0503a03800048803030f14492580c03210b07000f03540701a0100f021031204000c2561036507400ca040c00064003407085442d40d5102d000d020080c10081c2c60704140e111301d1840c2c00010010f081c0e2080c0340201c80041d5414803016400180500080803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 642757149 1250 642755899 642755923
    0x171303050a0504081015270e030d0203042102070f1203090509070c03031805030906090126040515060108060d080d0204061206061b081e1215100504090905 68
    0x1c68524040c0903010f60f80c2121880103089101c4042c407640d287d00340c05000c00e0340d1310100815454628100741200d8182c02c8181040c2040c421280703002c3c1160b80b446c0c103e074021a401d4881c40c900500801c00390720030700c1020311400014401000b1240c2071100c100307000c0d205445103240e420b0040d294081018001c2080c08002c000041c0808042d150071540503101c081c0c01241180024505002440540965501043e080350001300550429080310240011580a408403034180400b0301c4103040202c040351840e0300c807009000c81811540c1000d2510b5460003204404904034804170108004490741d111403c1c2c7d6110310100c4496003004038a051202c0244180341c2100032a0f0700006021500303a800946035020221100d60801c016a510076084030322007807031054800007859001c10719012811140c0941170000800e01c1440808281c08402c140381c0d800811000c103550071307040c104004525038142480311050180c17408503d00d11030200051291040f030240c00147c5070303120030200c18840c0400c44403001d06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 642758399 1250 642757149 642757153
    0xc060a0f12060902090f270a0b030a030507140106150f11070620010501030548040b03060f1801110c0c030706020d1e1b0c0501171303050a050408 64
    0x140c5803070f8604040e40c000d41426004007080e50383c0c407040741824460180485c60a050381d1040d480c41c4610501c04c0e0101030300b00b0b0035083e20750014012039582407003104000e0b40300c0e0307c1d9566500384c980743c05c00300c088466503c44280e0349807000800804016802e040b00712681c914000d00d2060103640140c510400850701804184680e80300070900035003101c05203110060540e01c20b4002c82181003042c1c2610401d0000504940010009078542e01c80100d240c0c182d4410100c0004000410522071700b0000c900070344031009064070003400178076410725116a81c0030366802d6020f0030340b41c5480e603030301480040e000c1c00d40e021074885900a851507000a40c450700d600308000c03a5140d40c41c1401c1c46455510389990424504c02e00403100e00098142c000034880000304c0741911011004a041700502100d03900c076004180038440200c0204080703039040c811400d2440d00c03490b00003180c40c0c2130200040140c0c3c090414205003104c03060034400b00c400355001e0b103014640d1614103903079541440c000482d03890103507074890030080c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 642759649 1250 642758399 642758411
    0x1504090204151e05150a05090a0305030a02010510140306040312060519030201020607093f060e120f16020d08030127050c090d02040b0a030c0807080c060a0f12 70
    0x6981100c001000c9140811003000054990042045c104045c1c1c1c1c0c000d000d814100300740345407103000e640a000c2111006001d00d10369503503615014110b40c045448100140d56601c10400042e0800c031052020b003501c003c1100302d2601005c0401e60304e040140000d002c1c8801d0a541566a01c1180c01038409040060000b698003007180300c5000403108140401ca01600030f00000445581c860816481202c254000c8800ca1403008082d40084465410319010b040c42d000c4200b168100c1c202500300159803055a0000360303a2003051000e400e104081c150241c2445040001c0052080c8100aa0351805000300c01090300ba41036100186d00700c0021600200442d002100000d4061200e031140c50159245404032a0003008603040c0c5800c40d1403c0790080d03036000c800e201a4115007000d135069001d0b40e1010f0070001ea182c90dd4000295250350551003100e04000d18001030158041c24400000180f02c03c01c000c3c5580301c2d0580000340d55000e0500346400f0000710a102100c140d00c03820203000840e122200030040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 642760899 1250 642759649 642759659
    0x60f0518190c0908101808070501060b0324040b060a080907030506010312080106020c01140c010608010618060b04060c1707020d0807050c010e0a0b0a050408011103011d150409020415 80
    0x100880e18413900c030b000d01441966204480031070140c0c0d000c90f0b40b51901500000c405a58041d955082400709480b10340d6035a5000c85c0301020500203601820140800c0007807144031130002c0304a00607510645e805035007013492140c080c2d02c4480640340d1549040c2002000c550300c0c241b0051603c603c0c0d0344090114400d2500000c2130003d03842030501c40d81050f598800250380c0310481030781c1c0c90881101032400102c24403120642e0b000080701410050003860004070715940c1d10000c19003981c2d03140c0c0040c0070a50800050740600d408921410000385082c01a1500b4145080e1014205945a000240503131444c0c002100f201d2000034111000030398010002035030501c2c03e0030104800d800c91001180c1501c560500368103258060a61020044801400c444200341096036000027600004207007001d000d400e010118440c4070a015500b99aa211240b41c0d490390325006c40100c0d0b00710800d41c20000107007004144614083d003c2031001c85100180e60208808645101140003081c58108104284413142404a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 642762149 1250 642760899 642760907
    0x1803090302011101020c030706020702032b022a040b03150c031815070e0d080f07062a05210a0614060903190203120f030a060f0518190c 60
    0x2628003c0e6249083c4200c0c100d043d030700301c0c170039129500780961041c041c2000056903034006020b80d910140640c2c0461400011031a288400c02c00c154051002c5a80c02c80c0700c15034100820403071074a26104142c040310010346080c0500c5299200d45000c0c1d511050030300d43c0c1d40c40400c80400d911400802c0080140303050500c0100540090b10060070301d4402645540132107000060b650740e4080501c2a00005855440d400d071185107207c036041d0b4010046010b2040813620101c0500701d280c042c1400690348102510300401107a01e055540e5074203110501c0949061000700c445000e0880007800e2850351004800448001c00c890741051624140d070700c0c000c11040d044107410080484a60001031a48e4a0387c640402c100c80c000d48046981682c0300d0441038405c1880f550300ea41000b40007a040d259104019007460886c0d80c0466803800450030700000b40000c00c159131055100500e1002c012555060a2000007155942038827041d0403c9150280811030030170b10050444ca0702c42d18041c00f009803001c4094083c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 642763399 1250 642762149 642762167
    0x3080c0319050c030a080a06050a0e040212010e060c0a0201061502030a11030f071104090602031e0c0712180f12230303010e04030c0b04030c0b07030c0e010c03031803 73
    0x9410035481c1c08103200c0250140c02582c00103c4504060350800260040881d11050020302e8000426114074001480d0340340d4451b40c034050001d8076224016480c1c02e0044c08226102d003045485540c1c9826000401e400d0b02007452908007110500c0786a03140c258100481c0506420b400001402d91031103158116150000000c00c000b05907038907981e0300303044011080703900c0307004801112070200001c04c41c1c200014811411048000e00007000021603000b191140e034201c0c0c104607481217403e4202e80c5072541c6d0700c00c00b03440f15900c000c4020340f0324070740400e035668011018880a031520500c1200e01074011004003a21610001c1c00003c14180100c0c0c0e51a214086088041388055811041840e2100034034614840b0800308548801c0065203964a012001c608001c4014003d80400c0200300c0000c3c00210030305075990089000303070348004505d070b900d0801000441d00a019203013454035001d498040240c01c071910107906002424402c9004a00d8141640600842504800c107806801251410590810342e04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 642764649 1250 642763399 642763417
    0x12100c090501230409020d0603290f09030d052725030203071a0d02031015020109020a03120c0f1202011113051302090603040605061002031318020403080c03 69
    0x720503042000780c003000004040c65841220f040100420302007060141c000b400300d03e041070400680141d42c0d48540780e00401c1c4003a01e4028030903415070082c010109680b402e8000c09a5050b01722142043c0380911f644e48226810000c1d42c0383c0b20800a203196000c1c48810010300c40da02d81ca40220030b0071020b442c1d114038050325118807082001c84c1d03072045900500c86240c1074a42c05002407203481d08045001013001c841d185070248000c01000303140004c00c20383c0040c50007003001301102c1d201142881c0300b202540e880300d14800c04680c03400000030f0240c3d480524030400c41790440e510104840010034116000b00c0c072001d000d0501b121141c4e45c6000c2050240103041188010b0b802004801c21868000009100c4c2d04041e4945481d0b400342800280303429015000d00e545404001031800c1c07412000f054850b04110f605969890341c1c0c2c010002141803162000a03519101e2010318900650500522081c202d07500039102c54039503480e81460b52036413170360440e40915000300d01d503078942d80d00b005083d0707172644140c0705 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 642765899 1250 642764649 642764657
    0x80f06070801140102120c0102190504080105010905040818062205041104080d03051323161a031302030316110a06050307031e05070201020403060e030c06040212100c090501 76
    0x1140781c00001c3c44450718805070b0182c40d80d0100d0941e448065000b000102e5490b56003000042c00e09207640400d4015810141c0707d0355140c6152143c400c4c2100c905a1220494904203810400000d200c60203c9440c000e03d10181c42004084102050072401410511100d006d048401403903043c0070014003008a50f0100c0b414803000c82d41a00f4800c041c048c40c032072043d441e880840c6203811f0758025084594003241f03a058042c44401180c03500d4101c0640e0316082801648036458080440e90180514006690925034040038645006004504c00120705503030054440040045a440440541c0440c03080e50014216a15250f0940032020325100010301103a454416580c200250308007030000e50304450342ca4480d04d00f941e48030602034028109a180c03070615600e4000b280004446248503c5006010320307400140c989055142410844560888001c00d80c0c0c0141319000ca4220009419540154140d031980411113035007183d40c1c80c100c2213003405008503041030303c8020a80e0b0b1100464007110402d0303803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 642767149 1250 642765899 642765901
    0xa0b030c0d121b0c0e0415050411040e0a1a01181e1802040f0c020f0c030c0d1e0302241005090718081c021603030e0a080f060708 57
    0x2088452420624010030706a00b4242d0100000d024034500c002e8a085110014200801a50341045a0003150400d02c8461383d0442408180f0410120003114048864402c10031414141c460000c0d000340c0301c48c0984990b0300d54594011050b001d110321064940d20111824400c05800292142501c090140754030505e0102c010700402c600500032034112018541100400701c0311500344502a00d031030210004401c81c0e60f810540162201d01c0b40c041c02781b10f4a140003611a69082c0000d00f8031880141c4542c20354405105840d07556000b046000c1381402c1250f102d5824900c900e00158004500c0301c4510360f0303215807111041450780106860160b40e10311000c01c040d0440c15244480b0445007598003140d0018400814060b90401440c147c1d0040f4240c1804022150501400c04403000e00d42c000200315048802440501c000c0c6148000304020240050000c2e04444403610b00d80318020b02c40681000040400141a52140c0b0740300400b0740720041c00e481c0004005d1044a82e5244103807810000205120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 642768399 1250 642767149 642767173
    0x4121403010f090213120b01090b010507150203090708120304030e1f140c1603020a0b03010e0a0906060f06170108010b030312060a05031e0607020d0c0f030306030501050a0b03 77
    0x100889050398000b500d41032020741040d1000c0000d400210000888200222010401d0a04801e0342c110340c03841024034882d5903040051401c00d40e0107000a60381440814402000015190300392598420200e2000603100c2e43d03290761661a20709680c1c801e1100b40110031000351441400001148128000d03143c655a900000d8140041008070501c124404800a002c50000074030500781110000c951600c82414058405007503801c01090310343c005a0005540c0042045003002c0840b0401003592044c1a4103640c03400d50250081200148400b40f120344d2991300c2010840141d101d10003034600c82001815541d100c2c1c4001c0e040c090f080f140e5200c0d200180000003102041402980490080a0f02850401c00500c10398256200050012544412030780c20200c4c0b1602c0420444411b00b007108007120f48500d106143c036007024405010302d030840d0032554507560a81e403c60490b241e6a80c3c0810305041c60500f07420100c0041415800c0100716509041c28452a00340d07036000040c00c1c0b00120242c4244410304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 642769649 1250 642768399 642768437
    0x70e010602100c05130b030703320f060a0501110304030501020d0b030c03012a1209060203070809030a080402011214090f07140a140d060c0c12110a0b090f01050412 72
    0x403074000e400031500300b1042c0806100c0f46c000c2c2d90010824140420904000c01e0b152088814614114440d6400d11000c08010b0f041901007036000000083e0784402824098080ba990803018002c441c18000241d02140801c0420000c440c02550010000c540ba80c402d0801c1c5400b414001081078400d200f2100d56540d41c0c501881440105100c02c070b2004190614140d013410ba40032580d001d1070a002c0641c004a109462501481000030710500006941c0d00d044031020746107003005807101021754010310020352500d03007107038110340c1240e0242070021150b1a1001c40d90040c04900d01d030301e000c4400c16818000031510000781610710355031007410ba816aa440e8a100f1035032210503120302c0d500c201201d10801400c2c60450341c001c100741f0301900f80d489030b4105480d00300540c1c619502c587c0c0018104024071342440110011f043c1c01850710b10702450081d230480000c80c1e0b43d5032a440090100603895000c1520007030700308107003440d00800d1340c006d1000b85064104888810b51050141001c26a031520740c4c0e03080451 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 642770899 1250 642769649 642769657
    0x13170118210210110909160c0b0a020f040314070b04030b010501080411100e0310020703120b01181d01050f060d1d0d02070801060812030a0b0d020919060e091b03070e010602100c05 79
    0x11a42d41c88d10003032941d880d40d00109101074480b01580d079080007002c0e4070688500050024600078602c1419160814a070a445d000303c03030388015160013051105000187d0210341c0b0604441c030900c1c0c402c541d0303211800c12000304a0b031000380c5ca51004038448840c0300507800104507000100e0450036200c2064071103000d00700b07034400d00c50020001609007400c1259002d03103920141000006241c20180456054500c854500742508880066017100e02198034244c2c5148a280c090001a144181000a4540440c0d060b000740c50140300c0060f119000340114040c01482c01140d03400032011611070000d41c610194441081d40030b006215400c103080480c07004000600781021030700c0300c0100c1b4915581d00d280da400500e0404602070b84085a41100405a41e4080c20f0314002d1a50781cac410f038402489d011044044554507409880c12655071402c004107c24042080003401c400340034843d46001034500040d05041c0280c014001207a40d8400100e00998009801c01d550a0700940400c0001c940d850251243d0203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 642772149 1250 642770899 642770941
    0x20030f0705160608071205090f06011d100e0127020a031a0a030f02100203130b0912011a060d1121010608060306010605070813170118210210110909 65
    0x11101b0090788040710180c2c03005900420180607108901c81a0944505018080c2c0c0921031b956400201000030040040301540c01c0800c1c0360340b80350500d1402482e140d0350039051154074540380340b04805000a0040100400441107080d000f1035960107032507c080c0081110000d050b407100c0c80c22803400d04c0b41c140003000c00f003520b03005111181003007403c1d03003001030441c24005510700f180814000907400441101c0700744050320941014548a4014005010100c0c061a174905556030408010128641c0026100c02e107601c001e60b4030581d9489600f00500180c030f01c8180142280c0c100158800c4d100411008043d0f036100090b0311406141d0b60b0b80021100000103950f6658150000c0004200a80c0103200611030544911440c80c00c1100c110322103a952a1070f6800031604510707100f264180c6000171311070149840c103d0001c0007240102601d40509242c076068900c0b12400d8209e00c144d84c4c8500030040000c3d820854081407100c0034420b689442d040d04001790150055004c44049100c42060380040080c8072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 642773399 1250 642772149 642772157
    0x1e181501150c02061b1005040606031106030712020d18050d090b12070806010c1b0603270213061802040f120b040b0a0e030f130902090120030f070516060807 69
    0x85140c003c94500c092060800103d10071000301031b0030564a03014281c8264082c3d00d001480c02c0c80d5040c82c00e1501d0054280c584106800c200b042030b10754112511044800c030902005849024101d4503600500812010070480d8240c02000002c005001500c0d80500c10a81e80d903200f40e941e01c0c90040441d0082003610710004004000103820303588141d01055102c80145070520600c01242c80d0700c044070a00210132440204424800c2c080141c05000315a41c2040e100036074100d9180c2c0b80301800700600c015070024411007040b426080e4889d07164100784040d186803424200311444201040009602c01d215448040600c0140011080072201c408408241c12906030861a42c3e6640c40c0d180c02c4800810f80c500f515540d940ca6251680b0410150240c07000c04180c290f07a030703201c0030200030b607100302c951100403840d00402c0186143c1c2da102c0301c1c01c0c140054524800e1201600010b1650440c0902007103820340610104120342409400100051000c4203103a00c02a19501d52000f2504d17040219110750101d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 642774649 1250 642773399 642773407
    0xf0b1e070b0f0a0615030207060b0f01020c09061f122a110a080c0307030815030d05072a051903030815030c04020c0a1a1e181501150c0206 61
    0x6a10303000380b940c015a04540082c000c1c2d1166540c00070340d480103d861000030f07408204c01d000c0140a00c030703141c00c03210101c842e068501d901600007590b030940e00307522900a400210104510340c031082030070420107083d0400005c6010303882000405200c65881c0114a5078184406000101031040c14a81c00320307404e11114616500100d404d035500b280e0510049901e20990712030502158000700039048550320f600c00303561794844500700100802da02a0841888581452a0340e0041e6000104554441c0366401c040d41c031602c86041405682d0800c001c0c501c40c4001541000b6808044c00c842042524411141541180c141c8915000000e001e07000c02008101c0ca0004100c408441e900007014490780101241e01e4180000c0105007641c209940144542d4806903001042100fa640d103204008250248082d9510703104100d10300c19148203812491036020b1002040900000444150b85814980120380d0010088078202a007124244280100c030f8032008804504540315212103080c01d90010006810 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 642775899 1250 642774649 642774661
    0x3051906150507020607050f0c010e04021819090504080703121407050d180b0f0123090a0e0a051b0a030c09020901020a15020c06061020070f0b1e070b 66
    0x3482d44404426030740905c0034442c0c100042c104001035258514001d0281c58243c032110700141404c0100702c81c01c1e101d2801400100010489a2100c00ca80d0b2003c89061900d41170303880342c85459800301d41140310f8060404c000c00c4148858031004044251003561108141c80f03100e1484821540c002c2d600d40d02008101c400304480c0c61058000c2d0001100c484000200c01801c0340e031900c3c1019007060102c034024400f50801c0b46110f0310144007030042030483e8501d1a02c130300586424042c050780101c418801d0f5180408203201101c4d03039100740d00c15007910086807050621400c06954406d40c0308003840408202d070f142030380c035403d041c0f8801e03003107a50010b03640f1112410400c5503030203900001403041c114880e5484442c04150381c821410b903940b02e0403100681e02c81c0d03000b249600340300004241901038a250004595903561254105c1555003440d0000a4004103070744046040403901c0d409190030b180c1e1184042004180e990040001c0524042c0d003509000409801c0300b424083c090001d800e481030603000800d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 642777149 1250 642775899 642775907
    0x70c0b07080702033f040c0e0903070f0f060c0f171509041419020a05040f0608031c0b030a0f1202030f040f090506190501050f07060207030305190615 66
    0x900240075006803800c001c40c1c00c16000780500010782c40188684905508000ca001c3c0c1c62000490b000300d001d4145d01c03482c1c19261180c00207040d104202050483c4d00c00039122590520641c0c1e5074541c88629208500e0756410b00e00c500c070001c2c4200351516841d05100d680f805000300040c05140d48161200c0390043d4030b0000120010038010112407904440c440306400c141d603002520b03481148960b01c0681e0700310201c10f01520b0984011107482c449001b0100403400340c7d45520a0100311101200c0118001045440c0d20703020740b106a1000105100c042101d42414101d00302e0f49002c5d540b03403070041200040301c40c100360751802c020030301400d400178a480781000311700040480e078600455401142d14000000c0001680d0f5405a440194211010002031150074801c1c000c0c0c42c0c01103001c841810100c2c50b292145403002409110380ca05018000610b03904512510050340d101580105045403a100a801c0c00760280c2800c580b06900020f0801c0b007048040e24900c46d07d416a81d18000b5410001c580c1e039030580b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 642778399 1250 642777149 642777151
    0x40506060d02060c07030317070503010b0301050d0303150306051b390601060309060e0606010f031503060603050706030506060c06220f0c0905060105040503121827070c0b0708 77
    0x683c00c01420805030018281c10008078000318440d50391820303500703814600010149400b03043c4108001c42000100000d0140901780d905448048a035541d400519240c19070060850344000e441181e0751400c000103015296201d28400c0200d01d40c0c04404d00344070310100c0018410b034860744120b0020803603503c030345007030303500d045203c2c1001440740d00c00502c0f644038030503e0071600760300030700010351606042d804025050041000e40382002000b003c0ca03042820001c2c0c010142e80030b801041640d0b0360260900008011040c01c001d41d0002e05c100710260716403c2c80c3e920ba140d1405240042030500c404075880c0c0c04d0120031502e81d03c03d40030141440792180b490100400c3c80c1c0784102907c21403107810100100d81140a50a80d02d88202e804420340e92411411405071540207044c1411701006010801c100d0320702107000500075440c100c000c2d5840ca19921310f240b00e4401c160704113400005a103160b108200d1311322484a056684071051031199a0f95a1040b02e48888000c8001c000300c0110020500e041d000d10005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 642779649 1250 642778399 642778403
    0x608030403051e1504080715110304021e1216080a0f1202071a09150a050409053409120809040b041e06060801081216080c060705041409040506060d 65
    0x5112200741c0d240e901c141d40e00045d6410f5904000c006a004200300383c0c4d01150b280061403250900805a03004240152404020070281c09000d00d0702d05800404241311101e6031a030002000c84804280d40c001503a541e01c00d02c0f0b1320034001103201d040400d9050000644d205a80c0c0c1c001024100101e842d90f891031080d01d41100f40c0c040d44540c1f4004030b44c5a0090420749140f2500b055040e8488580740d00b04483c0b6402200400000e0404000c1c9960b0a6807100464042e50b221030740100f00341c0c8803c02d40b000745202c02074941d850480b070302c01e12421920151100d03182060195a81750000d80e203500200c507aa21044000818107003080000341094142a04508480c000003007000602c0c02c40d20007820f82c40c1d100d6000154036940d9551050001a80000e055805070008200900341200e04600002d03491044180c0000400c0c204e10280c010001d1003001c4519001d071103400c1d100c1c182040e0101030aa904030740101000c1e080050402d803460304002000034440e5810000800c041d8540e0b00c1846400306102c00c4c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 642780899 1250 642779649 642779653
    0x201050f09210d140d0c0207080a080307090f050d0b04260912060606071b0f0306060e070219030f0c0b0c09040b01232b06050102010608030403051e 65
    0x10901503900d611031009565491468844066107001505042411186040050180513080c005040c0514402d6968120400f14009000c0c2c0113284103034980040b44e03201010f640b00d9101100c04000c0c081c00a14013565440d02d4102626803120510702e80d01046001d01070700003004034070342004641c5d40c418480d00140203c0300c2500490461814124002c1d03a12030903141400001449052401c0920071818840e40d0b800140030703039044c640001002803250980c09860200783c400c2080c1000b045400c02002429003034002d403a01e0f9641e01c0c0c0040901a1407003a034080e07001d00300000e4949800454499041808036403da0301c40d5a280c3c3c0d0559080c0c1d51107034524100195812082c0003d0a0928040c0c0500200b414068450400004001c1650490600349040141e60311034140209910030810444030980441652101100c41c0c0d40340c5644403c0804201c45922200c1114030106203900810035030f03000f03074002d00100c0d456104203680da10941c0300c0200203600c000c4200c0200082041045000622102 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 642782149 1250 642780899 642780907
    0xb0406150e15030d0c02130903170a0b03071d0711071d1501090b040b03040f020d031808070b2b050405060a0b030106140907020705030105130b090303010e01030201050f 74
    0x2492981c400071035400ca071040166144036428a0b00708102071841c2c0e02031500b1882100c25078085160040060712400c600c40d02c4004105c01c00d80500e8626550030180880500646001e0400002800f011154240a401001c0b0007240c00e0140b0000c042c4010070954804106d07403180e12084070000304544000180b4061001d000c544c440540701c544007002c0800c904040c0900b021400c082e21202d92020b400c2c14400c041404000036070743c101c16281240c12703c1e802140c5130b54032400c101c1ca924885d03d40007544450b81008403010144c1207041d0003003c40d100000002c5c1715403100c01d8a5600e240718011103001c550184112126148141c51140307440402c110483e010f403075924201c0d401c5d594161000c44854112a042029000c124840c41e404448106c0080c0041490101070107401c95160200c1801804030f80c3c00551220300030412903000f002d0160003000140703045101c5205d294000d0b40c0c101c4030301e001040491070200001041c0c0341620704100301920140d10399070054605520510b0000c1103110180 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 642783399 1250 642782149 642782159
    0xf02040b0a090204080105010f06020c060307170109020403060f0b1e010509031c110a03080c0a0509030609060105030f030306151e0f041419061b050124050d0b040615 73
    0x2050400c02010031010168549045c004842d003540d9058001b40203440b0710100c10000d50703500040281c4989001e4036103030342d01d85800004903160386032240d0042d2401c10700d13000061300e0070a603402030045170300441e02008015641c800350015600085a4980d121103012130081c880c41c0c1c1400003000ca001c05050030b610f0204813602090074403840c0700030305400048000c0010300d40c5802c40d03940b4190300400c0010b06040500c9a4024000c9040681144450b0401260700208540103108480c00040c00804070b038900d2801d003800316076600c824080e50380a80600002030540c01400003e0340d018a200500700034818a0101400c3c0003501300c009135003882d8203c00a0b064942c02400020f0020b0026044869641c0d81425600104040317004003042c001e0381c400018070070746403100d050a025130b00705140513101c80400400040c610410840c4c0a000c5501e4030302410b01e2655480c22901c480a2101070300d24003140d9031020230620002091000d0003140102e40050b00103800c981c44150b0305244420650049501c034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 642784649 1250 642783399 642783409
    0x603090a06051e0105010804030203030103030f03091e0302120f03180c0d0506060108070503010305190606091a09060405011505032d18030a0c020d02030f060c07170304030c0f02040b 80
    0x940d0580b40c20328458036641c0f21420424012805441c0a003010300580c1001c0d64002d50384c1c0b10522028041000c00380c1d1054000d072003900201007003030304810200d2062800241c42d81c04152082012405440f440b1a0b411414407010251035148882c00c0100d4291798907040941c42c02041684110918081e44010b0324150341d40304440100580184010442407401e540050000b00d8064100010704c1002d0004000043d4006201c1c022010012100c140c40d00e03051900501804180e0400ca00142c1411010314824002e0450403c48600403070340e08100703440d604140400c540d800c1c0148184203410604102e8820b0084009507004108070f4078500d1000e80b009103560352222110080d01d03454204c80140642c010102c1581404804001c000c0c44c600080b0380380250001261078402402518400615025503038140081d207107000101d000e0b2a410301d0041d480000c1270380102c20031103010150681d0b00c6c0706842c0c024242d034461071b0b154440c3c00b1030346050703240c0c50910311240744d049a0180d142c010064640d100c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 642785899 1250 642784649 642784651
    0x31512082208070807080604082506061d010909030207030201180510080108010c080106090501120603060e0d021203010303020a0b0a020c150915090d18080601031118150603090a0605 80
    0xb4a202901d00c00d41031400660404005600881c0264446410304c004030388090100ea00b0002d41d9814071200802414100a02d41b82003040604681c5c581100020a1a40c050310b94070700d22a0b090010003140c2e203505250b0101c07032080074040c0041e0b0102d01c01340010b50003400c0300240d030209040c650032440d55900008213203014020795100000e46d607900420800809001d01d00c00030070203085c00482581081ca000b04030741c12510843d8104003109014100c0b4845c2c5034420b00241d90060301c107011014000361166502e544051641e00140b1800280c3c4101005800507641a640d044d0701071702412801d5280c61501c810041d08100165900300801000340c4c01c2084203051705442c0c070320014031500c3c0206040b81800e8501c12040040680801000314500300440c000154844900706800000451441408032010980040701c0a1013110004824440e9440041007e0707103044600100c0450189100c00305410281c5490f006044105403003105481d240c03014590245100d81241c000f0b50b5261149001e03140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 642787149 1250 642785899 642785909
    0xf03220c0b07060b011d01050f1c05090f060118020d020d0903020c0f100801052107060926190201020325110301060806040605130b0a05070315120822 66
    0x10000389400c100f01040c010ba0418400900302031a543c0e030021185800c02c2601c44000d810820b00060045401e140d000a550b821801096200202e0495520200081c40d09558062141c80307007150301449401e00003101810307900102a071010010880e030144002e5000104540300254003400a0702d07010031035115404010380030341d004200626901081c040d054002c0001d040c041c50818091031416038004076001d0444000b03a907035018000119071844c0b441800180703603035914081c1400000c0d880c5c1d80403440f070007a200300a80c40c005440c1c0c0c0c000c100c418004041b0541701941c012076169404010214419002c0301e0041c01a01c1c980082600c1a2442200c0d0048403a040748201d031007101802242c1c82c0f42c15450a0580003040154140320409585445c010001408030341c40b58000b034011002084842c120b2035000c50403204a00348441c12801030041202d19500180c642015a06c40d40c41c030007045411a20441c00120981d2142d841c1c0d1081c0750300403d1305000b00d440c22800c5048001c012030084d00201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 642788399 1250 642787149 642787169
    0x100e070503180d0e090a06030f0804140105040f0302060c07030b07030603031206050303160c0504020f0a020f01141801060803030a02042301080a0b210d020d050f03220c 74
    0x850b000c210080701200015007050240d001851070030419400103041c0ca03a0f2001266170b40041d5540c092050064141c2c2e0300010401c1401852420070041ca400c00b41040d50104010750300e540000c01d0044170180500d20603002140300b1714000300701600380b034401850981612810341c0c80c416183e4507003036410071040d140030f4000f90b13980808009050348403442820000c0700c028144481450407000a6036400344600210990081480d08000c000245a00900030b2602030300a548816040d505100742d5000184058090700580b219074444a806119108586004600c01d00e441e464511084142c40c0040065690707640d6a444041100780080025502c81c9400d0100580c1e00c2e4104540c080089040f800307901002008281548042da8100d00c800e80d03c130f5007003d0001000e0101000007840d22159030f10410140050440d4075112181c041a0b000110071a5021a08400742c0014204d50340c2c802c058002e84d40d00c509201090350103807200f20f1005030030340c002c0e0703072410030803282d1502400840c0b980d100c01061 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 642789649 1250 642788399 642788401
    0xe0a020d0c060f021204140613030602030f09010912050f0702040e21030f0a1802040c1707111f0b10120c030203070c02041e0f20031e100e070503 64
    0x40354840f5118940d0f00d42072000d045400303046035841c07049010318020a00c10603410381068140d502d5010581c1c00c00c00e01e958600e03c0321996828864001c6d4001d640c84803000103d2400241c10382014050301080944c404a10040788a00042c104c0f60743e00000754050504104025071000741c2da0700c0c052006000100009000d140300943c2d003030280038617071b010910a100c1c824820880d640100703800840c6d219400000c049a001c0c0301000003200701a040c0c0000358080d240001043c0608c0e8040c213001d11b0541840751908450320784e00419600b0301c80e01d15240c1d4603507210280880c0c00c900c1024044441c66801000420240d4000700015940c40c4030040c40c1c8000307854000350244500b0240151001002103040462650501002c000c0c8a04181c0c2c0e40a8000e588030480d01440480c1424000103100d01c89204111840401a01001904051240f21500c1c1d00b05a001100701004008481c042da100e00b1544041001c2c52050900300b020080400300686404900000c0c00c151101601380304504030b0f0348003a5a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 642790899 1250 642789649 642789659
    0x80708150901090f080a02030708030a0b0316050d02011101020f0f0c16120201031a062d030606340605071b051218030111040810110d0e0a020d0c 64
    0x8a03140080030201268149000480464486400000d0407600038011a030b88040e81803060380f45110700500100000000030400c200c51310780340d00200011104a0503107184070f0036036134508685413360048941c00707004052440300642c003500d0b840e00300d40c405000150a02d0311501e020345860308140a4030700e0000d0001070541180030300384550b00c00d000d0b803a00f10514642c2009080320380714142d0803009060540c1c1d0420310074804641100750400c444c00804490343da494920900d0251940b1300010302ca881800303e00d40f1301c03400c80201074901c60580a04079604103200b20074440801022040000110105120f580303400c03111350860b6501c4580180c1c40401d86040c45103000703120b0404900100c0c0400e4080300a42c00056004c24804200942100400d459195080510160100c501c0e81d180d4103629260001c40e1825a03c0090320031903559100343d9000312681c124940640e041144144404c141c104456078034403056510401e11106860300302d500c03035126540402c004c080040811f8030446092041000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 642792149 1250 642790899 642790933
    0x170102130f03050607031806061503060603020306030318010903060f05040c05090601020c060a030e10050f06030a0c0e040f08071b0b160f110619030506010f0f0f0504080708 76
    0x521035125a00072441c07440d1119516442c01404e80c80405850350394075402d491948841c5124540c011b10100031180d940da503041640b01c03184406a022900741040020010701a00c00d0b41d21640e40900a9460320700041c070094440f03e04000e00ca41449882080440818220300c504030320880140b0300003400d0700740b40c20400b4111003598072451040d40c0900070410345036404a90810385440c166513554894552000940290580e5066645035200340b008009000400fa00200e0040d01022010145a241c240074141c4444803400c029088181c4408204041c4100d0314602d0b620901441091030219401e50301c0740000d40c8504030a4925042031070902c03583c5401201807000809015811710724000c0500661285945003800190a800300e820820082c012000005841160014030485d524404c02c1d1001c92507030b819550140000f0300e0400009c50340d502503501859841201d848404400c00103075004c8542c5240c0e03000328000c2080a00c030000e4a03407020007140001c3c103076407405070007000c2000444413 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 642793399 1250 642792149 642792187
    0x70203011805030717090d030305180d050403030f0909061508060349120b062a010906020a030f050f060609010f03320f01140d0c170102 60
    0x9000108003003035240005200008850044e80e000c2c5041040440382c840d6031401d4011101c0c801e812441828050080650543c016846103862100c06104000c1c0f88940e690340325206645c0b100802c6c000c00c07040c000300b402172010800c450305501d4044211a281c0440505980f00341c1d1080100c0d04001c2001c0a00d960041c0240f81c1c080019401486001690b508543c900c010784805645801b081400003941c2105984090002c499a840000c2c0000070003880104100075a1001c2c03d041d51030140c0018642c41d0040459407418000c518810302e4480340b40c004151164040d0640c500c1b03640c3c5a00b00d0000600b6400034020705110750b140004c0c04da480c0303d440701c180c90300204005e01134a864002c103c860740d5144150b402c4c5100c00c0c42c1454a01c0f030003d000740c00410710980c0700780d00c44109144038280000401111640781281e09030107142034a4211002d002d13500b082c0031700c03101c2d0341d0008500400b43c10021443c40f1164014002d0a440c0e0740d5481400c034205c807981c046a0348a035000a140c1d0382409940301d0030307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 642794649 1250 642793399 642793421
    0x30106030c0e18101a10090e07020604030e042a051e040b0d050714030415060e040507030b0601050d0608101811060703030207082a1908091206070507020301 69
    0x40104004405407464803502480310100113699a207008a11141003144440e80d10a0f01070140d55405281c030b04080c04018691241c03201140c43c1000082c1c8592020400600540e8551560740a803e514810400588800050000c008458070326210411240ca13100c501310511903292596903140d00c00144012407203501d09100c240d0000c003c10000c09a101c4100c0700326101c4100c0014094580d84000c845000010a09407207495010040c40103200b01110780144040e62070300c003080802c1d81c40c00b00e80000c1d00c0496001c0c015030088081000410b4106035801d40c0001e05140083c43c2c010200101c1c07044030100c0d0041001c030380c4100c0d00170756050181d128021001200c40c0c240410354045a0760303255921007000c83c007800f91a0100b84001014000c2c8c060ba60200c2d40030403942d4840c040d0700b40d554000e25000d194400c50703800302100042c01c444045080c160440144d0b4514a0000c01381c0c071100025403008194a806c0500350721010701e0f0100a02c20035000352455650300e6542c50f02030040500751034540000e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 642795899 1250 642794649 642794671
    0x30e030f03040e220302010b0a15051c1b08040b070809032218021207051602120a0605180c061c0b01030e100b1921060209030106030c0e 60
    0x680c4156500001030354125101c1c80e445142958400303500700381039400854070121106400034003404168064020f4040018140c80d0390b1640c5540b80e42042805110618000200d0340800c40c11401c81e00000c6100303051100c4000220306903c00142c094410343c40601018001040c40049c0020080e0680d504d9420540524200c813040c200780e00115142e00c078425400d10080c00d000b4201002080c000112030052034440528088064078100800203540f002c030503040a043e142c40050011030007002550b51082c01c03041180c90100036035090000706040a903240314503100703003001100081c1290080600c96410341c40c00b00e030301c210804510b030328180b21401003c1c414442030214004500c0c4040010390500c040301d801281e20600c2c0401a0020008104c2c441d00a0082204880c10008160884074104600fa5141c4040068880d40a0080f0030b140c025480004600d0041d40c04880e1008289001e103400340c3c40040c50040382200190031502c0036402112840110a810860403a842690603403003140c14030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 642797149 1250 642795899 642795913
    0x603060108030a0503180a30020309190302040e0a1202031c0b0d06050702060702101812051215100e010206010b130f1e120b0f0411041404030e03 64
    0x58080e4407030140d540f0311010010b01000046218240b603000c2e090410f5070f801943d0051089080807503036100c800f10281110550b980b20514a80c1e0b9a5410303000201a0b136014604101480f41042041c1d52402440c030000c102d0540c010001d070b640c500c40c5a200c01030103030041060054a24255480c4070100d501c040544d003044c81402c1303122000c10860358201100703103c002003a8826800040c4044a0050017174403040c07801d000c00c5001600021224001e40d160b400f128040b448108d4030005498040e001c1042216a1030b912000066008900080350901d41c01c0090412400b00403280702260701300c0c0c0a01000002e1881100c041c2002101000c108159192001021490030f002039924401031003416280c03030700015222a1445417840c090041d10f44201c00b5012aa65801007001c092240c000718007140701d20000003c0c580407015001880a070344404400364076590000d00e500400c01c0180240d0309a1040300c0000080e65442c4141d40c086c0028220ba0521400c045c00d00610305842d028849001e80e010714 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 642798399 1250 642797149 642797159
    0x1090c05030a11040f02070b04050c040b060408120d0612060b01090603020c03120c0d0606090521250506030702030a080105060421110a0303050403210525021c0b06030601 75
    0x19103d880c041c0d0301600c020a074044600c400c07100a104d100e0000d450700380020b080c4802c00a000c0b07022003207011708807420300541444a0400c541c922035481241071651001103180100e10340308011b008924408040015480d650b00a01038440c5038170a000c4411540e11a41d4040740d6806c003901c00c000c1e000030b103421410804c200d0b8403c0d64074811035a102c0c040c00400710014410300d0720b85080f02d0080840c000140300681d40c42d4401b60980d5443e0040c04e22030686d0280311000c0040c5043c030800040075040090005c240340f48012000c0c0c4440f0020701c1d480c2c2003c9000130510761549002907004a15035401180d03100c4003081c00400220041e003045115040411040000300840001d000300144031440000b0410090f14107140819145060190455006036001040c180c100e800713001124000e0755400c1980d0301603110f00840c0c07154202ca07140490b4051103810480488216607276842e98004841002d180381d1600040c860350006150382c042c0b03041020941c030400603803180058010000754000e1050f94104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 642799649 1250 642798399 642798413
    0xa030507080913020c0c040506040b0d0f080d1e150635040b0403020607090617060409060e01050717060901060c081308060f07080403020a060e01060b030901090c05030a 74
    0x48a8060a403441c080b070506800d0340c072011a00865004094210355a280c40b1060075201e040844401d40709501c0d00d40000c54600340f5001f903078010780e4010001000c0c5059607480c0c1d9410000e40030300380c1d0701d11014000c2180c022800d200b5a8004c034807a40082072840b2440a40405813403581a54410469800742d08000058204641b00c1411100c0640c90204030b810020f0075141c0c80400c01038201661940c000c2c0070074088e04440803170055000758240c92071a51104025600d1303c04500c074600001e6401c03000000070820065116801100080001c182580d032500e8080c1501c040040c03500440c0d666100f1300c05110741211801d81d10500090604809243c20700004031001414440c0809200c451103805e400c20010700c049844a0b0100c2d41000c07001c83d1150307003950380c4c1c18048074481c0500b103500000c107a41c01d00508049204c1c6925900415070186141c1e100806010100100c00070b9640364040890022402d0014500c12a02d130b02c0006800411420028558212340e4030285c02038000b8145180032841c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 642800899 1250 642799649 642799657
    0x21507030522031220040e011d01081506130507080114010c24090b040c210503030402191511060a060503120906070206030f160e031005040c03050d090905090a0305 72
    0x8078107001078030708000c0503082c4800200d44000800540c5c0007401280c00888410140c1c1600e003440488001081003061070254800280245803507a40001510f00c0d0000459203042c2e8400e0014100a094070414440c1e90141e0360140e4505020a020030014449130200c45544c241c074410900e03001000c48501d0f20341100715034400c807403134a03100e040301c420580380549608800350146c0d0240102141d0319140c2050400c4891502030041100c81080c02032000142010503c01c600390401e000d50300d161a02da080141807842c0c3c41d0382400016074000c00044d16005002c080807119465140c0360310b0b10300e035940058184040144042246480c020080c4004c0e1400a80f050075402d60040060751402d201c1d0004961340600310000350301100020401c807401e018054154019101d42141d800c040d440103206482d00081c030240c0c250558468107039003602a956801c115003017405a900716846035140e40f82c0a09180b140582e20700401c3c0c0c958000c01104403e845405e60085030345018280e0701c5296a0000e1442c49 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 642802149 1250 642800899 642800927
    0x5040302120f0f060708090102040e01061b0606081e060108150a060f12021003050f1506043302010b0a050103020a110f070510020c130203040302150703052203 70
    0x9110364034900801000c00c10000300954850071030b2488810300608613558a0100e81c40070010b80081e02240070031505000b03940944409068030301c49a800d2900444603a650007a0711000c1030031840b08200420003032700c0f030500500102d10182030003440000064481c4a0191041c0b162a442900104105600032811071003158500b03500c0c4916807909440031024011541207200d240220b5000002e503044501e06803008507209444001018040000a03404c03134408850210566211400084044802d0700d040d0300c101000801d0a820203880d4000807401101c40088500380c0b00c004850007410300035464180c3c4c80f01c0a90300c001d2241090350004507992a190307100710313818550003140c03100505000300b560413110520f1604a400e06802e030711034aa90b801c15482018003c5050300031100400f407011924490401c3c002c2c00b13281178904010b5001000703610041c8250114040e10403100300c480b010060b000d000b002c43c0c1da0042000d04180050442c01c20144251030765000b400c400c2200040d8200d0115204c440c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 642803399 1250 642802149 642802159
    0x50a06050f090d030c060e06010e01060c031718060a09022110050613090f030f020c060418090f1a070e1c05010e030f1213030903060905030d05010909120f05040302 72
    0x4045441c003611000d40c1e01c48010f0090b4145806c00702c01f5400020214101c607a003012100150744e0742c2c48107441c0c080803144060002544202240d001044522020760840881c00700e5008140d1454038003410603e003964101d001507140c5403c1070942c6046c410385945c2018a840060060191000303071682d0341104140c1850040c0c841d000a0069a602c2c0c94842c00c1c07507c80716081c805001e007480d1888560040240440215480c43e9081c0e00d507a1000407016046038016000c58035042c14031070742c0303013505000d00004075046845050354400240702c000c1c11840f81c0c3c4540700b100c0200d00d07614014441d1110040c07800003005110403820003151341d40c201080c1240c60031081403180310018202180944200c82823403040c0d00c4001440400350584400030701c50300c103140a04024507100c10310710b910030601140d8090b00181349500280003040c1203911503032482d8441c0c0c044910b09142c480c5654240c6009074045d24000360340700380c0c0809010100c2500318a41c2a180f40c070103006014690090814055408064058 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 642804649 1250 642803399 642803419
    0xf0f4a0109091e020c010f1b0f050306190f090f020a090302330912060114060d0605100306030308090a0201080a0c05040b07080405011706090103060e01150f050a06050f09 75
    0x11010f4681c501503c050078000e641e1420700b00842806080c002000740801c6240205140001e0307030100032440082041c0d605c0c1d00708450300e600d0440710b50300040d02181c0c3c000380360400c103070b034000d0ba03045c1d0300b03000b080382d01c1c44143d0191409002104554502da100c207615070042080c910f4890b0301c410444107a80e41141d4020b080c8a0000c0880c03141d0059900d00b4042200140c0354841c98000380000d00304444080366450300d0101c1c13800405807a058203104000c2181c840c200c285560317240c0b2502805420480110000300700780d1319000a154407100c90084000320340d036108284145540000c806501c5100e50000b0841c141043c1d0008080a5000740581112540c1e089450640d0307205108403070080140041d01600c0751180e061145581d80140300e05408203200f1030038142908000c1000d5441801c004101041681c6940c851401400e039010048405541c2c2d012844403040201ca09031010340a802c0c00240c005040400b0703c0080c840503004001445028468408442060000c132140140c09440001e44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 642805755 1106 642804649 642804671
    0x10905010e03042c04030c050a0b04030507060c2d03090209010311030f07060512060f09070c03020c012f070b03010e0403030b0f010f0f4a010909 64
    0x242101800005c020038003e0035200e40b550f001d24103448150300e040d901c10011540c120340c00c0300401e8000ca07230a403e0184901c00c50303100184605204104c4031504040c9800c4200c13092070180034038081060141200d1198010380d14580e400f9141c10742e956101e01e003001a48202d4007100d03020b0303c0b42c03103004d0803030800004404048412544032107260181400d400842e24400a111540220742c1e01b2044040741c5421f510548075100740d680d001c1c01068249002401d043c48046028100710f814100d64000700301c00410a072759800380b01d02d41454110202110744c206811030f4040f402070b80d00032000061000120b840540302d103202e603804005d50009803080104a121241c0e4150001c2d410b0260100480e00071a142900455542003244022504056400b060740e00f020001e002180c00d0070001d6090303849800603a4400301091801d0321401014400285032014910481c0509502c444181c50 = true := by decide +kernel

theorem cover : BRFrame.Cov 642625899 642805755 := by
  have h0 := BRFrame.cov_init 642625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 642625899 ≤ n) (h2 : n < 642805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
