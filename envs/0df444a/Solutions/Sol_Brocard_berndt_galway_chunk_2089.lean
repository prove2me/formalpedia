-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2089
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:37:35.85039+00:00
-- url     : https://prove2.me/submissions/b6d1c2e0-8124-414c-a256-6d4fa0dbea77

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 375539568 ≤ n < 375719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 375540818 1250 375539568 375539573
    0x50303130b0c0a0f05011a06070b04030305060114070b090c030705010c0f020604050604060e031203040f15020d020f0304020f0301140c07051e030307020f0106150507050f010c09090f110304 83
    0x15402202c0d41404078424100c1c00f40c003150000c414241694014000021550035119881f240185140da240f409540d0030892803000a0040702410380c8243c141c075001038280c071090012a100c2140040090a49201050070b03000e0100c41d5000502840040f07086900d019082c00c14036403120580d00c03c042c0031035626000040810760404040545c5071004100c41e2601d5143c90004115030000d4000000164138101c1144003800d041083c1c20300d44040614590440c603003940c078401c504d20341d80801480140407885081c3c490134950143e480c801d50000096440d40d09120349a00349030411a01603205111394800204981010710075100f603020318003034108c0c0c2c03aa076500080040e07a020030f8044400c1d00c00d80e490514036003580100701040080c240c02031603030390411400c001c1c9480010785014001c3c1c1d00d0000200000590340400300d540184904100e910b80e0040d040c42810120301c41034000280d401c0007110700281f40d0055182056503030480b001c11420b10000c01c0342e000c5500941003010419801c00c081000f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 375542068 1250 375540818 375540839
    0xb0708090415080f010609090c0b0703140a0e01180602150c0c1c030f0c021902120105070206040308090606060307120209030a080319020705030304060513210905030313 74
    0xe68500c0900049104001503141c109071000a40c07000006401010303a8198182080c0107150041032201e00511914109458031540d540d424443e007140710400007404010140145100049031016104454455010840180076070009d1125980021300e80c80e00c01080030040807211003651070642c02003203120500505a0040c0201402c6c0104188051100b102000c0e010000075000c2081c880d540c0b00740000d040005000da540c60084498007a007803201e0b50179400d0380010103041c1d00080503001c800350581400030070680c40091528501c2d07542004200310032240c0000d03041d4011407299441c2a555914020207030f07240c040135182c140d8000803c1001c10b0b0400d10880d254200c0e07110054005203072101100c00280360540e940c0c4225619240482000820b00c00c442d142c0200d4400c480003980707080c54980d05d176074891000030700007000300399568041010301e80186001c0c0207031036215600d1004400c031845003100c0075507986003074400250040c101090a04020080c0d425004003011a8030000d0704001c6c0503007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 375543318 1250 375542068 375542077
    0x602012f0409050a06092904050a0213030c080d05210a0f18210c08030c040f080102090a05010e0f0d111005090a060309080418060312170106090b0708 66
    0x80c84440521010445100034840d103401070701d004000252252806201c0801d90304480180c500410300070183c0702051454215070f42914004030380c0002c540e81d40080010080c004d010140d80928012903000c001c0003a0814440305888000c0d0488081c90000542121148a4504102d00c895a50000d50980007841c45405401500414003c645d5600a82c508004c4500c111040c51301810103200c1c3c50207206518549480080000800c1c00d0390f01205240900030131040311004008090004c00a0f485803801015a006086601c09600d10103644102d098007030340010b4a1984517111060001500d980144221b08051401030240300c28202030f6000c00c500f6800c0e07c842a544c4400083c005400c0d03036a0510100b444024980f1303280c0d1100c1008081c807804900350b070092001c1c1481e00c90304030042504401a1822990725a51004080005201d0a00544402d601c000c0c4484144d41154000680024084400804180740c1c1f84003681da0750030440301110039118080b02a0030800c245004280058001c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 375544568 1250 375543318 375543401
    0x1c0b0d0602071109090a0c060206100b0c0a0b07020706090b1206010309060b0901121a01080c060f041e0503011503020907030209010201090803130c08060606120702010f060306060906060201 83
    0x1c0c11140f0000214050380c03403c94201c00349130006094442000254204000500164070040c00c0ca4644001100c20580e128082d5408000700820641404201000905007490703215000002c1814100ba02a40c1c0341c00c18010350011441e0208045448005c01c000d60790800c1441e281c00d04030751034a8005400a115000c011b0784c3d02610303074004076110746454411500074620301a41e03680e013911038140103411036100c0301c2c00c980c044048401002200e00008443c507280301c00316001d55803581d0b04001d1401c0c40c45144c2c0314071070100e01e034141060002c2d8417914850482d501a0003d100c2c200322140c00e080c00b5092400000e600c05101d1002c61001803195001c0d103000b5606000000e100401c94032014190303001140c4441d07001201d104a02d042012001c80301d401000070000400c41400e10800080150280400140d08200e4000005010303078401d401113004074156690401230980c0b01c0c28100040c182d00d00034240c0083c100307040010041d205120300ca00c0070404000c505610f09000c050203d10a401078600d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 375545818 1250 375544568 375544583
    0x10030b0301050403080702010c020703021f260114030c03061b041a0d0605030d1b0c170a02150f3009032d03270a0303021c0b0d060207 59
    0x890405840c2442514000d90003034441c49100e141081e0300a09407200c1070212021908095000c2005031210322003658404449040c49022000310042110b2b400c0381000782c2004486014206603900c29654103145c180c81070400c0c2c544600c0414402e1584c0c9a400d428802c0d003561180e000543d5001c14045002410840001c2c000c0c40e1a6450f0705181c00e0381250380c04541d03010380008002d00d8145440c464580144819401ba0004003c031340f1004d842007200302003030140780131500c400c0c4c0100900d00840101420411030450820089920f505940f00000d4000724015066a001c06940b1030180041c0c4071070641c2500c0551078044129035115020400010f03900e0002e4484900c0b4200f0340c2c42e03034105c612494130840119111880074441c000392031031a6110440c4007401d10344207400c15046804070380d41b1541c0c0107602c000d00303801c10701c588007060000700000c6072030b025030540c02d020154540c0040010500e09030035030103400400410340d0b04490005501ea0b40c450180400c43c00020300369000b4180781c5014401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 375547068 1250 375545818 375545831
    0x302130207081e0f0a030605190b0a03090201020304090509100e120702040f060b040e0a0606030c1d011707030e0606090603150901110f250305041a070c090506010f05090108061003 79
    0xa144407036005405c808012940f21801802541861990020350001007195601050b1401701061106d1003901c3e584010076483d0031945096900806c1150014071042508000614000090540751001c0102c0d6011150400e200c80c15684400901240846c0e01100800c1c80c100807a4200002400003807060000303541c88460010f002d1004a001c0d000822a9091035506840e0518000307003211610382010302410315040340c1300c5603030f588412480c505003090742c54901d442c185070700182c45865240c40e01d6800d681280007086030701036264001c841d01240d023408072a0543c440d08100036010700b04540d10350300b41c0e00a510158441d003070030003a031b40c02542110002800c1c1c69444840c4645900400344a8030003000003c0b50000b6002e000316121004500110260890103a079a00800c50301c241d100d03802088800c2d01040000d901110101d80c11194409134082c0d5650795080d1690151900f00c50050114041c0c40c1c030031003007902510490300c1001c416035500303095503108010007250918520540e800c0598401c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 375548318 1250 375547068 375547087
    0x60d0c062f030a0906081e0402060712120f0501080a030c08300c0304170c100f09020306070809100c030204050d0b01030c051e36010302130207081e 65
    0x803000e160454890701656499106610140c0341c01100d900c0f00b03007080412410003603207107107007000d403500900e04030042c5415880e6800015850b0242020180446100041340180107820011400100072440401c0c40800c0e6001c0307460044503000d110b442c0c0d15400c00741040d800a48155901c0e19801e00c101d03000c5060000504680c2170485000340c80078840c03d044060f503c00740748100c3c0007540c03046030b0551043c6103203017a54031000900c10361241100d1203200030500040b50300f41880b607000013101d80c0300d042103d40030002e5080701610b40800b06901a003d0000440c050520582c0315611410102c00203207115440c1d18a03c90083c0100151100ac041d42030101140380d40e0303404c0b0152901e81c0200140061541142041c842004459104038031800302d007064108800c4503090011600349044a4885600c81c0c40036004002c450601000300c001410365131520b0303400794a6440b560680c5e00036146a0b882c0c54041c1810300c04c07441002c802a01c449024084078000140e1078040e10b0550504c0003440d8200030060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 375549568 1250 375548318 375548387
    0x90b041119080f070918020d02122a100215040204270302070602010506010912172a0c06030a15180c030e0703080307180305070b040e060d0c06 63
    0x1034001c800b154005032218448a407081011001400341d02d001007002851180c05010403982440c002401000c04140002c1507686e030b010011603d040b90003e44d01c040821074030140c80c14540411107080d0841800c5962010700741110440703820722658000b04083d05c00854541401040104101d902503101c2c000784286142101d0700e164810b4116a03a0300442c3c03440e05c1c1c007034108070083d00b283c8210380c50721040001c20381c2e1182c0c00d00b04440081074240400d42407402d0031181080c54070840d4015042c0081c6410ba200c03021100c082c221540f1400041300b511040f507510341c41d0071004006503401807051020460000b06940300d95100502124401080f0b5a40c002c0301d000400d11100c3c0120003961148002e02d29501070085001f04034100780078190340ca0641c1e035540c0c2c00e80406001071003001029030380f00c0c1c078010400f00350b0300146030040100c649181e0354561100c0554420700072101100302520100300300781000c0c20407009080d440504062503500380704080b1006501c0000041d0444c1e000780340022641d981d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 375550818 1250 375549568 375549619
    0x604032a03050304062003130602090604060203040510080f06100e090a02030703110306062b060b030709050105120103080d150f0608060a0f0b210a051009090b0411 72
    0x81e840b0039880703103028248035044039003070441902c0300028880016628844001120742c4011143d011407003140076824808000d005030120150880d00010300400c030250000701410486000701d504d81115903000307600701d483c41c4040c0c07000f0800c41e88010108540d40f03407101da100e035901910315106181d0350340e07400055495502034495620295001040c0301100f903150182d600c0b10950b07104401c1c43d40c03d110001c540544146203041c000f100081d500c200c40f803000c01006880a62042e0000c0c03120607225419008154400d440c8074000c509005000030301c5501070400e0790348040b68190a0202c030381c615100e01215a202641c0001d0700355940c0710030600103046001c0d6601824081081064103420220041c02c6141c02829462058013200001c211410070b010310300c02999140e0700381c2070b12581a8001e0500c000000c00c68001e040002ca010402212681d507c2140310f41d001e444e08003d01680d4691120855000e80c401030070101d00390300010b010410008114000c1c5070064001340b0050b4000b41440001000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 375552068 1250 375550818 375550823
    0x50102121012020303030609070c17040801050f04050a02010e03101d01050601080c0d0b030a210306050418030507020a090203010303091503060518060114041502010e0a03020604032a 80
    0x910350240040100c4035052440a4800c9088620140580d500000d0352400010511845084000d00040f0002d2150391a90b841c550300568100003289009807180c415000381c080c408a0358038150005500030030400c412801580c02c000600b40b000800d03001103030700441c0a41569054407803811034528800e10f900c81d000040100141101c5150180c1164509480c00580424100b00c5c20700706118006010f1000c079001802c030342400284040030035005c241861200100500041d000b808007040b18030400f01503104085541da01008119110001c100448803c0c0440d600e00490040c00e0800090044004200540c0020100a0400c1d61241000184c1c0c2c800d802c1200000c49445003004005000907003036080c4615030a007481550f00b004041120450040f162080c0a40d049012401036402040f0344c12428a0071a82603660326200c41c401036070718101e000d02c3d40042d0b1030520040c071001d00210300d084075264180d014000719210ba407000c49180d02580454240b540c1c03c2c80c82c069004550010000c601403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 375553318 1250 375552068 375552097
    0x90c170705030c0d0309150311070606080609070e0106180b0c1c0c0b06040c030f062919050a1202030f040314030603060703022a031905120a1107050102 67
    0x9042a080c542007400d46141140244080c0110b40700090b0010b1a940941e040000840e074100c00302c01c0118080c0050300300e4405181070004ad01c805000c0381e604664280c0b00c0f0300080351410344580360010781e141003034800d4650030100d0f0700041c081688520404000900c400c44244040b40d103c00c2c0c8030417250b0180c041086203a210301c0d50f4034034014140304422103045407814082c0d100c8200d03455080c03050100520f02c4d48115600c40c420603000b4042d0f0300c8442c500c42040d000700312f001d4803000a10b0348030b2088a01030741e2501012111240b00900340c412260209610319002c00c4900e00300006450b070360000c501e001c05004612460340d040a4040c406544200074991003550b49042c04d050181040340a951a090000c40800811005803400620301e82c11100510700143d40b506050134a00c000500c0c001404160011400d00c0500a04000068001c04015042c1d607010220004019283c038031440744140d108d044413a0000d4810b134580e80c072050141800515440c5403007050741c0d0392401c980c0102c00280703000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 375554568 1250 375553318 375553333
    0x80f0f0c0603090712030c1a0f010b160b090a050307030806040c0c03021b0a090e07140102030702100806130203010603091502040609030b090a060e06090f0a080a03090c17 75
    0x42508106841000000303a450354a14101800681d4882c40c3c41e008110a00d0000c07404141094400d40d40f20f40da40d50000111a070003d80190b800060300b000303580da03e2040300c0542c0042982c955400c1180d4070306105510000300318200369100b000c2e24400501e401c41d14000d00c400b290200d8001c4c001454003d11a44e0364107020b14042013003000310380a402030741d42040014600c5400090300014a480d2400c040c0c030a40400d6094600024082440c40d00f0001c00c407801d2443c0e9024a80c1e0005200d001c0d5048039003100340648176140120798a00481c0360103544500d07507600051419014410f100e0308600b002c0d10171212030310070500038004e0381d0007a80240d0001e80e80d03001075001c1c012400c10580c1395001800d41075107014074100c4014440368150001070824111131000c108071100806c01d6204490340950144040c464605100b5200c2c03104841d8441607005900001b000500086804c2c01c030b09030300c0a042c1e03051008408084008100ea5041158249220781c008a821084c4c07003809042c14040d5002800306 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 375555818 1250 375554568 375554593
    0x209090309121011122a0c0a0303060e0408030708041e030c110409080318030705100605090c03161209050a0537030e270f070509010e09070306080f 65
    0x3110075005030131658800c24400c100801750f010f100d650300400320780440002540945000c9050310910b030070012808000150380d10340307100b012880b04031a50080d2400c1048a0b070b42e683d00e05200c4800c45d40107003001c40403c00254840e01a00303103260090300078000c803010101c4400e98001ea1300c82e5014240c01040c403081c03c2804104034400e00e0521281d00f0b9509210f44c11255480d51000d0101408000c0302400681015a40b01c00401c10385a05030b80100c04c031a800d01480d070400c002000e83d80203842c0100440c80001d40000791040403640141c103a4402c15158048115044450172007500d0f007680c540c0c0c0c0f20349143c0040f4104004801c115400b035000740c16031309240c42440b4004000c003280c08500380c0401142c03e00303216040100c082d203250141880c000704a09180020a00e48201012984003d40c0c0e20480c02900781c50020320b4800c640c0c04141d04410b4640020a03a900e0090304080343c0012451100b15110f4201030942c203400004605001c140c103a144c0401c00d05206a01505006650060352407044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 375557068 1250 375555818 375555821
    0x1406040b0a0c0e10111b0405160801050105090406050d0b06010807020106030c0b0304050703050d020606130e03090409061b03020c0d03050402130e0c06030103211b02090903091210 79
    0x10010703060181000421030501000e0100e21514024a02ca61900030460290a0181d04900385d08040141501e055000484c060070344211103402c141e018514020004044520480c4a412000e5030b5450b51150313070380b810380111030075441001600d8100c0d46611000469440e01d840007040988202c50030356582c03404000050175004020412000c5a04088003000800c0b98078101c8019500c41114aa560340c2d1030b401d1923450702d4100d6100811030311483d540c07a03103c20f501050041c02210200d032220031451446020760140e4040e4071051140c0e400c20002040a0300d0160b11022905115980200e403e02d00c00e015100d004940080b04800f0a03000142c44907204020300206094541d00e003420091401c1036000315001214a44150130b405030380b40300d42001b0300801c02054021702c0005205c0c0d541e039a100e1800105100c0710f80301c414000022000b403e54824090440c4900d40c0c42c1080e03000c6200030058003002190500642140c007203000030800a0fa00b511034200c1d0040c00340c40308004003200082c0480000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 375558318 1250 375557068 375557071
    0x1c0224060310020f04060e0301020c0618070f06080a0209030109050706020c040b030312040f05030405030d0e04140f1302060c010c0503040203100c140d0b220e1b01031104031406040b 80
    0x10402441001001c000f02860020303170303081e1042407801c105445005804a80280320300f450b84580c038840e0034104064410f0640021aa080c454026621030503562901480e84080c00c0c042c0b50007096650340052440344c40c5a0103001c1c010f000800100e41d000c460f4807104c1c10100d8580201006030064070f01044030b4102070051b241034034004d800643c40c280d03020340300b0480c0282c00392000f4a0042000c01c10384c00d118040082e00c000c0c3c60000d0581d242c800c0c070602e010340380342590502d0f039000d2400d0400d240c185861841c6d00c1e82c400c801600706402c90b0340c1e40300301806854a0016089074400e800b8802c0101e841024410445810030319180d0540e41d04042c0101841c02502c811255182c50504082104496202c81142440c14001d030744103440303040c00790440d0080e003401d02c2e109400000d48180d603072004407042e6149440f400f5040303040006009442205440d640c1d000c00c40d165011302051891036039403195020304010841c01880601b025204c0d13a60700c484c2110304406040c2070380150140418804280f6209 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 375559568 1250 375558318 375558343
    0xb01080318030a0b0c2208060106080f041211070816080705120705010e0d0209160e0301060305070e04061503030c0b0c0918090304180912111c02240603 67
    0xb00748111180d99640301028004080c4260004d0202c3d1040b20380096031030a41c820030300d40e6070310f1b0308690300d81160a40c0d8803c00d1007000000f0b071000f4041110480c41400c95401942c0081c00d0b152031080503141500c42003800c410a4089200c1c0400c0041e034003800340312420181d82400c010b411654a0904268500900d0f500400c1c4264440c1131450702e83c140c002401800c07a407003820991404191500000c1d00e01480460103500407900d1000c100d11414a0041540700028076100c4440508621051600303c5206020050580c0c1c0140b4061003080c280c06000d5030700601c105c3d40468001d1100c041466484240c2c3e004801040c90300014008000390f0f80c0000c2e60100e440c1c1421800d011105000075002c003091240990054450720115400e080d09000321000b412884020392241c100f0f10f000e0f1380081c21a840b043d15042503009010122074030031a5080140b19001c8000c0c040310600d0f6804940307188000092400b0343c0b150807200003100720710103111441a90205442c290754a00003003458100010f000d0b41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 375560818 1250 375559568 375559573
    0x503131d0c0c030a0e01051c0507120b220609090f120503060108070c1505070e040612030e09090109051f0c020a05100207080f03040606170a1a130b0108031803 70
    0x15940c0000105644544e0140d1600540ca008458016a164420b0004510401c6048640310178114219049680600c00039500c00d07821030000303d020320031288400141d07613008400c480003403003000710303803d41d00745402c0c40c0c841c0090190f60721001c03141102c21000e4115142c89207840329009000c008170301d90700c206900e414054031b50b2a00e000001d00800c03000303054000340100d161619041c0507540149400b419121078081106050114010708815511030704a1312403414007402282d0003030f5019031041060780c151903030103000c0902d01c10030181910003008480c0030340d40d50050302c011a004111043e442d0041c034441950071202030190074107540c0051403040c01c1d5072006601100003000050000c22122001b20010303142d0b4500e1034254807070711851441d0302c0520004803d01c018480c0700d034031500032520904000245040c0101c0c405484032005080501180c0403c141c50b2129181c900c030041c0d10442c0e21101c021542c0030b655492100d100c01781c00c070700d60a9002045030700c19030105940030044960110700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 375562068 1250 375560818 375560827
    0x6010303090320030606090c070507061d0102010e0c040237080609040f060509160f050f030d1b0201120c02060412022b0507051009032307030c0503131d0c 68
    0x400e5032080c0180506d4010001400060f00e84681034081c0c40580d94031009071600c0c44c2d6902d0300281a1044a19481e45044078000400210b6005114040e0004014006005900d000b00704000c000c0d044280c014415044503002150080b007840d000801c000781d1010240a521031b01040107110100092845000d02c10680c00d0101041d40940003658542e40100085500c0c0c0d00c1c17610081c1484507038198541d00755610480802c5902c801610340703054507000c0c0d07a8420025000410540d65810000c140400b05110044070010241d05a00c0503042030b0040c10724040d201c0402a2503401c40347c1d042d43c480016003154051104110090509948034503040c4014000940c2c6103105080c00143c1006070700030384a04600b088945809141910442500318043d241c01d4250070043d030000c1c00742c40382c0450000e0851a0341000c41d00100d00d0a1044c60300210030b56003044583d5905849100e2030107800d1710f44d07100a0007a8104603945284a9010704080724a400c0782440004c007400c0b00903006040014803010601 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 375563318 1250 375562068 375562133
    0x40b0a080106090b10170702071a041e05010c060f090b01090b1002011b03020d0b030f0307060b0901030c0e0403030b041b113d0906020414010f08010b07060e060103030903 75
    0x210b03007186d1b80d150071401440030f48800f1801d0b445c0c10302583c483c0704414210f84550440c1000040500115800d0261040500101c1c02e21541d12000314010203001c6070001b8584408110796038051110101d010a0010f0701d0701c01500c030105c1c640310903031240c184281c46086070b1701c2e80c0c2003204001104a0b40c43c00248104051050f001c3d03020025400200205a404126910f9200950700190321130b060260a5499092800003c00c2c0c0b81d5000100c240c0700c0300c0c14140124040d04106100741e04980d04035050703c00407410310030301c41c00c00d61018000382c0c101610b03561a100a903a45200707100c00da00c041e14600e13418504c0000c5c06030031030580e40700382d9456401c042c0ca104803e0141c81c00d040603003100410040b20000303d00009a682d080c052604c400118604040d600402c46030394010301c2a14a040c0900007081000300c011a01192a521103000290b08440100880f07000c0c4406000344070b201d24404510080311084c41c81c07410134247e205600040c10b00c0d008200340940d10780324130701d041045190740c01c080801c403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 375564568 1250 375563318 375563327
    0x309010e010b06030106121401120203060106020a02010507150e07140a050a0e0a0506030f010207030314130f0305130503030708030106171b0306130c03091103010606120b040b0a080106090b10 84
    0x144100800d1040040e283c0c840441c0d2540030565604076450200009d58440090031362060804000724006c0c07040f000041035083c00000d021640a40c1655200d03d0030b04282d0b10f64180301c1d80e54400b1400c1684414044c14031032024005030b4050031940d0a0780080c142e02d5400c110742034595600c454098074084170b0500100f4824102c0b55800b4104401c045031030348840c400b1a1401c240c0c400000740551000c40e410080561540040c0c0b0091200303500c800d81604c2e505d04984e01140c02c40030090038450200001c03400240904098416880440005480d47e075455000c2421907004c524210342268001006008640c3c000b800584c01c51040d00d5041001c1c6046038100d0b07000c01410035240140400800040c10594550244403041030709011305000454059502070702806c0049403c403450454141503040320b090500c40c4030300b1030700155a030200500c1411a52401000e104101d20307000f035164180c00c00f0b103854010361140180510301c00000d590745170402c418221454130441c11310446a24103080c1c08a82d10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 375565818 1250 375564568 375564571
    0x17011502060a1a0d030903050c10050a2a0c09060f060516110a081b010206130b04020f061b010e0307030e010f090f0f0305010b030f19080d0f020309010e010b0603 71
    0x2e05000030b5000f103190098045201154a1a41d1240c85118114101540700700d00780c04681c8134008690b5190200300c10440759011140320074002407014007066580e903104481480c1e40510000c03010692801043c407100916130194003e0707030220054032040200c158503101d03101c000c040c0205090096410860018814400c9814010804ca42c013220b42042c0520000d481d5425a0000c00c1c2035440341d9158005915103400c14022023141300d5001400103254000b04405119403020a1560301d8031580e0307130f14810843c0c00500103a8126118003103a01050b1030325401042d14400700341c00310600c442160304440c25034000c400124080d8005020460001e48c209032080c0c48440242040e42d44081c1d941c00440303041216a200d05e41c800031000c40042c000201450403000d0341d0049009001c0d600895040c196561140c1d6103201d100d9111486201c40e45410301044200c8501ca03c02e42ca180540321030005040d80c440c0c2860a40c03041d40042401107526003403280d592142e409400070712280d034201c4c0008030640030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 375567068 1250 375565818 375565831
    0x30312070912030309060f09080f070305040b13151e05090102160329060f0f01020a15060e01050909060f100803031006030b03060c0403120e101701150206 68
    0x2020404140081c1c0507141c07410103007540d0482601101d009040c020080c28181d14160340300c500e001011070035560f95010b4000599000910b451500ca1000a01c94ae25400008240c04000c010b02003c108005488000d000d17400d403400c10320050303178241a408404081e501144005000d82602c482c00304031411128003000151900b0f005031030310a800b00507410550f46004001c010108041c012007006200c1d4418400c40c480304a0030880d803d0010915881c04d0310591307001c2e62002600c40400c0492400d60b0f25155001c0040c4190355902815031303244030014610002034505191203000c107200c000c000c090307614010102100d81c18020709000c6055070719000003802d45488000c1c2c520000d5041140080000010400070044035a40e14021240300c41c140c05501880e80000c0c10403a090340d01f480c0010f02c0300d00590302d541201d450a80f82d581c448c44000401003506c4184081c0f03490025150303541c907500300c80e80000c035254112400d80e0580350038081c18050300400721040c4041402c0105c0c550024042e640b120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 375568318 1250 375567068 375567097
    0x604050a110a0e0403021510080c1c0b13060f0c050a08070522231804061b030506030105061e09192f0406050703050d090501050915150303 61
    0x25201d80108a0b00e1080e50000001c0046100a100401d42e0000e07648581000c00c140488841c0c079455a808a100070394498001254030400c5120520f14001146191514200040d40c0d40d003003c07503031003821312070040314104c84064a110301c584c00d001d12402841c00407074004104110300344420708050301600a4141c104108404400010b2410380190200c424013800e20000416240c08880030b11103455007801000c40000b41c0303a8105040051400081010000080c130085510424054042041400500035203c0079154000f044034a41d0451540001d030445a0300407c01d8580704040c5400c0d124080c10f05806401960014000d0a40c00701c000a42d10000321008000750300c4814007112018000001c42c69440d150951003600761303888100c1e42c5030708499403c109902055500d05226540a00d100d42008141c0802106001920550007400403020701200007400420710b484c0c2c142161001c840c1da0300240d00c40b58030011100c52055401e94010380102c0d90314407116400003c00d0700ca0040701c1c41d052184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 375569568 1250 375568318 375568343
    0x1030b0a0e090c19050f0307081c051c0b042307030207020609100801030218090d0302070203160906050118030c15050c011b03232404020f0415020604050a 68
    0xe0014041140900b400605842c1c01c0e5030001091340900200e4840c0500c1132104203003031601e5050200d240411a030307104000e00030b030841c1400101c940402d4403103100200301c0104248500c00d01c040b031030082c0a003120710000406056000500c002c44490f0826000e00010501c010a40b6524000d4a1b980c040130780c0c607015850f0725141c40030a91900440844030362007100e0408040d425a0b1010b03860781200d0003200c12243c1d000b4641a101c0350000d061300e030007035035401810181c2000f60180d00200001d501c060122003409000e14010510201c69401004020f030700d902c03082000790b82c00a8550703000070000400b034503c40c1c51907440d480070b00c0091080011366003840500c00e90341c41c05081071381e02c411500d00091100c81000b60710b50840783c0d11203400c030002c60f03d44010191009849a05158a00c06d450302d540740644607a42c0e0045c0e009000b2100f000b81c0d16402c6103407121916907001a0034041d8030f94000c162118104495620140304901000e01154041001c1001103880054010000790b008001d50006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 375570818 1250 375569568 375569581
    0x30702030a1509080409050406050c13090515030a0b0108010e0c03070504050a0612031e03090506070809101a0f04020a0c0602070510020a050a03150612051e040f050c01030b0a0e 78
    0x9451100c2c030262404e803001c40d0029000307285805c51803050380302e103100b00090381c2c80d407807801d956021b9503034143c4200c21810002c1c00040c5050340035a0700701c4041c000c900303070799115500028948403c4800032101d84041200401c04444240107c2c0014041000501303401c1800401203661038079244a00e51040c0c0c1c840d0040380640321581e10071310151041c09040c0e610b400300e40c1406849a203c0c474284400c0c0c40c880a041100b0244684900c2e55000c1c1d00c60045e110341e446603002103034401e1000d0181043c1e03004161440010080340c0c0f080d504604866102001d5454212007000030140d904442c1602481c0100140c29616520091040c0119071101c001600c0b40010b00701685802006158184514400107103010103e4203e4058244d00c14141d41c180104225015001c445a40030710a55020800d1100030500f01e4035550842503201080310420007004505441d403841c5c0507070940301518a5804101850140f040034082041010000e08003401040301010205581c5201846001641217010300072030030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 375572068 1250 375570818 375570821
    0x3022815020f040618050108010e010b071b2304020421082118070323030d1a091b031b07063303050d030c020a080c010f0e030702030a15 60
    0x8000c10075050b2a151a1103c4000c1c01c070a49940d010710a04c01c00084c00035484d072184400605848101d44e514003140d107018402c0c8601d07004070400b112030321801560700d034031502d40c2d5242000418003551000b0b40044000c500641e088030310a590cd02981c0100401d0102e010151007010461040c006000c01c49800f60405000300d019282d00004a40300b0a600880b008120803c1ba90180e0605010f00e138003072a403044000e69403005488001d20400081d04800005c01486151440a0070780c00196031801c41030030000d40803540742c03504200c500c8074580c140072031034144600e06ca5030052680303403200c00d11403440024040d6400000c103c200c0002184a4046410030340070705440495074444010b1010340080d1409a0701d4000849131840c240e130b80150143c11022405059070210f0383c2100240503424600041100a080311104200951046000c0080040c0100c8010328041510400014100d5240e510b43c0081d2000c4030b1445510364418042000981c0d8041340201c440d81d4044115405030300342c51050310 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 375573318 1250 375572068 375572077
    0x11060d050405060604060b070b0609150607050304060f02060702060408030a231602010b0105030a02160b130308130201120c020f120910050a0903080f250302281502 72
    0xa01a00349010312003004400200e0364010b42c0704840131702160b40c035203a40c11524050b0540c090040c5010b1000f080c0a4103064100e140c0000b096800f000703030800c0082c040780881d80304000071100c690001504100c40c42e031000f00960301ca5841c0c0301030b0440d81010304000b075541d1400f90010b411120000007240c000c9005502100c50700e901d40d20701001e1000b40e410180c02d00002101c980d841c003088400011413441c810700c00c1d07480b6010b0585500b030641e120030101000035001400e440c480304443c8003408010035030940d401c030710902000d44102d41e001c0d41c2c0d10300200200b90291008212098034019900103170b07004480c0345a00caa0302500000c2c0b08009042c120302c0d065a04006410600a42070107214500e40071004000801d03043e620445582c10f45001240c446c460000300c100040d148401c1840001e040074010700003080c6420310035045c001005003c011541c5001d1000c041f03100101000c804054042c007551080c0404014400505204c1c040c0c00c1c008503007901c0f80104100a640200c0d201000c040c3e043d00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 375574568 1250 375573318 375573337
    0x12160c0305011b05041a03100b030c300406050402040f0c0c06112b0b03070e0f071106150406120c0e0c03010302011b080715061419031106 61
    0x100140e6a0508500034100074000400b881081c81810241c2ca00500498040f01e140e08014060404070003480c0d0f00395000501840842d80d1050750002304007031000c010354003030110481100d0381e40311903081c500a2070582c001c8031640d00d01c004031010052602c02255581c4190031410200d8235075181d00c0046c009100d80a03044054520b002c00410103154414812100a4800c07881046620301c500320440b600d0041205803501ca0f0020707130f01003101603800b41520188016217400401c501a207900001e0401c451900680640401041000246000074400ba84c01c0042c43c2840c10360000301d0b02100d43c40d8040200010380907a4000c840b1081038440d80d000600501c4500e1241d00e2000c00c920b040c064901142c8604030a0812031000b1550080096044038100d90f4141c4490984010407141e10791455040401920480421311003080800c21000881c24030401d40783c1c00207a001d04000c0c0e01e5070f601d140c1c00240d07405118150b030700074001504000c50b401a6a001250b8004174003a81c4009800d40c031510080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 375575818 1250 375574568 375574583
    0x1d01050601022a030102040311011b030c1721070e03031303030507050f0f011b0f0c03051606060305060703051f1e05100c020405090109080702040e010207050a060e1e0607110102090409080309061302031216 90
    0x9940b9022040b0094010708595842e06d1c030780409001016924062244042c081080720001007002074011802801024842c03401d40c0c01c801c1c0d48101e010704101e284045141c05944447c031458182144583c0c10703a010403d801c04a41c145120078006000d048005c0005003800310018100d0720760828035010001c8158410814000385890340343c22074603420242e99640201e42000081054104107100710b441d030082011550b00300324500440b5034242452880d00d21010b07404135101186c1a207858842241301c040b584c98904d85400184180400c4541c02010340b0f44a900d017003070076400607159400715603e058040394040382035400042c40c00d00a01c11054014444d00c16820840100040380d0060382c2d0f1b071001340c01928040502240740c0b0040d002c2400e4415850f4101100003000d46004252800f5041c4c1c54100050519100c000410300315a50840c0c10b0303a0503003000c41040140c0504102d242d901220f20128a221301c100c83c0e0100b940c8140400b641001141c01042100200110900001559401584 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 375577068 1250 375575818 375575857
    0x90603050c03060f06040b1c0516080708040807020405040503070309081f11160f060516080c03042103200c1504061e1d01050601022a030102040311011b030c17 70
    0x1c1d0001c03c80005808c03000c02c141001c0c00920343e4000004504081e21076621094125030341d0202c22540d0b007100400450700140c080c0000c00240c0c03641c3c41018803d130b10403001190760710154180a021460194003544c029401000a9004400d0407221100554003103000070486001d161841c0744680200907480024084010315807003440700e039814052401e402054100020707103070b503001070844c101e03282201008078000002242800745950b0007940e001707029000c5c0c0d0240c00c902d002100d05903070760318a0140000e5110700301c035200b45c94584101102c041840d1111480c01200d44015516031201ca82e961207070411400002d0288680c039081601410301c0740400000904018000e84d00510485010048290003240c01c1c4498000500c5154000c4405800030180c582211000480c0020400e8200d00c40c480715003d4241c0a4409001910240d88210032000d000c0780504001407901710310450310209095000e4803c4082030f04010256801a027140002c54050100711a102c607034410140c80082d030750082e80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 375578318 1250 375577068 375577087
    0x60801050901020310060503010b03010501050706020720120604021c050f010c020102180105090906130905011b032a030c0509180702070f03080d0b03011d01090201090603050c03060f06040b 83
    0x41c02140b16120740400d4605e4984c4403503045400340424010418684000c20040c4481e601a40c054100300f88a280301610f00001984c1d030300f400389081845400480500c0c0700245040c5014412303481c00c1c82c2920020b08081ca403c2d00000d403043c00d54503a602d10820030079100d0003031000900074002e1210300d00e0000d000c0f41d00b003181e0080c000d5000313a11240e840140300940e4042c541c86201254a280c500412809494035100100100740b145100e1011151365241108400150b0a0140382e01010980600b19807041d00340b9000b509440b03c418424041e0380030101d0810115118000c100b002150602d00020852038044054910f4411180900d0b441003800c010030410380c4804100901c104016170949002039650f00100002090900000300980001e215105c80005140c3c44600c1004c0001c00206081d0003200c50b480c01c907030f000c0d4501c0f0035a9444e64a500b0955802160100080c0020f2404110720300d401005903549010203004140b1640c004903070000b19646e4101a28042c007102550159181c1c5000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 375579568 1250 375578318 375578321
    0x150403032903060f130201111006090b1801030803042616060c02010614091f080a05010509160e06030c090907060e0607030c1203020c03070b06120f0c0d0303060801050901 75
    0x1103810510a100d54800200312494100404e8018460038031a0070039045035034010340703440b440c8104200f00c07845090b02e54440c000290041500910002c040010385c02c2012042c011407410b010f429a44814071400100002602841201d5000380c000031400b41510314403540701c075120030b5101e489403010000b042068460b50640002e5803c81d20a060400c0351008035001642694058418081103050704a00041d0a00f40203090983c804080744080d5052020728050304100501500650100e9005400b03040c10070400b44625a00070041100070304c0e1540710112242e1005841d801580146110b80b00841e40e140c50420902c0210700004042403010718001111340e0366100580300e01d00024510210340c0c0700c6420712008655041d0f030103a8a100715407840b6203074002100c0900344c0c03013820940c0c00c00c502006080140040c01e040d034800c0202103140d081c40410007102c411001d03000803a58022603001d05000400051105c00040207950f940d10081039414142c009003a96844501c442d400d01c000c200410906 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 375580818 1250 375579568 375579641
    0x50906070c120b0601030b040c0801051509030618070b090d060c02010e0607050a180302090a02031902160303050109022701030b03030408011b051219060315061406090315040303 78
    0x1ba41c007045261000d00c20881600e903038089900101c0c401c8001482b9070709041c104145020380c2070030300328640030ba040046480c03d442101e48140c0c00d4100c0d03940e40c6c18444144019001045160300d914102141c8000003083c0f85084803000309665941d400c40d4209038001c2d004403083c0301088054404074980000040c1007503111009800005400e850340042c00b00b1200070a8043d42d40142c00840b083e40c2e514040d01c005e5001501c500a0303600a100880801c035850b0008000395111140c04d11080034040c64090103550040e0400400a030041c0566110b0310b810b4012042c1c6107800c45081e00140c108000164020580a081260140000038021480d0041500090748402c500342c0301c00308043ca000421211030241c0c00700c000d600148240850420003941e008986204001107000640d45e503699107025101e140c44030520307505900c840080020306643d6110729030b0481c0c103903486460202c40c000004d40711005403440220034078514001ca0203142c4130754014060a00100301009500341a048504141c106 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 375582068 1250 375580818 375580831
    0x9061d2205070908101a121c0315051e01121e05180d05070f02180103050d030b041e02070c0b070b01152a0f05010203010b0408070e07050906070c120b 66
    0x98503010685e801c04d0b40300c2c0200419609400c226100c2000042012445a0345801b04440c0700344009116901141401c00c01d4441060b200024410740501c0100d0307100a165000034411180d040c800d508002260040f5601d08000b446d01107101481410340c240144100340c0300050503144007516501621455000d41c2c002d42c0c1c8200c08506449204101542e04d603805404400020024801000041d107100c1c00c29065904c001d0010920000f0f001c0b0b0b224141c4000d80c01525254440c5441e0410300744c1502c20f40069103400da0b010f000e0400c0c0c0c58541841400c03130180781000550b000640d0003d100c400030b8a00094220700490b155121094149200c0e248402e0040449005180451020140c000c2501c0003206100300e600310000002d0b0360a422004044500948846903510310520024000b0f00c000c602a20005400355100d03410000c0c11460700180360050403800d038501e01484801500501900c01d03201c0112061552464903141c0000c94101c298032600e001c0490f5400001004140102a0311505 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 375583318 1250 375582068 375582073
    0x5130203010608120702090c220905060a0f060e0d020d0f1a010302090c070609060617190507050402090d0f0303020a0311130501052104050a0309061d2205070908 71
    0x40c0c40f55042d584402e004a10382414401c1080b445006042446070f50ba4816610214681000382101c9001025203045644410404010070b00f401048000e120f2036410030b6040c2c4420200600741551a6403056040c06044148851101c1c000503564542812140300c0c0d5000d48010110303000383c50401e80c078403900d0342e00b107800c3e035011646410407210080c4c00034101d9400078141c5025860340b030b20030f14403030303014200503a4015160302a46000c00c00314042c01000b0081d903000e078000c1754000844c0e0350a01d00b000981035100b0700f1140000300414030000f100360030350b13004480042e5a0300300034000600300000800000c00d448185840e41091540540c09800e512079181c030240141031700c016540c030b128450181e0044030303060750000a01580d4410b0000d407200103588410901d24005102c0a2400880e0881e412903413580300707030b8071134003019402401a0020840c81c204440c200e1410259406203805114486009801c0e540b91b00e1504080c82107000d0301c11400300000c101c2414102402400c030001405225440e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 375584568 1250 375583318 375583331
    0xe0f0108061e0a1d06040b06030a02012309030607030c0207170a0303331406130608070302041a0c0f03030c07031805030f100c030b01050708070309090513020301 71
    0x40010a280388103564002810640c0c0c400524000001c0b603024008200340d90b600e0a014522400d510102002c01e005000203204502d000d140000b4845401440700340a50041042013006036001145413911a00c0740c01520240b0904a812034410b005401c4441e50610910040c1f000c040e03003640c00301c1c04406c059801c1d5003105840e0070344646010a0800e5081d40c0e9408132a1101c08280700740d00410a18034420000012943c5079402c0b0004010b100d2880408118441c008004040302010034007004102550060704044485c448410140000e200d84814082139500085040d4030030740c1210041e280507030302c41c1c6a03021a80414641078100300380e03800ca070340700d0f68403981c45003c00003003034034401d903400a05185002d100d5502102c2e000189003400c031454060502c0441e240d5030901404e45044448c200071b15a40d41001005c4094441c04144081030600e088580002030341d01408441c0025000600203944084500e000c980c4050207920607907019181505114000700e01c52204920b0700d00880003170000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 375585818 1250 375584568 375584579
    0x1612031104060807030c0201240f0504060e0c0f0f0315090f010e0a09060204090501060503061c03080103120e1e01090603050c03011427040606080a0b06130e070e0f01 73
    0x10703210300e0040c1c070046100000010802c4d0720075080303002003e00710b10002c10a40c114404c003800c100355998082c3d0760f4590b504420700200b41d101580c0c030002c200884003440664580f01c82d1104410028064204d1501c000a20b901c0c107015250480b0900210109416500d00d44480003014162002e0b9480b8841c0311414040703a25100644540d90590344403e04150103511550240002031041c01d804441c000e409210024014145204490080c811030b103400c1d9507032821208100c943d202d041440d1007089511503520021a5100581c0d81c10340e0b6000440c08500d410034402601c00820220b180c80e44500072000c1d4104601003d10014101e01c1e00381ca40c404041e44500054055820840300080b014006000410401090008850a505010b0081035038022040b54541e410040c0703400c602e0010240000b403104000091183c1001450740784082c10005005d540c92403040c0780f025002c54460610044030045400c42613100805064802e001c544070b03259210009e00002c1ca0032114103c070341100c8000000c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 375587068 1250 375585818 375585851
    0x9020a080a0302100b030a0c0e060111030a020c010f120c0201141006080429010609030201090f050f010309060f02071a0709120602030c190c0209100623161203 70
    0x14081e82c160042c0100c080d030034603071600070a007039941d4a90503c2081501c07000303d1074110040000c0c0130050074524161500d2070001d0302c000049080100e8690040000c200b140780e02051000c0004070902e041c0c0d100180e4964119141d076100303066601ca2501e80381c0724120132a015405003116500a2081003010394440d0070014641a040c07044c500410056000940080c490841c02543c00d000018860f4061400001c0a801394409802000c007140e00c234031081c0190740c0c07c0110f800007055807803400e200c1d06082402161304418154034043c18151500e020804008040c1c02c10300c0860307035801c021515004203041003020545014000c81910b1840720225100512130300d00e0500307a0b490044a15441e0f91256101d50007584024401200c0d000140030491500034113504c0400c07450090350390410140c41e1070040103107125000d0001e8403091400e09042010b0b80c0c003d584101c039000740030100503a1640005280c1c915105d0301c041c00c0c5500c0d8030b4841e140204002079580d06d02c2503007681e400f0440031000b00c480c0c0b00f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 375588318 1250 375587068 375587083
    0xb0d0e0d0509060a200304120b0f01140d0201110105090c01170702061602010b220e0c030c04090f150510120503090f010e0d0507140103111608040e010909020a08 71
    0x681001c010041d1041c4030740604910f2a42e04800300d01605c04d07048000380e1504540040d00015040c015808104044c022903c2d807075030700107545541c0e2603020f5240c0760740b16245040d00310465000300c1d2010340b9941560b000d142c00e400c0d101d1308540203112500c0c003102c0c0d140d21242440f1015010408480c101d10080554004b840d115007015002850340f5190f0300481a441c1280030500c20442d0348940300900182c440c001100c181c954103a4a00f100604201b8640c1c086d070748030074260411907100503104101c550f80060803a2001d0015940019100d03031500b0030002c06401d03881c01602c0108030b141c1c5612403e140f5408144a241040c0d0101c000b13903100c548030358810200010161141c3d0080c800501c5500c1d04407245001c08505042c0543d110741c032007020441e44000c4240540d440d40201408000320320705851029050b440901e010860300821001e440c0140c015a0803034070628547d81c201400308103609046401610b40800b071000305694520205000e0a1180e00403809040714030400980d0440010b481d2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 375589568 1250 375588318 375588337
    0x31505060414061c020301060e1801170123011d160e0414040506040b1806010b0705030c1605150a1e2303040209010605160803060402040b0d0e0d05 65
    0x649414038040780c4081e001444244154410b0f010030441071020020504180103003103a50002da141c0d0b01d4000090308011248031014015164860b11499046200f000d50381500e000c5c01d002d504003814224040d004103a040d240e06a20400c1c00701905844d401505a607049948400602000c06440780c0c10443c03a110a861507044030038001640080c0d180582c0220485280c0500002060b50202ea20400034840950301901c09811240c180014407110150b0160322a000b204c84042c643c10718003a459071143c05100e8003400c400c0200701042002000c0c0125908203102d0821604040746034140d45441a8980c86140e10401c1c118142d0500c2441c00d109440804070161619091002c2d84007130781001c581803080c02c204004049035100c288040c9001d980e4460200500c50355103a180c98410701c01404010307046001403040620036404060880001000360740d03400400185c032929824040340c00780c01903400ca071458503000301d1403c1d00d0040943c0044004040e03e01210040780302c0001c10b5400f44600c00c0d51 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 375590818 1250 375589568 375589579
    0x5150c030409020901020a0209040303151e0b0708040510081608010510050705010e01020d0204140618060a0c12051837050607141e100504020118060807031505 70
    0x401c40000b455024084204040c01590201c100740c1e070000d04004000c980407030200740e4a080a80343c00e030304103d146002e48524040079800100c40080c0b070341d03810703410300ca1806004000214641000640001d4078001d00015040101c010123003030006d4003a0303408642c002010340482d010007420500c20300d25507048800240002035581d9181c1d80456803584544016900b1790749030300f0801441c480920003003400c190044c0c030040c0c803076050140b010b001601500c1d8440c4101300078058034800710644040045240300840703d182d81c4545112094884000e41000500503c0f42c0c0e40030003001542000c01009015007070f014000100c40310004000c0b07110707a01802120020016206080c19922103081c80740102d00041070403034801d9482000802a61000f5000c0301c5034204640d00002c031000c01c01c0f01d0035042843e1100d205440c2d140d8039404d99a102150480c0c038404e51598046421f6902540e000480c2106504100c800c80d0746404c4003a24501003912440000b92034441c04051040f5203001d200d043d030364020308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 375592068 1250 375590818 375590827
    0x9100801061e26060a0b070b06270708040227180c120d090807060e0f01090518090d0504121403040803070b0412050306131e1505150c03 60
    0x15001003020b00c100102090201c191444221000d5025030007080c0d911100300d5001d07910b00041884101c40b03695008404050050041c9000101c05a00d11640103406a9011403203c0307504400c074024094400c0300e5040b00c001d040c18030000365444151980704500070748e40c24030b000403411090300680c440302015109018448000c03500c5000b06500c07172401400d404049581c0500c4a4000a040c0702c44800320341d2850b4015102c0e00c1841c1e40002044002f0303c1c482d0042c000080c03411401415408141030480d01c501c10139902d81c4100c3c0c0c051102e60020307002c09070246412107503c0340b000e48910b0094410314a5842207840d1840854400c0e404c03507040d550804a00c0321030800c1030340c81000c10020060580503a001c10700c00420310400420103484c1540c09695141d145041c04d060030049160f0b84040720b0100001081040501e4030340c00050081d09110030000034184030b40f100c00307007109004d840341505101d00708042c02001403501070410089e200c0c1150210811071411054248500c03403e046460190001e20 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 375593318 1250 375592068 375592097
    0x1409060a0b0a051005030406050901050f0a020d020d02041d160e193609020f011809180218130215090301060f1e03050309130b04110910080106 63
    0x800220545070003601000c02941c5650004840341e5000019600241d800300800003400360138090a500b004618000300300f982001915020b000e04020030200c4a0303074000840240030744c0c00e80c1c120740e030010b180341c070031901d842d1500c101a0202c07180c941e04e480c01c11150b401150402c030707203074070700303400d812a07684410301c05549070f40901280000c00d013500c40d40c1800c5003000103044d50b40b05490340304917955406003015681c0da0010762502c841c180109440001d00d010002001602c590b0b4014000410900f014844000790180140c000700c500e800014402c1e050104400800b00f80d07048200142c1d200700c60b07000050341030b012000002041100c00c68a5904d5030121a40541007200095407094003404115240080560119080d9200c2d5070050156600380038081110180020704c0054a102c0c2d44506130a0340c0c956110a80c0c1e90244d80200c80c032483d070b0440706003101d00007607222a1500c0c9000d00188040a041c0b810301c14581c1080d00c649014100c41c0703240c0e0382181c1c4126081070684440351039071040310f404d55 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 375594568 1250 375593318 375593321
    0x24030309120c0a06030b031506010c0f11030d09060f031104140607080a0e0405010602160b0f130f050103050f090a120e0301020d05060a08120f070512070b0601031409060a 75
    0x1901046094000c0c0103080e586a03e940346010098042d503100495070600c60030070725240c1403484a0120a2280d0388051022980e4482841992140c01a401200104040c00c181c0000b40c0d007200351a40c54400c10180143c1c41b9003001d0030302c08440281d2640085955411010b800b41d4408100031141590104024043c500349003044c8191204040e002c0e6003805115a074103c101e90240c9000c0c0041034248150752410715013405042d002d8121071005c0e01500b49031005120702c811903030140308038000340400c000040884420984004094144491000c41d139039800440b0a83c910b80603080c0041d0030400054071608000c01380c540540940c00040c04941202c0e140c900803824407424074001c00c000e041051740566800d00140042d0940c1000c0010607042080401c54a24200d0740310074110740005d1040010985804144c540192038000d056136030310b0840c94141c0c240468000491001030011680301b091003002d1552520a8100b13032010403402c482013410180e03a20341199005500e81c440800240441c285 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 375595818 1250 375594568 375594589
    0x606090c040e19060b070803060a090204080a0204092d060b01030902010f050c07030b0405060708070201110703271d0105060708040302130e100e060604060608040209090709050a0524030309 83
    0x9030340001140c0385c60701041102507010750004c0d00ea01d00c0c040140506480c3c2099180d00900880d40c2c11843c0903d0000101c0e1260b42c0428041d10580d40e51040206106441c204410480324020302c282010a810744000f49045902e5030940d03d040c07400c680c24420794068850209040c1d01612100e0007042001c0c0e0440b1180e22002599444d40202d08001000030b01554040d8099407042c0302400d410304c0e01c09001028207034018581021a03040c007210408508420044444098051500442c80030081e298001c0040884e00481100c8001040000340c0c0d011001c0c000d100e08281110f105d1030b40e41da4000b0001c0900840b0740140070300320100810401880c110400d00a03400c007200008c141010400031050034070340e44006140109032251005001140c042c0141e50b40414100c1d41005014104070000303141c2c1c41e00500013405000319101241c915002004150000d002001040c4024a4000044409410165901c04468080e80001801e8814080e019840c41402a000314204040c0c18100419800c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 375597068 1250 375595818 375595861
    0x60315050d020a15090b0d0209040c090e3607031b060f050306030c040e0102090307210204020f070c080a020a050108190b190b070b160207060c0204020c0f0606090c040e 74
    0x1405d04002a0f030790001020304007a803589000140ca4500b60420700090b85ca48030121410405001c40900000d0050802c20b5085410f0301c600c0c2090080500b088244100000e40c1845500e00d00300540c5110701000403134005480c41103444d998560b0300d142c1c4d40c140c401c40710300804010400030074000c02c129203d02d01940d4050402000c840c519807051020034111450803800ca02e0607500042e145081e400c0400c5400020f040c0800b090a24510003250120403400c00d103c006d01c1960000381103811201c41100b99245203401001e201e000079a43c0103c903580d64000304040740580c020702000903496000e0444c581c8201c80f041c1c1300f8a0300c102c203c50701c07d00034840003954551240600d4414084a854140c0e8003000d0070b010980f0b42d0f5038070407a003850001c081006184000c03001c002401e00030640c2c0e02241c0441260071505240c420302000384001000790140c1502042c16125141c401a0052000141940940d0041d108111541c031105a0090b10744142d00440a008001c040420703040003510107030b1b01c104c90 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 375598318 1250 375597068 375597077
    0x4110a18150b0a0206150111030d02130b04120b010b09090f0c220e0903090a0303080a110d0c0f020303090d0c141e0f0604020901270204060315050d020a15 68
    0x54030b802c0d04070525040f015507900140d200100300621160061081030544c002400c01c2a00c508040010581d05d204000c000f401090300030505041e2043c50a1480016003102d500c4c25444541760904007810010342401521401000000050a594100c04035003107000040c21102c500c1d1f40e00700740350f00c3c101c0c8080c00021010b1070800c80ca41102d0f0a103208101404281c80c524504030307141106491200c0c0001d0190b80098104103c1e141003a980c1c3c80100c0304995160a08d84095903800300d034131001b840311344c0c1210b00202c2e000030110080308080c0e0061040d5011034039040f080e031411010890345ca000441c0d4084c01c5070b0150f015022058041e18240328201d102d0701c80d0f01c80b4502e44141281c02e010f0f00c110030060800c183d01d11680c03016000d0041c10143d404000040045291540001c1c01030841881007004074080c409518284d80061940c0703a6030341c490410195501c0d03030356220003002030040700750321802e4214140000c0b41c24609050302c10f01c102c0d0000c25485813942040c1042e054250f09120310740500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 375599568 1250 375598318 375598361
    0x60902011106100f1d240402124002040b040e0a12020610180e07030521071a0c0409060b130608160f030209090c0304110a18 55
    0x401c800d0f0710070500800d00818a130f00d05141c002401d41e95410102c5045082c50002405043c204c49080e4050540d1201c1c1d0000c3c410900604028100500c0305034201380001110203071030040340c000e60300820b0070240c0300c85038403402c140e03800501d1002401c0f045151444482c0982804035000c0704040c141c00100300040d07003865200041c040780e11402c0c04195a4210134890014400144200703c05182d95002070401d43ca03003201d203049000241d000b28907041d55068a00e04481c115a4000c84101c02128120f805082e00d17810300643d1000b401e08544a00212190824400210310094540840d4441e410320000d1201002021940f0f90041507031000040a0000181d01c142d140038510007000c07a00785d0103994030009200094000d040f6005801802192014405015161031078a544a801807802d00445404000201e019101c3e016110b035100c000401444403100f50140150b00880c404c10111140b402c000d02070118104c3c2e10720640401100c4c018501c54002d034aa00030301c2d240e40c441310050001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 375600818 1250 375599568 375599597
    0x307060e060f0412020306241927060614090913020a060512060901030b040f0503191e0e031e030d020a030209190803040603021b060702030c07090506090406090201 72
    0x72600940e1102d124407182004036000c5d4101481a00c1d04aa5610185007922070004d145e1001c540500f20200d0080c054003101d00c00d44111540c5a001a00c003001a442209110300307200d01a429040d16020b0a0500e481d1300060260b0051110130000a42c0f0704c3c4070750402011004000094200904146203010460008801640d0350314500c1c0203440b603900c03660344801c1d01007402e45100a00a02d4035028210420041c008641e41000c440c3d8480c1d0700c600d240c04030407514a411429409000340d1074800c2c0035502840c0d410181c0105180c0e019010800e46a241d00d50b14100403581c01c0c10100540f80c154000b41c04060300e10b10605c51001e46a0100c00407680b0700020000d00e035040364482411200040c1d4082a108a140303810180300c100d140e03171000c954000b60308158542e51031344240d00c6500e09040d80000d00c1003c01d0140c00c2c0413108050b051065031401c1c602000c020b03480390310042c28804a40031350072021583c0c5c0081d02c10760340a110090702110b1039aa5a64400d00202080760b021307418007020f079001080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 375602068 1250 375600818 375600847
    0x14010f050d151508330f060d0b010206090102190c08040b16061506022a0a030506040b0a0c02030a050703050d060b0405040b1e09070908030403030f08070206060307060e06 75
    0xa00110b20209402d03070b000a401001a50041c00d060040d491607917110004444072812024a59881802481000200c900040314095070881180d00300c074021611116100450b444209160420b0b02580c850381e0790810440c3c00c034400d0800100110681c2007040001c1c611602111541c241b0031481d40e4507150f10b0b80d003823030450341080c50858205c103202002c01c8100706090107503181d0608415110343c9020b00300b031070103916604540100008042450384c1940c01d00d4041d14143e45480d40507100e00d00c03064036410101d441e41c200311000c5e91250480c4010840456882c85203044d420b80c07540c040d50800300d016404580e250700c101001c0d02042000d00c84051080b00600c28030f0700a0007a10325142e5175a16010911081c0c410300071810780306928848090b0f40d506860760a0000d44401107034662403990b40c49800303654024041d0450315207480b0108000c000c1580003c1440700c80e407030ba915074650036038403040304903a28901202c0091305a00705d81c0341000a140a861304034011400207240c00e0901100c0c105404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 375603318 1250 375602068 375602111
    0x2010207090e01020315010302070f0b1909061d07060e0f010309081c0f021e070f08030106050c0c09010b12040611070c030614010e0c0d060518040b0114010f050d 71
    0xb41e65035800070511041da28241000070f0b12080c2800c5c191300700344580d260480650b420f040050101501003002410411001c0d001440ea41c1e9038401c1080121010704242e00140b02d00600602c01658086e505020001c0006198085800340d0f83c07000795003803030300c1c09000400700360900040c107240d01c404202c8001509080680680c54403650205800a500b00c1c01c0350a55400b0720196100520420540f40c40d030585d01400b542900c074040d0070940e200c000b45004500ea2501a070701030900342000c800031810603170041c0100000312030002202c4044a5601c00c10969010a21402014590401050b0201d002c22006240d015000780030006201500c14005880c0c3d0740300c42d1084540305807002060040100d18030407250190040500880c01e98140901603140142c06004544030106c0400c80400c0c03e41141c00400c0900400b42441c02075607031503c4e00080080082e6405c40f0800034150002c200105800481c0071180c0c0165500d0134149040641034866034405295a8a0a40c64012200e51170303000040f000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 375604568 1250 375603318 375603341
    0x3120e130507020114100f06050c03090301020304030203040f0504050f04020108060d02150406110d0806120c0a06050414090c0a030e010914031902070311060f0d0e0f07300201020709 80
    0x1140541c601170921180040060071100329810a00040c07104030442488038003502c9041c1000c1340c1e01c41445c10694030b98044e0140b46549507000108001c101907010010308119592100100c510302c2d154420442910801c0b5100709140340280d00042c0035600c00c4035510b802c1100036102c1075100c91150003141000c401038501c0039041000007801c01540354002071008111b0b04c0e00300174203100051920000d242c00b20260189200303002803c908040c15805104018039440001e144420390303603544c140507140b0f82007449080c08074204030410034201d04100f10702900c00e0007243e480518102e0f22420a90080c4502070540b10b280d035854942a0000d0078940c4c04004101038640116111601007411880c60703a003440860707085421601040000400c000070480100004580303007511aa6035003240741d80e9000d61810000d10600b0800075134403440d03021400141c1c1d0301008041e1007501da02c0781c035919502d06400ca40c1015024210b070603204030701c0e1b4544d803d4100500c14070668801d00e0340c3c0c00d07448041e80d020403040d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 375605818 1250 375604568 375604571
    0xf260c09030a0605151e120f100f0f020903060f0c04030203010905010f0501051816030209040f090201020601060216150905030a1b15170a020d1508010f0603120e1305070201 76
    0x50142020b2051110780c1102001c0350070300e0400d202e1100c100b500c03207400c00d0900e011f40303c03054251103030010500c503600309400320000329818400707401c0c0010098050920b43d03d04491504103016101000c40c003c4a040c1b00010707004040c04e4035011074030300f4030100c02040400607000c240720200040e070b0280034820080b4012800031814080308801081142c00c103034881071154440350b8074446444c00c8615402c0c1c0c8912041050311031441103c0301034010348540944154440e10b0165802480c00c10341e0710145069000b0f0f401c5604507078a9800a907500e900442140e40140513a240400c04028008007440b000001894103c0c0354a603520046450000c4d0414120345420304108007100c842d05040761000105182c4169007207100204801a00040c21951000d6080b841880000d042807900d804840d0305d03120341d4000f04402000101042606c48c06801090425420b00c1c007100b803000d9107030042c0421b61b5041028884d420080d0703c001e448158112050380c2d0420054200b11000308828403c05126510a400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 375607068 1250 375605818 375605821
    0x1230f0306130603051b01050d0501030302100f1a0d0804050d08030a05090703020f0904050a05061314031806161a04030215090304050409031106070f0f260c09030a0605 74
    0x41004418a900c8008070b028542803080021543c002000d090419100d04c810320a0f031091801214180306200080e9100ca0401e4000000c155000a209240c01d80070002040312200000049054914000c5840342c101c0200c0c111294034984508512100c502c182c3c04549055510b802294101102d12015500320101104000d461002d0b402910360014800c00a01442411a40092a5244909040d500840419001404004080040220094000342115820b1500100c0c03401d11405181c0210745501000c0402c00e0480000810b0300c40c1103c865101e110a1f244000900c0000e80081c2102c44081204800f8400840c0d0410f10524000c41e10704640904d81c40c041c02c000c1c5c44c20228440300f5040005d44405c128070400040150b8041e60230072a00402c404034a81400c03620311080b00b110722003a0094000f0f00c02c40036023140100344011800d40354601c5000c108401078440c08404804040c20381c09510141102032030801c2980d90140c409140c0c00c0c206101c0341c010a150a058032000c942c03650343e440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 375608318 1250 375607068 375607081
    0x108011a1c0e100b010c0803150a0b0c010b03150106230c010c03060b070f0b0c0702030f0d0f14070b0601050c190b131e05150702071806030503030601230f03 69
    0x200c088243d01071003405121400f041030008005144481c0040d18911020021884080031010f0008111000030a100d1038562a40d03a05415507105022240d103940c038011a00c01c2c81e050100d02c01110201000300a00c6680c68040199209401c80180e2103400500c3d918004040032006c3c0506002111007000050001c0305a41c00340c21a191600031491a950070f002d4080010f514201e10949594001da1b8083c442c0c440e910b43d24020f001350b04000394107000c0c6d9000703070300305640005d046000c1e0380481d5a0128000c443c0802500d0007501d1142c10441100200010008940000840d40e040361040c58201e16001d40c44010a007022000140030404800c2c21504105001060804940004100350700c1604c5032802d0741c0c0d8840801c042c200140c20b03009071082a906105040c414040701a40c10a84030300280391104000752100210700031044111440035100c009402580300d02e40c20351768407200452030758603110019075011010441034140b014034100c03030304510800000684a0103c406c5407054503401c040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 375609568 1250 375608318 375608323
    0x903020f07030f0302281205040503030f180f06030c0702031203070302120105010206130b060d0204150315150504090f082118070605030a0e1e06070e0108011a1c0e 72
    0x110b5080641034240e5081c0400c1b00340c201810750703090380150300c03404241c54204140c5040c080c0f0790103143c0c180800f03d40e890060701c04000a10444034151400502101d004040068071988000144d070000d2080c07000503030740446880103098550000b021145616210107030700f40c09501c1210b5181c0000d401080040035400b682074010301511003400640418500921403401c1c01c445102c028007290601c2c3c000c900140c0780d0210700e884031a00070b0002e00003060030707001081c8090700a1008448045008000312000c41e00c0f4403c52090144000e0080706e0b4510b04010000a040c10301010768003000c1ca07203601800138416400800c11a25407440d800c0c120078003124032200750a401440c52403a06c000002401414102082042c207803a0142005502c03600c5810316030000f8100c880514085209080c402c150407505500e07903800030a4214103e642c1075540341022a00000d49040181c0412510380050060382c20b80007003103048880000780d4030705001a203090b5200d01000c0d08107600d2095940c0c001e0000c0703c54203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 375610818 1250 375609568 375609583
    0x10050112060302102f0c04021b01020316090e010303050405040e0f0a0507080c0f03030a05030919050c04050a020c0c011209050312040201080f01031a061302181201140a0903020f07030f0302 83
    0xc4d00c498011500d01701c03603505d80340d990140040c1d105503800140303002c0700251100101403810820000315107a290486400204d034221146110105000c03120020b00c221043c9400c42c1aa981139a506052510741f00500019080c041c0f05000e05002e030141542003004100051003030307940618014021f41780b4200b42c041c00c113001034190501a40481d001240d032074078000111205142e540c54140d6503030361000c1e96217043c40601c03042e0b0900c8031000701c3c0310802d010000503d51a110400c4800704010344030002800700f240b08504a00410307812131000c40700a58000c00b00100061035520010801d44035907940c49086d42d01c24440030b0360b100050001d22096591019002d070344080c1003c0b84420550454450380c42c07802080003040d09030040d410008409848003c0041c907100050b04056455407500c10704280c01c032541142071401010f5032000c0d803140c0d1105020701400c0e6070680c080b041064542d00d4111300540043d04040d410352142855a40126104100302d00c0194050511203079021102d1500a00306002d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 375612068 1250 375610818 375610877
    0x6040b270303160209040323030f01060c050c011d1c0b010503030913090f0209010603050a0f200702060910080a050a021315022a0f03061005011206030210 68
    0x14021000540303c00c3e4100c620054046036030b014031766124a41200c4543e004550940106150721492140c0005040070f1070151081d10700015980e0b0326014108d5140454090180c030590003135840c00b101e940504800b00b006043d000c00074101a6508d00480c2480790f500242c1d44030b034040c40761027000b80b0960204407400341c08220701642c541000c6400196116036622904625241e9680600d8104032038001900b10032640502200902d40c0e4030603020703009040071600502484c2c00c0c025202c0a40d062131080030802594080701180407641914503215540040e402260010700c2000241b0b881e03070307a4503c50342c008803859403084140d1921140420070386070b02402d034549050060110000c82d082240064090301c0d0241c03c09a04504902012842c00c003240d02c9008000046210080240403090000010741805687d0055009510028181d9815080300c0201b01c100800000348020740c03180218110403a050000410200d460344c0006160803403901c000710108019080000d2180c0040e80e81a41c00b80c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 375613318 1250 375612068 375612073
    0x807030606081501300c0602060f04260f2b1406040e031315020d17010e040f120807090902030f1503030d060f0303231806040b2703 58
    0x40c503d6035440140c40040c0500a01d00006104889950018468618020068401c5c048800c680c500700441c0072481c0d07014204c01402201c0c00a0b030020652480a40220703804200c0c0c4840c84a41c090760f208421007651182100a01004501c045841010181c00d150b0242c070100d1002110035000b082421841c1d0103942207060230540300340c618040c541020b95008100703560200310071f884801004e0462064202c442e0180b00320320000304084402c10896401c448054084846441641206443d01d40340c01c00c199410303141c8600180403c2d41e0069076035400510540140403508140e82c0c981104825030700c29400000c501104002140354040c641200414202d4011465400c048440c6004018000d000310b10009802a0143c4c035070300c0c00c1044628010a0200c100105034803100107011a450700e00c000d6001a061510303042443e0f07a00003056110f015110b4466203040345141d07041d0030f0240e43c2d0020075400750040c800014544c00310f4000307006418502c0003143c03115511810918552140e07040e114000c3d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 375614568 1250 375613318 375613333
    0x11121e1612030503040f020d060509010b0105090904020f12120a02071706270f03090f040e070311030307200109080d090506031008011e0f0504030c1b0f080703060608 73
    0x70001c14080044540c1610701144d49590301e09040344e0074082c14038025013040c02d204141c424000c0940c0028000c109510090164921500c01100c0ca070042c2d06040d5445a0f50001190051400b0703594280000702c0a030103912902700360100503040c401e010041e0302ca140c00000f0381c4a8190b13070601801d000b400100a141040c40c0450b441165640c3c00109130000341d0700c04000b07070307031400c446c60340b0005200810b1411940051070360040f05403039421103120035008182a03a0204121300d0140a418605200364001b4038240d4a50f464a060f540900c0c0d041d0364050000b00081d40110790142030030762101c0c0001d01d0035154180f05500041500c0d12035445038000c3c0d000740b02d10b003881980c04454501150300841e4040c1c0c03292241e803220030200b555503100a14039860030320b0205081c0c0500703008542e28203160004000020180c1c51031000e0740c40803038000780003c513040500c100241c0e5014441100c0c14100b468980c0c0c861700c1d5035035078004040580200c5400e034424442041008840d0043d100034003507100141258 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 375615818 1250 375614568 375614579
    0x152606040f1a070c030f031d0a02030c041109060703050d061403061008030d02090301060e07020601050108090f0c130b10110f01061410110312061206070c11121e16 72
    0x4d984000d0003d007080000c0c02c0b100c1c10a482074000540c5244200c000c5858212100c5600e90f81e9003010504900a00032000c0920007464a1300c24130b00034041000486281114810804c2660380c050401202400010310805030048600d208050107031941001041d41a0f403548105842c00c0c400030098a6a10f5000a081c01680b0010043d00d1204820900240c1c42d541001c2c0001e0140042d40c02c1002544000e0003044142079001a1080c102c982c2a00c600d08940c1360300c582c09480740b1440c1072406a0382d100c1c159141036414940e031052078940c103601001480a1410b00050300c40400000001c0004149001200c00182c0a100ba0041100000000c0111030b00d0420900403400741c000145100740d40320444005103600a040741401d80c0401030984e6620070740005401e40500e03043d034029024003005c0505124103400002d03120702624045d00c400801400c030b562081c0040040490040d00480d0a18a5216040042000c010448040c04000342c070100785444140c5012140390350003204940680b800c005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 375617068 1250 375615818 375615827
    0x120204060b070317060109091a1519180509090a11010e150a020f07090207060c051c09050102040f0803070b06010903020907111e0c13152606040f1a07 66
    0x240b020034885488100e40e18403005951f00190b030741c84000344c0c509100301302c032403107801000075880b0f00803c84898079148601c90004d034650041009010001c2400c41c100c082850040314401e14007105010312510350f030b0b191000b007408504180e44416507944140125000c0184408541c80e40301c03000e04e09100007094480000b60742401072520a03410182c00540704416520a002c1c04004401c000100c1d820240e1b11481c8200130752140360103807103107071410703045245441c82030040307070300040001a4001d0309a80d06403a001c000c9c00e511800b01d03078565081000280020100211740c000300341c1000950784030807030b07414403824212000b006541040302c82002440141d45d080145c030b40114203481d1441c0101505a189803a0103024114941648481c410119840a0014114011002c00c1c0c07030046581602440e10b0003619081c01450b601c010303404074284100d0030040214110f8003011b0842c40001e2030002402800e0180a540c00d0381c1801100398001d003800300705010003000207140000100d0500d8034500041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 375618318 1250 375617068 375617087
    0xb0910020d36060e0a05150103030f0804120e0406150f030510050120010608070308091e0310020d060f0306090b011a030a0506190801050106110c061801090f120204060b0703 76
    0x2450580c0c2c80041c690101d84c10060a41001d90050894020070301c0c038040f10819140900c012000114012034106405104601c00c0d80950f6200c6001155060f4960b000d480d03440900d6900c43d00565124000200c1c2103600030210001c520f00d0315178002c503241c001c9004042d00c0000f040c4400c43c580d007900c20052030740d2007110000d60815000480061001c0410851b000d0045a880245544260705001c81841503040040c04102c0c41200d00300642010164070342c150840c00c545007035140d0001800c0c0b4882901e10340080002040e9060700086294031129070032840303100b0340c0042c0e8149507583c000108200d010b11540c0e014203882c4450282c4c03008a011442e240d80310060403000059211070100f030700da4440740080f0301e200c415003018a16064843c111103000303000034030803000020b480010100446034081090303145480003806a519003140803d843c0c01c221401001075041040300c0100141c00f4410200250140941c00c0d1501982c80e07480c0108001c0d54015081090340350300810000c03000036040304000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 375619568 1250 375618318 375618323
    0x1060f030f080d050c1b1903050307140301090c02070e090303130f0816060507030b030703080c191101031505090a0903111002250c030b0910020d36 65
    0xc1403003891902c0d00425a02900401c1034020f400c1009200c528442040030f014164920003041d00300d481c103d40c3e499540c143c3c2c64401c00382080c00c0070032540030074426801190f00000a09180580c040200e1654145034026482a29a0769880b160b042031300c1c1e414020200101520764010050f420940310303c42e200d01c0b0250000caa01964081400108060711840680d0250414240c54485400c11401a81d403d1889811550b407860100002d00aa02034400c40da04c4040140080c003c0c2d905554800c0c8580c0d2040c141611a48038584a070403803510480031009001d0301c80e0403030b10640c84c00d500c005000e680c40c522241301c80f005100c5041c8681d86404054aa021b0210300002c11058124142915145500440c5070300c24007902c2a88411300249030010b00c0031511004842d240c0b40c04008012102c00003007a03000f0b0025440400030400701d440102d001e5048910002594582e441c41803641080340d002268100e03405803030b00844062500041075144919046003840702d41101100080b0f241c40e500d03940700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 375620818 1250 375619568 375619583
    0x8130e16030624030b04021c0b03030f090409020a03050106080313090203061f0908061302030c0609030d110114010321180603180204111b01090503030a0903020a120807030c0201060f03 81
    0x4203c986200e60029502d40b240504115a11000101e0f030301c0c0c4001c0080c440c10040c90804d010403a250800008884415030220080e5081841c004100005000404401c0e40e00c00440c0c01d021021840a200e110010404000190355a0b030031090351076411404d40d80080c021510500411502e600c51721a40310303079003102200040340c90b52580400e46100364a074101001600c15034082107501d9114040303450100e13008500b01d51280038070308108920b03032040014050701070700003220300c1e1034281c042d1031146141c0300510b002003440c40300c1315055036110100f648181c030980458a002c031502402c0503800c4c20341c3c41c0c462910b4501200020b06e90b040080c0705110b00c804140c3e980c000f214041d00400d0143e8500c95008000b44040400c2240c26200ca03080008802c0344007408141d160a1980144910300c030055208020f5801d6030359202d2001e009182c0014141c0950181079820f000003a42038030200c00f411a1529446103600b41400020b04641081c610391082d03a140003c1032040740325403050343e030489500650 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 375622068 1250 375620818 375620879
    0x1050108060913140d09120f0204151508071d0a030b10050402070c052809151d01030c05030d091703130603230c0307030908130e160306 60
    0x5140715001000340684100400703003041d01d407000e0100d0070303008032150f0341c0d6000d142644410280305030f0460587c00804140d1211001401030030150001018129821080c61000e60350340c03106049040000c0f5901c000404001c02c104c106600aa40b0242340041d00c42c40b240722001c02e402007200d07026180000340100307000304000381451500b41031880260001500640d260715241c07400c4038003034469001e2a44035141c0c4071070310070562000721910101d081b809040b043e115440c140b10340c03004102c0015013042e800200880410f141c1c9000c5910381e0a02006042002d20b50325505040e0300069446c1c11070751080e04100c010046150f4420f40000075151050231a2011000c104191171071841620700c0350786401c00d071140001307a6a800d0f500001c2c44840c1d0b8003509803840a101e508019035034048905500640b814004982d416203e9800a00f445128204c001c2c500b0b0166085c8000d449a541e2240b0000c070750544c104100343c90138038840f141240342418140140c904140001d90744003511240a44103146104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 375623318 1250 375622068 375622081
    0x12011a09042703081806090703030e030a020406170106060306120b060a030209070818011506030c0e221a0d12050405040903120b0117070f14030702030702090c03010501080609 77
    0x8100c4030b0400e8000701c01140c0a0380c10300d8040c1c00d1500440d0707000043c080b140d5408483c00d2020032020300c80d03041a005000d03124155541a00c1c460860344860303405200340001200103842303c1c403a01e400741101c440030141c139801c0d0101035420745209402020403d400c001e0208030400500c0250000e05501c136443d40116655000404d09558040d40040e521400c8002440101500000d503217000d250255801c0d041a03000c003e02c9405c0c0c401c82d1024580c2c1c010350700b40070400c40c0c2c40303580000c503020710510300080302c5840d800c0020b4508251024540b440014030070b07681c070311040c584079208180c103149101c2900c0d0f1110364005445c40300f5000001c0c00c030458485da12054640300e00201d4002d440006e008104600c0b1034200103100e102c040f01005402454440418181d600900702e03080e04482d070003041079940c2e0f141c00301100e2003544110201d050000d05003c060701004014061886002c080d0300560300d59440e4010400001005400b8260141003007006001f180d900141460303101c0025164910a521880b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 375624568 1250 375623318 375623351
    0x3122d1a1c0f0b071706010801180e06090f0d0306120605060d06050403020304091a220b030a0f060501050a03080a031d030720011814010302190512011a0904 69
    0xe400c02064000c100b1107400401ca100e06805005440a81d1103005801080c90350400b50201542c0150101c2d001a0040044a003501c2e101300080882034004600b01c1e1074081918070b408410344410b00d15400c201501d01091004100d42844130700d0034a414001c5918095810107145180300003e001c554a4000003000303512144010702096500407810170007071902c3d0600944135005800345501c01070819860401c00c107151008022005001041e600e00903503007906000041290380b001d07401082c0c85eaa8014030640e400d111014501c0c0c000e807045000041f640c60400c08842e0705800c8244564403030402400403a505100740c819000b41424001207400072042c074080d24035251030400300c01e4032000800c4010000c6c00a001ca9070504003403000200841c2c084010750302c1410103607008801d0240da4030100083d01109000d00741100041c1001442c00c0d00310384401d8002d190404081000c500c0c0001e820b100070094040060060142041d040400e0741007605500d40d074410960550705c9103403560301007030407584030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 375625818 1250 375624568 375624619
    0x160b09010302070c03060519020405011b06060f0605070b01050616060903020a15090302011103090d1404050d050d0806040b061218030307030b09130506010605030403122d1a 76
    0xc21392002c00265680b41a101514088940314065100c0c030050f0351150344503000380d40aa503416184c000d861840e1040d000040800c00f0b10655243c0d0301c40d8000a08540300100385d03030141c03415a565540d510744a0400300d0b007011040c4d01150060b58200010080100302c007105d01d92455201c2000700e2502a9410201d1809020080281c0034690000d1001c1c02c43c2c0080d403104034070034070a400911803103846080c4000305001c11036040c8074a8000d011000400c9211300301810074440501140ca08103178480d8041815124205400c94085c2e000407410b07003901c3e400900781c640c00701003280c0c1400b507404028040340050107103141000224082da00450003612a05e0240349640e0340d00422030b03031a4600404014050010055a0345c0141c00b1000414402c00000130001c3c4550380000080c0166484e000044805a100400c00c0d0100704a402c203075a01c07006240103c240d0b2415859440c3d03804802180c140c0b10762960580134038a464078010b600a0140c0c0c0184c01c44c0d4284004881c205108800112000b6074000b9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 375627068 1250 375625818 375625823
    0xa020a081209060703020c100c05061609050f13052a03160f0507050a05030d11030105030304030305071b260d1e02010902150a090b03010b09040b0612090f0d02160b0901030207 77
    0x151184c1d0188c086621940c8002d401d4010760844103180c0b2940881d00030050700107000030004000c03000a00180c101100c1d042401382000e000d4051900356214524101c4600b600e02d607103001b121900c81542c13000030050f401140503d000040d451428001d0042400300350408110042c03243c003101d41c54100d030107002910003054001c0d05955201c0c80c1850095203d41c050b02004041a20b0482c040200121200c1135a05030780c0041d000354a002d055071001d41e555007012030700306c1d0000c58039090702000c40744d00c8860b0002030180e08440780c0051000d0104c4101042d821361000744076444180c0000215034010040c1103000490b01c51208511120031080b8098001e0348400703500101e6960808481091210003080c25a255960340314446480380c282d980103100a00c602c48205109202001a518056004802e403400003440d1342d1618204490352041d81e10111840361041c0c000b85c0d10702a010a05000300d11502840d071004d805804095000c25400342454000e81c0c0c003880000c54000d80380d90095044802d580d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 375628318 1250 375627068 375627079
    0xa0b270907020a0c0f05010c0209040c05120304061706030a0210020f0a050312010603022b02090d150e0102190c050109080c0f15060d020f030c120a020a081209060703020c 75
    0x103404031010f96101410002220320b10025000000c0c14140020280c0035108140e5840540c40340035020031000f018003074400da80b81907c4420000b0b0030b50b03950b41e1074802c40385c002c3c01070358445140c104041c004c10050200c40411404070170400203140e40c04104020082c0e8100c0b079801400c041c082081b031030f000b28507810721a80e2055005500500030000040e00c00039621200d1410185c3c2c82e828110241c0c09604036079120303003021031514041030364840c152034111552000300504024102000880803152030b041500d075892581c0340d400d2038904900494141031048c8000754070b07041c01c081c08014600f80300c036001e400b003000b0120701e482001002e42210b080c1d241c101681c0c6440d50000c40201c2d894800300c1c207462026208003001010501b4406946501ca90001010084080a2074081c01918464803045590501600c084550240c3d280c00c0101c1e88035100400030898600e01748180301659180b604031701910340c842000c08441a03009411920f8149081d94059151412881c059107440c120550440c2d104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 375629568 1250 375628318 375628321
    0x31502030901060e0a02040f080c0904170708070602092e03020f19090602060708071e0e0d080406120605030c04020c16180501090b130b0102210310050a0b2709 70
    0x150031034000d1f00c2513460000b0f28180042e5190000d55489010b07002c2542c201e13a0001c00280420b003802c06c1218202510070348035142c0703103990380d80c4401a80038046c2161501d40c086a410400d050004040080d42c0c00c00c0b5507519029458803082941041d6403244004140c1c000034802c00c502d0020f42030f6030030785920b02d619517030b49044a04060000c0c2c600d400346034018031404000500e0b00c1d10402246000e0000c0382c6640400c03042da003d07032000e20103101c01203905005501c10100030300d45238481d444000354025403c8035212410014020100f0440e8042110600e04102081c030980d0340c04100c440c036041d42220016a14104400303e1418011502c115403030000341a85c0014592012a104145042d45001e040100c0c0c0c0e00e424070788003111040841c4030707001203d68680d400c50369250b81c010228a40140126500250110441e041c02c0c52240c03d00004004048113004035130b0130b03184041000e40401c80c0e181e541c40307050586200d140d01804001100003618003a03017111061a407401000360f640080c0405615 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 375630818 1250 375629568 375629581
    0x1205100f030b01060305070212071118070201060608011a0d0507140a090303022b0c021f03090203011d0312040813030f0b15030a0206030c040801020a11060603030301031502030901060e 81
    0x40b0100340b0609000c20b04000c00501450310104540c520380c011101918185582e645908004070001480320390000d4002045060300c3c074442100c580b04100310b500100301030303051000003810600306901110000503102c031108201c900e4841a0341120554080001d0595980101112182c40c8045550044140000c551820981c072520310402c0c1d80c02502140c2d000c9a8600c002c003815041a2034494071111009810b4401c0c0b031140c0c4800307661500043c407440320304040414a4040840c001d204c8bc0c00309944590f1102103003000e000b940c01f290102c1d1342204007580720320121074403889028401a900d51000002808000000007580c0b01610308403105c2c1445900c9280040c1c2298540c04d007a218501d501c1e00046050440101a40007030a02901400100c0450350034085950070141c96983c001b8400d100c046842d402c244040d00740190f0b241d0f229040300710b20201c414245100580024000e401c1000107001003025600814000c540249005035a9510040d9460051586400030b9854140841c28041c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 375632068 1250 375630818 375630833
    0x44040306050604020f0a09031b0b03040b090c030105070309150c14030a1107080306130605031e0705090915010918021003021201090509010605060c12130b03010303050d0506010804031205100f03 85
    0x1541d1040c0e14081c17271100345000d52a203442c05846103e07201c610030000200010f030701e03901c82508115402c08544a100408000909450086400c4c5002039503503421300c8207200390050800010048003604100203031484e20003c080c81c1c90719034400440a40007000c81e2490000358051a2030b605140007240e19071850345016211540300761006171054411002c0d00200300d042d8450401242c4000f4000c1c648159a4003080e45501070401a0000f1070040803030004242d2030f1f041600348a04607800250000381c0084041c1014044180c0003400c0e05441e00122081e82e000b4034490740350b1075404030303025440403070343d03101c120040d225104200c450060f040d0000642d49a8075008580941e050a0091140031344540c203005541c01500c1c00c00c07005520a50303502d591407645400900100080c1c984100035140c43c3c0001c20322a501c00c1e8021000aa400210350404220500c5542d4001100346801401c41c24103450091061840140700c1c201144d40d4004102000744008078070005005d41c280413868165241468078 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 375633318 1250 375632068 375632087
    0xe01180e10080102280320070b0708040506010e0604110c070602101104090b060c0a080a0e12030d0c110a05010906050a05010303230744040306050604020f0a 69
    0x41c154540480200303120006000781e88052810102065000d40e45642035a00c00306405d010100349599124440540071800103001515050840841c0c3d454a45113080c104241000308070000b008011001e0100291001c9501411502c1c001056266612103500040060141400d01c060b07591002a40300c02054001c609039003112810340070381d448604401f80c1c1c4d00c2a00e03c07224041d5400c0900704420711078001168000710241c00d02414245c01c00000005070340c94001d01c1e01055071982404550000060b034801d080b54851902a036449114a10380580d941d60b0b40a8144003002e010746071501014101d12650781c81c034490381200700310390803102d05040141c000d10303421800382e426905240000f0340f141e01c00d00466040340c0d81a510020400c03003600520174520310403142512108010030082020480101d50201d00c043c03240743e0385801c41c03142c46000c00085103940350180051200450340c0d05540012040c0c6d0f003100c0d000310002c42c01d0740d203002c00280240308003200004550004160f11424550141c0540c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 375634568 1250 375633318 375633331
    0x403080708010b091507050303091f0b3001230a060608010302010c060e0105071205150603061309080c070e0a021303080703021911040c0c080a0e01180e 67
    0x211254448500469405400f4059103490b4802040b01000e02d007000407440d0250451540311505088441e60742c2c40c150b0f442135442450035407000c140c0f10340b028100060b44261003120302c020800240ba440c00300d40700855041004040801881000a0700b40c0d03074103c06d0341d491320350750020440343c0444941c0000c0b180ea907500c0342341d080c485000090b50108442c4542d20941d1510345465503168607540c01102e0a0000203012100c007500c5080c92120b100340bd0103001e0041c140754480007480400074080c00b086400007040e1015104403188503000300d07140c00040f240c104006a0340d201d24000580c1d0760401611240000030720b140e400051042e41c2c5100403900704150b8003c90344e04149070f280c840c410000d80c026248000710f64a0908803c0000840f21001440207a2080c01540c04228003444558910b81e038020007911a06c00c40c414449151030588188500b9005906002400e03101e541c42c2d0103510700403004008240075610041000c0380e801502490b01c104900c07e0021882c50711180c800c4113801069446 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 375635818 1250 375634568 375634577
    0x409020a0905011e0e01150c0b0f0402121903050f040b040b030a0b09090c091e070f0206070f140304031e03020c07053111040311030c04060302033a080403 68
    0x101001d0b803c50780c101d003c4501c09401c64400f039092987c000e0f8090080c40d040c8080c40044015200096010400302d4130403658644c002c000b51610380140044e044a20600d01c1704c5400242c0c0c5808404003c80415080720f0300b6181c00d82c2c41e401e1000c000c01c2d0702c0c0300302d402602c0e90210105002a0505041005611900c5003440038060901d5000900c000404280d0303650030b05400102d4103507840c0c14150840396001c0407001401c040e80b031a00c0a8140010000e9a0860015103910319001c19940c0401c034082c0c00040a00c0c1a00c403840e0300c00350081450002641d104110ba400101080505220315010210300040072529042905072400c00b030001d5100042d140d9650003210350018040c9401c1140c05e5040798002202603515403a000c0000e2407141d805200900c4540e501414510100c0781c90282c00030b14414259240c50002503808c041ca0000d940c500d8070b201d14100001400161000f20704506002c00b100d001c0c182c942401088881d0b1030a0045184130311600300807a50030802da0148900c1c1c09030380203449 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 375637068 1250 375635818 375635849
    0x20717070512030307143702010c0212090f030f0111040f0b2701020109290a0207030f050d09080708090f01020a0804060e2d1002010b1804020409020a090501 69
    0x10090f10ba000403038102c2c001c260f1450902c58044c00d2030000f0540e04c42d150007040d0b081c4490b4410200c54189040c107100002d002c0c420840c06580d02485038980340c2c002da00041103030348140006007080d032041a4101d80030b0016022031040b141c0b4100880d04013020076100074005107222025900d200c0d001481541d1685003950400545000020f0440344a20880f958401440102045103c502401c0c00080c90456594000402c0410420009080c40002e1640b502c0e20002800340301c020640800b803e04191240704000035030029411011212058071103041c4143c07100c8141410300b00518920802518040b000208007041003035074401411940000c450500d02d45508000490785c4540844000703006180810040c0b10780c5004100000344d40c44001c0c8200705410254842d40544124001e0641c0e4244000f61010201c4c41c00070b0044030020044d1008111601c00103002901c00c1c0c80ca202d1007802611440041010754842d80c0060501a4020b032003000d5440da19015000140024811b59601e83e0b880c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 375638318 1250 375637068 375637099
    0x80c100e060307030518150603010f0513020103110c031c050705070b041e1401020301090b0603090a12090b0a0c0204150f0905090a020a03061a15030a09030207170705 73
    0x204042040300e0040e140c1c50555642c1c2200390f004003405040c401609481403000c40b041d08042214540e5035a9032080c20304103040c04410705096590384902148164205410040811141c40c4c40d068882e40919001c1404690703010071921910510612843c0b80c00b0024085a401c074040703440c42007880e136580d802c1025554803882202c041c051210010501e6414102140208079003030180a0701013112800600540d440d940d0301548030b40c0d041043c0f4031a94010004201020191051340c40c04081580c44601c0d41c40c0442d001030f256118150010940c00000c10340c240454800d030308090240400c21405c0d0b07540d240d0940d025100a030780110891055051031095100b1026003101041118055048040c0e42400c00808001a06008111103080d124010b140702c007590b22000c0d036000643c007900e00061003d00d2090022a2140f40a08860140003003500361505983d081017100d522454076040068400e2031840c040b41864004c2c1c1c40305103100c0508002400d4048003080810898000f282c10b03001c48070561 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 375639568 1250 375638318 375638327
    0x6211e0c0b27030a0615050a0f0311010c080304060c0212030906180d09050d02030a06091a01050108040c0e070915090503010f0e070b161a150909190219080c10 70
    0x550b0070383e406401080303110000076081d411003400700c4202c5030b11901c2a510b40010401d4000e050748411686074031360004000b0701040100040c5410300070300e803580a404650f19411401e100c0980001c02c440da460030b0050140303100b841180464a4600400c0e560780c1828802c4681e60703003041d5902c2c24580c44c0306a5210a042d0009064690031000380c80c3d170000b442c903140420011600301c042c26601030144414001c0000d4a82c031682c2000c900c00c805441d00c901d4007250b55a110070058125034180205941804041454501b461044410300c1246005c643d4811030122180641944124260038400f201451401d030010303265802d0f00ca05030020801d2801509450f01510483d0034881540d030000c0300140101d400c85e0004100b8510540359031030807819299280c6c002d0070314414080003811031113410f02036082031610b042c0c010780c50b0860f003201050525020131502e5409030304000280080402945085413203440007019034064051982a071280d441c8a212749035075103307010522401c4401e602012480c082c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 375640818 1250 375639568 375639637
    0x105041a0702150c2a07030302060106020d050915070f0b06010f41040f0f14090601031a03010203090106080712110409020d050a110406211e0c0b 64
    0xf0054855007603116224010856072160402000089001044402e004103c0d104101d003462454020030341d891450400030308189040c0c0040c8215004020040f0301d0990000c290b0310400030469040e400c400c041d1056503502d00c51400c0c020300d5010584059010700c02e4100c00180b20741d03402e0700d0f0803001d4424001c00329604410622a46c0c030703450040c80c5541221134000c210440c403c651504d209801c40c1800044800c40d0041d510021040c44804d2041c05403480001038500280380310710340824160b054000052125030010150303410103649032459921340e65039683c2801c07620b00140c02190740b030808215aa0181c030310390040304102d03c20030b07500294844000144101e1990400081c940042c2e1202c1000083c0c01c41d4081070342c0c000b01e80000040412014400c81c0c414601c18004442c14011203000c1c04280d0340141c1c401d064421850301c010422845003d52102c007290300c295200d40b200e03c59031008050760240c40c00a4086291400c002c98806109002088017030f03820711002c45240000038942840d001e5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 375642068 1250 375640818 375640843
    0x140a0f170415060f440604060c0905031515190f05030c0102060a150302041109130605011209020d0804150e040b011d0102071502032d03010501120e0105041a0702 71
    0x4110f1880c0900d200320302a0000b080140c40d080305c03540f480510b8240403541c540c0d030201d00e84c1d40100c0f0602c41040000d10508818148134282101c40900d800002501c40882403052420380c102c0c0704c00100074000f01907203c80344a00050050010300610210303400306810f18002c09005840c640404141d51400007050125600140e000b090a80e5961014101030910b0b0007900b110f80200e07140100060780c6500030300005213402a00325403504410350801c980403400d0081c0d503401500d003440920040c0d80c00340c00804119030060002c00c03030030324601c08a80003030340d07103140038090041c041400320700c80171585004003010703150b5654000400f10501c100001c4401016489002c01d0030704200c01e601c8189050340810b11101401660b003665542c020615180729109040c0700180c01c0001d100c0e922078071184c16901c0a155a25040705980030800490940d44018003e0301d0501800c5240f20040c102d20341c10140588098030003c0c0138900f46440c0c60b00070400c1d1807804c240022803510011f0b441c0761001400501c07510 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 375643318 1250 375642068 375642089
    0x90903110106260709110304121106010605090d0210030203040209150a51020609060601030506120304090203012301020a060e0102070218010501020d140a0f170415060f 74
    0xc94483c0d8004008003600768003a46405504000a000680c51169540400001c08860354a1826160107000700a82c00c00302c0c01400801c1c0b400300442c140000e02e041c1035481f6414041d030303145841e030000b07103010625401c02580719949140301c0c9101541900a1401188240d80c4041c0d0350321403008540c0d403003544142040d0000c0d0850010040c144901e0700e034030900b0204a803010403001843c0001c020107030480c4030000038661091442c1c1200c80039a107890300c003542a803014000505000c0012a1540d2001d00514105a140d00100d541c0b581c6100f410492880b00d04104d079555999203550f900690400d100d43c0000e10703044030b00310044400c81c2035410035883c3c05a001d0403900c03a16903a00402411126500c0f8001d40d8280034640050b1030742c0d19242e0101822841e01d0301e00c3d61400c0002841c1c442d00031140c0707040200b0a0f5a01d0701c44103460003074440c2c00d442414a000f0008000800f224003580d500105240500c5540a100900c07140c106da85801350321080060250075190404550842c0c114402c40c40c0b480c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 375644568 1250 375643318 375643349
    0x120c0312040c030b250e0d1b17010501080706030c0c0f080c031c0e0d02071502010f05010603020304030e030309150d020c0a050f0105130803012d090903110106 70
    0x291903120020380c094469402c4540c0a81c0304e445001400c00b044921300046030108900000118a0140703668a91401c0c0c40c1c120004c0b0924400b00b130340201501c5004100b038030b540790f6401c10f84403484441d8001d042c107110400303200048011f40c0c501914007032041441a004414010440a01ca402040c241d004262680100e00705a5590341e0070080018200303039203505081c8254118a841400204900e04d00100c83c2040c2d0110307403141c1412100b02c010752450a92011090704243d940110b44002182c03844501a00d884520602c141c2c007401920a14158180c541400480c000d034150740030318001c03406559101c041a80c59002c0c16600d01c111181c0c075130b01540902554444c041404000c02c030072000100003604100b44045202d06c0d001e1469005c8505400c80d01001261180c2449110303841424012800841e0580b0748a0341000d10041c094030300b001c00d00c12019000c0010700c5103425201c040040101900b280c1d1904030a00501c92460128009020107191050f038840501070b02040da20b02a0b00641d04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 375645818 1250 375644568 375644587
    0x501080c0a0e070c020a060e0414040f02091b070606140a0e18070902040b07021509010507060902040e060c040611060f0106031515090e010b1602190302150408120c03 73
    0x42d2000070075400c100482ca04d00b550041e2980541c0c080142466100c60f1400180b05003000b09031110360710307600e400342e0030f200c10040072074840c2030b0820045406a5004006840b44560060402142009402c500c10001405820810960700486c11980242041c0400b44200420072200186078402c00d00c4002c4013101082d00c2c54001c180301040b9200c82801c81d0b41c01951050410283c3c1c0055000c40d040410101c0c0b80303415428001c106064450071403085e10314291381180083c01600030110003502d6280d40d15070b02011510b480d44030f82c950707003801801c503110751030502c0d10004e16a100d0b005803c00240c24810542850b40001392040c000c039080f20740703d80e045e82014000c81c014051a0116024a070038030300c1c0040e01c000b4000c50740f501c00303d10b82e90b2960740500f00f03081c010b42003030181e000614403417003080004e40d0803100c1d8003840e1101d50b0440c0d0f200000c06164a031320808000759000a51f014009220181850401c54018800c50300140261207a0801c0700c820071081d40240c20801d1280e40080100300070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 375647068 1250 375645818 375645839
    0x4051f15060806030703050a060501050901060c030507120e09040b07030c0306060207030b0604090816050c01050703051b1f1e110d0e100507050c160b040504052707090501080c0a 78
    0x900003c0541269420b5569440340c3c3e241018290090f91065680c034014030640c1003403554640907026a040201450350650360040c05807282c200050f01540c00e0364038030b110040c824a0200e200c4000104650600d003000e00301501e841c0820307a07950000c02d10708190910100c0c0a4010401254469005411080e1854031071400a880080c03c950340903980b20001e000048642c1d01401c00450300200702080da0040d468154605201c2c1d04041d07043c000144085c1d000641e01004858403800c10032144a25125240d206600d06840400000c00911001d01101000c1c1c06682c090a01c0c01d21341c20780110348400604502d4120f540404111040360000c1014446542d6550400d0110781c092208549050050562020868070107030b917004001040094507540c00a41049108103007038915030307880481c500d400740d41000f5101d244038840c02942c403200004c0c0302c41006805120342410b086d007410342c7e0381030b030380031564480a160144240d020710740400030440c0d84000078400d034140c13400303440b0620030703810b1a01448 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 375648318 1250 375647068 375647071
    0x1240b0d050402060f120403080108070e0604090c03020303031302090a0203220f020a0f061e020c0d0f0f1419020f0f032401061d0d02090712020304051f150608 70
    0xb130f0001801c0043c1e120314140c110080104103800d184d4100e2504103450300500c40b01e03040e0f001c0c0d10f05901c00c69041c030140c07442003981c68003c03000303c07400034286010740781c00f585005041d80041e45c14000801041013546145a0b0080c0c0c10f48204d5603404c0558070a41e0b070004900040c3c0d01c212000245600410107080590007001d00c1364014068000903041aa0003c1c41c01e4600b074100344103c100c1a0800c00038240c004242440340d07030500a80c01d02c4100c0818000355035200c1107040c2c82c491f0140d9121403050000d014280d1484941113900d50181c1081803c0004ea1000104c0450620303100d50084140c141c2071860301c91144503801821064142c0108080141c540c8954400c4c5605015005411640d11400d0030301842c442401000100250715158001d04035110f4107400c1c503c030740402410444243e5a03440f090209903411034000303d1584956108440510028124901c3d4510000070b0206000001448a5030741030a840b03981c0e28030501c00400c3c415900e200748852040440000b0038445a0302640308c85 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 375649568 1250 375648318 375648323
    0x12040f0504020a0915050a111c0f140c0d0e0d0b061905060a030c030b0d02180703200d060914040f0201021f0b042406030b0102030d0c0201240b0d0504 66
    0x2c10310545c8039565036040d00c0e40715070000c010440019003002c02c0740c2c1045811002c80d4800015000e807030260300400b000b0210b07040c3c0c0c04041010743c4c1080c00d44580503054480d0740b5540c402000b0345481005640513034500c0400300050100e40318080da04640c0c500300a408140c26402070380342600c0c1c0c03501424088011880a4000405010f90101203900c1c0c50302406041d4500640c3d60204480b07011010240440d001314003e00d01a02e2000344040158441034004040300700c400d04003920f50754030004100c00400030205406001040c0035803034810102d0180140242c04001d82040000c140e60318080d0085688080640c5480c04030301e80001c0129440d520300941c40c0d401030040e94080e200700d0303a9400c1c01c640c1707040508102e80d03525a00b5120504142c442c00c214001911104116048115281a1a02000d114070340c20907468002028440e4424001c0c3c6034441c0c9142c42c24844d0581130600a4041c000640544402d00c5008010b121104507120f2400c01300c0b0740741e142c1c2c030340340481080c107440150000400c207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 375650818 1250 375649568 375649577
    0x1210020d0209090406140a0203100311041b0810060513030f1a13060b060f090d05190b0103030e0a050f12030412050601080d1107120318060e0312040f0504020a 70
    0x10300350743d00e4074240c0a1059226140000d0034820300d10800015000203440115400c2c03046c4100054000b01070030003410b50741c004040c0300d1003200c25030024019048190100e8a061004110710035900d410400301801140b60040341c040d46615000c08480381d0160800404800481803401c0022820840550b45c100d40a004117103060140505111861503041e0b803a18015180320030310038103000031481000707060201220320502d0600c00381c40c6080360340a404d494520a00c0c86184200801904125491610b4500c60080300d8280f9142805012001e09100550202d0300c030310241c9010f86071101c0168169040106013081201140d400c1c00300103864018110305d03a2200300400300b0003981c4015501612071181000b800b0f20740c18800b0090a0569000c2c00005014810f800350f0002e8a001c03958106640361488a0402020213080440710107000b08142c01d4280364881000c2801c1d6401848030350304040540131180d403c40c1d0102420342d0780c455071050b07500e08540c24109000d64545070f0014000d030840d9140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 375652068 1250 375650818 375650827
    0xf05070c0b16061b020705010203030402030303010e090f010f0f0606020c090109020a05040f0f0911120c07062307021b010210050a110d0e01110f090f0619031a1210020d02 75
    0x4440d0204c81300c0703003e8a18150303142c1c030613407071029410061a4064182840954190304107a40031a80d00e00041c011140d0250b00c0d0400160026403c000c03403140f40410600070b00c0030601a86a450041910501c0041c4c1c0f241094408201240005040901d81034040e2120340f02d070b8070702060b0f80000d4000c00c4095007000710400001072034160048010b0040d01070300030340c4c500c0a890882c11204880720159a040160300a200c440c0e40c0140f04c001c1d25600c80e06621000d83d40d0010b40c0740050081400001011001540e03403902490780304c2c0322800c5403280480d40c085511007508028019580c0c0030210095005a02184c4d0503200c811440e007100342c00006050001c140f109009481c8c100c03d40040460724101070b030301c080c02d9039a40802d0059030024004d0f510b00700d241a0f202d40d0000c40c6407040c5041503006514003800b9440a440312411168042c18504007000b44070142000140a03000092918078112040070404610740b606480b80703007500c05404014006800311145040c0650403110100b07013455030070701 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 375653318 1250 375652068 375652073
    0x20f0301060602071d0622060e0106031b05180609120f030a020106150504030b040309420801050d03120912120b0f040b06090d060c0f05070c0b16 64
    0xc1c0d41c05000b0319000341c08414100303022505804070040500d00b281104e1000d20255032540840c0c0e01d241c0b030103030058911144075840c0c000e01030306442e8803040c801c541c07517000001c0030b50741a403050f41292071a4512000103091b0752021140c9000c1c1504407007441142e9064074286240c11f0f0001c0400c1007006d040c1448021035280342c2400c0002d003840d5190349800c0001c6000f030866080c45200050004c00d408580443c0000300e009101c1c0c051408014180e40002e0045800d25001d030444030300038604c07040c005100503200c6d02d8801100c1c80085031b020940048109608080303030a0004450030b80700b19924001c043e0b28000c01c1200030564070400380c060018400d200e0035064407a00610310402d000d0758403c0f4810711060f0004101d050400d0306212030601d0900c0000c12a500d103042c0610f080c008072400f00d1190700d40800240a0310070b2250090b4804400c00002c0200010b81c0c2151000c0580307a1940b40403800500403d4519105201d402819180e05030000e00c243c244240180041d8825504046051000e55 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 375654568 1250 375653318 375653321
    0x5010f050403020f190519051603050304060e03060c03130c0b0c0c1018090b0109080115030203060601050319020711040c02060f06060a230c0d180e070c030c020f0301 73
    0x81e074040d00160000740142000260420902008011522206490307854036114651140940d550a880d2040700296035018080d00704a0211407154621101503095038a24100c0d039242c0c03040c03056001141b50032044410910b004103406200f01c1d08a195580345503a211400f1140802075901105c9280c9401c6020524101d440040c1010070349010042807010300003020800038180f12114001044000e2010490072001c400c041d00440d0f04118012480d40202c000682d141c00c0180c21401c3c40e5840d080c0b102c0c03040342095002d0000c4a000346c05071603c9441d40c2004407003d100880f8075094100381c0301c000d02d002c080242e0080821a0182c0350920094680100007402c1c0c0f85030910b250010782c4510240501c01002c80b03299034020b001200e06501c0c040b1402c501600200100c0000d426110103040203601241c0080100e4410b000c01c04150303114a145508040c0c0070608404240210706956100810210702c11a8007a006481c60f84a82e051540c0c40d0f901154000d071800f000f00c1e0001d1200c3c03106034407a1000d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 375655818 1250 375654568 375654571
    0x1110928090212010e0702100f06080f0115050f1c05010b04051608090c1c110a03080409060501030c0c11041401090e01141b030c0705030a090302010f0306050109060c05010f05 77
    0xc54601580c1d07699180b01801a504041e01700300030a051540a01002940002c1d2034042d0003c2c0001c00b08620941d884441d000f4140356000407052700400c0d030300d05d40b079040c10f600c1001c004a4003c8460345c507a48480c207110744110040c60361604440700024a041080f004944802c002d403152001082541a640100b4107556040d00c0009070912154100a1000d4101308015402011003004020f8114150006851072034080c41d1059001c80050810041c061617514000b162600a0040017101d0380d0389c9868015680a48100c4e0501480d004000c034a47d0720034001c44ca90714440d0343d00d0362044000c2d608c8010409440e00140756000d42d69005900759500c00000e4240206140c0c0c030300154140d80e07941c007a070070b460540c0449540b20701e00000700031b01580343c0040644042c800c80c083e2505c0b6522103140720320510800b000640184404555000c5c403a81c00100c460a40e80700303a8503c0c810b0b012402054066032254020180400e10310a4180045480707070301c0001007070307004200100c0c400791002402d02c11103c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 375657068 1250 375655818 375655829
    0x70515040f0f030209070206061f0e0913051204080307080c0102070221011104030c0e040201021e0d17100e0a0213090606110601082109041a1201110928 67
    0x5541d4041003517142c8035203c240d000f16607002070003483ca06100000e140c080d00040c00002c94040d001b500e15190710885d0315594940b009050b04c400e5041c0100310b80d45900a5000c01c0701c41e44588840f04940b1001101621b0071614040021414640503a8504907507411401c0405800d44d400e102d05405a039451030034400d00c6aa0a1040b5245542c40c0f030154251881850008902c84007004104001181103018004403401903480f0200c0b612907100403030a2041200d00350503a214030801613180664003050070048102242c5814501050005a000314581c0444640040c20440481082104100480a03510002040c00140780040d1040843c1e5403030400c2d00100212136950105001407500321029940440f140340081403d503140c0345041d070b5100c218404003503642100c480e061807180303407210640300394840c000d000340001e102d1005a2200040c6d01c02c00d0f54440c4280d580401c52518041c480c070441040c0080e81c0e2481c24803544107004010664a110400c440160807082c2191811001c03032501514 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 375658318 1250 375657068 375657089
    0x30c02090a180606093903110c01050717040201020a1127010509010f120f030c060212190501081e030c1204060e0301020f04091a0909030d1508070515040f 68
    0x7400c202403601250003003042c0010030100d00403101800458070301c0403d500311a0a10391b090548a44804038081c2079482e480340403441d0049603d403404041074004900c115459612502903621400344150800c1c0141d0340680986c100c4031101c4049103501030003840c0b083c0054816050205100c140d030703460a40c0f0100e41a284506040140107d290800d1400c4c0180a40716107254401e06101e8544c407800030f0100002d086191450030034003018000c014000c0c9054221104548a1780d0150364160400022203501c801c01e9010115001e2083c4c807480b4140c160740d207000003004400301e0a0000c03c030148542241c1030b440d1009004103040788904205441d03442d980c09032620b403268900b03d009040c680418124600c40d03401841070030301040780c0c0c10036101180c2010401007541d1070451040040f1041400085403c94203030010840400c1c8004001d03d031960541c4001c200001c0c00008a070243d64650107514025040002c0030030041c94100c941d22103034440c04051600d0140d070707242810320307185007a400aa00300c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 375659568 1250 375658318 375658331
    0xb0c280e040b12061602010608030f030703050604050c0a11150a090c0b0304030f080402040b0d030806120304080c01081909120f081312050705030301170f0a030c02090a1806 76
    0xc0c00c107805a01c0b0078882c15120440c1c2e00700380440180d01c1e20301c010407040b058586014140e1220f4400d40000000302101c50941c0d603100b03030040100c00c0c2e41d8421100140846e09200c00316100d03080901c641c521400c0c0b00c110840c2401030520b42250010303011891303400548141f03803005445130010145103001d00a10b08001844404601d46407000c115280d128961200782402040f0101e904810001c880c2c101516080326540d0320340c40001c00404a0030340040d0402c44601620303003016000081503008003401c513401e240c4110544501c03580c901c118042d9100c5078100680b413903229401100c409400030201a6001000c04030344040104840f90410140c0e02c0c8014400320601c2c41e03812514041d0344210b079141540a1385041503401ca01801c0c0190010403081e09903280081d920b101c0e0044d60103040d407210549650b5652400300c4102c1e001d00d081105100e006d030f020000b01910700001c80301780096064845820112046d020000c07941802050149015144d1500c100402d0700403000103062480360000064a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 375660818 1250 375659568 375659597
    0x15050306130c0306180f12080603010608030f1303050604060504110109150c0203071a040807090203091f0908040b19320904060b0418020301030b0c28 66
    0x1058009001c000050025448a1010484049204040c0c0380c20403000318070b80d11505503a5800d0581108003400c00b95494408808100e1544108a007005d100e42d16120700c1d4807a00101822200c162148007415801006130034050820307038003d04540380140707050707a080039981d0700e03103c0c20104100e03002c8400554a000300f200300208400321040c1a10207180c04c0e00c1a03410f14699140c04d44841c2d40c840144000084850115581045440c0160070301403001107026045d144086000c2d040f030f00900507a8001c100001c6a01489442640d2141d08031000510000035101c1090b038034402c044180000740350f00c68210380040b0300184000c10090943d070202a40d0f800c005008401755280b1030481404001440500a40c25101c85000c070083c00c1c0c04200004250445100c010524030955882ca5082824881d00044160100001c0c3c4105c03658007c00c400c83c0500f1032501070885c8402d000041115000c10003003041011054054448901302c08841c0c041d045a08040b82440300100020200003041862030020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 375662068 1250 375660818 375660823
    0x1091707051210050708040b041401090804230d080909040503040f0e071d0a090c050c0604080a110309060f0f0c1e0c180a0905070e0f0f0609130201030519150503 71
    0x2400a020b00d0406d03030720700300396403282601c03200a880075043c803a603502c40380c6401c5020340c400c3c3c0000754072041250361350f940c0e50201900c51022405d0000e0b0840e0040c1c902c10941490800c10400036400b0400f01d16050b1a28108461800003600036648c074842407102160032a091a1203001074203600d000f00120380b810030801060390b060441540581e006c107494002503a1030703401004003503d110400114100340700c4202219a40599030341003007548592000d010034030800f0310003001041c0403541e038080c14015881800380d880c1b0038103d0146c0c02c401c00300244540c08140202501544521181c0789152061a50115140000d10140134007424080704403055884410031611000d09002c0e20f081521079201101102c460100800ca441e030540c07503071003140400c4014070144000d004c9080414445091030b4000c60100b4038104d8003010008000004604246010388404d0310851000c905046910015401100507103005429054844003d141002d100c4809018480c2d00e248480d80900c0e50901d418100352 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 375663318 1250 375662068 375662071
    0xe0106150e0f060d0902040908040302030d050a0f080403360515070611040510030c03050601110309100207320117131707030e1e0109170705121005 65
    0x809210000e4181c081a4035082d41c0c0a1189004682d21502c69004000c80c0c406000c05a07802940700749426403410401c817451018206986c029401c03125000c803070707a40079100340c414102e085000c2080701d1410340b40035210b25107942d4003034860b00d845c484040380c0c0481819101c01c4400e00801141b40120803940380390304500c03204000c00c0100c44072442c0e0611480703030b074609101c9d208010b01115240e0549600e07500d02c1340202ea00410000c0c0a1901008805a00800400083c62803100181c1040301142941d1f02c22050410018111f4000c0c52800c03419004025003182910100301c154001c5030400035000ca03021a002e07084150300c4501110034201c0610404030f0000f449152414491000c42005071160504107032a8003049910f9007440d04c40d50750628400c04032604440b02e160000c002940c41c20180d014040b10340502003500c0300c00d6014046200e0145107141d240103240014440d02042220a10b030108410000b121102600c286546640105034600e0092030350351410780c4090111040c20000e0b1040743d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 375664568 1250 375663318 375663359
    0x50a0b12010606090b03060f0d230318040e0703140a0302060f01060507031101110406090915061b031124090106031e1b090f0b09040b06041107060e0106 67
    0x3000140d08080f00541202024020100d45140120001c1c005855060000103141d000401b0141440c015141c110302500c0180a07220041031110b841d24542000002500c20a031150840b860340c0c15110014040104211074990540d4400d9100000114000340121080016044007800c0041107604010b0b01d0403034040c0407414045900c0e4010020320b030348802580c2c12281d041c0b925100c2c0921449039103000d420b05100b07401c00c5600000b000140c80e03802c010540210b8111440900c00c0001002c500307600c078001c0d4450400800c810491103400700c0041180c01300c000b8481d00f0003d0320400c1d6031441514040030588000c40c160035100407040c901c0c11110807640d0112018009202c10750079070f940e2102444603841505002c4114009800402c42c640800e85805141c54200d000459030b90446070001e130011a82d501401403611042c1c2c4070504060002c544240d4018080541c0d030b4940509010003062031000c0c402c0c2c0500c00780251400145280030311b21100305036000124005051041d9000007003140b1000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 375665818 1250 375664568 375664571
    0x10b0105130e040309170610060c03021b060c0712110306010b07031d040f0b040b0d1110140705060106080f070804061a030a0303150603110f0307020c04050a0b1201 72
    0x4208044460107518020368008003140304a90716245400d8620142c3c40c2c10016070f500045000c142e00080002d40c0d144543c00f1780c01148007040d0f0700c81060341c2d203c1240102a0058112621605d41e044082d031a221003000058031551902e1209480c10742030115a8001c4204500c0032040c031000e1091100b0351801a900841c080e104035490140b1581851055590080a02421581c1211424079401d9a0030051001038401e005100001000500404994184500c25441c180140030035051850a0800459105e071038064000700b400100400380301c02100803010865001c0d110b040b8081a0307405441030600c02c600a007000d50419038050061038004040110381f101e01c0040101c0140d0042c200c3c0c0c3c2042d005031000481403c82d602070340c10030841e0980580c052040150601c10143e245d8403003483d0081c80e80240c0e00040d100c0c0c03021015181c0c0039800f0810b040c2c0510000003640001ca0080da0400b0032801100c91460a10001c582556000c4a40710f034910380d6044001c0309401c00c80381803178036850080300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 375667068 1250 375665818 375665827
    0x801020301081b0a1a090316141210020a090311010201270f0c0b041a04060c170405040f09210207091e110a0917030f070204021207090503010b0105 65
    0x80c1d80c3da0741e0510b10410468101e10510000d103454811000c400380c048004103000540240142d0401075000030000750180c0702c0c0b038420500320881d01d84410103444510780030f803d00b15501010004d01201d040103601c058021148440c08080d041d100401003503207580c555600031851070a1900d807145080801906590402003c01001c80c2000d04c80f0070b00c000701c0191401c103440c02d4107114460b100103000040c0118901500820300c0c40d00200600111088403175150042440744451022a004511900307010501c00c1c00c250300017803c1405001c0000d00e60014840c20a6601e070300040980f45805034030201e49a458140005212031104030b10020700305018444450152090001d542d04d5080c410390082c1c80d0317282c107046004256018510140d40a031101400520b003a50a40710540e0f104500103408100c200800003181ea41415044440c0c00880700a0341c2001d4580100340c6c09035010030700c1280e1150f0f080086a284101d00404580203c480ea81c0f5440c0450030301003451700b1120b030300701503a05003c0c0500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 375668318 1250 375667068 375667079
    0xa1d090d0314010302010c1109040503030612120f031b04140a0501030c081501110109060b0906030f06310b0a06090603020a09020901141b190809101e0302130801020301 74
    0xb100702c0c1140d03428a000d05001055080450340c01e41220342056200700c1402c10b000a0040004c081d502418044031082040407101c1d030003c1e610840c980103050b044506101100380e440740800034640c00b503110100ea008400c0f40c0d428018041d40950005000200341c0c400710b60142c241110b00303001903c403e00b130402c014003400c0d0003d443c20380d000b02100d4002100104400140e4854200c4021100f00c1d40000d0103031000b20f16108024000f440e2119000381c03000da000030850700c2c0c00a05050241d101c03402130985030711103454200d0190310aa20003c41285041144203a039072201501c1b000540c0900d4803440c0c0e60404180d44001d6801d40e50007500d81c1420300f1424000750ba1401102803c03540300d204010381c4e542003040149c445042d40018800000c3d0003240b512000c004044580b0100f10542c410b8461700203503025181403405860b940501001401d0190349010300300747c900150040381a00703110b030032580d520240075020401505400001394000c90345030350038070001501001804c0030300001d40c159030406 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 375669568 1250 375668318 375668351
    0x406082a1f02060a06050306160e0a17010c030203012301091d0f01081609020918010b030702010501080604031d01090504020406020c03011a030a0b07050705030f22051c020a1d090d03 80
    0x503101004040070400d42914990082d000840c0ad9203003c4c040700100c5070fa078101c0c004c58210380140f1440550038003644040180c8a8402c4906079250f03249601302d1b03120081108410341485103400e40c140b041d500e0010170034001011038001d411040380306c0c81e1650300e01814074000300341c3c0603400240c96900082120070422003052410040c0d03842c1d00780058482031014001015141c454170026450300b049400800d140c55441c009511901c5c0580085c80203903607903440c3e2950340170110340250000e80703211541e050b5081c8a006c05108a034051400302041c036129000202203030b10940c806005030740b00c020140800d0800703002c1e0303032090a806801c01c0710b84410140031940f6046100c500400c20f0803a900042c2e9945d00481c143d540154000044079110700d001019013285500040304826170364110800e1126590400618809890b4090f2840c0200c0d104010000100320f25000101d074003809803400860764450001102a01103400c44440c0802d0900410044c00c004998040388100350a1444400c0c0c0311100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 375670818 1250 375669568 375669571
    0x501091e0c0e100216030501090515060d0605060f03060c04060f080105090711160b030105040f1803081503030304060501030c240f09030506240406082a1f02060a06050306 75
    0xa0707840b041d0500101c3c01c12401e0004080d100b4025076406400071042c800150310000509204a0807500504520005075035903040490f035507035100c07a11440d02e400145803a004290000340103840000c0408040000030b0400070f040760b080d8902007010a0401110fa40325980a8800016041030400ac0d414200401c0942c3c40040c60541400040030084030903210030003400d00900d5024a1002c4032035200c1c4500142c5503c2071003000e2256052109540080107030f03220306400c203035071000742c915104880d40e4240c2d042c83c0020007886070501c3d01c0c10007910684043c0000c40c030992107850f000400790304604e044950300b10f00c0e8004400c50615802c0002c901030840100e600118541c5c24050b10130641c94400300c8007a04150030041c214081c100600c803e400130b8003c103502c0007140c00b81d802d409540c00b40c02e00084440364415068a6403006040c1c8180c10700190350060744840c0312a02000700314401e004506800036000007144038040c0c00c09240000c590510542d500240a40400d014003490100000d0745c40a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 375672068 1250 375670818 375670847
    0xc2003190f2003030403050d021219080c090d0f06050f0601020d0c0816050d090503160608130c06050304140105010303080c030a090606060e0f04090c170708010501091e0c 75
    0x20540c20316007a1049210b141c6400c40e401412640d07600c0d203a10b08281c49400301d6000304054460030b05c183c4100002101510581414840e00a040d07560125013201c001c0030141400c130003107200700403100c6c00303454417812100d4a50162410701a80009490042304444d00100700220740759012052050907039002c20042990805481d007005000d04c40c0c00c2030080c03441510b141004501c80d65000804200d40802d191030920025107420300e041c4e0b0784a0500d5111109010300d0f4030380c009850340520103140914001908041540c8450154032404d83e1418003581c110b130003000c0072420200411042000e80340c500c50000002170000c4c8095403441c0c0e0090540c00c40905112104240800090801106a40060101c540005040c840381c3d076220000f508940c070001d03242d4000c10240c048030031141480e0140b84d00306a4080e45000c066441c1503207814940000260210340c5024521001034840f80c24060b060281140d0701d000620185510320352800003041c103c0303d0320181c0c00c0205c0f0351652038000e4030000e003941 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 375673318 1250 375672068 375672083
    0x206031303050408010212041a09030a03021309020d0e062203120905060109060f1703040b0a0c050a06060f1e0612060e01080309041103011a09010c2003190f 69
    0x1080c92505a0701c0d401540c1001c00c1031741c400700d06607442c00c0c0345200c0140240e000c2c40d1404071007082d130201000503000455100000394010020054018401e500030210100100e001803581600e0354440c1c820b0740d00000455a450761038207095103002e0414000d158214900e01d00c0311607261400140903031404180e83d806001e010b00420392401c6958a0f4003d04031080d40402503504640c0c4601c1040700070b00743c500450240e240d50307540100f0400036a0690f1034025041c0e40c01582400e2420803212944e0384400340800030064180d1040700011401c02544c64164840c26000c2881428480d040d20b1080e001d6010301e4442000d44070200a0203585c0d4030010940e5150b240105a1541202c086005001c1e035078000381004040c18000030f0003407800b0002e03107040c2d070080b01d00380b110012140090f0540c2c0400c0c080c1404a840c400b62500740740c0d21400c010503203210103041c14030740181c81da142d05200042c0710340000210000c80c002d41c0003614088c403000381459002420800910510746400788004240500100002c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 375674568 1250 375673318 375673351
    0x30402060403080c0616020a0803041b0e040312110414130617011a09010e0f04060f0e06251704050a0f080a0f02010b01080c07170316090504020403020603 68
    0x5465031000c440c0510740107001c03181d51300d0848610325600d500407100c0410540e1303d40c850300380c0d0700d2000c1000d12000d6003008803603046841c0c1d511407292000300562005425a000440000c031a40300445861003107000303403120300804410700000025111080110841400e04010903c8810440808944607146c20385000405040440c68070700280099080200e501c034000c0d609061001054005001c04200e510709410500d8507003040c8035000c0c20070301070fa054145504000400015460229580c858000c210100385415011171140484406940200460b0805c0042010251414030102e550440103410320648003c151f000800300001d16a2010004040c0400318090020800400805d035400c41c0c002401c5c02d0407440d100348654414410040810122148024000d0040c480d42142001c10307101c1c02881d80e038090400c40c071540a10400c4454815100034040b5481c0300720b001e544550b0150340180c515441c2070b81d01514000b01940183d21980c01000144016242c200503a80c200040804040f80b4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 375675818 1250 375674568 375674573
    0x7030b100f15140d020a0905090c1902010b0a06030c110604080415020a05100903121103040204180b0705030603010e0102040f1a0f070303050613050403140c1f05270c01050304 77
    0x1050b002c408510301c0030f8030224404c0902002c2d64014103569080361075034115142ea44003441820b0200312404031004500344540c801c00d0190004141c85142184000658044103030002401002c06800c0040000e54610301620010340040c52188440583d00080205141550310000303540318034000c2c030424080d0414501082741c000c10031007104a85c1315041c1c07402840001900780041802d1030082c1c001413030f20000d2121401c5184103c100100c01903c0e03052840c0d5464081c400504508103203220050f40c8040c2c8800070030010719030303e400358119907509944c03400c10100301400d40f0704040d141c1140340d20400c0100807050711000000125040558450f00b60500306081218034052200b290201c12400507001c001c040d410740c091445003c003203410040c00184483c0f4a07040300d03c11280100850001d5407013000200d040380c00f6000f1128100b00300ca17130901902803203040103140382000105560311401802000201a40c0f0742070305802e100f40000030361904040582e41c45902d165114103101e00000490103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 375677068 1250 375675818 375675827
    0x6031c020c0603010e1614090d0305041205060405060705040503060103020d02030f060c0403050706090501080f0402031c0305180a020109030303090c0905012903010506180f040e07030b100f15 84
    0x101c0800510080d101e43e035aa05503504144201d0742c070300d91104441e000114071805030081300c5a142c00c0c203030f03c175082128031401c0c03045142c52860140c040c06004e01000035001603040c0c00c1941948914080c100354180707460070501e400e078094440000c0c03082c00d201c10322140e20001400e40c11203804450010000d007480c00400c0c2001240051086503005d00c208010384052044000c1040720302c6441107641265030b0350011150b080d00b40c010700340001c9080010541c68061442c0c1c1542150004050301e03818440d8242420712000c00d0749083c404a900d4000f008208141c0200c0380410036040c2019001140c003960000713100c2e030007a010007000d255413002d00c1400c1c040150743e4640a4a6581c030200180e58440c0b456040c070541800e03040281c404450b010422040e8900c00b41e07030407100050203503418201034000c484035152240c8451a0003036030405540003036540d82d005002600e00c0040c00340080c0740c25410500841140109041c282c091000420411201c0520b13040003140d01e144001040c84038041d00495 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 375678318 1250 375677068 375677083
    0x1b0607111b0612010305071a03071418030f010c030501093617070b07031529042402070806071b0b040309081513110112020d050402010e040506031c02 66
    0x105443d400c0004010058006145c0042d81ca8080100a2403802d00094000b030344801c40c0c00354001050009040810740c40e400141c08040c0030b00d4400d821003551030021038908200400c3e0425540c3d15480070f0304034a50940316480c05070003000014403100351a441610500007451300000c11a0289000081a143c50310942040e02c2c2c0d84600350340c80c0184110215101a00310b01c43c1a60501e2500300031541040c020b200b2801c40c188481803284840e8604098440303041142e0046000784142c8402c1c03580039401c4980100090701500440300540052409007460a528400c0c10605650004000307201125001414944c803010307900d0405000d41e4007006428079507034010401400442e0007000d0004040d00f081501056407650000c1b9001c96001304095620300303a064540c00110801400c62201103a08031480c0c940d02001070601c1c4003180840307800f2204aa110741000030807966210140400c560b80a0f20141e14000c04680c203000d24100640002d440d9076038003545921943d0300b001000d00c12130003448040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 375679568 1250 375678318 375678337
    0xe2806051e1908070503150603061203040803070303230f100306090f0210020109170f090d06020c0d08060f040e011116060c0c120e040f021b0607111b06 67
    0x1d4840310a05102810255802c01c20310124100c0c50004003200c0c40340e0241e9220f500380d40284d460009404082c40711941c40a0100c54000040b8468030f0b24150381000103000034000d0300d00550340d440032802c000302240c000402503160700f643d6118480b00c0b0381711048a280c010f46201c410816549440d40c1c440000074880e0b0006044a050811180502440c2c00b800045107000303030356903009a10000c01c201d0803240c6402e0010702d1a802000401d00496055002d01602201041004c0c60310480000062490074100821140c458000820040c4040244070b2220201200d06042c02141403190000d00c030040c4440606004680d54045944490000d40110400442c8004c0c800d64842c1c0303000c40301d02410030180e01961014100480010064861500700b00292380080d94406902102e8000704c840203441101d02e40e120361196980f140c00c81051000f00316a03401803410034a000b5510444c00d05111004000382c040c46202060064160b80100744401410160385600c141035040d540059494000c07445170 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 375680818 1250 375679568 375679627
    0x50f07060908070201140a02030403230f0f0708030f030105010c0f1226160f030902100c0515070203040b0706020f16020a09110711060c0109030e280605 67
    0x1203906001c1c0c2c202c024200e8034000e903101d5000c1c8141c00e240f4542481212424401a8402c101c100041000d8001e2031000441291081a0a54400706564500202c8001c41c80c00354000d00f074011441901042514020a9200003941c1072440390601a081400140300d21414450350070340803410800c3d03035017900342c4460713000d600d00040080600380109000ca040880c590b0f041040d510307013070350001c4280740705105c0c250b0940d280c2c0100c4101401103441c0903280391803600f03040d10364120341c0041e500d02071207042461540e0340b120072509603400c0546c80d0840101030003c00b03445520501c25072650200031102540c40102ca0151355180510b130040003841040c46810301c120340800da0051455030884000b038094001c69801c4200e54941d0012011a000a003004440d20004c10a21000540c0414140391204004000509010480100034290b800c0501d0031000101030701c0120101f07241c4801c240013440c42c4481030740f20f40326082c0302440310241c17603000342401c0c03080100300742030300c2441c80c0c0e000d01141d44440c80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 375682068 1250 375680818 375680831
    0x60311120f121b1b100903050a08090a09111c0b09010312020f010204080d180f1412061302031902060409022505100f05060907030c030b2e02030307020d050f0706 71
    0x1c0c0c013129030401e00480c03003010000200c1411500c10340702e140c156508180a400c1100803940d07010940c0d4840700c00607401150391000043c64400f68400c2d038a40166a002196803589880d40c250309117248028030308041d520708400d0143d681c44030030035141900e504c0306c66048480b94420040c1d24002241c3c2d0355181c15800000d000ca2960307000300d80c241022403281c0f02c9040c91404528a201d008895000f00409092000410040b04400030404c4400000252403040102c10044545040400c2240c02903d000c410012701c03011802c08024509550a1561201c4810f071100d500051aa100b544a00c1e0312181d0081040c1c0710006031602c1e280c000d200c800030060f0890303181d45401900d071500404a400d617140742030030580c14400e031801290300c02d200060504216560b41402940140050a9035808240c3d030703420211140c0c0c80e020340704403550b80348506580e40d81000d5541c4849c00700000c0c0100c02150000c3c020300c000e09400190f0300340c0384440d0741000f0351182d0148450400138014013002400e814102003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 375683318 1250 375682068 375682093
    0x4050405031c0b04060f0504050a05090d0f03060f06081005061e1e04120c0b07080d0203090106180f241203020c0a0b030916030507090f0f060311120f121b 68
    0x6140c0d807c40300c0036681802240d40c0c1c82c40c414200e800480d9105100d40002002c80f034041d2003001c401803400e289007800540d8a403a0901890007602942009012460480034000c1464090000c04010003044901601d0710400038015900ca0784c8405100840602c0403401c102c4c03044501c11040b10403c110301c1039070384407541d4542d1003080b030180507800d40d08800c50310b4020840a00b0142150a0b01c6d8100f04414917010100142000070b40c0018440c0c01c080d507070303690003094001e2442d04101d84d0380380a04000c681d0944207a590301c1152100d10841000300c00c4420810f062080240004085a144c491442c04400540c1016800d20420408803588510140008100c4242c075001075406000860210384048100402c0304603051141d0001420f01d520490003000604000e42284202c00d40c500c0c0042011700c03c0b42c1c3c6040c280c520b03903001220240a289a5030b69581404070100c0e900d4484440144154892040704584645200303110340c5e5446c00010b001745400c043d581c20312040034030002c100c84075018203a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 375684568 1250 375683318 375683339
    0x90b07060908031302130c050f030705090405310c050d17030f100806090a0b090c0d0c060807081302010e120a030c030f090617070207080d08010e0604050405031c0b0406 74
    0x4060480c4205100241c1c0e006c1e02545100304c180300e0907642c40300380c40c00200800040c1540c000030400710411008022103a00c90f02c0300d000b02d40c0100800c0000003850170394841784030640414081d408a143c00484408804980301008102c00c07510192400841c8003003d0900c1c01d040c0d18044040c5015201c000700344501d038100c030684144181c02c2c5105501ea0a41c8a1151310f480f0320054500350744941c0304100c400301284003540c5041d0040c51180803103200922600103d0900c1070800c106488140320128104000754200040300e500c210301307103420f9603030346000d54010500d6545414041d04014080c6841c0c580e83c3c4440181c12000682501100c00142083c40c00400d001d00c0101c04800081410003006100c034058814003041d01c03203e44800e0100c8051031482003480c0c400500040443c8520f030310014525900340310140520041d699080c01700d606000c1840345c0124064100c40c001d51034082084045940842520462003847e40341782c91b4918010802800b400074000074541c05031a1030800101d0a141 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 375685818 1250 375684568 375684601
    0xc0c0f0203210904050705090108060f03160f080d0206071209031701091e050603210f0307090920160309081207020405090114010e071e09050111010b01090b0706090803 74
    0x301d401784071070b503601c200480c0e403400f60040c9240401c40140118a10785410801041c1c2d0030805000c50350040d001c443d0050025150303a00c42940180d25103030902a120b007d004e00001c0c0c01c0c050005000718100030700e004000c005980c00380c88026a0b40d4685804042c45888a504056002e2140b2000c950711024110018059040c00c0c6854400900c5403a44e040c83e5402117a01c81d00c0d0090142100c40b074118100b540071140304080c007004403000c103d0920380d10002c00185000707462942c0d8a5803120f00f4012000100e914200d0380c2c0030303840300e117400364403200c0a903000700ca0000221a007610940c0070203140c150303511003143d0003014141c01940b58180c0038041d004050b203081802100c2c24016034849410303450803104101070314030003061046d0043c0072240303030414a183c00529a00d0401901c800c0d000002c40e81e62080c9441100090038220104845c0d17902240103002c0c402c0c810000c100414004c00060442905841403130540000495a88244407956000242150700300341d00030380d24a40320004c007080740c02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 375687068 1250 375685818 375685837
    0xb1b071e082a0f031f05040212070503030f22090e1501050a0312140a020105010f08030315040509120f0406170c0307201905100c0c0f020321 62
    0x10070101d81c101c0e0340c4002c09054a201450201500003002c0b009010182050590541d010f1280c65601c0c1c01c65001052903004598000000140600302441001078505050020500b241d128000510850740d011007180c100e0345043d0011540c41c54054003a50051100081d8245006240ca0b00040c034044940c0201c03801c1c05095054422196080d014a18800710a020306904011203400a00010300346603075800901c010740c00d040d50001d4000d500e4021070361150240c0070060351140c0040000350300c5000301201030241100994158640348107070040060300c013105181324903141c0d40808c24a4005200d05070b00e645070380c0b805a98600288a8101d4142e20612841c1c00281107029038801d42100000c020707008000031035202c0d01d0f580b10f24800f00c403141411408071900d0000702c014070405403001c009240c0500941b104254030024242051030030880b070035900712035590614031b2950619510450111800303a00545160807a400e500106e442c01014041183c40c010b600e0080f600502400b001400d10400b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 375688318 1250 375687068 375687073
    0x90b04030815031f020310050a0f03170a02030a0c2406140411070f0206090604080a03031a0a03031103120f01090c03020906030708040f05030412020103050a05010b1b071e08 76
    0x36902c14555030700601d50b84100904401e9100e4644a03010b500195044482d417440001d02e035880b6000101d96002c00c1d80400d04a100100d010000c005008407502c1041c03889030720050510780711100183d101d1040f404090104519001c07a0410041c28010302200c42ca90080700e8000b200c02401048002d2219000c3d0030074000c8585100c14141c5464060840400c2c841000d4600342021580c1d0380c1c1040b5001c0c5d0080340d10420134000082c0d40e4640e03102800c001c0c403005e07008210213101405c014086915039800c0c0d001d003110341d8510300c08903140c1c1001541165410300d840c0c4140c00b0115581e03411400b038a52450241c0003080d01b4011144000c03510300d4140e52081c40100308112408905a04910600048640000b420300c0025092400b510142e0b41c4240211000078140c4401d586450541e17015420014551b002c034551402503590611420b0b0f4850740c03040d8100329950400002210fa8020040c100022542090358510400010f00020b40281111400c204003101500002c40034008207010b40c9a051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 375689568 1250 375688318 375688351
    0x9080d11010e0304081509031c02040302131b1b12030c09080601260c0301050a05100e1b0708040f0b030627010303050a0c02030a06050a0b0303040e1603090b040308 72
    0x920000c01244c0c1111246001059201c005210013011048000d010251a000c18016501c40701c1c104044c15440e0a048400183d03954250700c10000c48000b580d108580c128640701c0c14034070003d01203960a00c005280d003000e6502c1c0711800605520b4041c1c4100003001c0d81c1c3c41500b01c101880d056008101d000c0c68a854000035151143e488036503d000c01d201d00440f43c02d414480720065404114088032007051002038032510031075940484d09441c025211001080d598000304042090324440340b801038049581e4141c042c0c2000c03100d0901c030b00802d8240c58030071381000032101c08204800c4116001000c0040890a07500c1c3c0e1038a0500b81c542084400e2030282806908401c8143e1000c44031003041250011101c00300e9003036481c00c43e03068009000020500c48056000c5003d80d5040205001082c85001c000c88c0900d04181030780c069803200c8001d00d00961081c40107000e240380243d003036940605100f20701180008160310440280084d0a8040d102903110360520003850307408048a03110300d02d54001800300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 375690818 1250 375689568 375689591
    0x5060c10050726060a0e070206070f0323060613060c03031109011d03010e0f0303041704050a030807060b04021803061f0614040906081b090f01090b0109080d1101 71
    0xd042c0620b401401c01034000400310210395283c000d15001300010b0300e07450001d41c856003440b001c20803d8441c2c0b005a4408000c0001461b4050250b091210007403409014142041c0c1c0c034465240040f80c2e02c1e201452003440014040d8a652060310600c08038400300044140d900c2c10041c6c07a480401d082940041d04000f00f6880541c0500708a410b0308406030340c0d5920386817000860b152404820184142c0c103548940482001107000c05c6004010103025015580d01c0c18180361004007449180d21240c04c0a005100070810303a61034030b0350b9000300c941100302241d07240181d142600003400c060041e10b620a101003600841106a01540c0001f4542a0100c4034580c0301e00c07294202481c8004450400c07a2111740c1e00f1b010f828400c140c14014022200e6040c0e04080c0c8900c48201528a190420007061b44106800680861100506504410152541078150070403d800310141401400342200d025260f4402d4119648200c2612008264640c01d80d68203401c039030341c02020000d81008a061940c00c00d02c0507880d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 375692068 1250 375690818 375690827
    0x1503030f2706070f23070f0e010e1305030c1902091003020906060a0302070f050604120503060d02040b0d0507180b010e06191704060c0305071d06031005060c100507 72
    0x40000091a0605040d0907030f1355081180458002100c24100c4001c1c062045011041c1800340588808040c0c0b403503604000945032210a5548035059200702e4900403c40e04000c0d4560340e0b045000708481c100c68a90314140b4070325512660034a11701501c10510a021800c8a484010725a00d1003113846d5402c0c1e481d88074181202c0b0615020181d40b1400281c003040461500350028025004681000f60900406485402d1007682251007503030150442800c00040280c01070b03009010058604009046080c0780020030b4200da00100e00038007495a400791180b1542d51a0500400320340d2090407500d105403a20490020301c1c100d81d00400c4031500303044ea007500a600542c0c0b41100381c20060001403c000f0200c10120202030600000d034144003119180011103004581c02034840c41c003c0d4004601c445030050f0007404c40b1070041240041000010000c1020803880407245031407442240c005032661124a40000a1040c0798015a40301c10000f81d058117161002c4bc2e400654081c00e0700411056803035000948 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 375693318 1250 375692068 375692137
    0x9010503010e10020a0c0b0f15120706050d141006090b070807061113080a0312090b07080a110c070e070c21090306090308102108031503030f 62
    0x50f811407800c0304610a80c507030280002103210700e4a500b603010180c03103800c101d60050f500c03144804040d10030091910600c0f0f442c09200b9400352045110000e0501c0d410b40c958226002c2d520030030030000ba0a41d40c189041d0001256486010f0485803241042420103400d101c0e58032030f15022900c01caa0000e84e9228481c2590304160f00400b20780e20b481040e9403040e00818584010f08210b400074080b0152050f00e140c000c40140441034000c002c4040300342405451941415088005681010b48a20002d148504c0300d68000d00541004420340d00e440486030003800e1003d000d45403400010078404038125000034440c1c21103514909105240c0c450000841c0c4022409a0140031203a2500c640da8220880304410984c1c250149880000d481d16a03603004283d495590040d0006028241403004030500e241c04a40108030f080780d03e40d050145601d1038000100007900c0070f030104001000062284280c100b0246522800500b40c076600c000048502c6800c0c0c00242141584400b02e24403141440c2000840b078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 375694568 1250 375693318 375693341
    0x1806010e0103051b0c1018060b060a120207020d050d020703140f0a02010513090f020d0b091504021e0c030703080106050a1e12060f080f061302040506010c0f060b0901050301 76
    0x41038001400101d1218960045407684214440d07020300c003036142014407a01480c134500c2c48a0074100011828858142e030b4409c2c00392413044100308008008650001c660712200c199010000d61079129070b0000030101019090080c0040c000d00980c000c0b803c0c4e02103028400c2d1f9102e11598100d00e5070f2810100e80d01c502501142e5100d501141d00c0f14003541c0510050900d03009640c0724a482035448003841010f070b50548440c280d2035500401e545080608600800e042564141c0d00f00d200361070720340d00049038a2040030410380602c0c2d000642070810740742c0c4822003200d184952070250f070350101c01c0101039481c1c2c00360034150005443d007000420103a1054085071080b00c1c456542c0194605461000401d40e500d6104034014403400180d640c0b01000240541070040c030803c21803030314440c50154454100801d107100b0304400e400c40420050201c440a81c1c68010580640f0005000c0d9a02d00043e81c1e800304511015004440e00800441040b20581284200c4c4000380c428000a0766903400345405c0c0c900b41000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 375695818 1250 375694568 375694591
    0xc0302041a12040209130c0602010b0418020121060308040305030c1e030901030507120513020307080705010c0809010504030218010f151e02070f08060405120301080307030e06091806010e010305 85
    0x104015282c4045e410350460400c1c00d82c1c601e140c240b03039501d120101403580480007503511400c0c1d15078189800d21075082e10b84440b620050380c400272940001c180803900c404111900440200441f1000250350054002e950f01448499680d41c5a091180c1e0b40d8200d1f8252183d248030f450440d048a20002d110f008104540b00d0043d410700030f1820066010f400001d0907e03082140c001501601c0d06608d020b071500852140958060251807030050500344002070f008180706034410601045a83d0303104c3e48096006401c00c0c030560301e5202080049a0303500c929880a9400002c900601c003540000400e42d904032000c40c0804621150b0301e05080e50110300c0c080c0d000b0b002c01c4156041c41c48400c4589002d128810052050700d141d10344604818450701103d070040703002076021408100400c41d0410140c0d03441030382c0d56641c504540c940301807580d9900c07c04c40c00a0030064801544803c075200c0d08269601c2020042254480660050424251400032030340680010090000c0062550092042d9802440e180380c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 375697068 1250 375695818 375695821
    0x1c0b0f04090c12031b0f060f0e070504021b0a08040e07020601150c020a0f0f08060903070c0501120f050c09030634170705091302090a0302010c020d05010c0302041a12 73
    0x910090b8002030f507400341c0c1030245004400030010480c441413000306115000a000043c09810042c00f19107410b000c4140861a000f000d48480c140002c001c0b0450b101150051781d07a01d04180c001424000d01d4205030030611840c2010b10410004001034410783d42c0440210000c2e07500c06a089030380700e00070301c00c1c3c04440c1d45690700c00241c14450043c2000b03c40c0044c1c03445c20250f03a02d20400b0407005203580b0440303008600101c14890756809004964001540e400294140011921040d48000e550b1054605005030ba20040d1b2440c01650007004001200482c2004503190050485080e6489045602e100380680000a039001522110343c91005251520a440c00006c0091903400009014249020301245c4010254524070450040d80b0a1410796149520399080b4814800c40c4c1c84810350040302d00340184103000b00d0f62100c0718550110f07030302403038201e402400d540086412207183c01c502a10550038131130b940030400e4258000703004035190b00b603408100b402030540d0041c41d8011030103035042020320b900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 375698318 1250 375697068 375697079
    0x1202031309090f140303090c01020f030f070c08010507020a0201080a14010e100e1003030801120314030604021c0606082409060117010e091603030210111c0b0f04090c 73
    0x1405585028400c0c40740c040c2000c1c0903152070700040b680314004d00c2e9a91000040207503a00050010710113080c000e00040144031100d02c0c190f0748034051840748026a1001043c80c4c0e06010b00c0d861003400900c0c03800000c02c21410007140c02501e45c41000d00590100e45400081403a1403504e104035043c0350040d014440b41c90b400e150b841640d642d005000700081c20f00c0f280c8042049011110407034007900f480304400014501e146400340c40f20405a110241d41c03650000c01601190300060001d260880c075070303c026601c1d0740d0000040c00078020100c0c5000511107041d4010301c400d200d603010340181c0d03069844420069a602040c10f00d1910081000401d0025615034001e4600303140d6803641c2c00400505006c1c0e00740d000c0c2c81640b254200264407040756030305820184030950a0505c51041e0805014120344100d504640b0007035a0307000c2d1075142000080d5554100c002601100040d250190007541c542d08107000030a10030400b411040414502c65403030582100b202c1c3c40d03c1d202c1e504902e40d000655503841850803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 375699568 1250 375698318 375698321
    0x503030105101b062d0203061c0f03050309120a03050906060901080307020904170313030f050a05040e040f0206041e0504061401121503060914010e060118020c01020d06031202031309 80
    0x441404400c469501741c0e07607858401185000101c0303007020001a00c0303242c03d4003001140700e5808035101002a03030100e85000f081003003c0c90701c070040c1c06040c9075540f6100d481419140c100c840d240c500b816080811000d46140e40364204034099040d0748100ca142e511010200801131000b8815503a16910805c600c1e0b00504002d13400380d501500904400c040c03664400c030400348990007114060440c00d5203040400070150800040d4000080030f1030100c0c101249481c0140052156001c6d0f11601441c1d240060104400010b8035402180d0141000d87c4403640d40034510950115a920100c0e0780340c5c0c600002c03d00c0d0400e0300c50003040b180c103d941e003000448200d005445900064011144c0c41d900c9145500038295642448001144652800101c9440c0350070310000f482400d1010202c96410a9075020f0f030104001a604d0544080300101090346000c02c15600080c494a4138620703c40d4000300e0320703441d076509030740c03100086a01400324201c407503c0032078041782c42c0d10640d40311807440703541140284142c5e20103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 375700818 1250 375699568 375699581
    0x10f1209110303130602150f01090b03010e010e060a06050d051c02030d06060e2b0303050c1b250312050313060504060603140a030e0d0318030503030105101b06 70
    0x140031580000c1c214100842e045a202400d80d07900c501d6200f10410003141c1c10010281002c222801c1180b0504040e4100c4010844c180300f842d45690f107070102d80180c1d507002e5110b540c80b04103c00080121441051a03640c83c1d032822030340820640c1c1f8028001038541440056207820aa01002801d50055640780b1400c0780700360244542c0441c8020300801041105c1842104003a0815448103d0495541c3c000c00c1542c118200703940140300410310840d007080c006600914109545402c010505945c2d141004545000d420b80403c42c10411074403034890701001143c006d408c10b2102d140c2410302030007804160f188904900c401011400c8445002c60312920500c00746410a440710a000102c2605803650302c16110255002d8078110390b00c1c2d60810030001d030368005d070224000c81009055000315075203010b010044c00703414030ac0c0160306e00440a010075100c0c518078100002400d000c45a0151030b81000c0781d0ba50006d004650081d12015892540b2a02800c544d5203400c0780c54240c1880c81f0b90765940d00c1c000c2c021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 375702068 1250 375700818 375700823
    0xc0903080a020304090f021602040e032106090f0f0a0522050312090c0d170403020306070f0e18070e030a08040b090103110306240f0301090c0806010f1209 68
    0x514000100000381030314020251101c003507000b5a19036040c503d0000494941140c00c0645034810030841000382464145010502d40440703000444400b001481c03070851084909401d281452800455070030103090041c01d01500007036501400f550b40b070b8284500f0040742034a154122100c454002410302000340c00c500d60110390750095062a5810040303031715070107001c901c00300c410f0740011602d040074100629407107074001540b41c028240d41e444100421440508202c000c0e00c484020044003232058a45011100211b034041c0844400e0300d80310720020b050300d1500d119100018028800f504891400750b0b0922100d106d003441070105030b25640d400756000e036101117085405009070b202010210304810094030003410025080c5030b03107115000004046034140c40c600303840d0160500500000340c035800e001c100d00d9240c0c000d8020a100341c41002e09414050f0a2440c5030101c000000840e5000552b040248805250b468818260700d82c0001174501282503460314001407950b90004d2848109a041542c0450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 375703318 1250 375702068 375702077
    0x20d030905100503010503011a060a050f091002030909101a2203060510060305013519060f0b150f0c060f0f090f0a0809040e03031302040c11060a0c 65
    0x641c1e80c000304549008141408000c50070100042150341001e0145420101c4005404215141a5000182c0314000c03c0125401c100c0046058a950050361044136160300c00204580034400017001c0c025a01d40c0a00b80300d5004034024804148005100001c0301c0235920303c440702400502c1c107540e69000303581020160091060302300c4504450142840d040c1000b460059001080c680b03042401c045200747d084d03100908261030080108128483c11200d83d10f4600c1105036012034009071800718898840c2e880210510340140802a0010211400c03010581ca108510511240f1a480d0031034003220243c0100070780010103910140c094180007802460300d5a0300c084c005061402c0590b0051500008640340c01000340000d01f4004100447c5064640c402c110b00000c210010b800e12400e81c6079541080010b00f00c400218804040760340c0d40d000540b20140181c00c5a4032803500380801e019842204005a00071441c04040101c000d104404440d0200e508030010521501c1d11644200142440c904410421 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 375704568 1250 375703318 375703337
    0xf0306020711061204020306070f0e0409030c020a171006030f03140f0d020403050c040204060207030308060a3c2714011203110c010e12120c01061d04020d020d03 71
    0xd0743c940d07014100145480c50554420b00d400d2061519280c80a8103042c1070000c23070803079214020307809080030000131420342d0040b45600051405840041c00d80c1c0000f940002d8082c4003050740ca98143c140d07000c14000601303d40108541010b100c088406a000107403010542d411444040ba020703944105100d50400d03949498a40c0007080010b00e40c11a0603105002600045c0c2041444000c00a0302034480341201e0840c601813034888003039074840745444010103000c14031000030829503410020b031005040120500c0701d00d82900e00741d0321400f80c540400418642d13402c010101d1740800c0d0141c13001a182190000740240c0c2005d0102c18200e0f80400c01e0500198844001c0c0d0103504109045500034900100d06801c03241c2c5c0707490090f20010340f0601820956010f03040e1200160b0b800121403030a644107444d03103400101d50103000c6040004480101c0c40c10075000407980140075055001508846903407616151320800d001407004031110644000c1d5015429009800151400c12462443c140c4a4100700401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 375705818 1250 375704568 375704603
    0x3060a080708240c031b0c0106062115060c020f1503100b0310060e061605030a110f070303030e24060a0501030b28030804030f1202070f03060207 64
    0x70401581c0002c0d0780340e0000040c12010342140202032611143d010203200084c58401042042400000c02c0c40394401d446040c4100c000807920704881c1060b4445000b405195120074000d090961040070b160b001c160407007620041c0b28628030400112800340065040a6071600d030040f181c611184005036408282c122407010603a0381d201000f120310003036006468481c50086c951b961540182c0d407003020501410010040750b04508122141030380c0e00307030401031401f04041020842d140540c0c9000251f00000842104c240400000603240c046410b540b001110340682038215194195480012180c5d4440c10302031002034060340001c07607880001d030100c4200780b40c07040750744a440c00c10415040e0046a503605000040c1462040342002d03142c2820148848040c078804104a07030070260082111462045d01e0341c46001c1c3e9001804000d54004c0d1029840c1ea0b00e0f030820543c4040700c0402181e4940050110340741d13042c00803916400f20390b145a505900e8500e1b40c1c03034480c0a0f50043d60700320b59120926243d04070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 375707068 1250 375705818 375705823
    0x60806160309120e060412060b01090501020a030e0d0602070203010c111c020c0918070f06170603030901121107050f07080a0506042006030702030912030414040e010b210d080c0f03060a08 82
    0x6001e1080801c9c24450940003500031511038118504540007104080003194000121924480701954170a2509082c0e08005001340100940254036500f0b0101d80795955074440c140c4001841c40c01c7c113903090000842d4501c1c40105000486a000da040114041d02030701d0450b1b86654000856460040c0d110301c180322290074640740b86c108050840700302c0800c2c805950b0090f142340f80c0d011400354280c03880c02c0007000a6560b00450384898100000c103000f00019903801d402491407013022840342501d69850345441c0382c03034070042c1c0303a01096407151281c0090900000543d0180b8103421a000d4542c07910796855201d107800f2000141e8003002c04003100681c4949440b001144641503d41c051030f190b51100003044034540e080d00340041160b205020900c001c014142540000300d608840016082040c1d4801502500040443c5903008002000300c0003029030004040c01d421180d8815140c0c182d810345010303540202c05403070b062582c0405102c02054072580c2d034021604040002c1c005074500d5924031000b417 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 375708318 1250 375707068 375707099
    0x30b12070501140c1c140703050906090f1521070c080d1503030c0b100605160524101505030a2d06080d0804020612040206040306060806160309120e0604 67
    0x117268210f100e1aa00740d56500408503088650300f460014503098194400602d50f024030549584141c10000d50700b0344a030b0f14501c08a00d00340c4080c00100d0003468040400c1d40c00d400c50805800640421f860480f40502c500401c280700709040e8681c11340002d0b0035107c80701c49401080c100560555100003031440c0d0700d0f00545c1900103520941c0c1e1902c9880c481e1410007204c54000d4040091500c2e0500103000880c0c025041c2e030b00e61600d10f151403902c05800c0c1881840d0600081011601e0500741c00348801c02c80c10080b859114006a008102c00d02d969103041e05001c985c4908a100010030034004250140300c3c54001c05401c4001841c4c0c00d420300c42289803800c00c5003051584000181c1d5074102000148028400c01c0600f088a0500a0380c80c82d198000c121148038101d101f40c1d900044800107011560f60701c040e24081c5410013810042180c89000f055511007080c6d0b00f15100d49210084004182d00c01d014034502d46a005074005a07101100a040d07400d10100021075a0101d001d10020070b03081c9000b0b9155 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 375709568 1250 375708318 375708343
    0x1204030c0516061106070f1103070602040f170a050601060e1203030a0c080a090b0a0e01270b01050d2609060c1507051201170a02120d030b12070501140c 67
    0x3441d06602e0b04030068207400811032075141da17401103c00c0002540d04503982d8031890040d4100340500500b07448100f4114400c2e802c000302141d2001c00c0100b200e0030164601805d031014820004210400b000300b643d17aa19241400a0045e07014400620900e407103400450050b40010701a002e00e82070114100d81190070807111580d44507030720a80ea941841d4044007280c0c02c52111a0104501405034907085031280f4001c21400c0020340f43c0d00b0000e0a10303425030006800208040403900000e86103a0f401400705004c0d002035503000c40281c000f0805242c0554440320503540010362450a600c503509400c05030385504907100d10800288403510450711001c00a0801a101e2009030049540701c1c58101003014000d0200b808010b02440011000490007070054152031601e0b81641c110301003240c0552070b1000d0407a00941260f0850072001b0312040000751004c0c4000703036803000e0007048030342000c2c4620440700c0142d420059005002c200415401000103c8405110106180c034041c0c54130482032400074030300e090 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 375710818 1250 375709568 375709603
    0x423071d010308030114061308061b090a0b160b16170f01031511031e15090c13030203070e18010b0f06130914060112090c0e13050d120f111204030c05 66
    0x200150340a0103056000b00c0050b0000060413303010001282c4115558080d50f245003400042506800007605218040c0039400302d102d015600c0c210941c000c07500d00d50141100450594017402ea05000410220b510840d6148403007010741c1c3c07031a20b0b40c040600c0480c40701c5a1443c2ea500301c0390f2840c00d8910040d8404c66201d1014400100030341240000302800616101a50b2030a2140b0680c40da01c9810341d03508540b1445e82d19480d4580441400703075882c01640000d50520690200080e040c041c1c908051080440001c1c141c1c00c0070000062a081c0c4003400e41c0c055111a44101c0306003545440000340041045045040c4c811585901c1c1581c1140c0c000754000070408803140400c4103039a444011061900d084500034030460450b0b0303403540140743c65801840707250040c503400944000d05042c0c0840b0381c25009401c07902c4043d042c0030007070705420344045500142c50a01006400301e045502800390074058207054240340020b108002583c4d0314000d0070803410028401141004904100001e0ba0105500000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 375712068 1250 375710818 375710821
    0xf06250c0f0c241b0f0c09050a14060d032f03030a1a03031303080d1e0501060806150403060b03011b0e040f05040503030703050423071d01030803011406130806 70
    0x2ca070f581e1454180080340c00c003c2e8403105815510019445000d809502885940355a00140b038980c4c80300d407031500045100f40c81c140401440c0c0d0700b950803440c0780118400c2e0451042d02d4103c10701280b202554400b80104004a43d2047d0700403200d0324aa0301340011017080c40079020b0403844079003150b00c1036331520003558032000f1525520281d00052178000d50110003c518040d0000440541c81d1550b10002c0c1c145480828940c0344050309400486c2580505103840002c2d11440914100a01080c0505c000080e1070344006023007800d000001e01c001000032144181406c0c0780d40d46010141c4107102c0a6034042d500c620341a210078040e40c08000010485403030b02c0100c404240c00780402c8030034001c3d844040e24100402e0002194000c0201c94000ea150319011519079924140460740e0040ca420038100c0c215001d412000c2e108020076490207540941c0040000400301ca02110341c00e1801780009440014100b00400c00c040c1240003804802c04003801e0181003603860802d0b500519a603034040445a00041c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 375713318 1250 375712068 375712109
    0xb040311070f05100314010b0f0405040203070c0501060e071d0411041d150f040c09170f06010803092803080d02090f03010e0606040b04021207020f06250c0f0c 70
    0x8034802d444d002a24007008001e01649040110740018440c0c9048040000740700c3e000e40b82c050046034040c10005d0410343d900c0c1050741c1c009010310a40c040994142d468514040340b042c0380307074501c0c50186041c0c1da24881850407080e075500710402c00400c1d0315842551908038070051004400904010107440008181c0810400b0402084e100300808021031441e01440401242e1303600e00e11203065800c00d941c001070600700315a09a0710f240c2290000c43e900c20340d16591b5800340400003541142049500240c5a00741d07640d101142d5079000d84054180e000c402ca90070a2000c854461006a80780b0110700c16541c0144e0703d8440030201e50101c7d4900ca0740780c0d000200700c61241045500a601907100b80c008200d410034119090703454140190000307110340e407142900401c44da10b68055030045c11007469a008581440000a9a104420f42c0e982e2203a008290025408280c407446190780c803900c030011001002e103426002c40e80d00582000480d240402c201100740811503101c0d030400a0400304440031500154031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 375714568 1250 375713318 375713329
    0x30e0306090d0c030804081614010c09050a0b0c03040b0a050307090e070903120903080c0102090f060f030a09150903020c030601150203120907050d06020306010e100c0b040311070f05 80
    0x207101600a0380072103070000c1c07401d0380052030904868240c03509800c2602e035442c0c100d41c24411010030b11004a0074007441c0080c0000e019180c00311006075030003080b07001c111001c02e03210718000384500f0f680500140020000c04030340100400d81c3d4500c91054034a46a220b005d0b00d80b00d40c000c0520f4800041d8007204102003190020160005044011102115441c01500003000221140002800c0465190030b083c4075074001d010741d00146600c551486d8841d6144040c16000303400c409405440b8035500a600101410404100e450a0700d44001040c07a5940307440d480c2c000b03400051000c480c440402c07070300307030100004034441c00310b600d0300c03075805010440282010146410810303040700c40140f40000e10805a590000111050401b030481d410010b941c0d0020346508184003540196001100002039804114165004505c9008241c0300c0603030140d40c0009200e001e181884140d00402c007946250008200b11041080e4050b10902c1c2008084079003031151418415940e0200d1134003c010341c810b05c65803400f03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 375715818 1250 375714568 375714571
    0x60204031e050d09050913060e030a0206041e02031c052109010509011b0c02121606030516080c030a200a0806060316050a050f1201030501140411040209180103030e0306 74
    0x1103107010103880d81080005030b440030780917006207d164403940701401008200d4000c0e054544070784090343d0300e41e003a90324007079190b050840c0c1c00c581174003d550117907050038100b902043c413407600a030042a00c410301600700c03180140318188010500c01c0500401e544902580b480311112a88040d0003845070401d210901c0c2924005030482480d40d0608400d01c22908400c1c0310b0302030918280c035110050f4a041d00108507940001c0d000507005000d80e40380c00c0f450b81d10180000c02224056541001a9900c004c40500f15850301884400040c0390903011030078110450020b03507045894200c0004420004000b40c949400724503074104034070000810850031483e00040240e82c002c4003618014a18608048a038890030540390112060020104000010620460070740300004980c5245a55400d0b581078807005148091204079010b43c02c01586400c00d501401b01c1c00d02807903004212200f00030b402020803000c2d410229046400c0b04c0b941d6880080310500c0c5044078000c5019440301ca485010450901d41001c40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 375717068 1250 375715818 375715843
    0xc030d0c050c090c3004060204050a08150c03190e0c0109060306030f060504082106120a12050901261509010303080a0902010905041a0108220f060204031e05 69
    0x1070312001c1040d134060030401c64010318150107034004105000303600741413804804e16039801016880d6080000b0402180d00074010340e14112100c01e60713030740c0c3d5550703a95441b070318140301c6007801c0441c001040741c1101d054059600201d425050481c602d098000340421603079100c03805c2e85c2a07440b4074001809940c00c829000050711840c03805014940c2907854034840040c0210000742826a92800101440f0faa50166000540c509480b4001002c250307501c0c0030a002c044ea0840d100d0341c64403012241d01103001a83c0e0301096030042c50141d000020f0b81051f540b03a0880d0121606010701c4508103d948130080080c034061810030000c00d80a810211201040760000c4003d40d4091a0041c00501c0072903007240b0401d5100400c0b000109c4c021b03003113100480e90442c0c6544190740203400c043c42610a2408007140307048e81002a621181c0c0f07583d0300d52201c5010140c1c1c600010b120801c100700b54001c148100840451140580000751501d5038960369440007481201e650881022501e0011041100900c90144a1017 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 375718318 1250 375717068 375717079
    0x2d1b0a120b06180f061b0307030e010e0d02040e072c0a02040302010c060b0d060603111305060d0807060219050d06140a050d0203010b060d0b040608010507020307080c0c030d0c050c 79
    0x48100c03002e0340b1501429245900c1030014a508100561700e01c000c8522000c0d00b00f0a6100c0d0310385004900b59243c010354021008a840c20083c1e24030395100d048540001980103010f10400318058082c0320040400c1081c10741e90b405100000315103800c1c0e40e14545006520551041c1c400c4050140c1c2565140b0080c10702216280100170400240c0e80c001d0354451610f17000680002c031a1203a10029013a031000f03c1000380324504004000003030080000c40c43e25100019610301218800e42d501031001c4134822101d05a01083c69900c810202d8510b601806a1521030720005142c88520400221100c0030348156a00043c00002c0c00180c803451402440010302d821410000c900602c4400214040540d005a9000e00c1d46614800107655007500a02500b160107081999140d0603525600068203070140d40307034025410300c24000b07100b00c2d05124440c4152050b41c040c40c10901e031903a4003140f50307210441c203102c10b20a1290440030f070fa0f814840f0f9000f490f0903480d40c101b04817040c5402800c5c072104c40c000d82e06c60ba = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 375719424 1106 375718318 375718327
    0x90f030819030e06070c02121005071b080306010e0607020d082101030c03020603190c0216081605040b18011d2d1b0a120b06 55
    0x8100070000e01d03103065041582641034030409140c0b402d2903806500000d5086210795601106d0070b10040c03141803003c1502040b20f1504900c0701060303802c5a48c0301c080c0100b003a08200700d1134131028452a941c2509402da1038142c1c1c3c50100401c03c1d81800054400790181e40d491104641d203066004016603103a03005403e00c0d19050300b2007205440d00400382c04034480450025070b0040c1c102c0327900019508981d415036090104e15040681001010360803881584104001801100012103041e030046c03403116031000810310410340e44d5001c0d0007150083c0c81d82040404890044005950044c1c4010400e118100d002c941300c220000c143c40f820000150011410744000c0c6900021900703590328081903034503085842c00c00703520100c2043c40c0e030102d821a1019a4a0500b0007103034030001c041d032055440406860744030880e0b0301403000c0c00300003140480071403c1c694440c8201c5064074802e40c1c00320f082 = true := by decide +kernel

theorem cover : BRFrame.Cov 375539568 375719424 := by
  have h0 := BRFrame.cov_init 375539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 375539568 ≤ n) (h2 : n < 375719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
