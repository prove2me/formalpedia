-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5373
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:39:36.122506+00:00
-- url     : https://prove2.me/submissions/0420bc6f-513b-4aad-b9e0-5b747b687fc4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 966187050 ≤ n < 966366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 966188300 1250 966187050 966187063
    0xc030516091a011b020d05210304080f1c020d0b040609020306010203040e130b2d010506160c031712070801050d060b040b0a0f090c02060919020105211b0a02 69
    0x202131804039801c1880c0b0520700314020104138002d4101c00b601c1c96a0042c40030100c0d043d2050b45c0c07110340310707a5440a01c00000340c03640400e0b100504640e03002c0102d1211900c03080010040a0130342081241021191107001d012a04a0034400c40c0c46a01c80342c2030b035554581403140c44040c0c030140c9011403c42c182140000e50701d016902941e141b1440d01070100346034501500c41c6408240d800b202891091a01151400921082b2124280c0001e540351040c1d281a1100c1c01c0c0b5410b0b1680603100b1800c0c030f00200ca00c00f01c0c2007040b1005841c0b407460030710003002103080e16144201d012107100045580c3d001800821104520041a00d01005003100040c000360b40c603541000140c1c0d4120901103070418444000800400ca01c0c5038a644c094040900060303031901d00541d0360115074900320108070040302c0700c0081c4e0f02c0b404111080318917a0811008d104102c030642058441d141e0040c50040d082c17004801e0942c0303440400245513589480c0800c10040e004a40d1502407240c2c0182250b128200110104041d50b107a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 966189550 1250 966188300 966188351
    0x80c160f0e0c071b0302090606190e120102040b03010303180305030307140d14090c040902010504051314010b04030b0a0212150418080301242304030c03051609 70
    0x82081d001c0350740002107009a840c02a00501d1403c0d6610342000c1e44042c0700c02030301c400c07406240d0b40400184180340405c2a6105e000f10321402841e4201c1d0311b5811110003000301c0040e944010514101c22056a007403001d08050300070006815a40e5045003030140c0140341c09a0807401403030303c2002c00c2c4000b80d000300c00d6a40001c0304d07080c2011071095134240049207000e1501500d4044d464040d01c51102400006894040e540c40720613648000207031403c0c4410b841402e100a40491010082005141404024010540c42c044030004d0505400703081840d5400081e8800c510b07000c8003107014014010300000480e00a040c15500b140741c100e580001c4810100010001442c030594644894259103031600100701c10886d01001e80d851050602d05900207400a0180d000b220b40314490070300c0c178031204a104a0028550b40c840c0c000b20104c030141c4040410883c404440c06150504c400000200c0d81c42c940030141d0701c01c50182c0320100740a000b4132030b240b00d103a000c58200340c202103940d201030341005426100303007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 966190800 1250 966189550 966189569
    0x70e04020a0b1c0e0109020402030f15042310030f0f0507060801140103020c10050709140a06050712020f06040f050c100e12160e0105030d020f0709050601110a080c160f 74
    0x31a00d201c546401000190710188d0464000010003140850f40d044c2148208610246851751030310160a000c119230f10202d0b4103035001d142c004229a4540c1d84c0e001c190340413240000c40d08085407070303a581520218801d8030031942c0f5021829140c080000c1405030801402091070302d00c840d98540201c80305001040c0b0241c506055000900f00340d806818826104141d0300c451003070010342045640105181154429240300800e0151010313003a2034114a2102107806a544582c02c1441c15114070113088048620101580724200c00859500028480f1034450360180c1d040d441d40074201e00b00300e401d20035039010b0944036a044000580c0225009809400070f11410f603010b00402c540300041c18508400c04e0600c50310241414000590640320381082c0717058840a03026103040351607486050b603644c0d40030303d0085082d410078030f030900440f14280e00c20750b800001450070b03611112503900e1003414820741060944030144006030803d803c4108022910b8142c0b0285001c080d22403900929801a840700c0c09040d040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 966192050 1250 966190800 966190811
    0xf1914120c010e090c1e04050301060f030507030303051305011e0e0c09011701140c0d0606020303041e08040308030709050109080705181003020a06051305010908060621070e04020a0b1c 81
    0x44441038415030b2003a108840d52040d8111081b11803403a960000d12522388a9820b1030408a03801070500c0c6484110b980c03040042110710305640d001d80141100401c00e4840302c0002e250040410401d000d02681165060070340c810300b44c82080060140e0348200d60100d0703581e003c1501d00310640c592681090446502d910f4818114103c1e00b4454050300007203a2810404418000307200240309260000d0146941000c400c0048035960350040e0303201d000444000d40380654064402c800d403264003600c0044a417062142518040d101d68270a13500d90802c1d24000005110150280400c1d40c1190104c0040d0160780020200c15180030006040c070052141c0000c1d004004201007a40f0b82c5124410f5000303907a00034803401c031a54031640c0003040d80d00030304070700300c04200c0500700088c40394080c40c1080e068404032406400181c1c0e0785001d0020050301c407584020341415030710110385030850500121001d40703000da40030b1040b4201801040500039841e00680c0d040c0100308982d22210020a01c0030080ca0341140010a2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 966193300 1250 966192050 966192061
    0x815010c0f08130305061015020601090207050c040603111e0d0f06062615070e040209220b0915010f0c110a09021c1a0f1914120c010e09 60
    0x14020f407070b0345409043d405a4003104020022464a2044012101c0705020550b00d26543e9074507440c400422001d82c004100610000390340750010b12803d40160200c031a200c50440100e4203c50181e4070581d00b0800c01080303680c0d2417500001030340c12080c0c6141038440085000d00081c00325200000014111014100e084041003e5504018002c260104508450000c12007a02101540100351400f007030140112421b5803070b030000661400b0300007039640c45102007004001e000007940714960390340d8031503014024031080c00711402487c03e1f422302e60701001c207031010740c1003c0c03100c0c3d00700160011020101d2060a906242d900681e40114a466440d0035900c2c0402d90070094031209141070171a8101c4103940011a20741d109400920b40700b1101403000281e900100d239080c044546019540482e1168900d0b1400b0030300e0200d240350240c080041003072001011f4603204c2140d120440c1e02c1b1754400c01b006a030011440c50128040c0290034a0a0702401c0c03c1140000003c060751110006a03110b00e110602141 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 966194550 1250 966193300 966193313
    0xc0510090f1410080402030c010c11060c0102130f06050702060d0f060612060603050f0f0612010908090a0b07020d03080603120c0706180f15030e0a1b0602011401140103111204030815010c0f 83
    0xd2118000c1c10300782d6103c2c0f180cdc5202d4040e40c001e0302160041c016145001440c19001e030240012a4240d80d11b00c0d0526001c0da0030410191b0184220825883d183c1d100e9150314042403040304c00810703180c0c650040c1040038003424002e45210303600102c149031502c4104140d84820004566110703800040305003da41e1210f0006008600240b1005040e600c0c14124004024070036002b4041500210751314100706540351410710712842400307002500200c003a20381d030001030300034000c241d0800b000505458003064084c44018058028040250a03948584400c01c0140c0e00b00301d4006003a038440304407040d501d09129120740b00031007500c10300d80028600b00d099150341e84258480110842c4280c20ba403813440309810504050030b00c42c1d07141c07402c0303042ca890001485801442a00b02c105096000d01009a203001e5442e507042e00041d06e100c0c140340e11010020504581ca4004000f820311200b00b441c081d00349400c00400030040282440b41c403030a04052140640c0e0460305030b040071a40084001d181000b03130725040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 966195800 1250 966194550 966194573
    0x180c020a08070c0f170c01030c0306050310020d0b040603080403030c0c05180f0906070e011b0f030f030609020a08060f0f09011205010b0d0c0510090f1410080402030c010c 75
    0x25248490104021040018040c031500c00c030741d035134505080134030307110403440c0e0940c507040c440b950383c6511642d41400c0c0b41d4000e800c40f1015644e50304000803541e0b940d0300402e0902c076112155000719036000910135000900303481010902002590b0402202e030031a6155000ca201e64003000d401d002014190324100300020002c0400f80201a0092070117010b40224000500c1c401d41d201ca0386a40d503100007400f00b00d400202c0501c1a0304681d02d44884101c144015625100c007d4940801742d1180f942060228140100c4010041d1080e910740e036040215140c024129021070b04421011401001800340259000034000c0d08a0070445a1100c1070740840001030703c440b1410002c036081401c400001075511805104d10035800d010324000e10010004a0070032900310424a4010300134102103505110905000944018481c02c0b800c0100d0706540380e0318601c0241c402d951002d0f0829868289560b100d0030300000b505234220381070401c0901420a64002600c600c3c594810034100081403081109000743c0c43d00c1c1c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 966197050 1250 966195800 966195803
    0x103150b060a09090e0d0e040b0a15052205030d03020a030f060b37050c0a06090f0c0803030f06100c060f05040318060507030c020f120c120304180c020a 67
    0x142da488034a05005000009284181d5400303d141c0501702a02080c04109050716041d070396540d01000540074200401041c2108140350400c030311020220b4410400c50000c140944c2689400751036100b031000707101090429454001d1070030420f03030301001651000580c0100780c105a040158407242e0400c0100c0052129030302c039124403410204c0004002401c01c000b08406109441100e07d8081c5804070103500140c00516101041700d94810000c1a610407000750205c03c080313000b550540d0020352a010252084610242c4158100c1002d01d8100561074000100600750000507600314585511010401100204030700c1c0107462064250104500c078030071410107940e2111040241200125010002b020200c1c0d04030041806514142440850721709250121452030362280c2c40c02030305541c211508550940201c5e0000015041070b40180d0780c100380040301c01006001030007841c902c0c104000c0d02603111a040c0181da00100f1043c0409000360682210340089440081030407840204228541300d4207480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 966198300 1250 966197050 966197059
    0x1060f03030f031a09040b040c090209030319200102030109050112080a0e120d11070501141603090306090501020307030f0e12280c030906030606080114030c0901120b09010902090103150b 82
    0x10007003040b47c801c4000340564080d019441d140c0b900c0d506007a04921034070400642c90382c028003c5e28402000203094110402940c500740050524403107000969143e1024140f003d0703500800140140101d40c410140100384c4407180390074401645e01d82244a01c00c09204008001c0741403180d0250740c41d1180030000784025038013141c0d0b409220380b600134031080881d01d0950443c01514800100d5620a8814002404941c00d490b4500540780c0000540f246000d2011414040d040d800003021a6081c40f038001d1071401000056030700c0c5004900101201c02114407030441500d8101100a1031000040b040420102c43d180d440e907507184d400190701001c1078040807c60000b01e40400b03200541d440040180518429181c1c1c64205884420503010f98841d0b0040000003488640108000440d01610b2420544054142c41d00710031300a001c0303003a01750f09030491405002e064200e00700704620401d0381d651002c000b0000b0800a14107178001034146d807040c40094071388000c03c100102021480e61103c001108000d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 966199550 1250 966198300 966198319
    0x300807061e060305060603070b0a21020406031a04110d0c0e0904030215070f0806010f0314040b1e01080c0f0315131505090a080f0c06011701060f03030f031a 69
    0x1c0509019100500040700d450182102107031003420005010380584285e20210307130424654610850b80110f64502e1203640303014407842006000c02620082020b0b0039a99001720f00100b90300500d44101d60b4401e1010701540c0741061048103c034224041e00c88141e180e07940800c541c0e45094048030503803000d0700c1c400c3c0e0240c0c0700c1080c00205900040c03149031481c02c10008030741070b603140402a20030045514403200410f14003000680e45603ca01c0407400d10703101e0350600043c05006040b0382e620529040b101158000400002c1c0070704118441c0d000f034040c011700c0c1c10b10070482d8100310f0a144c4581000882c1e81c001c900e160460300203541e0034000114440f040a00051a41c5440081c1402c0f148110100341c0d00b000314000c2c00b01e07503007200d401094407504190000f0703c411409941c0c1c8016950224001c0400854240113a169844090008900800801c4d065114002c80c2d44a114212410b0390b000c801016240b24003080020382290794141080c900c1d042c0043c00355081082608192844200160301070441c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 966200800 1250 966199550 966199601
    0x10090c0c0c08070302030d0f050d090312021209070b04030201090911090904060917031e0415060f080c030d080106030b19060c050f1f11091930080706 66
    0x210750b42124000c034200c80d007c406030b100588806c11102601c02c000307041001000d20120b003940106000c244640380102c089003907070007030f13000700e0f04000034121104c1c11800611104180c204103d20141460080e0a40b030b00e407650f40083c003001c241c0e109074081c094884400340c035142085000d0350319064002e000c1400320701d041d140c610020420040c00b1100e0000702190300d106000e4407400d4921542c2c006250b072100e083c1c01d03c94010143d00051040310800c40c1c011220200c200baa00803000144244913000c600e160170402c00d10304000c44100a6030003a4001141403600d980d03c07070401411100941400030340000080701040d0b40145a01c2c07210fa40714030081d0005129584982101003d500a0058903c590326882d059600c90b1101100c0d94203501c581c0c0000e0b0341c04070084c0d11140196511042d0146080c2217032010030040400c0b101034803148041400208052814161128513580030700c00c400d003280a0b2140c0a03420074000c81c0c030103030400102080315002c12046034030104441174100c40352003002090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 966202050 1250 966200800 966200803
    0xa20031c091e050d091a0714070807080c040c140c1219030f0c0207060e0a05100807270909080903011d101107020105070c12081e0310090c0c0c08 64
    0x203044210f07560720410b101445030510800b101e17010345028030001903d0030034588400e04241c0114105450000c0001511172080720104400c000805011000d4402c03140703490016406c00c00c040303061030300490410800c1c89071654000103840080d203001d04150f86039014184203c3c9401c1c810000c0c2e90030584000781d9403600950140030074686c54000d603000e00211400000c14001e4505500d65940568003005d82840100c1c000c1070b0042c44c0d100c2c054210841d81c0c1ea14000202c0b1204116168000f0510314018024840d40c040c840c0d8288925a400942139005035008190751000c00d4451021400c5d6035605c0308007009600e00850345010740050003031251201e42e50100c14055041461401c0038032596200b402c0342d0000e40074480c0410610341c0c0c0300c3c5c1017500310340040d52550720400c812200140621004640119041c054249003405a10f10740d8413038452800b4a004007070791000d140240e913002d00130818000c2130000290240e880e154401704003400b43d10025600c14200d404000e00840a074600131580550 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 966203300 1250 966202050 966202103
    0x170703060e0a1802090c070803040c06030e0a0b28050a15090c020c040b0a0b0301060c2003061812070819050a091203021905030a20031c09 61
    0x380c0d0051201d40d80342c21085000300c80d00e0340c0000d550380140c100d0040242c5881c2880e541d020301d02600c114640b100c50303512003400b81d100b241c013118a50000caa040c0302c1e441d4148914900e80c3c05c004000d061503104d9841710101c0d0400206022045018a00c0118072408000c03030721a02c1000c504001d101d81e080400c41d0002809003a00e45180d2001804c400144440050003000b8160311260080c02b881c0d9904028007015101207c10250820540140000c1610014008500a09041d5a141c1e007913003140c0303418501e0001c41030030201240c0c10f0340d81a2119940c00f02360700360003100001048111420801119080c0340201004505283c004074046082c01050300007004c201c809034007440c2c41c110440c0800e440074010101e03018000b5100010034000c054055140401c0c4500900407526101a2013010b628803a888010846281d0008656280e507603810104582c3c42848500104080b14150b419042c1d0328001da020008450784032100c4560410784640c003500360260004518480410340c010030446240 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 966204550 1250 966203300 966203309
    0x70605011706060123030604090b04031205090606060909060a2c100b0f0d06050901180e06190902040e030c03040f0b090d17160606050411070809090717070306 70
    0x2400000748aa61285c00e81040103000410352000f40088016980025040201580d402a0b0748242a10121310000aa58440d40c4240d443c440007032000100034099a0014240c4100c950181090001541c1d45900740c541048080e202400c4903520b00d0005400043c4da6400028495100004046543c80c81d640d605000c060162503032445448031200740010100c248191803a100c011301c002d00c001d0a184004000d903100b03402000c50416212400244180c80030b0f8002d0300510742ca40c034903960122280c059030b0141d41c3c03010301800340e41c6070000807209102502c41424400d80d0b40c0d000c84070b0441d99107501408058050408980d191001c03c100c865903903200703001d1f240c4e0fa100c0c065030000c0d20f605031404540440001038150340c4044181c2d618551070020000c03203010450380501085045100400072582c4880c06041c000c00c0c01860300d01400211075541d019481d001208200360404102c2040403190708402c192000701180d560f80740101c0b48200d1042148544414117014000582d505421401c1070780c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 966205800 1250 966204550 966204553
    0x60b0403030804031b3c08030726010614070302100f020d02041205070503060103080d1a0d111215130c0b0c0703051c020d03050a11120901050c0328020706050117 71
    0x706c0c500100c62140c0c001001c50b884401104009400024008901541d0495214100f064444440c8040e240b02c40352844003090104400000401c102d5500c03114403909503480384a800e00d0144a80c400030740360320704421443d01d8181c43c2da00490f08401e9650498100a903009000c545590f1581c101c0701c02c18402c0f90007940c06101d81c0c0001b1510b4036020501031304882c2c4c0107040a00c2d007014251108050910420703e04000141011040c486440c2d8460101c0e00700d11445110820708082c008002a41c406d11031007040303940c844003070814624010361400e0b070400000079040e80040064904400c2c1010550041070341c00310007187c0c9041d596000540042a40e21500c160740d143e2401844031a980c40c0120f031b81d41d0060380604221070406c0d0207940002d07000701d01040f01050b00c110136442414035520103a002c0c80b075036644600300004082c080c464503403c0f07880c400d40c0c2c0b851030038290105106040d08a04d03c280c40400d02901441804695040700c070000d500c1902844150f965903501c1807441c1c24000940c016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 966207050 1250 966205800 966205853
    0x30105150301060f0f12060b030f0c030105060d0e100c09090e12030f100f0f061b050a02120102130b04090b040b060a030e0708030c1f060b0403030804031b 68
    0xd62102805880c143c074a10b603202070380d14400705002c440a0380b2004101050041403510300e09200000e00416014045402405640b4204008080c0740c00c0320051011401c00010300040c030081c2e0310202110603020300f0040c0403c00ba250414500e09109a501c1c1502c90985441a807030241c0f80c00c903081000302c5031144801c210703409041c5d6a4a0304c480340c940d1707a40c009250400c00561140e800012080d0800c0c00c2c0d141c1402c1e1a916400d560200007400d130003a054014202100304019588031203010071810600301c00481001c1640c0d81d45594003228170340240309030269135035899008402d50503540e03551100c40c14803011540d03c060b0300c80c07a0361050082442160424460802505080c0140c04113100c1c00f504161815924500c1200141400a115410341c001e04a0000d507441041003d0184020810050002c91101c000c1e05000f20303054000d52400981000707820000b0068103016101100d4050a0a10256556140071107800d04003012048020301d1000e1600b051080c070001a100070b002042043d9075 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 966208300 1250 966207050 966207079
    0x60612060302031b01440f0a090f02030604140c0f060a27061706010e01090311010201020702060f0d1d07061206080d020d08010605040e0a0e0f07080a0c09050c030601140d020c03030105 81
    0x40e04003044030190400403c0d0b40210b03004040542c00b510085005082b100703c0300296500080c00c003081a40c0655269501404400d12050244818442d880048460404400c8031802042c200d00031400000300380f054030001c00c90240c50301d80d42c400c1020065140e107089076840c3c0c0340260103407094aa5100d0004200000201c16501078810a00201c2d0b0503122004d40914503546e0003285400c0101e405d0455400780f0a090068896002500c0d0751004140040c1d158503c62400c4001c40344441a41c10f2031440c07004052541d80e1000c2a41420745000d441c1c060761821501c40310740c01824440d8400313291352181c08520584181d000c81c10b56501031a690342d100d92a44e0300c120442c0c0601490292240041c40039000c94905480d540c0004007915000041d01c40c5008480107860400045502c19401c6401542511081003140180c420280071010020852420450303004000350000410481c1808100045072041c04003040948002440c4200250f5681e600c09108a449030001c1c07043e6401200c10319034206 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 966209550 1250 966208300 966208427
    0x50307030b09011a010e130615030506040c02030412060903180602010c030f0b0f010c1104020f030417070807060b0112060801060f0b12060d03050d020d060612060302031b01 76
    0x14030005051b51822094401d1604005406000c80c4003103444583d00e01d000250312480c19a102c45c1c0418a032400501e038a4282c0c184008e1701d43d0010000215042007000344043d1f50103020121034035400c010001158461403a0503215032604845864004403d5200010b1056054100c5001b040407954103012071425154441e060700c10b0b82c0011a4003058a540341e2401c0d51103100e422000c0e6000d401c00c690012000c20100f07080341d01110126200c800b00108100a01000c07034031500120018480b2146060304507298060940101500201400d40359200c1d0191a0b2051200740c042ca00c018074100003180e91803400c01c0c020400c0d4032801c80704c0d01e40c407840001c0040c00e25059503511860080d41c0c08582e510081040350300400c40030101d041c40000d10140c0c04600c028406494002d2031004c00140441c10079002910718105284d0b481c416509010040c00180c0f00860003040640440c3c0301401c40022007001070b01c21140350360740120411590074480507031090705a2500036180078280e00f00074001041c44100c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 966210800 1250 966209550 966209591
    0x515040206040621090521030103230a1202060703200a2d0201020301030c05061e0d091527080405091305010203090c0f0d11060304020109050307030b0901 68
    0x19501500c00e000070029513016000700b45000c02c60703409414450407081044d400300d5030410f0040d201c503800314207441811411800f10307003d8112244400c0e4103641c55692800c010100100c0c41c1c85107400556580a0550800c10045441650041c01012101602c4000035a640300c2154060000390400c501daa03100124569503e0840f400088024030340919503009403118140c20b00c164010300041d081d407080c0c4901e00841c080c030580b6aa400581d030782d451420605980f8825400851042004100010512174610500402d4441000300b0740d440f0f40c881036042004110006029140c04260300095840c1103840c0d200280c01c00042100e02140c88001d1450b030034080700a200140785110403c4140306910348503a0541e4045010107450410b918240d41d010700f6a001542c0121150f4001d8580e8040d5140216420901c900c06072196402c000c1c40c0c0e15940301100c1003a0074240105000000314082d03910034000e4102400c000b800b01d415003039403840c00c5000910121510191075103007030035410304400b81d003848 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 966212050 1250 966210800 966210803
    0xa031506051809090a050303090106090c1103120c1b071502010507090611160611070501050f07031d06040b0c0c1e0111010609051906050a080a1403070204050a09051504 74
    0x451400c0b03808184a12010044c1c64052903115109003040024400c01c001d51040a400c1c001280c0705141c4203280040d070300842c030128180b0007868404484510f0000030f40303107884050141003481c0d0301c402280303c4441c4560891942801e000040314580c4a20000b071400880d2850707141c3d000c02151000041382251002d0782c640000a8130f417402008054030401d81a0030b106c103108260740124110007000040c1081d140e000d81d0128031a0a00b0b040c0241d818020305000f040300303003030281c500721820550ba240e13840346050007000e10480b1540081d00381c0c1251000442c000e80580800d0360f6a4030780300341d5a01a0010314044100d80b0030600188000d0400880e400c11040003242c20301000309001c001075848015000905900e5940c4a000080c1103240340a02402003860074061105040040c50420030351700c503030304914001c800c802001c004069000071075170324950f000065810359040c0d024205003540b14944020398003e0501d0244000c146040e80030158142c4240201c4504011912090128400c00c560 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 966213300 1250 966212050 966212077
    0xf060302090a0216080c0309090703060e0f040b190612030822050a0210170106090f0621020a1407050601090506030a030f080c0405040e030307230307180503030a03150605 75
    0x20340d4400160032002130046150302d06c040d80d09003966600402c08050781200e04100107612902c0c200410402500b80d83c1d00041e044803e54418945600c0f005140c10014050f0340d000c03000017481061151440e0300030009805c000d0700079034511a43d070900410b0f1030010740e001e910002c07059100304901351600500340c80007540800a0450050140c0802403000c0d8910360180610000921b480098008982414080e1107280c07038040d01c0908200f204401c1c1105508560244a45102c0000001c4401040b140b203800c0078000240c0c0e61a0f40b044102e40341040e020807081400c01c0400d004003008008106e0380d0680d08005010030080e950542050f54502c250762002e03001c1802c510280103020b00c01c0a0301ca52140e00c64081c14642030fa42d00100301150b45101c00303407140d500044103112000380e0000000d540808041120300041c4404004014540f2000d80600f00703011440c007554400d415402c844000500000301603e480c0d26a002c8003070041c000e059000780c0300c2400d1480100b1440e0084054aa80071003420 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 966214550 1250 966213300 966213337
    0x403020a0b061804120207080c06092b0c0501120c0c02040c26041a0f0106051608040e0a200403081b07061119030f030518010f060302090a02 62
    0x300c80d03104101e0050079060b0007040345000c240d0382c0c03201050094056441104804030800c04030034000d0034418a500021500c0c4c20006451040340d4030f440c2070304c0150604503070309841b041c2e0b400b440a030400401040707502c80f01d400e0170015040c858080a603800300c0300c080c0c03203c4030980c04498001c022990100b9648000c501255039000c00350400d64407544c02c0d09035070b040c18401ca40e48508582104000220080310492281c402c020030000100c00380710940b0b0b40901040482c0c241031480f207601d90014010b41303040001c00f180c950400c190780070005800346d400c000c00d50703034a0740c0b40d0111461089003141c4284060381001d0300c074048071501c0280102c1d60788200300402d05190844d03880009580c085546030309a5489001d03c441640c60078400040103000c141c0302c240b041c014406150b8100344c0111440d140850707481c207564001c02e4020315111020b80441c03600140b26502e81408481c40540b5440d200011342c680005510340032555031042e41564000c940c3c3c640c869580b041caa800360b22403491001e03041c0caa481d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 966215800 1250 966214550 966214553
    0x3110303240f0604080a1502160308040f0812010501020f060108120c12030a1e0501121205072a08011109010e130c3b060306220603030f080403020a 65
    0x24444449100070051900c0194500b050003e02e45400a403c011580e804c40c801940800c8540b030000b45651a003601c0c01c2d41061150159401c6400814402400303020103000050b00704008103049a1106c1d502003509511480f400316a41c4c01054240916400340c4660417282c0c1d075024000031000d048607d800c00908000200001c1c84000d40c00400840f48030348185112284c01c0300c0c1c08000740d8400c50007000002144000400100441a02c8c90b2002c0c45003072605c40107104244660009500c66500816a271240444c044002c46003031007501c0c0301525140f001305071a420900503c1d120f0105600c0b0414066100d625446401d0888114070300c6441c120074204200c00c2e00d540242c00c1008091002041550203240360320701007040c0d0740803400000018900c00b5452400d80c40d910b150030301448405c0c0e41c85030106003002c1c10612032042c4000840c81044d020002034442d41d03070031494040040040b40032809000c112071400c07000d052076001c04c8010a44116060303140512030100e00c4e00c6150194010034201805 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 966217050 1250 966215800 966215851
    0x9061e10140c031207050c0316031707020c0907020c010c0f030207030b0f09010c030b06270406060509041b09061d0d03020f0c0301060515030a0608160303110303 71
    0x40c5000c107008200d4034440840300e000e00600100050200a507a81d880c1076000f8107013024000b410300c400d214061000300003810000040c0c3c0c0103503500828036000c0c140d0a04040d070f103504041d003107101285941c0c0104900d099000c51400045d00f025102d08410751626403050380c40314104e1000f14001201c9404c6400800d0000c40060007185c0640180c0b4005601c90301c80328503240c02103500b203d40006045c1030001d840024801d030011016039241c100f06008202000403524852480da04104640552410032442c408030360905c581400200100081c654516000d892a0441d4412500c20351401c0c40b50017442c1c0041c075520400200390b03a40d5044050816005507030125940701010304546100b40309098580342c04803000e14543c040d0f001003485940c4003101c98074214449080c24066410400208516262100714480c8061502d20700d030b450fa50340341603080c002d02082c1d104600c184100004030b612500700c02e40c100141c90080d41e80f41d1844000000c220740d203110075213072303402110113040c60542daaa01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 966218300 1250 966217050 966217069
    0x10e030d0c080c1c260c09030c060d0f050a0204030201050a0804080c0706080103120f0518030f151602030309100f091a09070501020f07140a0e011409061e 68
    0x30880b0070350300b40b81900380150300d080d0702c40f040b05520341040c00e540501542c0014100007040901100030859003c411a024181c0300c002d40010044480407d520042e07941c00d003c102807052000d4407954841c4400801900900740700c14881840702d2506001c1603c0300850700803201920303010386802c0d250241c00c44048804000013013055609400600042c02e005806010340c100510595460004650450404282061103a6502400d0102c110a6150100d170070400b6946045e070054100741382030207102c0100b8140a00c2000710300c40c81c003818040140b40d008201c0c00c50300030010686816440c2403412002d81e600e1100351404c0030f49034000010350840c42c806412030a00e13252115070115a4001c156500c0944c2251070900d42c054400304010480e10740400c00802d0000c00d000d20041c07200b00701c14280c80e612009c01c0e014042e5502d0101a2403a00c584030b102d003c20003484a907035846165030b0b690414020030b0f0b42c0505c0062254402c0c4000c10240d14000c1241d034220102c4020701da0410599030b007004000c84 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 966219550 1250 966218300 966218303
    0x20403050d0f090f080703120201020c06040206130b0d020d1401060c0b040f02180403080703150320030a0302010f141e090c060a020714010804051c02010204240e010e030d0c 76
    0xa1a40004502e03a410b146851004000800061881b41d045181c201c0c210304403200d0351411684148100c1c400c1180010350b6a40058051300c8007a0b840400381031100700c080280c0c111400301c04001601002e1520194014120380d020041e08001444003028090304400083c0b10342000591240c6a080204190308801a0058410582d010402d0303084d030701040b01030007140d4043c1d916001c000f003000281a00b00d02500d41c032080c030b46010000b02d09805141507020400d40800785c080025a10408200c034540703910740b05d0365803004044541d2500b00d450028003918080c0c00c00c0c0c503503d040014060f2502c8a0a8030540900c3c1034642c0069180c62854007800381c2440203004803694880c2c2c1c0740784c074029261140144134a0b00389602511890341090f49895909030024041c504101a100801000c22008280301120345000050342c0d200002d0490124064020b581003107041c2c4504882120000d00c1b040721110032503410b0f4407521050070322100103460070060700301c030790f6050f41100001403030b02c0748a841c4035041c3d0b5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 966220800 1250 966219550 966219557
    0x801050906041b05371d011b020d05070b0403120f050306012717150105010f0507210f080601111b0604180207230c0d081b1c03020403050d0f 62
    0x1400403402d090342840043c010858401103c000e517610560f441150802450b00c003805199000e8202c20000300b000c0250141805a410b42c80c1d43e030011582c400ba9042400d9400004840f07a40d0f8594410362115802444102c400c400740032130801002d8010700c101e1006000980700c0c01c1c2907941d003c00550700803001d00d00d42d005207180a0f60740341c820f26410f02070714050b000c2c0c01b82d0184101840320445103418a014a01c61070380130b118004000e940c1e0b2211a4028408041c503100d6150100c5141c44111301c41d1400950071144680010317820300c594400e000ca17401c4800c55a0311011601c0710303c01911540e03018000c101258105c05104000e2a001264501010201400b42031400f541c40365900c10104000e0b0034070207000d40005041c801c1c481b01611048584007038a08002d0032039000f04401c0d070345280b0800d0660040992462580c00d00c9101000e42d06e04401c4007031203201040d5480541d41e19070705a8007284a4402e201c1c1a1080914860b1080d5030540e68020020004501520000d0790000c4198000c0c8080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 966222050 1250 966220800 966220837
    0xc0a0c12030b010f031109040207050f03030415240b0a14070515010b030112022209140105070512180a02030703151d2a0604060801050906041b05 64
    0x10802040341840400e01d540004110080000040010f04199001c0f010582400c000d070310254030740c1c0100d41e040541103900607661041898030604001e204a140d56543c0800302c100402d1001c0c95042e40e80d02c4021240401c0700a003c01c4d0710950340d8910303054906c030041c101c0c0424040c850700380c2e000b4403e004442c03c254114002c0c81458401c2039100c03080c11902034000710380910240a801c4000c9024001c42c0d01e0703050070756041c01036a074822511101d020344a070400307000741c5610050b06010315190709c07418541400600f03030178101803088181c601444038156203000c2c001407001e4454025030703050300300b5402038892a85501c031050546158007004856a8000d1010180c01698104481002180b0915491801c500725460000803a65040c40805c59800b4855a06000030004101952900300481c080903140d609131000341011600c0b11007240d009000080c01241081e0810007050481d60102d81c1d01402d40d8030401032100b6104d6010324050602c4441ea40c140289008030050080e0f44100078402c585d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 966223300 1250 966222050 966222053
    0x15220305030904241205160b0a03240902070b0a020313020607020f0901080708010507020601060905120717010618022119050103031205090c130f090507060807170601080c0a0c 77
    0x1000366907801041038117540c0700b0140400c0005d1041c000340070f44121102020030301e4010903580600c02c420a00b410144d0765901d4a0351a040c4401412036060580f80c0c9040d0b02da1142e0204009511010040c0c44044040c2c0009905100e00d00071a4481c904411a01714080d200d1350900926801c0300c4002c03a4000806d01c0603100586030710542078000c00000004003585803418101c2400c40b000602004210341288005100d1280c0040a00d001c0303032000c0d0350300c400c160303103100b0300310b0a0811980050140f07030b140161140c1c002405400c2007013502c0b416088030304004401c0da454402ca12801d907400d01c0c608245640c8091510000407042d40c04410350403103024507100c4038401c1007107481c2600100d000c14a06c07417040c441e580240c0720b59075105c00320600600d0540c081c2d41c0012612104045c0c07900c403803619500d0410400c8469004884015400002c0358491500c80380c000d445078a0450b2420300003082004010011392041a0f81341c000e01040e15401119121501c965074241c1c001c81c0c544051040900c280320 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 966224550 1250 966223300 966223361
    0x2030106090f0c09090e1e150a1b0804021c0312020705032104150e0c03070306020d05070503010b2a1902150403080f03041115220305030904 62
    0x2040591890400520080c20480113048034041d81c10143c0440e241c41006010180001a40e410501d40e48184820f2088407800b11403a101d2001d02007100c1c100400140400c804031500040c00001480341d08003404850000111802642110065030040000c00382c0003c1c00d042c0c21601c040f5a000340340c000d4040040349083c5060fa413001204440315070000820740740002140890f9205100b04070102d00c2030341003541380c5103582030304030340110b12a541d1400500c3c442101000075100d026009000d50300c1c195500d0078000000c6d009506504161802c02c0000366003a0300c140c003100d041e268521030b060708040014145154081c0854091100c0805601c00e03260b10320810000c252207010603141c0c02c10010594414029074014008c501010440d0a000a1000816520a460801040d405001e8603039a8509005203a02e0441e141203820600c0302d0891701e000f07a40740000704074107400f1149044420325699010300b4545440d10010300507420902c5250041d250035003045c012401c02c1e60060304a0344e00b0400c0030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 966225800 1250 966224550 966224561
    0x120f0804060e090115170a0b031e010b01030c09090f0609020708030a0b060c07030609050a061d01060b04030c0b0d06051302040806061c02061605100e16060f0c0203010609 75
    0x200040350307118800103014501481003d000d0018005c0c075801081c000303100940510302074801c0e00d01c1603104100042500c01c0301d5100a090f8440181210004005890b5440040c2c4010510007895420031401b000ba03540640128143d808090355801c0c161840c1c101d01a0040c2800f20000c108a62520b1000550808500190007401d0040046a65074184001880c08850020501c0745c010181400492000d100120b8558101c94103d0008143c1c0c40d810f1810701d05150b50114000d000d149070400100161a002e045804074001e100020008640c580d14035141c18017540c40020910007050700140108001a005044600d4103a01d002c5507050f01c840010300c07030343c0d030102c00102600e5001c41e00300100f0400300806604500c0981d04000a01603c1c0904031035848900000fa002d900001581803d0522210910794003d40100179035000b51486855500175001400c40e84541d0c0c8598588260101e003142600d001300c40703c036140c40300c60b03400340d250680c0c0701031400d2000d0307900d0b540c0c5880000300402c1c40c1c041c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 966227050 1250 966225800 966225809
    0x41a091b070c062705060714010203040b0402120303090307060b01111b0f010503090304031205070b01290307021e010207051c270905130f05070312050f04120f0804 72
    0x5151001d400e0420003400201844090601c0c68188139281030346450410151050328070a444095403804941400811210460b2140d000b5601c00400c2000f482100410316014900c01c07141400e8481c03803403817200d503240015103600b40150402c210031400102954489107002e203040c107000845000c07188841b4100949154035801200d111444040f003403070018002c1c4801036090a0050450070218045662800b4500004001145408070b03151340600a8054440159004c0c0000d0595a168150820714003411007802014400208000e0024901c4109491140a280e8000c1c440381d5542003001450414248942000f9542080602e01040c0140700001e094480707841c042c0c0ca1044080c400401e41c1205000c80ca036040316001c00319103c403c9000b44141240d4140c08042450b40f10040d40170031607002104028450703424800000c08005003c81c1401c00c0324022a102d0b060841d40c42010b0b5501e201d810501000b002041106018040001c02242801c2d4001e660100303e5240d40e540ea03085540c0079420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 966228300 1250 966227050 966227063
    0x1a18030a120c30111b0f03030f03040c050f01030902030c0f190602010e060a090503121b0304060506100306080d180e0906010f1202060301050915030615040b041a091b07 74
    0x1103c0c41064110b060307600e070290440010004900340d00051802502040900c41c4200c4404031051010b680030400c1d28100740d0a030741a240c4da402c203072502c15070400580c070803503004109080c0620619030080c40f650703420a4000d0040d104034800f000801c41e070840786240e039544c0f25800e11042809964000420000f8000c16000082d076001d10307030420fa19000000300150350590401004c640011408810346a540c4143e0011850607100c1031040c00759100390442e0b9a00c03240000c020481440150703041980203400070b65060090f41000b860032410b40359140103144066000595021815204090060103183c0300100514201d03261120100e0034207050714040140d0780a41c2c0180801e1107221030740c4004144501d0503201c42e040350f50108505020500c101c80c4521081c900040701003401c906c100d841940003c00f0349100d13140148840004440721003405000c1c1d03141c84820445401c15200e4040e04c2801c42840c0220007007982c0c20410101030060000c203070041c401014001130751545000d400d0781c501c0360301b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 966229550 1250 966228300 966228383
    0x11116061e020c030c25060f0c0213141b040b1602030d090303110a030e040c110d02070914100308030601170108030405011202090d1203061a18030a120c 67
    0x500700713450500c146d14103032001d00e010080d03401400c0b00d511807582103a0490400e642c8901c0c1c2a5400c0d82d4541c000f01010b504400b80c040c0c1c0070507081099002d4604c0c0c812400c441c60700c0341c950810546001044440c5048000c03000c0006002c10f4120a015010400c151102c0c0b0380042c51030740c0803900308904003032000c02040a00703c0c11300401d41c0003140c222000402c1c0c0c0041162a0b01a20300819100d0302211a50240d503840c1244103000e4814503410826a0302102101e100d080c203510020759030800c91103415080b03407808484c8001c80455250550003400c1c200cd5040c03083d42507440d0f440c1650b20240c00541880b61640c0080440c2c4582c2c00028002c0403801e014603151864400050441041c8004120340d81e44100724071310380c03965142030303444800d90400680c000b00141444140d0003000d058021300d9140400072141c0d20450000802050012141681c8003150100301c024185e031101c03140d40040c000c41043d81e4142c400d900c54079413941d045008800b220481d80d003041420380c00c03030484400c41a80303c400c007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 966230800 1250 966229550 966229567
    0x5010b04050c0f090f0d080c100c0215010918050723010e0108070e04021c1d060c070f0204140901020c250905042303070302011116061e020c03 63
    0xd10641d58000b08102c0c82924203104001024014413401400e1881881c1d00788414040c0d40b602441c0719046079020003e20b5031080e000c41e10300c2c0d88041e885100303100c0a060040c0d42c0e001ca4400300d4040c05a28400c0c01c00103859081c5455039006c2c01c2500f441261084114070b01c4c50200d1002c018100050401301042c0c0e4442c00a11082050041c02c030f81c01d00c3c140010f001507d0b1050741d00c144200da00500615240c220760388000c001070301070b2150400c81d14400d0314141002c44d0000780340e84219450100680b8070304182000151158944008413240c07154070405000c4030021880e149000c4005034401030002031326524240d200b0b40c0f900010f5030107641980d404110301034600c00410200b00301e044146030181180c24070210314843c81204d802074000268454003c9401c03c86c070498500001300c4c4000c00403603401c0501e052030b07660b50090101940158200200d550540e5601c070100da80e00c3c240d901c50040954006c5d107809000c0c0812002c3c04d1113140406000e56070066480c4090018151890044c1d035498940 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 966232050 1250 966230800 966230809
    0x903280309060305011d0910061412010501030809010c0f08070c05040506041505120f1504050607090f0302040911102f060a0e07030c08010c030501080a03020a081e0705010b 76
    0x21078020b003040c540f611005001d1700c59540400d01c0341e9420040e6021441c1e5401b1140c600708903a00c0e5031f080e0324900308034021511500400340c1160040d010b0343c0c500c0c01c982c1c4084030907003a180203201c082c1c406d0b4810410011154030074075400070440e00506a0054110450b56040d41961060740c090f00e100c0400c0c0b00c00d0000d031419004180d0052412035003030001e05484105400c85150a116481c8500d811002240200c1410300880d2800d884070380a039022003005207500000b848040303404891602503880014080e6008290074410381d107011039401186030440d42031100900e00028191484034400d102c103c0665a41c0085190f0802d060313682d452407481c8040b08014004071049044196000107140815100001503955070001080c840410010882d602d41c0b1308001c0c007508080c003054140300000c910303104150801c00c1c1c001086d941c01c00c0700b0783e6699415910b4841810b801001600840b02036004520b480d000340416040c1d003441c544203620407805410060707210420407100d03651a454401c2c180e140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 966233300 1250 966232050 966232067
    0x215040312060506070b0a0203270c011106010602061605040b2205030c0f1302190c03021b030d080c09030a0c030b0705090139050102070605090c01050703030209032803 74
    0x3c042c0c500b1418410740303a40f14011030704000d188042c10707039010000410750306040080c03203c0c003074215000903000d840110640d0b0b100c0c0041d240b010b0200b20307507024040c141400001d8a0f8102d440755806480551a00c41304d40042c1803043c15004c003007180c1404013040b0103502800604140026a1503a04400413040811619991642c001c078401d401c4401e42d055107485160091441c1c0108540b0b6603502c031807a08800e40280900d0f20480e02001030019a104c10b56080101040c54038000e800b02d82d69000e010b02610403040400301500d40540000e0300c0110380c1130041ca002c9410005840c10503090040c0781020902e000c825a10075581ca446180c4100280603041400c560082f00901c3d14074680686c1e01c001030010b40081642c0c10800171030031004203884850070207620203440042440503120400e814914082d420861003a1051460440418522000040d028110f51010703103c407400c204a035101a0001d4000110068142c0929400a01420200c85101d0410508c680c4205609011414010141807 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 966234550 1250 966233300 966233309
    0x14121501120509070b0702040e03030c3103110a030611071b0503070b0706090206070f0b1014060a09030b010305070e0901020306030a02151e0307140304020a03060b01021504031206 79
    0x34036110034065070303c0300400c200040c1c845a0703030040c0c0e60384224030101c2c1c000c003517012070007641740004428041016075001c0182044500300d0039085840a1034210313810244069040c02032180740c1c0e000308000040e0444210704290000a0078902d075599070351101c1098410061075031445500006524041080e0486038540c95646818441121410500030036500c11050160586500c4042441401c000490300440080e0b90301400c11038580c078003803824080519840c1800c55421072910005200402e80001100c11560316814210f140034024040c0f1a0a5101680f40c004102c12504c000c804156018540c5000314840c030002c1104502c2c140d0b0b02c1c80d0400d0301030150348aa90040051140645d030000c2c2e1824900d4040703070003210b68603c22080c070b0700384d02c00c000050326031070500280d10354212040b00207188965070584940104100d45c04040e400c600c4110382c001e5001005010a1010803011b50100f00200c806004a41c144680b210301e540455078103d404a0008041104403034040341140140740041c07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 966235800 1250 966234550 966234587
    0xa030212010602030a0c230f0304170a0f2301060b09040c0c11066102090a240302030105012108030604021e070c15021506010915090312050c03040614121501 69
    0x100d2041e51050b001002d10391001c0c0ec0303c03580014140c0c911a039800c1b14000d044410000300011a901c06010074142c0108000c103224526040310110140e0085200e510355541c0b00380803401d086100740820805d0342042d58a10111070f40904000014214486a0200034561141300c90b0a5001c10000000c1340c0c550301c8001510800802e450642804031000c0d036094030307138119142c0301c0740c0d6602642d0708001c02410728101c1c5481c0300c2c92000703181007031100ca800058074000c0e40240200e0385c88204161440c082c80360304d01110980c1002c61008101d5440245801440c01440985040c56070035981c8440401140c0900d018000051060100086010510020818540c0c160410700701c5a41c00703034841106418045c0349440d510009200c6a1044020601500301541d9641c030400004200600840150004035211113502c1140907040d40100107036208041514021490181001000c4464000104140002117410700583c401003d101c0030586c800d0181c0d14001e01d442281200060014000c507070344000b030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 966237050 1250 966235800 966235813
    0x11040305060103120203160b040204062103050d09020a0b0c15010518070207180905060108030702060f070303021e0a1706061603140a030212010602030a0c230f030417 73
    0x5540400c24604413608460104031a0709044030a030700314460b0040400d14038603c083d080080003440040315010307a0007601d003000a01e071943c940305003000441100042940c0b81e98034000002348500014070b0051007070100880c03220030641c0802d00510356500030040c0c10001240e000d40101c4200b10306d6041d10500b0240780c0303095142502003903000202400d882100b507426000590654000c1007204c006140d003142000007400311040b44e07001000c1842044449028100000646450001c00d0f10800750b002080b092a090818a103509c0c5175114440c1201415020300c8102503d030268059868405080c01c100c0780d440161440040c02d0801c50201204c51442c14014841c03640c69403425501078103001164001c1503030850506448072400b541c4107001ea03880002c0c481c004035a15401401c0703040510702c21640c1690302d134401a6105c0c051061400c0019025074480e4002c1940080c9000c0b08410071107400e51500d81c40a407080c10a0040030140e50303242d03c0010104500c01c1c200d540e0969025052018001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 966238300 1250 966237050 966237053
    0x60c020109260d2705010c170f06062a0c0108060d1505060114193c0c0501020a02071806030f020f031603120e010306150f020708100f110403 62
    0x20038010b40300301040c4941d5400f0050080d1519011500c0c0842c0014044d4807901c4961800ca4007030880303140d40300c2c0061015010385601034200040640a5185814202c44594844060003240e800004440d0100e07110b400c054418100200094858210154042e09071b0600000000d171003418003030403850083d214506a000803443c0c0d14014810045c5900000c219070311024012110f040c40d21025a400c2000003513490300500d40400a03105801e42512050181d029404240f48203445040d500f005902010a404890b03600c4501d99420300c1481e4200103020380500d889640c22a0040f500800150703000d4001801100d0340301041842c0d18074881002d00c0210705541d40c2c036011240d0b02400901035003110b8005025687c2c144075401003c81c1003804926595603c0c24401c446d003000c0c4804002142d8002d12410380b5510034001c5105070b80b80c510040002070300c2c10508031040a05c540032241117004440b00414064014004c1d02151850480003240d580c0010413800c0031903031035404041c08080100300c00c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 966239550 1250 966238300 966238373
    0x1030305070b1521010b06040e0603070b19030b010c0c090e060906010602030f0f070605040c0306140720070f060e09090106060207031203020c0613120903030e06090607060c020109 79
    0x4c4035083e0700c00c05200303058260098103016101078030100764405800b04001c91141407020244e8800d140407021554415512001080548039610030410a014907180140701035002e5008408920018500032031480140d4403a50300308019500000c1c60310b500c03081d030023030324020400082d82c0060b08440030f03090719413414002035981e201d81c0a000411080104200c0d60060070513042c1c2d54815040348041c040c500e003528040414454501003110180e107000c4080d0750300303501141b04a00c201d016440784040f1140100075005400c0b034114840b9928803881c0340c0802d4207100d406070800240190b8030307190ba42c2081c070800c00c840784000810070542d9070300d0080c0400c00b90394005071801c212a000020001c0c0034800303100840c081d1084015010041c4071321410f100c51406c0c242800300e502d902500300142c200c41204812075516445100180002d1507500d01c105092900c40000c00d40c3e03c1c001006646026100d41c6c07a07100340c440340280d07040940d540760f01040503c80c8100c1c2d4144030205010003d000000f40c00c0415 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 966240800 1250 966239550 966239569
    0x1e04060b071101022e062408371d07060e3019080913021204080d090516080c0108040804060e04140a06050f0d020a09050705090901030305070b15 64
    0x20a8801a000d910001d52807544d070124000c0c0014024447c007404030030207a0030691503182000000a024040065403001032584181802c46040140c2d007402c00c0c070455110022544130032006032142da034189400340c8035064032402c440c003d2404003400900d46070600240608291441c0240a40c8400307549084d0351414141c101d05911666601c1c2c0a8903900c420b5403460582d011526004200007051000c0500c440e07003000d40381c0c024040710504009103c0000400582c00782c24805c564500703ca8010400103484500035100c41000b01d1400900c41e11a503c0d558034000a480030074050614044007400444030521400c4500380c070a00300000181050f80e103403022481944660001c1240031322900300a5600c68000140c40c190200704a0b445060020901008198a00c81c141c428807220084044a00740001751100d910f400404c0030004600d0040b800d0041d000c0281118100141004000c01b01d503500542c15001c0d501903a01c154468500d441d180e07102d0140604003c0e5142d0901201401c55940c03c0b10386c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 966242050 1250 966240800 966240853
    0xa031a150702190b0a030f1b020a3504081c021b190b0c06060301061d06040f110301030314040e070f120e0c03070b0f091e04060b07110102 61
    0x6120031090f442014180a061a00450301d0054001004011154540c11105003604200001c02800b442d811030310007100d004038490b0001d030300540800e40c0801d0455802003403190701c000c2095168244902244000d5200703c10b040001c5002003000d1142c21410480d9510a142d410050090408901406552540c001e00c2c030001640214901c074a0a40780c9845542c81300c010801d040000d59140c166440341d0780c00c203001d0744007036101d01c800051480c6414041c0c4012507401d0f030f4901466241d0507943e114807038401829103400c1619402c0700300b5513002074400c00034141c1d45c094900d83c2f29411483d00400c001e51074021a00404810310003800011048002140c10583c94108818103480362003040d141c4000c23901d02c4a411b00d1414800040c03403080844c41c100381e91000c40a032102c40340c075465100c11314040c051200c6a0f4400a0000a2807820142d5010707002400840515940b410904006800d4909903000441c844801088402c02c0041200301008115000d0000d0070031100107020046241151010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 966243300 1250 966242050 966242059
    0x320041503061a04180f050c030405010506030a0b181204080a0506013f1202060115111507020a0b0106020705120c0d081c090c03051c0807140409020a031a150702 71
    0x5c00040070b40031b0fa100c2d044040e0032130001d00552408281c0f4401c180c100311000d0b640365003840009241c6180104e0880c0d042caa10400100d403030b44904040185851010f08044d001c2d2090b40030b458018030b002c1000d003005040700c100a0981c0c920a250090038060180d00544656000410810301091003942c40a082809800380c01d0200a18000f0a44074461060707014004141951504040759404aa168142c0d401c1c9540404881545101141c11900c0404044503075004851075503003001810010300e400c15050310496400c0c241ca600c820456070701c00e07400003000d81d0140404028170700307200c40003801c1c82d452000500825051140030070794080341400000e00c4d6840008400d40c04001d03015018600d114000401c01500365a03140c1045512250302098506200c0e07590303840c0090000015401c240d04943e0b4407a55a5101e82c4400c3e10b4080b1050202d18801c075081c400854459501c0c805411108100d42e00810811480b038100d020b0424101c0035180540b00503210b5030744080105046403281d030380c1074a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 966244550 1250 966243300 966243329
    0xf0f0e0d0f0204020c0d09050d050c100c0203060f07030501060903030c0b0c0c100204030203060c042105010912051308010e0d0e040e0601060206071205040c05010320041503061a04 79
    0x60981480d5030074190080d4030620104150301742d9400059804500d17026503c4012071541c40c7c5081016803608042c00a200d5480700c03810790418207080051004e00c10090608400903020703540000e0401e04100c0783d03070350440f10140410011651501a003401811541001c403106410343e10010540040404042c4c8400181c00100320150308860480310943e0303549085d100340c030500c040080081e5100d4841a1b203c0d1042c400800c03030b8140c0c031608032400c071360b42482180c0410398a42d01c0d084a0349003044082d141c1c0e558810003d000310703805030640b41001c642580d42c295203441c0300e40c40052102c11f0381c02c0044103030726004002001150018001c5c0545840c2d04003e207003103094000040281c013507074480c141240613100001400c3d5800045c2c1e41e00030f05103510b0300c20b0290220032204003103510454000d01007a25141d030030007180d40240c0c08284204411000250410281c000d900c04a50140d8804180c02001d041c01c040e4081d410710031480a801c81000f0b0060130261240e40d8266800782d40611000c108510 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 966245800 1250 966244550 966244553
    0xc15020c0a060219090905092109030304093e0705010b060a080f0f0f010e060d061a010908010b03060402062d07020f0301020a080a1802030a120f0f0e0d 67
    0x20800d015599a11002c199a44d2040740806506071304104c0240020858035117004c195902c40c0c1c0244c40c4500000b1005002c1514098421100c580500c14034409442041080000d0358a0900081000d000a6031303010503206000e17016610004c048500c5400342200d501e072400d07441c100071007130700c00c0c00c1c42080300641d1038031031a05110740101242d0721240d60021000541d520310f10381164a0174401d244220700c6220350ba442090140b925401207403a0740c0f028600600510020714004103c607009040603000c0c0c02c04e542265a02c004540c07021100c4d58101d5803500303007178500c0d6921251400150040500074014103506c0d0003c01d0f0380d1000908003d1080102113100c51903500450035400010001d00c0711004450100700720301700c6960102038241e00a62024001c1d00260a05000b211590f118694070090b03142d85401c0c10400806107121034003100442c7d01c440c1d50269904100c51450280500d940c1c007181c1e45200000342079191002c02510a11810030760300a00e6035008a4800c0c140001a6016200136038107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 966247050 1250 966245800 966245803
    0x1050103050708071103160c1511070e07211d0f12030a020c16080c0405061305060406152703031e0e0904140c1c021201061205030705010c0c15020c 65
    0x400c01ca91600b07d044400070400c0c003410300c0c1600215a00b40d58505c10300029848101e48075098000401104d6128400810040c10649a480d60007401c40c40c000c803411070105802c0500c8a0403c02d0450303040e480340700100c22a03c2e500f4110706a5041030b0000d005c203035419964191940b00c0e440c02c846102d500400012101001ca804031040d0b02c1d140400d41741d201032080006503146003640036041441c820f07050007900c64101407064a0240304020a402001d485035031403100a40002004144c1042d15408002240c0810303040c840d0055005032107820140301c01a020b022000d114010704240700e103c4000800100740c21500340207140c8884004a017102440f0102500d10504058401d0b0300540010204000e0002140c81548940403403019100000d2048080000c003290004c2103104540803d50140010310341404844c42c02010a030000c14113030782c1d0300380007402c0c030352609000e46440d00000f400000b080000c0c89801c54075141810030070100c0ca560b4661500d07423a40d80030480a451303400105114027a90 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 966248300 1250 966247050 966247057
    0x1514031e01150312020c0d200409021306030209060901061418030d0504090507090807091d060f010510170403030504051507030c02071a071e0b011d01050103050708071103 75
    0x502114110660f40d107444070511501001076401070180200940b010701d07056090110440d04000d520382c01184054030824002c1d141119254419502e0440d08010703255803070503800f50319010b00c000581613358018003403550401084580700c2c00d280c80060180e6500038504142d00d0914a41c03003511342040c013207008903d20740c048012340d00d4400c2542283c0b9555014008000b0f13110046028061521954802c0c0d651a003031340600320f65504a01402c1c401d0049036800b10070340c0712072480700c0d14000002660060520601f541c40c050310002440c018021030800d040207072046c40a42c50551002c0e8402100d40714680c03000f40c001010152035801060600c0380c10023a04549a642000942d99810a01009030060010f03548100243c02a1000011040c41e02000c403240c030450880380d18605501556041d001d000c611000c0c401aa082041250100c5c00f112030f12400f0301140c080a03050400c0d080e1040c01400310582c42a41013600b403031f0802403055480015540c21504500304901c1d07024031020380d10b08502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 966249550 1250 966248300 966248321
    0x40602010c02010b03100b0a091b0329010e040f05131209030c27020c0f1603030c0f081c020a02100b18040213020703051e031b030601050d020403061514031e01 70
    0x142402b0034607580000d04032208100c030840707880400001c58032110603c80c42810b240d10540d1500c0b6101100c03050350154801e0b2410740d030000c000044e00000c3c8852101201c5040da43d220358807000450f02010131505524180e000b0350207041043d004c51940d40c80d0841003d0501a07a05092078103012030940c0c0621a0489000c044030003000c0d51178035602d4444581c0c500c81180501000e105514103020916070301d4045030180da40598480841c2845500c1d081a69480403c1c22030340200c0c100050401d00c1d070180030180030000c0501300135a50303d01083d0000e1510703101402d400312103072821084007856170b06c802c0c1151008076845a6060f03265194000100c00b10852418141020f0000501e40101540b00300240100400020041c80150011001c0c1c0705602003107490300b01144568030a80000a6444055580f01c40d051521501d80400c642074001030b60030640c0100c0300103444030062a128940c000d8500040d00c440511800b80d0b00100002980c0c68070045082548040380521000444000390032500404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 966250800 1250 966249550 966249569
    0x16140412050a0215130303080c0408070339050d0201020c0a0902131719110a0e0a2901110a061b020d05030c031501050c060c040602010c02010b03100b0a 67
    0x3000e250400d26110482c0c040300320302c2040e00075400141c03013a840065039060030f00b80d010354281d5421070350142c940725009488901e00500030f0000040d034400401070b182c0594844c01040403042c2460044104010a00c44030384200790008140700491500103e52104544048441441c92003071400142d04151206403060342245070004049041a8907400404000000e108400d0080f03036591070b0703201c1020b01401c8681d00c0d070b00304c81c0e104da050807104e29601007124010312418021a01d21800203184d40015804141d1400c0005c08000c00c07491548a15980c82c420010400d13404004080041c2000c001c2561444c1030100380100148070384802c02c00310250030341c0320508201d02959488007800441034061000c0041c4500c45510070701604c80c40603617001300b5010f0302003170464650361003041000841500a904101050040c0c0c40d5070003040203198001c01e4142d8165513542c0c14180d009082d941018100f400b035a06142a440303060b2030015a8590f26401e200307000810340c807801c2c00955240401e41c01070f80903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 966252050 1250 966250800 966250829
    0x14030433050f061201020702130207170c0d09050405070e211b1507110d0609050d0c050c03120301031101050712050a02010c08060609040509100f090b0609161404 71
    0x309070000c0195014403421a0448004d000301d2031258240e00c01d10f48001d4118240c04107049940002e500900141c9120700d40c66001074044c0640001a074104240b4000e1903408401d40d010a1500028034001601e401ea400b07000174500347e0400b07015030880d640124014202c1d8111800300c0000501100b003000000b5007681c02002c44203900040510228008520074100740b851130700c403401d00000320b681841c0d00000c01c0c040282e003207003080b03807822500b203003542d00c983c45d2800b0380d000130400d000c1051460f10a40300e40907440c3c070741c0c1031003482d100407221440d020398041e090410281c1d000310b0607070341141d910141d400c100c2200c04d001200e06020b000801000c12482400302102c1681010142041000c1a4020040f48800310001c50740d4140030740e0035903041602040290b40350b00f42504840e80c401036680c2203981102e030080c2d46204032600c610710212040d503943d140e50104680104040d401140c00c484031081410302d0400711061100c140029002c0c482607003d032980e4502c58105070340041c600a03010300348 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 966253300 1250 966252050 966252061
    0xa03030807360527310b0f10050105180a0806010617060906061801031508031e0a0503063309030f07270905010c02010c1403043305 58
    0x30080000d00806128400f08140b001805841c683c50040f1303020240d040c805241c95640007031031482d8494420381251400d4804800300c0301c1e0615110288244a0007541303940d450200e50540700030b038020b00b4030b0a41c9082c01d034041003030380e07841702c05c1d205c3e070342010b842840414041d200010540c02d0303254454000e50041d10700019540c1d402200e0542c0c24201800729a0340c5941d10000c011051a0443d0440d81c00602440444882100c2d005070404010044c140024910045440703500390700c0305da0b4400889540b0000300e403503440a24418103004134495802e80f508242196030040c002e0b0000a1016001c0c140d820a00e00b4403800744050712400207109442c81c0404400ba500c0f40c0455800780300303918004d00ca1206c41c0c120b40c101c006007030412034000c0c00200785000146072010500701b5203c0e81e200200390721002c0c0c42e000b050081c0f003249040901d0350000220418289005494690007404e951038602043c410000415845248800c0c140100a149084550380807245100c0c400c3d031605221505142c80100031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 966254550 1250 966253300 966253397
    0x160f05010509040b0918150601020a030507110d151410140604091506030b1207060e040608010f0605010f09081002030414010207030801031110090b070201020109080c0610050a03030807 81
    0x20400e00090544a802d1940d007c04541c0b4241600c84c94016031101101501192244014195081c40364031140401004600014407925404000743c403102c03814007519095510901c00e4007130980c031010f4029840d1401d41030700d1b40da50050744180c5408110620940d08103582d100b0440300a8084108200002c4000e148240060070b003600688010906e413400034109072810324040b0391768501c0706005002c110304190080300d03041020042d5079046a1180e102040320b900a0280c1d21408a106500168091406000601310340c400c0540700c09001d145c640a20005c130010812000350001c140000d61b4a4966180c500c2211072880c48086042d407000c070f103002c10194407110590403280121036002c0c2d4901e50004205140e0134614040c2c021501a083c104401c13040308001c3d02600e8014000021401504c5d2690305540d0301107007203403009030846010440c4608011441c1401380030240c45000c0158110780e005810004060005000e01c0010800c01308050b14803c0c0071604905142084180c507000005883d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 966255800 1250 966254550 966254581
    0x60a081218191d0a0207020d230312150d03050d180c03080a12180b0c070605190608010908030a200a09090b100206040b0c0d0c11160f05010509040b09 66
    0x25000031076a0000300d41e00c50005c1c020f643c4c0f030640090811704010b09640d164000d03811199100840c00c148920344501c6000c00740064003800245044458052812842151803d9850420188200c9d98007032035002003039004080e03c0c0741f400084400540c0c6100c144d02100030080f09a0000c080c100703902000b00822440f4805800c4a007456210701c40e00c401f0502202c03050740c41150070004003001050f030400200307040d0805150019207000d411071420361180c841390b05a4408a904134148c081c0c0c44070411401c0900d108020040884200800490300039546022072844003400a105d92519051a0f40740c0c402400c003215228120400382e9a52003404100150500001c2d110b00d4403010325208001360b05003045203501218021aa0103020103030364590311305c031a80802070101c4d20400802d205824040d0039901c580c1040c0c0c402911503005086070381920b00c0c17800b480000c41203500c00401c0f804200c489409a132110a40b0000d007421510303082140301040041c050a402154000726400a01c2011501e03201300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 966257050 1250 966255800 966255839
    0x30912060c0831030504050301180b07080403021b04230901061a09280e0103022e08060d0605130204050f01140f06040e0f060a08121819 60
    0x144040382c0d8a84500c900b2109000180260f2480080c40142c040185814a802c40c0c3e031090809600b004e4440001c01d00311002485511242c3d070040740301d01c3c28020008040ca5010901c0e1038079880502d031a9500a442c0d00950b01d01e40042e50400485c02087d603100d400048074203680c1d50700301c401c006140380051000713401607502007640e500c2c0c0980414140c00e21160701b030103a14800c005a14291000c400d0000c07000c9139043c06542c03003010904c510550308000e000c0d40000c1885034882025035045004000043c3c20360200d011075507070741e111100d00300021045a560710710307a94103054885551f68008a80d844c03422140007084d05140404100080341114502c0034690b00030b450800040c0e6038100006e91445d02800740c0c50920400481b42c400900c2c02c12001000a0005080503081a903a503080280605c41680d9105008160500b080540c1c10540e24210040c1400402080006d4444106202503c10f0385d8140712514007003880c80000da118100d00440b4913401c1030240190a54076504a0901408041d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 966258300 1250 966257050 966257057
    0x1810060f060c11060901140309010b0109050616031119060f0b150f030604020723060702210309030c07080706021203310507060f030e01090308010b07030912060c 71
    0x40215107a8400c104116010340e1040700910700b554404108513580c1c0120001074104a44540d40e0540e41d5008400756004101503c004940b0b8180d100024007401419001640145018040207a00704140242e50704016010f0520700142030254141278141103945610043c645d1021648908108440e804600c01d4402ca000c1085001400e00400c100300d01103614401380d2101c10300241704140d80080c021500420020401031800d002039031020300300b1070903031107204040c0103007640c1c0b100d40b40701840302644c040c10b0b41c40a080340040e203079075141c0038140354110034038800030100008803c007030f0030400c80e00c515469608543c0c0066455240b190345140031300804005002d821140e0184892407c240c1e4010070b5541c611000790f0402800d28810f0010401095801250110004012a10503c0b4503800340805541c0c95801e03103140403001e01640c5002e003043c00300742c2c5054961400719030700611250541c3c040e02040383e075401c01400c048031641c00e03d03000707050f52900c0740140c50308004c515400340c4003441d9180c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 966259550 1250 966258300 966258329
    0x905072d03140915090a170d051003020303030c0a050c0105091c020a0b0f04030e0904050610081911210304050907020c010c15061806031703070215181006 68
    0x400c4081c020307400c0c1c5403c0100c0c0d100340c240300c0c0f2158013000c1c1e0f142c2c4444202e0440c1c01c0d40b40c560f12000c0c913035880141448203c90002502c82510740341b5014907076110441700d282e0300c441403455021a95078440100a00b2717114101148400240f485203040382d01e85a0303602c000b0f00460400e020255181d4209074034600d48a40c1104c0008062070001c81ca180d0b600d0b8210314050096991441d10201c2d4090090040b01003181840d45007805586410f000c50081c0e0058000b054285801207010044d9540c0342c10561050f80000d155058440200c3e151400c0c5552007400d00d1101148100403403580505076104403184000d900f01c0301c80d070135000405801283c0040311044100d0315691000e90321204140b1410340081d030a9407480010031401c0b056a0000301083e600003d11680e60350a20624541d000101320704035480360400c000307000815204a0f070103950703011131902d1400c014401035620148964030581884104000420706c035181e02004a2400c80481500d90344d04c04440341400400082c06000900d44645 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 966260800 1250 966259550 966259571
    0xc1403040c06170f0a15050409150c0201060806160e1305092407080402030709110705070501050f370e0a06020c1c05010204080f1c08100905072d03 65
    0x10810390302990034007100300c40945840724100b002e4000c08400c491407051b0b00300000385030344940c814082c205000300c00d000390004c1d80c0901c00003550100310319a4210781c14110140119000403071117a820250321031180c090038500b080c0980d868034000d82d015170300c04d03060f00b80c403194440300360000303445420303141c0070703145201d01840251940c000c0d4240c1c06611029900005070701d0b00c0c00b910b0340540043c0020700721013003070b07030b80c1c030710b801d003038a40e2141030880094011840c5403c0100401400001c3e16003400c1003810000380ca00d458035113004850344140001d0a10702c900303103a002500c40841c004e13148103401601007414550040d0211080b000b0b290301840c00d02000140b154400310703a100c01c80800500c4070007116400c044207104403184030400c2d05c0c155400c02c030000d07540c04200007118680a0301f902030041a40200245806c9482d2003c0c3c2105100102003004032088a1183d0102940c40c1c0d140001581e071201d07001192181030f400411341c1e40e1030403018025145940440c00c1c040032261a5814003080c00c0c070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 966262050 1250 966260800 966260837
    0x26011b050307121514031e0d180e07200303041118060306130c050a0e09060c0306010e01111011030604060b04050d08031f060504170a020f040c1403040c06 68
    0x607154546510121100c2407042003131703500d01c4500d820401022110180307a4018040720161900100b120141d101c1c0d040740b52101d40220003030644880c0c901c41800460b292012204100c68020060020011103075030b00c4401c0c68401c00009444e480c2241103079200c0c5001e180400302d000782c449c60a841401901d00c3c132604851a80d0141c0e101d6400903028042e44d450700c01c41507000c200445811916880c1e44c60010138551621031800008000a81103018241030280e05a42000030107054003006d140c00f041001001e0742c1014003c0038150702842d0894109001d000141d0400c402411041d00c3e040c1005100d10407030003480040d5014050445040121954078184125584605c1c0b0480d508020000f0740707032010130903803405123a018016200321412a80c660441800101054009401140740450b02740043c40718041c0741c0301c11020403001032034469074a03000035003c8400112224410342d103a55102e22024443c0d11203600134003044041545a080610303200c01401018010400001d10122111080c0b1a8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 966263300 1250 966262050 966262061
    0x3033607091e020c01020a2606062b05160f0c0f14060414010b040b210c030304061d010302041211030106030212030307030c020726011b05030712 64
    0x2040002049824a0200e10340040c08180c0201c0100d49070000d01e080082100b800100100d07003c0c02c00060b510084000c014211001405004c8100d521260314a8024400d822005400c4070088881588402c102d80b058800500c4003600c120041c2100031050141510f9600120b00031400c5411002101040c0b09007254940c8807104058006070141c59860041080c03a100401541e0060415200e0b46d00c9940600e442c1c940d06550407120824030341404d0781404030a02c07074011002c00484041c050203100c00c00107000c4101c42c508110841d0007070755020110100030054242c01a03c041d05407500d5665440002d41080c3c1000d4081413a00141028408258801e100315820340d80740303245450090140e5102e082140c0c034100c0115415651706c000c00720160b501d0310314180c02041c16000865691502030001410303200c50300504815584400c100744210498002c1410601c0c0052100c1d01c2500b50114601d03000d01203000c288034802d40b46811301e42c0e40c2076018008500c1030045458522031590012291021580d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 966264550 1250 966263300 966263401
    0x618150a0e09060d1a0411030c0a0b03060a03021023040f060c030504030209013512130f06030212090c18090a0c0806070906020a0b0103020409050304080303 69
    0x1900c40020922034030300400a83d4011101074001040d441e203503502e084240e01c0c084141e80c3c01c04c04140c01c110405c2400e1040360103e11007a005090341034816004914140e02a000b8000c07140c60100008815443d01080f5030029a002030281032140da03040c3c0c0c0074040d00d40c078800c07451111b9881e6200c0c5103a45c07041c0301168210307000380c4016035600e8541101252254540441213040013003c100000250350b401120601a082038441304004007400311107280c640400e103c00d01404c04d0313241502020b090f008125a01c0c4078a00030f9019980d5076180000643e2458144c00c4011850000c46011901c6581039001d00004500c103100d11a5548910003403a50b5955500c151179801035a01035440d00100f6054091600129040300b25181e549490b5100112000950081202548403008110007594401c0e05c4200919a50001d42042c1603a0b0f1a220418001404040d000380c1d01c4600d01002c004041088900034440b00041e03d032a41465120721040d1014503c100441990801c100445112703000644003c1c1e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 966265800 1250 966264550 966264557
    0x525090806060126012301170402040f0902150a02011415010f030b2205150108150109050d0302163206040b0f1e030603030a050708090618150a 63
    0x540e50b410046641444010003400c2c8910300031801c81c0c6415008120502030076503a00c407000c40488241c41000314490a100d0301d4104450740b1000628030b1031103408181c205406a4012507992680401d07100640046180250019070152100b1070403040310b4050710800100354004d2004144641e01c0c008200d0301a10006c2c80d540d18000c0d06241c44d800b54180d42c010805604020440166100025030380c80c2030700400000c40d000450b6a14070b54801e5100e0a40d00100e803030b8044c4000036400c0002052108014408509500401400c0c501c4c5e07801409070310300618004004003c507080300d190085d1541c140203d035001003d888140803e4108480c3d6401c6801112060345051707400a11501d2112000c5602070180c0291003000302090901383c00c401000c403e01c0030040d5542d62030303a01e202d404070700c8034605e80703a180f8140600500c42980e8010080380c8610f605450140d803503e9240c10201442e1184c0724120390321410000d50803100700c1d844502890b10810840e0181c1c1a41403014441c0741c54071036095140c000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 966267050 1250 966265800 966265813
    0x1b0105101208270405041103160605091c050718110301150f03150603142d07050f0412110d0308060d050a0b01080c1002210a1205250908 60
    0x101440305200c900c04011006446070341070b003c0807504565082c0d8007030f00d80004052005809007410459204501141a440340c0c2c000d1811400078446c2c000c0003074003445140e1000d40c0340c0c1130030415008403418581240966500030b60f07072203542802201401d843c0c003003e401c04c240d0aa00d2140b0100b528100d0300e54481c441c440c0e0302017900490346141c1061480c8285903485071542800440080c1000180070140c8000516140740045918084d04c01002c4d244248200d030481c401074404400c0300c403400c464002c1400362589075144141e80301d0044c140a03032905080071034005070301c45203e403110301454010400305071008507440601c000803141d5440a004500003202081060400e003030010080760040e8143e4820061130303961120700d1042a8000f000300d134130100e100203c51404103070891034240d144c00105000f40d21202c0202110791140e4203503581420200f03c01031058010020581d25810702c82c0c041003146001300d10640d0004034240d03540c25201c21154085840f034040c50b4010141c40c0080d001b07204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 966268300 1250 966267050 966267067
    0x2030904020f120108030306010912110105071703090a03120209010c021201020d09050a030e0604080a030806130903020109030e04020702060403062d050609100308090f03031b0105101208 82
    0x203540320a42d03540c502d010800801041d480c50011190280070701801442d03590502c00d00041140b84541c02004003140c155400100240382c142d250b68100380213003441d5842e542541080340b100164050038806c1d07280d0010420814400205014020b180310381c03030b001c844000e07140c0b404049005040245010981c180e4000f009803801d855040c149580c03142c0094600484024400181d0b5101603080b13483d540028603010805803c04e60050612401365140d90074185082c0c0026503594030703954090244952100440c4451b107402d02c0088105062100c01d1159486902d002402441000400c0e4002001291202c0052815008440049400900d00381c2001c0c10b5458201c0100b1391145604003162390310b203017410307000003548000b018981000000690791400e102440003841c0d0080c55543d0410850b6000c4c00003c2481041e0344540106450001d0340c010b0100c04a86103104440303070f2100c100c20555811400d5101508024418030113074500c01c020325642c15110b18400b00d08400280b17000410b02c030451 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 966269550 1250 966268300 966268309
    0x324021c090c0906140f011b1b2c060103020901050403030806060706050c0a1106160e010e09091b100203070b041e030305040638030a05120307020706020706020309 72
    0x901c06802110700c81981580d41d507480044840940c01040c0c0c65090342e095180520b014400150700d46000c1c21314051014810b01049150190758000804410117100888110400002c08001810700518291103c102d10001031070004548180c0000c1d80304100c3c0000c0c2154440d0003901c108010686605040500310360701940d42e1b450060035250849001e00000001c52890f00800b40a82c9299400700c1e90303a2401280280030002d00e049800c0786034800800d02c091340e0141c010015042c0030919040860340d904c9c4c00109c555111280e19642c4c0404a28280b102c1c2d2140410304e40050340c24040e0308080602000c0034400502403491082015070010322061012420354014164401e00c51411500c4c071b1001c035028000101c2c46040141c00203a0f89404000800c0805e2241c480c03050003440c904142d2210401c60340e85261a002d540c0720081510740c0586140fa20700b001040506580b020940316110041e44100c52940c00403640d480051103442000500c090021894109803000756019502d002d82200501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 966270800 1250 966269550 966269561
    0xb01090311061b1b03070e010501050d052205010b180f07082a0421050717010902060d05150a0803040e1003120e0f0f06030a050c070c0324021c 63
    0x1c2c002d0f410346140211480500b840103800410380c40c0224652040041c050628014481e04250500307104840103103ca41c0e0054143c1c0c0e0b131000b1402c4041850303503501c03400d06440981600d41c04040035110004d0003c001040d000b08910100c103513105011203054049102441505a442c20360094035900410340107486140e140e0303484090304410709905c95544102d84080f01d140000c409440b2008502400401303500450340101e5241e625a000c1090455150b041c0c4541080c814491f000410324460780c0c0d1503100b0b410408034190002e203201d44804143c140b0401501046442c608840c40321624150145003039120f501c2176540070401582410308002641d124030740c000d4601c0d80500c041f0080000020001001148003100d0380da00c0030402d403c540c1c18004060b48165019100c1e10000e440c02903151500c0c2c0030f4a40c40681c8400120300c60312003083d050303041e20032001c0c0070380030440125003c01401004282c1d06900c04c80c0c0350000213203011030a0130300c04a006003a0180b1401c0d50f443d5091100c100c054111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 966272050 1250 966270800 966270817
    0xc051218090915070915080415051519050411070308070e03150a0c11010221040c080f1e010219050a200109020f09010503030304080c0709060b09040b0109031106 71
    0x40f42d0f04611801c030300d0074034802c00b12849000542c0c148014031403004031403c40140966103041c500683c3c18076540e040d0160400d048415a840d0b52080001d0001000059104c0181c0c4040c00904e1480701564921448951074000d0302c1c040c50404880c0131241c03500300c0c1111030407038141d5680009515041e20482e02024014a1958940b01b0b0500808000c8031580b0818094170316104002007000d540c0b280903107102a0340c0c25690381a40b061081020f4210b04c0c010a0512880241c209103003a5602e242c03284a030f440b56004891036108145440c0c0c0380c000001000726201074201e102140c40c204011101c0d0a034401c50f40031020440c0e402c0120201c96001e030001d01020403603402c040701c1c3c0313204910b8810070440c686100c0349040e80d11588050306509205c0b0801c40c15100a543d00d412660500c00840e50302c0c400500020b106031000294140707014403d100400c054640d408007030040380d075603202c0090f00b0780100944610451600140226540c010542c00045a6011801da0310700c0c46c0d6441000782a8200040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 966273300 1250 966272050 966272053
    0x6040b0f0c09100c120c021f05070f05160b03130807080c061611060f0105091b030c0d0608160614070f080408210f07140d0c0512180909 60
    0x1010318559074030882420580381a548030301c2c0071101805c0c4805c640e2442d112400a10141030002000f40e20b64483c0c0007a001031840010300c001200007400c940d2031240d03143c06000ca85110401c0000c001c80456940980100c8025803074401d600c0e0002403415100948500810044d00380c0304100280c50803001e0121a4041d140d004e0802214100103403d1910455a00e00c070800e20711801d200c42c80d00502840e080d0b0305c8000040103149000c04806820140c103000c0c85201c4c829010000300114820081c510f8032152002c1c01a0322403c221041e0b0480d41c20107100b10010380d06124000c9480c210001c0c08a41d0001c110f450070100c01d1601105a070f0386092801017003180c07002000715030702089940c0c082031a5588146140d9a4542c0303005116403d1840c080b095100c1c214200384041c540d1030244047d40c20f11210640e08030307602c216901d4005a162456003908000d0700641c140481401d401004020b1840d0192050362880040c881030100b403031050034081e026500307230000d1200050030706000d015030042d1940c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 966274550 1250 966273300 966273307
    0xb070303180b13020102010e0115090b0a081e0712021c02150403030c1a2418180d03021e070f05011107050c0a0501211e06060e0306040b0f0c 62
    0x226980250b0304100d40c0c40e07000c440510b412a04650b0b092141341d80500c6c00d41c000f044031100340001d42e54450120311034911030385c1d100c0d96044026076803d40c524006141520480b001030010b190107191010070004419034034002c1000000754117421107801d0810f070382c0c0146488488d0001c020200d082454003d8180d130070084260500c452801b15000031f10141d402a200c1e001801d140d40341c4203000403650104400a041c4000c140503084030128102c02d00c0020701c01c80d84550000c480003080442c00c4030680550898484402e11070b0300e0f1b8a44608503517040090090701d144005002040c0c007a03105503118901111102d100c50009524010042c00c83d107403141c1014035038800184c6450b820746042204075154130a00017846030800104111407245284140d68101550b807a00b000680081e25201c20a0200c03510f060062030010840c0d8840c44403420724645500000511502c150001d010301e0244030080344109084900720710340044e0f0103202d40d5010075410510755502107103004030003019008041d00b850a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 966275800 1250 966274550 966274553
    0x90b03041b03120c0b0a110304031d10031b0f0519090f0602060123090f09010e07060206090f062a19032c0c0f010207080f0a110306010b07030318 64
    0x100101c0340f03000070a940d0078010107654200581c411038003500150245107046003000c041c480c22025640c1c0710b41c00d03041c210b00c0504611000102d04a42c00b003ca5884041c0c007060048454040d84041d03c440d4003e03c5900b174a141189042d130340e02d2020516140070071000c0c0403c2d1103d441301e51044440503424a80380c402142d881039005100c0400e50441405600840014081100c1408a20f00c1c401280d940c1d031521089820045407510350081c008c0245120b44400240340c10000350010b903800d0161700c00f00c031042503031040005d41b18003007580e54407014040c4841b2084080c0c0300040d000d00407400790081c041d242103000b0300302d640d8020b0308081c4283c0c41400d000000c80c444950710003403020030301c43d200860b4a40f01c1d8488401d50710822501041440d01204000c9050074000406084400068810182400c2c54600503458440390b540003004c42c2c030840141c800b00060104000440d144110340c001c4180582c00e00f0107445403c02d004400c4031000c1444a0b07408207211780c10030a2b001da000580220700c507206 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 966277050 1250 966275800 966275813
    0xe101403150717010e011a1201050618030609070302040e0d14070606030803010e0103030912030804022404120506090c06030a05070e12030a0e010306050a03150f05040f0b07090b03041b03 82
    0x991000900c1c100e402d004020700845034030017a041540500340d00b490408207018058440b1010b004003401050f020441c400c03360104088648000c074000d00320b80051514156166544001f40400c80c05107007020a181e600c940002403150317400080c0c0d1540b140300c0ca024403d4540503000010141e40c03481c0c48500000114803000003d5001c0c08201414160720b60540c200900607800e140e0041902c01401e803899008254003455041e00f059045400102042d550b10707200f00801d4040d0000e202e00000082d00090140e20304821411903441390080d240e40e40d441082c440e858085003000981c10100070000a0506907080d4007280d44000039003020705010740444080b07101c000d5014440c5da0a5071002540c00b000c1a0010402c4030841d009190500c0740c281004042680007400e48001042020b003091500d0004206400c04c0f5040700300c641041013036242c6400c06a40b18070b01d810082d190714842d030f4041003004ac40b031629641550349061045143d40c1303039a41c0d68003014501040110b074520300c6600110000b5030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 966278300 1250 966277050 966277097
    0x109020310020f340c17070b030a02030a0f0513151406061606050c0a080f070504060e04090503070f1a01080606060d2301081006080712020114040e1014031507 70
    0x4545c0034519504241c2103140c030141108001855034000b150401c00300001c3d83c1160382c4801c1410001d80c41c3c0d190612454050602c1c1200e0300c1019040404000c0401c41c0c020300c01c00c404d40070f030f121501404515416402165840c1d01d00e8444244060002116814440d004200c440c181d046044400c400546440b41180c0040d103010030001c0700019100720300f0303600108190300900780006500c40ca0504090240c0b181c0300b184502d40511820404c09507299860344d00140c015500941074075510304045c504850000e80c200c504440031611540c0803c02c0d40c00340010725059030400e000401050301c40d5800c106268200b02034802c1419180c01254400491a80704100000b420280c20071465040610417801c04130b8494403401103500e8800204100d2000203844011102c0000074180c000d4403500048030103c6801c103108002002c000303030005071022545442481505421144100d00b81c50303034002201c40c42c08158040e13040e0300045a1988a5403002200c0e504001241450380d10b06100c242c00d80d45500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 966279550 1250 966278300 966278303
    0x200601060306060e03060f07080a141602150c0301060c060b1e0906030d0c0b0c1e040518070816031d100b030703020105070308070309080c0109020310020f34 69
    0x80e02d940e42080101d80000a4000b594811005041c140c505181c59000e0080010a20340800c0f4451004c07810800d45603009000c40c82101820045500e0320071140b441c14072140f907a01c00140b01d0031002009501c200c0c100d96008842c0728602e14070b982d2030000b0450340800c1d10719055900c1035a03030a40710708270380d10f245610010050403240b81000c044000d0030000c4141e0018034060181e0480080c00d0041383d132004940c182301d5480880444141c0351500544070902804111001c0002050700c0a06404915809003080700e404651903020202c80940e5201c40c010300755200004510a9000b051014203188444442e410700391500142c0604001d07a1019461900e0441c0702c8a500b0103179440b00c501049000340918100e050f801401900c0ca590300080c414405c0c58009000c01040a01081d001d9210390451200d00d42c120360960348544040140500a020a030f90480c880c0c890901c031180704035610b00a8907031081141d4011810324144c1e60b05c250320400401400360001091414200301080707000c1c43c0c0e0002c103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 966280800 1250 966279550 966279557
    0x3042d03030c06060801020c03040e0c190207080d0201060b030a0c14031302040605040e0607050703020109052a0f150a021516020706030216020103111620180720060106 74
    0x2c202d0304202d0100d0b0703660b80141e292640100003e8442c08000001c8400b00d400c01c084018044d84c40f040800d40a001307207120302600020002c0c24801c030503800a1440d0549203000244d804120104806900b2165588100c010007881400051001441c903401045a900c1c03a00b03285056000e25911004580d000307c0d101c0300d40340c0f2031003016410350a042c485d48020700000e940c20080a0180c845540e6204070040009003040400100c00041520030f420510302264808121101d00c0ca8005c81c856101440071805907856940a00b0035016103844a943e040d003400103041e41c000c0e48507030201407415500c040760035015880f403184100e6880320681c20140c4901480702c0314010a8401100003030509000798041010940180301e10b4540003006844601042d60900380010855885000d00701e140c0207a1404003030460000700c01c0c0c028032902803506440750071100804448480c8090030004540e25080034040c07281900e40009003501d01038545416441d4108005900800505003000d1904200f6088030002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 966282050 1250 966280800 966280817
    0x9150301090c06120c020f060406050907170303041a040b0a052a19020313210827030d02060130140c0103020f120411040c090e0906010803042d0303 65
    0x100891180d01c0410641d8070243c951440c600c00c0688c1e5400c001b030310240a207a0343c1c0e0089001103004100307040003000950307050140e60707200b008541d45a230021902601d0300c003207940c2008049206d040f05a88180c0c0d1250182145850340700c41e41e0000c00c80100225415010807103003000e40c00189812024406090303040682d1000000312011070b45041c242d00340255807050101845140d11504c141d0140c800c034148100e158400d603115050400700303003900501f1000002807001e15000c08045041c0f110017010f07075801754500705003050540c0d64900490020050b007180c001401112001081c61401c00120b800c0e003600d10131030b0500ea81c070fa4420720408443e0844500d8039520800c60a200c1e9211405003403c0071030806864030f41c0c1c480c0314070070001f200c400c15640c3c10010781042a08034943d007810801400403c400c02c20688042c1c441c4403540554181003509000003400303400c0c0041c049060f650304501850520389801c41c126588c8010448850124007800c4000703109500702106c1100035406540c44017013 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 966283300 1250 966282050 966282077
    0x140a0b01050a2106090305040f1e050312180a0308130f0801150608070c0813030605010902091f0207051906081302031c0e0a0e04031106040209150301090c06 69
    0x10080c0c42e6500114a40e41c0000012458080f554424541e01e900004085040701c1c103840c0c2110148902d82040d40c0f02408400040380450980c940306c6484e140041d010485245c64008043d500c0350700100308004c10741e01700110300d1520250705504540240242598683ca6141c0c4c1c2d60702019040f810041403c0719068908000040100c5d900c80014441710f80204603004404402e11440c1100d80502c0c000d0005d5035010505031407058082c2036003181c1012605481d0044406001c000c180e080c4000c1c0c5545040030000300c0c09103d6803084401c1e14100510703050072070b400840c003000d840300011100c0003540500d060004003038984440341921021000b44440f821403e205000d810303603002601c104064101d1a40410050310f00060580f481e41d6000c0c09407030f1101e03492400300ca040354030300705d0700742c0024500400003101481c9080319401a8426200c00018800c41078403650b03075003000c40e4080e5028846c2400300b080c848503070340300701500e0740c2c0a000418400d91545a1071000c910561101d000120f00114940 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 966284550 1250 966283300 966283309
    0x70801060c050604020603150301051f08070e27010e06220b0a0f02040807080c091305060c09040902040516080106020a03020304092d0204230d0f140a0b0105 69
    0x1809400d590409001544068072180d54880b00104024040d040000204008200e0a0600b200c0080b008000340b1007480c3c401251041d20310130180b1000c0004100002081c0c8110102e00641920b46600c4404005d541c7c100c680000304048882a2001001e40d440104554400b8002d02c50b40da101000207103960b00b400d00882501092040042d0300030400c003560040016425658140c000a120788089000980145e120f0002d100700d6100c418144101d5100144010001c68582c204520450301c8240700d81d29104504500001e082c401810350300108009051250707104040c024401015200098090181d804201220000c1c0c2c1c48aa040300340c1185d80000644c4400840c0c09800300744060000210f80e6070700a5039a000310300821030b140381c0b10010310745103080c403031110500250140702c0c5400090544a00c07200a50080c0581c8480f408107040f81500c0b042841e403085ea2108001c3d181e00c10903402a10b0b078441c2c1084c950003ca0706e1540700c0f0001c00303d180080001d11500ca0144800c040c803945003c0030070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 966285800 1250 966284550 966284567
    0x140a09050c150d0b01020111130e060a030302101e0f0f0e030c0c010311090607030503011703070309091509050a23010501091a0f030112020f0409020a0603020f041a0307 74
    0x2984500180c203849002d80100d002503c0400b280498003040c0c003059900180e0150191310071240b008040800c03403c03e400903a18504040f40d20343c030071264590b1034020a018429045010280141c2d210f01d1214002130380c0355001103481c007800400b40d101c0c1c10a003d04681625801041d01583c04d448090441505000b889420890041d0000461a1025299820f92610920701c1514181651018500342c4600340000321041458000d0140e07a42d800b442c41d002c0c089810038000c20551400c9000010020300c0700008448415803d1780f2843d0001d0b203000098009071010080300b26131800d50100c0020320f41014041c442c001c1d40c8810020031a22060318002c8401c541041400c02d800360040010482a600142200f05442c1010082050a01030140a444510903240703101d501e00d0300000002103203100745031940c800c3c900c01c4880721009140c080401c000d80325180f501a520150540041051501980c002e2810029608802d82401d66032952002c4220460320100907010000040144540e40050213 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 966287050 1250 966285800 966285823
    0xf090218090123030a1a220807110d060908041508061026160807020d1218020307090603061404030905060304061409070501020d0e090606070204140a0905 68
    0x4041d0324005401e03880e448003240c02006214400035858650f241800461701311038215501c10b0b81e0040c8010708110414046522070400c2c404612100c02c0000c0f81c2220701d103d95003002c500c0d4181030168035440c181c0d040c40108030364011aa20300c0c0b070002a005002c2c01c50f030740e4000c5410f01d03103461808014003410006413008070100130760b9004100841e620744080f600d10102a00e4001d0030695038202030030040e81c182d04910b81c0054000d04108170580700100204240c809542e442c0da554582c01010b9940726220807444010a07110400341c580c3c08015130103070514884500360b0006200b1a0b402003802c1c81c1d040e80014403256241c034130602c2030203114010110b070325140100346401403078a900d0041c00000180580e0b80f041030000041014410715400c54000b540d000c918426290a207418403d40d12a8207115103809401408004040b550040304c601c110b003e0302814208895031000d003081141d610801040b0b074020343d150ba503488040024240d03144516081100001c5420b2a13040241c5000200c460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 966288300 1250 966287050 966287059
    0x10b04030503041502160e1b0703050702190b07030806090714070b150913030e01030204052101020f0c16051005121b0c0c18060a031401060f090218 65
    0x2040002400000446003121059500c950800d41c045004078108a65151100c1d581202c40d440450b100a2040c41940108210043ca41041190007043c0240340211040940400c109100002c05401c3c1070854101c1100c0c00c2901001d46529180e10f0b0301c1a8001140940000714042c04010321030805445154001d412030421008442d100b140c40307261841400c00080c18260424013083c0480d00d10001c0b01200382000b412012645458031501c0c0030442d9501d010380008044640d01c022950091086405a5201920910501901448070114801c031000d82c03450540d030030040c1c800b01000c0030000d49030300e08141d0701a22003012100401600c2c45850380140e0321501c400010001c2d40742d040001c40c0d040718000284581d0f0344e9034007403110956100094000c00b09207000108102c03e004007003580aa8407078200c07402d0f0404c11000c0a00ca40d031540c219051908004803900500100300c02031601102400f03a50b001091283e04d90200301501141644084c44040d004201135080614040022840400540c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 966289550 1250 966288300 966288307
    0xc03090b07051c121a01030f05100603090311010903080f0117060a0e0c0d080a140708030402121c020a06050114030c0f040f050f0f09060405100c0c05061806010b 71
    0x200c81d40d40303c211000302100380e52850342c45100705030f000d0400d0300301080d40d02004014115003003000903080c0360f400322101c1c0041d10304125020704400505c50b0328050070725100100380310b90400009034002c2c40e071035a05600307001d8046014000d003d824000c210320a84284c0e034140103400c100301d03496002401070300803202070550001c070104c0c80d44001039190360180000101140c00e8a01001d00703801d011000c000d84c2e07003191003061888140b040c500000c0201c168190303a00d50060883c040c00e54a02e0046800041c184902080401c000d80351040d500c064850041059500884281c0701403404514128604009a04001b04035018010188205130062094800410103a100e6000190321000c43c02078035880b03007003d40d005000645480c4e005c2c1c0c28588424204002e0781c1000b01c00480d490408480404825540c40002a0300c2080881c850303020350707488002001681200c1c0c5008015242c0c040c28034040140b09050040400d20401c03c1501071599003204040c107a007016801802c000058019452001042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 966290800 1250 966289550 966289553
    0x1c050409020c0a0b09302101080c040902030319140a031418060610020106080304180b010516080f131202040f0509071217070c08160f030206070218070c03090b07 71
    0x1508400e2410611b0424041c152000000ca00d4281c00349100c8880d9a480d014007038000c000510011906035100c0c40110fa65000c5041c0c100400e07903444200094140d002400303103400e030652181e0500110546800d14030494036460f516000103800c2030040e40006a1901c4860801040721203401e50002100101c1e00082a00e6404640c0d4541c00075014500a00000c22502000b61007980000041e001c2141900d41d150303a104034608080400480c210303166441d041c04c4511a40c020811501c541c0040280002032a0054441c050309030800510164414010010300e00390110254080000d0110010b182d60041c0d000d00610049982c40c801c0340f03070300c10324003018011408030005070001102e0b100064a442400145000305408a03040c02c0321254400104010080015031510103050b100150b0440b04050305209000000703031110300c5003c466400401080c400f50034404001c110950001c1c082c00030051a10581c0584528100c1c0c41500088a0180210030164010309050013410070481640c00d01800c2d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 966292050 1250 966290800 966290833
    0xa0f0309060936020309070e010e1021061e050f09060627090a1202030310030f110a0f051c08030f070c0503040b04030b010e04051c050409020c0a0b09 66
    0x8410722440040c4000c0d42c9001c1c40214020840d003951a008015501c0381001c0ca10710369135007c0ba020b00026810031400100d04000c5000399035100d000030840096500340b9045c0b02001001c03081d1040720401040d4100c18000c2481800b4818440d0412014245482d0b1030004443c2140d00140c42c0721043d922141c2400f20301040020004d401210482c2c4903d0f41c029506010340b401d0319110641c178600c0e02070700304000c21060041080d83c1030602514909940460340c2c80100c0c0c89100031248246400184501072011624040c1901600d82c401c0d25138002445500c0006900c0d401e03d80d0000200790314092090040d070501d147c0702c5c00400d01c007205151102c04030f91fa92080d1070000601c004019210300d40001c01d06449001401c0c2020340000940e507032a0b0301c07904200b49036803090009495a103104400090900840200c4511490704000a0041900c0c16540700e21480d80b07202204042000520010440d07480c80e1000301009100000140400c0c0d01c5031500d081c2e61280100145041e4001c08140c0c4002030b074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 966293300 1250 966292050 966292079
    0x105160210030e0a0f0219080601060806182701090b040f02060405060403050f06061f0807051309020d0e0111030c0906040e090c0a14030d1b050a0f03090609 69
    0x203045920444614004004400030714896880820354400c80140606200110403c200010300a6031100307180114801001000484c9208a082c42d600480042082901c90030055800140040c10410b0004100d100d082400310140c034180c0d20005a08140c181c0c2111540c00c00c100e8018102c000e101c402010340f0381c3c0e003800f07800800280010559904c21320443d0b686100301c07005000d0003021f05494907181d040460360b400c40740c0100e000921076140031400c0c0380303804001172000140c1113600d0030038081004022075103500068851000d0020502c23000c640014003040c164058940d110006840703880340c040404c190703074003642c00c00c0300e9914000c0b0605030621844112981b00300c110f00c1013541c80c0401800300c2c0480c807403980030740c800c20407420a1016542021951408500303080741e00f10300b0300307898048070032520740e1004600360700d40e1002c00a0201a80202c8607060114000301c00d802001c0c0d025100c0e01d00b4020003070350848850250101d4001096000050b88005d058a0701d00180c9460926081b000e8082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 966294550 1250 966293300 966293303
    0x71805010918020c030405061606050a0b0907030b010201091e031404080309011407150b0f01080c03060d0c050d030908070b04120602090d3315270603031d010516 71
    0x540014180413000f0081089800a080141c111990703003946603407010000256802c00c95240703051402045640d1001e0282002d0184020200242074a07502d006a00401b800b4903603a056548403039440c001328445001d00c400100384800303001c44041340e40c42e0060136503407440300030707070401c2c105000500500c0400019102504002e00b00a00c40c4c0044440c0f94230035000345400140ba01011241000106409800080e4441c00c00e54203999400c05500054900c20f100305c44003215088180009081494030340b50180320306000d100c40407140b92f1244040f81d600d9144040c10340118413103403820007441e10204001e4009022801d412810141026104c00e48004501000b0b130400c3d4007c80c52144542d165140010300380e61000070380070b410240c01e440c0b20318000d0591b00b00801e40000c1460b5a000c1440d0300a2900c20450b000f8500c540c5814030602c00d085061483c040c1016400925a0340811440d034451500074500a8035040c8150400c00c2c1c10341c05000b54070340c03018100310040c00403820a09841407003c0415 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 966295800 1250 966294550 966294599
    0xf0812070c0519080d0306031109061305061203121f152d03060602070902041a030702010b03061305071401021c050d140105030d0507050d0807030902090718050109 72
    0x210f0501c9040701040300c113600a91050b0141054440800e6015405030040300d2140510800c034000d0350003045945e410440b06150000034000010f4001c1a0f65400b050b17110200421001c400a0b403003100c0d5181d41c000580400310f0b500274a052020f1101001c141c0030074090002a1074210908048911040c0192610740000380311039210403c1140030781032551071895180c141c1000200d101c5000040c0502101d10a01015000b40b00c00825500007034000c81e415105000b00700000c91a00c1c1c0480c480c1070b03000503d840c045541c1d810b0051071a03a414084c050140d00050741841461240e410040e08200703c81e88850300540c0f4a0351ba41c80d042c0d03000300350140c80341c1e0486078480c007407242d0050a1325284a10315000080c20304c1c14071800304003908004103d0588078141c0444801c6011600159110b200d1580082c00e05d40c881c0a003264014400c0ca50b4a40c0008030b4503000c1107400090b400300d0b040b0385c1d0541d0840003061843e076200e805841100001d4005103024642015030354542300c0c072150041c60020403008403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 966297050 1250 966295800 966295819
    0x15060706020708190c06150b04120804091d0705240a030b060f0408070803030c040509090a021306031e23030c15090d020a1104090218010f0812070c05 66
    0x80c80480300a548031104d6051031101032850140c0010400701c100c3da000c13180945050190030001d400414040241c2d43d0424170540380c103040c03610302401c07221010400c452109081001040e400c169008500e05079200c03130840c0d45030400d0342c81ca031030134030445420646c040c10342e004080030384603088100c01c588084030074045550b0303642c0080201c0242c081c0c4210250001400100300360072040f404020320032140c0c0401600c00258452102c01e482e80300580b0a00f00c0c2c441e0a200900241ca01000300b40d070807940c1c2e01d040381e100c00c01030b902140d41148c500805446141d56510300b04148441c5031114200452010001e004042042e5a20000070040c6c011380101484c2c0140c162140301001c008440c000c0110707504071612808004031202c850038040340d05094500420341400045800001c0c2003081a90120000e400d684901040c44002c00c03403400c0503640541401c40843d15615aa00254080c1803040041644242001d003840d00e426145a5080c3d41c0c54000c00880d0f020078400d000501c142d5204451120300e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 966298300 1250 966297050 966297053
    0x6082707090f140f090114040b160203040807080a0c05010f0c082a030a090b0f0304060b150705062e09050403021e0d08010605120f07110a06090b150607060207 70
    0x400034034000c0d03004500f0300c00034010b4400c4034002c070500c2001e251009201c541c14805280761b82c440240d40062040440c3c030049480c8010382e0482c403101503580c2c07040706c5c100355450303440030700e0606258070136200e540200b00c400c81030101c0301480c0030103880282007031540248440302c018a4a48600d2000d0701345480440d121100f81d50801c030000f20219100038081c0c02064030400c0e1030b12a40003a40701404680410000140d400c000000d03140300d0361852003228110b1f582c685501c00501180500103600c0036100302c40b02d88455141001c1d043c414020401844241340c02d004081481c10f07801031111260741031180004044000307003002401d0301d070a040701040e5501c47c0e107400da1a00c0c51f140c0007900040c070340c69040e02000900080d050940e21080d40c8040550741c0c3c82c03806440910544100b200d1010380356000610310301e582c0603601d421143d545000401c2013011600c0c5030078028480030803956151503091500030710000c41c14282d000101070001000350f0044074001507061043d58002007407030340c02084000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 966299550 1250 966298300 966298331
    0x50d09080d06030b060f0301060305030a230a050c060117071427040b01060c020d060911090717010911040501200a0308160201090c2603040608270709 66
    0x120309540044050201c0703610f80c60603040040088403214001e40e0920701240b072a181c14012001245d4001016624000740d0034421501d07005a03848030ba40010080b01c00e0400390040301c0040c0250212662910b4681d0b5240203458107107001030307200c44074881e2000c5200318900b10108000341150b80c0020414000c031542c41c0424801c404081c005c1256128440205c85c4540203500b40e240701e14444e980074200c40e0b803240000c1e5010360b182c56000e900b09407441031541c001022940802107550140d91350a110786103a000040c50b10108407114800603481e006003113200001d00100c0c902602000f00309121a1600c541154081d010314402d581c1004051a045c00b010080403500c03c11040803101070300d1407002c0c03e0070090403400060300d00021420022080c2a02548184034900480b0380c0000d1a40c01645007079000c0b601e02d00c407004031a10034802c40348403d003c000208014001400c958907040034038944460142c20003803504149076580384406032810b4801c000400c2400079243e15200003e840b078001a07940 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 966300800 1250 966299550 966299557
    0x3040b0d060b0c0a02012a06091401050a0605030d050306060726071a0c0c07090b1c12090803040b0a08101508060a0b07150b1c081c0c050d0908 63
    0xc02c002100203a282c41c1c011010540101d4a03000780c035011064280d41c115021094250059031495000e0940400d0002c0c0494001c0700001e80a48083d80110f100d40c072050382160019194242080c0d9102da04000c1c03070400344404140c81c88542001415031801901007100c5100e0160b004145008010590000e0590031802c1040200792040050315524603203031900c144071244001c403450380308100c0021402010502221078a100b00000f81014a10f00501c00014004404d01c040c4e000e0135247ca03607141904003a64424641d4055071a902c841807500201030050030131604a00c1981c0c10400040c0040d4a801d82117841500700c624102e111036890840e00d050902103a000019035181e541c207064001750b446242540220b50454401c110030fa91110b1201d580e1081c804000d140c088503200d0801180c000c0c1e400f0b10400b080c0504210303402c4014010010341004244001c41c0d0125010403800701c2c24844c00d85103c40b003100700c07400300103a042019016209004d06480840c036940c841039040100000b183c1034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 966302050 1250 966300800 966300809
    0x30a091e050a060b041806020a20030910091a0301050907030c0c0f0c09050115121503080708070204110c0c03070e130f06050a0902120604080a080903040510030f0e0c0303040b0d06 79
    0x8a011806d4a141c480042d502003040c840000c0c820800b01162500200d60500c0843c5408000f9440c12140c1d205002c081049102c0020600244402c0003484c1d9444d200b114124040b0050120764942c104000c00401c1e6102410023010540381243c600740c160b4001c0415203c907500410720b00710210951402060500b0a130700140301090900000103994545007003201c0000c3d080e51584405410b03441045011100300c00300450507544015030403c08251654010407070180103880082c070740401d0707401050a5a080802d81500c81d480080d0b001401c403411b001c0444007000450252488030f01c0d00c00701000803400901116822145040b480c010000701e241d0b0340e000343d60320020500c140c0ca40340f1540002480214010303402a40001c03039120700f510004c41c009126981c4810201d081078070054085800400c0244206c0d0184802c00000c16207039601030031282d040c0096500172418035000104401071b20704244031250698018404c1850991380401500e00b580c0c240c140c2142c5030240c882c06100a400e19622 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 966303300 1250 966302050 966302081
    0x10810260c03100501080105150a061d060c062a0f030a021303030305060a0e0108070611071e03061118010806181005040e060702070b1e030a091e050a060b04 69
    0x120506003c850740000b0304999011008000755540e9000507544d4a940c00696503004072001424003185000d1130781da0041003000e5170300d001e000d440345000c40e031240d201740c03152042d039804101013064a041c407510944040f641d4005243c00014200340060103405525044000380c00301200140000c503c50b4140c0d2003004284c40584445607403802c014004104c140d030300764054030990700045041c04110582034121032444008001981c43d060049540900420500310240100300e000a41c40143c0712103220308501144140140c1c514625218040321100b5200c810945810300007110049450000314000d0300c02802c1c114080d0392003030000355966142100f000b000e081c0c1d860074003200c02c1c0c82552800999109903400c100c4004940001651110100c0d241c4005a102c607a0906c00210b070000035103581285045400c280c0b40698070074814a4004684043e00d8554802d05c004c01c0c000001100703051201103244c001c1400d12151905500c507140c000010b000c4a46890014040392101d81c0002044140c40c03a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 966304550 1250 966303300 966303313
    0x4150507080d0e061501090909050a140c0109050409050c040b040b1336080a0909020c06041a071b02030f010203160201060518161404080c010810260c03 67
    0x4220390014440740e9101c840318428003001400c0c11741d50070900d858255050711151a500c1c600001203014107034150045070140100513418000903542c43e01d100d20284580081e110300440c410005107407402c0369005034425130030b01d10034001180d000305041d40241c5048d034010410048480108028152145800340c021008024551605100790b0021813034182d22540588014401c2003101110140441c003031108500134082c02c4000381d5004001e0202448038100015030300c3c3e42d440e04008030381000c0c021400d00d400c0403042004000015094000c00000b0300c0e4804114146000c0003400b032420740c078515400040c02c0740d082c000c0d580e04107d202502e4605100a642c0c83ca00042e50241d4083c01c100004055130030140c020070076291041494043c0002c8209013001940d41e00c4030800020800d1840809001401d00704000c41d001c0e1100600c0640b002c14001c056803102c40c0c0c0014440c01e00102091001c0310f101c4014854001d116105001c400038114580b20044e40510450b070411300f2140021341d2621403503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 966305800 1250 966304550 966304567
    0x24140406081b0411040b1c09050703031e021209040c020c0406030c0e0a051302060a03090b0103121202091302070213050a062309190b06030c0301030c08120415050708 73
    0xc4011880d018810340f001e122200c0e041c13080c02aa0b0155000d40341c1d4454061240005c118110840e00035600030920022541000d5a1a440e05140280c1c205900040001c03c0b40603032210690303007140020246100418000403070810b1354003240690b80d06584680e40741c480c0420401d02c04c1000c084100c0d0001c0003044000d0303580ca00300b42c802456109800481101400060900850f40f06883c0329000190b0004c1042040394200f00740c50b80900410001d140e0384200881c0801d0502c6001d40c0610322920b030403890400014405031602c92215804850745004202900d80d40c0c41d48203000f5a030110508c00507032101c0c01c0f072000500c4d21000c024859141403804003044040b4255030044000c80d074048903000b44040f0b403920341074241508014441e8011080101003481c608a101f100e00351031100c010002010340482000031503a9000f0303030742c0007107982e80400180188015645448000c007481e00007031200c106482c1c00054280103030300c01c0b030f8510440c0b002d801041c140654225484980e001329030541e6003030708 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 966307050 1250 966305800 966305833
    0x30a0f061505130e070602070e0f270d03180f080c0109170712030612031107080102161509051009150207050a0b010e010605040306050c041a0a02012414040608 70
    0x44d03200040c007481000070006209002158079019a10341e10030b038805580c1c40c48a0141041800390030340070b445490042c030038030809210398044001294400034102c0c0c0c25860f10f0003010b503095a08046081010440403000068200c1c0c18440b0316980f000d680794503075060704203241c01413500c00000340c1072442c2d5009c2c1c1c0700842c0e160001050030340d1045520049210b9240d104404948142c05100302e501214400304000c280641c42900f150903250040390440c80d147c8a80c24266003042d03200c25105031903040e00108118030344115207400b03a0300c280d0030415030300d958a41560b6020325040e068483e80e44c0c1c5e130b031603020f024084881e10b44040074148190754810079894240e5448290080590305206450000300317492190300c66090407148956601130038981191100e000420001e0071405d83c003002000001801071100071705a118280060780d40f501c50300302d8600030382901c80113000d00410900400c0030301201c40154042105aa182e00b84020591a8000205005101503004503405100b000d4200051a80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 966308300 1250 966307050 966307061
    0x100618061b062408010212060105030411030d0216080d0504031403091804021f02031c02090a0b04030213110d0504020f0d0c150c0c15170a060501030b030a0f06150513 73
    0xf140c1514424141d030b11126039080b802500390750b000c1040c001c404214191301c0b540c055a000b44c0a0f000c4492070380483c0000901e040c03c100100e20144e04194500c954550398450104002c15520015100010610384001c00520860100409000c92501840500e413002c01c15504d6109020740b4842e0b503103003100440d410a0508880482c0310b1a150300c281c5c0500f108080341344000c0c05407900110300b4120f20240b00e910150b00440400d1600364203204c561030580ea46400d01c0300820100d030140341d5450139070060017801c0b03142c1102640550300300441c2c0701c0c41807500c10440d104d07801040c200040c1034079113100155004103082d078419808400305100b0003d020808100d401100c181038641011501030040c160340000e02d0301009484010400710800c8003e005c1114000008224944a40780803c140c2100400e5841070360f03000042641c407003040c800e958140c441c0e9605c01c0c0e8101d00038140d4410035038611214200c0b000c402840c0948810f80340041030740c0c440c006406400010240400461840440c030018107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 966309550 1250 966308300 966308351
    0x6030c120d0f530402090603210c0106170601050d140109060c020c0f0a0b030907230312072a050d050102070c1a0322020612100618061b06 61
    0x2e044004040c842c4006040b618503c1a41449441e82e80d942c0070030030f8206000300300540500138010b20b03008204501d114403500c1c1c4042d404503600c8403000340e9401c0c02c480300c81d08074031000c0f4100d514400101400207131283c1112000c40b01500580124a04048803030802144c6540560a084010b0b00308030705a0040720346114240d00f210080300c9040200580b04105401464002001c000244a00341030b460095030b01c41c044000315908141c1d280d2110f06100c0001d40300320750701e611000f00c0300350910b000d00c03c64881d4805903030b80783e09280c00c5403185140d090760f2100c0c20718402c840c540c00d525801c0240c0b07985401400002d0810240640b5800c103d40070303501102046440304400100812a2591084010f03141488411000c0c115078400100d0346280346d49580414051201d02c0010006270b68140080c00d0382d401c2c034486401c0c2e41c28495485000412a9000801401003030580d114042e008103280c4821203903289030062407503481c1c44007103d008041000c00340405007044030001c1441e401c0e00c4914901c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 966310800 1250 966309550 966309647
    0x212071a09012f090105181012060f0612020c1510031b03030813050c0604030f120c050d0513030807060219020606060706091a0f06030c120d0f 63
    0x9541d46503c00f41d8103400c001c603000710070310144110111940f00380c010b402184540c00448944c00c0f00070000450b03084085101030001050701c00000c0300040e490091070700900b003007070b03025070418100780c2c0c0a0040504091203c00342076021035010000c103400c03c010404161055944800c60504072100404245140400d8800f000050b025581400c06000c94204881e050750b03038418039440f04090f42c82c042c1c240c0700d4150703407a02c65800030355130560f180c500800c001c4d849002400307500011450f0550300d0380948001c5c1c40c18403082031901808030341d0126020300c1000c0c01d481c14607914942000b40c440e1040c0340b03410103480d130040440e5103820402d99034000c104030303444601600c407031040140e0226a80d0408075260343d004201804120b000404503040400d4042c800c003025540707040f10200c103210a180c102d41c01e1000000007003d1141d0b6003410700c140c00744868190341d41200001a40c002e0350b40c41d20754010784001c0024000c54140c03658454000542000401c00c00d04d601c11001c1c24003c0c0c1010300d0f441410201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 966312050 1250 966310800 966310841
    0x7031211210f0103061119030213090b0307030602130812040801050916090b0d050f06101e0e0a0902060a0906030506090112150b04060618060f0212071a0901 69
    0xc140720700e40d10703200d81807803564041a60300350b0703680310702a0a86900340300c00f0a40a000e91110ba0f081601001c500c0050f80c0e0700180c6076008144000c071280d000b544400d4040c1d1401071200207030384001c99940c041e00e0f000100569109040d82040380c1c2e5041c540c2c4401c500703001e0546015001d0160701d00610072204007070020310490720345078112604c0391008041099640b44103c4100802e840942210300e8a80c030082c9034943d64407198451505020304070aa050440d0890f03400c01030031641c6d603080c0c00e0140842c2910802183d42c070031031401e8400303414001c003d0300525200010704030140c0f40d08180d43ea10340c0505205d0310380d0240c04020380054124019940483d09100c0021140e05080c07589a040fa61010090b4000c2a51625140003051100401c1c2241c030b034035001c2810740c54459008810051140703a44107061003034001c8a0550702841a04400c04000c41b250714400403540c000380c60840c0311800030768282e4800d19440c0400050f55814040850074180c0020442160010741c449015241407445890700c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 966313300 1250 966312050 966312097
    0x60f081513091103010e0606210703060b010c200306010803030106140903121b0c091b2110090e0102070c2d030b0702010507170c0d02070803040803271207031211 71
    0x14270920011280d507258001070f01003000c1203e6411207c00c1d41018100b49540048a072035000030031040003004025413041c01c50b64035440c28100034243c010326000001d5421541064030003401c5004900a06904c0c1c4400f20f42c2200136501404901d0125640b40402c6503145121607e4081003d100c04c072a0710580200d0307840c0d00440c1001070b181846415a2a105043c4040d0101d1400541e040313003c0c081c007880b4109803042042d014200303046019000052440344514a4125078005076a843e00a50071300341d005008100000d46103a4111050b2000d4007102c5109010740362144603031491785440744003255a507500c008240000b1111082c050110340c1d00a202e260342e250811703110f1307007003400c0911100b00e07180001400030f180e90340281082c01c0603500c01501c0c01c803454449040c50703001a1004e6400c2c1c9000000d20400782d0150a000121140115030f0071000c42c0300400302c079101c4030300c0c0c0780ea4050310740700162801c209845920b051481e1a102074080010b0010359003821701e550003068015120884020f0801d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 966314550 1250 966313300 966313339
    0x50c120c060f01120c06141902010f1a06180d080d0c17040c0b03060a18023006010c1a09010c0905040e03030a0f15060f081513091103010e0606 63
    0x3501303141c00c410080b18661034004111074049001103015030f208000c1c490011040c0d11150320681b40500340d40041a80300c941004241101c5005014601c011304e0768000c410719450380c46c103540c0074465030301c10f121611803002c1c040b401300340704814010058040020b070080b04000701c0d440000c600c14981ea0350101386a20341521070b0310b080c0c2920050324407a4452810440340d40020007c66000001400a044040e03075001004500001008880a140d4020400d60044188400c00304541210322001002900030034a400e6804140a000c00341001650f10701c0505103c1c05003500e1096580040d083d201301e140c010f41c018001d0224451103400640150700c001118a49405452603404000740554038640314281000c1c020000b009444901d642c56000b007a8580d181c1e14001402047c65848025071100600b10040c524100184041035090b00d5801d8000c40d40c0701e410501800c40580d04c2c001440900307600300b8190a01007501180d501d5070a00350034091010000c01c41c2c0340662001d5801180c481d11200020f03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 966315800 1250 966314550 966314579
    0x10b0301031e0b0a1a030d05040312030606051b15160f0302030c040909050f06070f180e0c09012708010b18070503071206060521010b0901050c120c060f01 68
    0xd02110043d502081e185501a40512104105000303044c134988008000b00e41401075100459000c0b0704046401c2050050f12400c40081400300e1404200d242e0401c44007816a00500000c2010310100e11030f004400c1d00104220b140c010b4900c0111045460300c20040c28076030310102260400100312000180d0300500a000b43c90040c6400c0600d0b03401c0504141009005042100c8140e4462247c00100c2413620014087c0c43c1c0100200d540350004c4c507264440140c100408039000084c8002c52020800180708040c40254000105032480c51b550701400c1d0048841540121603000e6600700400f803204000c80c8200400f044894984c0240640020101000340d228070a140a41c012000031000a80b524810802581c2c0a001814012401c10803052410f044036021b0300042c022a4002500e018441910844200b014081e40d940e0b5000c0c0d8180340d0004214040c100d2000e051003c0407500b108540c3d000d1103c520798045500fa076075150040180303001d41d218005c1d19201c1c004d48000c000801d8804401034074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 966317050 1250 966315800 966315803
    0x3060204060f0c080d020703091e0509011401050a03020903031909080d110a111f020d080a0213050f0111060c030109110a050319020403051b0310060e060d050a0b010b0301031e 77
    0x5170421968800030000781d480100100c1c100b02010a01044030080040500c4000080c0504007100c40d00300310034040c2d8140107800c6950b408400c1c401910080e80d2103811140482e015103400f584500e001004285503019103001188140d04410301d00704041d83c418120022555020115604240c5400080c0d40c4041202e8202c0c003250803502406000c02d140440b8015840d5016009900800550200c4550a8070b650f04040060700301c05018007500d0390118520381c121a02d02021407400c0101c0e008155101e9440c4509802588408104205a8042c1c03140d241018030200139100545880c2081490a610034010491020b14116030340468101c21402d541008403251030f8940b03541c41c0c00c1d1940c900400360340003102e1016001c10001c40003840c10f012010905201c034140007400d42404080600380400000402e400524204007000280c3c0142c000e640c1000003a103c200420078107007420350600d0403014020b011001413100000381241c2c036400841c101c2e0300614050181d10121003411043c1d9204410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 966318300 1250 966317050 966317063
    0x1103191b140c0f0f190513150b0903060a050c1603180f0f0b09151b0606041505010c301101060605040504051513020a1b020d03081b030103060204060f0c 67
    0x110070070350070210300032036141400134840c486090380c030070004949010001300c2000342912400c140b08c41d40d0f031008281c005070003c0045281042d59900101e99038500c0280841c2006460320080340c0074950400c03c44464080c2d855075406030381c0310303414058a0b03020030800380700c44a0002c140008050007a0f5007050140c03842c020320f0b0301240d450480103005a4101500465202501003420040705400800400c0810552051103111001ca000c07400e0a00b0f800174803442c0120304080f41f070b50300f01c9107071071102080d0b41003420424840c01013414074080101003004805c10280b448480a0034403004443d1402c0c90000316550314080d40c00401040d800d980d5036120b040e011820600061100d407826400c42540100100c0401008410030303000039500001560b0f40640159000a28450781980700d0504001e0030030803a554980f1440ca607010598208072460003404000541c004a804d40002089441142400d5048036450796142d0800100a40c0302c1e206941c08a0700c922203c0e02118007903c03406606580004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 966319550 1250 966318300 966318319
    0x9050307081509010b040213060f110309100509130e0706020109081206011211090f12030a0c050a0b011d01092c010b030a0b0609071103191b140c0f 65
    0x34654100d030310080d0403e1515500c980c2c017803443d0745840c03000e0030b65a13141c04004150107103480d001070082c209030006c0380e0401911802d50410a03000008440d8107581c00c0e0340040d0305141d500021122800384a030500e50080c0c2e00185030000c10256000686144034034800c3c2e070302150703072070a003a030894040000080041038284051040c1d000f042d1034596000070181030118079040e802d88030030210340c080f03e24003030814404681c00100741081a16025500700581d00303154600c2d9080074040d42c17030103582d0417001040071042e0140d0030002d041c094001e00c10341c050070b26030303607542c50317141e40040103025a18595052014500004440e41c0f98002e9500100201d400d820f50a0300b0310f8800e0f03112080c0030100d0394981d0b40311883c1d00c0f0315442c104000e0b016036000304800000c5d410f216080100800000d002e107020404402005181c8003000b00c21680350300c054018903054540345440913180d5040c100c1040d07800b140d080c801e0b1418444a0380c007143e12400d406094502ca030b545101007040308010103d046030010040c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 966320800 1250 966319550 966319573
    0xd05130309090b180f0906011e0504090206070c0611100b010804020f2d0a060c0b070e0a050901060c030906021b0d06060902030c0a02070905041a0a1d030a0905030708 73
    0x9501041c0c00000151694401c2103181d0b4800303040d070209440f017103500d512039401c001d004002848000d014028050100b00005182481c01e0040c2005001d4240714556410f024400c558400e811280d0f8980d00c48244100e081d1b40d008040d145010003070312211107024000c22280890414442d500006070305031a0144907403100c1d001c1c0a05010005200c81c0c0107401241c1c844200302c1c0081c990a8008c604c0d01520901003158014071001200a90242d0240704003147c040d8002031002c1b01255000f241864002405545000051005805944019048481500040361007544038071808180b602a4030f486545964803801240d9403c1111130000060311030303540c00c014074940f0080b4500c0c101e01941d00411126182c00314201240d000740c44200104000044401d00710341c050011400502040c0010045403500b520781803000c15602c22041e80015074040000d4415440d0743c0910440310054004155040d0a140d02c1c035582d604c08000100030815150000403036240010300001075800103400303480c06000c0c0c1d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 966322050 1250 966320800 966320819
    0x30a0b030f0d230d0f2a020c030607050418060b120718210f0b010b0a08010b040f0b09010201020c070e060a0b25020a080d08040b0f040201020a03050922020d05130309 73
    0x889403607651a403219020200c1c148111b034101000d120010104400c0e1109842c0a403600c0703200340e515406900620304121405400005031000c560064182c0c07544494400340000040005421643d012072000c0380d01c8484900c1d0b070b0040752103040f043c0c461088504090800d202030001c5842070207004403501400031607401c125441d00645a01c52054641d540b40f8a039a0100c11072001d0f00700340074a40c2d0114025030b92a40c00700d001030041260a000910b403c0c209074146012021901031b4000f603050002c0c01c01100c1c3d100b541119207102000d0161031002d900d400c0d210040c8842540c5843c41054810f03000f10f12000d00703201f181c0102403200c401922001ca0515241d46803002c4000a070382c04940300740000750f50741060050740c480c03000aa49509c0146010315040b44015009890316601c52000001c100040c0d070001051155260035003009074480240d07200003030f241e000c928504c1141c6800c2c2d07881c043e1401e2058000c1c10300820b50302d0040c0301c1c5548500d001000100c4020014002503060340080065100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 966323300 1250 966322050 966322061
    0x63111041107050f0604030e0108040b3d15020f0604020f0a15030e01140103050d140904090c030c1208040311030a0f150c091a030a0b030f0d230d 64
    0x100e82042d0414101c0d4650702d0404940000c9202d054014a04210130142d10040e40b8006200c01d003031170060303814a5203404003c01001892003071920381d200c03030244016600410400600c115042c40850064401c1e81c0e6800060940c415000c080b505880e142c43c5242c000b18056504449500084c0741c550385540030010501d20740c85001b07400820540c00411526a402900700c155445e031345010510200c0240020700311145003164038001e502c0307800140000341003c543e080d844012484e0180465440d07250007241480358100e00c80d4018907000e8044200011140c07104216400384c1d1002c848695500c140845541d0000401000c09000708414000134903410140b1000074005000c603010740b42140d9a0418050703c10106135524040801501d003a0300b04c5004811450b1118a440b86042c1c1c9401031040d0720a442201e40440c181c0c0100000310141c03d968044c0285050060880d11821408408182c0b2401c1e039031076100003e082d0804070fa6505200001d25881c480410355403502c0c018441e03450f42d0007401c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 966324550 1250 966323300 966323321
    0xd1a070320030c12040305271f091e060908070e01151101050a09050105060103110912120406030c02160f06081302130c030c0315030b130506311104 65
    0x4402d0144120800072224818421446074464613501c40058030b500c02303085540c4008001d440354500f1900d4013921501c080ca100c5240800705a81c0030800a5015241c420803038001c901c143c681c0302c0740c1030001544100f12030200c54141e1154407034562078a0585446400c18060031902802d1300c4010803a5654483c5442c000d48214900008403800c02504942907690a65040014548540c07506041c40428400c0079044282420100020303540700ca2107590340d000300c10100b07108941c0981e925001c000240041003500d1410704681796250f442e100050b005004030300d07040700144103c0341c07a220166000c142d500190342c9401c0c200440c0c0c0e071174640c0444200e8001001c0002d00742100006400680f4ad002d040025507880c2d010210b1410140326000301200e000310700c25003c1506041c0e02c50007021001c40703110240c0e41c002040c08159614050511701804420354000c045108640401c40025290078605140d100c1c0f0129281142c00c0c9a250a44001c0b0303602c002600c1c1d450100c03401d041614296100140c400f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 966325800 1250 966324550 966324571
    0x230705150901020f0609100b0118050405060307080109080c011407141e07050d0e0609010903021509060f07020a0b0301030b240d0501061a13060c110d1a07032003 71
    0xe1361030084190804400355246480b40d0f10559410000e016079000d140c1084a0a18000040300e0b02d00200d903003003c081d4440c10b80a44e51710004500a9101800703442d000d403015200a10104145207011a01c07544002241b0100d5441c0544103036400d40c11740d000b43d00a80440e078414130f4ad40720252075a034040d48030011104443d0300121181c1103482004020f03010090284001d0110050312000140000c05402000c0d413094600b04183e141c2a078100200c1d00035650151468501003102c0340c5d09000c07601c1000c004545c400001310303000303d03658041d81c01400f0543c07081c0e0320740c0b1000c2d90b00c074480072550000717000080c031240d41d00001a8002d040300b1900e80e5099003440300028040e10030800f00d0289098424180d43e80d035100e5009012040c012262250a42c06d010348c51031502680a04400f034901c090f000b40760400c00501816405d000940404e0703e086c000081220450310100d10b00103000e4440221641c00d000b02c244001840789010b40f00d460f14118a1903803002c000d02143c8003002d0150300017000c1c403004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 966327050 1250 966325800 966325813
    0x10b04030804150e120f1507021213030c0e0406060905040308040803101e140a06020c060c0c061902010e010c02060a09030507061506090b04080712020103140423070515090102 77
    0x203950301c45c0c0f416030302c840c080c07000b4018942c5194041c60408070556040c04444e00807106202d40355900203403081400c3c40003100716454900b41c0c0c410b40721029440e40301800d004406a4042060640c11000e103001d1407203540100141d40d0307503080d01015124103c0700680402d240f400082d0109200500840d1301a00342005188225192075554807040c09208041c031804406c80420f1007100c120010085c0f140d078040710003101952410000079074980d4045211341c0a91008242103c0f81c40d0200002450710200a20554a61003401c42c3d0b41c0c045040015080c2c019804d03c0e014424201041c822055101e10030350191140b0760f180500003018002c0c000c000c40c1041010490003000c100785204500a181d9032083c0182460f141220003002103565405c03d0700000010002080140000031324a002c96a0315241800c40d19000c0c00141e00502405a030f0014420141080004001d10044000800b2422607640300341382881420242d1344418034001c0580102500b2102e45c042040e543c0030f0186820144125410f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 966328300 1250 966327050 966327077
    0x30e0307151a010201090206090436020f010f0c060507091d0405150c030f0c16050a050607050c060105040504060b0303040e0f0106110d0c03030b0d0f0209010b0403080415 75
    0x712074800d10014050141c1c2c8500d90080e42c4070030340c802d0500c800244000d00400080340c0001d0920711550107002d200d40d41e00c1a400c00780900c201c01c922000c5c01c2c22242402c03c07000300000640c03540d20b4140200d00c03510213001011031560040032400b03041180d0741d890202e4034680fa910000200005030521092060242c40082c1c02c1d080c01400b6100125106032003070b80c904052400c146481c02c071160103031f990449007040283c040002c40030b5942c001a4007500c0c04003070712500e05045192040301750001c00100c0b401e1140040c01400101c030004540308070f040703ccc020b03a00c01e40100c440b400342c0f20110810742c0190004004614007a0800c0f41c00c5401100c00103511407210000900c6c0d64456030010340110390100822401203106494680108000d041806540041580c1d20782c4801d4001410b0007409140c641d8601814442e030700101000c00e000e44000d0307620b401030800c401c41456503c4100d01c100c10680010517100600b07001d44045952016a117400c050925030b0410791150004408420400c041c140f480c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 966329550 1250 966328300 966328313
    0x1f051b0d090206190507110105030606160215040905070801060320070615150e01050f220510030f05060d0308040807030e040c08010918031416140304170106031101030e0307 76
    0x145c488550310032062a048039000405a1705074103201c1c0600410035552142e01c1201d01e05034941e482c810740603000d440000c0d9900b80342d0341c1e00200514042408214124039501140c01070b0120b4981c504a80e9990008500341e480c10804248140e403881581076074418520094010f42d840307030f0030101f8881c014203001112042da0381e01680e6218030b68005515056088084039110440c00c0c41c0c1075242504150b0340c98070300d01c507442c1c0c500d882510074507500510703580c1181c00001030000144100c0e8034041c6003000801038082542c49990161400010403010320380440750541c51356240d21403100340c0d5115210169150080304080d82800030342c268a55050351103204d03030306414030720b9240c0c2c03400340d41082e062004403410442c24490850080f0590800709400100c01881c40340544c00c0700b0b81c1c84150011100d44001d148500901e090f011014842c00900c0110292095079030340800721202410021444e401c0e140c1c68400640180e00100c12241994401e41096204915880c1100d141c000140d4500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 966330800 1250 966329550 966329587
    0x6031005012d150e19140f010c061a100806030d21090b010e07210e0307050102040f0e09071802180303030702060103060e03180904060e1f051b0d090206 67
    0x10001403e1644c45901c901d8070170004105c0e00c0d030145c600c440d1181401d402070981400e2420542c4500804081050185c0c07041601801059100109004a071194034401450131200301c1103d01c10602d210030003d0300f5110700310f4140300380d90090081414103441c03072080d11400030210704c06c145201a0010200c4004031401000c103900e02c90a030429003589000d075220410700300909200300f08514540c124410184008c424801c00b50980800202c20b280307266070618511031140010602c4d400030900082190100b540b8000700e5680c4103081400d40c2c0d80342c11664440685001d170ae00090030b464814070191580d030340541541802043c008982d10b1a03840000e00e5600125050710050344010010706c204015406010200c8800d28011800c01c0c4a5003041004400010f60f040d0051180303500050501c1180e800039920f0320300b52400d4894092100080f03641c00340602d0000c040d400c0c1068081900d020080421241202c05403103014189180668004007820322098141c1e4049000d00c030ba401c03c1400e406e41c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 966332050 1250 966330800 966330839
    0x31806020a0302011407050a0311130b120601030504231207050115080d051804180309030b06010c020f060a140f210402030c01120f02030c0306031005012d 68
    0x10031a035001ca10780242501c5142d005800301e541d51304288528143c100c02540e019440c80d040c081481080410300b121207008448180b484905052800503a85094500801c100211402402d8070b076529500103409844055900410604413040c088002d40413a46000005000d42d8050719502e0241050103d001e03003040200740d8150755104045014000000300c403100610307580f4054000c00c003807008080d0241c060709040d00349002d81201041d2143d5955441410300e0300065400d088011014240106070840d140011110420994003041856000d102d8025865500400384a002d0440e0b1041c000d254100c007001070240042c0c0b034a1920014460300181445483c46941c20f626401148121042e681d10440b5a4200d00c800034148809618045442488880c0a0818003c0c0f1010066510700030a0041d48100c00c4510110034400040c1100c401140154000c408454900d00daa405c503004480d020700c40d4000c907803045403900ca80481d4501c40042c502807000040c0d024150340d961600c454414a811 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 966333300 1250 966332050 966332053
    0xc0204020a0302092e030c0908010204090603020312040f030f03210e070e09070603021e03012309100302040f0b0d050c01080108030307020705040b1c2d03080a0903180602 75
    0x114009103040030251702001c0010800070f0110031074140380a01030340c41140340c600100b41d207980700040d0150041c0e19003001410250000c5658036564612600280b1007070000301e12074003c04c03003a4544bd41a420541c0c0585d1a00d60007540d81c0ca195540707440042c218100c040f802d10038107050901c4000c1c82e4000a4042c0312500d140030452070b040c0818030b410a611b941000705185000c10a02c64401000166442a51014100169618520055444668608441034145080000c008103402800c807000e11044518030050ba1800c02c00780f003c00c5211001200c640c400f03840340035000c001518207604160006021210001401c01c41d40f4045542c000d01349605a40c20380c800c0100c4116964800100380c01071002d03802450039800c0044000f51681d0480c070031144240c0e240d050039101a075480c0d042030101041440400400301d00c511706101d8071454a5002420103012900e41c0007000b00d56640e07011105d5069803501d14603a1030000390002450070880075820407003003103401c810035001a01c242024042540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 966334550 1250 966333300 966333307
    0x6050415150c0f0221070312030c0c0201081f0506040303021c2d0203190206070e01051e0c2127060409091a070c05010510030c03120c0204020a0302 65
    0xc0004020744403072100204840705400b2000309142801c0741c2074680d411a05203024034400345041d580100a002d40c0c681d58061060008108500034012012985841d04e060241c1c0c4a080c80994840e1003011020740030079840c500160564030304401880d0060081e20080c15501d4a580c041887c58019404c2140507902a00d91850300740e81138032900481c89040c0c90b2021203440c0c03950a20040300880c10008a10240288000c4000e500a01c196040000e03000d002c03581030301142c200207554090540e49030780410501c0b0042d210b1544200d08541215942ca03140c0201c80000c0819080702d6172100e840c2d11a14080c040c403218650300c0040d1502e1072030390100a09074403005500390010040201ca20307010059002c1070800d001549aa80c1903070704844085000141708845424080802c024186034507140e0107102c020054802c0e0070007601e02c02207001e40020041c984c0c0b416800503840c1503034040504243c426120800000751900c0d80129524050f18009441101c2c1d5404075040c1e0300700c0b4116a0102e034011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 966335800 1250 966334550 966334559
    0xa09050a140a0509280614030f031b0c0d030201060303110106030c050411090d081306020c130b13050c1801030b0f01030513020d0503180604080c1306050415 69
    0xc0c00048041c10444001551101c10400051041c0e40584507090159101100254002d8851002c69504101c007020302c02c00d292046003400e000301800e00505006141403000b840140c00d00040c00b1081c40019001145080d07064040144980000f0004880510600c12140d0b52070301c1d442405c10301d00303201b070300003003029811481c024280c01250100421300743e14144040000c01d240c80d45000803501d040c0c8000a00d00303070582800c02d0174442c030354440c2d41040c00303200010304019074100140403030008004800003154907808101c1c2c03641c9008110503444110040240a051035075030000c3e5800d00f00070319035000172140c1c2c3e03031036002d0700c0003150415080540030a000e40c1c102c904400b80007078902c09103010811085070200081000c0c17171400c942e9040554030f10004584d404800d06c50a9100c2d00104002451401440e146680707038400c0c0c1c000224aa46008034140f1030a00c4400d4130250f5240401610040031200b007440820100c865941081c181c030383c3d10010386030700c070b0307202d00e82906045045070754031507061 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 966337050 1250 966335800 966335809
    0x1020d051b0c031215100806010201050901090b2707080d02010617060f0c0c0a0605042306010e0702010f020d090203120406050d150510170f0601140306010c05030a0905 74
    0x41c15101c9807890200041c0c403520601000f1034442020450349848903882e06081c4441d4110141c40c1240c00000c2007144000c5643c1007400e152198000342d000b0310080d55518250390a0301d446160050074032074030300302245d40b01e50f0002c541c4901e0080c8030105038060001601903460100e180d402201180c0000b03034003004a681c28020030024212445401300c07140c03069402e0955075100145440c3d61401c205012500300d0103001c4c2100d002480c114220752040d40e150410a00500d8103407002c6a00c80142d09001d5892015952040d580a4404024083ea80c0c80e01c165411f00c4200104128115581c40554001061192005d003003441c1c1c01150000c0c428410b403041c18504400401c55402c130702e03000d01c030421091ba4800d080740c0135001c0c83c03d4017294030b410083c0807880520154005542c4644c00b5002d0100c59a1301080d4821948011444444640ca40c450210902001a42d0715070000b940341034100e250f0703112440103580101d4103151458454805480319421500108025000502050320402c01d5180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 966338300 1250 966337050 966337081
    0x1b210c08010e060a140618031014010e09070b0a0c020301110d0c03110405060d140a0b1e0334030311070b0c0a110105130e010504050717061c0501020d05 67
    0x2099404e880e0b80ca0400044a00c6500018000c81c480e40002600c510644030000301c04448200250849080e010440403020140807564120404084907c00000e078900c2404100b07030040c0740c00e10150000c242460300c011181da00c0100c00f081480508000400142c0f0309204010a900c1c407030005c1501c0e620b500c01d042c402d440c80007031402c0030507040149100542e43e0400840d030403500c0483e82e655454820400442c041c0c02c0300048030401c3c40910b0f080280004041c1c201d40000e80044481c490500035000c100c803094140070750810f815a0110302405000320f0b8040720b980c03444404080f500f010707882803608006402155082200040c408014103003c0c0b01c806c00c01d6501622050b0b00c000d00b41045210860764030200000080c24048043c070540d011039001c2d174116038001520740b19981d5626120042511720140a00c14030b07005902d444d000072046c0d8801c02d69043c04030f19a81c070700078946d01e5400c10084800805085c03ca4105400710011001407000d10007032020b540d0030200400c1ca0703d482c0b05164240700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 966339550 1250 966338300 966338311
    0xc0c06160f0503060a0e090109060609060314031602010c0f080c0c1908060402040507090e010b04210f060e010204151d03030f030c0c01020d020408031c1b210c08010e 73
    0x4050090040c0c41c0c0e5484203120070398015030306c0d11801e942d41c2034156001d032070140c101508080c07808401044505031904043c0549018940b0041c076007004941480e62841042118109040003184100042d032203400b5403012030740161042120541c0319240d20000e81e00c011340310000c1d903000a001e0600d905210104203441c8006800400407039181141c51900c0e18070051009104907510700c000380449008820041c06019283c1d0800020342e1074488036402a8424003a20b08103680083c08a6130820f400303025103004a61040306401071000f0795613600f000d00b0800880042c0788d502800b010800c0c0e4009924068010003075620305811036007002e03181118081c1d403000c45000350801c005400f158515002129001a0355150742540e49487d40002802030180c1c401071001c190000400007155040040a080c041c01c00c0000d4105a044506440c801c8550440740324078460103803205e24040a001d511801c0700190404511065016100501e5040361404210540810b441a005006420f4103459441d0f100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 966340800 1250 966339550 966339557
    0x92d05060f04120602040801050f0f1501050a12060803030a0f050901021905070f0f061b020c0a061b1a04050609061e0603030c1b15070f0b0c0c06160f 66
    0x3a012401101d0300307118a010b4007403114408044001041803981c1220300806031074000300428103080041444580c0d007a902101c11244550104182c1fa1004040c22801807058480030f10f415941c11003a00c00308004615038071003590f64900018030340030a10085101d0000d5600008440c210f034000c2c10100d40002d03140080c0380e8170501000800f401e0701214044940c089060682d00d810161038426208c0c02c0700b500040074410069030341004c11102d43c00c521045000500074070300340c0c4000f4000320395500d0004412a40b01011810400ca400d00800700020455501320507240460a136485e488085a060140b041701c1446110400060010500850b42c00c410f55002402c000d040c072180504a85501141c2e02c6843d54013800800d4840d64100b0486d62462000d600740e80a0720501d08854450301070207800700f07028244541007840c0e034155090807220b4480d403040c503080e401e2003035132140805220004c10300804803004203d1b0b65060761042000f0b6106203020602d542c05030090384030040210300c0180c52070090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 966342050 1250 966340800 966340807
    0x170c0a110c0a0302010305060a030c0905041505071205092515050a0e0f040f05040b1005010f05030f060f03030c0d20060610030f15050909030304051b01092d0506 71
    0x5076440d90b81c1041240e80900e808102a01d601000031190075180d4401856000010800240084590400c51103203014440c21036101c0c294110b11000d8600850760400040e410305520121903203a40e00c42d1750000d0f0b108040700e40600a6206c00c503880d20407000c03414440c0941c1d1a0030001d0701100500416452118502981050302401d000b4140d01c0d04002841d2003070000c80741565017900c4980c010300000107204801d0109040c10304103880859801d941c042c0b16008251004076043d401072103184d076005225a151860b560b1003580d0382e0319002001e0551503010301d0402c005207030707690704101a204030343e0004003403e40c0840710720000d404d1160030f0304001004112b881c00781811070000b04006a2010055411440c0e04880c590200c000741100358080042c0c0d80f801c0c00d450f040c400203c24000c2981d0f17042e20010100e803a00580f443e038a0200b200e00402542c80001d43c000601d200e103240080d0007506052001c6074070f84a5411820b03030054851010602130890304040c0501104840c2c0714000d100c2944c0302d614 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 966343300 1250 966342050 966342073
    0xc0f090d151e0f020c1020030a0e06010e09101a0604080303150d1205030405010f06080714090c0a0f020703050a06020d0c09061d0a030602030a140c090109050907170c0a11 75
    0x100d500c5039044020301b2030390710681c3d00640100000d0b0340807580b4145c007145a80745000c210355001040303c0030801140b07115172000415600c0b0000030340c0c0e0041c10007a00800350b051900410307030081d20101e5000e00b40380900203810039541c4c0b10400a00043d0000001a40c0c030b0703151605070304030158424501684141c1e0f50901850100384001c044c50040f40302c1d840c0c980e40d20f55560401c0c03405442d03401c4108540e0f03031030090006904440800d1245c1600e901c03508050f110400c072805c02070804016039520b030310140e04110421215000340c080a141d184903005941c10075580703440701401d000c10000151005074000a5080720b00030503125405d20f41d143c80c1003518440b0308084004001d10346500d1050820704c070020001410390340303140c0e8210066174400700a41d902d160400e00c40c1c1c040c0580301e05607510100190003140240c094107040c0c500c110010f0b55054079480c07900040004440b00a8039070310030703c0381c040304c0383c0c0001d1110001d0a11418102841c960b07603c10003080101000d0901444900d6500035004550 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 966344550 1250 966343300 966343303
    0x9030a110a08070602030403031805010f06060201020f090402160602030a0609180b150604230913081c0b030a030207080c010908030d0b0a080318090c0f090d151e0f020c 74
    0x20f412a070032200c0142c99580300c0ca01600280300c112503001192903122080001c1090540005c110b081c8000d005101103a91100c06134240e000303801c0c009400406c18002504642070941c0640003c800c010b2009010401644541080f41d001342d070307050b102c603843e64824012150750380150031001e42e042805080165041c0c40301c40419002411042200d000184540225079403034003602e0260021154014800003e500d01041da0010307040800e000781a401e0025840c0d2852100320002e0540010719285802550440f4800000784e4a544030760180d500d0300c0411043d00c00704006000c040c03194005040044c00c00c03e44520704217262230600d040141d46a02400307144808011f5403c0d400b100d01010801d680c040d40021300c0480a80c004103401e10003c41d0200881c42c5010800c0a100c000780c032501c0081d00c9101016005200e145e07240380b0403044c10450105181041e240a003c181d014032540d101c00f081100203441510808501521503080400c80c44507a8280e9104a041c00c003680340c021882c1c902911002c9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 966345800 1250 966344550 966344557
    0x20a0905041b06080f1b0c010e25060f0201091a0a0f0b0604140a03051501090c020a0b0705090a0f06050903241b12010b0c010b040b0901181409030a110a08 68
    0x2c1c05405c1d1400101d8000d90010304c62030050300403445003076121030303138015124024012105111001d00c02e4803600032003154000f040a00c1003080300c015082090070240150340e1030301072950f440115135a85041c04042000031101c04072411600b141c6030310034100b940851058a100300b007041c0d02c03145000b02c514510f680e8003007214101e5141c106c0784011000400d0010303840b4620b42d40081c109008410081041c0030343c01448074142c41203024208011002514104d130f4454601600030803003000400030504642c0200c0c09010302e03d078018170007002c1c1921141041d284003169403010b4046100030501901b186001c0c0701104c4030a00e401c0281c11b030003041c2d4103011091072003e00b075515480b000f02d6040300003601050444808040c182032141c0a540c0d59800036080b6031082098007469480c06641210038a814020006c2507030000704403410503420700c002410201810160305e0a02a903c101c0010f51460121205225042c00005152154058031018120b1510100041c8040d04003404040c001a50001038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 966347050 1250 966345800 966345811
    0x21506040e0708030f0702190501050a030b06090a090c2607050901050c01060303080105130903170604090203070e071b05030304170c0610230a1e03020a0905041b0608 73
    0x12030841e50078a8941e040000c40d0700314039041c0c000028038100d03415051005091461007a500038240d8007248040c005401000d020312400a0020004145054440e07081042c1440c0300901161411031a0000903c08010650200b280c50781c448100384034464010850000d94074070500814640042d032820360901c01001004172040c84004646040c0d075900c6401905d0540c41c800008100700c6850342070140c050f0340244180fa200380080c41c00500c801d00140606d0002c103500d13031200d581c8a54403078056002c50700002e040540241d034442c8a8005030b5001c0041e031009240d8548030035201d003050324000344801d4030710400080902d11003904c81c00050001089940c801d400000100124880b80c0d4105514819890750420620445062241036049000348404454520714403000f604c06103500c0321440d15082d405a644000801c0040081c10306141c01106482e00d050001d42400340c59a000855041071078020405e800d50341e901308070070040078001101460a100d2074800306203141c040000e000e068002c10b0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 966348300 1250 966347050 966347059
    0x120901020c0904030219080405030613050c0103050403111b0901120818010e060307051902280507091d0111030105100c0f050d030902090f1015020f1e010507021506 72
    0x10f0b050500c2032052449144500c00310b13000504a40c1000b038003541041c0140e81c0310380940030100398002012141c2100b0154068007600d1128030400040d0020040100240c040c007400b034041d000d4103070041c080d03811100346204040203510380583c02d00950b110305822160b00001c5d0415200c021070300e80015266a03402d0440d08450707121403140100d4544611141c4030b60030003004824802c000741c000014019820340083d407190f001600041c102c0e1744070704d0100b1415100506225901940d2010109110030303a004004807aa0103a031071000c07000f01d4407103035001d40f001d008021841120801c01c0c012030b01c0c1600000102c3e4119410000050ba100c030851400c42d080c0320400e4503100801041c102c2001c4003d402109942940b200e18030302801a1041d500304a2180350904002640c034001d207401e0074001d5001d0f141006c5070605202941091110085c0858107501c215110100500f004101d00d40313110608802d01c40701c4006144010b800d4030f101074101010354200300f40f5201c1e02c810100c03a02d50b01c14822103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 966349550 1250 966348300 966348319
    0x130302250e0c040906060815011706060c0f03070b09061806010605071b03080306280b0306060c010c020d0306084614070819061508061602120901020c 66
    0x1400d07502240f25542c450322400c4c0c01d0040c0090356a07008003115100706803504444520000203401120651a6521036402a03d070507808160786040c88006081010425022265a0800e4030a554655044000100c4a18a0708410014211011302280e900148810001e00303820001155554944105010762010444042219418080148088024aa90541c0d500c0d24583c407800e10340b042d03500c100d170010301070b0680e00355002e82842c02c0300404d8122195078404450345810710801000684c40600920381c04003060202e901002c03030a1041d900d020340b80390020203500b040a03a0141c2601c4003039104400503040000b84030100911014540f0196071040300e40200316050880b0b0264061740c0400c05072038110a00e540000b04807503501d50410441e50f04044641c01996101c4d850b681e0a11003c04031074a0071840c5042d000108a80c03c04042e80c40490300d07421601c1d4071000340900d804011600356401491208000c1003541c0c0521002000d031100e600414035200110002130769404143c41403900911450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 966350800 1250 966349550 966349561
    0x9090a170702060c010c030501060c0803010308030402060705060109050a0b0607020f010e1215090f240405010209040f020a0e0f010e21010e0f0f1b0f031005130302250e 74
    0xc00465070312580c003d0a81d03031180e00001416009012984483c03011a14000002c5411401841c0606195501c060500d24580c2140d44401150704080c0c4201d030030030018000d010020b0070030f21010303000e0301071903c1c0005e25181403405c8809a84401d8411405030b40104038050142e00c4401e403400c204102030030554980d0101c031003c58080e40c070584082c1018040c692203800c01c8000c1440060007294030310100c0e9040c80e0300b00225038442078101d03144581141002c2075030105035000394507158480e02542c0018207000c3c0d49000b14081e54004068405000da00084080d5080d4000c940c0c080649019604014070701c0c0721800103418403006103a0700c1c0c4224070f0660160007225034075045000c0713030a0390002030100d0b000f42c2d4015503941c400c081722403015028911240c8600300380082c445040940c011303110f05581c0b036a01d0611010700f0500701d00940501500529441c05140c2e805035a0050412411118100601d030400a085c01e81c20744c4012a030322408849000d8030120301e8011000c0e20501c20114007e0707200d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 966352050 1250 966350800 966350843
    0x14060f0a0c0c080a0c150828090b071d060d02090307080a08070b090607020c010e040e12190905060a08101e090501061125030c090c02070509090a 64
    0x900d07005195101c4200702240108001c41c0c048130a40c030039000c04070fa90303864451503414030141c0c0003d0000613404100181d2903400104d46010040381980810311101050460b010075511040c1050b1452440817050100c0b1a520019240c4c4108035503c82a0200644800190581c480e41c400d18040c03070f4000c10284601e98040c00180d004200d07174000c44000258a02c7c0c0004c55030440407040e9001440400010b030080b0010500a10419895001d8061000500010345003a035200a800d07030031a03070300c800640b903a0804010b0400c03080f86020886807180402000d55440d01c0c22558100100305540e5020041d68841d1801d176940a00c0a0a14407410758844194030031850450b40646a41d000b81440035041103441c240d04000daa103041c0c000e0149a0703c549083ea684d201d418080304059100f81390240624142c403005541c00c0d45688225403201d50345e9101c0001a09040c0c00010507540d98600c8041e9143e0104816402414295441d4005c0d141c81c181a43d01c91104075005013030345403401a0004074028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 966353300 1250 966352050 966352067
    0x1203072616050904060e011d07140313120e03010b040603030203040311180a02030403170c0d0e010e010c1806081e0a1103041101140c2a120a0c14060f0a 67
    0x140503004010172a90303904200043c5c2000e204501d0701c8420410000309445614030001d211b910243c484403480d1080c2c080c040e0b40c60f0300090003da40041000e1012001952619078005c0c0c4c076406680300d241e0140c04408040c03c5030502c01c001840780f0f02d051804c20010b9000b0050b00d0442c0d03088004003859074003040101c2c1da2649400740c5e0080c03411303012041040c000001d50145000764000c9e51240c03076250a450144451140c1614861090b80b4240b000c13591404003034000b040c596580000110301450180304075829501c4540c0c808020a41184070750088500e40182030b00103150310b207024030385824100c070095000ca02d403014550bd44e03041400004d00402c0c2e07540002c0f20003a00596069524900b60034240b901c5502080000c0c005000c4601c09400c03d01c5280a541440b110080038024015100e04095141445251000341a4080c6010b15005680366142a450b02e07416001500401d10a4508210000c819410030001c80040000e5041c81c2d86072001607130520401e9059242d0b4440389a43d00765440c48 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 966354550 1250 966353300 966353317
    0xd050109030c060509121b01141815061507031e030e16240315080a0c0e0907030305031909080a030b040207081812120307261605 57
    0x18200080181010b03802040003a034903008070300c20403481d190303426113945030406070f160b242e03404c013007032004900074401b0915090a03400c452000180443c0a2407000c040c2c0c41d000c61300e106a0307103400000385a5844050003400302c1d500040c0300701811450500001403150088058904101002061000416020302d80c204c1c007202d1071050006c0e5005418600030060b00107000004e0190043c1c43c501c180700d000500100c4155803600301f0a032180e0b0704080c113000106002c010003104254581000340b115016080902d0083e0841c64090624010366003001c4c2c9550030540d002c1a21005014204409182d0110300311080d00c1c1d0602d06070381d40343c4580b481003e420b80c0203a12044080d24122141040107080d44c010f000c14041510148110141e010401c4202d0044203030103000e11104106101c2945034421805140080c001c000036451001101445e01d040360a01000303242180010501541541001c14804808001903d6034030315050000a8a030303018010b449003140404610482c1c2209005405071034005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 966355800 1250 966354550 966354553
    0x40f030c0201090f0915090510050603100b1602041401081c0e06180f030c0f0904030c0819030b0a030f030e0103021c050a050717040f0807060906050405071e0b07020d05 74
    0x391170b890400300400900b58900d80c018031003030340011001680d00503184285107000c1c403045000d00d440c080c030410303a00040c900348550140c514041035141c0a0805404070303148048411308085007510500080383c1680d01c0d0900d0f074001d1603004120000d00058a01111078040c415140306050110b400c3e507824600810b101c0d071080340814203030281e0f04c111102c1003640c042168040da44824200c02d054999200111464002c09440707a407408600b489840e582e003103807207803070300c1000e1442980300d000881c2c201030305501089460342062a4031a0385405400d40c0350000f1106401000d242d40c3c2c40c12401c002c02c2c0001001d004040490310380c2da80c002c0c0d06030341ca050041d0840c462803421a0035140d0042008540340520545000003060300d1078401c07842d58030504012244c0440070785a80d1036a41b80003200394400c4504500401c00d001c0041c0f03140c000c1d004000e218200104260074030b0b1070710500340302c01d0b60002054001c0039004148800190407600d811203045130002691500c1c0f60020400c4810b00e840081e04e03e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 966357050 1250 966355800 966355829
    0x13031b1d19020408030f160203161404021206040e010b090901020d0509010b15160602070605010e090a050607030c0e03011401050a060903080f0a0c0f030f110105040f030c020109 78
    0x1450004a05a8410900340d0691072681c1c100040040c100e000b140949402c5900c10300c102d071200c601d264010302201198000142c801070b82035001070b00c0d2203003c0005000030343d0800340070420365480c4908458913000864003503040560720440f178058503500a00c503610560f107540c03401c18200e60030751101480c0e00000d818400c4078600800844e001c2e503c440110034116242c100002d006103c103105a003c1810000c2c244106854122420081604012001c00400101001a1000410070700c01041038038421080030840d585803140d40749a040005004000c076420050006001480c0413411aa100c045e5090000c0d07100d8088104550740d0071500c100e243c040d80303404542c81404680c0030807030307040300c8003140e45240c3c45444901c1150703250b5840c400101001000e0100401240c5410f000d010351b00481e19240309081c28075212001c100c82c26202c1a401301d82241c0c003000301941d00c51818250b18100f600240014209681c8620502e14820340c0074080121100400c811a845510707100e000f0300040841070341 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 966358300 1250 966357050 966357089
    0x618040b0d05011b0810050103110c010504061b051e0f090904050f0c1c0803070c080a0309150b0d0204050a181209060f1e020c120106180213031b 64
    0x91080c1c81020132440e0645500c501e46a101302c907014441c051344502c0c00c03455403600c00158050030200542c044058001e11004064401c02d100b4148260300603040070440b0800b940c800100b60b42001c98902c20403008100e000485600240c83c00d203100150034108ac2d40c0d5900300c050722220b00a4070300b40780d071082d040130a00c030900000007441c544442c51801500d48101100041144184001211001841c0b00c3e68038280820003040186074011910308100b91004566513900091f13501c01210240400c1e0baa50700030f42400840a1000b090300000041045045c00142c00280b24403400b440007441a9114400102d0344000350b000b00c10707044d080b80d8a8800c0c454041c5000000030021046590004154440000c0c019200300d840c1c09545c000b544411b101003c801d11410704200c080344001066114600000300251151150172501c5c180c503400006880341403100550b00d5482035402c100c4224010301c00b07541c903031141c03412007070490b90700110365000a003d484d4440003264080c1c0c011269018008000d11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 966359550 1250 966358300 966358303
    0x6090d140304180c08040b0412020115060305040c060906020a0204050c070c0b180108060922020a0b0a110a021807030b0a030c1e0819060f0c02010213080307020618040b0d05 76
    0x500141e44400d05101c1341940d42c00c2103820303035000c036000342030048050045008540079242c0712441691610010520700c45010004101220551000300003a907200308120501200440b00f1001d0807581c40c14030000d80c0b9045000b90b0311848408042d128076079a201051411031110b08451f0307280ea100b90101203450361140b04002a82046c1414409400f488005038042d41c800c9494900c1500014542c600c2e47d1115520706400c0c041c5444070885032403a0305078100c0503988209000c401002c0840c41c1d541c1d1041c01000003030031420a0141540c1e00d134485465940107a503144e00510040c2d4109059400302e582d00d4104501400c0c08007010758210500c601d0100030b0181d129525010340d2500210f00d0102800b040f83c505180260784948011a0841d8414407080c003504241314a58902903603001c540c100e483d466800840e03407948540c80140c0c1d400160f500400f02e15404640041c505a009542080c0c400c0e00452034a1003031001ca00e1000d203407908402e00719565a0701c10450a80050481d404640e068500303903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 966360800 1250 966359550 966359579
    0xc0a0804030b010e0c0315042c070806130615030c090b090c03040510050c0d020414030f0f03041401030914010b010e03012306031e030702090106050906090d140304 72
    0x82d20401e03039120010950440d0890058016950200c0c00c03803035641c03030481d00b0021a056804460784035449448480b880ca02d10039403138450101108070341c0d1640383e00000051612446034085c4045030009810084060b00c84802ca0b0741e081c1c0c000001003003480d058480c482c42e82605810007000c844a510b40450345c1c41490f808844a5a4152560840c43e203a86055a1031400100c600034555070118251030580d100f17507049140c210362010400c42c2840100c035506402e0740c00541007040303e034000c00d0000e140351400700048011034030780b140500074145109003c80e44a2042d409000350324922680c00c000664440c1e800b2040164105001e0b4017549105017126028001c01d5640c80c0c00035a03481c40c4540c0d185010b03c20032070021645804d00d00d100c003421034600107408008103c2a414065200001047d00b185070804071041c60301b0300599a030b5402481005000031060700f141042002c140500e108035191902203420411084480d0080d0f000507142450f004480040c4155540c000400d0014400d118015075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 966362050 1250 966360800 966360803
    0x12c0a02060c0601091d100c02011107060b0312090901060f120203190b041e0f020705030a02070e0a021e130305120c010f0c090302060309010e0604030e03010b0a030c0611030c0a080403 81
    0xd0148200c82071100c0c0341c90341482200c102e00d1308102d901405800c000c0d401403a82381c04a000110b00f0481d150140c00441e000000191480e42c2c40d0f401c0c1103040e1409119020600390101d15950a1440010110b0a0302c1414003030b03501805440740a0392402406000c9038024a0040c00c03080d55a4900306400705000d010b4001200d0f01e680c248144034640346854004c4260880c1050103400c41099583e402d48080c040e000d030f01607640c82d400c00001001c42e10078001010340c11081d40041041c00e1400e04a0704000ca001800e03490814418804200d0403140095000b1862080001181d150001c0d03950400070300806620013826842943c41c04480640c0c20f001400002290300004c1055440840580302030340c6404411000107140c8800510040c0340105c082c0d5040000304c1e00019203094009100741c68064140c8050b0040b5403111880c103000d14007409005a4640143d56007005945550388281c01d95080d8020b580511040e81c9000060354401c00c00c0d80c1610045004507030440f542820f002400c1e074802e010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 966363300 1250 966362050 966362069
    0x307050702180c191e03020301050a0b090d030c050f100b0f0904081905040e1f091a15071e02150406021f060504050a1d012c0a02060c0601 61
    0x10b00040c225003000101e20400c1c40301c10103490400200c1122403090500a0504244201c0300040000707205852604030300d4200b291401a901d5061008102d007069940d4440d03c2814020401e030700c0d5030703201d40f0b0316032040030b602d810f100031080802d2401604000e0b4040c890030035481001e60603820303424150001da4003038030706441c00c04c0c4840c0d200e028004000c40849010b03050623010070160084c150080303c0303610602c3c0f5500d04641001c0d103e10840d111044e0540300ca424070b05c210501c0d06145915800d00f140100303451082000265841c50105040080300d16400d445500480c8601c500c141081c8101c03540190700140c10110303504416407080342d00b02c2c82c680c03c1e4058407840211181c9410741204650030307141280c008084c4000d820111401c00740c10080180c1c0030071b4a8050008494850b03002c1d80380184080759000c502c4280000d01c00c003280642a03080c00140e070500218242c506510011003107001107a010610400074a050b8480c5070940c6031703800941201000075520101e07440070956178140e4201c0c1c60f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 966364550 1250 966363300 966363319
    0xf0a05060304110a080a0f021507020909030306090a06030f0323070b0f09010c02070e040c0e0106030902040c020316031d18070801050a050f061c020a0c0c0f031a0c09060307050702 79
    0x20045940c51040c00402031002468247c0d40c0701529080400040d002c100c5030300c4034035115059020500d0340e5030503164540c0592000c01800101d00d003904946500480301107080110707900e5500d91340b100c6100000050700340001c020401c0400700c070060140c070300d500b0601d074010780c0d600440c41c0c100c582308000c444c1400200c0503540499413020040c081e15002c0d0100d540204109400d013600d8051000b0003800c100c1d02250340764400140387c52034802e11402005682c900144007541c40c010b110684001e40110703001c41d0070800c04540d81910544a1200c56a050310f0903002d0030554200ba504424031012109038400324040d4241a24114401e0b00b83c131880d11507840c1841d50341d80302c0a000c2c0ca07500d00c0c003806502c000c2c1841c280d00360b410440c0182142080d802002041d41000300013040481c0d2101c0d4501d000500203607440001d00909c003c51a00502e038403451071030628556100c594080307407100d40070022500942d02056020910318191901214014401640d80c14041c20280c2a58007040e42207010302d5820 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 966365800 1250 966364550 966364559
    0x170a0e1029151b01140a050106120507051804201308010e07121b030804061709060c130b030708040b070806091501090b070c0603060b0a020c0f0a05060304110a 70
    0x100448005021409000f420708041801c00e59003c40c2038011001c10350f507142c0990b0010742540391740034001c1c0d9003030078000749950400d81d005012030703417240307005580500f000d0038000d00301d900904880c594440880c04140c0c1c1035600f4006406005000c0c01d0800301d851a108491205940000500b00c440b181000ca4012640e600a40390907106050190304203a00302c080104082c0a03117047c01e40884c0c3c490021023040240510707614540361410707041a2400d840104007440a40e4110041419101c88015071003031072f2501075030869840d980140031108425010078491030341380c4054000740143c01c1a05000c3d449182c450001008200119070a5820340020404101c2e40380c0201c030040e000b0721003e0710b82a8240c0e01d400211007241c1c80c031410241008401540058901410000752201602c5512045032030351070400010305642d07482d0480030130404200030300306980e900000d9401c00c10380250341d070003a01e485c10000108403c0550f40026040040041040104070300441e0815948008940780c5410350b884 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 966366906 1106 966365800 966365809
    0xa0203060121061e0e04110d080301090c09060f0203090919060810150b07060f020f030a0e0f0d2309100c0c06170a0e1029 54
    0xe59a003442000f0110442090b000140101004c60a09019101e042e0190280005088506901145c00d00b5100e02a4507844943c01884941d265a52a99101d028120500b010382c0050b40d035940100f5441c0c0141903ca003400c4190f0300450800b107119040c8280c3d204007130442c040402000f21142107034000c40c0503000252402e02d024107108444121b041042e9807030081b64241c60916075805100460b410425a201c4c2504040c02242c40c40381d900c4c0000c000d1288903420001103100004104500c2402e0f041310300d6101c0000b08988008502c0541c540c0c940c0504113420001804032202c1f41012100c5240043c803105002444901e40707804a400500801348110803030022600c1400000c040c40309010b0840700420442c14007840302d07408404600b00e41030b40140040030305503850440c00c1024104110790b02444401b00000c0115088030b12001c0c1c26420641440c0c0c005c940c204446580c2c5041 = true := by decide +kernel

theorem cover : BRFrame.Cov 966187050 966366906 := by
  have h0 := BRFrame.cov_init 966187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 966187050 ≤ n) (h2 : n < 966366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
