-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4122
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:37:50.277277+00:00
-- url     : https://prove2.me/submissions/0b9a2e7e-7d5f-413e-9574-c51d764b0f43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 741187050 ≤ n < 741366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 741188300 1250 741187050 741187061
    0xb030601030525032a09020c0c100513090914071806050103050603030901030c050c012c0106180f0605090405031e030c1c0204030203030c0a0b0a050f040b06031609 72
    0x20066500000f10305488921521000303400058008050454207140c9010f078650404038200d40408619040c0e61592584016a803108a840019500c10840040f8503d0701d0b41c0100d10040c0c00c2e090040ca0074001586d2080022001d105010590383d41300d41080910001621a1720300001c0c0005071001e45403241c8914041d8400c07102540c4a1a213000b601240e01e5000e481854010400280110705200b0020300444c0607290300001c1804102c800d11021000d400240039642042c40b9069000e10314802d5152031303400303048440101041c02e83c10298200301c9002c000c404a074403155244804605842107400d030380040c02d555071080360001c1260003008248040440a41030380c01c2518551000c01001c584202c0642c00169040e0281e210200419854100c20070b000c071140415950340981003070350b6a0002410360b0869074030072080f9042500a103080010003800e041c0d1051070000200014102600c842c0034016000f400240341e00d4007107010441d02e5030b003001444200308060f0600340070951281c100002401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 741189550 1250 741188300 741188323
    0xf19081b03010c080103020402161b06080a0501050a151106070306140a03080f07020109080303010b1201060f0c0b0411091501030c0203030c18011101020d0204050a050d12050d0b0306010305 83
    0x240300e4440140103203010f00846441d0b0340660b980143c3d0741d00f1502008000d5118000e0324161140c0c081c0c03c43c1c0021600080e07090140386514070407004074a04840944244002810501d650f031410006001650314181c280c01603034207000d200b0303910101c400410380c2e258509001c01503080c49804100b0070790980c9900200207550325104001c0d000d05850041c8003c40d88140070040c00d611051225406070700481000d0031099005240c205441541d498206003582d00a800004003c06c0000701c10080c080a10381c1c8900412a516100107403020180004040521001d4010108452400481c040c00340c6c00c4200a034041d0300501004182c1003241d0100714000d070040c0c002e07010074140300313800b40c000e4008810f60f4804e0281c80d803420300d020f01040035410341141ca02e03485414042c003609100f00b00c8030244042c00d5604190707940140d90710b06280421520001503031200e480b8081c00a00f01d40002e02901001041c4000c034240345484025812088000c0c00300c0b0201c982e00b51003508000410b200300041c0035513006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 741190800 1250 741189550 741189583
    0xf040e0a2007020a030803100b03160f0903110607150c2705011403040215030f060f0627041d03070b0124050c2803020c01020303010807050f1908 64
    0x10070000e030721850040500c0a544451100780c1000810005030040d41d01002006198042d5511942c0924640e00203a5080c1c00d0025120428820aa001481003090f1909820243e01e454515510079915041c03004010f809920045502001c1025020a9022000c220780c8240042c02000f4002010b4400340c55011101103590401800030f500e26102220a48806940e10415449000920035607076201a000300d801861209941000503010000b6600070100300d512070000b41006002c01c1404601c0310315a42c8960740401210792a940306143d03c620241507119440001c246401c002001401100140c0b24140d06d548000c11040c42c000c4001e191047c0f08841802050f621540d10f4845098500d2013a0a400034203000040300c0340c0200302502500c101c80c0111600302c40407545424610200c1031101044419040c030384420903070140404102010203200942c107641c0b6281003290b441d84184541ca006000c0d0b8a0144119181c0464411851180b0300d1441c0c4000d68072540b480e600c444030400c00c01c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 741192050 1250 741190800 741190841
    0x7020a0b030709090b10030207050c0613090b01080c0a1b0503030109021209012c01090c090608011404051902010c0b070207061d0f060a23180a080706050f040e0a 71
    0x81d01135104541080502800120080c40300035810b50095010000075500e51054000d03034451a515400140745505500c0c12980240d0315000304a0180c0303104182d0107040c84940700800c041642c1c80303803e40341198140e10b0400104c039481031107000d60380240c0e18040c5c0300d408000f00101d000c0d001a0001c00d0b4103120016118143d944107070a003801ca5522880c0d401c000200c0e9000e001207c0f054148084407034039201c0000440152907940c2600e05a4250321003500305840d120100041c80083c8503005001e4510f8a4001d841c0c5401c2c1d48840d1034240c05801c85161905000e00b400a5900c501940e81e03499910080b1142141820f0b00080d41d1032030b007071090303000081c00300c1c10000e402c0543c429014040310700680000d00e009079001c108180c1e0340001c07031910100017280100e100f9940703d007199458104142d24038281d4400c500090b0361021843d1f14452805116244410003040800080b1407085494031319085440b00042c9140316050b01c1a5880b0800000008003403080a004036800700c10350007103099071041c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 741193300 1250 741192050 741192059
    0x120c0c0d0201060305030409110f030a0b0f03010c080c0a0201060801020f070c1a0406121b08010812120c031503070801050906100303051b010b030a060207020a0815130807020a0b030709 81
    0x361000d84c0001002c9801c1407004004e00300507500b0180380aa02c0405071400c00d2200450413949030800c44440c0c82d01d5407a008001c2c2c55003044c1c003224000d01c5c0160700030b00000b1203001d009860084060500c0c48481c00c00910000030f14400c1d40000301410a2000039551001c006096101e1500002c0068500c50721a0000080d5005006071010b443c040680016007058070700181074902d045d019000601da562217a03200d00c2c0b080c015072070a90b51510180c885a01c1541004116883d1100d181f608692521041060352640382401c0011980140c0c5001a00d41e40d070354101030140a1582c03041583c1c4c0610450201091560042d003147d8801c0010400301c0b90741380c6d5408041405003000c0d11010300480d10402070300d481c030401c0b200000c8000440303e0002c0b0b04100300e103010910308509000251103240d40807402c00118070b030040d5804003c0c03180b0001810a0a45030604600320300010741070422500c191340c4802d041050b100180c80d20540c0050a240d9140d544d4910751903141c4c01219600c0010318070303200c0400c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 741194550 1250 741193300 741193303
    0xa3003061d01080a0b091504050a0303060515040306051f030b070f02030306010906030b011e0e0301060b0c0601300c060225050f0316080708070b03070212070206120c0c0d02 76
    0x6049a043c8402054807505686582c110303000082c3c0701240c41d002e912540d06100c005555680d0096210ba00101b0058049050050880d203442c0c219500c90f8400074694901004044151000d69811950000e060780707036120f040c642440e0414074030781c04030602c21001060040c4104c10030311581003a195801240c04080c0101d840b44000c459440c04101d080c402801018801c0c0d100300c4a040043c103011007403c040100403900d00e145200c030701000400e1142c203000c0900f030a000e0940180800c201560030308007580307030042c3c403a901401a603c80f45803901180078001c146010f0748501000c10038000340c415150b8100070355201d41c1d40c016a40944900385403452103080e0700103d40c2101c6003080001034143d00780400c21009090000b17005900d841142c444081c030001c4c4003000e900500722440200301c414a0000d13902e0030010281d01c030f810030389414020441d41e1038010414140c0e443c11840000d43d64179091001030001c2c080c484e040303001003484100700710310004088000c0c00009815002c50341201c1450000701e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 741195800 1250 741194550 741194609
    0x150801080106061b030c0b0f0a061a0a0302031b040e010501080105060903210f03010906031211030d0b040225030311040b09120a120e1e030a300306 65
    0x31000036404d0710710540341c2049403440e110014801d1a01031000a030b5600c0f01901d220007a07407034181d03100d04030090009640d01c07072140c00002c0543c80145c100100fa040c486107070b54081c06406505041c0c00000044401e044803819022a90825000585a5444001548000009004031400b140d01540089010b14246003030720842e48005000700803d240042c0582080e141c0854420005c01c0288030343c0001409001c0590702806904400150003072850420703401d01c0f24150214028400140002150728070007000700d554015045001042c0c0500c1800403400030700c500459002c510100c40c021411072080c6c00220b1030b0b5180243d4041c04410b99a81d8550524425072080001521040103018500e01f425014050002d0080d000d03582922407030303200c180c5082d580582042c0010301020401d4564074010328107000c103190144030500b890076454003007a545c44070581d0184c84c0c151010808100c000c08201c5482c403a0035180d1144c607020316006801703409801c2e54044c40034000000d0b841d042811600b036881 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 741197050 1250 741195800 741195809
    0x10501030b060901080c011836020307050a180504050f06030f0102041d0606070b040503030123010f0c0c08101e05070e010c0618030e18101806050307150801080106 72
    0x5444050702010065038440c23501c4100d40d4450040301d00c000307901c3c1440e08110840c01c1d0941201c0c440308900840446141d01c0b10f6031a01c0c00c0321f00c14402c0c01110355000e002e44403014102d080c2104000b83e400c2c940ca00a45540c0d00c8264030a05210400100b02c8c918140dda01071003064084508040c006007a160903030249014030b25014041031762141d855132344080543d401c0751015010381d207010041e46503d04243e5085a080d07074268800001000b5844050380c504580c3c2c0c0312150b0350000072041c00c00080100e010002c0c46e41c10001c0d42450107090180d6105000700906089044032070b203200c6003590030301a180e0552039444c801d0044204618100407401114813402a999507441d266960000541b4a076114a0042e0303085a035650031000714517905154400c0c030324040d480300440031403000200203041c084414181d100d04000c40901c54845280d840394815110000351014083c0c142c0d4005c00000d0150740d01095040c0302c0c501c800500d19000d01062408990507555040003aa210f40d241400c2e100507124 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 741198300 1250 741197050 741197053
    0x1614100f14100b2a0703080a090e06090103060207031b1b0e1603020705030705150105210a080d0e12120f0708070f0e13060e0105040612060c090512010501030b06090108 74
    0xd840d90700d0b03c400740c107045404c83d0a85000307980800c41c84034900301464100b110a000c0014503004181e81191382600105031142c0e0b640070901c0c0c070341d0100e01c9494043c0700003012141c0100342a400c041c0689849030b4002c4100d40d45440600b05030038a0180620203c2610004031084540410000e000d8400c0c81c0c4254803001034091079094100085000f90321003031095580c0d0100f0300c5002c0008109200c031507044102d4500009055040008202000b55410400303041241c0d59400c03118000c0707010400d811030640064010fa1140e0401c6161005401d00c0e09a441c00ca008040c0c400c184d0300f41c1100030742086c4003a10540c00341a0307108920210094070a540da100803911071800102c9140c07081a210648070024984400007500007030108001c24028045822000d46804c1c0a01c10b203050210210b004181c00c450602000380740070b02c01c0325810351044028100e1070312002340440e080d0054402100030880900940c50007400700c1c005600800d428002152060840d0b0302051492611407041c5051701e24a10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 741199550 1250 741198300 741198307
    0x90c09190f121a040507051f0201182a052e110616090f1511010612021e060708070b070c21091e090509031614100f14100b 54
    0x4101407081d51008000305c4061155140c0411561605040140b0807800c0710044420071b800140c0181c01e66840d484681420403003050100003058081c2c00110700c1c0d070443c1d2250300c4040f41021004800c41c0542c3c0080303130800c0c2e1052541d2071006580a00300810541c501c003107600894440c000302c2d02c0c000c01070040395140e4080804910401041c034040c0b400d4040b00d042c60a00c4036910318445424001642c80700d22300010702d000c55103c0b160003040c0140301044110080107a5401c2c016001180d1000c1c0b0800380c05800700440e951842546444034900c0700000400c101d45504007031406074440d5000c0a011a128803181e004611100c0c0503100076400b05a0250812448443d4044440c0e9203003c4202c44104201c40c094000a07241c0c40041d988408900340d480d4070091034280b0f2580d8050707590140c070b1344a096000f002150b50018101c528001c0a5078040c40c2e040309842c050740618074003401c00c042502c40c1482c0090309001c4905941c0409440c4043d503503003101e15a1100107030307021407403103110b0046040000c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 741200800 1250 741199550 741199583
    0x727180515060f0a1107030b0405060a060b160305040305120a1101140112050a0c0e06190f14030f031303021e010f030b0a0803040b07050c1e090c09190f12 68
    0xe82c003800d6408014071709122064103440441d40317804442d40c801c1d546016608140000d0101c1440710f2030f400300080b0b80c103202052030710203080114421460142c00c1c094140d942e04040604c40c0003107038002c5400030f0890f1200d540858860786554003a0040c00003091001d0101504a8410b0041c2400309590304003140c1180c2c60200380100c046e800c0e080840b598003a0b01800c5000840401d04900a800d16186024840c40d082003400807003684e54440a03d016074080080000681d2a6685029107440114910492075200c000ca81340150b1313140000881d010100d06a00080d600e01c0004080340e00803aa044c0c2140000550218803c00040c400350000d0110420340c042d00d40290440300d0803040190404154698601e41d90313095800c580c05c0a402018001500c01c1070100c10044c004120104507080c0c92030200d0383c011082c01e924186003031030085c416900010000340560b42501c001c0703a00582100d02024050710308146c030300103500401c00e91000d06a0007180d01c66072144411001030b4080c8030030810b211034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 741202050 1250 741200800 741200827
    0x803030a0b01140a0c030309050604050a0b0c0c19020301060314030702011806020a0f0203030f0a030f0507030c082a0301090b0301060906061b15090b01140303030609072718051506 79
    0x40d030001b64141601c41500700c000940c00c11103640310310b00a5001d071203800c07042d02d8800200d4a002d40240030024061101e4440940c010800f07a00042c010721a55520200c40c4c070110b03000d0540c07540041d006201e0302c1307069400440048014070f0303414800d98501c01c03140c0e43ca201101482c1d0490043c000103074018030001d8005901c1d8919402c0b8240002d0031241810716951243c9a03d60003220352100281d10340c803010740d25030900e004080e0030001ca8141800005201c402c018085035008003c40c1041c1c00101a0107aa0001814000c1c2440c0000a0a56881da141c10b02c0102910001c440140250310f0040300141207203140c41008182c815039552880c0d80510004004440348080a046d0344680f1104134040e90398400d80f080003412845a0000c148a626020082c82d8240400011a019410410422a043d44d4201c001c542c0804507040000c9180d101c4032040031603201c1015280c06071111070310045035407001580011070402c9400407c1c40103a41f40000803d10304014a00c07260400000e00224003000032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 741203300 1250 741202050 741202067
    0x1d010302130f0803040512010e0d050d06031a0618070503130312020706051b0715050a14091c02010b15030705070c0905180a0b041113060803030a0b01140a 68
    0x201001009070240d25030840454406a90303100d07069940c8005002c0085003070910861f05400c100f40020041443c0a10342152251300039106002000f0340001c6207041005180d10000c0615007000c1000c1602e01c0c0b114484049070704c2550303050b1040004030404401044000b80c802d116000c2c6030b4a60341103403101c42e0240318008401c01c0880c10b2103210107048030a000c451000d0000e00740903040c01300b000c2c10301142e0300c0c1c0c0c142040c3c0c0c00f01c0c21501c000c10480c1c01041380461008120640c1d00000600b50f80c629040c80300402050b01458642c18102c5c040c0305105100044030b88540d401c407100144074a007003c0d810ba00702d0b18008107130303a000350800031702d025000c0d1035001650380b150303071424035918104841d9124082d60340c15070007044a0a9840c801d01040c000c00d41450114501c9207001000040b0107038480d105e400074020001081c1a000c543c4440da10744ad42400d040001070310180034040580c944030515140d4104503410b0210394900321059038150700c541950501020042e11040c40c0035280003007110b0000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 741204550 1250 741203300 741203317
    0xf0d110c03300c06100b0703140304021c140f15011502071703040602060609070503040b040203010204092901020a1a0702010912020d120516030e0a0203030a020a050606011d010302 79
    0x1030b1520360b6a60410b02e98002888000e0100300945420f19007881152824201a0000304400c0f82c00c2c002500043c0c0c1103807907180e1042c840183c00c0d031683d80d9171001030a290384000001e030444406405000400810101280c41003800300c0070b5425107142c1c101c616559010260183d08050208001005807020a4051003207440c41071055842841d20366107400a9942703100d100e41515400018100031203a81485a6a0048003c482d03002c4581495400103000d03000c01f90014084080d1070020508665003503041303800400d01c20b00c05001034025411610407020000000e9540e01c40400203c01f032541c030101d0b40014450340007440104c9040d04404c0000b07011002440f5200b59035903024610046848800d0560064440c1e50007094607410a0a004007008000b0000b44852400c2c041401a02d00791880c1c40142c0b241c00e03280000d001c0b45003042030342c60300500481c082d40501001801c0f1807403d5000c900e840c6060300920450303c0300c2e180e801c01100c42c220080603100560310760007803c1010b58801d030000d01070030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 741205800 1250 741204550 741204613
    0xc0d03090620040f1e05040f0b10030623030a0b0711030313060f0b01050a3501051203090105040312020c040c03050709051e0d02120f0d110c03 63
    0x1901c0b01854602d20060650500e50000808030b410814800c000701028054043c45004200e049450076080307220707441034010b2511450301c0306014003030081154070041e5945c41c01000c0002400040d41c01030024082405044103001c6002c4030074888081035031200c0c0030303440058020001a62162612018100f003e403038101004590320117000e81500c1040514003440d034004980035808100d10703140048901201d03003030411034140750501c41140e0700b100a8a61840190905240c0008164020000f040b0542d411103541303106541c6e2000030031350b5201800c0c1654400c3d10280021241d0324a107644d80d009035a03210b800240c0030442880050310415254044c030b0b9450040b180f0b038400c20400901a80c040d0582d010009070750b0010808920343c48120003004100903640d901c1c203100043c0304d0700342c10741040c0c01d403602496a0694650841d101da82501ca100804c080c01d40d0200d80d143c0003d90340b00c00c807000500c000a00b45001c050b5081101003484a00c0c500e00400170800310313401001c114080040d414554004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 741207050 1250 741205800 741205811
    0x7030506030a080304050102030a05070804032c03160906060c0807110a170d0318022803080406020d090b090f01031e090b1902030702060c090301230a110c0d030906 72
    0x43d0101018501a43c86800003584a01c0c0c1508540201d842c014941400c00500a05000101b60010540c3c00300f6980c95005002c03c004082e800094000d00c281215058801c041e50900407590320802002511302c200f0080c0301741981c4060484d00c03800e140d14060001c080c10802800020358807490f0540c0340f00054044800d003651407114054040c81441e00c1c1d0b4950f044401c90040341545882078804014210a200404828940100780d80802038002d140d41c000403054000c10011840c0c0c055001140d100c09a10741d12502c45c440291107105081a01020039017060b80401d00d9552441520203050010741010169038005c40110043c04002c3c0340c0c490751924020342901c0815035806085c04060144680001303500b030400e4041031501c40c1056484030540306000340520158003041d03080d0881c02c00498107403a1a1705400103401000041180340c1c07840055040c00076548592800144908410481007110981c18454141603103ea000200710356001040e0500c0a00c1c000d0748044519030180c0400603c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 741208300 1250 741207050 741207053
    0x1050a06261c051306051c18140a031404030305182d01140f030f0403120501180f0b0609060f1303060b090a02122707090e0f0705030607030506030a 65
    0x1c00b4541c100801d000910005007000081d01c101c4004030041142d4900145442c03d04c50728040c02104c40c54154680036141c1420f4a142c1121012095174280c104080d0040c207c60441c4081d95000d08060847c0440e00e681c9900d0440c8044005490844e41c05803105031502c01500c051201c0011a001c0580d40404c1c6a104202c50001c043d0701440e20381580c8410344e61451171440050305c0d00d90307401d4503250451010003100c402075084105803074101804000f20344103034031185825921001c0082090810514100000a2211040c83d0090340801c44100401070b03c00680c06002c02e550603100142c3c0c010740b04000c1c100890411700c001303200e500325401d003640c20321100440718600d00c06154402d80b400d0ba110218401e440c603000b5156034104030030f034204619251031044545a082c030300171b100010b952107001c55024031801030001c1c0c1e100f8841342c01c29500d5054a03001448024502c03001c0055180c850461108504400012140c0940b100200242026a641c402c01c4001c0c0000611035074060007002995030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 741209550 1250 741208300 741208333
    0x70906030323131e0902091c03050d0c08010311030604022404080f1b18070e12030c0d08011710020f1b2a0607020415050316050301050a0626 62
    0xc0c060000019400303000501c02d0508400064108280f120720400001d42c140e9106c0c1001ca1260207588e80c200d280c140315050968990050703010a039200e904010703c10319403d6000903c80c0c1680d110b8062000c1c81c042403424950b03911800c4800031340010922440021072484026401c020300b440b45503941c9000c0d02e50242074100079014622140300e61101514130301d00e000c0360481c4850071009032408d0300504002c034030000c0841c031701500d181c1c140040d03202d01420684501214144022030103080702d69039040e6400a03a40c0740a0851280e000460b030f500080360015141520b400714200c000d000384442071041015000a60001000c000c034082d04015050342c0c852001d44400c9003418505c060704c0740e05115104000c54441038840311100c00d65240302d00c40a5982c04060301c0e2071903019100081d86445074008900b841e807241e00500c0e49846900c4000307281460310400c40042d00d0042d40244a181c40340003034402a40c8050003801c030031215100710849a0741142511030b82c070081800c1100c4440c003440c04c40c00b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 741210800 1250 741209550 741209587
    0x6190305031b12120603010f090b0604050f061e0307030f230d052b02041412071a210f04050d14030a0914011805070906030323 56
    0x100da4682000c01c4000d90000366101c5455840a1807001c0c044070003001511119901c03038124003903011220f4101181a81d00e0944c44520700d00d40c0319104208200b154281031020031411583c1901c51814200040c0c00710700720100c0035014040192030500381c01000d10400791250b106044a0b90144522000040403a80c440030282c0214090300c07180607100003480f01c0d18039a03402d018043c0003c0c0c0c002c1c0144007000d0303840400c80702a00100c0e10f003918400c800f49080d1070242e00004100b080280040760100c0c489030030080348902d40c0c60445e010104070a00b10360341c41d201d4405105040c0c0703042c0040a440340500c1031317000a04070b4aa40d860000e041c1d100b010a1f0301c0c0d100390f0585140e00100041c104200810000b0400150000c6c0b0764144410340c40101219810188002881124500d440303421840401141032a200a4402c01d200280030903c9880403070b11400b0340004040e110f900c2010307000580c250003445000c0075240c2541d42c000320f598900d90501606c4546060f4120504010010006010828001d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 741212050 1250 741210800 741210803
    0x70302030f0907050310020c0f0a051b0904020906010305040f0b01084b0106080304030501150e0f061e120a02120d080619030b010905100609060c0209061903 69
    0x684908065010903000c420041c0000d2a9900c0410f003400036640008a2210f94400070b0000350303172010000e1625040c0100160341030b0342c61040d0460f0500300f20303020031004d80c1603e030007115840c8007404400f0071031414000da9011390041c800354041030f0554460741201d54058000c411280040c20282c1e245804101d09a0141b14160801540d81403a074000929440302c40c80b50310310000741903c100c8401d610f0040d8800f40724080314454440341060035801e4003e80000c0c03204905880d221552424154003070202c002810607480740c80c0c0300c04103050000c0e00d80d0b1401180010100072055407120709001d40124152401c821000503410b00e641596590b501c01070417100c1d9103020348000c00c491300c14070207820a5080200c1540c1c1010000320480c42c3e1041c0c1d80b42c0e0140003240d207101074502c2c0004407079074001b543d040504a403c19100204049045410190041c182c508118080c140e50f907030202c440c4621030162900042e8954840c002625141041d50f0300403100600e1f448006032800ca2010400d207040c0c0c030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 741213300 1250 741212050 741212057
    0x602070b1f050f01271a090f0402070f080702060d0501242613080c07060f03060b0d0518010204181d120d18030c05190305090f130507 59
    0x39031aa180c221141041c0080505848407090080200c0001c0c0c80b0492070340303075843d0f0451100c000c980c0114480e54a00014503502e5841d945030303402c083e18101c1603801800b420340100101d4441260030305151003141d4940d07400201c59415600306643e001000c0d4004441aa0f2040003030180034030342c400500c511802010300d0714031141c1d00210703040005000300903d41c4020600c558002036200004049401c4400c000c40d00081070030650320146c0d00b00303000c0d800640c00b03000400007207400f5001810000712042902e02d552140d110440641c0c031b045060780c40743e0041c07070315011040c80401c12440d0f05401003038000c5440038410010101c04401d0508a8115511900721240114101c07607004241d44514090b44000070b0f00540d081204042a9946400302c10004119850000e45001d80c1030700780c2d0100d001c641c00d41e4004140c0f6a480c1c10020f024504800c000c0c4c42c0d500440c81c0c2418080c1c0c94280c0e2580050703141d258141804410802c020200d03941d4006030303070000c00c2070410050b0004944a124030a081946 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 741214550 1250 741213300 741213331
    0x414010302041503020f06090607060204080604030810030c05090c090306151504050a0302060306130c0f09060302131503110708070b06010203070b060402030411031e100b0f0d0602070b 81
    0x4100903034800f81090103003111203150920260312500311304003201d081560515a200d05c0503002c282203100d07800340502014804a400b05a2a50108460340a035000b03a071010050b0711072081038242c8005e03500c030003410703400020310400090501600c1b240d80000c0d00c0d030170705040c40b100b100030a00b841c1040b140e103035085406580c1703240b030b500c0e1000d174215848600001041c01c083c1480702064881e00d0900010b4440c100110005006075500405580c000205600c2440340300e26003c000342a004004204074007003010124049003940c46842902d8042004034100c1d00300314a0481e00a00c0710501c0d0511904241e140c141282003006450010012280f0410b40c00d40d03503200c5810400b075030740700c00740501c2e0464004200c000c0205942080407600480215401070380c070340b6540380c5400d06034050442a0340600840c1c4040c0d50b25406100390840c0180d966090342e9a8060410801c4101ea00c00c0c44495030107000f10318002a2810200307219500e885c03060a0051a000241c5c442c0c802d0f225040740d008070300c4503600703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 741215800 1250 741214550 741214553
    0x8040807120e1002030a02100b0427020f10020a0b04050f1615020c1003020f0d060b0715050105060f030c040f17010f06030c140a0306051914100b0d0b04140103 70
    0x841001d0303030b49031441c0701446c1400c08008000751a9048015503500340c03a02c41e64400320b00e03a41c5a01100d403140c9010400c0a9a8610300030030a4542c070052002c3c0d04c42c00d44e4401c43d11103820034601180c0108029400b030040d0010f603541d010110300c0f01400541e101e1103024001d110004c1d0820034050381e1260031010254480ca1702070228400038070418024219080600316100c16201d4411141c1d0248050402588400600404c1c03001401303610ba41a92a0303040002c0040c441a80c00e0080c000e490103050118003c00700c810390042a10800e02c41c040e04103000700594030520318400e01554010500003070040c03610790349150342d0140b048650010200c00140c40211500313040d0901c5040700443c2152001e104451a6403034050101c1c4203032040c10f1612034100c450400c0c0d0b50f42d03a504e1101542d0701900070007007811301c200b4003030340d542240c01108070301882d00c5084100c00b01c1100043d03125070a1204481001406c0085080154000c0b0360a0f0100c1c0f92600103404150f916405a00701d0707850700c10034103402585503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 741217050 1250 741215800 741215809
    0x301060c14030708090d1b0b04030218070e0f040b03010603080a090602010501051c060e1e0706050c0c2b05030d11070c090510030b010b120c0a0c0308040807120e 71
    0x11400762001c5500030404440003481c0715040c0d40c1d0143c4103d07040d1045000c2d905107600d0101583c03e2640807140c510502042ca11614405001071383e0082e904030721600c03040560160306000c19a948000706001c4138054400f803408065100c08550301500204040c4620f0020909645898004581c01c520100b411288150f020b005a001403619100900c0b15515060100c2c49410401c40070039201898074400ca0244405078104000700c4c008032044030300f11031502001060351210700481c210030b030041c2880003944511031300c25106085418406425020044010080c44210503403070003040401074201c1c0d07a4040811342040d900c0d240141d002d55541e41112501b1811200c560418105058040c80310502241c222030816060310002480050203403120010300d410000640c1c401040d0b88c0510001003908103240c80a0005d20301208500310300758079400c245c40c0560040560141c0005c05110705031011034400d40415030041d002d403225910f415100d0721038140c0200b10780598408208400c003800040d090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 741218300 1250 741217050 741217073
    0x60a0504030f06021e0a080103080d110d0e01230f060301140c090a0f0e270307030908060a051306020a120c021c050a0c0305030916030b101d010e1503030301060c 71
    0x3171402909192691140c0043e02020042c00081c01d215008162030f0100800c03684500d1441e00f0840115454a0031050010050414041010125420300c41440e01a088107115100c8102c4010f6407000309547d0744a2010f441100204019415901d48003041003503041c09a81782c0c00b5807200412240d03511203450900c00980d80640c802c0b840d50070591420001c140703200801a40200c5082041240d0340501d803403801d443c00c1400020140c43c00001011030805800c800700710120760001069078903d541e14445841240c100315058800707100780882c102c001070055030041c00038115038248140c209540a040d00100e514859100026034000b01845000d424801e054500003612854031900d001383c9607000802c0e03080381c44001020721101001281c0c0c114400e00c560204205c08240b90100c082e603034103041041d2001a10018549000403c012039140000d004502d00c240c45001c074100c20b030f46842881c88048800920900c80c0b411003c03401d105581d803c1c0000d5000380301c0c13075070341c1e800c40691828000d01041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 741219550 1250 741218300 741218347
    0xf040609060927020a020f06070e01020f011a0607051014060f090105011209020103110d0204030308070c0c0312030b0d0b0604060b070224070c030b070f031406060a0504030f0602 78
    0x4400c0402045007410004240c030f46001c44000258031252141c40980c980008403036040c002d07004e04030800242580c85000020010026400c44070070040e8407841e50300300e8601030540c0f1000b6900b000440500d050000080407524481c00407134201d80864400070741102d40740e1800c56107070a51380040c4800d600e4101d401c400c00c0072045a6414440d40742400180120301c038054192612903d441505055a00030303400354148449401c1220380d10a20440840020351040c001100031440300004070b041584a64044481c281c0e01081c05006282907403aa0044090507040b00c00c20961260b11050003901c4221a580d6002e01c41c0f8010070407410010200320969295800c4011041d00902c200400350342d42c00e44c03084c2084e004102c2300900b89001c2101c0d40315846408000fa0400444e010300100b0002440031042c030621503560703846201840160304030152a420941d14050700d414002103021498403d00425581d41c10341031680c1350651700d954030700001c1843d46c8280c41499020828480c030445d207104100240303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 741220800 1250 741219550 741219569
    0x60203090102061906030507090906061a09060d0209061c051308090613080f030a0806010c2102010e010c2a05060f15040e0109052506080c0f0406090609 67
    0x400c11000035503d60006010f0300702010ba04107030900501c03041e031003d0059600b080565680a443d42d804a026003000f401c21180130780303400c030f00040e0800d101c1c500070000511001d03401d141040388010032050350000b140320a20186d0803c200103040d500c1a008110034003c4100d040008481140190101c400003004655290030341e480020000f1f602d64115010b031007040300c0c2992504038016803650000f00c0342c3c0141e007084c03151118142030b00c00d00002400d125001035403507a04a69803a4011a07c000840d03200602c008000d81d149000d80180c089e9504d8050000d100015090071210b030701c01d0a440b58141c1c110f010814500e101c100300c46649016040c450510030005a103c0d080c0e0340c403503555200062555441202c62008240d20404100ca9160105030052040c441c40c41ca43c8011030003000d040404036418460513007000c007903401c031070110868400780141000d00c1619168042e51044002080d030f0140c180304000340141c101c4284060f00103071560390340b94003905003030070800f4207130b0722444c0c2000750351 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 741222050 1250 741220800 741220807
    0xc051c090302011d03011d01050606090105070b09013209070605041a041d010608150f010c020604090507180f1203050f091323010f331206060203 64
    0x40350440c80d403500701c942c203184c4805000560503000d40403a55a0003100d5141d4245054001e000e100c03481c1041031040280020843e035110803041080c584240f140c030f5400304d80306109460214034004e4140d58000404000813900c0e00c00c4035080e01081d203110120500b2141c1c004202c800111a1000c0f81e503000341032300002d000c601d0400101400c40d004500c40c0ca9202808092902c5840f10b81000341d800605021226450003400400044415030b024054000003d40c02ca0009221a580009540c00188085c00711207800843e03c2c01115031204003282a86c004400f044006401c83c00d038400c1d40d03ca140c00744c1d68250080e00241c2c42041f07a860300e92100396070041710001403107283d211504c021040d5074541000c0f40e075400085001411405208802d941c800c20b00108003d021400c2d800011440f51111518100011140f60680043d102030040d2079211550030b00031703c005105445490880d001c0025001022090200040641381410301c0d1040021044881c101d8003410a00504001c2c280d180051800d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 741223300 1250 741222050 741222103
    0xa09141b030f06340504050907080f0c0901020a080c0109142b0e040f14100b040b0f0903070603140f04110f12070824010b1c18030c05 59
    0xf507410003e484202c580c44c10b25061202103516800c500342082a20f42d070310300100d1041402030501e402901c903c074080c506400010320318510617030f00c0310b20a010f0034460003c55200c0500c00195608140e10b02c40c1548102c0503d07002194031720011b0480789180c640049900c0545144ca5490021000310818840c1e0103c4a00c0130b1002102880302d04188140a440c10469030307145084540156060301e841e00a8981980315a00019a40080403039040340b80c40705060b80c5400041c0141411648129600e00109020130f0103c2c884000c02003106881030001c0504001d44000000c2c246030540c0e000e4008a0364510f4456a1800c0ca110802d80c0941c00b050210344500d8a519150711030000139048512425411841d0303030b03503a40c40304443c0e0700c0002071000b1110260784450710349e5962000c032201c20b002c000c00607150b44520340c41102024182c40d2030755045c60810030354a0750303203c00c1e01061503000300d4262140740c00c072900074640300302411841c042d507101082c2448a00313016007040c01004a81c0e4180010303042640 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 741224550 1250 741223300 741223303
    0x402010219020f060f120108160b0f070c15030608150a0903020a06051f0b0405010509060310030b160806010f1d120105010920090d06050a09141b030f 66
    0x24441240c020300c1ca400c0a44002451511800301196000c1c0740450070012140c1040082c00c120380e844040c4000d980d0300c5e032441e1691350002c042c1204c1c0c003200c213201c140440c00304030f07014051040031070f1681400c040312940c0b6044124a03070b0308404160546401d5401c1480d905002d8030f070051208802600341c1281e40326981e6010b0100412000714592100c5050303080520800c2854040381c1c008904000c68101a16038030551000300c11402c038094000c0201243d6081c21104a8085450584960b0b1030251480188181a000105001403400000c000000486c80d100c0505204400d2200a02c3d5103000200c0c001d409284007822136810000d50740f02450300c09400c8030203a01d0b0442e5002613004207240c0300f40042ca04034503a1004510320f5003000000103c0401c8c6401c500b1312008411042d030200074400c2c0540d501401480b00c1240d10a1004590202254a070f50200d604160070f400c01280b80d0b480750302c0740c0815418490150340903901200410507901410b0000150004046000c0c0600010602549 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 741225800 1250 741224550 741224563
    0x9091404020909190803070e220b01050705010e060a0f02091003020903030d020d0b030606150f0f07120c0209100602060c0c0309120606041a090403030f020f1803010f0504020102 78
    0x2e000e52804000704900704420803d00415520340007040c03104000515000c4219041507a078500400e541e804100d1052601641609114800c0d8000140d103005108494018002010040341800360401841012407401c2c0a810a83c00031174004020500385070044c88102d030101c3c64402c180520600c03149042c0c0d81c0c2e40080d880301a040f0302d40940c8076450780300002d080d0311a582003400454030000d00c024010b0040d800503e07400c04100c040c0c90640d607820303050102c4c9001c410300d00131100340b04010f040028030940e000f4051003102031020794240211543c4500016207030004d000d01203078003d4054021854002c0725103500c041d444480320301c03252a00101a54400c0003401c01060b80b1804101c1c0107800000300305442020000030000ca4a00254440e181e0315100c1c141c039500e00450400c980c41d1348e5900b100b060080c40c0000078000c05003554403034900700d0040c0314000c0c1a54803141c00300061200c4039003d00103488030b0111700038150100001c61003054216003160031486200c03802c0c1010000540c0c7c02283d107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 741227050 1250 741225800 741225803
    0x6060c060b0102010204051306030204060b0f04060f1e1d03010c2c0d15050f0f06060a09090618060503061b0d0e0604030507060e0c0916110102070302030a09091404 72
    0x418507040d1200140e000e40a00d07084190442c040031207841c0306400e41d411101c101c90080d6000c00840341c0b120302054043c0f06211400c0e903280300401c01002020311615280750900402d00c0c150f80c029222801da0407044089181c1e0a000840c1100500380640311030408100500080b0001c0040052041024007500c203402c58142d001c841414ac1803c0040c034a81d500c0900a41c0180b15145403202450304e00b0003a5000030300d0882a91402d000941c0500b40305801900400041d4142c401c00d03524582001803992108003440104030030f00d0000110780c503142c081c11018222030b1103505107040c102c00700c81d411a120780e84254440c2d48042c00340040003107448801d01800b4591100c07036546900400030340f406403403000e01c803090621a503401c05c400e06034000041c04041d84a80000d000c0300d66400c040c10b60700d0403000c00c8660f021000300301203511485000c00c0442d14808901701010000300a4a80350f089800194003580940c000080c4800c000d03034080b0f19500a0290902c0c10803042079088800080030700001c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 741228300 1250 741227050 741227063
    0x4110d05070611161d07090b030f0601120501060f021203010308040e0c120103050109110f0a0e0a0b04090c0515030f1614070f0615030b15190e1906060c 67
    0xb0321030003001e030500602d41c540400f04c904901069445a0001694281c01c1d842c1e0520b494500100c3c1c0300c00c3c400c64140044909500141e0300750303140d81030030320460300300900114180551450042442d5405010702c80c005d0a172a04d07101c05030164840c000c0d050101c1240300d03400041e020801030000402c040d0644003958202d4110740459038580b0307a500c0a611480744e41690540080000000b04032054000d40140c078440d242d0072980318910424440c04c2e00031285c00071380c400c00e603810038400842d0745402280d100350202e00100c1c0320300d401c4010508079103130840242d400e50140003060040d810f0140e81000c150780c0001c800351a604d004441d6010400010701420055004181031a071403030701c039022030300e210030807804202d0b552121441c05071900c421040040312441d00300b4241e400001d13001b131003a4003104d410051207101503444a100c100c6100c4007140e2607520241ca2a00d6140c03400b9601514006004140800031150415881b0700c1c09040e403490b080460076041200c14001107612140c02c40c0101d41c00300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 741229550 1250 741228300 741228317
    0x605010b0702031e121804060b07030e0d03090f0b090f061905130e0f04020315060f01050702060f0a0807091509030605190c0509010801080a020603040227040b04110d050706 76
    0x100ea4201030240440c04240c81c2d02065016a0285440c0c48602e4030f1b1007240c04015196480151051601440c00e0190104243c405907080904100c0016003000c0d200e8070705216001d03244c0b074045204e8801030300b116901e56000f0801032802c1c2000e040b0200d002030b003291150308001244650641c2001c102005400704000440c090360707450040da002401400c03007070310608a41d1810021080b00c030700741102d099101b445440c3c6102128034003620028040d00e005008501114100c05c015540703035007e420f0898000b0801c000540324a10814050150003203a07a80b40000e60403e1107000f00303500c0b010b4000d003030329a20400c0c8182ca6941c100031032130200e17a2701040c080341c03036681c1d05480c40307075a03109114110040b0b040c0100c44015aa001000740f82d80d020980701c01034540d0701d40b550555207005001380290800c0c01040800e01524144182c20060320620305c4600c2040705c0c0420b2480340a0054900b01c0d140002003080c0070802c081103007014101e0b6402c1d41d0000b4036070140d844482d9140c03005d210310018041c555 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 741230800 1250 741229550 741229603
    0x110d05030c031b0d0309150e0703050f0706120e0a111305090d180509070327300e0f0409080f041d130201030b0a091401030605010b070203 61
    0x6106807204240480180c0f516280351480d000c41c0c06443e0b19040c06035010b4501e04c41290fa0080c41114080354001500010710b40c009042000100300140c107504162103015070000c00104104111003090503910b0141003c98a802d00241c008400310180d200000c1c18902110440d40e000911003da080d00041042c207403402d071101041c410b40310444168205820030003000040d281c0058200c480c01a156a8040202e4002c489101240c546d80100355201d2002070100312524425004040101100c0000c12205907840c245800c0c580380007803049568400c0891580c03009480d4007240308540c4460302801c105200d0802000300f01062040f0039900c10404c05d11b0720300003629154040c100e1141e1090003180e40d601103036211540c0780c21a102d0340c00d04030a030021001844030100b06460150101e184002c4020b101a80150301404085005d01c0d003007004610001000c0000340144152031100f0040042c040d4150b040074070541d0016007041007110310400140c80140c03000644000704445580c0c5020030119103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 741232050 1250 741230800 741230803
    0xb010504030206030403030e2413020604080d030e0d05090d2310140604060b0304060504240b0f0f06090d0804080312010e09070302011413031b05040b0607110d05 71
    0x2141c0020750869804410441050703010f900c4100c4014421003283c10802d0102d40c80601d06900344101c00c20680800c010448220341c1101001280c1e2004104038240317902e51440d41e203072190710039104000031340325034502c281000244119a440c43c1c81c1c4c6001c80c6040c0403c0701040000046200c020305078174a45100916054100035500054040702e400c3e5a007220903045100040c220110a454000c001600450b01910f0702d0b00c14032049a800010160660f50b95440c0e0320010f040090054500945d03207040c0700b441e0326000c001011211506800002c4050455083c8041c10f444814258011034001610352a240e0324403003a914540700c00c071a83d000c0300741d035841c00d48503e01950341b101030f40740300100b001148602d03220036460503108441c40d200c41c00e03591150129502d410510019000c038003813490680d01c03450114014015454110041030016659a480c00720b030f40c0c01121200c1d24042e00140a21640ca81030280d84040c882c00c5401314140341c0349840707023075005d8410a1401d2080d850060b003c1d040020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 741233300 1250 741232050 741232057
    0x503070321022701020c0a150311040e0103030c031707050c150c04120302010608031204050d020d1704021903050106090e010221091609150801021206040c0504080a051c140307030b0105 81
    0xc1c043c1c0790110b032a94503a2305951010b2603080420120b428005801207000150303080d1811103002048000d0140d203141c40c152651000464190204141200000c511602000c000d0303005c0c082d150381d11980c440c10b404841d410701c14031030710745603030311121400740300814428800340c07400c1c0d40e0258a02d003044c408916003680180b00980c01a50a8080486d103441203a40a51a82d44501d010310183e425402d03a1035000ca84a202648501c408180509030105008030724942079940544050040800740c04845e902c4980309216500c1203072203a444200600582c2c0301401190b00d880e441d81c000b542017210076452001d1400b88428424411689140050340c842c20401001001184018503403a5084e00c070580700300584040c49110160050580300001c5071041442260380d615403030107007940183c65020800000c0c00680705ca0700100001070001049030300d0280006241c20307225900400b10081e00b070700200740341607440441e00300348144912103807082d50328030044030b500a96a140011300008a10016540c500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 741234550 1250 741233300 741233323
    0x4050c03071e0909050f040201030e03030c030106030f0603080c1006060c080d0504060209130605010905090606070605090c0301020c03040815090615030a0f0b0703060e060303071509050307032102270102 89
    0x1e0400c8180706d1301002e110440e034020340c000c0c4c0e8140410b030301450a00313587e40310550304100090350400040186034070030303403085086180726030300400d007a0358130749074030085030001007411803103400651045d102454507206400041010303040481c079180711511a0885402000d038034160f400c1d201c01c00101040080d038105c074560310b0001c0c080c035108240150840012301040c00340902149501d034002c119071902d40005485000002c20291512a13185ea454014000c00740140e181803180c41009001990280050004030003040021615103107002c011900d0301e4221f00d40002041104000c0c0204218040ba0443e403004014503490711030860b040120785012144000904a000311850300803c0040c4141c00c03502825090350140007075512910f5a2010103400e17a07419a0681c0100900f00000d104141e4200b05986100c500003841101600e4882c10750307110202c01c50004e4a0002c4514050024206000f20075101900440c1802c0301c00d0001101200c0800110200008040944010b0b0388200f28444904 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 741235800 1250 741234550 741234569
    0x307030821010b0a0906170a0b030c1c0b0109050106080403081003120f0f0201051524040b0903071502150c0d090b01060e010c05030a14040f030c0504050c03071e09 72
    0x150380d180c00342c90180c1c0013110803200140300c0f41c0000407168465008580340c0c001e22840a00d140d101d400400009080c10885a43c250081d01e250790003598600b6040300002408440c0b0561800541c41c0c075403900c400581181030304600d45001440280c0d4441400d540c0b00d641030130109155182e4008800349901640d1004044204412082d00230700e502110070303240760241d41c03075aa0354880b000005070700360780c811158003003150708084241d0b60501d0310780003a1403000b00f0511030901008000384004010340c0300d80c0090300c00300750000e100645410700f0400d0302c0c0205038070341c0103189148500c40c0094891680005005101c0607101c0400c650786084812a041075080c54400c10180e5003501d071116001c4e100740303e82d401092105445882a5016031211507a080d03200c406540b03030652518080d14142c0c9100f5800340005024000032881d500f0310518540514000e400c010081c0e46010b003000107440e030050180505080520601c0700040d000444d10541603c50070000308005076004c030840360340392607a0110701c85 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 741237050 1250 741235800 741235867
    0x80c0a080d0c1101051303031d0a0606050901050324060f030d03090c1a040b0c01090f051b0d0b180c0d0b0603060a0204030c12050a0f030f120b03070308 67
    0x120815501484018001d5221040182268540c5508131741c000c81c0c1d450410482601c03403600080c0700354000082e16034803000c1040d80c1e5070b940a242d0706d4810203600c11210b40303541e8423041c8501e20b44569035500408046000700300c6020b180400000b4001040114a14010601c0200b600d945d100c2900d40c01c1d542c0702904031202416070b424001c02031704c200c03030040e035a00031354005c0450f180300191009108110b104640c5c500c2e0500e0a2000800c039444000d688809540c1d812038600060080f43c1d4070b1071720070300503801810804101c80d640d4080550f051545823041a101000030b0010f5003c8a1595010940380e002c0c80507114032815940c2051102c088242e4841c500c0301142e010402c8803a499070050005904481140c1da584440100f01d10aa000180000a8920040094400c01c42010050503c181d040d1020051140e035a15074120b411503003240803c8580c0400401503034012049002550030850500100070024003007502c6410500028203007480005406821305002c2c02142594408040000b14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 741238300 1250 741237050 741237067
    0x15010f1208120c0d0506120a0212150108030a0f0513090c0905060d1406040e190305070b0f06030d09051e010c050d0306080f0c18091f050a0c03110403080c0a08 70
    0x7025031280584d03410305440c0002281d12401e00103070134107800e0075110083c2040d91990302000000102c400c40401d05101c0c140740c1c450005e0441d65500d00030010b0744015521107000f01030203841900312032303d11020800140450a500034044140c101211040b960000702000e03070b440100c030054015044142c06c000d001400c100440141d60100e14110480340d0780b41c81c0380e1030f04000c00003074904a00024003076a0046490034104055036a01c03d40852003070234290300e01001582c506280b090110785250700d40e0365800c10044336040912003254110801d2030b21100d050b0030000010540420000f0340c54104941c400440c80b2039004e4101c8502d110340002c100c4111459450b80200500007034081c58140e4003030710f00115400c20000030b031002c140d100100040202c2098030824962044000c0c007424182c41480d40d4900154015880c030744150480000c046518030b45070007840e040da50002002c8041500d01552030f00d00d20480400d65041d01d83c81500c40d903460050b0504180741c202d10b5000500700e020000b50790f40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 741239550 1250 741238300 741238321
    0x60403062408031e430602040501090806090709020d02360904171c0207050607110d090506030702010b061204020a05042d02041203020a0515010f120812 67
    0x6040300303400c140d001001841c0c86501640151402240d1002c2d0409100324941c45000082880e44000e50b484c2d15072614803464035203003020030307802130f21100d1f0f0000f410f01c1156405010071001c0c041070310003400343e0308004558581d194100d2040f8200b0f1076010a0a801312030150b0100da005000f40300c00d9105500c40c1d68007580304014190311030401120003000390030309400c020003032520442d00000b5a04955080111000181d4440410340c42011168110050074400c0da101030704c00140918002c01c11441c0a035000b41003503260140c8030120ba80a90941034040307a1042920040c0c800c2038408986075124107506a000d4800201140d6100c0d1000c00e1183c0c1e0142a800220300c510700031143d070380e01d1941d180c0500007200d041d02d00e01104240f040c00b0000d0000c0c01d070f090642c1c8030700c2541c1005141131355406600303841210180003100141c0000c009901849010050404224075009611049500d0140d0820021401e0300c2910281c044001c00708040c0404401a105034181c41d100480c0c040c0341c004401d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 741240800 1250 741239550 741239557
    0xa05060a0b040c050d020a1206030b040b0916030615080601030506090106060f0801050f180106030b01121b121b2f06150a03050a06021b010b06040306240803 69
    0x10306140c0d1034110551100d14160140e0154500103450b0b582c900080c1c051550007941c8150303280e405100d02000c0c2c05144960300d100f4000258007554032144141094035098505420241c505070307070b692006042410804440345960100d0750300450010700300601141500081c81d0643c003070304250007860000018040302144030b0740b003131821030001c000d01030300e0740d80a8490001c200741d07140c0010752100c0140400d082c03202c0362000b036010081050308100c100031410305d1541400d800820005c3e8446072020141c0d43c122030b200b110046110400c2c03024003280520a503448001c0c40280f010410b4070400c0c038110000e90784c4546440ea241850307001d189240360307001824010340f00b080290b280c3c03040041c0109103d080200540c690001b0740c040c10541c0c1703c400e2a02c0d02404d6280341907902001c1100004000b61b410013034100031b280304035030150310340900054180c3d242101c40482101a418104456502e40d40e51044030166030b480750700003590713001581c0b44406501c182e0013145414810410f012490001c0040034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 741242050 1250 741240800 741240811
    0x1140a050301180c0b0a051c090203010e030a020c04140f04081201150f03020315040e030d14070905091911040915050306070e09011a0c0a0305040f050f010503160e030a0506 76
    0x444c4001e81c3e41d1130180b0300c94440d00c416000028400c0c4000700d50380254500ca0025019140300202e01d52840e81c001a084440500a00341940d00c0013030b10b0820150107014944042e07600f11010841588455440c00c481d00e40200b803804030342e45000001e0f00f001b9040050f562030203031034000035206603140c0c610745002101101840000c1440004925481403190003141c0c8161481883c204074a459042480003421030300402001c40c1c0018081260504041c2c410300803070030350b60740c00c500d02410400d1003d8003030390107500294013900c0403100308940100b69400c200b00704200f01200041100003920703450040c0c040c40e008242c00301e041211a40322034190260701000e440084081c0e4000e40c81d011000d9940030100c12130b454008002c0001001810764084e2405010b4102c2c848081c0f43c041c03482001801e00640322022404210089820b001050411403144050b107801e9070b0f0b44c10021030601c00039102e80401042c81c2d40095031030f88403e845911070000091082409000c0701c4c0040301501d0502c0d101c3c18101c1c0c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 741243300 1250 741242050 741242063
    0x180911040506030c01030b06041d01090f0c140d09080a03022a0d0509040e0d05041809020604050402130b0c0c01110c011407050106080a080c2401140a05030118 70
    0x41021061600d80704541c040c180080c02070103200501e800650140250000c0305a00c00c80500c00010007020800508034220440350004d9400c2d0304005030303c0115140c4840d000850391403c072030880201c2d08414803854100022000e65115120140c421001d0280124010900440818511552074260700a01024822595400c1200c0060301c405c00003219011565007282d44610800803da0b80102c000748001c0c0800340020801c0700017034a10b40d01d0600659030000008100040030000c40c086101d840443c061192014405108150000340d681e01560050328070455000650040c2e00b5220a8510000c1540c00309180e1109010041140c40340343c1c0101d254045009c41c50f0321f50152002083c6072048190586418540b6800085014000e40044d4012a0341750b41c0c2c0ca4020400c074504100644c145441445080d54404840301100e04200e24519807012958042d620410382d009445685810356400901c845040d0400b8000100d04064540c4840d8041d4606002c0f0980281c0941c03c1c071003014050311 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 741244550 1250 741243300 741243323
    0x160305100e030307030b0609060309060402091303020309060307051905090a0504060308040308091c260306090103061e05150301140c030403080601140c0601090b0105070312020309071809 82
    0x150101929007880460316290020000104440d001c0e610001e02e1210180801d07061804400200d0203903882038910740c880b6840b0f5400c110440c40e00020842d400111500c020341c104666640180d641c0c051108040e1080c04040006424240700b1820750b0521780041c10030340c0c04040c071198080d000c0c4d44020f101d54042c01c0003181c0442c50f03040902500301280d502c2034166180c03c0c0703551190901500020341c0319a004c0701c4800607419030400c000d203078128103014107a100e100f03465048000c00b440b442d4161401040380140200460342d6600c5181c00d04503508180c01007071141c807107800903030001041c60402d5402450f01091040c40c1c05d0700d0301501d0b01d105c400e4000700450f1241c044081c0c070111f070455038007540d407404000080c00644188541d50304980103040036000100c0781d403000e0f900c0750880084082e281d44800010025400c1c50b000300d0000c2038082c00d040745041c8850320010002201e8903900011150000b01203444c81c02c040000300c0c0207059940320764084071803442c0c0ea43e000d0544180103680d02040d42 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 741245800 1250 741244550 741244573
    0x16120515010e2202030604110a09091409060f0a0f0608101109100c0206121f0f1a0f041e090509121b07090f0c091d0c0f0903160305 58
    0x81540b20605107030030a0f5860800d8105030300010307600040440b90000d86401c40c554020600d50041d211300d060300d071600050700741017155560454003070303200c44540c055603581400680f0300080781e0709800c000605030000c1d8990300c2c20261000382c007061401c485824a4110300140450012510300f1105c1d00321101400584080d0b01440824000c00c0c03159584980000300c3c080c0054042c0c4400c0020034806804241090024461030881043c01c40e0a10000210340244140c00709510781404064010421709903030349810803102080501c0b400303801718040c0304005a040d5900425805030b80040951010200e103040b000030581c032440748544507100066062001040c8480c0e0080780c9409004414040076082010388000e00c00c800162003040405801032000204121105008890306071400b01c00100b0074180e0003200805800c1c51380d00000d0000d9030701d0f8200305400609448240c0111500400c1c40d1100448007102100b440382d2109958107200b01d40c1c0d80c818840c00c8240d02000c03a402401920040c079540c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 741247050 1250 741245800 741245809
    0x13020402071407060c0213061d070221040302040f271b06021c02030901020c150d0501090b031905100b0109170a0605070c050d05210c0c1e0616120515010e 68
    0x54000c03a070461002030040090160000305482d4084950310441d90b480c1c0c1c40340800544444030720340c33406c480800000c050007503092134003a01e202200c0f40c2c1d104101c021040310442818000162545403402d000034100d405104c00441003642114007c00040c42c560b41c6c8200c060f5581e5039040c440304140300c14581a10310103001105480d6480b00603005440901000f804100e004840c020b400300c05030409020030103a107c1035204840c0600240748000901c1010041090b141500401240309404d02c0300c690040098404a101d111010051310040340c400d101a0060718400e0303440c0c004207011503052182a02210000449414a601170301741009581c4401030200c0d06280703a000b0280c0a40d00060848002d5403094005184150845d02480040301c0440840b40c01540b055802c1b00e20b03c000800c3e84015290280f041c1558404040c84614103d110021516224000200042040312801c18034081d11401001d42002410180000300410b26103190f20b00d08140040341d030030f400100184a08811404d2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 741248300 1250 741247050 741247061
    0x10e0d080c041520010c120f020a0c060506120d03090b0a05090c01120f060b09030705030105240f04050c030708010b0310030b1b1308011413020402071407060c0213 72
    0x2003d40c00a00510054820707595079545012802c0e0713009004141c4245075070203200b4962003140a50300d499081010715442400e907180d0080c0300c001076104100317520203560480e00c0f540d01d03640d000c40085000e07aa003a0001d4682e4110380c5150910340036548021454075410790100c078046204404103407542c1c88000e500c03000c4800441e495510760344000400304542d80555400107070480da05c00c0120b004c410000c0e604003134500e03660100140300804140302d0258501400b5000152a0640007081585000454100200110b0240d00130b24118502c0c0c900309500d400955000c0180c01410601290a0011358860303242e100310b51200c000790341c600000c03554200f0718003141d001d0052000011501400e5480314a1130802c0501074140b00d01c81c5640035a21440d0b520b0280400b1130007680e100ca605450100d880b401c0d5110402100000d1480800700a010780540c0504045160161001030300c484680c940100d04d042000c0b11a08c0512a9000c0011a681d11945501c5c00c0c510a4920842501d240301200c4107a95 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 741249550 1250 741248300 741248309
    0x31401030201091707091113140f1011070e1636120b070206010b09010f05090f0a14040e1b0f130509031315230903010e0d080c04 57
    0x42c10381404000881400c1300e110210b4424400760b824141d601e44082003107a42150341141d400341c01043c104081d079010040400144480d003c1c00c400400480d00182c2c40443c490351840c4194000c42d010022103105403a00d4605012507400c88000f1600d40c40e2400040504560010740d85941c06503c07510b462040301c401c00b0741000c01184403140004952807214000e20f8140f500c4000303a0740000000e803090307089070b40e0400078002d00c0025102c5c10160b03002410410142c019a00e4044108201c040c03d036445640c000d80c1821500e48581c07606400c1000840340060480c002d03a015000403408151140a1501d1a0142d442103504005403000400c045403603200100300f03166502c507035102804190a064000003d0014000c00c0d801c00b80c0b000080600840d102030354041010b42c00401c6000405d16545030f180007800354072803802d108094010006051000600007201c512820303107804da00c01c3d100c58003903d03101d180040c000e01c0020315038800c003070703a03001c02c1c05596002070495408503a01c400030004403030644 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 741250800 1250 741249550 741249557
    0x2041118061803030d2301150810050306150909070302010503010306110405090a06030302010501050a0e0426070b1e09100e100e0a0c0603020c190f0602030c030106031401030201 78
    0x908054200a62034104106000050010302c0c0406066039051008080030056042c0000700303001c3c0082e10040303190441d4030b034030054206100180301c03200400c030000341e100c501d92400c26659a203038041c01ca503800c02c65000070381500c100405d000ca1a181d00c802c013140c5081c10b0362000700e59a1004905a560740c86440081d011580c20001440844c640307800c150300443da041d039294909640c440110300600003c0f111858010740e603610602c100f642c2801950f00400c02101c1812843d82010a16612910301901c014003610954041508156207100c88440c0c00c5280d804035500c80c1c00a00f0180140e100840351400318160301c3c1e940340e01c180b03001540140036900300801000c0d40c032031905e0840014141c05100c64000d2141d030300d51395400e1000b4011034507030042c070401130301018440c3d107000c4006424a800c00014940140304000c1c040e407000500001d9080c160030045210082800d085095503c8040050045030000041242c201d40100c0110304941031030350100583d4000880c0707501150300c00c3c00001e001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 741252050 1250 741250800 741250837
    0x1e0705010f1514180708040c09060e060103090f0b0901020c0f010c0f0f031e060e0714090d0309050607140d020304050a030204091103060108010c170405120304051c030207020411 78
    0x5010180110120040016040f600190860000c3d0441ea0000320740c0c0f4030000d07402030100010040c0241001008060344901402543d0074400bc1625500e0000d00c1203040680e0382d4981003d204508142034491074001009081e54103288080c94043d43c04004140da10b0311640c401000e120b58144204584901107680360414543c19130000c0350900800e03504101096180c070700c80c0ca4120b0700180604000ca50001c0c00289043c507004600c014a01c000b4604020b108031320024240c0e0581103012614810421101300c0720081c4146010b40794108039400607034100901254040030032088240c480191290301084964120600c403040303030b0f46c0c4128001c054104e003240000b0001420550003021a80788650412044075200e40d01280c94414241c4c48612180e45588644039000d8001445800c0411107081641091130f107a11032170380da12501140d00c550740e500000020306014062084030880112102c691560301c004240c024060340140e40181d1140349058a003d09032000c6504640c0300b284a521000c90 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 741253300 1250 741252050 741252059
    0x60a0608011a130f060f03051f03080a111009050f03040305101d010c02101d030418090b01030302070807091b14090301020c0307110301021201090c03021e0705010f15 73
    0xc560803c45044001216001c0007007425858030003400050011940c9021010485840c0141916009040905081182142010403482400c2205e040c1d940110038282c0d03a90201100b03c902031030f031074040086030066014587c0e410400780c008030704140c00781080f240d290a104e45800c1e100d100c0c030320000340181e2001b0b0b204900290103801200410031710180741c4200c0d070b0340c401c40d050941d0440000d070801a0440030319001180701610800c0c90302805142e070240d10f995481e10841c1d50344243c0c0111f200b800d210418038584100a600300d046000d03800320995159503981d15002c2c1d079603a154000c2c07107498000c4280c0030400d075140780700740511144c85000b8940314010340e0b03074240c8a003c4401508100c0c490108804141600d01340014801040c035a00110381d9a902410b088009000c1402b150b40320340d0040260100c070707036400640b06064800c80b100000d80280151400e8000384160b034800308010802d00c0c0c2010210310040d01900c00240500f00901c1107079040d82051040740d40316a815a10303401c64000600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 741254550 1250 741253300 741253349
    0x615050c101812020d021203070c0605060d06020f07050106060f0804020f010903020307083003041b0e0c030a0b1915050f0f070210030b0109090b0303090a080303060a060801 76
    0x10602521032030140400d02c1e40b0307210300040081e01d55140015a00c000c026070810ba60400501c150050b00c1d900366030440c20101c0b401810350081c80302c06010b042d21740340403da142d03a500c019000402d0340017000715903598070380c00d11030301940040328251429440d0042c001442401030200111481040d6980c18040d0b95a900f0025217490740c40d802c5040121249012005071410020240945070510040c61a00760404101d02c908591004086092a4a2050f552074072070503400d0380d80042d44901c1c1108994144148a031086440c0c0d844a444400034105000a80c0035510040d8001c0108032030500040c00c03008141300d1180c6035400d9030792140e10201402c204404200d01200030040c09450b18034940070080b05103c4081d04081ca0105146500240da1700440c5096000003119800500342030000344a4140080c100144610801c988103440341d001c40c0896406104440c5154402442c201c405a00c80c0b01a0750f5a40040701d00c6030103060700fa04086402400f84440720304840b030b0008155885403d041c040c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 741255800 1250 741254550 741254561
    0x501080a0e100e1e120703030b03101103070f03090b010b1b06010305011b141c0b1c060506120316020301021603050903010c2c030715030615050c10 65
    0x8981c500411408000700300300c40c050b00398820100c0c4010072080d601d2400701694542c88094241055101d5403001d002c0b140e000040d0744d00207415081c0050549000380106e820200d181c1038080c41c3d0740c541022501000c0c07210f00918041e16003561199480d4828000070350884401030300c080d060f0b010400042240e5103600c80140345012200f1144440c15402d0b80b40b8502d001c0c820381040f5000d94488280403d400e40c2d003103075010000490700d02040c0504d00c01781d80300a0340c42948203501c01c2c42c8501051202c46007860f0400821301b01d0180039021646402c00b21000e8148008000300c1740c0b43c0c2000e011519519011207401c4076000a5030103145006c4900b003062010300c0e4909000c98240d50240025001250002da4604040d03029459860b500c407100d208050840ea18041084140f010320f80150f500e04111035102403e0140058040382849140300000e0b1070045107a100c5e84030144460880d507040780d8160000c41c101d454030040c11400005011044c2c804d8060300b61003a0059002c405104a21600c58004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 741257050 1250 741255800 741255821
    0x180b0d0b09030d020d14060409080d0e070b03010b0910020c0105040e0612011404063206040e100b01030f020a0f1803050a0b0403020c03010903050f130b1317070501080a 74
    0x8503032030201882c0e00441645c00204208203407903982c00b8080d00c40e040b506e029952101040310304100c04262581d81580600509a03070781c0d0600d648424412640c00304010000117040785190b204c0c4c9130360b03684007800c0d516440802c1843c040d0350b01880c01041140005250000030070161182818607060554050882a004051640c03000240700b4444d0f5100d000c1c4900341600d00710700a83d002a01d042e080000a8480c4c0b11740902c0c4030203400c860040b1030200d100f012120b42c103007034820316090f0303d41e04002405010400400802c80c09030b500d184051a04030303482081c542c1c1080e2010f0180040804030f900481c040e402006c008113691400740281d0340d21420b2140c04280e442c0150030f2045449454031031504501c10340c2101c1c507107810340c240001d04da0100100e030300d4881c0481c001d1000e44160340d002080360241c81d101c403541c40008240c0313804c0308818038080000ba2440e48030040e129010802c61083d4001e282c40780030240e030441075903603600200c0455140f0655006849100554030740303103403017402040b61914 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 741258300 1250 741257050 741257053
    0x12020c0c0d0303060e0c040e010501030b010e09010602070f050915010305040311011107020a0b0304120503060a03170a030e031e1c14091b0d061d1501180b0d0b09 71
    0x108001640e036469864041d5406560001880d50410041c0300301e17890003820304e42260b04144410040812030205150644a0a1801094560101e001a9825502c01541a91083c6c4500021610790341c0003c90000700c4010711410408207555105103c280030381503079014540e0f0b0400c08150f45a50007038018075001482882c0c41c00d242e214000c5614211461401a47c02c96a00026003100b1740c5000d00304103014014080c410761540c1400d68403401c182c004941181c00f8800048002260b40d40e50300b000c100259000700b244480180d00c100401441d901204111022914040d81403400f40d4000055070b44100001502103000d0a502d40d003030003141c2140980d0f08801c5000c003100224412240100540651181081c40d024140031030190b007010010301c5011840b0081d00b68030002c55446201d925101c41c0c001000048030308211004e580324040f20a940c081c144100c2d401070300c51114000059040302c0254500554000525904c1030030303940d09110040d84501100403410105100c40c802c2900309a1410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 741259550 1250 741258300 741258313
    0x1090b0904021c020a092901020606010f031b050d11070b0f2502030c0f0615090a06030204110a08061816090e0717061c0b1005180105011d0112020c 65
    0x1400903003030600a800c200c2c80c00707460b601f0301030000b20391407011100144003103800c044c84203070100000e58035600100300d541003028031b0810000c2c0c903000c2c1e8041c0d0003044032290303074080315855080042c0951b4070450080c0c2c40c45107454494050000c15000740c6022030f502038100a4540c0710303d036545c115100043d01c0c01c644000d00e25000c06008402c0b09484607043c0842c1c02650b100d101000a69003804103407640896960405806c00070b10b400e81041c45074800d00c040b2400f001d55200c074540e9000410040d00000e4000d860f0548070ba104400030400b4041400b25959440703986d545d80070510a4120740c0051610304000c0c07080201729000b141e041020600c1d20030b468640001940d400070b2545204007a582c4901142c218002812407881e003181131030b0b000310107035001521a0207918a0608803044e001015250300803480c041559003500031128401044000c011200106100c3d480d600072140030300c626401f0490f1014902503482e00383c1500c1c400502c050711044813003900b00388840065403180c00c0305406809603a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 741260800 1250 741259550 741259553
    0x1050c0312070903120c0506012c04030c0b0a0c09060804020102010905010912030e0102091f17010902090f0102060f06060d0914060412020318040f0204170d0801090b0904021c 77
    0x2099180c4a000d9640d42e10071014035505242c28400c0d868031285c801c12488032402008142c0000e002411102014a00b1010350031250703400c0e5410326040141074081031410709000605901412046000c4d00592072030803da150b42500c10116601400d0700408542c1e40101040b20070b000b00101c60303000d80180008514441540d560508440c9400002c03140c12400101d6060202d515216910310911031a008618040f0b120002456405060f1740c4140c0250030200340c2c40e902c5101d400c113000c80d4420922188119615927540c98060f41003500b00c0c1e800740c01509980d0f101340d840090800d000d1111503449043c03607140ca40501106900100391844030b55103035000c840000302c13648460319800d004c80303003d0aa00d050030301d000b0181a05070103450742107510034004c1d404400d0140210707451501007210002038130020224220040c1c020b65203c1142c3d0710740f803400345d0309840010580c0c00b0440070a1f030380c006a9130f032628942012907102200094001800301d00180040c101742104100c032017407007132051085440a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 741262050 1250 741260800 741260827
    0x80703050c010f0903020f0325020102010e0d050405041401120201030f2705151e0a060f03030f08010504021e030c120709060e010c02060322021005040e01090e070501050c03 76
    0x700c8010000c0c04c0da41e03c1100207266040c8140f20310f10700c100d000345213400c05140320021000a8503010011aa2104c0b0504046a000354806001d130b9000e402a207101056020b8040d08030782052090318011030400b4010b07a00c00c101d802d07803541a10701d00000c0341011041a00114010201e4405030100583d5031501c24540d81e85000355004880ca04592421842000b840c00d50300381424100590400000382050010800c54090a070070700c4401d0002c09099580e0f202a25009003480d81c3c85000040c29510021040c140d2050125001500d16120340c0c6480e6615001c1c40704a02c201116068151184c900302c82c2c12603503100c015a002003810b124541442003d42c480c1c500090291103440102d90880c00411030150841142900c4103c01d0074031445500258001c5a9a0300c8000d011114003007029a0b4042841c103080d1400c0034141e00500034806d5085290000342c1203900030302469400c4a03003c8000078058103140612100402c6c2580900b666a281c00c00540d00ca0b002500a0140340c041032050386400c001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 741263300 1250 741262050 741262061
    0x13080601150306170d050a0509090f07030c0e030c0118030204050106051207020105010e071b141e070b0d0506181314010203090601031101090b190e120a080703050c01 73
    0x10381c145030000d502090324010b41140d41c030f81d014020301241c04c00d0302c4211003008a10310344450210708006a032109a16021991441503101d020360150401c0240034014082414080c46000692810841618080800e80d80d4821110090350715a020092410445d44200d2034000c40007458030802d61042d0702c81d40041c0941e1001d0b00150002a0041150100b18400075100c80c0c01202d18002040a94181a44441641c4004194809000380d00350792682103500681040302403500a26440c481c006c203140480e444810302210021031501300f200c981c1c115840842c0031000c1341c011400ca189008244006000a4040148629070000400b50400d8036426441c0c001031098030407446c094261541441c099191100041d040f2540741c4c0f050003002a40e07440003031400c0c15250017484c0020042041d00040b03c00c9151078020b4501c01c640828108075009085a4519426409464407146245d4034024007030542d801022412031548005500c802040300480103246081c001e05d8164600003010070304609446 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 741264550 1250 741263300 741263309
    0x21040306050c220f06031d01020d0b01080106022b02010b030d0e04050109050403051c0f240b03040512030901150b0a12020c0318040e2a0103050412030213080601 71
    0x3440000c8940360384545408900c00d140d00c44400120f01c0c1d0900000750301c41d4030140103850a2560328181c8264180d000c009192003921000e00032340d03807419140400c0010f80021950b0601044540340041000c0e40046801292110042c0026100642800040c501001200120401d5560f030304640140c0b500d0900154003c2e0320a81c48401c10458400c00b0300c821100f059001c01403203441c107400c0c0720001c0d500004030791084e0420354141080c1d144024680008105600380002c45610b00446865074a01940c0503020101021200c5c0d500c1d0341d0f81d000420b10302d110444000b45150880d404a0300c0680003800910740002c000f07000003811070b24014200000300c2803a08407924550000c2040c41409600800520103020080000d50608440740700071513690041000345030352811422148640d5803030f00e5020199400d080c1080758510781640c040401e0504060301e07004495804082c01b10100d50103400303054003c0d0703402512004a0808c0c2c2808030025004400007200d460000100080c0038401000a1030180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 741265800 1250 741264550 741264571
    0x2070602100216020105070203010e03030127090816030311070b0115020d1202070f020d0b041505040b0a0e0c040903090f080f0c060a09090504060207232104030605 72
    0x6810418040e1414040302144041c09004000e810000c80e001074640c888580c0c20f007800c40c3c40f03085030710000f809041502c9400303406100110002904070181644082c83d4550080d81942048085500005484100b4400341c450201007000041c07583d040508400200e009180c00510b0401c000c4003010b856000010035940c0606000c010701c040100454000c0303440c5042c1c0001c1031969100b032000b40804490490980710950f020a07010144030900c3c4c41d417006140e0090140c4001e102a244c02403c1100a80b802d990030340d824074038100d840080c3d110303d5018a401c419200b0701944c80103c40c10281c231076048501801c0c0034840782c0703101d2500d41d4081c800700c06109442d8101450700304012041c60b43c19540c0314040f00c0d4400c8218a401c0880800c82c410403090903120203940d22030000d0305079038000041d0b01045655180c0030030403003441000d9020300a0b44d072287c56544d248480440d0407585440d50210b41000a811030882001110014401c0c45842c0c07214059460400e55281c44410840d01c1c1290300b160704 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 741267050 1250 741265800 741265813
    0x1020606062d0c1b0102010911100216081005090316020f0f030f0a350f0f0a121107110f0f03010f05040b0105060301030b15130603150605030606100c0c051002 70
    0x302900d88808a103160344c20300c000c010000c0940c66860b0b40c0c4404d460130500402018440300c0c946403082c0200c00025031a410080482a51104030580d129181120f17445203501e04400b0414050001c002c43d46181940e10300d10802e04030355001c0040004202c500c40da401082e929250300705480c240401408089074a0241c50215030b942400080c100e0141401ca050756061482c001c0e003c41542e00c1c100300244108449504e41c12120000c800c6c911980c0001c0d02612000304003013081651040b010300705c0152007401407241c0307030a1008450007406144001000000d012000c1015410516001200444024407804121034001c001ca030840b01040020309c078907915a8100014411720125035401040c0c1525203c0ca5981746440e001d6102e20041c0c01ea4818810304040c141440d91043e1501c1480141c403081004060740c2d030b241c0602e044001104c10320741c990618100160038580814064810030000d010070109220304402143c0003130300307858200d910356658900070074161130301d000c4058030003100d8008203070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 741268300 1250 741267050 741267073
    0x6120a020702031606021905190822270f0501260c101115180d0f020705130e060f060114031b162f01020606062d0c 51
    0x4000901d5a150058403903c8000c20172160300040500c01424103070481110700c900741c80e2450826000b080708110036044c035039490007880700e480000d12401c494030040703403c000031034122a14192002d1040038001c501c0e101c466200e114401001c98402c0b203170b440c00010301000c1d500141c4211002070304010300c820384524911400044034001c6140420a41c03005006c1c000d100f03400111400c502014000c02c000c3c4808440c0d0381200104401e00c0390405001d602480c501d01000604524901d05081c0015403003035000d02802070780595907108103440d91350701800d010350030030090000700003d00f00b20200b120b45c0c0341d1402007416002c4c804540104540c1d001425282050000180902d146040401c4064030400500448050440c80c0340407000d10183c8140d02c5103418800703429001c00e101c0b00500180701c20403521480000c2100164008508850b40c0c120b424103210049030f90302000c4682d6900050100500c11269900d15603540b402d910552001c103034022065041003941d00b150180706000c0d8061819045c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 741269550 1250 741268300 741268303
    0xf070f05010201020913020a021903081e2403030409140105040b2b0314030703090209090d0e06180a060203180d020619050405031b1207060207090b06120a02070203 72
    0x80288030900c001c0d070820441c0c00000300c402044034110309541e0b50009507211101e00901451444c204004a5841044500e0401401c080c504682910050300c0c8080185513040086094038000c100b801c44103500001001c01c041d403378440030328046501d84801d0000042d48501070180250480d1042c81301e08095240c42c0502c03055501720030700d041c89a90143c2c4900030107880c1c642c4003c40111030402c40481404030707083c03e84506120781d5200e81d101900004100800e60180c102e41901482540c40700745aa4039440000c0e01c2d18008500303480010020261540646429070141c914001c0284003012119103080015035840c3d03490b4400405a0004106100c01c1603038032850b041082c20031f40d0341075030320a2961f0000e03c840c881c040700c5140c14042c00e4103112500b44200e0648000e00030140c201c0c2d0746c8020b20700b90350019010020b146442240c07000312040541102242034012a00681c0041c0703011800c09204c0e1024250740b901094000c01c1c24044443e203880f51030f101364003854041e100141c0d1100c3c3c074014035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 741270800 1250 741269550 741269579
    0x21150b061b0610061707051201081b060a090611120a020f060a020f030c030406060e1306110c121b070e04060e070f1e0503060a0b0102190c030204021b0f07 68
    0x241c0396254000c0c001c001312030304110403044840c1e40c20500c443c1c5a41d50740f410340ea10300429880803c040c94040012945010001b02c044000d14200e4007a4241403494041000c40d00c5841078040001d468140b08202d264025000c190310280000306403107044164503404611a00080b40450060f840420680001c0c1d6050091641000e00b0405c294540050102c03120614030018260001c0c81c8070000c001400e00c0302a40c00000030700340000445a0b50704003c00036800702c40000307034181c88031031802c4c3e0707032014035500201140c00401600d009040840d40320321010186810014074161440c0601d624940c01440500406024042003181d43c449400c20f820050211180c4407060581a4020081885081c0740e0245c0c00044130004a0b4422000e5032640401d69442c20650100340c043c4601814031410000741d07003003190940000c0c4d00f2205c00c0d02c4031440c00f0b02e05075a41c600141000ca448681800982080c1e0000c080c40300301414195003107224001c4041c07603c5a00606e41001d6004090140701c58032000100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 741272050 1250 741270800 741270811
    0xc1203020316140a0f110703052104050a0909080f04030606030c08010c201603062f04090906091b0504150e0a0207021801060503090721150b061b06 65
    0xb6582004204001c070f4a03a10400300c162090007081c3d0100b10b140703841038940940030701d80700081d2681c0c3c9689280440e81c400741032802a040f85000c04600400b1b90f4503500751022244010101d84110f464504440010300d4407040681303071024200702e20820040044028001103204e0000010100d02d9030420040d00402074101c042983d0528040c00c605940c0642d20707001c075541c5ca000b00071404004800c2d480c60725000c04000c44801808400010034001e855010070b420041a00c00028864440c4000c640c1541e80c0c69006281c1a00910041c040400740d40e01c00c15400d8800d9200252900041d00c0703202d002d040620440002240b000c13002d000505260107020b850306201d298070314100c3d080951100310301d60002d00143c5103640c089644001e5590b200740707148000058031541038803942c448a000307085034000c07108100c0910400350000342904480c5100d10301c408151004100c03491103940d038076008050a851b4002010f845480f008c001e580d5410003440c4640403001784243c24142d10842900f80b00c0d000341f2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 741273300 1250 741272050 741272057
    0x50309060f04050f0409020310050c130f0905090d02060a0b011404080f100b030a30090614090f010302031902030a090309170d0f0201020f0d0204090e1b04020a0c1203020316 76
    0x6c403600140c034002078000b486d520000002c50141d913015008000b50081407402002d400b03800900140001140007103c090741c0151006018560315800c2e03469503000810507000060707000070300040309401d07660f01c03441c2c00c1d11052400c040b03c0c6903604641001500107400c812032301d07005148404002c141c10000f040000c40000400d024014401340041e80368900500080c29846070003600300000071014982c0e00e0001e03070340000d520300580042401084900d1078002d480200d00e6121903000341002d58410740350101001040700c0b03900d900210044000e5040908946445d0140304007440284460340060740c450350f0403c4d8006005192410010040300140d407003e006100601d90780c2d001d02a002c10b00c50780d010240c0c1000d842100d9205e81c120300a10980603405203100010400c100700810b0b40c3c00400407038201d035a0500100e4180340b11140c403510090320a4840c0d000d40001c6080c1400d25070050003e545050825207a8000c2036250120380d040048403900000344d0002c00c0200810702005224005035040c503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 741274550 1250 741273300 741273311
    0xf011509050f0c040501260a0c080a0207050303010510050d09030f03200912030d06140111032703072d0f03080703050d061d0a06080c0a050d050309060f04050f04 71
    0x4005113110382d004503410415040ca0502d0705201040240c45010307103000001d501171524500d0035005001120340300000490820114509007958020b40d4802c41d0000c01443c6103174a00000c000c20030300704280000a00c0b00620501c04144e81d9441040b80d124005d8a4841f042821003000804aa901c481d440c0440141030048100e440201401c1c1c6006404c03e5030400d11065042242d14998000c030741c40007010500300703040810740011052514510751801e0300e070071003107440507462a6140e00503200904a2807098200c07403d1003264400000f001c1000140c1075540d21503d4108a822410925200d040242c40f1409181880e95104540070010700380750300c080542606513500d81a281c420413201600300310010401640303a4201e42d0262005040c0040300700c07202140c200110221072000c4135644052071500038006000c400c0801c24458040c00100240314413410301c000c000440447c41e50540d0703244400d00c6504001e8039107100610a2003185042c03070383c95030700c1c150420540d142d801113854015400c0c10b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 741275800 1250 741274550 741274561
    0x50405010e1015050415051023030411090c13081b03010b01050708030a18110901060905060a210e0a0c05031b060c010f0c0e03190f080c0f011509050f 66
    0x241c0c3d19000c1d904126004242c141c0e200740091400100f941043e544580700e001c1c0410400e4200808006c0a01034502c0e0051512608580b03540902089070090591350203090450f03250324211100c940d11010f4400d4442c10880069030720340c141802034220503425807020500328801c5a00801c0c0000340740c4120000d018000720200000d11070302441170014092507011001c0b604280b4207170008812000c0050400c3c15175160341c100b0910014000040710f01903c40c81c00045411880781000360161000a03040c0d42c50b10000314000c46000b2510310156140140c04540c0381c001d48580d024501c10220503200818400005003004040b00708a039111074070a9020004082c61203034800c1501004c0302003260915210590680ca1a000d480b69040d42c540152528000d114825084907035114006810703800c940300f02415400804c0050909280a094580e000c0d0545000501c1940141204a65041951507100b941403d10342514098840040b02100481081c840c20704607114442e44140710014401550425 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 741277050 1250 741275800 741275831
    0x1060f0812031e1005030a0308180114150303040e070c0c0e071b020103090b1801111e0901020708070e01031101030903211503050c18070f030b0d0501050405010e10 72
    0x10042c1800002c400c4009003007140801031500041070081e090b07c9422150b4907000700040b1007240c1e03c1080c84181003038403001c04014440d0583d40008104041d5640d2581e0141e03129014000306c500364548003c10003c01c01c5000102500d010380000d40740c86902082e42d140c0b14503069003541204030b2089190080140345503000038015400a03036007090b040b41d6481400124003408031040d02400c4860407030140940316080e510803180e901d42d070310b008028855081140b03180c0351142200781d62104141c061030007008000c54004000405e0705004442034140d641c0050741c10689907501994550071160010010b1011003092000700041c01d00e0300300310b458402e030340150203009003c80284180020090304402030310365520414030b88c40b400180081c07181d900d19250340d030307203004440030b90080d4180015410f10001c2000c2c0d66018446984984100700c5400004138000e00002c62105c0d40040347c8881e00c4c000c501d00b84201406640240004502d541034083c0062030028002400315100340750440c01403450a8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 741278300 1250 741277050 741277081
    0x20411190507080417060907080307020109050f0301090203070816093b0109060b041a0a1701140403050c0609060903070b09010929010b0414010309060e01060f081203 73
    0x4190600c1030b1615041e00300b400c000d006580050070810400c0306140b8845000080c260312862580c82203078030385d41c0c0394070b0080e4403030290540080c0881c800003801d01c03c610b040c1d2a8103c158101500000740c40510ba00000c1c50074641e0750004100e904413641d00481c1030074081c074200181c81d100c1014060744024030341c040603030440030105c980d07034030702282d0f16109004080c80b1180340700510b48000d002201e400d06100d4010010009078910070352038008440702c002410030f582c405021000304441081031411075188085031210301614015540c400b007210b201e003c1401d500380514003070f076105030b11405051500d0340342607030103003440031103900c0358003040490003000048076003255120b0440c626039155859145d0241403446d0340200311003070904241c41d1a0600134001050304c2c4030380070b1004060743d17034080414180c0b00360302444580c064480c041d42e03c02e5009810200640b0710541c00014800c44141c009403c444142d04000b2254140c00000c01101c0402c01004041d05110480030b45907040805a0940c80d14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 741279550 1250 741278300 741278347
    0x19140702010c0b1f1d090705061605010213060509090a14150f030d020f060a0902010c020103110d0e07090b01050f03071803120315140d02060d15030f020411 69
    0x50b5841c0005800c0624580050344c001c03d480071041c142910b074100c0a4600360000c0c51406006080c00000781c0c0310b100000e0000440d64050304081c940b4500740600034000400c3d450640e810364007080b40a01c048040c030007010040583c2d03501c00780c07150364041c20444c001030040c0418540c41e042040c0920307040c1117804ca103034000c03804a11502c2c00b0302115012455451038200026414003030740c1c60840701c03603401007080087c0d0742d03002c0e0542d401a5140709080c001c459140b01e010780080c04e10030510700194000d5010000e02c0065603111350908a254101c2e2081d0388a070350150301c1c40c0d009003004005000360b50140c156503920908201e400c0046040c040b40b07060000034111010803d110f074180c68030055461050015542161031094036100c105000f82c050300d1400340740d01005146610000301d070411a0a085401d0800070010b4400910300c0d02041090342100c1140c0c140c060b9110554a010b06a0b01541801980f1400b40304c640001e0500411040740c810703101800f0381d52010000e039000b850b5890482b84209 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 741280800 1250 741279550 741279563
    0x30e0109030e120c0303041206060e0405030412031e0c1202030f071509080c03040302030d0905091501030b0a030308161b1707020603130510060605090909011119140702010c 76
    0xa0b400110f050b4544541d01107015090b010016003c00c0d03c0c11018010139210340903684c1441916655a9024601001120040c010340c0050200384207188078894920340302c501901c0c1c140500702c08a243e0301900d900e01910007010440c183c55800400030100806d611018003400a18107142034081c55003024411008001d04960301c1204030543c003030b01c6501c1495081d030054051500c40040e0a0b0183da079910600080c1c0c8680305044550180c0d0380300b60307000710a90301c002d080c00c690707a140d8130121024030520070311441c141522004004560b0311180214002140a07a86407000d50600707001c0f103107000300080c240c4010025a00250301d1300c40a4584007244059014069481503074500300c03c802980504080203500c000c000051100108041340403403007560244050b2604940040800c00071a6254442c180c00706406002283d1245801d0807403540c04000c00001044900c0003507c0b543d10b5a00c6202c00c4000c9009403e50b40c80810350040943c1010841420160715140341600044e0001031501c4004010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 741282050 1250 741280800 741280819
    0xb070609020a03061121150907110d0504091406100c06060b070b06030d0c0308150a05100306080d11070905130c0b0918060d030804030212030a020a030e0109030e 71
    0x11500c034022481e000f19000312081000c0c64581c1038608590b03002d2034000e04002480c41c100c1c1040103403203d25038044d5002050203d640981d074000e01c88050300081c4501c0038000880da4000030490280200600407545544017070b980c90070000304e04200d82581056030704201b241c034104842a1201e240030320300840a810405100d0340145824406006550840000000e002c69000308009030f074800d460240104401b540c0b004554940200d81c811921000a03001a040300d01103003100c11061441d0350051400f80c400140241c42d0720202d034089032190000070019584003003c0126150500c0200c2218010349008444c2940500c42565202c2c0580203038181556148085060010020101d440740c0d07074081041010903a54440c034074295080480054012900c2c84070301101a016010300c2440f50304010b000c0f103031802d82c6440c100c5007210000e01c00c506511515030101d584a00003c0518440c802c41c2c4800340e40d4014a900040c01c0e6254413803502d000740e040600240000b0780040010b603e910040d1a444103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 741283300 1250 741282050 741282053
    0x3200a03020c0708100204060306050303120f09210c070f0e150f4504080c0a0c0305010902180442051812040303030b0105121806010806010b070609 65
    0xc11000d5402480d1300d1091038041320310116260003400c12520030303490810402d540c0d103050540301d00c2000460300c88071601c1c100084a42020f50111900b00d6001d8040760292410b00040910f004845600801203070f20210b584c3d200c0410030040b00010704903c0c2201c0e0a0185440c00e000038801c0064280002c50003a0442d407401e42d151142540f25000d0020b0201e2110b0900108440b0110a40320081c2d0180582c2003180c8603000070140b000d000b00e0006400b403090360350f60b6140ca501d0b54010400690390380c0100408080800e0203518414042e40c015400095051280d104110080226051190010700d03818104404202b1100380d56810f4041c03d20031810343e600581802812100c502c0114000b40a002c4040e0b40f07002107540103520a0351540040000805408801687c070981e41842c02d100c0d020400050001074800c0c0c000440c2c203541810042e0501310410f028540001c8111040421000e50500e401420482000424010300440c40902995410041c4154651140a10103890140c88820f000d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 741284550 1250 741283300 741283303
    0x906250813021302030403120c0e0d0609060524040b01050a0e031507050a0206130c030f1406040f0b0709060f140c07060c020a0603020310030b1f03060c03200a03020c 73
    0x12042d80c020301800c041080f10340c03400025041942d00341c00141004613421a03070a66803007071031908080d984508000381c049804100800c040c900044540b9511495a81d0004160f0301030603001e90003035031941144452004600b0402481907407e58841ca007412103514107a40c211040b07480c007480c00e1400b00c811420b8800031a2408945000c00390741020060100405190310201a114070040d903402d6400e183c5803464842400c24802e4005496501c64280400000b04501000140e030f03481400c6c00e454481010740038a0400900321003c1e2404022024000200443c040b18164001d0850900c0d08200d41840d0700201600c200280e200c0902c04448a580c0c5070005260aa4032480348500495007542e803641d40042001000381c8040f40180c1800c100031464a009000360303441102c1030080001224515111a0150340c03002d0001c01562080303003c1c42311410400801d004c051401000d010540c0944018000c040b01c00da42c0c1d1609400031314014005403503141030100e078280d03141c03843d000d40c86225080000303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 741285800 1250 741284550 741284581
    0x121509031b010c0e0906011e1d090f0a0510080703050c100c0c0506030606090d06061502032803060302040f200403021503100e042604081f0e031209062508 68
    0x3007480442e000c25170344188c1d41c482c41c120382c0d00508010744011b4100240500601285c1550b0015044070100c001030b00c004003a1344440e500070a50100500d4031a50342000e242050456002915190003417100030416080c585021000e41203246811050054151030705000742c541b5008840c440c50f000008550241c0d60082651002c0c08010b01c0140c0e400200d1600c0c500030500752103240c5c100042051094201400402583c030a4402002c9242e84182102184a25800544001418513690b00c2c000304c00b60f02c540c0300f04101c100326210009075082020100f02c2484034140d40c5c04162400800090005032928605151000d05000c4095281e86480f01840c00408040d0402e06600110000f00014481c140b90861030700160605070b034043c1310603000b040c0c041b03101c0c501440200360701110040c080440903484029080c802c00400142c9811204902821540300112021040c1018014841011401d019142e0030196150f51032183d603050312401d106d4090051080014041d504000850a45500002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 741287050 1250 741285800 741285827
    0x1404080d0b03160914070c0f0b060a15051b070f060e0d061118030105040c180e0106080d03140709030206031f030305030906070c03020c121509031b010c0e090601 71
    0x3d19140644821501d03008013500959550036480c074801040c0c1c083d0160103d44003103030304035039070401c070010a848100d84010003804c0250002c80d52a03000030390340568100c800070808ca60795210368484005040214646103504e251416400c58141082004100c504041c201c0e2403904000c1500b5040c540011f2121560120207000350f07042071644401401648002c15032800202e03a060200405001410308843e4101d030020083c0850001c240101c0074400c4890042c062501070210b408000800e54609441c41d56002126692207814900c0100f500b5004000040c11480541803007450903440081c60a407403131001900950000000c40c43c80c80860300b0001c1c403645054884207a00d592032034014003540c4110307143c620038015513020841c09849000801c49158059009250140e13000381007100042141e0f0315500c692103580f40038548001080065131003003007400069515a00340300b180100141060094100726403400e8800c6040c1d5411001a8450010544248041c1d60f00c2200582e40b01d90301001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 741288300 1250 741287050 741287083
    0xb040204030506010f17100e010b04091b060309170901020f03030f010f0918030e18040c0509010f21030314130611042402160f0303031404080d0b03 65
    0x3000300500000203425412140401089058266592448040300c1c03030000e0706508a1700107100e01581c034145900041d140301d104100004e0303805482c8002900312110071a003180c1d81304440b01030b005c0c00c0003502c58050040104d401c051143c99641e41d41e403c03d100d00020341e0516030f500400d80c0882648208280d80c0341d17241503c1126036078100700c80c1c00c20180e54244103a00380a041c0c41070105100c0101e00403001b080952607981482c2c041295019524181201551500300508010746040540002c040710302403070041c496000c115062200780049018142c0290b4034000c1848410440304040411220808040d0114040c1b4403482e440e0481c003400c95a1544d80c030f811001020721071840c00311201d03550203602c90001040300400c0400c14034094050f906ca4001c101e4980202c083c03003624240707260301820300c440c816222003d16200c60320b0180120fa03044040c2540580d2014820180c1520804070101ca646480660501d029a00ca200c94030600c0080c0d40e050351a080c4c01e14142d1010803642440b40c041c80c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 741289550 1250 741288300 741288307
    0x8041502060609150105030a0c12090b01080c1219050a2a050909031b16060807090f050a05010c0614070512060f0d020904030516030c120206010608190b0402 69
    0x440203559600603201c19102e00060f80c08a501e80103460781c40c0c01c58000603100d003401c2d0356480e0010001000107200300018004004d641c503030740103094450507030f203140b14084298455041ca4007079841c181e00901030130f004420262402c0300350070f0000b5200040341000c401c0c09000c7d50b064641716041c10702003500103003082c00004c001024459281d035041822801c080390b0703441581d5030b00c0030045011170590b000c070790541041200e5100c042100460700582480d04d412500d000001c3d0345602256241a40303d040083c454505100b0280d0340902c454006048865040700c0090801c4000380600c4681c0c030820341403258040c114003c1004641001000240990b43c031101441c010300003415540c01700f0350400d00c61841e0170000314145048056503914031070282150400501d1582400008174000c1c0003501403200038001b940300500e10701c8102c01840c0c0f103603482460141c510310b0006a0700d400340f5548401c0d504240c0041c40001c0d841900705511203060400b800c2c000d1005020348009101951015800c140000f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 741290800 1250 741289550 741289589
    0x6050d08070314030f090f01150b0901051309140124050a030e011508150f041419031706031b04020a03060302031c17010f060302070327080d0314010e040804 69
    0x1041c580d1189a11809945035401c221f020642201d1b2443d64031103020341500d005001241c080f0020f407682001c1030601c4c6181c405002c2c00100e50200e203074020280d00d5141c400d4201ca0138131484e00d0368014081039100640861380c145001e1082c03144881c45004004001c501c0218079446608441c0c215041c1c0070082014041403118071031000704901401c40e80b0320610380c0f004520a1680741d80352080b070310a0480d108680756030b038a011504803e6018403529105000036000750b080c00d2402042070314440e0702e4041d0716107c0ba5500751001c43d00108882d10070b800c0103492100d9159192840310503c4422600143e40f000f07200b2040d0010b065942010350144141c4a52040007403500035429842d8140d619042078400c1c440c035002e25014800d004000c0c070007400220400130f40d4043c0e0040c11034a0302ca405c0006140102c4150b0306041c4031041600030191191a408002c00c180034458122540b00500d0103202c20102d0040b40705031400e043c4220030f031030201003000806001c1c24200b43d4028100c1e4113120442e01c500d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 741292050 1250 741290800 741290821
    0x711060d0605090a29010806150403050304121209180b0402040b180a0f0b0a1d040f0f0608010b010c0f08090612010f0e0402100e03010603081c0b0406050d0807031403 73
    0x2c1400348407440e141c2d40350145010205c1c3c08090a8078140d40c1c28245175151028002808150304580c03e00c08401c0c44040f0020358280b0107000a000140d04081c00e5031070504221030082d40c104400020b00519407010b000d145503581c18501d10700207100012030405140d60209000348240e5001c0c4a407414082203103c40c04059682c0300d0140c0300115080c0041d941c1760790250210030b49500c903c90008108201c2c0240c03150180c4904001034001f0f840d6050b404191802103800d490300d081924092650b190f01d550060302d058441e40001c3c0c11110000c010780c20040002802c000c00307540000c0c1c20070400e104480c0420500100722456624058030843d01d030f00d4a4544034413440828040d03503584181000380403459284442045101c2c40d00140010f50091942e001502e614a90014094265480361404400b00e1a01801456802204140650074000c0410141c04a49240400520a90500c1d10030003040d039404112107042504140381547e180407034034082d280c281400066039141c0e20003204000c01401e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 741293300 1250 741292050 741292061
    0x13031808070e0603030313030c1e0807050124090e3309010506033403080309070512030d0b0117011e0b03060916120f020306150711060d0605090a 64
    0x500e010540d400d038540f00304058583c00120380752010341854990a20100380704041858041e8041c0c40d24803403081d500400f012599070246815288110009a25000c00100340300e040c05007215605540810b545210131280d00030050300c1050107454a800b1040c0703900301c007405528411101c000700281d0000300d0745081810f8103c008981e0b4000700050000421015060040d6441004000c016010901c0c1ca8801d86045c880704501c112068201c0c1c00d5000c101c8419a11442d014501501c001902c03803804009041c074284d101c0d0030103805286085402082043c001081d2001503020b4000403070340144c0c00c40121443c1a8140e21380518102202c0000b4649182c5040104030043c551039108040380c541800f071a807480140c42c1945c00c141c5500005000e0100302d0446407125045140140c0e10702c002100c010b05842c0c0c03403d82c1c030101c1039001041c0002850300c035001d40b038406e210042603420704142c0d40311b44c510014042092070041d01c0000740007404486c1a44040c010700001414007480f0304044e00a8002400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 741294550 1250 741293300 741293309
    0x5090109020a0501021f1a060a0804050c120303040609240c08060108070c260d0605041b0f110a140109200f060d091e050c0103141303180807 62
    0x414444081002d503c04075148000341000148644c59604500000005003070040f1420301f900000b880c14029985c0305401083c4413900c1e5a5005080d080a0403c64107014401c092140324105e04a8a076010700000f10580b684070340c00403c00541d100b0a4106101eaa104008003072104000310550700c14429072580c42000741c00c100380e0315541c05640710030055800007400c1c0c80e1f40d00031440d0400303030600050000d035103281030f030321840d5205118025028100d4460317040304504901c03281e120002405142028821a82400e0240d81543d5020340ba01002420381a0365074030400c00c10400d0040c4445110702085400c800a5008110b191007221201e45503000b410070712001c88440c07043c0611020005070038200712003240801030611251414520400c2180e500c80901c04c0e600c0c6407200d0081c030105070b040305020f280c20f000800224440c0428680035040c88032181403541814580844401240c00390780b262603014101500c4500054904e042c1500c075520080d24000c240c2030714640100310345101140101c00c48 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 741295800 1250 741294550 741294559
    0x7150501030326010f0308090409080f180906010f111510030b28090501090b010b250510090218070207060e0a050d0308040f15090b06061305120708010509010902 71
    0xc44405044520f8243c0070f11400795641d85050043c40483c094800070f01110800900020340450f480d582c01400c0d8006110400c00d000001c0b5505022021910861a8029007200c1c040e5880c9400400038010300300ba650420108000f05e0241c0000e00c01c204000c601d41d14060b00c10803064034022010402c0c1c88280e000840d00c1102354400f00b000d10845042c8448100e03550031417481d10100c5581903000500c00038209545540d20b4803000b4010961012205020b000514440740c0d5a000322018041e4014031240310114a61003981d04001244003c2201080294842c2009c24802d0b00d900025060f044000c01d00072002d5418130501820719000108a422140d464403482c030218040d8003000a000454441d182d000100c9061142c000380c0310300c41c0503510501c6142c40f030340c02c50030944a5107600d5180303070301240c05142d803001d1302014006800d40b0340c0c0e482007040360304624005407a444040d0032182c07803049130b004002c81416003d15210030301ca120b019080c060020000d901d0544c5407039010f45400380059005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 741297050 1250 741295800 741295847
    0x216110405040b0f07020304091b021c0801091a13060303080c120f071407030323011203030519021201031b031707150603121404050f06071505010303 66
    0x50a007402018030558018104020036a1064626a44141c1c010010011400708000108814455201d60305440c4a414542c0303201c184c403104082d150144a900c1110441780304180084403692001c151410348400c410017080516054030788201c10007903207900b01e5000ba03042c030b1510000c0e051a842034044030b000c1d0b683c482c03081e143ca000c1020544209038242520030516000504000c2d51b1034091500029545400c1c81c000b00c1d00003080304107421000c1c0c120f00207034071010111001c00d000a07100c1801d0400740e40f210101c1d49080380440084525800003028183c80d00c0026609000c1f540314450307008000002590b4480c803640000e202e0b00424041120f81540c015100189181a09280c509480e80400c1a03a407500d540e403102020358014010850300041d403441c41c0b80c0ea08099016040045119080b03042a500305000003808400d071a80351002c280c00d00340404c101c581e0360380081d031941280c184c4200d03645200c18140180c58060030707400ca40c41c0e1410a40000704069005072584040129600d05514 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 741298300 1250 741297050 741297083
    0x11040f06080316113c0604030605091e0c0a0905130201110f0a060b010e1906050f040e010f06020607020f0601050616060c03021804020304021003090c03060216 70
    0x21940da5004040240c1e00c1800200749414480814a440701d0088180320440c1c0c884000192806034045a041c148051001030344c00d40744503403202070300070403030005044c0c40311032000001c42e14502480c40051f00d125100c4010505272032091001c81641013144001448013007c2542e15541d4200c1c2c00e028502804610b40c00250350801c91203407234020a0f258a2201d80041d01e6001100c00e05980d5500d0b031424090703103070402d17a001d1b000c1041c5040385108940104903200d4000c009054a10070f18000e070b0250101d001141000340d0010315038801c0e0340643c10510748400c248841c207492401a070300141a5910310380004140036070000c000c001260134990890383c0c0d940c0c481000f2a00e4900a8148181c3c1d503203c0401031107145402406008171000b14565606c50b0070003a219101540c14140d5620040381e400289007403200e845000e04c004000c0140c400790b142d801d2640c04a4207200c800c0034800b003010366604440b0208407803020001c00954200380d05540f01c115034100d90740c004003e800b04a0b44030720406100c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 741299550 1250 741298300 741298331
    0x2a07080706020111090927061510091a09030307050c0316080606090a0f0c0807180303020c0f03070b0d020306040b0a0303020319120c08010e070503090703060e03090d1104 75
    0x3000d000000213080e007805140b205102400350094030a000c0b0010b0315141010300c1d03015501626100700ca41009007c5d03800c012101001c07042c140c4c2e5186008040307480c40d222983d5084400c00d001c9441a2100001c120390341001000c0d070313008100019a160000050034414014005080090701208800380c411314152017041010941980c031841070207070401400541c41c0c0c6050303042aa070068500002150b844201d0384898211200703c0040800304400c0024030008070b501c80d01c030700d20400804090811841c190784010b9512070300e022402d07101e01c6803080e5070030f80d0b40c405104540040c808003012079100c075290306141c4082e410803518540120316116903072a107494000000c40850381c05401542c80c1503080d04501111000c3c00c0e4450301070055440d000848007403544194284110303140c0d0707510519410f0403c2d84036007040203402c03101040418030a004d1500d01c04102d90041780d41c807010009903800c404191504500440c280310b9800b40c010300f0000c0500005034102482403000307d5081242c0895440e40c80e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 741300800 1250 741299550 741299561
    0x120b0405130807021908031306112a10050a0201240b03100506040f0e1e1909060c08060f040501270204030c120b0f060603040201052a070807060201 65
    0xd0070320181d40d50500045550702d4000c00d03035180058660820b04000003204481c00d01c490744052a55400040d5006200f00b01d820710101a007060314000c44122140e1407001d586050441e071210700c01048000100c01400300e800c540f8160706029001c002c2c4001442000341040d000640c40d03801550800144400d00038190811401c1484001c840181e03a0341440c10003005500f004000340083c203803100e00818070b55502c601500c001e00c44880715072411810481180d40c0d05c1000317800c9043c0380c03800501c1c03440c02a51410344c5590005c0c0b848058000000508071410140250880180c41180303400308520071320307038041d020601c5414261003283d541044042400220f0b5424400c6816604e580800ea90006402c1c2c610071f004000c000d0005800c0940f40d840d8032458102c0d6610401c40c0d0702c0d940d1280f0080200084e00c040e4010404034032000a03240003804200d00344030081c0024100400001c18604440c41d8481014403020360740141c20a40c01025040c0d5030319544d50240307000724454403e001542c0307881401007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 741302050 1250 741300800 741300811
    0x20301051305120f030708071101090809100302270d080a0207031a091209012615030f03030105040228092414070314030c0301030b010f05010f0f14040303120b0405 72
    0x142861350303441d15030880340447c003c0d0102041000a5a00621104090040880b0b04d0701812110b03030703100e211034208003c454146007404107260040c00b4509243c0c0c000c0c21450400910b071403134004051001000a02905940c08005001c5000400e1071903009a0018419040e64440d40215007809003010440d01c20020484280b82958461008a0740601d00540908110a030604051a0024800140241d48800c1c1080300000e101744208001000003c035082e0610300b01d058001e46065030b500f603c1781d07460340302c140507090103190001040310304584a00300e8101c40c0e19074034800728130740008604014803001c032501c2038298404079000c100e5072842d01101d0700310001410f501d80d0a1480c0c4005201d01140e00914400d40500000c16280303001d450300d150045110310b1100003495a80d606600c0d00c1c019586041e00203480c80b40d2840d1050290b80d80002e602440109641000ba80381c1d400080e00b107a4065206501000340c050103d40042011380003d04004100c50440f0188154031815041c4012901c4c1241c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 741303300 1250 741302050 741302077
    0xb01080402032a0d1a0a02070b13030c080a1214150906060409050c04060f03061d09160612050108191211160e091605040e010902030105130512 63
    0x812081904922100800380c041c509401e4460004142c001010f14100080588020b80107001700b00d444142803501a50200446100718104445074807040d4620000921182d00c50303020340d1000c01418010ba04d401e000076440004640d4810109000034110f03d60310f5140d4000c2c034109420301d528040d107140810f100f502806010501258607100704070781650044e00341341c0c11490410011813407114502866104143c0d401d455961035141800042270090358001d01c4007014074045040c881e050100c1c5141e0030b200d0418204040d55201c0140791400e00d1515801c50189260a400008810750400d02c40042e44400c000300f04810f0b030761484907540b42e4000102d00032920820f481600009a1002c22032010481c60340b03806400070741030b440d00c1898030899010403d04c2c0c3c061034004000107181207100390b038800c1441018001c1d02c60303803071290040514030b0b008146c8036548690307211910050035885109a01d400500a00caa410200c00a000700f400405051341c007805000c0368180d0a001403002c480c0072420102 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 741304550 1250 741303300 741303313
    0x120331180c08090d0f180e0103020102060c13050f120f0d12060e070503090a14061b0a0804110d020405040804210302030f160803041b051207050f01230d0b0108040203 73
    0x113802c5860b00106035040d0306001d081c0321000410840e8003c4507006c0d150b500c0c0014040e50540c000640f50110041002c00d6046007040041010200c1d4a0100c00b1903605403a211120b9000c4400511482d10180c40b5036114402c03042d02284800c0c00158490591140340c03182d030791008144c2c0e420020344549001d10128031700007801180f00c05204c2d2008507800580c4030140c0d2480074881d079440e00300202100455804c7c0d0b0119040c003031381c0b02c151001c05800d804a402014a404044600a445424000d00181c803090082124003040d40301d0312030844140303900500400c0a413a0170300e00069160041e0080e90f000e0962103180c80c60b0700c0346900111071900d415800a6080106400500126501103d20120140a6804035000003031450024501861140c1c01c1c80018150004000c0880c80c07407a0b04c5544503810480c0e14092200307000c01c075081520802d65840c078510341090300580c1c00c5441412072420519100348184c0489280d000030340030a055035001849241245c86c01103170405c109940183d455000310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 741305800 1250 741304550 741304573
    0xf01050406081b0609040b12010c020613020f0111030d020a020a0c08060903030103080f07210e030d0c0b09340801020a0504140d020301020a030c0e120331180c0809 72
    0xa1014102404004001040400147c404101c40f226240b10401190391100c41e8048050b4040c082e081d448170104403c000ba440c102e800060254240303000450502500c0510640026014030840302d108003034000c259074034401080d0096a42003c901c064842c2080c1e81008601c646002c0f440d2802a58948010350459003161a4008154801c030000b182c0b40c0780800c203144c001880c0702c0045801610b111901860341180d0403000e007034800341130f880a101e50050703811081c2683e0403a0b80b07032071910b401034560045c56541d415110320b407609654400428017030320a50728840303000408401904444049402d0000c903580ca000900341c0c0586000340011030410b110600c01443c0407407500c6030929000700006100c0807181c0100c0e0880e489101c0103c00203072542c02101803103070400e8a1032568042070f20860310b50029408031540724025000411092036800c60601400c03061621004403600c070440e18600704541d00c14081c02030180814625517058180b40045d5001c074000d6804c98894080e00f0701500440600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 741307050 1250 741305800 741305809
    0x207051e2806050405090a090b0c07020303130b1e0c060106050702011b080d14130605420609030c19030b040b150d12180e0f01050406081b 61
    0x103078000c00741c0007081e4124424810700c0d101d401030003030200e922055526400d25050200c094001022140b81c00d05104442000941490780303680e00c814841102070300c460182c400a415442481d403c2c00102c2c1e6801400302c2d10407484001080c401c003802e5200702c921012461105030f2170064061523070440d04500c0040140c2400380d00141030f15881450010742c00204408104850000d80005495028000c1600c0001a41c81e2003283c28090345000c50103403610307100703034100d907034401c2a14000d04840d1108017045014100100c00c1040c3d8140840402c502900d0103100e00300c07442030b40c0281c84280c007079140d220624100320088901d5048090058014240b062060261440350382d00d1a9107056044030380000840d40d28011580900d104207034010460400f400d1944035401e034400401e101d00c12510019001810000514180105030704280503c01d0490340e00ba8840c0c01e4a0340316244161409040080110100c1c2d00d4505980d400c0300c0401182c0d03140d078161a40c0d1001c048c2104c0660f107a6000e042c841d0300c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 741308300 1250 741307050 741307069
    0x10804060e160303021902150d02090901060201140604110d05041104020a03060f090203010605041e1a0a180501021f0f020406020a0b01050d0c03140a0503031302010207051e 76
    0xa5900032031400000440c082c50000d01e4400994501507510040c0205075041c004203000745041c07142a006610281c0000c2c41844403110301d034403c15000600780d0410f0007250140c4c0d015441c01407403008250395a01002c0c0c042c00b01c60301610405034240d40024110b20b02441000f050850100c1014100011400030a0003000064000e40d81500a030508015035540d500040c0702c00c11203039074041203040c90041d080c0c2500c2100e420044280d07006000500072544c0c01419130302150b416020b004840354288820f9500076101e90041c0c1000d9810380c0301e1100e4030201c280201407400480d80d42170b503030044000c14901d100c04e15011751030060704040c4101440c9034851f802c0148815420200240840e40d1081a00407644541c0c03114002d600140c94120600c45000c21050041c9000e85480103160010380e00c140010405000041060f05041d4030001101820040c00c100c1325440f1045030307680c1c14041d4100c03076580d89941089005124a120114081c00c140b03110b40c960400f1440c040f8038441d64041000f02610 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 741309550 1250 741308300 741308303
    0x308040f02010228230a2a230d05190c080d0306030b0903030c07060c0203090904061a03120a0c0512070b010f050d0b070305130204091a1f05010804 65
    0x4075440c400c0100e800c00040c4d11910080007078081c0d550303550750b2a14400c868000c1440400d0f01400b60703103c04012802054403409203174040c26400180343c510440d003a070010000c9500840702c0c400360001c200d61074110040c8191000812000c0d02d1508490200104c0b094400002007564010548101c2e1603600701c13481d000c56510980301c581c0640c0c1c075801902d00d04100c0110600009841d02020014046550300d00c50700030b00341c04061482c5145c207039040600c911807500c004217a59a03840900f101240b00340103890040304010105000d034241414513402034007c10710074245240803204640c00301c2c60005100c0500a5940742440e09105480c442a0790300400900c00340d903d80200071090800305000c20060071100e201c1c40760301c400c42d410450141441d0ba401c2c0c02c80d41c01825070030307988004240d070011242d610003090700e0007081c80e6a8024030345105440c803200c000e400c01e04100140d03080040d414070700b00440d0389030081d082040d5184c0301c0e040030144450b84a206071824010013072000354442c03484c42d42e005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 741310800 1250 741309550 741309553
    0xf051909260f030c03040209070f0c02100311030405010b03060604021318020403080304050d0f0903021810170102030a0b09100308070206092e08090c010315080604030203030709120308040f020102 86
    0x140002d0141005a07200316040c00a40c1070000c1000704500d041900e09807c00951f203851301038008402c0303002e0110030310b104000c2d01c900e03c0c921030041340c0782c4aa08898046503004217403640b03e080600d0024043c0003007650300c03403003070041c5000501d103820a8400d0f51680444036031440d14991400c0d4030203e9240003c1610404141c0800000c80415004401107008620500040a40300c40f0507100030004a00004000204010b4450400c0980d40340d2141c00c0003030451414000c0d01da150180d8070034030740e0580e40c000d440070b20300340343302d10340c4904113502541c4101c41c407040c1800340122200070042c07403050440f400351042a0100701030010500c03480190810a201030000c0780381c420b904002580b000e40b2146820141c41d0420000740041402c00c02a0452142a082420781403c0000c0555110421038022a0401d640e40c203c070283c81c4000d911401c01407e403842503854904082c20002d440f0780c0104d8060380480c450410020382c41c181801d82042440c0c166540c01c0c030301e44880d501c070011015401c9082c2d046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 741312050 1250 741310800 741310807
    0x90301021213060e060c0910091503090c0503030702150c030d060f08101406041a06040303030b120f060105040c0509030714030d02010905070509090703060f05190926 73
    0xc11103075403032441c06450340c100d015180710040d1914100391644011004483d40241052108a010303070002e540000741e0032101d40c3d4044600004c115850082031703201d0f501c0040740c1800ca18515030550701c46a0444d008070450749030980c40e41c0a041d0340e40304014000390862110a0341d001181e5900300940540042017060302c2c5055400c0822005075901500300b110091400b80d010000201e041007802c81c865401d10301404010241c4610355079000c00107010780e0289848104948030000740c007c8011020400030100ea0700d564590030000c0c0104000440300c1c1c018a002505500403405c0011701d0644102c1c0c0d030000704280d070b007440e080c00003030548010050305120060010710100d0f42c0034410302e005089034842c1c0850074070494040526003000d0316408015645001c9290003c07600c041005802d40e24140c42c610340175103c00c7d8002c9d25200c02a40042d00d0989406002041004203800c240c0c0600a954420501140038580d034504580300204000c0080c407203454400108807807120302c48400c00601030010f04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 741313300 1250 741312050 741312067
    0x8040b13090606050a260a05070302120408070201030e03130918061e1a03060a1a06071b0e220305040902211b0403030c06021b0f01061401021209030102 67
    0x1600c42e280c03c4540071070310110b506050103500c80d80340301c982c10140345518940649100540a03010000d040107188513181c00c00182c429001e42c04882d030780300809042400c3c030315241c28181580e0304154001c90000b800d195010a1401000098078621106a1902e051032460950000300610303451081032103070307034060200c00c001c03c0841c800e9810741c40500d03440d043c007504141080c804407400d90500000d02441140380d004a5140040d034968000642c25000403d0300003113580808030a60300d00348583c40040001c403d010800d550003008001114141c0c040c070030030340780e200030521120100e40c00d5040080e00c0d0000c1c41d0f00541c200115940d20f000381051031409442d818048240e902c9182d080e044504401820f032000e1900401c01a441000c0c01010540c0d8030503184603101500c41c0d80310160400001494490902c03243e0340c12030399071100050888610307240c0d1030600c0d921203da8200c040306c154605040050a051105900080080168040c24498120013406101504a25800e50300741d0350a00c160807 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 741314550 1250 741313300 741313319
    0x100b04080a1203020f04140d08070c03050f0d050702040c09050402030a1505100804030c0c080102071103010e07142202030f0619050102073b090c030a08040b13 70
    0x9400018040e014005a81c200746140107454502c070310405204100600d80b00d10704009540a4906814280031000e0296001602d250440e20703001c0c0199600203201010000e01240c170740100d92082c4151161501e400b821300b620307171642c102d038540411410030005005140582c4000c1003104242044401561a0000300b0100d030406c4501c904000c0e60b40e40c1c54540d106203455000d000b04400c032120480c00d902403100503c07142001e0001014460001000e4082240502001c00038252101c021900e070170090503d810307202c0304107903018000d51030f1840780c60b41c106000c81d50b031050b110011024410403101100340b280780c00d01594030804448400c0c1c004003210708070b40000d6020b5031551b8200c01e020704103607080140c1c80b000f00c40c403818440e003068010840b071398000c107840003119140c05120496201c903e1550000c4024400c600a20150421a0540082c5400c1100d070069644201f114001c0361413200345030b81d6240026000d882c410b1b090104011840c00c070401004d801581c045241071003a0784402c1d18 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 741315800 1250 741314550 741314557
    0x3040819080106090509060a0b1e0f040306050705090a0e0c090424061e1b0f030206010f0b040e2202100503040203210d090507050a030606080c091608100b 68
    0x100014041d80010803c01e640150b0040240004a510050780e05010000400c44e542c50700c20700031482c03c049a800c009945008036000034100e2800c4955a596a40e4203007405a881800700b2140c9629080104a200780300c0c1042e21040c000182c07010f1401814800755505400c001050400b01c64010821036515454034061074101d0303001e82c00b80640b40e03c04030106580c500e100b6000001000600d4100c10070080700c0103d4158000030398101503242d00344801039901d01540000d005048084204102d008040d80092281d040700e40750345034804641d0700c2d400300b8040d5120b80e00c1114441c1e10300e2808611120311086070810360410030b24905444841c1c560203c0c55280c040003042c0c0201c2c84c040f0030001541401c1c03150724080b00c452556030902ca00070b120301c520f030703400340d02c1854098554030052007040080c01c0141002170720005203070b410116035a240020143c0010300401d81a4000e44000803294106101c0c3d40d07005940e80c07030380c4a40c100c0d48900c044407a014018030b0140009091440040d03c0071041008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 741317050 1250 741315800 741315847
    0x240603060209040e0c01090905040804150206060906030f10020f0d110d0b09040222091e05010e0a031b11130b010e01020c03061b12011d01060302090105030a02030408 73
    0x540c5949110040104883c403000e403d44281e01725040000280e039000380020184e81600200040c03a0312182808440e030701903a04330301203c91841d11191000c0d500040c03801c0c46482c00715120100756480300c041c103440d0a0701e184100300640c888051610a8055a0054640c01c40460009800c040f00940b00d0002d0799245104000a0100080c400b03140640a000c5c000f10040c00351060365882c100303540442d0220b0b2200c010100b00c0b9040c0d20465142504503004052001d0300164100f403003041d040103001e1240344522046074503620b4000c0c200020074000c1502da4880b07415880f00111400382c0e03841503a40b1907a030340c0d04480789030f042d1181449640c0c0c1c0d142c820301d00300d00c10500081c01a00c40000905040c50070346030b01b810b5502c0f48030101c0c100d650004d2020b0784a00c1d1102c080714103282007a601000d82c01501d1100210610060020030074042d04440400703404042080d85480d80d994410070780480c03040010700c500240b030400014010315000c2c0c00441e0410712a19000e40b603c9a260700c050040c3e22903601 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 741318300 1250 741317050 741317063
    0x21f0504032d05070501090b090d091e05010806031c0f0e030c030606042c060603070b0f090d080c0618060a060819060b060d050f0112020d240603 64
    0x1848289580012425016181c018101121080e242401d151050316010018100000040c104080005c20341111700000e80c00111080503042c80d40300c613074940441c1c48c009070000711800c60001c2c4145c540c0074445141c101c483d0b100011141842c004594800c4020440381d0544956200e8031492440088000652100d5503226000b0004031040181489030b00040d00d80329900c029196003a550303000c200c0c0d07a00040110b0380051100c410000c55222100a041002c8000c10361036206140060040764107072007583e0032029600f0f0281c5540c80c905550080715541c0f40d019000703110003c0c03641080724145003100c0c0140c4440c1e050003e5004545d2030542c0803100c03482c1000301201c0c8015504010000e490300400c03052402d00266080c411820780e22145a005140412641c4846d07905101c200d038414000000064a466524029450010b024181c2500c5d01c00c02c450385203000260900000b40d9001d030255005203843e14281070f03612002403620300c45000400c880d8800b202c0300c0b81c242d8140303d2040258420746 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 741319550 1250 741318300 741318311
    0x6020405030d030623040e0d0c021f4b0e0a080307020f04020d060803071e0f020409030e09180609010501260a06020a03141003051c021f 60
    0x80c2858100000c00020209140c240041445070f0400c90542c101c03006001605621002032100005000c0c080e25207400c2054000e08040320107070381c0c0c0309030310ba40707014000d9030f0365100c0700a00d800756212504c40215070300001c1c10103c684211202c841c030f0281f01c07190f00d6899101540300320409204242d800d18039030403840324408507a160b009410804024420701c040310001c09182c605040c282e224070920b18000d200f8001d8410320b107200d60300c0e50b054030b00780c40c43e03c4420460f035511045225541d030b1284c0c2065415040c41b020581c7c1150103503070b90307100c4c0b0340d0301c12602d02a2500a50a102c05000850380441c00e01c4280e225050b49503d5084816101d9490105400c0c4c000c4078240078142454400780c82500281d041100600940d41e2040d020100c0040401d880c502d0342547c1000c8074245804440010b00d9039000082b207507202d43d4075803c825690b50904074002c003580c81c0d030015000340142c2440010610b80225100700303506108595404140500c078015140801c40e08100e60300d0310b52203010320720140366640 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 741320800 1250 741319550 741319559
    0x5040201080906190b0604090212010518040312020a0e040e0304050a0602070e0601050705030d0906060905181e3306010903030507021e09041101111f0504050304080307060204 77
    0x18800c0c0750040e82103000f810640c1032207202d800d01c01d01082e10074456162110390202c0c0c0e50b102e400c1164010208a0003c540710f40220341c68043c180e8080c0b003554495160b40e2101e22010862503400c50007243d041c0c8520f49252101040000139400504c800c1c0e09010410725400a50703110380c021802200100310245641c2e50800c0d042140b00d01d91500311208651281d2403c0c0940fa0300e200761581c1080090030304c20303150001803038481c1c618441e96010a0303609090000301000c022660b0003920070380b08a0135083c811640d03018509000c0b502c0c480403101c400c2d405690341e84e044084600201580040203820b5802c1804099407840c460307050515100b000c542040321204024a15405840d0071800901c0c11000035451034500408a0140302d101a109151103030402031201d2080034203000d007034000392626030146002d0500f100903072240c3c1c14190128142c00b00486482401240703914030032626042c2d40c00701200b400001001020002c0044030640300400000c55040340c104007a00600b481400c015a40340e041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 741322050 1250 741320800 741320807
    0xc03020105100e0114121606020c121f0b0d0b1005010f020607030509010f090f02130b0114030417072f0108010306050601030b15041a1911120d05040201 67
    0x70504140d09501c02e00a000b9070b5405400c01d811035242c40c0b68584100d040ca000200c84046090390008603200300d0305c4904554071701b1b0a5541c11170b00d4036001d07221100032807003c0c0220304000080e17003c0f05400c90400c94040e140c126402c0243c400f517000d40064082c0a050100d185100c0700303401902c1c849240c030b04000401480c00c0744c200c00381c0f9081c80c3c0519650394002010307545900c045c061009240d1140000b0300c50390380075840034204000d0a9410722289002c0d08259015884501c001d0f4000d2640c80c00c0f0303000c2652180100000c3c1d590607540d000243c4941d24081205420183c41111402245031031f40d00c82c40c105c4030250031075074090400e001110711208002c50165407400c0c02c650301c400e03890341c5541d0242c3e04406520704490304804045001d50318080100c000b0f100c8107154030303401800041c0b400720002207800030700b0545074000304400210004000d03081e441c0c0500c0300001045c580850111480d50f105003401c0c0d4141e14070310100c84000100c9003d071011034225440d800c01e455922410801550790 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 741323300 1250 741322050 741322061
    0x10207060b03010905060f1e07091e260a121e0e0105030f060f18160315030f0201050d06092310090c020c060d32010e060406150c030201 60
    0x440007000b1400c055501e5540b11b013002824212130714503010001c0c0641e007000008601510481c0c08038405484c00c600003500359501406400e160010700c160000e10013101c091944103850203680c20303412300c11800e2600180301c10f02c0e038030004050043e5101034000660040806540103582e0b1103805000202c06041320801110407400403c00102c03440c00d02080e41c121003180d4200c44052805a00c0350f913030300c0100b00700b641d4178852150040c0000091145d42c048040700903009002000001c10006402e16048003075400101850307500420b107130010400507101c0d2444200300362040c14041e003040051001c180031180f240d8400722a0326200c00140481c22112242105003903420b429400300b90034001c4000f10400114001c000700c840e6240700d4406524020412081045002880d85a82d4010030300e160020f4511201c115009503d0304280d82d240c001446100711030036025003007030b885980c40c01080182030380003d44480c0c0c2243d070381c0d6800708100c01c0780442040041d010341c9401c082d1510510f030003401c445 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 741324550 1250 741323300 741323321
    0xf1308100e060c07030c02040608030d0f0c0f02060118150906060e10051c020d0e030d06080309064f050913020120032a120a030507020a02090901020706 67
    0x1c1220081041144020013581d5011760140b81c18405050b2520104004010a03002201c091101155460b0081000c1c2c000241c03200740300c0000c0c00700345040d89041e079056446201c00b2002d07810440041c4a080d11800e55640c525120030808156601c103c2075044413a859900302e050080c0d01e901c02448801d800580038030180302c043c0c60305001c103401c810303000b055170081c4116101042403508282440512a405446400e4401041002401d0414074020340d241d0211000f0401941070600004101ea4044140c41001401618040c980150b100072150300101c0850304031640c0d03030714850390201315102c44080380101607e08111142c1d50800c10b07203181108015803002e4407600b4803d0411098501c0b0050311104c240d820b081030707101484100403070799000401c2c030700180b064070000c956401001050040c0004800814440801100e0f05520300758440e80329196406030729004005960342c2c1c17071080e4462a072100d45441511554010f560000d000b060060301d444e010f603034001c41c0c04405d00405104101510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 741325800 1250 741324550 741324553
    0x41b0810060b030c03040609020a0302030d1d04020a0507020907090e0c0a030e010b0a0911072a060f0f081f030b09070815150d05030309010203190203040203060c0f1308100e 76
    0x14600101902c13014400240300800094035403080c80115140c1000c0a1b01940c0e0040a46412003054a0000c150015401e00301d954000284007907a4107003017034422a00020020b42e1950b113802d06940030701031051005050102000004000021907003040b0125500880320f01d071049039140070000008050314034180f10003134140d14009001100d5610030300c11504448180740089640e11410fa4100d990380a17509000e0302c0e81148000020149000c220740102840841d052508040d03120780d01200c0142d030030f2001e00081b440d400004070401b4041d2441d103620805500030382a12104c3c903481501004490b0380202e9a000d0120207000e0488000e000b19800381c04100000d020702201010606012440a00321030070b4801c030b94034400400d1b214403140602d200c0d0002c00301c0b42e403414640e2800b07000303500444038261545500b1100814003403880c002c880c003c42d0014001d000540ba1107440d0038040e44000103070700d0410000c022041d003040340c640e070030001010b0b544044c041c0d03030500ca843c900c2030751540e00501030ba6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 741327050 1250 741325800 741325807
    0xc0114070e0d03030f0204090f0c080f010b0306040510051c0201140a0804170c07080604060c0e0d141f090b06010c0c060302070c171b060c1203041b0810060b 69
    0x10b8407075000b080d030540d80600e40442d44e40382c15405500240b2407a003005070050b00380300700c420548245070040c03010b04802e0350781c40c01640d842450308001c00d5000c0c00351250501040021a207a40740603040181c0281024100310702c00c659400014940080d50b5110740b04501e4211005d0065607006a030034100c4802940b2018a0b19203c610010503035a80240004c0100c0c0300c0a1291403500028000c1e2000d071625541100c1300241c50340d04190b80c03840101c50840f8024105000359603081d00c9658804020703c0b0142000048040030394030b9002c2d102643e015005944649165010078910710f8007a4140c3e0002da600000f24210395040000410300014082c5040c420140442ca0018500c0803111040342e4461500603150703209841c1113511880180c3c0611410041060080c04003840820480c8400700d0320401602414080d00600c01c0702d000b008140c00d40e6400030454280b605141c50021984603202c0c41004516955500c04480b5000140c1c020112a0384002c00f0b4041100e414402d880c0030b41450300f5502e04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 741328300 1250 741327050 741327077
    0x9010f06050a0809070f0b0309010e0a0206120a141303080901271e061a0415060c0804030609050d080f04200d060e0105150604030b0402060f0408030c011407 69
    0x254894180190200401c240002d0040c002c117005030400b521a65000c02900d99444485054035001030380c3c0e01d000c6501e0004080403071040000d40d000311070ba000c2c24050900042160921246a0040103044c08035260404e4401c61141c00800c81d11441004102030002d81c1c15080c000d00c4003000408803440c41c0c0c5030074540513002110107192809000e06210aa144000c02e103000305400425480e4141d4101d41c02c1c088108005a50b001160415a84109001301142040401054070b91030320b20700c102c90303078482014800280318224484006004075000b9207070507981c0c0c0e149000c8500d00c5a050310240c100c0205440d045506c0519290420445030003071505040c16101d1280902600301d0f1450085124400c00640740c5811200b07503032031a001102027000a561040c140d0207400d00f1200001980e1200e5814071300e0f0304e8203005541c1036942017950506584d440b6800d226496100ea441d4824000d0203200000380c00c0d60030402020150714960010620040d20391200741010409070030107040c840500c0106032b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 741329550 1250 741328300 741328307
    0x3191a04030221040e060f150f04091103040f0803180a0803010603060608040c050427061e0e210f0406020706141c110d0603081c11030112020604051c0209010f06 71
    0x150841400c540c00347d070000b01c4100194030000c803850007071032030840890182c1641e039401000d40200c4880c1d4100703005c0b01e000c20030780e5191407008807001019489210b6000c0049807103400556840007120401075251744c1100170503880c00d001c000c4201c96152000006108103a07150051000401250a0044a5007005e65a02d0040d10443c02118060340e034900d081c480081020b8911030003440c0e0004d60b01c1d154092030030183c020b007402030301c40c0391081e1402200c07254403c2c0a12810341211760400203446184917001050483d003074948000e50754a5018000b020381d0344070b14001032004140c150001d1902600d80603026021060710444299100d80c18041a101d00b0701c45600b86225a104070000521325402c43d800b62201e00030f90246a95180c0391000100403c00310314020151401034105c2401416041c0d1901d1058860300e43c80405020014401008140090b8040c6d084551004100e14105a128008204d00ba40401111071042188681c284154103040d1241c03805040307203107040c410b00f41c00e100015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 741330800 1250 741329550 741329579
    0x3020616030302040e180d020d0207051908030c03032a0d0510030507060c0203010e19080d02040b160303200306061806030408070210030b03191a0403022104 69
    0x14165120805200c0c1003522990490740030b00601c2c211250303107040520381200c8280b800c144850040c450848510b644034000200c0d4407404400754000c11542e07040c1000d000071140c05111540203a501c5100204c0e004006201074115005030200554903481e101e40f81c00ba1031302401d030140780304005040014083c0ca803490f04950414a02d81004030f41074651484482c80b0140f164005000d501603075074080f07403550b03018005c28030301c50089009124201181090790b40f03843c41e58038040c071031000f101500030018480b040500041442c280005042c103640e49800107456203c164603803194581a1244420184c1500c80d01d1001c080500402d40c40480041d404081413102070f181d00c0c8684000b01703401c2c02401074110242541e420140c2007948a050500d0140c01c2c03030304200d0080348544c0400c40d13642c0c2490300ca4402c0c62000c000040003422080e840000001c044c9138100016142d406c01318056a020f8454840030f070b400b49100350300401541000c160169031000c07060440795694001084200100c0d40c080204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 741332050 1250 741330800 741330817
    0x7050319090f090c0c0c0303030213060e0f0d0f0b09331504090510200a0206040f0201030209030a0309090606050a050405190305070e060406120b070e24071b030206 72
    0x160788030f0b03148064901c290320341d000409200501b0408010958582c000d82064203080f86245c0c880c5485003010f17955400210f03045e0b40c10540d04081d4401e20b1030305440c102d01c428000e030182042c00350b5540303c0d1341140c2e00c2124821544d50044030508020b4103002e04007466001c429580c5190305c15200703111811701101500340705624140c0110410150313204da10004240798403000b1a181100b059800758050301002c1180314409e003001c04080d07015040032044401941e83c1d40d000d0052a0b5075907440780c080315841001a410950b0a1000d074180c0e03102001013945450080e00d40001c5146084100e0083d1142034100b03104101051144000d59070300842602d00b520030407180c80a40c49010b040c0c00ca001d440c2c80e40040d00c03920841a000640580b168565409418103031814000d0380e840355001e07606801b8402000305410003060004816504c94401d4000c0040020100d900c0d0310b10644030341e0412032500481501c5600002608410007a491049410b141c2010320100a09403458000400c0b9004c0c00c02c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 741333300 1250 741332050 741332069
    0x51911120f07181109030604030c0809060a08040b060303160b061302041707051f0e13050c0a0320040302011202041203031b02010b090a0209040603060207050319090f 73
    0x3185080180540d4400da45254129100143e41e41200c40f14150b051020f40202e41c03804002c4100d00c1814400c4802090002d00206010740311680d045031030b40b030b03102d500755444241848a0b48165441030020b001050703040da5070f0222401c0034148049440d902801c1c1610a174410080303200600103028841c06296000100300710395549031401310b00e0105180202c0d296042c80000c0225016103207001c040c0c0040070001c11240c0b21500e8900b449040941c5000c3d401ca10043c0304440007125118002000c0010400741c050740ca49610400008142c0e202a981409100c2c800b1455402240d031620955010880320070b5583d1564440c42c038501c80c14031441c0000b078104412211035031140526501103074002e200610104036451090b04004005103108800039440a030703003c0c410041e45205000d2050760400061403104140c8411181000079070180c03280c2d9400c680c84240020114400c0c1c8060301400b4014005584d5419000c24039040d040110441c000500042c08000e0000c220100380090039507403000c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 741334550 1250 741333300 741333319
    0x2009040b15211507030e03040b0f07020405070305070e030102070c090e1504030216060806032805030301140301060501050c1c090b03072102070f0b0c0421051911 71
    0x1011592400c4016165500c1e0101490703070a00300840081c0b0fa04440200380341c503500329141d22100b213082e40c20001031280158002e00c428841012103c0c0106240d003000e4005a00c1c2c94110303408070f01a520201e520a0110380d44d40100105507800089200109100724002c51420b4480d40d40c1d100144e0045c002c45860070741d10701a8412880c0200980345c2d40b10403107a20101149040e00e0700030360301c0950078074030346c51000c1c0b020000610302d008145190046000070090b0404482803c40950440440d00003074000120a00e90040415014070040d070180034101803149240d180380040c14203503100e99010344c0c100700c020480303070b40800340c00302d17800e9100b0300001b006003607007074003114111803112447d0802c1400c14000000c0c4030101c2c0e0040c50070750b0722002100280c041032407104d1440080780600303c40030b080a0300c4d07022141d0010b2819101e55900002411000307042a0b2125000c24880040100c050b143e4401007822200340241005005049114600c450400d42720395561242d603100340080b0b4030f025900c40f9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 741335800 1250 741334550 741334591
    0xb06010c0b0108010c0e011e0809100c0513050108040b0106030e12030a14071b230d051b060615090a150509180915090c0406032009040b 60
    0x1861042000398211012001c0e558448420600030b001d100c100170302191484000e440d00d54000c804000c00520303449035001c4000001981038504042c024040007641c000d07514841d01d00304580c4242071102d00c141e61010784895080e03c000160070b419402c00341c1801450010000028601c603d580e0550b5224900851000089020f89207070a010210500003d4801b1041000400340c4e540312000b00408000780b964191100b000945580b40c7c1c40380c034122034040c41120b100c04607a01000781010505100300c282c00708200c4040090801c01114004c03070000da00003440320b6120002c100c0c140358180420000c1c10490038500300103008600d00c00320003440c0c1400402d4520b600d075030b582d003000014403e12003241660300054500030708541c0000d00840c8507800d070208900201a0040056119902c8040240700200e004999860303044070050164203503100e65510200d447d26140150002980f140c082000ca01034150402d4960136110502d16028032305041c10400407880b48507240c0d4000c5c1c0350b41800c241c01000c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 741337050 1250 741335800 741335807
    0x180907050112060810020702130603020619110d05040509090d0c02040b01020c0405151c0b0a3c1409250302150304030e030a05210d2f090a030b0601 65
    0x4d81c04020740c0e0280003041010000d40d600109001c501c2204c032240c44117903144119013211494000030350091418032008900c1d05100032190102d4402d800c01402801a0015080c900501224071800040d0046020051414400b00054110304100003800c10354040c07100c014a405a4044083d204544840c804000c81c2d000348210407000300c000d40140301c0391501515504504c038510400c03a000f00b801310b02214400308600b20b89003440c0d41c401c00c0c42a01e03850341e40c608405401400b028441c545c00355120b030341d816a000b0700c101402007940b8014113114616482d0130411101c8403018400169078040030070140500c04541d40100e907070113220307080b20010a010744004480c030a400003034014559407400400c000e86038000c0c601c101c0c030035591109075000314410303d5214540403100500a40c0402e00c00d03042c2c0c04151012105010a1725811810620004180c1c0203450207a230740e450307000b20030b000c084003401e60200c0c1e0440141d000982c902c0c90101c00d200070941001d801e2001928144880b03004c180240c0c071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 741338300 1250 741337050 741337061
    0xd0c030e0913140c130c0c0b06030111160b0708070804020d06060f06180503190b0a140f0a060b031b090d06090302030d0f0b0a0b180a14180907050112 66
    0x810105810001c4042c0182d10364900400213030394480c940540042202020501480c20122466551a04240441c0d13446800c20000985081d506540b5903d003410017030b48c031a0180904108102d8800403050351800c4c210104200580745108019820080101c81c1d07030404115500030740d05035a00c951102c124100400188003e4026200b001c0612000091403540005103042000b00d541007400e06070783d40e00405541e880110701407a0f81c07a910b1420a00400c3c140c080702a03102824000104440810084030b000100046510300d58403915001480300c8a920741c442c24015100f0074400f185141004480c1348511140342e861841c0079480050361314190f846843e00c14180301e80c48003085c407070100c80d4900652a6000b0403111421545482036003030440c500e41c02010240c0ca401741a22000c41c1c24408501c0c1076602034034800313042d01010703000d1015035205c154500000b03011900e42c0c5154005242c00704141a84030929209040801d44280410b822002c1601400c0322403d08224007601040741d0500003810 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 741339550 1250 741338300 741338303
    0xf250c0807050c1c03080903090306071202070b0a1413031e14040f1d19050604021c05160305040206091909110d0c05070b1f050a0b04080d0c030e0913 66
    0x280c004c010113064510803050001e507520944501c9041c2c3e9a49050326a04c0c094504035503459400f060100e204a030007000c402811a5980301c01600d4664a620791700703142082600c41c40419591200030408861000c50074075040310000d40c1540069849840040400740141e21441403150007072481e4211500890540308070100e60020503884941d6101510382ca0b9503140b0405400b0862110000d4003d01c00c100302d00e01c100c01c814210f0110780c04400f110310003480b00401c3c00750019401c120041020b458001040c52207204080082924507207200d0b812a90401c41d0f221105043c1440c01b07210043c3d071010252024100140c41900387c40d1008030140035210120b40c44140c51a24200184e81c125015400030f0060804080c002e00442408000842d1716106500b0090101c0000b031020540091a860401080554001c10b200d03000d034803800090010405580032613140d20000408018060f414066036031031246c1c9040a828540d801e40300600020b0080398501d210700540c2000820707100c001080c0c0c0e00e109 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 741340800 1250 741339550 741339559
    0x4171f02092205040203071509060c030e091510020c22061e1e06020d120b12010509010605041b0c060219020d1404061b050c090f250c0807050c 63
    0x194802e07042c0c04001d01060300c00f41d010b070240031804030b004000d181d041c0005072a2661002c100618003507045500390b1142004400700050301d0259080342d60f0314540a80030b060b002c0d0340000840d07046010805117042000c004c5095401a4125001c00d9483c890b662100b000d41c801d85222007020600b1240c02403034145c1000e8504021001d2600d0104000c0c1f6000069400c04403442c29841404242c1030390364200c0c0e115420040e8042031151001e24410748048100f03000c1c12001040c00e0305200d0029010701c0e00301031500942e82d55141000700141003405030f00010300d41078504004c1102203903607130144c0b00c0d40e00d881002480410021142046141e604640c05900014182e40103000d080c0c60081d02d8010006184000518000c0c0300080c0850b10400c4404840461325005402d203840e00e02d41c07540002c2c0000c1560640a016800b00941d02c0300707034444c5c0c860280044a03017882e16103040901040c0d02480e11074029501c4051400c10400c4c1c20011001b215500300315a2a190b54a030f141082c0f03402010354006420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 741342050 1250 741340800 741340849
    0x6100909080f0a080a060b070b0c0a020a050d05130906052b06020d0515150301090908071205031f0501020a0f020d060f0501090b011b12020708070b04171f0209 70
    0xf203540c80407920f405000e85410030b02c2940d6807056110107900908038007400030480340b004580c0801d503030310042c0102042801514000c0c01709403622800c140401e00c0040205000088814042d02803900d4100a41100d0030308100c00b9042c9004207108981c40707c08441c40d0005138980305034603050f0138204c49803954000010341d03036000701403e44005020f041c0c9074204501c6012040c0c40c00f07460445d102d20760842444043c42d00b035030310301840d42003e4140010140c0f038860003000b0300f1020076410800b01d901d40c0341c15281c6554a05201d543c0f4100e11b0303c20362244c040081000c13030a00c00f41c2e0380403903d034440701d0304a0181c0d180010300d4000554010b91585000304914a4002240c41004060701b00904031248841c0800064641100540c1c0c2008070302c0181da103c603040b00700745c4d000860b1030003600380d01c0340b4601c1150900e94503030140b6450002103408c151442040803c0c10080e403c0007aaa07100d0948000000d4000541654102459012860b0aca03031142a000b01381c02d15103480e10a040204810a000d031040d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 741343300 1250 741342050 741342067
    0x904031704030c060506010201020306010c1b051503040308060a030812060105220f061103091311070f1b030519030203160309051e0a0303110c12100e06100909080f 72
    0x403c6001c203004842d401d043c000092055130042c400d07280f1884041c0c40d0782000354002c0d036450074201c0302c01090324607400003020041855220381e5140300c40b11844006082c0e5a00707090030007400380400100314a218010508080c070020300c24205031209800f20710b03183c01c5161500001030320903005502d05038016200060740d468000410380c1081c030445000c90f1400b241e45849120845601d4101901114103500404c01103040b82081600031450014401e4001020000c4e404030b9a00f903404204192018400e480d08401801030211034041200b496541c08034443e4603690340c0320740340da014005c9044400158650601803500030b02c2114000041c00450607100b500915002e4040c81e81070103090702a0204144500210030081d204400c0c1c00350082c0811242444d5640444142c2c0b8504443c80c079500805500041640f500ca410404d28100b80029060405011540d14115035400000325500da02c00014003054001d9401d8800a9889107000032031401c2031428003515038414104503d81c00c0c0d10024403800f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 741344550 1250 741343300 741343307
    0xf071b0b1e0c010b0d12030c02010b012c0604081501090506010903031107030803241005040e04030e04061805160e010f0c080310050117010e0c070615090e0c12030702090403170403 79
    0x1b0507581658800300890800102c04030b088458015010380440c84083c001010105406122050f17468080304000650f1620300c045011a00103620200700d03540b00307604201d0000980010b09001d000461070401c00d91a2000008001110512000c0c081c48082c0051a40d40d4609000c180051500078038010f03602d040c9030124100510300c0e0500cac0c0d00e401c1d840c007546403150b20305010580418134850741c620f82441d041c004d2400100c0c00103002202440380ca080c1680310350329580540700c01800500d6440016608004010341540d0006001211602c030420740510b446401c6410241c1000084c613006840b28502c9000307071130b40c507091040504040380102c00c010061800060311710907500300f80e03500b1007401034045c1c245c1d40144080c05807003141d104034400076140c040c8030400703000c200380140c80100b215040607502d42054ed07159040409003035201c1c1141400c01c481081800020001a9aa4440b068020a0060700c0c5e000d40c003030092107080300c400800d081c10b20458601040c0072038039a964040c1c1c01c0a25001c3d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 741345800 1250 741344550 741344573
    0x21f020c031b0d0b072001020301150c0b0f070201020c06090708070e010308180f060712110c010c06150503060c040806010e010b1b030f071b0b1e0c010b0d 68
    0x35446403203145081007502e0300880c602004031030094203100b0b01408036611104001c4008101000300b151301c0d5032a00d007001c0c0d100b5508240003284800141c2c1d0303504140c6a0307540341c141124220144080d080c0310700700040601344620b074446030203809045944c440c0c0008034060f20900502001030b00c111803d100a00e00c000c034042040700d842000300c0d510b8a50704c0c4e10b2144601002d100150080314103100d6802c22102c40103180d650b1020003049070310001e440f100003650b00e8008400c2a501100c4c80d0b0050440950000907c283d003209600003805001f02c90f8000030701c1d001c00442c0c0146015122000c00d0032a692184044025260003400e03100c1c2032400c00d20314600303904203104502051040400004500c8200e010303850598030048035103443c09030b9000d031100400c1c50803241440240300c2080302c2d10b1034040010207001250312070390000040448124100050020b603422407100c06408006840c249001c4440780c44010708844450b90312400e000440c00c1c010030884810f40d8002c0024407460341008800d0105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 741347050 1250 741345800 741345823
    0x18011103040f0e1504092a030b0708060301050a1e1505060a0f14040f0b130803030901091130010b0402040303080609130201020316240606090806040b04020904021f02 73
    0x2080d100385403040400003691449000030b08807407001201c40040d08444840000503500e07d8000509060b0b42e540c1e405261101140e0031400504079a0500141e85002e001e00364020700380714000e100543c4010300c81010554040d1406500660340c02c1402c3d007001180c65050000d01d8002d0141d6292301000c0c1c0c4c003034001c64440c000400002c000d2132444030b0a0320010240d4060300c03c44480741d009075041250640b0940c1c0f1006000c0650207146038000703404041000210703c03034005580042170b88082071904030110701d0141861489401c210004034512400448a1101e42c81a4022034855074500c0002c0b9005000346007400342c00c103000040210a064002001901480781a107880d021650760304442214061503401c020300607041009900c00040048200d10a070901600c110b640c0c0000d10b00d65481004000d0074115003042d02e441c4100b04558100c502a03004140c1400981940c0c40d150740c1d0b0101c0d1001c000c0000b8410b502c854040740545d00c40030001495003140150640fa65032031005d0180d5100b958818 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 741348300 1250 741347050 741347071
    0x402010815040b182a04060507030215272b050c0d0e0109080a030e01030203311b060e0d0c0801051005031b01020a020405060102011103040602040303031118011103040f0e 75
    0x1101d9030503206590041d581c2d8a175400055080c41d007004012101c070f501141041c0d046228101c2c159801009520034540070381c1c42110070410b4640b81c914070311184400c520320440d80e504850310748450040b60708103610380c41001c4124501c880c0712000701a94140500d02c5004030368071601c454401043d40000c08a240b254090f01d880902c60342d2100703043d17503440702d140c40240059901da079160742c0d03540250051a0420403003d0000401100d0007480d00c0202e000070304c041d43c550b4112a00400b80940c0c0b07901036250b0f14003800c0f4264100e00f0028060501800a081107004000140026013800043d0903440c015051010003407185042006d0b02640010407406194400d00503280d44418034503044400c40741011040c2c001d09880c4a0a800304401003000030710040c1555220724800c3c20700440c0308021441144901001600c0d90304609009084440b926681e01c42804100410252100c2030302055042c01c3d02480e1803000d0380c0d004143c1600310700030340c0d10603000a03c02440215249010760849840f0b03061100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 741349550 1250 741348300 741348331
    0x90a031e15061a07020609012109082109070e070309060615020f0705180903070206030c0307020705030c0d0803040311010e070302040e06011a0708091f11060402010815040b18 77
    0x1003ca0b4140c460301c240258807590400c02ca041550184a030503079142c461480c1801201c0144051606076800010101d9a10304c000502c0314004264a040220868100320340c00c0003803401c2441c071513484e0b80740e0041542807030b02540010700b698800e030000d1010702d91002c41032199542c1c481301040a03191078504940540035044118250304030000b41407007140d20017002c0115400031480c2a64070200080c0410120f80070410800d80543ca88000440c09824181c00741542e918051600070b08000e00c0c1d82219200f1b800400643c07280ba92030100c081d134020b4100c8040c6540b81c0316403406a502c6101170072800340ca9424052581d00248000c1004402c0f68026141801011001c510490310b81c48c00f40500c240310b50b000d080900d0342605d18000303406614821201c0300e2030401c0090014480c0c1390b02e20080b14104000c0c586070b80040b90f00812a60349518200010242c03400c169001801100006298904d41c042e115280c0041e542d40d0341116540283c00390000180301c240c66419014003a0803100c248007101c114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 741350800 1250 741349550 741349589
    0x90c031c1b030e0607020a1d0106091505040e0c07060911100201050606070303150e151e0d0209070309150603110a030c090b0d1e05070506090a031e1506 67
    0xa10940328282e456510801050035200c10404c060300641801d9801008150b00460512006511307502003000380040600a50301d4044000d01043d190340050b6030740d0340380c03150841c200782e003003800c3c2c3c0c1c15960101d04c00c03103180d503500070140704900400c0009003080b420b0403050003c0c0a102e050311042c20b602a9032103241700319202000c0c0d00740c42c001d854440e00900c0800c40240468400e500c000c480c001d8000c2c003021030030340d5242c0303441c0d0450302035444100107502c0c42c0078440c1c4c41c0f4000c4800800001c1c40644003140c9000040000c00709140500302078012810140002c0d9260b00c01e078403000d24294051083c030b40f490702d0f46520400a1400b400700300c1301081a40c2c2c2e114802c3c42e100300c060741103d40c8029000010b5050005103000740050000030b507003008080d440c00c4001600720180b505c18121821040c0860741041c1041751814941780d00c12070040e541007140a803542c940302d0400c003d4a400103088030300b542034298051501c00b00542c0140600c440300d40309452401448d000501200d64500d82046071131901c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 741352050 1250 741350800 741350837
    0x6160e01020307020913020315070503150d0209070804020406050409140708010509031c1401080a031205060607170c0109030c0b060f06040e1018061a03010f030b090c031c 75
    0x203043c0d01030350110314400050380c0b024945840541052019007070b1414005200c10542c04810261442c2d00412804400c12019113020034441000d09012642c10200c2001a004103142c000d01901e40c0c000c01a14100040030b646031504280000d00002e04104000d200e0b900f00000d41010712213003290140114100090440014000d4900481044014520f800c504940030451048a40c203d204c0ba10385868800c01800c0807aa040c50090150301e025080e681e07600c0c0303401441c00c1a241009030013180340c1003c3c030025444070801c0c1d42025a100144004a20140300c4400c4540900110b4111640c280740300300b41052340c840e50400c2624802e9003909580d071210410003410b1040e00c00b0041d04144140810803031142000310043e000441565031006058a0b900001c0c040c104c10f02e0f16010582d1610010011540b90920861038040c881102d5400c55040c014104443c900c684805060502d220b404601000d0b0705011050140200404440c0502c244068a9218052402800b008240300c04d1480007003844 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 741353300 1250 741352050 741352057
    0xf04091a0604050d0302070503120406202a03030a050705150112230f010c270b0715051614120a0c0c020402041410050a020607030b1206160e010203 65
    0x4009181e0781c2400e0408050103001032141c10180c0c00c610603a4000981b17031702c060121044c59a82800d0083d0b40f541001e802070310b04c6d9486182051007108500d8480c0746101c010410b15070f8413404003400c02d40e84200c0800c00070811221060300b5070500000540141030354000004180161040c0280d4840c0100c0c40842ca201c403400740b01d0140072800c058561000100c18600111008201c40c1c0109952101c0e0100b451801c01c02d0111030500340e55032500b445a42c1d41024204400c6200c0101d01c004182490150400021b96441754000a11002c00c00c00c0412141004810200d0040c2d40c0403c030703916001903084e4841c0c02c4d01c1800c6c00814001798612021108030740468245520046801d0314541b900c00180340203007405403040e420001d6032a040da0040c1d0b140e000a100030020300d40c1ea0b00035441d0303800410282105002d086814080c080003070103202a0003080c4540d000b0341c141000540b4641c5023010801c14407017800649040c0c000d003001c11042d04055980f2100d1500713683d41d41d0303561540c1e83d4016a904c0c070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 741354550 1250 741353300 741353351
    0x120903030813080f030708090609010b06040b0a051605010b040f060b071403040810020d05070509101103090a080609160b0405120a120c120306060926030f0409 70
    0x4180340c0c0080c019084240c1d5054085201d10b2a4501c0d000354604c840c4001e40040c2d43c000c00041d14402408070441040040f10740000c0c00314001c1149951180c0029054800c0344180e0855020100386104a41d01942c1074818074007011803203c98880d1607160187c000c04807440214801c40c0b40222441d00318482d8440c240c280c540c583c56051401c000c54071419160034500c480507200c0d100401012981140520044003003c4403000d01603114480400c0320801d4070340003041001040001d008402e11992070b10051140101d06040103400c4080303050002d0b0462051401ca40d422081168001504a0001407010703c243d07002401c0c0c5001008001810401c5a40da10a851500340140010b008a00d0000c0000300c10114003401c4840002c0c090303407104561600b000d502d0011a265800c144144500c1d03800000360140a0b1408000082c2409806095800d9178065a0412400703250064500f66a5082c8425809041c02c00c4a482e0140c0d03041d084500da1080c040c03425a5400c1950f50380c000c01d0389610030003041c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 741355800 1250 741354550 741354557
    0x30a08090105151e1003090b010e13020d11150d0b0306010312140d050109063003030c0c050f011a030a020625120305010320100e03070b0c06010312090303 68
    0x84080c004012a60000f0042c10522201c01102c0400a42c0d9171224000a0b4811b80c80105041c00b05003014480040140e22112001c161101041501468444401c46495049540e0400c443c0d45080403100b44d175018803101c1d04030700e2a0310080d07500110700380a0328100440740d40610401c09000240743d201d06080c44000c145100002c486910309000703031807048103100d00c04040c030304001c1d00383c0f40f803010344000ba030000e01141c2e90b03140280850400210705d0700041a86c5850300c8203131140c40e0b81040c1d00060300c507400340c00c042da110040e00700c00388191068151241c0103000c0f100c5000746030303128500801c0c01d201407010323400c0804594905418003040084c203c40e001884141041c1c03c640501c0c038540a144c0c0130b000d07000b240300601c500003666070406a003249003542d00003c01c1e60551601040208084203003a00c04030260120703901c69601c1c0c040a095415262910000601010022038a40b09060304a240c50380c40200b07261120507000603403241240c1c000d402620b400d0511400035140c3c02c0351400f028000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 741357050 1250 741355800 741355831
    0x8011b0809010f02040311031203010b07061a03031908130201052208032101050d0b04020f1906020115121a0903130e06121b09060a17030a08090105 65
    0x12601903190207910140300300011600e88542c1808104990081d00126821700f1181104400c90a007000b480c00810030340040c4620b1541000600901400344040c0144201e0321001d409003400c07216a41100300650203401c40340c0f5511482d028001c43e120766071204001502041c00290628031070014012039a4043e15000c0c940301d048020342903d00b20003890040c100f9425400090031500410082c20645c581e03604003110075134058901290f031401a40321511500036005200042a0f11281641d003065040303406001070010400032504600b082d035512100d141c0440341c00298160190440c030040c002c1001001141511903101901c0100170f00400740081e1035010399060f2880181184540102000701280d007414000d00140e1648400e40d004012034000b1031062080500f03020712907510004030003000d00102090318082131811074135407904a03c5800038002042281d1104d86110024251102682c50b5014040505680e03941c0400d2110000034a81c0c000203080500c18402c950280c0780da281c3e001c04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 741358300 1250 741357050 741357101
    0x60c081602120d0b040b0907200304051011010b09100e1605070308090f0304030602040602010c021b0423130b070801210516060905010908031602090907091a0a0801 72
    0x70705040038421703081a40c0e000c00740f01030342d9204900d030b120310044e9580394a5004038001d049100082c446001001ba48140428803541c0e82e0000d0b031401502e0985031405020308418a41d6000d405001c0045030005e03504000c1c001d03002c1404849034152520741014070020784541c418107070805000820640043c3c41800b0b0600002c0c81114640e80040311a0100c981500c2518601815640682c2c03040780e07400e40c0017800b00701507602802024440c14550000e0110224450038030744400e0200740d4010310075580c6080480202c10599004403904c030125030310042d680b40c281c40084107205010404d8a010a081c0c0001d06000d110300c4005058445078000c00303500c424051781c8101c00e40c8000c04101c83c0740c02902103404540789007403d4840140910780c1c40d0f049448c9003500141c40b69807150420385468004128242109803c11010300000394152124017139551071800d142e05101c00f81d005501d02c0b5080201d002030900e188112144a00707002c03a551000c0c06e698035002401ca9171420005081100529035044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 741359550 1250 741358300 741358327
    0x504140913080c0f01020c0703020a0e090d11160e041b210303020f0a081623030402030102071205070b0114010c0f0203011b020a06140903160c03060c08160212 70
    0x401d90400310229460052001161170036070f000421000f485a10420041041d0300c1c24055071801824120a541c40310304185001c01c0c1c41d601a03101d104c0a101000c3c40a068064042141150014400900d8412103450f10130004003c04c09a50660b100c074241102c5215030b801e8403004030300f11a4000e056655034000907020340340142da442c07000d4060503400e02c0f1714078002441500130828460a55601b5126141c00030410f503200c1d110920500c204801008002c030045035100200c90249040480035880303a84038800039000e41b1408000038a0010311115641600b41c212020b41305992150110300010782c3c856049503010303681c1c5028240010078415003280403551080c60401000d00240000c0784031164542030310026102da81c06100140e001140010074440984900b0b0700b500b80e110fa58680c41d04050002075500d0261170180c0002001540081c000c100040c0f1440c0c0c0210b0740002309000001400704080d1488500316001e225500e00001c070b04e10307010702c00f20700c40d0710824008640e507007042c0c0a0122803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 741360800 1250 741359550 741359557
    0x30b0109030609050a020307240c080d0e100c05090a030803041a010611060c0c071806031a15030706021209040b090c03040201180b0415050d0903050414091308 70
    0x181440003048022000c20440c1c041d0b107052502800003402000aa03206042c581504e5a0101c0e80c078400207202d00d800d1851a8254200240a9103406413141d1031a0400c0007191259041e403166942c50205104072a60001c2031100c601c104a01c010044040c0003802030302c0a100c0c0010752588558540c90074800120388030b0285030005c1c014450001094410001070032000400e030802c80214421020341019204200100b507400100c080030141000c0d1044440c5954000c22f0140c2c104003910303150750101e02c41403130707000c02c00860304013140180307501e1003908604203408155a1782140c0e42614005030594140040c10404a0300e1a60090407040920701c3c0a80d25034001211841c1d00c1a22031100b100c032940c400c00145e0203038071120790903a40c038200340c40058026100c901e0543c0085a03400e07010450008080d0554044808248070030741c002c00415011107492180e134103c908058601700080080c503601c00c0c0917000791100c00703050b034001742402c42c2007105880f802c4410303501c03080031071800e11f0009414801a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 741362050 1250 741360800 741360821
    0x70302090a06080a060b1c0509030c010c030902010e060a09090203130501110a0e190b0304080c0f060702070f080a11011817060f01142b03030920060a03 67
    0x141803140840004030488402da00c604001440c84041c803149403810b1003800c00400505101524151007039a1060108000c01024000240c1d01c00c00501108020700c110b400b81002c6c60000c00405011001c054024005220142e0000c1c22070141040982040c80840b010306a07140c071071480780352411210501030b40c0700803d071502c001e4560100c8070001e142402104100b110041025484000030341001704041520130001c1d21800b9511019110702c0b100114080944441d45030142d580d9656003840d050900c14056000d80c58451440c1d148850f04002c01d8144c01551171307909450043e540c1c0c4039843c0c8550014003130064150000084000061402c0141e42060401030410300f114032030340c900440e10104694044e180000480782000e00e442c509018840d401203c2c0e00c0ca1400c2c03941030a5809421045010019000e85c0940141c0e126007000c5842c102c56400080840c08186d80d07951500801401c90700e0303c1101e4801040120008029048000c3c07109c420018009509100121390124043d0503000790 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 741363300 1250 741362050 741362057
    0x303030f0c201606090e070906080a0911090a0b130203061c0212060106050d0c02011406040504050a150c030e070e070507060605091005030c0a2403180c15051201060807 74
    0x1c41102c40f0000d540600020402e5403245141d2614042c4030b40040d0340024100000c0004103c3c0a005075900080800d81103140318400080c4004286003518040c2000388040d40c2c480100030400c0207811a80c9c0004111100c180c4203407050b4171444100d01c05030f000c01c3e100780340e12000a018114111008842c0300c100769000401d001c03850300e5400005070501c3c500780c01610005000141445030500b140c02070a081c1121440200404185420905064100a8100e40c4510307101c01c089414408100220504c05802c154265058040004090000d240c6540a00042410504103550080012841604541c10034a605072243ea4550045030715a204100031a80349544c0e00001c10a51541441d6a20691507150300b41200c80c00c10080626125217181401e1040c460600140203c00c410920010228240036001c0c08035010440c0542c0603214440d818131410200300180c4042c07124070042d260448220505241a0303442c0c008003100c2520922000f80000204071004000440c0b144041c0b5034044600e1a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 741364550 1250 741363300 741363313
    0x40605030c0f03100e07030b01060c03120c12060f060908010e070302010324080c2d0f03071d180601030807021c080a080411060c0a060209040b0a080102040303030f0c20 74
    0x1001c1c0c03070480f80030720495110307a401b0600500801c00c2040700d450240103d4100310404850503540103107020107640900000c5502c0d1071076a50b6450040300040751600728950140500c40e03ca001d006161035151003201c00003985407000140049040c450381c501001b070308010f040c0282c150340040d8040e00d500803590409603400b100450000c000c0ba040c6202504c0c030580a0140300e080c80041082c1d8220040d0681003c0801802203100c041409107546d0346518251082c60922010400003420700c40c00d0342c0281c00f0741044034102042c0c10500014113125168202000c50410100c1c0c03c041d40c0c0308000d00006060003002c014040144c500b5031184110310309100d07502c031603686e03c0313079507291b0750303030004c2034070030003041e0310000348810029000907100030340c0303402d0700c0b20340c104004450303e5a550134403850044d290070340c0094041ca0640f5150403a0800c040054080c40c001980c400c1100d000354040c5c8416000a49080c803500810070043c000d50f54110000e0307481e040c40361100440c100008003900c440f030403a4030402c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 741365800 1250 741364550 741364573
    0x2c0a060b0a050306161e0c02090601090810020309010f05010602071403070909080a0e1c06240b0d0501090501050d0b0a091506051203070521040801090b07020c040605030c0f03 77
    0x100a02441442c0308111700f00556000c42003c1c00e20501800c4080f80d2959003104080c220f980701251b044440e4040b5040001a1610300041e9400020764001c054a4001c1d9a83e40190580540085020346121002000003d1107481e0f50000c84001703004501c01600048010011003440c03118117901100d00509985001d55210200703000c90380c101c50708981006007c14840a459040507082c0543c0505680007681103240c03090889404651110007850380c2d41d5288640f00040100c043c1c4d2414600320f1484043d01611008203496980110120115072030505001007400e41071785c0075040c101c81001e0b10991302d01105030b40e00c65a0410050400d2a50381c0d440722480049070031485c0000d84402921800504035040c50300f80142307007a0141e0020007582c020450040081c03400070380212840b0340c00c0f0110394400c0282c050b803581446550301c0b4a80b291f0804200c081484050200c4030b0040c200e46e000c951094800e0000d103c26034401344202c0d6416040b048505103e420007a07540d250f100002001d8402c051100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 741366906 1106 741365800 741365803
    0xe010e0d050a020109052409070e04021507062a020a05060c0c1204180605010816030f06170c0418051b060415032c0a060b0a0503 57
    0x905070b414034400c0d405190341a07440016941039415100c0307080d07105142c034076600600040c01c001040c9002800540c2d04c003201e0500b000c1446650300e90b001c00090521846801d4642d4004200c0c100c0026a2031185685652500107884099541804007103c400540c1486905540c004030070b0b000401c00016040c4e601070700711000940c1ea0804044110304104003503c03040034045001c140414030f2205880c07881c0e41000d0000d02003000540d80c0e801120920826540f210000c00701c45000c3c1c001600ca908030100d084800340340881c0f05617030b400c00c6004811040d08042447d80080c600000d41e46803030b0041d091640040c0c040b820300020140c461503124a08810a040d005542c428200c90545500d0b0548005042c2c001c01013035105c00d900790140c040d0402d002c00601d07e441c407441c0e50554810b4103110580c104480002032504c1451940c3c0e6400030860040c0c106d40c02015000c000410340c2c0c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 741187050 741366906 := by
  have h0 := BRFrame.cov_init 741187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 741187050 ≤ n) (h2 : n < 741366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
